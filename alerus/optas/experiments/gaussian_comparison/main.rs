// Discrete Gaussian comparison harness: exact CKS against the OPTAS sampler
// (Saad et al., POPL 2020) as verified in alerus::optas. σ = n/d throughout.
//
// usage: gcmp MODE NSAMP n d OUT [B nt mb k]
//   cks              exact CKS (dashu bignums)
//   saad             the verified OPTAS pipeline, packed encoding and matrix
//   bench            where the time of one OPTAS sample goes (prints only;
//                    pass any OUT)
// Every mode but bench writes OUT: a header line of `key value` pairs, then
// one `z count` line per sampled value.
use alerus::cks::discrete_gaussian;
use alerus::ddg_walk::walk::{DdgWalk, Step};
use alerus::optas::{construct, examples::gaussian, matrix, opt, sample};
use std::collections::BTreeMap;
use std::io::Write;
use std::time::Instant;
use vstd::prelude::*;

// Ghost and tracked arguments are erased at run time.
fn g<T>() -> Ghost<T> { Ghost::assume_new() }
fn t<T>() -> Tracked<T> { Tracked::assume_new() }

fn cks_exact(n: u64, d: u64) -> i64 {
    i64::try_from(&discrete_gaussian::sample_discrete_gaussian_entry(n, d)).unwrap()
}

/// nsamp samples: the histogram, ns per sample, and RNG calls and bits per
/// sample (counted by the instrumented `random`, see random_counter.patch).
struct Run { hist: BTreeMap<i64, u64>, ns: f64, calls: f64, bits: f64 }

fn run(nsamp: u64, mut f: impl FnMut() -> i64) -> Run {
    let mut hist = BTreeMap::new();
    let (c0, b0) = random::rng_stats();
    let st = Instant::now();
    for _ in 0..nsamp { *hist.entry(f()).or_insert(0) += 1; }
    let ns = st.elapsed().as_nanos() as f64 / nsamp as f64;
    let (c1, b1) = random::rng_stats();
    Run { hist, ns, calls: (c1 - c0) as f64 / nsamp as f64, bits: (b1 - b0) / nsamp as f64 }
}

fn dump(path: &str, r: &Run, extra: &str) {
    let mut f = std::fs::File::create(path).unwrap();
    writeln!(f, "ns {} calls {} bits {}{}", r.ns, r.calls, r.bits, extra).unwrap();
    for (z, c) in &r.hist { writeln!(f, "{} {}", z, c).unwrap(); }
}

/// The OPTAS parameters: B, Taylor terms nt, weight bits mb, precision k.
struct Saad { b: u64, nt: u64, mb: u64, k: u64 }

fn saad(n: u64, d: u64, nsamp: u64, out: &str, s: &Saad) {
    // x = 1/(2σ²) = d²/(2n²)
    let (xn, xd) = (d * d, 2 * n * n);
    let st = Instant::now();
    let enc = gaussian::construct_gauss_encoding(xn, xd, s.b, s.nt, s.mb, s.k);
    let prep = st.elapsed().as_secs_f64();
    // the encoding in the C format of the artifact (senc.c): length, entries
    let mut f = std::fs::File::create(format!("{}.enc", out)).unwrap();
    writeln!(f, "{}", enc.enc.len()).unwrap();
    for v in &enc.enc { write!(f, "{} ", v).unwrap(); }
    writeln!(f).unwrap();
    let r = run(nsamp, || gaussian::sample_gauss_table(&enc, s.b, g(), g(), g(), t(), g()).0);
    // the matrix sampler, and M itself for the analysis
    let w = gaussian::gauss_input(xn, xd, s.b, s.nt, s.mb);
    let ms = opt::get_optimal_probabilities(1u128 << s.k, &w);
    let (p, k2, l2, _) = matrix::make_ddg_matrix(&ms, s.k, s.k);
    let rm = run(nsamp.min(1_000_000), || {
        sample::sample_ky_matrix(&p, k2, l2, g(), g(), t(), g()).0 as i64 - s.b as i64
    });
    let ms = ms.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    dump(out, &r, &format!(" ns_matrix {} prep_s {} enc_len {} k2 {} ms {}", rm.ns, prep, enc.enc.len(), k2, ms));
}

/// Where the time of one OPTAS sample goes, layer by layer.
fn bench(n: u64, d: u64, nsamp: u64, s: &Saad) {
    let w = gaussian::gauss_input(d * d, 2 * n * n, s.b, s.nt, s.mb);
    let ms = opt::get_optimal_probabilities(1u128 << s.k, &w);
    let (p, k2, l2, ms2) = matrix::make_ddg_matrix(&ms, s.k, s.k);
    let enc = construct::encode_ky_matrix(&p, k2, l2, ms2).unwrap();
    let time = |name: &str, f: &mut dyn FnMut() -> u64| {
        let st = Instant::now();
        let mut acc = 0u64;
        for _ in 0..nsamp { acc = acc.wrapping_add(f()); }
        println!("{:<58} {:>8.1} ns   (checksum {})", name, st.elapsed().as_nanos() as f64 / nsamp as f64, acc % 7);
    };
    // one coin flip
    time("opendp fill_bytes(1 byte)  [OpenSSL RAND_priv_bytes]", &mut || {
        let mut buf = [0u8; 1];
        opendp::traits::samplers::fill_bytes(&mut buf).unwrap();
        buf[0] as u64
    });
    time("random::rand_u64(2)        [opendp uint_below]", &mut || random::rand_u64(2));
    time("random::rand_ubig(2)       [opendp ubig_below]", &mut || {
        random::ubig_to_u64(&random::rand_ubig(random::ubig_from_u64(2)))
    });
    time("alerus rand_2_u64", &mut || alerus::rand_primitives::rand_2_u64(t(), g()).0);
    time("random::rand_bit()         [buffered 64-bit word]", &mut || random::rand_bit());
    time("alerus rand_2_u64_fast     [what the samplers call]", &mut || alerus::rand_primitives::rand_2_u64_fast(t(), g()).0);
    // a whole sample
    time("sample_ky_encoding (verified)", &mut || sample::sample_ky_encoding(&enc, g(), t(), g()).0);
    // the same walk on a buffered xorshift bit source, as C's flip() over rand()
    let mut st: u64 = 0x9E3779B97F4A7C15;
    let (mut word, mut pos) = (0u64, 0u32);
    let mut flip = move || -> u64 {
        if pos == 0 { st ^= st << 13; st ^= st >> 7; st ^= st << 17; word = st; pos = 64; }
        pos -= 1;
        (word >> pos) & 1
    };
    let mut flip2 = flip.clone();
    time("verified Encoded::root/step + xorshift bits", &mut || {
        let mut q = match enc.root() { Step::Next(q) => q, _ => unreachable!() };
        loop {
            match enc.step(q, flip()) {
                Step::Done(v) => return v,
                Step::Restart => q = 0,
                Step::Next(r) => q = r,
            }
        }
    });
    let e = &enc.enc;
    time("plain loop, as senc.c, + xorshift bits", &mut || {
        let mut c = 0usize;
        loop {
            c = e[c + flip2() as usize] as usize;
            if e[c] < 0 { return (-e[c]) as u64; }
        }
    });
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let num = |i: usize| -> u64 { a[i].parse().unwrap_or_else(|_| panic!("argument {} is not a number", i)) };
    let (mode, nsamp, n, d) = (a[1].as_str(), num(2), num(3), num(4));
    match mode {
        "cks" => dump(&a[5], &run(nsamp, || cks_exact(n, d)), ""),
        "saad" => saad(n, d, nsamp, &a[5], &Saad { b: num(6), nt: num(7), mb: num(8), k: num(9) }),
        "bench" => bench(n, d, nsamp, &Saad { b: num(6), nt: num(7), mb: num(8), k: num(9) }),
        _ => panic!("unknown mode {}", mode),
    }
}
