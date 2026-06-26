use alerus::{alias, cks, fldr, geo, geo_dist, ho_rej_samp};

fn main() {
    println!("Geometric Distribution Test");
    for _ in 0..100 {
        println!("{}", geo::geometric());
    }

    println!("Geometric Distribution (UBig) Test");
    for _ in 0..100 {
        let v = geo_dist::geo_dist_sample();
        println!("{}", v);
    }

    println!("Discrete Laplace (scale=4) Test");
    let mut res = Vec::new();
    for _ in 0..100 {
        let v = cks::discrete_laplace::sample_discrete_laplace_entry(1, 4);
        res.push(v);
    }
    println!("{:?}", res);

    println!("Rejection Sampler Test");
    println!("{}", ho_rej_samp::example_rejection_sampler());

    println!("FLDR p = (7/19, 4/19, 8/19)");
    let mut bad = [0u64; 3];
    for _ in 0..1900 {
        bad[fldr::example_fldr() as usize] += 1;
    }
    println!("{:?}  (expected ratio 7:4:8)", bad);

    println!("Alias method p = (7/19, 4/19, 8/19)  [weights 7,4,8]");
    let mut al = [0u64; 3];
    for _ in 0..1900 {
        al[alias::example_alias() as usize] += 1;
    }
    println!("{:?}  (expected ratio 7:4:8)", al);
}
