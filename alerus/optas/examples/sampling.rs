//! Algorithm 3, then a sampler. `optimal_matrix` and
//! `construct_optimal_encoding` build a table of the optimal M / Z_kl for
//! p = a / Σa, within n / (2 Z_kl) of p; `sample_approx` samples it, and
//! `sample_optimal` builds the matrix and samples once:
//!
//! ```text
//!   ε ≥ E_p[ℰ]        ℰ ∈ [0, 1]
//!   ----------------------------------------------------------------
//!   [{ ↯(ε + n / (2 Z_kl)) }] sample_optimal(a, k, l) [{ r. ↯(ℰ(r)) }]
//! ```

use vstd::prelude::*;

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::optas::utils::get_zkl;
use crate::optas::opt::get_optimal_probabilities;
use crate::optas::matrix::make_ddg_matrix;
use crate::optas::sample::MatrixWalk;
use crate::optas::approx::sample_approx;
use crate::optas::construct::encode_ky_matrix;
use crate::optas::tree::OptasSpec;
use crate::ddg_walk::encoding::Encoded;
#[cfg(verus_keep_ghost)]
use crate::ddg_walk::walk::{DdgSpec, DdgWalk};
#[cfg(verus_keep_ghost)]
use crate::optas::sample::sampler_input;
#[cfg(verus_keep_ghost)]
use crate::optas::utils::{zkl, lemma_zkl};
#[cfg(verus_keep_ghost)]
use crate::optas::opt::{ratio, lemma_near_bound};
#[cfg(verus_keep_ghost)]
use crate::optas::approx::{pexp, credit_alloc_bound, approximates, lemma_approximates_tv};
#[cfg(verus_keep_ghost)]
use crate::optas::ztype::{wsum_nat, lemma_ddg_exp_scale};

/// The inputs `sample_optimal` accepts: weights a (the target is p = a / Σa)
/// and a precision (k, l). Only size bounds; the optimal M is computed from
/// them (`optimal_matrix`).
pub open spec fn wf_weights(a: Seq<u128>, k: nat, l: nat) -> bool {
    &&& 0 < k <= 124 && l <= k
    &&& a.len() >= 1 && a.len() < 0x4000000000000000
    &&& 0 < wsum_nat(a, 0) <= 0x10000000000000000000000000000000
}

/// The slack of Theorem 4.17: n / (2 Z_kl).
pub open spec fn optimal_slack(n: nat, k: nat, l: nat) -> real {
    (n as real) / (2real * (zkl(k, l) as real))
}

/// Algorithm 3, then the matrix of Section 5: the matrix of the TV-optimal
/// Z_kl-type approximation M / Z of p = a / Σa (reduced to M′ / Z′), which
/// approximates p within n / (2 Z_kl).
pub fn optimal_matrix(a: &Vec<u128>, k: u64, l: u64) -> (r: (Vec<Vec<u8>>, u64, u64, Ghost<Seq<u128>>))
    requires wf_weights(a@, k as nat, l as nat),
    ensures
        sampler_input(r.0@, r.3@, r.1 as nat, r.2 as nat),
        r.3@.len() == a.len(),
        approximates(OptasSpec { ms: r.3@, k: r.1 as nat, l: r.2 as nat }, ratio(a@, wsum_nat(a@, 0)),
            optimal_slack(a.len() as nat, k as nat, l as nat)),
{
    let ghost p = ratio(a@, wsum_nat(a@, 0));
    let z = get_zkl(k, l);
    proof {
        lemma_zkl(k as nat, l as nat);
        crate::fldr_helper::lemma_pow2_mono(k as nat, 124);
        crate::optas::utils::lemma_pow2_consts();
    }
    // Obtain optimal probabilities (Algorithm 3).
    let ms = get_optimal_probabilities(z, a);
    // Construct the sampler (Section 5).
    let (p_mat, k2, l2, ms2) = make_ddg_matrix(&ms, k, l);
    proof {
        // E_{M/Z}[ℰ] ≤ E_p[ℰ] + TV ≤ E_p[ℰ] + n/(2Z)  (Theorem 4.17)
        let os = OptasSpec { ms: ms@, k: k as nat, l: l as nat };
        let os2 = OptasSpec { ms: ms2@, k: k2 as nat, l: l2 as nat };
        lemma_near_bound(a@, z as nat, ms@);
        lemma_approximates_tv(os, p);
        lemma_zkl(k2 as nat, l2 as nat);
        assert forall |e: spec_fn(nat) -> real| credit_alloc_bound(e) implies
            #[trigger] os2.target(e) <= pexp(p, e, ms2@.len(), 0) + optimal_slack(a.len() as nat, k as nat, l as nat) by {
            // the reduced fractions are the same distribution
            lemma_ddg_exp_scale(ms@, z as nat, ms2@, zkl(k2 as nat, l2 as nat), e);
            assert(os.target(e) <= pexp(p, e, ms@.len(), 0) + optimal_slack(a.len() as nat, k as nat, l as nat));
        }
    }
    (p_mat, k2, l2, ms2)
}

/// Sample the TV-optimal Z_kl-type approximation of p = a / Σa: build its
/// matrix and sample it once.
pub fn sample_optimal(
    a: &Vec<u128>,
    k: u64,
    l: u64,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        wf_weights(a@, k as nat, l as nat),
        credit_alloc_bound(e),
        eps >= pexp(ratio(a@, wsum_nat(a@, 0)), e, a.len() as nat, 0),
        input_credit@ =~= (Value { car: eps + optimal_slack(a.len() as nat, k as nat, l as nat) }),
    ensures
        (value as nat) < a.len(),
        out_credit@@ =~= (Value { car: e(value as nat) }),
{
    let (p_mat, k2, l2, ms2) = optimal_matrix(a, k, l);
    let w = MatrixWalk { p: &p_mat, k: k2, l: l2, ms: ms2 };
    sample_approx(&w, Ghost(ratio(a@, wsum_nat(a@, 0))), Ghost(optimal_slack(a.len() as nat, k as nat, l as nat)),
        Ghost(e), Tracked(input_credit), Ghost(eps))
}

/// The packed encoding of the optimal sampler, built as
/// `construct_sample_ky_encoding` builds it. Sample it with `sample_approx`.
pub fn construct_optimal_encoding(a: &Vec<u128>, k: u64, l: u64) -> (enc: Encoded<OptasSpec>)
    requires wf_weights(a@, k as nat, l as nat), a.len() < 0x4000000000000,
    ensures
        enc.wf(),
        enc.spec@.ms.len() == a.len(),
        approximates(enc.spec@, ratio(a@, wsum_nat(a@, 0)), optimal_slack(a.len() as nat, k as nat, l as nat)),
{
    let (p_mat, k2, l2, ms2) = optimal_matrix(a, k, l);
    encode_ky_matrix(&p_mat, k2, l2, ms2).unwrap()
}

} // verus!
