//! Fast sampler for Geometric(1 − e^{−n/d}) (CKS20).
//!
//! Algorithm:
//!
//! ```text
//!   u ← sample_exp_rejection(d)        // u ~ rejection_dist(d)
//!   v ← sample_geometric_exp(1, 1)     // v ~ Geometric(1 − e^{−1})
//!   z ← u + d · v
//!   return z / n                       // floor division
//! ```
//!
//! Distribution claim:  result ~ Geometric(1 − e^{−n/d}),  with PMF
//!
//!   outer_geom_pmf(r) = (e^{−n/d})^r · (1 − e^{−n/d}).
//!
//! Hoare rule we prove:
//!
//! ```text
//!   ε ≥ Σ_{r=0}^∞ outer_geom_pmf(r) · F(r)
//!   ─────────────────────────────────────────────────────
//!   [{ ↯(ε) }] sample_geometric_exp_fast(n/d) [{ r. ↯(F(r)) }]
//! ```
//!
//! ```text
//! Let
//!      N       := Σ_{u=0}^{d−1} e^{−u/d}                            [rej_norm_const]
//!                  (normalizer of rejection_dist on {0..d−1};
//!                   closed form: N = (1 − e^{−1})/(1 − e^{−1/d}),
//!                   discharged by `lemma_norm_const_identity`)
//!      g(u, v) := F((u + d·v) / n)                                  [g spec_fn]
//!      f(u)    := lim_{m→∞} Σ_{v<m} inner_geom_summand(v) · g(u, v) [f spec_fn]
//!      inner_geom_summand(v) := (e^{−1})^v · (1 − e^{−1})
//! ```
//! 
//! I.e. f(u) is the expected value of g(u, ·) under v ~ Geom(1 − e^{−1});
//! the inner Geom partial sums converge to f(u) (`lemma_f_is_limit`).
//!
//! We establish  E_{u ~ rejection_dist}[ f(u) ]  ≤  ε   via
//! ```text
//!   E_{u ~ rejection_dist}[ f(u) ]                                          (E6)
//!      = (1/N) · Σ_{u<d} e^{−u/d} · f(u)                                    (E5)
//!      = (1/N) · Σ_{u<d} e^{−u/d} · Σ_{v∈ℕ} inner_geom_summand(v) · g(u,v)  (E4)
//!      = (1 − e^{−1})/N · Σ_{u<d, v∈ℕ}                                      (E3)
//!                            e^{−u/d − v} · F((u + d·v) / n)
//!                  BIJECTION:      ℕ × {0..d−1}  ↔  ℕ, 
//!                                  (v, u)        ↔ u + d·v = k
//!      = (1 − e^{−1})/N · Σ_{k∈ℕ} e^{−k/d} · F(k / n)                       (E2)
//!                  BIJECTION:      ℕ × {0..n−1}  ↔  ℕ,
//!                                  (r, i)        ↔ n·r + i = k
//!        so F(k/n) = F(r),  e^{−k/d} = (e^{−n/d})^r · e^{−i/d};
//!        Σ_{i<n} e^{−i/d} = (1 − e^{−n/d})/(1 − e^{−1/d})  (closed form),
//!        and  N = (1 − e^{−1})/(1 − e^{−1/d})  cancels the (1 − e^{−1/d})
//!        denominator, leaving the prefactor (1 − e^{−n/d}).
//!      = Σ_{r∈ℕ} outer_geom_pmf(r) · F(r)                                   (E1)
//!      ≤ ε                                                                  (pre)
//! ```
//! EQUATION ↔ PROOF FUNCTION  (each step listed as "E_{from} → E_{to}"):
//!
//!   E6 → E5    Unfold rejection_dist.  Definitional:
//!              `rej_weighted_avg(d, F) := rej_weighted_sum(d, F, d) / N`.
//!              Discharged inside `lemma_weighted_avg_bound`.
//!
//!   E5 → E4    Unfold f as the limit of inner Geom partial sums.
//!              `lemma_f_is_limit` identifies f(u) with that limit, and
//!              `lemma_geo_exp_partial_eq_inner` bridges
//!                  (1 − e^{−1}) · inner_at_u  =  geo_exp_partial_sum.
//!
//!   E4 → E3    Per-term algebraic factoring (no limit interchange): pull
//!              (1 − e^{−1}) out of the inner sum and combine exponents,
//!              e^{−u/d} · (e^{−1})^v = e^{−u/d − v}.  Both lines carry the
//!              same Σ_{v∈ℕ}; this is just the summand rewritten.
//!
//!   E3 ↔ E2    EUCLIDEAN BIJECTION (divisor d):
//!              `lemma_euclidean_bijection_partial` proves the finite
//!              re-indexing  Σ_{u<d, v<M} = Σ_{k<d·M}  term-by-term.
//!
//!   E2 → E1    BUCKETING (divisor n) + closed-form sums:
//!              `lemma_outer_partial_buckets`         (k → (r, i) bucketing);
//!              `lemma_rej_weight_sum_telescope`      (Σ_{i<n} e^{−i/d}
//!                                                     telescoping closed form);
//!              `lemma_norm_const_identity`           (N · (1 − e^{−1/d}) = 1 − e^{−1});
//!              `lemma_key_identity`                  glues the three together.
//!
//!   E1 ≤ ε     Hoare-rule precondition handed in by the caller.
//!
//! FINITE TRUNCATION + PASS TO THE LIMIT.  The bijection / bucket / closed-form
//! lemmas above operate at a finite v-cutoff m, so the chain is run truncated:
//! `lemma_partial_weighted_avg_bound` bundles E3 ↔ E2 → E1 at each m,
//!      ∀ m.  (1 − e^{−1}) · joint_helper(numer, denom, e, m, d)  ≤  N · dist_bound,
//! where the LHS is the m-th partial sum of the E3 double-sum.  Write
//! S := Σ_{u<d} e^{−u/d} · f(u)  (so E6 = S / N).  Two limit facts finish:
//!   • `lemma_weighted_joint_helper_converges`:  as m → ∞ that LHS converges to
//!     S  (sum-of-limits over the finite outer u-sum, via
//!     `math::series::lemma_limit_add` / `lemma_limit_scale`), and
//!   • `math::series::lemma_limit_le_bound`:  a limit of values all ≤ N · dist_bound
//!     is itself ≤ N · dist_bound,  so  S ≤ N · dist_bound.
//! Dividing by N gives  E6 = S / N ≤ dist_bound,  i.e. dist_bound ≥ E_{u ~ μ_{L(d)}}[ f(u) ].
//!
//! LIMIT-PASS-THROUGH LEMMAS (lifting partial-sum facts to facts about f):
//!
//!   • `lemma_f_nonneg`           — f(u) ≥ 0 for u < d
//!                                  (`lemma_inner_partial_nonneg_at`
//!                                   + `math::series::lemma_limit_ge_bound`).
//!   • `lemma_f_bounds_inner`     — f(u) ≥ every inner Geom partial sum
//!                                  (`lemma_geo_exp_partial_nondecreasing`
//!                                   + `math::series::lemma_monotone_limit_upper_bound`).
//!   • `lemma_weighted_avg_bound` — dist_bound ≥ E_{u ~ rejection_dist}[ f(u) ]
//!                                  (the E6 → E1 chain, packaged).
//!

use vstd::prelude::*;

use random::{UBig, ubig_div, ubig_add, ubig_mul};

verus! {

use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::cks::geometric_exp_fast_helper::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::{ExUBig, ubig_view};
#[cfg(verus_keep_ghost)]
use crate::math::exp::{exp, axiom_exp_zero, axiom_exp_neg_range, axiom_exp_neg_strict, axiom_exp_add};
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;
#[cfg(verus_keep_ghost)]
use crate::math::series::{
    is_nondecreasing, is_bounded_above, is_bounded_below,
    converges, converges_to, exists_close_suffix, suffix_is_close,
    seq_at,
    axiom_monotone_convergence, lemma_monotone_limit_upper_bound,
    lemma_limit_ge_bound, lemma_limit_le_bound,
    lemma_limit_add, lemma_limit_scale, lemma_limit_pointwise_eq,
    lemma_pow_nonneg,
};
use crate::cks::exp_rejection::{sample_exp_rejection,};
#[cfg(verus_keep_ghost)]
use crate::cks::exp_rejection::{rej_weight, rej_weight_sum, rej_weighted_sum, rej_norm_const, rej_weighted_avg};
#[cfg(verus_keep_ghost)]
use crate::cks::exp_rejection_helper::{lemma_rej_weight_sum_telescope, lemma_norm_const_identity};
#[cfg(verus_keep_ghost)]
use crate::cks::geometric_exp::{
    geo_exp_series_bounded_by, geo_exp_partial_sum, geo_exp_summand
};
use crate::cks::geometric_exp::{
    sample_geometric_exp as sample_geometric_exp_slow
};

/// Outer Geometric PMF:  μ_S(r) = (e^{−n/d})^r · (1 − e^{−n/d}).
pub open spec fn outer_geom_pmf(numer: nat, denom: nat, r: nat) -> real {
    geo_exp_summand(exp(-(numer as real / denom as real)), |k: nat| 1real, r)
}

/// Inner-call postcondition at residue u:
///   g(u, v) = F((u + d·v) / n)
pub open spec fn g(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real,
) -> spec_fn(nat) -> real {
    |v: nat| e((v * denom + u) / numer)
}

/// Named sequence  m ↦ Σ_{v<m} (e^{−1})^v · (1 − e^{−1}) · g(u, v)
/// — avoids per-callsite lambda creation that confuses Z3 in
/// `is_nondecreasing` proofs.
pub open spec fn inner_partial_seq(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real,
) -> spec_fn(nat) -> real {
    |m: nat| geo_exp_partial_sum(exp(-1real), g(numer, denom, u, e), m)
}

/// Credit handed to L(d) at residue u:  f(u) = E_v[g(u, v)].
///
///   For u < d:  the limit of the inner Geom(1 − e^{−1}) partial sums with
///               postcondition g(u, ·).  The partial sums are nondecreasing
///               and nonneg; `lemma_partial_weighted_avg_bound` (via the
///               proved bijection + bucket bound) gives a uniform upper bound,
///               so by monotone convergence the limit exists and `choose`
///               picks it.  See `lemma_inner_seq_converges`, `lemma_f_is_limit`.
///   For u ≥ d:  0  (never arises from L(d); giving f a uniform nonneg default
///               keeps the credit allocation nonneg without a partial-domain dance).
pub open spec fn f(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real,
) -> real {
    if u < denom {
        choose |l: real| converges_to(
            inner_partial_seq(numer, denom, u, e), l)
    } else { 0real }
}

// All partial sums below are written so the (1 − e^{−1}) factor is not
// included; we multiply once at the end when extracting the inner Geom
// partial-sum identity. This keeps every recursion clean.

/// Single-index partial sum, abbreviated `outer(K)` in comments:
///   outer(K) := Σ_{k<K} e^{−k/d} · F(k/n).
pub open spec fn outer_partial(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, k_bound: nat,
) -> real
    decreases k_bound,
{
    if k_bound == 0 { 0real }
    else {
        outer_partial(numer, denom, e, (k_bound - 1) as nat)
            + rej_weight(denom, (k_bound - 1) as nat)
                * e(((k_bound - 1) as nat) / numer)
    }
}

/// Inner sum at residue u (without the (1−e^{−1}) factor), abbreviated
/// `inner(u, m)` in comments:
///   inner(u, m) := Σ_{v<m} (e^{−1})^v · F((u + d·v)/n).
pub open spec fn inner_at_u(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real, m: nat,
) -> real
    decreases m,
{
    if m == 0 { 0real }
    else {
        inner_at_u(numer, denom, u, e, (m - 1) as nat)
            + pow(exp(-1real), (m - 1) as nat)
                * e((u + denom * ((m - 1) as nat)) / numer)
    }
}

/// The joint (u, v) partial sum, abbreviated `joint(m, u_max)` in comments:
///   joint(m, u_max) := Σ_{u<u_max} e^{−u/d} · Σ_{v<m} (e^{−1})^v · F((u + d·v)/n)
///                    = Σ_{u<u_max} e^{−u/d} · inner(u, m).
pub open spec fn joint_helper(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat, u_max: nat,
) -> real
    decreases u_max,
{
    if u_max == 0 { 0real }
    else {
        joint_helper(numer, denom, e, m, (u_max - 1) as nat)
            + rej_weight(denom, (u_max - 1) as nat)
                * inner_at_u(numer, denom, (u_max - 1) as nat, e, m)
    }
}

/// Row sum at depth m, abbreviated `row(m, u_max)` in comments:
///   row(m, u_max) := Σ_{u<u_max} e^{−u/d} · F((u + d·m)/n).
pub open spec fn outer_row_partial(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat, u_max: nat,
) -> real
    decreases u_max,
{
    if u_max == 0 { 0real }
    else {
        outer_row_partial(numer, denom, e, m, (u_max - 1) as nat)
            + rej_weight(denom, (u_max - 1) as nat)
                * e((((u_max - 1) as nat) + denom * m) / numer)
    }
}

/// Σ_{r<R} p^r · e(r)  — partial sum without the (1−p) factor.
pub open spec fn pow_partial(p: real, e: spec_fn(nat) -> real, r_max: nat) -> real
    decreases r_max,
{
    if r_max == 0 { 0real }
    else {
        pow_partial(p, e, (r_max - 1) as nat)
            + pow(p, (r_max - 1) as nat) * e((r_max - 1) as nat)
    }
}

// ============================================================================
// Fast sampler  (composes L(d) and slow Geom).
//   • `lemma_f_nonneg` + `lemma_weighted_avg_bound`  →  feed L(d).
//   • `lemma_f_bounds_inner` (specialized to the sampled u)  →  feed slow Geom.
// ============================================================================

/// Fast Geometric(1 − e^{−n/d}) sampler:
///   u ← sample_exp_rejection(d);
///   v ← sample_geometric_exp(1, 1);
///   return (u + d·v) / n.
///
///   ε ≥ Σ_{r=0}^∞ (e^{−n/d})^r · (1 − e^{−n/d}) · F(r)
///   ─────────────────────────────────────────────────────
///   [{ ↯(ε) }] sample_geometric_exp_fast(n/d) [{ r. ↯(F(r)) }]
pub fn sample_geometric_exp_fast(
    numer_x: &UBig,
    denom_x: &UBig,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(dist_bound): Ghost<real>,
) -> ((value, out_credit): (UBig, Tracked<ErrorCreditResource>))
    requires
        ubig_view(numer_x) > 0, ubig_view(denom_x) > 0,
        0real < p < 1real,
        p == exp(-(ubig_view(numer_x) as real / ubig_view(denom_x) as real)),
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        input_credit@ =~= (Value { car: dist_bound }),
        geo_exp_series_bounded_by(p, e, dist_bound),
    ensures
        out_credit@@ =~= (Value { car: e(ubig_view(&value)) }),
{
    let ghost nx = ubig_view(numer_x);
    let ghost dx = ubig_view(denom_x);
    // f packaged as a spec_fn, used as the postcondition handed to L(d).
    let ghost f_of_u: spec_fn(nat) -> real = |u: nat| f(nx, dx, u, e);

    // Ingredients needed for the L(d) call: f(u) ≥ 0 for all u, and
    // dist_bound ≥ E_{u ~ μ_{L(d)}}[f(u)].
    proof {
        // Nonneg for u < d via the per-residue limit lemma; for u ≥ d the
        // 0-default in `f` gives nonneg trivially.
        assert forall |u: nat| (#[trigger] f_of_u(u)) >= 0real by {
            if u < dx {
                lemma_f_nonneg(nx, dx, e, dist_bound, u);
            } else {
                assert(f_of_u(u) == 0real);
            }
        };
        lemma_weighted_avg_bound(nx, dx, e, dist_bound);
    }

    let (u, Tracked(u_credit)) = sample_exp_rejection(
        denom_x,
        Ghost(f_of_u),
        Tracked(input_credit),
        Ghost(dist_bound),
    );
    // Post: ↯(f(u))
    let ghost un = ubig_view(&u);

    let ghost g_at_u = g(nx, dx, un, e);
    let ghost f_at_u = f(nx, dx, un, e);
    let ghost p1 = exp(-1real);

    proof {
        axiom_exp_neg_range(1real);
        axiom_exp_neg_strict(1real);
        // g(u, v) = e((v·d + u) / n) ≥ 0 since e ≥ 0 everywhere.
        assert(forall |v: nat| (#[trigger] g_at_u(v)) >= 0real);
        // f(u) bounds every inner Geom partial sum at this specific u.
        //   f(u) ≥ Σ_{v<m} (e^{−1})^v (1 − e^{−1}) g(u, v)  ∀m
        lemma_f_bounds_inner(nx, dx, e, dist_bound, un);
    }

    let (v, Tracked(v_credit)) = sample_geometric_exp_slow(
        1u64, 1u64, Ghost(p1), Ghost(g_at_u), Tracked(u_credit), Ghost(f_at_u),
    );
    // Post: ↯(g(u, v)) = ↯(e((v·d + u) / n))

    // Algorithmic step: z = u + d·v; return z / n.
    // Postcondition: e((v·d + u) / n) = e(result), so we get ↯(F(result)).
    let ghost vn = ubig_view(&v);
    let v_scaled = ubig_mul(&v, &denom_x);
    let sum = ubig_add(&v_scaled, &u);
    let result = ubig_div(&sum, &numer_x);
    proof {
        assert(ubig_view(&v_scaled) == vn * dx);
        assert(ubig_view(&sum) == vn * dx + un);
        assert(ubig_view(&result) == (vn * dx + un) / nx);
    }
    (result, Tracked(v_credit))
}

} // verus!
 