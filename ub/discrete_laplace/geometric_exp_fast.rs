// Fast sampler for Geometric(1 − e^{−n/d}) (CKS20).
//
// Algorithm:
//
//   u ← sample_exp_rejection(d)        // u ~ rejection_dist(d)
//   v ← sample_geometric_exp(1, 1)     // v ~ Geometric(1 − e^{−1})
//   z ← u + d · v
//   return z / n                       // floor division
//
// Distribution claim:  result ~ Geometric(1 − e^{−n/d}),  with PMF
//
//   outer_geom_pmf(r) = (e^{−n/d})^r · (1 − e^{−n/d}).
//     same as μₛ(r)
//
// Hoare rule we prove:
//
//   ε ≥ Σ_{r=0}^∞ outer_geom_pmf(r) · F(r)
//   ─────────────────────────────────────────────────────
//   [{ ↯(ε) }] sample_geometric_exp_fast(n/d) [{ r. ↯(F(r)) }]
//
// ─────────────────────────────────────────────────────────────────────────────
//  EQUATIONAL DERIVATION (the chain of identities the proof mirrors)
//
//  Equations are labeled E1 … E6 (top-of-chain = E6).  See the
//  "EQUATION ↔ PROOF FUNCTION" block below for the mapping from each step
//  to the Verus lemma that discharges it.
// ─────────────────────────────────────────────────────────────────────────────
//
// Let
//      N       := Σ_{u=0}^{d−1} e^{−u/d}                            [rej_norm_const]
//                  (normalizer of rejection_dist on {0..d−1};
//                   closed form: N = (1 − e^{−1})/(1 − e^{−1/d}),
//                   discharged by `lemma_norm_const_identity`)
//      g(u, v) := F((u + d·v) / n)                                  [g spec_fn]
//      f(u)    := lim_{m→∞} Σ_{v<m} inner_geom_summand(v) · g(u, v) [f spec_fn]
//      inner_geom_summand(v) := (e^{−1})^v · (1 − e^{−1})
//
// I.e. f(u) is the expected value of g(u, ·) under v ~ Geom(1 − e^{−1});
// the inner Geom partial sums converge to f(u) (`lemma_f_is_limit`).
//
// We establish  E_{u ~ rejection_dist}[ f(u) ]  ≤  ε   via
//
//   E_{u ~ rejection_dist}[ f(u) ]                                          (E6)
//      = (1/N) · Σ_{u<d} e^{−u/d} · f(u)                                    (E5)
//      = (1/N) · Σ_{u<d} e^{−u/d} · Σ_{v∈ℕ} inner_geom_summand(v) · g(u,v)  (E4)
//      = (1 − e^{−1})/N · Σ_{u<d, v∈ℕ}                                      (E3)
//                            e^{−u/d − v} · F((u + d·v) / n)
//        EUCLIDEAN BIJECTION:      ℕ × {0..d−1}  ↔  ℕ, 
//                                  (v, u)        ↔ u + d·v = k
//      = (1 − e^{−1})/N · Σ_{k∈ℕ} e^{−k/d} · F(k / n)                       (E2)
//        EUCLIDEAN BIJECTION:      ℕ × {0..n−1}  ↔  ℕ,
//                                  (r, i)        ↔ n·r + i = k
//        so F(k/n) = F(r),  e^{−k/d} = (e^{−n/d})^r · e^{−i/d};
//        Σ_{i<n} e^{−i/d} = (1 − e^{−n/d})/(1 − e^{−1/d})  (closed form),
//        and  N = (1 − e^{−1})/(1 − e^{−1/d})  cancels the (1 − e^{−1/d})
//        denominator, leaving the prefactor (1 − e^{−n/d}).
//      = Σ_{r∈ℕ} outer_geom_pmf(r) · F(r)                                   (E1)
//      ≤ ε                                                                  (pre)
//
// EQUATION ↔ PROOF FUNCTION  (each step listed as "E_{from} → E_{to}"):
//
//   E6 → E5    Unfold rejection_dist.  Definitional:
//              `rej_weighted_avg(d, F) := rej_weighted_sum(d, F, d) / N`.
//              Discharged inside `lemma_weighted_avg_bound`.
//
//   E5 → E4    Unfold f as the limit of inner Geom partial sums.
//              `lemma_f_is_limit` identifies f(u) with that limit, and
//              `lemma_geo_exp_partial_eq_inner` bridges
//                  (1 − e^{−1}) · inner_at_u  =  geo_exp_partial_sum.
//
//   E4 → E3    Algebraic factoring + finite sum-of-limits (over u ∈ {0..d−1}).
//              `lemma_weighted_joint_helper_converges` does the induction on
//              u_max, using `math::series::lemma_limit_add` and
//              `lemma_limit_scale`.  The Σ_{v ∈ ℕ} on the E4 line is realized
//              only at the limit; the partial-sum analog at each m sits inside
//              `joint_helper(m, d)`.
//
//   E3 ↔ E2    EUCLIDEAN BIJECTION (divisor d):
//              `lemma_euclidean_bijection_partial` proves the finite
//              re-indexing  Σ_{u<d, v<M} = Σ_{k<d·M}  term-by-term.  The
//              ∞-form is reached after `lemma_weighted_joint_helper_converges`
//              passes to the limit.
//
//   E2 → E1    BUCKETING (divisor n) + closed-form sums:
//              `lemma_outer_partial_buckets`         (k → (r, i) bucketing);
//              `lemma_rej_weight_sum_telescope`      (Σ_{i<n} e^{−i/d}
//                                                     telescoping closed form);
//              `lemma_norm_const_identity`           (N · (1 − e^{−1/d}) = 1 − e^{−1});
//              `lemma_key_identity`                  glues the three together.
//
//   E1 ≤ ε     Hoare-rule precondition handed in by the caller.
//
// PARTIAL-SUM BUNDLING.  Steps E3 ↔ E2 → E1 are bundled at the finite
// (m-truncated) level by `lemma_partial_weighted_avg_bound`:
//      ∀ m.  (1 − e^{−1}) · joint_helper(numer, denom, e, m, d)  ≤  N · dist_bound,
// whose LHS is the m-th partial sum of the E3 double-sum.  Passing this
// uniform bound through the limit (`lemma_weighted_joint_helper_converges`
// for convergence + `math::series::lemma_limit_le_bound` for the pass-through)
// is what gives E6 ≤ N · dist_bound, i.e. dist_bound ≥ E_{u ~ μ_{L(d)}}[ f(u) ].
//
// LIMIT-PASS-THROUGH LEMMAS (lifting partial-sum facts to facts about f):
//
//   • `lemma_f_nonneg`           — f(u) ≥ 0 for u < d
//                                  (`lemma_inner_partial_nonneg_at`
//                                   + `math::series::lemma_limit_ge_bound`).
//   • `lemma_f_bounds_inner`     — f(u) ≥ every inner Geom partial sum
//                                  (`lemma_geo_exp_partial_nondecreasing`
//                                   + `math::series::lemma_monotone_limit_upper_bound`).
//   • `lemma_weighted_avg_bound` — dist_bound ≥ E_{u ~ rejection_dist}[ f(u) ]
//                                  (the E6 → E1 chain, packaged).
//
// No axioms remain beyond standard exp / series ones.  The fast sampler then
// composes the two already-formalized Hoare rules:
//
//   • sample_exp_rejection :  ε ≥ E_{u ~ rejection_dist}[ f(u) ]   (consumes E6 ≤ ε)
//   • sample_geometric_exp :  f(u) ≥ E_{v ~ Geom(1 − e^{−1})}[ g(u, v) ]
//                                                                 (consumes E5 → E4)

use vstd::prelude::*;

use random::{UBig, ubig_div_u64, ubig_add_u64, ubig_mul_u64};

verus! {

use crate::ub::*;
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
use crate::discrete_laplace::exp_rejection::{sample_exp_rejection,};
#[cfg(verus_keep_ghost)]
use crate::discrete_laplace::exp_rejection::{
    rej_weight, rej_weight_sum, rej_weighted_sum, rej_norm_const, rej_weighted_avg,
    lemma_rej_weight_step, lemma_rej_weight_sum_telescope, lemma_norm_const_identity,
};
#[cfg(verus_keep_ghost)]
use crate::discrete_laplace::geometric_exp::{
    geo_exp_series_bounded_by, geo_exp_partial_sum, geo_exp_summand
};
use crate::discrete_laplace::geometric_exp::{
    sample_geometric_exp as sample_geometric_exp_slow
};

// ============================================================================
// Spec functions
// ============================================================================

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

// ============================================================================
// Building blocks for the bijection proof (E3 ↔ E2)
// ============================================================================

// All partial sums below are written so the (1 − e^{−1}) factor is *not*
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

// ----------------------------------------------------------------------------
// Helper lemmas about e^{−m} and the row block
// ----------------------------------------------------------------------------

/// e^{−m} == (e^{−1})^m.
proof fn lemma_exp_neg_nat(m: nat)
    ensures exp(-(m as real)) == pow(exp(-1real), m),
    decreases m,
{
    if m == 0 {
        axiom_exp_zero();
        assert(-(0nat as real) == 0real);
        assert(pow(exp(-1real), 0nat) == 1real);
    } else {
        lemma_exp_neg_nat((m - 1) as nat);
        // e^{−m} = e^{−((m−1) + 1)} = e^{−(m−1)} · e^{−1}
        axiom_exp_add((m - 1) as real, 1real);
        assert((m - 1) as real + 1real == m as real) by(nonlinear_arith);
        // (e^{−1})^m = e^{−1} · (e^{−1})^{m−1}
        assert(pow(exp(-1real), m) == exp(-1real) * pow(exp(-1real), (m - 1) as nat));
        // Combine
        assert(exp(-(m as real)) == pow(exp(-1real), m)) by(nonlinear_arith)
            requires
                exp(-(m as real)) == exp(-((m - 1) as real)) * exp(-1real),
                exp(-((m - 1) as real)) == pow(exp(-1real), (m - 1) as nat),
                pow(exp(-1real), m) == exp(-1real) * pow(exp(-1real), (m - 1) as nat);
    }
}

/// e^{−(u + d·m)/d}  ==  e^{−u/d} · (e^{−1})^m.
proof fn lemma_rej_weight_shift(d: nat, u: nat, m: nat)
    requires d > 0,
    ensures
        rej_weight(d, u + d * m) == rej_weight(d, u) * pow(exp(-1real), m),
{
    let a = u as real / d as real;
    let b = m as real;
    assert(a >= 0real) by(nonlinear_arith) requires d > 0, a == u as real / d as real;
    assert(b >= 0real);
    axiom_exp_add(a, b);
    // e^{−(a+b)} = e^{−a} · e^{−b}
    // a + b = u/d + m = (u + d·m) / d
    assert((u + d * m) as real / d as real == a + b) by(nonlinear_arith)
        requires d > 0, a == u as real / d as real, b == m as real;
    // e^{−(u + d·m)/d} = e^{−(a+b)}
    assert(rej_weight(d, u + d * m) == exp(-(a + b)));
    assert(rej_weight(d, u) == exp(-a));
    // e^{−m} = (e^{−1})^m
    lemma_exp_neg_nat(m);
}

// ----------------------------------------------------------------------------
// outer_partial block extraction
// ----------------------------------------------------------------------------

/// Σ_{k < d·m + u_max} e^{−k/d} · F(k/n)  −  Σ_{k < d·m} e^{−k/d} · F(k/n)
///   = (e^{−1})^m · Σ_{u < u_max} e^{−u/d} · F((u + d·m)/n).
///
/// (The row sum uses e^{−u/d}; the outer sum at offset d·m uses
/// e^{−(d·m + u)/d} = e^{−u/d} · (e^{−1})^m.  The (e^{−1})^m factor bridges
/// the two.)
#[verifier(spinoff_prover)]
proof fn lemma_outer_partial_block_scaled(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat, u_max: nat,
)
    requires denom > 0,
    ensures
        outer_partial(numer, denom, e, denom * m + u_max)
            == outer_partial(numer, denom, e, denom * m)
                + pow(exp(-1real), m) * outer_row_partial(numer, denom, e, m, u_max),
    decreases u_max,
{
    if u_max == 0 {
        assert(denom * m + 0 == denom * m);
        assert(outer_row_partial(numer, denom, e, m, 0nat) == 0real);
        assert(pow(exp(-1real), m) * 0real == 0real) by(nonlinear_arith);
    } else {
        let k = (u_max - 1) as nat;
        lemma_outer_partial_block_scaled(numer, denom, e, m, k);
        assert(denom * m + u_max == (denom * m + k) + 1) by(nonlinear_arith)
            requires u_max == k + 1;
        // outer sum step at index d·m + k.
        assert(outer_partial(numer, denom, e, denom * m + u_max)
            == outer_partial(numer, denom, e, denom * m + k)
                + rej_weight(denom, denom * m + k) * e((denom * m + k) / numer));
        // row sum step at index k.
        assert(outer_row_partial(numer, denom, e, m, u_max)
            == outer_row_partial(numer, denom, e, m, k)
                + rej_weight(denom, k) * e((k + denom * m) / numer));
        // Key identity: e^{−(d·m + k)/d} = e^{−k/d} · (e^{−1})^m.
        lemma_rej_weight_shift(denom, k, m);
        // Index match: (denom*m + k) / numer == (k + denom*m) / numer
        assert(denom * m + k == k + denom * m) by(nonlinear_arith);
        // Combine via nonlinear_arith.
        let pwr = pow(exp(-1real), m);
        let wk = rej_weight(denom, k);
        let ev = e((denom * m + k) / numer);
        assert((k + denom * m) / numer == (denom * m + k) / numer);
        assert(outer_partial(numer, denom, e, denom * m + u_max)
            == outer_partial(numer, denom, e, denom * m)
                + pwr * outer_row_partial(numer, denom, e, m, u_max))
            by(nonlinear_arith)
            requires
                outer_partial(numer, denom, e, denom * m + u_max)
                    == outer_partial(numer, denom, e, denom * m + k) + (wk * pwr) * ev,
                outer_partial(numer, denom, e, denom * m + k)
                    == outer_partial(numer, denom, e, denom * m) + pwr * outer_row_partial(numer, denom, e, m, k),
                outer_row_partial(numer, denom, e, m, u_max)
                    == outer_row_partial(numer, denom, e, m, k) + wk * ev,
                rej_weight(denom, denom * m + k) == wk * pwr;
    }
}

// ----------------------------------------------------------------------------
// joint_helper step
// ----------------------------------------------------------------------------

/// joint(m+1, u_max) − joint(m, u_max) = (e^{−1})^m · row(m, u_max),
/// where joint, row are the joint and row partial sums respectively.
#[verifier(spinoff_prover)]
proof fn lemma_joint_helper_step(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat, u_max: nat,
)
    requires denom > 0,
    ensures
        joint_helper(numer, denom, e, m + 1, u_max)
            == joint_helper(numer, denom, e, m, u_max)
                + pow(exp(-1real), m) * outer_row_partial(numer, denom, e, m, u_max),
    decreases u_max,
{
    if u_max == 0 {
        assert(outer_row_partial(numer, denom, e, m, 0nat) == 0real);
        assert(pow(exp(-1real), m) * 0real == 0real) by(nonlinear_arith);
    } else {
        let k = (u_max - 1) as nat;
        lemma_joint_helper_step(numer, denom, e, m, k);
        let wk = rej_weight(denom, k);
        let pwr = pow(exp(-1real), m);
        // inner step: inner(k, m+1) = inner(k, m) + (e^{−1})^m · F((k + d·m)/n).
        assert(inner_at_u(numer, denom, k, e, m + 1)
            == inner_at_u(numer, denom, k, e, m)
                + pow(exp(-1real), m) * e((k + denom * m) / numer));
        // joint step at k:
        assert(joint_helper(numer, denom, e, m + 1, u_max)
            == joint_helper(numer, denom, e, m + 1, k)
                + wk * inner_at_u(numer, denom, k, e, m + 1));
        assert(joint_helper(numer, denom, e, m, u_max)
            == joint_helper(numer, denom, e, m, k)
                + wk * inner_at_u(numer, denom, k, e, m));
        // row step at k:
        assert(outer_row_partial(numer, denom, e, m, u_max)
            == outer_row_partial(numer, denom, e, m, k)
                + wk * e((k + denom * m) / numer));
        let ev = e((k + denom * m) / numer);
        // Combine via nonlinear_arith
        assert(joint_helper(numer, denom, e, m + 1, u_max)
            == joint_helper(numer, denom, e, m, u_max) + pwr * outer_row_partial(numer, denom, e, m, u_max))
            by(nonlinear_arith)
            requires
                joint_helper(numer, denom, e, m + 1, u_max)
                    == joint_helper(numer, denom, e, m + 1, k)
                        + wk * (inner_at_u(numer, denom, k, e, m) + pwr * ev),
                joint_helper(numer, denom, e, m + 1, k)
                    == joint_helper(numer, denom, e, m, k) + pwr * outer_row_partial(numer, denom, e, m, k),
                joint_helper(numer, denom, e, m, u_max)
                    == joint_helper(numer, denom, e, m, k) + wk * inner_at_u(numer, denom, k, e, m),
                outer_row_partial(numer, denom, e, m, u_max)
                    == outer_row_partial(numer, denom, e, m, k) + wk * ev;
    }
}

// ----------------------------------------------------------------------------
// Finite Euclidean bijection (E3 ↔ E2)
// ----------------------------------------------------------------------------

/// Σ_{u<d, v<m} e^{−u/d} · (e^{−1})^v · F((u + d·v)/n)
///   == Σ_{k < d·m} e^{−k/d} · F(k/n).
///
/// The joint (u, v) double sum equals the single-index k sum via the
/// Euclidean bijection (u, v) ↔ u + d·v on {0..d-1} × ℕ ↔ ℕ.
pub proof fn lemma_euclidean_bijection_partial(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat,
)
    requires denom > 0,
    ensures
        joint_helper(numer, denom, e, m, denom)
            == outer_partial(numer, denom, e, denom * m),
    decreases m,
{
    if m == 0 {
        // joint(0, d) = 0 (each inner(_, 0) = 0).
        lemma_joint_helper_zero_m(numer, denom, e, denom);
        // outer(d·0) = outer(0) = 0.
        assert(denom * 0 == 0);
    } else {
        let k = (m - 1) as nat;
        lemma_euclidean_bijection_partial(numer, denom, e, k);
        // IH:  joint(k, d) == outer(d·k).
        lemma_joint_helper_step(numer, denom, e, k, denom);
        // joint(m, d) = joint(k, d) + (e^{−1})^k · row(k, d).
        lemma_outer_partial_block_scaled(numer, denom, e, k, denom);
        // outer(d·k + d) = outer(d·k) + (e^{−1})^k · row(k, d).
        assert(denom * m == denom * k + denom) by(nonlinear_arith)
            requires m == k + 1;
        // Combine: joint(m, d) = outer(d·m).
    }
}

/// Auxiliary: joint(0, u_max) = 0 for all u_max.
proof fn lemma_joint_helper_zero_m(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, u_max: nat,
)
    ensures joint_helper(numer, denom, e, 0nat, u_max) == 0real,
    decreases u_max,
{
    if u_max > 0 {
        let k = (u_max - 1) as nat;
        lemma_joint_helper_zero_m(numer, denom, e, k);
        // inner(_, 0) = 0
        assert(inner_at_u(numer, denom, k, e, 0nat) == 0real);
        // joint(0, u_max) = joint(0, k) + e^{−k/d} · 0 = 0 + 0 = 0
        assert(joint_helper(numer, denom, e, 0nat, u_max)
            == joint_helper(numer, denom, e, 0nat, k)
                + rej_weight(denom, k) * inner_at_u(numer, denom, k, e, 0nat));
        assert(rej_weight(denom, k) * 0real == 0real) by(nonlinear_arith);
    }
}

// ----------------------------------------------------------------------------
// Bucket bound (E2 → E1)
//
// The header equational chain bucketizes k ∈ ℕ as  k = n·r + i  with
// i ∈ {0..n−1} and r ∈ ℕ (running bucket index).  The lemmas in this
// section work with finite truncations of that infinite r-sum.
//
// `lemma_outer_partial_buckets(r)` proves
//      outer(r·n)  ≤  (Σ_{i<n} e^{−i/d}) · (Σ_{j<r} (e^{−n/d})^j · F(j))
// — truncating both sides at the running index < r.  Letting r → ∞ recovers
// the header's E2 → E1 step.
//
// The helpers (`lemma_outer_partial_bucket_helper`, `lemma_rej_weight_bucket_step`,
// `lemma_pow_exp_neg_scale`) take `r` as a *specific* bucket index — one rung
// of the induction in `lemma_outer_partial_buckets`.
// ----------------------------------------------------------------------------

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

/// Trigger-aid: instantiate the forall e(k) ≥ 0 at a specific k.
proof fn lemma_e_nonneg_at(e: spec_fn(nat) -> real, k: nat)
    requires forall |j: nat| (#[trigger] e(j)) >= 0real,
    ensures e(k) >= 0real,
{}

/// Σ_{k<K} e^{−k/d} · F(k/n) is nondecreasing in K when F ≥ 0.
proof fn lemma_outer_partial_monotone(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, k1: nat, k2: nat,
)
    requires
        denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        k1 <= k2,
    ensures
        outer_partial(numer, denom, e, k1) <= outer_partial(numer, denom, e, k2),
    decreases k2,
{
    if k2 > k1 {
        lemma_outer_partial_monotone(numer, denom, e, k1, (k2 - 1) as nat);
        let kp = (k2 - 1) as nat;
        let term = rej_weight(denom, kp) * e(kp / numer);
        assert(outer_partial(numer, denom, e, k2)
            == outer_partial(numer, denom, e, kp) + term);
        // term ≥ 0 since e^{−kp/d} > 0 and F ≥ 0
        assert(0real < rej_weight(denom, kp)) by {
            assert(kp as real / denom as real >= 0real) by(nonlinear_arith)
                requires denom > 0;
            axiom_exp_neg_range(kp as real / denom as real);
        };
        let kpn = (kp / numer) as nat;
        lemma_e_nonneg_at(e, kpn);
        assert(term >= 0real) by(nonlinear_arith)
            requires rej_weight(denom, kp) > 0real, e(kpn) >= 0real,
                term == rej_weight(denom, kp) * e(kpn);
    }
}

/// Bucket lemma: at offset R·n, summing the next i ≤ n terms gives
///   Σ_{k < R·n + i} e^{−k/d}·F(k/n)  −  Σ_{k < R·n} e^{−k/d}·F(k/n)
///     = (e^{−n/d})^R · (Σ_{j<i} e^{−j/d}) · F(R).
///
/// Within bucket r = R, k = R·n + j with j < n, so (R·n + j)/n = R and
/// e^{−(R·n + j)/d} = (e^{−n/d})^R · e^{−j/d}.  At i = n this gives the
/// "complete bucket" identity used in the bucket bound.
proof fn lemma_outer_partial_bucket_helper(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, r: nat, i: nat,
)
    requires numer > 0, denom > 0, i <= numer,
    ensures
        outer_partial(numer, denom, e, r * numer + i)
            == outer_partial(numer, denom, e, r * numer)
                + pow(exp(-(numer as real / denom as real)), r)
                    * rej_weight_sum(denom, i) * e(r),
    decreases i,
{
    if i == 0 {
        assert(r * numer + 0 == r * numer);
        assert(rej_weight_sum(denom, 0nat) == 0real);
        let pwr = pow(exp(-(numer as real / denom as real)), r);
        assert(pwr * 0real * e(r) == 0real) by(nonlinear_arith);
    } else {
        let j = (i - 1) as nat;
        lemma_outer_partial_bucket_helper(numer, denom, e, r, j);
        // outer-sum step: at index r·n + j.
        assert(r * numer + i == (r * numer + j) + 1) by(nonlinear_arith)
            requires i == j + 1;
        assert(outer_partial(numer, denom, e, r * numer + i)
            == outer_partial(numer, denom, e, r * numer + j)
                + rej_weight(denom, r * numer + j) * e((r * numer + j) / numer));
        // Divisibility: (r·n + j) / n == r since 0 ≤ j < n.
        assert((r * numer + j) / numer == r) by(nonlinear_arith)
            requires numer > 0, 0 <= j < numer;
        // Weight identity: e^{−(r·n + j)/d} = (e^{−n/d})^{r} · e^{−j/d}.
        lemma_rej_weight_bucket_step(numer, denom, r, j);
        // partial-row-sum step
        assert(rej_weight_sum(denom, i)
            == rej_weight_sum(denom, j) + rej_weight(denom, j));
        let pwr = pow(exp(-(numer as real / denom as real)), r);
        let wj = rej_weight(denom, j);
        let er = e(r);
        assert(outer_partial(numer, denom, e, r * numer + i)
            == outer_partial(numer, denom, e, r * numer)
                + pwr * rej_weight_sum(denom, i) * er)
            by(nonlinear_arith)
            requires
                outer_partial(numer, denom, e, r * numer + i)
                    == outer_partial(numer, denom, e, r * numer + j) + (pwr * wj) * er,
                outer_partial(numer, denom, e, r * numer + j)
                    == outer_partial(numer, denom, e, r * numer) + pwr * rej_weight_sum(denom, j) * er,
                rej_weight_sum(denom, i) == rej_weight_sum(denom, j) + wj;
    }
}

/// Auxiliary: e^{−(r·n + j)/d} = (e^{−n/d})^{r} · e^{−j/d}.
proof fn lemma_rej_weight_bucket_step(numer: nat, denom: nat, r: nat, j: nat)
    requires numer > 0, denom > 0,
    ensures
        rej_weight(denom, r * numer + j)
            == pow(exp(-(numer as real / denom as real)), r) * rej_weight(denom, j),
{
    // e^{−(r·n + j)/d}
    //   = e^{−(r·n)/d − j/d}
    //   = e^{−(r·n)/d} · e^{−j/d}
    //   = (e^{−n/d})^{r} · e^{−j/d}
    let a = (r * numer) as real / denom as real;
    let b = j as real / denom as real;
    assert(a >= 0real) by(nonlinear_arith)
        requires denom > 0, a == (r * numer) as real / denom as real;
    assert(b >= 0real) by(nonlinear_arith)
        requires denom > 0, b == j as real / denom as real;
    axiom_exp_add(a, b);
    assert((r * numer + j) as real / denom as real == a + b) by(nonlinear_arith)
        requires denom > 0, a == (r * numer) as real / denom as real,
            b == j as real / denom as real;
    // exp(-(r * numer)/d) = pow(e^{-numer/d}, r)
    lemma_pow_exp_neg_scale(numer, denom, r);
}

/// e^{−(r·n)/d} = (e^{−n/d})^{r}.
proof fn lemma_pow_exp_neg_scale(numer: nat, denom: nat, r: nat)
    requires denom > 0,
    ensures
        exp(-((r * numer) as real / denom as real))
            == pow(exp(-(numer as real / denom as real)), r),
    decreases r,
{
    if r == 0 {
        axiom_exp_zero();
        assert(0 * numer == 0);
        assert((0nat as real) / (denom as real) == 0real) by(nonlinear_arith)
            requires denom > 0;
        assert(pow(exp(-(numer as real / denom as real)), 0nat) == 1real);
    } else {
        let k = (r - 1) as nat;
        lemma_pow_exp_neg_scale(numer, denom, k);
        // r·n = k·n + n
        assert(r * numer == k * numer + numer) by(nonlinear_arith)
            requires r == k + 1;
        // e^{−(r·n)/d} = e^{−(k·n + n)/d} = e^{−(k·n)/d} · e^{−n/d}
        let a = (k * numer) as real / denom as real;
        let b = numer as real / denom as real;
        assert(a >= 0real) by(nonlinear_arith) requires denom > 0, a == (k * numer) as real / denom as real;
        assert(b >= 0real) by(nonlinear_arith) requires denom > 0, b == numer as real / denom as real;
        axiom_exp_add(a, b);
        assert((r * numer) as real / denom as real == a + b) by(nonlinear_arith)
            requires denom > 0, a == (k * numer) as real / denom as real,
                b == numer as real / denom as real,
                r * numer == k * numer + numer;
        // pow step: p^{r} = p^k · p
        assert(pow(exp(-(numer as real / denom as real)), r)
            == exp(-(numer as real / denom as real)) * pow(exp(-(numer as real / denom as real)), k));
        // Combine
        assert(exp(-((r * numer) as real / denom as real))
            == pow(exp(-(numer as real / denom as real)), r))
            by(nonlinear_arith)
            requires
                exp(-((r * numer) as real / denom as real)) == exp(-a) * exp(-b),
                exp(-a) == pow(exp(-(numer as real / denom as real)), k),
                exp(-b) == exp(-(numer as real / denom as real)),
                pow(exp(-(numer as real / denom as real)), r)
                    == exp(-(numer as real / denom as real)) * pow(exp(-(numer as real / denom as real)), k);
    }
}

/// Bucket bound:
///   Σ_{k < R·n} e^{−k/d} · F(k/n)  ≤  (Σ_{i<n} e^{−i/d}) · Σ_{r<R} (e^{−n/d})^r · F(r).
///
/// (Equality, in fact, for "complete buckets" since each bucket r contributes
/// exactly (e^{−n/d})^r · (Σ_{i<n} e^{−i/d}) · F(r).  We state ≤ since that's
/// what we need downstream and to keep the assertion small.)
pub proof fn lemma_outer_partial_buckets(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, r: nat,
)
    requires
        numer > 0, denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
    ensures
        outer_partial(numer, denom, e, r * numer)
            <= rej_weight_sum(denom, numer)
                * pow_partial(exp(-(numer as real / denom as real)), e, r),
    decreases r,
{
    if r == 0 {
        assert(0 * numer == 0);
        assert(pow_partial(exp(-(numer as real / denom as real)), e, 0nat) == 0real);
        assert(rej_weight_sum(denom, numer) * 0real == 0real) by(nonlinear_arith);
    } else {
        let k = (r - 1) as nat;
        lemma_outer_partial_buckets(numer, denom, e, k);
        lemma_outer_partial_bucket_helper(numer, denom, e, k, numer);
        // outer-sum at k·n + n  =  outer-sum at k·n  +  p^k · (Σ_{i<n} e^{−i/d}) · F(k)
        // outer-sum at r·n  =  outer-sum at k·n + n
        assert(r * numer == k * numer + numer) by(nonlinear_arith)
            requires r == k + 1;
        // pow_partial step
        let p = exp(-(numer as real / denom as real));
        let s = rej_weight_sum(denom, numer);
        let pwr_k = pow(p, k);
        let ek = e(k);
        assert(pow_partial(p, e, r)
            == pow_partial(p, e, k) + pwr_k * ek);
        // Combine
        assert(outer_partial(numer, denom, e, r * numer)
            <= s * pow_partial(p, e, r))
            by(nonlinear_arith)
            requires
                outer_partial(numer, denom, e, r * numer)
                    == outer_partial(numer, denom, e, k * numer) + pwr_k * s * ek,
                outer_partial(numer, denom, e, k * numer) <= s * pow_partial(p, e, k),
                pow_partial(p, e, r) == pow_partial(p, e, k) + pwr_k * ek;
    }
}

// ----------------------------------------------------------------------------
// pow_partial bound (E1 numerics) and key closed-form identity
// ----------------------------------------------------------------------------

/// Σ_{r<R} p^r · F(r)  ≤  dist_bound / (1 − p),
/// extracted from geo_exp_series_bounded_by (which has the (1 − p) factor).
proof fn lemma_pow_partial_bound(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, r_max: nat,
)
    requires
        numer > 0, denom > 1,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(
            exp(-(numer as real / denom as real)), e, dist_bound,
        ),
    ensures
        pow_partial(exp(-(numer as real / denom as real)), e, r_max)
            * (1real - exp(-(numer as real / denom as real)))
            <= dist_bound,
{
    let p = exp(-(numer as real / denom as real));
    // Σ_{i<r_max} p^i · (1−p) · e(i) = (1−p) · Σ_{i<r_max} p^i · e(i)
    lemma_geo_exp_partial_sum_eq_pow_partial(p, e, r_max);
    // ... and the LHS is bounded by dist_bound (precondition).
    assert(dist_bound >= geo_exp_partial_sum(p, e, r_max));
}

/// Σ_{i<n} p^i · (1 − p) · e(i)  ==  (Σ_{i<n} p^i · e(i)) · (1 − p).
proof fn lemma_geo_exp_partial_sum_eq_pow_partial(
    p: real, e: spec_fn(nat) -> real, n: nat,
)
    ensures geo_exp_partial_sum(p, e, n) == pow_partial(p, e, n) * (1real - p),
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_geo_exp_partial_sum_eq_pow_partial(p, e, k);
        // Σ_{i<n} p^i·(1−p)·e(i) = Σ_{i<k} p^i·(1−p)·e(i) + p^k·(1−p)·e(k)
        // Σ_{i<n} p^i·e(i)       = Σ_{i<k} p^i·e(i)       + p^k·e(k)
        assert(geo_exp_partial_sum(p, e, n)
            == geo_exp_partial_sum(p, e, k) + pow(p, k) * (1real - p) * e(k));
        assert(pow_partial(p, e, n) == pow_partial(p, e, k) + pow(p, k) * e(k));
        let pwr = pow(p, k);
        let ek = e(k);
        assert(geo_exp_partial_sum(p, e, n) == pow_partial(p, e, n) * (1real - p))
            by(nonlinear_arith)
            requires
                geo_exp_partial_sum(p, e, n)
                    == geo_exp_partial_sum(p, e, k) + pwr * (1real - p) * ek,
                geo_exp_partial_sum(p, e, k) == pow_partial(p, e, k) * (1real - p),
                pow_partial(p, e, n) == pow_partial(p, e, k) + pwr * ek;
    }
}

/// Key identity:
///   (1 − e^{−1}) · (Σ_{i<n} e^{−i/d})  ==  N · (1 − e^{−n/d}).
///
/// From the two telescoping identities
///   (Σ_{i<n} e^{−i/d}) · (1 − e^{−1/d}) = 1 − e^{−n/d}
///   N                  · (1 − e^{−1/d}) = 1 − e^{−1}
/// multiplied crosswise.
proof fn lemma_key_identity(n: nat, d: nat)
    requires d > 0,
    ensures
        (1real - exp(-1real)) * rej_weight_sum(d, n)
            == rej_norm_const(d) * (1real - exp(-(n as real / d as real))),
{
    lemma_rej_weight_sum_telescope(d, n);
    // (Σ_{i<n} e^{−i/d}) · (1 − e^{−1/d}) = 1 − e^{−n/d}
    lemma_norm_const_identity(d);
    // N · (1 − e^{−1/d}) = 1 − e^{−1}
    let r1 = rej_weight(d, 1);
    let rn = rej_weight(d, n);
    let s = rej_weight_sum(d, n);
    let nc = rej_norm_const(d);
    // (1 − e^{−1}) · s = N · (1 − e^{−1/d}) · s = N · (1 − e^{−n/d})
    assert(rn == exp(-(n as real / d as real)));
    assert((1real - exp(-1real)) * s == nc * (1real - rn))
        by(nonlinear_arith)
        requires
            s * (1real - r1) == 1real - rn,
            nc * (1real - r1) == 1real - exp(-1real);
}

// ----------------------------------------------------------------------------
// Partial weighted-average bound (combine bijection + bucket + identity)
// ----------------------------------------------------------------------------

/// Partial-sum form of the weighted-average bound:
///   Σ_{u<d} e^{−u/d} · Σ_{v<m} (e^{−1})^v · (1 − e^{−1}) · F((u + d·v)/n)
///     ≤ N · dist_bound,    for any m.
///
/// Equivalently: (1 − e^{−1}) · joint(m, d) ≤ N · dist_bound, where the
/// inner factor (1 − e^{−1}) · inner(u, m) is precisely the m-th partial
/// sum of the inner Geom(1 − e^{−1}) series at residue u.
pub proof fn lemma_partial_weighted_avg_bound(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, m: nat,
)
    requires
        numer > 0, denom > 1,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        (1real - exp(-1real)) * joint_helper(numer, denom, e, m, denom)
            <= rej_norm_const(denom) * dist_bound,
{
    let p = exp(-(numer as real / denom as real));
    let s = rej_weight_sum(denom, numer);
    let nc = rej_norm_const(denom);
    let pp = pow_partial(p, e, denom * m);
    let op_dm = outer_partial(numer, denom, e, denom * m);
    let op_full = outer_partial(numer, denom, e, denom * m * numer);
    let jh = joint_helper(numer, denom, e, m, denom);
    let r1me = 1real - exp(-1real);
    let r1mp = 1real - p;

    // The five identities the final nonlinear_arith step composes:
    //   jh == op_dm                                    (Euclidean bijection)
    //   op_dm <= op_full                               (monotonicity)
    //   op_full <= s · pp                              (bucket bound)
    //   pp · r1mp <= dist_bound                        (pow-partial bound)
    //   r1me · s == nc · r1mp                          (key identity)
    lemma_euclidean_bijection_partial(numer, denom, e, m);
    assert(denom * m <= denom * m * numer) by(nonlinear_arith) requires numer >= 1;
    lemma_outer_partial_monotone(numer, denom, e, denom * m, denom * m * numer);
    assert(denom * m * numer == (denom * m) * numer) by(nonlinear_arith);
    lemma_outer_partial_buckets(numer, denom, e, denom * m);
    lemma_pow_partial_bound(numer, denom, e, dist_bound, denom * m);
    lemma_key_identity(numer, denom);

    // Sign facts:  1 − p > 0 (since p < 1),  1 − e^{−1} ≥ 0,  s ≥ 0,  nc ≥ 0.
    assert(0real < numer as real / denom as real) by(nonlinear_arith)
        requires numer > 0, denom > 1;
    axiom_exp_neg_strict(numer as real / denom as real);
    axiom_exp_neg_range(1real);
    crate::discrete_laplace::exp_rejection::lemma_rej_weight_sum_bounds(denom, numer);
    crate::discrete_laplace::exp_rejection::lemma_rej_weight_sum_bounds(denom, denom);

    assert(r1me * jh <= nc * dist_bound) by(nonlinear_arith)
        requires
            jh == op_dm,
            op_dm <= op_full,
            op_full <= s * pp,
            pp * r1mp <= dist_bound,
            r1me * s == nc * r1mp,
            r1me >= 0real, r1mp > 0real, dist_bound >= 0real, s >= 0real, nc >= 0real;
}

// ----------------------------------------------------------------------------
// Per-residue bound, monotone convergence, and properties of f
// ----------------------------------------------------------------------------

/// Σ_{v<m} (e^{−1})^v · F((u + d·v)/n)  ≥  0.
proof fn lemma_inner_at_u_nonneg(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real, m: nat,
)
    requires
        numer > 0, denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
    ensures inner_at_u(numer, denom, u, e, m) >= 0real,
    decreases m,
{
    if m > 0 {
        let j = (m - 1) as nat;
        lemma_inner_at_u_nonneg(numer, denom, u, e, j);
        let term = pow(exp(-1real), j) * e((u + denom * j) / numer);
        assert(inner_at_u(numer, denom, u, e, m)
            == inner_at_u(numer, denom, u, e, j) + term);
        axiom_exp_neg_range(1real);
        lemma_pow_nonneg(exp(-1real), j);
        let k_nat = (u + denom * j) / numer;
        lemma_e_nonneg_at(e, k_nat);
        assert(term >= 0real) by(nonlinear_arith)
            requires
                pow(exp(-1real), j) >= 0real,
                e(k_nat) >= 0real,
                term == pow(exp(-1real), j) * e(k_nat);
    }
}

/// Σ_{u<u_max} e^{−u/d} · Σ_{v<m} (e^{−1})^v · F((u + d·v)/n)  ≥  0.
proof fn lemma_joint_helper_nonneg(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat, u_max: nat,
)
    requires
        numer > 0, denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
    ensures joint_helper(numer, denom, e, m, u_max) >= 0real,
    decreases u_max,
{
    if u_max > 0 {
        let k = (u_max - 1) as nat;
        lemma_joint_helper_nonneg(numer, denom, e, m, k);
        lemma_inner_at_u_nonneg(numer, denom, k, e, m);
        let term = rej_weight(denom, k) * inner_at_u(numer, denom, k, e, m);
        assert(joint_helper(numer, denom, e, m, u_max)
            == joint_helper(numer, denom, e, m, k) + term);
        assert(0real < rej_weight(denom, k)) by {
            assert(k as real / denom as real >= 0real) by(nonlinear_arith)
                requires denom > 0;
            axiom_exp_neg_range(k as real / denom as real);
        };
        assert(term >= 0real) by(nonlinear_arith)
            requires
                rej_weight(denom, k) > 0real,
                inner_at_u(numer, denom, k, e, m) >= 0real,
                term == rej_weight(denom, k) * inner_at_u(numer, denom, k, e, m);
    }
}

/// For u < u_max:  joint(m, u_max) ≥ e^{−u/d} · inner(u, m).
proof fn lemma_joint_helper_term_at_u(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, m: nat, u: nat, u_max: nat,
)
    requires
        numer > 0, denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        u < u_max,
    ensures
        joint_helper(numer, denom, e, m, u_max)
            >= rej_weight(denom, u) * inner_at_u(numer, denom, u, e, m),
    decreases u_max,
{
    let k = (u_max - 1) as nat;
    if u == k {
        lemma_joint_helper_nonneg(numer, denom, e, m, k);
        let term = rej_weight(denom, u) * inner_at_u(numer, denom, u, e, m);
        assert(joint_helper(numer, denom, e, m, u_max)
            == joint_helper(numer, denom, e, m, k) + term);
        assert(joint_helper(numer, denom, e, m, u_max) >= term)
            by(nonlinear_arith)
            requires
                joint_helper(numer, denom, e, m, u_max)
                    == joint_helper(numer, denom, e, m, k) + term,
                joint_helper(numer, denom, e, m, k) >= 0real;
    } else {
        lemma_joint_helper_term_at_u(numer, denom, e, m, u, k);
        lemma_inner_at_u_nonneg(numer, denom, k, e, m);
        let term_k = rej_weight(denom, k) * inner_at_u(numer, denom, k, e, m);
        assert(0real < rej_weight(denom, k)) by {
            assert(k as real / denom as real >= 0real) by(nonlinear_arith)
                requires denom > 0;
            axiom_exp_neg_range(k as real / denom as real);
        };
        assert(term_k >= 0real) by(nonlinear_arith)
            requires
                rej_weight(denom, k) > 0real,
                inner_at_u(numer, denom, k, e, m) >= 0real,
                term_k == rej_weight(denom, k) * inner_at_u(numer, denom, k, e, m);
        assert(joint_helper(numer, denom, e, m, u_max)
            == joint_helper(numer, denom, e, m, k) + term_k);
    }
}

/// Σ_{v<m} (e^{−1})^v · (1 − e^{−1}) · g(u, v)  ==  (1 − e^{−1}) · inner(u, m).
proof fn lemma_geo_exp_partial_eq_inner(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real, m: nat,
)
    ensures
        geo_exp_partial_sum(exp(-1real), g(numer, denom, u, e), m)
            == (1real - exp(-1real)) * inner_at_u(numer, denom, u, e, m),
    decreases m,
{
    if m > 0 {
        let j = (m - 1) as nat;
        lemma_geo_exp_partial_eq_inner(numer, denom, u, e, j);
        let p1 = exp(-1real);
        let r1mp = 1real - p1;
        let gv = (g(numer, denom, u, e))(j);
        let ev = e((u + denom * j) / numer);
        assert(gv == ev) by {
            assert((j * denom + u) / numer == (u + denom * j) / numer) by(nonlinear_arith);
        };
        let pwr = pow(p1, j);
        assert(geo_exp_partial_sum(p1, g(numer, denom, u, e), m)
            == geo_exp_partial_sum(p1, g(numer, denom, u, e), j)
                + pwr * r1mp * gv);
        assert(inner_at_u(numer, denom, u, e, m)
            == inner_at_u(numer, denom, u, e, j) + pwr * ev);
        let geps_j = geo_exp_partial_sum(p1, g(numer, denom, u, e), j);
        let iau_j = inner_at_u(numer, denom, u, e, j);
        let iau_m = inner_at_u(numer, denom, u, e, m);
        let geps_m = geo_exp_partial_sum(p1, g(numer, denom, u, e), m);
        assert(geps_m == r1mp * iau_m) by(nonlinear_arith)
            requires
                geps_j == r1mp * iau_j,
                geps_m == geps_j + pwr * r1mp * gv,
                iau_m == iau_j + pwr * ev,
                gv == ev;
    }
}

/// Per-residue partial-sum bound:
///   e^{−u/d} · Σ_{v<m} (e^{−1})^v · (1 − e^{−1}) · g(u, v)  ≤  N · dist_bound.
proof fn lemma_inner_partial_sum_bounded(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real,
    u: nat, m: nat,
)
    requires
        numer > 0, denom > 1, u < denom as nat,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        rej_weight(denom, u)
            * geo_exp_partial_sum(exp(-1real), g(numer, denom, u, e), m)
            <= rej_norm_const(denom) * dist_bound,
{
    lemma_partial_weighted_avg_bound(numer, denom, e, dist_bound, m);
    lemma_joint_helper_term_at_u(numer, denom, e, m, u, denom);
    lemma_geo_exp_partial_eq_inner(numer, denom, u, e, m);

    let r1me = 1real - exp(-1real);
    let wu = rej_weight(denom, u);
    let nc = rej_norm_const(denom);
    let jh = joint_helper(numer, denom, e, m, denom);
    let iau = inner_at_u(numer, denom, u, e, m);
    let geps = geo_exp_partial_sum(exp(-1real), g(numer, denom, u, e), m);

    axiom_exp_neg_range(1real);
    // r1me >= 0
    assert(r1me >= 0real);
    // wu > 0
    assert(u as real / denom as real >= 0real) by(nonlinear_arith) requires denom > 0;
    axiom_exp_neg_range(u as real / denom as real);
    assert(wu > 0real);
    // iau >= 0
    lemma_inner_at_u_nonneg(numer, denom, u, e, m);

    // (1−e^{−1})·joint ≥ (1−e^{−1})·(e^{−u/d} · inner) = e^{−u/d} · ((1−e^{−1})·inner) = e^{−u/d} · geps
    // and (1−e^{−1})·joint ≤ N · dist_bound.  So e^{−u/d} · geps ≤ N · dist_bound.
    assert(wu * geps == wu * (r1me * iau)) by(nonlinear_arith)
        requires geps == r1me * iau;
    assert(wu * (r1me * iau) == r1me * (wu * iau)) by(nonlinear_arith);
    assert(r1me * (wu * iau) <= r1me * jh) by(nonlinear_arith)
        requires r1me >= 0real, jh >= wu * iau;
    assert(wu * geps <= nc * dist_bound) by(nonlinear_arith)
        requires
            wu * geps == r1me * (wu * iau),
            r1me * (wu * iau) <= r1me * jh,
            r1me * jh <= nc * dist_bound;
}


/// The inner Geom partial-sum sequence at u is nondecreasing.
proof fn lemma_geo_exp_partial_nondecreasing(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real,
)
    requires
        numer > 0, denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
    ensures
        is_nondecreasing(inner_partial_seq(numer, denom, u, e)),
{
    let p1 = exp(-1real);
    axiom_exp_neg_range(1real);
    assert forall |m: nat|
        #[trigger] seq_at(inner_partial_seq(numer, denom, u, e), m)
            <= seq_at(inner_partial_seq(numer, denom, u, e), m + 1) by {
        let gv = (g(numer, denom, u, e))(m);
        let pwr = pow(p1, m);
        lemma_pow_nonneg(p1, m);
        lemma_e_nonneg_at(e, (m * denom + u) / numer);
        assert(geo_exp_partial_sum(p1, g(numer, denom, u, e), m + 1)
            == geo_exp_partial_sum(p1, g(numer, denom, u, e), m) + pwr * (1real - p1) * gv);
        assert(pwr * (1real - p1) * gv >= 0real) by(nonlinear_arith)
            requires pwr >= 0real, 0real < p1, p1 <= 1real, gv >= 0real;
    };
}

/// Inner Geom(1 − e^{−1}) partial sums at residue u converge, for each u < d.
/// Combine monotone convergence + per-residue partial-sum bound.
proof fn lemma_inner_seq_converges(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, u: nat,
)
    requires
        numer > 0, denom > 1, u < denom as nat,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        converges(inner_partial_seq(numer, denom, u, e)),
{
    let seq = inner_partial_seq(numer, denom, u, e);
    lemma_geo_exp_partial_nondecreasing(numer, denom, u, e);
    let nc = rej_norm_const(denom);
    let wu = rej_weight(denom, u);
    assert(wu > 0real) by {
        assert(u as real / denom as real >= 0real) by(nonlinear_arith) requires denom > 0;
        axiom_exp_neg_range(u as real / denom as real);
    };
    let bound = nc * dist_bound / wu;
    assert(is_bounded_above(seq, bound)) by {
        assert forall |m: nat|
            #[trigger] seq_at(seq, m) <= bound by {
            lemma_inner_partial_sum_bounded(numer, denom, e, dist_bound, u, m);
            assert(seq_at(seq, m) <= bound) by(nonlinear_arith)
                requires
                    wu * seq_at(seq, m) <= nc * dist_bound,
                    wu > 0real,
                    bound == nc * dist_bound / wu;
        };
    };
    axiom_monotone_convergence(seq, bound);
}

/// f(u) is the limit of the inner partial sum sequence (for u < d).
proof fn lemma_f_is_limit(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, u: nat,
)
    requires
        numer > 0, denom > 1, u < denom as nat,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        converges_to(
            inner_partial_seq(numer, denom, u, e),
            f(numer, denom, u, e),
        ),
{
    lemma_inner_seq_converges(numer, denom, e, dist_bound, u);
}



/// Each partial sum of the inner Geom series at u is ≥ 0 (nondecreasing,
/// nonneg starting value).
proof fn lemma_inner_partial_nonneg_at(
    numer: nat, denom: nat, u: nat, e: spec_fn(nat) -> real, m: nat,
)
    requires
        numer > 0, denom > 0,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
    ensures
        geo_exp_partial_sum(exp(-1real), g(numer, denom, u, e), m) >= 0real,
    decreases m,
{
    if m > 0 {
        let j = (m - 1) as nat;
        lemma_inner_partial_nonneg_at(numer, denom, u, e, j);
        let p1 = exp(-1real);
        let gv = (g(numer, denom, u, e))(j);
        let pwr = pow(p1, j);
        axiom_exp_neg_range(1real);
        lemma_pow_nonneg(p1, j);
        let k_nat = (j * denom + u) / numer;
        lemma_e_nonneg_at(e, k_nat);
        assert(gv == e(k_nat));
        assert(geo_exp_partial_sum(p1, g(numer, denom, u, e), m)
            == geo_exp_partial_sum(p1, g(numer, denom, u, e), j) + pwr * (1real - p1) * gv);
        assert(pwr * (1real - p1) * gv >= 0real) by(nonlinear_arith)
            requires pwr >= 0real, 0real < p1, p1 <= 1real, gv >= 0real;
    }
}

// ============================================================================
// Limit pass-through: f(u) ≥ 0 and f(u) bounds inner Geom partial sums.
// ============================================================================

/// For each u < d, f(u) ≥ 0.
///
/// Proof: `lemma_f_is_limit` gives `converges_to(seq, f(u))`; partial sums
/// are nonneg (`lemma_inner_partial_nonneg_at`); apply `lemma_limit_ge_bound`.
#[verifier::spinoff_prover]
proof fn lemma_f_nonneg(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, u: nat,
)
    requires
        numer > 0, denom > 1, u < denom as nat,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        f(numer, denom, u, e) >= 0real,
{
    let seq = inner_partial_seq(numer, denom, u, e);
    let limit = f(numer, denom, u, e);
    lemma_f_is_limit(numer, denom, e, dist_bound, u);
    assert(is_bounded_below(seq, 0real)) by {
        assert forall |n: nat| #[trigger] seq_at(seq, n) >= 0real by {
            lemma_inner_partial_nonneg_at(numer, denom, u, e, n);
        };
    };
    lemma_limit_ge_bound(seq, limit, 0real);
}

/// For each u < d, f(u) is an upper bound for every inner Geom(1 − e^{−1})
/// partial sum with postcondition g(u, ·).
///
/// Proof: `lemma_f_is_limit` + `lemma_geo_exp_partial_nondecreasing` +
/// `lemma_monotone_limit_upper_bound` give `is_bounded_above(seq, f(u))`,
/// which is definitionally the goal.
#[verifier::spinoff_prover]
proof fn lemma_f_bounds_inner(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, u: nat,
)
    requires
        numer > 0, denom > 1, u < denom as nat,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        geo_exp_series_bounded_by(
            exp(-1real),
            g(numer, denom, u, e),
            f(numer, denom, u, e),
        ),
{
    let seq = inner_partial_seq(numer, denom, u, e);
    let limit = f(numer, denom, u, e);
    lemma_f_is_limit(numer, denom, e, dist_bound, u);
    lemma_geo_exp_partial_nondecreasing(numer, denom, u, e);
    lemma_monotone_limit_upper_bound(seq, limit);
    assert forall |n: nat|
        limit >= #[trigger] geo_exp_partial_sum(exp(-1real), g(numer, denom, u, e), n) by {
        assert(seq_at(seq, n) <= limit);
    };
}

// ============================================================================
// Weighted-average bound: dist_bound ≥ E_{u ~ rejection_dist}[ f(u) ].
// ============================================================================

/// For each u_max ≤ d, the weighted partial-sum sequence
///
///   W(u_max) := m ↦ (1 − e^{−1}) · joint(m, u_max)
///             = Σ_{u<u_max} e^{−u/d} · Σ_{v<m} (e^{−1})^v · (1 − e^{−1}) · g(u, v)
///
/// converges to
///   Σ_{u<u_max} e^{−u/d} · f(u).
///
/// Proof: induction on u_max.  The step uses `lemma_geo_exp_partial_eq_inner`
/// to bridge inner(u, m) and the inner Geom partial sum at u, then
/// `lemma_limit_scale` (scale by e^{−k/d}) and `lemma_limit_add` (sum of
/// converging sequences) to combine the IH with `lemma_f_is_limit`.
#[verifier::spinoff_prover]
proof fn lemma_weighted_joint_helper_converges(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real, u_max: nat,
)
    requires
        numer > 0, denom > 1, u_max <= denom as nat,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        converges_to(
            |m: nat| (1real - exp(-1real)) * joint_helper(numer, denom, e, m, u_max),
            rej_weighted_sum(denom as nat, |u: nat| f(numer, denom, u, e), u_max),
        ),
    decreases u_max,
{
    let r1me = 1real - exp(-1real);
    let target = |m: nat| r1me * joint_helper(numer, denom, e, m, u_max);
    let fF: spec_fn(nat) -> real = |u: nat| f(numer, denom, u, e);
    let target_limit = rej_weighted_sum(denom as nat, fF, u_max);

    if u_max == 0 {
        // joint(_, 0) ≡ 0 and Σ_{u<0}(·) = 0, so target ≡ 0 converges to 0.
        assert forall |epsilon: real| epsilon > 0real
            implies #[trigger] exists_close_suffix(target, 0real, epsilon) by {
            assert(suffix_is_close(target, 0real, epsilon, 0nat));
        };
    } else {
        let k = (u_max - 1) as nat;
        let tail = |m: nat| r1me * joint_helper(numer, denom, e, m, k);
        let tail_limit = rej_weighted_sum(denom as nat, fF, k);
        let inner = inner_partial_seq(numer, denom, k, e);
        let f_k = f(numer, denom, k, e);
        let wk = rej_weight(denom, k);
        let scaled = |n: nat| wk * seq_at(inner, n);
        let sum_seq = |n: nat| seq_at(tail, n) + seq_at(scaled, n);
        let sum_limit = tail_limit + wk * f_k;

        // IH + per-residue limit + scale + add → sum_seq converges to sum_limit.
        lemma_weighted_joint_helper_converges(numer, denom, e, dist_bound, k);
        lemma_f_is_limit(numer, denom, e, dist_bound, k);
        lemma_limit_scale(inner, f_k, wk);
        lemma_limit_add(tail, scaled, tail_limit, wk * f_k);

        // sum_limit = target_limit by the rej_weighted_sum recursion (fF(k) = f_k).
        assert(fF(k) == f_k);

        // Pointwise: target(m) = sum_seq(m), via
        //   target(m) = (1−e^{−1}) · [joint(m, k) + e^{−k/d}·inner(k, m)]
        //             = tail(m) + e^{−k/d} · (1−e^{−1}) · inner(k, m)
        //             = tail(m) + e^{−k/d} · geo_exp_partial_sum_at_k(m)
        //             = sum_seq(m).
        assert forall |m: nat| #[trigger] seq_at(sum_seq, m) == seq_at(target, m) by {
            lemma_geo_exp_partial_eq_inner(numer, denom, k, e, m);
            let iau = inner_at_u(numer, denom, k, e, m);
            assert(joint_helper(numer, denom, e, m, u_max)
                == joint_helper(numer, denom, e, m, k) + wk * iau);
            assert(seq_at(target, m) == seq_at(sum_seq, m)) by(nonlinear_arith)
                requires
                    seq_at(target, m)
                        == r1me * (joint_helper(numer, denom, e, m, k) + wk * iau),
                    seq_at(tail, m) == r1me * joint_helper(numer, denom, e, m, k),
                    seq_at(scaled, m) == wk * (r1me * iau),
                    seq_at(sum_seq, m) == seq_at(tail, m) + seq_at(scaled, m);
        };

        lemma_limit_pointwise_eq(sum_seq, target, sum_limit);
    }
}

/// Weighted-average bound: dist_bound ≥ E_{u ~ rejection_dist}[ f(u) ].
///
/// Proof: `lemma_weighted_joint_helper_converges` gives the limit of
/// (1 − e^{−1}) · joint(_, d) as Σ_{u<d} e^{−u/d} · f(u);
/// `lemma_partial_weighted_avg_bound` bounds every partial by N · dist_bound;
/// `lemma_limit_le_bound` passes the bound through to the limit, and
/// dividing by N > 0 (from `lemma_norm_const_identity`) finishes.
#[verifier::spinoff_prover]
proof fn lemma_weighted_avg_bound(
    numer: nat, denom: nat, e: spec_fn(nat) -> real, dist_bound: real,
)
    requires
        numer > 0, denom > 1,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        geo_exp_series_bounded_by(exp(-(numer as real / denom as real)), e, dist_bound),
    ensures
        dist_bound >= rej_weighted_avg(
            denom as nat,
            |u: nat| f(numer, denom, u, e),
        ),
{
    let r1me = 1real - exp(-1real);
    let nc = rej_norm_const(denom);
    let fF: spec_fn(nat) -> real = |u: nat| f(numer, denom, u, e);
    let w_seq = |m: nat| r1me * joint_helper(numer, denom, e, m, denom as nat);
    let wf = rej_weighted_sum(denom as nat, fF, denom as nat);
    let bound = nc * dist_bound;

    // w_seq → wf, each w_seq(m) ≤ bound, so wf ≤ bound.
    lemma_weighted_joint_helper_converges(numer, denom, e, dist_bound, denom as nat);
    assert(is_bounded_above(w_seq, bound)) by {
        assert forall |m: nat| #[trigger] seq_at(w_seq, m) <= bound by {
            lemma_partial_weighted_avg_bound(numer, denom, e, dist_bound, m);
        };
    };
    lemma_limit_le_bound(w_seq, wf, bound);

    // N > 0:  from N · (1 − e^{−1/d}) = 1 − e^{−1}, with both factors on the
    // right positive (since 1/d > 0 ⇒ e^{−1/d} < 1, and e^{−1} < 1).
    lemma_norm_const_identity(denom);
    assert(1nat as real / denom as real == 1real / denom as real) by(nonlinear_arith)
        requires denom > 0;
    assert(1real / denom as real > 0real) by(nonlinear_arith) requires denom > 1;
    axiom_exp_neg_strict(1real / denom as real);
    axiom_exp_neg_strict(1real);
    assert(nc > 0real) by(nonlinear_arith)
        requires
            nc * (1real - rej_weight(denom, 1)) == 1real - exp(-1real),
            rej_weight(denom, 1) < 1real,
            exp(-1real) < 1real;

    // rej_weighted_avg = wf / N ≤ dist_bound.
    assert(dist_bound >= rej_weighted_avg(denom as nat, fF)) by(nonlinear_arith)
        requires
            wf <= nc * dist_bound,
            nc > 0real,
            rej_weighted_avg(denom as nat, fF) == wf / nc;
}

// ============================================================================
// Fast sampler  (composes L(d) and slow Geom).
//
// The two limit-pass-through ingredients (formerly bundled in an axiom) are
// now called inline, each right before the call site that consumes them:
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
    numer_x: u64,
    denom_x: u64,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(dist_bound): Ghost<real>,
) -> (ret: (UBig, Tracked<ErrorCreditResource>))
    requires
        numer_x > 0, denom_x > 1,
        0real < p < 1real,
        p == exp(-(numer_x as real / denom_x as real)),
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        dist_bound >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: dist_bound }),
        geo_exp_series_bounded_by(p, e, dist_bound),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&ret.0)) }),
{
    // f packaged as a spec_fn, used as the postcondition handed to L(d).
    let ghost f_of_u: spec_fn(nat) -> real =
        |u: nat| f(numer_x as nat, denom_x as nat, u, e);

    // Ingredients needed for the L(d) call: f(u) ≥ 0 for all u, and
    // dist_bound ≥ E_{u ~ μ_{L(d)}}[f(u)].
    proof {
        // Nonneg for u < d via the per-residue limit lemma; for u ≥ d the
        // 0-default in `f` gives nonneg trivially.
        assert forall |u: nat| (#[trigger] f_of_u(u)) >= 0real by {
            if u < denom_x as nat {
                lemma_f_nonneg(numer_x as nat, denom_x as nat, e, dist_bound, u);
            } else {
                assert(f_of_u(u) == 0real);
            }
        };
        lemma_weighted_avg_bound(numer_x as nat, denom_x as nat, e, dist_bound);
    }

    // E5 step: L(d) call, handing f as postcondition with eps_avg = dist_bound.
    let (u, Tracked(u_credit)) = sample_exp_rejection(
        denom_x,
        Ghost(f_of_u),
        Tracked(input_credit),
        Ghost(dist_bound),
    );
    // Post: ↯(f(u))

    // E4 step: slow Geom call, handing g(u, ·) as postcondition.
    let ghost g_at_u = g(numer_x as nat, denom_x as nat, u as nat, e);
    let ghost f_at_u = f(numer_x as nat, denom_x as nat, u as nat, e);
    let ghost p1 = exp(-1real);

    proof {
        axiom_exp_neg_range(1real);
        axiom_exp_neg_strict(1real);
        // g(u, v) = e((v·d + u) / n) ≥ 0 since e ≥ 0 everywhere.
        assert forall |v: nat| (#[trigger] g_at_u(v)) >= 0real by {};
        // f(u) bounds every inner Geom partial sum at this specific u.
        //   f(u) ≥ Σ_{v<m} (e^{−1})^v (1 − e^{−1}) g(u, v)  ∀m
        lemma_f_bounds_inner(numer_x as nat, denom_x as nat, e, dist_bound, u as nat);
    }

    let (v, Tracked(v_credit)) = sample_geometric_exp_slow(
        1u64, 1u64, Ghost(p1), Ghost(g_at_u), Tracked(u_credit), Ghost(f_at_u),
    );
    // Post: ↯(g(u, v)) = ↯(e((v·d + u) / n))

    // Algorithmic step: z = u + d·v; return z / n.
    // Postcondition: e((v·d + u) / n) = e(result), so we get ↯(F(result)).
    let v_scaled = ubig_mul_u64(&v, denom_x);
    let sum = ubig_add_u64(v_scaled, u);
    let result = ubig_div_u64(sum, numer_x);
    proof {
        let vn = ubig_view(&v);
        assert(ubig_view(&v_scaled) == vn * denom_x as nat);
        assert(ubig_view(&sum) == vn * denom_x as nat + u as nat);
        assert(ubig_view(&result) == (vn * denom_x as nat + u as nat) / numer_x as nat);
    }
    (result, Tracked(v_credit))
}

} // verus!
 