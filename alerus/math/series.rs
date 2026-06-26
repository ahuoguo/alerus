//! Real Analysis: Limits, Sequences, and Series
//!
//! Partly follows the structure of Dafny-VMC's Math/Analysis library:
//!   https://github.com/dafny-lang/Dafny-VMC/tree/main/src/Math/Analysis

use vstd::prelude::*;

verus! {
#[cfg(verus_keep_ghost)]
use crate::math::pow::pow;

// ============================================================================
// Basic definitions: abs, dist, sequences
// ============================================================================

pub open spec fn abs(x: real) -> real {
    if x >= 0real { x } else { -x }
}

pub open spec fn dist(x: real, y: real) -> real {
    abs(x - y)
}

/// Trigger helper for sequence evaluation
// TODO: do you need this?
pub open spec fn seq_at(s: spec_fn(nat) -> real, n: nat) -> real {
    s(n)
}

/// Monotone non-decreasing: s(n) ≤ s(n+1) for all n
pub open spec fn is_nondecreasing(s: spec_fn(nat) -> real) -> bool {
    forall |n: nat| #[trigger] seq_at(s, n) <= seq_at(s, n + 1)
}

/// Monotone non-increasing: s(n) ≥ s(n+1) for all n
pub open spec fn is_nonincreasing(s: spec_fn(nat) -> real) -> bool {
    forall |n: nat| #[trigger] seq_at(s, n) >= seq_at(s, n + 1)
}

/// Bounded above: s(n) ≤ bound for all n
pub open spec fn is_bounded_above(s: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| #[trigger] seq_at(s, n) <= bound
}

/// Bounded below: s(n) ≥ bound for all n
pub open spec fn is_bounded_below(s: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| #[trigger] seq_at(s, n) >= bound
}


// ============================================================================
// Convergence (ε-N definition)
// ============================================================================

/// All terms from index start onward are within eps of limit
pub open spec fn suffix_is_close(s: spec_fn(nat) -> real, limit: real, eps: real, start: nat) -> bool {
    forall |n: nat| n >= start ==> dist(#[trigger] seq_at(s, n), limit) < eps
}

/// There exists a suffix within eps of limit
pub open spec fn exists_close_suffix(s: spec_fn(nat) -> real, limit: real, eps: real) -> bool {
    exists |start: nat| suffix_is_close(s, limit, eps, start)
}

/// ε-N convergence: s converges to limit
pub open spec fn converges_to(s: spec_fn(nat) -> real, limit: real) -> bool {
    forall |epsilon: real| epsilon > 0real ==> #[trigger] exists_close_suffix(s, limit, epsilon)
}

/// s converges to some limit
pub open spec fn converges(s: spec_fn(nat) -> real) -> bool {
    exists |limit: real| converges_to(s, limit)
}

// ============================================================================
// Partial sums and series
// ============================================================================

/// Partial sum: s(0) + s(1) + ... + s(n-1)
pub open spec fn partial_sum(s: spec_fn(nat) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { partial_sum(s, (n - 1) as nat) + s((n - 1) as nat) }
}

/// Named wrapper for the sequence of partial sums (avoids lambdas in triggers)
pub open spec fn partial_sum_seq(s: spec_fn(nat) -> real) -> spec_fn(nat) -> real {
    |n: nat| partial_sum(s, n)
}

/// Series s sums to sum: the partial sums converge to sum
pub open spec fn sums_to(s: spec_fn(nat) -> real, sum: real) -> bool {
    converges_to(partial_sum_seq(s), sum)
}

/// Series s is summable (partial sums converge)
pub open spec fn is_summable(s: spec_fn(nat) -> real) -> bool {
    exists |sum: real| sums_to(s, sum)
}

/// All partial sums bounded above
pub open spec fn partial_sums_bounded_by(s: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| bound >= #[trigger] partial_sum(s, n)
}

// ============================================================================
// Geometric series: Σ_{i=0}^∞ (1/2)^(i+1) · e(i)
//
// The weight (1/2)^(i+1) matches the geometric distribution PMF:
// outcome i has probability (1/2)^(i+1) (i tails then 1 heads).
// ============================================================================

/// The weighted summands: (1/2)^(i+1) · e(i)
pub open spec fn geo_summands(e: spec_fn(nat) -> real) -> spec_fn(nat) -> real {
    |i: nat| pow(0.5real, i + 1) * e(i)
}

/// Partial sum of the geometric series
pub open spec fn geo_partial_sum(e: spec_fn(nat) -> real, n: nat) -> real {
    partial_sum(geo_summands(e), n)
}

/// Bound on all finite partial sums of the geometric series
pub open spec fn geo_series_bounded_by(e: spec_fn(nat) -> real, bound: real) -> bool {
    partial_sums_bounded_by(geo_summands(e), bound)
}

/// Shifted sequence: e'(i) = e(i + 1)
pub open spec fn shift_e(e: spec_fn(nat) -> real) -> spec_fn(nat) -> real {
    |i: nat| e(i + 1)
}

// ============================================================================
// Arithmetic lemmas
// ============================================================================

#[verifier::nonlinear]
proof fn lemma_abs_triangle(a: real, b: real)
    ensures abs(a + b) <= abs(a) + abs(b),
{}

pub proof fn lemma_triangle_inequality(x: real, y: real, z: real)
    ensures dist(x, z) <= dist(x, y) + dist(y, z),
{
    lemma_abs_triangle(x - y, y - z);
}

#[verifier::nonlinear]
pub proof fn lemma_dist_pos(x: real, y: real)
    requires x != y,
    ensures dist(x, y) > 0real,
{}

#[verifier::nonlinear]
pub proof fn lemma_dist_symmetric(x: real, y: real)
    ensures dist(x, y) == dist(y, x),
{}

#[verifier::nonlinear]
pub proof fn lemma_pow_nonneg(x: real, n: nat)
    requires x >= 0real,
    ensures pow(x, n) >= 0real,
    decreases n,
{
    if n > 0 {
        lemma_pow_nonneg(x, (n - 1) as nat);
    }
}

// ============================================================================
// Convergence lemmas
// ============================================================================

/// Monotone convergence: a bounded non-decreasing sequence converges.
/// (Requires completeness of reals — axiomatized.)
#[verifier::external_body]
pub proof fn axiom_monotone_convergence(s: spec_fn(nat) -> real, bound: real)
    requires is_nondecreasing(s), is_bounded_above(s, bound),
    ensures converges(s),
{}

/// Monotone convergence for non-increasing bounded-below sequences.
/// Derived from the non-decreasing version by negation.
pub proof fn lemma_monotone_convergence_decreasing(s: spec_fn(nat) -> real, bound: real)
    requires is_nonincreasing(s), is_bounded_below(s, bound),
    ensures converges(s),
{
    let neg_s = |n: nat| -seq_at(s, n);
    assert(is_nondecreasing(neg_s)) by {
        assert forall |n: nat| #[trigger] seq_at(neg_s, n) <= seq_at(neg_s, n + 1) by {
            assert(seq_at(s, n) >= seq_at(s, n + 1));
        };
    };
    assert(is_bounded_above(neg_s, -bound)) by {
        assert forall |n: nat| #[trigger] seq_at(neg_s, n) <= -bound by {
            assert(seq_at(s, n) >= bound);
        };
    };
    axiom_monotone_convergence(neg_s, -bound);
    let neg_limit = choose |l: real| converges_to(neg_s, l);
    assert(converges_to(s, -neg_limit)) by {
        assert forall |epsilon: real| epsilon > 0real
            implies #[trigger] exists_close_suffix(s, -neg_limit, epsilon) by {
            assert(exists_close_suffix(neg_s, neg_limit, epsilon));
            let start = choose |start: nat| suffix_is_close(neg_s, neg_limit, epsilon, start);
            assert(suffix_is_close(s, -neg_limit, epsilon, start)) by {
                assert forall |n: nat| n >= start implies
                    dist(#[trigger] seq_at(s, n), -neg_limit) < epsilon by {
                    assert(dist(seq_at(neg_s, n), neg_limit) < epsilon);
                    assert(dist(seq_at(s, n), -neg_limit) == dist(seq_at(neg_s, n), neg_limit))
                        by(nonlinear_arith)
                        requires seq_at(neg_s, n) == -seq_at(s, n),
                            dist(seq_at(s, n), -neg_limit) == abs(seq_at(s, n) - (-neg_limit)),
                            dist(seq_at(neg_s, n), neg_limit) == abs(seq_at(neg_s, n) - neg_limit);
                };
            };
        };
    };
}

/// Limit uniqueness: s → L1 and s → L2 implies L1 = L2.
pub proof fn lemma_limit_unique(s: spec_fn(nat) -> real, limit1: real, limit2: real)
    requires converges_to(s, limit1), converges_to(s, limit2),
    ensures limit1 == limit2,
{
    if limit1 != limit2 {
        lemma_dist_pos(limit1, limit2);
        let d = dist(limit1, limit2);
        let half_d = d / 2real;
        assert(half_d > 0real) by(nonlinear_arith)
            requires d > 0real, half_d == d / 2real;
        assert(exists_close_suffix(s, limit1, half_d));
        assert(exists_close_suffix(s, limit2, half_d));
        let n1: nat = choose |start: nat| suffix_is_close(s, limit1, half_d, start);
        let n2: nat = choose |start: nat| suffix_is_close(s, limit2, half_d, start);
        let n: nat = if n1 >= n2 { n1 } else { n2 };
        assert(dist(seq_at(s, n), limit1) < half_d);
        assert(dist(seq_at(s, n), limit2) < half_d);
        lemma_triangle_inequality(limit1, s(n), limit2);
        lemma_dist_symmetric(limit1, s(n));
        assert(false) by(nonlinear_arith)
            requires d > 0real, half_d == d / 2real,
                d <= dist(limit1, s(n)) + dist(s(n), limit2),
                dist(limit1, s(n)) == dist(s(n), limit1),
                dist(s(n), limit1) < half_d, dist(s(n), limit2) < half_d;
    }
}

/// Non-decreasing transitivity: s(n) ≤ s(m) when n ≤ m.
pub proof fn lemma_nondecreasing_le(s: spec_fn(nat) -> real, n: nat, m: nat)
    requires is_nondecreasing(s), n <= m,
    ensures seq_at(s, n) <= seq_at(s, m),
    decreases m - n,
{
    if n < m {
        lemma_nondecreasing_le(s, n + 1, m);
        assert(seq_at(s, n) <= seq_at(s, n + 1));
    }
}

/// The limit of a non-decreasing convergent sequence is an upper bound.
pub proof fn lemma_monotone_limit_upper_bound(s: spec_fn(nat) -> real, limit: real)
    requires
        is_nondecreasing(s),
        converges_to(s, limit),
    ensures
        is_bounded_above(s, limit),
{
    assert forall |n: nat| #[trigger] seq_at(s, n) <= limit by {
        if seq_at(s, n) > limit {
            let eps = seq_at(s, n) - limit;
            assert(eps > 0real) by(nonlinear_arith)
                requires seq_at(s, n) > limit, eps == seq_at(s, n) - limit;
            assert(exists_close_suffix(s, limit, eps));
            let start = choose |start: nat| suffix_is_close(s, limit, eps, start);
            let m: nat = if n >= start { n } else { start };
            assert(dist(seq_at(s, m), limit) < eps);
            lemma_nondecreasing_le(s, n, m);
            assert(false) by(nonlinear_arith)
                requires
                    seq_at(s, n) <= seq_at(s, m),
                    dist(seq_at(s, m), limit) < eps,
                    dist(seq_at(s, m), limit) == abs(seq_at(s, m) - limit),
                    seq_at(s, n) > limit,
                    eps == seq_at(s, n) - limit;
        }
    };
}

/// Shifted sequence converges to the same limit.
pub proof fn lemma_limit_shift(s: spec_fn(nat) -> real, limit: real)
    requires converges_to(s, limit),
    ensures converges_to(|n: nat| seq_at(s, n + 1), limit),
{
    let shifted = |n: nat| seq_at(s, n + 1);
    assert forall |epsilon: real| epsilon > 0real
        implies #[trigger] exists_close_suffix(shifted, limit, epsilon) by {
        assert(exists_close_suffix(s, limit, epsilon));
        let start = choose |start: nat| suffix_is_close(s, limit, epsilon, start);
        assert(suffix_is_close(shifted, limit, epsilon, start)) by {
            assert forall |n: nat| n >= start implies
                dist(#[trigger] seq_at(shifted, n), limit) < epsilon by {
                assert(n + 1 >= start);
                assert(dist(seq_at(s, n + 1), limit) < epsilon);
            };
        };
    };
}

/// If s1 → L1 and s2 → L2 then (s1 + s2)/2 → (L1 + L2)/2.
pub proof fn lemma_limit_average(
    s1: spec_fn(nat) -> real, s2: spec_fn(nat) -> real, l1: real, l2: real,
)
    requires converges_to(s1, l1), converges_to(s2, l2),
    ensures converges_to(|n: nat| (seq_at(s1, n) + seq_at(s2, n)) / 2real, (l1 + l2) / 2real),
{
    let avg = |n: nat| (seq_at(s1, n) + seq_at(s2, n)) / 2real;
    let l_avg = (l1 + l2) / 2real;
    assert forall |epsilon: real| epsilon > 0real
        implies #[trigger] exists_close_suffix(avg, l_avg, epsilon) by {
        assert(exists_close_suffix(s1, l1, epsilon));
        assert(exists_close_suffix(s2, l2, epsilon));
        let n1 = choose |start: nat| suffix_is_close(s1, l1, epsilon, start);
        let n2 = choose |start: nat| suffix_is_close(s2, l2, epsilon, start);
        let start: nat = if n1 >= n2 { n1 } else { n2 };
        assert(suffix_is_close(avg, l_avg, epsilon, start)) by {
            assert forall |n: nat| n >= start implies
                dist(#[trigger] seq_at(avg, n), l_avg) < epsilon by {
                lemma_abs_triangle(seq_at(s1, n) - l1, seq_at(s2, n) - l2);
                assert(dist(seq_at(avg, n), l_avg) < epsilon) by(nonlinear_arith)
                    requires abs(seq_at(s1, n) - l1) < epsilon,
                        abs(seq_at(s2, n) - l2) < epsilon,
                        abs((seq_at(s1, n) - l1) + (seq_at(s2, n) - l2))
                            <= abs(seq_at(s1, n) - l1) + abs(seq_at(s2, n) - l2),
                        seq_at(avg, n) == (seq_at(s1, n) + seq_at(s2, n)) / 2real,
                        l_avg == (l1 + l2) / 2real,
                        dist(seq_at(avg, n), l_avg) == abs(seq_at(avg, n) - l_avg),
                        dist(seq_at(s1, n), l1) == abs(seq_at(s1, n) - l1),
                        dist(seq_at(s2, n), l2) == abs(seq_at(s2, n) - l2);
            };
        };
    };
}

/// If s1 → L1 and s2 → L2 then s1 + s2 → L1 + L2.
pub proof fn lemma_limit_add(
    s1: spec_fn(nat) -> real, s2: spec_fn(nat) -> real, l1: real, l2: real,
)
    requires converges_to(s1, l1), converges_to(s2, l2),
    ensures converges_to(|n: nat| seq_at(s1, n) + seq_at(s2, n), l1 + l2),
{
    let sum = |n: nat| seq_at(s1, n) + seq_at(s2, n);
    let l_sum = l1 + l2;
    assert forall |epsilon: real| epsilon > 0real
        implies #[trigger] exists_close_suffix(sum, l_sum, epsilon) by {
        let half: real = epsilon / 2real;
        assert(half > 0real) by(nonlinear_arith) requires epsilon > 0real, half == epsilon / 2real;
        assert(exists_close_suffix(s1, l1, half));
        assert(exists_close_suffix(s2, l2, half));
        let n1 = choose |start: nat| suffix_is_close(s1, l1, half, start);
        let n2 = choose |start: nat| suffix_is_close(s2, l2, half, start);
        let start: nat = if n1 >= n2 { n1 } else { n2 };
        assert(suffix_is_close(sum, l_sum, epsilon, start)) by {
            assert forall |n: nat| n >= start implies
                dist(#[trigger] seq_at(sum, n), l_sum) < epsilon by {
                assert(n >= n1);
                assert(n >= n2);
                assert(dist(seq_at(s1, n), l1) < half);
                assert(dist(seq_at(s2, n), l2) < half);
                lemma_abs_triangle(seq_at(s1, n) - l1, seq_at(s2, n) - l2);
                assert(dist(seq_at(sum, n), l_sum) < epsilon) by(nonlinear_arith)
                    requires abs(seq_at(s1, n) - l1) < half,
                        abs(seq_at(s2, n) - l2) < half,
                        abs((seq_at(s1, n) - l1) + (seq_at(s2, n) - l2))
                            <= abs(seq_at(s1, n) - l1) + abs(seq_at(s2, n) - l2),
                        seq_at(sum, n) == seq_at(s1, n) + seq_at(s2, n),
                        l_sum == l1 + l2,
                        dist(seq_at(sum, n), l_sum) == abs(seq_at(sum, n) - l_sum),
                        half == epsilon / 2real;
            };
        };
    };
}

/// If s → L and c is any real, then c · s → c · L.
pub proof fn lemma_limit_scale(s: spec_fn(nat) -> real, l: real, c: real)
    requires converges_to(s, l),
    ensures converges_to(|n: nat| c * seq_at(s, n), c * l),
{
    let scaled = |n: nat| c * seq_at(s, n);
    let l_scaled = c * l;
    assert forall |epsilon: real| epsilon > 0real
        implies #[trigger] exists_close_suffix(scaled, l_scaled, epsilon) by {
        // Pick δ = ε / (|c| + 1) > 0 so we don't need a case split on c = 0.
        let abs_c_plus_one: real = abs(c) + 1real;
        assert(abs_c_plus_one > 0real) by(nonlinear_arith)
            requires abs_c_plus_one == abs(c) + 1real, abs(c) >= 0real;
        let delta: real = epsilon / abs_c_plus_one;
        assert(delta > 0real) by(nonlinear_arith)
            requires epsilon > 0real, abs_c_plus_one > 0real,
                delta == epsilon / abs_c_plus_one;
        assert(exists_close_suffix(s, l, delta));
        let start = choose |start: nat| suffix_is_close(s, l, delta, start);
        assert(suffix_is_close(scaled, l_scaled, epsilon, start)) by {
            assert forall |n: nat| n >= start implies
                dist(#[trigger] seq_at(scaled, n), l_scaled) < epsilon by {
                assert(dist(seq_at(s, n), l) < delta);
                // |c · s(n) − c · L| = |c| · |s(n) − L|.
                assert(seq_at(scaled, n) - l_scaled == c * (seq_at(s, n) - l))
                    by(nonlinear_arith)
                    requires seq_at(scaled, n) == c * seq_at(s, n),
                        l_scaled == c * l;
                assert(abs(c * (seq_at(s, n) - l)) == abs(c) * abs(seq_at(s, n) - l))
                    by(nonlinear_arith);
                assert(dist(seq_at(scaled, n), l_scaled) < epsilon) by(nonlinear_arith)
                    requires
                        seq_at(scaled, n) - l_scaled == c * (seq_at(s, n) - l),
                        abs(c * (seq_at(s, n) - l)) == abs(c) * abs(seq_at(s, n) - l),
                        dist(seq_at(scaled, n), l_scaled)
                            == abs(seq_at(scaled, n) - l_scaled),
                        dist(seq_at(s, n), l) == abs(seq_at(s, n) - l),
                        abs(seq_at(s, n) - l) < delta,
                        delta == epsilon / abs_c_plus_one,
                        abs_c_plus_one == abs(c) + 1real,
                        abs(c) >= 0real,
                        epsilon > 0real;
            };
        };
    };
}

/// Limit of a sequence bounded above by B is at most B.
pub proof fn lemma_limit_le_bound(s: spec_fn(nat) -> real, limit: real, bound: real)
    requires converges_to(s, limit), is_bounded_above(s, bound),
    ensures limit <= bound,
{
    if limit > bound {
        let eps = limit - bound;
        assert(eps > 0real) by(nonlinear_arith) requires limit > bound, eps == limit - bound;
        assert(exists_close_suffix(s, limit, eps));
        let start = choose |start: nat| suffix_is_close(s, limit, eps, start);
        assert(dist(seq_at(s, start), limit) < eps);
        assert(seq_at(s, start) <= bound);
        assert(false) by(nonlinear_arith)
            requires dist(seq_at(s, start), limit) < eps,
                dist(seq_at(s, start), limit) == abs(seq_at(s, start) - limit),
                seq_at(s, start) <= bound, eps == limit - bound, limit > bound;
    }
}

/// Limit of a sequence bounded below by B is at least B.
pub proof fn lemma_limit_ge_bound(s: spec_fn(nat) -> real, limit: real, bound: real)
    requires converges_to(s, limit), is_bounded_below(s, bound),
    ensures limit >= bound,
{
    if limit < bound {
        let eps = bound - limit;
        assert(eps > 0real) by(nonlinear_arith) requires limit < bound, eps == bound - limit;
        assert(exists_close_suffix(s, limit, eps));
        let start = choose |start: nat| suffix_is_close(s, limit, eps, start);
        assert(dist(seq_at(s, start), limit) < eps);
        assert(seq_at(s, start) >= bound);
        assert(false) by(nonlinear_arith)
            requires dist(seq_at(s, start), limit) < eps,
                dist(seq_at(s, start), limit) == abs(seq_at(s, start) - limit),
                seq_at(s, start) >= bound, eps == bound - limit, limit < bound;
    }
}

/// Pointwise-equal sequences share limits.
pub proof fn lemma_limit_pointwise_eq(
    s1: spec_fn(nat) -> real, s2: spec_fn(nat) -> real, limit: real,
)
    requires converges_to(s1, limit),
        forall |n: nat| seq_at(s1, n) == seq_at(s2, n),
    ensures converges_to(s2, limit),
{
    assert forall |epsilon: real| epsilon > 0real
        implies #[trigger] exists_close_suffix(s2, limit, epsilon) by {
        assert(exists_close_suffix(s1, limit, epsilon));
        let start = choose |start: nat| suffix_is_close(s1, limit, epsilon, start);
        assert(suffix_is_close(s2, limit, epsilon, start)) by {
            assert forall |n: nat| n >= start implies
                dist(#[trigger] seq_at(s2, n), limit) < epsilon by {
                assert(seq_at(s1, n) == seq_at(s2, n));
            };
        };
    };
}

/// If s → L and delta > 0, there exists N with s(N) < L + delta.
pub proof fn lemma_convergent_witness(s: spec_fn(nat) -> real, limit: real, delta: real)
    requires converges_to(s, limit), delta > 0real,
    ensures exists |d: nat| seq_at(s, d) < limit + delta,
{
    assert(exists_close_suffix(s, limit, delta));
    let start = choose |start: nat| suffix_is_close(s, limit, delta, start);
    assert(seq_at(s, start) < limit + delta) by(nonlinear_arith)
        requires dist(seq_at(s, start), limit) < delta,
            dist(seq_at(s, start), limit) == abs(seq_at(s, start) - limit);
}

// ============================================================================
// Series convergence
// ============================================================================

/// Partial sums of non-negative terms are non-decreasing.
pub proof fn lemma_partial_sums_nondecreasing(s: spec_fn(nat) -> real)
    requires forall |n: nat| #[trigger] seq_at(s, n) >= 0real,
    ensures is_nondecreasing(partial_sum_seq(s)),
{
    assert forall |m: nat|
        #[trigger] seq_at(partial_sum_seq(s), m) <= seq_at(partial_sum_seq(s), m + 1) by {
        assert(seq_at(s, m) >= 0real);
    };
}

/// Bounded non-negative series is summable.
pub proof fn lemma_bounded_series_summable(s: spec_fn(nat) -> real, bound: real)
    requires
        forall |n: nat| #[trigger] seq_at(s, n) >= 0real,
        partial_sums_bounded_by(s, bound),
    ensures is_summable(s),
{
    lemma_partial_sums_nondecreasing(s);
    assert forall |m: nat| #[trigger] seq_at(partial_sum_seq(s), m) <= bound by {
        assert(bound >= partial_sum(s, m));
    };
    axiom_monotone_convergence(partial_sum_seq(s), bound);
    let limit: real = choose |limit: real| converges_to(partial_sum_seq(s), limit);
    assert(sums_to(s, limit));
}

// ============================================================================
// Geometric series lemmas
// ============================================================================

/// First-step decomposition:
///   geo_partial_sum(e, n+1) = 0.5·e(0) + 0.5·geo_partial_sum(shift_e(e), n)
proof fn lemma_series_first_step(e: spec_fn(nat) -> real, n: nat)
    ensures
        geo_partial_sum(e, n + 1) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), n),
    decreases n,
{
    if n == 0 {
        assert(pow(0.5real, 0nat) == 1real);
        assert(geo_partial_sum(e, 1nat) == 0.5real * e(0nat)) by(nonlinear_arith)
            requires geo_partial_sum(e, 1nat) == geo_partial_sum(e, 0nat) + geo_summands(e)(0nat),
                geo_partial_sum(e, 0nat) == 0real,
                geo_summands(e)(0nat) == pow(0.5real, 0nat + 1) * e(0nat),
                pow(0.5real, 1nat) == 0.5real * pow(0.5real, 0nat),
                pow(0.5real, 0nat) == 1real;
    } else {
        lemma_series_first_step(e, (n - 1) as nat);
        assert(pow(0.5real, n + 1) == 0.5real * pow(0.5real, n));
        assert(geo_partial_sum(e, n + 1) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), n))
            by(nonlinear_arith)
            requires
                geo_partial_sum(e, n) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), (n - 1) as nat),
                geo_partial_sum(e, n + 1) == geo_partial_sum(e, n) + geo_summands(e)(n),
                geo_partial_sum(shift_e(e), n) == geo_partial_sum(shift_e(e), (n - 1) as nat) + geo_summands(shift_e(e))((n - 1) as nat),
                geo_summands(e)(n) == pow(0.5real, n + 1) * e(n),
                geo_summands(shift_e(e))((n - 1) as nat) == pow(0.5real, n) * e(n),
                pow(0.5real, n + 1) == 0.5real * pow(0.5real, n);
    }
}

/// Distribution bound transfers through recursion:
/// if geo_series_bounded_by(e, eps - slack) and e(i) ≥ 0,
/// then geo_series_bounded_by(shift_e(e), 2·eps - e(0) - 2·slack).
///
/// Uses S = (1/2)·e(0) + (1/2)·S', so S ≤ eps - slack ⟹ S' ≤ 2·eps - e(0) - 2·slack.
pub proof fn lemma_shift_bound(e: spec_fn(nat) -> real, eps: real, slack: real)
    requires
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        geo_series_bounded_by(e, eps - slack),
    ensures
        geo_series_bounded_by(shift_e(e), (2real * eps - e(0nat)) - 2real * slack),
{
    assert forall |n: nat| ((2real * eps - e(0nat)) - 2real * slack)
        >= #[trigger] partial_sum(geo_summands(shift_e(e)), n) by {
        lemma_series_first_step(e, n);
        assert(eps - slack >= partial_sum(geo_summands(e), n + 1));
        assert(((2real * eps - e(0nat)) - 2real * slack) >= partial_sum(geo_summands(shift_e(e)), n))
            by(nonlinear_arith) requires
                geo_partial_sum(e, n + 1) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), n),
                eps - slack >= geo_partial_sum(e, n + 1),
                e(0nat) >= 0real,
                geo_partial_sum(shift_e(e), n) == partial_sum(geo_summands(shift_e(e)), n);
    };
}

/// Bounded geometric series is summable.
pub proof fn lemma_geo_series_summable(e: spec_fn(nat) -> real, bound: real)
    requires
        forall |i: nat| #[trigger] seq_at(e, i) >= 0real,
        geo_series_bounded_by(e, bound),
    ensures is_summable(geo_summands(e)),
{
    assert forall |n: nat| #[trigger] seq_at(geo_summands(e), n) >= 0real by {
        assert(seq_at(e, n) >= 0real);
        lemma_pow_nonneg(0.5real, n + 1);
        assert(geo_summands(e)(n) >= 0real) by(nonlinear_arith)
            requires pow(0.5real, n + 1) >= 0real, e(n) >= 0real;
    };
    lemma_bounded_series_summable(geo_summands(e), bound);
}

} // verus!
