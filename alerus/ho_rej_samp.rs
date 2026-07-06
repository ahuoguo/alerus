//! Higher Order Rejection Sampler.
//!
//! <https://logsem.github.io/clutch/clutch.eris.examples.approximate_samplers.approx_higherorder_rejection_sampler.html>
//!
//! TODO: might split this into 2 files, to move the instantiation out of the generic code.
//!
//! A sampling scheme is parameterized by:
//! - `sampler`: A sampling function that generates candidate values
//! - `checker`: A predicate that determines if a sample should be accepted
//! - `εfactor`: Error amplification factor
//!
//! Spec (from Clutch):
//!   Given ↯ε, after sampler() returns v, either:
//!   - checker(v) = true and Θ(v) holds
//!   - OR we have ↯ε' where ε ≤ ε' * εfactor

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::calc_macro::*;
use crate::ec::*;
#[cfg(verus_keep_ghost)]
use crate::ec::ErrorCreditCarrier::Value;
use crate::rand_primitives::{rand_u64, thin_air};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{average, sum_credit};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{pow, archimedean_exp_growth};
#[cfg(verus_keep_ghost)]
use crate::math::real::real_assoc_mult;

verus! {


/// Outcome of a sampling step in a sampling scheme.
///
/// After calling sample(), we get a value and one of:
/// - `Accepted`: checker will return true, postcondition Θ holds
/// - `Rejected`: we have amplified error credit, checker returns false
pub enum SampleOutcome {
    Accepted,
    Rejected(Tracked<ErrorCreditResource>),
}

/// A sampling scheme packages a sampler and checker with their specifications.
///
/// The key spec (matching Clutch's `sampling_scheme_spec`):
/// ```
/// Given ↯ε, after sampler() returns v:
///   Either: checker(v) = true ∧ Θ(v)
///   Or:     ↯ε' where ε ≤ ε' * self.amp()
/// ```

pub trait SamplingScheme {
    // TODO: do we really need a separate postcondition spec?
    // in the threshold example they are the same...
    /// The postcondition Θ that holds when a sample is accepted
    spec fn postcond(&self) -> spec_fn(u64) -> bool;

    /// The checker specification (what values are accepted)
    spec fn check_spec(&self) -> spec_fn(u64) -> bool;

    /// Amplification factor: on reject, ε becomes amp * ε
    spec fn amp(&self) -> real;

    /// Validity predicate - scheme-specific requirements for error credit accounting
    spec fn valid(&self) -> bool;

    /// Sample a value with error credit accounting
    ///
    /// Returns (v, outcome) where:
    /// - If outcome is Accepted: check_spec(v) is true and postcond(v) holds
    /// - If outcome is Rejected: check_spec(v) is false and we have amp*ε credit
    fn sample(
        &self,
        Tracked(e): Tracked<ErrorCreditResource>,
        Ghost(eps): Ghost<real>,
    ) -> ((value, outcome): (u64, SampleOutcome))
        requires
            self.valid(),
            eps > 0real,
            e@ =~= (Value { car: eps }),
        ensures
            match outcome {
                SampleOutcome::Accepted => {
                    &&& (self.check_spec())(value)
                    &&& (self.postcond())(value)
                }
                SampleOutcome::Rejected(ref amplified_credit) => {
                    &&& !(self.check_spec())(value)
                    &&& amplified_credit@@ =~= (Value { car: self.amp() * eps })
                }
            };

    /// Execute the checker (for use in the rejection loop)
    fn check(&self, v: u64) -> (ret: bool)
        ensures ret == (self.check_spec())(v);
}

// ============================================================================
// Higher-Order Rejection Sampler
// ============================================================================

/// Bounded rejection sampler over any sampling scheme
///
/// Loops until sample() returns an accepted value.
/// Uses error credit invariant: eps * amp^depth >= 1
pub fn bounded_rejection_sampler<S: SamplingScheme>(
    scheme: &S,
    Tracked(e): Tracked<ErrorCreditResource>,
    Ghost(depth): Ghost<nat>,
) -> (ret: u64)
    requires
        scheme.amp() > 1real,
        scheme.valid(),
        exists |eps: real| {
            &&& eps > 0real
            &&& e@ =~= (Value { car: eps })
            &&& eps * pow(scheme.amp(), depth) >= 1real
        },
    ensures
        (scheme.check_spec())(ret),
        (scheme.postcond())(ret),
    decreases depth,
{
    let ghost amp = scheme.amp();
    let ghost eps: real;

    proof {
        eps = choose |v: real| {
            &&& v > 0real
            &&& e@ =~= (Value { car: v })
            &&& v * pow(amp, depth) >= 1real
        };

        // Base case: depth == 0 implies eps >= 1, contradiction
        if depth == 0nat {
            assert(pow(amp, 0nat) == 1real);
            assert(eps >= 1real);
            ec_contradict(&e);
        }
    }

    let (val, outcome) = scheme.sample(Tracked(e), Ghost(eps));

    match outcome {
        SampleOutcome::Accepted => {
            val
        }
        SampleOutcome::Rejected(e1_tracked) => {
            let ghost new_eps = amp * eps;

            proof {
                // e1 has amp * eps credit
                assert(e1_tracked@@ =~= (Value { car: new_eps }));

                // Show new_eps > 0
                lemma_pos_mult(amp, eps);

                // Show: new_eps * amp^(depth-1) >= 1
                calc! {
                    (==)
                    new_eps * pow(amp, (depth - 1) as nat); {}
                    (amp * eps) * pow(amp, (depth - 1) as nat); {
                        real_assoc_mult(eps, amp, pow(amp, (depth - 1) as nat));
                    }
                    eps * (amp * pow(amp, (depth - 1) as nat)); {}
                    eps * pow(amp, depth);
                }
                assert(new_eps * pow(amp, (depth - 1) as nat) >= 1real);
            }

            bounded_rejection_sampler(scheme, e1_tracked, Ghost((depth - 1) as nat))
        }
    }
}

/// Unbounded rejection sampler
pub fn rejection_sampler<S: SamplingScheme>(
    scheme: &S,
) -> (ret: u64)
    requires
        scheme.amp() > 1real,
        scheme.valid(),
    ensures
        (scheme.check_spec())(ret),
        (scheme.postcond())(ret),
{
    // OBSERVE: the thin_air credit is created here
    // TODO: maybe we should take a thin_air credit as input instead?
    let Tracked(e) = thin_air();
    let ghost amp = scheme.amp();

    let ghost hi: nat;
    let ghost epsilon: real;

    proof {
        if e@.value() =~= None { }
    }
    assert(exists |v: real| e@.value() == Some(v));

    proof {
        epsilon = choose |i: real| e@.value() == Some(i);
        crate::math::pow::archimedean_exp_growth(epsilon, amp);
        assert(exists |k: nat| epsilon * pow(amp, k) >= 1real);
        hi = choose |k: nat| epsilon * pow(amp, k) >= 1real;
    }

    bounded_rejection_sampler(scheme, Tracked(e), Ghost(hi))
}

// ============================================================================
// Helper lemmas
// ============================================================================

#[verifier::nonlinear]
proof fn lemma_pos_mult(a: real, b: real)
    requires
        a > 0real,
        b > 0real,
    ensures
        a * b > 0real,
{
}

/// Lemma: a/b > 1 when a > b > 0
#[verifier::nonlinear]
proof fn lemma_div_gt_1(a: real, b: real)
    requires
        a > b,
        b > 0real,
    ensures
        a / b > 1real,
{
}

// ============================================================================
// Lemmas for average bound
// ============================================================================

/// Credit allocation for uniform threshold sampling.
/// - For outcomes i < threshold: credit = 0 (accepted, no amplification needed)
/// - For outcomes i >= threshold: credit = amp * eps where amp = bound / (bound - threshold)
pub open spec fn threshold_credit_alloc(bound: u64, threshold: u64, eps: real) -> spec_fn(nat) -> real {
    |i: nat| if i < threshold as nat { 0real } else { (bound as real / (bound - threshold) as real) * eps }
}

/// Lemma: sum_credit(threshold_credit_alloc, n) for n <= threshold is 0,
///        and for n > threshold equals (n - threshold) * amp * eps
proof fn lemma_sum_threshold(bound: u64, threshold: u64, eps: real, n: nat)
    requires
        bound > 0,
        threshold < bound,
        n <= bound,
    ensures
        n <= threshold ==> sum_credit(threshold_credit_alloc(bound, threshold, eps), n) == 0real,
        n > threshold ==> sum_credit(threshold_credit_alloc(bound, threshold, eps), n) ==
            (n - threshold) as real * (bound as real / (bound - threshold) as real) * eps,
    decreases n,
{
    let credit_alloc = threshold_credit_alloc(bound, threshold, eps);
    let amp = bound as real / (bound - threshold) as real;

    if n == 0 {
        // Base case: sum of empty range is 0
    } else {
        lemma_sum_threshold(bound, threshold, eps, (n - 1) as nat);
        let prev_sum = sum_credit(credit_alloc, (n - 1) as nat);
        let curr_credit = credit_alloc((n - 1) as nat);

        if n <= threshold {
            // n-1 < threshold, so credit_alloc(n-1) = 0
            assert(((n - 1) as nat) < threshold as nat);
            assert(curr_credit == 0real);
            // prev_sum == 0 by IH (since n-1 <= threshold)
        } else if (n - 1) as nat <= threshold as nat {
            // Transition case: n > threshold but n-1 <= threshold
            // So n-1 == threshold, meaning n == threshold + 1
            // credit_alloc(n-1) = credit_alloc(threshold) = amp * eps (since threshold >= threshold)
            assert(!(((n - 1) as nat) < threshold as nat));
            assert(curr_credit == amp * eps);
            // prev_sum == 0 by IH (since n-1 <= threshold)
            assert(prev_sum == 0real);
            // sum = 0 + amp * eps = 1 * amp * eps = (n - threshold) * amp * eps
            assert((n - threshold) as nat == 1nat);
            assert((n - threshold) as real == 1real);
            assert(sum_credit(credit_alloc, n) == amp * eps);
            assert((n - threshold) as real * amp * eps == amp * eps) by(nonlinear_arith)
                requires (n - threshold) as real == 1real;
            assert(sum_credit(credit_alloc, n) == (n - threshold) as real * amp * eps);
        } else {
            // Both in rejected region: n > threshold and n-1 > threshold
            assert(!(((n - 1) as nat) < threshold as nat));
            assert(curr_credit == amp * eps);
            // prev_sum == (n-1-threshold) * amp * eps by IH
            // sum = prev_sum + amp * eps = (n-threshold) * amp * eps
            assert(sum_credit(credit_alloc, n) == (n - threshold) as real * amp * eps) by(nonlinear_arith)
                requires
                    prev_sum == ((n - 1) as nat - threshold as nat) as real * amp * eps,
                    curr_credit == amp * eps,
                    sum_credit(credit_alloc, n) == prev_sum + curr_credit,
                    n > threshold,
            ;
        }
    }
}

/// Lemma: eps >= average(bound, threshold_credit_alloc)
///
/// Proof: sum = (bound - threshold) * amp * eps = bound * eps, so average = eps
proof fn lemma_average_bound(bound: u64, threshold: u64, eps: real)
    requires
        bound > 0,
        threshold < bound,
        eps > 0real,
    ensures
        eps >= average(bound, threshold_credit_alloc(bound, threshold, eps)),
{
    let credit_alloc = threshold_credit_alloc(bound, threshold, eps);
    let amp = bound as real / (bound - threshold) as real;

    lemma_sum_threshold(bound, threshold, eps, bound as nat);
    // sum_credit = (bound - threshold) * amp * eps

    // (bound - threshold) * amp * eps = (bound - threshold) * (bound / (bound - threshold)) * eps = bound * eps
    // average = sum / bound = (bound * eps) / bound = eps
    assert(average(bound, credit_alloc) == eps) by(nonlinear_arith)
        requires
            sum_credit(credit_alloc, bound as nat) == (bound - threshold) as real * amp * eps,
            amp == bound as real / (bound - threshold) as real,
            bound > threshold,
            bound > 0,
    ;
}

// ============================================================================
// Concrete Implementation: Uniform + Threshold
// ============================================================================

/// A sampling scheme with uniform sampling and threshold checking.
/// - Samples uniformly from [0, bound)
/// - Accepts values < threshold
/// - Postcondition: v < threshold
pub struct UniformThresholdScheme {
    pub bound: u64,
    pub threshold: u64,
}

impl SamplingScheme for UniformThresholdScheme {
    open spec fn postcond(&self) -> spec_fn(u64) -> bool {
        |v: u64| v < self.threshold
    }

    open spec fn check_spec(&self) -> spec_fn(u64) -> bool {
        |v: u64| v < self.threshold
    }

    /// Amplification factor = bound / (bound - threshold)
    open spec fn amp(&self) -> real {
        self.bound as real / (self.bound - self.threshold) as real
    }

    /// Valid requires:
    /// - threshold < bound (for amp to be defined and > 1)
    open spec fn valid(&self) -> bool {
        self.threshold < self.bound
    }

    fn sample(
        &self,
        Tracked(input_credit): Tracked<ErrorCreditResource>,
        Ghost(eps): Ghost<real>,
    ) -> ((value, outcome): (u64, SampleOutcome))
        ensures
            match outcome {
                SampleOutcome::Accepted => {
                    &&& (self.check_spec())(value)
                    &&& (self.postcond())(value)
                }
                SampleOutcome::Rejected(ref amplified_credit) => {
                    &&& !(self.check_spec())(value)
                    &&& amplified_credit@@ =~= (Value { car: self.amp() * eps })
                }
            },
    {
        let ghost credit_alloc = threshold_credit_alloc(self.bound, self.threshold, eps);

        proof {
            lemma_average_bound(self.bound, self.threshold, eps);
            assert forall |i: nat| (#[trigger] credit_alloc(i)) >= 0real by {
                if i < self.threshold as nat {
                } else {
                    assert(credit_alloc(i) == (self.bound as real / (self.bound - self.threshold) as real) * eps);
                    assert(credit_alloc(i) >= 0real) by(nonlinear_arith)
                        requires
                            eps > 0real,
                            self.bound as real > 0real,
                            (self.bound - self.threshold) as real > 0real,
                            credit_alloc(i) == (self.bound as real / (self.bound - self.threshold) as real) * eps;
                }
            };
        }

        let (val, Tracked(outcome_credit)) = rand_u64(self.bound, Tracked(input_credit), Ghost(credit_alloc));

        if val < self.threshold {
            proof {
                assert(credit_alloc(val as nat) == 0real);
            }
            (val, SampleOutcome::Accepted)
        } else {
            (val, SampleOutcome::Rejected(Tracked(outcome_credit)))
        }
    }

    fn check(&self, v: u64) -> (ret: bool)
        ensures ret == (self.check_spec())(v),
    {
        v < self.threshold
    }
}

// ============================================================================
// Expectation transformation rule for the full rejection sampler
// ============================================================================

/// Per-step credit alloc for the rejection loop with output credit:
///   accepted (v < threshold) → ℰ(v)
///   rejected (v ≥ threshold) → amp·eps + eps_avg  (fuels next iteration)
pub open spec fn mixed_credit_alloc(
    threshold: u64, amp: real, e: spec_fn(u64) -> real, eps: real, eps_avg: real,
) -> spec_fn(nat) -> real {
    |v: nat| if v < threshold as nat { e(v as u64) } else { amp * eps + eps_avg }
}

/// For n <= threshold, mixed_credit_alloc agrees with |v| e(v.floor() as u64), so sums match.
proof fn lemma_sum_mixed_lower(
    threshold: u64, amp: real, e: spec_fn(u64) -> real, eps: real, eps_avg: real, n: nat,
)
    requires
        n <= threshold,
    ensures
        sum_credit(mixed_credit_alloc(threshold, amp, e, eps, eps_avg), n) ==
        sum_credit(|v: nat| e(v as u64), n),
    decreases n,
{
    let alloc = mixed_credit_alloc(threshold, amp, e, eps, eps_avg);
    if n == 0 {
        // Both sums are 0 by definition
    } else {
        lemma_sum_mixed_lower(threshold, amp, e, eps, eps_avg, (n - 1) as nat);
        // Step index n-1 < threshold: both credit fns return e(floor(n-1))
        let ghost idx = (n - 1) as nat;
        assert(idx < threshold as nat);
        // mixed_credit_alloc takes the then-branch when idx < threshold
        assert(alloc(idx) == e(idx as u64)) by {
            assert(idx < threshold as nat);
        };
        assert((|v: nat| e(v as u64))(idx) == e(idx as u64));
        // Unfold sum_credit on both sides so the solver sees the equality
        assert(sum_credit(alloc, n) ==
               sum_credit(alloc, (n - 1) as nat) + alloc(idx));
        assert(sum_credit(|v: nat| e(v as u64), n) ==
               sum_credit(|v: nat| e(v as u64), (n - 1) as nat) +
               (|v: nat| e(v as u64))(idx));
    }
}

/// For n >= threshold, sum_credit splits: lower prefix + uniform tail.
proof fn lemma_sum_mixed_upper(
    threshold: u64, amp: real, e: spec_fn(u64) -> real, eps: real, eps_avg: real, n: nat,
)
    requires
        threshold <= n,
    ensures
        sum_credit(mixed_credit_alloc(threshold, amp, e, eps, eps_avg), n) ==
        sum_credit(mixed_credit_alloc(threshold, amp, e, eps, eps_avg), threshold as nat) +
        (n - threshold) as real * (amp * eps + eps_avg),
    decreases n,
{
    let alloc = mixed_credit_alloc(threshold, amp, e, eps, eps_avg);
    if n == threshold as nat {
        assert((n - threshold) as real == 0real);
    } else {
        // n > threshold, so n - 1 >= threshold
        lemma_sum_mixed_upper(threshold, amp, e, eps, eps_avg, (n - 1) as nat);
        // Step index n-1 >= threshold: credit = amp*eps+eps_avg
        assert(!(((n - 1) as nat) < threshold as nat));
        assert(alloc((n - 1) as nat) == amp * eps + eps_avg);
        let ghost x = amp * eps + eps_avg;
        let ghost base = sum_credit(alloc, threshold as nat);
        // Unfold sum_credit(alloc, n) so nonlinear_arith can use it
        assert(sum_credit(alloc, n) == sum_credit(alloc, (n - 1) as nat) + alloc((n - 1) as nat));
        // IH + step → (n-1-threshold+1) * x = (n-threshold) * x
        assert(sum_credit(alloc, n) == base + (n - threshold) as real * x) by(nonlinear_arith)
            requires
                sum_credit(alloc, (n - 1) as nat) == base + ((n - 1) as nat - threshold as nat) as real * x,
                alloc((n - 1) as nat) == x,
                sum_credit(alloc, n) == sum_credit(alloc, (n - 1) as nat) + alloc((n - 1) as nat),
                n > threshold,
            ;
    }
}

/// eps + eps_avg ≥ average(bound, mixed_credit_alloc)
///
/// Proof sketch:
///   sum = Σ_{v<threshold} e(v) + (bound-threshold)·(amp·eps + eps_avg)
///       ≤ threshold·eps_avg + (bound-threshold)·amp·eps + (bound-threshold)·eps_avg
///       = (bound-threshold)·amp·eps + bound·eps_avg
///       = bound·eps + bound·eps_avg    ← since (bound-threshold)·amp = bound
proof fn lemma_mixed_alloc_average(
    bound: u64, threshold: u64, amp: real, e: spec_fn(u64) -> real, eps: real, eps_avg: real,
)
    requires
        threshold < bound,
        threshold > 0,
        amp == bound as real / (bound - threshold) as real,
        eps > 0real,
        eps_avg >= 0real,
        eps_avg >= average(threshold, |v: nat| e(v as u64)),
    ensures
        eps + eps_avg >= average(bound, mixed_credit_alloc(threshold, amp, e, eps, eps_avg)),
{
    let alloc = mixed_credit_alloc(threshold, amp, e, eps, eps_avg);
    let ghost e_real_sum = sum_credit(|v: nat| e(v as u64), threshold as nat);

    // Unfold average definitions so nonlinear_arith can use them
    assert(average(threshold, |v: nat| e(v as u64)) == e_real_sum / threshold as real);
    assert(average(bound, alloc) == sum_credit(alloc, bound as nat) / bound as real);
    // Derive: eps_avg >= e_real_sum / threshold  (by transitivity from average defn)
    assert(eps_avg >= e_real_sum / threshold as real);

    // Lower part sum equals pure e_real sum
    lemma_sum_mixed_lower(threshold, amp, e, eps, eps_avg, threshold as nat);
    let ghost lower_sum = sum_credit(alloc, threshold as nat);
    assert(lower_sum == e_real_sum);

    // Total sum = lower + (bound - threshold) * (amp * eps + eps_avg)
    lemma_sum_mixed_upper(threshold, amp, e, eps, eps_avg, bound as nat);
    let ghost total_sum = sum_credit(alloc, bound as nat);
    assert(total_sum == lower_sum + (bound - threshold) as real * (amp * eps + eps_avg));

    // Lower sum <= threshold * eps_avg
    assert(e_real_sum <= threshold as real * eps_avg) by(nonlinear_arith)
        requires
            eps_avg >= e_real_sum / threshold as real,
            threshold > 0,
        ;

    // Total sum <= bound * (eps + eps_avg)
    // Key: (bound-threshold)*amp = bound, so (bound-threshold)*(amp*eps+eps_avg)
    //      = bound*eps + (bound-threshold)*eps_avg
    assert(total_sum <= bound as real * (eps + eps_avg)) by(nonlinear_arith)
        requires
            total_sum == lower_sum + (bound - threshold) as real * (amp * eps + eps_avg),
            lower_sum == e_real_sum,
            e_real_sum <= threshold as real * eps_avg,
            amp == bound as real / (bound - threshold) as real,
            bound > threshold,
            eps > 0real,
            eps_avg >= 0real,
        ;

    // average(bound, alloc) = total_sum / bound <= eps + eps_avg
    assert(eps + eps_avg >= average(bound, alloc)) by(nonlinear_arith)
        requires
            total_sum <= bound as real * (eps + eps_avg),
            average(bound, alloc) == total_sum / bound as real,
            bound > 0,
        ;
}

/// Bounded rejection sampler satisfying the expectation transformation rule:
///
///   eps · amp^depth ≥ 1
///   eps_avg ≥ 𝔼_{v ~ Uniform[0,threshold)}[ℰ(v)]
///   ─────────────────────────────────────────────
///   [{ ↯(eps + eps_avg) }]
///     bounded_rejection_exp_preserving
///   [{ v < threshold. ↯(ℰ(v)) }]
pub fn bounded_rejection_exp_preserving(
    scheme: &UniformThresholdScheme,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(e): Ghost<spec_fn(u64) -> real>,
    Ghost(depth): Ghost<nat>,
    Ghost(eps): Ghost<real>,
    Ghost(eps_avg): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        scheme.valid(),
        scheme.amp() > 1real,
        scheme.threshold > 0,
        eps > 0real,
        eps_avg >= 0real,
        forall |v: u64| (#[trigger] e(v)) >= 0real,
        input_credit@ =~= (Value { car: eps + eps_avg }),
        eps * pow(scheme.amp(), depth) >= 1real,
        eps_avg >= average(scheme.threshold, |v: nat| e(v as u64)),
    ensures
        value < scheme.threshold,
        out_credit@@ =~= (Value { car: e(value) }),
    decreases depth,
{
    let ghost amp = scheme.amp();
    let ghost credit_alloc = mixed_credit_alloc(scheme.threshold, amp, e, eps, eps_avg);

    proof {
        if depth == 0nat {
            assert(pow(amp, 0nat) == 1real);
            assert(eps >= 1real);
            assert(eps + eps_avg >= 1real) by(nonlinear_arith)
                requires eps >= 1real, eps_avg >= 0real;
            ec_contradict(&input_credit);
        }
        lemma_mixed_alloc_average(scheme.bound, scheme.threshold, amp, e, eps, eps_avg);
        assert forall |i: nat| (#[trigger] credit_alloc(i)) >= 0real by {
            if i < scheme.threshold as nat {
                // unfolds to e(i as u64) >= 0
            } else {
                assert(amp * eps + eps_avg >= 0real) by(nonlinear_arith)
                    requires amp > 1real, eps > 0real, eps_avg >= 0real;
            }
        };
    }

    let (val, Tracked(outcome_credit)) = rand_u64(
        scheme.bound,
        Tracked(input_credit),
        Ghost(credit_alloc),
    );

    if val < scheme.threshold {
        let ghost vr = val as nat;
        assert(vr < scheme.threshold as nat);
        assert(vr as u64 == val);
        // credit_alloc takes then-branch: e(vr as u64) == e(val)
        assert(credit_alloc(vr) == e(val)) by {
            assert(vr < scheme.threshold as nat);
            assert(vr as u64 == val);
        };
        (val, Tracked(outcome_credit))
    } else {
        let ghost new_eps = amp * eps;
        assert(credit_alloc(val as nat) == new_eps + eps_avg) by {
            assert(!((val as nat) < (scheme.threshold as nat)));
        };

        proof {
            lemma_pos_mult(amp, eps);
            real_assoc_mult(eps, amp, pow(amp, (depth - 1) as nat));
            assert(new_eps * pow(amp, (depth - 1) as nat) == eps * pow(amp, depth));
        }

        bounded_rejection_exp_preserving(
            scheme, Tracked(outcome_credit), Ghost(e),
            Ghost((depth - 1) as nat), Ghost(new_eps), Ghost(eps_avg),
        )
    }
}

/// Unbounded rejection sampler satisfying the expectation transformation rule:
///
///   eps_avg ≥ 𝔼_{v ~ Uniform[0,threshold)}[ℰ(v)]
///   ─────────────────────────────────────────────
///   [{ ↯(eps_avg) }]
///     unbounded_rejection_exp_preserving
///   [{ v < threshold. ↯(ℰ(v)) }]
///
/// Internally allocates a thin-air credit for termination; caller only provides eps_avg.
pub fn unbounded_rejection_exp_preserving(
    scheme: &UniformThresholdScheme,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(e): Ghost<spec_fn(u64) -> real>,
    Ghost(eps_avg): Ghost<real>,
) -> ((value, out_credit): (u64, Tracked<ErrorCreditResource>))
    requires
        scheme.valid(),
        scheme.amp() > 1real,
        scheme.threshold > 0,
        eps_avg >= 0real,
        forall |v: u64| (#[trigger] e(v)) >= 0real,
        input_credit@ =~= (Value { car: eps_avg }),
        eps_avg >= average(scheme.threshold, |v: nat| e(v as u64)),
    ensures
        value < scheme.threshold,
        out_credit@@ =~= (Value { car: e(value) }),
{
    let ghost amp = scheme.amp();
    let Tracked(eps_credit) = thin_air();

    let ghost eps: real;
    let ghost depth: nat;

    proof {
        eps = choose |v: real| v > 0real && (Value { car: v } =~= eps_credit@);
        archimedean_exp_growth(eps, amp);
        depth = choose |k: nat| eps * pow(amp, k) >= 1real;
    }

    let tracked combined: ErrorCreditResource;
    proof {
        combined = ec_combine(input_credit, eps_credit, eps_avg, eps);
    }

    bounded_rejection_exp_preserving(
        scheme, Tracked(combined), Ghost(e),
        Ghost(depth), Ghost(eps), Ghost(eps_avg),
    )
}

/// Example: Sample from [0, 8) but only accept < 5
/// Rejection rate = 3/8, so amp = 8/3
pub fn example_rejection_sampler() -> (ret: u64)
    ensures ret < 5,
{
    let scheme = UniformThresholdScheme { bound: 8, threshold: 5 };
    proof {
        assert(scheme.valid());
        lemma_div_gt_1(8real, 3real);
        assert(scheme.amp() > 1real);
    }
    rejection_sampler(&scheme)
}

} // verus!
