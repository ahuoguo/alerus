// NumSparseVector (LightDP, Figure 11 / §6.1).
//
// Numeric variant of SparseVector. Three independent noise sources:
//   η₁ : num(1)                         — threshold noise, scale 3/ε
//   η₂ : num(2 if q[i]+η₂ ≥ T else 0)  — comparison noise, scale 6N/ε
//   η₃ : num(−^q[i])                    — release noise, scale 3N/ε
//
// η₂ decides the branch exactly as in SparseVector. In the TRUE branch we
// sample a *fresh* η₃ whose distance cancels ^q[i], so the released value
// q[i]+η₃ has distance 0 (LightDP `num(0)`, safe to release).
//
// No adjacency assumption needed. Per-iter η₃ cost ≤ 1·ε/(3N), summing
// to ≤ N·(ε/(3N)) = ε/3 over N TRUE branches.
//
// Budget accounting (total ε):
//   η₁:  1 / (3/ε)         = ε/3
//   η₂:  per TRUE 2 / (6N/ε) = ε/(3N); N TRUEs       ⇒ ε/3
//   η₃:  per TRUE |^q[i]| / (3N/ε) ≤ ε/(3N); N TRUEs ⇒ ε/3

use vstd::prelude::*;
use random::IBig;

verus! {

use crate::dp::mult_credit::*;
use crate::dp::num_d::NumD;
#[cfg(verus_keep_ghost)]
use crate::dp::num_d::abs_int;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExIBig;

pub fn num_sparse_vector(
    epsilon: u64,
    big_n: u64,
    big_t: IBig,
    q: &Vec<NumD>,
    Tracked(credit): Tracked<MultCreditResource>,
    Ghost(eps_budget): Ghost<real>,
) -> ((value, out_credit): (Vec<NumD>, Tracked<MultCreditResource>))
    requires
        epsilon > 0,
        big_n > 0,
        big_n <= u64::MAX / 6,
        q.len() < u64::MAX,
        forall |i: int| 0 <= i < q.len() as int ==>
            abs_int(#[trigger] q@[i].dist()) <= 1,
        credit.view() =~= (MultCreditCarrier::Value { car: eps_budget }),
        // LightDP Fig. 11: total budget ε.
        eps_budget >= (epsilon as real),
    ensures
        value.len() <= q.len(),
        // Privacy: every released value has distance 0 (LightDP `num(0)`).
        forall |k: int| 0 <= k < value.len() as int ==>
            (#[trigger] value@[k].dist()) == 0int,
        // Total DP cost ≤ ε.
        exists |r: real|
            out_credit@.view() =~= (MultCreditCarrier::Value { car: r })
            && r >= eps_budget - (epsilon as real),
{
    let mut out: Vec<NumD> = Vec::new();
    let tracked mut cred = credit;
    let ghost mut spent: real = 0real;
    let ghost mut eta3_cum: real = 0real;   // cumulative η₃ cost so far

    // ─── η₁ : scale 3/ε, distance 1, cost ε/3 ─────────────────────────
    let (eta_1, Tracked(cred1)) = NumD::laplace(
        3, epsilon, Ghost(|_v: int| 1int), Ghost(1int),
        Ghost(eps_budget), Tracked(cred),
    );
    proof {
        cred = cred1;
        spent = (epsilon as real) / 3real;
        assert((abs_int(1int) as real) * (epsilon as real) / (3 as real)
               == (epsilon as real) / 3real) by(nonlinear_arith);
        assert(spent == (epsilon as real) / 3real
               + (0 as real) * (epsilon as real) / (3real * (big_n as real))
               + (0 as real))
        by(nonlinear_arith)
            requires spent == (epsilon as real) / 3real, big_n > 0;
    }

    // T_threshold = T + η₁ → distance 1.
    let t_threshold: NumD = NumD::from_ibig(big_t).add(&eta_1);

    let mut c1: u64 = 0;
    let mut i: u64 = 0;

    while c1 < big_n && (i as usize) < q.len()
        invariant
            big_n > 0,
            big_n <= u64::MAX / 6,
            epsilon > 0,
            eps_budget >= (epsilon as real),
            0 <= c1 as int <= big_n as int,
            0 <= i as int <= q.len() as int,
            q.len() < u64::MAX,
            out.len() <= i as int,
            out.len() <= c1 as int,
            t_threshold.dist() == 1int,
            cred.view() =~= (MultCreditCarrier::Value { car: eps_budget - spent }),
            forall |k: int| 0 <= k < q.len() as int ==>
                abs_int(#[trigger] q@[k].dist()) <= 1,
            // Budget decomposition:
            //   spent = ε/3  +  c1·ε/(3N)       [η₁ + η₂ cumulative]
            //                +  eta3_cum         [η₃ cumulative]
            //   with 0 ≤ eta3_cum ≤ c1 · ε/(3N).
            spent == (epsilon as real) / 3real
                   + (c1 as real) * (epsilon as real) / (3real * (big_n as real))
                   + eta3_cum,
            0real <= eta3_cum,
            eta3_cum <= (c1 as real) * (epsilon as real) / (3real * (big_n as real)),
            spent >= 0real,
            spent <= (epsilon as real),
            // Privacy of outputs.
            forall |k: int| 0 <= k < out.len() as int ==>
                (#[trigger] out@[k].dist()) == 0int,
        decreases q.len() as int - i as int,
    {
        let qi: &NumD = &q[i as usize];
        let ghost qi_d = qi.dist();

        let ghost qi_v = qi.val();
        let ghost t_v = t_threshold.val();
        let ghost chooser2: spec_fn(int) -> int = |v: int|
            if qi_v + v >= t_v { 2int } else { 0int };

        // Pre-call reservation: credit ≥ 2 · ε / (6N) = ε/(3N).
        proof {
            assert(eps_budget - spent
                   >= (2int as real) * (epsilon as real) / ((6 * big_n) as real))
            by(nonlinear_arith)
                requires
                    eps_budget >= (epsilon as real),
                    spent == (epsilon as real) / 3real
                           + (c1 as real) * (epsilon as real) / (3real * (big_n as real))
                           + eta3_cum,
                    eta3_cum <= (c1 as real) * (epsilon as real) / (3real * (big_n as real)),
                    (c1 as real) + 1real <= big_n as real,
                    big_n > 0;
        }

        let (eta_2, Tracked(cred2)) = NumD::laplace(
            6 * big_n, epsilon, Ghost(chooser2), Ghost(2int),
            Ghost(eps_budget - spent), Tracked(cred),
        );
        proof { cred = cred2; }

        let lhs: NumD = qi.add(&eta_2);

        // T-ODOT for the comparison (same as SparseVector).
        let is_above: bool = lhs.ge_aligned(&t_threshold);

        if is_above {
            // η₂ contributed ε/(3N); update spent.
            proof {
                let prev_spent = spent;
                spent = spent + (epsilon as real) / (3real * (big_n as real));
                assert((abs_int(chooser2(eta_2.val())) as real) * (epsilon as real)
                       / ((6 * big_n) as real)
                       == (epsilon as real) / (3real * (big_n as real)))
                by(nonlinear_arith)
                    requires
                        chooser2(eta_2.val()) == 2int,
                        big_n > 0;
                // New formula: spent = ε/3 + (c1+1)·ε/(3N) + eta3_cum.
                assert(spent == (epsilon as real) / 3real
                       + ((c1 + 1) as real) * (epsilon as real) / (3real * (big_n as real))
                       + eta3_cum)
                by(nonlinear_arith)
                    requires
                        spent == prev_spent + (epsilon as real) / (3real * (big_n as real)),
                        prev_spent == (epsilon as real) / 3real
                            + (c1 as real) * (epsilon as real) / (3real * (big_n as real))
                            + eta3_cum,
                        epsilon > 0, big_n > 0;
            }

            // ─── η₃ : scale 3N/ε, distance −^q[i]. ──────────────────
            // Per-TRUE cost ≤ 1·ε/(3N). Over N TRUEs, η₃_cum ≤ ε/3.
            let ghost chooser3: spec_fn(int) -> int = |_v: int| -qi_d;

            // Pre-call reservation: credit ≥ 1 · ε / (3N) = ε/(3N).
            proof {
                assert(eps_budget - spent
                       >= (1int as real) * (epsilon as real) / ((3 * big_n) as real))
                by(nonlinear_arith)
                    requires
                        eps_budget >= (epsilon as real),
                        spent == (epsilon as real) / 3real
                               + ((c1 + 1) as real)
                                 * (epsilon as real) / (3real * (big_n as real))
                               + eta3_cum,
                        eta3_cum <= (c1 as real)
                                    * (epsilon as real) / (3real * (big_n as real)),
                        (c1 as int + 1) <= big_n as int,
                        epsilon > 0, big_n > 0;
            }

            let (eta_3, Tracked(cred3)) = NumD::laplace(
                3 * big_n, epsilon, Ghost(chooser3), Ghost(1int),
                Ghost(eps_budget - spent), Tracked(cred),
            );
            proof {
                let prev_eta3_cum = eta3_cum;
                // η₃ actual cost = |−qi_d|·ε/(3N) ≤ ε/(3N).
                eta3_cum = eta3_cum + (abs_int(-qi_d) as real)
                                      * (epsilon as real) / (3real * (big_n as real));
                spent = spent + (abs_int(-qi_d) as real)
                                 * (epsilon as real) / (3real * (big_n as real));
                cred = cred3;
                // eta3_cum ≤ (c1+1)·ε/(3N).
                assert(eta3_cum <= ((c1 + 1) as real)
                                  * (epsilon as real) / (3real * (big_n as real)))
                by(nonlinear_arith)
                    requires
                        eta3_cum == prev_eta3_cum + (abs_int(-qi_d) as real)
                                    * (epsilon as real) / (3real * (big_n as real)),
                        prev_eta3_cum <= (c1 as real)
                                         * (epsilon as real) / (3real * (big_n as real)),
                        abs_int(-qi_d) <= 1,
                        big_n > 0;
                // eta3_cum ≥ 0.
                assert(eta3_cum >= 0real) by(nonlinear_arith)
                    requires
                        eta3_cum == prev_eta3_cum + (abs_int(-qi_d) as real)
                                    * (epsilon as real) / (3real * (big_n as real)),
                        prev_eta3_cum >= 0real,
                        big_n > 0;
            }

            // q[i] + η₃: distance 0 (^q[i] + (−^q[i]) = 0), safe to release.
            let value: NumD = qi.add(&eta_3);
            out.push(value);
            c1 = c1 + 1;

            proof {
                // Re-establish spent ≤ ε at loop-invariant level.
                assert(spent <= (epsilon as real)) by(nonlinear_arith)
                    requires
                        spent == (epsilon as real) / 3real
                               + (c1 as real) * (epsilon as real) / (3real * (big_n as real))
                               + eta3_cum,
                        eta3_cum <= (c1 as real)
                                    * (epsilon as real) / (3real * (big_n as real)),
                        (c1 as int) <= big_n as int,
                        big_n > 0;
            }
        } else {
            // FALSE branch: chooser2 returns 0, so η₂'s actual cost is 0
            // and cred2.view() = eps_budget − spent already.
            proof {
                assert((abs_int(chooser2(eta_2.val())) as real) * (epsilon as real)
                       / ((6 * big_n) as real) == 0real) by(nonlinear_arith)
                    requires chooser2(eta_2.val()) == 0int, big_n > 0;
            }
        }

        i = i + 1;
    }

    (out, Tracked(cred))
}

} // verus!
