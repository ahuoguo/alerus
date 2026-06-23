// SmartSum (LightDP, Figure 12)
//
//   precondition: only one entry of q may have nonzero distance
//   epsilon, M: num(0); (note: i don't know why LightDP introduced this T thing...)
//   q : list num(*); 
//   out : list num(0);
//   next, n, i : num(0);
//   sum : num(*);
//   eta_1 : num(-^sum-^q[i]); 
//   eta_2 : num(-^q[i])
//
// LightDP-style guarantee (Fig. 12):
//   • Privacy: every released value has distance 0.
//   • Budget:  total cost ≤ 2·ε under the adjacency assumption
//              (at most one q[i] has nonzero distance).
//
// Each q[j] shows up in at most two cost events:
//   1. Its own iteration i = j contributes |^q[j]| · ε.
//   2. The window-close that covers j (if j wasn't itself closed)
//      contributes another |^q[j]| · ε via the accumulated ^sum.
// Under adjacency only one j has |^q[j]| > 0, so total ≤ 2|^q[j]|·ε ≤ 2·ε.

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use random::IBig;

verus! {

use crate::dp::mult_credit::*;
use crate::dp::num_d::NumD;
#[cfg(verus_keep_ghost)]
use crate::dp::num_d::abs_int;

/// Sum of `q[j].dist()` for j ∈ [lo, hi).
pub open spec fn dsum(q: Seq<NumD>, lo: int, hi: int) -> int
    decreases hi - lo when lo <= hi
{
    if lo >= hi { 0int } else { q[lo].dist() + dsum(q, lo + 1, hi) }
}

/// `dx` witnesses adjacency: every other index has zero distance.
pub open spec fn is_adjacency_witness(q: Seq<NumD>, dx: int) -> bool {
    0 <= dx < q.len()
    && (forall |i: int| 0 <= i < q.len() && i != dx ==>
            #[trigger] q[i].dist() == 0int)
}

proof fn lemma_dsum_extend(q: Seq<NumD>, lo: int, hi: int)
    requires lo <= hi,
    ensures dsum(q, lo, hi + 1) == dsum(q, lo, hi) + q[hi].dist(),
    decreases hi - lo,
{
    if lo == hi {
        assert(dsum(q, lo + 1, lo + 1) == 0int);
    } else {
        lemma_dsum_extend(q, lo + 1, hi);
    }
}

/// Under the adjacency assumption (only `d_idx` has nonzero distance),
/// the window sum equals `^q[d_idx]` when d_idx is in [lo, hi), else 0.
proof fn lemma_dsum_adjacency(q: Seq<NumD>, lo: int, hi: int, d_idx: int)
    requires
        0 <= lo <= hi <= q.len(),
        0 <= d_idx < q.len(),
        forall |j: int| #![auto] 0 <= j < q.len() && j != d_idx ==> q[j].dist() == 0int,
    ensures
        lo <= d_idx < hi ==> dsum(q, lo, hi) == q[d_idx].dist(),
        !(lo <= d_idx < hi) ==> dsum(q, lo, hi) == 0int,
    decreases hi - lo,
{
    if lo >= hi {
        return;
    }
    lemma_dsum_adjacency(q, lo + 1, hi, d_idx);
}

pub fn smart_sum(
    epsilon: u64,
    big_m: u64,
    q: &Vec<NumD>,
    Tracked(credit): Tracked<MultCreditResource>,
    Ghost(eps_budget): Ghost<real>,
) -> ((value, out_credit): (Vec<NumD>, Tracked<MultCreditResource>))
    requires
        epsilon > 0,
        big_m > 0,
        q.len() < u64::MAX,
        forall |i: int| 0 <= i < q.len() as int ==>
            abs_int(#[trigger] q@[i].dist()) <= 1,
        // Adjacency: at most one index may have nonzero distance.
        exists |dx: int| #[trigger] is_adjacency_witness(q@, dx),
        credit.view() =~= (MultCreditCarrier::Value { car: eps_budget }),
        eps_budget >= 2real * (epsilon as real),
    ensures
        value.len() == q.len(),
        // Privacy: every released value has distance 0.
        forall |k: int| 0 <= k < value.len() as int ==>
            (#[trigger] value@[k].dist()) == 0int,
        // Budget: total credits spent ≤ 2·ε.
        exists |r: real|
            out_credit@.view() =~= (MultCreditCarrier::Value { car: r })
            && r >= eps_budget - 2real * (epsilon as real),
{
    // Extract the differing index from the existential precondition.
    let ghost d_idx: int = choose |dx: int| is_adjacency_witness(q@, dx);

    let mut out: Vec<NumD> = Vec::new();
    let mut next: NumD = NumD::lit(0);
    let mut n:    NumD = NumD::lit(0);
    let mut sum:  NumD = NumD::lit(0);
    let ghost mut last_reset: int = 0;
    let ghost mut paid_d: nat = 0;   // # times d_idx has been charged (≤ 2)
    let mut i: u64 = 0;
    let tracked mut cred = credit;
    let ghost mut spent: real = 0real;

    while i < q.len() as u64
        invariant
            0 <= i as int <= q.len() as int,
            0 <= last_reset <= i as int,
            out.len() == i as int,
            last_reset % (big_m as int) == 0,
            (i as int) - last_reset <= (big_m as int) - 1,
            sum.dist() == dsum(q@, last_reset, i as int),
            next.dist() == 0,
            n.dist() == 0,
            // Adjacency carried through.
            0 <= d_idx < q.len() as int,
            abs_int(q@[d_idx].dist()) <= 1,
            forall |j: int| 0 <= j < q.len() as int && j != d_idx ==>
                #[trigger] q@[j].dist() == 0int,
            // LightDP accounting: d_idx contributes at most twice.
            // Position-indexed bound on paid_d:
            //   i ≤ d_idx                  ⇒ paid_d = 0
            //   i > d_idx, last_reset ≤ d_idx ⇒ paid_d ≤ 1  (own-iter paid, window open)
            //   last_reset > d_idx          ⇒ paid_d ≤ 2  (window closed)
            (i as int) <= d_idx ==> paid_d == 0,
            (i as int) > d_idx && last_reset <= d_idx ==> paid_d <= 1,
            paid_d <= 2,
            spent >= 0real,
            spent <= (paid_d as real)
                     * (abs_int(q@[d_idx].dist()) as real) * (epsilon as real),
            cred.view() =~= (MultCreditCarrier::Value { car: eps_budget - spent }),
            q.len() < u64::MAX,
            big_m > 0,
            epsilon > 0,
            eps_budget >= 2real * (epsilon as real),
            forall |k: int| 0 <= k < out.len() as int ==>
                (#[trigger] out@[k].dist()) == 0int,
        decreases q.len() as int - i as int,
    {
        let ghost prev_spent = spent;
        let ghost prev_paid = paid_d;
        let ghost prev_sum_d = sum.dist();
        let ghost qi_d = q@[i as int].dist();
        let ghost qd_d = q@[d_idx].dist(); // also ^q[d_idx]

        // Under adjacency, |sum.dist()| ≤ |^q[d_idx]| (= 0 unless d_idx is in
        // the current open window). qi_d = 0 unless i == d_idx.
        proof {
            lemma_dsum_adjacency(q@, last_reset, i as int, d_idx);
        }

        let ghost j = (i as int) - last_reset;
        if (i + 1) % big_m == 0 {
            // Window close: η₁ has distance −(^sum + ^q[i]).
            let ghost d1: int = -(prev_sum_d + qi_d);
            // |d1| ≤ |qi_d|: sum and qi_d can't both be nonzero

            proof {
                // Pre-call reservation: |d1|·ε ≤ |qd_d|·ε ≤ ε, and
                // eps_budget − spent ≥ 2·ε − paid_d·|qd_d|·ε ≥ |qd_d|·ε
                // (since paid_d ≤ 2 − 1 = 1 whenever |d1| > 0, by the
                // positional invariants).
                assert((abs_int(d1) as real) * (epsilon as real)
                       <= eps_budget - spent) by(nonlinear_arith)
                    requires
                        abs_int(d1) <= abs_int(qd_d),
                        prev_paid == 2nat ==> abs_int(d1) == 0,
                        eps_budget >= 2real * (epsilon as real),
                        spent <= (prev_paid as real)
                                 * (abs_int(qd_d) as real) * (epsilon as real),
                        prev_paid <= 2, abs_int(qd_d) <= 1,
                        epsilon > 0;
            }

            let (eta1, Tracked(cred2)) = NumD::laplace(
                1, epsilon, Ghost(|_v: int| d1), Ghost(abs_int(d1)),
                Ghost(eps_budget - spent), Tracked(cred),
            );
            proof {
                cred = cred2;
                assert((abs_int(d1) as real) * (epsilon as real) >= 0real) by(nonlinear_arith)
                    requires abs_int(d1) >= 0, epsilon > 0;
                spent = spent + (abs_int(d1) as real) * (epsilon as real);
                // Bump paid_d iff the actual cost came from d_idx.
                if last_reset <= d_idx && d_idx <= (i as int) {
                    paid_d = paid_d + 1;
                }
            }

            let qi: &NumD = &q[i as usize];
            n = n.add(&sum).add(qi).add(&eta1);
            assert(n.dist() == 0);
            next = n.clone();
            sum = NumD::lit(0);
            out.push(next.clone());

            proof {
                last_reset = i as int + 1;
                assert(spent <= (paid_d as real)
                             * (abs_int(qd_d) as real) * (epsilon as real))
                by(nonlinear_arith)
                    requires
                        spent == prev_spent + (abs_int(d1) as real) * (epsilon as real),
                        prev_spent <= (prev_paid as real)
                                      * (abs_int(qd_d) as real) * (epsilon as real),
                        abs_int(d1) <= abs_int(qd_d),
                        (paid_d == prev_paid + 1) || (paid_d == prev_paid && abs_int(d1) == 0),
                        epsilon > 0;
            }
        } else {
            // Intra-window. Force j < big_m − 1 (else j+1 == big_m and
            // (i+1) % big_m would be 0, contradicting the branch).
            proof {
                if j == (big_m as int) - 1 {
                    assert((i as int + 1) % (big_m as int) == 0) by(nonlinear_arith)
                        requires
                            last_reset % (big_m as int) == 0,
                            (i as int + 1) == last_reset + (big_m as int),
                            big_m > 0;
                }
            }

            let ghost d2: int = -qi_d;

            // Pre-call reservation: |d2| ≤ |^q[d_idx]|, with d2 = 0 if i ≠ d_idx.
            proof {
                assert((abs_int(d2) as real) * (epsilon as real)
                       <= eps_budget - spent) by(nonlinear_arith)
                    requires
                        abs_int(d2) <= abs_int(qd_d),
                        (i as int) != d_idx ==> abs_int(d2) == 0,
                        eps_budget >= 2real * (epsilon as real),
                        spent <= (prev_paid as real)
                                 * (abs_int(qd_d) as real) * (epsilon as real),
                        (i as int) == d_idx ==> prev_paid == 0nat,
                        prev_paid <= 2, abs_int(qd_d) <= 1,
                        epsilon > 0;
            }

            let (eta2, Tracked(cred2)) = NumD::laplace(
                1, epsilon, Ghost(|_v: int| d2), Ghost(abs_int(d2)),
                Ghost(eps_budget - spent), Tracked(cred),
            );
            proof {
                cred = cred2;
                assert((abs_int(d2) as real) * (epsilon as real) >= 0real) by(nonlinear_arith)
                    requires abs_int(d2) >= 0, epsilon > 0;
                spent = spent + (abs_int(d2) as real) * (epsilon as real);
                if (i as int) == d_idx {
                    paid_d = paid_d + 1;
                }
            }

            let qi: &NumD = &q[i as usize];
            next = next.add(qi).add(&eta2);
            sum = sum.add(qi);
            out.push(next.clone());

            proof {
                lemma_dsum_extend(q@, last_reset, i as int);
                assert(spent <= (paid_d as real)
                             * (abs_int(qd_d) as real) * (epsilon as real))
                by(nonlinear_arith)
                    requires
                        spent == prev_spent + (abs_int(d2) as real) * (epsilon as real),
                        prev_spent <= (prev_paid as real)
                                      * (abs_int(qd_d) as real) * (epsilon as real),
                        abs_int(d2) <= abs_int(qd_d),
                        (paid_d == prev_paid + 1) || (paid_d == prev_paid && abs_int(d2) == 0),
                        epsilon > 0;
            }
        }

        i = i + 1;
    }

    // Bound paid_d · |qd_d| · ε ≤ 2 · ε. So spent ≤ 2·ε, hence residual ≥ eps_budget − 2·ε.
    proof {
        assert(spent <= 2real * (epsilon as real)) by(nonlinear_arith)
            requires
                spent <= (paid_d as real)
                         * (abs_int(q@[d_idx].dist()) as real) * (epsilon as real),
                paid_d <= 2,
                abs_int(q@[d_idx].dist()) <= 1,
                epsilon > 0;
    }

    (out, Tracked(cred))
}

} // verus!
