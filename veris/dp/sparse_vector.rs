// SparseVector (LightDP, Figure 1).
//
//   precondition : forall i (-1 <= ^q[i] <= 1);
//   T, N, len, epsilon : num(0);  
//   q : list num(*);  
//   out : list bool_0;
//   c1, c2, i : num(0); 
//   T_threshold, eta_1 : num(1);
//   eta_2 : num(2 if q[i] + eta_2 >= T_threshold else 0)
//
// Budget (multiplicative credits, tight actual-cost residual):
//   η₁       d = 1, scale 2/ε    ⇒ cost ε/2
//   η₂ True  d = 2, scale 4N/ε   ⇒ cost ε/(2N)
//   η₂ False d = 0               ⇒ cost 0
// At most N True branches ⇒ total ≤ ε/2 + N · ε/(2N) = ε.

use vstd::prelude::*;
use random::IBig;

verus! {

use crate::dp::mult_credit::*;
use crate::dp::num_d::NumD;
#[cfg(verus_keep_ghost)]
use crate::dp::num_d::abs_int;
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ExIBig;

pub fn sparse_vector(
    epsilon: u64,
    big_n: u64,
    big_t: IBig,
    q: &Vec<NumD>,
    Tracked(credit): Tracked<MultCreditResource>,
    Ghost(eps_budget): Ghost<real>,
) -> ((value, out_credit): (Vec<bool>, Tracked<MultCreditResource>))
    requires
        epsilon > 0,
        big_n > 0,
        big_n <= u64::MAX / 4,
        q.len() < u64::MAX,
        forall |i: int| 0 <= i < q.len() as int ==>
            abs_int(#[trigger] q@[i].dist()) <= 1,
        credit.view() =~= (MultCreditCarrier::Value { car: eps_budget }),
        eps_budget >= (epsilon as real),
    ensures
        value.len() <= q.len(),
        exists |r: real|
            out_credit@.view() =~= (MultCreditCarrier::Value { car: r })
            && r >= eps_budget - (epsilon as real),
{
    let mut out: Vec<bool> = Vec::new();
    let tracked mut cred = credit;
    let ghost mut spent: real = 0real;

    // η₁ : fixed d = 1, scale 2/ε → pay ε/2.
    let (eta_1, Tracked(cred1)) = NumD::laplace(
        2, epsilon, Ghost(|_v: int| 1int), Ghost(1int),
        Ghost(eps_budget), Tracked(cred),
    );
    // ε/2 + c₁ · ε/(2N) at c₁ = 0.
    proof {
        cred = cred1;
        spent = (epsilon as real) / 2real;
        assert((abs_int(1int) as real) * (epsilon as real) / (2 as real)
               == (epsilon as real) / 2real) by(nonlinear_arith);
        assert(spent == (epsilon as real) / 2real
            + (0 as real) * (epsilon as real) / (2real * (big_n as real)))
        by(nonlinear_arith)
            requires spent == (epsilon as real) / 2real, epsilon > 0, big_n > 0;
    }

    // T_threshold = T + η₁ → distance 1.
    let t_threshold: NumD = NumD::from_ibig(big_t).add(&eta_1);

    let mut c1: u64 = 0;
    let mut c2: u64 = 0;
    let mut i: u64 = 0;

    while c1 < big_n && (i as usize) < q.len()
        // TODO comment: lightdp doesn't really have this i < q.len() check...
        invariant
            big_n > 0,
            big_n <= u64::MAX / 4,
            epsilon > 0,
            eps_budget >= (epsilon as real),
            0 <= c1 as int <= big_n as int,
            0 <= c2 as int <= q.len() as int,
            c1 as int + c2 as int == i as int,
            0 <= i as int <= q.len() as int,
            q.len() < u64::MAX,
            out.len() == i as int,
            t_threshold.dist() == 1int,
            cred.view() =~= (MultCreditCarrier::Value { car: eps_budget - spent }),
            spent == (epsilon as real) / 2real
                + (c1 as real) * (epsilon as real) / (2real * (big_n as real)),
            spent <= (epsilon as real),
            forall |k: int| 0 <= k < q.len() as int ==>
                abs_int(#[trigger] q@[k].dist()) <= 1,
        decreases q.len() as int - i as int,
    {
        let qi: &NumD = &q[i as usize];
        let ghost qi_v = qi.val();
        let ghost t_v = t_threshold.val();

        // d(v) = 2 if q[i] + v ≥ T else 0.
        let ghost chooser: spec_fn(int) -> int = |v: int|
            if qi_v + v >= t_v { 2int } else { 0int };

        // Pre-call reservation: credit ≥ 2 · ε / (4N) = ε/(2N).
        proof {
            assert(eps_budget - spent
                   >= (2int as real) * (epsilon as real) / ((4 * big_n) as real))
            by(nonlinear_arith)
                requires
                    eps_budget >= (epsilon as real),
                    spent == (epsilon as real) / 2real
                        + (c1 as real) * (epsilon as real) / (2real * (big_n as real)),
                    (c1 as real) + 1real <= big_n as real,
                    epsilon > 0, big_n > 0;
        }

        let (eta_2, Tracked(cred2)) = NumD::laplace(
            4 * big_n, epsilon, Ghost(chooser), Ghost(2int),
            Ghost(eps_budget - spent), Tracked(cred),
        );
        // Thread residual credit. The actual charge (|d|/r) gets
        // added to `spent` below, once we know the branch outcome.
        proof { cred = cred2; }

        // T-ODOT: the ≥ comparison agrees between adjacent worlds because
        //   True  (d=2): shifted diff = (lhs.v − t.v) + (^q[i] + 1) ≥ 0
        //   False (d=0): shifted diff = (lhs.v − t.v) + (^q[i] − 1) ≤ 0
        // given |^q[i]| ≤ 1. `ge_aligned`'s precondition discharges the
        // alignment proof, so the returned bool is identical in both worlds —
        // that's the ε-DP output witness.
        let is_above: bool = qi.add(&eta_2).ge_aligned(&t_threshold);

        if is_above {
            // chooser = 2 ⇒ cost ε/(2N). Re-establish loop invariant's
            // spent formula with c₁ incremented.
            proof {
                let prev_spent = spent;
                spent = spent + (epsilon as real) / (2real * (big_n as real));
                assert((abs_int(chooser(eta_2.val())) as real) * (epsilon as real)
                       / ((4 * big_n) as real)
                       == (epsilon as real) / (2real * (big_n as real)))
                by(nonlinear_arith)
                    requires
                        chooser(eta_2.val()) == 2int,
                        big_n > 0;
                assert(spent == (epsilon as real) / 2real
                    + ((c1 + 1) as real) * (epsilon as real) / (2real * (big_n as real))
                    && spent <= (epsilon as real)) by(nonlinear_arith)
                    requires
                        spent == prev_spent + (epsilon as real) / (2real * (big_n as real)),
                        prev_spent == (epsilon as real) / 2real
                            + (c1 as real) * (epsilon as real) / (2real * (big_n as real)),
                        (c1 as int + 1) <= big_n as int,
                        epsilon > 0, big_n > 0;
            }
            out.push(is_above);  // value is `true`, aligned
            c1 = c1 + 1;
        } else {
            // chooser = 0 ⇒ actual cost is 0, so `spent` doesn't change.
            // We just need to show the laplace residual matches the
            // invariant (|0| · ε / (4N) simplifies to 0).
            proof {
                assert((abs_int(chooser(eta_2.val())) as real) * (epsilon as real)
                       / ((4 * big_n) as real) == 0real) by(nonlinear_arith)
                    requires chooser(eta_2.val()) == 0int, (4 * big_n) as real > 0real;
            }
            out.push(is_above);  // value is `false`, aligned
            c2 = c2 + 1;
        }

        i = i + 1;
    }
    (out, Tracked(cred))
}

} // verus!
