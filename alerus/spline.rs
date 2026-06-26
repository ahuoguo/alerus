//! The Escaping Spline — an almost-sure-termination example from the ICFP'24 paper.
//!
//! ```
//! rec spline n = let x = rand (n + 1) in if x = 0 then () else spline (n+1)
//! ```
//!
//! Following the ICFP'24 paper, we prove this lemma ():
//! ```
//! ∀ n. [ ↯( n/(n+k+1) )] spline n [ True ]
//! ```
//! 
use vstd::prelude::*;

use random::{UBig, ubig_succ, ubig_is_zero, ubig_from_u64};

verus! {

use crate::ec::*;
use crate::rand_primitives::{rand_ubig, thin_air};
#[cfg(verus_keep_ghost)]
use crate::rand_primitives::{average_nat, sum_credit};
#[cfg(verus_keep_ghost)]
use crate::math::pow::{nat_to_real, archimedean_nat};
#[cfg(verus_keep_ghost)]
use crate::extern_spec::ubig_view;

pub open spec fn spline_credit(n: nat, k: nat) -> real {
    (n as real) / ((n + k + 1) as real)
}

pub open spec fn spline_alloc(n: nat, k: nat) -> spec_fn(real) -> real {
    |x: real| if x == 0real { 0real } else { (n + 1) as real / ((n + k + 1) as real) }
}

/// Σ_{i<m} spline_alloc(i) = (m−1)·(n+1)/(n+k+1)  for m ≥ 1
pub proof fn lemma_spline_sum(n: nat, k: nat, m: nat)
    requires m >= 1,
    ensures
        sum_credit(spline_alloc(n, k), m)
            == ((m - 1) as real) * ((n + 1) as real / ((n + k + 1) as real)),
    decreases m,
{
    let alloc = spline_alloc(n, k);
    let c = (n + 1) as real / ((n + k + 1) as real);
    if m == 1 {
        assert(alloc(0real) == 0real);
        assert(sum_credit(alloc, 1nat) == sum_credit(alloc, 0nat) + alloc(0real));
    } else {
        lemma_spline_sum(n, k, (m - 1) as nat);
        assert(alloc((m - 1) as real) == c);
        assert(sum_credit(alloc, m) == sum_credit(alloc, (m - 1) as nat) + alloc((m - 1) as real));
        assert(((m - 2) as real) * c + c == ((m - 1) as real) * c) by(nonlinear_arith);
    }
}

/// the position credit `n/(n+k+1)` is
/// average of the `rand (n+1)` allocation `(n+1)/(n+k+1)` over `{0,…,n}`.
pub proof fn lemma_spline_avg(n: nat, k: nat)
    ensures average_nat((n + 1) as nat, spline_alloc(n, k)) == spline_credit(n, k),
{
    lemma_spline_sum(n, k, (n + 1) as nat);   // sum = n·(n+1)/(n+k+1)
    // average = sum / (n+1) = n/(n+k+1)
    assert(average_nat((n + 1) as nat, spline_alloc(n, k))
        == sum_credit(spline_alloc(n, k), (n + 1) as nat) / ((n + 1) as real));
    assert(average_nat((n + 1) as nat, spline_alloc(n, k)) == spline_credit(n, k))
        by(nonlinear_arith)
        requires
            average_nat((n + 1) as nat, spline_alloc(n, k))
                == sum_credit(spline_alloc(n, k), (n + 1) as nat) / ((n + 1) as real),
            sum_credit(spline_alloc(n, k), (n + 1) as nat)
                == (n as real) * ((n + 1) as real / ((n + k + 1) as real)),
            spline_credit(n, k) == (n as real) / ((n + k + 1) as real);
}

/// For `k` large enough (`k ≥ n/ε`), the position credit `n/(n+k+1)` drops below `ε > 0`
pub proof fn lemma_spline_credit_le(n: nat, k: nat, eps: real)
    requires eps > 0real, nat_to_real(k) >= (n as real) / eps,
    ensures spline_credit(n, k) <= eps,
{
    assert(spline_credit(n, k) <= eps) by(nonlinear_arith)
        requires
            eps > 0real,
            nat_to_real(k) == k as real,
            (k as real) >= (n as real) / eps,
            spline_credit(n, k) == (n as real) / ((n + k + 1) as real);
}

// ∀ n. [ ↯( n/(n+k+1) )] spline n [ True ]
pub fn spline_aux(n: &UBig, Ghost(k): Ghost<nat>, Tracked(credit): Tracked<ErrorCreditResource>)
    requires
        credit.view() =~= (ErrorCreditCarrier::Value { car: spline_credit(ubig_view(n), k) }),
    decreases k,
{
    let ghost nv = ubig_view(n);           // current position value
    let n1 = ubig_succ(n.clone());         // n+1  (ubig_view(&n1) == nv + 1)
    let ghost alloc = spline_alloc(nv, k);
    proof {
        lemma_spline_avg(nv, k);           // average_nat(nv+1, alloc) == spline_credit(nv,k)
        assert forall |i: nat| (#[trigger] alloc(i as real)) >= 0real by {
            // each value is 0 or (nv+1)/(nv+k+1) ≥ 0
            assert((nv + 1) as real / ((nv + k + 1) as real) >= 0real) by(nonlinear_arith);
        }
    }

    let (x, Tracked(out)) = rand_ubig(&n1, Tracked(credit), Ghost(alloc));

    if ubig_is_zero(&x) {
    } else {

        proof {
            assert(ubig_view(&x) >= 1);
            assert(alloc(ubig_view(&x) as real) == (nv + 1) as real / ((nv + k + 1) as real));
            if k == 0 {
                assert((nv + 1) as real / ((nv + 0 + 1) as real) == 1real) by(nonlinear_arith);
                ec_contradict(&out);
            }
            assert((nv + 1) as real / ((nv + k + 1) as real)
                == spline_credit(ubig_view(&n1), (k - 1) as nat));
        }
        spline_aux(&n1, Ghost((k - 1) as nat), Tracked(out));
    }
}

pub fn spline(n: u64) {
    let Tracked(cred) = thin_air();
    let n_big = ubig_from_u64(n);
    let ghost eps: real;
    let ghost k: nat;
    proof {
        eps = choose |v: real| v > 0real && cred.view() =~= (ErrorCreditCarrier::Value { car: v });
        let n1 = ubig_view(&n_big);
        // pick k ≥ n/ε  (Archimedean), so spline_credit(n,k) ≤ ε.
        assert((n1 as real) / eps >= 0real) by(nonlinear_arith) requires eps > 0real;
        archimedean_nat((n1 as real) / eps);
        k = choose |j: nat| nat_to_real(j) >= (n1 as real) / eps;
        lemma_spline_credit_le(n1, k, eps);
    }

    // Peel the thin-air credit down to exactly spline_credit(n,k) (discard the rest).
    let tracked aux_cred;
    proof {
        let n1 = ubig_view(&n_big);
        let sc = spline_credit(n1, k);
        assert(sc >= 0real) by(nonlinear_arith) requires sc == (n1 as real) / ((n1 + k + 1) as real);
        let tracked (a, _rest) = ec_split(cred, sc, eps - sc);
        aux_cred = a;
    }

    spline_aux(&n_big, Ghost(k), Tracked(aux_cred));
}

} // verus!
