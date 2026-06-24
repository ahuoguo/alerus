/-
Verification of the Verus axiom `axiom_exp_taylor_bounds` in Lean 4.

For x ∈ (0, 1] and n ≥ 1, the partial sum T_n = Σ_{k < n} (-x)^k / k! satisfies:
  1. 0 ≤ T_n
  2. T_n ≤ 1
  3. n even → T_n ≤ exp(-x)
  4. n odd  → exp(-x) ≤ T_n

Strategy: Show even partial sums are monotone increasing to exp(-x) and odd
partial sums are monotone decreasing to exp(-x), via the alternating series
structure and absolute convergence of the exponential series.
-/
import Mathlib

open Finset Real BigOperators Filter

noncomputable section

/-! ## Definitions -/

/-- Partial sum T_n(x) = Σ_{k < n} (-x)^k / k!.
    Matches Verus `partial_sum(exp_taylor_seq(x), n)`. -/
def T (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-x) ^ k / (Nat.factorial k : ℝ)

/-- Absolute value of the k-th Taylor term: x^k / k! -/
def expAbsTerm (x : ℝ) (k : ℕ) : ℝ := x ^ k / (Nat.factorial k : ℝ)

/-! ## Basic properties of T -/

@[simp] lemma T_zero (x : ℝ) : T x 0 = 0 := by simp [T]

@[simp] lemma T_one (x : ℝ) : T x 1 = 1 := by simp [T, Nat.factorial]

lemma T_succ (x : ℝ) (n : ℕ) :
    T x (n + 1) = T x n + (-x) ^ n / (Nat.factorial n : ℝ) := by
  simp only [T, Finset.sum_range_succ]

/-! ## Properties of absolute terms -/

lemma expAbsTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ expAbsTerm x k := by
  unfold expAbsTerm; positivity

/-- Terms decrease for x ∈ [0, 1]. -/
lemma expAbsTerm_succ_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    expAbsTerm x (k + 1) ≤ expAbsTerm x k := by
  have hrel : expAbsTerm x (k + 1) = expAbsTerm x k * (x / (↑(k + 1) : ℝ)) := by
    simp only [expAbsTerm, pow_succ, Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hrel]
  exact mul_le_of_le_one_right (expAbsTerm_nonneg hx0 k)
    (div_le_one_of_le₀ (le_trans hx1 (by exact_mod_cast Nat.le_add_left 1 k))
      (by positivity))

/-! ## Relating T to expAbsTerm -/

/-- T(n+1) = T(n) + (-1)^n · expAbsTerm(n). -/
lemma T_succ_a (x : ℝ) (n : ℕ) :
    T x (n + 1) = T x n + (-1) ^ n * expAbsTerm x n := by
  rw [T_succ]; unfold expAbsTerm
  congr 1
  rw [show (-x) ^ n = (-1 : ℝ) ^ n * x ^ n from by rw [← neg_one_mul, mul_pow]]
  ring

/-- Two-step difference: T(n+2) - T(n) = (-1)^n · (expAbsTerm(n) - expAbsTerm(n+1)). -/
lemma T_two_step (x : ℝ) (n : ℕ) :
    T x (n + 2) - T x n = (-1) ^ n * (expAbsTerm x n - expAbsTerm x (n + 1)) := by
  have h1 := T_succ_a x (n + 1)
  have h2 := T_succ_a x n
  have hpow : (-1 : ℝ) ^ (n + 1) = -((-1) ^ n) := by rw [pow_succ]; ring
  rw [hpow] at h1
  -- h1 : T x (n + 2) = T x (n + 1) + -((-1)^n) * expAbsTerm x (n + 1)
  -- h2 : T x (n + 1) = T x n + (-1)^n * expAbsTerm x n
  have hmul := mul_sub ((-1 : ℝ) ^ n) (expAbsTerm x n) (expAbsTerm x (n + 1))
  -- hmul : distributivity of (-1)^n over the difference
  linarith

/-! ## Convergence -/

/-- The Taylor series for exp(y) has sum exp(y). -/
lemma hasSum_exp_real (y : ℝ) :
    HasSum (fun n => y ^ n / (Nat.factorial n : ℝ)) (exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

/-- Partial sums T(x, ·) converge to exp(-x). -/
lemma T_tendsto (x : ℝ) :
    Tendsto (T x) atTop (nhds (exp (-x))) := by
  have h := (hasSum_exp_real (-x)).tendsto_sum_nat
  exact h.congr (fun n => by simp only [T])

/-- Even subsequence tends to exp(-x). -/
lemma tendsto_T_even (x : ℝ) :
    Tendsto (fun m => T x (2 * m)) atTop (nhds (exp (-x))) :=
  (T_tendsto x).comp
    (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) (fun n => ⟨n, by omega⟩))

/-- Odd subsequence tends to exp(-x). -/
lemma tendsto_T_odd (x : ℝ) :
    Tendsto (fun m => T x (2 * m + 1)) atTop (nhds (exp (-x))) :=
  (T_tendsto x).comp
    (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) (fun n => ⟨n, by omega⟩))

/-! ## Monotonicity of even/odd subsequences -/

/-- One-step even monotonicity: T(2m) ≤ T(2m+2). -/
lemma T_even_step {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    T x (2 * m) ≤ T x (2 * m + 2) := by
  have h := T_two_step x (2 * m)
  have hsgn : (-1 : ℝ) ^ (2 * m) = 1 := by
    exact Even.neg_one_pow ⟨m, by omega⟩
  have ha := expAbsTerm_succ_le hx0 hx1 (2 * m)
  nlinarith

/-- One-step odd antitonicity: T(2m+3) ≤ T(2m+1). -/
lemma T_odd_step {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    T x (2 * (m + 1) + 1) ≤ T x (2 * m + 1) := by
  have hrw : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
  rw [hrw]
  have h := T_two_step x (2 * m + 1)
  have hsgn : (-1 : ℝ) ^ (2 * m + 1) = -1 :=
    Odd.neg_one_pow ⟨m, rfl⟩
  have ha := expAbsTerm_succ_le hx0 hx1 (2 * m + 1)
  nlinarith

/-- Even partial sums form a monotone sequence. -/
lemma monotone_T_even {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Monotone (fun m => T x (2 * m)) :=
  monotone_nat_of_le_succ fun m => by
    rw [show 2 * (m + 1) = 2 * m + 2 from by omega]
    exact T_even_step hx0 hx1 m

/-- Odd partial sums form an antitone sequence. -/
lemma antitone_T_odd {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun m => T x (2 * m + 1)) :=
  antitone_nat_of_succ_le fun m => T_odd_step hx0 hx1 m

/-! ## Main alternating bounds (Properties 3 & 4) -/

/-- **Property 3**: Even partial sums underestimate exp(-x). -/
theorem T_even_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    T x (2 * m) ≤ exp (-x) :=
  (monotone_T_even hx0 hx1).ge_of_tendsto (tendsto_T_even x) m

/-- **Property 4**: Odd partial sums overestimate exp(-x). -/
theorem exp_le_T_odd {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    exp (-x) ≤ T x (2 * m + 1) :=
  (antitone_T_odd hx0 hx1).le_of_tendsto (tendsto_T_odd x) m

/-! ## Bounds in [0, 1] (Properties 1 & 2) -/

/-- **Property 1**: Partial sum is non-negative. -/
theorem T_nonneg {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ℕ} (_hn : 1 ≤ n) :
    0 ≤ T x n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm' : n = 2 * m := by omega
    rw [hm']
    calc (0 : ℝ) = T x (2 * 0) := by simp
      _ ≤ T x (2 * m) := monotone_T_even hx0.le hx1 (Nat.zero_le m)
  · have hm' : n = 2 * m + 1 := by omega
    rw [hm']
    exact le_trans (le_of_lt (exp_pos (-x))) (exp_le_T_odd hx0.le hx1 m)

/-- **Property 2**: Partial sum is at most 1. -/
theorem T_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ℕ} (_hn : 1 ≤ n) :
    T x n ≤ 1 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm' : n = 2 * m := by omega
    rw [hm']
    exact le_trans (T_even_le_exp hx0.le hx1 m)
      (exp_le_one_iff.mpr (neg_nonpos.mpr hx0.le))
  · have hm' : n = 2 * m + 1 := by omega
    rw [hm']
    calc T x (2 * m + 1)
        ≤ T x (2 * 0 + 1) := antitone_T_odd hx0.le hx1 (Nat.zero_le m)
      _ = 1 := by simp

/-! ## Main theorem -/

/-- **Verification of Verus axiom `axiom_exp_taylor_bounds`.**

For x ∈ (0, 1] and n ≥ 1, the Taylor partial sum T_n(x) = Σ_{k < n} (-x)^k / k! satisfies:
  - 0 ≤ T_n(x)
  - T_n(x) ≤ 1
  - n even → T_n(x) ≤ exp(-x)
  - n odd  → exp(-x) ≤ T_n(x) -/
theorem exp_taylor_bounds {x : ℝ} {n : ℕ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hn : 1 ≤ n) :
    0 ≤ T x n ∧
    T x n ≤ 1 ∧
    (n % 2 = 0 → T x n ≤ exp (-x)) ∧
    (n % 2 = 1 → exp (-x) ≤ T x n) := by
  refine ⟨T_nonneg hx0 hx1 hn, T_le_one hx0 hx1 hn, fun heven => ?_, fun hodd => ?_⟩
  · have hm : n = 2 * (n / 2) := by omega
    rw [hm]; exact T_even_le_exp hx0.le hx1 _
  · have hm : n = 2 * (n / 2) + 1 := by omega
    rw [hm]; exact exp_le_T_odd hx0.le hx1 _

end
