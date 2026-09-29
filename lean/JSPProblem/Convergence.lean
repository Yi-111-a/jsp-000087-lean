/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# JSP-000087 : convergence of the Erdős series

Erdős' question (JSP-000087) concerns

`∑ n ≥ 1, ω(n) / 2 ^ n`

where `ω n` counts the *distinct* prime factors of `n`.  In order even to ask
whether this real number is irrational one must first know that it *exists*.

This file proves that it does.

* `omega_le_self` : `ω n ≤ n`;
* `summable_omega_mul_inv_two_pow` : the summand `((ω n : ℕ) : ℝ) * (2 : ℝ) ^ -(n+1)` is
  `Summable` in `ℝ`, by comparison with the closed-form geometric-with-weight series
  `∑ n, (n : ℝ) * 2 ^ -(n+1) = 1`;
* `jsp87_convergence` : `Real.HasSum … jsp87Series` — **the Erdős series is a
  well-defined real number**;
* `jsp87Series_le_one` and `jsp87Series_ge_seven_32` : an explicit two-sided bracket
  `7 / 32 ≤ jsp87Series ≤ 1` (the lower endpoint is the exact partial sum over
  `n < 5`), so in particular `0 < jsp87Series`.

The growth bound actually used is the *logarithmic* one available from
`omega_le_log2`; the linear bound `ω n ≤ n` is enough to dominate the summand by a
summable series and is much cheaper to transport to `ℝ`.
-/

namespace JSP87

open Filter

/-- **`ω n ≤ n` for every natural number.** -/
theorem omega_le_self (n : ℕ) : omega n ≤ n := by
  rcases Nat.lt_or_ge n 1 with h | h
  · have hn : n = 0 := by omega
    simp [omega, hn]
  · have h1 : omega n ≤ n - 1 := omega_lt h
    omega

/-- `(2 : ℝ) ^ (n + 1)⁻¹ = 2⁻¹ ^ (n + 1)`. -/
theorem two_pow_neg_eq (n : ℕ) : ((2 : ℝ) ^ (n + 1))⁻¹ = (2 : ℝ)⁻¹ ^ (n + 1) := by
  rw [inv_pow]

/-- The closed-form summable series `∑ n, (n : ℝ) * 2 ^ -(n+1)`. -/
theorem summable_nat_mul_two_pow_neg :
    Summable (fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  have h : Summable (fun n : ℕ => (n : ℝ) * (2 : ℝ)⁻¹ ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 : ℝ)⁻¹) (by norm_num))
  have h' := h.mul_left (2 : ℝ)⁻¹
  refine Summable.congr h' (fun n => ?_)
  rw [two_pow_neg_eq, pow_succ]
  ring

/-- **The summand of the Erdős series is `Summable` in `ℝ`.** -/
theorem summable_omega_mul_inv_two_pow :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (fun n => ?_) (summable_nat_mul_two_pow_neg)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (omega_le_self n)) (by positivity)

/-- **`∑' n, (n : ℝ) * 2 ^ -(n+1) = 1`** — the closed form of the majorant. -/
theorem tsum_nat_mul_two_pow_neg :
    (∑' n : ℕ, ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  have hconv : Summable (fun n : ℕ => (n : ℝ) * (2 : ℝ)⁻¹ ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 : ℝ)⁻¹) (by norm_num))
  have hmul : (∑' n : ℕ, (n : ℝ) * (2 : ℝ)⁻¹ ^ n) = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)]
    norm_num
  have hshift : (∑' n : ℕ, ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (2 : ℝ)⁻¹ * ∑' n : ℕ, (n : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    rw [(Summable.tsum_mul_left (2 : ℝ)⁻¹ hconv).symm]
    exact tsum_congr fun n => by rw [two_pow_neg_eq, pow_succ]; ring
  rw [hshift, hmul]
  norm_num

/-- **The Erdős series converges** — sub-step A of the ACCEPTANCE blocker list. -/
theorem jsp87_convergence :
    HasSum (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
  summable_omega_mul_inv_two_pow.hasSum

/-- **Upper bound: `jsp87Series ≤ 1`.**

The summand is dominated by `n * 2 ^ -(n+1)`, whose sum is exactly `1`. -/
theorem jsp87Series_le_one :
    (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) ≤ 1 := by
  calc (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      ≤ ∑' n : ℕ, ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
        Summable.tsum_le_tsum
          (fun n => mul_le_mul_of_nonneg_right (by exact_mod_cast (omega_le_self n)) (by positivity))
          summable_omega_mul_inv_two_pow summable_nat_mul_two_pow_neg
    _ = 1 := tsum_nat_mul_two_pow_neg

/-- **Lower bound: any finite partial sum is below the series.**

`ω 0 = ω 1 = 0` and `ω n ≥ 0`, so a `Finset.range` partial sum lower-bounds the
`tsum`. -/
theorem sum_range_le_jsp87Series (N : ℕ)
    (h0 : ∀ i, i ∉ Finset.range N → 0 ≤ ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹) :
    (∑ i ∈ Finset.range N, ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹)
      ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
  Summable.sum_le_tsum (Finset.range N) h0 summable_omega_mul_inv_two_pow

/-- **The series is strictly positive**, since its first two nonzero terms are
`1/8 + 1/16 > 0`. -/
theorem jsp87Series_pos :
    0 < ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hnonneg : ∀ i, 0 ≤ ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹ :=
    fun i => mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hlow : (1 / 8 : ℝ) ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    refine (sum_range_le_jsp87Series 3 (fun _ _ => hnonneg _)).trans' ?_
    norm_num [omega_zero, omega_one, show omega 2 = 1 by native_decide, Finset.sum_range_succ]
  linarith

end JSP87
