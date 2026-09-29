/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertIdentity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic

/-!
# JSP-000087 : the Diophantine scaffold of the Erdős–Pratt argument

Erdős' proof that the *unrestricted* Lambert series `∑ n ≥ 1, 1 / (2^n - 1)` is
irrational (J. Indian Math. Soc. **12** (1948), 63–66), and Pratt's adaptation of
it to the *prime-restricted* series `∑ p, 1 / (2^p - 1)` (arXiv:2409.15185), rest
on the same two elementary devices.

**1. The carry decomposition.**  Multiplying the Erdős series by `2 ^ N` pushes a
finite *integer* part in front of a *carry* term which is a weighted average of
`ω` just after the cut point:

`2 ^ N · ∑ n ω(n) 2^-(n+1)  =  I N  +  2 ^ N · τ N`,

with the integer `I N = ∑ n < N ω(n) 2^(N-n-1)` and the tail
`τ N = ∑' k, ω(N+k) 2^-(N+k+1)`.

**2. The denominator obstruction.**  If the series were the rational `a / b` then,
by the carry decomposition, *every* carry `2 ^ N · τ N` would be a rational whose
denominator divides `b` — uniformly in `N`.  Rationality therefore freezes the
carries into the fixed lattice `(1/b) ℤ`, while the arithmetic of the Lambert
denominators `2 ^ p - 1` (prime `p`) forces ever larger prime divisors to appear.

This file formalises device 1 completely and unconditionally, states device 2 as
a general lemma, and proves the arithmetic fact the second half of device 2 rests
on: **for prime `p`, every prime factor of `2 ^ p - 1` exceeds `p`**, hence
`2 ^ p - 1` is divisible by no product of primes `≤ p`.

## Main results

* `hasSum_jsp87Tail`, `jsp87Tail_nonneg`, `jsp87Tail_pos`, `jsp87Tail_le` — the
  carry tail `τ N` exists, is positive for `1 ≤ N`, and satisfies
  `0 < τ N ≤ (N+1) · 2^-N`;
* `jsp87_series_eq_sum_add_tail` — `S = ∑ n<N ω(n) 2^-(n+1) + τ N`;
* `jsp87_sum_range_eq_intPart` and `jsp87_scaled_decomposition` — the carry
  decomposition `2 ^ N · S = I N + 2 ^ N · τ N` with `I N ∈ ℤ`;
* `jsp87_carry_mul_eq_int` — if `S = a / b` with `b > 0` then
  `b · 2^N · τ N ∈ ℤ`: the denominator obstruction, with `b` fixed;
* `jsp87_carry_ge_inv` — consequently a positive carry is `≥ 1/b`;
* `jsp87_carry_bounds` — quantitatively `0 < 2^N · τ N ≤ N + 1`;
* `pow_two_eq_one_of_dvd`, `two_ne_zero_of_ne_two`, `dvd_sub_one_prime_gt`,
  `two_pow_sub_one_prime_gross`, `primeFactors_sub_one_gt`,
  `prod_primes_le_not_dvd` — the Lambert denominator arithmetic: for prime `p`,
  `2 ^ p - 1` is `p`-rough.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The carry tail -/

/-- **The carry tail** of the Erdős series after the index `N`:
`τ N = ∑' k, ω(N + k) 2^-(N+k+1)`. -/
noncomputable def jsp87Tail (N : ℕ) : ℝ := ∑' k : ℕ, jsp87Term (N + k)

/-- Each summand of the carry tail is nonnegative. -/
theorem jsp87Tail_term_nonneg (N k : ℕ) : 0 ≤ jsp87Term (N + k) :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The carry tail is a summable series, by reindexing the summable Erdős series. -/
theorem summable_jsp87Tail (N : ℕ) : Summable (fun k : ℕ => jsp87Term (N + k)) := by
  have hj : Summable jsp87Term := summable_omega_mul_inv_two_pow
  have h1 : Summable (fun k : ℕ => jsp87Term (k + N)) :=
    (summable_nat_add_iff (f := jsp87Term) N).2 hj
  exact h1.congr fun k => by rw [Nat.add_comm]

/-- **The carry tail is a convergent series, with closed-form value `τ N`.** -/
theorem hasSum_jsp87Tail (N : ℕ) : HasSum (fun k : ℕ => jsp87Term (N + k)) (jsp87Tail N) :=
  (summable_jsp87Tail N).hasSum

/-- `0 ≤ τ N`. -/
theorem jsp87Tail_nonneg (N : ℕ) : 0 ≤ jsp87Tail N :=
  tsum_nonneg (jsp87Tail_term_nonneg N)

/-- **The Erdős series splits into its partial sums and its carry tail.** -/
theorem jsp87_series_eq_sum_add_tail (N : ℕ) :
    jsp87Series = (∑ i ∈ Finset.range N, jsp87Term i) + jsp87Tail N := by
  have h := summable_omega_mul_inv_two_pow.sum_add_tsum_nat_add N
  have htail : (∑' k : ℕ, ((omega (k + N) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + N + 1))⁻¹)
      = jsp87Tail N := by
    unfold jsp87Tail
    refine tsum_congr fun k => ?_
    have h1 : k + N = N + k := Nat.add_comm k N
    have h2 : k + N + 1 = N + k + 1 := by omega
    simp only [jsp87Term, h1]
  calc jsp87Series
      = ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := rfl
    _ = (∑ i ∈ Finset.range N, ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹)
        + ∑' k : ℕ, ((omega (k + N) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + N + 1))⁻¹ := h.symm
    _ = (∑ i ∈ Finset.range N, jsp87Term i) + jsp87Tail N := by rw [htail]; rfl

/-- `‖2⁻¹‖ < 1`. -/
theorem norm_inv_two_lt_one : ‖(2 : ℝ)⁻¹‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
  norm_num

/-- The geometric series `∑' k, (2⁻¹)^k` is summable. -/
theorem summable_inv_two_pow : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) :=
  (hasSum_geometric_of_norm_lt_one norm_inv_two_lt_one).summable

/-- `∑' k, (2⁻¹)^k = 2`. -/
theorem tsum_inv_two_pow : (∑' k : ℕ, (2 : ℝ)⁻¹ ^ k) = 2 := by
  rw [tsum_geometric_of_norm_lt_one norm_inv_two_lt_one]
  norm_num

/-- The series `∑' k, k · (2⁻¹)^k` is summable. -/
theorem summable_nat_mul_inv_two_pow : Summable (fun k : ℕ => (k : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
  simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 : ℝ)⁻¹) (by norm_num))

/-- `∑' k, k · (2⁻¹)^k = 2`. -/
theorem tsum_nat_mul_inv_two_pow : (∑' k : ℕ, (k : ℝ) * (2 : ℝ)⁻¹ ^ k) = 2 := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one norm_inv_two_lt_one]
  norm_num

/-- `(2⁻¹)^r ≤ 1` for every `r`. -/
theorem inv_two_pow_le_one (r : ℕ) : (2 : ℝ)⁻¹ ^ r ≤ (1 : ℝ) := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  have h1 : (2 : ℝ)⁻¹ ≤ (1 : ℝ) := by norm_num
  exact pow_le_one₀ h0 h1

/-- `1 ≤ 2 ^ k` for every `k`. -/
theorem one_le_two_pow (k : ℕ) : 1 ≤ (2 : ℕ) ^ k := by
  induction k with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; nlinarith [ih]

/-- `2^-(m+1) ≤ 1`. -/
theorem two_pow_neg_le_one (m : ℕ) : ((2 : ℝ) ^ (m + 1))⁻¹ ≤ (1 : ℝ) := by
  have h : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  calc ((2 : ℝ) ^ (m + 1))⁻¹ = 1 / (2 : ℝ) ^ (m + 1) := by
        rw [div_eq_mul_inv, one_mul]
    _ ≤ (1 : ℝ) := (div_le_one h).mpr (by exact_mod_cast one_le_two_pow (m + 1))

/-- The inverse power reindexing: `2^-(N+j+1) = 2^-(N+1) · 2^-j`. -/
theorem two_pow_neg_reindex (N j : ℕ) :
    ((2 : ℝ) ^ (N + j + 1))⁻¹ = ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ j := by
  have hN : N + j + 1 = (N + 1) + j := by omega
  rw [hN, pow_add, DivisionMonoid.mul_inv_rev, inv_pow, mul_comm]

/-- **Shifted inverse powers are bounded by unshifted ones: `2^-(N+j+1) ≤ 2^-j`.** -/
theorem two_pow_neg_le (N j : ℕ) : ((2 : ℝ) ^ (N + j + 1))⁻¹ ≤ (2 : ℝ)⁻¹ ^ j := by
  have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ j := by positivity
  calc ((2 : ℝ) ^ (N + j + 1))⁻¹
      = ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ j := two_pow_neg_reindex N j
    _ ≤ (1 : ℝ) * (2 : ℝ)⁻¹ ^ j := mul_le_mul_of_nonneg_right (two_pow_neg_le_one N) hp
    _ = (2 : ℝ)⁻¹ ^ j := one_mul _

/-- The shifted majorant `∑' k, (N+k) 2^-(N+k+1)` is summable. -/
theorem summable_shift_nat_mul_two_pow_neg (N : ℕ) :
    Summable (fun k : ℕ => ((N + k : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹) := by
  have hsplit : Summable (fun k : ℕ => (N : ℝ) * (2 : ℝ)⁻¹ ^ k + (k : ℝ) * (2 : ℝ)⁻¹ ^ k) :=
    Summable.add (summable_inv_two_pow.mul_left (N : ℝ)) summable_nat_mul_inv_two_pow
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (fun k => ?_) hsplit
  calc ((N + k : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹
      ≤ ((N + k : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ k) :=
        mul_le_mul_of_nonneg_left (two_pow_neg_le N k) (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) * (2 : ℝ)⁻¹ ^ k + (k : ℝ) * (2 : ℝ)⁻¹ ^ k := by
        push_cast
        linarith

/-- **Closed form of the shifted majorant: `∑' k, (N+k) 2^-(N+k+1) = (N+1) 2^-N`.** -/
theorem tsum_shift_nat_mul_two_pow_neg (N : ℕ) :
    (∑' k : ℕ, ((N + k : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹)
      = ((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N)⁻¹ := by
  have hsplit : Summable (fun k : ℕ => (N : ℝ) * (2 : ℝ)⁻¹ ^ k + (k : ℝ) * (2 : ℝ)⁻¹ ^ k) :=
    Summable.add (summable_inv_two_pow.mul_left (N : ℝ)) summable_nat_mul_inv_two_pow
  have hconvN : Summable (fun k : ℕ => ((N + k : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : ℕ => (N : ℝ) * (2 : ℝ)⁻¹ ^ k + (k : ℝ) * (2 : ℝ)⁻¹ ^ k)
      (fun k => by positivity) (fun k => ?_) hsplit
    push_cast
    linarith
  have htsplit : (∑' k : ℕ, ((N + k : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k)
      = ∑' k : ℕ, ((N : ℝ) * (2 : ℝ)⁻¹ ^ k + (k : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
    refine tsum_congr fun k => ?_
    push_cast
    ring
  have htsplit' : (∑' k : ℕ, ((N + k : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k)
      = (∑' k : ℕ, (N : ℝ) * (2 : ℝ)⁻¹ ^ k) + (∑' k : ℕ, (k : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
    rw [← Summable.tsum_add (summable_inv_two_pow.mul_left (N : ℝ)) summable_nat_mul_inv_two_pow]
    exact htsplit
  have hfun : ∀ k : ℕ,
      ((N + k : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹
        = ((2 : ℝ) ^ (N + 1))⁻¹ * (((N + k : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
    intro k
    have h1 : ((2 : ℝ) ^ (N + k + 1))⁻¹
        = ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ k := two_pow_neg_reindex N k
    rw [h1]
    ring
  calc (∑' k : ℕ, ((N + k : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹)
      = ∑' k : ℕ, ((2 : ℝ) ^ (N + 1))⁻¹ * (((N + k : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k) :=
        tsum_congr fun k => hfun k
    _ = ((2 : ℝ) ^ (N + 1))⁻¹ * ∑' k : ℕ, (((N + k : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k) :=
      Summable.tsum_mul_left _ hconvN
    _ = ((2 : ℝ) ^ (N + 1))⁻¹
        * (∑' k : ℕ, (N : ℝ) * (2 : ℝ)⁻¹ ^ k + ∑' k : ℕ, (k : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
      rw [htsplit']
    _ = ((2 : ℝ) ^ (N + 1))⁻¹ * ((N : ℝ) * 2 + 2) := by
      rw [Summable.tsum_mul_left _ summable_inv_two_pow, tsum_inv_two_pow,
        tsum_nat_mul_inv_two_pow]
    _ = ((2 : ℝ) ^ (N + 1))⁻¹ * (2 * ((N + 1 : ℕ) : ℝ)) := by
      have hcast : ((N : ℝ) * 2 + 2 : ℝ) = 2 * ((N + 1 : ℕ) : ℝ) := by
        norm_cast
        ring
      rw [hcast]
    _ = ((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N)⁻¹ := by
      have h1 : ((2 : ℝ) ^ (N + 1))⁻¹ * 2 = ((2 : ℝ) ^ N)⁻¹ := by
        rw [pow_succ]
        field_simp
      rw [← mul_assoc, h1]
      ring

/-- **The carry tail is bounded: `τ N ≤ (N+1) 2^-N`.** -/
theorem jsp87Tail_le (N : ℕ) : jsp87Tail N ≤ ((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N)⁻¹ := by
  have hle : ∀ k : ℕ, jsp87Term (N + k)
      ≤ ((N + k : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹ := by
    intro k
    refine mul_le_mul_of_nonneg_right (by exact_mod_cast (omega_le_self (N + k))) ?_
    positivity
  rw [← tsum_shift_nat_mul_two_pow_neg N]
  exact Summable.tsum_le_tsum hle (summable_jsp87Tail N) (summable_shift_nat_mul_two_pow_neg N)

/-- **The carry tail is strictly positive for `1 ≤ N`.** -/
theorem jsp87Tail_pos {N : ℕ} (hN : 1 ≤ N) : 0 < jsp87Tail N := by
  have hle : (∑ i ∈ ({N} : Finset ℕ), jsp87Term (N + i)) ≤ jsp87Tail N := by
    show (∑ i ∈ ({N} : Finset ℕ), jsp87Term (N + i)) ≤ ∑' i : ℕ, jsp87Term (N + i)
    exact Summable.sum_le_tsum (s := ({N} : Finset ℕ)) (f := fun k : ℕ => jsp87Term (N + k))
      (fun k _ => jsp87Tail_term_nonneg N k) (summable_jsp87Tail N)
  have hω : 0 < omega (N + N) := by
    have hp : Nat.Prime 2 := by norm_num
    have hd : (2 : ℕ) ∣ N + N := by omega
    exact omega_pos_of_prime_dvd hp hd (by omega)
  have hterm : (0 : ℝ) < jsp87Term (N + N) :=
    mul_pos (by exact_mod_cast hω) (by positivity)
  have hlt : (0 : ℝ) < ∑ i ∈ ({N} : Finset ℕ), jsp87Term (N + i) := by simpa using hterm
  exact lt_of_lt_of_le hlt hle

/-! ## 2. The integer part, and the carry decomposition -/

/-- `2 ≤ 2 ^ p` as soon as `p ≥ 1`. -/
theorem two_pow_ge_two_of_pos {p : ℕ} (hp : 1 ≤ p) : 2 ≤ 2 ^ p := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [pow_succ]
  nlinarith [one_le_two_pow k]

/-- **The integer part** `I N = ∑ n < N ω(n) 2^(N-n-1)`.  For `1 ≤ N` this is a
nonnegative integer: the exponents `N-n-1` are nonnegative on `n < N`. -/
noncomputable def jsp87IntPart (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, (omega n : ℤ) * 2 ^ (N - n - 1)

/-- `I N` is nonnegative. -/
theorem jsp87IntPart_nonneg (N : ℕ) : 0 ≤ jsp87IntPart N := by
  have h : ∀ n ∈ Finset.range N, 0 ≤ (omega n : ℤ) * 2 ^ (N - n - 1) := by
    intro n _
    exact Int.mul_nonneg (Int.natCast_nonneg _) (by positivity)
  exact Finset.sum_nonneg h

/-- The integer part, read in `ℝ`. -/
theorem jsp87IntPart_cast (N : ℕ) :
    (jsp87IntPart N : ℝ) = ∑ i ∈ Finset.range N, ((omega i : ℕ) : ℝ) * (2 : ℝ) ^ (N - i - 1) := by
  simp only [jsp87IntPart, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The reindexing identity `2^-(n+1) = 2^-N · 2^(N-n-1)`, in `ℝ`. -/
theorem two_pow_neg_eq_scaled (N i : ℕ) (hi : i < N) :
    ((2 : ℝ) ^ (i + 1))⁻¹ = ((2 : ℝ) ^ N)⁻¹ * (2 : ℝ) ^ (N - i - 1) := by
  have hN : N = (N - i - 1) + (i + 1) := by omega
  have hA : (2 : ℝ) ^ N = (2 : ℝ) ^ (N - i - 1) * (2 : ℝ) ^ (i + 1) :=
    (congrArg (fun m : ℕ => (2 : ℝ) ^ m) hN).trans (pow_add (2 : ℝ) (N - i - 1) (i + 1))
  have hz : (2 : ℝ) ^ (N - i - 1) ≠ 0 := by positivity
  calc ((2 : ℝ) ^ (i + 1))⁻¹
      = ((2 : ℝ) ^ (i + 1))⁻¹ * ((2 : ℝ) ^ (N - i - 1))⁻¹ * (2 : ℝ) ^ (N - i - 1) := by
        rw [mul_assoc]
        simp [hz]
    _ = ((2 : ℝ) ^ (N - i - 1) * (2 : ℝ) ^ (i + 1))⁻¹ * (2 : ℝ) ^ (N - i - 1) := by
        rw [DivisionMonoid.mul_inv_rev]
    _ = ((2 : ℝ) ^ N)⁻¹ * (2 : ℝ) ^ (N - i - 1) := by rw [← hA]

/-- **The partial sums of the Erdős series are the integer part divided by `2^N`.** -/
theorem jsp87_sum_range_eq_intPart (N : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range N, jsp87Term i) = ((2 : ℝ) ^ N)⁻¹ * (jsp87IntPart N : ℝ) := by
  have hterm : ∀ i ∈ Finset.range N,
      jsp87Term i = ((2 : ℝ) ^ N)⁻¹ * (((omega i : ℕ) : ℝ) * (2 : ℝ) ^ (N - i - 1)) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [jsp87Term, two_pow_neg_eq_scaled N i hi]
    ring
  calc (∑ i ∈ Finset.range N, jsp87Term i)
      = ((2 : ℝ) ^ N)⁻¹ * ∑ i ∈ Finset.range N, ((omega i : ℕ) : ℝ) * (2 : ℝ) ^ (N - i - 1) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    _ = ((2 : ℝ) ^ N)⁻¹ * (jsp87IntPart N : ℝ) := by rw [jsp87IntPart_cast]

/-- **The carry decomposition.**  For `1 ≤ N`,
`2^N · S = I N + 2^N · τ N`, with `I N` an integer. -/
theorem jsp87_scaled_decomposition (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N * jsp87Series
      = (jsp87IntPart N : ℝ) + (2 : ℝ) ^ N * jsp87Tail N := by
  rw [jsp87_series_eq_sum_add_tail N, jsp87_sum_range_eq_intPart N hN]
  have h1 : (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ = (1 : ℝ) := by field_simp
  rw [mul_add, ← mul_assoc, h1, one_mul]

/-! ## 3. The denominator obstruction -/

/-- **The denominator obstruction.**  If the Erdős series is the rational `a / b` with
`b > 0`, then every carry `2^N · τ N` is a rational whose denominator divides `b`,
*uniformly in `N`*.  This is the key rigidity statement of the Erdős argument: it
is exactly the property that rationality imposes on the tails. -/
theorem jsp87_carry_mul_eq_int {N : ℕ} (hN : 1 ≤ N) {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, (((2 : ℝ) ^ N) * jsp87Tail N) * (b : ℝ) = (c : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hdecomp := jsp87_scaled_decomposition N hN
  have hsplit : ((2 : ℝ) ^ N) * jsp87Tail N
      = (2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)) - (jsp87IntPart N : ℝ) := by
    rw [← h]
    linarith
  have hcast : (2 : ℝ) ^ N * (a : ℝ) = ((2 : ℕ) ^ N * a : ℤ) := by norm_cast
  refine ⟨(2 : ℕ) ^ N * a - b * jsp87IntPart N, ?_⟩
  rw [hsplit, sub_mul, ← mul_div_assoc, div_mul_cancel₀ _ hb0, hcast]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow]
  ring

/-- **A positive carry of a rational series is at least `1/b`.**  Together with
`jsp87_carry_bounds` this is the quantitative window the Erdős–Pratt argument
plays in. -/
theorem jsp87_carry_ge_inv {N : ℕ} (hN : 1 ≤ N) {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) (hc : 0 < ((2 : ℝ) ^ N) * jsp87Tail N) :
    (1 / (b : ℝ)) ≤ ((2 : ℝ) ^ N) * jsp87Tail N := by
  obtain ⟨c, hc'⟩ := jsp87_carry_mul_eq_int (N := N) hN hb h
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcp : (1 : ℤ) ≤ c := by
    have hpos' : (0 : ℝ) < 2 ^ N * jsp87Tail N * (b : ℝ) := mul_pos hc hbpos
    rw [hc'] at hpos'
    have hz : ((0 : ℤ) : ℝ) < (c : ℝ) := by simpa only [Int.cast_zero] using hpos'
    exact_mod_cast Int.lt_iff_add_one_le.mpr (Int.cast_lt.mp hz)
  have hkey : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcp
  calc (1 / (b : ℝ)) ≤ (c : ℝ) / (b : ℝ) :=
      div_le_div_of_nonneg_right hkey (by exact_mod_cast (le_of_lt hb))
    _ = (((2 : ℝ) ^ N) * jsp87Tail N) := by rw [← hc']; field_simp

/-- **Quantitative window for the carries: `0 < 2^N · τ N ≤ N + 1`.** -/
theorem jsp87_carry_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 < ((2 : ℝ) ^ N) * jsp87Tail N ∧ ((2 : ℝ) ^ N) * jsp87Tail N ≤ (N + 1 : ℕ) := by
  constructor
  · exact mul_pos (by positivity) (jsp87Tail_pos hN)
  · calc ((2 : ℝ) ^ N) * jsp87Tail N
        ≤ ((2 : ℝ) ^ N) * (((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N)⁻¹) :=
      mul_le_mul_of_nonneg_left (jsp87Tail_le N) (by positivity)
    _ = (N + 1 : ℕ) := by field_simp

/-! ## 4. The arithmetic of the Lambert denominators `2 ^ p - 1`

For the rest, `p` and `q` range over primes.  The engine is Fermat's little theorem
together with the multiplicative order of `2` in `ZMod q`. -/

/-- `2 ^ p = 1` in `ZMod q` whenever `q ∣ 2 ^ p - 1`. -/
theorem pow_two_eq_one_of_dvd {q p : ℕ} (hd : q ∣ 2 ^ p - 1) : (2 : ZMod q) ^ p = 1 := by
  have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hpos : 1 ≤ 2 ^ p := by
    cases p with
    | zero => norm_num
    | succ k => exact one_le_two_pow (k + 1)
  have hsub : ((2 ^ p - 1 : ℕ) : ZMod q) = ((2 ^ p : ℕ) : ZMod q) - 1 := by
    have e := Nat.cast_sub (R := ZMod q) hpos
    rw [Nat.cast_one] at e
    exact e
  have hmain : ((2 ^ p : ℕ) : ZMod q) = 1 := by
    rw [← sub_add_cancel (b := (1 : ZMod q)) ((2 ^ p : ℕ) : ZMod q), ← hsub, hz, zero_add]
  have hcast : (2 : ZMod q) ^ p = ((2 ^ p : ℕ) : ZMod q) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast]
  exact hmain

/-- `q` does not divide `2` when `2 ≤ q` and `q ≠ 2`. -/
theorem not_dvd_two {q : ℕ} (h2 : 2 ≤ q) (hq2 : q ≠ 2) : ¬ q ∣ 2 := by
  intro hd
  have hle : q ≤ 2 := Nat.le_of_dvd (by omega) hd
  omega

/-- `2` is a nonzero unit-like element in `ZMod q` when `q` is an odd prime. -/
theorem two_nat_ne_zero_mod {q : ℕ} (h2 : 2 ≤ q) (hq2 : q ≠ 2) : ((2 : ℕ) : ZMod q) ≠ 0 :=
  fun hz => not_dvd_two h2 hq2 ((ZMod.natCast_eq_zero_iff 2 q).mp hz)

/-- `2 ≠ 1` in `ZMod q` when `2 ≤ q` and `q ≠ 2`. -/
theorem two_nat_ne_one_mod {q : ℕ} (h2 : 2 ≤ q) (hq2 : q ≠ 2) : ((2 : ℕ) : ZMod q) ≠ 1 := by
  intro hz
  have hsub := Nat.cast_sub (R := ZMod q) (m := (1 : ℕ)) (n := 2) (by norm_num)
  have hzero1 : ((1 : ℕ) : ZMod q) = 0 := by
    calc ((1 : ℕ) : ZMod q) = ((2 - 1 : ℕ) : ZMod q) := by norm_num
      _ = ((2 : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) := hsub
      _ = 1 - 1 := by rw [hz, Nat.cast_one]
      _ = 0 := sub_self 1
  have hdvd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).mp hzero1
  have hle : q ≤ 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- `2 ≠ 1` in `ZMod q` when `2 ≤ q` and `q ≠ 2`. -/
theorem two_ne_one_of_ne_two {q : ℕ} (h2 : 2 ≤ q) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 1 := by
  intro hcon
  exact two_nat_ne_one_mod h2 hq2 hcon

/-- **`(2 : ZMod q) ≠ 0` whenever `q ≠ 2`.** -/
theorem two_ne_zero_of_ne_two {q : ℕ} (h2 : 2 ≤ q) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 :=
  two_nat_ne_zero_mod h2 hq2

/-- **Fermat: every prime divisor `q` of `2 ^ p - 1` (with `p` prime) is `≡ 1 (mod p)`.**

This is the arithmetic fact at the heart of the Erdős–Pratt denominator
obstruction: when `p` is prime, the denominators `2^p - 1` of the
prime-restricted Lambert series are divisible only by primes exceeding `p`. -/
theorem dvd_sub_one_prime_gt {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hodd : q ≠ 2)
    (hd : q ∣ 2 ^ p - 1) : p ∣ q - 1 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h2q : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hne : (2 : ZMod q) ≠ 0 := two_ne_zero_of_ne_two h2q hodd
  have htwo : (2 : ZMod q) ^ p = 1 := pow_two_eq_one_of_dvd hd
  have hdvdp : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one htwo
  have hfermat : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hdvdq : orderOf (2 : ZMod q) ∣ q - 1 := orderOf_dvd_of_pow_eq_one hfermat
  rcases (Nat.dvd_prime hp).mp hdvdp with h | h
  · exfalso
    exact (two_ne_one_of_ne_two h2q hodd) ((orderOf_eq_one_iff).mp h)
  · simpa [h] using hdvdq

/-- **`2 ^ p - 1` is odd, so `2 ∤ 2 ^ p - 1` for every `p ≥ 1`.** -/
theorem two_not_dvd_two_pow_sub_one {p : ℕ} (hp : 1 ≤ p) : ¬ (2 : ℕ) ∣ 2 ^ p - 1 := by
  intro hd
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have h2p : 2 ∣ 2 ^ (k + 1) := by
    rw [pow_succ]
    exact ⟨2 ^ k, by ring⟩
  rcases h2p with ⟨c1, hc1⟩
  rcases hd with ⟨c2, hc2⟩
  have hone : 1 ≤ 2 ^ (k + 1) := one_le_two_pow _
  omega

/-- **The Lambert denominators `2 ^ p - 1` for prime `p` are `p`-rough:**
no prime `q ≤ p` divides them. -/
theorem two_pow_sub_one_prime_gross {p : ℕ} (hp : p.Prime) {q : ℕ} (hq : q.Prime)
    (hqp : q ≤ p) : ¬ q ∣ 2 ^ p - 1 := by
  have h2q : 2 ≤ q := hq.two_le
  intro hc
  by_cases hq2 : q = 2
  · subst hq2
    exact two_not_dvd_two_pow_sub_one hp.one_le hc
  · have hq1 : 0 < q - 1 := by omega
    have hge : p ≤ q - 1 := Nat.le_of_dvd hq1 (dvd_sub_one_prime_gt hq hp hq2 hc)
    omega

/-- **For prime `p`, every prime factor of `2 ^ p - 1` strictly exceeds `p`.** -/
theorem primeFactors_sub_one_gt {p : ℕ} (hp : p.Prime) :
    ∀ q ∈ (2 ^ p - 1).primeFactors, p < q := by
  intro q hq
  obtain ⟨hqp, hqd, hne⟩ := Nat.mem_primeFactors.mp hq
  have hodd : q ≠ 2 := by
    intro hqc
    subst hqc
    exact two_not_dvd_two_pow_sub_one hp.one_le hqd
  have hge := dvd_sub_one_prime_gt hqp hp hodd hqd
  have h2q : 2 ≤ q := hqp.two_le
  have hq1 : 0 < q - 1 := by omega
  have hgt : p ≤ q - 1 := Nat.le_of_dvd hq1 hge
  omega

/-- **No product of primes `≤ p` divides `2 ^ p - 1`.**

This is the Erdős step in its sharpest form: the denominator `2^p - 1` of the
Lambert term attached to the prime `p` introduces prime divisors that no fixed
finite set of primes can produce. -/
theorem prod_primes_le_not_dvd {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (hsle : ∀ q ∈ s, q ≤ p) (hsne : s.Nonempty) :
    ¬ (∏ q ∈ s, q) ∣ 2 ^ p - 1 := by
  intro hd
  obtain ⟨q₀, hq₀⟩ := hsne
  have hq0p : q₀.Prime := hs q₀ hq₀
  have hq0le : q₀ ≤ p := hsle q₀ hq₀
  have hgross := two_pow_sub_one_prime_gross hp hq0p hq0le
  have hdvd0 : q₀ ∣ ∏ q ∈ s, q := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq₀
  exact hgross (hdvd0.trans hd)

end JSP87
