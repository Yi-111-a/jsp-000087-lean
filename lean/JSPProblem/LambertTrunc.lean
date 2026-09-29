/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertGcd

/-!
# JSP-000087 : the Lambert truncation and the clearing of denominators

`JSPProblem/LambertIdentity.lean` proved the reduction

`∑ n ≥ 1, ω(n) / 2 ^ n = ∑ p prime, 1 / (2 ^ p - 1)`,

and `JSPProblem/LambertGcd.lean` proved the arithmetic of the Lambert
denominators: distinct primes give coprime `2 ^ p - 1`, so the clearing
denominator of a truncation is the exact product `∏_{p<N} (2^p - 1)`, and no
product of primes `≤ p` divides `2 ^ p - 1`.  But the two halves had never been
*joined*.  Nothing in the tree said that **the clearing denominator of the
truncated Lambert sum is an exact `ℤ` multiplier** — that multiplying the
truncation by `∏_{p<N} (2^p - 1)` gives an integer, with nothing cancelling.  That
is the step on which every Erdős-style irrationality argument of this shape
rests, and it is what this file supplies.

## Main results

* `jsp87_lambertTerm`, `jsp87_lambertAll` — the Lambert summands and the full
  prime-restricted Lambert series, in exactly the form of `PROBLEM.md`;
* `jsp87_lambertAll_eq` — `∑' p prime, 1/(2^p - 1) = 2 · S`, in this notation;
* `jsp87_lambertTrunc`, `jsp87_lambertTail` — the truncation at `N` and the
  tail beyond `N`;
* `jsp87_lambert_decomp` — the splitting `2 · S = T N + R N`;
* `jsp87_lambertTrunc_mul_den` — **THE JOIN**: `lambertDen (range N) · T N` is an
  integer, i.e. the truncation is an exact rational whose denominator is the
  product of the `2^p - 1` and nothing cancels;
* `jsp87_lambertTail_pos`, `jsp87_lambertTail_le` — `0 < R N` and
  `R N ≤ 4 · 2^-N`: the tail is positive and exponentially small;
* `jsp87_lambert_rat_obstruction`, `jsp87_lambert_rat_ge_one`,
  `jsp87_lambert_window` — **if `2 · S = a / b` with `b > 0` then
  `b · lambertDen (range N) · R N` is a positive integer, hence `≥ 1`**, and it is
  simultaneously `≤ 4 · b · lambertDen (range N) · 2^-N`.  This is the
  *Lambert-side* denominator obstruction, the exact mirror image of
  `jsp87_carry_mul_eq_int` on the Erdős/carry side of `JSPProblem/Diophantine.lean`.

Mathlib has no Lambert-series truncation machinery of this shape, and none of
these statements.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The Lambert summand and the Lambert series -/

/-- The `j`-th summand of the prime-restricted Lambert series:
`1 / (2 ^ j - 1)` when `j` is prime, `0` otherwise. -/
noncomputable def jsp87_lambertTerm (j : ℕ) : ℝ := if j.Prime then ((2 : ℝ) ^ j - 1)⁻¹ else 0

/-- The full prime-restricted Lambert series `∑ p prime, 1 / (2 ^ p - 1)`. -/
noncomputable def jsp87_lambertAll : ℝ := ∑' j : ℕ, jsp87_lambertTerm j

/-- `2 ^ j - 1 > 0` for every `j`: every Lambert denominator is positive. -/
theorem two_pow_sub_one_pos {j : ℕ} (hj : 1 ≤ j) : 0 < (2 : ℝ) ^ j - 1 := by
  induction j with
  | zero => omega
  | succ k ih =>
    rw [pow_succ]
    have h1 : (1 : ℝ) ≤ 2 ^ k := by exact_mod_cast one_le_two_pow k
    linarith

/-- Each Lambert summand is nonnegative. -/
theorem jsp87_lambertTerm_nonneg (j : ℕ) : 0 ≤ jsp87_lambertTerm j := by
  by_cases hp : j.Prime
  · rw [jsp87_lambertTerm, if_pos hp]
    have h2j : 1 ≤ j := by have := hp.two_le; omega
    exact (inv_pos.mpr (two_pow_sub_one_pos h2j)).le
  · simp [jsp87_lambertTerm, hp]

/-- **The Lambert denominators dominate `2 · 2⁻ʲ`.**  For `1 ≤ p`,
`1 / (2 ^ p - 1) ≤ 2 · 2⁻ᵖ`, so the Lambert series is dominated by a geometric
series. -/
theorem jsp87_lambertTerm_le (j : ℕ) :
    jsp87_lambertTerm j ≤ 2 * ((2 : ℝ)⁻¹) ^ j := by
  by_cases hp : j.Prime
  · rw [jsp87_lambertTerm, if_pos hp]
    have h2ple : 2 ≤ j := hp.two_le
    have h1j : 1 ≤ j := by omega
    have hposA : (0 : ℝ) < (2 : ℝ) ^ j - 1 := by nlinarith [two_pow_gt_one h2ple]
    have hposB : (0 : ℝ) < (2 : ℝ) ^ (j - 1) := by positivity
    have hR : 2 * ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (j - 1))⁻¹ := by
      have h2j : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1) * 2 := by
        calc (2 : ℝ) ^ j = (2 : ℝ) ^ ((j - 1) + 1) := by congr 1; omega
          _ = 2 ^ (j - 1) * 2 := pow_succ _ _
      rw [h2j]
      field_simp
    rw [inv_pow, hR]
    exact (inv_le_inv₀ hposA hposB).mpr (two_pow_succ_le h1j)
  · rw [jsp87_lambertTerm, if_neg hp]
    positivity

/-- The Lambert series is summable. -/
theorem summable_jsp87_lambertTerm : Summable jsp87_lambertTerm :=
  Summable.of_nonneg_of_le jsp87_lambertTerm_nonneg jsp87_lambertTerm_le
    (summable_inv_two_pow.mul_left (2 : ℝ))

/-- **The Lambert series equals twice the Erdős series**, in the notation of this
file.  This is `jsp87_lambert_classic` of `JSPProblem/LambertIdentity.lean`. -/
theorem jsp87_lambertAll_eq : jsp87_lambertAll = 2 * jsp87Series := by
  show (∑' j : ℕ, (if j.Prime then ((2 : ℝ) ^ j - 1)⁻¹ else 0)) = 2 * jsp87Series
  exact jsp87_lambert_classic

/-! ## 2. Truncation and tail -/

/-- The **truncated Lambert sum** at `N`:
`T N = ∑ p < N prime, 1 / (2 ^ p - 1)`. -/
noncomputable def jsp87_lambertTrunc (N : ℕ) : ℝ := ∑ p ∈ Finset.range N, jsp87_lambertTerm p

/-- The **Lambert tail** beyond `N`:
`R N = ∑' i, 1 / (2 ^ (N+i) - 1)` over the primes `p ≥ N`. -/
noncomputable def jsp87_lambertTail (N : ℕ) : ℝ := ∑' i : ℕ, jsp87_lambertTerm (N + i)

/-- The integer numerator of the truncation over its clearing denominator. -/
noncomputable def jsp87_lambertNumer (N : ℕ) : ℕ :=
  ∑ p ∈ Finset.range N,
    if p.Prime then lambertDen (Finset.range N) / (2 ^ p - 1) else 0

/-- The truncated tail series is summable. -/
theorem summable_jsp87_lambertTail (N : ℕ) : Summable (fun i : ℕ => jsp87_lambertTerm (N + i)) := by
  have h1 : Summable (fun i : ℕ => jsp87_lambertTerm (i + N)) :=
    (summable_nat_add_iff (f := jsp87_lambertTerm) N).2 summable_jsp87_lambertTerm
  exact h1.congr fun i => by rw [Nat.add_comm]

/-- **THE SPLITTING: `2 · S = T N + R N`.**  The Lambert series splits at any
cut point `N` into the primes below `N` and the primes from `N` on. -/
theorem jsp87_lambert_decomp (N : ℕ) :
    jsp87_lambertAll = jsp87_lambertTrunc N + jsp87_lambertTail N := by
  have h := summable_jsp87_lambertTerm.sum_add_tsum_nat_add N
  have htrunc : (∑ i ∈ Finset.range N, jsp87_lambertTerm i) = jsp87_lambertTrunc N := rfl
  have htail : (∑' k : ℕ, jsp87_lambertTerm (k + N)) = jsp87_lambertTail N := by
    refine tsum_congr fun k => ?_
    congr 1
    omega
  rw [htrunc, htail] at h
  calc jsp87_lambertAll = ∑' i : ℕ, jsp87_lambertTerm i := rfl
    _ = jsp87_lambertTrunc N + jsp87_lambertTail N := h.symm

/-- The truncation is nonnegative. -/
theorem jsp87_lambertTrunc_nonneg (N : ℕ) : 0 ≤ jsp87_lambertTrunc N :=
  Finset.sum_nonneg fun p _ => jsp87_lambertTerm_nonneg p

/-- `0 ≤ R N`. -/
theorem jsp87_lambertTail_nonneg (N : ℕ) : 0 ≤ jsp87_lambertTail N :=
  tsum_nonneg fun i => jsp87_lambertTerm_nonneg (N + i)

/-- The truncation never exceeds the full Lambert series. -/
theorem jsp87_lambertTrunc_le_all (N : ℕ) : jsp87_lambertTrunc N ≤ jsp87_lambertAll := by
  rw [jsp87_lambert_decomp N]
  linarith [jsp87_lambertTail_nonneg N]

/-- **THE LAMBERT TAIL IS POSITIVE.**  There is a prime at or beyond every cut
point, so the tail of the Lambert series is never zero. -/
theorem jsp87_lambertTail_pos (N : ℕ) : 0 < jsp87_lambertTail N := by
  obtain ⟨u, hu, hup⟩ := Nat.exists_infinite_primes (N + 1)
  have hle : N ≤ u := by omega
  set i₀ : ℕ := u - N with hi₀
  have hi₀N : N + i₀ = u := by
    dsimp [i₀]
    omega
  have hsum : (∑ i ∈ ({i₀} : Finset ℕ), jsp87_lambertTerm (N + i)) ≤ jsp87_lambertTail N := by
    show (∑ i ∈ ({i₀} : Finset ℕ), jsp87_lambertTerm (N + i))
        ≤ ∑' i : ℕ, jsp87_lambertTerm (N + i)
    exact Summable.sum_le_tsum (s := ({i₀} : Finset ℕ))
      (f := fun k : ℕ => jsp87_lambertTerm (N + k))
      (fun k _ => jsp87_lambertTerm_nonneg (N + k)) (summable_jsp87_lambertTail N)
  have hone : (∑ i ∈ ({i₀} : Finset ℕ), jsp87_lambertTerm (N + i))
      = (1 : ℝ) / ((2 : ℝ) ^ u - 1) := by
    have h1 : (∑ i ∈ ({i₀} : Finset ℕ), jsp87_lambertTerm (N + i))
        = jsp87_lambertTerm (N + i₀) := by
      show (∑ i ∈ ({i₀} : Finset ℕ), jsp87_lambertTerm (N + i)) = jsp87_lambertTerm (N + i₀)
      simp
    rw [h1, hi₀N, jsp87_lambertTerm, if_pos hup, one_div]
  have h2u : 1 ≤ u := by have := hup.two_le; omega
  have hpos : (0 : ℝ) < (1 : ℝ) / ((2 : ℝ) ^ u - 1) := one_div_pos.mpr (two_pow_sub_one_pos h2u)
  exact lt_of_lt_of_le hpos (by rw [← hone]; exact hsum)

/-- The reindexed geometric majorant: `∑' i, 2 · 2^-(N+i) = 4 · 2⁻ᴺ`. -/
theorem tsum_two_mul_inv_two_pow_add (N : ℕ) :
    (∑' i : ℕ, (2 * ((2 : ℝ)⁻¹) ^ (N + i) : ℝ)) = 4 * ((2 : ℝ) ^ N)⁻¹ := by
  have h1 : (∑' i : ℕ, (2 * ((2 : ℝ)⁻¹) ^ (N + i) : ℝ))
      = (2 * ((2 : ℝ)⁻¹) ^ N * ∑' i : ℕ, ((2 : ℝ)⁻¹) ^ i : ℝ) := by
    calc (∑' i : ℕ, (2 * ((2 : ℝ)⁻¹) ^ (N + i) : ℝ))
        = ∑' i : ℕ, (2 * ((2 : ℝ)⁻¹) ^ N * ((2 : ℝ)⁻¹) ^ i : ℝ) := by
          refine tsum_congr (f := fun i : ℕ => (2 * ((2 : ℝ)⁻¹) ^ (N + i) : ℝ)) ?_
          intro i
          have heq : ((2 : ℝ)⁻¹) ^ (N + i) = ((2 : ℝ)⁻¹) ^ N * ((2 : ℝ)⁻¹) ^ i := by
            rw [← pow_add]
          rw [heq, mul_assoc]
    _ = 2 * ((2 : ℝ)⁻¹) ^ N * ∑' i : ℕ, ((2 : ℝ)⁻¹) ^ i := by
      rw [Summable.tsum_mul_left (2 * ((2 : ℝ)⁻¹) ^ N)
        (summable_inv_two_pow : Summable (fun i : ℕ => ((2 : ℝ)⁻¹) ^ i))]
  rw [h1, tsum_inv_two_pow]
  have hk : ((2 : ℝ)⁻¹) ^ N = ((2 : ℝ) ^ N)⁻¹ := inv_pow _ _
  rw [hk]
  ring

/-- **THE LAMBERT TAIL IS EXPONENTIALLY SMALL: `R N ≤ 4 · 2⁻ᴺ`.** -/
theorem jsp87_lambertTail_le (N : ℕ) : jsp87_lambertTail N ≤ 4 * ((2 : ℝ) ^ N)⁻¹ := by
  have hle : ∀ i : ℕ, jsp87_lambertTerm (N + i) ≤ 2 * ((2 : ℝ)⁻¹) ^ (N + i) := by
    intro i
    exact jsp87_lambertTerm_le (N + i)
  have hsumm : Summable (fun i : ℕ => 2 * ((2 : ℝ)⁻¹) ^ (N + i)) := by
    have hreindex : (fun i : ℕ => 2 * ((2 : ℝ)⁻¹) ^ (N + i))
        = (fun i : ℕ => (2 * ((2 : ℝ)⁻¹) ^ N) * ((2 : ℝ)⁻¹) ^ i) := by
      funext i
      have heq : (2 : ℝ)⁻¹ ^ (N + i) = (2 : ℝ)⁻¹ ^ N * (2 : ℝ)⁻¹ ^ i := by
        rw [← pow_add]
      rw [heq, mul_assoc]
    rw [hreindex]
    exact (summable_inv_two_pow.mul_left (2 * ((2 : ℝ)⁻¹) ^ N))
  calc jsp87_lambertTail N
      = ∑' i : ℕ, jsp87_lambertTerm (N + i) := rfl
    _ ≤ ∑' i : ℕ, 2 * ((2 : ℝ)⁻¹) ^ (N + i) :=
      Summable.tsum_le_tsum hle (summable_jsp87_lambertTail N) hsumm
    _ = 4 * ((2 : ℝ) ^ N)⁻¹ := tsum_two_mul_inv_two_pow_add N

/-! ## 3. THE JOIN: clearing the Lambert denominators -/

/-- **One prime step of the join.**  If `p` is a prime below `N`, then
multiplying its Lambert summand by the clearing denominator `D = ∏_{q<N} (2^q-1)`
gives the natural number `D / (2 ^ p - 1)`: the truncation is an exact rational
whose denominator is `D` and nothing cancels. -/
theorem jsp87_lambertTerm_mul_den {N p : ℕ} (hp : p.Prime) (hps : p < N) :
    jsp87_lambertTerm p * (lambertDen (Finset.range N) : ℝ) = ((lambertDen (Finset.range N) / (2 ^ p - 1 : ℕ) : ℕ) : ℝ) := by
  have hmem : p ∈ Finset.range N := Finset.mem_range.mpr hps
  obtain ⟨k, hk⟩ := lambertDen_mem_factor hp hmem
  have hD : (lambertDen (Finset.range N) : ℝ) = ((2 : ℝ) ^ p - 1) * (k : ℝ) := by
    have e1 : (lambertDen (Finset.range N) : ℝ) = (((2 ^ p - 1) * k : ℕ) : ℝ) := by
      rw [← hk]
    have h1p : (1 : ℕ) ≤ 2 ^ p := by
      have hh := succ_le_two_pow p
      omega
    have hcs : (((2 ^ p - 1 : ℕ) : ℕ) : ℝ) = ((2 : ℝ) ^ p - 1) := by
      have hh := Nat.cast_sub (R := ℝ) h1p
      simpa only [Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using hh
    have e2 : (((2 ^ p - 1) * k : ℕ) : ℝ) = ((2 : ℝ) ^ p - 1) * (k : ℝ) := by
      push_cast
      rw [hcs]
    rw [e1, e2]
  have hq : lambertDen (Finset.range N) / (2 ^ p - 1) = k := by
    have h2p : 2 ≤ p := hp.two_le
    have hpos : 0 < 2 ^ p - 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
      rw [pow_succ]
      have h1 := one_le_two_pow m
      omega
    have hk' : lambertDen (Finset.range N) = k * (2 ^ p - 1) := by rw [hk, mul_comm]
    rw [Nat.div_eq_of_eq_mul_left hpos hk']
  have h1p' : 1 ≤ p := by have := hp.two_le; omega
  have hz : (0 : ℝ) < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos h1p'
  rw [jsp87_lambertTerm, if_pos hp, hq, hD]
  field_simp

/-- **THE JOIN.**  Multiplying the truncated Lambert sum by its clearing
denominator gives an *integer*:

`lambertDen (range N) · ∑_{p<N prime} 1 / (2 ^ p - 1) ∈ ℤ`.

This is the statement that was missing between `JSPProblem/LambertIdentity.lean`
(the reduction) and `JSPProblem/LambertGcd.lean` (the denominator arithmetic).
It is exactly the integrality step an Erdős-style irrationality argument needs. -/
theorem jsp87_lambertTrunc_mul_num (N : ℕ) :
    jsp87_lambertTrunc N * (lambertDen (Finset.range N) : ℝ) = ((jsp87_lambertNumer N : ℕ) : ℝ) := by
  classical
  simp only [jsp87_lambertTrunc, jsp87_lambertNumer, Finset.sum_mul, Nat.cast_sum,
    Nat.cast_ite]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases hpp : p.Prime
  · rw [if_pos hpp, jsp87_lambertTerm, if_pos hpp]
    simpa [jsp87_lambertTerm, hpp, mul_comm] using
      (jsp87_lambertTerm_mul_den hpp (Finset.mem_range.mp hp))
  · simp [jsp87_lambertTerm, hpp]

/-- **THE JOIN.**  Multiplying the truncated Lambert sum by its clearing
denominator gives an *integer*:

`lambertDen (range N) · ∑_{p<N prime} 1 / (2 ^ p - 1) ∈ ℤ`.

This is the statement that was missing between `JSPProblem/LambertIdentity.lean`
(the reduction) and `JSPProblem/LambertGcd.lean` (the denominator arithmetic).
It is exactly the integrality step an Erdős-style irrationality argument needs. -/
theorem jsp87_lambertTrunc_mul_den (N : ℕ) :
    ∃ m : ℤ, jsp87_lambertTrunc N * (lambertDen (Finset.range N) : ℝ) = (m : ℝ) :=
  ⟨(jsp87_lambertNumer N : ℤ), by push_cast; exact jsp87_lambertTrunc_mul_num N⟩

/-- The numerator is nonnegative, so `T N` is a *nonnegative* rational over `D`. -/
theorem jsp87_lambertTrunc_eq_div (N : ℕ) :
    jsp87_lambertTrunc N = ((jsp87_lambertNumer N : ℕ) : ℝ) / (lambertDen (Finset.range N) : ℝ) := by
  have hmul := jsp87_lambertTrunc_mul_num N
  have hDpos : 0 < lambertDen (Finset.range N) := lambertDen_pos (Finset.range N)
  have hD0 : (0 : ℝ) ≠ (lambertDen (Finset.range N) : ℝ) := by
    have hh : (0 : ℝ) < (lambertDen (Finset.range N) : ℝ) := by exact_mod_cast hDpos
    exact Ne.symm hh.ne'
  symm
  calc ((jsp87_lambertNumer N : ℕ) : ℝ) / (lambertDen (Finset.range N) : ℝ)
      = (jsp87_lambertTrunc N * (lambertDen (Finset.range N) : ℝ))
          / (lambertDen (Finset.range N) : ℝ) := by rw [hmul]
    _ = jsp87_lambertTrunc N := by field_simp

/-! ## 4. The Lambert-side denominator obstruction -/

/-- **THE LAMBERT-SIDE DENOMINATOR OBSTRUCTION.**  If `2 · S = a / b` with
`b > 0`, then for every `N` the number `b · D_N · R N` — where `D_N` is the
clearing denominator of the truncation at `N` — is an *integer*, and it is
*positive*, hence `≥ 1`.

This is the exact mirror image of `jsp87_carry_mul_eq_int` on the Erdős/carry
side: a hypothetical rationality freezes the tail of the Lambert series into the
lattice `(1/b) ℤ` even after the finite truncation has been cleared. -/
theorem jsp87_lambert_rat_obstruction {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) (N : ℕ) :
    ∃ c : ℤ, 0 < c ∧ (((b : ℝ) * (lambertDen (Finset.range N) : ℝ) * jsp87_lambertTail N) = (c : ℝ)) := by
  have hDpos : 0 < lambertDen (Finset.range N) := lambertDen_pos (Finset.range N)
  have hDposR : (0 : ℝ) < (lambertDen (Finset.range N) : ℝ) := by exact_mod_cast hDpos
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hmul := jsp87_lambertTrunc_mul_num N
  have hk : jsp87_lambertAll = jsp87_lambertTrunc N + jsp87_lambertTail N :=
    jsp87_lambert_decomp N
  -- `b · D_N · R N = a · D_N − b · numer N`, using the splitting and the join.
  have hform : (b : ℝ) * (lambertDen (Finset.range N) : ℝ) * jsp87_lambertTail N
      = (a : ℝ) * (lambertDen (Finset.range N) : ℝ) - (b : ℝ) * ((jsp87_lambertNumer N : ℕ) : ℝ) := by
    have e1 : (a : ℝ) * (lambertDen (Finset.range N) : ℝ)
        - (b : ℝ) * ((jsp87_lambertNumer N : ℕ) : ℝ)
        = (b : ℝ) * (2 * jsp87Series) * (lambertDen (Finset.range N) : ℝ)
          - (b : ℝ) * (jsp87_lambertTrunc N * (lambertDen (Finset.range N) : ℝ)) := by
      have hbpos0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hb0 : (0 : ℝ) ≠ (b : ℝ) := Ne.symm hbpos0.ne'
      rw [h, hmul]
      field_simp
    have e2 : (b : ℝ) * (2 * jsp87Series) * (lambertDen (Finset.range N) : ℝ)
          - (b : ℝ) * (jsp87_lambertTrunc N * (lambertDen (Finset.range N) : ℝ))
        = (b : ℝ) * (lambertDen (Finset.range N) : ℝ) * jsp87_lambertTail N := by
      rw [← jsp87_lambertAll_eq, hk]
      ring
    rw [e1, e2]
  refine ⟨(a * (lambertDen (Finset.range N) : ℕ) - b * (jsp87_lambertNumer N : ℕ) : ℤ), ?_, ?_⟩
  · have hlt : b * (jsp87_lambertNumer N : ℕ) < a * (lambertDen (Finset.range N) : ℕ) := by
      have h1 : (0 : ℝ) < (a : ℝ) * (lambertDen (Finset.range N) : ℝ)
          - (b : ℝ) * ((jsp87_lambertNumer N : ℕ) : ℝ) := by
        have hpos : (0 : ℝ) < (b : ℝ) * (lambertDen (Finset.range N) : ℝ) * jsp87_lambertTail N :=
          mul_pos (mul_pos hbpos hDposR) (jsp87_lambertTail_pos N)
        rw [hform] at hpos
        exact hpos
      have h2 : (b * (jsp87_lambertNumer N : ℕ) : ℝ)
          < (a * (lambertDen (Finset.range N) : ℕ) : ℝ) := by linarith
      exact_mod_cast h2
    have hltR : (b * (jsp87_lambertNumer N : ℕ) : ℝ)
        < (a * (lambertDen (Finset.range N) : ℕ) : ℝ) := by
      exact_mod_cast hlt
    have hpos' : (0 : ℝ) < (a * (lambertDen (Finset.range N) : ℕ) : ℝ)
        - (b * (jsp87_lambertNumer N : ℕ) : ℝ) := by linarith
    exact_mod_cast hpos'
  · rw [hform]
    push_cast
    ring

/-- **A positive integer is at least `1`: the rational Lambert tail is at least
`1 / (b · D_N)`.**  This is the quantitative window the Erdős–Pratt argument
plays in, on the Lambert side. -/
theorem jsp87_lambert_rat_ge_one {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) {N : ℕ} :
    (1 : ℝ) / ((b : ℝ) * (lambertDen (Finset.range N) : ℝ))
      ≤ jsp87_lambertTail N := by
  have hDpos : 0 < lambertDen (Finset.range N) := lambertDen_pos (Finset.range N)
  have hbd : (0 : ℝ) < (b : ℝ) * (lambertDen (Finset.range N) : ℝ) := by
    have hd : (0 : ℝ) < (lambertDen (Finset.range N) : ℝ) := by exact_mod_cast hDpos
    have hb : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    positivity
  obtain ⟨c, hc, hce⟩ := jsp87_lambert_rat_obstruction hb h N
  have hz : ((c : ℤ) : ℝ) = (b : ℝ) * (lambertDen (Finset.range N) : ℝ) * jsp87_lambertTail N := by
    linarith [hce]
  have hci : 1 ≤ c := Int.add_one_le_iff.mpr hc
  have hcr : (1 : ℝ) ≤ (c : ℤ) := by exact_mod_cast hci
  rw [div_le_iff₀ hbd]
  have hkey : (1 : ℝ) ≤ jsp87_lambertTail N * (b : ℝ) * (lambertDen (Finset.range N) : ℝ) := by
    calc (1 : ℝ) ≤ (b : ℝ) * (lambertDen (Finset.range N) : ℝ) * jsp87_lambertTail N := by
          rw [← hz]
          exact hcr
      _ = jsp87_lambertTail N * (b : ℝ) * (lambertDen (Finset.range N) : ℝ) := by ring
  linarith

/-- The clearing denominator is at least `1`, for every truncation. -/
theorem lambertDen_one_le (s : Finset ℕ) : 1 ≤ lambertDen s := by
  unfold lambertDen
  refine Finset.one_le_prod ?_
  intro p _
  by_cases hp : p.Prime
  · simp only [hp, if_true]
    show (1 : ℕ) ≤ 2 ^ p - 1
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    rw [pow_succ]
    have h1 := succ_le_two_pow m
    omega
  · simp only [hp, if_false]
    show (1 : ℕ) ≤ 1
    exact le_rfl

/-- **THE COMBINED LAMBERT WINDOW.**  Under a rationality assumption, at every
cut point the cleared Lambert tail is simultaneously at least `1 / (b · D_N)` and
at most `4 · D_N · 2⁻ᴺ`:

```
1 / (b · D_N)  ≤  R N  ≤  4 · D_N · 2⁻ᴺ .
```

The lower bound is arithmetic (integrality after clearing denominators), the
upper bound is analytic (geometric decay of the tail).  Closing the gap between
them is the content of the Erdős–Pratt argument. -/
theorem jsp87_lambert_window {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) {N : ℕ} :
    (1 : ℝ) / ((b : ℝ) * (lambertDen (Finset.range N) : ℝ)) ≤ jsp87_lambertTail N
      ∧ jsp87_lambertTail N ≤ 4 * (lambertDen (Finset.range N) : ℝ) * ((2 : ℝ) ^ N)⁻¹ :=
  ⟨jsp87_lambert_rat_ge_one hb h, by
    calc jsp87_lambertTail N ≤ 4 * ((2 : ℝ) ^ N)⁻¹ := jsp87_lambertTail_le (N := N)
      _ = 4 * ((2 : ℝ) ^ N)⁻¹ * 1 := by ring
      _ ≤ 4 * ((2 : ℝ) ^ N)⁻¹ * (lambertDen (Finset.range N) : ℝ) := by
          have h1 : (1 : ℝ) ≤ (lambertDen (Finset.range N) : ℝ) := by
            exact_mod_cast lambertDen_one_le (Finset.range N)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * (lambertDen (Finset.range N) : ℝ) * ((2 : ℝ) ^ N)⁻¹ := by ring⟩

end JSP87
