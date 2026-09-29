/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Periodicity

/-!
# JSP-000087 : binary-digit bookkeeping, and the Erdős–Pratt endgame

`JSPProblem/Periodicity.lean` (round 40) established the *dynamics* of the
carries of the Erdős series,

`θ N = 2 ^ N · τ N`,   `θ (N+1) = 2 · θ N − ω N`,   `θ N ≥ 1/4`,

and proved that the digit function `ω` is not eventually periodic.  What it
could not do is *bookkeep*: it never related the carried quantity `θ N` to the
genuine `2`-adic expansion of the number `S = ∑ ω(n) 2^{-(n+1)}`.

This file supplies exactly that bookkeeping, and then closes the endgame.

## 1. The digit window carried by `θ N`

* `jsp87Carry_window` : for every `N, m`,
  `∑_{k ≤ m} ω(N+k) · 2^{m−k} ≤ 2^{m+1} · θ N`.

  The carry at the cut point `N` therefore *dominates the binary value of the
  next `m+1` digits*, uniformly in the cut point.  Concretely
  `jsp87CarryExcess_pos` shows the carry excess is already `≥ 1` whenever two
  consecutive integers have at least one and at least two prime factors — the
  first genuine carry of the series happens at `N = 5`, because `ω 5 = 1` and
  `ω 6 = 2`.

## 2. The carry excess

`jsp87CarryExcess N = ⌊θ N⌋` is the amount the series really carries past the
cut point.  `jsp87_floor_scaled` is the **missing link** between the round-40
carry and the round-38 integer part: the true binary floor of `2^N · S` is

`⌊2^N · S⌋ = I N + ⌊θ N⌋`,

i.e. the integer part `I N` is *not* the binary prefix of `S` — the carry excess
`⌊θ N⌋` is missing from it, and that is exactly why the naive Erdős argument
does not close.

## 3. The exact digit identity

With `jsp87Digit N = ⌊2^{N+1} S⌋ − 2 ⌊2^N S⌋` the `N`-th binary digit of `S`
(one always has `jsp87Digit N ∈ {0, 1}`), the bookkeeping is the identity

`jsp87_digit_bookkeeping` : `d N = ω N + c (N+1) − 2 c N`,  `c N = ⌊θ N⌋`.

So the `ω`-digit at `N` is the binary digit *plus* the change of the carry
excess.  Everything about the series is now expressed in integers.

## 4. Rationality forces eventually-periodic binary digits — from scratch

`jsp87_digit_eventuallyPeriodic`: if `S = a / b` with `b > 0` then the binary
digits of `S` are eventually periodic.  This is proved here elementarily — the
fractional parts `fract (2^N S)` are `c(N)/b` with `c(N) < b`, they obey the
doubling map `f(N+1) = fract (2 f(N))`, and the pigeonhole principle makes the
numerators eventually periodic.  Mathlib has no such statement.

## 5. The endgame

Combining §4 with §3 and `omega_not_eventuallyPeriodic` (round 40):

* `jsp87Series_irrational_of_carryExcess_eventuallyPeriodic` : **if the carry
  excess `⌊2^N τ N⌋` is eventually periodic then `S` is irrational**;
* `jsp87Series_irrational_of_carry_lt_one` : in particular, if the carries stay
  below `1` from some point on, `S` is irrational;
* `jsp87Series_rational_imp_carryExcess_not_periodic` : conversely, rationality of
  `S` *forces* the carry excess to be a non-eventually-periodic integer
  sequence.

This isolates exactly the arithmetic input a full proof still needs: a
quantitative statement about the integer part `⌊2^N · τ N⌋` of the Erdős
series.  (In Pratt's proof of arXiv:2409.15185 that input is a uniform prime
`k`-tuples correlation hypothesis, so the headline theorem `jsp_000087_main`
stays withheld.)
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The digit window carried by `θ N` -/

/-- Rescaling the term of the series sitting `k` places past the cut point
`2 ^ N · jsp87Term (N + k)` erases `N` entirely: it depends only on the offset
`k`.  Equivalently `θ N = ∑' k, ω (N+k) 2^{-(k+1)}`. -/
theorem two_pow_mul_jsp87Term_shift (N k : ℕ) :
    (2 : ℝ) ^ N * jsp87Term (N + k) = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
  simp only [jsp87Term]
  have hD : (2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
    have hb : (2 : ℝ) ^ N * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (N + k + 1) := by
      rw [← pow_add]
      congr 1
    rw [← hb]
    calc (2 : ℝ) ^ N * ((2 : ℝ) ^ N * (2 : ℝ) ^ (k + 1))⁻¹
        = (2 : ℝ) ^ N * (((2 : ℝ) ^ (k + 1))⁻¹ * ((2 : ℝ) ^ N)⁻¹) := by
          rw [DivisionMonoid.mul_inv_rev]
      _ = (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ * ((2 : ℝ) ^ (k + 1))⁻¹ := by ring
      _ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ N) ≠ 0), one_mul]
  calc (2 : ℝ) ^ N * (((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹)
      = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹) := by ring
    _ = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by rw [hD]

/-- **The digit window.**  For `k ≤ m`, rescaling the term at `N + k` by
`2^{m+1} · 2^N` turns it into the digit `ω (N+k)` weighted by `2^{m−k}`. -/
theorem two_pow_two_pow_mul_jsp87Term {N m k : ℕ} (hk : k ≤ m) :
    (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Term (N + k))
      = ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k) := by
  have hD : (2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
    have hb : (2 : ℝ) ^ N * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (N + k + 1) := by
      rw [← pow_add]
      congr 1
    rw [← hb]
    calc (2 : ℝ) ^ N * ((2 : ℝ) ^ N * (2 : ℝ) ^ (k + 1))⁻¹
        = (2 : ℝ) ^ N * (((2 : ℝ) ^ (k + 1))⁻¹ * ((2 : ℝ) ^ N)⁻¹) := by
          rw [DivisionMonoid.mul_inv_rev]
      _ = (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ * ((2 : ℝ) ^ (k + 1))⁻¹ := by ring
      _ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ N) ≠ 0), one_mul]
  have hC : (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ (k + 1))⁻¹ = (2 : ℝ) ^ (m - k) := by
    have hb : (2 : ℝ) ^ (m - k) * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (m + 1) := by
      rw [← pow_add]
      congr 1 <;> omega
    rw [← hb, mul_assoc, mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ (k + 1)) ≠ 0), mul_one]
  simp only [jsp87Term]
  calc (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * (((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹))
      = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹)) := by
        ring
    _ = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ (k + 1))⁻¹) := by rw [hD]
    _ = ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k) := by rw [hC]

/-- **THE DIGIT WINDOW.**  For every cut point `N` and every window length `m`,

`∑_{k ≤ m} ω (N+k) 2^{m−k} ≤ 2^{m+1} · θ N`.

The carry at the cut point dominates the binary value of the next `m+1`
digits, uniformly in the cut point. -/
theorem jsp87Carry_window (N m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k))
      ≤ (2 : ℝ) ^ (m + 1) * jsp87Carry N := by
  have hsumm : Summable (fun k : ℕ => (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Term (N + k))) :=
    Summable.mul_left ((2 : ℝ) ^ (m + 1)) (Summable.mul_left ((2 : ℝ) ^ N) (summable_jsp87Tail N))
  have hstep : ∀ k ∈ Finset.range (m + 1),
      ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k)
        = (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Term (N + k)) := by
    intro k hk
    have hk' : k < m + 1 := Finset.mem_range.mp hk
    symm
    exact two_pow_two_pow_mul_jsp87Term (N := N) (m := m) (hk := by omega)
  calc (∑ k ∈ Finset.range (m + 1), ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k))
      = ∑ k ∈ Finset.range (m + 1), (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Term (N + k)) :=
        Finset.sum_congr rfl hstep
    _ ≤ ∑' k, (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Term (N + k)) :=
        Summable.sum_le_tsum (s := Finset.range (m + 1))
          (f := fun k : ℕ => (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Term (N + k)))
          (fun k _ => mul_nonneg (by positivity)
            (mul_nonneg (by positivity) (jsp87Tail_term_nonneg N k))) hsumm
    _ = (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ N * jsp87Tail N) := by
        have hsumm2 : Summable (fun k : ℕ => (2 : ℝ) ^ N * jsp87Term (N + k)) :=
          Summable.mul_left ((2 : ℝ) ^ N) (summable_jsp87Tail N)
        rw [Summable.tsum_mul_left ((2 : ℝ) ^ (m + 1)) hsumm2,
          Summable.tsum_mul_left ((2 : ℝ) ^ N) (summable_jsp87Tail N)]
        rfl
    _ = (2 : ℝ) ^ (m + 1) * jsp87Carry N := by simp only [jsp87Carry]

/-! ## 2. The carry excess -/

/-- **The carry excess** `c N = ⌊θ N⌋`: how much the series really carries past
the cut point `N`.  This is the integer part of the rescaled tail, i.e. the
amount by which the `2`-adic prefix `I N` of round 38 falls short of the true
binary prefix `⌊2^N S⌋`. -/
noncomputable def jsp87CarryExcess (N : ℕ) : ℤ := ⌊jsp87Carry N⌋

/-- The carry excess is a nonnegative integer. -/
theorem jsp87CarryExcess_nonneg (N : ℕ) : 0 ≤ jsp87CarryExcess N :=
  Int.floor_nonneg.mpr (jsp87Carry_pos N).le

/-- **The carry excess in `ℝ`:** `c N ≤ θ N < c N + 1`, and the leftover is
exactly the fractional part of the carry. -/
theorem jsp87Carry_excess_lt_one (N : ℕ) :
    (jsp87CarryExcess N : ℝ) ≤ jsp87Carry N ∧ jsp87Carry N < (jsp87CarryExcess N : ℝ) + 1 := by
  refine ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- **The fractional part of the carry is the leftover of the excess.** -/
theorem jsp87Carry_excess_fract (N : ℕ) :
    jsp87Carry N - (jsp87CarryExcess N : ℝ) = Int.fract (jsp87Carry N) := by
  have key : jsp87Carry N - Int.fract (jsp87Carry N) = (jsp87CarryExcess N : ℝ) := by
    rw [Int.self_sub_fract]
    rfl
  linarith

/-- **A long enough digit window forces a genuine carry.**  If the binary value
of the next `m+1` digits reaches `2^{m+1}`, then the carry excess is `≥ 1`. -/
theorem jsp87CarryExcess_ge_window {N m : ℕ}
    (h : (2 : ℝ) ^ (m + 1)
        ≤ ∑ k ∈ Finset.range (m + 1), ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k)) :
    1 ≤ jsp87CarryExcess N := by
  have hw := jsp87Carry_window N m
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  have h1 : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ (m + 1) * jsp87Carry N := h.trans hw
  have h2 : (1 : ℝ) ≤ jsp87Carry N := by
    have h3 : (2 : ℝ) ^ (m + 1) * 1 ≤ (2 : ℝ) ^ (m + 1) * jsp87Carry N := by linarith
    exact le_of_mul_le_mul_left h3 hp0
  exact Int.floor_pos.mpr h2

/-- **Two consecutive integers with one and two prime factors already force a
carry.**  Concretely, the first carry of the Erdős series happens at the cut
point `N = 5` (`ω 5 = 1`, `ω 6 = 2`). -/
theorem jsp87CarryExcess_pos {N : ℕ} (h1 : 1 ≤ omega N) (h2 : 2 ≤ omega (N + 1)) :
    1 ≤ jsp87CarryExcess N := by
  have hω1 : (1 : ℝ) ≤ (omega N : ℝ) := by exact_mod_cast h1
  have hω2 : (2 : ℝ) ≤ (omega (N + 1) : ℝ) := by exact_mod_cast h2
  have hsum : (∑ k ∈ Finset.range 2, ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (1 - k))
      = 2 * (omega N : ℝ) + (omega (N + 1) : ℝ) := by
    have hstep : (∑ k ∈ Finset.range 2, ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (1 - k))
        = ((omega (N + 0) : ℕ) : ℝ) * (2 : ℝ) ^ (1 - 0)
          + ((omega (N + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (1 - 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [hstep]
    norm_num [Nat.add_zero, Nat.sub_zero]
    ring
  refine jsp87CarryExcess_ge_window (N := N) (m := 1) ?_
  rw [hsum]
  norm_num
  linarith

/-- **The first carry of the Erdős series is a real carry: `⌊θ 5⌋ ≥ 1`.** -/
theorem jsp87CarryExcess_five_ge_one : 1 ≤ jsp87CarryExcess 5 := by
  have h5 : omega 5 = 1 := by native_decide
  have h6 : omega 6 = 2 := by native_decide
  refine jsp87CarryExcess_pos (N := 5) (le_of_eq h5.symm) (le_of_eq h6.symm)

/-- **No carry at the cut point** is the same as vanishing excess. -/
theorem jsp87CarryExcess_eq_zero_iff {N : ℕ} : jsp87CarryExcess N = 0 ↔ jsp87Carry N < 1 := by
  have hiff : ⌊jsp87Carry N⌋ = 0 ↔ jsp87Carry N < 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · intro h
      simpa using h.2
    · intro h
      exact ⟨by simpa using (jsp87Carry_pos N).le, by simpa using h⟩
  exact hiff

/-- **The binary prefix obeys the doubling recurrence.**  The integer part of
round 38 — the `2`-adic prefix `I N = ∑_{n<N} ω n · 2^{N−n−1}` — satisfies

`I (N+1) = 2 I N + ω N`,

so the whole `2`-adic content of the series is the digit string `ω 0, ω 1, …`
read in base two.  (This is what makes the missing carry excess in
`jsp87_floor_scaled` the *only* obstruction to reading `S` in base two.) -/
theorem jsp87IntPart_succ (N : ℕ) : jsp87IntPart (N + 1) = 2 * jsp87IntPart N + omega N := by
  simp only [jsp87IntPart]
  have hstep : ∀ i ∈ Finset.range N,
      (omega i : ℤ) * 2 ^ (N + 1 - i - 1) = 2 * ((omega i : ℤ) * 2 ^ (N - i - 1)) := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    have hexp : N + 1 - i - 1 = (N - i - 1) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  have hlast : (omega N : ℤ) * 2 ^ (N + 1 - N - 1) = omega N := by
    have hexp : N + 1 - N - 1 = 0 := by omega
    rw [hexp, pow_zero, mul_one]
  rw [Finset.sum_range_succ, Finset.sum_congr rfl hstep, Finset.mul_sum, hlast, add_comm]

/-- **THE MISSING LINK between the round-38 integer part and the round-40
carry.**  For `1 ≤ N` the true binary floor of the rescaled series is

`⌊2^N · S⌋ = I N + ⌊θ N⌋`,

so the `2`-adic prefix `I N` misses exactly the carry excess. -/
theorem jsp87_floor_scaled {N : ℕ} (hN : 1 ≤ N) :
    ⌊(2 : ℝ) ^ N * jsp87Series⌋ = jsp87IntPart N + jsp87CarryExcess N := by
  have hdecomp := jsp87_scaled_decomposition N hN
  rw [hdecomp, Int.floor_intCast_add]
  rfl

/-! ## 3. The binary digits of the series -/

/-- The `N`-th binary digit of the Erdős series,
`d N = ⌊2^{N+1} S⌋ − 2 ⌊2^N S⌋`. -/
noncomputable def jsp87Digit (N : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (N + 1) * jsp87Series⌋ - 2 * ⌊(2 : ℝ) ^ N * jsp87Series⌋

/-- **Doubling the fractional part.** `fract (2 x) = fract (2 · fract x)`: the
binary digits of a real number are generated by iterating the doubling map on
its fractional part. -/
theorem Int.fract_two_mul {x : ℝ} : Int.fract (2 * x) = Int.fract (2 * Int.fract x) := by
  have h1 : 2 * x = 2 * ((⌊x⌋ : ℤ) : ℝ) + 2 * Int.fract x := by
    calc 2 * x = 2 * (((⌊x⌋ : ℤ) : ℝ) + Int.fract x) := by rw [Int.floor_add_fract x]
      _ = 2 * ((⌊x⌋ : ℤ) : ℝ) + 2 * Int.fract x := by ring
  have h2 : (2 : ℝ) * ((⌊x⌋ : ℤ) : ℝ) = ((2 * ⌊x⌋ : ℤ) : ℝ) := by norm_cast
  rw [h1, h2, add_comm, Int.fract_add_intCast]

/-- **The fractional parts of the rescaled series obey the doubling map.** -/
theorem jsp87_fract_scaled_succ (N : ℕ) :
    Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series) = Int.fract (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)) := by
  have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  rw [hpow]
  convert Int.fract_two_mul (x := (2 : ℝ) ^ N * jsp87Series) using 1 <;> ring

/-- **A binary digit is the doubling of the previous fractional part.** -/
theorem jsp87_digit_eq_fract (N : ℕ) :
    (jsp87Digit N : ℝ) = 2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)
      - Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series) := by
  have h1 : (2 : ℝ) ^ (N + 1) * jsp87Series
      = 2 * (((⌊(2 : ℝ) ^ N * jsp87Series⌋ : ℤ) : ℝ) + Int.fract ((2 : ℝ) ^ N * jsp87Series)) := by
    have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
    have hfr := Int.floor_add_fract ((2 : ℝ) ^ N * jsp87Series)
    rw [hpow]
    nlinarith [hfr]
  have h2 : (2 : ℝ) ^ (N + 1) * jsp87Series
      = (((⌊(2 : ℝ) ^ (N + 1) * jsp87Series⌋ : ℤ) : ℝ) + Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series)) :=
    (Int.floor_add_fract ((2 : ℝ) ^ (N + 1) * jsp87Series)).symm
  have key : ((⌊(2 : ℝ) ^ (N + 1) * jsp87Series⌋ : ℤ) : ℝ)
      = (2 : ℝ) ^ (N + 1) * jsp87Series - Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series) := by
    have hfr := Int.self_sub_fract ((2 : ℝ) ^ (N + 1) * jsp87Series)
    linarith
  simp only [jsp87Digit]
  push_cast
  rw [key, h1]
  ring

/-- **The binary digits of the Erdős series are `0` or `1`.** -/
theorem jsp87Digit_mem (N : ℕ) : jsp87Digit N = 0 ∨ jsp87Digit N = 1 := by
  have hkey := jsp87_digit_eq_fract N
  have h0 : (0 : ℝ) ≤ 2 * Int.fract ((2 : ℝ) ^ N * jsp87Series) := by positivity
  have h1 : 2 * Int.fract ((2 : ℝ) ^ N * jsp87Series) < 2 := by
    have := Int.fract_lt_one ((2 : ℝ) ^ N * jsp87Series)
    linarith
  have h2 : (0 : ℝ) ≤ Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series) := Int.fract_nonneg _
  have h3 : Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series)
      ≤ 2 * Int.fract ((2 : ℝ) ^ N * jsp87Series) := by
    rw [jsp87_fract_scaled_succ N]
    have hfr := Int.self_sub_floor (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series))
    have hfl0 : (0 : ℤ) ≤ ⌊2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (by norm_num) (Int.fract_nonneg _))
    have hfl : (0 : ℝ) ≤ ((⌊2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ : ℤ) : ℝ) := by
      exact_mod_cast hfl0
    linarith
  have hd0 : (0 : ℤ) ≤ jsp87Digit N := by
    have : (0 : ℝ) ≤ (jsp87Digit N : ℝ) := by linarith
    exact_mod_cast this
  have hd1 : jsp87Digit N < 2 := by
    have : (jsp87Digit N : ℝ) < 2 := by linarith
    exact_mod_cast this
  by_cases hz : jsp87Digit N = 0
  · exact Or.inl hz
  · have hpos : (0 : ℤ) < jsp87Digit N := lt_of_le_of_ne hd0 (Ne.symm hz)
    have hone : (1 : ℤ) ≤ jsp87Digit N := by omega
    refine Or.inr (by omega)

/-- **THE EXACT BOOKKEEPING IDENTITY.**  For `1 ≤ N`,

`d N = ω N + c (N+1) − 2 c N`,

where `d N` is the `N`-th binary digit of the series, `ω N` the `ω`-digit, and
`c N = ⌊θ N⌋` the carry excess.  The `ω`-digit is the binary digit *plus* the
change of the carry excess: this is the whole arithmetic content of the
Erdős series, expressed over `ℤ`. -/
theorem jsp87_digit_bookkeeping {N : ℕ} (hN : 1 ≤ N) :
    jsp87Digit N = omega N + jsp87CarryExcess (N + 1) - 2 * jsp87CarryExcess N := by
  have h1 := jsp87_floor_scaled (N := N + 1) (by omega)
  have h2 := jsp87_floor_scaled (N := N) hN
  have hrec := jsp87IntPart_succ N
  simp only [jsp87Digit]
  rw [h1, h2]
  omega

/-- **The digits read as `ω` wherever the series does not carry.** -/
theorem jsp87_digit_eq_omega {N : ℕ} (hN : 1 ≤ N) (h0 : jsp87Carry N < 1) (h1 : jsp87Carry (N + 1) < 1) :
    jsp87Digit N = omega N := by
  have hb := jsp87_digit_bookkeeping hN
  have hz0 : jsp87CarryExcess N = 0 := (jsp87CarryExcess_eq_zero_iff.mpr h0)
  have hz1 : jsp87CarryExcess (N + 1) = 0 := (jsp87CarryExcess_eq_zero_iff.mpr h1)
  omega


/-! ## 4. Rationality forces eventually-periodic binary digits -/

/-- **The numerator of the fractional part.**  If the series is the rational
`a / b` with `b > 0`, the fractional part of `2^N · S` is `jsp87FracNum b N / b`
with `jsp87FracNum b N < b`: the fractional parts live in a *finite* set of
size `b`, uniformly in `N`. -/
noncomputable def jsp87FracNum (b : ℕ) (N : ℕ) : ℕ :=
  (⌊(b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ : ℤ).toNat

/-- **The fractional parts of a rational rescaling are `c / b` with `c < b`.** -/
theorem jsp87FracNum_spec {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    {N : ℕ} (hN : 1 ≤ N) :
    jsp87FracNum b N < b
      ∧ Int.fract ((2 : ℝ) ^ N * jsp87Series) = (jsp87FracNum b N : ℝ) / (b : ℝ) := by
  obtain ⟨c, hc0, hc1, hc2⟩ := jsp87_fract_scaled_eq_div (N := N) hN hb h
  have hmul : (b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87Series) = (c : ℝ) := by
    rw [hc2]
    field_simp
  have hfloor : ⌊(b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ = c := by
    rw [hmul, Int.floor_intCast]
  have hcast : ((jsp87FracNum b N : ℕ) : ℤ) = c := by
    show (↑((⌊(b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ : ℤ).toNat : ℕ) : ℤ) = c
    rw [Int.toNat_of_nonneg (by rw [hfloor]; exact hc0), hfloor]
  have hltN : jsp87FracNum b N < b := by
    have hz : ((jsp87FracNum b N : ℕ) : ℤ) < (b : ℕ) := by
      rw [hcast]
      exact hc1
    exact_mod_cast hz
  refine ⟨hltN, ?_⟩
  have hR : ((jsp87FracNum b N : ℕ) : ℝ) = (c : ℝ) := by
    norm_cast
  calc Int.fract ((2 : ℝ) ^ N * jsp87Series) = (c : ℝ) / (b : ℝ) := hc2
    _ = (jsp87FracNum b N : ℝ) / (b : ℝ) := by rw [hR]

/-- **Equal fractional parts have equal successors** (the doubling map is a
function of the fractional part alone). -/
theorem jsp87FracNum_succ {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h' : jsp87FracNum b i = jsp87FracNum b j) :
    jsp87FracNum b (i + 1) = jsp87FracNum b (j + 1) := by
  have hs := jsp87FracNum_spec (N := i) hb h hi
  have hs' := jsp87FracNum_spec (N := j) hb h hj
  have hfrac : Int.fract ((2 : ℝ) ^ (i + 1) * jsp87Series)
      = Int.fract ((2 : ℝ) ^ (j + 1) * jsp87Series) := by
    rw [jsp87_fract_scaled_succ i, jsp87_fract_scaled_succ j, hs.2, hs'.2, h']
  have h1 := (jsp87FracNum_spec (N := i + 1) hb h (by omega)).2
  have h1' := (jsp87FracNum_spec (N := j + 1) hb h (by omega)).2
  rw [← hfrac] at h1'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have key : ((jsp87FracNum b (i + 1) : ℕ) : ℝ) / (b : ℝ)
      = ((jsp87FracNum b (j + 1) : ℕ) : ℝ) / (b : ℝ) := by
    rw [← h1, ← h1']
  have key' : (jsp87FracNum b (i + 1) : ℝ) = ((jsp87FracNum b (j + 1) : ℕ) : ℝ) :=
    (div_left_inj' hb0).mp key
  exact_mod_cast key'

/-- The numerator sequence propagates along the doubling map. -/
theorem jsp87FracNum_period_aux {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (h0 : jsp87FracNum b i = jsp87FracNum b j) (k : ℕ) :
    jsp87FracNum b (i + k) = jsp87FracNum b (j + k) := by
  induction k with
  | zero => rw [Nat.add_zero]; exact h0
  | succ k ih =>
    have h1 : jsp87FracNum b (i + Nat.succ k) = jsp87FracNum b (j + Nat.succ k) := by
      have hstep := jsp87FracNum_succ hb h (by omega) (by omega) ih
      convert hstep using 1 <;> omega
    exact h1

/-- **THE FINITE-RANGE ARGUMENT.**  A sequence of `b+1` numerators taking values
in `range b` has two equal entries, and the doubling map then propagates the
equality forever.  So the fractional parts of the rescaled series are
*eventually periodic*. -/
theorem jsp87FracNum_period {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → jsp87FracNum b (n + t) = jsp87FracNum b n := by
  have hlt : ∀ i : ℕ, jsp87FracNum b (i + 1) < b :=
    fun i => (jsp87FracNum_spec (N := i + 1) hb h (by omega)).1
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (b + 1) => (⟨jsp87FracNum b (i.val + 1), hlt i.val⟩ : Fin b)) (by simp)
  have hne' : x.1 ≠ y.1 := fun hh => hne (Fin.ext hh)
  have h0 : jsp87FracNum b (x.1 + 1) = jsp87FracNum b (y.1 + 1) := congrArg Fin.val heq
  rcases lt_trichotomy x.1 y.1 with hxy | hxy | hxy
  · have ht : 0 < y.1 - x.1 := by omega
    have hN : 1 ≤ x.1 + 1 := by omega
    refine ⟨y.1 - x.1, x.1 + 1, ht, hN, ?_⟩
    intro n hn
    have hk := jsp87FracNum_period_aux hb h (by omega) (by omega) h0 (n - (x.1 + 1))
    rw [Nat.add_sub_of_le hn] at hk
    have hkey : n + (y.1 - x.1) = (y.1 + 1) + (n - (x.1 + 1)) := by omega
    rw [← hkey] at hk
    exact hk.symm
  · exact (hne' hxy).elim
  · have ht : 0 < x.1 - y.1 := by omega
    have hN : 1 ≤ y.1 + 1 := by omega
    refine ⟨x.1 - y.1, y.1 + 1, ht, hN, ?_⟩
    intro n hn
    have hk := jsp87FracNum_period_aux hb h (by omega) (by omega) h0.symm (n - (y.1 + 1))
    rw [Nat.add_sub_of_le hn] at hk
    have hkey : n + (x.1 - y.1) = (x.1 + 1) + (n - (y.1 + 1)) := by omega
    rw [← hkey] at hk
    exact hk.symm

/-- **RATIONALITY ⇏ NON-PERIODIC DIGITS: the digits of a rational are eventually
periodic.**  If `S = a / b` with `b > 0` then the binary digits `jsp87Digit N`
of the Erdős series are eventually periodic in `N`.  Proved from scratch (finite
range + pigeonhole + the doubling map); Mathlib has no such statement. -/
theorem jsp87_digit_eventuallyPeriodic {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n := by
  obtain ⟨t, M, ht, hM1, hper⟩ := jsp87FracNum_period hb h
  refine ⟨t, M, ht, hM1, ?_⟩
  intro n hn
  have hs := jsp87FracNum_spec (N := n) hb h (by omega)
  have hs' := jsp87FracNum_spec (N := n + t) hb h (by omega)
  have hc := hper n hn
  have hfrac : Int.fract ((2 : ℝ) ^ (n + t) * jsp87Series) = Int.fract ((2 : ℝ) ^ n * jsp87Series) := by
    rw [hs'.2, hs.2, hc]
  have hfrac' : Int.fract ((2 : ℝ) ^ (n + t + 1) * jsp87Series)
      = Int.fract ((2 : ℝ) ^ (n + 1) * jsp87Series) := by
    calc Int.fract ((2 : ℝ) ^ (n + t + 1) * jsp87Series)
        = Int.fract (2 * Int.fract ((2 : ℝ) ^ (n + t) * jsp87Series)) := jsp87_fract_scaled_succ (n + t)
      _ = Int.fract (2 * Int.fract ((2 : ℝ) ^ n * jsp87Series)) := by rw [hfrac]
      _ = Int.fract ((2 : ℝ) ^ (n + 1) * jsp87Series) := (jsp87_fract_scaled_succ n).symm
  have h1 := jsp87_digit_eq_fract n
  have h2 := jsp87_digit_eq_fract (n + t)
  rw [hfrac, hfrac'] at h2
  rw [← h1] at h2
  exact_mod_cast h2

/-! ## 5. The Erdős–Pratt endgame -/

/-- **Eventual periodicity with period `t` gives period `k · t`.** -/
theorem eventuallyPeriodic_mul {f : ℕ → ℤ} {t N : ℕ} (_ht : 0 < t)
    (hN : ∀ n, N ≤ n → f (n + t) = f n) (k : ℕ) : ∀ n, N ≤ n → f (n + k * t) = f n := by
  induction k with
  | zero => intro n _; rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
    intro n hn
    have h1 : f (n + Nat.succ k * t) = f (n + k * t) := by
      have hstep := hN (n + k * t) (by omega)
      rw [show n + Nat.succ k * t = (n + k * t) + t by
        simp only [Nat.succ_eq_add_one]; ring, hstep]
    rw [h1]
    exact ih n hn

/-- **THE ENDGAME, step 1.**  If the Erdős series is rational and its carry
excess `⌊2^N · τ N⌋` is eventually periodic with period `t > 0`, then `ω` itself
is eventually periodic (with period `s · t`, where `s` is a period of the binary
digits). -/
theorem jsp87_omega_eventuallyPeriodic_of_rational {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) {t N : ℕ} (ht : 0 < t)
    (hN : ∀ n, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n) :
    ∃ t' N' : ℕ, 0 < t' ∧ ∀ n, N' ≤ n → omega (n + t') = omega n := by
  obtain ⟨s, M, hs, hM1, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  refine ⟨s * t, max M N, by positivity, ?_⟩
  intro n hn
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have h1n : 1 ≤ n := le_trans hM1 hnM
  have hd := eventuallyPeriodic_mul hs (fun n hn => hper n hn) t n hnM
  have hd' : jsp87Digit (n + s * t) = jsp87Digit n := by simpa [Nat.mul_comm] using hd
  have hc : jsp87CarryExcess (n + s * t) = jsp87CarryExcess n :=
    eventuallyPeriodic_mul ht hN s n hnN
  have hc' := eventuallyPeriodic_mul ht hN s (n + 1) (le_trans hnN (Nat.le_succ n))
  have hstep : jsp87CarryExcess (n + s * t + 1) = jsp87CarryExcess (n + 1) := by
    simpa [Nat.add_assoc, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm] using hc'
  have hb1 := jsp87_digit_bookkeeping (N := n) h1n
  have hb2 := jsp87_digit_bookkeeping (N := n + s * t) (le_trans h1n (Nat.le_add_right n (s * t)))
  have hb1' : ((omega n : ℕ) : ℤ) = jsp87Digit n - jsp87CarryExcess (n + 1)
      + 2 * jsp87CarryExcess n := by omega
  have hb2' : ((omega (n + s * t) : ℕ) : ℤ) = jsp87Digit (n + s * t)
      - jsp87CarryExcess (n + s * t + 1) + 2 * jsp87CarryExcess (n + s * t) := by omega
  have key : ((omega (n + s * t) : ℕ) : ℤ) = ((omega n : ℕ) : ℤ) := by
    rw [hb2', hb1', hd', hc, hstep]
  exact_mod_cast key

/-- **THE ENDGAME.**  **If the carry excess `⌊2^N · τ N⌋` of the Erdős series is
eventually periodic, then the series is irrational.**

Indeed, rationality makes the binary digits eventually periodic
(`jsp87_digit_eventuallyPeriodic`), the bookkeeping identity
`d N = ω N + c (N+1) − 2 c N` then transfers that periodicity to the digits
`ω N`, and `omega_not_eventuallyPeriodic` (round 40) contradicts it.

This isolates the arithmetic input a complete proof still needs: a
*quantitative* statement about the integer part `⌊2^N · τ N⌋` of the tail. -/
theorem jsp87Series_irrational_of_carryExcess_eventuallyPeriodic {t N : ℕ} (ht : 0 < t)
    (hN : ∀ n, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  obtain ⟨t', N', ht', hN'⟩ := jsp87_omega_eventuallyPeriodic_of_rational
    (a := q.num) (b := q.den) hden (by rw [← hq, Rat.cast_def]) ht hN
  exact omega_not_eventuallyPeriodic ⟨t', N', ht', hN'⟩

/-- **The carries staying below `1` from some point on force irrationality:**
then the carry excess vanishes, `jsp87_digit_eq_omega` makes the binary digits
equal the `ω`-digits, and `ω` is aperiodic. -/
theorem jsp87Series_irrational_of_carry_lt_one {N : ℕ} (h : ∀ n, N ≤ n → jsp87Carry n < 1) :
    Irrational jsp87Series := by
  refine jsp87Series_irrational_of_carryExcess_eventuallyPeriodic (t := 1) (N := N) (by omega) ?_
  intro n hn
  rw [jsp87CarryExcess_eq_zero_iff.mpr (h n hn), jsp87CarryExcess_eq_zero_iff.mpr (h (n + 1) (by omega))]

/-- **A stabilising carry excess forces irrationality** (period `1` is
eventual periodicity). -/
theorem jsp87Series_irrational_of_carryExcess_eventuallyConst {C : ℤ} {N : ℕ}
    (hC : ∀ n, N ≤ n → jsp87CarryExcess n = C) : Irrational jsp87Series := by
  refine jsp87Series_irrational_of_carryExcess_eventuallyPeriodic (t := 1) (N := N) (by omega) ?_
  intro n hn
  rw [hC n hn, hC (n + 1) (by omega)]

/-- **The contrapositive: rationality forces the carry excess NOT to be
eventually periodic.**  This is the precise remaining obstruction. -/
theorem jsp87Series_rational_imp_carryExcess_not_periodic {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n := by
  rintro ⟨t, N, ht, hN⟩
  obtain ⟨t', N', ht', hN'⟩ := jsp87_omega_eventuallyPeriodic_of_rational hb h ht hN
  exact omega_not_eventuallyPeriodic ⟨t', N', ht', hN'⟩


/-- **THE DICHOTOMY (cleanest statement of this round).**  Either the Erdős
series is irrational, or the carry excess `⌊2^N · τ N⌋` is an integer sequence that
is *not* eventually periodic.  In particular, any proof of
`jsp87_irrational_of_carryExcess_eventuallyPeriodic` reduces JSP-000087 to
exhibiting eventual periodicity of `⌊2^N · ∑' k, ω(N+k) 2^{-(k+1)}⌋` — the exact
arithmetic input Pratt (arXiv:2409.15185) obtains from a uniform prime-`k`-tuples
hypothesis. -/
theorem jsp87Series_irrational_or_carryExcess_not_periodic :
    Irrational jsp87Series
      ∨ ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n := by
  by_cases hr : ∃ q : ℚ, jsp87Series = (q : ℝ)
  · right
    rintro ⟨t, N, ht, hN⟩
    obtain ⟨q, hq⟩ := hr
    obtain ⟨t', N', ht', hN'⟩ := jsp87_omega_eventuallyPeriodic_of_rational
      (a := q.num) (b := q.den) (Rat.den_pos q) (by rw [hq, ← Rat.cast_def]) ht hN
    exact omega_not_eventuallyPeriodic ⟨t', N', ht', hN'⟩
  · left
    show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
    rintro ⟨q, hq⟩
    exact hr ⟨q, hq.symm⟩

/-- **The carry excess is at most the cut point**: `c N ≤ N + 1` for `1 ≤ N`. -/
theorem jsp87CarryExcess_le {N : ℕ} (hN : 1 ≤ N) : (jsp87CarryExcess N : ℝ) ≤ (N + 1 : ℕ) := by
  have hb := jsp87_carry_bounds (N := N) hN
  have hf := (jsp87Carry_excess_lt_one N).1
  simp only [jsp87Carry] at hf
  linarith

end JSP87
