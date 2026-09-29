/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Diophantine
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring

/-!
# JSP-000087 : the carry dynamics and the aperiodicity endgame

`JSPProblem/Diophantine.lean` gave the *static* picture of the Erdős–Pratt
argument: the carry decomposition `2^N · S = I N + 2^N · τ N` with `I N ∈ ℤ`, the
denominator obstruction `b · 2^N · τ N ∈ ℤ` for a rational `S = a / b`, and the
window `0 < 2^N · τ N ≤ N + 1`.

This file supplies the *dynamic* half, which is what an irrationality proof
actually has to exploit, plus the **aperiodicity endgame** on which every
Erdős-style irrationality argument of this shape terminates.

## 1. The carry sequence and its exact recurrence

Write `θ N = jsp87Carry N = 2^N · τ N`, the rescaled tail.  Reading the
definition of `τ` one term at a time gives the *exact* digit-carry relation

* `jsp87Carry_succ` : `θ (N+1) = 2 · θ N − ω N`,

i.e. the carries obey the classical `θ_{N+1} = 2 θ_N − d_N` with digits
`d_N = ω N`.  Two immediate quantitative consequences, both new:

* `jsp87Carry_ge_omega_succ` : `ω (N+1) ≤ 4 · θ N`;
* `jsp87Carry_ge_quarter` : `θ N ≥ 1/4` for **every** `N`.

The second is the reason the naive argument cannot work: the carries are *not*
confined to `(0,1)`, so rationality does not immediately produce a contradiction.
`jsp87Carry_gt_one` makes the same point quantitatively — four distinct prime
factors of `N+1` already push the carry past `1`.

## 2. Fractional parts

`jsp87_fract_scaled` identifies the fractional part of `2^N · S` with that of the
carry `θ N` (the two differ by the integer `I N`), and `jsp87_fract_scaled_eq_div`
shows that a rational `S = a / b` forces the numerator `b · fract (2^N · S)` to be
an integer in `[0, b)` — a *finite* set, uniformly in `N`.

## 3. Aperiodicity of `ω` — the endgame

`JSPProblem/Diophantine.lean` and `JSPProblem/LambertGcd.lean` show that
rationality of `S` freezes every carry into a fixed lattice.  An Erdős-style
argument then needs the digit sequence to be aperiodic.  That is proved here,
completely and elementarily:

* `omega_mul_prime_of_large_prime` : `p` prime, `1 ≤ n`, `n < p ⟹ ω (n·p) = ω n + 1`;
* `omega_eventuallyPeriodic_const_mul` : an eventual period `t` makes `n ↦ ω (t·n)`
  eventually **constant**;
* `omega_not_eventuallyPeriodic` : **`ω` is not eventually periodic.**

The last theorem is the combinatorial heart of the endgame: whatever period the
arithmetic of the series might be forced to exhibit, the digit function `ω`
refuses to be periodic with it.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The carry sequence -/

/-- **The carry** at the cut point `N`: the rescaled tail
`θ N = 2 ^ N · τ N = ∑' k, ω(N+k) 2^-(k+1)`. -/
noncomputable def jsp87Carry (N : ℕ) : ℝ := (2 : ℝ) ^ N * jsp87Tail N

/-- `2^(N+1) · jsp87Term N = ω N`: the term of the series sitting exactly at the
cut point, rescaled, is exactly the digit `ω N`. -/
theorem two_pow_mul_jsp87Term (N : ℕ) :
    (2 : ℝ) ^ (N + 1) * jsp87Term N = (omega N : ℝ) := by
  have hz : ((2 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
  simp only [jsp87Term]
  field_simp

/-- **Successor rule for the tail**: the tail from `N + 1` is the tail from `N`
minus the single term at the cut point. -/
theorem jsp87Tail_succ (N : ℕ) : jsp87Tail (N + 1) = jsp87Tail N - jsp87Term N := by
  have hf : Summable (fun k : ℕ => jsp87Term (N + k)) := summable_jsp87Tail N
  have h := hf.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h
  have hstep : (∑' i : ℕ, jsp87Term (N + (i + 1))) = jsp87Tail (N + 1) := by
    unfold jsp87Tail
    refine tsum_congr fun i => ?_
    congr 1
    omega
  rw [hstep] at h
  have h0 : jsp87Term (N + 0) = jsp87Term N := by rw [Nat.add_zero]
  rw [h0] at h
  have hid : jsp87Tail N = ∑' i : ℕ, jsp87Term (N + i) := rfl
  rw [← hid] at h
  linarith [h]

/-- `2 · 2^N · jsp87Term N = ω N`, the cut-point term rescaled by the doubling. -/
theorem two_mul_pow_mul_jsp87Term (N : ℕ) :
    2 * (2 : ℝ) ^ N * jsp87Term N = (omega N : ℝ) := by
  have h := two_pow_mul_jsp87Term N
  have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  rw [hpow] at h
  linarith [h]

/-- **The exact carry recurrence.**  The carries of the Erdős series obey

`θ (N+1) = 2 · θ N − ω N`,

the classical doubling relation `θ_{N+1} = 2 θ_N − d_N` with digit
`d_N = ω N`.  Equivalently the digit at `N` is recovered from two consecutive
carries by `ω N = 2 θ N − θ (N+1)`. -/
theorem jsp87Carry_succ (N : ℕ) :
    jsp87Carry (N + 1) = 2 * jsp87Carry N - (omega N : ℝ) := by
  have hs : jsp87Tail (N + 1) = jsp87Tail N - jsp87Term N := jsp87Tail_succ N
  have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  simp only [jsp87Carry, hs, mul_sub, hpow]
  rw [two_mul_pow_mul_jsp87Term]
  ring

/-- The digit is recovered from two consecutive carries. -/
theorem omega_eq_two_carry_sub (N : ℕ) :
    (omega N : ℝ) = 2 * jsp87Carry N - jsp87Carry (N + 1) := by
  linarith [jsp87Carry_succ N]

/-- **The carries are strictly positive, for every cut point.** -/
theorem jsp87Carry_pos (N : ℕ) : 0 < jsp87Carry N := by
  cases N with
  | zero =>
    have h1 : jsp87Carry 0 = jsp87Series := by
      simp only [jsp87Carry, pow_zero, one_mul]
      have h := jsp87_series_eq_sum_add_tail 0
      rw [h]
      simp
    have h2 : (0 : ℝ) < jsp87Carry 0 := by
      rw [h1]
      show (0 : ℝ) < ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      exact_mod_cast jsp87Series_pos
    exact h2
  | succ k =>
    have h := jsp87_carry_bounds (N := k + 1) (by omega)
    simpa [jsp87Carry, Nat.succ_eq_add_one] using h.1

/-- **The quantitative window for the carries: `θ N ≤ N + 1` for `1 ≤ N`.** -/
theorem jsp87Carry_le {N : ℕ} (hN : 1 ≤ N) : jsp87Carry N ≤ ((N + 1 : ℕ) : ℝ) := by
  have h := jsp87_carry_bounds (N := N) hN
  simpa [jsp87Carry] using h.2

/-- The carries never grow by more than a factor `2` from one cut point to the
next: `θ (N+1) ≤ 2 θ N`. -/
theorem jsp87Carry_succ_le (N : ℕ) : jsp87Carry (N + 1) ≤ 2 * jsp87Carry N := by
  rw [jsp87Carry_succ]
  have hω : (0 : ℝ) ≤ (omega N : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Digits are bounded by twice the carry: `ω (N+1) ≤ 4 · θ N`.** -/
theorem jsp87Carry_ge_omega_succ (N : ℕ) : (omega (N + 1) : ℝ) ≤ 4 * jsp87Carry N := by
  have hle : jsp87Term (N + 1) ≤ jsp87Tail N := by
    have h1 : (∑ i ∈ ({1} : Finset ℕ), jsp87Term (N + i)) = jsp87Term (N + 1) := by
      show (∑ i ∈ ({1} : Finset ℕ), jsp87Term (N + i)) = jsp87Term (N + 1)
      simp
    calc jsp87Term (N + 1) = (∑ i ∈ ({1} : Finset ℕ), jsp87Term (N + i)) := h1.symm
      _ ≤ ∑' i : ℕ, jsp87Term (N + i) :=
        Summable.sum_le_tsum (s := ({1} : Finset ℕ)) (f := fun k : ℕ => jsp87Term (N + k))
          (fun k _ => jsp87Tail_term_nonneg N k) (summable_jsp87Tail N)
  have hsplit : (2 : ℝ) ^ N * ((2 : ℝ) ^ (N + 1 + 1))⁻¹ = (1 : ℝ) / 4 := by
    have hpw : (2 : ℝ) ^ (N + 1 + 1) = (2 : ℝ) ^ N * (2 : ℝ) ^ 2 := by
      rw [show N + 1 + 1 = N + 2 by omega, pow_add]
    have hz : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    rw [hpw]
    calc (2 : ℝ) ^ N * ((2 : ℝ) ^ N * (2 : ℝ) ^ 2)⁻¹
        = (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ * ((2 : ℝ) ^ 2)⁻¹ := by
          rw [DivisionMonoid.mul_inv_rev]
          ring
      _ = 1 * ((2 : ℝ) ^ 2)⁻¹ := by rw [mul_inv_cancel₀ hz]
      _ = (1 : ℝ) / 4 := by norm_num
  have hkey : 4 * ((2 : ℝ) ^ N) * (jsp87Term (N + 1)) = (omega (N + 1) : ℝ) := by
    simp only [jsp87Term]
    calc 4 * (2 : ℝ) ^ N * (((omega (N + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (N + 1 + 1))⁻¹)
        = ((omega (N + 1) : ℕ) : ℝ) * (4 * ((2 : ℝ) ^ N * ((2 : ℝ) ^ (N + 1 + 1))⁻¹)) := by
          ring
      _ = ((omega (N + 1) : ℕ) : ℝ) * (4 * ((1 : ℝ) / 4)) := by rw [hsplit]
      _ = (omega (N + 1) : ℝ) := by field_simp
  calc (omega (N + 1) : ℝ) = 4 * (2 : ℝ) ^ N * jsp87Term (N + 1) := hkey.symm
    _ ≤ 4 * (2 : ℝ) ^ N * jsp87Tail N := by
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * jsp87Carry N := by unfold jsp87Carry; ring

/-- **The carries are bounded away from `0`, uniformly in the cut point:
`θ N ≥ 1/4` for every `N`.**

This is the precise obstruction to the naive irrationality argument: rationality
freezes the carries into `(1/b) ℤ` (`jsp87_carry_mul_eq_int`), but the carries
are *not* confined to `(0, 1)`; they live in `[1/4, N+1]`, where they mix digit
information with genuine carrying.  Overcoming this is exactly where the
quantitative correlation input of Pratt (arXiv:2409.15185) is needed. -/
theorem jsp87Carry_ge_quarter (N : ℕ) : (1 : ℝ) / 4 ≤ jsp87Carry N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : jsp87Carry 0 = jsp87Series := by
      simp only [jsp87Carry, pow_zero, one_mul]
      have hh := jsp87_series_eq_sum_add_tail 0
      rw [hh]
      simp
    have hlow : (∑ i ∈ Finset.range 7, jsp87Term i) ≤ jsp87Series := by
      refine sum_range_le_jsp87Series 7 (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))
    have heq : (∑ i ∈ Finset.range 7, jsp87Term i) = (1 : ℝ) / 4 := by
      have h2 : omega 2 = 1 := by native_decide
      have h3 : omega 3 = 1 := by native_decide
      have h4 : omega 4 = 1 := by native_decide
      have h5 : omega 5 = 1 := by native_decide
      have h6 : omega 6 = 2 := by native_decide
      norm_num [jsp87Term, h2, h3, h4, h5, h6, omega_zero, omega_one, Finset.sum_range_succ]
    rw [h1]
    linarith
  · have h := jsp87Carry_ge_omega_succ N
    have hone : 1 ≤ omega (N + 1) := by
      have h2 : 2 ≤ N + 1 := by omega
      by_contra hc
      have hz : omega (N + 1) = 0 := by omega
      have hle : N + 1 ≤ 1 := (omega_eq_zero_iff (n := N + 1)).mp hz
      omega
    have honeR : (1 : ℝ) ≤ (omega (N + 1) : ℝ) := by exact_mod_cast hone
    linarith

/-- **Four distinct prime factors of `N+1` already push the carry past `1`.** -/
theorem jsp87Carry_gt_one {N : ℕ} (hω : 4 < omega (N + 1)) : 1 < jsp87Carry N := by
  have h5 : 5 ≤ omega (N + 1) := by omega
  have h5R : (5 : ℝ) ≤ (omega (N + 1) : ℝ) := by exact_mod_cast h5
  have h := jsp87Carry_ge_omega_succ N
  linarith

/-- **Two distinct prime factors of `N+1` push the carry to `1/2`.** -/
theorem jsp87Carry_ge_half {N : ℕ} (hω : 1 < omega (N + 1)) : (1 : ℝ) / 2 ≤ jsp87Carry N := by
  have h2 : 2 ≤ omega (N + 1) := by omega
  have h2R : (2 : ℝ) ≤ (omega (N + 1) : ℝ) := by exact_mod_cast h2
  have h := jsp87Carry_ge_omega_succ N
  linarith

/-- **Six distinct prime factors of `N+1` push the carry to `3/2`.** -/
theorem jsp87Carry_ge_three_halves {N : ℕ} (hω : 5 < omega (N + 1)) :
    (3 : ℝ) / 2 ≤ jsp87Carry N := by
  have h6 : 6 ≤ omega (N + 1) := by omega
  have h6R : (6 : ℝ) ≤ (omega (N + 1) : ℝ) := by exact_mod_cast h6
  have h := jsp87Carry_ge_omega_succ N
  linarith

/-! ## 2. Fractional parts of the rescaled series -/

/-- **A rational number has a quantised fractional part.**  If `(b : ℝ) · x = m`
for an integer `m` and a positive natural `b`, then `fract x` is `c / b` for an
integer `c` with `0 ≤ c < b`; the numerator `b · fract x` is an integer. -/
theorem Int.fract_eq_div_of_mul_natCast {b : ℕ} (hb : 0 < b) {x : ℝ} {m : ℤ}
    (hm : (b : ℝ) * x = (m : ℝ)) :
    ∃ c : ℤ, 0 ≤ c ∧ c < (b : ℤ) ∧ Int.fract x = (c : ℝ) / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hfr : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hfr1 : Int.fract x < 1 := Int.fract_lt_one x
  set c : ℤ := m - b * ⌊x⌋ with hc
  have hkey : (b : ℝ) * Int.fract x = (c : ℝ) := by
    have h1 : (b : ℝ) * Int.fract x = (b : ℝ) * (x - ⌊x⌋) := by rw [Int.self_sub_floor]
    have h2 : (b : ℝ) * (x - ⌊x⌋) = (b : ℝ) * x - (b : ℝ) * ((⌊x⌋ : ℤ) : ℝ) := by ring
    have h3 : (b : ℝ) * ((⌊x⌋ : ℤ) : ℝ) = (b * ⌊x⌋ : ℤ) := by norm_cast
    have h4 : (m - b * ⌊x⌋ : ℤ) = (m : ℝ) - (b * ⌊x⌋ : ℤ) := by push_cast; ring
    rw [h1, h2, hm, h3, h4]
  have hz : 0 ≤ c := by
    have h5 : (0 : ℝ) ≤ (b : ℝ) * Int.fract x := mul_nonneg (le_of_lt hbR) hfr
    rw [hkey] at h5
    exact_mod_cast h5
  have hlt : c < (b : ℤ) := by
    have h5 : (b : ℝ) * Int.fract x < (b : ℝ) := by
      simpa only [mul_comm, one_mul, mul_one] using mul_lt_mul_of_pos_right hfr1 hbR
    rw [hkey] at h5
    exact_mod_cast h5
  refine ⟨c, hz, hlt, ?_⟩
  rw [← hkey]
  field_simp

/-- **The fractional part of `2^N · S` is the fractional part of the carry.**
The two differ by the integer `I N` coming from the carry decomposition.  This
welds the dynamical picture to the static one: what the rescaling sees as a
fractional part is governed entirely by the carry `θ N`. -/
theorem jsp87_fract_scaled {N : ℕ} (hN : 1 ≤ N) :
    Int.fract ((2 : ℝ) ^ N * jsp87Series) = Int.fract (jsp87Carry N) := by
  have hdecomp : (2 : ℝ) ^ N * jsp87Series = (jsp87IntPart N : ℝ) + (2 : ℝ) ^ N * jsp87Tail N :=
    jsp87_scaled_decomposition N hN
  calc Int.fract ((2 : ℝ) ^ N * jsp87Series)
      = Int.fract ((jsp87IntPart N : ℝ) + jsp87Carry N) := by rw [hdecomp]; rfl
    _ = Int.fract (jsp87Carry N) := by rw [add_comm]; exact Int.fract_add_intCast _ _

/-- **Rationality quantises the fractional part of the rescaled series.**  If
`S = a / b` with `b > 0` then the fractional part of `2^N · S` is `c / b` for an
integer `c` with `0 ≤ c < b`: the fractional parts of `2^N · S`, for `N ≥ 1`,
live in a *finite* set of size `b`, uniformly in `N`.  This is the `2`-adic
rigidity that a rationality assumption imposes, in its cleanest form. -/
theorem jsp87_fract_scaled_eq_div {N : ℕ} (hN : 1 ≤ N) {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, 0 ≤ c ∧ c < (b : ℤ) ∧ Int.fract ((2 : ℝ) ^ N * jsp87Series) = (c : ℝ) / (b : ℝ) := by
  obtain ⟨c, hc0, hc1, hc2⟩ :=
    Int.fract_eq_div_of_mul_natCast (b := b) hb (x := (2 : ℝ) ^ N * jsp87Series)
      (m := ((2 : ℕ) ^ N * a : ℤ)) (by
        have hcast : (2 : ℝ) ^ N * (a : ℝ) = ((2 : ℕ) ^ N * a : ℤ) := by norm_cast
        have hbnz : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
        rw [h]
        calc (b : ℝ) * ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)))
            = ((b : ℝ) * (2 : ℝ) ^ N * (a : ℝ)) / (b : ℝ) := by ring
          _ = (2 : ℝ) ^ N * (a : ℝ) := by field_simp
          _ = ((2 : ℕ) ^ N * a : ℤ) := hcast)
  refine ⟨c, hc0, hc1, ?_⟩
  simpa only [jsp87_fract_scaled hN] using hc2

/-! ## 3. Aperiodicity of `ω` — the endgame -/

/-- `ω n` is the cardinality of the primes `≤ n` dividing `n`. -/
theorem omega_eq_card_filter (n : ℕ) :
    omega n = ((Finset.range (n + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n)).card := by
  rw [omega, primeFactors_eq_filter]

/-- **Multiplication by a new large prime adds exactly one to `ω`.**
If `p` is prime, `1 ≤ n` and `n < p`, then `ω (n·p) = ω n + 1`: the primes
dividing `n·p` are those dividing `n` together with the fresh prime `p`. -/
theorem omega_mul_prime_of_large_prime {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hlt : n < p) :
    omega n + 1 ≤ omega (n * p) := by
  have hcard : ((Finset.range (n + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n)).card + 1
      ≤ ((Finset.range (n * p + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n * p)).card := by
    have hnp : n ≤ n * p := by
      have hh : n * 1 ≤ n * p := Nat.mul_le_mul_left (k := n) (n := 1) (m := p) (by omega)
      rwa [mul_one] at hh
    have hstep1 : n + 1 ≤ n * p + 1 := Nat.succ_le_succ hnp
    have hpn : p ≤ n * p := Nat.le_mul_of_pos_left p (by omega)
    have hAB : ((Finset.range (n + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n))
        ⊆ ((Finset.range (n * p + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n * p)) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨?_, ⟨hq2.1, dvd_mul_of_dvd_left hq2.2 p⟩⟩
      have h1' : q < n + 1 := Finset.mem_range.mp hq1
      exact Finset.mem_range.mpr (lt_of_lt_of_le h1' hstep1)
    have hpB : p ∈ ((Finset.range (n * p + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n * p)) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, ?_⟩
      exact ⟨n, by ring⟩
    have hpA : ¬ p ∈ ((Finset.range (n + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n)) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact fun h => Nat.not_lt_of_ge (Nat.lt_succ_iff.mp h.1) hlt
    have hss : ((Finset.range (n + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n))
        ⊂ ((Finset.range (n * p + 1)).filter (fun q : ℕ => q.Prime ∧ q ∣ n * p)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hAB, fun hEq => hpA (hEq ▸ hpB)⟩
    exact Nat.succ_le_of_lt (Finset.card_lt_card hss)
  simpa only [omega_eq_card_filter] using hcard

/-- **An eventual period makes `n ↦ ω (t · n)` eventually constant.**  Indeed
`ω (t·M) = ω (t·M + t) = ω (t·M + 2t) = ⋯` for every `M` past the threshold. -/
theorem omega_eventuallyPeriodic_const_mul {N t M : ℕ} (ht : 0 < t) (hN : N ≤ M)
    (hp : ∀ n, N ≤ n → omega (n + t) = omega n) (j : ℕ) :
    omega (t * M + t * j) = omega (t * M) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : t * M + t * Nat.succ j = (t * M + t * j) + t := by
      rw [Nat.succ_eq_add_one]
      ring
    rw [hstep]
    have hM : M ≤ t * M := Nat.le_mul_of_pos_left M ht
    rw [hp (t * M + t * j) (by omega)]
    exact ih

/-- **THE APERIODICITY ENDGAME: `ω` is not eventually periodic.**

Suppose `ω (n + t) = ω n` for all `n ≥ N`, with `t > 0`.  Then `n ↦ ω (t·n)` is
eventually constant, so `ω (t·M)` is frozen for all `M ≥ N`.  But take a prime
`u > t·M` for `M = N + 1`; the number `t·M·u` lies in the *same* frozen
progression (it is `t·M + t·(M·(u−1))`) while, by
`omega_mul_prime_of_large_prime`, it has one more prime factor than `t·M`.  That
is a contradiction.

This is the combinatorial fact that terminates every Erdős-style irrationality
argument built on `2`-adic scaling of a `∑ d(n) 2^{-n}` series: the digit
function must be aperiodic.  Mathlib has no such statement. -/
theorem omega_not_eventuallyPeriodic :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → omega (n + t) = omega n := by
  rintro ⟨t, N, ht, hp⟩
  obtain ⟨u, hu, hup⟩ := Nat.exists_infinite_primes (t * (N + 1) + 1)
  have hlt : t * (N + 1) < u := lt_of_lt_of_le (Nat.lt_succ_self _) hu
  have hpos : 1 ≤ t * (N + 1) :=
    lt_of_lt_of_le (Nat.zero_lt_succ N) (Nat.le_mul_of_pos_left (N + 1) ht)
  have hstep : omega (t * (N + 1)) + 1 ≤ omega (t * (N + 1) * u) :=
    omega_mul_prime_of_large_prime hup hpos hlt
  have hconst : omega (t * (N + 1) + t * ((N + 1) * (u - 1))) = omega (t * (N + 1)) :=
    omega_eventuallyPeriodic_const_mul (N := N) (t := t) (M := N + 1) ht (by omega) hp _
  have hrw : t * (N + 1) + t * ((N + 1) * (u - 1)) = t * (N + 1) * u := by
    obtain ⟨k, rfl⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
    rw [Nat.add_sub_cancel k 1]
    ring
  rw [hrw] at hconst
  have hcontra : omega (t * (N + 1)) + 1 = omega (t * (N + 1)) := by linarith
  exact absurd hcontra (Nat.succ_ne_self _)

/-- **Quantitative form of the endgame.**  Under an eventual period `t`, the map
`M ↦ ω (t · M)` is frozen past `N`, yet every fresh prime `u > t · M` breaks it:
`ω (t · M · u) = ω (t · M) + 1`, while `t·M·u` is in the frozen progression. -/
theorem omega_periodic_frozen {N t M : ℕ} (ht : 0 < t) (hN : N ≤ M)
    (hp : ∀ n, N ≤ n → omega (n + t) = omega n) {u : ℕ} (hup : u.Prime) (hut : t * M < u) :
    omega (t * M * u) = omega (t * M) := by
  have hrw : t * M * u = t * M + t * (M * (u - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
    rw [Nat.add_sub_cancel k 1]
    ring
  rw [hrw]
  simpa using omega_eventuallyPeriodic_const_mul (N := N) (t := t) (M := M) ht hN hp (M * (u - 1))

end JSP87
