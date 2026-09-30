/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.OrbitArith
import JSPProblem.PeriodEquation
import JSPProblem.BlockPeriod

/-!
# Round 65 -- the Mersenne modulus of the `ω`-window, and the denominator spectrum

## The gap in the development

Rounds 46, 48, 50, 52 and 64 all manipulate the *digit block*
`B N t = jsp87DigitBlock N t` and the *`ω`-window*
`Ω N t = ∑_{j<t} ω (N+j) 2^{t−1−j}`, and round 52 (`PeriodEquation.lean`)
stated the **window–block equation**

`c (N+t) + Ω N t = 2^t · c N + B N t`

*under the hypothesis that the binary digits are eventually periodic* -- and then
concluded from it the **window congruence**

`(2 : ℤ)^t − 1 ∣ c (N+t) − c N + Ω N t − B N t`,  with quotient exactly `c N`.

That congruence is the "obstruction" recorded as `round51_blocker`
(`jsp87_window_congr_fails`) in `acceptance.json`.  **It is vacuous.**  The
quantity on the left is an *identity*:

`c (N+t) − c N + Ω N t − B N t = (2^t − 1) · c N`

for **every** `N ≥ 1` and **every** `t`, with no hypothesis whatsoever
(`jsp87_window_residue` below).  So the divisibility can never fail, the
"blocker" cannot be attacked because it is false, and the recorded gate status
is misleading.  This round proves the identity, refutes the recorded blocker
(`not_jsp87_window_congr_fails`), and replaces it by a **well-posed** statement.

The replacement is the *reduced Mersenne obstruction*: if `S = a/b` in lowest
terms and the digits are eventually periodic from `M` with period `t`, then the
`t`-digit block is a multiple of

`u = (2^t − 1) / jsp87OddPart b`,

and the minimal period satisfies `t ≤ jsp87OddPart b`.  Mathlib has no
statement about the base-`2` expansion of a real number, hence none of this.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87_windowBlock_identity` | **THE WINDOW–BLOCK EQUATION, UNCONDITIONALLY**: `B N t = Ω N t + c (N+t) − 2^t c N` for `1 ≤ N`.  Round 52 needed eventual periodicity |
| `jsp87_window_residue` | **THE RESIDUE IS AN IDENTITY**: `c (N+t) − c N + Ω N t − B N t = ((2 : ℤ)^t − 1) · c N` |
| `not_jsp87_window_congr_fails` | **ROUND 51'S RECORDED BLOCKER `jsp87_window_congr_fails` IS VACUOUS** — refuted, machine-checked |
| `jsp87_window_block_dvd_iff` | the *honest* obstruction: `(2^t−1) ∣ Ω N t − B N t ↔ (2^t−1) ∣ c (N+t) − c N` |
| `jsp87_carryExcess_window_bounds` | **the carry excess along a window, unconditionally**: `c (N+t) ≤ 2^t c N` |
| `jsp87_digitBlock_eq_fracCarry` | **the block as a difference of orbit points**: `B N t = 2^t f N − f (N+t)`, `f N = Int.fract (θ N)` |
| `jsp87_fracCarry_eq_oddPart_num` | **THE ORBIT POINT LIVES ON THE ODD PART**: `b' · f N = n < b'` for `v_2(b) ≤ N` |
| `jsp87_digitBlock_dvd_reduced_mer` | **THE REDUCED MERSENNE OBSTRUCTION**: `(2^t−1)/jsp87OddPart b ∣ B N t` |
| `jsp87_digitPeriod_le_oddPart` | **THE PERIOD IS AT MOST THE ODD PART OF THE DENOMINATOR**: a minimal period `t` satisfies `t ≤ jsp87OddPart b` |
| `jsp87_denominator_ge_period` | `2^{v_2(b)} · t ≤ b`: the denominator dominates the period |
| `jsp87_blockNotDvd_impossible` | **THE FIFTH IRRATIONALITY CRITERION** (for a reduced value `a/b`) |
-/

namespace JSP87

private theorem one_le_two_pow_nat (k : ℕ) : 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

private theorem one_lt_pow_two_nat (k : ℕ) (hk : 1 ≤ k) : 1 < 2 ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ]
  have hm := one_le_two_pow_nat m
  nlinarith

private theorem pow_two_dvd_pow_two {a b : ℕ} (h : a ≤ b) : 2 ^ a ∣ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, Nat.mul_comm]
  exact Nat.dvd_mul_left _ _

/-! ## 0. A weighted shift identity, from scratch

For `c : ℕ → G` in an additive commutative group, the weight `2^{t−1−j}` shifts by
one place when `j ↦ j+1`, so the shifted sum telescopes:

`∑_{j<t} c (N+j+1) 2^{t−1−j} = 2 ∑_{j<t} c (N+j) 2^{t−1−j} − 2^t c N + c (N+t)`.

The two versions needed here (`ℝ` and `ℤ`) are proved by induction on `t`. -/

private theorem sum_split_diff (c d : ℕ → ℝ) (N t : ℕ)
    (hrel : ∀ j, d (N + j) = 2 * c (N + j) - c ((N + j) + 1)) :
    (∑ j ∈ Finset.range t, d (N + j) * 2 ^ (t - 1 - j))
      = 2 * (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - 1 - j))
        - ∑ j ∈ Finset.range t, c ((N + j) + 1) * 2 ^ (t - 1 - j) := by
  have key : ∀ j ∈ Finset.range t, d (N + j) * 2 ^ (t - 1 - j)
      = 2 * (c (N + j) * 2 ^ (t - 1 - j)) - c ((N + j) + 1) * 2 ^ (t - 1 - j) := by
    intro j _
    rw [hrel]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem sum_shift_real (c : ℕ → ℝ) (N : ℕ) (t : ℕ) :
    (∑ j ∈ Finset.range t, c ((N + j) + 1) * 2 ^ (t - 1 - j))
      = 2 * (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - 1 - j))
        - 2 ^ t * c N + c (N + t) := by
  induction t generalizing N with
  | zero => simp
  | succ t ih =>
      simp only [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      have key : (∑ j ∈ Finset.range t, c (N + j + 1) * 2 ^ (t - j))
          = 2 * (∑ j ∈ Finset.range t, c (N + j + 1) * 2 ^ (t - 1 - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        have h1 : t - j = t - 1 - j + 1 := by omega
        rw [h1, pow_succ]
        ring
      have key2 : (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - j))
          = 2 * (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - 1 - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        have h1 : t - j = t - 1 - j + 1 := by omega
        rw [h1, pow_succ]
        ring
      rw [key, key2, ih]
      ring

private theorem sum_split (f g h : ℕ → ℤ) (t : ℕ) :
    (∑ j ∈ Finset.range t, (f j * 2 ^ (t - 1 - j) + g j * 2 ^ (t - 1 - j)
        - 2 * (h j * 2 ^ (t - 1 - j))))
      = (∑ j ∈ Finset.range t, f j * 2 ^ (t - 1 - j))
        + (∑ j ∈ Finset.range t, g j * 2 ^ (t - 1 - j))
        - 2 * (∑ j ∈ Finset.range t, h j * 2 ^ (t - 1 - j)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

private theorem sum_split_real (c : ℕ → ℝ) (N t : ℕ) :
    (∑ j ∈ Finset.range t, (2 * (c (N + j) * 2 ^ (t - 1 - j))
        - c ((N + j) + 1) * 2 ^ (t - 1 - j)))
      = 2 * (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - 1 - j))
        - ∑ j ∈ Finset.range t, c ((N + j) + 1) * 2 ^ (t - 1 - j) := by
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

private theorem sum_shift_int (c : ℕ → ℤ) (N : ℕ) (t : ℕ) :
    (∑ j ∈ Finset.range t, c ((N + j) + 1) * 2 ^ (t - 1 - j))
      = 2 * (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - 1 - j))
        - 2 ^ t * c N + c (N + t) := by
  induction t generalizing N with
  | zero => simp
  | succ t ih =>
      simp only [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      have key : (∑ j ∈ Finset.range t, c (N + j + 1) * 2 ^ (t - j))
          = 2 * (∑ j ∈ Finset.range t, c (N + j + 1) * 2 ^ (t - 1 - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        have h1 : t - j = t - 1 - j + 1 := by omega
        rw [h1, pow_succ]
        ring
      have key2 : (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - j))
          = 2 * (∑ j ∈ Finset.range t, c (N + j) * 2 ^ (t - 1 - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        have h1 : t - j = t - 1 - j + 1 := by omega
        rw [h1, pow_succ]
        ring
      have hmain := ih N
      rw [key, key2, hmain]
      ring

/-! ## 1. The window–block equation is an identity, not a conditional -/

/-- **THE WINDOW–BLOCK EQUATION, UNCONDITIONALLY.**  For `1 ≤ N` and any `t`,

`jsp87DigitBlock N t = (jsp87OmegaWindow N t : ℤ) + jsp87CarryExcess (N+t) − 2^t · jsp87CarryExcess N`.

Round 52 (`jsp87_window_block_equation`) proved this *only* under the hypothesis
that the binary digits are eventually periodic with period `t`; it is in fact a
pure `ℤ`-identity, valid for every cut point and every window. -/
theorem jsp87_windowBlock_identity {N t : ℕ} (hN : 1 ≤ N) :
    jsp87DigitBlock N t
      = (jsp87OmegaWindow N t : ℤ) + jsp87CarryExcess (N + t)
        - 2 ^ t * jsp87CarryExcess N := by
  have hbk : ∀ j ∈ Finset.range t,
      jsp87Digit (N + j)
        = (omega (N + j) : ℤ) + jsp87CarryExcess ((N + j) + 1)
          - 2 * jsp87CarryExcess (N + j) := by
    intro j _
    have hj : 1 ≤ N + j := by omega
    have h := jsp87_digit_bookkeeping (N := N + j) hj
    exact_mod_cast h
  have hcast : ∑ j ∈ Finset.range t, ((omega (N + j) : ℤ) * 2 ^ (t - 1 - j))
      = (jsp87OmegaWindow N t : ℤ) := by
    unfold jsp87OmegaWindow
    push_cast
    rfl
  unfold jsp87DigitBlock
  calc jsp87DigitBlock N t
      = ∑ j ∈ Finset.range t,
          ((omega (N + j) : ℤ) * 2 ^ (t - 1 - j)
            + jsp87CarryExcess ((N + j) + 1) * 2 ^ (t - 1 - j)
            - 2 * (jsp87CarryExcess (N + j) * 2 ^ (t - 1 - j))) := by
        exact Finset.sum_congr rfl (fun j hj => by rw [hbk j hj]; ring)
    _ = (jsp87OmegaWindow N t : ℤ)
          + (∑ j ∈ Finset.range t, jsp87CarryExcess ((N + j) + 1) * 2 ^ (t - 1 - j))
          - 2 * (∑ j ∈ Finset.range t, jsp87CarryExcess (N + j) * 2 ^ (t - 1 - j)) := by
        rw [sum_split, hcast]
    _ = (jsp87OmegaWindow N t : ℤ) + jsp87CarryExcess (N + t)
          - 2 ^ t * jsp87CarryExcess N := by
        rw [sum_shift_int]
        ring

/-- The same statement, in round 52's orientation: the `ω`-window, the carry
excess one period ahead, twice the carry excess and the digit block determine
each other -- **with no hypothesis**. -/
theorem jsp87_window_block_eq {N t : ℕ} (hN : 1 ≤ N) :
    jsp87CarryExcess (N + t) + (jsp87OmegaWindow N t : ℤ)
      = 2 ^ t * jsp87CarryExcess N + jsp87DigitBlock N t := by
  have h := jsp87_windowBlock_identity (t := t) hN
  linarith

/-- **THE WINDOW IS THE BLOCK PLUS THE CARRY SHIFT.**  For `1 ≤ N`,
`(jsp87OmegaWindow N t : ℤ) − jsp87DigitBlock N t = 2^t · c N − c (N+t)`. -/
theorem jsp87_omegaWindow_sub_block {N t : ℕ} (hN : 1 ≤ N) :
    (jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t
      = 2 ^ t * jsp87CarryExcess N - jsp87CarryExcess (N + t) := by
  have h := jsp87_windowBlock_identity (t := t) hN
  linarith

/-- **THE RESIDUE IS AN IDENTITY.**  For `1 ≤ N`,

`c (N+t) − c N + Ω N t − B N t = ((2 : ℤ)^t − 1) · c N`.

So the `ℤ`-divisibility recorded as round 51's "obstruction" holds at *every* cut
point, with quotient exactly `c N`. -/
theorem jsp87_window_residue {N t : ℕ} (hN : 1 ≤ N) :
    jsp87CarryExcess (N + t) - jsp87CarryExcess N + (jsp87OmegaWindow N t : ℤ)
        - jsp87DigitBlock N t
      = ((2 : ℤ) ^ t - 1) * jsp87CarryExcess N := by
  have h := jsp87_windowBlock_identity (t := t) hN
  rw [h]
  ring

/-- **THE WINDOW CONGRUENCE ALWAYS HOLDS.**  For `1 ≤ N`,
`(2 : ℤ)^t − 1 ∣ c (N+t) − c N + Ω N t − B N t`, with quotient `c N`. -/
theorem jsp87_window_congr_always {N t : ℕ} (hN : 1 ≤ N) :
    (2 : ℤ) ^ t - 1
      ∣ jsp87CarryExcess (N + t) - jsp87CarryExcess N
        + (jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t := by
  have h := jsp87_window_residue (t := t) hN
  refine ⟨jsp87CarryExcess N, ?_⟩
  rw [h]

/-- **ROUND 51'S RECORDED BLOCKER `jsp87_window_congr_fails` IS VACUOUS.**
There is **no** cut point `N` and **no** period `t` at which the divisibility
`(2 : ℤ)^t − 1 ∣ c (N+t) − c N + Ω N t − B N t` fails; it holds identically
(`jsp87_window_residue`).  The obstruction recorded in `acceptance.json` under
`round51_blocker` must therefore be replaced by `jsp87_window_block_dvd_iff`
below, which is non-vacuous as soon as `2 ≤ t`. -/
theorem not_jsp87_window_congr_fails :
    ¬ (∃ (N t : ℕ), 1 ≤ N ∧
        ¬ ((2 : ℤ) ^ t - 1 ∣ jsp87CarryExcess (N + t) - jsp87CarryExcess N
            + (jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t)) := by
  rintro ⟨N, t, hN, h⟩
  exact h (jsp87_window_congr_always hN)

/-- **THE HONEST OBSTRUCTION.**  For `1 ≤ N`,

`(2 : ℤ)^t − 1 ∣ Ω N t − B N t  ↔  (2 : ℤ)^t − 1 ∣ c (N+t) − c N`.

The two differ by the identity `jsp87_window_residue`, so rationality together
with eventual periodicity of the digits with period `t` would force the carry
excess `c N` to be periodic modulo the Mersenne number `2^t − 1`.  For `t = 1`
this is vacuous (`2^1 − 1 = 1`); for `t ≥ 2` it is a genuine condition. -/
theorem jsp87_window_block_dvd_iff {N t : ℕ} (hN : 1 ≤ N) :
    (2 : ℤ) ^ t - 1 ∣ (jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t
      ↔ (2 : ℤ) ^ t - 1 ∣ jsp87CarryExcess (N + t) - jsp87CarryExcess N := by
  have hsum : (jsp87CarryExcess (N + t) - jsp87CarryExcess N)
      + ((jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t)
        = ((2 : ℤ) ^ t - 1) * jsp87CarryExcess N := by
    have h := jsp87_window_residue (t := t) hN
    linarith
  have hm : (2 : ℤ) ^ t - 1
      ∣ (jsp87CarryExcess (N + t) - jsp87CarryExcess N)
        + ((jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t) := by
    refine ⟨jsp87CarryExcess N, ?_⟩
    rw [hsum]
  constructor
  · intro h1
    exact (Int.dvd_iff_dvd_of_dvd_add hm).mpr h1
  · intro h1
    exact (Int.dvd_iff_dvd_of_dvd_add hm).mp h1

/-! ## 2. The carry excess along a window -- unconditionally -/

/-- **THE CARRY EXCESS AT MOST `2^t`-FOLD PER WINDOW, UNCONDITIONALLY.**  For
`2 ≤ N` and any `t`, `c (N+t) ≤ 2^t · c N`.  Round 52
(`jsp87_carryExcess_window_le`) could only prove this under eventual
periodicity of the digits; it follows from the identity alone. -/
theorem jsp87_carryExcess_window_le_uncond {N t : ℕ} (hN : 2 ≤ N) :
    (jsp87CarryExcess (N + t) : ℝ) ≤ 2 ^ t * (jsp87CarryExcess N : ℝ) := by
  have hZ := jsp87_window_block_eq (t := t) (by omega : (1 : ℕ) ≤ N)
  have heq : (jsp87CarryExcess (N + t) : ℝ) + (jsp87OmegaWindow N t : ℝ)
      = 2 ^ t * (jsp87CarryExcess N : ℝ) + (jsp87DigitBlock N t : ℝ) := by
    exact_mod_cast hZ
  have hB : (jsp87DigitBlock N t : ℝ) ≤ 2 ^ t - 1 := by
    have h := (jsp87_digitBlock_bounds N t).2
    have h' : jsp87DigitBlock N t ≤ 2 ^ t - 1 := by omega
    exact_mod_cast h'
  have hc : (0 : ℝ) ≤ (jsp87CarryExcess (N + t) : ℝ) := by
    have h := jsp87CarryExcess_nonneg (N + t)
    exact_mod_cast h
  have hO : (2 : ℝ) ^ t - 1 ≤ (jsp87OmegaWindow N t : ℝ) := by
    have h := jsp87OmegaWindow_ge (N := N) (t := t) hN
    have hle : ((2 ^ t - 1 : ℕ) : ℝ) ≤ (jsp87OmegaWindow N t : ℝ) := by
      exact_mod_cast h
    have hh : ((2 ^ t - 1 : ℕ) : ℝ) = (2 : ℝ) ^ t - 1 := by
      calc ((2 ^ t - 1 : ℕ) : ℝ) = ((2 ^ t : ℕ) : ℝ) - ((1 : ℕ) : ℝ) :=
            Nat.cast_sub (one_le_two_pow_nat t)
        _ = ((2 ^ t : ℕ) : ℝ) - 1 := by norm_num
        _ = (2 : ℝ) ^ t - 1 := by push_cast; ring
    exact hh ▸ hle
  linarith

/-- **THE CARRY EXCESS AT `N+t` IS ALSO BOUNDED FROM BELOW.**  For `2 ≤ N`,
`2^t · c N − Ω N t ≤ c (N+t)`. -/
theorem jsp87_carryExcess_window_ge_uncond {N t : ℕ} (hN : 2 ≤ N) :
    2 ^ t * (jsp87CarryExcess N : ℝ) - (jsp87OmegaWindow N t : ℝ)
      ≤ (jsp87CarryExcess (N + t) : ℝ) := by
  have hZ := jsp87_window_block_eq (t := t) (by omega : (1 : ℕ) ≤ N)
  have heq : (jsp87CarryExcess (N + t) : ℝ) + (jsp87OmegaWindow N t : ℝ)
      = 2 ^ t * (jsp87CarryExcess N : ℝ) + (jsp87DigitBlock N t : ℝ) := by
    exact_mod_cast hZ
  have hB : (0 : ℝ) ≤ (jsp87DigitBlock N t : ℝ) := by
    have h := (jsp87_digitBlock_bounds N t).1
    exact_mod_cast h
  linarith

/-- **THE `ω`-WINDOW IS SQUEEZED BY THE CARRY EXCESS.**  For `1 ≤ N`,
`2^t c N − c (N+t) ≤ Ω N t ≤ 2^t c N + 2^t − 1 − c (N+t)`. -/
theorem jsp87_omegaWindow_carryExcess_bounds {N t : ℕ} (hN : 1 ≤ N) :
    2 ^ t * jsp87CarryExcess N - jsp87CarryExcess (N + t)
        ≤ (jsp87OmegaWindow N t : ℤ)
      ∧ (jsp87OmegaWindow N t : ℤ)
        ≤ 2 ^ t * jsp87CarryExcess N + (2 ^ t - 1) - jsp87CarryExcess (N + t) := by
  have h := jsp87_window_block_eq (t := t) hN
  have hB : (0 : ℤ) ≤ jsp87DigitBlock N t := (jsp87_digitBlock_bounds N t).1
  have hB' : jsp87DigitBlock N t ≤ 2 ^ t - 1 := by
    have h := (jsp87_digitBlock_bounds N t).2
    omega
  constructor
  · linarith
  · linarith

/-- **THE CARRY EXCESS VANISHES ONLY AT THE FIRST TWO CUT POINTS.**
`jsp87CarryExcess N = 0 ↔ N ≤ 1`: `c 0 = ⌊S⌋ = 0` and `c 1 = ⌊2S⌋ = 0`
(round 47), while `c N ≥ 1` for `2 ≤ N` (round 44). -/
theorem jsp87CarryExcess_zero_iff_cutPoint {N : ℕ} : jsp87CarryExcess N = 0 ↔ N ≤ 1 := by
  constructor
  · intro hz
    have h2 : ¬ 2 ≤ N := by
      intro hh
      have := jsp87CarryExcess_ge_one hh
      omega
    omega
  · intro hN
    rcases N.eq_zero_or_pos with rfl | hpos
    · exact jsp87CarryExcess_zero
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      by_cases hk : k = 0
      · subst hk
        have hfloor := jsp87_floor_scaled (N := 1) (by omega)
        have hI : jsp87IntPart 1 = 0 := by
          simp only [jsp87IntPart, Finset.sum_range_one]
          norm_num [omega]
        have hf' : ⌊(2 : ℝ) ^ 1 * jsp87Series⌋ = jsp87CarryExcess 1 := by
          rw [hI] at hfloor
          simpa only [zero_add] using hfloor
        rw [← hf']
        simpa only [pow_one] using jsp87_floor_two_S
      · exfalso
        have h2 := jsp87CarryExcess_ge_one (N := k + 1) (by omega)
        omega

/-- **THE RESIDUE IS ZERO ONLY AT `N = 1`.**  For `1 ≤ N`, `1 ≤ t`,
`c (N+t) − c N + Ω N t − B N t = 0 ↔ N = 1`. -/
theorem jsp87_window_residue_eq_zero_iff {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t) :
    (jsp87CarryExcess (N + t) - jsp87CarryExcess N + (jsp87OmegaWindow N t : ℤ)
        - jsp87DigitBlock N t = 0) ↔ N = 1 := by
  constructor
  · intro h0
    have h := jsp87_window_residue (t := t) hN
    rw [h] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · have h3 : 1 < ((2 : ℤ) ^ t) := by
        nlinarith [one_lt_pow_two_nat t ht]
      exact absurd h1 (by omega)
    · have h3 : N ≤ 1 := (jsp87CarryExcess_zero_iff_cutPoint).mp h2
      omega
  · intro h1
    subst h1
    have hz : jsp87CarryExcess 1 = 0 :=
      (jsp87CarryExcess_zero_iff_cutPoint).mpr (by omega)
    rw [hz]
    have h := jsp87_window_residue (t := t) (by omega : (1 : ℕ) ≤ 1)
    rw [hz] at h
    simpa using h

/-- **THE RESIDUE IS AT LEAST THE MERSENNE NUMBER PAST THE FIRST CUT POINT.**
For `2 ≤ N`, `(2 : ℤ)^t − 1 ≤ c (N+t) − c N + Ω N t − B N t`. -/
theorem jsp87_window_residue_ge {N t : ℕ} (hN : 2 ≤ N) :
    ((2 : ℤ) ^ t - 1)
      ≤ jsp87CarryExcess (N + t) - jsp87CarryExcess N
        + (jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t := by
  have h := jsp87_window_residue (t := t) (by omega : (1 : ℕ) ≤ N)
  have hc : (1 : ℤ) ≤ jsp87CarryExcess N := jsp87CarryExcess_ge_one hN
  have hnonneg : (0 : ℤ) ≤ (2 : ℤ) ^ t - 1 := by
    have h1 : (1 : ℤ) ≤ (2 : ℤ) ^ t := by
      exact_mod_cast (one_le_two_pow_nat t)
    linarith
  calc (2 : ℤ) ^ t - 1 = 1 * ((2 : ℤ) ^ t - 1) := by ring
    _ ≤ jsp87CarryExcess N * ((2 : ℤ) ^ t - 1) := Int.mul_le_mul_of_nonneg_right hc hnonneg
    _ = ((2 : ℤ) ^ t - 1) * jsp87CarryExcess N := mul_comm _ _
    _ = jsp87CarryExcess (N + t) - jsp87CarryExcess N
        + (jsp87OmegaWindow N t : ℤ) - jsp87DigitBlock N t := h.symm

/-! ## 3. The orbit point lives on the odd part of the denominator -/

/-- **THE RESIDUE ORBIT IS INVISIBLE TO THE `2`-PART OF THE DENOMINATOR.**
For `0 < b` and `jsp87Val2 b ≤ N`, `2^{v_2(b)} ∣ (2^N a mod b)`. -/
theorem jsp87OrbitNum_dvd_two_pow {a b N : ℕ} (hb : 0 < b) (hval : jsp87Val2 b ≤ N) :
    2 ^ jsp87Val2 b ∣ jsp87OrbitNum a b N := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hb2 : 2 ^ jsp87Val2 b ∣ b := jsp87Val2_dvd hbne
  have hmod : jsp87OrbitNum a b N = 2 ^ N * a % b := rfl
  have hA : ((2 ^ N * a : ℕ) : ℤ) = (b : ℤ) * ((2 ^ N * a / b : ℕ) : ℤ)
      + (jsp87OrbitNum a b N : ℤ) := by
    have hk := Nat.div_add_mod (2 ^ N * a) b
    rw [← hmod] at hk
    exact_mod_cast hk.symm
  have hsub : ((2 : ℤ) ^ N) * (a : ℤ) = ((2 ^ N * a : ℕ) : ℤ) := by
    push_cast
    ring
  have h2' : ((2 : ℤ) ^ jsp87Val2 b) ∣ (2 : ℤ) ^ N := by
    simpa using (Int.natCast_dvd_natCast).mpr (pow_two_dvd_pow_two hval)
  have h1 : ((2 : ℤ) ^ jsp87Val2 b) ∣ ((2 : ℤ) ^ N) * (a : ℤ) :=
    dvd_mul_of_dvd_left h2' _
  have hb2' : ((2 : ℤ) ^ jsp87Val2 b) ∣ (b : ℤ) := by
    simpa using (Int.natCast_dvd_natCast).mpr hb2
  have hq : ((2 : ℤ) ^ jsp87Val2 b) ∣ (b : ℤ) * ((2 ^ N * a / b : ℕ) : ℤ) :=
    dvd_mul_of_dvd_left hb2' _
  have h4 : ((2 : ℤ) ^ jsp87Val2 b) ∣ (b : ℤ) * ((2 ^ N * a / b : ℕ) : ℤ)
      - ((2 : ℤ) ^ N) * (a : ℤ) := Int.dvd_sub hq h1
  rw [hsub] at h4
  have hkey : (b : ℤ) * ((2 ^ N * a / b : ℕ) : ℤ) - ((2 ^ N * a : ℕ) : ℤ)
      = -(jsp87OrbitNum a b N : ℤ) := by
    rw [hA]
    ring
  rw [hkey] at h4
  have h3 : ((2 : ℤ) ^ jsp87Val2 b) ∣ (jsp87OrbitNum a b N : ℤ) := Int.dvd_neg.mp h4
  exact (Int.natCast_dvd_natCast).mp h3

/-- **THE ORBIT POINT LIVES ON THE ODD PART OF THE DENOMINATOR.**  If
`jsp87Series = a/b` with `0 < a`, `0 < b` and `jsp87Val2 b ≤ N`, then there is
`n < jsp87OddPart b` with `jsp87OddPart b · Int.fract (θ N) = n`: the doubling
orbit of the carries takes at most `jsp87OddPart b` distinct values, and they
are the `jsp87OddPart b`-th fractions.  No coprimality hypothesis is needed. -/
theorem jsp87_fracCarry_eq_oddPart_num {a b N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hN : 1 ≤ N) (hval : jsp87Val2 b ≤ N) (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ n : ℕ, n < jsp87OddPart b
      ∧ (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry N) = n := by
  have hf := jsp87_fracCarry_eq_orbitNum ha hb hN hS
  have hb' : 0 < jsp87OddPart b := jsp87OddPart_pos hb
  obtain ⟨k, hk⟩ := jsp87OrbitNum_dvd_two_pow (a := a) (N := N) hb hval
  refine ⟨k, ?_, ?_⟩
  · have hlt : jsp87OrbitNum a b N < b := jsp87OrbitNum_lt hb
    have hdecomp := jsp87_pow_mul_oddPart b
    have hpos : (0 : ℕ) < 2 ^ jsp87Val2 b := pow_pos (by omega) _
    rw [hk] at hlt
    have hlt2 : 2 ^ jsp87Val2 b * k < 2 ^ jsp87Val2 b * jsp87OddPart b :=
      lt_of_lt_of_le hlt (by rw [hdecomp])
    have hlt' : k * 2 ^ jsp87Val2 b < jsp87OddPart b * 2 ^ jsp87Val2 b := by
      simpa only [Nat.mul_comm, Nat.mul_left_comm] using hlt2
    exact (Nat.mul_lt_mul_right hpos).mp hlt' 
  · have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
    have h2v0 : ((2 : ℝ) ^ jsp87Val2 b) ≠ 0 := by positivity
    have hb'eq : ((jsp87OddPart b : ℕ) : ℝ) * ((2 : ℝ) ^ jsp87Val2 b) = (b : ℝ) := by
      have hdecomp := jsp87_pow_mul_oddPart b
      calc ((jsp87OddPart b : ℕ) : ℝ) * ((2 : ℝ) ^ jsp87Val2 b)
          = ((2 ^ jsp87Val2 b * jsp87OddPart b : ℕ) : ℝ) := by push_cast; ring
        _ = (b : ℝ) := by exact_mod_cast hdecomp
    have hkR : ((2 : ℝ) ^ jsp87Val2 b) * (k : ℝ) = (jsp87OrbitNum a b N : ℝ) := by
      exact_mod_cast hk.symm
    calc (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry N)
        = ((jsp87OrbitNum a b N : ℕ) : ℝ) / ((2 : ℝ) ^ jsp87Val2 b) := by
          rw [hf]
          field_simp
          nlinarith [hb'eq]
      _ = k := by
        rw [div_eq_iff h2v0]
        linarith [hkR]

/-! ## 4. The reduced Mersenne obstruction -/

/-- **THE BLOCK AS A DIFFERENCE OF ORBIT POINTS.**  For `1 ≤ N`,
`(jsp87DigitBlock N t : ℝ) = 2^t · Int.fract (θ N) − Int.fract (θ (N+t))`,
with no periodicity hypothesis.  This is the unconditional form of round 48's
`jsp87_fracCarry_eq_block_of_digitPeriodic`. -/
theorem jsp87_digitBlock_eq_fracCarry {N t : ℕ} (hN : 1 ≤ N) :
    (jsp87DigitBlock N t : ℝ) = 2 ^ t * Int.fract (jsp87Carry N)
      - Int.fract (jsp87Carry (N + t)) := by
  have hsum : ∀ j,
      (jsp87Digit (N + j) : ℝ)
        = 2 * Int.fract (jsp87Carry (N + j)) - Int.fract (jsp87Carry ((N + j) + 1)) := by
    intro j
    have hj : 1 ≤ N + j := by omega
    have h := jsp87_digit_eq_fractCarry (N := N + j) hj
    have h' : N + j + 1 = (N + j) + 1 := by omega
    rw [h'] at h
    exact h
  have hcast : ((jsp87DigitBlock N t : ℤ) : ℝ)
      = ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℝ) * 2 ^ (t - 1 - j) := by
    unfold jsp87DigitBlock
    push_cast
    rfl
  have hshift := sum_shift_real (fun k => Int.fract (jsp87Carry k)) N t
  calc (jsp87DigitBlock N t : ℝ)
      = ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℝ) * 2 ^ (t - 1 - j) := hcast
    _ = 2 * (∑ j ∈ Finset.range t, (Int.fract (jsp87Carry (N + j)) : ℝ) * 2 ^ (t - 1 - j))
          - ∑ j ∈ Finset.range t, (Int.fract (jsp87Carry ((N + j) + 1)) : ℝ)
              * 2 ^ (t - 1 - j) := by
        exact sum_split_diff (fun k => Int.fract (jsp87Carry k))
          (fun k => (jsp87Digit k : ℝ)) N t hsum
    _ = 2 ^ t * (Int.fract (jsp87Carry N) : ℝ)
          - (Int.fract (jsp87Carry (N + t)) : ℝ) := by
        rw [hshift]
        ring

/-- **THE REDUCED MERSENNE NUMBER DIVIDES THE BLOCK.**  If
`jsp87Series = a/b` in lowest terms with `0 < a`, `0 < b`, `0 < t`, `1 ≤ M` and
the binary digits are eventually periodic from `M` with period `t`, then

`(2 ^ t - 1) / jsp87OddPart b ∣ jsp87DigitBlock N t`   for every `N ≥ M`.

This is the **non-vacuous replacement** for round 51's obstruction: the block is
a genuine multiple of the reduced Mersenne number, the multiple being exactly
the numerator of the orbit point on the odd-part grid. -/
theorem jsp87_digitBlock_dvd_reduced_mer {a b t M : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (ht : 0 < t) (hM : 1 ≤ M)
    (hval : jsp87Val2 b ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) {N : ℕ} (hN : M ≤ N) :
    (((2 ^ t - 1) / jsp87OddPart b : ℕ) : ℤ) ∣ jsp87DigitBlock N t := by
  obtain ⟨n, hn, hmul⟩ :=
    jsp87_fracCarry_eq_oddPart_num (N := N) ha hb (by omega) (by omega) hS
  obtain ⟨c, hc⟩ := jsp87_oddPart_dvd_mer_of_period hac hb ht hM hS hper
  have hdvd : jsp87OddPart b ∣ 2 ^ t - 1 := ⟨c, hc⟩
  have hdiv : (2 ^ t - 1) / jsp87OddPart b * jsp87OddPart b = 2 ^ t - 1 :=
    Nat.div_mul_cancel hdvd
  have hcc : c * jsp87OddPart b = 2 ^ t - 1 := by rw [hc]; ring
  have hb' : 0 < jsp87OddPart b := jsp87OddPart_pos hb
  have hhu : (2 ^ t - 1) / jsp87OddPart b = c :=
    Nat.mul_right_cancel hb' (hdiv.trans hcc.symm)
  refine ⟨n, ?_⟩
  have hB : (jsp87DigitBlock N t : ℝ)
      = ((2 ^ t - 1 : ℕ) : ℝ) * Int.fract (jsp87Carry N) := by
    have h1 := jsp87_digitBlock_eq_fracCarry (t := t) (by omega : (1 : ℕ) ≤ N)
    have h2 := jsp87_fracCarry_periodic_of_digitPeriodic ht hM hN hper
    rw [h2] at h1
    have hkey : 2 ^ t * Int.fract (jsp87Carry N) - Int.fract (jsp87Carry N)
        = ((2 ^ t - 1 : ℕ) : ℝ) * Int.fract (jsp87Carry N) := by
      have hsub : ((2 ^ t - 1 : ℕ) : ℝ) = 2 ^ t - 1 := by
        calc ((2 ^ t - 1 : ℕ) : ℝ) = ((2 ^ t : ℕ) : ℝ) - ((1 : ℕ) : ℝ) :=
              Nat.cast_sub (one_le_two_pow_nat t)
          _ = ((2 ^ t : ℕ) : ℝ) - 1 := by norm_num
          _ = 2 ^ t - 1 := by norm_num [Nat.cast_pow]
      rw [hsub]
      ring
    exact h1.trans hkey
  have hcast2 : ((jsp87OddPart b * c : ℕ) : ℝ) = ((jsp87OddPart b : ℕ) : ℝ) * ((c : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
  have hcast : (jsp87DigitBlock N t : ℝ) = ((n : ℕ) : ℝ) * ((c : ℕ) : ℝ) := by
    calc (jsp87DigitBlock N t : ℝ)
        = ((2 ^ t - 1 : ℕ) : ℝ) * Int.fract (jsp87Carry N) := hB
      _ = ((jsp87OddPart b * c : ℕ) : ℝ) * Int.fract (jsp87Carry N) := by rw [hc]
      _ = ((jsp87OddPart b : ℕ) : ℝ) * ((c : ℕ) : ℝ) * Int.fract (jsp87Carry N) := by
          rw [hcast2]
      _ = ((n : ℕ) : ℝ) * ((c : ℕ) : ℝ) := by
          calc ((jsp87OddPart b : ℕ) : ℝ) * ((c : ℕ) : ℝ) * Int.fract (jsp87Carry N)
              = ((c : ℕ) : ℝ) * ((jsp87OddPart b : ℕ) : ℝ) * Int.fract (jsp87Carry N) := by ring
            _ = ((c : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by rw [← hmul]; ring
            _ = ((n : ℕ) : ℝ) * ((c : ℕ) : ℝ) := by ring
  rw [hhu]
  exact_mod_cast (show (jsp87DigitBlock N t : ℝ) = ((c * n : ℕ) : ℝ) by
    rw [hcast]
    simp only [Nat.cast_mul]
    ring)

/-- **THE MINIMAL PERIOD IS AT MOST THE ODD PART OF THE DENOMINATOR.**  Let
`jsp87Series = a/b` in lowest terms with `0 < a`, `0 < b`, let `t > 0` be an
eventual period of the doubling orbit which is *minimal* in the arithmetical
sense `∀ u < t, 0 < u → ¬ jsp87OddPart b ∣ 2^u − 1`, and let `1 ≤ M` with
`jsp87Val2 b ≤ M`.  Then

`t ≤ jsp87OddPart b`.

Indeed the orbit points are the `jsp87OddPart b`-th fractions
(`jsp87_fracCarry_eq_oddPart_num`) and a minimal period visits pairwise distinct
points (`jsp87_fracCarry_distinct`), so the period cannot exceed their number.
This is the first *upper* bound on the period of the binary expansion of the
Erdős series in terms of its denominator. -/
theorem jsp87_digitPeriod_le_oddPart {a b M t : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (_ht : 0 < t) (hM : 1 ≤ M)
    (hval : jsp87Val2 b ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hmin : ∀ u, 0 < u → u < t → ¬ jsp87OddPart b ∣ 2 ^ u - 1) :
    t ≤ jsp87OddPart b := by
  have hb' : 0 < jsp87OddPart b := jsp87OddPart_pos hb
  have hnum : ∀ i : ℕ, ∃ n : ℕ, n < jsp87OddPart b
      ∧ (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry (M + i)) = n := by
    intro i
    obtain ⟨n, hn, hmul⟩ :=
      jsp87_fracCarry_eq_oddPart_num (N := M + i) ha hb (by omega) (by omega) hS
    exact ⟨n, hn, hmul⟩
  have hvalf : ∀ i : ℕ, ∃ n : ℕ, n < jsp87OddPart b
      ∧ (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry (M + i)) = n := fun i => hnum i
  set val : ℕ → ℕ := fun i => Exists.choose (hvalf i) with hvaldef
  have hval_lt : ∀ i : ℕ, val i < jsp87OddPart b := fun i => (Exists.choose_spec (hvalf i)).1
  have hval_mul : ∀ i : ℕ, (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry (M + i))
      = val i := fun i => (Exists.choose_spec (hvalf i)).2
  have hcard : Fintype.card (Fin t) ≤ Fintype.card (Fin (jsp87OddPart b)) := by
    refine Fintype.card_le_of_injective (fun i : Fin t => ⟨val i, hval_lt i⟩) ?_
    intro i j hij
    by_contra hcon
    have hv : val i = val j := congrArg Fin.val hij
    have hkey : (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry (M + i))
        = (jsp87OddPart b : ℝ) * Int.fract (jsp87Carry (M + j)) := by
      rw [hval_mul i, hval_mul j, hv]
    have hfrac : Int.fract (jsp87Carry (M + i)) = Int.fract (jsp87Carry (M + j)) := by
      exact mul_left_cancel₀ (by positivity : (jsp87OddPart b : ℝ) ≠ 0) hkey
    rcases lt_or_gt_of_ne hcon with hlt | hgt
    · exact jsp87_fracCarry_distinct (a := a) (b := b) ha hac hb hM hval hS hmin
        hlt j.isLt hfrac
    · exact jsp87_fracCarry_distinct (a := a) (b := b) ha hac hb hM hval hS hmin
        hgt i.isLt hfrac.symm
  simpa using hcard

/-- **THE DENOMINATOR DOMINATES THE PERIOD.**  Under the hypotheses of
`jsp87_digitPeriod_le_oddPart`, `2^{v_2(b)} · t ≤ b`. -/
theorem jsp87_denominator_ge_period {a b M t : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (ht : 0 < t) (hM : 1 ≤ M)
    (hval : jsp87Val2 b ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hmin : ∀ u, 0 < u → u < t → ¬ jsp87OddPart b ∣ 2 ^ u - 1) :
    2 ^ jsp87Val2 b * t ≤ b := by
  have hle := jsp87_digitPeriod_le_oddPart ha hac hb ht hM hval hS hmin
  have hdecomp := jsp87_pow_mul_oddPart b
  have hmul : 2 ^ jsp87Val2 b * t ≤ 2 ^ jsp87Val2 b * jsp87OddPart b :=
    Nat.mul_le_mul_left _ hle
  rw [hdecomp] at hmul
  exact hmul

/-- **A HYPOTHETICAL RATIONAL VALUE WITH A MINIMAL PERIOD `1` IS DYADIC.**
If `t = 1` is the minimal eventual period then `jsp87OddPart b = 1`. -/
theorem jsp87_digitPeriod_one_oddPart {a b M : ℕ} (_ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (hM : 1 ≤ M) (_hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + 1) = jsp87Digit n)
    (_hmin : ∀ u, 0 < u → u < 1 → ¬ jsp87OddPart b ∣ 2 ^ u - 1) :
    jsp87OddPart b = 1 := by
  have hd : jsp87OddPart b ∣ 2 ^ 1 - 1 :=
    jsp87_oddPart_dvd_mer_of_period (t := 1) hac hb (by omega) hM hS hper
  rw [show (2 : ℕ) ^ 1 - 1 = 1 from by norm_num] at hd
  exact Nat.dvd_one.mp hd

/-- **A HYPOTHETICAL RATIONAL VALUE WITH MINIMAL PERIOD `2` HAS ODD PART `3`.** -/
theorem jsp87_digitPeriod_two_oddPart {a b M : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + 2) = jsp87Digit n)
    (hmin : ∀ u, 0 < u → u < 2 → ¬ jsp87OddPart b ∣ 2 ^ u - 1) :
    jsp87OddPart b = 3 := by
  have h2 := jsp87_digitPeriod_le_oddPart (t := 2) (a := a) (b := b) (M := M) ha hac hb
    (by norm_num) hM hval hS hmin
  have hd : jsp87OddPart b ∣ 2 ^ 2 - 1 :=
    jsp87_oddPart_dvd_mer_of_period (t := 2) hac hb (by norm_num) hM hS hper
  rw [show (2 : ℕ) ^ 2 - 1 = 3 from by norm_num] at hd
  by_cases hc : jsp87OddPart b = 3
  · exact hc
  · have h3 : jsp87OddPart b ≤ 3 := Nat.le_of_dvd (show 0 < (3 : ℕ) by omega) hd
    have hd' : jsp87OddPart b = 2 := by omega
    exact absurd (hd' ▸ hd) (by decide)

/-- **A HYPOTHETICAL RATIONAL VALUE WITH MINIMAL PERIOD `≥ 2` HAS ODD PART `≥ 2`.** -/
theorem jsp87_digitPeriod_ge_two_oddPart {a b M t : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (ht : 0 < t) (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) (ht2 : 2 ≤ t)
    (hmin : ∀ u, 0 < u → u < t → ¬ jsp87OddPart b ∣ 2 ^ u - 1) :
    2 ≤ jsp87OddPart b := by
  have h := jsp87_digitPeriod_le_oddPart ha hac hb ht hM hval hS hmin
  omega

/-! ## 5. The fifth criterion, and the corrected blocker -/

/-- **A REDUCED RATIONAL VALUE FORCES THE BLOCKS TO BE MULTIPLES OF THE REDUCED
MERSENNE NUMBERS.**  If `jsp87Series = a/b` in lowest terms (`0 < a`,
`0 < b`), then there are `t ≥ 2` and `M ≥ 1` with

`(2 ^ t - 1) / jsp87OddPart b ∣ jsp87DigitBlock N t`   for all `N ≥ M`.

The `t₀ = 1` case (eventually constant digit string) is handled directly: then
`jsp87OddPart b = 1`, all orbit points vanish and all blocks past `M` are `0`. -/
theorem jsp87Series_rational_imp_block_dvd {a b : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t M : ℕ, 2 ≤ t ∧ 1 ≤ M ∧ ∀ N, M ≤ N →
      (((2 ^ t - 1) / jsp87OddPart b : ℕ) : ℤ) ∣ jsp87DigitBlock N t := by
  obtain ⟨t₀, M₀, ht₀, hM₀, hper⟩ := jsp87_digit_eventuallyPeriodic (a := (a : ℤ)) hb hS
  by_cases h1 : t₀ = 1
  · refine ⟨2, max M₀ (jsp87Val2 b), by omega, by omega, ?_⟩
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have hper1 : ∀ n, M₀ ≤ n → jsp87Digit (n + 1) = jsp87Digit n := by
      intro n hn
      simpa [h1] using hper n hn
    have hodd : jsp87OddPart b = 1 := by
      have hd := jsp87_oddPart_dvd_mer_of_period (t := 1) hac hb (by omega) hM₀ hS hper1
      rw [show (2 : ℕ) ^ 1 - 1 = 1 from by norm_num] at hd
      exact Nat.dvd_one.mp hd
    have hval : jsp87Val2 b ≤ N := by omega
    obtain ⟨n, hn, hmul⟩ :=
      jsp87_fracCarry_eq_oddPart_num (N := N) ha hb (by omega) hval hS
    rw [hodd] at hn hmul
    have hzero : Int.fract (jsp87Carry N) = 0 := by
      have hn0 : n = 0 := by omega
      rw [hn0] at hmul
      norm_num at hmul
      exact hmul
    have hstep : Int.fract (jsp87Carry (N + 1)) = Int.fract (jsp87Carry N) :=
      jsp87_fracCarry_periodic_of_digitPeriodic (M := M₀) (N := N) (t := 1) (by omega)
        (by omega) (by omega) hper1
    have hstep2 : Int.fract (jsp87Carry (N + 2)) = Int.fract (jsp87Carry (N + 1)) :=
      jsp87_fracCarry_periodic_of_digitPeriodic (M := M₀) (N := N + 1) (t := 1) (by omega)
        (by omega) (by omega) hper1
    have hz2 : Int.fract (jsp87Carry (N + 2)) = 0 := by
      rw [hstep2, hstep]
      exact hzero
    have hB := jsp87_digitBlock_eq_fracCarry (t := 2) hN1
    rw [hzero, hz2] at hB
    ring_nf at hB
    refine ⟨0, ?_⟩
    exact_mod_cast hB
  · refine ⟨t₀, max M₀ (jsp87Val2 b), by omega, by omega, ?_⟩
    intro N hN
    refine jsp87_digitBlock_dvd_reduced_mer (M := max M₀ (jsp87Val2 b)) ha hac hb ht₀
      (by omega) (le_max_right _ _) ?_ hS hN
    intro n hn
    exact hper n (by omega)

/-- **THE FIFTH IRRATIONALITY CRITERION -- AND THE CORRECTED BLOCKER.**  Let
`c ≥ 1` and suppose that for every `t ≥ 2` and every `M ≥ 1` there is a cut point
`N ≥ M` at which the `t`-digit block of the Erdős series is **not** a multiple of
the reduced Mersenne number `(2^t − 1)/c`.  Then no reduced rational value
`jsp87Series = a/b` with `jsp87OddPart b = c` exists.

This is the **well-posed replacement** for round 51's vacuous
`jsp87_window_congr_fails`, which this round refutes. -/
theorem jsp87_blockNotDvd_impossible {a b c : ℕ} (ha : 0 < a) (hac : Nat.Coprime a b)
    (hb : 0 < b) (_hc : 0 < c) (hodd : jsp87OddPart b = c)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (h : ∀ t M : ℕ, 2 ≤ t → 1 ≤ M →
      ∃ N, M ≤ N ∧ ¬ ((((2 ^ t - 1) / c : ℕ) : ℤ) ∣ jsp87DigitBlock N t)) :
    False := by
  obtain ⟨t, M, ht, hM, hdv⟩ :=
    jsp87Series_rational_imp_block_dvd ha hac hb hS
  have hdv' : ∀ N, M ≤ N → (((2 ^ t - 1) / c : ℕ) : ℤ) ∣ jsp87DigitBlock N t := by
    intro N hN
    rw [← hodd]
    exact hdv N hN
  obtain ⟨N, hN, hbad⟩ := h t M ht hM
  exact hbad (hdv' N hN)

end JSP87
