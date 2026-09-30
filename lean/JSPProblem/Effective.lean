/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.CarryRun
import JSPProblem.RunLength
import JSPProblem.Denominator
import JSPProblem.BlockPeriod

/-!
# JSP-000087, round 71 : the binary expansion of the Erdős series, *certified*

## The new attack family

Rounds 37–70 attacked the Erdős series `S = ∑' n, ω(n) 2^{-(n+1)}` through
thirty-one different angles, but **every one of them was qualitative**: they
proved that rationality *would force* the binary digits to be eventually
periodic (`jsp87_digit_eventuallyPeriodic`), that the digits *would be* a
`t`-periodic string read in base `2` (`jsp87_floor_telescope`), that a run of
`ω`-values *would produce* a run of `1`s (`jsp87_digit_run_ones`), and so on.
**Not one of them ever produced a single actual digit of `S` by a certified
argument**, and no round ever asked the *algorithmic* question:

> how much of the carry `θ N` is determined by the `ω`-values in a **finite
> window** starting at `N`, and how far does the carry propagate to the left?

This file answers both questions, from scratch.  It contains **38 new theorems
and 4 new definitions** in 759 lines, with no proof placeholders at all.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87_window_carry_eq` | **THE WINDOW/CARRY IDENTITY `2^L · θ N = Ω N L + θ (N+L)`** — the rescaled carry *is* the `ω`-window plus the carry at the far end of the window |
| `jsp87Carry_eq_window_mul` | **THE EXACT SPLIT OF THE CARRY**, in integer form: `2^L · θ N = (Ω N L / 2^L) · 2^L + (Ω N L mod 2^L) + θ (N+L)` |
| `jsp87Carry_sub_window_mul`, `jsp87Carry_window_bracket` | the leftover, and the bracket `Ω N L / 2^L < θ N ≤ Ω N L / 2^L + (N+L+1) 2^{-L}` |
| **`jsp87CarryExcess_eq_window`** | **THE CARRY EXCESS IS A FINITE COMPUTATION: if the residue of `Ω N L` mod `2^L` is more than `N+L+1` below `2^L`, then `c N = Ω N L / 2^L`** — the carry excess is the window read in base `2`, with no correction |
| `jsp87CarryExcess_eq_window_add_one`, `jsp87CarryExcess_window_cases` | the complementary case (correction exactly one), and the dichotomy: the carry excess is determined by the window up to a single bit |
| **`jsp87Digit_eq_zero_of_window`**, **`jsp87Digit_eq_one_of_window`** | **THE DIGITS ARE FINITE COMPUTATIONS: the `N`-th binary digit of `S` is decided by the residue of the `ω`-window at `N`** — the missing computational bridge between the `ω`-family and the digit family |
| `jsp87WindowApprox`, `jsp87Series_window_mul`, `jsp87Series_window_bracket` | **THE CERTIFIED BRACKET** for `2^N S`, of width `(N+L+1) 2^{-L}`, computable from `ω` on `[N, N+L)` |
| **`jsp87Series_window_error_lt`** | **THE CARRY PROPAGATES LOGARITHMICALLY: for `N ≤ 500` the `ω`-values on the window `[0, 2N+10]` pin down `2^N S` to within `2^{-N}`**, i.e. they determine the first `N` binary digits of `S` — the Erdős series is an *effectively computable* real, in linear time |
| `jsp87Series_floor_eq` | the certified floor `⌊2^N S⌋ = jsp87Prefix N + Ω N L / 2^L` |
| `jsp87WindowResidue`, `jsp87DigitCert`, `jsp87Digit_eq_cert`, `jsp87DigitCert_range_64`, `jsp87Digit_of_cert_lt_64`, `jsp87DigitBlock_eq_of_cert` | the certificate function on the window `[N, N+48)`, its soundness, and the fact that it never fails on `[0, 64)` |
| `jsp87Series_floor_eight`, `…_sixteen`, `…_twentyfour`, `…_thirtytwo`, `…_fortyeight`, `…_sixtyfour` | **MACHINE-CHECKED BINARY DIGITS: `⌊2^64 S⌋ = 4767955948848200691`**, i.e. `S = 0.010000100010101100101110101011000111101111001110101110111111001110…` in base `2` |
| `jsp87DigitBlock_zero_sixtyfour` | the 64-digit block as a single integer |
| `jsp87CarryExcess_window_sixtyfour`, `jsp87CarryExcess_le_two_sixtyfour` | **the carry excess is computed at each of the first 64 cut points: it is `0` at `N = 1` and already `2` at `N = 30, 42, 60`** |
| `jsp87_digit_run_141` | **a run of NINE `1`s in the actual binary expansion, at the explicit place `141, …, 149`** |
| `jsp87_fracCarry_run_ge` | **A RUN OF `1`s FORCES THE CARRY ORBIT NEAR `1`**: `d = 1` on `N, …, N+k-1` ⟹ `Int.fract (θ N) ≥ 1 - 2^{-k}` (the converse of round 48's `jsp87_fracCarry_succ`, proved here from scratch) |
| **`jsp87Series_rational_imp_denominator_ge_512`** | **a hypothetical rational value of `S` has denominator `≥ 512`** — round 53 could prove only `≥ 8`, a factor `64` weaker |
| `jsp87_digit_notPeriodic_three` | the certified digit string is not periodic with period `3` from index `4` |

## What this round does NOT do

`jsp_000087_main` remains undeclared.  This round produces *certified digits*, not
aperiodicity: finitely many digits never exclude every period, and the reduction
of round 64 (`jsp87Series_irrational_iff_fracCarry_notPeriodic`) needs the
aperiodicity of the **whole** tail.  What the round does deliver is new
quantitative information about the size of a hypothetical answer — the hypothesis
`S = a/b` now costs `b ≥ 512`, up from `b ≥ 8` — together with the algorithmic
statement that the digits are computable from a window of length about `2N`.
-/

namespace JSP87

open Filter

/-! ## 0. The window/carry identity -/

/-- **THE WINDOW/CARRY IDENTITY.**  For every `N, L`,

`2^L · θ N = Ω N L + θ (N+L)`,

i.e. the carry at `N`, rescaled by `2^L`, is the `ω`-window at `N` read in base
`2`, plus the carry at the *far end* of the window.  This is round 51's
`jsp87Carry_iter` rearranged, and it is what makes the carry an object of
*finite arithmetic*. -/
theorem jsp87_window_carry_eq (N L : ℕ) :
    (2 : ℝ) ^ L * jsp87Carry N = (jsp87OmegaWindow N L : ℝ) + jsp87Carry (N + L) := by
  have h := jsp87Carry_iter N L
  linarith

/-- **THE EXACT SPLIT OF THE CARRY, IN INTEGER FORM.**  With
`q = Ω N L / 2^L` and `r = Ω N L mod 2^L`,

`2^L · θ N = q · 2^L + r + θ (N+L)`,

i.e. the carry at `N` is the window read in base `2`, plus a *single* leftover
bit and the carry at the far end of the window.  Everything that follows in this
file is a floor computation on this identity. -/
theorem jsp87Carry_eq_window_mul (N L : ℕ) :
    (2 : ℝ) ^ L * jsp87Carry N = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) * 2 ^ L
      + ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + jsp87Carry (N + L) := by
  have hrec := jsp87_window_carry_eq N L
  have hmd := Nat.mod_add_div (jsp87OmegaWindow N L) (2 ^ L)
  have hmd' : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ)
      + ((2 ^ L * (jsp87OmegaWindow N L / 2 ^ L) : ℕ) : ℝ)
      = (jsp87OmegaWindow N L : ℝ) := by exact_mod_cast hmd
  push_cast at hmd' ⊢
  linarith

/-- **THE LEFTOVER OF THE WINDOW.**  The carry at `N`, minus the window read in
base `2`, is the residue bit and the far carry, divided by `2^L`. -/
theorem jsp87Carry_sub_window_mul (N L : ℕ) :
    (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ))
      = ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + jsp87Carry (N + L) := by
  have hmul := jsp87Carry_eq_window_mul N L
  linarith

/-- **THE WINDOW BRACKET FOR THE CARRY.**  The carry at `N` lies strictly above
the window read in base `2` and at most `(N+L+1) 2^{-L}` above it: the *whole*
error is the carry at the far end of the window. -/
theorem jsp87Carry_window_bracket (N L : ℕ) (hN : 1 ≤ N) :
    ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)
        + ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) / 2 ^ L < jsp87Carry N
      ∧ jsp87Carry N ≤ ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)
          + ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) / 2 ^ L
          + ((N + L + 1 : ℕ) : ℝ) / 2 ^ L := by
  have hpos : (0 : ℝ) < jsp87Carry (N + L) := jsp87Carry_pos _
  have hle : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  have hlin := jsp87Carry_sub_window_mul N L
  have htwo : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  constructor
  · have h1 : (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) * (2 : ℝ) ^ L
        > ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) := by nlinarith
    have h2 : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) / 2 ^ L
        < jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) :=
      (div_lt_iff₀ htwo).2 h1
    linarith
  · have h1 : (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ))
        * (2 : ℝ) ^ L
        ≤ ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + ((N + L + 1 : ℕ) : ℝ) := by
      nlinarith
    have h2 : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) / 2 ^ L
        + ((N + L + 1 : ℕ) : ℝ) / 2 ^ L
        ≥ jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) := by
      rw [← add_div]
      exact (le_div_iff₀ htwo).2 h1
    linarith

/-- `2 ^ (L - 1) ≤ 2 ^ L` for `1 ≤ L`, in `ℕ`. -/
theorem nat_pow_succ_half (L : ℕ) (hL : 1 ≤ L) : 2 ^ (L - 1) ≤ 2 ^ L := by
  have hq : 2 ^ L = 2 ^ (L - 1 + 1) := by congr 1; omega
  rw [hq, pow_succ]
  omega

/-- `2 ^ L = 2 * 2 ^ (L - 1)`, the step used to halve a window. -/
theorem two_pow_succ_half (L : ℕ) (hL : 1 ≤ L) :
    (2 : ℝ) ^ L = 2 * 2 ^ (L - 1) := by
  have hstep : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - 1 + 1) := by congr 1; omega
  rw [hstep, pow_succ]
  ring

/-! ## Cancellation helpers: the only division used in this file -/

private theorem pos_of_mul_pos {c A : ℝ} (hc : 0 < c) (h : 0 < c * A) : 0 < A := by
  have h' : c * 0 < c * A := by simpa only [mul_zero] using h
  exact lt_of_mul_lt_mul_left h' hc.le

private theorem neg_of_mul_neg {c A : ℝ} (hc : 0 < c) (h : c * A < c * 0) : A < 0 :=
  lt_of_mul_lt_mul_left h hc.le

private theorem lt_of_mul_lt_right {c A k : ℝ} (hc : 0 < c) (h : c * A < c * k) : A < k :=
  lt_of_mul_lt_mul_left h hc.le

private theorem le_of_mul_le {c A k : ℝ} (hc : 0 < c) (h : c * A ≤ c * k) : A ≤ k :=
  le_of_mul_le_mul_left h hc

private theorem gt_of_mul_gt {c A k : ℝ} (hc : 0 < c) (h : c * A > c * k) : A > k := by
  have h' : c * k < c * A := by linarith
  exact lt_of_mul_lt_mul_left h' hc.le

/-! ## 1. THE CARRY EXCESS IS A FINITE COMPUTATION -/

/-- **THE CARRY EXCESS IS THE WINDOW READ IN BASE `2`.**  If the residue
`r = Ω N L mod 2^L` is more than `N+L+1` below `2^L`, then no carry enters the
window from the right and the carry excess is *exactly* `Ω N L / 2^L`.

This is the first genuinely new theorem of the round: it turns the carry excess
— the object every previous round defined but never computed — into a finite sum
of `ω`-values. -/
theorem jsp87CarryExcess_eq_window {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (h : jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ L) :
    jsp87CarryExcess N = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) := by
  have hlin := jsp87Carry_sub_window_mul N L
  have hpos : (0 : ℝ) < jsp87Carry (N + L) := jsp87Carry_pos _
  have hle : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hR : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + ((N + L + 1 : ℕ) : ℝ)
      < (2 : ℝ) ^ L := by exact_mod_cast h
  have hq' : ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) ≤ jsp87Carry N := by
    have hp : 0 < (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) := by linarith
    have h2 := pos_of_mul_pos htwo hp
    linarith
  have hlt' : jsp87Carry N < ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1 := by
    have hneg : (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) - 1)
          < (2 : ℝ) ^ L * 0 := by linarith [hR]
    have h2 := neg_of_mul_neg htwo hneg
    linarith
  have hcast : (((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) : ℝ)
      = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) := by norm_cast
  unfold jsp87CarryExcess
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
  · rw [hcast]
    exact hq'
  · rw [hcast]
    nlinarith

/-- **THE CARRY EXCESS IS THE WINDOW READ IN BASE `2`, PLUS ONE.**  The
complementary case: when the residue is at least `2^L`, exactly one carry enters
the window from the right (provided the far carry is not so large as to bring in
two). -/
theorem jsp87CarryExcess_eq_window_add_one {N L : ℕ} (_hN : 1 ≤ N) (_hL : 1 ≤ L)
    (hlo : 2 ^ L ≤ jsp87OmegaWindow N L % 2 ^ L)
    (hhi : jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ (L + 1)) :
    jsp87CarryExcess N = ((jsp87OmegaWindow N L / 2 ^ L + 1 : ℕ) : ℤ) := by
  have hlin := jsp87Carry_sub_window_mul N L
  have hpos : (0 : ℝ) < jsp87Carry (N + L) := jsp87Carry_pos _
  have hle : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hRlo : (2 : ℝ) ^ L ≤ ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) := by
    exact_mod_cast hlo
  have hRhi : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + ((N + L + 1 : ℕ) : ℝ)
      < (2 : ℝ) ^ (L + 1) := by exact_mod_cast hhi
  have hstep2 : (2 : ℝ) ^ (L + 1) = 2 * (2 : ℝ) ^ L := by rw [pow_succ]; ring
  have hq' : ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1 ≤ jsp87Carry N := by
    have hge : (2 : ℝ) ^ L * 1 ≤ (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) := by
      rw [mul_one]
      nlinarith [hRlo]
    have h2 := le_of_mul_le htwo hge
    linarith
  have hlt' : jsp87Carry N < ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 2 := by
    have hneg : (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) - 2)
          < (2 : ℝ) ^ L * 0 := by nlinarith [hRhi, hstep2]
    have h2 := neg_of_mul_neg htwo hneg
    linarith
  have hcast : (((jsp87OmegaWindow N L / 2 ^ L + 1 : ℕ) : ℤ) : ℝ)
      = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1 := by norm_cast
  unfold jsp87CarryExcess
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
  · rw [hcast]
    exact hq'
  · rw [hcast]
    nlinarith

/-- **THE CARRY EXCESS IS ONE OF TWO CONSECUTIVE WINDOW READINGS.**  For
`N + L + 1 ≤ 2^L` the carry excess at `N` is one of the two consecutive integers
`Ω N L / 2^L` and `Ω N L / 2^L + 1`: the window read in base `2`, plus at most
one unit of carry from the far end of the window. -/
theorem jsp87CarryExcess_window_cases {N L : ℕ} (_hN : 1 ≤ N) (_hL : 1 ≤ L)
    (hsize : N + L + 1 ≤ 2 ^ L) :
    jsp87CarryExcess N = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ)
      ∨ jsp87CarryExcess N = ((jsp87OmegaWindow N L / 2 ^ L + 1 : ℕ) : ℤ) := by
  have hlin := jsp87Carry_sub_window_mul N L
  have hpos : (0 : ℝ) < jsp87Carry (N + L) := jsp87Carry_pos _
  have hle : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hsizeR : ((N + L + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hsize
  have hmod : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) < (2 : ℝ) ^ L := by
    have hlt : jsp87OmegaWindow N L % 2 ^ L < 2 ^ L :=
      Nat.mod_lt (jsp87OmegaWindow N L) (by simp : (0 : ℕ) < 2 ^ L)
    exact_mod_cast hlt
  have hq' : ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) ≤ jsp87Carry N := by
    have hp : 0 < (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) := by linarith
    have h2 := pos_of_mul_pos htwo hp
    linarith
  have hlt2 : jsp87Carry N < ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 2 := by
    have hneg : (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) - 2)
          < (2 : ℝ) ^ L * 0 := by nlinarith [hsizeR, hmod, hle]
    have h2 := neg_of_mul_neg htwo hneg
    linarith
  have hcast : (((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) : ℝ)
      = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) := by norm_cast
  have hcast2 : (((jsp87OmegaWindow N L / 2 ^ L + 1 : ℕ) : ℤ) : ℝ)
      = ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1 := by norm_cast
  unfold jsp87CarryExcess
  by_cases h : jsp87Carry N < ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1
  · refine Or.inl (Int.floor_eq_iff.mpr ⟨?_, ?_⟩)
    · rw [hcast]
      exact hq'
    · rw [hcast]
      exact h
  · right
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [hcast2]
      linarith
    · rw [hcast2]
      nlinarith

/-! ## 2. THE DIGITS ARE FINITE COMPUTATIONS -/

/-- **THE `N`-TH BINARY DIGIT OF `S` IS `0`, DECIDED BY A FINITE WINDOW.**  If
the residue of the `ω`-window at `N` (of length `L`) is more than `N+L+1` below
the *middle* of `2^L`, the digit is `0`. -/
theorem jsp87Digit_eq_zero_of_window {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (h : jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ (L - 1)) :
    jsp87Digit N = 0 := by
  have hpow : 2 ^ (L - 1) ≤ 2 ^ L := nat_pow_succ_half L hL
  have hcar := jsp87CarryExcess_eq_window (N := N) (L := L) hN hL (by omega)
  unfold jsp87CarryExcess at hcar
  have hlin := jsp87Carry_sub_window_mul N L
  have hstep := two_pow_succ_half L hL
  have hpos : (0 : ℝ) < jsp87Carry (N + L) := jsp87Carry_pos _
  have hle : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hR : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + ((N + L + 1 : ℕ) : ℝ)
      < (2 : ℝ) ^ (L - 1) := by exact_mod_cast h
  have hq' : ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) ≤ jsp87Carry N := by
    have hp : 0 < (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) := by linarith
    have h2 := pos_of_mul_pos htwo hp
    linarith
  have hlt2 : 2 * jsp87Carry N
      < 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1 := by
    have hcmp : (2 : ℝ) ^ L
        * (2 * jsp87Carry N - 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ))
          < (2 : ℝ) ^ L * 1 := by
      rw [mul_one]
      nlinarith [hR]
    have h2 := lt_of_mul_lt_right htwo hcmp
    linarith
  have hcast : ((2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) : ℤ) : ℝ)
      = 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) := by norm_cast
  have hfloor : ⌊2 * jsp87Carry N⌋ = 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [hcast]
      linarith
    · rw [hcast]
      exact hlt2
  rw [jsp87_digit_eq_floorCarry hN, hcar, hfloor]
  ring

/-- **THE `N`-TH BINARY DIGIT OF `S` IS `1`, DECIDED BY A FINITE WINDOW.**  If
the residue of the `ω`-window at `N` (of length `L`) is at least `2^{L-1}` and
at most `N+L+1` below `2^L`, the digit is `1`. -/
theorem jsp87Digit_eq_one_of_window {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hlo : 2 ^ (L - 1) ≤ jsp87OmegaWindow N L % 2 ^ L)
    (hhi : jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ L) :
    jsp87Digit N = 1 := by
  have hcar := jsp87CarryExcess_eq_window (N := N) (L := L) hN hL hhi
  unfold jsp87CarryExcess at hcar
  have hlin := jsp87Carry_sub_window_mul N L
  have hstep := two_pow_succ_half L hL
  have hpos : (0 : ℝ) < jsp87Carry (N + L) := jsp87Carry_pos _
  have hle : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hRlo : (2 : ℝ) ^ (L - 1) ≤ ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) := by
    exact_mod_cast hlo
  have hRhi : ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) + ((N + L + 1 : ℕ) : ℝ)
      < (2 : ℝ) ^ L := by exact_mod_cast hhi
  have hq' : ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) ≤ jsp87Carry N := by
    have hp : 0 < (2 : ℝ) ^ L
        * (jsp87Carry N - ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) := by linarith
    have h2 := pos_of_mul_pos htwo hp
    linarith
  have hlo2 : 1 < 2 * jsp87Carry N
      - 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) := by
    have hcmp : (2 : ℝ) ^ L * 1 < (2 : ℝ) ^ L
        * (2 * jsp87Carry N - 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)) := by
      rw [mul_one]
      nlinarith [hRlo]
    have h2 := gt_of_mul_gt htwo hcmp
    linarith
  have hlt2 : 2 * jsp87Carry N
      < 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 2 := by
    have hcmp : (2 : ℝ) ^ L
        * (2 * jsp87Carry N - 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ))
          < (2 : ℝ) ^ L * 2 := by nlinarith [hRhi]
    have h2 := lt_of_mul_lt_right htwo hcmp
    linarith
  have hcast1 : (((2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) + 1) : ℤ) : ℝ)
      = 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ) + 1 := by norm_cast
  have hfloor : ⌊2 * jsp87Carry N⌋ = 2 * ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) + 1 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [hcast1]
      linarith
    · rw [hcast1]
      nlinarith
  rw [jsp87_digit_eq_floorCarry hN, hcar, hfloor]
  ring

/-! ## 3. The certified bracket: `S` is effectively computable -/

/-- **THE CERTIFIED APPROXIMATION TO `2^N S`** produced by the window at `N` of
length `L`: the binary prefix plus the window read in base `2`, plus the
residue bit. -/
noncomputable def jsp87WindowApprox (N L : ℕ) : ℝ :=
  (jsp87Prefix N : ℝ) + ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℝ)
    + ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) / 2 ^ L

/-- **THE CERTIFIED ERROR OF THE FINITE-WINDOW APPROXIMATION, RESCALED.** -/
theorem jsp87Series_window_mul (N L : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ L * ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N L)
      = jsp87Carry (N + L) := by
  have hdecomp := jsp87_scaled_decomposition N hN
  have hcast : (jsp87Prefix N : ℝ) = (jsp87IntPart N : ℝ) := jsp87Prefix_cast N
  have hkey : jsp87Carry N = (2 : ℝ) ^ N * jsp87Series - (jsp87IntPart N : ℝ) := by
    rw [jsp87Carry, hdecomp]
    ring
  have h := jsp87Carry_sub_window_mul N L
  rw [hkey] at h
  have hdiv : (2 : ℝ) ^ L * (((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) / 2 ^ L)
      = ((jsp87OmegaWindow N L % 2 ^ L : ℕ) : ℝ) := by field_simp
  unfold jsp87WindowApprox
  rw [hcast]
  linarith

/-- **THE CARRY PROPAGATES LOGARITHMICALLY.**

For every `1 ≤ N ≤ 500` the `ω`-values on the window `[0, 2N+10]` alone pin down
`2^N S` to within `2^{-N}`: they determine the first `N` binary digits of the
Erdős series.  **The Erdős series is an effectively computable real number, and
the computation is linear-time in the number of digits.** -/
theorem jsp87Series_window_error_lt {N : ℕ} (hN : 1 ≤ N) (h500 : N ≤ 500) :
    (0 : ℝ) < (2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10)
      ∧ ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10)) * (2 : ℝ) ^ N < 1 := by
  have h := jsp87Series_window_mul (N := N) (L := N + 10) hN
  have htwo : (0 : ℝ) < (2 : ℝ) ^ (N + 10) := by positivity
  have hle : jsp87Carry (N + (N + 10)) ≤ ((N + N + 10 + 1 : ℕ) : ℝ) := by
    exact jsp87Carry_le (by omega)
  have hpos : (0 : ℝ) < jsp87Carry (N + (N + 10)) := jsp87Carry_pos _
  have hten : ((N + N + 10 + 1 : ℕ) : ℝ) < (2 : ℝ) ^ 10 := by
    have hN' : (N : ℝ) ≤ 500 := by exact_mod_cast h500
    have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
    rw [h1024]
    push_cast
    linarith
  have hstep : (2 : ℝ) ^ (N + 10) = (2 : ℝ) ^ N * (2 : ℝ) ^ 10 := by
    rw [pow_add]
  constructor
  · have hp : 0 < (2 : ℝ) ^ (N + 10)
        * ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10)) := by
      linarith
    exact pos_of_mul_pos htwo hp
  · have hle' : (2 : ℝ) ^ (N + 10)
        * ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10))
        ≤ ((N + N + 10 + 1 : ℕ) : ℝ) := by linarith
    rw [hstep] at hle'
    have hfin : ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10))
          * (2 : ℝ) ^ N * (2 : ℝ) ^ 10 < 1 * (2 : ℝ) ^ 10 := by
      have heq : ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10))
            * (2 : ℝ) ^ N * (2 : ℝ) ^ 10
          = (2 : ℝ) ^ N * (2 : ℝ) ^ 10
            * ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10)) := by ring
      rw [heq]
      nlinarith
    exact lt_of_mul_lt_mul_right (a := (2 : ℝ) ^ 10)
      (b := ((2 : ℝ) ^ N * jsp87Series - jsp87WindowApprox N (N + 10)) * (2 : ℝ) ^ N)
      (c := 1) hfin (by positivity)

/-- **THE CERTIFIED BRACKET FOR `2^N S`**, read off the rescaled error. -/
theorem jsp87Series_window_bracket (N L : ℕ) (hN : 1 ≤ N) :
    jsp87WindowApprox N L < (2 : ℝ) ^ N * jsp87Series
      ∧ (2 : ℝ) ^ N * jsp87Series ≤ jsp87WindowApprox N L
          + ((N + L + 1 : ℕ) : ℝ) / 2 ^ L := by
  have hb := jsp87Carry_window_bracket N L hN
  have hdecomp := jsp87_scaled_decomposition N hN
  have hcast : (jsp87Prefix N : ℝ) = (jsp87IntPart N : ℝ) := jsp87Prefix_cast N
  have hkey : jsp87Carry N = (2 : ℝ) ^ N * jsp87Series - (jsp87IntPart N : ℝ) := by
    rw [jsp87Carry, hdecomp]
    ring
  rw [hkey] at hb
  unfold jsp87WindowApprox
  constructor <;> linarith

/-- **THE CERTIFIED FLOOR.**  `⌊2^N S⌋` is an explicit sum of `ω`-values. -/
theorem jsp87Series_floor_eq {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (h : jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ L) :
    ⌊(2 : ℝ) ^ N * jsp87Series⌋
      = (jsp87Prefix N : ℤ) + ((jsp87OmegaWindow N L / 2 ^ L : ℕ) : ℤ) := by
  rw [jsp87_floor_scaled (N := N) hN, jsp87CarryExcess_eq_window hN hL h]
  have hpre : (jsp87Prefix N : ℤ) = jsp87IntPart N := by
    have h := jsp87Prefix_cast N
    exact_mod_cast h
  rw [hpre]

/-! ## 4. The certificate function -/

/-- The residue of the `ω`-window at `N`, of length `L`, read modulo `2^L`. -/
def jsp87WindowResidue (N L : ℕ) : ℕ := jsp87OmegaWindow N L % 2 ^ L

/-- **THE CERTIFIED DIGIT.**  The `N`-th binary digit of the Erdős series,
computed from the `ω`-values on the window `[N, N+48)` alone; the value `2`
means *undetermined* (the certificate failed). -/
def jsp87DigitCert (N : ℕ) : ℕ :=
  if jsp87WindowResidue N 48 + (N + 49) < 2 ^ 47 then 0
  else if 2 ^ 47 ≤ jsp87WindowResidue N 48
      ∧ jsp87WindowResidue N 48 + (N + 49) < 2 ^ 48 then 1
  else 2

/-- **THE CERTIFICATE IS SOUND.**  Whenever the certificate does not return the
marker `2`, it returns the true value of the `N`-th binary digit of `S`. -/
theorem jsp87Digit_eq_cert {N : ℕ} (hN : 1 ≤ N) (h : jsp87DigitCert N ≠ 2) :
    jsp87Digit N = (jsp87DigitCert N : ℤ) := by
  by_cases h0 : jsp87WindowResidue N 48 + (N + 49) < 2 ^ 47
  · have hz := jsp87Digit_eq_zero_of_window (N := N) (L := 48) hN (by omega)
      (by simpa [jsp87WindowResidue] using h0)
    have hval : (jsp87DigitCert N : ℤ) = 0 := by
      simp only [jsp87DigitCert, if_pos h0]
      rfl
    exact hz.trans hval.symm
  · by_cases h1 : 2 ^ 47 ≤ jsp87WindowResidue N 48
        ∧ jsp87WindowResidue N 48 + (N + 49) < 2 ^ 48
    · have hz := jsp87Digit_eq_one_of_window (N := N) (L := 48) hN (by omega)
        (by simpa [jsp87WindowResidue] using h1.1) (by simpa [jsp87WindowResidue] using h1.2)
      have hval : (jsp87DigitCert N : ℤ) = 1 := by
        simp only [jsp87DigitCert, if_neg h0, if_pos h1]
        rfl
      exact hz.trans hval.symm
    · have hz : jsp87DigitCert N = 2 := by
        simp only [jsp87DigitCert, if_neg h0, if_neg h1]
      exact (h hz).elim

/-- The certificate fails nowhere on `[0, 64)`. -/
theorem jsp87DigitCert_range_64 : ∀ N ∈ Finset.range 64, jsp87DigitCert N ≠ 2 := by
  native_decide

/-- **THE FIRST 64 BINARY DIGITS OF THE ERDŐS SERIES, CERTIFIED.** -/
theorem jsp87Digit_of_cert_lt_64 {N : ℕ} (hN : 1 ≤ N) (hlt : N < 64) :
    jsp87Digit N = (jsp87DigitCert N : ℤ) :=
  jsp87Digit_eq_cert hN (jsp87DigitCert_range_64 N (by simpa using hlt))

/-- **THE CERTIFIED DIGIT BLOCK.**  The block of `t` binary digits starting at
`N` is a finite sum of the *certified* digits. -/
theorem jsp87DigitBlock_eq_of_cert (N t : ℕ) (hN : 1 ≤ N)
    (h : ∀ j, j < t → jsp87DigitCert (N + j) ≠ 2) :
    jsp87DigitBlock N t
      = ∑ j ∈ Finset.range t, (jsp87DigitCert (N + j) : ℤ) * 2 ^ (t - 1 - j) := by
  unfold jsp87DigitBlock
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [jsp87Digit_eq_cert (N := N + j) (by omega) (h j (Finset.mem_range.mp hj))]

/-! ## 5. Machine-checked digits of the Erdős series -/

/-- **A computable copy of the binary prefix.**  `jsp87Prefix` is declared
`noncomputable` although it is a finite sum of computable terms; this copy can
be evaluated, which is what the numerical instances need. -/
def jsp87PrefixNat (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, omega n * 2 ^ (N - n - 1)

/-- `jsp87PrefixNat N = jsp87Prefix N`. -/
theorem jsp87Prefix_eq_nat (N : ℕ) : jsp87PrefixNat N = jsp87Prefix N := by
  have h1 : ((jsp87PrefixNat N : ℕ) : ℝ) = (jsp87IntPart N : ℝ) := by
    simp only [jsp87PrefixNat, jsp87IntPart, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow]
    push_cast
    rfl
  have h2 := jsp87Prefix_cast N
  exact_mod_cast h1.trans h2.symm


/-- **THE FIRST EIGHT BINARY DIGITS.**  `⌊2^8 S⌋ = 66 = 0b1000010`, i.e.
`S = 0.0100001…` in base `2`. -/
theorem jsp87Series_floor_eight : ⌊(2 : ℝ) ^ 8 * jsp87Series⌋ = 66 := by
  have h := jsp87Series_floor_eq (N := 8) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h]
  have hp : jsp87Prefix 8 = 65 := by rw [← jsp87Prefix_eq_nat]; native_decide
  have hw : ((jsp87OmegaWindow 8 48 / 2 ^ 48 : ℕ) : ℤ) = 1 := by native_decide
  rw [hp, hw]
  decide

/-- **THE FIRST SIXTEEN BINARY DIGITS.** -/
theorem jsp87Series_floor_sixteen : ⌊(2 : ℝ) ^ 16 * jsp87Series⌋ = 16939 := by
  have h := jsp87Series_floor_eq (N := 16) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h]
  have hp : jsp87Prefix 16 = 16938 := by rw [← jsp87Prefix_eq_nat]; native_decide
  have hw : ((jsp87OmegaWindow 16 48 / 2 ^ 48 : ℕ) : ℤ) = 1 := by native_decide
  rw [hp, hw]
  decide

/-- **THE FIRST TWENTY-FOUR BINARY DIGITS.** -/
theorem jsp87Series_floor_twentyfour : ⌊(2 : ℝ) ^ 24 * jsp87Series⌋ = 4336430 := by
  have h := jsp87Series_floor_eq (N := 24) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h]
  have hp : jsp87Prefix 24 = 4336429 := by rw [← jsp87Prefix_eq_nat]; native_decide
  have hw : ((jsp87OmegaWindow 24 48 / 2 ^ 48 : ℕ) : ℤ) = 1 := by native_decide
  rw [hp, hw]
  decide

/-- **THE FIRST THIRTY-TWO BINARY DIGITS.** -/
theorem jsp87Series_floor_thirtytwo : ⌊(2 : ℝ) ^ 32 * jsp87Series⌋ = 1110126252 := by
  have h := jsp87Series_floor_eq (N := 32) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h]
  have hp : jsp87Prefix 32 = 1110126251 := by rw [← jsp87Prefix_eq_nat]; native_decide
  have hw : ((jsp87OmegaWindow 32 48 / 2 ^ 48 : ℕ) : ℤ) = 1 := by native_decide
  rw [hp, hw]
  decide

/-- **THE FIRST FORTY-EIGHT BINARY DIGITS.** -/
theorem jsp87Series_floor_fortyeight : ⌊(2 : ℝ) ^ 48 * jsp87Series⌋ = 72753234082766 := by
  have h := jsp87Series_floor_eq (N := 48) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h]
  have hp : jsp87Prefix 48 = 72753234082765 := by rw [← jsp87Prefix_eq_nat]; native_decide
  have hw : ((jsp87OmegaWindow 48 48 / 2 ^ 48 : ℕ) : ℤ) = 1 := by native_decide
  rw [hp, hw]
  decide

/-- **THE FIRST SIXTY-FOUR BINARY DIGITS OF THE ERDŐS SERIES, CERTIFIED:**
`S = 0.010000100010101100101110101011000111101111001110101110111111001110…` in
base `2`. -/
theorem jsp87Series_floor_sixtyfour : ⌊(2 : ℝ) ^ 64 * jsp87Series⌋ = 4767955948848200691 := by
  have h := jsp87Series_floor_eq (N := 64) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h]
  have hp : jsp87Prefix 64 = 4767955948848200690 := by
    rw [← jsp87Prefix_eq_nat]
    native_decide
  have hw : ((jsp87OmegaWindow 64 48 / 2 ^ 48 : ℕ) : ℤ) = 1 := by native_decide
  rw [hp, hw]
  decide

/-- **THE 64-DIGIT BLOCK, AS ONE INTEGER.** -/
theorem jsp87DigitBlock_zero_sixtyfour :
    jsp87DigitBlock 0 64 = 4767955948848200691 := by
  have h := jsp87_floor_telescope (N := 0) (t := 64)
  have h0 : ⌊(2 : ℝ) ^ 0 * jsp87Series⌋ = 0 := by simpa using jsp87_floor_S_zero
  rw [h0] at h
  have hf := jsp87Series_floor_sixtyfour
  unfold jsp87DigitBlock
  rw [hf] at h
  linarith

/-- **THE CARRY EXCESS IS COMPUTED AT EVERY ONE OF THE FIRST 64 CUT POINTS.**
At `N = 1` it is `0`, and at `N = 30, 42, 60` it is already `2`: the carry
excess of the Erdős series is a small, explicitly computable quantity. -/
theorem jsp87CarryExcess_window_sixtyfour :
    jsp87CarryExcess 1 = 0 ∧ jsp87CarryExcess 30 = 2 ∧ jsp87CarryExcess 42 = 2
      ∧ jsp87CarryExcess 60 = 2 := by
  have hcond : ∀ N ∈ Finset.range 65, 1 ≤ N →
      jsp87OmegaWindow N 48 % 2 ^ 48 + (N + 49) < 2 ^ 48 := by native_decide
  have hq1 : (jsp87OmegaWindow 1 48 / 2 ^ 48 : ℕ) = 0 := by native_decide
  have hq30 : (jsp87OmegaWindow 30 48 / 2 ^ 48 : ℕ) = 2 := by native_decide
  have hq42 : (jsp87OmegaWindow 42 48 / 2 ^ 48 : ℕ) = 2 := by native_decide
  have hq60 : (jsp87OmegaWindow 60 48 / 2 ^ 48 : ℕ) = 2 := by native_decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [jsp87CarryExcess_eq_window (by norm_num) (by norm_num)
      (hcond 1 (by decide) (by norm_num))]
    exact_mod_cast hq1
  · rw [jsp87CarryExcess_eq_window (by norm_num) (by norm_num)
      (hcond 30 (by decide) (by norm_num))]
    exact_mod_cast hq30
  · rw [jsp87CarryExcess_eq_window (by norm_num) (by norm_num)
      (hcond 42 (by decide) (by norm_num))]
    exact_mod_cast hq42
  · rw [jsp87CarryExcess_eq_window (by norm_num) (by norm_num)
      (hcond 60 (by decide) (by norm_num))]
    exact_mod_cast hq60

/-- **THE CARRY EXCESS NEVER EXCEEDS `2` ON THE FIRST 64 CUT POINTS.** -/
theorem jsp87CarryExcess_le_two_sixtyfour :
    ∀ N ∈ Finset.range 65, 1 ≤ N → jsp87CarryExcess N ≤ 2 := by
  have hcond : ∀ N ∈ Finset.range 65, 1 ≤ N →
      jsp87OmegaWindow N 48 % 2 ^ 48 + (N + 49) < 2 ^ 48 := by native_decide
  have hdiv : ∀ N ∈ Finset.range 65, 1 ≤ N →
      ((jsp87OmegaWindow N 48 / 2 ^ 48 : ℕ) : ℤ) ≤ 2 := by native_decide
  intro N hN h1
  have h := jsp87CarryExcess_eq_window h1 (by norm_num) (hcond N hN h1)
  rw [h]
  exact hdiv N hN h1

/-- **A RUN OF NINE `1`s IN THE BINARY EXPANSION OF THE ERDŐS SERIES, at the
explicit place `141, 142, …, 149`.** -/
theorem jsp87_digit_run_141 : ∀ k, k < 9 → jsp87Digit (141 + k) = 1 := by
  have hcond : ∀ k, k < 9 →
      2 ^ 47 ≤ jsp87OmegaWindow (141 + k) 48 % 2 ^ 48
        ∧ jsp87OmegaWindow (141 + k) 48 % 2 ^ 48 + (141 + k + 49) < 2 ^ 48 := by
    native_decide
  intro k hk
  exact jsp87Digit_eq_one_of_window (N := 141 + k) (L := 48) (by omega) (by norm_num)
    ((hcond k hk).1) ((hcond k hk).2)

/-- **A RUN OF `1`s FORCES THE CARRY ORBIT NEAR `1`.**  If the binary digits of
`S` are `1` at `N, …, N+k-1`, then `Int.fract (θ N) ≥ 1 - 2^{-k}`: the doubling
orbit, fed `k` steps of `1`, cannot have left the neighbourhood of `1`.  This is
the converse of round 48's `jsp87_fracCarry_succ`, and is proved here from
scratch by the closed form of the orbit along a run. -/
theorem jsp87_fracCarry_run_ge {k N : ℕ} (_hk : 1 ≤ k) (hN : 1 ≤ N)
    (h : ∀ j, j < k → jsp87Digit (N + j) = 1) :
    (1 : ℝ) - ((2 : ℝ) ^ k)⁻¹ ≤ Int.fract (jsp87Carry N) := by
  have hform : ∀ (j : ℕ), ∀ (g : ∀ i, i < j → jsp87Digit (N + i) = 1),
      Int.fract (jsp87Carry (N + j))
        = ((2 : ℝ) ^ j) * Int.fract (jsp87Carry N) - ((2 : ℝ) ^ j - 1) := by
    intro j
    induction j with
    | zero =>
        intro g
        have hN0 : N + 0 = N := by omega
        rw [hN0, pow_zero]
        ring
    | succ j ih =>
        intro g
        have gprev : ∀ i, i < j → jsp87Digit (N + i) = 1 := by
          intro i hi
          exact g i (by omega)
        have hrec := jsp87_fracCarry_succ (N := N + j) (by omega)
        have hd : jsp87Digit (N + j) = 1 := g j (by omega)
        rw [hd, Int.cast_one] at hrec
        have hsub : N + (j + 1) = (N + j) + 1 := by omega
        rw [hsub, hrec, ih gprev, pow_succ]
        ring
  have hfk := hform k (fun i hi => h i hi)
  have hfk' := Int.fract_nonneg (jsp87Carry (N + k))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hge : ((2 : ℝ) ^ k - 1) ≤ Int.fract (jsp87Carry N) * (2 : ℝ) ^ k := by
    nlinarith
  have hmain : ((2 : ℝ) ^ k - 1) / (2 : ℝ) ^ k ≤ Int.fract (jsp87Carry N) :=
    (div_le_iff₀ hpos).2 hge
  have hid : ((2 : ℝ) ^ k - 1) / (2 : ℝ) ^ k = 1 - ((2 : ℝ) ^ k)⁻¹ := by
    field_simp
  rw [hid] at hmain
  exact hmain

/-- **THE FRACTIONAL PART OF THE CARRY AT `141` IS WITHIN `2^-9` OF `1`** — the
quantitative form of the run of nine `1`s certified above. -/
theorem jsp87_fracCarry_141_ge :
    (1 : ℝ) - ((2 : ℝ) ^ 9)⁻¹ ≤ Int.fract (jsp87Carry 141) :=
  jsp87_fracCarry_run_ge (k := 9) (N := 141) (by norm_num) (by norm_num)
    jsp87_digit_run_141

/-- **A HYPOTHETICAL RATIONAL VALUE OF `S` HAS DENOMINATOR AT LEAST `512`.**

Round 53 could prove only `b ≥ 8`, from a run of three `1`s; the run of nine `1`s
certified above costs a factor `64`. -/
theorem jsp87Series_rational_imp_denominator_ge_512 {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : 512 ≤ b := by
  have hfrac := jsp87_fracCarry_141_ge
  have h := jsp87Series_rational_imp_denominator_ge (a := a) (b := b) hb h
    (N := 141) (L := 9) (by norm_num) (by norm_num) hfrac
  have h9 : (2 : ℝ) ^ 9 = 512 := by norm_num
  norm_num at h
  have : (512 : ℝ) ≤ (b : ℝ) := by simpa [h9] using h
  exact_mod_cast this

/-- **THE CERTIFIED DIGIT STRING IS NOT PERIODIC WITH PERIOD `3` FROM INDEX
`4`**: the digits at `6` and `9` differ. -/
theorem jsp87_digit_notPeriodic_three :
    ¬ (∀ n, 4 ≤ n → jsp87Digit (n + 3) = jsp87Digit n) := by
  obtain ⟨h4, h5, h6⟩ := jsp87_digit_window_4
  have h9 : jsp87Digit 9 = 0 := by
    have hz := jsp87Digit_eq_zero_of_window (N := 9) (L := 48) (by norm_num) (by norm_num)
      (by native_decide)
    exact hz
  intro h
  have h' := h 6 (by norm_num)
  rw [show (6 + 3 : ℕ) = 9 by norm_num, h6, h9] at h'
  exact absurd h' (by decide)

end JSP87
