/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.MomentLadder
import Mathlib.Tactic

/-!
# JSP-000087 : the third rung of the moment ladder, and the Faulhaber arithmetic

Rounds 104–107 built the **layer-cake** decomposition of the Erdős series and its
first two moments:

```
S        = ∑' k, k   · L k                       (round 106, level family)
S + 1    = ∑' k,       A k                       (round 104, "at least" family)
∑' n, (ω n (ω n + 1) / 2) · 2^-(n+1) = ∑' k, k · A k        (round 107)
∑' n, ω n² · 2^-(n+1) + S = ∑' k, 2k · A k                 (round 107)
```

This module carries the ladder one rung further, and pays the two prices that
required: **Faulhaber's formula for squares** (which Mathlib does not have under
that name — proved here by induction, first in `ℝ`, then pushed back to `ℕ`), and
the **closed forms of the weighted geometric series** (which Mathlib *does* have,
in `Mathlib.Analysis.SpecificLimits.Normed`: `tsum_coe_mul_geometric_of_norm_lt_one`,
`tsum_sq_mul_geometric_of_norm_lt_one` and the Stirling-number form
`tsum_pow_mul_geometric_of_norm_lt_one` — the last of which was **absent from the
previous rounds' searches** and which is what closes round 107's recorded missing
lemma `tsum_jsp87Sq_two_pow_neg`).

## 1. The closed forms (§0)

With the normalisation `∑' n, nᵖ · 2^-(n+1)`:

```
∑' n, n   · 2^-(n+1) = 1
∑' n, n²  · 2^-(n+1) = 3          (the mirror image of `1`)
∑' n, n³  · 2^-(n+1) = 13
∑' n, (n+1)³ · 2^-n  = 52         (the shifted form, for the error term of §6)
```

The third of these is new and sharp: `jsp87CubeSeries ≤ 13`, an improvement on
round 107's `jsp87SquareSeries ≤ 2 · jsp87TriSeries ≤ 4`.

## 2. Faulhaber for squares (§1)

`jsp87_sq m = 1² + 2² + … + m²` satisfies `6 · jsp87_sq m = m (m + 1) (2m + 1)`,
hence `jsp87_sq m = m (m + 1) (2m + 1) / 6`.

## 3. The cube moment and the third reflection (§2–§3)

The cube moment `jsp87CubeSeries = ∑' n, ω n³ · 2^-(n+1)` is the *level*-side
third moment: weighting the *level* indicators by `k²` reproduces `ω n³` at each
cut point, exactly as round 106 reproduced `ω n` by weighting by `k`:

```
jsp87CubeSeries = ∑' k, k² · L k                   (the third reflection, level side)
```

## 4. The cumulative-square ladder (§4–§5)

Weighting the *"at least"* indicators by `k²` reproduces the **truncated square
sum** `1² + … + ω n²` at each cut point, and its columns saturate at the *same*
cut point `n = 2^M` as rounds 106 and 107:

```
jsp87CumSqSeries = ∑' k, k² · A k                   (the third reflection, at-least side)
6 · jsp87CumSqSeries = 2 · jsp87CubeSeries + 3 · jsp87SquareSeries + jsp87Series
```

so the three moments `S`, `S^(2)`, `jsp87CumSqSeries` and the cube moment are
**linearly dependent with rational coefficients** — the only new content of the
Faulhaber step, expressed as a theorem.

Nothing here moves the gate.  The headline `jsp_000087_main` is the irrationality
of `S`, which is *conditional* in the published literature (Pratt,
arXiv:2409.15185, under a uniform prime `k`-tuples hypothesis); the blocker is
unchanged, namely `jsp87_digit_not_eventuallyPeriodic` (aperiodicity of the binary
digit string of `S`, equivalently of the doubling orbit `Int.fract (θ N)`).
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 8000000

/-! ## 0. The shift relation, and the closed forms of the weighted geometric series -/

/-- **THE `tsum` SHIFT RELATION.**  `∑' l, f (l + 1)` is the full sum minus the
zeroth term — the source of every "shifted" closed form in this file. -/
private theorem tsum_shift_one {f : ℕ → ℝ} (hf : Summable f) :
    (∑' (l : ℕ), f (l + 1)) = (∑' (l : ℕ), f l) - f 0 := by
  have h := hf.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  linarith

/-- **THE WEIGHTED GEOMETRIC SERIES IS SUMMABLE**, for every exponent, in the
`(1/2)ⁿ` normalisation: `∑ n, nᵖ (1/2)ⁿ`.  This is Mathlib's
`summable_pow_mul_geometric_of_norm_lt_one`. -/
private theorem summable_pow_pow_half (p : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ p * ((2 : ℝ)⁻¹) ^ n) :=
  summable_pow_mul_geometric_of_norm_lt_one p (r := (2 : ℝ)⁻¹) (by norm_num)

private theorem summable_linear_pow_inv :
    Summable (fun n : ℕ => (n : ℝ) * ((2 : ℝ)⁻¹) ^ n) :=
  (summable_pow_pow_half 1).congr fun n => by rw [pow_one]

/-- **THE WEIGHTED GEOMETRIC SERIES IS SUMMABLE AFTER THE SHIFT `n ↦ n + 1`** —
Mathlib's `summable_nat_add_iff`; the reason every shifted series below is
summable, and the shift relation itself is `tsum_shift_one`. -/
private theorem summable_pow_pow_half_succ (p : ℕ) :
    Summable (fun n : ℕ => (((n + 1) ^ p : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (n + 1)) := by
  refine ((summable_nat_add_iff (k := 1)
      (f := fun n : ℕ => (n : ℝ) ^ p * ((2 : ℝ)⁻¹) ^ n)).mpr (summable_pow_pow_half p)).congr
    fun n => ?_
  rw [Nat.cast_pow]

/-- **THE LINEAR GEOMETRIC SERIES, EXACTLY**: `∑' n, n (1/2)ⁿ = 2`. -/
private theorem tsum_linear_pow_half : (∑' (n : ℕ), (n : ℝ) * ((2 : ℝ)⁻¹) ^ n) = 2 := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)]
  norm_num

/-- **THE QUADRATIC GEOMETRIC SERIES, EXACTLY**: `∑' n, n² (1/2)ⁿ = 6`.  This is
Mathlib's `tsum_sq_mul_geometric_of_norm_lt_one`, used here for the first time. -/
private theorem tsum_square_pow_half : (∑' (n : ℕ), (n : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ n) = 6 := by
  rw [tsum_sq_mul_geometric_of_norm_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)]
  norm_num

/-- **THE CUBIC GEOMETRIC SERIES, EXACTLY**: `∑' n, n³ (1/2)ⁿ = 26`.  Mathlib's
general form (`tsum_pow_mul_geometric_of_norm_lt_one`) evaluates the Stirling
number by hand; this lemma was NOT found in rounds 106–107's Mathlib searches. -/
private theorem tsum_cube_pow_half : (∑' (n : ℕ), (n : ℝ) ^ 3 * ((2 : ℝ)⁻¹) ^ n) = 26 := by
  rw [tsum_pow_mul_geometric_of_norm_lt_one 3 (r := (2 : ℝ)⁻¹) (by norm_num)]
  simp only [Finset.sum_range_succ_comm]
  norm_num [Nat.stirlingSecond, Nat.stirlingFirst]

private theorem summable_cube_two_pow :
    Summable (fun n : ℕ => ((n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  refine (summable_pow_pow_half 3).mul_left ((2 : ℝ)⁻¹) |>.congr fun n => ?_
  rw [Nat.cast_pow, two_pow_neg_eq, pow_succ]
  ring

private theorem summable_square_two_pow :
    Summable (fun n : ℕ => ((n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  refine (summable_pow_pow_half 2).mul_left ((2 : ℝ)⁻¹) |>.congr fun n => ?_
  rw [Nat.cast_pow, two_pow_neg_eq, pow_succ]
  ring

private theorem summable_linear_two_pow :
    Summable (fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  refine summable_linear_pow_inv.mul_left ((2 : ℝ)⁻¹) |>.congr fun n => ?_
  rw [two_pow_neg_eq, pow_succ]
  ring

/-- The cubic majorant `∑ n, (n + 1)³ · 2^-(n+1)` is summable: it is the shifted
cubic geometric series. -/
theorem summable_cube_majorant :
    Summable (fun n : ℕ => (((n + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  refine summable_pow_pow_half_succ 3 |>.congr fun n => ?_
  rw [two_pow_neg_eq]

/-- **THE SHIFTED CUBIC GEOMETRIC SERIES, EXACTLY**:
`∑' j, (j + 1)³ · 2^-(j+1) = 26`, the shift of `tsum_cube_pow_half`. -/
theorem jsp87_tsum_cube_shift_succ :
    (∑' (j : ℕ), (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹) = 26 := by
  calc (∑' (j : ℕ), (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹)
      = ∑' (j : ℕ), (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (j + 1) := by
        refine tsum_congr fun j => ?_
        rw [two_pow_neg_eq]
    _ = ∑' (l : ℕ), ((l + 1 : ℕ) : ℝ) ^ 3 * ((2 : ℝ)⁻¹) ^ (l + 1) := by
        refine tsum_congr fun j => ?_
        rw [Nat.cast_pow]
    _ = 26 := (tsum_shift_one (summable_pow_pow_half 3)).trans (by
      rw [tsum_cube_pow_half]
      norm_num)

/-- **THE CLOSED FORM OF THE LINEAR WEIGHTED GEOMETRIC SERIES**, in the
normalisation of the Erdős series: `∑' n, n · 2^-(n+1) = 1`. -/
theorem jsp87_tsum_linear_two_pow :
    (∑' (n : ℕ), ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  have hmain : (∑' (n : ℕ), ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (2 : ℝ)⁻¹ * ∑' (n : ℕ), (n : ℝ) * ((2 : ℝ)⁻¹) ^ n :=
    (tsum_congr fun n => by rw [two_pow_neg_eq, pow_succ]; ring).trans
      (Summable.tsum_mul_left ((2 : ℝ)⁻¹) summable_linear_pow_inv)
  rw [hmain, tsum_linear_pow_half]
  norm_num

/-- **THE CLOSED FORM OF THE QUADRATIC WEIGHTED GEOMETRIC SERIES** — round 107's
recorded missing lemma, now closed:

```
∑' n, n² · 2^-(n+1) = 3
```

(the value is `3`; round 107's policy file guessed `2`). -/
theorem jsp87_tsum_square_two_pow :
    (∑' (n : ℕ), ((n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 3 := by
  have hmain : (∑' (n : ℕ), ((n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (2 : ℝ)⁻¹ * ∑' (n : ℕ), (n : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ n :=
    (tsum_congr fun n => by rw [Nat.cast_pow, two_pow_neg_eq, pow_succ]; ring).trans
      (Summable.tsum_mul_left ((2 : ℝ)⁻¹) (summable_pow_pow_half 2))
  rw [hmain, tsum_square_pow_half]
  norm_num

/-- **THE CLOSED FORM OF THE CUBIC WEIGHTED GEOMETRIC SERIES**:
`∑' n, n³ · 2^-(n+1) = 13`. -/
theorem jsp87_tsum_cube_two_pow :
    (∑' (n : ℕ), ((n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 13 := by
  have hmain : (∑' (n : ℕ), ((n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (2 : ℝ)⁻¹ * ∑' (n : ℕ), (n : ℝ) ^ 3 * ((2 : ℝ)⁻¹) ^ n :=
    (tsum_congr fun n => by rw [Nat.cast_pow, two_pow_neg_eq, pow_succ]; ring).trans
      (Summable.tsum_mul_left ((2 : ℝ)⁻¹) (summable_pow_pow_half 3))
  rw [hmain, tsum_cube_pow_half]
  norm_num

/-- A factor `2` undoes one step of the `(1/2)ⁿ` normalisation. -/
private theorem two_mul_inv_pow_succ (j : ℕ) :
    (2 : ℝ) * ((2 : ℝ)⁻¹) ^ (j + 1) = ((2 : ℝ)⁻¹) ^ j := by
  rw [pow_succ, mul_comm ((2 : ℝ)⁻¹ ^ j) ((2 : ℝ)⁻¹), ← mul_assoc,
    mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]

/-- The same, with an arbitrary factor in between. -/
private theorem two_mul_middle (X : ℝ) (j : ℕ) :
    2 * (X * ((2 : ℝ)⁻¹) ^ (j + 1)) = X * ((2 : ℝ)⁻¹) ^ j := by
  have hz : (2 : ℝ) * ((2 : ℝ)⁻¹) = 1 := mul_inv_cancel₀ (by norm_num)
  calc 2 * (X * ((2 : ℝ)⁻¹) ^ (j + 1)) = 2 * (X * (((2 : ℝ)⁻¹) ^ j * (2 : ℝ)⁻¹)) := by
        rw [pow_succ]
    _ = ((2 : ℝ) * ((2 : ℝ)⁻¹)) * (X * ((2 : ℝ)⁻¹) ^ j) := by ring
    _ = X * ((2 : ℝ)⁻¹) ^ j := by rw [hz, one_mul]

/-- **THE SHIFTED CLOSED FORM** `∑' j, (j + 1)³ · 2^-j = 52`, the majorant used in
§6 for the doubly-exponential error term. -/
theorem jsp87_tsum_cube_shift :
    (∑' (j : ℕ), (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ j)⁻¹) = 52 := by
  have hconv : Summable (fun j : ℕ => (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
    refine (summable_pow_pow_half_succ 3).mul_left 2 |>.congr fun n => ?_
    rw [← inv_pow, Nat.cast_pow, two_mul_middle]
  have hmain : (∑' (j : ℕ), (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ j)⁻¹)
      = 2 * ∑' (j : ℕ), (((j + 1) ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹ :=
    (tsum_congr fun j => by
      simp only [← inv_pow]
      rw [two_mul_middle]).trans
      (Summable.tsum_mul_left 2 summable_cube_majorant)
  rw [hmain, jsp87_tsum_cube_shift_succ]
  norm_num

/-! ## 1. Faulhaber for squares -/

/-- **THE SQUARE SUM.**  `jsp87_sq m = 1² + 2² + … + m²`, the number that the
`k²`-weighted layer cake produces at a cut point whose `ω`-value is `m`. -/
def jsp87_sq (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), k ^ 2

theorem jsp87_sq_zero : jsp87_sq 0 = 0 := by
  norm_num [jsp87_sq]

theorem jsp87_sq_one : jsp87_sq 1 = 1 := by
  norm_num [jsp87_sq]

theorem jsp87_sq_two : jsp87_sq 2 = 5 := by
  norm_num [jsp87_sq]

theorem jsp87_sq_four : jsp87_sq 4 = 30 := by
  norm_num [jsp87_sq]

/-- **THE RECURSION** `jsp87_sq (m + 1) = jsp87_sq m + (m + 1)²`. -/
theorem jsp87_sq_succ (m : ℕ) : jsp87_sq (m + 1) = jsp87_sq m + (m + 1) ^ 2 := by
  simp only [jsp87_sq, Finset.sum_range_succ_comm]
  ring

/-- **FAULHABER'S FORMULA FOR SQUARES, IN `ℝ`.**  The degree-3 identity is closed
by `linear_combination` against the induction hypothesis. -/
private theorem jsp87_sq_cast_mul_six (m : ℕ) :
    6 * ((jsp87_sq m : ℕ) : ℝ) = ((m * (m + 1) * (2 * m + 1) : ℕ) : ℝ) := by
  induction m with
  | zero => norm_num [jsp87_sq]
  | succ m ih =>
    have hrec := jsp87_sq_succ m
    rw [hrec]
    push_cast at ih ⊢
    linear_combination ih

/-- **FAULHABER'S FORMULA FOR SQUARES, IN `ℕ`** — the arithmetic this round needed:
`6 · (1² + … + m²) = m (m + 1) (2m + 1)`. -/
theorem jsp87_sq_mul_six (m : ℕ) : 6 * jsp87_sq m = m * (m + 1) * (2 * m + 1) := by
  exact_mod_cast jsp87_sq_cast_mul_six m

/-- **FAULHABER'S FORMULA FOR SQUARES, WITH THE DIVISION.** -/
theorem jsp87_sq_formula (m : ℕ) : jsp87_sq m = m * (m + 1) * (2 * m + 1) / 6 := by
  have h := jsp87_sq_mul_six m
  have hd : 6 ∣ m * (m + 1) * (2 * m + 1) := by
    rw [← h]
    exact Nat.dvd_mul_right 6 (jsp87_sq m)
  have hm : 6 * (m * (m + 1) * (2 * m + 1) / 6) = m * (m + 1) * (2 * m + 1) :=
    Nat.mul_div_cancel' hd
  exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 6) (h.trans hm.symm)

/-- The same formula in `ℝ`, cleared of the denominator. -/
theorem jsp87_sq_cast_mul_six' (m : ℕ) :
    6 * ((jsp87_sq m : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) := by
  exact_mod_cast jsp87_sq_mul_six m

/-- **THE SQUARE SUM IS AT MOST THE NEXT CUBE** `1² + … + m² ≤ (m + 1)³` — the
majorant that makes `jsp87Sq2Term` summable. -/
theorem jsp87_sq_le_succ_cube (m : ℕ) : jsp87_sq m ≤ (m + 1) ^ 3 := by
  have h1 : ∀ k ∈ Finset.range (m + 1), k ^ 2 ≤ (m + 1) ^ 2 := fun k hk =>
    Nat.pow_le_pow_left (Nat.le_of_lt (Finset.mem_range.mp hk)) 2
  calc jsp87_sq m = ∑ k ∈ Finset.range (m + 1), k ^ 2 := rfl
    _ ≤ ∑ k ∈ Finset.range (m + 1), (m + 1) ^ 2 := Finset.sum_le_sum fun k hk => h1 k hk
    _ = (m + 1) * (m + 1) ^ 2 := by
        norm_num [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (m + 1) ^ 3 := by ring

theorem jsp87_sq_mono {m n : ℕ} (h : m ≤ n) : jsp87_sq m ≤ jsp87_sq n := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    rw [hm]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with hmn | hmn
    · have hm : m = n + 1 := by omega
      rw [hm]
    · have hm : m ≤ n := by omega
      rw [jsp87_sq_succ]
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.add_le_add_right (ih hm) ((n + 1) ^ 2))

/-! ## 2. The cube moment -/

/-- **THE CUBE MOMENT TERM.** -/
noncomputable def jsp87CubeTerm (n : ℕ) : ℝ := ((omega n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

theorem jsp87CubeTerm_nonneg (n : ℕ) : 0 ≤ jsp87CubeTerm n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE CUBE MOMENT OF `ω`.** -/
noncomputable def jsp87CubeSeries : ℝ := ∑' (n : ℕ), jsp87CubeTerm n

theorem summable_jsp87CubeTerm : Summable jsp87CubeTerm :=
  Summable.of_nonneg_of_le (fun n => jsp87CubeTerm_nonneg n)
    (fun n => mul_le_mul_of_nonneg_right
      (by have h1 : omega n ^ 3 ≤ (omega n + 1) ^ 3 := Nat.pow_le_pow_left
            (Nat.le_succ _) 3
          have h2 : omega n + 1 ≤ n + 1 := Nat.add_le_add_right (omega_le_self n) 1
          have h3 : ((omega n + 1) ^ 3 : ℕ) ≤ ((n + 1) ^ 3 : ℕ) := Nat.pow_le_pow_left h2 3
          exact_mod_cast Nat.le_trans h1 h3) (by positivity))
    summable_cube_majorant

theorem jsp87CubeSeries_nonneg : 0 ≤ jsp87CubeSeries :=
  tsum_nonneg fun n => jsp87CubeTerm_nonneg n

/-- **THE CUBE MOMENT IS AT MOST `13`** — the closed form of §0 attached to the
moment itself. -/
theorem jsp87CubeSeries_le_thirteen : jsp87CubeSeries ≤ 13 := by
  have h' := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right
      (by have : omega n ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left (omega_le_self n) 3
          exact_mod_cast this) (by positivity))
    summable_jsp87CubeTerm summable_cube_two_pow
  calc jsp87CubeSeries = ∑' (n : ℕ), ((omega n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := rfl
    _ ≤ ∑' (n : ℕ), ((n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := h'
    _ = 13 := jsp87_tsum_cube_two_pow

/-- **THE SQUARE MOMENT IS AT MOST `3`** — the improvement of round 107's
`jsp87SquareSeries ≤ 2 · jsp87TriSeries ≤ 4` enabled by `jsp87_tsum_square_two_pow`. -/
theorem jsp87SquareSeries_le_three : jsp87SquareSeries ≤ 3 := by
  have h' := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right
      (by have : omega n ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (omega_le_self n) 2
          exact_mod_cast this) (by positivity))
    summable_jsp87SqTerm summable_square_two_pow
  calc jsp87SquareSeries = ∑' (n : ℕ), ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := rfl
    _ ≤ ∑' (n : ℕ), ((n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := h'
    _ = 3 := jsp87_tsum_square_two_pow

/-- A closed-form lower bound for the cube moment. -/
theorem jsp87CubeSeries_ge_seventySeven : (77 / 256 : ℝ) ≤ jsp87CubeSeries := by
  have hsum := Summable.sum_le_tsum (Finset.range 8) (fun i _ => jsp87CubeTerm_nonneg i)
    summable_jsp87CubeTerm
  have hval : (∑ i ∈ Finset.range 8, jsp87CubeTerm i) = 77 / 256 := by
    have h0 : omega 0 = 0 := omega_zero
    have h1 : omega 1 = 0 := omega_one
    have h2 : omega 2 = 1 := by native_decide
    have h3 : omega 3 = 1 := by native_decide
    have h4 : omega 4 = 1 := by native_decide
    have h5 : omega 5 = 1 := by native_decide
    have h6 : omega 6 = 2 := by native_decide
    have h7 : omega 7 = 1 := by native_decide
    simp only [Finset.sum_range_succ_comm]
    norm_num [jsp87CubeTerm, h0, h1, h2, h3, h4, h5, h6, h7]
  rwa [hval] at hsum

theorem jsp87CubeSeries_pos : 0 < jsp87CubeSeries := by
  linarith [jsp87CubeSeries_ge_seventySeven, show (0 : ℝ) < 77 / 256 by norm_num]

/-- **THE SQUARE MOMENT IS AT MOST THE CUBE MOMENT**, pointwise in `ω`. -/
theorem jsp87CubeSeries_ge_squareSeries : jsp87SquareSeries ≤ jsp87CubeSeries := by
  refine Summable.tsum_le_tsum (fun n => ?_) summable_jsp87SqTerm summable_jsp87CubeTerm
  unfold jsp87SqTerm jsp87CubeTerm
  refine mul_le_mul_of_nonneg_right (by
    rcases Nat.eq_zero_or_pos (omega n) with h0 | h1
    · rw [h0]
      norm_num
    · have h2 : omega n ^ 2 * 1 ≤ omega n ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h1)
      exact_mod_cast (by simpa using h2)) (by positivity)

theorem jsp87CubeSeries_ge_triSeries : jsp87TriSeries ≤ jsp87CubeSeries := by
  have h1 := jsp87TriSeries_two_eq_add_sq
  have h2 : 0 ≤ jsp87Series := jsp87Series_nonneg
  have h3 : jsp87SquareSeries ≤ jsp87CubeSeries := jsp87CubeSeries_ge_squareSeries
  have h4 : jsp87Series ≤ jsp87TriSeries := jsp87TriSeries_ge_series
  linarith

/-- `dist x 0 = |x|`, needed by the metric convergence proofs below. -/
private theorem dist_zero_eq (x : ℝ) : dist x 0 = |x| := by
  rw [dist_eq_norm, Real.norm_eq_abs]
  simp

/-! ## 3. The third reflection: the square weight against the LEVEL family -/

/-- **THE SQUARE-WEIGHTED LEVEL COUNT AT `n`.**  Only the level of index `k = ω n`
contributes, and it carries weight `ω n²`; it is visible exactly when `ω n < M`.
The square-weighted mirror of round 106's `jsp87_weightCount`. -/
theorem jsp87_sqWeightCount (M n : ℕ) :
    ∑ k ∈ Finset.range M, k ^ 2 * jsp87Level k n = if omega n < M then omega n ^ 2 else 0 := by
  rcases Nat.lt_or_ge (omega n) M with hM | hM
  · have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
      intro a ha
      exact Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_of_lt hM))
    have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range (omega n + 1) →
        k ^ 2 * jsp87Level k n = 0 := by
      intro k _ hna
      have hna' : ¬ (k < omega n + 1) := fun hh => hna (Finset.mem_range.mpr hh)
      have hstep : omega n + 1 ≤ k := Nat.le_of_not_gt hna'
      have hne : omega n ≠ k := by
        intro hk
        have : omega n + 1 ≤ omega n := by rwa [← hk] at hstep
        exact (Nat.lt_irrefl (omega n)) (Nat.lt_succ_self _ |>.trans_le this)
      rw [jsp87Level_eq_zero_of_omega_ne hne]
      norm_num
    have hswap : (∑ k ∈ Finset.range (omega n + 1), k ^ 2 * jsp87Level k n)
        = ∑ k ∈ Finset.range M, k ^ 2 * jsp87Level k n :=
      Finset.sum_subset hsub hzero
    have hinner : (∑ k ∈ Finset.range (omega n + 1), k ^ 2 * jsp87Level k n)
        = omega n ^ 2 := by
      rw [Finset.sum_eq_single (omega n) (by
            intro b _ hb
            rw [jsp87Level_eq_zero_of_omega_ne (Ne.symm hb)]
            norm_num) (by simp [Finset.mem_range])]
      have hone : omega n ^ 2 * jsp87Level (omega n) n = omega n ^ 2 := by
        rw [jsp87Level_eq_one_of_omega_eq rfl]
        ring
      exact hone
    rw [← hswap, hinner, ite_eq_left hM]
  · have hzero : ∀ k ∈ Finset.range M, k ^ 2 * jsp87Level k n = 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hne : omega n ≠ k := by
        intro hkeq
        have hlt' : k < omega n := hk'.trans_le hM
        exact (Nat.lt_irrefl k) (hkeq ▸ hlt')
      rw [jsp87Level_eq_zero_of_omega_ne hne]
      norm_num
    rw [Finset.sum_eq_zero hzero, ite_eq_right (Nat.not_lt.mpr hM)]

/-- The square-weighted level count, read in `ℝ`. -/
theorem jsp87_sqWeightCount_cast (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k ^ 2 * jsp87Level k n : ℕ) : ℝ))
      = ((if omega n < M then omega n ^ 2 else 0 : ℕ) : ℝ) := by
  rw [← Nat.cast_sum, jsp87_sqWeightCount]

/-- **THE SQUARE-WEIGHTED COLUMN AT `n`.** -/
noncomputable def jsp87SqWeightColumn (M n : ℕ) : ℝ :=
  ((∑ k ∈ Finset.range M, k ^ 2 * jsp87Level k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

private theorem cast_sum_sqWeight (M n : ℕ) :
    ((∑ k ∈ Finset.range M, k ^ 2 * jsp87Level k n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range M, ((k ^ 2 * jsp87Level k n : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]

theorem jsp87_sqWeightedLevel_sum_eq (M n : ℕ) :
    (∑ k ∈ Finset.range M,
        ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n)) = jsp87SqWeightColumn M n := by
  unfold jsp87SqWeightColumn
  calc (∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑ k ∈ Finset.range M,
          (((k ^ 2 * jsp87Level k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [jsp87BitTerm]
        push_cast
        ring
    _ = ((∑ k ∈ Finset.range M, (k ^ 2 * jsp87Level k n : ℕ) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [cast_sum_sqWeight, Finset.sum_mul]

theorem jsp87SqWeightColumn_nonneg (M n : ℕ) : 0 ≤ jsp87SqWeightColumn M n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE LARGEST SUMMAND**: `m² ≤ jsp87_sq m`. -/
theorem jsp87_pow_le_sq (m : ℕ) : m ^ 2 ≤ jsp87_sq m := by
  induction m with
  | zero => rw [jsp87_sq_zero]; norm_num
  | succ m ih =>
    have hrec := jsp87_sq_succ m
    have hz : 0 ≤ jsp87_sq m := Nat.zero_le _
    omega

theorem jsp87SqWeightColumn_le_sqTerm (M n : ℕ) :
    jsp87SqWeightColumn M n ≤ jsp87SqTerm n := by
  unfold jsp87SqWeightColumn
  rw [cast_sum_sqWeight, jsp87_sqWeightCount_cast, jsp87SqTerm]
  rcases Nat.lt_or_ge (omega n) M with hM | hM
  · rw [ite_eq_left hM]
  · rw [ite_eq_right (Nat.not_lt.mpr hM)]
    simp only [Nat.cast_zero, zero_mul]
    positivity

/-- **THE SQUARE-WEIGHTED SATURATION POINT.**  Below `n = 2^M` the square-weighted
column *is* the `n`-th term of the square moment `jsp87SqTerm n = ω n² · 2^-(n+1)`. -/
theorem jsp87SqWeightColumn_eq_sqTerm {M n : ℕ} (hM : 1 ≤ M) (hn : n < 2 ^ M) :
    jsp87SqWeightColumn M n = jsp87SqTerm n := by
  have hωlt : omega n < M := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, omega_zero]
      have : 0 < M := hM
      omega
    · exact omega_lt_of_lt_two_pow hn0 hn
  unfold jsp87SqWeightColumn
  rw [cast_sum_sqWeight, jsp87_sqWeightCount_cast, ite_eq_left hωlt, jsp87SqTerm]

theorem summable_jsp87SqWeightColumn (M : ℕ) : Summable (jsp87SqWeightColumn M) :=
  Summable.of_nonneg_of_le (fun n => jsp87SqWeightColumn_nonneg M n)
    (fun n => jsp87SqWeightColumn_le_sqTerm M n) summable_jsp87SqTerm

/-- **THE SQUARE-WEIGHTED ROW PARTIAL SUM** `∑_{k<M} k² L k`. -/
noncomputable def jsp87SqWeightPartial (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87LevelSeries k)

/-- **THE FINITE SQUARE-WEIGHTED INTERCHANGE.** -/
theorem jsp87_sqWeightPartial_eq_tsum (M : ℕ) :
    (∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87LevelSeries k))
      = ∑' (n : ℕ), jsp87SqWeightColumn M n := by
  have hfin : (∑' (n : ℕ),
        ∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑ k ∈ Finset.range M,
        ∑' (n : ℕ), ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n) := by
    refine Summable.tsum_finsetSum fun i _ => ?_
    exact (summable_jsp87BitTerm (fun m => jsp87Level i m)
      (fun m => jsp87Level_le i m)).mul_left ((i : ℝ) ^ 2)
  have hrhs : (∑ k ∈ Finset.range M,
        ∑' (n : ℕ), ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87LevelSeries k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold jsp87LevelSeries jsp87BinarySeries
    exact Summable.tsum_mul_left ((k : ℝ) ^ 2) (summable_jsp87BitTerm
      (fun m => jsp87Level k m) (fun m => jsp87Level_le k m))
  have hlhs : (∑' (n : ℕ),
        ∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑' (n : ℕ), jsp87SqWeightColumn M n := by
    refine tsum_congr fun n => ?_
    exact jsp87_sqWeightedLevel_sum_eq M n
  calc (∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87LevelSeries k))
      = ∑ k ∈ Finset.range M,
          ∑' (n : ℕ), ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n) := hrhs.symm
    _ = ∑' (n : ℕ),
          ∑ k ∈ Finset.range M, ((k : ℝ) ^ 2 * jsp87BitTerm (fun m => jsp87Level k m) n) :=
        hfin.symm
    _ = ∑' (n : ℕ), jsp87SqWeightColumn M n := hlhs

theorem jsp87_sqWeightPartial_le_cubeSeries (M : ℕ) :
    jsp87SqWeightPartial M ≤ jsp87SquareSeries := by
  have h' := Summable.tsum_le_tsum (fun n => jsp87SqWeightColumn_le_sqTerm M n)
    (summable_jsp87SqWeightColumn M) summable_jsp87SqTerm
  exact (jsp87_sqWeightPartial_eq_tsum M).trans_le h'

theorem jsp87_colPartial_le_sqWeightPartial {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (2 ^ M), ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      ≤ jsp87SqWeightPartial M := by
  have hmin : ∀ n ∈ Finset.range (2 ^ M), jsp87SqWeightColumn M n
      = ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
    fun n hn => jsp87SqWeightColumn_eq_sqTerm hM (Finset.mem_range.mp hn)
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ M))
    (fun i _ => jsp87SqWeightColumn_nonneg M i) (summable_jsp87SqWeightColumn M)
  calc (∑ n ∈ Finset.range (2 ^ M), ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑ n ∈ Finset.range (2 ^ M), jsp87SqWeightColumn M n :=
        (Finset.sum_congr rfl hmin).symm
    _ ≤ ∑' (n : ℕ), jsp87SqWeightColumn M n := hsum
    _ = jsp87SqWeightPartial M := (jsp87_sqWeightPartial_eq_tsum M).symm

theorem jsp87_sqWeightGap_nonneg (M : ℕ) : 0 ≤ jsp87SquareSeries - jsp87SqWeightPartial M := by
  have h := jsp87_sqWeightPartial_le_cubeSeries M
  linarith

theorem jsp87_sqWeightGap_le_tail {M : ℕ} (hM : 1 ≤ M) :
    jsp87SquareSeries - jsp87SqWeightPartial M
      ≤ jsp87SquareSeries - ∑ n ∈ Finset.range (2 ^ M),
          ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hle := jsp87_colPartial_le_sqWeightPartial hM
  linarith

/-- **THE CUBE TAIL IS THE SHIFTED CUBE MOMENT.** -/
theorem jsp87SqSeries_sub_colPartial (N : ℕ) :
    jsp87SquareSeries - (∑ n ∈ Finset.range N, jsp87SqTerm n)
      = ∑' (k : ℕ), jsp87SqTerm (N + k) := by
  have h := summable_jsp87SqTerm.sum_add_tsum_nat_add N
  have h2 : (∑' (i : ℕ), jsp87SqTerm (i + N)) = ∑' (k : ℕ), jsp87SqTerm (N + k) :=
    tsum_congr fun i => by rw [Nat.add_comm]
  unfold jsp87SquareSeries
  linarith

/-- `2^(N+k+1) = 2^(N+1) · 2^k`, so the geometric weight splits. -/
private theorem two_pow_add_inv (N k : ℕ) :
    ((2 : ℝ) ^ (N + k + 1))⁻¹ = ((2 : ℝ) ^ (N + 1))⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
  rw [show N + k + 1 = (N + 1) + k by omega, pow_add, mul_inv_rev, mul_comm]

/-- **THE CUBE-MOMENT TAIL IS DOMINATED BY THE SHIFTED GEOMETRIC MAJORANT.** -/
theorem jsp87_sqTerm_le_scaled (N k : ℕ) :
    jsp87SqTerm (N + k)
      ≤ ((N + 1) ^ 2 : ℝ) * ((2 : ℝ) ^ (N + 1))⁻¹
        * (((k + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  have h1 : omega (N + k) ≤ N + k + 1 := by
    have := omega_le_self (N + k)
    omega
  have h2 : N + k + 1 ≤ (N + 1) * (k + 1) := by nlinarith
  have h3 : (omega (N + k)) ^ 2 ≤ (N + k + 1) ^ 2 := Nat.pow_le_pow_left h1 2
  have h4 : (N + k + 1) ^ 2 ≤ ((N + 1) * (k + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
  have h5 : ((N + 1) * (k + 1)) ^ 2 = (N + 1) ^ 2 * (k + 1) ^ 2 := by
    rw [mul_pow]
  have h6 : ((omega (N + k)) ^ 2 : ℝ) ≤ (((N + 1) ^ 2 * (k + 1) ^ 2 : ℕ) : ℝ) := by
    have := Nat.le_trans h3 h4
    rw [h5] at this
    exact_mod_cast this
  calc jsp87SqTerm (N + k)
      ≤ ((omega (N + k)) ^ 2 : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹ := by
        unfold jsp87SqTerm
        rw [Nat.cast_pow]
    _ ≤ (((N + 1) ^ 2 * (k + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = ((N + 1) ^ 2 : ℝ) * ((2 : ℝ) ^ (N + 1))⁻¹
        * (((k + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
        push_cast
        rw [two_pow_add_inv]
        ring

/-- The shifted square majorant `∑ k, (k + 1)² (1/2)ᵏ`, exactly. -/
private theorem summable_sq_shift_half :
    Summable (fun k : ℕ => (((k + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k) := by
  refine (summable_pow_pow_half_succ 2).mul_left 2 |>.congr fun k => ?_
  rw [two_mul_middle]

private theorem tsum_sq_shift_half :
    (∑' (j : ℕ), (((j + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ j) = 12 := by
  have h2 : (∑' (j : ℕ), (((j + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (j + 1)) = 6 := by
    calc (∑' (j : ℕ), (((j + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (j + 1))
      = ∑' (l : ℕ), ((l + 1 : ℕ) : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (l + 1) := by
          refine tsum_congr fun j => ?_
          rw [Nat.cast_pow]
      _ = 6 := (tsum_shift_one (summable_pow_pow_half 2)).trans (by
          rw [tsum_square_pow_half]
          norm_num)
  calc (∑' (j : ℕ), (((j + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ j)
      = 2 * ∑' (j : ℕ), (((j + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (j + 1) := by
        refine (tsum_congr fun j => ?_).trans
          (Summable.tsum_mul_left 2 (summable_pow_pow_half_succ 2))
        rw [pow_succ]
        ring
    _ = 2 * 6 := by rw [h2]
    _ = 12 := by ring

/-- **THE SQUARE-MOMENT TAIL IS ITS OWN SHIFT**: `jsp87SquareSeries − ∑_{n<N}`
tends to `0`. -/
theorem tendsto_sq_colPartial_tail :
    Tendsto (fun N => jsp87SquareSeries - ∑ n ∈ Finset.range N, jsp87SqTerm n) atTop (nhds 0) := by
  have h1 : Tendsto (fun _ : ℕ => jsp87SquareSeries) atTop (nhds jsp87SquareSeries) :=
    tendsto_const_nhds
  have htri : Tendsto (fun N => ∑ n ∈ Finset.range N, jsp87SqTerm n)
      atTop (nhds jsp87SquareSeries) := summable_jsp87SqTerm.hasSum.tendsto_sum_nat
  simpa only [sub_self] using h1.sub htri

/-- The gaps tend to `0`, hence the partial sums tend to the cube moment. -/
theorem tendsto_jsp87_sqWeightGap :
    Tendsto (fun M => jsp87SquareSeries - jsp87SqWeightPartial M) atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_sq_colPartial_tail ε hε
  refine ⟨N + 1, ?_⟩
  intro M hM
  have hMN : N ≤ M := by omega
  have hlt := jsp87_sqWeightGap_le_tail (show 1 ≤ M by omega)
  have hg0 := jsp87_sqWeightGap_nonneg M
  have hcol : (∑ n ∈ Finset.range M, jsp87SqTerm n)
      ≤ ∑ n ∈ Finset.range (2 ^ M), jsp87SqTerm n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (Nat.lt_trans (n := x) (m := M) (k := 2 ^ M) (Finset.mem_range.mp hx)
          (Nat.lt_two_pow_self (n := M))))
      (fun i _ _ => jsp87SqTerm_nonneg i)
  have ht0 : 0 ≤ jsp87SquareSeries - ∑ n ∈ Finset.range M, jsp87SqTerm n := by
    have h := Summable.sum_le_tsum (Finset.range M)
      (fun i _ => jsp87SqTerm_nonneg i) summable_jsp87SqTerm
    unfold jsp87SquareSeries
    linarith
  have hdist := hN _ hMN
  rw [dist_zero_eq, abs_of_nonneg ht0] at hdist
  rw [dist_zero_eq, abs_of_nonneg hg0]
  calc jsp87SquareSeries - jsp87SqWeightPartial M
      ≤ jsp87SquareSeries - ∑ n ∈ Finset.range (2 ^ M),
          ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := hlt
    _ ≤ jsp87SquareSeries - ∑ n ∈ Finset.range M, jsp87SqTerm n := by
        simpa only [jsp87SqTerm] using sub_le_sub_left hcol (jsp87SquareSeries)
    _ < ε := hdist

theorem tendsto_jsp87_sqWeightPartial :
    Tendsto jsp87SqWeightPartial atTop (nhds jsp87SquareSeries) := by
  have h3 : Tendsto (fun M : ℕ => jsp87SquareSeries
        - (jsp87SquareSeries - jsp87SqWeightPartial M)) atTop (nhds jsp87SquareSeries) := by
    simpa only [sub_zero] using tendsto_jsp87_sqWeightGap.const_sub (jsp87SquareSeries)
  refine h3.congr' (f₂ := jsp87SqWeightPartial) (Filter.Eventually.of_forall fun M => ?_)
  unfold jsp87SqWeightPartial
  ring

/-- The square moment, as a `HasSum` of the square-weighted levels. -/
theorem hasSum_sqWeightedLevels :
    HasSum (fun k : ℕ => ((k : ℝ) ^ 2 * jsp87LevelSeries k)) jsp87SquareSeries := by
  refine (hasSum_iff_tendsto_nat_of_nonneg
    (f := fun k : ℕ => ((k : ℝ) ^ 2 * jsp87LevelSeries k))
    (fun k => mul_nonneg (sq_nonneg _) (jsp87LevelSeries_nonneg k)) _).2 ?_
  exact tendsto_jsp87_sqWeightPartial

/-- **THE SQUARE-WEIGHTED LEVEL FAMILY IS SUMMABLE.** -/
theorem summable_sqWeightedLevels :
    Summable (fun k : ℕ => ((k : ℝ) ^ 2 * jsp87LevelSeries k)) :=
  ⟨jsp87SquareSeries, hasSum_sqWeightedLevels⟩

/-- **THE SQUARE-WEIGHTED LEVEL REFLECTION.**

```
jsp87SquareSeries = ∑' k, k² · L k
```

Weighting the *level* layers by the square of their index reproduces `ω n²` at
every cut point `n` (only the level `k = ω n` contributes), so the square moment
has a **third** decomposition, besides round 107's two:

```
S^(2) = ∑' k, k   L k                 (round 106, the first moment)
S^(2) = (∑' k, 2k · A k) − S          (round 107)
S^(2) = ∑' k, k²  · L k               (this round)
```

and the level/at-least sides are related by `L k = A k − A (k+1)`, which gives
`jsp87SquareSeries = ∑' k, k² A k − ∑' k, k² A (k+1)`. -/
theorem jsp87SquareSeries_eq_tsum_sqWeightedLevels :
    jsp87SquareSeries = ∑' (k : ℕ), ((k : ℝ) ^ 2 * jsp87LevelSeries k) :=
  hasSum_sqWeightedLevels.tsum_eq.symm

/-- **EVERY SQUARE-WEIGHTED LEVEL IS IRRATIONAL** (from height `1` up). -/
theorem jsp87_sqWeightedLevel_irrational {k : ℕ} (hk : 1 ≤ k) :
    Irrational (((k ^ 2 : ℕ) : ℝ) * jsp87LevelSeries k) :=
  (jsp87LevelSeries_irrational k hk).natCast_mul (m := k ^ 2)
    (by rw [pow_two]; exact Nat.mul_ne_zero (Nat.ne_of_gt hk) (Nat.ne_of_gt hk))

/-! ## 4. The cumulative-square ladder: the weight `k²` against the "at least" family -/

/-- **THE SQUARE-WEIGHTED CUMULATIVE COUNT, IN THE SATURATED RANGE.**  If all the
layers of `ω n` are present, the square-weighted cumulative count is the square sum
`jsp87_sq (ω n) = 1² + 2² + … + ω n²`. -/
theorem jsp87_sqCumCount_sat {M n : ℕ} (h : omega n + 1 ≤ M) :
    (∑ k ∈ Finset.range M, k ^ 2 * jsp87AtLeast k n) = jsp87_sq (omega n) := by
  have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
    intro a ha
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) h)
  have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range (omega n + 1) →
      k ^ 2 * jsp87AtLeast k n = 0 := by
    intro k _ hna
    have hk : omega n + 1 ≤ k := by
      rcases Nat.lt_or_ge k (omega n + 1) with hlt | hge
      · exact absurd hlt (fun hh => hna (Finset.mem_range.mpr hh))
      · exact hge
    have hne : omega n < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self (omega n)) hk
    have h1 : jsp87AtLeast k n = 0 := (jsp87AtLeast_eq_zero_iff k n).2 hne
    rw [h1]
    norm_num
  have hswap := Finset.sum_subset hsub hzero
  have hone : (∑ k ∈ Finset.range (omega n + 1), k ^ 2 * jsp87AtLeast k n)
      = ∑ k ∈ Finset.range (omega n + 1), k ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hle : k ≤ omega n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [(jsp87AtLeast_eq_one_iff k n).2 hle, mul_one]
  rw [← hswap, hone]
  rfl

/-- **THE SQUARE-WEIGHTED CUMULATIVE COUNT, IN THE UNSATURATED RANGE.** -/
theorem jsp87_sqCumCount_unsat {M n : ℕ} (h : M ≤ omega n) :
    (∑ k ∈ Finset.range M, k ^ 2 * jsp87AtLeast k n) = ∑ k ∈ Finset.range M, k ^ 2 := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hle : k ≤ omega n := Nat.le_of_lt (hk'.trans_le h)
  have h1 : jsp87AtLeast k n = 1 := (jsp87AtLeast_eq_one_iff k n).2 hle
  rw [h1]
  norm_num

/-- **THE SQUARE SUM DOMINATES THE SQUARE-WEIGHTED CUMULATIVE COUNT.** -/
theorem jsp87_sqCumCount_le (M n : ℕ) :
    (∑ k ∈ Finset.range M, k ^ 2 * jsp87AtLeast k n) ≤ jsp87_sq (omega n) := by
  rcases Nat.lt_or_ge (omega n + 1) M with h | h
  · rw [jsp87_sqCumCount_sat
      (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self (omega n)) h))]
  · have hsub : Finset.range M ⊆ Finset.range (omega n + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) h)
    calc (∑ k ∈ Finset.range M, k ^ 2 * jsp87AtLeast k n)
        = ∑ k ∈ Finset.range M, k ^ 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hle : k ≤ omega n :=
            Nat.lt_succ_iff.mp (show k < omega n + 1 from
              Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) (show M ≤ omega n + 1 from h))
          rw [(jsp87AtLeast_eq_one_iff k n).2 hle, mul_one]
      _ ≤ ∑ k ∈ Finset.range (omega n + 1), k ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => Nat.zero_le (k ^ 2)
      _ = jsp87_sq (omega n) := rfl

/-- The same, in `ℝ`. -/
theorem jsp87_sqCumCount_cast (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k ^ 2 * jsp87AtLeast k n : ℕ) : ℝ))
      ≤ ((jsp87_sq (omega n) : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]
  exact_mod_cast jsp87_sqCumCount_le M n

/-- **THE SQUARE-WEIGHTED COLUMN AT `n`, "at least" side.** -/
noncomputable def jsp87CumSqColumn (M n : ℕ) : ℝ :=
  ((∑ k ∈ Finset.range M, k ^ 2 * jsp87AtLeast k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

private theorem cast_sum_cumSq (M n : ℕ) :
    ((∑ k ∈ Finset.range M, k ^ 2 * jsp87AtLeast k n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range M, ((k ^ 2 * jsp87AtLeast k n : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]

/-- The `M` square-weighted layers of the "at least" family, at the cut point `n`. -/
theorem jsp87_sqWeightedCum_sum_eq (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n)
      = jsp87CumSqColumn M n := by
  unfold jsp87CumSqColumn
  calc (∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n)
      = ∑ k ∈ Finset.range M,
          (((k ^ 2 * jsp87AtLeast k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [jsp87BitTerm]
        push_cast
        ring
    _ = ((∑ k ∈ Finset.range M, (k ^ 2 * jsp87AtLeast k n : ℕ) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [cast_sum_cumSq, Finset.sum_mul]

theorem jsp87CumSqColumn_nonneg (M n : ℕ) : 0 ≤ jsp87CumSqColumn M n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE CUMULATIVE SQUARE-SUM TERM.** -/
noncomputable def jsp87Sq2Term (n : ℕ) : ℝ :=
  ((jsp87_sq (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

theorem jsp87Sq2Term_nonneg (n : ℕ) : 0 ≤ jsp87Sq2Term n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE SQUARE-WEIGHTED COLUMN IS AT MOST THE SQUARE-SUM TERM.** -/
theorem jsp87CumSqColumn_le_sq2Term (M n : ℕ) :
    jsp87CumSqColumn M n ≤ jsp87Sq2Term n := by
  unfold jsp87CumSqColumn jsp87Sq2Term
  rw [cast_sum_cumSq]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast jsp87_sqCumCount_cast M n) (by positivity)

/-- **THE SQUARE-WEIGHTED SATURATION POINT (AT-LEAST SIDE).** -/
theorem jsp87CumSqColumn_eq_sq2Term {M n : ℕ} (hM : 1 ≤ M) (hn : n < 2 ^ M) :
    jsp87CumSqColumn M n = jsp87Sq2Term n := by
  have hωlt : omega n + 1 ≤ M := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, omega_zero]
      have : 0 < M := hM
      omega
    · exact Nat.succ_le_iff.mpr (omega_lt_of_lt_two_pow hn0 hn)
  unfold jsp87CumSqColumn jsp87Sq2Term
  rw [cast_sum_cumSq, ← Nat.cast_sum, jsp87_sqCumCount_sat hωlt]

/-- **THE CUMULATIVE SQUARE-SUM MOMENT** `jsp87CumSqSeries = ∑' n, (1² + … + ω n²) 2^-(n+1)`. -/
noncomputable def jsp87CumSqSeries : ℝ := ∑' (n : ℕ), jsp87Sq2Term n

/-- **THE CUMULATIVE SQUARE-SUM MOMENT CONVERGES.** -/
theorem summable_jsp87Sq2Term : Summable jsp87Sq2Term :=
  Summable.of_nonneg_of_le (fun n => jsp87Sq2Term_nonneg n)
    (fun n => mul_le_mul_of_nonneg_right (by
      have h1 := jsp87_sq_le_succ_cube (omega n)
      have h2 : omega n + 1 ≤ n + 1 := Nat.add_le_add_right (omega_le_self n) 1
      have h3 : ((omega n + 1) ^ 3 : ℕ) ≤ ((n + 1) ^ 3 : ℕ) := Nat.pow_le_pow_left h2 3
      exact_mod_cast Nat.le_trans h1 h3) (by positivity))
    summable_cube_majorant

/-- **THE SQUARE-WEIGHTED ROW PARTIAL SUM** `∑_{k<M} k² A k`. -/
noncomputable def jsp87CumSqPartial (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k

/-- **THE FINITE SQUARE-WEIGHTED INTERCHANGE (AT-LEAST SIDE).** -/
theorem jsp87_cumSqPartial_eq_tsum (M : ℕ) :
    (∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k)
      = ∑' (n : ℕ), jsp87CumSqColumn M n := by
  have hfin : (∑' (n : ℕ),
        ∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n)
      = ∑ k ∈ Finset.range M,
        ∑' (n : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n := by
    refine Summable.tsum_finsetSum fun i _ => ?_
    exact (summable_jsp87BitTerm (fun m => jsp87AtLeast i m)
      (fun m => jsp87AtLeast_le i m)).mul_left ((i ^ 2 : ℕ) : ℝ)
  have hrhs : (∑ k ∈ Finset.range M,
        ∑' (n : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n)
      = ∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold jsp87AtLeastSeries jsp87BinarySeries
    exact Summable.tsum_mul_left ((k ^ 2 : ℕ) : ℝ) (summable_jsp87AtLeast k)
  have hlhs : (∑' (n : ℕ),
        ∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n)
      = ∑' (n : ℕ), jsp87CumSqColumn M n := by
    refine tsum_congr fun n => ?_
    exact jsp87_sqWeightedCum_sum_eq M n
  calc (∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k)
      = ∑ k ∈ Finset.range M,
          ∑' (n : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n := hrhs.symm
    _ = ∑' (n : ℕ),
          ∑ k ∈ Finset.range M, ((k ^ 2 : ℕ) : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n :=
        hfin.symm
    _ = ∑' (n : ℕ), jsp87CumSqColumn M n := hlhs

theorem summable_jsp87CumSqColumn (M : ℕ) : Summable (jsp87CumSqColumn M) :=
  Summable.of_nonneg_of_le (fun n => jsp87CumSqColumn_nonneg M n)
    (fun n => jsp87CumSqColumn_le_sq2Term M n) summable_jsp87Sq2Term

/-- **THE SQUARE-WEIGHTED ROWS NEVER OVERSHOOT THE CUMULATIVE SQUARE MOMENT.** -/
theorem jsp87_cumSqPartial_le_cumSqSeries (M : ℕ) :
    jsp87CumSqPartial M ≤ jsp87CumSqSeries := by
  have h' := Summable.tsum_le_tsum (fun n => jsp87CumSqColumn_le_sq2Term M n)
    (summable_jsp87CumSqColumn M) summable_jsp87Sq2Term
  exact (jsp87_cumSqPartial_eq_tsum M).trans_le h'

/-- **THE SQUARE-WEIGHTED ROWS DOMINATE THE COLUMNS BELOW `n = 2^M`.** -/
theorem jsp87_colSqPartial_le_cumSqPartial {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (2 ^ M), ((jsp87_sq (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      ≤ jsp87CumSqPartial M := by
  have hmin : ∀ n ∈ Finset.range (2 ^ M), jsp87CumSqColumn M n
      = ((jsp87_sq (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
    fun n hn => jsp87CumSqColumn_eq_sq2Term hM (Finset.mem_range.mp hn)
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ M))
    (fun i _ => jsp87CumSqColumn_nonneg M i) (summable_jsp87CumSqColumn M)
  calc (∑ n ∈ Finset.range (2 ^ M), ((jsp87_sq (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑ n ∈ Finset.range (2 ^ M), jsp87CumSqColumn M n :=
        (Finset.sum_congr rfl hmin).symm
    _ ≤ ∑' (n : ℕ), jsp87CumSqColumn M n := hsum
    _ = jsp87CumSqPartial M := (jsp87_cumSqPartial_eq_tsum M).symm

theorem jsp87_cumSqGap_nonneg (M : ℕ) : 0 ≤ jsp87CumSqSeries - jsp87CumSqPartial M := by
  have h := jsp87_cumSqPartial_le_cumSqSeries M
  linarith

theorem jsp87_cumSqGap_le_tail {M : ℕ} (hM : 1 ≤ M) :
    jsp87CumSqSeries - jsp87CumSqPartial M
      ≤ jsp87CumSqSeries - ∑ n ∈ Finset.range (2 ^ M),
          ((jsp87_sq (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hle := jsp87_colSqPartial_le_cumSqPartial hM
  linarith

/-- **THE CUMULATIVE-SQUARE TAIL IS THE SHIFTED MOMENT.** -/
theorem jsp87CumSqSeries_sub_colPartial (N : ℕ) :
    jsp87CumSqSeries - (∑ n ∈ Finset.range N, jsp87Sq2Term n)
      = ∑' (k : ℕ), jsp87Sq2Term (N + k) := by
  have h := summable_jsp87Sq2Term.sum_add_tsum_nat_add N
  have h2 : (∑' (i : ℕ), jsp87Sq2Term (i + N)) = ∑' (k : ℕ), jsp87Sq2Term (N + k) :=
    tsum_congr fun i => by rw [Nat.add_comm]
  unfold jsp87CumSqSeries
  linarith

theorem tendsto_cumSq_colPartial_tail :
    Tendsto (fun N => jsp87CumSqSeries - ∑ n ∈ Finset.range N, jsp87Sq2Term n) atTop (nhds 0) := by
  have h1 : Tendsto (fun _ : ℕ => jsp87CumSqSeries) atTop (nhds jsp87CumSqSeries) :=
    tendsto_const_nhds
  have htri : Tendsto (fun N => ∑ n ∈ Finset.range N, jsp87Sq2Term n)
      atTop (nhds jsp87CumSqSeries) := summable_jsp87Sq2Term.hasSum.tendsto_sum_nat
  simpa only [sub_self] using h1.sub htri

theorem tendsto_jsp87_cumSqGap :
    Tendsto (fun M => jsp87CumSqSeries - jsp87CumSqPartial M) atTop (nhds 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_cumSq_colPartial_tail ε hε
  refine ⟨N + 1, ?_⟩
  intro M hM
  have hMN : N ≤ M := by omega
  have hlt := jsp87_cumSqGap_le_tail (show 1 ≤ M by omega)
  have hg0 := jsp87_cumSqGap_nonneg M
  have hcol : (∑ n ∈ Finset.range M, jsp87Sq2Term n)
      ≤ ∑ n ∈ Finset.range (2 ^ M), jsp87Sq2Term n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (Nat.lt_trans (n := x) (m := M) (k := 2 ^ M) (Finset.mem_range.mp hx)
          (Nat.lt_two_pow_self (n := M))))
      (fun i _ _ => jsp87Sq2Term_nonneg i)
  have ht0 : 0 ≤ jsp87CumSqSeries - ∑ n ∈ Finset.range M, jsp87Sq2Term n := by
    have h := Summable.sum_le_tsum (Finset.range M)
      (fun i _ => jsp87Sq2Term_nonneg i) summable_jsp87Sq2Term
    unfold jsp87CumSqSeries
    linarith
  have hdist := hN _ hMN
  rw [dist_zero_eq, abs_of_nonneg ht0] at hdist
  rw [dist_zero_eq, abs_of_nonneg hg0]
  calc jsp87CumSqSeries - jsp87CumSqPartial M
      ≤ jsp87CumSqSeries - ∑ n ∈ Finset.range (2 ^ M), jsp87Sq2Term n := hlt
    _ ≤ jsp87CumSqSeries - ∑ n ∈ Finset.range M, jsp87Sq2Term n :=
        sub_le_sub_left hcol (jsp87CumSqSeries)
    _ < ε := hdist

theorem tendsto_jsp87_cumSqPartial :
    Tendsto jsp87CumSqPartial atTop (nhds jsp87CumSqSeries) := by
  have h3 : Tendsto (fun M : ℕ => jsp87CumSqSeries
        - (jsp87CumSqSeries - jsp87CumSqPartial M)) atTop (nhds jsp87CumSqSeries) := by
    simpa only [sub_zero] using tendsto_jsp87_cumSqGap.const_sub (jsp87CumSqSeries)
  refine h3.congr' (f₂ := jsp87CumSqPartial) (Filter.Eventually.of_forall fun M => ?_)
  unfold jsp87CumSqPartial
  ring

/-- The cumulative square moment, as a `HasSum` of the square-weighted "at least" levels. -/
theorem hasSum_weightedSqAtLeast :
    HasSum (fun k : ℕ => ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k) jsp87CumSqSeries := by
  refine (hasSum_iff_tendsto_nat_of_nonneg
    (f := fun k : ℕ => ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k)
    (fun k => mul_nonneg (Nat.cast_nonneg _) (jsp87AtLeastSeries_nonneg k)) _).2 ?_
  exact tendsto_jsp87_cumSqPartial

/-- **THE SQUARE-WEIGHTED "AT LEAST" FAMILY IS SUMMABLE.** -/
theorem summable_weightedSqAtLeast :
    Summable (fun k : ℕ => ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k) :=
  ⟨jsp87CumSqSeries, hasSum_weightedSqAtLeast⟩

/-- **THE THIRD REFLECTION (AT-LEAST SIDE) — THE HEADLINE OF THIS ROUND.**

```
jsp87CumSqSeries = ∑' k, k² · A k
```

Weighting the *"at least"* layers by the square of their index reproduces the
**truncated square sum** `1² + 2² + … + ω n²` at each cut point `n`, and the
columns saturate at the same cut point `n = 2^M` as rounds 106 and 107.  With
round 106 (`S = ∑' k, k L k`), round 107 (`S^(2) = ∑' k, k A k`) and §3 of this
file (`S^(2) = ∑' k, k² L k`), this completes the square-weight ladder. -/
theorem jsp87CumSqSeries_eq_tsum_weightedSqAtLeast :
    jsp87CumSqSeries = ∑' (k : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k :=
  hasSum_weightedSqAtLeast.tsum_eq.symm

/-- **EVERY SQUARE-WEIGHTED "AT LEAST" LEVEL IS IRRATIONAL** (from height `2` up). -/
theorem jsp87_weightedSqAtLeast_irrational {k : ℕ} (hk : 2 ≤ k) :
    Irrational (((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k) :=
  (jsp87AtLeastSeries_irrational k hk).natCast_mul (m := k ^ 2)
    (by rw [pow_two]; exact Nat.mul_ne_zero (Nat.ne_of_gt (by omega)) (Nat.ne_of_gt (by omega)))

/-- **THE SQUARE-WEIGHTED ROWS ARE DOMINATED BY `k² 2^-k`.** -/
theorem jsp87_weightedSqAtLeast_le_two_pow (k : ℕ) :
    ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k ≤ ((k ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0]
    simp [jsp87AtLeastSeries_zero]
  · have h1 : jsp87AtLeastSeries k ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have hP : 0 < (2 : ℝ) ^ k := by positivity
      have h2 : jsp87AtLeastSeries k ≤ (1 : ℝ) / (2 : ℝ) ^ k := by
        apply (le_div_iff₀ hP).2
        simpa only [mul_comm] using jsp87AtLeastSeries_mul_two_pow k (Nat.succ_le_of_lt hk0)
      rwa [div_eq_mul_inv, one_mul] at h2
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)

private theorem tsum_sq_two_pow :
    (∑' (k : ℕ), ((k ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹) = 6 := by
  calc (∑' (k : ℕ), ((k ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹)
      = ∑' (k : ℕ), (k : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ k := by
        refine tsum_congr fun k => ?_
        rw [Nat.cast_pow, inv_pow]
    _ = 6 := tsum_square_pow_half

/-- **THE CUMULATIVE SQUARE MOMENT IS AT MOST `6`** — the sharp analogue of round
107's `jsp87TriSeries_le_two`. -/
theorem jsp87CumSqSeries_le_six : jsp87CumSqSeries ≤ 6 := by
  have hconv : Summable (fun k : ℕ => ((k ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹) := by
    refine (summable_pow_pow_half 2).congr fun k => ?_
    rw [Nat.cast_pow, inv_pow]
  have h' := Summable.tsum_le_tsum (fun k => jsp87_weightedSqAtLeast_le_two_pow k)
    summable_weightedSqAtLeast hconv
  rw [jsp87CumSqSeries_eq_tsum_weightedSqAtLeast]
  rw [tsum_sq_two_pow] at h'
  exact h'

/-- **A CLOSED-FORM LOWER BOUND FOR THE CUMULATIVE SQUARE MOMENT**: the eight places
`n < 8` already contribute `71/256`. -/
theorem jsp87CumSqSeries_ge_seventyOne : (71 / 256 : ℝ) ≤ jsp87CumSqSeries := by
  have hsum := Summable.sum_le_tsum (Finset.range 8) (fun i _ => jsp87Sq2Term_nonneg i)
    summable_jsp87Sq2Term
  have hval : (∑ i ∈ Finset.range 8, jsp87Sq2Term i) = 71 / 256 := by
    have h0 : omega 0 = 0 := omega_zero
    have h1 : omega 1 = 0 := omega_one
    have h2 : omega 2 = 1 := by native_decide
    have h3 : omega 3 = 1 := by native_decide
    have h4 : omega 4 = 1 := by native_decide
    have h5 : omega 5 = 1 := by native_decide
    have h6 : omega 6 = 2 := by native_decide
    have h7 : omega 7 = 1 := by native_decide
    simp only [Finset.sum_range_succ_comm]
    norm_num [jsp87Sq2Term, jsp87_sq, h0, h1, h2, h3, h4, h5, h6, h7]
  rwa [hval] at hsum

theorem jsp87CumSqSeries_pos : 0 < jsp87CumSqSeries := by
  linarith [jsp87CumSqSeries_ge_seventyOne, show (0 : ℝ) < 71 / 256 by norm_num]

/-! ## 5. Faulhaber in the moment: the four moments are linearly dependent -/

/-- **FAULHABER AT THE CUT POINT `n`.**  Six times the truncated square sum is
`2 ω n³ + 3 ω n² + ω n` — the only new content of the Faulhaber step. -/
theorem jsp87Sq2Term_mul_six (n : ℕ) :
    6 * jsp87Sq2Term n = 2 * jsp87CubeTerm n + 3 * jsp87SqTerm n + jsp87Term n := by
  have hpoly : omega n * (omega n + 1) * (2 * omega n + 1)
      = 2 * omega n ^ 3 + 3 * omega n ^ 2 + omega n := by
    ring
  have h := jsp87_sq_mul_six (omega n)
  have hcast : ((omega n * (omega n + 1) * (2 * omega n + 1) : ℕ) : ℝ)
      = 2 * ((omega n ^ 3 : ℕ) : ℝ) + 3 * ((omega n ^ 2 : ℕ) : ℝ) + ((omega n : ℕ) : ℝ) := by
    rw [hpoly]
    push_cast
    ring
  have h' : 6 * jsp87_sq (omega n) = 2 * omega n ^ 3 + 3 * omega n ^ 2 + omega n := by
    rw [h, hpoly]
  have hmain : 6 * ((jsp87_sq (omega n) : ℕ) : ℝ)
      = 2 * ((omega n ^ 3 : ℕ) : ℝ) + 3 * ((omega n ^ 2 : ℕ) : ℝ) + ((omega n : ℕ) : ℝ) := by
    exact_mod_cast h'
  unfold jsp87Sq2Term jsp87CubeTerm jsp87SqTerm jsp87Term
  calc 6 * (((jsp87_sq (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (6 * ((jsp87_sq (omega n) : ℕ) : ℝ)) * ((2 : ℝ) ^ (n + 1))⁻¹ := by ring
    _ = (2 * ((omega n ^ 3 : ℕ) : ℝ) + 3 * ((omega n ^ 2 : ℕ) : ℝ) + ((omega n : ℕ) : ℝ))
        * ((2 : ℝ) ^ (n + 1))⁻¹ := by rw [hmain]
    _ = 2 * (((omega n ^ 3 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
        + 3 * (((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
        + (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by ring

/-- **THE FOUR MOMENTS ARE LINEARLY DEPENDENT — THE HEADLINE OF §5.**

```
6 · jsp87CumSqSeries = 2 · jsp87CubeSeries + 3 · jsp87SquareSeries + jsp87Series
```

So the square-weight ladder contributes exactly **one** new real number
(`jsp87CumSqSeries`), and it is a rational linear combination of the first and
third moments: the truncated square sum `1² + … + ω n²` is `(2ω³ + 3ω² + ω)/6`. -/
theorem jsp87CumSqSeries_six_eq :
    6 * jsp87CumSqSeries = 2 * jsp87CubeSeries + 3 * jsp87SquareSeries + jsp87Series := by
  have hs1 : Summable (fun n : ℕ => 2 * jsp87CubeTerm n) :=
    (summable_jsp87CubeTerm.mul_left 2).congr fun n => by ring
  have hs2 : Summable (fun n : ℕ => 3 * jsp87SqTerm n) :=
    (summable_jsp87SqTerm.mul_left 3).congr fun n => by ring
  have hs3 : Summable (fun n : ℕ => 2 * jsp87CubeTerm n + 3 * jsp87SqTerm n) := hs1.add hs2
  have e1 : jsp87CubeSeries = ∑' (n : ℕ), jsp87CubeTerm n := rfl
  have e2 : jsp87SquareSeries = ∑' (n : ℕ), jsp87SqTerm n := rfl
  have e3 : jsp87Series = ∑' (n : ℕ), jsp87Term n := jsp87_convergence.tsum_eq
  calc 6 * jsp87CumSqSeries = ∑' (n : ℕ), (6 * jsp87Sq2Term n) :=
      (Summable.tsum_mul_left 6 summable_jsp87Sq2Term).symm
    _ = ∑' (n : ℕ), ((2 * jsp87CubeTerm n + 3 * jsp87SqTerm n) + jsp87Term n) := by
      refine tsum_congr fun n => ?_
      exact jsp87Sq2Term_mul_six n
    _ = (∑' (n : ℕ), (2 * jsp87CubeTerm n + 3 * jsp87SqTerm n)) + ∑' (n : ℕ), jsp87Term n :=
      Summable.tsum_add hs3 summable_omega_mul_inv_two_pow
    _ = ((∑' (n : ℕ), 2 * jsp87CubeTerm n) + ∑' (n : ℕ), 3 * jsp87SqTerm n)
        + ∑' (n : ℕ), jsp87Term n := by rw [Summable.tsum_add hs1 hs2]
    _ = 2 * jsp87CubeSeries + 3 * jsp87SquareSeries + jsp87Series := by
        have g1 := Summable.tsum_mul_left 2 summable_jsp87CubeTerm
        have g2 := Summable.tsum_mul_left 3 summable_jsp87SqTerm
        rw [e1, e2, e3, ← g1, ← g2]

/-- **THE MOMENT LADDER IN ONE LINE** — the same identity solved for the new
number. -/
theorem jsp87CumSqSeries_eq_momentCombination :
    jsp87CumSqSeries = (2 * jsp87CubeSeries + 3 * jsp87SquareSeries + jsp87Series) / 6 := by
  have h := jsp87CumSqSeries_six_eq
  field_simp
  linarith

/-- **THE SQUARE-WEIGHTED "AT LEAST" LADDER IS A SHIFT OF ITSELF** (the mirror of
round 107's `jsp87TriSeries_eq_add_shiftedWeight`):

```
jsp87CumSqSeries = ∑' k, k² · A k = ∑' k, k² · A (k+1) + ∑' k, k² · L k
```

using `L k = A k − A (k+1)` and §3's `∑' k, k² L k = jsp87SquareSeries`. -/
theorem jsp87CumSqSeries_eq_add_sqLevelAndShift :
    jsp87CumSqSeries = jsp87SquareSeries + ∑' (k : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries (k + 1) := by
  have hsub : (∑' (k : ℕ), (((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k
        - (k : ℝ) ^ 2 * jsp87LevelSeries k))
      = jsp87CumSqSeries - jsp87SquareSeries :=
    (Summable.tsum_sub summable_weightedSqAtLeast summable_sqWeightedLevels).trans
      (congrArg₂ (· - ·) jsp87CumSqSeries_eq_tsum_weightedSqAtLeast.symm
        jsp87SquareSeries_eq_tsum_sqWeightedLevels.symm)
  have hshift : (∑' (k : ℕ), (((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k
        - (k : ℝ) ^ 2 * jsp87LevelSeries k))
      = ∑' (k : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries (k + 1) := by
    refine tsum_congr fun k => ?_
    have h := jsp87LevelSeries_sub k
    rw [h, Nat.cast_pow]
    ring
  calc jsp87CumSqSeries = (jsp87CumSqSeries - jsp87SquareSeries) + jsp87SquareSeries := by ring
    _ = (∑' (k : ℕ), (((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries k
          - (k : ℝ) ^ 2 * jsp87LevelSeries k)) + jsp87SquareSeries := by rw [hsub]
    _ = jsp87SquareSeries
        + ∑' (k : ℕ), ((k ^ 2 : ℕ) : ℝ) * jsp87AtLeastSeries (k + 1) :=
      (add_comm _ _).trans (by rw [hshift])

end JSP87
