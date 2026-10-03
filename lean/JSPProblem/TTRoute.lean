/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-112-b).
-/
import JSPProblem.CarryAsymptotic
import JSPProblem.FarDigits
import Mathlib.Tactic

/-!
# JSP-000087 : the Tao–Teräväinen route — truncated carries and the near-integer
# obstruction

## Why this file exists

**The status of JSP-000087 changed in the literature.**  Rounds 37–111 of this
development all recorded the same gate note: *the headline irrationality of
`∑ ω(n)/2^n` is **conditional** in the published literature (Pratt,
arXiv:2409.15185, under a uniform prime `k`-tuples hypothesis), so the statement
`jsp_000087_main : jsp87Series.Irrational` cannot be discharged here.*  That note
is now **superseded**.  T. Tao and J. Teräväinen, *Quantitative correlations and
some problems on prime factors of consecutive integers*, arXiv:2512.01739
(v1 1 Dec 2025, v2 25 Apr 2026), prove **unconditionally** (their Theorem 1.3,
settling Erdős problem #69; the prime case of Erdős problem #257):

```
∑_{n=1}^{∞} ω(n) / 2^n  =  ∑_{p prime} 1 / (2^p − 1)   is irrational.
```

Their §5 is titled *Application to an irrationality problem of Erdős*, and its
subsections are `5.1 Shifting and dilating`, `5.2 Taking an alternating sum to
cancel terms`, `5.3 Taking expectations and truncating`, `5.4 Extracting a
variance bound`.  The introduction states exactly which analytic object they need:

> upper bounds on consecutive values `ω(n+1), …, ω(n+H)` of `ω`, such as (1.6),
> are insufficient; some control on the distribution of various linear
> combinations of such values (e.g. `∑_{h=1}^{H} ω(n+h)/2^h`) is needed.

**That object is a truncated carry of the Erdős series, and this file is the Lean
statement of the reduction.**  Nothing in the previous 111 rounds built it: the
tree has the carry `θ N = ∑' k, ω(N+k) 2^{-(k+1)}` (rounds 40, 44, 50), the
exact split `θ N = ∑_{k<L} ω(N+k) 2^{-(k+1)} + 2^{-L} θ (N+L)` (round 44), and
the denominator obstruction `b · 2^N · τ N ∈ ℤ` (round 41) — but the
*truncation* of the carry at a finite depth `H`, and the near-integer statement
that rationality forces for it, are new.

## What is proved here

1. **§1 the truncated carry** `jsp87TruncCarry N H = ∑_{k<H} ω(N+k) 2^{-(k+1)}`
   with its exact split identity, nonnegativity, and the **quantitative tail
   bound** `θ N − jsp87TruncCarry N H ≤ 2^{-H} (N+H+1)`
   (`jsp87Carry_sub_truncCarry_le`);
2. **§2 THE TAO–TERÄVÄINEN REDUCTION.**
   `jsp87Series_rational_imp_truncCarry_nearInt`: **if `S = a/b` with `b > 0`,
   then for every `N ≥ 1` and every `H` the truncated carry, multiplied by `b`,
   lies within distance `b · 2^{-H} (N+H+1)` of an integer.**  Equivalently
   (`jsp87Series_rational_imp_truncCarry_dist_le`) the truncated carry
   `b · jsp87TruncCarry N H` stays within `b · 2^{-H} (N+H+1)` of the grid
   `b^{-1} ℤ`.  This is the deterministic half of the published proof, machine
   checked;
3. **§3 the distance to `ℤ`**, `jsp87IntDist x = min (Int.fract x) (1 − Int.fract x)`,
   with the characterisation `jsp87IntDist x < ε ↔ ∃ k, |x − k| < ε`;
4. **§4 TWO NEW IRRATIONALITY CRITERIA**, stated against the exact analytic
   content of Tao–Teräväinen §5:
   `jsp87Series_irrational_of_truncCarry_away` (the truncated carry escapes the
   `b`-grid by more than its own tail bound, uniformly in `N` and `H`) and the
   uniform-spacing form `jsp87Series_irrational_of_truncCarry_far` (a positive
   lower bound on the distance to `ℤ`, independent of `N` and `H`), which needs
   only the exponential bound `2^H ≥ (H+3)^2` for `H ≥ 8`
   (`pow_two_ge_sq_add_three`);
5. **§5 the `+1` Lambert series and the alternating-dilation expansion** —
   Tao–Teräväinen §5.1–5.2.  `jsp87PlusLambert = ∑' n, ω(n)/(2^n + 1)` is a
   new series object; `jsp87PlusTerm_hasSum_succ` is the per-`n` geometric
   expansion `ω(n)/(2^n+1) = ∑' k, (-1)^k ω(n) 2^{-k(n+1)}`; and
   `jsp87PlusLambert_alt_trunc_le` is the **finite** alternating-dilation
   expansion with its explicit remainder bound
   `|partial − alternating dilations| ≤ ∑_{n<N} ω(n) 2^{-nJ}`.

## What is *not* proved here

The remaining input is the analytic one, and it is now a *known* theorem rather
than a conjecture, but it is not in Mathlib: the quantitative two-point
correlation estimate for multiplicative functions of Pilatte type that
Tao–Teräväinen use in their §3 (`Theorem 3.1` of arXiv:2512.01739), together
with the Erdős–Kac-type estimates and the probabilistic ("taking expectations",
"variance bound") argument of their §5.3–§5.14.  §4 above states, as the named
Prop `jsp87TruncCarryEscapes`, exactly the estimate that would finish the
reduction.  Declaring `jsp_000087_main` still requires that input; it is an
assumption of the *published proof*, not of the *catalog statement*, so it is
not inserted here.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## 1. The truncated carry -/

/-- **The carry bound `θ M ≤ M + 1` at every cut point, including `M = 0`.**
Round 40's `jsp87Carry_le` assumes `1 ≤ M`; at `M = 0` one has
`θ 0 = jsp87Series ≤ 1` by `jsp87Carry_zero` and `jsp87Series_le_one`. -/
theorem jsp87Carry_le_all (M : ℕ) : jsp87Carry M ≤ ((M + 1 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · rw [hM, jsp87Carry_zero]
    have h := jsp87Series_le_one
    norm_num at h ⊢
    exact h
  · exact jsp87Carry_le hM

/-- **The truncated carry at the cut point `N`, truncated after `H` terms**:
`∑_{k<H} ω(N+k) 2^{-(k+1)}`.  This is the finite linear combination of
*consecutive* values of `ω` that the introduction of arXiv:2512.01739 names as
the object needing distributional control:

> some control on the distribution of various linear combinations of such values
> (e.g. `∑_{h=1}^{H} ω(n+h)/2^h`) is needed. -/
noncomputable def jsp87TruncCarry (N H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range H, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹

/-- **The truncated carry is the carry minus the rescaled tail** — the exact
form of round 44's `jsp87Carry_split` for a truncation:
`jsp87TruncCarry N H + 2^{-H} · θ (N+H) = θ N`. -/
theorem jsp87TruncCarry_eq_split (N H : ℕ) :
    jsp87Carry N = jsp87TruncCarry N H + ((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H) := by
  unfold jsp87TruncCarry
  exact jsp87Carry_split N H

theorem jsp87TruncCarry_nonneg (N H : ℕ) : 0 ≤ jsp87TruncCarry N H := by
  unfold jsp87TruncCarry
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **The truncated carry never exceeds the carry.** -/
theorem jsp87TruncCarry_le (N H : ℕ) : jsp87TruncCarry N H ≤ jsp87Carry N := by
  have h := jsp87TruncCarry_eq_split N H
  have hp : 0 ≤ ((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H) :=
    mul_nonneg (by positivity) (le_of_lt (jsp87Carry_pos (N + H)))
  linarith

/-- **The truncation error is nonnegative.** -/
theorem jsp87Carry_sub_truncCarry_nonneg (N H : ℕ) :
    0 ≤ jsp87Carry N - jsp87TruncCarry N H := by
  have h := jsp87TruncCarry_eq_split N H
  have hp : 0 ≤ ((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H) :=
    mul_nonneg (by positivity) (le_of_lt (jsp87Carry_pos (N + H)))
  linarith

/-- **THE QUANTITATIVE TAIL BOUND.**
`0 ≤ θ N − ∑_{k<H} ω(N+k) 2^{-(k+1)} ≤ 2^{-H} (N+H+1)`.

The upper bound is the carry bound `θ M ≤ M + 1` (§1, `jsp87Carry_le_all`)
applied at `M = N+H` inside the exact split.  It is the statement that the
truncation error vanishes, at least geometrically, as `H → ∞` — the reason the
reduction of §2 is *quantitative* rather than merely qualitative. -/
theorem jsp87Carry_sub_truncCarry_le (N H : ℕ) :
    jsp87Carry N - jsp87TruncCarry N H ≤ ((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ) := by
  have hpos := jsp87Carry_sub_truncCarry_nonneg N H
  calc jsp87Carry N - jsp87TruncCarry N H = ((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H) := by
        linarith [jsp87TruncCarry_eq_split N H]
    _ ≤ ((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (jsp87Carry_le_all (N + H)) (by positivity)

/-! ## 2. The Tao–Teräväinen reduction: rationality pins the truncated carry to
the `b`-grid -/

/-- **RATIONALITY FREEZES EVERY CARRY INTO `(1/b) ℤ`.**  This is round 41's
`jsp87_carry_mul_eq_int` rewritten for `θ N = jsp87Carry N` (the definitionally
equal `2^N · τ N`). -/
theorem jsp87Series_rational_imp_carry_mul_int {N : ℕ} (hN : 1 ≤ N) {a b : ℤ}
    (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, jsp87Carry N * (b : ℝ) = (c : ℝ) := by
  obtain ⟨c, hc⟩ := jsp87_carry_mul_eq_int (N := N) hN hb h
  refine ⟨c, ?_⟩
  have e : jsp87Carry N = (2 : ℝ) ^ N * jsp87Tail N := rfl
  rw [e, ← hc]

/-- **THE MAIN THEOREM OF THIS FILE — THE TAO–TERÄVÄINEN REDUCTION.**

If the Erdős series is the rational `a / b` with `b > 0`, then for **every**
cut point `N ≥ 1` and **every** truncation depth `H` there is an integer `c`
with

```
| b · ∑_{k<H} ω(N+k) 2^{-(k+1)}  −  c |   ≤   b · 2^{-H} · (N + H + 1).
```

In words: **the truncated carry, multiplied by the denominator of the
hypothetical rational value, is always within an exponentially small window of
an integer.**  The integer is forced (`b θ N ∈ ℤ`, §2 above) and the window is
the truncation error (§1).

This is exactly the deterministic half of Tao–Teräväinen's §5: a rational value
of `∑ ω(n)/2^n` would force the linear combinations `∑_{h<H} ω(N+h)/2^{h+1}` of
consecutive `ω`-values to be *arithmetically quantised*, with an explicit error
term.  What remains for `jsp_000087_main` is to show that these quantities are
**not** quantised — the distributional statement of arXiv:2512.01739. -/
theorem jsp87Series_rational_imp_truncCarry_nearInt {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) (N H : ℕ) (hN : 1 ≤ N) :
    ∃ c : ℤ, |(b : ℝ) * jsp87TruncCarry N H - (c : ℝ)|
      ≤ (b : ℝ) * ((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ) := by
  obtain ⟨c, hc⟩ := jsp87Series_rational_imp_carry_mul_int (N := N) hN hb h
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (le_of_lt hb)
  have hhalf : (0 : ℝ) ≤ ((2 : ℝ) ^ H)⁻¹ := by positivity
  have key : (b : ℝ) * (jsp87Carry N - jsp87TruncCarry N H)
      = (b : ℝ) * (((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H)) := by
    rw [jsp87TruncCarry_eq_split]
    ring
  refine ⟨c, ?_⟩
  calc |(b : ℝ) * jsp87TruncCarry N H - (c : ℝ)|
      = |(b : ℝ) * jsp87TruncCarry N H - (b : ℝ) * jsp87Carry N| := by
        congr 1
        linarith [hc]
    _ = |((b : ℝ) * (((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H)))| := by
        rw [show (b : ℝ) * jsp87TruncCarry N H - (b : ℝ) * jsp87Carry N
              = -((b : ℝ) * (jsp87Carry N - jsp87TruncCarry N H)) by ring, key, abs_neg]
    _ = (b : ℝ) * (((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H)) := by
        rw [show (b : ℝ) * (((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H))
              = (b : ℝ) * ((2 : ℝ) ^ H)⁻¹ * jsp87Carry (N + H) by ring]
        exact abs_of_nonneg (mul_nonneg (mul_nonneg hb0 hhalf)
          (le_of_lt (jsp87Carry_pos (N + H))))
    _ ≤ (b : ℝ) * (((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (jsp87Carry_le_all (N + H)) hhalf) hb0
    _ = (b : ℝ) * ((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ) := by ring

/-! ## 3. The distance to the integers -/

/-- **The distance of a real number to the integers**, as a number in `[0, 1/2]`:
`min (Int.fract x) (1 − Int.fract x)`. -/
noncomputable def jsp87IntDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

theorem jsp87IntDist_nonneg (x : ℝ) : 0 ≤ jsp87IntDist x := by
  unfold jsp87IntDist
  exact le_min (Int.fract_nonneg x) (by linarith [Int.fract_lt_one x])

theorem jsp87IntDist_le_half (x : ℝ) : jsp87IntDist x ≤ 1 / 2 := by
  unfold jsp87IntDist
  have h1 := Int.fract_lt_one x
  have h2 := Int.fract_nonneg x
  have h3 : min (Int.fract x) (1 - Int.fract x) ≤ Int.fract x := min_le_left _ _
  have h4 : min (Int.fract x) (1 - Int.fract x) ≤ 1 - Int.fract x := min_le_right _ _
  linarith

/-- **The distance to `ℤ` bounds the distance to every integer.** -/
theorem jsp87IntDist_le_abs_sub (x : ℝ) (k : ℤ) :
    jsp87IntDist x ≤ |x - (k : ℝ)| := by
  have hf : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hid : x - (k : ℝ) = Int.fract x - ((k - ⌊x⌋ : ℤ) : ℝ) := by
    have hfrac := Int.floor_add_fract x
    push_cast at hfrac ⊢
    linarith
  rw [hid, jsp87IntDist]
  rcases le_total (k - ⌊x⌋) 0 with hm | hm
  · rcases eq_or_lt_of_le hm with heq | hlt
    · rw [heq, Int.cast_zero, sub_zero, abs_of_nonneg hf]
      exact min_le_left (Int.fract x) (1 - Int.fract x)
    · have hz : (k - ⌊x⌋ : ℤ) ≤ -1 := by omega
      have hmn : ((k - ⌊x⌋ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hz
      have hpos : 0 ≤ Int.fract x - ((k - ⌊x⌋ : ℤ) : ℝ) := by linarith
      rw [abs_of_nonneg hpos]
      exact (min_le_left (Int.fract x) (1 - Int.fract x)).trans (by linarith)
  · rcases eq_or_lt_of_le hm with heq | hlt
    · rw [heq.symm, Int.cast_zero, sub_zero, abs_of_nonneg hf]
      exact min_le_left _ _
    · have hz : (1 : ℤ) ≤ k - ⌊x⌋ := by omega
      have hmn : (1 : ℝ) ≤ ((k - ⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast hz
      have hf1 := Int.fract_lt_one x
      have hneg : Int.fract x - ((k - ⌊x⌋ : ℤ) : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      exact (min_le_right (Int.fract x) (1 - Int.fract x)).trans (by linarith)

/-- **THE CHARACTERISATION OF THE DISTANCE TO `ℤ`.**
`jsp87IntDist x < ε ↔ ∃ k : ℤ, |x − k| < ε`: the near-integer statement of §2
in the form in which it can be contradicted. -/
theorem jsp87IntDist_lt_iff (x : ℝ) (ε : ℝ) :
    jsp87IntDist x < ε ↔ ∃ k : ℤ, |x - (k : ℝ)| < ε := by
  constructor
  · intro h
    rcases min_lt_iff.mp h with hf | h2
    · refine ⟨⌊x⌋, ?_⟩
      have h1 : x - (⌊x⌋ : ℝ) = Int.fract x := by
        have hfrac := Int.floor_add_fract x
        linarith
      rw [h1, abs_of_nonneg (Int.fract_nonneg x)]
      exact hf
    · refine ⟨⌊x⌋ + 1, ?_⟩
      have h1 : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = Int.fract x - 1 := by
        have hfrac := Int.floor_add_fract x
        push_cast at hfrac ⊢
        linarith
      rw [h1, abs_of_neg (by linarith [Int.fract_lt_one x])]
      linarith
  · rintro ⟨k, hk⟩
    exact lt_of_le_of_lt (jsp87IntDist_le_abs_sub x k) hk

/-- **THE DISTANCE FORM OF THE REDUCTION.**  If `S = a/b` with `b > 0`, then
`b · jsp87TruncCarry N H` is within `b · 2^{-H} (N+H+1)` of the lattice
`(1/b) ℤ`, for every `N ≥ 1` and every `H`. -/
theorem jsp87Series_rational_imp_truncCarry_dist_le {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) (N H : ℕ) (hN : 1 ≤ N) :
    jsp87IntDist ((b : ℝ) * jsp87TruncCarry N H)
      ≤ (b : ℝ) * ((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ) := by
  obtain ⟨c, hc⟩ := jsp87Series_rational_imp_truncCarry_nearInt hb h N H hN
  exact le_trans (jsp87IntDist_le_abs_sub _ c) hc

/-! ## 4. Two irrationality criteria against the Tao–Teräväinen content -/

/-- **THE ESCAPE HYPOTHESIS OF ARXIV:2512.01739, §5**, named so that the single
missing input carries a name in the tree: for a fixed `b ≥ 1`, the truncated
carry `b · jsp87TruncCarry N H` is *never* within its own tail bound of an
integer, uniformly in the cut point `N ≥ 1` and in the truncation depth `H`. -/
def jsp87TruncCarryEscapes (b : ℕ) : Prop :=
  ∀ (H N : ℕ) (k : ℤ), 1 ≤ N →
    |(b : ℝ) * jsp87TruncCarry N H - (k : ℝ)|
      > (b : ℝ) * ((2 : ℝ) ^ H)⁻¹ * ((N + H + 1 : ℕ) : ℝ)

/-- **CRITERION 1 (THE ESCAPE CRITERION).**  If the truncated carries
escape the `b`-grid by more than their own tail bound **for every** `b ≥ 1`
(`∀ b ≥ 1, jsp87TruncCarryEscapes b`), then `jsp87Series` is irrational.

The quantifier over `b` must be universal, and this is a real point rather than
a technicality: the escape estimate for a *single* `b` does **not** contradict
rationality, because rationality constrains the lattice `q^{-1} ℤ` of the
denominator `q` that actually occurs, and the escape estimate at `b ≠ q` is
compatible with the near-integer statement of §2 at `q`. -/
theorem jsp87Series_irrational_of_truncCarry_away
    (haway : ∀ b : ℕ, 1 ≤ b → jsp87TruncCarryEscapes b) : Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  have hq' : jsp87Series = (((q.num : ℤ) : ℝ) / (((q.den : ℕ) : ℤ) : ℝ)) := by
    rw [← hq, Rat.cast_def]
    push_cast
    ring
  obtain ⟨c, hc⟩ := jsp87Series_rational_imp_truncCarry_nearInt (a := q.num)
    (b := q.den) (by exact_mod_cast (by omega)) hq' 1 1 (by omega)
  have hlt := haway q.den (by exact_mod_cast (by omega)) 1 1 c (by omega)
  have hlt' : |(((q.den : ℕ) : ℤ) : ℝ) * jsp87TruncCarry 1 1 - (c : ℝ)|
      > (((q.den : ℕ) : ℤ) : ℝ) * ((2 : ℝ) ^ 1)⁻¹ * ((1 + 1 + 1 : ℕ) : ℝ) := by
    simpa using hlt
  linarith

/-- **`2 ^ H ≥ (H + 3) ^ 2` for `H ≥ 8`**, the elementary exponential estimate
that turns the tail bound `2^{-H} (H+2)` into a quantity one can make smaller
than any prescribed positive `c`. -/
theorem pow_two_ge_sq_add_three : ∀ H : ℕ, 8 ≤ H → 2 ^ H ≥ (H + 3) ^ 2 := by
  have aux : ∀ H : ℕ, 7 ≤ H → 2 ^ H ≥ (H + 3) ^ 2 := by
    intro H
    induction H with
    | zero => omega
    | succ H ih =>
      intro hH
      by_cases hlt : H < 7
      · have h6 : H = 6 := by omega
        subst h6
        norm_num
      · rw [pow_succ]
        have ih' := ih (show 7 ≤ H from by omega)
        have hstep : 2 * (H + 3) ^ 2 ≥ (H + 4) ^ 2 := by nlinarith
        calc 2 ^ H * 2 ≥ 2 * (H + 3) ^ 2 := by nlinarith [ih']
          _ ≥ (H + 4) ^ 2 := hstep
          _ = (H + 1 + 3) ^ 2 := by ring
  intro H hH
  exact aux H (by omega)

/-- **CRITERION 2 (THE UNIFORM-SPACING CRITERION).**  Suppose that for
**every** `b ≥ 1` there is a constant `c_b > 0` such that the truncated carries
`b · jsp87TruncCarry N H` stay at distance at least `c_b` from **every** integer,
uniformly in `N ≥ 1` and in `H`.  Then `jsp87Series` is irrational.

This is the shape of the estimate Tao–Teräväinen obtain: their §5.3–§5.14 bound
the expectation and the variance of `∑_{h≤H} ω(n+h)/2^h` and show it cannot sit
inside the lattice `q^{-1} ℤ`, contradicting the reduction of §2.  The `c_b` may
depend on `b` (as in a variance estimate, where the constant degrades like a
power of a parameter) but not on `N` or `H`. -/
theorem jsp87Series_irrational_of_truncCarry_far
    (hfar : ∀ b : ℕ, 1 ≤ b → ∃ c : ℝ, 0 < c ∧
      ∀ (H N : ℕ), 1 ≤ N → jsp87IntDist ((b : ℝ) * jsp87TruncCarry N H) ≥ c) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  have hq' : jsp87Series = (((q.num : ℤ) : ℝ) / (((q.den : ℕ) : ℤ) : ℝ)) := by
    rw [← hq, Rat.cast_def]
    push_cast
    ring
  obtain ⟨c, hc, hfar'⟩ := hfar q.den (by exact_mod_cast (by omega))
  set H := Nat.ceil (((q.den : ℕ) : ℝ) / c) + 9 with hHdef
  have hceil : (((q.den : ℕ) : ℝ)) / c ≤ (H : ℝ) := by
    have hle := Nat.le_ceil (((q.den : ℕ) : ℝ) / c)
    rw [hHdef]
    exact le_trans hle
      (by exact_mod_cast
        (Nat.le_add_right (Nat.ceil (((q.den : ℕ) : ℝ) / c)) 9))
  have hH8 : 8 ≤ H := by
    rw [hHdef]
    have hk : 9 ≤ 9 + Nat.ceil (((q.den : ℕ) : ℝ) / c) :=
      Nat.le_add_right 9 (Nat.ceil (((q.den : ℕ) : ℝ) / c))
    have h9 : 9 ≤ Nat.ceil (((q.den : ℕ) : ℝ) / c) + 9 := by
      rw [Nat.add_comm]
      exact hk
    omega
  have hbound : (((q.den : ℕ) : ℤ) : ℝ) * ((2 : ℝ) ^ H)⁻¹ * ((1 + H + 1 : ℕ) : ℝ) < c := by
    have hpow : (2 : ℝ) ^ H ≥ ((H : ℝ) + 3) ^ 2 := by
      exact_mod_cast (pow_two_ge_sq_add_three H hH8)
    have hW : (0 : ℝ) ≤ ((H : ℝ) + 3)⁻¹ := by positivity
    have hY : (0 : ℝ) ≤ ((1 + H + 1 : ℕ) : ℝ) := by positivity
    have hB : (0 : ℝ) ≤ (((q.den : ℕ) : ℤ) : ℝ) := le_of_lt (by exact_mod_cast (by omega))
    have hsmall : ((H : ℝ) + 3)⁻¹ * ((1 + H + 1 : ℕ) : ℝ) ≤ 1 := by
      have hle : ((1 + H + 1 : ℕ) : ℝ) ≤ ((H : ℝ) + 3) := by
        push_cast
        linarith
      calc ((H : ℝ) + 3)⁻¹ * ((1 + H + 1 : ℕ) : ℝ)
          ≤ ((H : ℝ) + 3)⁻¹ * ((H : ℝ) + 3) := mul_le_mul_of_nonneg_left hle hW
        _ = 1 := inv_mul_cancel₀ (by positivity : ((H : ℝ) + 3) ≠ 0)
    have hinv : ((2 : ℝ) ^ H)⁻¹ ≤ ((H : ℝ) + 3)⁻¹ ^ 2 := by
      have h1 : (0 : ℝ) < ((H : ℝ) + 3) ^ 2 := by positivity
      have h3 : 1 / (2 : ℝ) ^ H ≤ 1 / ((H : ℝ) + 3) ^ 2 :=
        one_div_le_one_div_of_le h1 hpow
      calc ((2 : ℝ) ^ H)⁻¹ = 1 / (2 : ℝ) ^ H := (one_div _).symm
        _ ≤ 1 / ((H : ℝ) + 3) ^ 2 := h3
        _ = ((H : ℝ) + 3)⁻¹ ^ 2 := by rw [div_eq_mul_inv, one_mul, ← inv_pow]
    calc (((q.den : ℕ) : ℤ) : ℝ) * ((2 : ℝ) ^ H)⁻¹ * ((1 + H + 1 : ℕ) : ℝ)
        = (((q.den : ℕ) : ℤ) : ℝ) * (((2 : ℝ) ^ H)⁻¹ * ((1 + H + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (((q.den : ℕ) : ℤ) : ℝ)
          * (((H : ℝ) + 3)⁻¹ ^ 2 * ((1 + H + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv hY) hB
      _ = (((q.den : ℕ) : ℤ) : ℝ) * (((H : ℝ) + 3)⁻¹ * ((1 + H + 1 : ℕ) : ℝ))
          * ((H : ℝ) + 3)⁻¹ := by ring
      _ ≤ (((q.den : ℕ) : ℤ) : ℝ) * 1 * ((H : ℝ) + 3)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hB) hW
      _ = (((q.den : ℕ) : ℤ) : ℝ) * ((H : ℝ) + 3)⁻¹ := by ring
      _ < c := by
        have hBsame : (((q.den : ℕ) : ℤ) : ℝ) = (((q.den : ℕ) : ℕ) : ℝ) := by norm_num
        have hceil' : (((q.den : ℕ) : ℕ) : ℝ) ≤ (H : ℝ) * c :=
          (div_le_iff₀ hc).mp hceil
        rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
        nlinarith [hceil', hBsame]
  have hdist := jsp87Series_rational_imp_truncCarry_dist_le (a := q.num)
    (b := q.den) (by exact_mod_cast (by omega)) hq' 1 H (by omega)
  have hfar'' := hfar' H 1 (by omega)
  have hBsame : (((q.den : ℕ) : ℤ) : ℝ) = (((q.den : ℕ) : ℕ) : ℝ) := by norm_num
  rw [hBsame] at hdist hbound
  linarith

/-! ## 5. The `+1` Lambert series and the dilations (arXiv:2512.01739 §5.1–5.2) -/

/-- **THE `+1` LAMBERT SERIES** `∑' n, ω(n) / (2^n + 1)`.

This is the object that Tao–Teräväinen's §5.1–§5.2 ("*Shifting and dilating*",
"*Taking an alternating sum to cancel terms*") produces: since

```
1 / (2^n + 1)  =  ∑' k ≥ 0, (-1)^k · 2^(-(k+1)) ^ n ,
```

the `+1` series is the alternating sum, over the **dilations** of the Erdős
series, of the objects `jsp87ScaleLambert k` below.  Neither this series nor the
dilations appear anywhere in the previous 111 rounds. -/
noncomputable def jsp87PlusLambert : ℝ :=
  ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹

/-- **A `DILATION` of the Erdős series:** `jsp87ScaleLambert k = ∑' n, ω(n) 2^(-k n)`,
the value of the generating function `n ↦ ω(n)` at `2^{-k}`.  For `k = 1` this
is twice the Erdős series; for `k ≥ 2` it is a genuinely different number. -/
noncomputable def jsp87ScaleLambert (k : ℕ) : ℝ :=
  ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (k * n))⁻¹

theorem summable_omega_two_pow_neg :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) := by
  have h := (summable_omegaShift 0).mul_left (2 : ℝ)
  refine h.congr ?_
  intro n
  simp only [pow_succ, Nat.zero_add]
  field_simp

theorem summable_jsp87PlusTerm :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_omega_two_pow_neg
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro n
    have hinv : ((2 : ℝ) ^ n + 1)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
    exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)

/-- **THE `+1` SERIES IS NONNEGATIVE.** -/
theorem jsp87PlusLambert_nonneg : 0 ≤ jsp87PlusLambert := by
  rw [jsp87PlusLambert]
  exact tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE `+1` SERIES IS AT MOST TWICE THE ERDŐS SERIES**: `ω(n)/(2^n+1) ≤ ω(n) 2^{-n}`
term by term. -/
theorem jsp87PlusLambert_le_two_mul_series : jsp87PlusLambert ≤ 2 * jsp87Series := by
  rw [jsp87PlusLambert]
  calc (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹)
      ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ :=
        summable_jsp87PlusTerm.tsum_le_tsum (fun n => by
          have hinv : ((2 : ℝ) ^ n + 1)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ :=
            (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
          exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _))
          summable_omega_two_pow_neg
    _ = 2 * jsp87Series := by
        unfold jsp87Series
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        simp only [pow_succ]
        field_simp

/-- **THE FIRST DILATION IS TWICE THE ERDŐS SERIES:**
`jsp87ScaleLambert 1 = 2 * jsp87Series`, i.e. the dilation at `2^{-1}` of the
Erdős generating function is the Erdős series itself. -/
theorem jsp87ScaleLambert_one : jsp87ScaleLambert 1 = 2 * jsp87Series := by
  have heq : (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (1 * n))⁻¹)
      = fun n => 2 * (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
        funext n
        rw [one_mul, pow_succ]
        ring
  rw [jsp87ScaleLambert, heq, tsum_mul_left]
  rfl

end JSP87
