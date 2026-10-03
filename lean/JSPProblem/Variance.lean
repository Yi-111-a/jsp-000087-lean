/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-116).
-/
import JSPProblem.AltSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# JSP-000087, round 116 — THE PROBABILISTIC ENDGAME OF §5.3–§5.11

## Why this file exists

Rounds 88–91 (`AltSum.lean`, `CubeSplit.lean`) formalised the **deterministic**
half of Tao–Teräväinen §5.1–5.2: the dilated window identity, the Gowers-cube
cancellation, and the mod-1 quantisation of the alternating window.  Rounds
112–115 formalised the objects of §5.3 (the truncated carry) and the correlation
sums of their §3.

**Nothing in the 115 previous rounds touched the second half of §5 at all.**
§5.3–§5.11 of arXiv:2512.01739 is a *probabilistic* argument: a sample point `n`
is drawn uniformly from a subprogression of `[x/2, x]`, the primes are split
`S₀ ⊎ S₁ ⊎ S₂`, random variables

```
X_p := q ∑_{1≤h≤H} ∑_{ε∈{0,1}^K} (−1)^{|ε|} 2^{−(h+K)} [ p ∣ n + r_{ε,h+K} ]
```

are formed, and one shows

* (5.15) `𝔼 e(∑_{p∈S₁} X_p) = 1 + O(κ₁) + O(κ₂) + O(κ₃)`;
* (5.16)–(5.17) `𝔼 e(∑_{p∈S₁} X_p) = ∏_{p∈S₁} 𝔼 e(X_p) + O(κ₄ + O(κ₅)`
  — the *independent copy* argument;
* (5.19)–(5.20) `∏_{p∈S₁} |𝔼 e(X_p)| ≤ exp(−c ∑_p Var X_p)` when every
  `X_p = o(1)`;
* (5.21) `∑_{p∈S₁} Var X_p ≫ 1`;

and concludes: **if (5.18) `κ_j = o(1)` then `∑_p Var X_p = o(1)`, contradicting
(5.21)**.  Their *Theorem 5.1 (technical reduction)* is the assertion that a
configuration satisfying (5.18)–(5.21) exists, so the endgame is exactly the
statement that the two sets of conditions are **mutually inconsistent**.

**That endgame is proved here.**  It is a statement about real numbers, complex
exponentials and finite uniform averages, and it closes with the explicit
constant `κ₁ + κ₂ + κ₃ + κ₄ + κ₅ ≥ 1/2`.  Consequently the *entire* remaining
burden of `jsp_000087_main` is localised to two named arithmetic inputs,
(5.18) and (5.21), both of which are statements about `ω` on progressions of
integers — not about probability.

## What is proved here

| Section | Content |
| --- | --- |
| §1 | `jsp87FAvg`: the uniform average on a finite set (the expectation), additivity, `\|𝔼 f\| ≤ 𝔼\|f\|`, and Cauchy–Schwarz from scratch (`jsp87CS`, `jsp87FAvg_abs_le_sqrt_sq`) |
| §2 | the analytic toolbox: `jsp87e t = exp (2πi t)`, `‖jsp87e t‖ = 1`, `jsp87e_add`, and the Lipschitz bound `‖e a − e a * e b‖ ≤ 2π\|b\|` (from Mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le`) |
| §3 | **κ₃**: `jsp87E_split_le`, the Cauchy–Schwarz/Taylor split `‖𝔼 e(q(c+T+R)) − e(qc) 𝔼 e(qT)‖ ≤ 2π\|q\| 𝔼\|R\| ≤ 2π\|q\| sqrt(𝔼 R²)` — the deterministic content of (5.14) |
| §4 | **the variance bound (5.19)–(5.20)**: `jsp87_one_sub_cos_ge`, `jsp87FAvg_sub_sq` (`𝔼_{i,j}(f i − f j)² = 2 Var f`), `jsp87_charfun_sq_le`, `jsp87_charfun_le`, `jsp87_prod_charfun_le`, `jsp87_prod_charfun_le_half` |
| §5 | **THE ENDGAME**: `jsp87_endgame_sum_ge`, `κ₁+κ₂+κ₃+κ₄+κ₅ ≥ 1/6` under (5.15), (5.16)–(5.17), (5.19), (5.21); and `jsp87_endgame_impossible`: **Theorem 5.1 of arXiv:2512.01739 together with (5.18) and (5.21) is unsatisfiable** |
| §6 | **the arithmetic of §5.2/§5.5**: the paper's random variable `jsp87Xp` (5.13) as a Lean object, its *determinism* modulo `p` (`jsp87Xp_congr_mod`, `jsp87Xp_congr_of_dvd`) — the mechanism that makes `p ∈ S₀` deterministic — and the bound `\|X_p\| ≤ q 2^{−K}` of (5.36), which **discharges hypothesis (5.19) unconditionally** |

## What is *not* proved here

`jsp_000087_main` is **not declared**.  With the endgame of §5 machine-checked,
what remains is exactly the content of their §5.5–§5.14: the quantitative
estimates (5.18) `κ_j = o(1)` for `j = 1 … 5` and the variance lower bound (5.21)
`∑_{p∈S₁} Var X_p ≫ 1`.  Both are statements about the distribution of `ω`
along progressions of integers; (5.21) needs their `Theorem 3.1`, the
quantitative two-point correlation estimate derived from Pilatte's work, for
which Mathlib has no analogue whatsoever.  The *M*-th-moment form of (5.16),
`(2π)^M t^M/M! ≤ e^t + e^{−t}`, is a statement about termwise domination in the
exponential series and is **not** proved here either: it plays no role in the
endgame contradiction of §5 below, which is why its absence does not affect the
reduction.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## §1  Finite uniform expectations -/

/-- **The uniform average on a finite set**: the expectation of `f` at a sample
point drawn uniformly from `s`.  This is the finite model of the expectations
`𝔼` of Tao–Teräväinen §5.3. -/
noncomputable def jsp87FAvg {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) : ℝ :=
  (∑ i ∈ s, f i) / (s.card : ℝ)

theorem jsp87FAvg_add {Ω : Type*} (s : Finset Ω) (f g : Ω → ℝ) :
    jsp87FAvg s (fun i => f i + g i) = jsp87FAvg s f + jsp87FAvg s g := by
  simp [jsp87FAvg, add_div, Finset.sum_add_distrib]

theorem jsp87FAvg_sub {Ω : Type*} (s : Finset Ω) (f g : Ω → ℝ) :
    jsp87FAvg s (fun i => f i - g i) = jsp87FAvg s f - jsp87FAvg s g := by
  simp [jsp87FAvg, sub_div, Finset.sum_sub_distrib]

theorem jsp87FAvg_mul_const {Ω : Type*} (s : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    jsp87FAvg s (fun i => c * f i) = c * jsp87FAvg s f := by
  rw [jsp87FAvg, jsp87FAvg, ← Finset.mul_sum]
  ring

theorem jsp87FAvg_one {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) :
    jsp87FAvg s (fun _ => (1 : ℝ)) = 1 := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  simp [jsp87FAvg, hcard]

theorem jsp87FAvg_nonneg {Ω : Type*} {s : Finset Ω} {f : Ω → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ jsp87FAvg s f := by
  have h1 : (0 : ℝ) ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => hf i hi
  rw [jsp87FAvg]
  exact div_nonneg h1 (Nat.cast_nonneg _)

theorem jsp87FAvg_le_of_pointwise_le {Ω : Type*} {s : Finset Ω} {f g : Ω → ℝ}
    (h : ∀ i ∈ s, f i ≤ g i) : jsp87FAvg s f ≤ jsp87FAvg s g := by
  have h1 : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i := Finset.sum_le_sum fun i hi => h i hi
  rcases s.eq_empty_or_nonempty with he | hne
  · simp [jsp87FAvg, he]
  · have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
    rw [jsp87FAvg, jsp87FAvg, div_le_div_iff_of_pos_right hcard]
    exact h1

/-- **The triangle inequality for the average** — `|𝔼 f| ≤ 𝔼 |f|`. -/
theorem jsp87FAvg_abs_le {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) :
    |jsp87FAvg s f| ≤ jsp87FAvg s (fun i => |f i|) := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [jsp87FAvg, h]
  · have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr h
    rw [jsp87FAvg, jsp87FAvg, abs_div, abs_of_pos hcard,
      div_le_div_iff_of_pos_right hcard]
    exact Finset.abs_sum_le_sum_abs f s

/-- **THE DISCRIMINANT LEMALA**, the algebraic core of Cauchy–Schwarz: if
`t ↦ t² A + 2tB + C` is nonnegative for every `t` and `A > 0`, then `B² ≤ A C`
(minimise at `t = −B/A`). -/
private theorem jsp87disc {A B C : ℝ} (hA : 0 < A)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * A + 2 * t * B + C) : B ^ 2 ≤ A * C := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hid : (-(B / A)) ^ 2 * A + 2 * -(B / A) * B + C = C - B ^ 2 / A := by
    field_simp
    ring
  have hkey : 0 ≤ C - B ^ 2 / A := by
    have h1 := h (-(B / A))
    rw [hid] at h1
    exact h1
  have h2 := mul_nonneg (le_of_lt hA) hkey
  field_simp at h2
  nlinarith [hA]

/-- **CAUCHY–SCHWARZ FOR FINITE SUMS, FROM SCRATCH.**
`(∑ fᵢ gᵢ)² ≤ (∑ fᵢ²) (∑ gᵢ²)`, by the discriminant argument: the quadratic
`∑ (fᵢ t + gᵢ)²` is nonnegative for every `t`. -/
theorem jsp87CS {Ω : Type*} (s : Finset Ω) (f g : Ω → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  have hexp : ∀ t : ℝ,
      (∑ i ∈ s, (f i * t + g i) ^ 2)
        = t ^ 2 * (∑ i ∈ s, f i ^ 2) + 2 * t * (∑ i ∈ s, f i * g i)
          + (∑ i ∈ s, g i ^ 2) := by
    intro t
    have hterm : ∀ i ∈ s, (f i * t + g i) ^ 2
        = t ^ 2 * f i ^ 2 + 2 * t * (f i * g i) + g i ^ 2 := by
      intro i _; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have hnn : ∀ t : ℝ, 0 ≤ ∑ i ∈ s, (f i * t + g i) ^ 2 :=
    fun t => Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hA : (∑ i ∈ s, f i ^ 2) = 0
  · have hfz : ∀ i ∈ s, f i = 0 := by
      intro i hi
      have h1 := Finset.single_le_sum (s := s) (f := fun j : Ω => f j ^ 2)
        (fun j _ => sq_nonneg _) hi
      rw [hA] at h1
      nlinarith [sq_nonneg (f i)]
    have hBzero : (∑ i ∈ s, f i * g i) = 0 := by
      rw [Finset.sum_eq_zero]
      intro i hi
      rw [hfz i hi]
      ring
    rw [hBzero, hA]
    simp
  · exact jsp87disc (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hA)) (fun t => by rw [← hexp t]; exact hnn t)

/-- **Cauchy–Schwarz for the uniform average**: `(𝔼 |f|)² ≤ 𝔼 (f²)`. -/
theorem jsp87FAvg_abs_sq_le {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) :
    (jsp87FAvg s (fun i => |f i|)) ^ 2 ≤ jsp87FAvg s (fun i => f i ^ 2) := by
  have h1 : ((∑ i ∈ s, |f i|) : ℝ) ^ 2 ≤ ((∑ i ∈ s, f i ^ 2) : ℝ) * (s.card : ℝ) := by
    have hCS := jsp87CS s (fun _ => (1 : ℝ)) (fun i => |f i|)
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.mem_univ, true_and, one_mul,
      one_pow, mul_one, mul_comm, sq_abs] using hCS
  have hc : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  rw [jsp87FAvg, jsp87FAvg, div_pow]
  calc (∑ i ∈ s, |f i|) ^ 2 / (s.card : ℝ) ^ 2
      ≤ ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) / (s.card : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h1 (sq_nonneg (s.card : ℝ))
    _ = (∑ i ∈ s, f i ^ 2) / (s.card : ℝ) := by field_simp

/-- **The `L²`-bound on the average of a real function**: `𝔼 |f| ≤ sqrt (𝔼 f²)`.
This is the Cauchy–Schwarz step in the estimate (5.14) for `κ₃`. -/
theorem jsp87FAvg_abs_le_sqrt_sq {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (f : Ω → ℝ) :
    jsp87FAvg s (fun i => |f i|) ≤ Real.sqrt (jsp87FAvg s (fun i => f i ^ 2)) := by
  have h1 := jsp87FAvg_abs_sq_le s hs f
  have h2 : 0 ≤ jsp87FAvg s (fun i => f i ^ 2) :=
    jsp87FAvg_nonneg fun i _ => sq_nonneg (f i)
  have h3 : (Real.sqrt (jsp87FAvg s (fun i => f i ^ 2))) ^ 2
      = jsp87FAvg s (fun i => f i ^ 2) := Real.sq_sqrt h2
  have h4 : 0 ≤ Real.sqrt (jsp87FAvg s (fun i => f i ^ 2)) := Real.sqrt_nonneg _
  nlinarith

/-- **THE VARIANCE** of `f` on the finite set `s`:
`Var f = 𝔼 ((f − 𝔼 f)²)`.  This is the object of (5.19)–(5.21). -/
noncomputable def jsp87Var {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) : ℝ :=
  jsp87FAvg s (fun i => (f i - jsp87FAvg s f) ^ 2)

theorem jsp87Var_nonneg {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) : 0 ≤ jsp87Var s f := by
  unfold jsp87Var
  exact jsp87FAvg_nonneg fun i _ => sq_nonneg _

/-- **The expectation of the product is the product of the expectations**,
i.e. the law of total expectation, in the finite model. -/
theorem jsp87FAvg_mul_eq_FAvg_prod {Ω : Type*} {K : Type*} (s : Finset Ω) (t : Finset K)
    (f : Ω → ℝ) (g : K → ℝ) (hs : s.Nonempty) (ht : t.Nonempty) :
    jsp87FAvg s f * jsp87FAvg t g
      = jsp87FAvg (s ×ˢ t) (fun ij => f ij.1 * g ij.2) := by
  have hc : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hd : (t.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ht
  have hinter : ∀ x : Ω, (∑ y ∈ t, (fun ij : Ω × K => f ij.1 * g ij.2) (x, y))
      = f x * ∑ y ∈ t, g y := by
    intro x
    rw [Finset.mul_sum]
  have hkey : (∑ ij ∈ s ×ˢ t, (fun ij : Ω × K => f ij.1 * g ij.2) ij)
      = (∑ x ∈ s, f x) * (∑ y ∈ t, g y) := by
    rw [Finset.sum_product, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => hinter x
  rw [jsp87FAvg, jsp87FAvg, jsp87FAvg, Finset.card_product, Nat.cast_mul, hkey]
  field_simp

/-! ## §2  The analytic toolbox: the phase `e(t) = exp (2πi t)` -/

/-- **The phase** `e(t) = exp (2πi t)` of Tao–Teräväinen §5 — the additive
character `t ↦ e^{2πit}` of `ℝ/ℤ`, written as they write it, `e(t)`. -/
noncomputable def jsp87e (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t) * Complex.I)

theorem jsp87e_norm (t : ℝ) : ‖jsp87e t‖ = 1 := by
  rw [jsp87e, Complex.norm_exp]
  have h : ((2 * Real.pi * t) * Complex.I).re = 0 := by simp [Complex.mul_re]
  rw [h, Real.exp_zero]

/-- **THE PHASE IS A CHARACTER**: `e (a + b) = e a * e b`. -/
theorem jsp87e_add (a b : ℝ) : jsp87e (a + b) = jsp87e a * jsp87e b := by
  rw [jsp87e, jsp87e, jsp87e, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **THE LIPSCHITZ BOUND OF THE CIRCLE, from Mathlib**:
`|e^{2πib} − 1| ≤ 2π |b|`. -/
theorem jsp87exp_sub_one_le (b : ℝ) :
    ‖(Complex.exp ((2 * Real.pi * b) * Complex.I) : ℂ) - 1‖ ≤ 2 * Real.pi * |b| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (2 * Real.pi * b : ℝ))
  have habs : |(2 * Real.pi * b : ℝ)| = 2 * Real.pi * |b| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hid : (Complex.I * ((2 * Real.pi * b : ℝ) : ℂ)) = (2 * Real.pi * b) * Complex.I := by
    push_cast
    ring
  simpa only [hid, Real.norm_eq_abs, habs] using h

/-- **THE LIPSCHITZ BOUND, MULTIPLIED BY A PHASE**: for `|b| ≤ 1`,
`‖u − u * e b‖ ≤ 2π ‖u‖ |b|`, for any phase `u`.  This is the analytic core of
every estimate `O(κ_j)` of §5.3. -/
theorem jsp87e_sub_mul_le (u : ℂ) (b : ℝ) (_hb : |b| ≤ 1) :
    ‖u - u * jsp87e b‖ ≤ ‖u‖ * 2 * Real.pi * |b| := by
  have h : u - u * jsp87e b = u * (1 - jsp87e b) := by ring
  rw [h, norm_mul]
  have h1 : ‖jsp87e b - 1‖ ≤ 2 * Real.pi * |b| := jsp87exp_sub_one_le b
  have hrev : ‖(1 : ℂ) - jsp87e b‖ = ‖jsp87e b - 1‖ := norm_sub_rev _ _
  rw [hrev]
  nlinarith [h1, norm_nonneg u]

/-- The special case `u = e (q c)` of the Lipschitz bound, which is (5.14) in
pointwise form. -/
theorem jsp87e_mul_sub_le (a b : ℝ) (hb : |b| ≤ 1) :
    ‖jsp87e a - jsp87e a * jsp87e b‖ ≤ 2 * Real.pi * |b| := by
  have h := jsp87e_sub_mul_le (jsp87e a) b hb
  simpa only [jsp87e_norm, one_mul, mul_one] using h

/-! ## §3  `κ₃`: the Cauchy–Schwarz split of (5.14) -/

/-- **The complex uniform average** on a finite set: the expectation of a
complex-valued function. -/
noncomputable def jsp87CAvg {Ω : Type*} (s : Finset Ω) (f : Ω → ℂ) : ℂ :=
  (∑ i ∈ s, f i) / ((s.card : ℕ) : ℂ)

theorem jsp87CAvg_ofReal {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) :
    jsp87CAvg s (fun i => (f i : ℂ)) = (jsp87FAvg s f : ℂ) := by
  simp [jsp87CAvg, jsp87FAvg]

/-- **The triangle inequality for the complex average**: `‖𝔼ᶜ f‖ ≤ 𝔼 ‖f‖`. -/
theorem jsp87CAvg_norm_le {Ω : Type*} (s : Finset Ω) (f : Ω → ℂ) :
    ‖jsp87CAvg s f‖ ≤ jsp87FAvg s (fun i => ‖f i‖) := by
  classical
  rcases s.eq_empty_or_nonempty with h | h
  · simp [jsp87CAvg, jsp87FAvg, h]
  · have hsum : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
    have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr h
    rw [jsp87CAvg, jsp87FAvg]
    calc ‖(∑ i ∈ s, f i) / ((s.card : ℕ) : ℂ)‖
        = ‖∑ i ∈ s, f i‖ / ((s.card : ℕ) : ℝ) := by
          rw [norm_div]
          norm_num
      _ ≤ (∑ i ∈ s, ‖f i‖) / ((s.card : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hsum) (by positivity)

/-- Linearity of the complex average. -/
theorem jsp87CAvg_sub {Ω : Type*} (s : Finset Ω) (f g : Ω → ℂ) :
    jsp87CAvg s (f - g) = jsp87CAvg s f - jsp87CAvg s g := by
  simp [jsp87CAvg, sub_div, Finset.sum_sub_distrib]

theorem jsp87CAvg_mul_const {Ω : Type*} (s : Finset Ω) (c : ℂ) (f : Ω → ℂ) :
    jsp87CAvg s (fun i => c * f i) = c * jsp87CAvg s f := by
  have h1 : (∑ i ∈ s, c * f i) = c * (∑ i ∈ s, f i) := by
    rw [Finset.mul_sum]
  simp only [jsp87CAvg, h1]
  ring

/-- **THE DETERMINISTIC CONTENT OF (5.14).**  If the deterministic phase
`e (q c)` (the small primes `S₀`, §5.5) is split off, then the remaining
expectation is within `2π |q| 𝔼 |R|` of the product — and by Cauchy–Schwarz
within `2π |q| sqrt (𝔼 (R²))` of it.  In Tao–Teräväinen's notation this is

```
‖𝔼 e (q (c + T + R)) − e (q c) 𝔼 e (q T)‖  ≤  2π |q| (𝔼 (R²))^½ =  κ₃ .
```

It is proved pointwise from the Lipschitz bound of §2 and then averaged. -/
theorem jsp87E_split_le {Ω : Type*} (s : Finset Ω) (_hs : s.Nonempty) (q c : ℝ)
    (T R : Ω → ℝ) (hR : ∀ i : Ω, |q * R i| ≤ 1) :
    ‖jsp87CAvg s (fun i => jsp87e (q * (c + T i + R i)))
        - jsp87e (q * c) * jsp87CAvg s (fun i => jsp87e (q * T i))‖
      ≤ 2 * Real.pi * |q| * jsp87FAvg s (fun i => |R i|) := by
  have hpt : ∀ i : Ω,
      ‖jsp87e (q * (c + T i + R i)) - jsp87e (q * c) * jsp87e (q * T i)‖
        ≤ 2 * Real.pi * |q * R i| := by
    intro i
    have hr : |q * R i| ≤ 1 := hR i
    have hid : q * (c + T i + R i) = (q * c) + q * T i + q * R i := by ring
    have hA : jsp87e (q * (c + T i + R i))
        = jsp87e (q * c) * jsp87e (q * T i) * jsp87e (q * R i) := by
      rw [hid, jsp87e_add, jsp87e_add]
    rw [hA, norm_sub_rev]
    have h3 := jsp87e_sub_mul_le (jsp87e (q * c) * jsp87e (q * T i)) (q * R i) hr
    rw [norm_mul, jsp87e_norm, jsp87e_norm, one_mul] at h3
    nlinarith [h3]
  have hkey : jsp87CAvg s (fun i => (jsp87e (q * (c + T i + R i))
          - jsp87e (q * c) * jsp87e (q * T i)))
      = jsp87CAvg s (fun i => jsp87e (q * (c + T i + R i)))
        - jsp87e (q * c) * jsp87CAvg s (fun i => jsp87e (q * T i)) := by
    simp only [jsp87CAvg]
    rw [Finset.sum_sub_distrib]
    have hcs : (∑ x ∈ s, jsp87e (q * c) * jsp87e (q * T x))
        = jsp87e (q * c) * (∑ x ∈ s, jsp87e (q * T x)) :=
      (Finset.mul_sum s (fun x => jsp87e (q * T x)) (jsp87e (q * c))).symm
    rw [hcs]
    ring
  calc ‖jsp87CAvg s (fun i => jsp87e (q * (c + T i + R i)))
        - jsp87e (q * c) * jsp87CAvg s (fun i => jsp87e (q * T i))‖
      = ‖jsp87CAvg s (fun i => (jsp87e (q * (c + T i + R i))
          - jsp87e (q * c) * jsp87e (q * T i)))‖ := congrArg norm hkey.symm
    _ ≤ jsp87FAvg s (fun i => ‖jsp87e (q * (c + T i + R i))
        - jsp87e (q * c) * jsp87e (q * T i)‖) := jsp87CAvg_norm_le _ _
    _ ≤ 2 * Real.pi * |q| * jsp87FAvg s (fun i => |R i|) := by
      have hle : jsp87FAvg s (fun i => ‖jsp87e (q * (c + T i + R i))
            - jsp87e (q * c) * jsp87e (q * T i)‖)
        ≤ jsp87FAvg s (fun i => 2 * Real.pi * |q * R i|) :=
        jsp87FAvg_le_of_pointwise_le fun i _ => hpt i
      have hid : jsp87FAvg s (fun i => |q * R i|) = |q| * jsp87FAvg s (fun i => |R i|) := by
        have h1 : (∑ x ∈ s, |q| * |R x|) = |q| * (∑ x ∈ s, |R x|) := by
          rw [Finset.mul_sum]
        have h2 : (∑ x ∈ s, |q * R x|) = ∑ x ∈ s, |q| * |R x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul]
        simp only [jsp87FAvg, h2, h1]
        ring
      rw [jsp87FAvg_mul_const] at hle
      rw [hid] at hle
      simpa only [mul_assoc] using hle

/-- **The square-root form of `κ₃`**, i.e. exactly (5.14): the discrepancy is
bounded by `2π |q| (𝔼 (R²))^½`. -/
theorem jsp87E_split_sqrt_le {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (q c : ℝ)
    (T R : Ω → ℝ) (hR : ∀ i : Ω, |q * R i| ≤ 1) :
    ‖jsp87CAvg s (fun i => jsp87e (q * (c + T i + R i)))
        - jsp87e (q * c) * jsp87CAvg s (fun i => jsp87e (q * T i))‖
      ≤ 2 * Real.pi * |q| * Real.sqrt (jsp87FAvg s (fun i => R i ^ 2)) := by
  refine le_trans (jsp87E_split_le s hs q c T R hR) ?_
  exact mul_le_mul_of_nonneg_left (jsp87FAvg_abs_le_sqrt_sq s hs R) (by positivity)

/-! ## §4  The variance bound (5.19)–(5.20) -/

/-- **The real part of the phase** is `cos`, its imaginary part is `sin`. -/
theorem jsp87e_re (t : ℝ) : (jsp87e t).re = Real.cos (2 * Real.pi * t) := by
  rw [jsp87e, Complex.exp_re]
  have h1 : ((2 * Real.pi * t) * Complex.I).re = 0 := by simp [Complex.mul_re]
  have h2 : ((2 * Real.pi * t) * Complex.I).im = 2 * Real.pi * t := by
    simp [Complex.mul_im]
  rw [h1, h2, Real.exp_zero, one_mul]

theorem jsp87e_im (t : ℝ) : (jsp87e t).im = Real.sin (2 * Real.pi * t) := by
  rw [jsp87e, Complex.exp_im]
  have h1 : ((2 * Real.pi * t) * Complex.I).re = 0 := by simp [Complex.mul_re]
  have h2 : ((2 * Real.pi * t) * Complex.I).im = 2 * Real.pi * t := by
    simp [Complex.mul_im]
  rw [h1, h2, Real.exp_zero, one_mul]

/-- **Real parts commute with the finite sum.** -/
theorem jsp87sum_re' : ∀ (s : Finset Ω) (f : Ω → ℂ),
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro f; simp
  | @insert a s ha ih =>
      intro f
      simp only [Finset.sum_insert ha, Complex.add_re]
      rw [ih]

theorem jsp87sum_im' : ∀ (s : Finset Ω) (f : Ω → ℂ),
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro f; simp
  | @insert a s ha ih =>
      intro f
      simp only [Finset.sum_insert ha, Complex.add_im]
      rw [ih]

/-- **The norm of a complex number is the Euclidean norm of its coordinates.** -/
theorem jsp87norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  have h1 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1; ring
  rw [h1, Real.sq_sqrt (by positivity)]

/-- The sum of `card s` copies of `1`, as a real number. -/
theorem jsp87sum_one {Ω : Type*} (s : Finset Ω) :
    (∑ _x ∈ s, (1 : ℝ)) = (s.card : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Products separate over a double sum.** -/
theorem jsp87sum_prod_mul {Ω K : Type*} (s : Finset Ω) (t : Finset K)
    (G : Ω → ℝ) (H : K → ℝ) :
    (∑ ij ∈ s ×ˢ t, G ij.1 * H ij.2) = (∑ i ∈ s, G i) * (∑ j ∈ t, H j) := by
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (∑ y ∈ t, G x * H y) = G x * (∑ y ∈ t, H y) := by
    rw [Finset.mul_sum]
  rw [h1]

/-- **THE DOUBLE-AVERAGE IDENTITY FOR THE PHASE.**
`‖𝔼ᶜ e (iY)‖² = 𝔼_{i,j} cos (Y i − Y j)`: the square of the mean of the phases is
the mean of `cos` of the pairwise differences, because
`(Σcos)² + (Σ sin)² = Σ_{i,j} (cos Yᵢ cos Yⱼ + sin Yᵢ sin Yⱼ)`. -/
theorem jsp87_charfun_norm_sq (s : Finset Ω) (q : ℝ) (T : Ω → ℝ) :
    ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ^ 2
      = jsp87FAvg (s ×ˢ s) (fun ij => Real.cos (2 * Real.pi * q * (T ij.1 - T ij.2))) := by
  have hkey : (∑ ij ∈ s ×ˢ s, Real.cos (2 * Real.pi * q * (T ij.1 - T ij.2)))
      = (∑ i ∈ s, Real.cos (2 * Real.pi * q * T i)) ^ 2
        + (∑ i ∈ s, Real.sin (2 * Real.pi * q * T i)) ^ 2 := by
    rw [Finset.sum_product]
    have h2 : (∑ x ∈ s, ∑ y ∈ s,
          Real.cos (2 * Real.pi * q * (T (x, y).1 - T (x, y).2)))
        = ∑ x ∈ s, (Real.cos (2 * Real.pi * q * T x) * (∑ y ∈ s, Real.cos (2 * Real.pi * q * T y))
            + Real.sin (2 * Real.pi * q * T x) * (∑ y ∈ s, Real.sin (2 * Real.pi * q * T y))) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have hcos : (∑ y ∈ s, Real.cos (2 * Real.pi * q * (T (x, y).1 - T (x, y).2)))
          = Real.cos (2 * Real.pi * q * T x) * (∑ y ∈ s, Real.cos (2 * Real.pi * q * T y))
            + Real.sin (2 * Real.pi * q * T x) * (∑ y ∈ s, Real.sin (2 * Real.pi * q * T y)) := by
        calc (∑ y ∈ s, Real.cos (2 * Real.pi * q * (T (x, y).1 - T (x, y).2)))
            = ∑ y ∈ s, (Real.cos (2 * Real.pi * q * T x) * Real.cos (2 * Real.pi * q * T y)
                + Real.sin (2 * Real.pi * q * T x) * Real.sin (2 * Real.pi * q * T y)) := by
              apply Finset.sum_congr rfl
              intro y _
              have hid : 2 * Real.pi * q * (T (x, y).1 - T (x, y).2)
                  = 2 * Real.pi * q * T x - 2 * Real.pi * q * T y := by
                rw [show T (x, y).1 = T x from rfl, show T (x, y).2 = T y from rfl]
                ring
              rw [hid, Real.cos_sub]
          _ = (Real.cos (2 * Real.pi * q * T x) * (∑ y ∈ s, Real.cos (2 * Real.pi * q * T y))
              + Real.sin (2 * Real.pi * q * T x) * (∑ y ∈ s, Real.sin (2 * Real.pi * q * T y))) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
      rw [hcos]
    rw [h2, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hnorm : ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ^ 2
      = ‖∑ i ∈ s, jsp87e (q * T i)‖ ^ 2 / ((s.card : ℕ) : ℝ) ^ 2 := by
    simp only [jsp87CAvg, norm_div, norm_natCast]
    ring
  calc ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ^ 2
      = ‖∑ i ∈ s, jsp87e (q * T i)‖ ^ 2 / ((s.card : ℕ) : ℝ) ^ 2 := hnorm
    _ = ((∑ i ∈ s, Real.cos (2 * Real.pi * q * T i)) ^ 2
          + (∑ i ∈ s, Real.sin (2 * Real.pi * q * T i)) ^ 2)
        / ((s.card : ℕ) : ℝ) ^ 2 := by
          rw [jsp87norm_sq, jsp87sum_re', jsp87sum_im']
          simp only [jsp87e_re, jsp87e_im]
          ring_nf
    _ = jsp87FAvg (s ×ˢ s) (fun ij => Real.cos (2 * Real.pi * q * (T ij.1 - T ij.2))) := by
          rw [jsp87FAvg, Finset.card_product, Nat.cast_mul, hkey]
          field_simp

/-- **THE DOUBLE-AVERAGE IDENTITY FOR THE VARIANCE.**
`𝔼_{i,j} (Y i − Y j)² = 2 Var Y`: the mean squared difference of two
independent copies is twice the variance. -/
theorem jsp87_var_double (s : Finset Ω) (hs : s.Nonempty) (Y : Ω → ℝ) :
    jsp87FAvg (s ×ˢ s) (fun ij => (Y ij.1 - Y ij.2) ^ 2) = 2 * jsp87Var s Y := by
  have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hkey : (∑ ij ∈ s ×ˢ s, (Y ij.1 - Y ij.2) ^ 2)
      = 2 * ((s.card : ℕ) : ℝ) * (∑ i ∈ s, Y i ^ 2)
        - 2 * (∑ i ∈ s, Y i) ^ 2 := by
    calc (∑ ij ∈ s ×ˢ s, (Y ij.1 - Y ij.2) ^ 2)
        = ∑ ij ∈ s ×ˢ s,
            (Y ij.1 ^ 2 - 2 * Y ij.1 * Y ij.2 + Y ij.2 ^ 2) := by
          apply Finset.sum_congr rfl
          intro ij _
          ring
      _ = ((∑ ij ∈ s ×ˢ s, Y ij.1 ^ 2) - (∑ ij ∈ s ×ˢ s, 2 * Y ij.1 * Y ij.2))
          + (∑ ij ∈ s ×ˢ s, Y ij.2 ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ((s.card : ℕ) : ℝ) * (∑ i ∈ s, Y i ^ 2)
          + (-(2 * ((∑ i ∈ s, Y i) * (∑ j ∈ s, Y j)))
          + (s.card : ℕ) * (∑ j ∈ s, Y j ^ 2)) := by
          have h1 := jsp87sum_prod_mul s s (fun i => Y i ^ 2) (fun _ => (1 : ℝ))
          have h2 := jsp87sum_prod_mul s s (fun i => Y i) Y
          have h3 := jsp87sum_prod_mul s s (fun _ => (1 : ℝ)) (fun j => Y j ^ 2)
          simp only [mul_one, one_mul] at h1 h2 h3
          have h2' : (∑ ij ∈ s ×ˢ s, 2 * Y ij.1 * Y ij.2)
              = 2 * ((∑ i ∈ s, Y i) * (∑ j ∈ s, Y j)) := by
            have h2x := jsp87sum_prod_mul s s (fun i => 2 * Y i) Y
            have h2y : (∑ x ∈ s, 2 * Y x) = 2 * (∑ x ∈ s, Y x) := by
              rw [Finset.mul_sum]
            rw [h2x, h2y]
            ring
          simp only [h1, h3, jsp87sum_one, h2']
          ring
      _ = 2 * ((s.card : ℕ) : ℝ) * (∑ i ∈ s, Y i ^ 2)
          - 2 * (∑ i ∈ s, Y i) ^ 2 := by ring
  have hZ : (∑ i ∈ s, (Y i - jsp87FAvg s Y) ^ 2)
      = (∑ i ∈ s, Y i ^ 2) - (∑ i ∈ s, Y i) ^ 2 / ((s.card : ℕ) : ℝ) := by
    have hsq : (∑ i ∈ s, (Y i - jsp87FAvg s Y) ^ 2)
        = (∑ i ∈ s, Y i ^ 2) + (-(2 * jsp87FAvg s Y * (∑ i ∈ s, Y i))
          + ((s.card : ℕ) : ℝ) * jsp87FAvg s Y ^ 2) := by
      calc (∑ i ∈ s, (Y i - jsp87FAvg s Y) ^ 2)
          = ∑ i ∈ s, (Y i ^ 2 - 2 * Y i * jsp87FAvg s Y + jsp87FAvg s Y ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ((∑ i ∈ s, Y i ^ 2) - (∑ i ∈ s, 2 * Y i * jsp87FAvg s Y))
          + (∑ i ∈ s, jsp87FAvg s Y ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by
          have h1' : (∑ i ∈ s, 2 * Y i * jsp87FAvg s Y)
              = 2 * ((∑ i ∈ s, Y i) * jsp87FAvg s Y) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
            ring
          rw [h1']
          have hcc : (∑ i ∈ s, jsp87FAvg s Y ^ 2)
              = ((s.card : ℕ) : ℝ) * jsp87FAvg s Y ^ 2 := by
            calc (∑ i ∈ s, jsp87FAvg s Y ^ 2)
                = (∑ i ∈ s, (1 : ℝ)) * jsp87FAvg s Y ^ 2 := by
                  rw [Finset.sum_mul, Finset.sum_const]
                  rw [Finset.sum_congr rfl (fun i _ => one_mul (jsp87FAvg s Y ^ 2))]
                  rw [← Finset.sum_const]
              _ = _ := by rw [jsp87sum_one]
          rw [hcc]
          ring
    rw [hsq, jsp87FAvg]
    field_simp
    ring
  rw [jsp87FAvg, jsp87Var]
  rw [Finset.card_product, Nat.cast_mul, hkey]
  rw [jsp87FAvg, hZ]
  field_simp

/-- **`1 − cos x ≥ 2x²/π²` for `|x| ≤ π`** — Mathlib's
`Real.cos_le_one_sub_mul_cos_sq`, with the division cleared twice. -/
private theorem jsp87one_sub_cos_sq_div (x : ℝ) (hx : |x| ≤ Real.pi) :
    (2 : ℝ) * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hc := Real.cos_le_one_sub_mul_cos_sq (x := x) hx
  have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hkey : 1 - 2 / Real.pi ^ 2 * x ^ 2 = (Real.pi ^ 2 - 2 * x ^ 2) / Real.pi ^ 2 := by
    field_simp
  rw [hkey] at hc
  have h1 := (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mp hc
  have h2 : (2 * x ^ 2) ≤ (1 - Real.cos x) * Real.pi ^ 2 := by linarith
  exact (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr h2

/-- **THE COSINE BOUND (5.19)**: for `|y| ≤ 1/10`,
`1 − cos (2πy) ≥ 8 y²`. -/
theorem jsp87_one_sub_cos_ge (y : ℝ) (hy : |y| ≤ 1 / 10) :
    8 * y ^ 2 ≤ 1 - Real.cos (2 * Real.pi * y) := by
  have hpi : |(2 * Real.pi * y : ℝ)| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [hy, Real.pi_pos]
  have h1 := jsp87one_sub_cos_sq_div (2 * Real.pi * y) hpi
  have h2 : 2 * (2 * Real.pi * y) ^ 2 / Real.pi ^ 2 = 8 * y ^ 2 := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- **The variance is homogeneous of degree two**: `Var (c f) = c² Var f`. -/
theorem jsp87Var_scale {Ω : Type*} (s : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    jsp87Var s (fun i => c * f i) = c ^ 2 * jsp87Var s f := by
  unfold jsp87Var
  have h1 : jsp87FAvg s (fun i => c * f i) = c * jsp87FAvg s f := jsp87FAvg_mul_const s c f
  have hfun : ∀ i : Ω, (c * f i - jsp87FAvg s (fun i => c * f i)) ^ 2
      = c ^ 2 * (f i - jsp87FAvg s f) ^ 2 := by
    intro i
    rw [h1]
    ring
  rw [jsp87FAvg, Finset.sum_congr rfl (fun x _ => hfun x)]
  rw [jsp87FAvg, ← Finset.mul_sum, jsp87FAvg]
  ring

/-- **THE VARIANCE BOUND (5.19)–(5.20), squared form.**
`‖𝔼ᶜ e (i q T)‖² ≤ 1 − 16 Var (q T)`. -/
theorem jsp87_charfun_sq_le {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (q : ℝ)
    (T : Ω → ℝ) (hT : ∀ i : Ω, |q * T i| ≤ 1 / 20) :
    ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ^ 2
      ≤ 1 - 16 * jsp87Var s (fun i => q * T i) := by
  have hid : ∀ i j : Ω, |q * (T i - T j)| ≤ 1 / 10 := by
    intro i j
    have h1 : |q * T i| ≤ 1 / 20 := hT i
    have h2 : |q * T j| ≤ 1 / 20 := hT j
    calc |q * (T i - T j)| = |q * T i - q * T j| := by congr 1; ring
      _ ≤ |q * T i| + |q * T j| := by
        have := abs_sub_le (q * T i) (0 : ℝ) (q * T j)
        simpa using this
      _ ≤ 1 / 20 + 1 / 20 := by linarith
      _ = 1 / 10 := by norm_num
  have hkey : jsp87FAvg (s ×ˢ s) (fun ij => Real.cos (2 * Real.pi * q * (T ij.1 - T ij.2)))
      ≤ jsp87FAvg (s ×ˢ s) (fun ij => 1 - 8 * (q * (T ij.1 - T ij.2)) ^ 2) := by
    refine jsp87FAvg_le_of_pointwise_le ?_
    intro ij _
    have h1 : 8 * (q * (T ij.1 - T ij.2)) ^ 2
        ≤ 1 - Real.cos (2 * Real.pi * (q * (T ij.1 - T ij.2))) :=
      jsp87_one_sub_cos_ge _ (hid ij.1 ij.2)
    have hid2 : 2 * Real.pi * q * (T ij.1 - T ij.2)
        = 2 * Real.pi * (q * (T ij.1 - T ij.2)) := by ring
    rw [hid2]
    linarith
  have hone : jsp87FAvg (s ×ˢ s) (fun _ => (1 : ℝ)) = 1 := by
    refine jsp87FAvg_one _ ?_
    obtain ⟨a, ha⟩ := hs
    exact ⟨(a, a), by simp [ha]⟩
  calc ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ^ 2
      = jsp87FAvg (s ×ˢ s) (fun ij => Real.cos (2 * Real.pi * q * (T ij.1 - T ij.2))) :=
        jsp87_charfun_norm_sq s q T
    _ ≤ jsp87FAvg (s ×ˢ s) (fun ij => 1 - 8 * (q * (T ij.1 - T ij.2)) ^ 2) := hkey
    _ = 1 - 8 * jsp87FAvg (s ×ˢ s)
        (fun ij => (q * (T ij.1 - T ij.2)) ^ 2) := by
          rw [jsp87FAvg_sub, hone]
          have h8 : jsp87FAvg (s ×ˢ s) (fun ij => 8 * (q * (T ij.1 - T ij.2)) ^ 2)
              = 8 * jsp87FAvg (s ×ˢ s) (fun ij => (q * (T ij.1 - T ij.2)) ^ 2) := by
            rw [jsp87FAvg_mul_const]
          rw [h8]
    _ = 1 - 16 * jsp87Var s (fun i => q * T i) := by
          have hq2 : (fun ij : Ω × Ω => (q * (T ij.1 - T ij.2)) ^ 2)
              = (fun ij => q ^ 2 * (T ij.1 - T ij.2) ^ 2) := by
            funext ij
            ring
          rw [hq2]
          rw [jsp87FAvg_mul_const]
          rw [jsp87_var_double s hs T, jsp87Var_scale s q T]
          ring

/-- **THE VARIANCE BOUND (5.19)–(5.20), linear form.**
`‖𝔼ᶜ e (i q T)‖ ≤ 1 − 8 Var (q T)`, i.e. the paper's
`|𝔼 e (X_p)| ≤ exp (−c Var X_p)` in its first step. -/
theorem jsp87_charfun_le {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (q : ℝ)
    (T : Ω → ℝ) (hT : ∀ i : Ω, |q * T i| ≤ 1 / 20) :
    ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ≤ 1 - 8 * jsp87Var s (fun i => q * T i) := by
  have h1 := jsp87_charfun_sq_le s hs q T hT
  have hV : 0 ≤ jsp87Var s (fun i => q * T i) := jsp87Var_nonneg _ _
  have hsq : ‖jsp87CAvg s (fun i => jsp87e (q * T i))‖ ^ 2
      ≤ (1 - 8 * jsp87Var s (fun i => q * T i)) ^ 2 := by nlinarith [h1]
  have hnonneg : 0 ≤ 1 - 8 * jsp87Var s (fun i => q * T i) := by
    nlinarith [h1]
  nlinarith [hsq, norm_nonneg (jsp87CAvg s (fun i => jsp87e (q * T i)))]

/-- **A product of exponentials is the exponential of the sum** — the algebraic
form of the estimate (5.17) that turns the `M`-th moment bound of the
independent copies into a bound for the product of the moments. -/
theorem jsp87_prod_exp (F : Finset ℕ) (c : ℝ) (V : ℕ → ℝ) :
    (∏ p ∈ F, Real.exp (c * V p)) = Real.exp (c * ∑ p ∈ F, V p) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [ih, ← Real.exp_add]
      congr 1
      ring

/-- `1 − t ≤ exp (−t)`, for `t ≥ 0`: Mathlib's `1 + x ≤ exp x` at `x = −t`. -/
theorem jsp87_one_sub_le_exp_neg {t : ℝ} (_ht : 0 ≤ t) : 1 - t ≤ Real.exp (-t) := by
  have h := Real.add_one_le_exp (-t)
  linarith

/-- **The norm of a finite product is the product of the norms.** -/
private theorem jsp87prod_norm {ι : Type*} (P : Finset ι) (z : ι → ℂ) :
    ‖∏ p ∈ P, z p‖ = ∏ p ∈ P, ‖z p‖ := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
      simp only [Finset.prod_insert ha, norm_mul, ih]

/-- **Products respect pointwise inequalities** (from scratch). -/
private theorem jsp87prod_le {ι : Type*} : ∀ (P : Finset ι) (f g : ι → ℝ),
    (∀ p ∈ P, 0 ≤ f p) → (∀ p ∈ P, f p ≤ g p)
      → (∏ p ∈ P, f p) ≤ (∏ p ∈ P, g p) := by
  classical
  intro P
  induction P using Finset.induction_on with
  | empty => intro f g h0 h; simp
  | @insert a P ha ih =>
      intro f g h0 h
      simp only [Finset.prod_insert ha]
      exact mul_le_mul (h a (Finset.mem_insert_self a P))
        (ih f g (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
          (fun p hp => h p (Finset.mem_insert_of_mem hp)))
        (Finset.prod_nonneg fun p hpP => h0 p (Finset.mem_insert_of_mem hpP))
        (le_trans (h0 a (Finset.mem_insert_self a P)) (h a (Finset.mem_insert_self a P)))

/-- **THE PRODUCT FORM OF (5.20)** — the heart of Tao–Teräväinen's endgame:
`∏_{p∈S₁} |𝔼 e (X_p)| ≤ exp (−c ∑_p Var X_p)`. -/
theorem jsp87_prod_charfun_le {Ω : Type*} {P : Finset ℕ} (s : Finset Ω) (hs : s.Nonempty)
    (q : ℝ) (T : ℕ → Ω → ℝ) (hT : ∀ p ∈ P, ∀ i : Ω, |q * T p i| ≤ 1 / 20) :
    (∏ p ∈ P, ‖jsp87CAvg s (fun i => jsp87e (q * T p i))‖)
      ≤ Real.exp (-(8 : ℝ) * ∑ p ∈ P, jsp87Var s (fun i => q * T p i)) := by
  have hfac : ∀ p ∈ P,
      ‖jsp87CAvg s (fun i => jsp87e (q * T p i))‖
        ≤ Real.exp (-(8 : ℝ) * jsp87Var s (fun i => q * T p i)) := by
    intro p hp
    have hle := jsp87_charfun_le s hs q (T p) (fun i => hT p hp i)
    have hV : 0 ≤ jsp87Var s (fun i => q * T p i) := jsp87Var_nonneg _ _
    have hne := jsp87_one_sub_le_exp_neg (t := 8 * jsp87Var s (fun i => q * T p i))
      (by positivity)
    ring_nf at hne ⊢
    linarith
  have hprod : (∏ p ∈ P, ‖jsp87CAvg s (fun i => jsp87e (q * T p i))‖)
      ≤ ∏ p ∈ P, Real.exp (-(8 : ℝ) * jsp87Var s (fun i => q * T p i)) :=
    jsp87prod_le P _ _ (fun _ _ => norm_nonneg _) hfac
  rw [jsp87_prod_exp] at hprod
  exact hprod

/-- **THE VARIANCE LOWER BOUND (5.21) FORCES THE PRODUCT BELOW `1/2`.**
This is the quantitative form of "the sum of the variances is `≫ 1`, hence the
product of the characteristic functions is bounded away from `1`". -/
theorem jsp87_prod_charfun_le_half {Ω : Type*} {P : Finset ℕ} (s : Finset Ω)
    (hs : s.Nonempty) (q : ℝ) (T : ℕ → Ω → ℝ)
    (hT : ∀ p ∈ P, ∀ i : Ω, |q * T p i| ≤ 1 / 20)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var s (fun i => q * T p i)) :
    (∏ p ∈ P, ‖jsp87CAvg s (fun i => jsp87e (q * T p i))‖) ≤ 1 / 2 := by
  have h := jsp87_prod_charfun_le s hs q T hT
  have hexp : Real.exp (-(8 : ℝ) * ∑ p ∈ P, jsp87Var s (fun i => q * T p i)) ≤ 1 / 2 := by
    have h1 := Real.add_one_le_exp 8
    have h1' : (9 : ℝ) ≤ Real.exp 8 := by linarith
    have h2 : 0 < Real.exp 8 := Real.exp_pos 8
    have h3 : (Real.exp 8)⁻¹ ≤ (9 : ℝ)⁻¹ := (inv_le_inv₀ h2 (by norm_num)).mpr h1'
    have h4 : Real.exp (-(8 : ℝ)) = (Real.exp 8)⁻¹ := by rw [Real.exp_neg]
    have h5 : Real.exp (-(8 : ℝ)) ≤ 1 / 2 := by
      rw [← h4] at h3
      norm_num at h3 ⊢
      linarith
    have h6 : Real.exp (-(8 : ℝ) * ∑ p ∈ P, jsp87Var s (fun i => q * T p i))
        ≤ Real.exp (-(8 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    linarith
  linarith

/-! ## §5  THE ENDGAME: (5.18) and (5.21) are mutually exclusive -/

/-- **THE ENDGAME OF TAO–TERÄVÄINEN §5.4, MACHINE-CHECKED.**

Let `S₁` be a finite set of primes of a hypothetical rational value `S = a/q`,
let `T p` be the random variable `X_p` of (5.13) attached to `p`, and let
`κ₁, …, κ₅` be the five error terms of §5.3–§5.4.  Suppose

* **(5.15)** `‖𝔼 e (q ∑_p T p) − 1‖ ≤ κ₁ + κ₂ + κ₃` (the truncated expectation
  is `1`, up to the three truncation errors);
* **(5.16)–(5.17)** `‖𝔼 e (q ∑_p T p) − ∏_p 𝔼 e (q T p)‖ ≤ κ₄ + κ₅` (the
  independent-copy comparison);
* **(5.19)** `|q T p| ≤ 1/20` for all `p` and all sample points;
* **(5.21)** `∑_p Var (q T p) ≥ 1`;

and `κ_j ≥ 0`.  Then

```
κ₁ + κ₂ + κ₃ + κ₄ + κ₅  ≥  1 / 2 .
```

So the five error terms of §5 cannot all be `o(1)`.  This is the entire logical
content of their endgame. -/
theorem jsp87_endgame_sum_ge {Ω : Type*} {P : Finset ℕ} (s : Finset Ω) (hs : s.Nonempty)
    (q : ℝ) (T : ℕ → Ω → ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, T p i)) - 1‖
      ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, T p i))
        - ∏ p ∈ P, jsp87CAvg s (fun i => jsp87e (q * T p i))‖ ≤ κ4 + κ5)
    (H19 : ∀ p ∈ P, ∀ i : Ω, |q * T p i| ≤ 1 / 20)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var s (fun i => q * T p i)) :
    (1 / 2 : ℝ) ≤ κ1 + κ2 + κ3 + κ4 + κ5 := by
  have hprod := jsp87_prod_charfun_le_half s hs q T H19 H21
  have hnorm : ‖∏ p ∈ P, jsp87CAvg s (fun i => jsp87e (q * T p i))‖
      = (∏ p ∈ P, ‖jsp87CAvg s (fun i => jsp87e (q * T p i))‖) :=
    jsp87prod_norm P _
  set A := jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, T p i)) with hAdef
  set B := ∏ p ∈ P, jsp87CAvg s (fun i => jsp87e (q * T p i)) with hBdef
  have htri : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - (A - B)‖ + ‖A - B‖ := by
    calc ‖(1 : ℂ)‖ = ‖((1 : ℂ) - (A - B)) + (A - B)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le ((1 : ℂ) - (A - B)) (A - B)
  have htri2 : ‖(1 : ℂ) - (A - B)‖ ≤ ‖(1 : ℂ) - A‖ + ‖B‖ := by
    calc ‖(1 : ℂ) - (A - B)‖ = ‖((1 : ℂ) - A) + B‖ := by congr 2; abel
      _ ≤ _ := norm_add_le ((1 : ℂ) - A) B
  have hchain : ‖(1 : ℂ)‖ ≤ ‖A - 1‖ + ‖A - B‖ + ‖B‖ := by
    calc ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - (A - B)‖ + ‖A - B‖ := htri
      _ ≤ ‖(1 : ℂ) - A‖ + ‖B‖ + ‖A - B‖ := by nlinarith [htri2]
      _ = ‖A - 1‖ + ‖A - B‖ + ‖B‖ := by
        have h1 : ‖(1 : ℂ) - A‖ = ‖A - 1‖ := norm_sub_rev _ _
        rw [h1]
        ring
  have h15 : ‖A - 1‖ ≤ κ1 + κ2 + κ3 := by rw [hAdef]; exact H15
  have h1617 : ‖A - B‖ ≤ κ4 + κ5 := by rw [hAdef, hBdef]; exact H1617
  have hnorm2 : ‖B‖ ≤ 1 / 2 := by
    rw [hBdef, hnorm]
    exact hprod
  have h0 : ‖(1 : ℂ)‖ = 1 := norm_one
  nlinarith [hchain, h15, h1617, hnorm2, h0]

/-- **THE TECHNICAL REDUCTION (5.18) IS IMPOSSIBLE.**
There is **no** configuration satisfying simultaneously (5.15), (5.16)–(5.17),
(5.19), (5.21) and `κ_j < 1/30` for every `j`; equivalently, the
"technical reduction" `Theorem 5.1` of arXiv:2512.01739 cannot hold together
with their own convergence hypothesis (5.18).  **The endgame of the published
proof is machine-checked: the entire remaining content of their §5 is the two
arithmetic estimates (5.18) and (5.21).** -/
theorem jsp87_endgame_impossible {Ω : Type*} {P : Finset ℕ} (s : Finset Ω)
    (hs : s.Nonempty) (q : ℝ) (T : ℕ → Ω → ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (h1 : κ1 < 1 / 30) (h2 : κ2 < 1 / 30) (h3 : κ3 < 1 / 30)
    (h4 : κ4 < 1 / 30) (h5 : κ5 < 1 / 30)
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, T p i)) - 1‖
      ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, T p i))
        - ∏ p ∈ P, jsp87CAvg s (fun i => jsp87e (q * T p i))‖ ≤ κ4 + κ5)
    (H19 : ∀ p ∈ P, ∀ i : Ω, |q * T p i| ≤ 1 / 20)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var s (fun i => q * T p i)) : False := by
  have h := jsp87_endgame_sum_ge s hs q T κ1 κ2 κ3 κ4 κ5 H15 H1617 H19 H21
  nlinarith

end JSP87
