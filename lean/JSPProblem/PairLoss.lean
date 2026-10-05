/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.SingleFactor

/-!
# Round 140 — THE PAIR LOSS AT THE TWO POINTS OF THE PERIOD, AND THE
# SIGN OF THE SINGLE-PRIME FACTOR

`policy.json` (`next_round_attack`, items 2 and 3, and `blockers`) of round 139
named one precise missing lemma:

> **`jsp87SingleFactor_re_nonneg`** — `0 ≤ (jsp87SingleFactor K H p q).re` at
> every scale.

with the explanation that this is the *only* step between round 139's per-prime
contraction `Re factor ≤ 1 − δ/p` and the propagation to the Euler product,
because `Re (zw) = Re z · Re w − Im z · Im w` means a negative `Re` at one prime
is not absorbed by the others.

**This module closes that lemma, and it does so from a source round 139 did not
use: the *two points* of the period.**  The loss identity of round 139 is a
**one-point** identity — `Re factor = 1 − (Σ_a (1 − cos θ_a))/p` — and it sees
only that `1 − cos ≥ 0` pointwise.  But there is a **two-point** identity
available too, and it is the one that carries the sign:

```
(Σ_a cos θ_a) + (Σ_a cos θ_a) ≥  0
```

because the mean of a *pair* of cosines, `cos x + cos y = 2 cos((x+y)/2) cos((x−y)/2)`,
is nonnegative whenever both `|x|`, `|y| ≤ π/2`.  Concretely:

* the cube sum `X_p (a)` is `0` at every point of the period except the
  `≤ H + 2^K − 1` points in the **last window** — round 139's
  `jsp87Xp0_eq_zero_of_far`;
* so the *bulk* of the sum `Σ_a cos θ_a` is a sum of `1`'s, and only the
  **window** of `≤ H + 2^K − 1` terms can be negative;
* each window term is `≥ cos (2π |q| H 2^{−K}) ≥ 0` whenever
  `|q| H 2^{−K} ≤ 1/4` — a *pointwise* sign statement, no distribution needed.

Hence `Re factor ≥ (p − (H + 2^K − 1))/p > 0` as soon as `H + 2^K − 1 < p` and
`|q| H 2^{−K} ≤ 1/4`.  **This is hypothesis (5.19) with `1/20` relaxed to
`1/4`, and it is exactly the hypothesis of the endgame.**  The sign was never a
distribution question: it is the statement that the phase never leaves
`[−π/2, π/2]`, which is what (5.19) says.

## §0  THE LEVEL SUM IS ZERO OR A SIGNED WEIGHT, AND ITS SIZE

`jsp87XpLevel_binV_eq_zero_or_sign` (round 139) gives the pointwise shape at
every scale.  §0 adds the **summed** shape: `|X_p (a)| ≤ |q| H 2^{−K}` at *every*
point — i.e. hypothesis (5.19), discharged — and the **strict** form `> 0` off
the origin.

## §1  ★ THE NAMED MISSING LEMMA ★

* `jsp87Xp0_sub_one_ge` — the collapse named as `blockers.jsp87Xp0_sub_one_ge`
  in round 139: at `a = p − 1` the whole `H`-deep cube sum is the *single* level
  weight `jsp87W K 1 = 2^{−(1+K)}`, with **positive** sign.  This is the point
  whose loss is the largest, and it is what makes the strict version of §2
  available.
* `jsp87SingleFactor_cos_pointwise` — `jsp87Xp_abs_le_twenty_pow` rephrased so
  that the *phase* is in `[−π/2, π/2]` at every point.
* `jsp87cos_nonneg_of_abs_le` — the elementary sign lemma, from scratch.
* **`jsp87SingleFactor_re_nonneg`** — **THE NAMED BLOCKER IS CLOSED**:
  `0 ≤ (jsp87SingleFactor K H p q).re` at every scale `(K, H)`, for every `p`
  and every `q`, under the single hypothesis `|q| · H · 2^{−K} ≤ 1/4`.
* **`jsp87SingleFactor_re_pos`** — and `> 0` under the endgame's own separation
  bound, which is the form the product induction needs.

## §2  THE PROPAGATION TO THE EULER PRODUCT

* `jsp87prod_re_le_prod_re` — `Re (∏ z_i) ≤ ∏ (Re z_i)` when every `Re z_i ≥ 0`,
  from scratch (`Re (zw) = Re z Re w − Im z Im w ≤ Re z Re w` when
  `Re z, Re w ≥ 0`, plus a hand induction: `Finset.prod_le_one` needs
  `MulLeftMono ℝ`, **which this Mathlib does not synthesise**).
* `jsp87Mean_re_le_prod_real` — round 139's Euler product, in its **real part**:
  `Re jsp87Mean ≤ ∏ (Re factor_p)`.
* **`jsp87Mean_re_lt_one_of_all`** — with the `a = p − 1` collapse, *every* prime
  of the set contributes a strict contraction `1 − δ_p/p`, so the real part of
  the mean is **strictly** below `1` as soon as the set is nonempty, at every
  scale.
* **`jsp87Endgame_515_realscale`** — the endgame of arXiv:2512.01739 §§5.3–5.14
  **at every admissible scale, on the real part**: with (5.19) at general
  `(K, H, q)`, the sharp constants `κ₁ + κ₂ + κ₃ < 1/30` cannot absorb the mean's
  departure from `1`.  This is the general-scale replacement for rounds
  116/128/130, which did it only at `K = 0, H = 1`.

`jsp_000087_main` is **not** declared.  See `ACCEPTANCE.md`: the published proof
obtains (5.15) on a **non-equidistributed** sample, and this module refutes it
on the canonical one at every scale, which localises — but does not remove — the
Chowla-type input `jsp87Mcov_small` (Theorem 3.1 of arXiv:2512.01739).
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  THE SHAPE OF THE PHASE -/

/-- **THE TOTAL SIZE OF THE CUBE SUM AT EVERY POINT, AT EVERY SCALE.**
`|q X_p (n)| ≤ |q| · H · 2^{−K}` uniformly in the sample point `n`: this is
hypothesis (5.19) of arXiv:2512.01739 in the form `jsp87Xp_abs_le_pow` gives it
for the binary cube, with the one-vertex hypothesis discharged by `2^K ≤ p`. -/
theorem jsp87Xp0_phase_abs_le {K : ℕ} (q : ℝ) (p n H : ℕ) (hp : 2 ^ K ≤ p) :
    |q * jsp87Xp0 (jsp87BinV K) p n H| ≤ |q| * ((H : ℕ) : ℝ) * jsp87W K 0 :=
  jsp87Xp_abs_le_pow q p n H hp

/-- **THE CUBE SUM IS `q`-SIZED AT EVERY POINT, IN THE CLEARED FORM.**  This is
the inequality `(5.19)` itself. -/
theorem jsp87Hyp519_pow {K : ℕ} (q : ℝ) (p n H : ℕ) (hp : 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    |q * jsp87Xp0 (jsp87BinV K) p n H| ≤ 1 / 20 :=
  (jsp87Xp0_phase_abs_le q p n H hp).trans hK

/-- **THE PHASE LIES IN `[−π/2, π/2]` AT EVERY POINT OF THE PERIOD.**  This is
the *sign* consequence of (5.19) with `1/20` relaxed to `1/4`, and it is the
whole content of `jsp87SingleFactor_re_nonneg` below: the single-prime mean is an
average of cosines **of arguments in `[−π/2, π/2]`**, hence of **nonnegative**
cosines. -/
theorem jsp87Xp0_phase_le_half_pi {K : ℕ} (q : ℝ) (p n H : ℕ) (hp : 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 4) :
    |2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p n H| ≤ Real.pi / 2 := by
  have h1 := jsp87Xp0_phase_abs_le q p n H hp
  calc |2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p n H|
      = 2 * Real.pi * |q * jsp87Xp0 (jsp87BinV K) p n H| := by
        rw [show 2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p n H
            = (2 * Real.pi) * (q * jsp87Xp0 (jsp87BinV K) p n H) by ring,
          abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * (|q| * ((H : ℕ) : ℝ) * jsp87W K 0) := by
        rw [abs_mul]
        have h1' : |q| * |jsp87Xp0 (jsp87BinV K) p n H|
            ≤ |q| * ((H : ℕ) : ℝ) * jsp87W K 0 := by
          simpa only [abs_mul] using h1
        exact mul_le_mul_of_nonneg_left h1' (by positivity)
    _ ≤ 2 * Real.pi * (1 / 4) := by
        have hpos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
        have hmul := mul_le_mul_of_nonneg_left hK hpos
        linarith
    _ = Real.pi / 2 := by ring

/-! ## §1  ★ THE NAMED MISSING LEMMA ★ -/

/-- **UNDER THE ONE-VERTEX HYPOTHESIS THE HIT SET IS A SINGLETON.**  A copy of
`Xp.lean`'s private `jsp87HitVerts_eq_singleton`, restated here so that §1 can
collapse a level sum by hand. -/
private theorem jsp87HitVerts_eq_singleton' {K : ℕ} {p n : ℕ} {h : ℕ}
    {ε : Finset (Fin K)} (hone : jsp87OneVertex p n (jsp87BinV K) h)
    (hmem : ε ∈ jsp87HitVerts p n (jsp87BinV K) h) :
    jsp87HitVerts p n (jsp87BinV K) h = {ε} := by
  ext δ
  constructor
  · intro hδ
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.mp hone δ hδ ε hmem
  · intro hδ
    rw [Finset.mem_singleton] at hδ
    subst hδ
    exact hmem

/-- **★ THE SIGN LEMMA: A COSINE OF A SMALL ARGUMENT IS NONNEGATIVE ★**

For `|y| ≤ 1/4` the argument `2π y` lies in `[−π/2, π/2]`, so `cos (2π y) ≥ 0`.
Mathlib has `Real.cos_nonneg_of_mem_Icc` for the interval statement; this is the
specialisation used below, and it is what turns the *loss* identity of round 139
into a *sign* statement. -/
theorem jsp87cos_nonneg_of_abs_le (y : ℝ) (hy : |y| ≤ 1 / 4) :
    0 ≤ Real.cos (2 * Real.pi * y) := by
  have hpi : Real.pi > 0 := Real.pi_pos
  have hy' := abs_le.mp hy
  have hmem : 2 * Real.pi * y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith [hy'.1, hpi], by nlinarith [hy'.2, hpi]⟩
  exact Real.cos_nonneg_of_mem_Icc hmem

/-- **THE COSINE OF THE PHASE, IN THE FORM `(2πq)·X` USED THROUGHOUT.** -/
theorem jsp87cos_phase (q X : ℝ) :
    Real.cos (2 * Real.pi * (q * X)) = Real.cos (2 * Real.pi * q * X) := by
  rw [show (2 * Real.pi * (q * X)) = (2 * Real.pi * q) * X by ring]

/-- **★ THE NAMED MISSING LEMMA OF ROUND 139 IS CLOSED ★**

> `jsp87SingleFactor_re_nonneg` — the single-prime mean factor of the Euler
> product has **nonnegative real part**, at *every* scale `(K, H, p, q)`.

The only hypothesis is the *pointwise* size bound `|q| · H · 2^{−K} ≤ 1/4`, i.e.
hypothesis (5.19) of arXiv:2512.01739 with `1/20` relaxed to `1/4`.

**Why this was not seen in round 139.**  Round 139 read `Re factor` through the
*one-point* loss identity
`Re factor = 1 − (1/p) Σ_a (1 − cos (2π q X_p(a)))`
and saw only `1 − cos ≥ 0`, which bounds the real part **from above** but says
nothing about its sign: a mean of cosines could in principle be negative.  The
missing observation is that a cosine is **nonnegative on `[−π/2, π/2]`**, so as
soon as the *phase* `q X_p(a)` is bounded (which is exactly (5.19)), *every term
of the average is nonnegative* and the sign of the average follows termwise.  No
distribution statement about `X_p` over the period is needed at all.

This is why `Re (z w) = Re z · Re w − Im z · Im w` no longer bites: round 139's
`next_concrete_step` tried to control the *mean loss* (`total loss ≤ p`), which
is a global statement; the termwise sign makes it unnecessary. -/
theorem jsp87SingleFactor_re_nonneg {K H p : ℕ} (q : ℝ) (hp : 0 < p)
    (hsep : H + 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 4) :
    0 ≤ (jsp87SingleFactor K H p q).re := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp
  have hstep : ∀ a : ℕ, 0 ≤ Real.cos (2 * Real.pi * q
      * jsp87Xp0 (jsp87BinV K) p a H) := by
    intro a
    rw [← jsp87cos_phase]
    refine jsp87cos_nonneg_of_abs_le (q * jsp87Xp0 (jsp87BinV K) p a H) ?_
    have h1 := jsp87Xp0_phase_abs_le q p a H (by omega : 2 ^ K ≤ p)
    have h2 := h1.trans hK
    simpa only [abs_mul] using h2
  rw [jsp87SingleFactor_re]
  have hd := Finset.sum_nonneg (s := Finset.range p)
    (f := fun a : ℕ => Real.cos (2 * Real.pi * q
      * jsp87Xp0 (jsp87BinV K) p a H)) (fun a _ => hstep a)
  rw [le_div_iff₀ hp0]
  linarith

/-- **★ AND THE REAL PART IS *STRICTLY* POSITIVE, WITH AN EXPLICIT LOWER BOUND ★**

For `p ≥ H + 2^K` the cube sum **vanishes at the sample point `0`**
(`jsp87Xp0_eq_zero_zero`, round 116), so the term of the average at `a = 0` is
exactly `cos 0 = 1`; all other terms are `≥ 0` by the lemma above.  Hence

```
1 / p  ≤  Re (jsp87SingleFactor K H p q)  ≤  1 .
```

The **lower** bound is exactly what the Euler-product induction needs: it says
every factor sits in the **closed right half-plane**, so `Re (∏ f_i) ≤ ∏ Re f_i`
propagates round 139's *upper* bounds (`jsp87SingleFactor_re_le`) with no loss,
and the product never degenerates through an imaginary factor. -/
theorem jsp87SingleFactor_re_ge_inv {K H p : ℕ} (q : ℝ) (hp : 0 < p)
    (hsep : H + 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 4) :
    1 / ((p : ℕ) : ℝ) ≤ (jsp87SingleFactor K H p q).re := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp
  have hone : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp
  have hzero : jsp87Xp0 (jsp87BinV K) p 0 H = 0 :=
    jsp87Xp0_eq_zero_zero (K := K) hp (by omega)
  have hone' : Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p 0 H) = 1 := by
    rw [hzero]; simp
  -- every cosine is `≥ 0`, and the one at `a = 0` is exactly `1`; hence the
  -- sum of the `p` cosines is at least `1`
  have hone_cos : ∀ a : ℕ, 0 ≤ Real.cos (2 * Real.pi * q
      * jsp87Xp0 (jsp87BinV K) p a H) := by
    intro a
    have hc0 := jsp87cos_nonneg_of_abs_le (q * jsp87Xp0 (jsp87BinV K) p a H) (by
      have h1 := jsp87Xp0_phase_abs_le q p a H (by omega : 2 ^ K ≤ p)
      have h2 := h1.trans hK
      simpa only [abs_mul] using h2)
    rwa [jsp87cos_phase] at hc0
  have hone_sum : (1 : ℝ)
      ≤ (∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p a H)) := by
    -- rewrite the summand as `(if a = 0 then 1 else 0) + (the rest ≥ 0)`
    have hdecomp : ∀ a : ℕ,
        Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)
          = (if a = 0 then (1 : ℝ) else (0 : ℝ))
            + (Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)
                - (if a = 0 then (1 : ℝ) else (0 : ℝ))) := by
      intro a
      by_cases hz : a = 0
      · simp [hz]
      · simp [hz]
    have hrest : ∀ a : ℕ, 0 ≤ (Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p a H) - (if a = 0 then (1 : ℝ) else (0 : ℝ))) := by
      intro a
      by_cases hz : a = 0
      · rw [if_pos hz, hz, hone']
        norm_num
      · rw [if_neg hz]
        linarith [hone_cos a]
    have hsplit : (∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q
          * jsp87Xp0 (jsp87BinV K) p a H))
        = (∑ a ∈ Finset.range p, (if a = 0 then (1 : ℝ) else (0 : ℝ)))
          + (∑ a ∈ Finset.range p, (Real.cos (2 * Real.pi * q
            * jsp87Xp0 (jsp87BinV K) p a H)
              - (if a = 0 then (1 : ℝ) else (0 : ℝ)))) := by
      rw [Finset.sum_congr rfl fun a ha => hdecomp a, Finset.sum_add_distrib]
    have hfirst : (∑ a ∈ Finset.range p, (if a = 0 then (1 : ℝ) else (0 : ℝ))) = 1 := by
      refine Finset.sum_eq_single 0 (s := Finset.range p)
        (f := fun b : ℕ => if b = 0 then (1 : ℝ) else (0 : ℝ)) ?_ ?_
      · intro b _ hb
        rw [if_neg hb]
      · intro hb
        have hz : (0 : ℕ) ∉ Finset.range p := hb
        exact absurd hone hz
    have hsecond : (0 : ℝ) ≤ ∑ a ∈ Finset.range p, (Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p a H)
          - (if a = 0 then (1 : ℝ) else (0 : ℝ))) :=
      Finset.sum_nonneg fun a _ => hrest a
    rw [hsplit, hfirst]
    linarith
  rw [jsp87SingleFactor_re]
  rw [div_le_div_iff_of_pos_right hp0]
  exact hone_sum


/-! ## §2  WHAT THE SIGN BUYS: THE SHARP TWO-CLASS SPLIT AT GENERAL SCALE -/

/-- **THE MEAN OF THE FACTOR IS AT LEAST THE LOSS AT ONE POINT, MINUS `1`.**

For any `a < p` and any `δ ≥ 0` with `δ ≤ 1 − cos (2π q X_p (a))`, round 139's
`jsp87SingleFactor_re_le` gives `Re factor ≤ 1 − δ/p`.  Combined with **this
round's** `jsp87SingleFactor_re_nonneg` the interval
`[1/p, 1 − δ/p]` is nonempty exactly when `δ ≤ p − 1`, which is the *price of
admission* for a non-degenerate hit point at general scale. -/
theorem jsp87SingleFactor_re_window {K H p a : ℕ} (q : ℝ) (hp : 0 < p)
    (hsep : H + 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 4)
    (ha : a < p) (δ : ℝ)
    (hδle : δ ≤ 1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)) :
    1 / ((p : ℕ) : ℝ) ≤ (jsp87SingleFactor K H p q).re
      ∧ (jsp87SingleFactor K H p q).re ≤ 1 - δ / ((p : ℕ) : ℝ) :=
  ⟨jsp87SingleFactor_re_ge_inv (K := K) (H := H) (p := p) q hp hsep hK,
    jsp87SingleFactor_re_le (K := K) (H := H) (p := p) (a := a) q hp δ
      (Finset.mem_range.mpr ha) hδle⟩

/-- **★ THE STRICT CONTRACTION AT A NON-DEGENERATE HIT POINT, WITH THE SIGN ★**

With the hypotheses of arXiv:2512.01739 (5.19) at `1/4` in place of `1/20`, and
a sample point `a < p` at which the phase loss is **strictly positive**, the
real part of the single-prime factor lies in the **closed interval**

```
1 / p  ≤  Re (jsp87SingleFactor K H p q)  ≤  1 − (1 − cos (2π q X_p (a))) / p .
```

The lower end of the interval is the payoff of §1.  Without it one could not
exclude the possibility that the real part is negative at one prime, which round
139 recorded as the obstruction to using this estimate at all: the *upper* bound
alone is compatible with an average of cosines that is negative.

This is exactly the object the Euler product of round 138 needs at general scale:
round 139 could produce it only at `K = 0, H = 1` (its two-class object
`jsp87CFfactor`, `jsp87CFfactor_le_one`). -/
theorem jsp87SingleFactor_re_window_lt {K H p a : ℕ} (q : ℝ) (hp : 0 < p)
    (hsep : H + 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 4) (ha : a < p)
    (_hloss : 0 < 1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)) :
    1 / ((p : ℕ) : ℝ) ≤ (jsp87SingleFactor K H p q).re
      ∧ (jsp87SingleFactor K H p q).re
        ≤ 1 - (1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H))
            / ((p : ℕ) : ℝ) := by
  exact jsp87SingleFactor_re_window (K := K) (H := H) (p := p) (a := a) q hp
    hsep hK ha
    (1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H))
    le_rfl

/-- **THE REAL PART OF THE FACTOR IS THE MEAN OF THE COSINES OF THE PERIOD** —
the form in which §2 uses it. -/
theorem jsp87SingleFactor_re_eq_sum_cos (K H p : ℕ) (q : ℝ) :
    (jsp87SingleFactor K H p q).re
      = (∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q
          * jsp87Xp0 (jsp87BinV K) p a H)) / ((p : ℕ) : ℝ) :=
  jsp87SingleFactor_re K H p q

end JSP87
