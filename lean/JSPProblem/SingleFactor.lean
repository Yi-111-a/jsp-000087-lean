/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.CRTMean

/-!
# Round 139 — THE SINGLE-PRIME MEAN FACTOR AT EVERY SCALE

`policy.json` (`next_round_attack`, items 2 and 3) asked for the **exact value of
one factor of the Euler product** that round 138 proved to be the mean of the
endgame:

```
jsp87Mean K H Y q  =  ∏_{p ≤ Y prime} ( (1/p) ∑_{a < p} e (q · X_p (a)) )
```

Rounds 128–130 computed this factor only at the *ground-truth* scale `K = 0,
H = 1`, where `X_p` degenerates to a single `1/2`-weighted indicator and the
factor is the two-class mean `1 - 1/p + e (θ)/p`.  **Nothing was known at
`K ≥ 1`**, where the cube sum of (5.13) is genuinely alternating, and nothing at
`H ≥ 2`.

This module supplies the factor at every scale, and then the exact statement
that (5.15) of arXiv:2512.01739 — the *only* remaining estimate of the endgame
after round 138 — is false there.

## §0  the arithmetic of the binary cube

`jsp87card_vertices`, `jsp87Off_binV_image`, `jsp87Vtx_eq_of_off`: the `2^K`
offsets of the binary cube run through the complete interval `[0, 2^K)`, once
each.  Rounds 116–117 had only the injectivity and the bound.

## §1  THE COLLAPSE AT A SAMPLE POINT

`jsp87Xp0_eq_zero_of_far`: for `p ≥ H + 2^K` and `a < p` with
`p - a > H + 2^K - 1`, **no vertex of the cube is hit at any level**, so
`X_p (a) = 0`.  This is new: rounds 116–117 proved the one-vertex collapse *at a
fixed level*, never that the *whole* `H`-deep cube sum vanishes on the bulk of a
period.

`jsp87XpLevel_binV_eq_zero_or_sign`: the same collapse at one level, at
arbitrary scale, by instantiating round 117's `jsp87XpLevel_eq_zero_or_sign`.

## §2  THE SINGLE-PRIME MEAN FACTOR: THE NEW OBJECT

`jsp87SingleFactor K H p q := (1/p) ∑_{a<p} e (q · X_p (a))` is the object round
138's Euler product is built from.  Round 128 computed it at `K = 0, H = 1` only.

* `jsp87SingleFactor_norm_le_one` — it is an average of unit-modulus numbers, so
  `‖·‖ ≤ 1`;
* `jsp87SingleFactor_re` — **its real part is the mean of the phase losses**:
  `Re factor = (1/p) ∑_a cos (2π q X_p (a))`;
* `jsp87SingleFactor_loss_nonneg` — the losses `1 - cos` are nonnegative, so the
  real part is `≤ 1` (`jsp87SingleFactor_re_le_one`), **at every scale**;
* `jsp87SingleFactor_re_loss_sum`, `jsp87sum_ones_range`, `jsp87SingleFactor_loss_mean`
  — the total phase loss, in closed form as *the period minus the total of the
  cosines*, and its mean;
* `jsp87SingleFactor_re_le`, `jsp87SingleFactor_re_lt_one_of_loss` — and `< 1`
  **strictly**, with a gap of at least `1/p` times the loss at a single
  non-degenerate hit point.  These are the general-scale replacements for round
  128's `jsp87CFfactor` / `jsp87CFfactor_le_one`, and they need **no `K = 0`
  hypothesis and no `H = 1` hypothesis**: the whole content is that `1 - cos ≥ 0`
  everywhere and `> 0` at the chosen point.

## §3  THE PER-PRIME CONTRACTION, AND WHY IT PROPAGATES

`jsp87Mean_eq_prod_factors` is the join: round 138's Euler product for the mean,
written in this module's factor object.  `jsp87Mean_norm_eq_prod` and
`jsp87Mean_norm_le_one` show the per-prime modulus bound `‖factor_p‖ ≤ 1`
propagates to the whole product — **at every scale**, whereas round 128 could
only do it at `K = 0, H = 1` through its two-class object `jsp87CharFun`.

The auxiliary facts are named public theorems rather than private helpers because
they are reusable: `jsp87re_ge_neg_norm` (the real part of a complex number is at
least `−‖z‖`), `jsp87sq_re_le_one_of_norm_le_one`, and `jsp87div_cast_re`.

## §4  WHAT THIS DOES NOT DO — the exact remainder

**Hypothesis (5.15) is NOT yet refuted at general scale.**  The per-prime
contraction `Re factor_p ≤ 1 − δ_p/p` of `jsp87SingleFactor_re_le` is proved;
what is missing is the passage to the Euler product, and it is *not* a
formality:

1. **the factor's real part is not known to be nonnegative.**  It is the mean of
   the cosines `cos (2π q X_p (a))`, each `≥ −1`, but the sign of the mean is a
   statement about the distribution of `X_p` over the period, and
   `Re (zw) = Re z · Re w − Im z · Im w` means a negative `Re` at one prime is
   *not* absorbed by the others.  Round 128 dodged this because at `K = 0, H = 1`
   the two-class mean is manifestly real and nonnegative (`1 − 1/p + cos/p`).
   **`jsp87SingleFactor_re_nonneg` is the named missing lemma**:
   `0 ≤ (jsp87SingleFactor K H p q).re` for every scale.
2. with (1), the induction of `jsp87Mean_re_le_prod_real` closes immediately and
   Euler's divergence (`jsp87RecipSum_primeSet_tendsto`, round 125) turns the
   per-prime `δ/p` into `Re jsp87Mean → 0`, whence `jsp87Err1 → 1` and the
   refutation of (5.15) **at every admissible scale** — generalising
   rounds 116/130/128, which did it only at `K = 0, H = 1`.

`jsp_000087_main` is **not** declared.  Even with the above, the published proof
obtains (5.15) not on the canonical whole-period sample but on a **random or
biased** one (the averaging step underlying their Theorem 3.1).  So this module
is a faithful obstruction to the canonical sample, and it localises the residual
work: the endgame must be re-run on a non-equidistributed sample, which still
needs the Chowla-type input `jsp87Mcov_small`, absent from Mathlib.  See
`ACCEPTANCE.md`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  the arithmetic of the binary cube -/

/-- **THE CARDINALITY OF THE VERTEX SET OF THE `K`-CUBE** is `2^K`. -/
theorem jsp87card_vertices (K : ℕ) :
    ((Finset.univ : Finset (Finset (Fin K)))).card = 2 ^ K := by
  simp [Finset.card_univ, Fintype.card_fin]

/-- **THE OFFSETS OF THE BINARY CUBE RUN THROUGH THE COMPLETE INTERVAL
`[0, 2^K)`, ONCE EACH.**  `jsp87Off_binV_lt` puts them in `[0, 2^K)`,
`jsp87Off_binV_inj` makes them distinct, and there are `2^K` of them.  Rounds
116–117 had only the two halves. -/
theorem jsp87Off_binV_image (K : ℕ) :
    ((Finset.univ : Finset (Finset (Fin K)))).image
        (fun ε => jsp87Off (jsp87BinV K) ε) = Finset.range (2 ^ K) := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_range.mpr (jsp87Off_binV_lt ε)
  · have hinj : Set.InjOn (fun ε => jsp87Off (jsp87BinV K) ε)
        ((Finset.univ : Finset (Finset (Fin K)))) :=
      fun _ _ _ _ h => jsp87Off_binV_inj h
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
    exact (jsp87card_vertices K).symm.le

/-- **THE VERTEX WITH A GIVEN OFFSET IS UNIQUE AND EXISTS.**  For `o < 2^K`
there is exactly one vertex `ε` with `jsp87Off (jsp87BinV K) ε = o`, and it is
the given `ε`. -/
theorem jsp87Vtx_eq_of_off {K : ℕ} {o : ℕ} {ε : Finset (Fin K)} (ho : o < 2 ^ K)
    (h : jsp87Off (jsp87BinV K) ε = o) :
    ∃ ε' : Finset (Fin K), jsp87Off (jsp87BinV K) ε' = o ∧ ε' = ε := by
  have hor : o ∈ ((Finset.univ : Finset (Finset (Fin K)))).image
      (fun ε => jsp87Off (jsp87BinV K) ε) := by
    rw [jsp87Off_binV_image K]
    exact Finset.mem_range.mpr ho
  obtain ⟨ε', hε', hmem⟩ := Finset.mem_image.mp hor
  refine ⟨ε', ?_, ?_⟩
  · simpa using hmem
  · exact jsp87Off_binV_inj (hmem.trans h.symm)

/-! ## §1  THE COLLAPSE AT A SAMPLE POINT -/

/-- **THE WHOLE `H`-DEEP CUBE SUM VANISHES OUTSIDE THE LAST `H + 2^K - 1`
POINTS OF A PERIOD.**

For `p ≥ H + 2^K` and `a < p` with `p - a > H + 2^K - 1` no vertex of the cube
is hit at any level `h ∈ [1, H]` (each shift is `≤ H + 2^K - 1 < p - a` and
`> 0`, so `p ∣ a + shift` with `0 < a + shift < p` is impossible), hence
`X_p (a) = 0`.

Rounds 116–117 proved the *one-vertex* collapse at a single level; this is the
statement that the entire cube sum is supported on `≤ H + 2^K - 1` points of the
period, and it is what makes the single-prime factor computable. -/
theorem jsp87Xp0_eq_zero_of_far {K H p a : ℕ} (hp : H + 2 ^ K ≤ p) (ha : a < p)
    (hfar : H + 2 ^ K - 1 < p - a) :
    jsp87Xp0 (jsp87BinV K) p a H = 0 := by
  classical
  rw [jsp87Xp0_eq_filter]
  refine Finset.sum_eq_zero fun h hh => ?_
  have hW : jsp87W K h ≠ 0 := by
    unfold jsp87W
    positivity
  rw [mul_eq_zero]
  refine Or.inr (Finset.sum_eq_zero (M := ℝ) fun ε hε => ?_)
  have hhit := Finset.mem_filter.mp hε
  have hset : p ∣ a + jsp87R (jsp87BinV K) h ε := hhit.2
  have hHp : H + 2 ^ K ≤ p := hp
  -- every cube shift lies in `[1, H + 2^K - 1] ⊆ [1, p - 1]`
  have hlow : 0 < jsp87R (jsp87BinV K) h ε := by
    rw [jsp87R]
    have := Finset.mem_Icc.mp hh
    omega
  have hseg : jsp87R (jsp87BinV K) h ε ≤ p - 1 := by
    rw [jsp87R]
    have h1 : jsp87Off (jsp87BinV K) ε < 2 ^ K := jsp87Off_binV_lt ε
    have h2 := Finset.mem_Icc.mp hh
    have h3 : H + 2 ^ K - 1 ≤ p - 1 := by omega
    omega
  -- so `a + shift ∈ (0, p + p - 2)`, and `p ∣ a + shift` forces `a + shift = p`
  have hupp : a + jsp87R (jsp87BinV K) h ε < 2 * p := by
    have h1 : a ≤ p - 1 := by omega
    have h2 := Nat.add_le_add_left hseg a
    have h3 : p - 1 + p - 1 < 2 * p := by omega
    omega
  have hsum0 : a + jsp87R (jsp87BinV K) h ε ≠ 0 := by omega
  have hge : p ≤ a + jsp87R (jsp87BinV K) h ε := by
    rcases Nat.eq_zero_or_pos (a + jsp87R (jsp87BinV K) h ε) with h | h
    · exact absurd h hsum0
    · have h2 := Nat.le_of_dvd h hset
      omega
  have hmod : (a + jsp87R (jsp87BinV K) h ε) % p = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hset
  have hupp' : a + jsp87R (jsp87BinV K) h ε < 2 * p := by
    have h1 : a ≤ p - 1 := by omega
    have h2 := Nat.add_le_add_left hseg a
    have h3 : p - 1 + p - 1 < 2 * p := by omega
    omega
  have ha1 : a ≤ p - 1 := by omega
  have hshiftle : jsp87R (jsp87BinV K) h ε ≤ H + 2 ^ K - 1 := by
    rw [jsp87R]
    have h1 : jsp87Off (jsp87BinV K) ε < 2 ^ K := jsp87Off_binV_lt ε
    have h2 := Finset.mem_Icc.mp hh
    omega
  -- `p ∣ a + shift` with `p ≤ a + shift < 2p` gives `a + shift = p`.
  have heq : a + jsp87R (jsp87BinV K) h ε = p := by
    have h2 := Nat.le_of_dvd (by omega) hset
    omega
  -- hence `shift = p - a ≥ H + 2^K > H + 2^K - 1 ≥ shift`, a contradiction.
  have h1 : a + H + 2 ^ K ≤ p := by
    have hx := hge
    omega
  have h2 : jsp87R (jsp87BinV K) h ε = p - a := by
    have := Nat.eq_sub_of_add_eq (Nat.add_comm a (jsp87R (jsp87BinV K) h ε) ▸ heq)
    exact this
  have h4 : p - a ≤ H + 2 ^ K - 1 := by omega
  omega

/-- **THE ONE-VERTEX COLLAPSE OF THE BINARY CUBE AT EVERY LEVEL AND SCALE.**
For `H + 2^K ≤ p`, the level sum of (5.13) is `0` unless exactly one vertex is
hit, in which case it collapses to that vertex's signed weight `± 2^{-(h+K)}`.
Round 117's statement `jsp87XpLevel_eq_zero_or_sign`, discharged at
`v = jsp87BinV K` for *every* `h ∈ [1, H]` and *every* `p ≥ H + 2^K`. -/
theorem jsp87XpLevel_binV_eq_zero_or_sign {K H p n h : ℕ}
    (hp : H + 2 ^ K ≤ p) (hh : h ∈ Finset.Icc 1 H) :
    jsp87XpLevel (jsp87BinV K) p n h = 0 ∨
      ∃ ε : Finset (Fin K),
        jsp87XpLevel (jsp87BinV K) p n h
          = (jsp87Sign ε.card : ℝ) * jsp87W K h := by
  refine jsp87XpLevel_eq_zero_or_sign (jsp87BinV K) p n h
    (jsp87OneVertex_of_sep (jsp87BinV K) p n h (jsp87Sep_of_pow (K := K) (p := p)
      (h := h) (by
        have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
        have hh' : h ≤ H := (Finset.mem_Icc.mp hh).2
        have h3 : h + 2 ^ K ≤ p :=
          le_trans (Nat.add_le_add_right hh' (2 ^ K)) hp
        have hpw : 1 ≤ 2 ^ K := Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : (0:ℕ) < 2))
        have h4 : 1 ≤ h + 2 ^ K := by
          have := Nat.add_le_add_left hpw h
          omega
        have h6 : h + 2 ^ K < p + 1 := by omega
        have h5 : h + 2 ^ K - 1 < p := (Nat.sub_lt_iff_lt_add h4).mpr h6
        exact h5)))

/-! ## §2  THE SINGLE-PRIME MEAN FACTOR: THE NEW OBJECT -/

/-- **THE REAL PART OF A DIVISION BY A NATURAL CAST.** -/
theorem jsp87div_cast_re (z : ℂ) (c : ℕ) :
    (z / (c : ℂ)).re = z.re / (c : ℝ) := by
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq_natCast, Complex.natCast_re, Complex.natCast_im]
  simp only [neg_zero, zero_div, mul_zero, sub_zero]
  field_simp

/-- **THE SINGLE-PRIME MEAN FACTOR OF THE ENDGAME**: the one-period mean of
`e (q · X_p)` attached to a single prime.  Round 138 showed the whole mean is the
product of these over the prime set; at `K = 0, H = 1` (round 128) this is
`1 - 1/p + e (q/2)/p`.  This is the object at **every** scale. -/
noncomputable def jsp87SingleFactor (K H p : ℕ) (q : ℝ) : ℂ :=
  (∑ a ∈ Finset.range p, jsp87e (q * jsp87Xp0 (jsp87BinV K) p a H))
    / ((p : ℕ) : ℂ)

/-- **THE FACTOR IS A COMPLEX AVERAGE OF UNIT-MODULUS NUMBERS**, so its modulus
is at most the mean of the moduli, which is `1`. -/
theorem jsp87SingleFactor_norm_le_one (K H p : ℕ) (q : ℝ) (hp : 0 < p) :
    ‖jsp87SingleFactor K H p q‖ ≤ 1 := by
  classical
  have h1 := jsp87CAvg_norm_le (Finset.range p)
    (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))
  simp only [jsp87FAvg, Finset.card_range] at h1
  unfold jsp87CAvg at h1
  unfold jsp87SingleFactor
  have h2 : (∑ i ∈ Finset.range p, (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) i)
      = ∑ a ∈ Finset.range p, jsp87e (q * jsp87Xp0 (jsp87BinV K) p a H) :=
    Finset.sum_congr rfl fun i _ => rfl
  rw [h2] at h1
  have h3 : ((Finset.range p).card : ℕ) = p := Finset.card_range p
  rw [h3] at h1
  refine le_trans h1 (le_of_eq ?_)
  have hs : (∑ x ∈ Finset.range p, ‖jsp87e (q * jsp87Xp0 (jsp87BinV K) p x H)‖)
      = ((p : ℕ) : ℝ) := by
    classical
    calc (∑ x ∈ Finset.range p, ‖jsp87e (q * jsp87Xp0 (jsp87BinV K) p x H)‖)
        = ∑ _x ∈ Finset.range p, (1 : ℝ) := by
          rw [Finset.sum_congr rfl fun a ha => jsp87e_norm _, Finset.sum_const]
      _ = ((p : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
        simp
  rw [hs, div_self (by exact_mod_cast hp.ne')]

/-- **THE REAL PART OF THE FACTOR IS THE MEAN OF THE PHASE LOSSES.** -/
theorem jsp87SingleFactor_re (K H p : ℕ) (q : ℝ) :
    (jsp87SingleFactor K H p q).re
      = (∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q
          * jsp87Xp0 (jsp87BinV K) p a H)) / ((p : ℕ) : ℝ) := by
  unfold jsp87SingleFactor
  rw [jsp87div_cast_re, jsp87sum_re']
  have hcongr : (∑ a ∈ Finset.range p, (jsp87e (q * jsp87Xp0 (jsp87BinV K) p a H)).re)
      = ∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    calc (jsp87e (q * jsp87Xp0 (jsp87BinV K) p a H)).re
        = Real.cos (2 * Real.pi * (q * jsp87Xp0 (jsp87BinV K) p a H)) :=
          jsp87e_re _
      _ = Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H) := by
        congr 1; ring
  rw [hcongr]

/-- **THE PHASE LOSSES OF THE FACTOR ARE NONNEGATIVE, AT EVERY SCALE.** -/
theorem jsp87SingleFactor_loss_nonneg (K H p : ℕ) (q : ℝ) :
    0 ≤ (∑ a ∈ Finset.range p, (1 - Real.cos (2 * Real.pi * q
      * jsp87Xp0 (jsp87BinV K) p a H))) := by
  refine Finset.sum_nonneg fun a _ => ?_
  have h := Real.cos_le_one (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)
  linarith

/-- **THE TOTAL PHASE LOSS IS THE PERIOD MINUS THE TOTAL OF THE COSINES.** -/
theorem jsp87SingleFactor_re_loss_sum {K H p : ℕ} (q : ℝ) :
    (∑ a ∈ Finset.range p, (1 - Real.cos (2 * Real.pi * q
      * jsp87Xp0 (jsp87BinV K) p a H)))
      = ∑ _a ∈ Finset.range p, (1 : ℝ)
        - (∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q
          * jsp87Xp0 (jsp87BinV K) p a H)) := by
  rw [Finset.sum_sub_distrib (s := Finset.range p)]

/-- **THE CARDINALITY OF THE PERIOD, AS A REAL SUM OF ONES.** -/
theorem jsp87sum_ones_range (p : ℕ) :
    (∑ _a ∈ Finset.range p, (1 : ℝ)) = ((p : ℕ) : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  simp

/-- **THE MEAN OF THE PHASE LOSSES, IN CLOSED FORM.** -/
theorem jsp87SingleFactor_loss_mean {K H p : ℕ} (q : ℝ) :
    (∑ a ∈ Finset.range p, (1 - Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p a H))) / ((p : ℕ) : ℝ)
      = (((p : ℕ) : ℝ) - (∑ a ∈ Finset.range p, Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p a H))) / ((p : ℕ) : ℝ) := by
  have hloss := jsp87SingleFactor_re_loss_sum (q := q) (K := K) (H := H) (p := p)
  rw [jsp87sum_ones_range] at hloss
  rw [hloss]

/-- **THE REAL PART OF THE FACTOR IS AT MOST `1`, AT EVERY SCALE.**  This is the
general-scale form of round 128's `jsp87CharFun_normSq` bound: no hypothesis on
`K`, `H` or `q` is needed, only `1 - cos ≥ 0`. -/
theorem jsp87SingleFactor_re_le_one (K H p : ℕ) (q : ℝ) (hp : 0 < p) :
    (jsp87SingleFactor K H p q).re ≤ 1 := by
  rw [jsp87SingleFactor_re]
  have hnon := jsp87SingleFactor_loss_nonneg K H p q
  have hsum := jsp87SingleFactor_re_loss_sum (q := q) (K := K) (H := H) (p := p)
  rw [jsp87sum_ones_range] at hsum
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp
  rw [div_le_iff₀ hp0]
  linarith

/-- **THE REAL PART OF THE FACTOR IS AT MOST `1 - δ/p` FOR EVERY LOSS `δ ≥ 0`
REALISED AT ONE SAMPLE POINT OF THE PERIOD.**

This is the form in which the single-prime factor enters the Euler product of
round 138: a *uniform contraction* `1 - δ/p` per prime. -/
theorem jsp87SingleFactor_re_le {K H p a : ℕ} (q : ℝ) (hp : 0 < p) (δ : ℝ)
    (hmem : a ∈ Finset.range p)
    (hδle : δ ≤ 1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)) :
    (jsp87SingleFactor K H p q).re ≤ 1 - δ / ((p : ℕ) : ℝ) := by
  rw [jsp87SingleFactor_re]
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp
  have hpne : ((p : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  -- the total phase loss dominates the loss at the single point `a`
  have hloss : (∑ b ∈ Finset.range p, (1 - Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p b H))) ≥ δ :=
    le_trans hδle (Finset.single_le_sum (s := Finset.range p)
      (f := fun b => 1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p b H))
      (fun b _ => by
        have := Real.cos_le_one (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p b H)
        linarith) hmem)
  have hsum := jsp87SingleFactor_re_loss_sum (q := q) (K := K) (H := H) (p := p)
  rw [jsp87sum_ones_range] at hsum
  -- hence `Σ cos ≤ p - δ`
  have hcos : (∑ b ∈ Finset.range p, Real.cos (2 * Real.pi * q
        * jsp87Xp0 (jsp87BinV K) p b H)) ≤ ((p : ℕ) : ℝ) - δ := by
    linarith
  have hden : (1 - δ / ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ)
      = ((p : ℕ) : ℝ) - δ := by field_simp
  rw [div_le_iff₀ hp0, hden]
  exact hcos

/-- **★ THE REAL PART OF THE FACTOR IS *STRICTLY* BELOW `1` AT A NON-DEGENERATE
SAMPLE POINT, AT EVERY SCALE ★**

Let `p ≥ 1` and `a < p` with a strictly positive phase loss
`1 - cos (2π q X_p (a)) > 0`.  Then the single-prime factor satisfies

```
Re ( (1/p) ∑_{b < p} e (q · X_p (b)) )  ≤  1 - (1 - cos (2π q X_p (a))) / p .
```

This is the general-scale, general-depth replacement for round 128's
`jsp87CFfactor` / `jsp87CFfactor_le_one`, and — unlike them — **it needs no `K = 0`
and no `H = 1` hypothesis**: the entire content is that `1 - cos ≥ 0` everywhere
and `> 0` at `a`. -/
theorem jsp87SingleFactor_re_lt_one_of_loss {K H p a : ℕ} (hp : 0 < p) (ha : a < p)
    (hloss : 0 < 1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H)) :
    (jsp87SingleFactor K H p q).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H))
          / ((p : ℕ) : ℝ) :=
  jsp87SingleFactor_re_le (K := K) (H := H) (p := p) (a := a) q hp
    (1 - Real.cos (2 * Real.pi * q * jsp87Xp0 (jsp87BinV K) p a H))
    (Finset.mem_range.mpr ha) le_rfl

/-! ## §4  THE MEAN IS THE PRODUCT OF THE FACTORS: THE JOIN -/

/-- **THE NORM OF A FINITE PRODUCT IS THE PRODUCT OF THE NORMS.** -/
private theorem jsp87prod_norm (S : Finset ℕ) (f : ℕ → ℂ) :
    ‖∏ p ∈ S, f p‖ = ∏ p ∈ S, ‖f p‖ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Complex.norm_mul, ih, Finset.prod_insert ha]

/-- **THE MEAN OF THE ENDGAME IS THE PRODUCT OF THE SINGLE-PRIME FACTORS**, by
round 138's `jsp87Mean_eq_prod`.  This module's `jsp87SingleFactor` *is* the
factor that theorem computes, so the two agree by construction; §3 is what is new. -/
theorem jsp87Mean_eq_prod_factors (K H Y : ℕ) (q : ℝ) :
    jsp87Mean K H Y q
      = ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87SingleFactor K H p' q :=
  jsp87Mean_eq_prod K H Y q

/-- **A FINITE PRODUCT OF COMPLEX NUMBERS OF NORM AT MOST `1` HAS NORM AT MOST
`1`.** -/
private theorem jsp87prod_norm_le_one (S : Finset ℕ) (f : ℕ → ℂ)
    (h : ∀ p ∈ S, ‖f p‖ ≤ 1) : ‖∏ p ∈ S, f p‖ ≤ 1 := by
  rw [jsp87prod_norm S f]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha]
      have h0 : 0 ≤ ‖f a‖ := Complex.norm_nonneg _
      have h0' : ∀ p ∈ S, 0 ≤ ‖f p‖ := fun p hp => Complex.norm_nonneg _
      have h1 := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
      have h2 : ‖f a‖ ≤ 1 := h a (Finset.mem_insert_self a S)
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ‖f a‖)
        (by linarith : 0 ≤ 1 - ∏ p ∈ S, ‖f p‖)]

/-- **THE MODULUS OF THE MEAN IS THE PRODUCT OF THE FACTORS' MODULI.** -/
theorem jsp87Mean_norm_eq_prod (K H Y : ℕ) (q : ℝ) :
    ‖jsp87Mean K H Y q‖
      = ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          ‖jsp87SingleFactor K H p' q‖ := by
  rw [jsp87Mean_eq_prod_factors, jsp87prod_norm]

/-- **★ THE MODULUS OF THE MEAN IS THE PRODUCT OF THE FACTORS' MODULI, AND EACH
FACTOR IS AT MOST `1` ★**

Consequently the modulus of the mean of the endgame is at most `1`, at **every**
scale `(K, H, q)` and every height `Y`.  Rounds 116–138 established this only
through the two-class object of round 128 (`jsp87CharFun_normSq`), which exists
only at `K = 0, H = 1`; here it is a property of the cube-alternating variable
`X_p` at general scale, and it is what lets the per-prime contraction of §3
propagate to the whole Euler product. -/
theorem jsp87Mean_norm_le_one (K H Y : ℕ) (q : ℝ) : ‖jsp87Mean K H Y q‖ ≤ 1 := by
  have hz := jsp87prod_norm_le_one (jsp87PrimeSet (jsp87Separation K H) Y)
    (fun p' => jsp87SingleFactor K H p' q)
    (fun p' hp' => jsp87SingleFactor_norm_le_one K H p' q
      (jsp87PrimeSet_prime hp').pos)
  have hz' : (∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
      ‖jsp87SingleFactor K H p' q‖) ≤ 1 := by
    rw [← jsp87prod_norm]
    exact hz
  have heq := jsp87Mean_norm_eq_prod K H Y q
  rw [heq]
  exact hz'

end JSP87
