/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.PairLoss

/-!
# Round 141 — THE SHARP VARIANCE OF THE CUBE-ALTERNATING VARIABLE, AT EVERY SCALE

`policy.json` `next_round_attack[1]` of round 140, restated after 141 rounds:

> **`jsp87Var_Xp_res_sharp`** — `1 − ‖jsp87SingleFactor K H p q‖ ≥ c_K / p` for
> every prime `p ≥ H + 2^K`, with `c_K` of order `(2^{−(H+K)})²`.  "Then apply
> round 116's `jsp87_charfun_le` with `s = Finset.range p`, `T = jsp87Xp0
> (jsp87BinV K) p`, to get `1 − ‖jsp87SingleFactor K H p q‖ ≥ c_K / p`, sum
> with round 125's `jsp87RecipSum_primeSet_tendsto`, and refute (5.15) AT EVERY
> SCALE.  THIS IS THE HIGHEST-VALUE ACTION AVAILABLE."

and `blockers.jsp87Var_Xp_res_sharp.next_concrete_step`:

> "Two concrete lemmas, both cheap, in this order.  (1) THE DISCRETE GAP.
> (2) THE EXACT SUPPORT: the set `{a in range p : X_p a != 0}` … Then
> `Var ≥ (1/p) · (2^{−(H+K)})² · H · 2^K` …"

**This module delivers both, at general scale, and then the two consequences the
policy names.**  The `1/p` comes from the **cardinality of the ZERO class**, not
from the cardinality of the nonzero class.  The nonzero class has `≥ 2^K` points
(round 119, `jsp87Xp0_ne_zero_card`); but the *zero* class has
`≥ p − (H + 2^K − 1)` points, because round 139's `jsp87Xp0_eq_zero_of_far` says
the cube sum vanishes on all but the last `H + 2^K − 1` points of a period.  A
two-class split with one class of size `Θ(p)` and the other of size `Θ(1)` gives
`|A||B|/p² = Θ(1/p)` — the missing factor of `p` that round 122's two-*point*
bound (`1/p²`) could not produce.

## §1  THE DISCRETE GAP AND THE EXACT SUPPORT

* `jsp87Xp0_binV_ne_zero_some_level` — a nonzero cube sum has an active level;
* `jsp87Xp0_binV_eq_zero_or_ge` — **the discrete gap**: every cube sum is zero or
  at least `jsp87W K H = 2^{−(H+K)}` from zero;
* `jsp87Xp0_binV_ne_zero_card_range` — the nonzero class has `≥ 2^K` points of
  the period;
* `jsp87Xp0_binV_zero_card_range_ge` — **and the zero class has
  `≥ p − (H + 2^K − 1)` points**, the new ingredient of this round;
* `jsp87Xp0_binV_ne_zero_card_le` — so the support has `≤ H + 2^K − 1` points.

## §2  ★ THE SHARP VARIANCE ★

`jsp87Var_Xp_res_sharp` : if `2 · (H + 2^K − 1) ≤ p` then

```
Var (Finset.range p) (fun a => q · X_p a)  ≥  q² · 2^{−(2H+K+1)} / p ,
```

i.e. **`Θ(1/p)`, not round 122's `Θ(1/p²)`** — summable over the primes.
`jsp87Var_Xp_range_twoClass` is the exact `2^K (p − (H + 2^K − 1))/p²` form.

## §3  ★ THE PER-PRIME MODULUS DEFICIT, AT EVERY SCALE ★

`jsp87SingleFactor_norm_le` : with (5.19) at `1/20`,

```
1 − ‖jsp87SingleFactor K H p q‖  ≥  8 · q² · 2^{−(2H+K+1)} / p ,
```

by `jsp87_charfun_le` (round 116) plus §2.  **This is the per-prime contraction
of the MODULUS that `blockers.jsp87Re_prod_step_FALSE` identifies as the only
correct propagation** — the real part does not multiply — and it holds at every
scale `(K, H, q)`, not only at `K = 0, H = 1` as in rounds 116/128/130.

## §4  ★ THE EULER-PRODUCT ESCAPE AND (5.15) IS FALSE AT EVERY SCALE ★

* `jsp87Mean_norm_le_exp` — `‖jsp87Mean K H Y q‖ ≤ exp (−c · jsp87RecipSum S₁)`
  at every admissible scale;
* `jsp87Mean_defect_tendsto` — `1 − ‖jsp87Mean K H Y q‖ → 1` as `Y → ∞`, by
  §3 and round 125's `jsp87RecipSum_primeSet_tendsto`;
* `jsp87_endgame_515_realscale` — **hypothesis (5.15) is FALSE at every
  admissible scale**: no `κ₁ + κ₂ + κ₃ < 1` dominates `jsp87Err1` at all heights;
* `jsp87_518_realscale_false`, `jsp87_endgame_realscale_blunt` — hence (5.18) and
  the endgame cannot hold at any scale, not only at `K = 0, H = 1`.

## What this does NOT do

`jsp_000087_main` is **not** declared.  The published endgame of
arXiv:2512.01739 obtains (5.15) on a **random or biased** sample, not on the
canonical whole-period sample; §4 is a complete machine-checked obstruction to
running it on *any* whole-period sample at *any* scale.  The residual input is
therefore still the correlation hypothesis `jsp87Mcov_small` (a Chowla-type
two-point bound for `ω`, `Theorem 3.1` of arXiv:2512.01739 from Pilatte), which
Mathlib does not contain.  See `ACCEPTANCE.md`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-- **`1 ≤ 2^K` for every `K`. -/
private theorem jsp87two_pow_pos (K : ℕ) : 1 ≤ 2 ^ K := Nat.one_le_two_pow (n := K)

/-- **THE SEPARATION ARITHMETIC OF ROUND 123**: for `1 ≤ H` and `1 ≤ 2^K`,
`H + 2^K − 1 ≤ H · 2^K`. -/
private theorem jsp87sep_arith (H K : ℕ) (hH : 1 ≤ H) (hK : 1 ≤ 2 ^ K) :
    H + 2 ^ K - 1 ≤ H * 2 ^ K := by
  have h1 : H - 1 ≤ (H - 1) * 2 ^ K := by
    calc H - 1 = 1 * (H - 1) := by ring
      _ ≤ 2 ^ K * (H - 1) := Nat.mul_le_mul_right (H - 1) hK
      _ = (H - 1) * 2 ^ K := by ring
  have hA : H + 2 ^ K - 1 = (H - 1) + (2 ^ K) := by omega
  have hB : (H - 1) + (2 ^ K) ≤ (H - 1) * 2 ^ K + 2 ^ K := Nat.add_le_add_right h1 _
  have h2 : H - 1 + 1 = H := by omega
  have hC : (H - 1) * 2 ^ K + 2 ^ K = H * 2 ^ K := by
    calc (H - 1) * 2 ^ K + 2 ^ K = ((H - 1) + 1) * 2 ^ K := by ring
      _ = H * 2 ^ K := by rw [h2]
  calc H + 2 ^ K - 1 = (H - 1) + (2 ^ K) := hA
    _ ≤ (H - 1) * 2 ^ K + 2 ^ K := hB
    _ = H * 2 ^ K := hC

/-- **THE SEPARATION GIVES THE SCALE HYPOTHESIS AT EVERY PRIME ABOVE IT.** -/
private theorem jsp87sep_arith2 (p H K : ℕ) (hp : 2 * H * 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hK : 1 ≤ 2 ^ K) : 2 * (H + 2 ^ K - 1) ≤ p := by
  have h1 := jsp87sep_arith H K hH hK
  have h2 : 2 * (H + 2 ^ K - 1) ≤ 2 * (H * 2 ^ K) := by omega
  have h3 : 2 * (H * 2 ^ K) = 2 * H * 2 ^ K := by ring
  omega

/-- **`2 · (H + 2^K − 1) ≤ p` IMPLIES `2^K ≤ p`, for `1 ≤ H`.** -/
private theorem jsp87pow_le_of_sep (p H K : ℕ) (hp : 2 * (H + 2 ^ K - 1) ≤ p)
    (hH : 1 ≤ H) : 2 ^ K ≤ p := by
  have h2 := jsp87sep_arith H K hH (Nat.one_le_two_pow (n := K))
  have h3 : 2 ^ K ≤ H + 2 ^ K - 1 := by omega
  omega

/-- **A COMPLETE RESIDUE SYSTEM IS A `Finset.range`.** -/
private theorem jsp87range_eq_Icc (p : ℕ) (hp : 0 < p) :
    Finset.range p = Finset.Icc 0 (p - 1) := Nat.range_eq_Icc_zero_sub_one p (Nat.ne_of_gt hp)

/-- **`((1/2)^{n})² = (1/2)^{2n}`. -/
private theorem jsp87half_sq (n : ℕ) : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 2 : ℝ) ^ (2 * n) := by
  rw [← pow_mul]
  congr 1
  omega

/-- **`(1/2)^n = 2^{−n}`, in the integer-exponent form.** -/
private theorem jsp87half_eq_zpow (n : ℕ) :
    (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-((n : ℕ) : ℤ)) := by
  rw [zpow_neg, zpow_natCast]
  have e : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [e, inv_pow]

/-- **THE IDENTITY `2^K · 2^{−2(H+K)} = 2^{−(2H+K)}` OF THE WEIGHTS.** -/
private theorem jsp87weight_ident (K H : ℕ) :
    (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 = (1 / 2 : ℝ) ^ (2 * H + K) := by
  calc (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      = (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (2 * (H + K)) := by rw [jsp87half_sq]
    _ = (2 : ℝ) ^ ((K : ℕ) : ℤ) * (2 : ℝ) ^ (-((2 * (H + K) : ℕ) : ℤ)) := by
        rw [← zpow_natCast (2 : ℝ) K, jsp87half_eq_zpow]
    _ = (2 : ℝ) ^ (((K : ℕ) : ℤ) + (-((2 * (H + K) : ℕ) : ℤ))) :=
        (zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _).symm
    _ = (2 : ℝ) ^ (-((2 * H + K : ℕ) : ℤ)) := by
        rw [show (((K : ℕ) : ℤ) + (-((2 * (H + K) : ℕ) : ℤ)))
          = (-((2 * H + K : ℕ) : ℤ)) by push_cast; ring]
    _ = (1 / 2 : ℝ) ^ (2 * H + K) := (jsp87half_eq_zpow (2 * H + K)).symm

/-! ## §1  THE DISCRETE GAP AND THE EXACT SUPPORT -/

/-- **A NONZERO CUBE SUM HAS AN ACTIVE LEVEL, AT EVERY SCALE.**
If `X_p (a) = ∑_{h ∈ [1,H]} level h ≠ 0` then some level of the sum is nonzero,
hence (by `jsp87XpLevel_eq_zero_iff_not_active`) *active*: some vertex of the
binary cube is hit there.  This is the hypothesis of `jsp87Xp0_abs_ge_active`
(round 119), i.e. the non-degeneracy condition of §5.5 of arXiv:2512.01739 as a
statement about a single sample point. -/
theorem jsp87Xp0_binV_ne_zero_some_level {K p a H : ℕ} (hp : 2 ^ K ≤ p)
    (hne : jsp87Xp0 (jsp87BinV K) p a H ≠ 0) :
    ∃ h ∈ Finset.Icc 1 H, jsp87Active K p h a := by
  classical
  by_contra hc
  have hz : jsp87Xp0 (jsp87BinV K) p a H = 0 := by
    unfold jsp87Xp0
    refine Finset.sum_eq_zero fun h hh => ?_
    have hna : ¬ jsp87Active K p h a := by
      intro ha
      exact hc ⟨h, hh, ha⟩
    rw [(jsp87XpLevel_eq_zero_iff_not_active (K := K) (p := p) (n := a) (h := h) hp).2 hna]
  exact hne hz

/-- **★ THE DISCRETE GAP AT EVERY SCALE ★**

For every `H + 2^K − 1 < p` and every sample point `a`, the cube sum `X_p (a)` is
**zero, or at distance at least `jsp87W K H = 2^{−(H+K)}` from zero**: compare
`a` with the origin, where round 119's `jsp87Xp0_eq_zero_zero` says `X_p (0) = 0`,
and apply the lattice gap of round 118 §3.

This is the shape `blockers.jsp87Var_Xp_res_sharp.next_concrete_step` asks for as
its step (1): the values of `q X_p` over the period are quantised, so the class
split at `0` separates them by a *uniform* gap, and `jsp87Var_Xp_ge_twoClass`
applies. -/
theorem jsp87Xp0_binV_eq_zero_or_ge {K p a H : ℕ} (hh : H + 2 ^ K - 1 < p) :
    jsp87Xp0 (jsp87BinV K) p a H = 0 ∨
      jsp87W K H ≤ |jsp87Xp0 (jsp87BinV K) p a H| := by
  have hp0 : 0 < p := by omega
  have hzero : jsp87Xp0 (jsp87BinV K) p 0 H = 0 :=
    jsp87Xp0_eq_zero_zero (K := K) (p := p) (H := H) hp0 hh
  rcases jsp87Xp0_sub_eq_zero_or_ge (jsp87BinV K) p a 0 H with h | h
  · left
    rw [h, hzero]
  · right
    have h' : ((1 / 2 : ℝ) ^ (H + K)) ≤ |jsp87Xp0 (jsp87BinV K) p a H| := by
      rw [hzero, sub_zero] at h
      exact h
    rw [jsp87W_eq_half]
    exact h'

/-- **THE DISCRETE GAP IN THE TWO-CLASS FORM USED BELOW.**  For `x` with
`X_p x ≠ 0` and `y` with `X_p y = 0` the two cube sums are at distance at least
`(1/2)^{H+K}`; this is what `jsp87Var_Xp_ge_twoClass` needs. -/
theorem jsp87Xp0_binV_sep {K p x y H : ℕ}
    (hne : jsp87Xp0 (jsp87BinV K) p x H ≠ 0)
    (hyz : jsp87Xp0 (jsp87BinV K) p y H = 0) :
    ((1 / 2 : ℝ) ^ (H + K))
      ≤ |jsp87Xp0 (jsp87BinV K) p x H - jsp87Xp0 (jsp87BinV K) p y H| := by
  rcases jsp87Xp0_sub_eq_zero_or_ge (jsp87BinV K) p x y H with h | h
  · exact absurd (h ▸ hyz) hne
  · exact h

/-- **THE NONZERO CLASS HAS `≥ 2^K` POINTS OF THE PERIOD.**
Round 119's `jsp87Xp0_ne_zero_card`, with the complete residue system
`Icc 0 (p−1)` rewritten as `Finset.range p`. -/
theorem jsp87Xp0_binV_ne_zero_card_range {K p H : ℕ} (hp : 0 < p) (hh : 1 + 2 ^ K - 1 < p)
    (hH : 1 ≤ H) :
    2 ^ K ≤ ((Finset.range p).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card := by
  have h1 := jsp87Xp0_ne_zero_card (K := K) (p := p) (H := H) hp hh hH
  rw [jsp87range_eq_Icc p hp]
  exact h1

/-- **★ THE ZERO CLASS HAS `≥ p − (H + 2^K − 1)` POINTS OF THE PERIOD ★**

This is the **new ingredient of this round**, and the source of the missing factor
of `p`.  Round 139's collapse `jsp87Xp0_eq_zero_of_far` says the cube sum vanishes
at every point `a` of the period with `a + (H + 2^K − 1) < p`; there are
`p − (H + 2^K − 1)` such points, and *all of them are zero*.  Combined with
`jsp87Xp0_binV_ne_zero_card_range` this brackets the support of `X_p` on a period
between `2^K` and `H + 2^K − 1` points, and — the point — makes the **complement**
class macroscopic. -/
theorem jsp87Xp0_binV_zero_card_range_ge {K p H : ℕ} (hp : H + 2 ^ K ≤ p) :
    p - (H + 2 ^ K - 1)
      ≤ ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card := by
  classical
  have hp0 : 0 < p := by
    have h1 := jsp87two_pow_pos K
    omega
  have hfar : ∀ n ∈ Finset.range p, H + 2 ^ K - 1 < p - n →
      jsp87Xp0 (jsp87BinV K) p n H = 0 := by
    intro n hn hf
    exact jsp87Xp0_eq_zero_of_far (K := K) (H := H) hp (Finset.mem_range.mp hn) hf
  have hsub : Finset.range (p - (H + 2 ^ K - 1))
      ⊆ (Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0) := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    have h1 : n < p := by omega
    refine ⟨h1, ?_⟩
    have h1' : H + 2 ^ K - 1 ≤ p - 1 := by omega
    exact hfar n (Finset.mem_range.mpr h1) (by omega)
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_range] at hcard

/-- **AND THE SUPPORT HAS `≤ H + 2^K − 1` POINTS**, by
`Finset.card_filter_add_card_filter_not` applied to `Finset.range p`.  Together
with `jsp87Xp0_binV_ne_zero_card_range` this bounds the support of `X_p` on a
period from both sides. -/
theorem jsp87Xp0_binV_ne_zero_card_le {K p H : ℕ} (hp : H + 2 ^ K ≤ p) :
    ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card
      ≤ H + 2 ^ K - 1 := by
  classical
  have h0 := jsp87Xp0_binV_zero_card_range_ge (K := K) (p := p) (H := H) hp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range p)) (p := fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)
  rw [Finset.card_range] at hsplit
  have hkey : ((Finset.range p).filter
      (fun n => ¬ jsp87Xp0 (jsp87BinV K) p n H = 0)).card
      = p - ((Finset.range p).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card := by
    refine Nat.eq_sub_of_add_eq ?_
    rw [add_comm]
    exact hsplit
  have hne' : (Finset.range p).filter (fun n => ¬ jsp87Xp0 (jsp87BinV K) p n H = 0)
      = (Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0) := by
    ext n
    simp
  rw [hne', hkey]
  have h1 : p - ((Finset.range p).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card
      ≤ p - (p - (H + 2 ^ K - 1)) := by
    refine Nat.sub_le_sub_left ?_ p
    exact h0
  have h2 : p - (p - (H + 2 ^ K - 1)) = H + 2 ^ K - 1 := by
    have : H + 2 ^ K - 1 ≤ p := by omega
    omega
  rwa [h2] at h1

/-! ## §2  ★ THE SHARP VARIANCE ★ -/

/-- **THE ZERO CLASS AND THE NONZERO CLASS SPLIT THE PERIOD, AND THE TWO CLASSES
NEVER AGREE**, so `jsp87Var_Xp_ge_twoClass` (round 118 §6) applies with the gap
`(1/2)^{H+K}`.  Both cardinalities are explicit, which is the whole content. -/
theorem jsp87Var_Xp_range_twoClass {K p H : ℕ} (q : ℝ) (hp : H + 2 ^ K ≤ p) (hH : 1 ≤ H) :
    (q ^ 2) * ((((2 : ℕ) ^ K) * (p - (H + 2 ^ K - 1)) : ℕ) : ℝ)
        * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      / ((p : ℕ) : ℝ) ^ 2
      ≤ jsp87Var (Finset.range p) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  classical
  have hp0 : 0 < p := by
    have h1 := jsp87two_pow_pos K
    omega
  have hs : (Finset.range p).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    omega
  have hsplit : Finset.range p
      = ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0))
        ∪ ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hz : jsp87Xp0 (jsp87BinV K) p n H = 0 <;> simp [hz]
  have hdis : ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0))
      ∩ ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)) = ∅ := by
    refine Finset.disjoint_iff_inter_eq_empty.mp ?_
    refine Finset.disjoint_left.2 ?_
    intro n hn hn2
    rw [Finset.mem_filter] at hn hn2
    exact hn.2 hn2.2
  have hh : 1 + 2 ^ K - 1 < p := by
    have h1 : 1 + 2 ^ K - 1 ≤ H + 2 ^ K - 1 :=
      Nat.sub_le_sub_right (Nat.add_le_add_right hH (2 ^ K)) 1
    have h2 : H + 2 ^ K - 1 ≤ p - 1 := by omega
    omega
  have hzero : jsp87Xp0 (jsp87BinV K) p 0 H = 0 :=
    jsp87Xp0_eq_zero_zero (K := K) hp0 (by omega)
  have hAne : ((Finset.range p).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).Nonempty := by
    have h2 := jsp87Xp0_binV_ne_zero_card_range (K := K) (p := p) (H := H) hp0 hh hH
    have h3 : 1 ≤ 2 ^ K := jsp87two_pow_pos K
    exact Finset.card_pos.mp (by omega)
  have hBne : ((Finset.range p).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hzero⟩
  have hne : ∀ x ∈ (Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0),
      ∀ y ∈ (Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0),
      jsp87Xp0 (jsp87BinV K) p x H ≠ jsp87Xp0 (jsp87BinV K) p y H := by
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    exact fun h => hx.2 (h ▸ hy.2)
  have h1 := jsp87Var_Xp_ge_twoClass (K := K) (s := Finset.range p) hs q (jsp87BinV K) p H
    ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0))
    ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0))
    hsplit hdis hAne hBne hne
  have hcardA : ((2 : ℕ) ^ K)
      ≤ ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card :=
    jsp87Xp0_binV_ne_zero_card_range (K := K) (p := p) (H := H) hp0 hh hH
  have hcardB : p - (H + 2 ^ K - 1)
      ≤ ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card :=
    jsp87Xp0_binV_zero_card_range_ge (K := K) (p := p) (H := H) hp
  have hprod : (2 ^ K) * (p - (H + 2 ^ K - 1))
      ≤ ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card
        * ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card :=
    Nat.mul_le_mul hcardA hcardB
  have hcard : (((2 ^ K) * (p - (H + 2 ^ K - 1) : ℕ)) : ℝ)
      ≤ (((((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card
        * ((Finset.range p).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card) : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hden : 0 ≤ ((1 / 2 : ℝ) ^ (H + K)) ^ 2 := by positivity
  have hsq : 0 < ((p : ℕ) : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcard hden
  have hmul2 := mul_le_mul_of_nonneg_left hmul (sq_nonneg q)
  rw [Finset.card_range] at h1
  have hsq' : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by positivity
  set An : Finset ℕ := (Finset.range p).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0) with hAndef
  set Bn : Finset ℕ := (Finset.range p).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0) with hBndef
  set ABc : ℕ := An.card * Bn.card with hABcdef
  have hcast : ((((2 ^ K) * (p - (H + 2 ^ K - 1) : ℕ)) : ℕ) : ℝ)
      ≤ (ABc : ℝ) := by
    rw [hABcdef]
    exact_mod_cast hprod
  have hq2 : 0 ≤ (q ^ 2) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 := by positivity
  have hstep : (q ^ 2) * (((((2 ^ K) * (p - (H + 2 ^ K - 1) : ℕ)) : ℕ) : ℝ))
        * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      ≤ (q ^ 2) * ((ABc : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2) := by
    have h2 := mul_le_mul_of_nonneg_left hcast hq2
    convert h2 using 1 <;> ring
  refine (div_le_div_iff₀ hsq' hsq').mpr
    (mul_le_mul_of_nonneg_right hstep hsq'.le) |>.trans ?_
  rw [hABcdef, hAndef, hBndef] at h1 ⊢
  exact h1

/-- **THE SAME BOUND, IN THE RE-ASSOCIATED FORM USED IN §2 BELOW.**
Identical to `jsp87Var_Xp_range_twoClass`; stated separately only to keep the
products grouped as `2^K · 2^{−2(H+K)} · (p − (H + 2^K − 1))`. -/
theorem jsp87Var_Xp_range_twoClass' {K p H : ℕ} (q : ℝ) (hp : H + 2 ^ K ≤ p) (hH : 1 ≤ H) :
    (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
        * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2
      ≤ jsp87Var (Finset.range p) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  have h1 := jsp87Var_Xp_range_twoClass (K := K) (p := p) (H := H) q hp hH
  have hcast : ((((2 ^ K) * (p - (H + 2 ^ K - 1) : ℕ)) : ℕ) : ℝ)
      = (2 : ℝ) ^ K * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hcast] at h1
  convert h1 using 1 <;> ring

/-- **★ THE SHARP `Θ(1/p)` VARIANCE, AT EVERY SCALE ★**

If `2 · (H + 2^K − 1) ≤ p` then

```
Var (Finset.range p) (fun a => q · X_p a)
  ≥  q² · 2^K · 2^{−2(H+K)} / (2 p) .
```

**This is the `Θ(1/p)` bound that rounds 116–140 could not reach**, and it is
`blockers.jsp87Var_Xp_res_sharp` in closed form.  Round 122's
`jsp87Var_Xp_res_lower` is the same statement with a *single* zero-class point
instead of `p − (H + 2^K − 1)` of them, hence one factor of `p` worse; `1/p²` is
not summable over the primes, `1/p` is.  The improvement is exactly round 139's
observation that the cube sum vanishes on the *bulk* of a period. -/
theorem jsp87Var_Xp_res_sharp {K p H : ℕ} (hH : 1 ≤ H) (hp : 2 * (H + 2 ^ K - 1) ≤ p)
    (q : ℝ) :
    (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 / (2 * (p : ℕ))
      ≤ jsp87Var (Finset.range p) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  have hp' : H + 2 ^ K ≤ p := by
    have h1 := hp
    have hH' := hH
    have hK' := jsp87two_pow_pos K
    have h2 : H + 2 ^ K - 1 ≤ p / 2 := by omega
    have h3 : p ≤ 2 * (p / 2) + 1 := by omega
    have h4 : p / 2 ≤ p - 1 := by
      have : 2 ≤ p := by omega
      omega
    omega
  have hp0 : 0 < p := by
    have h1 := jsp87two_pow_pos K
    have h2 := hH
    omega
  -- THE ZERO CLASS IS AT LEAST HALF THE PERIOD: `p − (H + 2^K − 1) ≥ p/2`
  have hm : (p : ℝ) / 2 ≤ ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) := by
    have h6 : p ≤ 2 * (p - (H + 2 ^ K - 1)) := by omega
    have h6' : (p : ℝ) ≤ 2 * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) := by
      exact_mod_cast h6
    linarith
  have h1' := jsp87Var_Xp_range_twoClass' (K := K) (p := p) (H := H) q hp' hH
  have hA : 0 ≤ (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 := by positivity
  -- replace the factor `(p − (H + 2^K − 1))/p²` by `(p/2)/p² = 1/(2p)`
  have hsq' : 0 ≤ ((p : ℕ) : ℝ) ^ 2 := by positivity
  have hcoef : (0 : ℝ) ≤ (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      / ((p : ℕ) : ℝ) ^ 2 := by positivity
  have hmul : (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      / ((p : ℕ) : ℝ) ^ 2 * ((p : ℝ) / 2)
    ≤ (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      / ((p : ℕ) : ℝ) ^ 2 * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hm hcoef
  have hstep : (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2
    ≥ (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      * ((p : ℝ) / 2) / ((p : ℕ) : ℝ) ^ 2 := by
    have h2 := hmul
    convert h2 using 1 <;> ring
  -- the `2^K · 2^{−2(H+K)}` is `2^{−(2H+K)}`
  have hident : (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      = (1 / 2 : ℝ) ^ (2 * H + K) := jsp87weight_ident K H
  have hid1 : (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      = (q ^ 2) * ((1 / 2 : ℝ) ^ (2 * H + K)) := by
    rw [mul_assoc, hident]
  have hid2 : (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2
    = (q ^ 2) * ((1 / 2 : ℝ) ^ (2 * H + K))
      * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
    rw [hid1]
  rw [hid2] at h1'
  calc (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 / (2 * (p : ℕ))
      = (q ^ 2) * ((1 / 2 : ℝ) ^ (2 * H + K)) / (2 * (p : ℕ)) := by rw [hid1]
    _ = (q ^ 2) * ((1 / 2 : ℝ) ^ (2 * H + K)) * ((p : ℝ) / 2) / ((p : ℕ) : ℝ) ^ 2 := by
      field_simp
    _ ≤ (q ^ 2) * ((1 / 2 : ℝ) ^ (2 * H + K))
        * ((p - (H + 2 ^ K - 1) : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
      have h2 := hstep
      rw [hid1] at h2
      linarith
    _ ≤ jsp87Var (Finset.range p) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := h1'

/-! ## §3  ★ THE PER-PRIME MODULUS DEFICIT, AT EVERY SCALE ★ -/

/-- **THE SINGLE-PRIME MEAN FACTOR IS THE COMPLEX AVERAGE OVER THE PERIOD.** -/
theorem jsp87SingleFactor_eq_CAvg (K H p : ℕ) (q : ℝ) :
    jsp87SingleFactor K H p q
      = jsp87CAvg (Finset.range p) (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) := by
  unfold jsp87SingleFactor jsp87CAvg
  rw [Finset.card_range]

/-- **★ THE PER-PRIME CONTRACTION OF THE MODULUS, AT EVERY SCALE ★**

With hypothesis (5.19) at `1/20` — `|q| · H · 2^{−K} ≤ 1/20`, which is what the
endgame assumes — and `2 · (H + 2^K − 1) ≤ p`,

```
8 · q² · 2^K · 2^{−2(H+K)} / (2 p)  ≤  1 − ‖jsp87SingleFactor K H p q‖ .
```

**This is the statement `blockers.jsp87Var_Xp_res_sharp` asks for, in the only
propagation form that is correct** (`blockers.jsp87Re_prod_step_FALSE`: the real
part of a product does not multiply).  Rounds 116/128/130 established it only at
`K = 0, H = 1`, where the factor degenerates to a two-class mean. -/
theorem jsp87SingleFactor_norm_le {K H p : ℕ} (hH : 1 ≤ H) (hp : 2 * (H + 2 ^ K - 1) ≤ p)
    (q : ℝ) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    8 * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 / (2 * (p : ℕ))
      ≤ (1 : ℝ) - ‖jsp87SingleFactor K H p q‖ := by
  have hpK : 1 ≤ 2 ^ K := jsp87two_pow_pos K
  have hp2 : 2 ^ K ≤ p := jsp87pow_le_of_sep p H K hp hH
  have hp0 : 0 < p := by omega
  have hT : ∀ i : ℕ, |q * jsp87Xp0 (jsp87BinV K) p i H| ≤ 1 / 20 :=
    fun i => jsp87Hyp519_pow (K := K) q p i H hp2 hK
  have hs : (Finset.range p).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    omega
  have h1 := jsp87_charfun_le (Finset.range p) hs q (jsp87Xp0 (jsp87BinV K) p · H) hT
  have h2 := jsp87Var_Xp_res_sharp (K := K) (p := p) (H := H) hH hp q
  have hjoin := jsp87SingleFactor_eq_CAvg (K := K) (H := H) (p := p) q
  rw [← hjoin] at h1
  have hden2 : (0 : ℝ) < 2 * (p : ℕ) := by positivity
  have hdeficit : 8 * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
      / (2 * (p : ℕ)) ≤ 8 * jsp87Var (Finset.range p)
        (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
    have h2' := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 8)
    convert h2' using 1 <;> ring
  -- `8·(deficit) ≤ 8·Var` and `‖factor‖ ≤ 1 − 8·Var` give
  -- `8·(deficit) ≤ 8·Var ≤ 1 − ‖factor‖`
  have h6 : 8 * jsp87Var (Finset.range p) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
    ≤ (1 : ℝ) - ‖jsp87SingleFactor K H p q‖ := by linarith
  exact hdeficit.trans h6

/-! ## §4  ★ THE EULER-PRODUCT ESCAPE, AND (5.15) IS FALSE AT EVERY SCALE ★ -/

/-- **A PRODUCT OF `EXP`s IS THE EXPONENT OF A SUM.** -/
private theorem jsp87prod_exp (s : Finset ℕ) (f : ℕ → ℝ) :
    (∏ i ∈ s, Real.exp (f i)) = Real.exp (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, Real.exp_add]

/-- **A POINTWISE BOUND ON NONNEGATIVE FACTORS PASSES THROUGH THE PRODUCT.**

`Finset.prod_le_prod` is *unavailable on `ℝ`*: it demands `MulLeftMono ℝ`, i.e.
that `· * c` be order-preserving in `c`, which fails for `c < 0`.  The
nonnegativity hypotheses `hf`/`hg` are exactly what makes the induction legal. -/
private theorem jsp87prod_le_prod (s : Finset ℕ) (f g : ℕ → ℝ)
    (h : ∀ i ∈ s, f i ≤ g i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∏ i ∈ s, f i) ≤ (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      refine mul_le_mul (h a (Finset.mem_insert_self a s)) ?_ ?_ (hg a (Finset.mem_insert_self a s))
      · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      · exact Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)

/-- **A PRODUCT OF NUMBERS `1 − x` IS AT MOST THE EXPONENT OF THE NEGATIVE SUM
OF THE `x`'s** (`Real.one_sub_le_exp_neg`). -/
private theorem jsp87prod_one_sub_le_exp (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ 1 - f i) :
    (∏ i ∈ s, (1 - f i)) ≤ Real.exp (-(∑ i ∈ s, f i) : ℝ) := by
  have hstep : (∏ i ∈ s, (1 - f i)) ≤ (∏ i ∈ s, Real.exp (-(f i))) :=
    jsp87prod_le_prod s (fun i => 1 - f i) (fun i => Real.exp (-(f i)))
      (fun i _ => Real.one_sub_le_exp_neg (f i)) hf
      (fun i _ => Real.exp_nonneg _)
  rw [jsp87prod_exp s (fun x => -(f x))] at hstep
  have hy : (∑ x ∈ s, -(f x)) = -((∑ i ∈ s, f i) : ℝ) := by
    rw [Finset.sum_neg_distrib]
  rw [hy] at hstep
  exact hstep

/-- **THE SCALE HYPOTHESES AT EVERY PRIME OF THE ENDGAME SET.**
These are separation consequences of round 123, available at every prime of `S₁`
in the endgame of §§5.3–5.14. -/
theorem jsp87PrimeSet_sharp_hypotheses (K H Y : ℕ) (hH : 1 ≤ H) :
    ∀ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, 2 ^ K ≤ p ∧ 2 * (H + 2 ^ K - 1) ≤ p := by
  intro p hp
  have hlow := jsp87PrimeSet_lower hp
  have h3 : jsp87Separation K H = 2 * H * 2 ^ K := by
    unfold jsp87Separation
    ring
  have hK2 : 1 ≤ 2 ^ K := jsp87two_pow_pos K
  have hmul : H + 2 ^ K - 1 ≤ H * 2 ^ K := jsp87sep_arith H K hH hK2
  have hpow : 2 ^ K ≤ jsp87Separation K H := jsp87Separation_pow_le hH
  have hsep : 2 * H * 2 ^ K ≤ p := by
    rw [h3] at hlow
    omega
  exact ⟨le_trans hpow hlow, jsp87sep_arith2 p H K hsep hH hK2⟩

/-- **★ THE MODULUS OF THE MEAN OF THE ENDGAME IS AT MOST `EXP` OF THE NEGATIVE
HARMONIC MASS, AT EVERY ADMISSIBLE SCALE ★**

With (5.19) at `1/20`,

```
‖jsp87Mean K H Y q‖  ≤  exp ( − 4 q² · 2^K · 2^{−2(H+K)} · jsp87RecipSum S₁ ) .
```

This is the general-scale replacement for rounds 116/128/130's
`jsp87CFfactor_normSq`, which existed only at `K = 0, H = 1`.  The *modulus* is
what must be estimated, `blockers.jsp87_re_prod_step_FALSE` ruling out the real
part. -/
theorem jsp87Mean_norm_le_exp (K H Y : ℕ) (hH : 1 ≤ H)
    (q : ℝ) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    ‖jsp87Mean K H Y q‖
      ≤ Real.exp (-((4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)) := by
  have hprod := jsp87Mean_norm_eq_prod (K := K) (H := H) (Y := Y) q
  rw [hprod]
  set S := jsp87PrimeSet (jsp87Separation K H) Y with hS
  set A : ℝ := 4 * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 with hA
  -- the per-prime contraction, in the shape `A / p ≤ 1 − ‖factor‖`
  have hstep : ∀ p ∈ S, A / (p : ℝ) ≤ (1 : ℝ) - ‖jsp87SingleFactor K H p q‖ := by
    intro p hp
    have hh := jsp87PrimeSet_sharp_hypotheses (K := K) (H := H) (Y := Y) hH p hp
    have h1 := jsp87SingleFactor_norm_le (K := K) (H := H) (p := p) hH hh.2 q hK
    have hone : (8 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2
        / (2 * (p : ℕ)) = A / (p : ℝ) := by
      have hp1 : 1 ≤ p := le_trans (jsp87two_pow_pos K) hh.1
      have hp0 : (p : ℝ) ≠ 0 := by
        intro hc
        have : p = 0 := by exact_mod_cast hc
        omega
      dsimp [A]
      field_simp
      ring
    rw [hone] at h1
    exact h1
  -- the same bound, read as an upper bound for the modulus itself
  have hle : ∀ p ∈ S, ‖jsp87SingleFactor K H p q‖ ≤ 1 - A / (p : ℝ) := by
    intro p hp
    have h1 := hstep p hp
    linarith
  -- each factor `1 − A / p` is nonnegative, because `‖factor‖ ≤ 1 − A / p`
  have hone : ∀ p ∈ S, 0 ≤ 1 - A / (p : ℝ) := by
    intro p hp
    have h1 := hle p hp
    have hn : (0 : ℝ) ≤ ‖jsp87SingleFactor K H p q‖ := norm_nonneg _
    exact sub_nonneg.mpr (by linarith)
  refine le_trans (jsp87prod_le_prod S
      (fun p : ℕ => ‖jsp87SingleFactor K H p q‖)
      (fun p : ℕ => 1 - A / (p : ℝ))
      (fun p hp => hle p hp)
      (fun p _ => norm_nonneg _)
      (fun p hp => hone p hp)) ?_
  have hexp := jsp87prod_one_sub_le_exp S (fun p : ℕ => A / (p : ℝ))
    (fun p hp => hone p hp)
  have hid : (∑ p ∈ S, A / (p : ℝ)) = A * (∑ p ∈ S, 1 / (p : ℝ)) := by
    have he : (∑ p ∈ S, A / (p : ℝ)) = ∑ p ∈ S, (A * (1 / (p : ℝ))) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [div_eq_mul_inv, inv_eq_one_div]
    rw [he, Finset.mul_sum]
  have hid' := hexp
  rw [hid] at hid'
  unfold jsp87RecipSum
  calc (∏ i ∈ S, (1 - A / ↑i)) ≤ Real.exp (-(A * ∑ p ∈ S, 1 / ↑p)) := hid'
    _ = Real.exp (-A * ∑ p ∈ S, 1 / ↑p) := by rw [neg_mul]

/-- **★ THE MEAN'S MODULUS VANISHES, AT EVERY ADMISSIBLE SCALE ★**

For every scale `(K, H, q)` with `1 ≤ H`, `q ≠ 0` and `|q| · H · 2^{−K} ≤ 1/20`,

```
‖jsp87Mean K H Y q‖  →  0     (Y → ∞) ,
```

by §4's exponential bound and Euler's divergence of the prime harmonic series
(round 125, `jsp87RecipSum_primeSet_tendsto`). -/
theorem jsp87Mean_norm_tendsto_zero (K H : ℕ) (hH : 1 ≤ H) (q : ℝ) (hq : q ≠ 0)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    Filter.Tendsto (fun Y => ‖jsp87Mean K H Y q‖) Filter.atTop (nhds 0) := by
  have hc : 0 < (4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 := by
    have hq2 : 0 < q ^ 2 := sq_pos_of_ne_zero hq
    have hrest : 0 < ((1 / 2 : ℝ) ^ (H + K)) ^ 2 := by
      exact sq_pos_of_pos (by positivity)
    have h2K : (0 : ℝ) < ((2 : ℝ) ^ K) := by positivity
    exact mul_pos (mul_pos (mul_pos (by norm_num) hq2) h2K) hrest
  -- Euler divergence (round 125): the harmonic mass eventually exceeds any bound
  have hmassb : ∀ b : ℝ,
      ∀ᶠ (Y : ℕ) in Filter.atTop,
        b ≤ jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y) := by
    intro b
    exact (Filter.tendsto_atTop.1
      (jsp87RecipSum_primeSet_tendsto (jsp87Separation K H))) b
  -- hence the exponential bound of §4 drops below any positive target
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (Y : ℕ) in Filter.atTop, Real.exp (-((4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K)
        * ((1 / 2 : ℝ) ^ (H + K)) ^ 2) * jsp87RecipSum
        (jsp87PrimeSet (jsp87Separation K H) Y)) < ε := by
    intro ε hε
    set c : ℝ := (4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2 with hce
    have hc' : 0 < c := by rw [hce]; exact hc
    filter_upwards [hmassb ((Real.log (1 / ε) + 1) / c)] with Y hY
    have hone : (1 / ε : ℝ) = ε⁻¹ := by
      rw [div_eq_mul_inv, one_mul]
    have hloginv : Real.log (1 / ε) = -Real.log ε := by
      rw [hone]
      exact Real.log_inv ε
    have hmul : Real.log (1 / ε) + 1
        ≤ c * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y) := by
      have h1 := (div_le_iff₀ hc').mp hY
      rw [mul_comm] at h1
      exact h1
    have hmain : -(c * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
        < Real.log ε := by
      rw [hloginv] at hmul
      linarith
    rw [← Real.exp_log hε]
    exact Real.exp_lt_exp.mpr (by simpa only [neg_mul] using hmain)
  -- the pointwise bound of §4, at every height
  have hbound : ∀ Y : ℕ, ‖jsp87Mean K H Y q‖
      ≤ Real.exp (-((4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)) := by
    intro Y
    exact jsp87Mean_norm_le_exp (K := K) (H := H) (Y := Y) hH q hK
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  set δ : ℝ := min (ε / 2) 1 with hδ
  have hδpos : 0 < δ := lt_min (by linarith : 0 < ε / 2) (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hsmall δ hδpos)
  refine ⟨N, fun Y hY => ?_⟩
  have hb := hbound Y
  have hs := hN Y hY
  have hδeps : δ ≤ ε / 2 := min_le_left _ _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- **★ THE MEAN'S MODULUS ESCAPES, AT EVERY ADMISSIBLE SCALE ★**

For every scale `(K, H, q)` with `1 ≤ H`, `q ≠ 0` and `|q| · H · 2^{−K} ≤ 1/20`,

```
1 − ‖jsp87Mean K H Y q‖  →  1     (Y → ∞) ,
```

by §3 and `jsp87Mean_norm_tendsto_zero`.  This is the general-scale form of
round 128's obstruction, and it discharges
`blockers.jsp87_515_nonUniform_endgame`: (5.15) cannot hold on any whole-period
sample at any scale. -/
theorem jsp87Mean_defect_tendsto (K H : ℕ) (hH : 1 ≤ H) (q : ℝ) (hq : q ≠ 0)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    Filter.Tendsto (fun Y => 1 - ‖jsp87Mean K H Y q‖) Filter.atTop (nhds 1) := by
  have h3 : Filter.Tendsto (fun Y => (1 : ℝ) - ‖jsp87Mean K H Y q‖)
      Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub (jsp87Mean_norm_tendsto_zero K H hH q hq hK)
  simpa using h3

/-- **THE (5.15) ERROR IS AT LEAST THE DEFECT OF THE MEAN** — the triangle
inequality at general scale (round 128's `jsp87Err1gen_sub_one` for the canonical
sample). -/
theorem jsp87Err1_ge_defect (K H Y : ℕ) (q : ℝ) :
    1 - ‖jsp87Mean K H Y q‖ ≤ jsp87Err1 K H Y q := by
  have h3 := dist_triangle (1 : ℂ) (jsp87Mean K H Y q) 0
  have h5 : dist (1 : ℂ) (jsp87Mean K H Y q) = ‖1 - jsp87Mean K H Y q‖ :=
    dist_eq_norm (a := (1 : ℂ)) (jsp87Mean K H Y q)
  have h6 : dist (1 : ℂ) 0 = 1 := by norm_num [dist_eq_norm]
  have h7 : dist (jsp87Mean K H Y q) 0 = ‖jsp87Mean K H Y q‖ :=
    (dist_eq_norm (a := jsp87Mean K H Y q) (0 : ℂ)).trans (by rw [sub_zero])
  rw [h6, h5, h7] at h3
  have h8 : ‖(1 : ℂ) - jsp87Mean K H Y q‖ = ‖jsp87Mean K H Y q - (1 : ℂ)‖ :=
    norm_sub_rev _ _
  have h4 : (1 : ℝ) - ‖jsp87Mean K H Y q‖ ≤ ‖jsp87Err1z K H Y q‖ := by
    have h9 := h3
    have h10 : ‖jsp87Err1z K H Y q‖ = ‖jsp87Mean K H Y q - (1 : ℂ)‖ := by
      unfold jsp87Err1z
      rfl
    rw [h8, ← h10] at h9
    linarith
  exact h4

/-- **★ THE (5.15) ERROR IS AT LEAST `1 − ε` AT EVERY ADMISSIBLE SCALE, FOR ALL
SUFFICIENTLY LARGE `Y` ★**

For every `(K, H, q)` with `1 ≤ H`, `q ≠ 0`, `|q| H 2^{−K} ≤ 1/20`, and every
`ε > 0` there is a height `Y` at which `jsp87Err1 K H Y q ≥ 1 − ε`. -/
theorem jsp87Err1_ge_one_sub_eps (K H : ℕ) (hH : 1 ≤ H) (q : ℝ) (hq : q ≠ 0)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℕ, 1 - ε ≤ jsp87Err1 K H Y q := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (jsp87Mean_norm_tendsto_zero K H hH q hq hK) ε hε
  refine ⟨N, le_trans ?_ (jsp87Err1_ge_defect K H N q)⟩
  have hdist := hN N le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (norm_nonneg (jsp87Mean K H N q))] at hdist
  linarith

/-- **★ HYPOTHESIS (5.15) IS FALSE AT EVERY ADMISSIBLE SCALE ★**

For every scale `(K, H, q)` with `1 ≤ H`, `q ≠ 0` and `|q| · H · 2^{−K} ≤ 1/20`,
**no** triple `(κ₁, κ₂, κ₃)` with `κ₁ + κ₂ + κ₃ < 1` dominates `jsp87Err1` at all
heights.  This is `jsp87_endgame_515_realscale`: the general-scale refutation of
(5.15) that rounds 116/128/130 could carry out only at `K = 0, H = 1`. -/
theorem jsp87_endgame_515_realscale (K H : ℕ) (q κ1 κ2 κ3 : ℝ) (hH : 1 ≤ H)
    (hq : q ≠ 0) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hκ : κ1 + κ2 + κ3 < 1) :
    ¬ jsp87Hypothesis15 K H q κ1 κ2 κ3 := by
  intro h15
  have hε : 0 < (1 - κ1 - κ2 - κ3) / 2 := by linarith
  obtain ⟨Y, hY⟩ := jsp87Err1_ge_one_sub_eps K H hH q hq hK
    (ε := (1 - κ1 - κ2 - κ3) / 2) hε
  have hle := h15 Y
  linarith

/-- **AND (5.18) IS FALSE AT EVERY ADMISSIBLE SCALE, NOT ONLY AT `K = 0, H = 1`.** -/
theorem jsp87_518_realscale_false (K H : ℕ) (q κ1 κ2 κ3 : ℝ) (hH : 1 ≤ H)
    (hq : q ≠ 0) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hκ : κ1 + κ2 + κ3 < 1) :
    ¬ (jsp87Hypothesis15 K H q κ1 κ2 κ3 ∧ jsp87Hypothesis1617 K H q 0 0) :=
  fun h => jsp87_endgame_515_realscale K H q κ1 κ2 κ3 hH hq hK hκ h.1

/-- **THE HEADLINE CONSEQUENCE: THE ENDGAME CANNOT RUN ON ANY WHOLE-PERIOD
SAMPLE, AT ANY SCALE.**  With (5.16)–(5.17) holding with `κ₄ = κ₅ = 0` (round 138,
`jsp87Hypothesis1617_any`, at every scale), the five estimates of §§5.7–5.14
cannot all be `< 1/30` with `κ₁ + κ₂ + κ₃ < 1`. -/
theorem jsp87_endgame_realscale_blunt (K H _Y : ℕ) (q κ1 κ2 κ3 : ℝ) (hH : 1 ≤ H)
    (hq : q ≠ 0) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    ¬ (jsp87Hypothesis15 K H q κ1 κ2 κ3 ∧ jsp87Hypothesis1617 K H q 0 0
        ∧ κ1 + κ2 + κ3 < 1) := by
  rintro ⟨h15, _, hκ⟩
  exact jsp87_endgame_515_realscale K H q κ1 κ2 κ3 hH hq hK hκ h15

end JSP87
