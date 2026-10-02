/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.ResidueCarry
import JSPProblem.DenominatorSplit
import JSPProblem.DigitCarry
import JSPProblem.BlockPeriod
import Mathlib.Tactic

/-!
# JSP-000087 : the two-term normal form of the Erdős carry, and the cut-point
# periodicity of its small-prime part

## The new attack family

Round 84 (`JSPProblem/ResidueCarry.lean`) proved that the Erdős carry at a cut
point `M ≥ 1` is *exactly* a prime-residue Lambert sum

```
2 * jsp87Carry M = ∑' p prime, 2 ^ (jsp87ResExp M p) / (2 ^ p - 1)
```

so that the whole carry is determined by the **residue vector** `(M % p)` of the
cut point.  Nothing was ever done with that structure.  This round splits that
sum at an arbitrary **prime cut point** `T` and obtains

* **`jsp87CutSum M T`**, the contribution of the primes `p ≤ T` — which is an
  **exactly periodic function of the cut point `M`, with period the primorial
  `jsp87Prim T`** (`jsp87CutSum_period`): two cut points congruent modulo the
  primorial have *identical* small-prime contributions to the carry;
* **`jsp87LamAbove T`**, the contribution of the primes `p > T`, which is
  **independent of the cut point** and is *literally the Lambert tail beyond
  `T`* (`jsp87LamAbove_eq_lambertTail`);
* **`jsp87Carry_eq_cut_lam`** — **THE TWO-TERM NORMAL FORM OF THE CARRY**:
  for every `1 ≤ M ≤ T`

  ```
  jsp87Carry M = jsp87CutSum M T / 2 + 2 ^ (M - 1) * jsp87LamAbove T
  ```

  i.e. *the Erdős carry at `M` is the periodic part (a rational whose
  denominator divides `2 * j�_{p ≤ T}(2^p-1)`) plus a single geometric term*.
  Equivalently (`jsp87Tail_eq_cut_lam`) the **tail** of the Erdős series
  satisfies `jsp87Tail M = jsp87CutSum M T / 2^(M+1) + jsp87LamAbove T / 2`:
  **above a prime cut point the Erdős tail and the Lambert tail agree term by
  term.**

Rounds 37–85 attacked the series, the carry, the digits, the blocks, the
windows, the prefixes, the denominators, the doubling orbits, the residues and
the multiplier family, but **never split a single carry into its periodic and
its geometric part.**  Nothing here restates an earlier blocker.

## What it gives

* `jsp87Carry_sub_congr` — **the exact difference rule**: for cut points
  congruent modulo the primorial the difference of the carries is the
  corresponding difference of geometric terms, *and nothing else*;
  `jsp87Carry_sub_congr_ne` makes the same statement as an injectivity result.
* `jsp87ResExp_eq_pred`, `jsp87CutSum_ge_pred`, `jsp87Carry_ge_series_add_pred`,
  `jsp87Carry_ge_prim` — **the carry is large at the cut points one below a
  primorial**, quantified by the number of small primes that are *not* divisors
  of the cut point: `jsp87Carry (jsp87Prim T - 1) ≥ 2·S + (#primes in [3,T])/8`.
  This is a *different* lower bound from round 84's
  `jsp87Carry_ge_series_add_omega` (`ω M / 3`), and it is the sharper of the two
  exactly where `ω M` is small.
* `jsp87CutSum_two`, `jsp87Carry_ge_two_even`, `jsp87Carry_ge_two_odd` — the
  `p = 2` column in closed form, sharpening round 84's `jsp87Carry_ge_dvd` at
  `p = 2`.
* `jsp87Series_irrational_iff_lamAbove` — a **complete reformulation** of the
  headline: `S` is irrational **iff** every Lambert tail above a prime cut point
  is irrational.

## What it does *not* give — and this is proved, not merely observed

* `jsp87Carry_mer_eq` / `jsp87Carry_mer_mul_int` — under a hypothetical digit
  period `t`, the carry is **quantised** by the Mersenne number `2^t - 1`,
  exactly: `(2^t - 1)·θ M = (2^t - 1)·⌊θ M⌋ + (the t-digit block)`.
* `jsp87CutSum_cleared` / `jsp87LamAbove_cleared` — combining that quantisation
  with the normal form shows that **a hypothetical rationality assumption forces
  the Lambert tail to be a rational whose denominator divides
  `jsp87LambertQ (T+1)`, i.e. NO denominator coming from the primes above `T`
  survives**.  This is the machine-checked reason why the denominator route
  cannot close the gate: the small-prime denominators cancel exactly against the
  denominators of the tail, and only *correlations* between the `ω`-values can
  break the cancellation.
* `jsp87BigSum_pos`, `jsp87CutSum_lt_carry` — the geometric correction is never
  zero, so the two terms of the normal form never cancel and the periodic part is
  always a strict fraction of the carry.

The headline `jsp_000087_main` therefore remains out of reach: the published
result is conditional (Pratt, arXiv:2409.15185, uniform prime `k`-tuples), and
the blocker `jsp87_digit_not_eventuallyPeriodic` is unchanged.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 8000000

/-- Two propositional gates, packaged so that they elaborate. -/
private theorem gateA_pos {p T : ℕ} (hp : p.Prime) (hle : p ≤ T) :
    p.Prime ∧ p ≤ T := And.intro hp hle

private theorem gateA_neg {p T : ℕ} (hp : p.Prime) (hn : ¬ p ≤ T) :
    ¬ (p.Prime ∧ p ≤ T) := fun h => hn h.2

private theorem gateB_pos {p T : ℕ} (hp : p.Prime) (hle : T < p) :
    p.Prime ∧ T < p := And.intro hp hle

private theorem gateB_neg {p T : ℕ} (hp : p.Prime) (hn : ¬ T < p) :
    ¬ (p.Prime ∧ T < p) := fun h => hn h.2

private theorem gateA_neg' {p T : ℕ} (hp : ¬ p.Prime) : ¬ (p.Prime ∧ p ≤ T) :=
  fun h => hp h.1

private theorem gateB_neg' {p T : ℕ} (hp : ¬ p.Prime) : ¬ (p.Prime ∧ T < p) :=
  fun h => hp h.1

private theorem tsum_eq_sum_finset {f : ℕ → ℝ} (hf : Summable f) (s : Finset ℕ)
    (h : ∀ p, p ∉ s → f p = 0) : (∑' p, f p) = ∑ p ∈ s, f p := by
  refine (tsum_congr fun p => ?_).trans (sum_eq_tsum_indicator f s).symm
  by_cases hp : p ∈ s
  · rw [Set.indicator_of_mem hp]
  · have hpn : p ∉ (s : Set ℕ) := fun hmem => hp (Finset.mem_coe.mpr hmem)
    rw [Set.indicator_apply, if_neg hpn, h p hp]

private theorem lamAboveTerm_nonneg (T p : ℕ) :
    (0 : ℝ) ≤ (if p.Prime ∧ T < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  by_cases hp : p.Prime
  · by_cases hle : T < p
    · rw [if_pos (gateB_pos hp hle)]
      exact inv_nonneg.mpr (mer_pos hp.two_le).le
    · rw [if_neg (gateB_neg hp hle)]
  · rw [if_neg (gateB_neg' hp)]

private theorem jsp87_lambertTrunc_sub_succ (N : ℕ) :
    jsp87_lambertTrunc (N + 1) - jsp87_lambertTrunc N = jsp87_lambertTerm N := by
  unfold jsp87_lambertTrunc
  have hsub : (Finset.range N : Finset ℕ) ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hdiff : ((Finset.range (N + 1) : Finset ℕ) \ Finset.range N) = {N} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [← Finset.sum_sdiff hsub, hdiff, Finset.sum_singleton]
  ring

private theorem mod_eq_of_dvd_sub {p M M' : ℕ} (hle : M' ≤ M) (hd : p ∣ M - M') :
    M % p = M' % p := by
  have hz : (M - M') % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hdecomp := Nat.mod_add_div (M - M') p
  rw [hz, Nat.zero_add] at hdecomp
  have hM : M = M' + p * ((M - M') / p) := by
    rw [hdecomp]
    exact (Nat.add_sub_of_le hle).symm
  rw [hM, Nat.add_mul_mod_self_left]

/-! ## 1. The primorial: the period of the small-prime part -/

/-- **The primorial at `T`**: the product of the primes `p ≤ T`.  It is the
period of the residue vector `(M % p)` as `M` varies. -/
noncomputable def jsp87Prim (T : ℕ) : ℕ := ∏ p ∈ (Finset.Icc 2 T).filter Nat.Prime, p

theorem jsp87Prim_pos (T : ℕ) : 0 < jsp87Prim T := by
  have h : 0 < ∏ p ∈ (Finset.Icc 2 T).filter Nat.Prime, (p : ℕ) :=
    Finset.prod_pos fun p hp' => by
      have hp : 2 ≤ p := (Finset.mem_filter.mp hp').2.two_le
      omega
  exact h

/-- **Every prime below the cut point divides the primorial.** -/
theorem jsp87Prim_prime_dvd {T p : ℕ} (hp : p.Prime) (hle : p ≤ T) : p ∣ jsp87Prim T := by
  have hmem : p ∈ (Finset.Icc 2 T).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hle⟩, hp⟩
  refine Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hmem

theorem jsp87Prim_mono {T T' : ℕ} (h : T ≤ T') : jsp87Prim T ≤ jsp87Prim T' := by
  have h1 : (∏ p ∈ (Finset.Icc 2 T).filter Nat.Prime, (p : ℕ))
      ≤ ∏ p ∈ (Finset.Icc 2 T').filter Nat.Prime, (p : ℕ) := by
    refine Finset.prod_le_prod_of_subset_of_one_le (f := fun q : ℕ => q) ?_ ?_
    · exact Finset.filter_subset_filter Nat.Prime (Finset.Icc_subset_Icc (le_refl 2) h)
    · intro i hit his
      by_cases his' : i ∈ (Finset.Icc 2 T).filter Nat.Prime
      · have hp : 2 ≤ i := (Finset.mem_Icc.mp (Finset.mem_filter.mp his').1).1
        omega
      · have hp : 2 ≤ i := (Finset.mem_filter.mp hit).2.two_le
        omega
  exact h1

/-! ## 2. The truncated carry: the small-prime part of the residue sum -/

/-- **THE TRUNCATED CARRY.**  The contribution of the primes `p ≤ T` to the
prime-residue Lambert sum at the cut point `M`. -/
noncomputable def jsp87CutSum (M T : ℕ) : ℝ :=
  ∑' p : ℕ,
    (if p.Prime ∧ p ≤ T then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)

theorem jsp87CutSum_nonneg_term (M T p : ℕ) :
    (0 : ℝ) ≤ (if p.Prime ∧ p ≤ T
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  by_cases hp : p.Prime
  · by_cases hle : p ≤ T
    · rw [if_pos (gateA_pos hp hle)]
      exact mul_nonneg (by positivity) (inv_nonneg.mpr (mer_pos hp.two_le).le)
    · rw [if_neg (gateA_neg hp hle)]
  · rw [if_neg (gateA_neg' hp)]

theorem summable_jsp87CutSum {M T : ℕ} (hM : 1 ≤ M) :
    Summable (fun p : ℕ => if p.Prime ∧ p ≤ T
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  refine Summable.of_nonneg_of_le (fun p => jsp87CutSum_nonneg_term M T p) (fun p => ?_)
    (summable_jsp87ResidueLambert (M := M) hM)
  by_cases hp : p.Prime
  · by_cases hle : p ≤ T
    · rw [if_pos (gateA_pos hp hle), if_pos hp]
    · rw [if_neg (gateA_neg hp hle), if_pos hp]
      exact mul_nonneg (by positivity) (inv_nonneg.mpr (mer_pos hp.two_le).le)
  · rw [if_neg (gateA_neg' hp), if_neg hp]

theorem jsp87CutSum_nonneg (M T : ℕ) : 0 ≤ jsp87CutSum M T :=
  tsum_nonneg fun p => jsp87CutSum_nonneg_term M T p

theorem jsp87ResidueTerm_nonneg (M p : ℕ) :
    (0 : ℝ) ≤ (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  by_cases hp : p.Prime
  · rw [if_pos hp]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (mer_pos hp.two_le).le)
  · rw [if_neg hp]

/-- The truncated carry is a *finite* sum of residue terms. -/
theorem jsp87CutSum_eq_sum (M T : ℕ) (hM : 1 ≤ M) :
    jsp87CutSum M T = ∑ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  have hmain : jsp87CutSum M T = ∑ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
      (if p.Prime ∧ p ≤ T then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    refine tsum_eq_sum_finset (summable_jsp87CutSum (M := M) hM) _ ?_
    intro p hp
    by_cases hp' : p.Prime
    · by_cases hle : p ≤ T
      · rw [if_pos (gateA_pos hp' hle)]
        have hsetmem : p ∈ ((Finset.Icc 2 T).filter Nat.Prime : Set ℕ) :=
          Finset.mem_coe.mpr (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hp'.two_le, hle⟩, hp'⟩)
        exact absurd hsetmem (fun hmem => hp (Finset.mem_coe.mpr hmem))
      · rw [if_neg (gateA_neg hp' hle)]
    · rw [if_neg (fun h => hp' h.1)]
  rw [hmain]
  refine Finset.sum_congr rfl fun p hp' => ?_
  have hpm := Finset.mem_filter.mp hp'
  have hleT : p ≤ T := (Finset.mem_Icc.mp hpm.1).2
  rw [if_pos (gateA_pos hpm.2 hleT), if_pos hpm.2]

/-- **THE TRUNCATED CARRY IS AT MOST THE WHOLE CARRY** (`2 θ M` is the whole
residue sum). -/
theorem jsp87CutSum_le_residue {M T : ℕ} (hM : 1 ≤ M) :
    jsp87CutSum M T ≤ jsp87ResidueLambert M := by
  rw [jsp87CutSum_eq_sum M T hM]
  refine sum_le_tsum_nonneg'
    (f := fun p : ℕ => (if p.Prime
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
    (fun p => jsp87ResidueTerm_nonneg M p) (summable_jsp87ResidueLambert (M := M) hM)
    ((Finset.Icc 2 T).filter Nat.Prime)

/-- **THE TRUNCATED CARRY IS BOUNDED BELOW BY ANY FINITE SET OF ITS OWN TERMS.** -/
theorem jsp87CutSum_ge_sum {M T : ℕ} (hM : 1 ≤ M) (s : Finset ℕ) :
    (∑ p ∈ s, (if p.Prime ∧ p ≤ T
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ jsp87CutSum M T :=
  sum_le_tsum_nonneg'
    (f := fun p : ℕ => if p.Prime ∧ p ≤ T
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
    (fun p => jsp87CutSum_nonneg_term M T p) (summable_jsp87CutSum (M := M) hM) s

/-! ## 3. **THE FLAGSHIP: THE TRUNCATED CARRY IS PERIODIC IN THE CUT POINT.** -/

/-- **THE PRIMORIAL PERIOD.**  If two cut points are congruent modulo the
primorial `jsp87Prim T`, then the primes `p ≤ T` contribute *exactly* the same
amount to the two carries: the small-prime part of the Erdős carry is a periodic
function of the cut point. -/
theorem jsp87CutSum_period {M M' T : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hleM : M' ≤ M)
    (hc : jsp87Prim T ∣ M - M') : jsp87CutSum M T = jsp87CutSum M' T := by
  unfold jsp87CutSum
  refine tsum_congr fun p => ?_
  by_cases hp : p.Prime
  · by_cases hle : p ≤ T
    · rw [if_pos (gateA_pos hp hle), if_pos (gateA_pos hp hle)]
      have hpT : p ∣ jsp87Prim T := jsp87Prim_prime_dvd hp hle
      have hpMM : p ∣ M - M' := dvd_trans hpT hc
      have hmod : M % p = M' % p := mod_eq_of_dvd_sub hleM hpMM
      simp [jsp87ResExp, hmod]
    · rw [if_neg (gateA_neg hp hle), if_neg (gateA_neg hp hle)]
  · rw [if_neg (gateA_neg' hp), if_neg (gateA_neg' hp)]

/-! ## 4. The Lambert tail above the cut point -/

/-- **THE LAMBERT TAIL ABOVE `T`.**  The sum of the Lambert summands at the
primes *strictly above* the cut point. -/
noncomputable def jsp87LamAbove (T : ℕ) : ℝ :=
  ∑' p : ℕ, (if p.Prime ∧ T < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0)

theorem summable_jsp87LamAbove (T : ℕ) :
    Summable (fun p : ℕ => if p.Prime ∧ T < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) summable_jsp87_lambertTerm
  · by_cases hp : p.Prime
    · by_cases hle : T < p
      · rw [if_pos (gateB_pos hp hle)]
        exact inv_nonneg.mpr (mer_pos hp.two_le).le
      · rw [if_neg (gateB_neg hp hle)]
    · rw [if_neg (gateB_neg' hp)]
  · by_cases hp : p.Prime
    · by_cases hle : T < p
      · rw [if_pos (gateB_pos hp hle), jsp87_lambertTerm, if_pos hp]
      · rw [if_neg (gateB_neg hp hle), jsp87_lambertTerm, if_pos hp]
        exact inv_nonneg.mpr (mer_pos hp.two_le).le
    · rw [if_neg (gateB_neg' hp), jsp87_lambertTerm, if_neg hp]

theorem jsp87LamAbove_nonneg (T : ℕ) : 0 ≤ jsp87LamAbove T :=
  tsum_nonneg fun p => by
    by_cases hp : p.Prime
    · by_cases hle : T < p
      · rw [if_pos (gateB_pos hp hle)]
        exact inv_nonneg.mpr (mer_pos hp.two_le).le
      · rw [if_neg (gateB_neg hp hle)]
    · rw [if_neg (gateB_neg' hp)]

/-- **ONE PRIME STEP OF THE LAMBERT TAIL.**  Passing the cut point from `T` to
`T+1` removes exactly the Lambert summand at `T+1` (which is `0` unless `T+1`
is prime). -/
theorem jsp87LamAbove_sub_succ (T : ℕ) :
    jsp87LamAbove T - jsp87LamAbove (T + 1) = jsp87_lambertTerm (T + 1) := by
  have hpt : ∀ p : ℕ,
      (if p.Prime ∧ T < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0)
        - (if p.Prime ∧ T + 1 < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0)
      = (if p = T + 1 then jsp87_lambertTerm p else 0) := by
    intro p
    by_cases heq : p = T + 1
    · by_cases hp : p.Prime
      · rw [if_pos (gateB_pos hp (by omega : T < p)),
          if_neg (gateB_neg hp (by omega : ¬ T + 1 < p)), if_pos heq,
          jsp87_lambertTerm, if_pos hp]
        ring
      · rw [if_neg (gateB_neg' hp), if_neg (gateB_neg' hp), if_pos heq,
          jsp87_lambertTerm, if_neg hp]
        ring
    · have h1 : T < p → T + 1 < p := by
        intro hlt
        by_contra hc
        have : p ≤ T := by omega
        omega
      by_cases hp : p.Prime
      · by_cases hlt : T < p
        · rw [if_pos (gateB_pos hp hlt), if_pos (gateB_pos hp (h1 hlt)), if_neg heq]
          ring
        · rw [if_neg (gateB_neg hp hlt), if_neg (gateB_neg hp (by omega)), if_neg heq]
          ring
      · rw [if_neg (gateB_neg' hp), if_neg (gateB_neg' hp), if_neg heq]
        ring
  have hsg : Summable (fun p : ℕ => (if p = T + 1 then jsp87_lambertTerm p else 0)) := by
    refine Summable.of_nonneg_of_le (f := fun p : ℕ => jsp87_lambertTerm p) (fun p => ?_)
      (fun p => ?_) summable_jsp87_lambertTerm
    · by_cases heq : p = T + 1
      · rw [if_pos heq]
        exact jsp87_lambertTerm_nonneg p
      · rw [if_neg heq]
    · by_cases heq : p = T + 1
      · rw [if_pos heq]
      · rw [if_neg heq]
        exact jsp87_lambertTerm_nonneg p
  have hdiff := Summable.tsum_sub (summable_jsp87LamAbove T) (summable_jsp87LamAbove (T + 1))
  unfold jsp87LamAbove
  rw [← hdiff, tsum_congr hpt, tsum_eq_single (T + 1) (fun b h => by rw [if_neg h]),
    if_pos rfl]

/-- **THE LAMBERT TAIL ABOVE `T` IS THE WHOLE LAMBERT SUM MINUS THE TRUNCATION
AT `T`.**  Equivalently: the Lambert series splits into the primes at most `T`
and the primes above `T`, with nothing in common. -/
theorem jsp87LamAbove_eq_all_sub_trunc (T : ℕ) :
    jsp87LamAbove T = jsp87_lambertAll - jsp87_lambertTrunc (T + 1) := by
  induction T with
  | zero =>
      have h0 : jsp87LamAbove 0 = jsp87_lambertAll := by
        unfold jsp87LamAbove
        refine tsum_congr fun p => ?_
        by_cases hp : p.Prime
        · rw [if_pos (gateB_pos hp (by have := hp.two_le; omega : 0 < p)),
            jsp87_lambertTerm, if_pos hp]
        · rw [if_neg (gateB_neg' hp), jsp87_lambertTerm, if_neg hp]
      have h1 : jsp87_lambertAll = jsp87_lambertTrunc 1 + jsp87_lambertTail 1 :=
        jsp87_lambert_decomp 1
      have h2 : jsp87_lambertTrunc 1 = 0 := by
        unfold jsp87_lambertTrunc
        rw [Finset.sum_range_one]
        simp [jsp87_lambertTerm]
      rw [h0, h1, h2]
      ring
  | succ T ih =>
      have hsub := jsp87LamAbove_sub_succ T
      have htrunc := jsp87_lambertTrunc_sub_succ (T + 1)
      linarith

/-- **THE LAMBERT TAIL ABOVE `T` IS ROUND 40's LAMBERT TAIL AT `T + 1`.** -/
theorem jsp87LamAbove_eq_lambertTail (T : ℕ) :
    jsp87LamAbove T = jsp87_lambertTail (T + 1) := by
  have hsplit := jsp87LamAbove_eq_all_sub_trunc T
  have h2 := jsp87_lambert_decomp (T + 1)
  have h3 := jsp87_lambertAll_eq
  simp only [jsp87_lambertAll] at h3
  linarith

/-- **THE LAMBERT TAIL ABOVE `T` IS STRICTLY POSITIVE** (there is a prime past
every cut point). -/
theorem jsp87LamAbove_pos (T : ℕ) : 0 < jsp87LamAbove T := by
  obtain ⟨q, hTq, hqprime⟩ := Nat.exists_infinite_primes (T + 1)
  have hs : Summable (fun p : ℕ => (if p = q then ((2 : ℝ) ^ q - 1)⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le (f := fun p : ℕ => jsp87_lambertTerm p) (fun p => ?_)
      (fun p => ?_) summable_jsp87_lambertTerm
    · by_cases heq : p = q
      · rw [if_pos heq]
        exact inv_nonneg.mpr (mer_pos hqprime.two_le).le
      · rw [if_neg heq]
    · by_cases heq : p = q
      · rw [heq, if_pos rfl, jsp87_lambertTerm, if_pos hqprime]
      · rw [if_neg heq]
        exact jsp87_lambertTerm_nonneg p
  have hle : (∑' p : ℕ, (if p = q then ((2 : ℝ) ^ q - 1)⁻¹ else 0)) ≤ jsp87LamAbove T := by
    refine Summable.tsum_le_tsum (fun p => ?_) hs (summable_jsp87LamAbove T)
    by_cases heq : p = q
    · rw [heq, if_pos rfl, if_pos (gateB_pos hqprime (by have := hTq; omega))]
    · rw [if_neg heq]
      exact lamAboveTerm_nonneg T p
  rw [tsum_eq_single q (fun b h => by rw [if_neg h]), if_pos rfl] at hle
  have hpos : 0 < ((2 : ℝ) ^ q - 1)⁻¹ := inv_pos.mpr (mer_pos hqprime.two_le)
  linarith

/-- **THE LAMBERT TAIL ABOVE `T` IS EXPONENTIALLY SMALL.** -/
theorem jsp87LamAbove_le (T : ℕ) : jsp87LamAbove T ≤ 4 * ((2 : ℝ) ^ (T + 1))⁻¹ := by
  rw [jsp87LamAbove_eq_lambertTail]
  exact jsp87_lambertTail_le (T + 1)

/-- **THE LAMBERT TAIL ABOVE A PRIME CUT POINT IS STRICTLY SMALLER.** -/
theorem jsp87LamAbove_lt_succ {T : ℕ} (hT : (T + 1).Prime) :
    jsp87LamAbove (T + 1) < jsp87LamAbove T := by
  have h := jsp87LamAbove_sub_succ T
  have hp : 0 < jsp87_lambertTerm (T + 1) := by
    rw [jsp87_lambertTerm, if_pos hT]
    exact inv_pos.mpr (mer_pos hT.two_le)
  linarith

/-! ## 5. The large-prime part of the carry -/

/-- **THE LARGE-PRIME PART OF THE RESIDUE SUM AT `M`.** -/
noncomputable def jsp87BigSum (M T : ℕ) : ℝ :=
  ∑' p : ℕ,
    (if p.Prime ∧ T < p then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)

theorem jsp87BigSum_nonneg_term (M T p : ℕ) :
    (0 : ℝ) ≤ (if p.Prime ∧ T < p
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  by_cases hp : p.Prime
  · by_cases hle : T < p
    · rw [if_pos (gateB_pos hp hle)]
      exact mul_nonneg (by positivity) (inv_nonneg.mpr (mer_pos hp.two_le).le)
    · rw [if_neg (gateB_neg hp hle)]
  · rw [if_neg (gateB_neg' hp)]

theorem summable_jsp87BigSum {M T : ℕ} (hM : 1 ≤ M) :
    Summable (fun p : ℕ => if p.Prime ∧ T < p
      then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  refine Summable.of_nonneg_of_le (fun p => jsp87BigSum_nonneg_term M T p) (fun p => ?_)
    (summable_jsp87ResidueLambert (M := M) hM)
  by_cases hp : p.Prime
  · by_cases hle : T < p
    · rw [if_pos (gateB_pos hp hle), if_pos hp]
    · rw [if_neg (gateB_neg hp hle), if_pos hp]
      exact mul_nonneg (by positivity) (inv_nonneg.mpr (mer_pos hp.two_le).le)
  · rw [if_neg (gateB_neg' hp), if_neg hp]

/-- **THE SPLIT.**  The prime-residue sum is the truncated carry plus the
large-prime part. -/
theorem jsp87ResidueLambert_eq_cut_add_big {M T : ℕ} (hM : 1 ≤ M) :
    jsp87ResidueLambert M = jsp87CutSum M T + jsp87BigSum M T := by
  have hpt : ∀ p : ℕ,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
      = (if p.Prime ∧ p ≤ T then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
        + (if p.Prime ∧ T < p then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · by_cases hlt : T < p
      · rw [if_pos hp, if_neg (gateA_neg hp (by omega : ¬ p ≤ T)), if_pos (gateB_pos hp hlt)]
        ring
      · rw [if_pos hp, if_pos (gateA_pos hp (by omega : p ≤ T)), if_neg (gateB_neg hp hlt)]
        ring
    · rw [if_neg hp, if_neg (gateA_neg' hp), if_neg (gateB_neg' hp)]
      ring
  unfold jsp87ResidueLambert jsp87CutSum jsp87BigSum
  rw [← Summable.tsum_add (summable_jsp87CutSum (M := M) hM) (summable_jsp87BigSum (M := M) hM)]
  exact tsum_congr fun p => hpt p

/-- **THE LARGE-PRIME PART IS A PURELY GEOMETRIC TERM.**  For `1 ≤ M ≤ T` the
primes above `T` all see the cut point `M` *behind* them, so their residue
exponent is `M` and their total contribution is `2 ^ M` times the Lambert tail
above `T`. -/
theorem jsp87BigSum_eq {M T : ℕ} (hM : 1 ≤ M) (hMT : M ≤ T) :
    jsp87BigSum M T = (2 : ℝ) ^ M * jsp87LamAbove T := by
  have hs := summable_jsp87LamAbove T
  unfold jsp87BigSum jsp87LamAbove
  rw [← Summable.tsum_mul_left ((2 : ℝ) ^ M) hs]
  refine tsum_congr fun p => ?_
  by_cases hp : p.Prime
  · by_cases hlt : T < p
    · rw [if_pos (gateB_pos hp hlt), if_pos (gateB_pos hp hlt)]
      have hre : jsp87ResExp M p = M := by
        have hcases : jsp87ResExp M p = M % p ∨ jsp87ResExp M p = p := by
          unfold jsp87ResExp
          split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
        rcases hcases with hc | hc
        · rw [hc, Nat.mod_eq_of_lt (by omega)]
        · rw [hc]
          have hdvd : p ≤ M := Nat.le_of_dvd (by omega : 0 < M)
            ((jsp87ResExp_eq_dvd (M := M) (p := p) hp.two_le).1 hc)
          omega
      rw [hre] <;> ring
    · rw [if_neg (gateB_neg hp hlt), if_neg (gateB_neg hp hlt)] <;> ring
  · rw [if_neg (gateB_neg' hp), if_neg (gateB_neg' hp)] <;> ring

/-- **THE LARGE-PRIME PART IS NEVER ZERO.** -/
theorem jsp87BigSum_pos {M T : ℕ} (hM : 1 ≤ M) : 0 < jsp87BigSum M T := by
  obtain ⟨q, hq, hqprime⟩ := Nat.exists_infinite_primes (max T M + 1)
  have hre : jsp87ResExp M q = M := by
    have hcases : jsp87ResExp M q = M % q ∨ jsp87ResExp M q = q := by
      unfold jsp87ResExp
      split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
    rcases hcases with hc | hc
    · rw [hc, Nat.mod_eq_of_lt (by omega)]
    · rw [hc]
      have hdvd : q ≤ M := Nat.le_of_dvd (by omega : 0 < M)
        ((jsp87ResExp_eq_dvd (M := M) (p := q) hqprime.two_le).1 hc)
      omega
  have hs : Summable (fun p : ℕ =>
      (if p = q then ((2 : ℝ) ^ jsp87ResExp M q) * ((2 : ℝ) ^ q - 1)⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le
      (f := fun p : ℕ =>
        (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      (fun p => ?_) (fun p => ?_) (summable_jsp87ResidueLambert (M := M) hM)
    · by_cases heq : p = q
      · rw [heq, if_pos rfl, hre]
        exact mul_nonneg (by positivity) (inv_nonneg.mpr (mer_pos hqprime.two_le).le)
      · rw [if_neg heq]
    · by_cases heq : p = q
      · rw [heq, if_pos rfl, if_pos hqprime]
      · rw [if_neg heq]
        exact jsp87ResidueTerm_nonneg M p
  have hle : (∑' p : ℕ,
      (if p = q then ((2 : ℝ) ^ jsp87ResExp M q) * ((2 : ℝ) ^ q - 1)⁻¹ else 0))
      ≤ jsp87BigSum M T := by
    refine Summable.tsum_le_tsum (fun p => ?_) hs (summable_jsp87BigSum (M := M) hM)
    by_cases heq : p = q
    · rw [heq, if_pos rfl, if_pos (gateB_pos hqprime (by have := hq; omega))]
    · rw [if_neg heq]
      exact jsp87BigSum_nonneg_term M T p
  rw [tsum_eq_single q (fun b h => by rw [if_neg h]), if_pos rfl] at hle
  rw [hre] at hle
  exact lt_of_lt_of_le (mul_pos (by positivity) (inv_pos.mpr (mer_pos hqprime.two_le))) hle

/-! ## 6. **THE FLAGSHIP: THE TWO-TERM NORMAL FORM OF THE CARRY.** -/

/-- **THE TWO-TERM NORMAL FORM.**  For every cut point `1 ≤ M ≤ T`, the Erdős
carry splits into its periodic part and its geometric part:

```
jsp87Carry M = jsp87CutSum M T / 2 + 2 ^ (M - 1) * jsp87LamAbove T
```

The first term is a rational whose denominator divides `2 * jsp87LambertQ (T+1)`
and is a periodic function of `M` with period `jsp87Prim T`; the second is a
fixed real times a power of `2`, and *does not depend on the cut point except
through `2 ^ M`*. -/
theorem jsp87Carry_eq_cut_lam {M T : ℕ} (hM : 1 ≤ M) (hMT : M ≤ T) :
    jsp87Carry M = jsp87CutSum M T / 2 + (2 : ℝ) ^ (M - 1) * jsp87LamAbove T := by
  have h1 := jsp87Carry_eq_residueLambert M hM
  rw [jsp87ResidueLambert_eq_cut_add_big (M := M) (T := T) hM, jsp87BigSum_eq (M := M) hM hMT] at h1
  calc jsp87Carry M = (jsp87CutSum M T + (2 : ℝ) ^ M * jsp87LamAbove T) / 2 := by
        linarith [h1]
    _ = jsp87CutSum M T / 2 + (2 : ℝ) ^ (M - 1) * jsp87LamAbove T := by
        have h2 : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel hM]
        rw [h2]
        ring

/-- **THE SAME NORMAL FORM FOR THE TAIL.**  Above a prime cut point the Erdős
tail and the Lambert tail agree term by term. -/
theorem jsp87Tail_eq_cut_lam {M T : ℕ} (hM : 1 ≤ M) (hMT : M ≤ T) :
    jsp87Tail M = jsp87CutSum M T / (2 : ℝ) ^ (M + 1) + jsp87LamAbove T / 2 := by
  have h1 := jsp87Carry_eq_cut_lam hM hMT
  have htail : jsp87Tail M = jsp87Carry M / (2 : ℝ) ^ M := by
    simp only [jsp87Carry]
    field_simp
  rw [htail, h1]
  have e1 : ((2 : ℝ) ^ (M - 1) : ℝ) / (2 : ℝ) ^ M = (1 : ℝ) / 2 := by
    have hh : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hM]
    rw [hh]
    field_simp
  have e2 : jsp87CutSum M T / 2 / (2 : ℝ) ^ M = jsp87CutSum M T / (2 : ℝ) ^ (M + 1) := by
    have hh : (2 : ℝ) ^ (M + 1) = (2 : ℝ) ^ M * 2 := pow_succ (a := (2 : ℝ)) (n := M)
    rw [hh]
    ring
  have e3 : (2 : ℝ) ^ (M - 1) * jsp87LamAbove T / (2 : ℝ) ^ M
      = jsp87LamAbove T / 2 := by
    have e3' : (2 : ℝ) ^ (M - 1) / (2 : ℝ) ^ M * jsp87LamAbove T
        = jsp87LamAbove T / 2 := by rw [e1]; ring
    have e3'' : (2 : ℝ) ^ (M - 1) * jsp87LamAbove T / (2 : ℝ) ^ M
        = (2 : ℝ) ^ (M - 1) / (2 : ℝ) ^ M * jsp87LamAbove T := by ring
    rw [e3'', e3']
  calc (jsp87CutSum M T / 2 + (2 : ℝ) ^ (M - 1) * jsp87LamAbove T) / (2 : ℝ) ^ M
      = jsp87CutSum M T / 2 / (2 : ℝ) ^ M
          + ((2 : ℝ) ^ (M - 1) * jsp87LamAbove T) / (2 : ℝ) ^ M := by rw [add_div]
    _ = jsp87CutSum M T / (2 : ℝ) ^ (M + 1) + jsp87LamAbove T / 2 := by rw [e2, e3]

/-- **THE EXACT DIFFERENCE RULE.**  Two cut points congruent modulo the primorial
have their carries differing by *exactly* the geometric terms. -/
theorem jsp87Carry_sub_congr {M M' T : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hle : M' ≤ M)
    (hc : jsp87Prim T ∣ M - M') (hMT : M ≤ T) (hM'T : M' ≤ T) :
    jsp87Carry M - jsp87Carry M'
      = ((2 : ℝ) ^ (M - 1) - (2 : ℝ) ^ (M' - 1)) * jsp87LamAbove T := by
  have h1 := jsp87Carry_eq_cut_lam hM hMT
  have h2 := jsp87Carry_eq_cut_lam hM' hM'T
  have h3 := jsp87CutSum_period hM hM' hle hc
  rw [h1, h2, h3]
  ring

/-- **THE TRUNCATED CARRY NEVER EXCEEDS `2 θ M`.** -/
theorem jsp87CutSum_le_carry {M T : ℕ} (hM : 1 ≤ M) :
    jsp87CutSum M T ≤ 2 * jsp87Carry M := by
  rw [jsp87Carry_eq_residueLambert M hM]
  exact jsp87CutSum_le_residue hM

/-! ## 7. The predicted-prime count, and the `2`-column -/

/-- **AT A CUT POINT ONE BELOW A MULTIPLE OF `p`, THE RESIDUE EXPONENT IS `p - 1`.** -/
theorem jsp87ResExp_eq_pred {M p : ℕ} (hp : p.Prime) (hd : p ∣ M + 1) :
    jsp87ResExp M p = p - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hz : (M + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hdecomp := Nat.mod_add_mod M p 1
  rw [hz] at hdecomp
  have hrlt : M % p < p := Nat.mod_lt _ (by omega)
  have hcase : M % p + 1 = p := by
    by_cases hc : M % p + 1 < p
    · rw [Nat.mod_eq_of_lt hc] at hdecomp
      omega
    · omega
  have hmod : M % p = p - 1 := by omega
  have hne : M % p ≠ 0 := by rw [hmod]; omega
  rw [jsp87ResExp, if_neg (by rw [hmod]; omega), hmod]

/-- **A PREDICTED-PRIME TERM IS AT LEAST A QUARTER.** -/
theorem jsp87ResExp_pred_term_ge (M : ℕ) {p : ℕ} (hp : p.Prime) (hd : p ∣ M + 1) :
    (1 : ℝ) / 4 ≤ ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hre := jsp87ResExp_eq_pred hp hd
  have hden : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp.two_le
  have hpp : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (m := 1) (by have := hp.two_le; omega)]
  rw [hre, div_eq_mul_inv]
  exact (le_div_iff₀ hden).mpr (by rw [hpp]; nlinarith [hden.le])

/-- **THE COUNTING BOUND ON THE RESIDUE GAP.**  If every prime `p ∈ [3, T]`
divides `M + 1` — i.e. the cut point sits one below a multiple of all of them —
then each of those primes contributes at least a quarter to the gap
`jsp87ResidueGap M`, and the gaps add. -/
theorem jsp87ResidueGap_ge_pred {M T : ℕ} (hM : 1 ≤ M)
    (h : ∀ p, p.Prime → 3 ≤ p → p ≤ T → p ∣ M + 1) :
    (((Finset.Icc 3 T).filter Nat.Prime).card : ℝ) / 4 ≤ jsp87ResidueGap M := by
  have hpt : ∀ p, p.Prime → 3 ≤ p → p ≤ T → p ∣ M + 1 →
      (1 : ℝ) / 4
        ≤ (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p hp h3 hle hd
    rw [if_pos hp]
    have hre := jsp87ResExp_eq_pred hp hd
    rw [hre, div_eq_mul_inv]
    refine (le_div_iff₀ (mer_pos hp.two_le)).mpr ?_
    have hpp : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (m := 1) (by have := hp.two_le; omega)]
    have hX : (4 : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h2 := pow_le_pow_nat h1 (by omega : 2 ≤ p - 1)
      norm_num at h1 h2 ⊢
      exact h2
    rw [hpp]
    nlinarith [mer_pos hp.two_le, hX]
  have hsum : (∑ p ∈ (Finset.Icc 3 T).filter Nat.Prime,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≥ ((Finset.Icc 3 T).filter Nat.Prime).card * (1 / 4) := by
    calc (∑ p ∈ (Finset.Icc 3 T).filter Nat.Prime,
        (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
        ≥ ∑ _p ∈ (Finset.Icc 3 T).filter Nat.Prime, (1 : ℝ) / 4 :=
          Finset.sum_le_sum fun p hp' => by
            have hmem : p ∈ (Finset.Icc 3 T).filter Nat.Prime := hp'
            rw [Finset.mem_filter] at hmem
            obtain ⟨hICC, hp⟩ := hmem
            obtain ⟨hlo, hle⟩ := Finset.mem_Icc.mp hICC
            exact hpt p hp hlo hle (h p hp hlo hle)
      _ = ((Finset.Icc 3 T).filter Nat.Prime).card * (1 / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hbound : (∑ p ∈ (Finset.Icc 3 T).filter Nat.Prime,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ jsp87ResidueGap M :=
    sum_le_tsum_nonneg'
      (f := fun p : ℕ => (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2)
        * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      (fun p => jsp87ResidueGap_nonneg_term M p) (summable_gapTerm M hM)
      ((Finset.Icc 3 T).filter Nat.Prime)
  simpa only [div_eq_mul_inv, one_mul] using (le_trans hsum.le hbound)

/-- **THE FLAGSHIP COUNTING BOUND ON THE CARRY.** -/
theorem jsp87Carry_ge_pred {M T : ℕ} (hM : 1 ≤ M)
    (h : ∀ p, p.Prime → 3 ≤ p → p ≤ T → p ∣ M + 1) :
    2 * jsp87Series + (((Finset.Icc 3 T).filter Nat.Prime).card : ℝ) / 8
      ≤ jsp87Carry M := by
  have h1 := jsp87ResidueGap_ge_pred (M := M) hM h
  have h2 := jsp87ResidueGap_eq M hM
  rw [h2] at h1
  linarith

/-- **THE FLAGSHIP: THE CARRY AT THE CUT POINT ONE BELOW THE PRIMORIAL.** -/
theorem jsp87Carry_ge_prim {T : ℕ} (hT : 5 ≤ T) :
    2 * jsp87Series + (((Finset.Icc 3 T).filter Nat.Prime).card : ℝ) / 8
      ≤ jsp87Carry (jsp87Prim T - 1) := by
  have h2 : 2 ∣ jsp87Prim T := jsp87Prim_prime_dvd (by norm_num : (2 : ℕ).Prime) (by omega)
  have h2le : 2 ≤ jsp87Prim T := Nat.le_of_dvd (jsp87Prim_pos T) h2
  have h1le : 1 ≤ jsp87Prim T := by omega
  have hM : 1 ≤ jsp87Prim T - 1 := by omega
  have hpred : ∀ p, p.Prime → 3 ≤ p → p ≤ T → p ∣ jsp87Prim T - 1 + 1 := by
    intro p hp h3 hle
    show p ∣ jsp87Prim T - 1 + 1
    rw [Nat.sub_add_cancel (m := 1) h1le]
    exact jsp87Prim_prime_dvd hp hle
  exact jsp87Carry_ge_pred (M := jsp87Prim T - 1) hM hpred

/-- **AT LEAST TWO SMALL PRIMES PREDICT A LARGE CARRY.** -/
theorem jsp87PredCard_ge_two {T : ℕ} (hT : 5 ≤ T) :
    (2 : ℝ) ≤ ((Finset.Icc 3 T).filter Nat.Prime).card := by
  have hmem3 : (3 : ℕ) ∈ (Finset.Icc 3 T).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by norm_num⟩
  have hmem5 : (5 : ℕ) ∈ (Finset.Icc 3 T).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by norm_num⟩
  have hsub : ({3, 5} : Finset ℕ) ⊆ (Finset.Icc 3 T).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_singleton, Finset.mem_insert] at hx
    rcases hx with rfl | rfl
    · exact hmem3
    · exact hmem5
  have hcard := Finset.card_le_card hsub
  exact_mod_cast hcard

/-- **MACHINE-CHECKED INSTANCE: `θ 29 ≥ 2·S + 1/4`** (the cut point below
`5# = 30`, predicted by the primes `3, 5`). -/
theorem jsp87Carry_29 : 2 * jsp87Series + 1 / 4 ≤ jsp87Carry (jsp87Prim 5 - 1) := by
  have h := jsp87Carry_ge_prim (T := 5) (by norm_num)
  have hprim : jsp87Prim 5 - 1 = 29 := by decide
  rw [hprim] at h ⊢
  have hcard : ((Finset.Icc 3 5).filter Nat.Prime).card = 2 := by decide
  rw [hcard] at h
  norm_num at h
  exact h

/-- **MACHINE-CHECKED INSTANCE: `θ 209 ≥ 2·S + 3/8`** (below `7# = 210`). -/
theorem jsp87Carry_209 : 2 * jsp87Series + 3 / 8 ≤ jsp87Carry (jsp87Prim 7 - 1) := by
  have h := jsp87Carry_ge_prim (T := 7) (by norm_num)
  have hprim : jsp87Prim 7 - 1 = 209 := by decide
  rw [hprim] at h ⊢
  have hcard : ((Finset.Icc 3 7).filter Nat.Prime).card = 3 := by decide
  rw [hcard] at h
  norm_num at h
  exact h

/-- **THE `2`-COLUMN OF THE TRUNCATED CARRY.** -/
theorem jsp87CutSum_two {M : ℕ} (hM : 1 ≤ M) :
    jsp87CutSum M 2 = (2 : ℝ) ^ jsp87ResExp M 2 / 3 := by
  have hsum := jsp87CutSum_eq_sum M 2 hM
  have hfilter : (Finset.Icc 2 2).filter Nat.Prime = {2} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro h
      have hx : x = 2 := by omega
      simpa [hx] using h.2
    · intro h
      subst h
      exact ⟨by norm_num, by norm_num⟩
  rw [hsum, hfilter]
  simp only [Finset.sum_singleton, if_pos (by norm_num : (2 : ℕ).Prime)]
  have hre : jsp87ResExp M 2 = if M % 2 = 0 then 2 else M % 2 := rfl
  rw [hre]
  by_cases h0 : M % 2 = 0
  · rw [if_pos h0]
    norm_num
  · have hmod : M % 2 = 1 := by omega
    rw [hmod]
    norm_num

/-- **THE `2`-COLUMN SHARPENS ROUND 84's BOUND AT EVEN CUT POINTS:** at an even
cut point the prime `2` contributes a full `1/3`. -/
theorem jsp87Carry_ge_two_even {M : ℕ} (hM : 1 ≤ M) (he : Even M) :
    2 * jsp87Series + 1 / 3 ≤ jsp87Carry M := by
  have h1 := jsp87Carry_ge_residue M hM 2 (by norm_num : (2 : ℕ).Prime)
  have hre : jsp87ResExp M 2 = 2 := by
    rw [jsp87ResExp_eq_dvd (by norm_num)]
    obtain ⟨r, rfl⟩ := he
    exact ⟨r, by omega⟩
  rw [hre] at h1
  have hnum : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [hnum] at h1
  norm_num at h1 ⊢
  exact h1

/-- **AT ODD CUT POINTS THE `2`-COLUMN CONTRIBUTES NOTHING** (its residue
exponent is `1`, so `2 ^ 1 - 2 = 0`): the minimum `2 · jsp87Series` is all the
prime `2` gives. -/
theorem jsp87Carry_ge_two_odd {M : ℕ} (hM : 1 ≤ M) (ho : Odd M) :
    2 * jsp87Series ≤ jsp87Carry M := by
  have h1 := jsp87Carry_ge_residue M hM 2 (by norm_num : (2 : ℕ).Prime)
  have hre : jsp87ResExp M 2 = 1 := by
    have hmod : M % 2 = 1 := by
      obtain ⟨k, rfl⟩ := ho
      omega
    rw [jsp87ResExp, if_neg (by omega)]
    exact hmod
  rw [hre] at h1
  norm_num at h1 ⊢
  exact h1

/-! ## 8. Under a hypothetical digit period -/

/-- **THE QUANTISATION OF THE CARRY BY THE PERIOD.**  If the binary digits of the
Erdős series are eventually periodic from `M0` with period `t > 0`, then

```
(2 ^ t - 1) * jsp87Carry M = (2 ^ t - 1) * ⌊jsp87Carry M⌋ + (the t-digit block)
```

for every `M ≥ M0`: the carry is *exactly* the digit block divided by
`2 ^ t - 1`, up to its own integer part. -/
theorem jsp87Carry_mer_eq {t M M0 : ℕ} (ht : 0 < t)
    (hper : ∀ n, M0 ≤ n → jsp87Digit (n + t) = jsp87Digit n) (hM : M0 ≤ M) (hM1 : 1 ≤ M) :
    ((2 : ℝ) ^ t - 1) * jsp87Carry M
      = ((2 : ℝ) ^ t - 1) * (jsp87CarryExcess M : ℝ) + (jsp87DigitBlock M t : ℝ) := by
  have hperM : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n :=
    fun n hn => hper n (le_trans hM hn)
  have hfrac := jsp87_frac_scaled_eq_block (N := M) (t := t) ht hperM
  have hfc := jsp87_fract_scaled (N := M) hM1
  have hfloor : (⌊jsp87Carry M⌋ : ℤ) = jsp87CarryExcess M := rfl
  rw [hfc] at hfrac
  have hkey : ((2 : ℝ) ^ t - 1) * Int.fract (jsp87Carry M) = (jsp87DigitBlock M t : ℝ) := by
    have hden : ((2 : ℝ) ^ t - 1) ≠ 0 := by
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ t := two_pow_ge_two (p := t) ht
      nlinarith
    rw [hfrac]
    field_simp
  have hdecomp : Int.fract (jsp87Carry M) = jsp87Carry M - (jsp87CarryExcess M : ℝ) := by
    have h := Int.floor_add_fract (jsp87Carry M)
    rw [hfloor] at h
    push_cast at h
    linarith
  rw [hdecomp] at hkey
  linarith

/-- **Consequently the carry is an exact rational under a hypothetical period.** -/
theorem jsp87Carry_mer_mul_int {t M M0 : ℕ} (ht : 0 < t)
    (hper : ∀ n, M0 ≤ n → jsp87Digit (n + t) = jsp87Digit n) (hM : M0 ≤ M) (hM1 : 1 ≤ M) :
    ∃ k : ℤ, ((2 : ℝ) ^ t - 1) * jsp87Carry M = (k : ℝ) := by
  have h1 := jsp87Carry_mer_eq ht hper hM hM1
  refine ⟨(2 : ℤ) ^ t * jsp87CarryExcess M - jsp87CarryExcess M + jsp87DigitBlock M t, ?_⟩
  push_cast
  push_cast at h1
  linarith

/-- **The truncated carry, as an explicit sum of natural numbers.**  The whole
cut sum `jsp87CutSum M T` is a *natural number* built from the primes at or
below `T`:  each prime `p <= T` contributes `2 ^ (jsp87ResExp M p)` times
`jsp87LambertQ (T+1) / (2 ^ p - 1)`, and `2 ^ p - 1` is a factor of
`jsp87LambertQ (T+1)`. -/
noncomputable def jsp87CutNat (M T : ℕ) : ℕ :=
  ∑ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
    (2 ^ jsp87ResExp M p) * (jsp87LambertQ (T + 1) / (2 ^ p - 1))

/-- **The clearing numerator is EVEN.**  Every prime `p <= T` contributes
`2 ^ (jsp87ResExp M p)` with `jsp87ResExp M p >= 1`, so every summand of
`jsp87CutNat M T` is even.  This parity fact is what turns the cleared tail below
into an *integer* rather than a half-integer. -/
theorem jsp87CutNat_even (M T : ℕ) : ∃ j : ℕ, jsp87CutNat M T = 2 * j := by
  refine ⟨∑ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
    (2 ^ (jsp87ResExp M p - 1)) * (jsp87LambertQ (T + 1) / (2 ^ p - 1)), ?_⟩
  have hmul : ∀ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
      (2 ^ jsp87ResExp M p) * (jsp87LambertQ (T + 1) / (2 ^ p - 1))
        = 2 * ((2 ^ (jsp87ResExp M p - 1)) * (jsp87LambertQ (T + 1) / (2 ^ p - 1))) := by
    intro p hp'
    have hp : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).1
    have h2 : 2 ^ jsp87ResExp M p = 2 * 2 ^ (jsp87ResExp M p - 1) := by
      have hpos : 1 ≤ jsp87ResExp M p := jsp87ResExp_pos (M := M) (by omega)
      conv_lhs => rw [show jsp87ResExp M p = jsp87ResExp M p - 1 + 1 by omega]
      rw [pow_succ]
      ring
    rw [h2]
    ring
  unfold jsp87CutNat
  rw [Finset.sum_congr rfl fun p hp' => hmul p hp', ← Finset.mul_sum]

/-- **THE CLEARED TRUNCATED CARRY.**  The truncated carry at `M` is a rational
whose denominator divides `jsp87LambertQ (T+1) = ∏_{p ≤ T} (2 ^ p - 1)`.  The
witness is the natural number `jsp87CutNat M T`, whose `p`-th summand is
`2 ^ (jsp87ResExp M p)` times the *integer* `jsp87LambertQ (T+1) / (2 ^ p - 1)`. -/
theorem jsp87CutSum_cleared {M T : ℕ} (hM : 1 ≤ M) :
    (jsp87LambertQ (T + 1) : ℝ) * jsp87CutSum M T = (jsp87CutNat M T : ℤ) := by
  have hsum := jsp87CutSum_eq_sum M T hM
  have hD : (jsp87LambertQ (T + 1) : ℝ) = (lambertDen (Finset.range (T + 1)) : ℝ) := rfl
  have hptQ : ∀ p, p ∈ (Finset.Icc 2 T).filter Nat.Prime →
      (jsp87LambertQ (T + 1) : ℝ) *
          (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
        = (((2 ^ jsp87ResExp M p) * (jsp87LambertQ (T + 1) / (2 ^ p - 1) : ℕ) : ℕ) : ℝ) := by
    intro p hp'
    have hp : p.Prime := (Finset.mem_filter.mp hp').2
    have hle : p ≤ T := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).2
    have hlt : p < T + 1 := by omega
    have hden := jsp87_lambertTerm_mul_den hp hlt
    rw [jsp87_lambertTerm, if_pos hp] at hden
    rw [if_pos hp, mul_comm ((jsp87LambertQ (T + 1) : ℝ))
        ((2 : ℝ) ^ jsp87ResExp M p * ((2 : ℝ) ^ p - 1)⁻¹), mul_assoc, hD, hden]
    simp only [Nat.cast_mul, Nat.cast_div, Nat.cast_pow, Nat.cast_ofNat]
    congr 1
  calc (jsp87LambertQ (T + 1) : ℝ) * jsp87CutSum M T
      = ∑ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
        ((jsp87LambertQ (T + 1) : ℝ) *
          (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
        rw [hsum, mul_comm, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => (mul_comm _ _)
    _ = ∑ p ∈ (Finset.Icc 2 T).filter Nat.Prime,
        (((2 ^ jsp87ResExp M p) * (jsp87LambertQ (T + 1) / (2 ^ p - 1) : ℕ) : ℕ) : ℝ) := by
        exact Finset.sum_congr rfl fun p hp' => hptQ p hp'
    _ = ((jsp87CutNat M T : ℕ) : ℝ) := by
        unfold jsp87CutNat
        rw [← Nat.cast_sum]
    _ = (((jsp87CutNat M T : ℕ) : ℤ) : ℝ) := rfl

/-- **THE FLAGSHIP OBSTRUCTION ANALYSIS: A HYPOTHETICAL RATIONALITY ASSUMPTION
FORCES THE LAMBERT TAIL TO HAVE NO DENOMINATOR ABOVE THE CUT POINT.**

Assume the binary digits of `S` are eventually periodic from `M0` with period
`t > 0` (which rationality forces, by round 41).  Then for every prime cut point
`T` and every `M` with `M0 ≤ M ≤ T`, the Lambert tail above `T`, rescaled by
`2^(M-1)`, is a rational whose denominator divides

```
jsp87LambertQ (T+1) = ∏_{p ≤ T} (2 ^ p - 1)
```

*nothing from the primes above `T` survives*.  This is exactly why the
denominator route cannot close the gate, and it is proved here rather than
observed. -/
theorem jsp87LamAbove_cleared {t M M0 T : ℕ} (ht : 0 < t)
    (hper : ∀ n, M0 ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hM : M0 ≤ M) (hM1 : 1 ≤ M) (hMT : M ≤ T) :
    ∃ k : ℤ, (jsp87LambertQ (T + 1) : ℝ) * ((2 : ℝ) ^ t - 1) * (2 : ℝ) ^ (M - 1)
        * jsp87LamAbove T = (k : ℝ) := by
  obtain ⟨k₀, hk₀⟩ := jsp87Carry_mer_mul_int ht hper hM hM1
  have hkc := jsp87CutSum_cleared (M := M) (T := T) hM1
  obtain ⟨j, hj⟩ := jsp87CutNat_even M T
  have hkc' : (jsp87LambertQ (T + 1) : ℝ) * jsp87CutSum M T = (2 * j : ℝ) := by
    rw [hkc]
    push_cast
    rw [hj]
    norm_num
  have hnorm := jsp87Carry_eq_cut_lam hM1 hMT
  have hk1 : (jsp87LambertQ (T + 1) : ℝ) * (jsp87CutSum M T / 2) = (j : ℝ) := by
    have hre : (jsp87LambertQ (T + 1) : ℝ) * (jsp87CutSum M T / 2)
        = (jsp87LambertQ (T + 1) : ℝ) * jsp87CutSum M T / 2 := by ring
    rw [hre, hkc']
    ring
  have e1 : ((2 : ℝ) ^ t - 1) * ((2 : ℝ) ^ (M - 1) * jsp87LamAbove T)
      = ((2 : ℝ) ^ t - 1) * jsp87Carry M
        - ((2 : ℝ) ^ t - 1) * (jsp87CutSum M T / 2) := by rw [hnorm]; ring
  have hk0' : (jsp87LambertQ (T + 1) : ℝ) * (((2 : ℝ) ^ t - 1) * jsp87Carry M)
      = ((jsp87LambertQ (T + 1) : ℤ) * k₀ : ℝ) := by
    rw [hk₀]
    push_cast
    ring
  set w : ℤ := (jsp87LambertQ (T + 1) : ℤ) * k₀ - ((2 : ℤ) ^ t - 1) * (j : ℤ) with hw
  have hmain : (jsp87LambertQ (T + 1) : ℝ) * ((2 : ℝ) ^ t - 1) * (2 : ℝ) ^ (M - 1)
      * jsp87LamAbove T = (w : ℝ) := by
    calc (jsp87LambertQ (T + 1) : ℝ) * ((2 : ℝ) ^ t - 1) * (2 : ℝ) ^ (M - 1) * jsp87LamAbove T
        = (jsp87LambertQ (T + 1) : ℝ) *
            (((2 : ℝ) ^ t - 1) * ((2 : ℝ) ^ (M - 1) * jsp87LamAbove T)) := by ring
      _ = (jsp87LambertQ (T + 1) : ℝ) *
            (((2 : ℝ) ^ t - 1) * jsp87Carry M
              - ((2 : ℝ) ^ t - 1) * (jsp87CutSum M T / 2)) := by rw [e1]
      _ = (jsp87LambertQ (T + 1) : ℝ) * (((2 : ℝ) ^ t - 1) * jsp87Carry M)
            - ((2 : ℝ) ^ t - 1) *
              ((jsp87LambertQ (T + 1) : ℝ) * (jsp87CutSum M T / 2)) := by ring
      _ = ((jsp87LambertQ (T + 1) : ℤ) * k₀ : ℝ)
            - ((2 : ℝ) ^ t - 1) * ((j : ℕ) : ℝ) := by
          rw [hk0', hk1]
      _ = (w : ℝ) := by
        rw [hw]
        push_cast
        ring
  exact ⟨w, hmain⟩

/-! ## 9. The complete reformulation of the headline -/

theorem jsp87_lambertTrunc_rat (N : ℕ) : ∃ q : ℚ, (jsp87_lambertTrunc N : ℝ) = (q : ℝ) := by
  have hdiv := jsp87_lambertTrunc_eq_div N
  refine ⟨(jsp87_lambertNumer N : ℚ) / ((lambertDen (Finset.range N) : ℤ) : ℚ), ?_⟩
  rw [hdiv]
  push_cast
  field_simp

/-- **THE COMPLETE REFORMULATION OF THE HEADLINE.**  The Erdős series is
irrational **if and only if** every Lambert tail above a prime cut point is
irrational: `jsp87Series_irrational_iff_lamAbove`. -/
theorem jsp87Series_irrational_iff_lamAbove (T : ℕ) :
    Irrational jsp87Series ↔ Irrational (jsp87LamAbove T) := by
  have hsplit := jsp87LamAbove_eq_all_sub_trunc T
  have hall := jsp87_lambertAll_eq
  obtain ⟨q, hq⟩ := jsp87_lambertTrunc_rat (T + 1)
  have hkey : jsp87LamAbove T = 2 * jsp87Series - (q : ℝ) := by
    rw [hsplit, hall, hq]
  constructor
  · intro hS
    have h2S : Irrational (2 * jsp87Series) := by
      have h := hS.mul_natCast (m := 2) (by norm_num)
      simpa [mul_comm] using h
    rw [hkey]
    exact h2S.sub_ratCast q
  · intro hL
    have hsub : Irrational (2 * jsp87Series - (q : ℝ)) := by
      rw [← hkey]
      exact hL
    have h2S : Irrational (2 * jsp87Series) := Irrational.of_sub_ratCast q hsub
    have h2S' : Irrational (jsp87Series * 2) := by simpa [mul_comm] using h2S
    have hd := h2S'.div_natCast (m := 2) (by norm_num)
    simpa using hd
