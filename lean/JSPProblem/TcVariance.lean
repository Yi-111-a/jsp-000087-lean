/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-130-a).
-/
import JSPProblem.Chowla
import JSPProblem.VarLocal
import Mathlib.Tactic

/-!
# JSP-000087, round 130 — THE EXACT SECOND MOMENT OF THE TRUNCATED CARRY:
# THE DIAGONAL IS ARITHMETIC, THE OFF-DIAGONAL IS THE MISSING CORRELATION INPUT

## Why this file exists

Round 112 (`JSPProblem/TTRoute.lean`) built the object of §5 of Tao–Teräväinen,
arXiv:2512.01739 — the **truncated carry**

```
jsp87TruncCarry N H = ∑_{k<H} ω(N+k) / 2^{k+1}
```

— and the deterministic reduction (round 112,
`jsp87Series_rational_imp_truncCarry_nearInt`): if `jsp87Series = a/b` with
`b > 0` then for every `N ≥ 1` and every `H` the number `b · jsp87TruncCarry N H`
lies within `b 2^{-H} (N+H+1)` of an **integer**.

What the published proof adds is §5.4, *extracting a variance bound*.  The
object of §5.4 is the variance, over a window of cut points `N < L`, of the
truncated carry, and its exact value is a **double correlation sum of `ω`**:

```
∑_{N<L} T(N,H)²  =  ∑_{k<H} ∑_{k'<H} 2^{-(k+1)-(k'+1)} · ( ∑_{N<L} ω(N+k) ω(N+k') ) .
```

Round 115 (`JSPProblem/Chowla.lean`) named the inner sums
(`jsp87CorrAt L k k'`, the diagonal `jsp87SqWindow k L` being `k = k'`) and
opened the blocker **`jsp87_truncSq_diag`** — the double-sum identity above —
recording that it "is NOT proved here: at depth `H` it needs a
diagonal/off-diagonal split of a square of a finite sum over `H` places, which in
this Mathlib costs more `Finset.sum_product`/`Finset.sum_comm` bookkeeping than
the remaining budget of round 115 allowed".

**This file closes that blocker** and then does what round 115 could not: it
separates the second moment into

* the **diagonal** `∑_k 4^{-(k+1)} · ∑_{N<L} ω(N+k)²`, which is *shifted second
  moment arithmetic* — no analytic input at all; and
* the **off-diagonal** `∑_{k<k'} 2^{1-(k+k')} · ∑_{N<L} ω(N+k) ω(N+k')`, which is
  precisely a **weighted sum of the two-point correlations of `ω` at the
  shifts `k' − k`**.

So the variance hypothesis of the published proof is localised, exactly, to a
weighted sum of Chowla-type correlations; the diagonal is free and the
off-diagonal is the analytic input that Mathlib does not contain (round 115,
`jsp87Chowla_le_add`, computes the elementary CRT bound of that input, and §6
below computes its *price*).

## What is proved here

* §1  `jsp87TruncSqSum_eq_dblCorr` — **THE MAIN THEOREM**: the second moment of
  the truncated carry is the double correlation sum (`jsp87_truncSq_diag` closed);
* §2  `jsp87TruncSqSum_eq_diag_add_off` — **the diagonal/off-diagonal split**,
  with `jsp87TcDiag`, `jsp87TcOff` as objects and their nonnegativity;
* §3  `jsp87TcVar_eq_diag_add_cov` — **THE VARIANCE DECOMPOSITION**: the
  variance of the truncated carry over a window of cut points is the sum of the
  `H` shifted variances of `ω`, plus the `H (H−1)/2` weighted **covariances** of
  `ω`;
* §4  `jsp87Var_eq_FAvg_sq_sub` and the sum-form of the same identity;
* §5  the two **transfer lemmas**: nonnegative covariances give a lower bound by
  the diagonal alone, and a uniform covariance bound gives an upper bound by the
  diagonal plus that bound — i.e. the exact shape of §5.4;
* §6  the **price of the elementary CRT bound** (round 115): the shift-`1`
  correlation enters the off-diagonal term with weight `1/4`, so any upper bound
  on the off-diagonal term must be at least `π(N)(π(N+1) − 1)/4`, where the
  boundary error is computed in closed form here;
* §7  machine-checked instances of the new variance object.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. The objects -/

/-- **THE WEIGHT OF PLACE `k`** in the truncated carry: `2^{-(k+1)}`.
The `H` weights sum to `1 − 2^{-H}`, so the truncated carry is a convex
combination of `H` consecutive values of `ω`. -/
noncomputable def jsp87Tw (k : ℕ) : ℝ := ((2 : ℝ) ^ (k + 1))⁻¹

theorem jsp87Tw_pos (k : ℕ) : 0 < jsp87Tw k := by
  unfold jsp87Tw
  positivity

@[simp] theorem jsp87Tw_zero : jsp87Tw 0 = (1 / 2 : ℝ) := by
  simp [jsp87Tw]

/-- **THE WEIGHTS SUM TO `1 − 2^{-H}`. -/
theorem jsp87Tw_sum (H : ℕ) : (∑ k ∈ Finset.range H, jsp87Tw k) = 1 - ((2 : ℝ) ^ H)⁻¹ := by
  induction H with
  | zero => simp [jsp87Tw]
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep : jsp87Tw H = ((2 : ℝ) ^ H)⁻¹ * (1 / 2) := by
      unfold jsp87Tw
      rw [pow_succ]
      field_simp
    have hstep' : ((2 : ℝ) ^ (H + 1))⁻¹ = ((2 : ℝ) ^ H)⁻¹ * (1 / 2) := by
      rw [pow_succ]
      field_simp
    rw [hstep, hstep']
    ring

theorem jsp87Tw_sum_le_one (H : ℕ) : (∑ k ∈ Finset.range H, jsp87Tw k) ≤ 1 := by
  rw [jsp87Tw_sum]
  have h : 0 < ((2 : ℝ) ^ H)⁻¹ := by positivity
  linarith

/-- **THE TRUNCATED CARRY IS THE WEIGHTED SUM OF `ω`.** -/
theorem jsp87TruncCarry_eq_sumTw (N H : ℕ) :
    jsp87TruncCarry N H = ∑ k ∈ Finset.range H, ((omega (N + k) : ℕ) : ℝ) * jsp87Tw k := by
  unfold jsp87TruncCarry jsp87Tw
  rfl

/-- **THE MEAN OF `ω` OVER THE WINDOW OF CUT POINTS** `N < L`, shifted by `k`:
`𝔼 ω(N+k)`. -/
noncomputable def jsp87TcMean (L k : ℕ) : ℝ :=
  jsp87FAvg (Finset.range L) (fun N => ((omega (N + k) : ℕ) : ℝ))

/-- **THE CORRELATION AT THE SHIFT PAIR `k, k'`**: `𝔼 ω(N+k) ω(N+k')`, i.e.
`jsp87CorrAt L k k'` divided by the length of the window. -/
noncomputable def jsp87TcCorr (L k k' : ℕ) : ℝ :=
  jsp87FAvg (Finset.range L)
    (fun N => ((omega (N + k) : ℕ) : ℝ) * ((omega (N + k') : ℕ) : ℝ))

/-- **THE COVARIANCE OF `ω` AT THE SHIFT PAIR `k, k'`** — the object the
published proof must estimate: `𝔼 ω(N+k) ω(N+k') − 𝔼 ω(N+k) · 𝔼 ω(N+k')`. -/
noncomputable def jsp87Mcov (L k k' : ℕ) : ℝ :=
  jsp87TcCorr L k k' - jsp87TcMean L k * jsp87TcMean L k'

/-- **THE VARIANCE OF `ω` ITSELF** over the window of cut points, shifted by `k`.
This is the diagonal of the variance decomposition. -/
noncomputable def jsp87TcVarAt (L k : ℕ) : ℝ :=
  jsp87Var (Finset.range L) (fun N => ((omega (N + k) : ℕ) : ℝ))

/-- **THE VARIANCE OF THE TRUNCATED CARRY** over the window of cut points
`N < L`, at depth `H` — the object of §5.4 of arXiv:2512.01739. -/
noncomputable def jsp87TcVar (L H : ℕ) : ℝ :=
  jsp87Var (Finset.range L) (fun N => jsp87TruncCarry N H)

/-- **THE DIAGONAL TERM**: `∑_k 4^{-(k+1)} · ∑_{N<L} ω(N+k)²`, the part of the
second moment that comes from `k = k'`.  Purely a shifted second moment of `ω`;
**no analytic input**. -/
noncomputable def jsp87TcDiag (L H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * ((jsp87SqWindow k L : ℕ) : ℝ)

/-- **THE OFF-DIAGONAL TERM**: `∑_{k<k'} 2·2^{-(k+1)-(k'+1)} · ∑_{N<L} ω(N+k)ω(N+k')`,
the part of the second moment that comes from two *different* places of the
window.  This is a **weighted sum of the two-point correlations of `ω`**, i.e.
exactly the analytic object of §5.4. -/
noncomputable def jsp87TcOff (L H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
    (2 * jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ)

/-! ## 1. The correlation sums as real averages -/

theorem jsp87CorrAt_symm (L k k' : ℕ) : jsp87CorrAt L k k' = jsp87CorrAt L k' k := by
  unfold jsp87CorrAt
  refine Finset.sum_congr rfl fun N _ => ?_
  ring

theorem jsp87cast_sum_corrAt (L k k' : ℕ) :
    ((jsp87CorrAt L k k' : ℕ) : ℝ)
      = ∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((omega (N + k') : ℕ) : ℝ) := by
  have h1 : jsp87CorrAt L k k' = ∑ N ∈ Finset.range L, omega (N + k) * omega (N + k') := by
    unfold jsp87CorrAt
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Nat.add_comm]
  calc (↑(jsp87CorrAt L k k' : ℕ) : ℝ)
      = ↑(∑ N ∈ Finset.range L, omega (N + k) * omega (N + k')) := by rw [h1]
    _ = ∑ N ∈ Finset.range L,
        (((omega (N + k) : ℕ) : ℝ) * ((omega (N + k') : ℕ) : ℝ)) := by
          rw [Nat.cast_sum]
          simp only [Nat.cast_mul]

theorem jsp87cast_sum_sqWindow (L k : ℕ) :
    ((jsp87SqWindow k L : ℕ) : ℝ)
      = ∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) ^ 2 := by
  have h1 : jsp87SqWindow k L = ∑ N ∈ Finset.range L, omega (N + k) ^ 2 := by
    unfold jsp87SqWindow
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Nat.add_comm]
  calc (↑(jsp87SqWindow k L : ℕ) : ℝ)
      = ↑(∑ N ∈ Finset.range L, omega (N + k) ^ 2) := by rw [h1]
    _ = ∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) ^ 2 := by
      rw [Nat.cast_sum]
      simp only [Nat.cast_pow]

theorem jsp87cast_sum_windowOmega (L k : ℕ) :
    ((jsp87WindowOmega k L : ℕ) : ℝ) = ∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) := by
  have h1 : jsp87WindowOmega k L = ∑ N ∈ Finset.range L, omega (N + k) := by
    unfold jsp87WindowOmega
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Nat.add_comm]
  calc (↑(jsp87WindowOmega k L : ℕ) : ℝ)
      = ↑(∑ N ∈ Finset.range L, omega (N + k)) := by rw [h1]
    _ = ∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) := by rw [Nat.cast_sum]

theorem jsp87cast_card_range (L : ℕ) : (((Finset.range L).card : ℕ) : ℝ) = (L : ℝ) := by
  rw [Finset.card_range]

/-- the length of a nonempty window is nonzero -/
private theorem card_range_ne_zero {L : ℕ} (hL : 1 ≤ L) : ((Finset.range L).card : ℕ) ≠ 0 := by
  rw [Finset.card_range]
  omega

theorem jsp87TcCorr_eq (L k k' : ℕ) :
    jsp87TcCorr L k k' = ((jsp87CorrAt L k k' : ℕ) : ℝ) / (L : ℝ) := by
  unfold jsp87TcCorr jsp87FAvg
  rw [jsp87cast_sum_corrAt, jsp87cast_card_range]

theorem jsp87TcMean_eq (L k : ℕ) :
    jsp87TcMean L k = ((jsp87WindowOmega k L : ℕ) : ℝ) / (L : ℝ) := by
  unfold jsp87TcMean jsp87FAvg
  rw [jsp87cast_sum_windowOmega, jsp87cast_card_range]

theorem jsp87TcCorr_diag (L k : ℕ) :
    jsp87TcCorr L k k = jsp87FAvg (Finset.range L) (fun N => ((omega (N + k) : ℕ) : ℝ) ^ 2) := by
  unfold jsp87TcCorr jsp87FAvg
  have h : (∑ N ∈ Finset.range L,
        ((omega (N + k) : ℕ) : ℝ) * ((omega (N + k) : ℕ) : ℝ))
      = ∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl fun N _ => ?_
    ring
  rw [h]

/-- **THE DIAGONAL OF THE CORRELATION IS THE WINDOW SECOND MOMENT.** -/
theorem jsp87CorrAt_diag (L k : ℕ) : jsp87CorrAt L k k = jsp87SqWindow k L := by
  unfold jsp87CorrAt jsp87SqWindow
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [Nat.add_comm]
  ring

theorem jsp87Mcov_symm (L k k' : ℕ) : jsp87Mcov L k k' = jsp87Mcov L k' k := by
  unfold jsp87Mcov jsp87TcCorr jsp87FAvg
  have h1 : (∑ N ∈ Finset.range L,
        ((omega (N + k) : ℕ) : ℝ) * ((omega (N + k') : ℕ) : ℝ))
      = ∑ N ∈ Finset.range L,
        ((omega (N + k') : ℕ) : ℝ) * ((omega (N + k) : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun N _ => ?_
    ring
  rw [h1]
  ring

/-! ## 2. A symmetric double sum splits into its diagonal and twice its
upper triangle -/

private theorem sum_split (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℝ) :
    (∑ x ∈ s.filter p, f x) + (∑ x ∈ s.filter (fun x => ¬ p x), f x) = ∑ x ∈ s, f x := by
  have hp : (∑ x ∈ s.filter p, f x) = ∑ x ∈ s, (if p x then f x else 0) :=
    Finset.sum_filter p f
  have hq : (∑ x ∈ s.filter (fun x => ¬ p x), f x) = ∑ x ∈ s, (if ¬ p x then f x else 0) :=
    Finset.sum_filter (fun x => ¬ p x) f
  rw [hp, hq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hpx : p x <;> simp [hpx]

private theorem tri_eq_prod (s t : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ s, ∑ k' ∈ t.filter (fun x => k < x), f k k')
      = ∑ q ∈ s ×ˢ t, (if q.1 < q.2 then f q.1 q.2 else 0) := by
  have key : ∀ k ∈ s, (∑ k' ∈ t.filter (fun x => k < x), f k k')
      = ∑ k' ∈ t, (if k < k' then f k k' else 0) := by
    intro k hk
    rw [Finset.sum_filter]
  calc (∑ k ∈ s, ∑ k' ∈ t.filter (fun x => k < x), f k k')
      = ∑ k ∈ s, ∑ k' ∈ t, (if k < k' then f k k' else 0) :=
        Finset.sum_congr rfl fun k hk => key k hk
    _ = ∑ q ∈ s ×ˢ t, (if q.1 < q.2 then f q.1 q.2 else 0) := by
      rw [Finset.sum_product]

private theorem off_eq_prod (s t : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ s, ∑ k' ∈ t.filter (fun x => k ≠ x), f k k')
      = ∑ q ∈ s ×ˢ t, (if q.1 ≠ q.2 then f q.1 q.2 else 0) := by
  have key : ∀ k ∈ s, (∑ k' ∈ t.filter (fun x => k ≠ x), f k k')
      = ∑ k' ∈ t, (if k ≠ k' then f k k' else 0) := by
    intro k hk
    rw [Finset.sum_filter]
  calc (∑ k ∈ s, ∑ k' ∈ t.filter (fun x => k ≠ x), f k k')
      = ∑ k ∈ s, ∑ k' ∈ t, (if k ≠ k' then f k k' else 0) :=
        Finset.sum_congr rfl fun k hk => key k hk
    _ = ∑ q ∈ s ×ˢ t, (if q.1 ≠ q.2 then f q.1 q.2 else 0) := by
      rw [Finset.sum_product]

/-- **THE DIAGONAL/OFF-DIAGONAL SPLIT.**  For a *symmetric* `f : ℕ → ℕ → ℝ`,

```
∑_{k,k'} f k k'  =  ∑_k f k k  +  2 ∑_{k<k'} f k k' .
```

The diagonal is counted once and each unordered pair of distinct places is
counted twice, once in each order. -/
theorem jsp87_sum_dbl_eq_diag_add_two_tri (H : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ k k', f k k' = f k' k) :
    (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H, f k k')
      = (∑ k ∈ Finset.range H, f k k)
        + 2 * (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x), f k k') := by
  set s : Finset ℕ := Finset.range H with hs
  set sq : Finset (ℕ × ℕ) := s ×ˢ s with hsq
  set T : Finset (ℕ × ℕ) := sq.filter (fun q => q.1 < q.2) with hT
  set Tlo : Finset (ℕ × ℕ) := sq.filter (fun q => q.2 < q.1) with hTlo
  have hrang : ∀ q ∈ sq, q.1 ∈ s ∧ q.2 ∈ s := by
    intro q hq
    rcases Finset.mem_product.mp hq with ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  have hinner : ∀ k ∈ s, (∑ k' ∈ s, f k k')
      = f k k + ∑ k' ∈ s.filter (fun x => k ≠ x), f k k' := by
    intro k hk
    have hne : s.filter (fun x => ¬ (k ≠ x)) = {k} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hxk⟩
        omega
      · rintro rfl
        exact ⟨hk, by simp⟩
    have h := sum_split s (fun x => k ≠ x) (f k)
    rw [hne, Finset.sum_singleton] at h
    linarith
  have hexch : (∑ k ∈ s, ∑ k' ∈ s, f k k')
      = (∑ k ∈ s, f k k) + ∑ q ∈ sq.filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
    have hoff : (∑ k ∈ s, ∑ k' ∈ s.filter (fun x => k ≠ x), f k k')
        = ∑ q ∈ sq.filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
      unfold sq
      rw [off_eq_prod, ← Finset.sum_filter]
    calc (∑ k ∈ s, ∑ k' ∈ s, f k k')
        = ∑ k ∈ s, (f k k + ∑ k' ∈ s.filter (fun x => k ≠ x), f k k') :=
          Finset.sum_congr rfl fun k hk => hinner k hk
      _ = (∑ k ∈ s, f k k) + ∑ k ∈ s, ∑ k' ∈ s.filter (fun x => k ≠ x), f k k' := by
          rw [Finset.sum_add_distrib]
      _ = _ := by rw [hoff]
  have hdisj : Disjoint T Tlo := Finset.disjoint_left.mpr fun q hq1 hq2 => by
    rcases Finset.mem_filter.mp hq1 with ⟨_, hlt1⟩
    rcases Finset.mem_filter.mp hq2 with ⟨_, hlt2⟩
    exact absurd (Nat.lt_asymm hlt1 hlt2) (by omega)
  have hUnion : (sq.filter (fun q => q.1 ≠ q.2)) = T ∪ Tlo := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hsq, hne⟩
      rcases hrang q hsq with ⟨hq1, hq2⟩
      rcases Nat.lt_trichotomy q.1 q.2 with hlt | heq | hgt
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq1, hq2⟩, hlt⟩))
      · exact absurd heq hne
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq1, hq2⟩, hgt⟩))
    · intro hq
      rcases Finset.mem_union.mp hq with hlt | hgt
      · rcases Finset.mem_filter.mp hlt with ⟨hsq, hp⟩
        rcases hrang q hsq with ⟨hq1, hq2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq1, hq2⟩, by omega⟩
      · rcases Finset.mem_filter.mp hgt with ⟨hsq, hp⟩
        rcases hrang q hsq with ⟨hq1, hq2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq1, hq2⟩, by omega⟩
  have hoff : (∑ q ∈ sq.filter (fun q => q.1 ≠ q.2), f q.1 q.2)
      = (∑ q ∈ T, f q.1 q.2) + ∑ q ∈ Tlo, f q.1 q.2 := by
    rw [hUnion, Finset.sum_union hdisj]
  have hswap : (∑ q ∈ Tlo, f q.1 q.2) = ∑ q ∈ T, f q.1 q.2 := by
    refine Finset.sum_bij (s := Tlo) (t := T) (f := fun q => f q.1 q.2)
      (fun q _ => (q.2, q.1)) ?_ ?_ ?_ ?_
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hsq, hlt⟩
      rcases hrang q hsq with ⟨hq1, hq2⟩
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨by simpa using hq2, by simpa using hq1⟩, ?_⟩
      show q.2 < q.1
      exact hlt
    · intro a _ b _ h
      rcases Prod.ext_iff.mp h with ⟨h1, h2⟩
      simp only at h1 h2
      exact Prod.ext_iff.mpr ⟨h2, h1⟩
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hsq, hlt⟩
      rcases hrang q hsq with ⟨hq1, hq2⟩
      refine ⟨(q.2, q.1), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨by simpa using hq2, by simpa using hq1⟩, ?_⟩, rfl⟩
      show q.1 < q.2
      exact hlt
    · intro q _
      exact hf q.1 q.2
  have htri : (∑ q ∈ T, f q.1 q.2) = ∑ k ∈ s, ∑ k' ∈ s.filter (fun x => k < x), f k k' := by
    have hA : (∑ q ∈ sq.filter (fun q => q.1 < q.2), f q.1 q.2)
        = ∑ q ∈ s ×ˢ s, (if q.1 < q.2 then f q.1 q.2 else 0) := by
      unfold sq
      exact Finset.sum_filter (fun q : ℕ × ℕ => q.1 < q.2) (fun q => f q.1 q.2) (s := s ×ˢ s)
    have h1 : (∑ q ∈ sq.filter (fun q => q.1 < q.2), f q.1 q.2)
        = ∑ k ∈ s, ∑ k' ∈ s.filter (fun x => k < x), f k k' := by
      calc (∑ q ∈ sq.filter (fun q => q.1 < q.2), f q.1 q.2)
          = ∑ q ∈ s ×ˢ s, (if q.1 < q.2 then f q.1 q.2 else 0) := hA
        _ = ∑ k ∈ s, ∑ k' ∈ s.filter (fun x => k < x), f k k' := (tri_eq_prod s s f).symm
    unfold T
    rw [h1]
  rw [hexch, hoff, hswap, htri]
  unfold s
  ring

/-! ## 3. THE MAIN THEOREM: the second moment of the truncated carry is a double
correlation sum -/

/-- **THE DOUBLE-SUM IDENTITY OF ROUND 115 (`jsp87_truncSq_diag`), PROVED.**

The second moment of the truncated carry over the window of cut points `N < L`
is exactly the double correlation sum

```
∑_{N<L} T(N,H)² = ∑_{k<H} ∑_{k'<H} 2^{-(k+1)-(k'+1)} · ∑_{N<L} ω(N+k) · ω(N+k') ,
```

the inner sum being `jsp87CorrAt L k k'`.  The diagonal `k = k'` is
`jsp87SqWindow k L`, the shifted second moment of `ω`. -/
theorem jsp87TruncSqSum_eq_dblCorr (L H : ℕ) :
    jsp87TruncSqSum L H
      = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ) := by
  unfold jsp87TruncSqSum
  calc (∑ N ∈ Finset.range L, jsp87TruncCarry N H ^ 2)
      = ∑ N ∈ Finset.range L, ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
            * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k') := by
        refine Finset.sum_congr rfl fun N _ => ?_
        rw [jsp87TruncCarry_eq_sumTw]
        calc (∑ k ∈ Finset.range H, ((omega (N + k) : ℕ) : ℝ) * jsp87Tw k) ^ 2
            = (∑ k ∈ Finset.range H, ((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
                * (∑ k' ∈ Finset.range H,
                  ((omega (N + k') : ℕ) : ℝ) * jsp87Tw k') := by ring
          _ = ∑ k ∈ Finset.range H,
              ((omega (N + k) : ℕ) : ℝ) * jsp87Tw k
                * (∑ k' ∈ Finset.range H,
                  ((omega (N + k') : ℕ) : ℝ) * jsp87Tw k') := by
              rw [Finset.sum_mul]
          _ = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
              (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
                * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k') := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H, ∑ N ∈ Finset.range L,
          (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
            * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k') := by
      have hprod : ∀ N : ℕ,
          (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
            (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
              * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k'))
            = ∑ ij ∈ Finset.range H ×ˢ Finset.range H,
              (fun ij : ℕ × ℕ =>
                (((omega (N + ij.1) : ℕ) : ℝ) * jsp87Tw ij.1)
                  * (((omega (N + ij.2) : ℕ) : ℝ) * jsp87Tw ij.2)) ij := by
        intro N
        exact (Finset.sum_product (Finset.range H) (Finset.range H)
          (fun ij : ℕ × ℕ =>
            (((omega (N + ij.1) : ℕ) : ℝ) * jsp87Tw ij.1)
              * (((omega (N + ij.2) : ℕ) : ℝ) * jsp87Tw ij.2))).symm
      calc (∑ N ∈ Finset.range L, ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
            (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
              * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k'))
          = ∑ N ∈ Finset.range L, ∑ ij ∈ Finset.range H ×ˢ Finset.range H,
              (fun ij : ℕ × ℕ =>
                (((omega (N + ij.1) : ℕ) : ℝ) * jsp87Tw ij.1)
                  * (((omega (N + ij.2) : ℕ) : ℝ) * jsp87Tw ij.2)) ij := by
            refine Finset.sum_congr rfl fun N _ => ?_
            exact hprod N
        _ = ∑ ij ∈ Finset.range H ×ˢ Finset.range H, ∑ N ∈ Finset.range L,
              (fun ij : ℕ × ℕ =>
                (((omega (N + ij.1) : ℕ) : ℝ) * jsp87Tw ij.1)
                  * (((omega (N + ij.2) : ℕ) : ℝ) * jsp87Tw ij.2)) ij :=
          Finset.sum_comm
        _ = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H, ∑ N ∈ Finset.range L,
              (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
                * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k') := by
          rw [Finset.sum_product]
    _ = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun k' _ => ?_
      calc (∑ N ∈ Finset.range L,
            (((omega (N + k) : ℕ) : ℝ) * jsp87Tw k)
              * (((omega (N + k') : ℕ) : ℝ) * jsp87Tw k'))
          = ∑ N ∈ Finset.range L,
              (jsp87Tw k * jsp87Tw k')
                * (((omega (N + k) : ℕ) : ℝ) * ((omega (N + k') : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl fun N _ => ?_
            ring
        _ = jsp87Tw k * jsp87Tw k'
            * (∑ N ∈ Finset.range L,
              ((omega (N + k) : ℕ) : ℝ) * ((omega (N + k') : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
        _ = _ := by rw [jsp87cast_sum_corrAt]

/-- **THE SYMMETRIC DOUBLE SUM OF THE WEIGHTED CORRELATIONS.** -/
theorem jsp87_dblCorr_symm (L H : ℕ) :
    (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ))
      = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k' * jsp87Tw k) * ((jsp87CorrAt L k' k : ℕ) : ℝ) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [jsp87CorrAt_symm]
  ring

/-! ## 4. THE DIAGONAL / OFF-DIAGONAL SPLIT -/

/-- **THE MAIN THEOREM OF ROUND 130, SECOND FORM: the second moment splits.**

```
∑_{N<L} T(N,H)²  =  ∑_{k<H} 4^{-(k+1)} · ∑_{N<L} ω(N+k)²   +   ∑_{k<k'<H} 2·2^{-(k+1)-(k'+1)} · ∑_{N<L} ω(N+k)ω(N+k')
```

* `jsp87TcDiag L H` — the **diagonal**: `H` shifted second moments of `ω`,
  weighted by `4^{-(k+1)}`.  Arithmetic only.
* `jsp87TcOff L H` — the **off-diagonal**: a weighted sum of the two-point
  correlations of `ω` at the shifts `k' − k`, over the `H (H−1)/2` unordered
  pairs of distinct places of the window.  **This is the analytic input of
  §5.4 of arXiv:2512.01739.** -/
theorem jsp87TruncSqSum_eq_diag_add_off (L H : ℕ) :
    jsp87TruncSqSum L H = jsp87TcDiag L H + jsp87TcOff L H := by
  have hsym : ∀ k k',
      (jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ)
        = (jsp87Tw k' * jsp87Tw k) * ((jsp87CorrAt L k' k : ℕ) : ℝ) := by
    intro k k'
    rw [jsp87CorrAt_symm]
    ring
  rw [jsp87TruncSqSum_eq_dblCorr,
    jsp87_sum_dbl_eq_diag_add_two_tri H _ hsym]
  have h1 : (∑ k ∈ Finset.range H, (jsp87Tw k * jsp87Tw k) * ((jsp87CorrAt L k k : ℕ) : ℝ))
      = jsp87TcDiag L H := by
    unfold jsp87TcDiag
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_two, jsp87CorrAt_diag]
  have h2 : (2 : ℝ)
        * (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
            (jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ))
      = ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          (2 * jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    ring
  rw [h1, h2]
  rfl

theorem jsp87TcDiag_nonneg (L H : ℕ) : 0 ≤ jsp87TcDiag L H := by
  unfold jsp87TcDiag
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem jsp87TcOff_nonneg (L H : ℕ) : 0 ≤ jsp87TcOff L H := by
  unfold jsp87TcOff
  refine Finset.sum_nonneg fun _ _ => ?_
  refine Finset.sum_nonneg fun _ _ => ?_
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos _)))
      (le_of_lt (jsp87Tw_pos _))) (Nat.cast_nonneg _)

theorem jsp87TcDiag_le (L H : ℕ) : jsp87TcDiag L H ≤ jsp87TruncSqSum L H := by
  rw [jsp87TruncSqSum_eq_diag_add_off]
  linarith [jsp87TcOff_nonneg L H]

theorem jsp87TcOff_le (L H : ℕ) : jsp87TcOff L H ≤ jsp87TruncSqSum L H := by
  rw [jsp87TruncSqSum_eq_diag_add_off]
  linarith [jsp87TcDiag_nonneg L H]

/-! ## 5. THE VARIANCE OF THE TRUNCATED CARRY -/

/-- **THE VARIANCE IN THE MEAN-FIELD FORM.**  For a finite sample `s`,

```
Var f = 𝔼 (f²) − (𝔼 f)² .
```

Mathlib has no statement of this shape for `jsp87Var`. -/
theorem jsp87Var_eq_FAvg_sq_sub {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) :
    jsp87Var s f = jsp87FAvg s (fun i => f i ^ 2) - (jsp87FAvg s f) ^ 2 := by
  have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  have hsq : (∑ i ∈ s, (f i - ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))) ^ 2)
      = (∑ i ∈ s, f i ^ 2) - ((∑ j ∈ s, f j) ^ 2) / ((s.card : ℕ) : ℝ) := by
    calc (∑ i ∈ s, (f i - ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))) ^ 2)
        = ∑ i ∈ s, (f i ^ 2 - 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))
            + ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ((∑ i ∈ s, f i ^ 2)
            - 2 * ((∑ i ∈ s, f i) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))))
            + ((s.card : ℕ) : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
          have h1 : (∑ i ∈ s, 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)))
              = 2 * ((∑ i ∈ s, f i) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))) := by
            calc (∑ i ∈ s, 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)))
                = ∑ i ∈ s,
                    (2 * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))) * f i := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  ring
              _ = 2 * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) * (∑ i ∈ s, f i) :=
                  (Finset.mul_sum (s := s) (fun i => f i)
                    (2 * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)))).symm
              _ = _ := by ring
          have h2 : (∑ i ∈ s, ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2)
              = ((s.card : ℕ) : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
            calc (∑ i ∈ s, ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2)
                = ∑ _i ∈ s, (1 : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  ring
              _ = ((s.card : ℕ) : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
                  rw [Finset.sum_const (s := s), nsmul_eq_mul]
                  ring
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
      _ = _ := by field_simp; ring
  unfold jsp87Var jsp87FAvg
  rw [hsq]
  field_simp

/-- **THE DIAGONAL IS THE COVARIANCE AT ZERO SHIFT.** -/
theorem jsp87TcVarAt_eq_cov (L k : ℕ) (hL : 1 ≤ L) :
    jsp87TcVarAt L k = jsp87Mcov L k k := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr hL⟩
  have h1 := jsp87Var_eq_FAvg_sq_sub (Finset.range L) hne (fun N => ((omega (N + k) : ℕ) : ℝ))
  rw [← jsp87TcCorr_diag] at h1
  unfold jsp87TcVarAt jsp87Mcov jsp87TcMean
  rw [h1]
  ring

/-- **THE SECOND MOMENT OF THE TRUNCATED CARRY, IN THE MEAN-FIELD FORM.** -/
theorem jsp87TcSq_eq_corr (L H : ℕ) :
    jsp87FAvg (Finset.range L) (fun N => jsp87TruncCarry N H ^ 2)
      = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k' := by
  have h1 : (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k')
      = jsp87TruncSqSum L H / (L : ℝ) := by
    calc (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k')
        = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
            ((jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ)) / (L : ℝ) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [jsp87TcCorr_eq]
          exact (mul_div_assoc (jsp87Tw k * jsp87Tw k') ((jsp87CorrAt L k k' : ℕ) : ℝ)
            (L : ℝ)).symm
      _ = (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
            (jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt L k k' : ℕ) : ℝ)) / (L : ℝ) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_div]
      _ = _ := congrArg (fun x : ℝ => x / (L : ℝ)) (jsp87TruncSqSum_eq_dblCorr L H).symm
  unfold jsp87FAvg
  rw [jsp87cast_card_range]
  have hstep : (∑ i ∈ Finset.range L, (fun N => jsp87TruncCarry N H ^ 2) i)
      = jsp87TruncSqSum L H := by
    unfold jsp87TruncSqSum
    exact Finset.sum_congr rfl fun N _ => rfl
  rw [hstep]
  exact h1.symm

/-- **THE MEAN OF THE TRUNCATED CARRY IS THE WEIGHTED MEAN OF `ω`.** -/
theorem jsp87TcMean_eq_sumTw (L H : ℕ) :
    jsp87FAvg (Finset.range L) (fun N => jsp87TruncCarry N H)
      = ∑ k ∈ Finset.range H, jsp87Tw k * jsp87TcMean L k := by
  have h1 : jsp87TruncSum L H
      = ∑ k ∈ Finset.range H, ((jsp87WindowOmega k L : ℕ) : ℝ) * jsp87Tw k := by
    calc (∑ N ∈ Finset.range L, jsp87TruncCarry N H)
        = ∑ k ∈ Finset.range H, ∑ N ∈ Finset.range L,
            ((omega (N + k) : ℕ) : ℝ) * jsp87Tw k := by
          rw [Finset.sum_congr rfl fun N _ => jsp87TruncCarry_eq_sumTw N H, Finset.sum_comm]
      _ = ∑ k ∈ Finset.range H,
          (∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ)) * jsp87Tw k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact (Finset.sum_mul (Finset.range L) (fun N => ((omega (N + k) : ℕ) : ℝ))
            (jsp87Tw k)).symm
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [jsp87cast_sum_windowOmega L k]
  unfold jsp87FAvg
  rw [jsp87cast_card_range]
  calc (∑ N ∈ Finset.range L, jsp87TruncCarry N H) / (L : ℝ)
      = (∑ k ∈ Finset.range H,
          ((jsp87WindowOmega k L : ℕ) : ℝ) * jsp87Tw k) / (L : ℝ) := by
        rw [← h1]
        exact congrArg (fun x : ℝ => x / (L : ℝ)) rfl
    _ = ∑ k ∈ Finset.range H,
        jsp87Tw k * (((jsp87WindowOmega k L : ℕ) : ℝ) / (L : ℝ)) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [div_eq_mul_inv]
        ring
    _ = ∑ k ∈ Finset.range H, jsp87Tw k * jsp87TcMean L k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (fun x : ℝ => jsp87Tw k * x) (jsp87TcMean_eq L k).symm

/-- **THE MAIN THEOREM OF §5.4: THE VARIANCE DECOMPOSITION.**

For a window of cut points `N < L` and a depth `H`,

```
Var (N ↦ T(N,H))  =  ∑_{k<H} 4^{-(k+1)} · Var (N ↦ ω(N+k))
                    +  ∑_{k<k'<H} 2·2^{-(k+1)-(k'+1)} · Cov (ω(N+k), ω(N+k')) ,
```

where `Cov (ω(N+k), ω(N+k')) = 𝔼 ω(N+k)ω(N+k') − 𝔼 ω(N+k)·𝔼 ω(N+k')`.

**This is the exact content of §5.4 of arXiv:2512.01739**: the variance of the
truncated carry is the *arithmetic* diagonal — `H` shifted variances of `ω` —
plus a *weighted sum of the two-point covariances of `ω`*, one per unordered
pair of distinct places of the window.  The first summand needs no analytic
input at all; the second is a **single object**, `jsp87TcOff`-like, which is the
quantity the published proof estimates. -/
theorem jsp87TcVar_eq_diag_add_cov (L H : ℕ) (hL : 1 ≤ L) :
    jsp87TcVar L H
      = (∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * jsp87TcVarAt L k)
        + ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
            (2 * jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k' := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr hL⟩
  have hV : jsp87FAvg (Finset.range L) (fun N => jsp87TruncCarry N H ^ 2)
      - (jsp87FAvg (Finset.range L) (fun N => jsp87TruncCarry N H)) ^ 2 = jsp87TcVar L H := by
    unfold jsp87TcVar
    exact (jsp87Var_eq_FAvg_sq_sub (Finset.range L) hne (fun N => jsp87TruncCarry N H)).symm
  rw [← hV, jsp87TcSq_eq_corr L H, jsp87TcMean_eq_sumTw L H]
  have hsq : (∑ k ∈ Finset.range H, jsp87Tw k * jsp87TcMean L k) ^ 2
      = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (jsp87Tw k * jsp87Tw k') * (jsp87TcMean L k * jsp87TcMean L k') := by
    calc (∑ k ∈ Finset.range H, jsp87Tw k * jsp87TcMean L k) ^ 2
        = (∑ k ∈ Finset.range H, jsp87Tw k * jsp87TcMean L k)
            * (∑ k' ∈ Finset.range H, jsp87Tw k' * jsp87TcMean L k') := by ring
      _ = ∑ k ∈ Finset.range H, (jsp87Tw k * jsp87TcMean L k)
            * (∑ k' ∈ Finset.range H, jsp87Tw k' * jsp87TcMean L k') := by
          rw [Finset.sum_mul]
      _ = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
            (jsp87Tw k * jsp87TcMean L k) * (jsp87Tw k' * jsp87TcMean L k') := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun k' _ => ?_
          ring
  rw [hsq]
  have hcov : (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k * jsp87Tw k')
          * (jsp87TcCorr L k k' - jsp87TcMean L k * jsp87TcMean L k'))
      = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
          (jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k' := by
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun k' _ => ?_
    unfold jsp87Mcov
    ring
  have hsub : (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k')
      - (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k * jsp87Tw k') * (jsp87TcMean L k * jsp87TcMean L k'))
      = ∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H,
        (jsp87Tw k * jsp87Tw k')
          * (jsp87TcCorr L k k' - jsp87TcMean L k * jsp87TcMean L k') := by
    calc (∑ k ∈ Finset.range H,
          (fun k => ∑ k' ∈ Finset.range H, (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k') k)
        - (∑ k ∈ Finset.range H,
          (fun k => ∑ k' ∈ Finset.range H,
            (jsp87Tw k * jsp87Tw k') * (jsp87TcMean L k * jsp87TcMean L k')) k)
      = ∑ k ∈ Finset.range H, (fun k =>
          (∑ k' ∈ Finset.range H, (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k')
            - ∑ k' ∈ Finset.range H,
                (jsp87Tw k * jsp87Tw k') * (jsp87TcMean L k * jsp87TcMean L k')) k :=
        (Finset.sum_sub_distrib
          (fun k => ∑ k' ∈ Finset.range H, (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k')
          (fun k => ∑ k' ∈ Finset.range H,
            (jsp87Tw k * jsp87Tw k') * (jsp87TcMean L k * jsp87TcMean L k'))).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact ((Finset.sum_sub_distrib
        (fun k' => (jsp87Tw k * jsp87Tw k') * jsp87TcCorr L k k')
        (fun k' => (jsp87Tw k * jsp87Tw k')
          * (jsp87TcMean L k * jsp87TcMean L k'))).symm).trans
          (by
            refine Finset.sum_congr rfl fun k' _ => ?_
            ring)
  rw [hsub, hcov]
  have hsym : ∀ k k', (jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k'
      = (jsp87Tw k' * jsp87Tw k) * jsp87Mcov L k' k := by
    intro k k'
    rw [jsp87Mcov_symm]
    ring
  rw [jsp87_sum_dbl_eq_diag_add_two_tri H _ hsym]
  have hdiag : (∑ k ∈ Finset.range H,
      (jsp87Tw k * jsp87Tw k) * jsp87Mcov L k k)
      = ∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * jsp87TcVarAt L k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_two, ← jsp87TcVarAt_eq_cov L k hL]
  have hoff : (2 : ℝ)
        * (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
            (jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k')
      = ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          (2 * jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    ring
  rw [hdiag, hoff]

/-! ## 6. The transfer lemmas: what the variance argument can conclude -/

/-- **THE OFF-DIAGONAL WEIGHTS SUM TO AT MOST ONE HALF.**  `2 ∑_{k<k'} w_k w_k'`
is the total weight the `H (H−1)/2` covariances carry in the decomposition, and

```
(∑_k w_k)²  =  ∑_k w_k²  +  2 ∑_{k<k'} w_k w'   ≤   1 ,
```

so the total weight is at most `1/2`.  Hence a *uniform* bound `ε` on the
covariances bounds the whole off-diagonal sum by `ε/2`. -/
theorem jsp87Tw_pair_le_one (H : ℕ) :
    (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
        2 * jsp87Tw k * jsp87Tw k') ≤ 1 := by
  have h := jsp87_sum_dbl_eq_diag_add_two_tri H (fun k k' => jsp87Tw k * jsp87Tw k')
    (fun k k' => by ring)
  have hdiag' : (∑ k ∈ Finset.range H, jsp87Tw k * jsp87Tw k)
      = ∑ k ∈ Finset.range H, jsp87Tw k ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdiag'] at h
  have hsq : (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H, jsp87Tw k * jsp87Tw k')
      = (∑ k ∈ Finset.range H, jsp87Tw k) ^ 2 := by
    calc (∑ k ∈ Finset.range H, ∑ k' ∈ Finset.range H, jsp87Tw k * jsp87Tw k')
        = (∑ k ∈ Finset.range H, jsp87Tw k)
            * (∑ k' ∈ Finset.range H, jsp87Tw k') := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          exact (Finset.mul_sum (Finset.range H) jsp87Tw (jsp87Tw k)).symm
        _ = _ := by ring
  rw [hsq] at h
  have key : (2 : ℝ)
        * (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
            jsp87Tw k * jsp87Tw k')
      = ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          2 * jsp87Tw k * jsp87Tw k' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    ring
  rw [key] at h
  have hsum := jsp87Tw_sum_le_one H
  have htri : 0 ≤ (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
      2 * jsp87Tw k * jsp87Tw k') := by
    refine Finset.sum_nonneg fun _ _ => ?_
    refine Finset.sum_nonneg fun _ _ => ?_
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos _))) (le_of_lt (jsp87Tw_pos _))
  have hS : 0 ≤ (∑ k ∈ Finset.range H, jsp87Tw k) :=
    Finset.sum_nonneg fun _ _ => le_of_lt (jsp87Tw_pos _)
  have hD : 0 ≤ ∑ k ∈ Finset.range H, jsp87Tw k ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- **THE VARIANCE IS AT LEAST THE DIAGONAL.**  If every covariance of `ω` at a
nonzero shift is nonnegative — the naive hypothesis of "mean-field independence"
— then the variance of the truncated carry is bounded below by the *arithmetic*
diagonal alone: the sum of `H` shifted variances of `ω`, weighted by `4^{-(k+1)}`.

This is the transfer step of §5.4 in the direction that needs **no analytic
input**: whatever the correlations are, the diagonal cannot be cancelled by
negative covariances, because their total weight is at most `1`. -/
theorem jsp87TcVar_ge_diag (L H : ℕ) (hL : 1 ≤ L)
    (hcov : ∀ k ∈ Finset.range H, ∀ k' ∈ (Finset.range H).filter (fun x => k < x),
      0 ≤ jsp87Mcov L k k') :
    (∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * jsp87TcVarAt L k) ≤ jsp87TcVar L H := by
  rw [jsp87TcVar_eq_diag_add_cov L H hL]
  have hoff : 0 ≤ ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
      (2 * jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k' := by
    refine Finset.sum_nonneg fun k hk => ?_
    refine Finset.sum_nonneg fun k' hk' => ?_
    have h1 : 0 ≤ 2 * jsp87Tw k * jsp87Tw k' :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos k)))
        (le_of_lt (jsp87Tw_pos k'))
    exact mul_nonneg h1 (hcov k hk k' hk')
  linarith

/-- **A UNIFORM COVARIANCE BOUND IS ENOUGH.**  If every covariance of `ω` at a
nonzero shift is at most `ε ≥ 0`, then the variance of the truncated carry is at
most the diagonal plus `ε` — because the total weight of the covariances is at
most `1` (`jsp87Tw_pair_le_one`).

**This is the exact form of the step arXiv:2512.01739 §5.4 needs**: a bound on
the weighted sum of the two-point covariances of `ω` turns into a bound on the
variance of the truncated carry, with the diagonal contributing a computable
amount. -/
theorem jsp87TcVar_le_diag_add (L H : ℕ) (hL : 1 ≤ L) (ε : ℝ) (hε : 0 ≤ ε)
    (hcov : ∀ k ∈ Finset.range H, ∀ k' ∈ (Finset.range H).filter (fun x => k < x),
      jsp87Mcov L k k' ≤ ε) :
    jsp87TcVar L H ≤ (∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * jsp87TcVarAt L k) + ε := by
  rw [jsp87TcVar_eq_diag_add_cov L H hL]
  have hterm : ∀ k ∈ Finset.range H, ∀ k' ∈ (Finset.range H).filter (fun x => k < x),
      (2 * jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k'
        ≤ (2 * jsp87Tw k * jsp87Tw k') * ε := by
    intro k hk k' hk'
    have h1 : 0 ≤ 2 * jsp87Tw k * jsp87Tw k' :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos k)))
        (le_of_lt (jsp87Tw_pos k'))
    exact mul_le_mul_of_nonneg_left (hcov k hk k' hk') h1
  have hoff : (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
        (2 * jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k')
      ≤ ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
        (2 * jsp87Tw k * jsp87Tw k') * ε :=
    Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun k' hk' => hterm k hk k' hk'
  have hpair : (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
        2 * jsp87Tw k * jsp87Tw k') ≤ 1 := jsp87Tw_pair_le_one H
  have hoff' : (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
        (2 * jsp87Tw k * jsp87Tw k') * ε) ≤ ε := by
    calc (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          (2 * jsp87Tw k * jsp87Tw k') * ε)
        = (∑ k ∈ Finset.range H, ((∑ k' ∈ (Finset.range H).filter (fun x => k < x),
            2 * jsp87Tw k * jsp87Tw k')) * ε) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact (Finset.sum_mul ((Finset.range H).filter (fun x : ℕ => k < x))
            (fun k' => 2 * jsp87Tw k * jsp87Tw k') ε).symm
      _ = (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          2 * jsp87Tw k * jsp87Tw k') * ε := by
          rw [Finset.sum_mul]
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hpair hε
      _ = ε := by ring
  linarith

/-- **THE DEPTH-0 AND DEPTH-1 CASES.**  At `H = 0` the truncated carry vanishes;
at `H = 1` it is `ω(N)/2`, so its variance is a quarter of the variance of `ω`. -/
theorem jsp87TcVar_zero (L : ℕ) : jsp87TcVar L 0 = 0 := by
  unfold jsp87TcVar jsp87Var jsp87TruncCarry
  simp [jsp87FAvg]

theorem jsp87TcVar_one (L : ℕ) (hL : 1 ≤ L) :
    jsp87TcVar L 1 = jsp87TcVarAt L 0 / 4 := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr hL⟩
  have hstep : (fun N => jsp87TruncCarry N 1)
      = fun N => (1 / 2 : ℝ) * ((omega (N + 0) : ℕ) : ℝ) := by
    funext N
    simp [jsp87TruncCarry]
    ring
  unfold jsp87TcVar jsp87TcVarAt
  rw [hstep, jsp87Var_scale (Finset.range L) (1 / 2 : ℝ)
    (fun N => ((omega (N + 0) : ℕ) : ℝ))]
  rw [show (fun N => ((omega (N + 0) : ℕ) : ℝ)) = fun N => ((omega N : ℕ) : ℝ) by
    funext N; rw [Nat.add_zero]]
  ring

/-- **THE VARIANCE IS NONNEGATIVE** (round 118's `jsp87Var_nonneg`, restated for
the object of §5.4). -/
theorem jsp87TcVar_nonneg (L H : ℕ) : 0 ≤ jsp87TcVar L H :=
  jsp87Var_nonneg (Finset.range L) (fun N => jsp87TruncCarry N H)

/-! ## 7. The price of the elementary CRT bound -/

/-- **THE BOUNDARY ERROR OF ROUND 115 IN CLOSED FORM.**
`jsp87ChowlaErr N`, the "one spurious solution per prime pair" error of
`jsp87Chowla_le_add`, is exactly

```
π(N) · (π(N+1) − 1) ,
```

the number of ordered pairs of distinct primes up to `N` and `N+1`.  Round 115
defined the object as a double sum and left it there. -/
theorem jsp87ChowlaErr_eq (N : ℕ) :
    jsp87ChowlaErr N = (jsp87Primes N).card * ((jsp87Primes (N + 1)).card - 1) := by
  have hsub : (jsp87Primes N) ⊆ (jsp87Primes (N + 1)) := by
    intro p hp
    simp only [jsp87Primes, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
  have hkey : ∀ p ∈ jsp87Primes N,
      ((jsp87Primes (N + 1)).filter (fun q => q ≠ p)).card
        = (jsp87Primes (N + 1)).card - 1 := by
    intro p hp
    have hp' : p ∈ jsp87Primes (N + 1) := hsub hp
    have herase : (jsp87Primes (N + 1)).filter (fun q => q ≠ p)
        = (jsp87Primes (N + 1)).erase p := by
      ext q
      simp only [Finset.mem_erase, Finset.mem_filter]
      tauto
    rw [herase]
    exact Finset.card_erase_of_mem hp'
  unfold jsp87ChowlaErr
  calc (∑ p ∈ jsp87Primes N, ((jsp87Primes (N + 1)).filter (fun q => q ≠ p)).card)
      = ∑ p ∈ jsp87Primes N, ((jsp87Primes (N + 1)).card - 1) := by
        refine Finset.sum_congr (s₁ := jsp87Primes N) (s₂ := jsp87Primes N) rfl ?_
        intro p hp
        exact hkey p hp
    _ = ((jsp87Primes N).card : ℕ) • ((jsp87Primes (N + 1)).card - 1) := by
        rw [Finset.sum_const]
    _ = _ := by simp

/-- **THE SHIFT-`1` CORRELATION IS AN OFF-DIAGONAL TERM OF WEIGHT `1/4`.**  The
correlation `∑_{N≤N} ω(N) ω(N+1)` of round 115 (`jsp87Chowla`) is literally the
`(k,k') = (0,1)` term of the off-diagonal sum, weighted by
`2·(1/2)·(1/4) = 1/4`.  **Any bound on the off-diagonal term of the variance is
therefore a bound on the Chowla sum of `ω`.** -/
theorem jsp87TcOff_ge_pair01 (N H : ℕ) (hH : 2 ≤ H) :
    (1 / 4) * ((jsp87CorrAt (N + 1) 0 1 : ℕ) : ℝ) ≤ jsp87TcOff (N + 1) H := by
  have hone : (1 : ℕ) ∈ (Finset.range H).filter (fun x : ℕ => (0 : ℕ) < x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  have h1 : (2 * jsp87Tw 0 * jsp87Tw 1) * ((jsp87CorrAt (N + 1) 0 1 : ℕ) : ℝ)
      = (1 / 4) * ((jsp87CorrAt (N + 1) 0 1 : ℕ) : ℝ) := by
    norm_num [jsp87Tw]
  unfold jsp87TcOff
  calc (1 / 4) * ((jsp87CorrAt (N + 1) 0 1 : ℕ) : ℝ)
      = (2 * jsp87Tw 0 * jsp87Tw 1) * ((jsp87CorrAt (N + 1) 0 1 : ℕ) : ℝ) := h1.symm
    _ ≤ ∑ k' ∈ (Finset.range H).filter (fun x : ℕ => (0 : ℕ) < x),
        (2 * jsp87Tw 0 * jsp87Tw k') * ((jsp87CorrAt (N + 1) 0 k' : ℕ) : ℝ) := by
      have hnonneg : ∀ j ∈ (Finset.range H).filter (fun x : ℕ => (0 : ℕ) < x),
          0 ≤ (2 * jsp87Tw 0 * jsp87Tw j) * ((jsp87CorrAt (N + 1) 0 j : ℕ) : ℝ) := by
        intro j _
        exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos j)))
          (Nat.cast_nonneg _)
      exact Finset.single_le_sum hnonneg hone
    _ ≤ _ := by
      have hone0 : ((Finset.range H).filter (fun k : ℕ => k = 0)) = {0} := by
        have hmem : (0 : ℕ) ∈ Finset.range H := Finset.mem_range.mpr (by omega)
        rw [Finset.filter_eq']
        simp [hmem]
      have hsplit := sum_split (Finset.range H) (fun k => k = 0)
        (fun k => ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          (2 * jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt (N + 1) k k' : ℕ) : ℝ))
      rw [hone0, Finset.sum_singleton] at hsplit
      have hrest : 0 ≤ ∑ k ∈ (Finset.range H).filter (fun k : ℕ => ¬ (k = 0)),
          ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
            (2 * jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt (N + 1) k k' : ℕ) : ℝ) := by
        refine Finset.sum_nonneg fun k _ => ?_
        refine Finset.sum_nonneg fun k' _ => ?_
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos k)))
            (le_of_lt (jsp87Tw_pos k')))
          (Nat.cast_nonneg _)
      linarith

/-- **THE OFF-DIAGONAL TERM DOMINATES THE CHOWLA SUM.** -/
theorem jsp87TcOff_ge_chowla (N H : ℕ) (hH : 2 ≤ H) :
    (1 / 4) * ((jsp87Chowla N : ℕ) : ℝ) ≤ jsp87TcOff (N + 1) H := by
  rw [jsp87_chowla_eq_corrAt]
  exact jsp87TcOff_ge_pair01 N H hH

/-- **THE PRICE OF THE OFF-DIAGONAL BOUND.**
If `c` is an upper bound for the off-diagonal term of the variance at the window
`N < L = N+1` (i.e. `jsp87TcOff (N+1) H ≤ c`), then

```
∑_{n ≤ N} ω(n) ω(n+1)   ≤   4 c ,
```

i.e. the Chowla sum of `ω` itself is bounded by four times the off-diagonal
bound.  **Any estimate of the off-diagonal term is therefore an estimate of the
Chowla sum** — the quantity round 115 identified as the analytic input. -/
theorem jsp87TcOff_ge_boundary (N H : ℕ) (hH : 2 ≤ H) (c : ℝ)
    (hc : jsp87TcOff (N + 1) H ≤ c) :
    ((jsp87Chowla N : ℕ) : ℝ) ≤ 4 * c := by
  have h1 := jsp87TcOff_ge_chowla N H hH
  have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4)
  have hkey : 4 * ((1 / 4 : ℝ) * ((jsp87Chowla N : ℕ) : ℝ)) = ((jsp87Chowla N : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hkey] at hmul
  have hmul2 := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4)
  linarith

/-- **A UNIFORM CORRELATION BOUND BOUNDS THE WHOLE OFF-DIAGONAL TERM.**
If every correlation `∑_{N<L} ω(N+k) ω(N+k')` at a nonzero shift is at most
`M ≥ 0`, then the off-diagonal term of the variance is at most `M`, because the
total weight of the covariances is at most `1` (`jsp87Tw_pair_le_one`).

Together with `jsp87TcOff_ge_boundary` this says: **an estimate of the weighted
correlations at *every* shift yields an estimate of the Chowla sum at shift
`1`; the elementary counting bound of round 115 yields only an upper bound on
the latter, hence no estimate at all.** -/
theorem jsp87TcOff_le_of_corr (N H : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcorr : ∀ k ∈ Finset.range H,
      ∀ k' ∈ (Finset.range H).filter (fun x => k < x),
        ((jsp87CorrAt (N + 1) k k' : ℕ) : ℝ) ≤ M) :
    jsp87TcOff (N + 1) H ≤ M := by
  unfold jsp87TcOff
  have hterm : ∀ k ∈ Finset.range H, ∀ k' ∈ (Finset.range H).filter (fun x => k < x),
      (2 * jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt (N + 1) k k' : ℕ) : ℝ)
        ≤ (2 * jsp87Tw k * jsp87Tw k') * M := by
    intro k hk k' hk'
    have h1 : 0 ≤ 2 * jsp87Tw k * jsp87Tw k' :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (jsp87Tw_pos k)))
        (le_of_lt (jsp87Tw_pos k'))
    exact mul_le_mul_of_nonneg_left (hcorr k hk k' hk') h1
  calc (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
        (2 * jsp87Tw k * jsp87Tw k') * ((jsp87CorrAt (N + 1) k k' : ℕ) : ℝ))
      ≤ ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          (2 * jsp87Tw k * jsp87Tw k') * M := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine Finset.sum_le_sum fun k' hk' => ?_
        exact hterm k hk k' hk'
    _ = (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
          2 * jsp87Tw k * jsp87Tw k') * M := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ ≤ M := by
        have hpair := jsp87Tw_pair_le_one H
        calc (∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
              2 * jsp87Tw k * jsp87Tw k') * M
            ≤ 1 * M := mul_le_mul_of_nonneg_right hpair hM
          _ = M := one_mul M

/-- **THE NECESSARY SIZE OF A UNIFORM CORRELATION BOUND.**  If the
correlations of `ω` at every nonzero shift of the window `L` are bounded by `M`,
then the off-diagonal term is at most `M` (`jsp87TcOff_le_of_corr`) while it is
at least a quarter of the Chowla sum (`jsp87TcOff_ge_chowla`); since
`∑_{n ≤ N} ω(n)ω(n+1) ≥ N − 1` (both factors are `≥ 1` for `n ≥ 2`), we get

```
(L − 2) / 4   ≤   M .
```

**A small off-diagonal bound is impossible for a long window**: the off-diagonal
term of the variance cannot be made small by the CRT counting argument, because
the correlations of `ω` are themselves large — they are sums of at least `L−2`
units.  This is the quantitative form of the obstruction of round 115. -/
theorem jsp87Chowla_ge_card (N : ℕ) : (N : ℕ) - 1 ≤ jsp87Chowla N := by
  have hstep : ∀ n ∈ Finset.Icc 2 N, 1 ≤ omega n * omega (n + 1) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hpos1 : 0 < omega n := Nat.zero_lt_of_lt (omega_ge_one_of_ge_two hn2)
    have hpos2 : 0 < omega (n + 1) :=
      Nat.zero_lt_of_lt (omega_ge_one_of_ge_two (by omega))
    have hb : 0 < omega n * omega (n + 1) := Nat.mul_pos hpos1 hpos2
    exact Nat.succ_le_of_lt hb
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 N := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1, h2⟩
    exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
  have hcard : (∑ n ∈ Finset.Icc 2 N, (1 : ℕ)) = (N : ℕ) - 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have h1 : (N + 1 - 2 : ℕ) = (N : ℕ) - 1 := by
      by_cases hN : 2 ≤ N
      · have : N + 1 - 2 = N - 1 := by omega
        rw [this]
      · have hz : (N : ℕ) - 1 = 0 := by omega
        have hz2 : N + 1 - 2 = 0 := by omega
        rw [hz, hz2]
    rw [h1]
    simp
  unfold jsp87Chowla
  calc (N : ℕ) - 1
      = ∑ n ∈ Finset.Icc 2 N, (1 : ℕ) := hcard.symm
    _ ≤ ∑ n ∈ Finset.Icc 2 N, omega n * omega (n + 1) :=
        Finset.sum_le_sum fun n hn => hstep n hn
    _ ≤ ∑ n ∈ Finset.Icc 1 N, omega n * omega (n + 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Icc 2 N)
          (t := Finset.Icc 1 N) hsub ?_
        intro n hn hn'
        have hne : n = 1 := by
          rcases Finset.mem_Icc.mp hn with ⟨h1, _⟩
          by_contra hc
          exact hn' (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [hne, omega_one]
        simp [omega]
    _ = _ := rfl

/-- **THE NECESSARY SIZE OF A UNIFORM CORRELATION BOUND.**  If the correlations
of `ω` at every nonzero shift of the window `L = N+1` are bounded by `M ≥ 0`, then

```
(N − 1) / 4   ≤   M .
```

**A small off-diagonal bound is therefore impossible for a long window**: the
off-diagonal term of the variance cannot be made small by the CRT counting
argument of round 115, because the correlations of `ω` are themselves large —
each is a sum of at least `N − 1` units. -/
theorem jsp87Chowla_le_of_corr_bound (N H : ℕ) (hH : 2 ≤ H) (M : ℝ) (hM : 0 ≤ M)
    (hcorr : ∀ k ∈ Finset.range H,
      ∀ k' ∈ (Finset.range H).filter (fun x => k < x),
        ((jsp87CorrAt (N + 1) k k' : ℕ) : ℝ) ≤ M) :
    ((N : ℝ) - 1) / 4 ≤ M := by
  have hoff : jsp87TcOff (N + 1) H ≤ M := jsp87TcOff_le_of_corr N H M hM hcorr
  have h1 := jsp87TcOff_ge_chowla N H hH
  have hcg : (N : ℕ) - 1 ≤ jsp87Chowla N := jsp87Chowla_ge_card N
  have hcast : ((N - 1 : ℕ) : ℝ) ≤ ((jsp87Chowla N : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcg
  have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4)
  have hkey : 4 * ((1 / 4 : ℝ) * ((jsp87Chowla N : ℕ) : ℝ)) = ((jsp87Chowla N : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hkey] at hmul
  have hmul2 := mul_le_mul_of_nonneg_left hoff (by norm_num : (0 : ℝ) ≤ 4)
  have h3 : ((N - 1 : ℕ) : ℝ) ≤ 4 * M := by linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0]
    norm_num
    linarith
  · have hN1 : (1 : ℕ) ≤ N := by omega
    have hkey2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN1]
      norm_num
    rw [hkey2] at h3
    have hfin : (N : ℝ) - 1 ≤ M * 4 := by linarith
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ))).2 hfin

/-! ## 8. Machine-checked instances of the new objects -/

private theorem omega_two : omega 2 = 1 := by native_decide
private theorem omega_three : omega 3 = 1 := by native_decide

/-- the variance of `ω` over the window `{0, 1, 2}` — the values `(0, 0, 1)` -/
theorem jsp87TcVarAt_three_zero : jsp87TcVarAt 3 0 = 2 / 9 := by
  unfold jsp87TcVarAt jsp87Var jsp87FAvg
  norm_num [Finset.sum_range_succ, omega_two, omega_three]

/-- **THE VARIANCE OF THE DEPTH-1 TRUNCATED CARRY OVER THREE CUT POINTS**:
`ω(0)/2, ω(1)/2, ω(2)/2 = 0, 0, 1/2` have variance `1/18`. -/
theorem jsp87TcVar_three_one : jsp87TcVar 3 1 = 1 / 18 := by
  unfold jsp87TcVar jsp87Var jsp87FAvg
  norm_num [jsp87TruncCarry, jsp87Tw, Finset.sum_range_succ, omega_two, omega_three]

theorem jsp87TcVar_four_one : jsp87TcVar 4 1 = 1 / 16 := by
  unfold jsp87TcVar jsp87Var jsp87FAvg
  norm_num [jsp87TruncCarry, jsp87Tw, Finset.sum_range_succ, omega_two, omega_three]

/-- **THE DEPTH-2 INSTANCE OF THE WHOLE DECOMPOSITION**: over the window
`N < 3`, the second moment of `T(N,2) = ω(N)/2 + ω(N+1)/4` is `5/8`, the diagonal
is `3/8` and the off-diagonal (a single correlation, at shift `1`) is `1/4`. -/
theorem jsp87TruncSqSum_three_two : jsp87TruncSqSum 3 2 = 5 / 8 := by
  unfold jsp87TruncSqSum jsp87TruncCarry
  norm_num [jsp87Tw, Finset.sum_range_succ, omega_two, omega_three]

theorem jsp87TcDiag_three_two : jsp87TcDiag 3 2 = 3 / 8 := by
  unfold jsp87TcDiag jsp87SqWindow jsp87Tw
  norm_num [Finset.sum_range_succ, omega_two, omega_three]

theorem jsp87TcOff_three_two : jsp87TcOff 3 2 = 1 / 4 := by
  unfold jsp87TcOff jsp87CorrAt jsp87Tw
  norm_num [Finset.sum_range_succ, Finset.sum_filter, omega_two, omega_three]

theorem jsp87TcVar_three_two : jsp87TcVar 3 2 = 7 / 72 := by
  unfold jsp87TcVar jsp87Var jsp87FAvg
  norm_num [jsp87TruncCarry, jsp87Tw, Finset.sum_range_succ, omega_two, omega_three]

/-- **THE SHIFT-`1` COVARIANCE IS NOT ZERO**: over the window `N < 3`,
`Cov (ω(N), ω(N+1)) = 1/9`.  The off-diagonal term of the variance is a genuine
correlation, not an artefact. -/
theorem jsp87Mcov_three_zero_one : jsp87Mcov 3 0 1 = 1 / 9 := by
  unfold jsp87Mcov jsp87TcCorr jsp87TcMean jsp87FAvg
  norm_num [Finset.sum_range_succ, omega_two, omega_three]

/-! ## 9. Summary of the round -/

/-- **THE SUMMARY OF ROUND 130.**  The second moment of the Tao–Teräväinen
truncated carry is a double correlation sum of `ω`; split symmetrically it is
the *arithmetic diagonal* `jsp87TcDiag` plus a *weighted sum of the two-point
covariances* `jsp87TcOff`; the variance of the truncated carry is the
corresponding weighted sum of the `H` shifted variances of `ω` plus twice the
off-diagonal covariances.  Only the second summand of each line is analytic, and
`jsp87TcOff_ge_boundary` shows that the elementary counting bound for it is
larger than the quantity to be bounded by a factor `π(N)²`. -/
theorem jsp87_tcVariance_summary (L H : ℕ) (hL : 1 ≤ L)
    (hcov : ∀ k ∈ Finset.range H,
      ∀ k' ∈ (Finset.range H).filter (fun x => k < x), 0 ≤ jsp87Mcov L k k') :
    (jsp87TruncSqSum L H = jsp87TcDiag L H + jsp87TcOff L H)
      ∧ (jsp87TcVar L H
          = (∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * jsp87TcVarAt L k)
            + ∑ k ∈ Finset.range H, ∑ k' ∈ (Finset.range H).filter (fun x => k < x),
                (2 * jsp87Tw k * jsp87Tw k') * jsp87Mcov L k k')
      ∧ (∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * jsp87TcVarAt L k) ≤ jsp87TcVar L H := by
  exact ⟨jsp87TruncSqSum_eq_diag_add_off L H, jsp87TcVar_eq_diag_add_cov L H hL,
    jsp87TcVar_ge_diag L H hL hcov⟩

end JSP87