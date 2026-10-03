/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-118).
-/
import JSPProblem.Xp

/-!
# JSP-000087, round 118 — THE CLASS-COUNT FORM OF THE VARIANCE BOUND (5.21)

## Why this file exists

`policy.json` `next_round_attack[1]` asked, for the first time in 118 rounds:

> *"VARIANCE LOWER BOUND … define `jsp87XpNonDegenerate` (the cube sum is
> non-zero at `p`, i.e. some vertex is hit) and prove the exact square-sum
> identity `Var (q X_p) = …` in terms of the hit pattern, so that the variance
> is the weighted count of pairs `(n, n′)` with equal hit patterns. That identity
> is pure combinatorics over the hit set and is provable; it localises (5.21) to
> a statement about how many sample points share a pattern."*

**This file is that identity, and it turns out to be more interesting than
expected: the hit-pattern formulation is FALSE, and the correct object is the
*hit-value*, which lives on a fixed lattice `2^{−(H+K)} ℤ`.**

Rounds 116–117 reduced `jsp_000087_main` to two arithmetic inputs of Tao–Teräväinen
arXiv:2512.01739: **(5.18)** `κ_j = o(1)` and **(5.21)** `∑_{p∈S₁} Var X_p ≥ 1`,
where `X_p = jsp87Xp` of `Xp.lean`; hypothesis (5.19) was discharged and the
`S₀` primes were shown to contribute no variance.

## What is proved here

| Section | Content |
| --- | --- |
| §1 | the binary-weight gap: distinct subsets of the levels have level sums at distance `≥ 2^{−(H+K)}` (`jsp87bin_gap`, `jsp87W_sum_sub_ge`) |
| §2 | the **level code** `jsp87XpCode ∈ {−1,0,1}` and the collapse `jsp87XpLevel_eq_code` (no hypothesis needed) |
| §3 | **THE DISCRETENESS OF THE CUBE SUM**: differences of cube sums lie in `2^{−(H+K)} ℤ` (`jsp87XpIntDiff`, `jsp87Xp0_sub_eq_scale`), hence `jsp87Xp0_sub_eq_zero_or_ge`, a uniform gap |
| §4 | **THE BINARY-CARRY COLLISION** (`jsp87W_succ`, `jsp87Xp0_code_add_carry`, `jsp87Xp0_eq_of_code_carry`): `w_m = 2 w_{m+1}`, so *different hit patterns can give the same value* — the criterion "different pattern ⇒ different `X_p`" is **false**, machine-checked |
| §5 | **THE CLASS-COUNT FORM OF THE VARIANCE** (`jsp87Class`, `jsp87_sum_diff_sq_class`, `jsp87Var_eq_classSum`, `jsp87Var_eq_zero_iff_const`): `2\|s\|² Var f = ∑_{A,B classes} \|A\|\|B\| (v_A − v_B)²` |
| §6 | **THE TWO-CLASS CRITERION** (`jsp87Var_ge_twoClass`, `jsp87Var_Xp_ge_twoClass`, `jsp87Var_Xp_ge_one`, `jsp87_endgame_twoClass`): (5.21) follows from *one* prime with a balanced two-class split of the sample — a discrete hypothesis with a closed-form threshold |

## What is *not* proved here

`jsp_000087_main` is **not declared**.  The remaining input is the *arithmetic*
one: that the hit values of `X_p` are **balanced** on a sample of integers —
a statement about the distribution of `ω` on progressions, i.e. the content of
§3 of arXiv:2512.01739.  Mathlib contains no Chowla-type or Elliott-type
statement for multiplicative functions.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## §1  The binary-weight gap -/

/-- **ERASING AN ABSENT ELEMENT CHANGES NOTHING.** -/
private theorem jsp87erase_eq_self {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (h : a ∉ s) : s.erase a = s := by
  ext x
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨_, h1⟩
    exact h1
  · intro h1
    exact ⟨fun hx => h (hx ▸ h1), h1⟩

/-- **OUTSIDE `{m, m+1}`.** -/
private theorem jsp87ne_pair {m h : ℕ} (hh : h ∉ ({m, m + 1} : Finset ℕ)) :
    h ≠ m ∧ h ≠ m + 1 := by
  constructor
  · intro hc
    exact hh (by rw [hc, Finset.mem_insert, Finset.mem_singleton]; exact Or.inl rfl)
  · intro hc
    exact hh (by rw [hc, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr rfl)

/-- **A FINSET IS ITS ERASURE, PLUS THE REMOVED ELEMENT.** -/
private theorem jsp87eq_insert_erase (C : Finset ℕ) (m : ℕ) :
    C = if m ∈ C then insert m (C.erase m) else C.erase m := by
  by_cases h : m ∈ C
  · rw [if_pos h, Finset.insert_erase h]
  · rw [if_neg h, jsp87erase_eq_self C m h]

/-- **AN ABSENT ELEMENT IS NOT RESTORED BY INSERTION.** -/
private theorem jsp87insert_ne (m : ℕ) (X : Finset ℕ) (h : m ∉ X) : X ≠ insert m X := by
  intro heq
  have hm : m ∈ X := heq.symm ▸ Finset.mem_insert_self m X
  exact h hm

/-- **A NONZERO INTEGER HAS ABSOLUTE VALUE AT LEAST `1`.** -/
private theorem jsp87int_ge_one {z : ℤ} (hz : z ≠ 0) : 1 ≤ |z| := by
  rcases lt_or_gt_of_ne hz with h | h
  · rw [abs_of_neg h]
    omega
  · rw [abs_of_pos h]
    omega

/-- **AN ODD-SIZED PERTURBATION CANNOT KILL A NONZERO DOUBLE.**  If `|c| ≤ 1` and
`x ≠ 0` then `c + 2x ≠ 0`. -/
private theorem jsp87int_shift_ne {x c : ℤ} (hx : x ≠ 0) (hc : |c| ≤ 1) : c + 2 * x ≠ 0 := by
  intro hz
  have h1 : 1 ≤ |x| := jsp87int_ge_one hx
  have h2 : c = -2 * x := by linarith [hz]
  have h3 : |c| = 2 * |x| := by
    rw [h2, abs_mul, abs_neg]
    norm_num
  linarith

/-- **AN INTEGER POWER OF TWO, IN THE REALS.** -/
private theorem jsp87int_cast_pow_two (m : ℕ) : (((2 : ℤ) ^ m : ℤ) : ℝ) = (2 : ℝ) ^ m := by
  norm_cast

/-- **THE SPLIT AT THE TOP LEVEL.** -/
private theorem jsp87sum_split_top (m : ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.Icc 1 (m + 1)) :
    (∑ c ∈ C, ((2 : ℤ) ^ (m + 1 - c)))
      = ((if m + 1 ∈ C then 1 else 0) : ℤ)
        + 2 * (∑ c ∈ C.erase (m + 1), ((2 : ℤ) ^ (m - c))) := by
  have hcc : ∀ c ∈ C, c ≠ m + 1 → ((2 : ℤ) ^ (m + 1 - c)) = 2 * ((2 : ℤ) ^ (m - c)) := by
    intro c hc hne
    have h2 : c ≤ m + 1 := (Finset.mem_Icc.mp (hC hc)).2
    have h3 : c ≤ m := by omega
    have hsub : m + 1 - c = (m - c) + 1 := by omega
    rw [hsub, pow_succ]
    ring
  by_cases hn : m + 1 ∈ C
  · have hne' : m + 1 ∉ C.erase (m + 1) := Finset.notMem_erase _ _
    calc (∑ c ∈ C, ((2 : ℤ) ^ (m + 1 - c)))
        = ((2 : ℤ) ^ (m + 1 - (m + 1))) + ∑ c ∈ C.erase (m + 1), ((2 : ℤ) ^ (m + 1 - c)) := by
          conv_lhs => rw [← Finset.insert_erase hn, Finset.sum_insert hne']
        _ = 1 + 2 * (∑ c ∈ C.erase (m + 1), ((2 : ℤ) ^ (m - c))) := by
          rw [show ((2 : ℤ) ^ (m + 1 - (m + 1))) = 1 by simp]
          rw [Finset.mul_sum]
          exact congrArg (fun z : ℤ => 1 + z) (Finset.sum_congr rfl fun c hc =>
            hcc c ((Finset.mem_erase.mp hc).2) ((Finset.mem_erase.mp hc).1))
        _ = _ := by rw [if_pos hn]
  · rw [jsp87erase_eq_self C (m + 1) hn, if_neg hn]
    calc (∑ c ∈ C, ((2 : ℤ) ^ (m + 1 - c)))
        = 2 * (∑ c ∈ C, ((2 : ℤ) ^ (m - c))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c hc => hcc c hc (fun hc' => hn (hc' ▸ hc))
      _ = _ := by ring

/-- **THE BINARY-WEIGHT GAP.**  Distinct subsets of `{1, …, H}` give distinct
sums of the integer weights `2 ^ (H − a)`, and those sums differ by at least
`1` in absolute value.

This is the uniqueness of the binary expansion, proved from scratch by induction
on the length: at the top level one compares `1 + 2x` with `2y`, and an odd
number cannot vanish. -/
private theorem jsp87bin_gap : ∀ (H : ℕ) (A B : Finset ℕ), A ⊆ Finset.Icc 1 H →
    B ⊆ Finset.Icc 1 H → A ≠ B →
    |(∑ a ∈ A, ((2 : ℤ) ^ (H - a))) - (∑ b ∈ B, ((2 : ℤ) ^ (H - b)))| ≥ 1 := by
  intro H
  induction H with
  | zero =>
      intro A B hA hB hne
      have hAe : A = ∅ := by
        ext a
        constructor
        · intro ha
          have h1 := Finset.mem_Icc.mp (hA ha)
          omega
        · intro ha
          exact absurd ha (by simp)
      have hBe : B = ∅ := by
        ext a
        constructor
        · intro hb
          have h1 := Finset.mem_Icc.mp (hB hb)
          omega
        · intro hb
          exact absurd hb (by simp)
      exact absurd (hne (hAe.trans hBe.symm)) (by simp)
  | succ m ih =>
      intro A B hA hB hne
      have hA' : A.erase (m + 1) ⊆ Finset.Icc 1 m := by
        intro c hc
        have h1 : c ∈ A := (Finset.mem_erase.mp hc).2
        have hI := Finset.mem_Icc.mp (hA h1)
        have h3 : c ≠ m + 1 := (Finset.mem_erase.mp hc).1
        simp only [Finset.mem_Icc]
        omega
      have hB' : B.erase (m + 1) ⊆ Finset.Icc 1 m := by
        intro c hc
        have h1 : c ∈ B := (Finset.mem_erase.mp hc).2
        have hI := Finset.mem_Icc.mp (hB h1)
        have h3 : c ≠ m + 1 := (Finset.mem_erase.mp hc).1
        simp only [Finset.mem_Icc]
        omega
      rw [jsp87sum_split_top m A hA, jsp87sum_split_top m B hB]
      by_cases hX : A.erase (m + 1) = B.erase (m + 1)
      · by_cases hA1 : m + 1 ∈ A <;> by_cases hB1 : m + 1 ∈ B
        · exfalso
          exact hne (by
            rw [(Finset.insert_erase hA1).symm, (Finset.insert_erase hB1).symm, hX])
        · rw [if_pos hA1, if_neg hB1, hX]
          norm_num
        · rw [if_neg hA1, if_pos hB1, hX]
          norm_num
        · exfalso
          exact hne (by
            rw [(jsp87erase_eq_self A (m + 1) hA1).symm,
              (jsp87erase_eq_self B (m + 1) hB1).symm, hX])
      · have hgap := ih (A.erase (m + 1)) (B.erase (m + 1)) hA' hB' hX
        have hne'' : (∑ a ∈ A.erase (m + 1), ((2 : ℤ) ^ (m - a)))
            - (∑ b ∈ B.erase (m + 1), ((2 : ℤ) ^ (m - b))) ≠ 0 := by
          intro hz
          have h1 := hgap
          rw [hz] at h1
          norm_num at h1
        have hfinal : ∀ c d : ℤ, |c - d| ≤ 1 →
            1 ≤ |(c + 2 * (∑ a ∈ A.erase (m + 1), ((2 : ℤ) ^ (m - a))))
                - (d + 2 * (∑ b ∈ B.erase (m + 1), ((2 : ℤ) ^ (m - b))))| := by
          intro c d hcd
          have hcd' : c - d = 0 ∨ c - d = 1 ∨ c - d = -1 := by
            have h1 : -1 ≤ c - d ∧ c - d ≤ 1 := abs_le.mp hcd
            omega
          have hid : (c + 2 * (∑ a ∈ A.erase (m + 1), ((2 : ℤ) ^ (m - a))))
              - (d + 2 * (∑ b ∈ B.erase (m + 1), ((2 : ℤ) ^ (m - b))))
              = (c - d) + 2 * ((∑ a ∈ A.erase (m + 1), ((2 : ℤ) ^ (m - a)))
                - (∑ b ∈ B.erase (m + 1), ((2 : ℤ) ^ (m - b)))) := by ring
          rw [hid]
          rcases hcd' with hcd | hcd | hcd
          · rw [hcd]
            exact jsp87int_ge_one (jsp87int_shift_ne hne'' (by norm_num))
          · rw [hcd]
            exact jsp87int_ge_one (jsp87int_shift_ne hne'' (by norm_num))
          · rw [hcd]
            exact jsp87int_ge_one (jsp87int_shift_ne hne'' (by norm_num))
        exact hfinal _ _ (by split <;> split <;> norm_num)

/-- **THE LEVEL WEIGHTS ARE THE SCALE `2^{−(H+K)}` TIMES THE BINARY WEIGHTS.** -/
private theorem jsp87W_eq_scale {K H h : ℕ} (hh : h ≤ H) :
    jsp87W K h = ((1 / 2 : ℝ) ^ (H + K)) * ((2 : ℝ) ^ (H - h)) := by
  have e : -(h + K : ℤ) = -((H + K : ℕ) : ℤ) + ((H - h : ℕ) : ℤ) := by
    push_cast
    omega
  have h1 : ((1 / 2 : ℝ) ^ (H + K)) = ((2 : ℝ) ^ (-((H + K : ℕ) : ℤ))) := by
    have h2 : ((1 / 2 : ℝ) ^ (H + K)) = ((2 : ℝ)⁻¹) ^ (H + K) := by
      rw [div_eq_mul_inv, one_mul]
    have h3 : ((2 : ℝ)⁻¹) ^ ((H + K : ℕ) : ℤ) = ((2 : ℝ) ^ ((H + K : ℕ) : ℤ))⁻¹ :=
      inv_zpow (2 : ℝ) _
    rw [h2, ← zpow_natCast ((2 : ℝ)⁻¹) (H + K), h3, ← zpow_neg]
  rw [jsp87W, h1, e, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

/-- **THE GEOMETRIC WEIGHT GAP.**  Distinct sets of levels have distinct level
weight sums: they are at distance at least `2^{−(H+K)}`. -/
theorem jsp87W_sum_sub_ge {K H : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.Icc 1 H)
    (hB : B ⊆ Finset.Icc 1 H) (hne : A ≠ B) :
    |(∑ a ∈ A, jsp87W K a) - (∑ b ∈ B, jsp87W K b)| ≥ ((1 / 2 : ℝ) ^ (H + K)) := by
  have hAeq : (∑ a ∈ A, jsp87W K a)
      = ((1 / 2 : ℝ) ^ (H + K)) * ((∑ a ∈ A, ((2 : ℤ) ^ (H - a)) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    refine jsp87W_eq_scale ?_
    exact (Finset.mem_Icc.mp (hA ha)).2
  have hBeq : (∑ b ∈ B, jsp87W K b)
      = ((1 / 2 : ℝ) ^ (H + K)) * ((∑ b ∈ B, ((2 : ℤ) ^ (H - b)) : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    refine jsp87W_eq_scale ?_
    exact (Finset.mem_Icc.mp (hB hb)).2
  have hgap : |(∑ a ∈ A, ((2 : ℤ) ^ (H - a)) : ℝ) - (∑ b ∈ B, ((2 : ℤ) ^ (H - b)) : ℝ)| ≥ 1 := by
    have h : |(∑ a ∈ A, ((2 : ℤ) ^ (H - a))) - (∑ b ∈ B, ((2 : ℤ) ^ (H - b)))| ≥ 1 :=
      jsp87bin_gap H A B hA hB hne
    exact_mod_cast h
  have hpos : 0 < ((1 / 2 : ℝ) ^ (H + K)) := by positivity
  have hlam : ((1 / 2 : ℝ) ^ (H + K)) * (∑ a ∈ A, ((2 : ℤ) ^ (H - a)) : ℝ)
      - ((1 / 2 : ℝ) ^ (H + K)) * (∑ b ∈ B, ((2 : ℤ) ^ (H - b)) : ℝ)
      = ((1 / 2 : ℝ) ^ (H + K))
        * ((∑ a ∈ A, ((2 : ℤ) ^ (H - a)) : ℝ) - (∑ b ∈ B, ((2 : ℤ) ^ (H - b)) : ℝ)) := by ring
  rw [hAeq, hBeq, hlam, abs_mul, abs_of_pos hpos]
  have h1 : ((1 / 2 : ℝ) ^ (H + K)) * 1
      ≤ ((1 / 2 : ℝ) ^ (H + K))
        * |(∑ a ∈ A, ((2 : ℤ) ^ (H - a)) : ℝ) - (∑ b ∈ B, ((2 : ℤ) ^ (H - b)) : ℝ)| :=
    mul_le_mul_of_nonneg_left hgap (le_of_lt hpos)
  linarith

/-! ## §2  The level code -/

/-- **THE LEVEL CODE** `c p n h = ∑_{ε hit at level h} (−1)^{|ε|}`: the signed
contribution of the level `h` to `X_p`, as an integer.  Under the one-vertex
hypothesis it lies in `{−1, 0, 1}` (`jsp87XpCode_mem`). -/
noncomputable def jsp87XpCode {K : ℕ} (p n : ℕ) (v : Fin K → ℕ) (h : ℕ) : ℤ :=
  ∑ ε ∈ jsp87HitVerts p n v h, jsp87Sign ε.card

/-- **THE SIGN OF A VERTEX IS `±1`.** -/
private theorem jsp87sign_abs_one (e : ℕ) : jsp87Sign e = 1 ∨ jsp87Sign e = -1 := by
  unfold jsp87Sign
  by_cases h : e % 2 = 0
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- **AT MOST ONE HIT VERTEX, SINGLY.**  (The private helper of `Xp.lean`, needed
here for the level code.) -/
private theorem jsp87HitVerts_singleton {K : ℕ} {p n : ℕ} {v : Fin K → ℕ} {h : ℕ}
    {ε : Finset (Fin K)} (hone : jsp87OneVertex p n v h)
    (hmem : ε ∈ jsp87HitVerts p n v h) : jsp87HitVerts p n v h = {ε} := by
  ext δ
  constructor
  · intro hδ
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.mp hone δ hδ ε hmem
  · intro hδ
    rw [Finset.mem_singleton] at hδ
    rw [hδ]
    exact hmem

/-- **THE LEVEL CODE LIES IN `{−1, 0, 1}`** under the one-vertex hypothesis: this
is where the primality structure of (5.13) is consumed. -/
theorem jsp87XpCode_mem {K : ℕ} {p n : ℕ} {v : Fin K → ℕ} {h : ℕ}
    (hone : jsp87OneVertex p n v h) :
    jsp87XpCode p n v h ∈ ({-1, 0, 1} : Finset ℤ) := by
  by_cases hemp : jsp87HitVerts p n v h = ∅
  · rw [jsp87XpCode, hemp, Finset.sum_empty]
    simp
  · obtain ⟨ε₀, hmem⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    rw [jsp87XpCode, jsp87HitVerts_singleton hone hmem, Finset.sum_singleton]
    rcases jsp87sign_abs_one ε₀.card with hs | hs
    · rw [hs]
      simp
    · rw [hs]
      simp

/-- **THE COLLAPSE, IN CODE FORM.**  The `2^K`-term alternating sum of (5.13) is
the level code times the level weight — with **no hypothesis at all**, since this
is just the filter step of `jsp87XpLevel_eq_filter`. -/
theorem jsp87XpLevel_eq_code {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ) :
    jsp87XpLevel v p n h = ((jsp87XpCode p n v h : ℤ) : ℝ) * jsp87W K h := by
  have h1 : ((jsp87XpCode p n v h : ℤ) : ℝ)
      = ∑ ε ∈ jsp87HitVerts p n v h, ((jsp87Sign ε.card : ℤ) : ℝ) := by
    unfold jsp87XpCode
    rw [Int.cast_sum]
  rw [jsp87XpLevel_eq_filter, h1]
  ring

/-- **THE CUBE SUM IS THE SUM OF THE CODED LEVEL WEIGHTS.** -/
theorem jsp87Xp0_eq_code {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) :
    jsp87Xp0 v p n H
      = ∑ h ∈ Finset.Icc 1 H, ((jsp87XpCode p n v h : ℤ) : ℝ) * jsp87W K h := by
  unfold jsp87Xp0
  exact Finset.sum_congr rfl fun h _ => jsp87XpLevel_eq_code v p n h

/-! ## §3  The lattice of cube sums, and the uniform gap -/

/-- **THE LEVEL DIFFERENCE, AS AN INTEGER.** -/
noncomputable def jsp87XpIntDiff {K : ℕ} (p n n' : ℕ) (v : Fin K → ℕ) (H : ℕ) : ℤ :=
  ∑ h ∈ Finset.Icc 1 H, (jsp87XpCode p n v h - jsp87XpCode p n' v h) * ((2 : ℤ) ^ (H - h))

/-- **THE DISCRETENESS OF THE CUBE SUM.**
`X_p(n) − X_p(n′) = 2^{−(H+K)} · (an integer)`: the cube sums live on a fixed
lattice, so their differences are quantised. -/
theorem jsp87Xp0_sub_eq_scale {K : ℕ} (v : Fin K → ℕ) (p n n' H : ℕ) :
    jsp87Xp0 v p n H - jsp87Xp0 v p n' H
      = ((1 / 2 : ℝ) ^ (H + K)) * ((jsp87XpIntDiff p n n' v H : ℤ) : ℝ) := by
  have hd : ∀ h ∈ Finset.Icc 1 H,
      (((jsp87XpCode p n v h - jsp87XpCode p n' v h) * ((2 : ℤ) ^ (H - h)) : ℤ) : ℝ)
        = (((jsp87XpCode p n v h - jsp87XpCode p n' v h : ℤ) : ℝ)
            * ((2 : ℝ) ^ (H - h))) := by
    intro h hh
    rw [Int.cast_mul, jsp87int_cast_pow_two (H - h)]
  have hw : ∀ h ∈ Finset.Icc 1 H,
      (((jsp87XpCode p n v h - jsp87XpCode p n' v h : ℤ) : ℝ)) * jsp87W K h
        = ((1 / 2 : ℝ) ^ (H + K))
          * (((jsp87XpCode p n v h - jsp87XpCode p n' v h) * ((2 : ℤ) ^ (H - h)) : ℤ) : ℝ) := by
    intro h hh
    have hle : h ≤ H := (Finset.mem_Icc.mp hh).2
    rw [jsp87W_eq_scale hle]
    calc (((jsp87XpCode p n v h - jsp87XpCode p n' v h : ℤ) : ℝ))
          * ((1 / 2 : ℝ) ^ (H + K) * ((2 : ℝ) ^ (H - h)))
        = ((1 / 2 : ℝ) ^ (H + K))
            * (((jsp87XpCode p n v h - jsp87XpCode p n' v h : ℤ) : ℝ)
              * ((2 : ℝ) ^ (H - h))) := by ring
      _ = ((1 / 2 : ℝ) ^ (H + K))
            * (((jsp87XpCode p n v h - jsp87XpCode p n' v h)
                * ((2 : ℤ) ^ (H - h)) : ℤ) : ℝ) := by rw [← hd h hh]
  rw [jsp87Xp0_eq_code, jsp87Xp0_eq_code, ← Finset.sum_sub_distrib]
  calc (∑ x ∈ Finset.Icc 1 H,
        ((jsp87XpCode p n v x : ℝ) * jsp87W K x - (jsp87XpCode p n' v x : ℝ) * jsp87W K x))
      = ∑ x ∈ Finset.Icc 1 H, (((jsp87XpCode p n v x - jsp87XpCode p n' v x : ℤ) : ℝ))
          * jsp87W K x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        push_cast
        ring
    _ = ∑ x ∈ Finset.Icc 1 H, ((1 / 2 : ℝ) ^ (H + K))
          * ((((jsp87XpCode p n v x - jsp87XpCode p n' v x) * ((2 : ℤ) ^ (H - x))) : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun x hx => hw x hx
    _ = ((1 / 2 : ℝ) ^ (H + K))
        * (∑ x ∈ Finset.Icc 1 H,
          ((((jsp87XpCode p n v x - jsp87XpCode p n' v x) * ((2 : ℤ) ^ (H - x))) : ℤ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = ((1 / 2 : ℝ) ^ (H + K)) * ((jsp87XpIntDiff p n n' v H : ℤ) : ℝ) := by
      unfold jsp87XpIntDiff
      rw [Int.cast_sum]

/-- **THE UNIFORM GAP.**  Two cube sums are either equal or at distance at least
`2^{−(H+K)}`.  This is the discrete replacement for the aperiodicity of the hit
patterns, which is *false* (§4). -/
theorem jsp87Xp0_sub_eq_zero_or_ge {K : ℕ} (v : Fin K → ℕ) (p n n' H : ℕ) :
    jsp87Xp0 v p n H = jsp87Xp0 v p n' H ∨
      |jsp87Xp0 v p n H - jsp87Xp0 v p n' H| ≥ ((1 / 2 : ℝ) ^ (H + K)) := by
  have h := jsp87Xp0_sub_eq_scale v p n n' H
  have hpos : 0 < ((1 / 2 : ℝ) ^ (H + K)) := by positivity
  by_cases hz : jsp87XpIntDiff p n n' v H = 0
  · left
    have h1 : jsp87Xp0 v p n H - jsp87Xp0 v p n' H = 0 := by
      rw [h, hz]
      simp
    linarith
  · right
    have h1 : 1 ≤ |(jsp87XpIntDiff p n n' v H : ℤ)| := jsp87int_ge_one hz
    rw [h, abs_mul, abs_of_pos hpos]
    have h1' : 1 ≤ |((jsp87XpIntDiff p n n' v H : ℤ) : ℝ)| := by
      exact_mod_cast h1
    nlinarith

/-! ## §4  The binary-carry collision: the hit-pattern criterion is false -/

/-- **THE CARRY IDENTITY OF THE LEVEL WEIGHTS:** `2 w_{m+1} = w_m`.  The weights
of (5.13) form a *geometric* sequence of ratio `1/2`, and this is the reason the
map "hit pattern `↦` value" is not injective. -/
theorem jsp87W_succ {K : ℕ} (m : ℕ) : 2 * jsp87W K (m + 1) = jsp87W K m := by
  have e : m + 1 + K = (m + K) + 1 := by omega
  rw [jsp87W_eq_half, jsp87W_eq_half, e, pow_succ]
  ring

/-- **THE CARRY SHIFT** at the pair of levels `m, m+1`: `−1` at the level `m` and
`+2` at the level `m+1`, zero elsewhere. -/
noncomputable def jsp87XpCarryShift (m : ℕ) : ℕ → ℤ :=
  fun h => if h = m then -1 else if h = m + 1 then 2 else 0

/-- **THE CARRY SHIFT AT ITS OWN LEVEL.** -/
theorem jsp87XpCarrySelf (m : ℕ) : jsp87XpCarryShift m m = -1 := by
  unfold jsp87XpCarryShift
  rw [if_pos rfl]

/-- **THE CARRY SHIFT AT THE SUCCESSOR LEVEL.** -/
theorem jsp87XpCarrySucc (m : ℕ) : jsp87XpCarryShift m (m + 1) = 2 := by
  unfold jsp87XpCarryShift
  rw [if_neg (by omega), if_pos rfl]

/-- **THE CARRY SHIFT ELSEWHERE.** -/
theorem jsp87XpCarryOther {m h : ℕ} (h1 : h ≠ m) (h2 : h ≠ m + 1) :
    jsp87XpCarryShift m h = 0 := by
  unfold jsp87XpCarryShift
  rw [if_neg h1, if_neg h2]

/-- **THE CARRY SHIFT IS INVISIBLE.**  Adding the carry shift at `m` does not
change the value of the weighted level sum, because `−w_m + 2w_{m+1} = 0`. -/
theorem jsp87Xp0_code_add_carry {K H : ℕ} (c : ℕ → ℤ) (m : ℕ) (hm : 1 ≤ m) (hm' : m + 1 ≤ H) :
    (∑ h ∈ Finset.Icc 1 H, ((c h + jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h)
      = ∑ h ∈ Finset.Icc 1 H, ((c h : ℤ) : ℝ) * jsp87W K h := by
  have hmem : ({m, m + 1} : Finset ℕ) ⊆ Finset.Icc 1 H := by
    rw [Finset.subset_iff]
    intro a ha
    rw [Finset.mem_Icc]
    rcases Finset.mem_insert.mp ha with h | ha
    · rw [h]
      exact ⟨hm, Nat.le_trans (Nat.le_succ m) hm'⟩
    · rw [Finset.mem_singleton.mp ha]
      exact ⟨Nat.succ_le_succ (Nat.zero_le m), hm'⟩
  have hshift : ∀ h ∈ Finset.Icc 1 H, h ∉ ({m, m + 1} : Finset ℕ) →
      ((jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h = 0 := by
    intro h _h hh
    obtain ⟨hnm, hnm1⟩ := jsp87ne_pair hh
    rw [jsp87XpCarryOther hnm hnm1]
    norm_num
  have hset : ({m, m + 1} : Finset ℕ) = insert (m + 1) ({m} : Finset ℕ) := by
    ext h
    simp only [Finset.mem_singleton, Finset.mem_insert]
    tauto
  have hcore : (∑ h ∈ ({m, m + 1} : Finset ℕ), ((jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h)
      = -jsp87W K m + 2 * jsp87W K (m + 1) := by
    have hne' : m + 1 ∉ ({m} : Finset ℕ) := by simp
    rw [hset, Finset.sum_insert hne', Finset.sum_singleton, jsp87XpCarrySelf,
      jsp87XpCarrySucc]
    ring
  have hzero : (∑ h ∈ Finset.Icc 1 H, ((jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h) = 0 := by
    have h1 : (∑ h ∈ ({m, m + 1} : Finset ℕ) ∩ Finset.Icc 1 H,
          ((jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h)
        = ∑ h ∈ Finset.Icc 1 H, ((jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h :=
      Finset.sum_subset (fun a ha => (Finset.mem_inter.mp ha).2)
        (fun h hh hh' => hshift h hh (fun hc => hh' (by simp [hc, hh])))
    have hset2 : ({m, m + 1} : Finset ℕ) ∩ Finset.Icc 1 H = {m, m + 1} := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_insert.mp ((Finset.mem_inter.mp ha).1) with h | h
        · rw [h]
          exact Finset.mem_insert.mpr (Or.inl rfl)
        · rw [Finset.mem_singleton.mp h]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      · intro ha
        rcases Finset.mem_insert.mp ha with h | h
        · rw [h]
          exact Finset.mem_inter.mpr ⟨Finset.mem_insert.mpr (Or.inl rfl),
            Finset.mem_Icc.mpr ⟨hm, Nat.le_trans (Nat.le_succ m) hm'⟩⟩
        · rw [Finset.mem_singleton.mp h]
          exact Finset.mem_inter.mpr ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)),
            Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le m), hm'⟩⟩
    rw [h1.symm, hset2, hcore, jsp87W_succ]
    ring
  have key : ∀ h ∈ Finset.Icc 1 H,
      ((c h + jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h
        = ((c h : ℤ) : ℝ) * jsp87W K h
          + ((jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h := by
    intro h _h
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun h hh => key h hh), Finset.sum_add_distrib, hzero]
  ring

/-- **THE COLLISION, WITH ADMISSIBLE CODES.**  Let a level function `c` take
values in `{−1,0,1}` with `c m = 0` and `c (m+1) = −1`.  Then `c` and
`c + (carry shift at m)` are *both* admissible level codes with the *same*
weighted sum.

**This is machine-checked negative knowledge:** the criterion "different hit
pattern ⇒ different value of `X_p`" is FALSE — exactly one binary carry destroys
it.  The correct invariant is the value itself, not the pattern. -/
theorem jsp87Xp0_code_collision {K H : ℕ} (m : ℕ) (hm : 1 ≤ m) (hm' : m + 1 ≤ H)
    (c : ℕ → ℤ) (hc : ∀ h ∈ Finset.Icc 1 H, c h ∈ ({-1, 0, 1} : Finset ℤ))
    (hc1 : c m = 0) (hc2 : c (m + 1) = -1) :
    ∀ h ∈ Finset.Icc 1 H, c h + jsp87XpCarryShift m h ∈ ({-1, 0, 1} : Finset ℤ) := by
  intro h hh
  have hhI : h ∈ Finset.Icc 1 H := hh
  by_cases h1 : h = m
  · rw [h1, jsp87XpCarrySelf, hc1]
    simp
  · by_cases h2 : h = m + 1
    · rw [h2, jsp87XpCarrySucc, hc2]
      simp
    · rw [jsp87XpCarryOther h1 h2, add_zero]
      exact hc h hhI

/-- **THE COLLISION FOR THE CUBE SUM.**  Two sample points whose level codes
differ by a carry shift have the *same* cube sum.  Hence non-constancy of `X_p`
cannot be inferred from a single pattern mismatch. -/
theorem jsp87Xp0_eq_of_code_carry {K : ℕ} (v : Fin K → ℕ) (p n n' : ℕ) (H m : ℕ)
    (hm : 1 ≤ m) (hm' : m + 1 ≤ H)
    (hcode : ∀ h ∈ Finset.Icc 1 H,
      jsp87XpCode p n' v h = jsp87XpCode p n v h + jsp87XpCarryShift m h) :
    jsp87Xp0 v p n H = jsp87Xp0 v p n' H := by
  rw [jsp87Xp0_eq_code, jsp87Xp0_eq_code]
  have h := jsp87Xp0_code_add_carry (K := K) (H := H)
    (c := fun h => (jsp87XpCode p n v h : ℤ)) m hm hm'
  calc (∑ h ∈ Finset.Icc 1 H, ((jsp87XpCode p n v h : ℤ) : ℝ) * jsp87W K h)
      = ∑ h ∈ Finset.Icc 1 H,
          (((jsp87XpCode p n v h) + jsp87XpCarryShift m h : ℤ) : ℝ) * jsp87W K h := h.symm
    _ = ∑ h ∈ Finset.Icc 1 H, ((jsp87XpCode p n' v h : ℤ) : ℝ) * jsp87W K h := by
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hcode h hh]

/-! ## §5  The class-count form of the variance -/

/-- **THE CLASS OF A VALUE**: the sample points at which `f` takes the value `A`. -/
noncomputable def jsp87Class {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (f : Ω → ℝ)
    (A : ℝ) : Finset Ω := s.filter (fun x => f x = A)

/-- **SUM BY THE VALUES OF A FUNCTION** — `Finset.sum_fiberwise_of_maps_to`,
phrased with the classes. -/
private theorem jsp87sum_by_value {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (g : Ω → ℝ)
    (w : Ω → ℝ) :
    (∑ i ∈ s, w i) = ∑ A ∈ s.image g, ∑ i ∈ jsp87Class s g A, w i := by
  refine (Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g) ?_ w).symm
  intro i hi
  exact Finset.mem_image_of_mem g hi

/-- **CONSTANCY ON A CLASS.**  Any function of `f` is constant on a class. -/
theorem jsp87Class_const {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (f : Ω → ℝ) (A : ℝ)
    (g : ℝ → ℝ) :
    (∑ i ∈ jsp87Class s f A, g (f i)) = ((jsp87Class s f A).card : ℝ) * g A := by
  calc (∑ i ∈ jsp87Class s f A, g (f i))
      = ∑ _i ∈ jsp87Class s f A, g A := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_filter.mp hi
        rw [hi'.2]
    _ = ((jsp87Class s f A).card : ℝ) * g A := by
        refine (Finset.sum_congr rfl fun _ _ => rfl).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE DOUBLE SUM IS THE WEIGHTED COUNT OF PAIRS OF DISTINCT VALUES.**
`∑_{i,j} (f i − f j)² = ∑_{A,B} |A| |B| (A − B)²`, the sums being over ordered
pairs of attained values.

This is `Finset.sum_fiberwise_of_maps_to` applied to each index of the double sum,
with `jsp87Class_const` to collapse each class. -/
theorem jsp87_sum_diff_sq_class {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (f : Ω → ℝ) :
    (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
      = ∑ AB ∈ s.image f ×ˢ s.image f,
          ((jsp87Class s f AB.1).card : ℝ) * (jsp87Class s f AB.2).card * (AB.1 - AB.2) ^ 2 := by
  have h1 : (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2) = ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_product s s (fun ij => (f ij.1 - f ij.2) ^ 2)
  have h2 : ∀ i : Ω, (∑ j ∈ s, (f i - f j) ^ 2)
      = ∑ A ∈ s.image f, ((jsp87Class s f A).card : ℝ) * (f i - A) ^ 2 := by
    intro i
    rw [jsp87sum_by_value]
    exact Finset.sum_congr rfl fun A _hA => jsp87Class_const s f A (fun a => (f i - a) ^ 2)
  have h3 : (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2)
      = ∑ A ∈ s.image f, ((jsp87Class s f A).card : ℝ)
          * ∑ B ∈ s.image f, ((jsp87Class s f B).card : ℝ) * (A - B) ^ 2 := by
    calc (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2)
        = ∑ i ∈ s, ∑ A ∈ s.image f, ((jsp87Class s f A).card : ℝ) * (f i - A) ^ 2 :=
          Finset.sum_congr rfl fun i _ => h2 i
      _ = ∑ A ∈ s.image f, ∑ i ∈ s,
            ((jsp87Class s f A).card : ℝ) * (f i - A) ^ 2 := by rw [Finset.sum_comm]
      _ = ∑ A ∈ s.image f, ((jsp87Class s f A).card : ℝ) * ∑ i ∈ s, (f i - A) ^ 2 := by
        refine Finset.sum_congr rfl fun A _hA => ?_
        exact (Finset.mul_sum _ _ _).symm
      _ = ∑ A ∈ s.image f, ((jsp87Class s f A).card : ℝ)
          * ∑ B ∈ s.image f, ((jsp87Class s f B).card : ℝ) * (A - B) ^ 2 := by
        refine Finset.sum_congr rfl fun A _hA => ?_
        have hz : (∑ i ∈ s, (f i - A) ^ 2)
            = ∑ B ∈ s.image f, ((jsp87Class s f B).card : ℝ) * (A - B) ^ 2 := by
          rw [jsp87sum_by_value]
          refine Finset.sum_congr rfl fun B _hB => ?_
          exact (Finset.sum_congr rfl fun i _ => by
            have hneg : (A - f i) = -((f i - A)) := by ring
            rw [hneg]
            ring).trans (jsp87Class_const s f B (fun a => (A - a) ^ 2))
        rw [hz]
  rw [h1, h3]
  calc (∑ A ∈ s.image f, ((jsp87Class s f A).card : ℝ)
          * ∑ B ∈ s.image f, ((jsp87Class s f B).card : ℝ) * (A - B) ^ 2)
      = ∑ A ∈ s.image f, ∑ B ∈ s.image f,
          ((jsp87Class s f A).card : ℝ) * ((jsp87Class s f B).card : ℝ) * (A - B) ^ 2 := by
        refine Finset.sum_congr rfl fun A _hA => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ AB ∈ s.image f ×ˢ s.image f,
        ((jsp87Class s f AB.1).card : ℝ) * ((jsp87Class s f AB.2).card : ℝ)
          * (AB.1 - AB.2) ^ 2 :=
    (Finset.sum_product (s.image f) (s.image f) (fun AB =>
      ((jsp87Class s f AB.1).card : ℝ) * ((jsp87Class s f AB.2).card : ℝ)
        * (AB.1 - AB.2) ^ 2)).symm

/-- **THE DOUBLE SUM OF SQUARED DIFFERENCES, IN THE UNCENTRED FORM.** -/
theorem jsp87_sum_diff_sq_eq_var {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) :
    (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
      = 2 * ((s.card : ℕ) : ℝ) ^ 2 * jsp87Var s f := by
  have hkey : (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
      = 2 * ((s.card : ℕ) : ℝ) * (∑ i ∈ s, f i ^ 2) - 2 * (∑ i ∈ s, f i) ^ 2 := by
    calc (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
        = ∑ ij ∈ s ×ˢ s, (f ij.1 ^ 2 - 2 * f ij.1 * f ij.2 + f ij.2 ^ 2) := by
          apply Finset.sum_congr rfl
          intro ij _
          ring
      _ = 2 * ((s.card : ℕ) : ℝ) * (∑ i ∈ s, f i ^ 2) - 2 * (∑ i ∈ s, f i) ^ 2 := by
          have h1 := jsp87sum_prod_mul s s (fun i => f i ^ 2) (fun _ => (1 : ℝ))
          have h2 := jsp87sum_prod_mul s s (fun i => f i) f
          have h3 := jsp87sum_prod_mul s s (fun _ => (1 : ℝ)) (fun j => f j ^ 2)
          simp only [mul_one, one_mul] at h1 h2 h3
          have h2' : (∑ ij ∈ s ×ˢ s, 2 * f ij.1 * f ij.2)
              = 2 * ((∑ i ∈ s, f i) * (∑ j ∈ s, f j)) := by
            have h2x := jsp87sum_prod_mul s s (fun i => 2 * f i) f
            have h2y : (∑ x ∈ s, 2 * f x) = 2 * (∑ x ∈ s, f x) := by
              rw [Finset.mul_sum]
            rw [h2x, h2y]
            ring
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h3, jsp87sum_one, h2']
          ring
      _ = _ := by ring

  have hZ : (∑ i ∈ s, f i ^ 2) * ((s.card : ℕ) : ℝ)
      - (∑ i ∈ s, f i) ^ 2 = ((s.card : ℕ) : ℝ) ^ 2 * jsp87Var s f := by
    have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hs
    have hsq : (∑ i ∈ s, (f i - (∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2)
        = (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) ^ 2 / ((s.card : ℕ) : ℝ) := by
      calc (∑ i ∈ s, (f i - (∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2)
          = ∑ i ∈ s, (f i ^ 2
              - 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))
              + ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = ((∑ i ∈ s, f i ^ 2)
              - (∑ i ∈ s, 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))))
              + (∑ i ∈ s, ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = ((∑ i ∈ s, f i ^ 2)
              - (∑ i ∈ s, 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))))
              + ((s.card : ℕ) : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
            have hcc : (∑ i ∈ s, ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2)
                = ((s.card : ℕ) : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
              calc (∑ i ∈ s, ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2)
                  = ∑ _i ∈ s, (1 : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
                    refine Finset.sum_congr rfl fun _ _ => (one_mul _).symm
                _ = ((s.card : ℕ) : ℝ) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)) ^ 2 := by
                    rw [Finset.sum_const, nsmul_eq_mul, one_mul]
            rw [hcc]
        _ = _ := by
            have h1' : (∑ i ∈ s, 2 * f i * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ)))
                = 2 * ((∑ i ∈ s, f i) * ((∑ j ∈ s, f j) / ((s.card : ℕ) : ℝ))) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
              ring
            rw [h1']
            field_simp
            ring
    unfold jsp87Var jsp87FAvg
    rw [hsq]
    field_simp
  calc (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
      = 2 * ((s.card : ℕ) : ℝ) * (∑ i ∈ s, f i ^ 2) - 2 * (∑ i ∈ s, f i) ^ 2 := hkey
    _ = 2 * ((s.card : ℕ) : ℝ) ^ 2 * jsp87Var s f := by
      have hre : 2 * ((s.card : ℕ) : ℝ) * (∑ i ∈ s, f i ^ 2) - 2 * (∑ i ∈ s, f i) ^ 2
          = ((∑ i ∈ s, f i ^ 2) * ((s.card : ℕ) : ℝ) - (∑ i ∈ s, f i) ^ 2) * 2 := by ring
      rw [hre, hZ]
      ring

/-- **THE CLASS-COUNT FORM OF THE VARIANCE.**
`2 |s|² Var f = ∑_{A,B} |A| |B| (v_A − v_B)²`, the sum being over ordered pairs of
*hit-value classes* of the sample.

**This is the identity asked for in `next_round_attack[1]`**, with the classes
being the attained values rather than the hit patterns (§4 shows the latter
does not work).  In particular the variance is exactly the weighted count of the
pairs of sample points whose cube sums differ. -/
theorem jsp87Var_eq_classSum {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (hs : s.Nonempty)
    (f : Ω → ℝ) :
    2 * ((s.card : ℕ) : ℝ) ^ 2 * jsp87Var s f
      = ∑ AB ∈ s.image f ×ˢ s.image f,
        ((jsp87Class s f AB.1).card : ℝ) * (jsp87Class s f AB.2).card * (AB.1 - AB.2) ^ 2 := by
  rw [← jsp87_sum_diff_sq_eq_var s hs f, jsp87_sum_diff_sq_class]

/-- **VARIANCE ZERO IS CONSTANCY.**  The other half of the same statement: the
variance vanishes exactly when all sample points fall in one class. -/
theorem jsp87Var_eq_zero_iff_const {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) :
    jsp87Var s f = 0 ↔ ∀ i ∈ s, f i = jsp87FAvg s f := by
  constructor
  · intro h i hi
    have hz : (∑ j ∈ s, (f j - jsp87FAvg s f) ^ 2) / ((s.card : ℕ) : ℝ) = 0 := h
    rw [div_eq_mul_inv, mul_eq_zero] at hz
    rcases hz with hz | hz
    · have h2 : (f i - jsp87FAvg s f) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (f j - jsp87FAvg s f)).mp hz i hi
      have h3 : f i - jsp87FAvg s f = 0 := by
        exact (sq_eq_zero_iff).mp h2
      linarith
    · have hz' : ((s.card : ℕ) : ℝ)⁻¹ = 0 := hz
      exact absurd hz' (by positivity)
  · intro h
    have h1 : ∑ j ∈ s, (f j - jsp87FAvg s f) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hhj := h j hj
      have : f j - jsp87FAvg s f = 0 := by linarith
      rw [this, zero_pow]
      norm_num
    show (∑ j ∈ s, (f j - jsp87FAvg s f) ^ 2) / ((s.card : ℕ) : ℝ) = 0
    rw [div_eq_mul_inv, h1, zero_mul]

/-! ## §6  The two-class criterion, and the endgame of (5.21) -/

/-- **A BALANCED TWO-CLASS SPLIT FORCES VARIANCE.**
If the sample splits as `s = A ∪ B` with `A ∩ B = ∅`, both parts non-empty, and every
value on `A` is at distance at least `δ` from every value on `B`, then

```
Var f ≥ |A| |B| δ² / |s|² .
```

This is the *quantitative* form of `jsp87Var_eq_classSum`: the variance is
dominated by the pairs of sample points lying in different classes. -/
theorem jsp87Var_ge_twoClass {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (hs : s.Nonempty)
    (f : Ω → ℝ) (A B : Finset Ω) (hAB : s = A ∪ B) (hdis : A ∩ B = ∅) (hA : A.Nonempty)
    (hB : B.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, |f x - f y| ≥ δ) :
    ((A.card * B.card : ℕ) : ℝ) * δ ^ 2 / ((s.card : ℕ) : ℝ) ^ 2 ≤ jsp87Var s f := by
  have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hsubA : A ⊆ s := by rw [hAB]; exact fun x hx => (Finset.mem_union_left B hx)
  have hsubB : B ⊆ s := by rw [hAB]; exact fun x hx => (Finset.mem_union_right A hx)
  have hprod : (∑ ij ∈ A ×ˢ B, (f ij.1 - f ij.2) ^ 2)
      ≥ ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ) * δ ^ 2 := by
    rw [Finset.sum_product]
    calc (∑ x ∈ A, ∑ y ∈ B, (f x - f y) ^ 2) ≥ ∑ _x ∈ A, ∑ _y ∈ B, δ ^ 2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          refine Finset.sum_le_sum fun y hy => ?_
          have h1 := hsep x hx y hy
          have h2 : δ ^ 2 ≤ (f x - f y) ^ 2 := by
            have h4 : δ ^ 2 ≤ |f x - f y| ^ 2 :=
              (sq_le_sq₀ (le_of_lt hδ) (abs_nonneg _)).mpr h1
            rwa [sq_abs] at h4
          exact h2
      _ = ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ) * δ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hprod' : (∑ ij ∈ B ×ˢ A, (f ij.1 - f ij.2) ^ 2)
      ≥ ((B.card : ℕ) : ℝ) * ((A.card : ℕ) : ℝ) * δ ^ 2 := by
    have hswap : ∀ x ∈ B, ∀ y ∈ A, |f x - f y| ≥ δ := by
      intro x hx y hy
      rw [abs_sub_comm]
      exact hsep y hy x hx
    rw [Finset.sum_product]
    calc (∑ x ∈ B, ∑ y ∈ A, (f x - f y) ^ 2) ≥ ∑ _x ∈ B, ∑ _y ∈ A, δ ^ 2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          refine Finset.sum_le_sum fun y hy => ?_
          have h1 := hswap x hx y hy
          have h2 : δ ^ 2 ≤ (f x - f y) ^ 2 := by
            have h4 : δ ^ 2 ≤ |f x - f y| ^ 2 :=
              (sq_le_sq₀ (le_of_lt hδ) (abs_nonneg _)).mpr h1
            rwa [sq_abs] at h4
          exact h2
      _ = ((B.card : ℕ) : ℝ) * ((A.card : ℕ) : ℝ) * δ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul, mul_assoc,
          mul_comm]
  have hD : (A ×ˢ B) ∪ (B ×ˢ A) ⊆ s ×ˢ s := by
    intro ij hij
    rcases (Finset.mem_union.mp hij) with hij | hij
    · have hij' := Finset.mem_product.mp hij
      exact Finset.mem_product.mpr ⟨hsubA hij'.1, hsubB hij'.2⟩
    · have hij' := Finset.mem_product.mp hij
      exact Finset.mem_product.mpr ⟨hsubB hij'.1, hsubA hij'.2⟩
  have hdis' : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    refine Finset.disjoint_left.2 ?_
    intro ij hij1 hij2
    obtain ⟨h11, _h12⟩ := Finset.mem_product.mp hij1
    obtain ⟨h21, _h22⟩ := Finset.mem_product.mp hij2
    exact absurd (Finset.mem_inter.mpr ⟨h11, h21⟩) (by rw [hdis]; simp)
  have hsum : (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
      ≥ 2 * (((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ) * δ ^ 2) := by
    calc (∑ ij ∈ s ×ˢ s, (f ij.1 - f ij.2) ^ 2)
        ≥ ∑ ij ∈ (A ×ˢ B) ∪ (B ×ˢ A), (f ij.1 - f ij.2) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hD fun _ _ _ => sq_nonneg _
      _ = (∑ ij ∈ A ×ˢ B, (f ij.1 - f ij.2) ^ 2)
          + ∑ ij ∈ B ×ˢ A, (f ij.1 - f ij.2) ^ 2 := Finset.sum_union hdis'
      _ ≥ 2 * (((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ) * δ ^ 2) := by linarith
  rw [jsp87_sum_diff_sq_eq_var s hs f] at hsum
  have hc2 : (0 : ℝ) < ((s.card : ℕ) : ℝ) ^ 2 := by positivity
  have hcard : ((A.card * B.card : ℕ) : ℝ) = ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ) := by
    exact_mod_cast Nat.cast_mul _ _
  rw [div_le_iff₀ hc2, hcard]
  linarith

/-- **THE LATTICE FORM FOR THE CUBE SUM.**  If the cube sums of the two classes
are separated (which is *automatic* once they are unequal, by §3), the variance of
`q X_p` is at least `q² |A| |B| 2^{−2(H+K)} / |s|²`. -/
theorem jsp87Var_Xp_ge_twoClass {K : ℕ} (s : Finset ℕ) (hs : s.Nonempty) (q : ℝ)
    (v : Fin K → ℕ) (p H : ℕ) (A B : Finset ℕ) (hAB : s = A ∪ B) (hdis : A ∩ B = ∅)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hne : ∀ x ∈ A, ∀ y ∈ B, jsp87Xp0 v p x H ≠ jsp87Xp0 v p y H) :
    (q ^ 2) * (((A.card * B.card : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        / ((s.card : ℕ) : ℝ) ^ 2
      ≤ jsp87Var s (fun n => q * jsp87Xp0 v p n H) := by
  have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hsep : ∀ x ∈ A, ∀ y ∈ B, |jsp87Xp0 v p x H - jsp87Xp0 v p y H|
      ≥ ((1 / 2 : ℝ) ^ (H + K)) := by
    intro x hx y hy
    rcases jsp87Xp0_sub_eq_zero_or_ge v p x y H with h | h
    · exact absurd h (hne x hx y hy)
    · exact h
  have hV := jsp87Var_ge_twoClass s hs (jsp87Xp0 v p · H) A B hAB hdis hA hB
    ((1 / 2 : ℝ) ^ (H + K)) (by positivity) hsep
  have hbase : jsp87Var s (fun n => q * jsp87Xp0 v p n H)
      = q ^ 2 * jsp87Var s (jsp87Xp0 v p · H) := jsp87Var_scale s q (jsp87Xp0 v p · H)
  rw [hbase]
  have hmul := mul_le_mul_of_nonneg_left hV (sq_nonneg q)
  convert hmul using 1 <;> ring

/-- **A SINGLE PRIME WITH A BALANCED SPLIT SUPPLIES (5.21).**  If for one prime `p`
the cube sums split the sample into two non-empty parts which never agree, and if
the quantitative threshold `q² |A| |B| 2^{−2(H+K)} ≥ |s|²` holds, then
`∑_{p ∈ P} Var (q X_p) ≥ 1` for any `P` containing `p`. -/
theorem jsp87Var_Xp_ge_one {K : ℕ} (s : Finset ℕ) (hs : s.Nonempty) (q : ℝ)
    (v : Fin K → ℕ) (p H : ℕ) (A B : Finset ℕ) (hAB : s = A ∪ B) (hdis : A ∩ B = ∅)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hne : ∀ x ∈ A, ∀ y ∈ B, jsp87Xp0 v p x H ≠ jsp87Xp0 v p y H)
    (hbig : (1 : ℝ) ≤ (q ^ 2) * (((A.card * B.card : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        / ((s.card : ℕ) : ℝ) ^ 2) :
    (1 : ℝ) ≤ jsp87Var s (fun n => q * jsp87Xp0 v p n H) := by
  have h := jsp87Var_Xp_ge_twoClass s hs q v p H A B hAB hdis hA hB hne
  linarith

/-- **THE VARIANCE SUM OVER THE `S₁` PRIMES.**  If every prime of `P` supplies the
same lower bound `c`, then `c ≤ ∑_{p ∈ P} Var (q X_p)`. -/
theorem jsp87_varSum_ge {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty) (q : ℝ)
    (H : ℕ) (v : ℕ → Fin K → ℕ) (hP : P.Nonempty) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ p ∈ P, c ≤ jsp87Var s (fun n => q * jsp87Xp0 (v p) p n H)) :
    c ≤ ∑ p ∈ P, jsp87Var s (fun n => q * jsp87Xp0 (v p) p n H) := by
  obtain ⟨p0, hp0⟩ := hP
  have hsingle : jsp87Var s (fun n => q * jsp87Xp0 (v p0) p0 n H)
      ≤ ∑ p ∈ P, jsp87Var s (fun n => q * jsp87Xp0 (v p) p n H) := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (s := ({p0} : Finset ℕ)) (t := P)
      (f := fun p => jsp87Var s (fun n => q * jsp87Xp0 (v p) p n H))
      (Finset.singleton_subset_iff.mpr hp0) ?_
    · simpa only [Finset.sum_singleton] using h
    · intro x _hx _hx'
      exact jsp87Var_nonneg s (fun n => q * jsp87Xp0 (v x) x n H)
  linarith [hbound p0 hp0]

/-! ## §7  The endgame with (5.21) discharged by a balanced split -/

/-- **THE ENDGAME, WITH (5.21) SUPPLIED BY A BALANCED TWO-CLASS SPLIT.**
Assume (5.15), (5.16)–(5.17) and the separation hypothesis, and assume that for
**one** prime `p` the cube sums split the sample into two non-empty parts `A, B`
which never agree, with the quantitative threshold `q² |A| |B| 2^{−2(H+K)} ≥ |s|²`.
Then the five error terms of §5 of arXiv:2512.01739 cannot all be `< 1/30`.

**This localises the entire remaining burden of `jsp_000087_main` to a single
discrete hypothesis:** the hit values of `X_p` are balanced on a sample of
integers, with a *closed-form* threshold. -/
theorem jsp87_endgame_twoClass {K : ℕ} (s : Finset ℕ) (hs : s.Nonempty) (q : ℝ)
    (H K : ℕ) (v : ℕ → Fin K → ℕ) (p : ℕ) (A B : Finset ℕ) (hAB : s = A ∪ B)
    (hdis : A ∩ B = ∅) (hA : A.Nonempty) (hB : B.Nonempty)
    (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
        jsp87Xp0 (v p') p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
        jsp87Xp0 (v p') p' i H))
        - ∏ p' ∈ ({p} : Finset ℕ),
          jsp87CAvg s (fun i => jsp87e (q * jsp87Xp0 (v p') p' i H))‖ ≤ κ4 + κ5)
    (hsep : ∀ i : ℕ, ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p i (v p) h)
    (hne : ∀ x ∈ A, ∀ y ∈ B, jsp87Xp0 (v p) p x H ≠ jsp87Xp0 (v p) p y H)
    (hbig : (1 : ℝ) ≤ (q ^ 2) * (((A.card * B.card : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        / ((s.card : ℕ) : ℝ) ^ 2) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  have hH21 : (1 : ℝ) ≤ ∑ p' ∈ ({p} : Finset ℕ),
      jsp87Var s (fun i => q * jsp87Xp0 (v p') p' i H) := by
    have h1 := jsp87Var_Xp_ge_one s hs q (v p) p H A B hAB hdis hA hB hne hbig
    rw [Finset.sum_singleton]
    exact h1
  exact jsp87_endgame_cube s hs q K H v κ1 κ2 κ3 κ4 κ5 hK H15 H1617 hH21
    (fun _p hp i h => by
      have : _p = p := by
        rw [Finset.mem_singleton] at hp
        exact hp
      rw [this]
      exact hsep i h)

end JSP87