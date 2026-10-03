/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.Variance

/-!
# JSP-000087, round 117 — THE CUBE-ALTERNATING VARIABLE `X_p` (§6 of arXiv:2512.01739)

## Why this file exists

Round 116 (`Variance.lean`) proved the **endgame** of Tao–Teräväinen §5: their
reduction `Theorem 5.1 (technical reduction)` together with their own
convergence hypothesis (5.18) is unsatisfiable
(`jsp87_endgame_impossible`).  It identified the two remaining arithmetic inputs
(5.18) `κ_j = o(1)` and (5.21) `∑_{p∈S₁} Var X_p ≥ 1`, and it explicitly
recorded as *abandoned* the very object those hypotheses are about:

> "SECTION 6 of the plan (the paper's random variable `X_p` (5.13) as a Lean
> object …) was WRITTEN AND THEN CUT … NEXT ROUND: re-derive §6 from the
> definitions above."

**This file is that §6, and it discharges one of the five hypotheses of the
endgame.**  The random variable of (5.13) is

```
X_p = q ∑_{1≤h≤H} ∑_{ε∈{0,1}^K} (−1)^{|ε|} 2^{−(h+K)} [ p ∣ n + r_{ε,h+K} ]
```

— an *alternating sum over the vertices of a Hilbert cube*, whose differences
are the shifts `r_{ε,h}`.  Its size is the whole content of hypothesis
**(5.19)** `|q X_p| ≤ 1/20`, and two purely arithmetic facts control it:

* **(A) the one-vertex collapse.**  If the `2^K` cube shifts at a level `h` are
  pairwise distinct modulo `p`, then at most **one** vertex is hit, so the
  level sum is `0` or `± 2^{−(h+K)}` — hence
  `|X_p| ≤ |q| · Σ_{h≤H} 2^{−(h+K)} ≤ |q| · H · 2^{−K}`.  This is (5.36).
* **(B) the all-hit collapse.**  If *every* vertex is hit at a level, the
  `2^K` alternating signs cancel and the level sum is `0`.  This is what makes
  the primes of `S₀` (those dividing all the shifts) contribute **nothing**:
  for them `X_p ≡ 0`, hence `Var (q X_p) = 0`, which is exactly why (5.21)
  only sums over `S₁`.

Together: **(5.19) holds for the cube-alternating variable for all sufficiently
large `K`, unconditionally**, and the endgame of round 116 applies to it
(`jsp87_endgame_cube`).  What is left is unchanged — the two *quantitative
arithmetic* estimates (5.18) and (5.21), which are statements about the
distribution of `ω` along progressions of integers and have no Mathlib
analogue.

## What is proved here

| Section | Content |
| --- | --- |
| §1 | `jsp87Off`, `jsp87R` (the cube shift), `jsp87HitVerts`, `jsp87W` (the level weight), `jsp87XpLevel`, `jsp87Xp0`, `jsp87Xp` — the objects of (5.13) |
| §2 | `jsp87Sep` (pairwise distinctness of the shifts), `jsp87OneVertex`, the collapse `jsp87XpLevel_eq_of_hit`, and the size bound (5.36) `jsp87Xp_abs_le` |
| §3 | **hypothesis (5.19) is discharged**: `jsp87Xp_abs_le_twenty`, `exists_K_abs_le`, and `jsp87_endgame_cube` — the round-116 endgame applied to the cube-alternating variable |
| §4 | **the `S₀` mechanism**: `jsp87XpLevel_eq_zero_of_allHit`, `jsp87Xp0_eq_zero_of_dvd_all`, `jsp87Var_zero_of_zeroPrime`, and the variance bounds `jsp87Var_le_avg_sq`, `jsp87Var_le_sq`, `jsp87Var_Xp_le` |
| §5 | **determinism**: `jsp87XpLevel_eq_of_pattern`, `jsp87Xp0_eq_of_pattern`, `jsp87Xp0_eq_of_hitSet` — `X_p` depends on the sample point only through the signs of the hit vertices |

## What is *not* proved here

`jsp_000087_main` is **not declared**.  The bound proved here is the *size* of
`X_p`; the content of (5.21) is the *variance* of `X_p` over the sample set,
which requires Tao–Teräväinen's `Theorem 3.1` (a quantitative two-point
correlation estimate for `ω`, from Pilatte's work).  Mathlib contains no
Chowla-type or Elliott-type statement for multiplicative functions, so that
input cannot be supplied here.  See `ACCEPTANCE.md` for the exact blocker.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## §0  The cube shifts `r_{ε,h}` -/

/-- **THE VERTEX OFFSET** of the cube with common differences `v`. -/
def jsp87Off {K : ℕ} (v : Fin K → ℕ) (ε : Finset (Fin K)) : ℕ :=
  ∑ k ∈ ε, v k

/-- **THE CUBE SHIFT** `r_{ε,h} = h + Σ_{k ∈ ε} v_k`: the integer by which the
sample point `n` is translated at the vertex `ε` of the `K`-cube, at the level
`h`.  In §5.1 of arXiv:2512.01739 this is `p₀·h − Σ_{k=1}^{K} k ε_k v_k`; what
the argument of §6 uses of it is only the *pairwise distinctness modulo `p`* of
these shifts, which is `jsp87Sep` below. -/
def jsp87R {K : ℕ} (v : Fin K → ℕ) (h : ℕ) (ε : Finset (Fin K)) : ℕ :=
  h + jsp87Off v ε

theorem jsp87R_congr {K : ℕ} {v : Fin K → ℕ} {h : ℕ} {ε ε' : Finset (Fin K)}
    (hε : ε = ε') : jsp87R v h ε = jsp87R v h ε' := by rw [hε]

theorem jsp87R_mem_le {K : ℕ} (v : Fin K → ℕ) (h : ℕ) (ε : Finset (Fin K)) :
    jsp87R v h ε ≤ h + (∑ k : Fin K, v k) := by
  have hcore : jsp87Off v ε ≤ ∑ k : Fin K, v k := by
    unfold jsp87Off
    exact Finset.sum_le_sum_of_subset_of_nonneg (s := ε) (t := (Finset.univ : Finset (Fin K)))
      (Finset.subset_univ ε) (fun a _ _ => Nat.zero_le (v a))
  unfold jsp87R
  exact Nat.add_le_add_left hcore h

/-! ## §1  The hitting vertices, the level sums and the variable `X_p` -/

/-- **THE HITTING VERTICES** at level `h`: the vertices `ε` of the cube for
which `p` divides the translated integer `n + r_{ε,h}`.  This is the set `T`
of §6. -/
def jsp87HitVerts {K : ℕ} (p n : ℕ) (v : Fin K → ℕ) (h : ℕ) : Finset (Finset (Fin K)) :=
  (Finset.univ : Finset (Finset (Fin K))).filter (fun ε => p ∣ n + jsp87R v h ε)

/-- **THE LEVEL WEIGHT** `2^{−(h+K)}` of (5.13). -/
noncomputable def jsp87W (K h : ℕ) : ℝ := 2 ^ (-((h + K) : ℤ))

/-- The level weight is the `h+K`-th power of `1/2` — the elementary form used
for the estimates below. -/
theorem jsp87W_eq_half (K h : ℕ) : jsp87W K h = ((1 / 2 : ℝ)^(h + K)) := by
  rw [jsp87W, zpow_neg]
  have hc : ((h : ℤ) + (K : ℤ)) = ((h + K : ℕ) : ℤ) := by norm_cast
  rw [hc, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  rw [zpow_natCast]

theorem jsp87W_pos (K h : ℕ) : 0 < jsp87W K h := by
  rw [jsp87W_eq_half]
  positivity

theorem jsp87W_le_one (K h : ℕ) : jsp87W K h ≤ 1 := by
  rw [jsp87W_eq_half]
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **THE WEIGHTS DECREASE WITH THE LEVEL.** -/
theorem jsp87W_anti (K h h' : ℕ) (hh : h ≤ h') : jsp87W K h' ≤ jsp87W K h := by
  rw [jsp87W_eq_half, jsp87W_eq_half,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_pow]
  have h1 : (2 : ℝ)^(h + K) ≤ (2 : ℝ)^(h' + K) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hh K)
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr h1

/-- **THE LEVEL SUM** `∑_ε (−1)^{|ε|} 2^{−(h+K)} [p ∣ n + r_{ε,h}]`, the inner sum
of (5.13). -/
noncomputable def jsp87XpLevel {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ) : ℝ :=
  ∑ ε ∈ (Finset.univ : Finset (Finset (Fin K))),
    (jsp87Sign ε.card : ℝ) * jsp87W K h
      * (if p ∣ n + jsp87R v h ε then (1 : ℝ) else 0)

/-- **THE CUBE-ALTERNATING VARIABLE** of (5.13), without the leading factor `q`. -/
noncomputable def jsp87Xp0 {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, jsp87XpLevel v p n h

/-- **THE VARIABLE `X_p` OF (5.13)**, with the leading factor `q`. -/
noncomputable def jsp87Xp {K : ℕ} (q : ℝ) (v : Fin K → ℕ) (p n H : ℕ) : ℝ :=
  q * jsp87Xp0 v p n H

/-- The absolute value of the sign of a vertex. -/
theorem jsp87Sign_abs (e : ℕ) : |(jsp87Sign e : ℝ)| = 1 := by
  unfold jsp87Sign
  split <;> norm_num

/-- **THE LEVEL SUM IS THE WEIGHT TIMES THE SIGN-SUM OVER THE HIT VERTICES.** -/
theorem jsp87XpLevel_eq_filter {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ) :
    jsp87XpLevel v p n h
      = jsp87W K h * ∑ ε ∈ jsp87HitVerts p n v h, (jsp87Sign ε.card : ℝ) := by
  unfold jsp87HitVerts
  have hstep : jsp87XpLevel v p n h
      = ∑ ε ∈ (Finset.univ : Finset (Finset (Fin K))).filter
          (fun ε => p ∣ n + jsp87R v h ε), (jsp87Sign ε.card : ℝ) * jsp87W K h := by
    unfold jsp87XpLevel
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun ε _ => by split <;> ring
  rw [hstep, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ε _ => by ring

theorem jsp87Xp0_eq_filter {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) :
    jsp87Xp0 v p n H
      = ∑ h ∈ Finset.Icc 1 H, jsp87W K h * ∑ ε ∈ jsp87HitVerts p n v h,
          (jsp87Sign ε.card : ℝ) := by
  unfold jsp87Xp0
  exact Finset.sum_congr rfl fun h _ => jsp87XpLevel_eq_filter v p n h

/-! ## §2  The one-vertex collapse, and the size bound (5.36) -/

/-- **THE SEPARATION HYPOTHESIS** at level `h`: the prime `p` exceeds every cube
shift, and the shifts are pairwise distinct.  Then they are pairwise distinct
*modulo* `p`; this is the hypothesis on the primes of `S₀` in §5.5. -/
def jsp87Sep {K : ℕ} (p : ℕ) (v : Fin K → ℕ) (h : ℕ) : Prop :=
  (∀ ε : Finset (Fin K), jsp87R v h ε < p) ∧
    (∀ ε ε' : Finset (Fin K), ε ≠ ε' → jsp87R v h ε ≠ jsp87R v h ε')

/-- **AT MOST ONE VERTEX IS HIT** — the consequence of the separation hypothesis
on which the whole of §6 rests. -/
def jsp87OneVertex {K : ℕ} (p n : ℕ) (v : Fin K → ℕ) (h : ℕ) : Prop :=
  (jsp87HitVerts p n v h).card ≤ 1

private theorem jsp87_sub_ne_of_dvd {p a b : ℕ} (hd : p ∣ a - b)
    (hle : b ≤ a) (h2 : a < p) (hne : a ≠ b) : False := by
  have hlt : a - b < p := by omega
  have h0 : (a - b) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  rw [Nat.mod_eq_of_lt hlt] at h0
  have h1 := Nat.sub_add_cancel hle
  rw [h0] at h1
  exact hne (by simpa using h1.symm)

private theorem jsp87_sub_shift (n a b : ℕ) : (n + a) - (n + b) = a - b := by omega

private theorem jsp87_hit_ne {K : ℕ} {p n h : ℕ} {v : Fin K → ℕ} (hsep : jsp87Sep p v h)
    {ε ε' : Finset (Fin K)} (h1 : p ∣ n + jsp87R v h ε) (h2 : p ∣ n + jsp87R v h ε')
    (hne : ε ≠ ε') : False := by
  rcases le_total (jsp87R v h ε) (jsp87R v h ε') with hle | hle
  · have hz : p ∣ jsp87R v h ε' - jsp87R v h ε := by
      have hz1 := Nat.dvd_sub h2 h1
      rwa [jsp87_sub_shift] at hz1
    exact jsp87_sub_ne_of_dvd hz hle (hsep.1 ε') (hsep.2 ε' ε (fun h' => hne h'.symm))
  · have hz : p ∣ jsp87R v h ε - jsp87R v h ε' := by
      have hz1 := Nat.dvd_sub h1 h2
      rwa [jsp87_sub_shift] at hz1
    exact jsp87_sub_ne_of_dvd hz (by omega) (hsep.1 ε) (hsep.2 ε ε' hne)

/-- **THE SEPARATION HYPOTHESIS IMPLIES THE ONE-VERTEX PROPERTY.** -/
theorem jsp87OneVertex_of_sep {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ)
    (hsep : jsp87Sep p v h) : jsp87OneVertex p n v h := by
  unfold jsp87OneVertex
  refine Finset.card_le_one.mpr fun ε hε ε' hε' => ?_
  by_cases hcc : ε = ε'
  · exact hcc
  · exfalso
    have h1 : p ∣ n + jsp87R v h ε := (Finset.mem_filter.mp hε).2
    have h2 : p ∣ n + jsp87R v h ε' := (Finset.mem_filter.mp hε').2
    exact jsp87_hit_ne hsep h1 h2 hcc

private theorem jsp87HitVerts_eq_singleton {K : ℕ} {p n : ℕ} {v : Fin K → ℕ} {h : ℕ}
    {ε : Finset (Fin K)} (hone : jsp87OneVertex p n v h)
    (hmem : ε ∈ jsp87HitVerts p n v h) :
    jsp87HitVerts p n v h = {ε} := by
  ext δ
  constructor
  · intro hδ
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.mp hone δ hδ ε hmem
  · intro hδ
    rw [Finset.mem_singleton] at hδ
    rw [hδ]
    exact hmem

/-- **THE COLLAPSE.**  If a vertex `ε₀` of the cube is hit at the level `h` and
at most one vertex is hit, then the whole `2^K`-term alternating sum collapses
to that single vertex:

```
∑_ε (−1)^{|ε|} 2^{−(h+K)} [p ∣ n + r_{ε,h}]  =  (−1)^{|ε₀|} · 2^{−(h+K)} .
```

This is the mechanism of (5.36). -/
theorem jsp87XpLevel_eq_of_hit {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ)
    (hone : jsp87OneVertex p n v h) (ε₀ : Finset (Fin K))
    (hhit : p ∣ n + jsp87R v h ε₀) :
    jsp87XpLevel v p n h = (jsp87Sign ε₀.card : ℝ) * jsp87W K h := by
  have hmem : ε₀ ∈ jsp87HitVerts p n v h :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩
  rw [jsp87XpLevel_eq_filter, jsp87HitVerts_eq_singleton hone hmem, Finset.sum_singleton]
  ring

/-- **THE LEVEL SUM IS `0` OR A SINGLE SIGNED WEIGHT.** -/
theorem jsp87XpLevel_eq_zero_or_sign {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ)
    (hone : jsp87OneVertex p n v h) :
    jsp87XpLevel v p n h = 0 ∨
      ∃ ε₀ : Finset (Fin K),
        jsp87XpLevel v p n h = (jsp87Sign ε₀.card : ℝ) * jsp87W K h := by
  by_cases hemp : jsp87HitVerts p n v h = ∅
  · left
    rw [jsp87XpLevel_eq_filter, hemp, Finset.sum_empty, mul_zero]
  · right
    obtain ⟨ε₀, hmem⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    exact ⟨ε₀, jsp87XpLevel_eq_of_hit v p n h hone ε₀ (Finset.mem_filter.mp hmem).2⟩

/-- **THE ABSOLUTE VALUE OF A LEVEL SUM.** -/
theorem jsp87XpLevel_abs_le {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ)
    (hone : jsp87OneVertex p n v h) :
    |jsp87XpLevel v p n h| ≤ jsp87W K h := by
  have hcore : |∑ ε ∈ jsp87HitVerts p n v h, (jsp87Sign ε.card : ℝ)| ≤ 1 := by
    calc |∑ ε ∈ jsp87HitVerts p n v h, (jsp87Sign ε.card : ℝ)|
        ≤ ∑ ε ∈ jsp87HitVerts p n v h, |(jsp87Sign ε.card : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ((jsp87HitVerts p n v h).card : ℝ) := by
        have hc : (∑ ε ∈ jsp87HitVerts p n v h, |(jsp87Sign ε.card : ℝ)|)
            = ∑ _ε ∈ jsp87HitVerts p n v h, (1 : ℝ) :=
          Finset.sum_congr rfl fun ε _ => by rw [jsp87Sign_abs]
        rw [hc, Finset.sum_const, nsmul_eq_mul]
        norm_cast
        ring
      _ ≤ 1 := by exact_mod_cast hone
  rw [jsp87XpLevel_eq_filter, abs_mul, abs_of_pos (jsp87W_pos K h)]
  exact calc jsp87W K h * |∑ ε ∈ jsp87HitVerts p n v h, (jsp87Sign ε.card : ℝ)|
      ≤ jsp87W K h * 1 :=
        mul_le_mul_of_nonneg_left hcore (le_of_lt (jsp87W_pos K h))
    _ = _ := mul_one _

/-- **THE SIZE BOUND (5.36)**, in the unevaluated form. -/
theorem jsp87Xp0_abs_le_weight {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ)
    (hone : ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n v h) :
    |jsp87Xp0 v p n H| ≤ ∑ h ∈ Finset.Icc 1 H, jsp87W K h := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact Finset.sum_le_sum fun h _ => jsp87XpLevel_abs_le v p n h (hone h ‹h ∈ _›)

/-- **THE SIZE BOUND (5.36)**: `|X_p| ≤ |q| · H · 2^{−K}`. -/
theorem jsp87Xp_abs_le {K : ℕ} (q : ℝ) (v : Fin K → ℕ) (p n H : ℕ)
    (hone : ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n v h) :
    |jsp87Xp q v p n H| ≤ |q| * ((H : ℕ) : ℝ) * jsp87W K 0 := by
  have h1 : |jsp87Xp q v p n H| = |q| * |jsp87Xp0 v p n H| := by
    rw [jsp87Xp, abs_mul]
  have h2 := jsp87Xp0_abs_le_weight v p n H hone
  have h3 : (∑ h ∈ Finset.Icc 1 H, jsp87W K h)
      ≤ ((Finset.Icc 1 H).card : ℝ) * jsp87W K 0 := by
    calc (∑ h ∈ Finset.Icc 1 H, jsp87W K h)
        ≤ ∑ _h ∈ Finset.Icc 1 H, (jsp87W K 0 : ℝ) :=
          Finset.sum_le_sum fun h _ => jsp87W_anti K 0 h (Nat.zero_le h)
      _ = ((Finset.Icc 1 H).card : ℝ) * jsp87W K 0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h4 : ((Finset.Icc 1 H).card : ℝ) = (H : ℝ) := by
    norm_cast
    simp
  calc |jsp87Xp q v p n H| = |q| * |jsp87Xp0 v p n H| := h1
    _ ≤ |q| * ∑ h ∈ Finset.Icc 1 H, jsp87W K h :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg q)
    _ ≤ |q| * (((Finset.Icc 1 H).card : ℝ) * jsp87W K 0) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg q)
    _ = |q| * ((H : ℕ) : ℝ) * jsp87W K 0 := by rw [h4]; ring

/-- The variable is a *small* multiple of `q`: the error of the cube sum is
`O(H 2^{−K})`, uniformly in the sample point. -/
theorem jsp87Xp_abs_le_twenty {K : ℕ} (q : ℝ) (v : Fin K → ℕ) (p n H : ℕ)
    (hone : ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n v h)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    |jsp87Xp q v p n H| ≤ 1 / 20 :=
  (jsp87Xp_abs_le q v p n H hone).trans hK

/-! ## §3  Hypothesis (5.19) is discharged, and the endgame of round 116 applies -/

/-- **THE CUBE DIMENSION `K` CAN ALWAYS BE CHOSEN LARGE ENOUGH.**  For every
`q > 0` and `H` there is `K ≥ 1` with `q · H · 2^{−K} ≤ 1/20`: the weights
`2^{−K}` decay geometrically, so hypothesis (5.19) is satisfiable — indeed
automatic — for the cube-alternating variable. -/
theorem exists_K_abs_le {q H : ℝ} (hq : 0 < q) :
    ∃ K : ℕ, K ≥ 1 ∧ q * H * jsp87W K 0 ≤ 1 / 20 := by
  by_cases hH : 0 < H
  · have hqH : 0 < q * H := by positivity
    have hb : 0 < 1 / 20 / (q * H) := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_real (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hb
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · refine ⟨1, by norm_num, ?_⟩
      have hlt : (1 : ℝ) * (q * H) < 1 / 20 := (lt_div_iff₀ hqH).mp hn
      have hW : jsp87W 1 0 = 1 / 2 := by rw [jsp87W_eq_half]; norm_num
      rw [hW]
      nlinarith
    · refine ⟨n + 1, by omega, ?_⟩
      have hanti : jsp87W n 1 ≤ jsp87W n 0 := jsp87W_anti n 0 1 (Nat.zero_le 1)
      have hanti' : (1 / 2 : ℝ)^(n + 1) ≤ (1 / 2 : ℝ)^n := by
        calc (1 / 2 : ℝ)^(n + 1) = (1 / 2 : ℝ)^(1 + n) := by rw [Nat.add_comm]
          _ ≤ (1 / 2 : ℝ)^(0 + n) := by
            rw [← jsp87W_eq_half n 1, ← jsp87W_eq_half n 0]
            exact hanti
          _ = (1 / 2 : ℝ)^n := by rw [Nat.zero_add]
      have hW : jsp87W (n + 1) 0 = (1 / 2 : ℝ)^(n + 1) := by
        simpa using jsp87W_eq_half (n + 1) 0
      rw [hW]
      have hmain : q * H * (1 / 2 : ℝ)^(n + 1) < 1 / 20 := by
        calc q * H * (1 / 2 : ℝ)^(n + 1) ≤ q * H * (1 / 2 : ℝ)^n :=
            mul_le_mul_of_nonneg_left hanti' (le_of_lt hqH)
          _ < q * H * (1 / 20 / (q * H)) := mul_lt_mul_of_pos_left hn hqH
          _ = 1 / 20 := by field_simp
      exact le_of_lt hmain
  · refine ⟨1, by norm_num, ?_⟩
    have hW : jsp87W 1 0 = 1 / 2 := by rw [jsp87W_eq_half]; norm_num
    rw [hW]
    have hmul : q * H * (1 / 2 : ℝ) ≤ 0 := by
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hH)
      linarith
    linarith

/-- **HYPOTHESIS (5.19) HOLDS FOR THE CUBE-ALTERNATING VARIABLE.**  Given the
separation hypothesis at every level, `|q X_p| ≤ 1/20` holds at every sample
point, provided `K` is large enough. -/
theorem jsp87Xp0_abs_le_twenty {K : ℕ} (q : ℝ) (v : Fin K → ℕ) (p n H : ℕ)
    (hone : ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n v h)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    |q * jsp87Xp0 v p n H| ≤ 1 / 20 :=
  jsp87Xp_abs_le_twenty q v p n H hone hK

/-- **THE ENDGAME OF ROUND 116, SPECIALISED TO THE CUBE-ALTERNATING VARIABLES.**

Let the primes of `S₁ ⊆ P` be given their cubes `v p`, let the sample points be
`i : Ω`, and suppose that the hypotheses of §5 hold with

* `T p i = X_p(i) = jsp87Xp0 (v p) p i H`;
* **(5.15)**, **(5.16)–(5.17)** and **(5.21)** as in `Variance.lean`;
* the separation hypothesis `jsp87OneVertex` at every level, and `K` large
  enough that `|q| H 2^{−K} ≤ 1/20` — which *discharges* **(5.19)**.

Then the five error terms `κ₁, …, κ₅` of §5 cannot all be `< 1/30`: their sum
is at least `1/2` by `jsp87_endgame_sum_ge`.  **So the entire probabilistic
content of the reduction reduces to the two arithmetic estimates (5.18) and
(5.21), with hypothesis (5.19) discharged.** -/
theorem jsp87_endgame_cube {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (K : ℕ) (H : ℕ) (v : ℕ → Fin K → ℕ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, jsp87Xp0 (v p) p i H)) - 1‖
      ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P, jsp87Xp0 (v p) p i H))
        - ∏ p ∈ P, jsp87CAvg s (fun i => jsp87e (q * jsp87Xp0 (v p) p i H))‖
      ≤ κ4 + κ5)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var s (fun i => q * jsp87Xp0 (v p) p i H))
    (Hsep : ∀ p ∈ P, ∀ i : ℕ, ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p i (v p) h) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  intro hcontra
  exact jsp87_endgame_impossible s hs q (fun p i => jsp87Xp0 (v p) p i H) κ1 κ2 κ3 κ4 κ5
    hcontra.1 hcontra.2.1 hcontra.2.2.1 hcontra.2.2.2.1 hcontra.2.2.2.2 H15 H1617
    (fun p hp i =>
      jsp87Xp0_abs_le_twenty q (v p) p i H (fun h hh => Hsep p hp i h hh) hK)
    H21

/-! ## §4  The `S₀` mechanism: degenerate cubes, and the variance -/

/-- **THE ALTERNATING SIGNS OF THE CUBE SUM TO ZERO** (for `K ≥ 1`). -/
theorem jsp87sign_sum_zero {K : ℕ} (K1 : 1 ≤ K) :
    ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), (jsp87Sign s.card : ℝ) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le K1
  subst hk
  exact jsp87_cube_cancelR ⟨0, by omega⟩ (fun s => (jsp87Sign s.card : ℝ))
    (fun s => by exact_mod_cast jsp87AltSign_toggle ⟨0, by omega⟩ s)

/-- A multiple of the vanishing alternating sign sum. -/
theorem jsp87sign_sum_mul {K : ℕ} (K1 : 1 ≤ K) (c : ℝ) :
    c * ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), (jsp87Sign s.card : ℝ) = 0 := by
  rw [jsp87sign_sum_zero K1, mul_zero]

/-- **THE ALL-HIT COLLAPSE.**  If *every* vertex of the cube is hit at the level
`h`, the level sum vanishes: the `2^K` alternating signs cancel.  This is the
mechanism behind the role of `S₀` in the split `S₀ ⊎ S₁ ⊎ S₂`. -/
theorem jsp87XpLevel_eq_zero_of_allHit {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ) (K1 : 1 ≤ K)
    (halls : ∀ ε : Finset (Fin K), p ∣ n + jsp87R v h ε) :
    jsp87XpLevel v p n h = 0 := by
  have hset : jsp87HitVerts p n v h = (Finset.univ : Finset (Finset (Fin K))) := by
    ext ε
    simp only [jsp87HitVerts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => halls ε⟩
  rw [jsp87XpLevel_eq_filter, hset]
  exact jsp87sign_sum_mul K1 _

theorem jsp87Xp0_eq_zero_of_allHit {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) (K1 : 1 ≤ K)
    (_H1 : 1 ≤ H)
    (halls : ∀ h ∈ Finset.Icc 1 H, ∀ ε : Finset (Fin K), p ∣ n + jsp87R v h ε) :
    jsp87Xp0 v p n H = 0 := by
  unfold jsp87Xp0
  exact Finset.sum_eq_zero fun h hh =>
    jsp87XpLevel_eq_zero_of_allHit v p n h K1 (halls h hh)

/-- **THE ZERO-PRIME MECHANISM.**  If `p` divides every cube shift *and* `p`
divides the sample point `n`, then every vertex is hit at every level, hence

```
X_p = 0 .
```

This is the reason the primes of `S₀` — those dividing all the cube shifts —
contribute nothing to (5.21): their variable is identically `0`. -/
theorem jsp87Xp0_eq_zero_of_dvd_all {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) (K1 : 1 ≤ K)
    (_H1 : 1 ≤ H) (hn : p ∣ n)
    (hall : ∀ ε : Finset (Fin K), ∀ h : ℕ, p ∣ jsp87R v h ε) :
    jsp87Xp0 v p n H = 0 :=
  jsp87Xp0_eq_zero_of_allHit v p n H K1 (by exact _H1)
    (fun h _ ε => Nat.dvd_add hn (hall ε h))

/-- A function which vanishes everywhere has zero variance. -/
theorem jsp87Var_zero_of_zero {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) (hf : ∀ i : Ω, f i = 0) :
    jsp87Var s f = 0 := by
  have hμ : jsp87FAvg s f = 0 := by
    unfold jsp87FAvg
    rw [Finset.sum_eq_zero fun i _ => by rw [hf i], zero_div]
  have hg : jsp87FAvg s (fun i => (f i - jsp87FAvg s f) ^ 2) = 0 := by
    rw [show (fun i => (f i - jsp87FAvg s f) ^ 2) = (fun _ => (0 : ℝ)) by
      rw [hμ]
      funext i
      rw [hf i]
      norm_num]
    unfold jsp87FAvg
    rw [Finset.sum_const_zero, zero_div]
  unfold jsp87Var
  rw [hg]

/-- **THE `S₀` PRIMES CONTRIBUTE NO VARIANCE.**  If every sample point is
congruent to `0` modulo a prime `p` which divides all the cube shifts, then the
variance of `q X_p` over the sample set vanishes identically.  This is the
reason (5.21) sums only over `S₁`. -/
theorem jsp87Var_zero_of_zeroPrime (s : Finset ℕ) (q : ℝ)
    {K : ℕ} (v : Fin K → ℕ) (p H : ℕ) (K1 : 1 ≤ K) (H1 : 1 ≤ H) (hn : ∀ i : ℕ, p ∣ i)
    (hall : ∀ ε : Finset (Fin K), ∀ h : ℕ, p ∣ jsp87R v h ε) :
    jsp87Var s (fun i => q * jsp87Xp0 v p i H) = 0 := by
  refine jsp87Var_zero_of_zero s _ fun i => ?_
  rw [jsp87Xp0_eq_zero_of_dvd_all v p i H K1 H1 (hn i) hall]
  ring

/-- The average of a constant function is that constant. -/
theorem jsp87FAvg_const {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (c : ℝ) :
    jsp87FAvg s (fun _ => c) = c := by
  have h1 : jsp87FAvg s (fun _ => c) = c * jsp87FAvg s (fun _ => (1 : ℝ)) := by
    simpa using jsp87FAvg_mul_const s c (fun _ => (1 : ℝ))
  rw [h1, jsp87FAvg_one s hs, mul_one]

/-- **THE VARIANCE IS AT MOST THE SECOND MOMENT.**  This is the elementary
inequality `Var f = 𝔼 f² − (𝔼 f)² ≤ 𝔼 f²`, from scratch. -/
theorem jsp87Var_le_avg_sq {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) :
    jsp87Var s f ≤ jsp87FAvg s (fun i => f i ^ 2) := by
  by_cases hs : s.Nonempty
  · have hstep : jsp87FAvg s (fun i => (f i - jsp87FAvg s f) ^ 2)
        = jsp87FAvg s (fun i => f i ^ 2 - 2 * jsp87FAvg s f * f i
            + (jsp87FAvg s f) ^ 2) := by
      congr 1
      funext i
      ring
    have hcalc : jsp87FAvg s (fun i => f i ^ 2 - 2 * jsp87FAvg s f * f i
            + (jsp87FAvg s f) ^ 2)
        = jsp87FAvg s (fun i => f i ^ 2) - (jsp87FAvg s f) ^ 2 := by
      rw [jsp87FAvg_add, jsp87FAvg_sub, jsp87FAvg_mul_const, jsp87FAvg_const s hs]
      ring
    unfold jsp87Var
    rw [hstep, hcalc]
    have hsq : 0 ≤ (jsp87FAvg s f) ^ 2 := sq_nonneg _
    linarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have h0 : jsp87Var s f = 0 := by simp [jsp87Var, jsp87FAvg, he]
    have h1 : jsp87FAvg s (fun i => f i ^ 2) = 0 := by simp [jsp87FAvg, he]
    rw [h0, h1]

/-- **A POINTWISE BOUND ON THE VARIANCE.**  If `|f| ≤ B` pointwise on the sample
set then `Var f ≤ B²`. -/
theorem jsp87Var_le_sq {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) : jsp87Var s f ≤ B ^ 2 := by
  refine le_trans (jsp87Var_le_avg_sq s f) ?_
  by_cases hs : s.Nonempty
  · refine le_trans (jsp87FAvg_le_of_pointwise_le (g := fun _ => (B ^ 2 : ℝ))
      (fun i hi => ?_)) ?_
    · have h2 : f i ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hB).mpr (hf i hi)
      exact h2
    · rw [jsp87FAvg_const s hs]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have h1 : jsp87FAvg s (fun i => f i ^ 2) = 0 := by simp [jsp87FAvg, he]
    rw [h1]
    exact sq_nonneg B

/-- **THE VARIANCE OF THE CUBE-ALTERNATING VARIABLE DECAYS LIKE `4^{−K}`.**  This
is the quantitative statement that makes (5.19) usable in (5.20). -/
theorem jsp87Var_Xp_le {K : ℕ} (s : Finset ℕ) (q : ℝ) (v : Fin K → ℕ) (p H : ℕ)
    (hone : ∀ i ∈ s, ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p i v h) :
    jsp87Var s (fun i => q * jsp87Xp0 v p i H) ≤ ((|q| * ((H : ℕ) : ℝ) * jsp87W K 0) ^ 2) := by
  refine jsp87Var_le_sq s _ _ (mul_nonneg (mul_nonneg (abs_nonneg q)
    (Nat.cast_nonneg H)) (le_of_lt (jsp87W_pos K 0))) fun i hi => ?_
  simpa [jsp87Xp] using jsp87Xp_abs_le q v p i H (hone i hi)

/-- **THE VARIANCE IS ZERO WHEN THE CUBE IS NEVER HIT.** -/
theorem jsp87Var_Xp_zero_of_noHit {K : ℕ} (s : Finset ℕ) (q : ℝ) (v : Fin K → ℕ)
    (p H : ℕ) (hno : ∀ i : ℕ, jsp87Xp0 v p i H = 0) :
    jsp87Var s (fun i => q * jsp87Xp0 v p i H) = 0 := by
  refine jsp87Var_zero_of_zero s _ fun i => ?_
  rw [hno i]
  ring

/-! ## §5  Determinism: `X_p` depends only on the hit pattern -/

/-- **DETERMINISM AT ONE LEVEL.**  If the hit pattern of one sample point
matches that of the other one — a hit at each level, carrying the same sign —
then the two level sums agree.  This is the mechanism behind (5.16)–(5.17):
the variable `X_p` is *determined* by the hit pattern, so two sample points with
the same pattern contribute the same phase. -/
theorem jsp87XpLevel_eq_of_pattern {K : ℕ} (v : Fin K → ℕ) (p n n' h : ℕ)
    (hA : jsp87OneVertex p n v h) (hB : jsp87OneVertex p n' v h)
    (Hpat : ∀ ε : Finset (Fin K), (p ∣ n + jsp87R v h ε) →
      ∃ ε' : Finset (Fin K), p ∣ n' + jsp87R v h ε' ∧
        (jsp87Sign ε'.card : ℝ) = (jsp87Sign ε.card : ℝ))
    (Hpat' : ∀ ε' : Finset (Fin K), (p ∣ n' + jsp87R v h ε') →
      ∃ ε : Finset (Fin K), p ∣ n + jsp87R v h ε ∧
        (jsp87Sign ε.card : ℝ) = (jsp87Sign ε'.card : ℝ)) :
    jsp87XpLevel v p n h = jsp87XpLevel v p n' h := by
  by_cases hA0 : jsp87HitVerts p n v h = ∅
  · have hB0 : jsp87HitVerts p n' v h = ∅ := by
      by_contra hcon
      obtain ⟨ε', hmem⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
      obtain ⟨ε, hmem0, _⟩ := Hpat' ε' (Finset.mem_filter.mp hmem).2
      have hmem2 : ε ∈ jsp87HitVerts p n v h :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem0⟩
      rw [hA0] at hmem2
      simp at hmem2
    rw [jsp87XpLevel_eq_filter, jsp87XpLevel_eq_filter, hA0, hB0, Finset.sum_empty,
      mul_zero]
  · obtain ⟨ε₀, hmem0⟩ := Finset.nonempty_iff_ne_empty.mpr hA0
    obtain ⟨ε₁, hhit1, hsign⟩ := Hpat ε₀ (Finset.mem_filter.mp hmem0).2
    have hmem1 : ε₁ ∈ jsp87HitVerts p n' v h :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit1⟩
    have hB1 : jsp87HitVerts p n' v h = {ε₁} := jsp87HitVerts_eq_singleton hB hmem1
    calc jsp87XpLevel v p n h
        = (jsp87Sign ε₀.card : ℝ) * jsp87W K h :=
          jsp87XpLevel_eq_of_hit v p n h hA ε₀ (Finset.mem_filter.mp hmem0).2
      _ = (jsp87Sign ε₁.card : ℝ) * jsp87W K h := by rw [hsign]
      _ = jsp87XpLevel v p n' h :=
          (jsp87XpLevel_eq_of_hit v p n' h hB ε₁ (Finset.mem_filter.mp hmem1).2).symm

/-- **DETERMINISM OF THE VARIABLE**: `X_p` depends on the sample point only
through the signs of the hit vertices at each level. -/
theorem jsp87Xp0_eq_of_pattern {K : ℕ} (v : Fin K → ℕ) (p n n' H : ℕ)
    (hone : ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n v h)
    (hone' : ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n' v h)
    (Hpat : ∀ h ∈ Finset.Icc 1 H, ∀ ε : Finset (Fin K), (p ∣ n + jsp87R v h ε) →
      ∃ ε' : Finset (Fin K), p ∣ n' + jsp87R v h ε' ∧
        (jsp87Sign ε'.card : ℝ) = (jsp87Sign ε.card : ℝ))
    (Hpat' : ∀ h ∈ Finset.Icc 1 H, ∀ ε' : Finset (Fin K), (p ∣ n' + jsp87R v h ε') →
      ∃ ε : Finset (Fin K), p ∣ n + jsp87R v h ε ∧
        (jsp87Sign ε.card : ℝ) = (jsp87Sign ε'.card : ℝ)) :
    jsp87Xp0 v p n H = jsp87Xp0 v p n' H := by
  unfold jsp87Xp0
  apply Finset.sum_congr rfl
  intro h hh
  exact jsp87XpLevel_eq_of_pattern v p n n' h (hone h hh) (hone' h hh)
    (Hpat h hh) (Hpat' h hh)

/-- **DETERMINISM FROM THE HIT SET**: the same set of hit vertices gives the
same variable — no one-vertex hypothesis needed. -/
theorem jsp87Xp0_eq_of_hitSet {K : ℕ} (v : Fin K → ℕ) (p n n' H : ℕ)
    (Hset : ∀ ε : Finset (Fin K), ∀ h ∈ Finset.Icc 1 H,
      (p ∣ n + jsp87R v h ε ↔ p ∣ n' + jsp87R v h ε)) :
    jsp87Xp0 v p n H = jsp87Xp0 v p n' H := by
  unfold jsp87Xp0
  apply Finset.sum_congr rfl
  intro h hh
  rw [jsp87XpLevel_eq_filter, jsp87XpLevel_eq_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr (show jsp87HitVerts p n v h = jsp87HitVerts p n' v h from ?_) ?_
  · ext ε
    simp only [jsp87HitVerts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Hset ε h hh
  · intro ε _
    rfl

end JSP87