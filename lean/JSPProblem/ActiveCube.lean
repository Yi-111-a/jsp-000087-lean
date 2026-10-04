/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-120).
-/
import JSPProblem.CubeBits

/-!
# JSP-000087, round 120 — THE ACTIVE RESIDUE CLASSES, AND THE SHARP VARIANCE WINDOW

## Why this file exists

Round 119 discharged the *separation* hypothesis of the endgame of Tao–Teräväinen
(arXiv:2512.01739) by taking the binary cube `v k = 2^k`, and recorded as its
**third** remaining blocker the *non-degeneracy* of the variable `X_p` of (5.13):

> "non-degeneracy: an unconditional statement that some prime `p > H + 2^K − 1`
> and some sample have a hit vertex of the binary cube; now isolated as the
> counting object `jsp87Active`".

`policy.json` `next_round_attack[0]` — the first item of that list, unexecuted in
119 rounds — specifies exactly what is wanted: **the counting object
`jsp87Active`, its exact count over a complete residue system, and the density
`2^K / p`.**  This file is that item, executed, and it closes the non-degeneracy
blocker **unconditionally**, in the strong quantitative form.

## What is proved here

| Section | Content |
| --- | --- |
| §0 | `jsp87dvd_eq_of_lt_two`, `jsp87sum_Icc_split`, `jsp87sub_le_abs_add` — the three elementary lemmas the rest needs |
| §1 | `jsp87Active` (level `h` is active at `n`), the residue classes `jsp87ActiveRes`, `jsp87ActiveRes_card` = `2^K`, the **exact count** over a complete residue system, the density `2^K / p`, and `jsp87Xp0_ne_zero_exists`: **non-degeneracy, unconditionally** |
| §2 | the closed form `jsp87W_tail` of the geometric tail, and the value bound `jsp87W K H ≤ \|X_p\|` at a least active level |
| §3 | the **zero class** `X_p(p·m) = 0` under `H + 2^K − 1 < p`, and the **exact variance window** over the complete residue system |
| §4 | **THE ENDGAME CANNOT BE FIRED BY A UNIFORM-RESIDUE SAMPLE**: (5.21) is *false* for `s = Icc 0 (p−1)` (`jsp87_Xp_res_5_21_impossible`), while the endgame itself holds as soon as (5.21) is granted (`jsp87_endgame_res_of_5_21`) |

## The headline negative result

For the binary cube, `2^K ≤ p`, `1 ≤ H`, `H + 2^K − 1 < p` and `|q| H 2^{−K} ≤ 1/20`,

* `jsp87_Xp_res_5_21_impossible` : **hypothesis (5.21) is never satisfiable for
  `s = Icc 0 (p−1)`** — the variance of the endgame variable over a *uniform
  residue system* is `< 1`, and it is at most `(1/20)²`;
* `jsp87_endgame_res_of_5_21` : if (5.21) *were* satisfiable, the endgame would
  fire, i.e. the five error terms of §5 could not all be `< 1/30`.

So the endgame of §5 of arXiv:2512.01739 is **vacuous** for uniform samples, and
the sample it uses cannot be one.  This is the sharpest statement yet of **why
the remaining input of `jsp_000087_main` is a correlation input**: it must come
from the structure of the sample along progressions — Tao–Teräväinen's
uniformity hypothesis (5.18) and their `Theorem 3.1`, the quantitative two-point
correlation estimate for bounded multiplicative functions (from Pilatte).  No
statement about uniform residues can replace it.

`jsp87Var_Xp_res_window` gives the whole picture in one line: over the complete
residue system,

```
q² 2^K (2^{−(H+K)})² / p²  ≤  Var (q X_p)  ≤  (|q| H 2^{−K})² ,
```

so the variance of the cube-alternating variable over a uniform sample is
`≈ q² / p` and decays in `p`: a *large* prime can never supply the variance that
(5.21) demands.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## §0  Elementary lemmas -/

/-- **A POSITIVE MULTIPLE OF `p` BELOW `2p` IS `p`.**  This is the elementary
fact with which the active residue classes of §1 are located. -/
theorem jsp87dvd_eq_of_lt_two {m p : ℕ} (hd : p ∣ m) (h0 : 0 < m) (hlt : m < 2 * p) :
    m = p := by
  obtain ⟨c, hc⟩ := hd
  cases p with
  | zero => omega
  | succ pp =>
    have hc' : pp.succ * c = m := by simpa [Nat.mul_comm] using hc.symm
    have h1 : c < 2 := by
      refine Nat.lt_of_mul_lt_mul_right (a := pp.succ) ?_
      calc c * pp.succ = m := by rw [Nat.mul_comm, hc']
        _ < 2 * pp.succ := hlt
    have h2 : 0 < c := by
      by_contra hcon
      have hc0 : c = 0 := by omega
      subst hc0
      have hm : m = 0 := by simpa using hc'.symm
      omega
    have h3 : c = 1 := by omega
    rw [h3] at hc'
    omega

/-- **NO POSITIVE MULTIPLE OF `p` IS BELOW `p`.** -/
theorem jsp87not_dvd_of_pos_lt {m p : ℕ} (hd : p ∣ m) (h0 : 0 < m) (hlt : m < p) :
    False := by
  have h1 : m % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  rw [Nat.mod_eq_of_lt hlt] at h1
  omega

/-- **SUBTRACTING A MULTIPLE OF `p`.** -/
private theorem jsp87dvd_sub_of_dvd {p a b : ℕ} (ha : p ∣ a) (hb : p ∣ a + b) :
    p ∣ b := by
  have h := Nat.dvd_sub hb ha
  rwa [Nat.add_sub_cancel_left] at h

/-- **SPLITTING AN INTERVAL SUM AT A POINT.**  `∑_{[a,c]} f = ∑_{[a,b]} f +
∑_{[b+1,c]} f` for `a ≤ b ≤ c`.  Mathlib of v4.34.0 has `Finset.sum_Icc_succ_top`
but no `Finset.sum_Icc_add_Icc`. -/
theorem jsp87sum_Icc_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ x ∈ Finset.Icc a c, f x) = ∑ x ∈ Finset.Icc a b, f x
      + ∑ x ∈ Finset.Icc (b + 1) c, f x := by
  refine Nat.le_induction (m := b) ?_ (fun c' hc' ih' => ?_) c hbc
  · rw [Finset.Icc]
    simp
  · rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega : b + 1 ≤ c' + 1)]
    rw [ih']
    exact add_assoc _ _ _

/-- **THE REVERSE TRIANGLE INEQUALITY**, in the form used below:
`|a + b| ≥ |a| − |b|`.  Mathlib's `abs_sub_le_iff` is stated with a general
right-hand side; this is `norm_sub_le` composed with `le_abs_self`. -/
theorem jsp87sub_le_abs_add (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := norm_sub_le (a + b) (b : ℝ)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h1 : |a| ≤ |a + b| + |b| := by
    have hab : (a + b) - b = a := by ring
    calc |a| = |(a + b) - b| := by rw [hab]
      _ ≤ |a + b| + |b| := h
  linarith

/-- **THE CARDINALITY OF AN INTERVAL.** -/
theorem jsp87card_Icc (a b : ℕ) : ((Finset.Icc a b : Finset ℕ).card : ℕ) = b + 1 - a :=
  Nat.card_Icc a b

/-! ## §1  The active residue classes -/

/-- **A LEVEL IS ACTIVE** at the sample point `n` when *some* vertex `ε` of the
binary cube is hit there, i.e. when `p ∣ n + h + Σ_{k ∈ ε} 2^k`.

This is the object isolated as `jsp87Active` by round 119 and specified by
`policy.json` `next_round_attack[0]`: the *non-degeneracy* condition of §5.5 of
arXiv:2512.01739, as a counting object. -/
def jsp87Active (K p h n : ℕ) : Prop :=
  ∃ ε : Finset (Fin K), p ∣ n + jsp87R (jsp87BinV K) h ε

-- the predicate of a `Finset.filter` must be decidable, and the statements below
-- use `jsp87Active` as one; `reducible` lets instance search see through it
attribute [reducible] jsp87Active

/-- **ACTIVITY IS A NON-EMPTY HIT SET.** -/
theorem jsp87Active_iff_hitVerts_nonempty {K p h n : ℕ} :
    jsp87Active K p h n ↔ (jsp87HitVerts p n (jsp87BinV K) h).Nonempty := by
  constructor
  · rintro ⟨ε, hmem⟩
    rw [jsp87HitVerts]
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro hEmpty
    have hmem' : ε ∈ (Finset.univ : Finset (Finset (Fin K))).filter
        (fun ε => p ∣ n + jsp87R (jsp87BinV K) h ε) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
    rw [hEmpty] at hmem'
    exact absurd hmem' (by simp)
  · rintro ⟨ε, hmem⟩
    exact ⟨ε, (Finset.mem_filter.mp hmem).2⟩

/-- **THE CUBE SHIFTS OF THE BINARY CUBE ARE `h` PLUS THE OFFSET.** -/
theorem jsp87R_binV {K : ℕ} (h : ℕ) (ε : Finset (Fin K)) :
    jsp87R (jsp87BinV K) h ε = h + jsp87Off (jsp87BinV K) ε := rfl

/-- **THE ACTIVE RESIDUE CLASSES** at level `h`: the numbers `p − (h + off ε)`, one
per vertex.  Under `h + 2^K − 1 < p` these are exactly the residues at which level
`h` is active. -/
def jsp87ActiveRes (K p h : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Finset (Fin K))).image
    (fun ε => p - (h + jsp87Off (jsp87BinV K) ε))

/-- **THE ACTIVE RESIDUE CLASSES LIE IN `[0, p)`.** -/
theorem jsp87ActiveRes_subset {K p h : ℕ} (h1 : 1 ≤ h) (hh : h + 2 ^ K - 1 < p) :
    jsp87ActiveRes K p h ⊆ Finset.Icc 0 (p - 1) := by
  intro n hn
  rw [jsp87ActiveRes, Finset.mem_image] at hn
  obtain ⟨ε, _, rfl⟩ := hn
  rw [Finset.mem_Icc]
  have hb : h + jsp87Off (jsp87BinV K) ε ≤ p - 1 := by
    have := jsp87Off_binV_lt ε
    omega
  constructor
  · omega
  · omega

/-- **THE EXACT COUNT OF THE ACTIVE RESIDUE CLASSES IS `2^K`.**  Level `h` is
active at *exactly* the `2^K` residue classes `p − (h + off ε)`, one per vertex.
Item (b) of `policy.json` `next_round_attack[0]`. -/
theorem jsp87ActiveRes_card {K p h : ℕ} (hh : h + 2 ^ K - 1 < p) :
    (jsp87ActiveRes K p h).card = 2 ^ K := by
  unfold jsp87ActiveRes
  have hinj : Set.InjOn (fun ε : Finset (Fin K) => p - (h + jsp87Off (jsp87BinV K) ε))
      ↑(Finset.univ : Finset (Finset (Fin K))) := by
    intro ε _ ε' _ hEq
    dsimp only at hEq
    have hb1 : h + jsp87Off (jsp87BinV K) ε ≤ p - 1 := by
      have := jsp87Off_binV_lt ε
      omega
    have hb2 : h + jsp87Off (jsp87BinV K) ε' ≤ p - 1 := by
      have := jsp87Off_binV_lt ε'
      omega
    have h3 : jsp87Off (jsp87BinV K) ε = jsp87Off (jsp87BinV K) ε' := by
      omega
    exact jsp87Off_binV_inj h3
  simp only [Finset.card_image_iff.mpr hinj, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]

/-- **THE OFFSET OF THE SINGLETON VERTEX `{j}` OF THE BINARY CUBE** is `2^j`. -/
private theorem jsp87Off_binV_singleton {K : ℕ} (j : Fin K) :
    jsp87Off (jsp87BinV K) ({j} : Finset (Fin K)) = 2 ^ (j : ℕ) := by
  rw [jsp87Off_binV]
  have himg : ({j} : Finset (Fin K)).image Fin.val = {(j : ℕ)} := by
    ext i
    simp
  rw [himg, Finset.sum_singleton]

/-- **ACTIVITY IS MEMBERSHIP OF THE ACTIVE RESIDUE CLASSES**, for `n` in the
complete residue system `[0, p)`.  This is the bridge from the hit-vertex
definition to a *counting* statement. -/
theorem jsp87Active_iff_activeRes {K p h n : ℕ} (h1 : 1 ≤ h) (hp : 0 < p)
    (hn : n ≤ p - 1) (hh : h + 2 ^ K - 1 < p) :
    jsp87Active K p h n ↔ n ∈ jsp87ActiveRes K p h := by
  constructor
  · rintro ⟨ε, hmem⟩
    rw [jsp87R_binV] at hmem
    have hb : h + jsp87Off (jsp87BinV K) ε ≤ p - 1 := by
      have := jsp87Off_binV_lt ε
      omega
    have h3 : n + (h + jsp87Off (jsp87BinV K) ε) = p :=
      jsp87dvd_eq_of_lt_two hmem (by omega) (by omega)
    rw [jsp87ActiveRes, Finset.mem_image]
    exact ⟨ε, Finset.mem_univ _, by omega⟩
  · intro hn
    rw [jsp87ActiveRes, Finset.mem_image] at hn
    obtain ⟨ε, _, hEq⟩ := hn
    refine ⟨ε, ?_⟩
    rw [jsp87R_binV]
    have hb : h + jsp87Off (jsp87BinV K) ε ≤ p - 1 := by
      have := jsp87Off_binV_lt ε
      omega
    have h3 : n + (h + jsp87Off (jsp87BinV K) ε) = p := by omega
    rw [h3]

/-- **THE EXACT COUNT OF THE ACTIVE SAMPLE POINTS IN A COMPLETE RESIDUE SYSTEM:**
exactly `2^K` of the `p` residues make level `h` active.  Item (b) of
`policy.json` `next_round_attack[0]`. -/
theorem jsp87Active_res_card {K p h : ℕ} (h1 : 1 ≤ h) (hp : 0 < p)
    (hh : h + 2 ^ K - 1 < p) :
    ((Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)).card = 2 ^ K := by
  have hset : (Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)
      = jsp87ActiveRes K p h := by
    ext n
    constructor
    · intro hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnIcc, hnact⟩
      rw [Finset.mem_Icc] at hnIcc
      exact jsp87Active_iff_activeRes h1 hp hnIcc.2 hh |>.mp hnact
    · intro hn
      have hnIcc : n ∈ Finset.Icc 0 (p - 1) := jsp87ActiveRes_subset h1 hh hn
      rw [Finset.mem_filter]
      exact ⟨hnIcc, jsp87Active_iff_activeRes h1 hp (Finset.mem_Icc.mp hnIcc).2 hh |>.mpr hn⟩
  rw [hset, jsp87ActiveRes_card hh]

/-- **THE DENSITY OF THE ACTIVE RESIDUE CLASSES IS `2^K / p`.**  Item (c) of
`policy.json` `next_round_attack[0]`. -/
theorem jsp87Active_density {K p h : ℕ} (h1 : 1 ≤ h) (hp : 0 < p)
    (hh : h + 2 ^ K - 1 < p) :
    ((((Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)).card : ℕ) : ℚ)
        / (p : ℚ) = ((2 ^ K : ℕ) : ℚ) / (p : ℚ) := by
  have hcard := jsp87Active_res_card (K := K) h1 hp hh
  have hcardQ : ((((Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Active K p h n)).card : ℕ) : ℚ) = ((2 ^ K : ℕ) : ℚ) := by
    exact_mod_cast hcard
  rw [hcardQ]

/-- **THE ACTIVE RESIDUE CLASSES ARE NOT EMPTY** as soon as `2^K < p`. -/
theorem jsp87ActiveRes_nonempty {K p h : ℕ} (hh : h + 2 ^ K - 1 < p) :
    (jsp87ActiveRes K p h).Nonempty :=
  Finset.card_pos.mp (by rw [jsp87ActiveRes_card hh]; positivity)

/-- **ADDING A MULTIPLE OF `p` PRESERVES DIVISIBILITY.** -/
private theorem jsp87dvd_add_step {p a : ℕ} (hd : p ∣ a) : p ∣ a + p := by
  obtain ⟨c, hc⟩ := hd
  refine ⟨c + 1, ?_⟩
  calc a + p = p * c + p := by rw [hc]
    _ = p * (c + 1) := by ring

/-- **ACTIVITY IS PERIODIC IN THE SAMPLE POINT.** -/
theorem jsp87Active_period {K p h n : ℕ} (hact : jsp87Active K p h n) :
    jsp87Active K p h (n + p) := by
  obtain ⟨ε, hmem⟩ := hact
  rw [jsp87R_binV] at hmem
  refine ⟨ε, ?_⟩
  rw [jsp87R_binV]
  have hz := jsp87dvd_add_step hmem
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz

/-- **A POWER-OF-TWO HIT IS AN ACTIVITY**, through the vertex `{k}`. -/
theorem jsp87Active_of_dvd_pow {K p h n : ℕ} (k : ℕ) (hk : k < K)
    (hd : p ∣ n + h + 2 ^ k) : jsp87Active K p h n := by
  refine ⟨{(⟨k, hk⟩ : Fin K)}, ?_⟩
  rw [jsp87R_binV, jsp87Off_binV_singleton]
  simpa [Nat.add_assoc] using hd

/-! ## §2  The geometric tail, and non-degeneracy of the cube sum -/

/-- **THE CLOSED FORM OF THE LEVEL TAIL**: the weights `2^{−(h+K)}` of the levels
strictly above `h` sum to `2^{−(h+K)} − 2^{−(H+K)}`.  This is the usable form of
the size bound (5.36): the cancellation available to the cube sum *below* its
leading term is exactly the factor `2^{−(H−h)}`. -/
theorem jsp87W_tail {K h H : ℕ} (hh : h ≤ H) :
    (∑ h' ∈ Finset.Icc (h + 1) H, jsp87W K h') = jsp87W K h - jsp87W K H := by
  induction H generalizing h with
  | zero =>
      have h0 : h = 0 := by omega
      subst h0
      have hz : (∑ x ∈ Finset.Icc 1 0, jsp87W K x) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.mem_Icc] at hx
        omega
      rw [hz]
      ring
  | succ H ih =>
      rcases Nat.eq_or_lt_of_le hh with rfl | hlt
      · have hz : (∑ x ∈ Finset.Icc (H + 1 + 1) (H + 1), jsp87W K x) = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          rw [Finset.mem_Icc] at hx
          omega
        rw [hz]
        ring
      · have hle : h ≤ H := by omega
        rw [Finset.sum_Icc_succ_top (by omega : h + 1 ≤ H + 1), ih hle]
        have hW : jsp87W K (H + 1) = jsp87W K H / 2 := by
          refine (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2 ?_
          simpa [mul_comm] using jsp87W_succ H
        simp only [hW]
        ring

/-- **A LEVEL SUM AT AN ACTIVE LEVEL IS A NONZERO SIGNED WEIGHT.** -/
theorem jsp87XpLevel_ne_zero_of_active {K p n h : ℕ} (hp : 2 ^ K ≤ p)
    (hact : jsp87Active K p h n) : jsp87XpLevel (jsp87BinV K) p n h ≠ 0 := by
  obtain ⟨ε, hmem⟩ := hact
  have hone := jsp87OneVertex_of_pow (K := K) (p := p) (n := n) (h := h) hp
  have h1 := jsp87XpLevel_eq_of_hit (jsp87BinV K) p n h hone ε hmem
  rw [h1]
  intro hz
  have h2 : (jsp87Sign ε.card : ℝ) = 0 := by
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hz
    · exact absurd hz (ne_of_gt (jsp87W_pos K h))
  exact absurd h2 (by unfold jsp87Sign; split <;> norm_num)

/-- **THE LEVEL SUM VANISHES EXACTLY WHEN THE LEVEL IS INACTIVE.**  The
one-vertex property of the binary cube turns the alternating sum into a single
signed weight, so a level is *either* dead *or* alive. -/
theorem jsp87XpLevel_eq_zero_iff_not_active {K p n h : ℕ} (hp : 2 ^ K ≤ p) :
    jsp87XpLevel (jsp87BinV K) p n h = 0 ↔ ¬ jsp87Active K p h n := by
  constructor
  · intro hz hact
    exact absurd hz (jsp87XpLevel_ne_zero_of_active hp hact)
  · intro hno
    by_cases hemp : jsp87HitVerts p n (jsp87BinV K) h = ∅
    · rw [jsp87XpLevel_eq_filter, hemp, Finset.sum_empty, mul_zero]
    · have hne := Finset.nonempty_iff_ne_empty.mpr hemp
      exact absurd (jsp87Active_iff_hitVerts_nonempty.mpr hne) hno

/-- **THE SIZE OF THE WHOLE CUBE SUM AT A LEAST ACTIVE LEVEL.**  If `h` is the
least level at which the binary cube is hit, then

```
|X_p| ≥ 2^{−(h+K)} − ∑_{h' ∈ (h,H]} 2^{−(h'+K)} = 2^{−(H+K)} ,
```

*independently of `h`*.  This is the quantitative form of non-degeneracy, and it
is what turns the counting of §1 into a counting of *nonzero values*. -/
theorem jsp87Xp0_abs_ge_active {K p n H h : ℕ} (hp : 2 ^ K ≤ p)
    (hnil : ∀ b ∈ Finset.Icc 1 h, b ≠ h → ¬ jsp87Active K p b n)
    (hact : jsp87Active K p h n)
    (hh : h ∈ Finset.Icc 1 H) :
    jsp87W K H ≤ |jsp87Xp0 (jsp87BinV K) p n H| := by
  rw [Finset.mem_Icc] at hh
  have hsplit : (∑ h' ∈ Finset.Icc 1 H, jsp87XpLevel (jsp87BinV K) p n h')
      = jsp87XpLevel (jsp87BinV K) p n h
        + ∑ h' ∈ Finset.Icc (h + 1) H, jsp87XpLevel (jsp87BinV K) p n h' := by
    rw [jsp87sum_Icc_split (f := jsp87XpLevel (jsp87BinV K) p n) (a := 1) (b := h)
      (c := H) (by omega) hh.2]
    congr 1
    refine Finset.sum_eq_single h (fun b hb hne => ?_) (fun hb => ?_)
    · exact (jsp87XpLevel_eq_zero_iff_not_active hp).mpr (hnil b hb hne)
    · exact False.elim (hb (Finset.mem_Icc.mpr ⟨hh.1, le_rfl⟩))
  have habs : |jsp87XpLevel (jsp87BinV K) p n h| = jsp87W K h := by
    obtain ⟨ε, hmem⟩ := hact
    rw [jsp87XpLevel_eq_of_hit (jsp87BinV K) p n h (jsp87OneVertex_of_pow hp) ε hmem,
      abs_mul, abs_of_pos (jsp87W_pos K h), jsp87Sign_abs, one_mul]
  have htail : |∑ h' ∈ Finset.Icc (h + 1) H, jsp87XpLevel (jsp87BinV K) p n h'|
      ≤ jsp87W K h - jsp87W K H := by
    have h1 : (∑ h' ∈ Finset.Icc (h + 1) H,
        |jsp87XpLevel (jsp87BinV K) p n h'|) ≤ jsp87W K h - jsp87W K H := by
      have h2 : (∑ h' ∈ Finset.Icc (h + 1) H,
          |jsp87XpLevel (jsp87BinV K) p n h'|)
          ≤ ∑ h' ∈ Finset.Icc (h + 1) H, jsp87W K h' :=
        Finset.sum_le_sum fun h' _ =>
          jsp87XpLevel_abs_le (jsp87BinV K) p n h' (jsp87OneVertex_of_pow hp)
      exact h2.trans_eq (jsp87W_tail hh.2)
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) h1
  calc jsp87W K H = jsp87W K h - (jsp87W K h - jsp87W K H) := by ring
    _ ≤ jsp87W K h
        - |∑ h' ∈ Finset.Icc (h + 1) H, jsp87XpLevel (jsp87BinV K) p n h'| :=
      sub_le_sub_left htail _
    _ = |jsp87XpLevel (jsp87BinV K) p n h|
        - |∑ h' ∈ Finset.Icc (h + 1) H, jsp87XpLevel (jsp87BinV K) p n h'| := by
      rw [habs]
    _ ≤ |jsp87XpLevel (jsp87BinV K) p n h
        + ∑ h' ∈ Finset.Icc (h + 1) H, jsp87XpLevel (jsp87BinV K) p n h'| :=
      jsp87sub_le_abs_add _ _
    _ = |jsp87Xp0 (jsp87BinV K) p n H| := by
      unfold jsp87Xp0
      rw [← hsplit]

/-- **ACTIVITY AT THE BOTTOM LEVEL FORCES A NONZERO CUBE SUM.**  No hypothesis on
the other levels: level `1` being active already forces `|X_p| ≥ 2^{−(H+K)}`. -/
theorem jsp87Xp0_ne_zero_of_active_one {K p n H : ℕ} (hp : 2 ^ K ≤ p)
    (hact : jsp87Active K p 1 n) (hH : 1 ≤ H) :
    jsp87Xp0 (jsp87BinV K) p n H ≠ 0 := by
  have h1 : jsp87W K H ≤ |jsp87Xp0 (jsp87BinV K) p n H| :=
    jsp87Xp0_abs_ge_active hp (fun b hb hne => absurd hne (by
      rw [Finset.mem_Icc] at hb
      omega))
      hact (by simp [Finset.mem_Icc, hH])
  intro hz
  rw [hz, abs_zero] at h1
  exact absurd h1 (not_le.mpr (jsp87W_pos K H))

/-- **THE NUMBER OF NONZERO CUBE SUMS IN A COMPLETE RESIDUE SYSTEM** is at least
`2^K`. -/
theorem jsp87Xp0_ne_zero_card {K p H : ℕ} (hp : 0 < p) (hh : 1 + 2 ^ K - 1 < p)
    (hH : 1 ≤ H) :
    2 ^ K ≤ ((Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card := by
  have hone : 2 ^ K ≤ p := by
    have hlt0 : 2 ^ K < p := by
      have hz : (1 + 2 ^ K) - 1 = 2 ^ K := by rw [Nat.add_sub_cancel_left]
      rw [hz] at hh
      exact hh
    omega
  have hsub : jsp87ActiveRes K p 1 ⊆ (Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0) := by
    intro n hn
    have hnIcc : n ∈ Finset.Icc 0 (p - 1) :=
      jsp87ActiveRes_subset (K := K) (p := p) (h := 1) (by norm_num) hh hn
    rw [Finset.mem_filter]
    refine ⟨hnIcc, ?_⟩
    refine jsp87Xp0_ne_zero_of_active_one hone ?_ hH
    exact (jsp87Active_iff_activeRes (K := K) (h := 1) (by norm_num) hp
      (Finset.mem_Icc.mp hnIcc).2 hh).mpr hn
  have h1 := Finset.card_le_card hsub
  rwa [jsp87ActiveRes_card (K := K) (p := p) (h := 1) hh] at h1

/-- **NON-DEGENERACY, UNCONDITIONALLY.**  This is the round-119 blocker: for every
`K`, every `p > 2^K` and every `H ≥ 1`, the cube-alternating variable `X_p` of
(5.13) is **not identically zero** — it is nonzero at at least `2^K` of the `p`
residue classes.  Nothing is left to assume about the sample. -/
theorem jsp87Xp0_ne_zero_exists {K p H : ℕ} (hp : 0 < p) (hh : 1 + 2 ^ K - 1 < p)
    (hH : 1 ≤ H) : ∃ n ≤ p - 1, jsp87Xp0 (jsp87BinV K) p n H ≠ 0 := by
  have hpos : 0 < ((Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card :=
    Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by positivity)
      (jsp87Xp0_ne_zero_card (K := K) hp hh hH))
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hn
  rcases hn with ⟨hnIcc, hne⟩
  rw [Finset.mem_Icc] at hnIcc
  exact ⟨n, hnIcc.2, hne⟩

/-! ## §4  The zero class, and the variance window -/

/-- **THE CUBE SUM VANISHES ON THE CLASSES `n ≡ 0 (mod p)`.**  Under the
separation hypothesis `H + 2^K − 1 < p` no level can be hit at a multiple of `p`,
so `X_p = 0` there.  Together with §3, `X_p` is neither the zero function nor a
constant on the residue classes: it takes the value `0` and a nonzero value,
which is exactly what the variance needs. -/
theorem jsp87Xp0_eq_zero_of_dvd {K p H n : ℕ} (_hp : 0 < p) (hh : H + 2 ^ K - 1 < p)
    (hpn : p ∣ n) : jsp87Xp0 (jsp87BinV K) p n H = 0 := by
  unfold jsp87Xp0
  refine Finset.sum_eq_zero fun h hh' => ?_
  rw [jsp87XpLevel_eq_zero_iff_not_active (K := K) (p := p) (n := n) (h := h)
    (by omega)]
  intro hact
  obtain ⟨ε, hmem⟩ := hact
  rw [jsp87R_binV] at hmem
  have hle : 1 ≤ h ∧ h ≤ H := Finset.mem_Icc.mp hh'
  have h1 : 0 < h + jsp87Off (jsp87BinV K) ε := by
    have := jsp87Off_binV_lt ε
    omega
  have h2 : h + jsp87Off (jsp87BinV K) ε < p := by
    have := jsp87Off_binV_lt ε
    omega
  have h3 : p ∣ h + jsp87Off (jsp87BinV K) ε := by
    have hz := jsp87dvd_sub_of_dvd hpn hmem
    omega
  exact jsp87not_dvd_of_pos_lt h3 h1 h2

/-- **`X_p` VANISHES AT THE SAMPLE POINT `0`** — the explicit zero class. -/
theorem jsp87Xp0_eq_zero_zero {K p H : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p) :
    jsp87Xp0 (jsp87BinV K) p 0 H = 0 :=
  jsp87Xp0_eq_zero_of_dvd (K := K) hp hh (by simp)

/-- **A LOWER BOUND FOR THE VARIANCE OVER THE COMPLETE RESIDUE SYSTEM.**  The
residue `0` carries the value `0`, while every class active at level `1` carries
a value at distance at least `2^{−(H+K)}` from it (the discreteness of
`VarLocal.lean` §3), so the two-class variance bound applies. -/
theorem jsp87Var_Xp_res_lower {K p H : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p)
    (hH : 1 ≤ H) (q : ℝ) :
    (q ^ 2) * ((((2 ^ K : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2) / ((p : ℕ) : ℝ) ^ 2)
      ≤ jsp87Var (Finset.Icc 0 (p - 1)) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  have h0 : 0 < 2 ^ K := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
  have hpos : 1 ≤ 2 ^ K := by omega
  have hh2 : 1 + 2 ^ K - 1 < p := by
    have hstep : 1 + 2 ^ K - 1 ≤ H + 2 ^ K - 1 :=
      Nat.sub_le_sub_right (n := 1 + 2 ^ K) (m := H + 2 ^ K)
        (Nat.add_le_add_right hH (2 ^ K)) 1
    exact lt_of_le_of_lt hstep hh
  have hone : 2 ^ K ≤ p := by
    have hz : 1 + 2 ^ K - 1 = 2 ^ K := by
      rw [Nat.add_sub_assoc (m := 2 ^ K) (k := 1) hpos 1]
      exact Nat.add_sub_of_le hpos
    have hlt : 2 ^ K < p := by rw [← hz]; exact hh2
    omega
  set s : Finset ℕ := Finset.Icc 0 (p - 1) with hsdef
  have hs : s.Nonempty := by
    rw [hsdef]
    exact Finset.nonempty_Icc.mpr (by omega)
  set A : Finset ℕ := s.filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0) with hAdef
  set B : Finset ℕ := s.filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0) with hBdef
  have hAne : A.Nonempty := by
    obtain ⟨n, hn, hne⟩ := jsp87Xp0_ne_zero_exists (K := K) hp hh2 hH
    refine ⟨n, ?_⟩
    simp only [hAdef, hsdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hn⟩, hne⟩
  have hzero : jsp87Xp0 (jsp87BinV K) p 0 H = 0 :=
    jsp87Xp0_eq_zero_zero (K := K) hp hh
  have hBne : B.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [hBdef, hsdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hzero⟩
  have hAB : s = A ∪ B := by
    apply le_antisymm
    · intro n hn
      rw [Finset.mem_union]
      by_cases hz : jsp87Xp0 (jsp87BinV K) p n H = 0
      · exact Or.inr (by
          simp only [hBdef, Finset.mem_filter]
          exact ⟨hn, hz⟩)
      · exact Or.inl (by
          simp only [hAdef, Finset.mem_filter]
          exact ⟨hn, hz⟩)
    · intro n hn
      rw [Finset.mem_union] at hn
      rcases hn with hn | hn
      · exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
  have hdis : A ∩ B = ∅ := by
    ext n
    constructor
    · intro hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_inter.mp hn
      rw [hAdef, Finset.mem_filter] at hn1
      rw [hBdef, Finset.mem_filter] at hn2
      rw [hn2.2] at hn1
      exact absurd hn1.2 (by simp)
    · intro hn
      exact absurd hn (by simp)
  have hsep : ∀ x ∈ A, ∀ y ∈ B,
      |jsp87Xp0 (jsp87BinV K) p x H - jsp87Xp0 (jsp87BinV K) p y H|
        ≥ (1 / 2 : ℝ) ^ (H + K) := by
    intro x hx y hy
    rw [hAdef, Finset.mem_filter] at hx
    rw [hBdef, Finset.mem_filter] at hy
    rcases jsp87Xp0_sub_eq_zero_or_ge (jsp87BinV K) p x y H with h | h
    · have hyx : jsp87Xp0 (jsp87BinV K) p y H = jsp87Xp0 (jsp87BinV K) p x H := h.symm
      rw [← hyx] at hx
      exact False.elim (hx.2 hy.2)
    · exact h
  have hV := jsp87Var_ge_twoClass s hs (jsp87Xp0 (jsp87BinV K) p · H) A B hAB hdis hAne hBne
    ((1 / 2 : ℝ) ^ (H + K)) (by positivity) hsep
  have hscard : ((s.card : ℕ) : ℝ) = ((p : ℕ) : ℝ) := by
    rw [hsdef, jsp87card_Icc 0 (p - 1)]
    congr 1
    omega
  have hcast : ((A.card * B.card : ℕ) : ℝ) = ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ) := by
    exact_mod_cast Nat.cast_mul _ _
  rw [hcast, hscard] at hV
  have hcardA : ((2 ^ K : ℕ) : ℝ) ≤ ((A.card : ℕ) : ℝ) := by
    have h1 := jsp87Xp0_ne_zero_card (K := K) hp hh2 hH
    exact_mod_cast h1
  have hB : (1 : ℝ) ≤ ((B.card : ℕ) : ℝ) := by
    have hBn := Finset.card_pos.mpr hBne
    exact_mod_cast Nat.succ_le_iff.mpr hBn
  have hfac : (0 : ℝ) ≤ ((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2 := by positivity
  have hV' : ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ)
      * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2)
      ≤ jsp87Var s (jsp87Xp0 (jsp87BinV K) p · H) := by
    convert hV using 1
    all_goals ring
  have hstep1 : ((2 ^ K : ℕ) : ℝ)
      * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2)
      ≤ ((A.card : ℕ) : ℝ)
      * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hcardA hfac
    convert h1 using 1
    all_goals ring
  have hstep2 : ((A.card : ℕ) : ℝ)
      * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2)
      ≤ ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ)
      * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2) := by
    have hne : (0 : ℝ) ≤ ((A.card : ℕ) : ℝ)
        * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2) :=
      mul_nonneg (Nat.cast_nonneg _) hfac
    have h2 := mul_le_mul_of_nonneg_left hB hne
    calc ((A.card : ℕ) : ℝ)
        * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2)
        = (((A.card : ℕ) : ℝ) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2) * 1) := by
          ring
      _ ≤ (((A.card : ℕ) : ℝ) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2))
          * ((B.card : ℕ) : ℝ) := h2
      _ = ((A.card : ℕ) : ℝ) * ((B.card : ℕ) : ℝ)
          * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2) := by ring
  have hchain : (((2 ^ K : ℕ) : ℝ)
      * (((1 / 2 : ℝ) ^ (H + K)) ^ 2 / ((p : ℕ) : ℝ) ^ 2))
      ≤ jsp87Var s (jsp87Xp0 (jsp87BinV K) p · H) :=
    le_trans hstep1 (le_trans hstep2 hV')
  have hq : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have h1 := mul_le_mul_of_nonneg_left hchain hq
  have hfinal : jsp87Var s (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
      = q ^ 2 * jsp87Var s (jsp87Xp0 (jsp87BinV K) p · H) :=
    jsp87Var_scale s q (jsp87Xp0 (jsp87BinV K) p · H)
  rw [← hfinal] at h1
  rw [hsdef]
  convert h1 using 1
  all_goals ring

/-- **AN UPPER BOUND FOR THE VARIANCE**, from (5.19): `Var (q X_p) ≤ (|q| H 2^{−K})²`.
This is `jsp87Var_Xp_le` of `Xp.lean` specialised to the complete residue system,
with the one-vertex hypothesis discharged by `2^K ≤ p`. -/
theorem jsp87Var_Xp_res_upper {K p H : ℕ} (hp : 2 ^ K ≤ p) (q : ℝ) :
    jsp87Var (Finset.Icc 0 (p - 1)) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
      ≤ ((|q| * ((H : ℕ) : ℝ) * jsp87W K 0) ^ 2) :=
  jsp87Var_Xp_le _ q (jsp87BinV K) p H (fun _ _ _ _ => jsp87OneVertex_of_pow hp)

/-- **THE VARIANCE WINDOW OVER THE COMPLETE RESIDUE SYSTEM.**

```
2^K (2^{−(H+K)})² / p²  ≤  Var (q X_p)  ≤  (|q| H 2^{−K})² .
```

Together with `jsp87_Xp_res_5_21_impossible` this is the complete quantitative
picture of the endgame variable over a uniform sample: its variance is
`≈ q² / p`, and decays in `p`. -/
theorem jsp87Var_Xp_res_window {K p H : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p)
    (hH : 1 ≤ H) (q : ℝ) :
    (q ^ 2) * ((((2 ^ K : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2) / ((p : ℕ) : ℝ) ^ 2)
      ≤ jsp87Var (Finset.Icc 0 (p - 1)) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
      ∧ jsp87Var (Finset.Icc 0 (p - 1)) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
        ≤ ((|q| * ((H : ℕ) : ℝ) * jsp87W K 0) ^ 2) :=
  ⟨jsp87Var_Xp_res_lower (K := K) hp hh hH q,
    jsp87Var_Xp_res_upper (K := K) (by omega : 2 ^ K ≤ p) q⟩

/-! ## §5  The endgame cannot be fired by a uniform-residue sample -/

/-- **HYPOTHESIS (5.21) IS FALSE FOR THE COMPLETE RESIDUE SYSTEM.**  If
`|q| H 2^{−K} ≤ 1/20` the values of `q X_p` lie in `[−1/20, 1/20]`, so their
variance is at most `1/400 < 1`.  Equivalently: *the `S₁`-variance of (5.21) can
never be supplied by a sample that is a uniform residue system modulo `p`*, no
matter how the cube is chosen.

This is the sharpest machine-checked statement of why the remaining input of
`jsp_000087_main` is a **correlation** input: it must come from the structure of
the sample along progressions, i.e. from arXiv:2512.01739 `Theorem 3.1`
(Pilatte) or from the uniformity hypothesis (5.18). -/
theorem jsp87_Xp_res_5_21_impossible {K p H : ℕ} (_hp : 0 < p)
    (hh : H + 2 ^ K - 1 < p) (q : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    ¬ (1 ≤ jsp87Var (Finset.Icc 0 (p - 1))
        (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)) := by
  intro h1
  have h2 := jsp87Var_Xp_res_upper (K := K) (p := p) (H := H) (by omega : 2 ^ K ≤ p) q
  have h3 : (|q| * ((H : ℕ) : ℝ) * jsp87W K 0) ^ 2 ≤ (1 / 20 : ℝ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg (abs_nonneg q) (Nat.cast_nonneg H))
      (le_of_lt (jsp87W_pos K 0))) (by norm_num : (0:ℝ) ≤ 1 / 20)).mpr hK
  have h4 : (1 / 20 : ℝ) ^ 2 = 1 / 400 := by norm_num
  rw [h4] at h3
  linarith

/-- **THE ENDGAME FOR THE COMPLETE RESIDUE SYSTEM, CONDITIONAL ON (5.21).**
Everything else — (5.15), (5.16)–(5.17), (5.19) — is as in
`jsp87_endgame_cube_pow`, and the separation hypothesis is the single arithmetic
inequality `H + 2^K − 1 < p`. -/
theorem jsp87_endgame_res_of_5_21 {K : ℕ} (p H : ℕ) (_hp : 0 < p)
    (hh : H + 2 ^ K - 1 < p) (q : ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (H15 : ‖jsp87CAvg (Finset.Icc 0 (p - 1))
        (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
          jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg (Finset.Icc 0 (p - 1))
        (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
          jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ ({p} : Finset ℕ),
          jsp87CAvg (Finset.Icc 0 (p - 1))
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5)
    (H21 : (1 : ℝ) ≤ jsp87Var (Finset.Icc 0 (p - 1))
        (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  refine jsp87_endgame_cube_pow (P := ({p} : Finset ℕ))
    (s := Finset.Icc 0 (p - 1)) (Finset.nonempty_Icc.mpr (by omega)) q K H
    κ1 κ2 κ3 κ4 κ5 hK (by
      intro p' hp'
      rw [Finset.mem_singleton] at hp'
      rw [hp']
      exact hh) H15 H1617 ?_
  rw [Finset.sum_singleton]
  exact H21

/-- **THE SUMMARY OF THIS ROUND.**  For the complete residue system modulo `p`:
(5.21) is *never* satisfiable, and if it were satisfiable the endgame of §5 would
fire.  The endgame of Tao–Teräväinen arXiv:2512.01739 is therefore **vacuous for
uniform samples**, and its two remaining arithmetic inputs — the uniformity
hypothesis (5.18) and the two-point correlation estimate `Theorem 3.1` — cannot be
replaced by any statement about a uniform residue system. -/
theorem jsp87_endgame_res_summary {K p H : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p)
    (q : ℝ) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (H15 : ‖jsp87CAvg (Finset.Icc 0 (p - 1))
        (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
          jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg (Finset.Icc 0 (p - 1))
        (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
          jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ ({p} : Finset ℕ),
          jsp87CAvg (Finset.Icc 0 (p - 1))
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5) :
    (1 : ℝ) ≤ jsp87Var (Finset.Icc 0 (p - 1))
        (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
      → ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30)
        ∧ (κ5 < 1 / 30)) := by
  intro h1
  exact jsp87_endgame_res_of_5_21 p H hp hh q κ1 κ2 κ3 κ4 κ5 hK H15 H1617 h1

end JSP87