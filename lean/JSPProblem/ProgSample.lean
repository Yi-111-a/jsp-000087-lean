/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-118).
-/
import JSPProblem.CorrelSample

/-!
# JSP-000087, round 123 — THE SAMPLE AS AN OBJECT: EQUIDISTRIBUTION OF THE CUBE
# SUM ALONG AN ARITHMETIC PROGRESSION

## Why this file exists

Round 122 proved that hypothesis (5.21) of the endgame of arXiv:2512.01739 is a
**purely geometric condition on the sample**,

```
(5.21′)   1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ S₁} f_p (1 − f_p) ,
          f_p = jsp87NzFrac K p H s  =  #{ n ∈ s : X_p n ≠ 0 } / #{ n ∈ s } ,
```

and that it is impossible for a sample supported on one residue class modulo some
`p ∈ S₁` (`jsp87_5_21_singleRes_impossible`).  `policy.json`
`next_round_attack[0]` asked for exactly one object:

> "Make `s` an explicit structured set — the two candidates are (a) the AP sample
> `s = image (fun k => n0 + D*k) (Icc 0 N)`, and (b) the sieve sample
> `s = {n : n ≤ N, p ∣ n}` — and **COMPUTE `jsp87NzFrac K p H s` for it** …
> Deliverable: either a (5.21′) witness (which would CLOSE `jsp_000087_main`
> modulo (5.18)) or a machine-checked obstruction for the AP sample."

**This file computes it, for both candidates, and settles them.**

* §1: the residue map `j ↦ (n₀ + D j) mod p` of a progression is a **permutation
  of the residue system** whenever `p` is prime and `p ∤ D`
  (`jsp87Prog_block_bij`, proved in `ZMod p`, where `ZMod p` is a field exactly
  when `p` is prime).
* §2: `jsp87NzResCard K p H` — the number of residues at which the cube sum is
  nonzero — with `2^K ≤ jsp87NzResCard K p H ≤ H · 2^K` and `≤ p − 1`.  The upper
  bound needs the converse half of `jsp87XpLevel_eq_zero_iff_not_active`
  (`jsp87Xp0_ne_zero_iff_active`), which is new.
* §3: a *block* of `p` consecutive terms of a progression contains **exactly**
  `p − jsp87NzResCard K p H` zeros (`jsp87Prog_zero_card_block`), hence for a
  whole number of blocks the **exact value** of the quantity (5.21) needs
  (`jsp87_nzFrac_prog_blocks`):

  ```
  jsp87NzFrac K p H (jsp87Prog n₀ D (c·p − 1))  =  jsp87NzResCard K p H / p
  ```

  for **every** `c ≥ 1`, **every** `n₀` and **every** `D` coprime to `p` — the
  nonzero fraction is independent of the sample length, of the starting point and
  of the step.  This is the first *exact* value of `f_p` that is not the
  degenerate complete-residue-system value of round 120.
* §4: `jsp87ProgFull n₀ D P := jsp87Prog n₀ D (∏ P − 1)` is the **canonical
  structured sample** of `policy.json` item 1: a whole number of blocks for
  *every* prime of `S₁` at once.  `jsp87ProgFull_nzFrac` computes `f_p` on it and
  `jsp87ProgFull_hne` supplies the two-class hypothesis `hne`
  **unconditionally**.
* §5: **candidate (b) is dead.**  The sieve sample is *exactly* the zero class of
  `X_p` (`jsp87_nzFrac_sieve_zero`), and its variance contribution to (5.21) is
  literally `0` (`jsp87Var_sieve_zero`, `jsp87_5_21_sieve_impossible`).
* §6: **the endgame on the canonical sample.**  `jsp87_endgame_progFull` is
  arXiv:2512.01739 §5.3–§5.14 with (5.21) replaced by the *explicit arithmetic*
  (5.21b) `1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ S₁} (c_p/p)(1 − c_p/p)`,
  `c_p = jsp87NzResCard K p H`; and §6.2 converts (5.21b) into a statement about
  the **harmonic mass of the prime set**:

  ```
  (5.21b)  ⟹  ∑_{p ∈ S₁} 1/p  ≥  2^{2H+K} / (H q²)     (jsp87_5_21_needs_recipSum)
  ```

  while `jsp87_5_21_prog_of_recipSum` is the converse: an explicit **sufficient**
  condition, in terms of `p ≥ H·2^K` and one reciprocal sum only, under which
  (5.21b) *holds*.

## What is *not* proved here

`jsp_000087_main` is **not declared**.  Two arithmetic inputs remain, both
statements about the prime set `S₁`, and neither a Mathlib lemma:

* **(5.18)** the five estimates `κ_j = o(1)`, `j = 1 … 5`;
* **(5.21b)** the reciprocal-sum inequality above, i.e. that `S₁` has enough prime
  mass.  Mathlib contains no Chowla-type or Elliott-type statement for
  multiplicative functions, so `Theorem 3.1` of arXiv:2512.01739 (from Pilatte),
  the tool that produces such a prime set, cannot be supplied here.

What is new is that both remaining inputs are statements about **one explicit
object**, `jsp87ProgFull n₀ D P`, and that the progression candidate (a) is
settled in both directions instead of being merely excluded.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 4000000

/-! ## §0  The progression sample -/

/-- **AN ARITHMETIC-PROGRESSION SAMPLE**: the image of `[0, N]` under
`j ↦ n₀ + D j`.  Candidate (a) of `policy.json` `next_round_attack[0]`. -/
def jsp87Prog (n0 D N : ℕ) : Finset ℕ :=
  (Finset.Icc 0 N).image (fun j => n0 + D * j)

attribute [reducible] jsp87Prog

/-- **MEMBERSHIP IN THE PROGRESSION SAMPLE.** -/
theorem jsp87Prog_mem_iff {n0 D N n : ℕ} :
    n ∈ jsp87Prog n0 D N ↔ ∃ j ≤ N, n = n0 + D * j := by
  constructor
  · intro h
    rw [jsp87Prog, Finset.mem_image] at h
    obtain ⟨j, hj, heq⟩ := h
    exact ⟨j, (Finset.mem_Icc.mp hj).2, heq.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hj⟩, rfl⟩

/-- **THE PROGRESSION MAP IS INJECTIVE AS SOON AS THE STEP IS POSITIVE.** -/
private theorem jsp87prog_injOn {n0 D : ℕ} (hD : 0 < D) (s : Finset ℕ) :
    Set.InjOn (fun j : ℕ => n0 + D * j) ↑s := by
  intro a _ b _ heq
  have hab : n0 + D * a = n0 + D * b := heq
  exact Nat.mul_left_cancel hD (by omega)

/-- **THE CARDINALITY OF THE PROGRESSION SAMPLE** is the length of the index
interval. -/
theorem jsp87Prog_card {n0 D N : ℕ} (hD : 0 < D) : (jsp87Prog n0 D N).card = N + 1 := by
  rw [jsp87Prog, Finset.card_image_iff.mpr (jsp87prog_injOn hD _), jsp87card_Icc]
  omega

/-- **THE PROGRESSION SAMPLE IS NONEMPTY.** -/
theorem jsp87Prog_nonempty {n0 D N : ℕ} : (jsp87Prog n0 D N).Nonempty :=
  ⟨n0, Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le N⟩, rfl⟩⟩

/-- **SPLITTING AN INTERVAL.**  This Mathlib tree has no `Finset.Icc_union_Icc`;
this is the one-line replacement. -/
private theorem jsp87Icc_split {a b c : ℕ} (h1 : a ≤ b) (h2 : b < c) :
    Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
  ext n
  rw [Finset.mem_Icc, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
  omega

/-! ## §1  The residue map of a progression permutes the residue system -/

/-- **ADDING A MULTIPLE OF `p` DOES NOT CHANGE THE RESIDUE.** -/
private theorem jsp87mod_add_dvd {p a m : ℕ} (_hp : 0 < p) (hm : p ∣ m) :
    (a + m) % p = a % p := by
  rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hm, Nat.add_zero, Nat.mod_mod]

/-- **THE RESIDUE MAP OF A PROGRESSION IS INJECTIVE ON ONE BLOCK** whenever `p` is
prime and `p ∤ D`.  This Mathlib tree has no lemma on the injectivity of a
multiplication map modulo a prime; the argument is done in `ZMod p`, which is a
field exactly when `p` is prime. -/
private theorem jsp87prog_res_inj {p n0 D : ℕ} (hpc : p.Prime) (hD : ¬ p ∣ D)
    {j j' : ℕ} (hj : j ≤ p - 1) (hj' : j' ≤ p - 1)
    (heq : (n0 + D * j) % p = (n0 + D * j') % p) : j = j' := by
  have hp0 : 0 < p := hpc.pos
  letI : Fact p.Prime := ⟨hpc⟩
  have hZ : ((n0 + D * j : ℕ) : ZMod p) = ((n0 + D * j' : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ p).mpr heq
  have hmul : ((D : ℕ) : ZMod p) * ((j : ℕ) : ZMod p)
      = ((D : ℕ) : ZMod p) * ((j' : ℕ) : ZMod p) := by
    have hdj : ((D : ℕ) : ZMod p) * ((j : ℕ) : ZMod p)
        = ((n0 + D * j : ℕ) : ZMod p) - ((n0 : ℕ) : ZMod p) := by
      rw [Nat.cast_add, Nat.cast_mul]
      ring
    have hdj' : ((D : ℕ) : ZMod p) * ((j' : ℕ) : ZMod p)
        = ((n0 + D * j' : ℕ) : ZMod p) - ((n0 : ℕ) : ZMod p) := by
      rw [Nat.cast_add, Nat.cast_mul]
      ring
    rw [hdj]
    rw [hdj']
    rw [hZ]
  have hD0 : ((D : ℕ) : ZMod p) ≠ 0 :=
    fun hz => hD ((ZMod.natCast_eq_zero_iff D p).mp hz)
  have hzero : ((D : ℕ) : ZMod p) * (((j : ℕ) : ZMod p) - ((j' : ℕ) : ZMod p)) = 0 := by
    rw [mul_sub, hmul]
    ring
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hD0
  · have hjZ : ((j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) := sub_eq_zero.mp h
    have hmod := (ZMod.natCast_eq_natCast_iff' j j' p).mp hjZ
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    exact hmod

private theorem jsp87prog_res_injOnIcc {p n0 D : ℕ} (hpc : p.Prime) (hD : ¬ p ∣ D) :
    Set.InjOn (fun j : ℕ => (n0 + D * j) % p) ↑(Finset.Icc 0 (p - 1)) := by
  intro a ha b hb heq
  exact jsp87prog_res_inj hpc hD (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2 heq

/-- **THE RESIDUE MAP OF A PROGRESSION IS A PERMUTATION OF THE RESIDUE SYSTEM.**
`jsp87Prog_block_bij`: if `p` is prime and `p ∤ D` then

```
{ (n₀ + D j) mod p : j < p }  =  { 0, 1, …, p − 1 } ,
```

so the sample points of any `p`-block of a progression hit **every** residue class
exactly once.  This is the arithmetic core of item 1 of `policy.json`
`next_round_attack[0]`. -/
theorem jsp87Prog_block_bij {p n0 D : ℕ} (hpc : p.Prime) (hD : ¬ p ∣ D) :
    (Finset.Icc 0 (p - 1)).image (fun j => (n0 + D * j) % p) = Finset.Icc 0 (p - 1) := by
  have hp0 : 0 < p := hpc.pos
  have hsub : (Finset.Icc 0 (p - 1)).image (fun j => (n0 + D * j) % p)
      ⊆ Finset.Icc 0 (p - 1) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨j, _, rfl⟩ := hn
    refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
    have hlt : (n0 + D * j) % p < p := Nat.mod_lt _ hp0
    omega
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_iff.mpr (jsp87prog_res_injOnIcc hpc hD)]

/-- **EVERY RESIDUE IS HIT BY SOME SAMPLE POINT OF THE FIRST BLOCK.** -/
theorem jsp87Prog_res_surj {p n0 D r : ℕ} (hpc : p.Prime) (hD : ¬ p ∣ D) (hr : r < p) :
    ∃ j < p, (n0 + D * j) % p = r := by
  have hmem : r ∈ (Finset.Icc 0 (p - 1)).image (fun j => (n0 + D * j) % p) := by
    rw [jsp87Prog_block_bij hpc hD]
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
  rw [Finset.mem_image] at hmem
  obtain ⟨j, hj, heq⟩ := hmem
  refine ⟨j, ?_, heq⟩
  have := (Finset.mem_Icc.mp hj).2
  omega

/-- **THE CUBE SUM AT A SHIFTED SAMPLE INDEX.**  `jsp87Prog_shift_eq`: the cube sum
at the sample index `a + j` equals the cube sum at the index `j`, for every `a` —
the `j`-indexed form of `jsp87Xp0_eq_of_res`. -/
theorem jsp87Prog_shift_eq {K p H n0 D a j : ℕ} (hp : 0 < p) (ha : p ∣ a) :
    jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H
      = jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H := by
  obtain ⟨k, hk⟩ := ha
  have h1 : (n0 + D * (a + j)) % p = (n0 + D * j) % p := by
    have hconv : n0 + D * (a + j) = (n0 + D * j) + D * a := by ring
    rw [hconv]
    exact jsp87mod_add_dvd (p := p) (a := n0 + D * j) (m := D * a) hp
      ⟨D * k, by rw [hk]; ring⟩
  exact jsp87Xp0_eq_of_res (jsp87BinV K) h1

/-- **SHIFTING THE SAMPLE INDEX BY A WHOLE BLOCK MULTIPLE CHANGES NOTHING.** -/
theorem jsp87Prog_zero_shift {K p H n0 D a j : ℕ} (hp : 0 < p) (ha : p ∣ a) :
    (jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H = 0)
      ↔ (jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0) :=
  (jsp87Prog_shift_eq (K := K) hp ha).symm ▸ Iff.rfl

/-! ## §2  The number of nonzero cube sums in one block -/

/-- **THE NUMBER OF NONZERO CUBE SUMS IN A COMPLETE RESIDUE SYSTEM** — the exact
constant that enters (5.21′) along a progression. -/
noncomputable def jsp87NzResCard (K p H : ℕ) : ℕ :=
  ((Finset.Icc 0 (p - 1)).filter
    (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card

/-- **A NONZERO CUBE SUM MEANS THAT SOME LEVEL IS ACTIVE.**  This is the converse
half of `jsp87XpLevel_eq_zero_iff_not_active`, summed over the levels; it is what
makes the *union bound* of `jsp87NzResCard_bounds` legitimate. -/
theorem jsp87Xp0_ne_zero_iff_active {K p n H : ℕ} (hK : 2 ^ K ≤ p) (_hH : 1 ≤ H)
    (hne : jsp87Xp0 (jsp87BinV K) p n H ≠ 0) :
    ∃ h ∈ Finset.Icc 1 H, jsp87Active K p h n := by
  by_cases hex : ∃ h ∈ Finset.Icc 1 H, jsp87Active K p h n
  · exact hex
  · have hz : jsp87Xp0 (jsp87BinV K) p n H = 0 := by
      have heq : jsp87Xp0 (jsp87BinV K) p n H
          = ∑ h ∈ Finset.Icc 1 H, jsp87XpLevel (jsp87BinV K) p n h := rfl
      rw [heq]
      refine Finset.sum_eq_zero fun h hh' => ?_
      rw [jsp87XpLevel_eq_zero_iff_not_active hK]
      exact fun hact => hex ⟨h, hh', hact⟩
    exact (hne hz).elim

/-- **THE NUMBER OF NONZERO CUBE SUMS IS POSITIVE** — the quantitative
non-degeneracy of round 120, packaged as a single number. -/
theorem jsp87NzResCard_pos {K p H : ℕ} (hp : 0 < p) (hH : 1 ≤ H)
    (hh : 1 + 2 ^ K - 1 < p) : 1 ≤ jsp87NzResCard K p H := by
  unfold jsp87NzResCard
  have h := jsp87Xp0_ne_zero_card (K := K) hp hh hH
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  omega

/-- **THE NUMBER OF NONZERO CUBE SUMS IS AT MOST `p − 1`**, because the residue `0`
carries the zero value (`jsp87Xp0_eq_zero_zero`). -/
theorem jsp87NzResCard_le_p {K p H : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p) :
    jsp87NzResCard K p H ≤ p - 1 := by
  unfold jsp87NzResCard
  have hzero0 : jsp87Xp0 (jsp87BinV K) p 0 H = 0 := jsp87Xp0_eq_zero_zero (K := K) hp hh
  have hsub : (Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0) ⊆ Finset.Icc 1 (p - 1) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hne⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      have hz : jsp87Xp0 (jsp87BinV K) p n H = 0 := by rw [hn0]; exact hzero0
      exact hne hz
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, (Finset.mem_Icc.mp hnIcc).2⟩
  have h1 := Finset.card_le_card hsub
  rw [jsp87card_Icc] at h1
  omega

/-- **THE NUMBER OF NONZERO CUBE SUMS IS BETWEEN `2^K` AND `H · 2^K`.**
The lower bound is round 120's non-degeneracy; the upper bound is the union bound
over the `H` levels, each of which is active at exactly `2^K` residues. -/
theorem jsp87NzResCard_bounds {K p H : ℕ} (hp : 0 < p) (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + 2 ^ K - 1 < p) :
    2 ^ K ≤ jsp87NzResCard K p H ∧ jsp87NzResCard K p H ≤ H * 2 ^ K := by
  constructor
  · unfold jsp87NzResCard
    have hz : 1 + 2 ^ K - 1 = 2 ^ K := by rw [Nat.add_sub_cancel_left]
    have hh2 : 1 + 2 ^ K - 1 < p := by rw [hz]; omega
    have h := jsp87Xp0_ne_zero_card (K := K) hp hh2 hH
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    omega
  · have hsub : (Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)
      ⊆ Finset.biUnion (Finset.Icc 1 H)
        (fun h => (Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)) := by
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hne⟩
      rw [Finset.mem_biUnion]
      obtain ⟨h, hh', hact⟩ := jsp87Xp0_ne_zero_iff_active hK hH hne
      exact ⟨h, hh', Finset.mem_filter.mpr ⟨hnIcc, hact⟩⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (∑ h ∈ Finset.Icc 1 H,
          ((Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)).card)
        = H * 2 ^ K := by
      calc (∑ h ∈ Finset.Icc 1 H,
            ((Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)).card)
          = ∑ _h ∈ Finset.Icc 1 H, (2 ^ K : ℕ) := by
            refine Finset.sum_congr rfl fun h hhm => ?_
            have h1h : 1 ≤ h := (Finset.mem_Icc.mp hhm).1
            have hh2 : h + 2 ^ K - 1 < p := by
              have hle : h ≤ H := (Finset.mem_Icc.mp hhm).2
              have hstep : h + 2 ^ K - 1 ≤ H + 2 ^ K - 1 := by omega
              exact lt_of_le_of_lt hstep hh
            exact jsp87Active_res_card (K := K) (p := p) (h := h) h1h hp hh2
        _ = H * 2 ^ K := by
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul]
          rw [show ((Finset.Icc 1 H).card : ℕ) = H by rw [jsp87card_Icc]; omega]
          congr 1
    have h3 : ((Finset.Icc 1 H).biUnion
          (fun h => (Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n))).card
        ≤ ∑ h ∈ Finset.Icc 1 H,
          ((Finset.Icc 0 (p - 1)).filter (fun n => jsp87Active K p h n)).card :=
      Finset.card_biUnion_le
    have h4 : ((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card ≤ H * 2 ^ K :=
      le_trans h1 (le_trans h3 h2.le)
    unfold jsp87NzResCard
    exact h4

/-- **THE NUMBER OF ZERO CUBE SUMS IN ONE COMPLETE RESIDUE SYSTEM** is
`p − jsp87NzResCard K p H`. -/
theorem jsp87zeroRes_card_res {K p H : ℕ} (hp : 0 < p) :
    ((Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card = p - jsp87NzResCard K p H := by
  have h1 : ((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)).card
      + ((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card
      = (Finset.Icc 0 (p - 1)).card := by
    classical
    exact Finset.card_filter_add_card_filter_not
      (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)
  unfold jsp87NzResCard
  rw [jsp87card_Icc] at h1
  omega

/-! ## §3  The exact count along a progression -/

/-- **THE FIRST BLOCK OF A PROGRESSION CONTAINS EXACTLY `p − jsp87NzResCard`
ZEROS** — the discrete equidistribution statement that round 122 lacked. -/
theorem jsp87Prog_zero_card_base {K p H n0 D : ℕ} (hp : 0 < p) (hpc : p.Prime)
    (hD : ¬ p ∣ D) :
    ((Finset.Icc 0 (p - 1)).filter
      (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
        = p - jsp87NzResCard K p H := by
  have hmaps : Set.MapsTo (fun j : ℕ => (n0 + D * j) % p)
      ((Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0))
      ((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)) := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjz⟩
    show (n0 + D * j) % p ∈ (Finset.Icc 0 (p - 1)).filter
      (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
      have hlt : (n0 + D * j) % p < p := Nat.mod_lt _ hp
      omega
    · rw [← jsp87Xp0_eq_of_res (jsp87BinV K) (n := n0 + D * j) (r := (n0 + D * j) % p)
        ((Nat.mod_mod _ _).symm)]
      exact hjz
  have hinj : Set.InjOn (fun j : ℕ => (n0 + D * j) % p)
      ↑((Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)) := by
    intro a ha b hb heq
    rcases Finset.mem_filter.mp ha with ⟨haIcc, _⟩
    rcases Finset.mem_filter.mp hb with ⟨hbIcc, _⟩
    exact jsp87prog_res_inj hpc hD (Finset.mem_Icc.mp haIcc).2
      (Finset.mem_Icc.mp hbIcc).2 heq
  have hsurj : Set.SurjOn (fun j : ℕ => (n0 + D * j) % p)
      ((Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0))
      ((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)) := by
    rintro r hr
    rcases Finset.mem_filter.mp hr with ⟨hrIcc, hrz⟩
    have hlt : r < p := by
      have := (Finset.mem_Icc.mp hrIcc).2
      omega
    obtain ⟨j, hj, heq⟩ := jsp87Prog_res_surj (n0 := n0) (D := D) (r := r) hpc hD hlt
    refine ⟨j, ?_, ?_⟩
    · show j ∈ (Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
      · have h1 : (n0 + D * j) % p = ((n0 + D * j) % p) % p := (Nat.mod_mod _ _).symm
        rw [jsp87Xp0_eq_of_res (jsp87BinV K) h1, heq]
        exact hrz
    · exact heq
  rw [Finset.card_nbij (fun j : ℕ => (n0 + D * j) % p) hmaps hinj hsurj,
    jsp87zeroRes_card_res hp]

/-- **A BLOCK OF LENGTH `p` IS A TRANSLATE OF THE FIRST BLOCK.** -/
private theorem jsp87Prog_zero_card_Icc_shift {K p H n0 D a : ℕ} (hp : 0 < p) :
    ((Finset.Icc a (a + p - 1)).filter
      (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
      = ((Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H = 0)).card := by
  have hmaps : Set.MapsTo (fun j : ℕ => j - a)
      ((Finset.Icc a (a + p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0))
      ((Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H = 0)) := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjz⟩
    have hjle := (Finset.mem_Icc.mp hjIcc).2
    have hjge := (Finset.mem_Icc.mp hjIcc).1
    show (j - a) ∈ (Finset.Icc 0 (p - 1)).filter
      (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H = 0)
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    · have h1 : a + (j - a) = j := Nat.add_sub_of_le hjge
      rw [h1]
      exact hjz
  have hinj : Set.InjOn (fun j : ℕ => j - a)
      ↑((Finset.Icc a (a + p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)) := by
    intro x hx y hy heq
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, _⟩
    rcases Finset.mem_filter.mp hy with ⟨hyIcc, _⟩
    have h1 := (Finset.mem_Icc.mp hxIcc).1
    have h2 := (Finset.mem_Icc.mp hyIcc).1
    have h3 : x - a = y - a := heq
    omega
  have hsurj : Set.SurjOn (fun j : ℕ => j - a)
      ((Finset.Icc a (a + p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0))
      ((Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H = 0)) := by
    rintro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbIcc, hbz⟩
    have hble := (Finset.mem_Icc.mp hbIcc).2
    refine ⟨a + b, ?_, ?_⟩
    · show a + b ∈ (Finset.Icc a (a + p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · have hid : a + p - 1 = a + (p - 1) := by omega
        exact Finset.mem_Icc.mpr ⟨Nat.le_add_right a b,
          by rw [hid]; exact (Nat.add_le_add_left hble) a⟩
      · exact hbz
    · show a + b - a = b
      exact Nat.add_sub_cancel_left a b
  exact Finset.card_nbij (fun j : ℕ => j - a) hmaps hinj hsurj

/-- **A WHOLE `p`-BLOCK OF A PROGRESSION CONTAINS EXACTLY `p − jsp87NzResCard`
ZEROS** — the zeros of the cube sum along a progression, *for any position of the
block*.  By `jsp87Prog_block_bij` the `p` sample points of a block hit every
residue class of `p` exactly once, so the block carries precisely the
residue-system count. -/
theorem jsp87Prog_zero_card_block {K p H n0 D : ℕ} (hp : 0 < p) (hpc : p.Prime)
    (hD : ¬ p ∣ D) (a : ℕ) :
    ((Finset.Icc a (a + p - 1)).filter
      (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
        = p - jsp87NzResCard K p H := by
  rw [jsp87Prog_zero_card_Icc_shift (K := K) (p := p) (H := H) (n0 := n0) (D := D) (a := a) hp]
  have h := jsp87Prog_zero_card_base (K := K) (p := p) (H := H) (n0 := n0 + D * a) hp hpc hD
  have hset : (Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * a + D * j) H = 0)
      = (Finset.Icc 0 (p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * (a + j)) H = 0) := by
    ext j
    have heqa : n0 + D * (a + j) = n0 + D * a + D * j := by ring
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hj, hz⟩
      exact ⟨hj, by rw [heqa]; exact hz⟩
    · rintro ⟨hj, hz⟩
      exact ⟨hj, by rw [← heqa]; exact hz⟩
  rw [hset] at h
  exact h

/-- **THE EXACT COUNT OF ZEROS ALONG `c` WHOLE BLOCKS.**  For every `c ≥ 1`,
every `n₀` and every step `D` with `p ∤ D`, the progression hits the zero class of
`X_p` exactly `c (p − jsp87NzResCard K p H)` times. -/
theorem jsp87Prog_zero_card_blocks {K p H n0 D : ℕ} (hp : 0 < p) (hpc : p.Prime)
    (hD : ¬ p ∣ D) :
    ∀ c : ℕ, 1 ≤ c →
      ((Finset.Icc 0 (c * p - 1)).filter
        (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
          = c * (p - jsp87NzResCard K p H) := by
  intro c
  induction c with
  | zero =>
      intro hc
      omega
  | succ c ih =>
      intro hc
      by_cases hz : c = 0
      · subst hz
        have hle : Nat.succ 0 * p - 1 = p - 1 := by omega
        rw [hle]
        rw [jsp87Prog_zero_card_base (K := K) (p := p) (H := H) (n0 := n0) hp hpc hD]
        omega
      · have hcp : 1 ≤ c := by omega
        have hid : Nat.succ c * p - 1 = c * p + (p - 1) := by
          rw [Nat.succ_mul]
          omega
        have hcore : Finset.Icc 0 (c * p + (p - 1))
            = Finset.Icc 0 (c * p - 1) ∪ Finset.Icc (c * p) (c * p + (p - 1)) := by
          have hpos : 1 ≤ c * p := Nat.succ_le_iff.mpr (by positivity)
          rw [jsp87Icc_split (a := 0) (b := c * p - 1) (c := c * p + (p - 1)) (by omega)
            (by omega)]
          simp only [Nat.sub_add_cancel hpos]
        have hsplit : (Finset.Icc 0 (c * p + (p - 1))).filter
              (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)
            = ((Finset.Icc 0 (c * p - 1)).filter
                (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0))
              ∪ ((Finset.Icc (c * p) (c * p + (p - 1))).filter
                (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)) := by
          rw [← Finset.filter_union]
          exact congrArg (fun T : Finset ℕ =>
              T.filter (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)) hcore
        have hdisj : Disjoint
            ((Finset.Icc 0 (c * p - 1)).filter
              (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0))
            ((Finset.Icc (c * p) (c * p + (p - 1))).filter
              (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)) := by
          rw [Finset.disjoint_left]
          intro n hn hn'
          rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnz⟩
          have hnIcc' := Finset.mem_Icc.mp hnIcc
          have hle' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn').1).1
          have hnIcc'' := Finset.mem_Icc.mp hnIcc
          have hpos : 0 < c * p := by positivity
          have hlt : n < c * p := by omega
          exact absurd (Nat.lt_of_le_of_lt hle' hlt) (lt_irrefl _)
        have hid2 : c * p + p - 1 = c * p + (p - 1) := by omega
        have htail : ((Finset.Icc (c * p) (c * p + (p - 1))).filter
              (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
            = p - jsp87NzResCard K p H := by
          rw [← hid2]
          exact jsp87Prog_zero_card_block (K := K) (p := p) (H := H) (n0 := n0) (D := D)
            hp hpc hD (c * p)
        have h1 : ((Finset.Icc 0 (c * p + (p - 1))).filter
              (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
            = ((Finset.Icc 0 (c * p - 1)).filter
                (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card
              + ((Finset.Icc (c * p) (c * p + (p - 1))).filter
                (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card := by
          rw [hsplit, Finset.card_union_of_disjoint hdisj]
        have hid3 : (c + 1) * p - 1 = c * p + (p - 1) := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        rw [hid3, h1, ih hcp, htail]
        rw [Nat.add_mul, Nat.one_mul]

/-- **THE EXACT NONZERO FRACTION ALONG A WHOLE NUMBER OF BLOCKS.**  This is the
answer to item 1 of `policy.json` `next_round_attack[0]`:

```
jsp87NzFrac K p H (jsp87Prog n₀ D (c·p − 1))  =  jsp87NzResCard K p H / p
```

for every `c ≥ 1`, `n₀ ∈ ℕ` and `D` coprime to `p` — the nonzero fraction is
**independent of the sample length, of the starting point and of the step**. -/
theorem jsp87_nzFrac_prog_blocks {K p H n0 D c : ℕ} (hD : 0 < D) (hpc : p.Prime)
    (hDnd : ¬ p ∣ D) (hc : 1 ≤ c) (hh : H + 2 ^ K - 1 < p) :
    jsp87NzFrac K p H (jsp87Prog n0 D (c * p - 1))
      = ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
  have hp0 : 0 < p := hpc.pos
  have hcard : (jsp87Prog n0 D (c * p - 1)).card = c * p := by
    rw [jsp87Prog_card hD]
    exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (by positivity))
  have hz : (jsp87ZeroRes K p H (jsp87Prog n0 D (c * p - 1))).card
      = c * (p - jsp87NzResCard K p H) := by
    have h1 : (jsp87ZeroRes K p H (jsp87Prog n0 D (c * p - 1))).card
        = ((Finset.Icc 0 (c * p - 1)).filter
          (fun j => jsp87Xp0 (jsp87BinV K) p (n0 + D * j) H = 0)).card := by
      rw [jsp87ZeroRes, jsp87Prog, Finset.filter_image,
        Finset.card_image_iff.mpr (jsp87prog_injOn hD _)]
    rw [h1]
    exact jsp87Prog_zero_card_blocks hp0 hpc hDnd c hc
  have hn : (jsp87NzRes K p H (jsp87Prog n0 D (c * p - 1))).card
      = c * jsp87NzResCard K p H := by
    have h1 := jsp87card_nz_add_zero (K := K) (p := p) (H := H)
      (jsp87Prog n0 D (c * p - 1))
    rw [hcard, hz] at h1
    have hle : jsp87NzResCard K p H ≤ p := by
      have := jsp87NzResCard_le_p (K := K) hp0 hh
      omega
    calc (jsp87NzRes K p H (jsp87Prog n0 D (c * p - 1))).card
        = c * p - c * (p - jsp87NzResCard K p H) := by omega
      _ = c * (p - (p - jsp87NzResCard K p H)) := by
        rw [← Nat.mul_sub_left_distrib]
      _ = c * jsp87NzResCard K p H := by
        congr 1
        omega
  unfold jsp87NzFrac
  have hsc : ((c * p : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hn, hcard]
  field_simp
  push_cast
  ring

/-- **THE NONZERO FRACTION ALONG A PROGRESSION IS BOUNDED BY THE RESIDUE
DENSITIES.** -/
theorem jsp87_nzFrac_prog_blocks_bounds {K p H n0 D c : ℕ} (hD : 0 < D) (hpc : p.Prime)
    (hDnd : ¬ p ∣ D) (hK : 2 ^ K ≤ p) (hH : 1 ≤ H) (hh : H + 2 ^ K - 1 < p) (hc : 1 ≤ c) :
    (((2 : ℝ) ^ K) / (p : ℝ)) ≤ jsp87NzFrac K p H (jsp87Prog n0 D (c * p - 1))
      ∧ jsp87NzFrac K p H (jsp87Prog n0 D (c * p - 1))
        ≤ (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)) := by
  have h1 := jsp87_nzFrac_prog_blocks (K := K) (p := p) (H := H) (n0 := n0)
    hD hpc hDnd hc hh
  have h2 := jsp87NzResCard_bounds (K := K) hpc.pos hK hH hh
  constructor
  · rw [h1]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h2.1) (by positivity)
  · rw [h1]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h2.2) (by positivity)

/-- **THE NONZERO FRACTION ALONG A PROGRESSION IS NONDEGENERATE** — it lies
strictly between `0` and `1` on every whole number of blocks, for every step
coprime to `p`.  This is the positive counterpart of round 122's
`jsp87_5_21_prog_impossible`. -/
theorem jsp87_nzFrac_prog_blocks_pos {K p H n0 D c : ℕ} (hD : 0 < D) (hpc : p.Prime)
    (hDnd : ¬ p ∣ D) (hc : 1 ≤ c) (hH : 1 ≤ H) (hh : H + 2 ^ K - 1 < p) :
    0 < jsp87NzFrac K p H (jsp87Prog n0 D (c * p - 1))
      ∧ jsp87NzFrac K p H (jsp87Prog n0 D (c * p - 1)) < 1 := by
  have hhpos : 1 + 2 ^ K - 1 < p := by omega
  have h1 := jsp87_nzFrac_prog_blocks (K := K) (p := p) (H := H) (n0 := n0)
    hD hpc hDnd hc hh
  rw [h1]
  have hpos := jsp87NzResCard_pos (K := K) hpc.pos hH hhpos
  have hle := jsp87NzResCard_le_p (K := K) hpc.pos hh
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpc.pos
  have hp1 : 1 ≤ p := by omega
  have hlt : ((jsp87NzResCard K p H : ℕ) : ℝ) < p := by
    have h2 : jsp87NzResCard K p H < p := by omega
    exact_mod_cast h2
  constructor
  · positivity
  · exact (div_lt_one hp0).2 hlt

/-! ## §4  The canonical whole-block sample -/

/-- **THE PRODUCT OF THE PRIMES OF `S₁`** — the modulus that makes the sample of
§4 a whole number of `p`-blocks for every `p ∈ P` at once. -/
def jsp87Prod (P : Finset ℕ) : ℕ := ∏ q ∈ P, (q : ℕ)

/-- **THE CANONICAL STRUCTURED SAMPLE** of `policy.json` `next_round_attack[0]`
item 1: the progression `n₀ + D j` for `j < ∏_{p ∈ P} p`, i.e. a whole number of
`p`-blocks for **every** prime of `P` at once. -/
def jsp87ProgFull (n0 D : ℕ) (P : Finset ℕ) : Finset ℕ := jsp87Prog n0 D (jsp87Prod P - 1)

/-- **THE CANONICAL SAMPLE HAS `∏ P` POINTS.** -/
theorem jsp87ProgFull_card {n0 D : ℕ} (hD : 0 < D) (P : Finset ℕ)
    (hpos : 0 < jsp87Prod P) :
    (jsp87ProgFull n0 D P).card = jsp87Prod P := by
  rw [jsp87ProgFull, jsp87Prog_card hD]
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)

/-- **THE CANONICAL SAMPLE IS NONEMPTY.** -/
theorem jsp87ProgFull_nonempty {n0 D : ℕ} (P : Finset ℕ) : (jsp87ProgFull n0 D P).Nonempty :=
  ⟨n0, jsp87Prog_mem_iff.mpr ⟨0, Nat.zero_le _, rfl⟩⟩

/-- **EVERY PRIME OF `P` DIVIDES `∏ P`.** -/
private theorem jsp87dvd_prod_mem {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) : p ∣ jsp87Prod P := by
  obtain ⟨c, hc⟩ := (Finset.dvd_prod_of_mem (f := id) (s := P) (a := p) hp)
  refine ⟨c, ?_⟩
  unfold jsp87Prod
  simpa only [id_eq] using hc

/-- **A PRIME OF `P` IS AT MOST `∏ P`** (given `P` nonempty). -/
private theorem jsp87le_prod {P : Finset ℕ} (hpos : 0 < jsp87Prod P) {p : ℕ} (hp : p ∈ P)
    (_hpc : p.Prime) : p ≤ jsp87Prod P := by
  obtain ⟨c, hc⟩ := jsp87dvd_prod_mem (P := P) hp
  rcases Nat.eq_zero_or_pos c with hcz | hcpos
  · rw [hcz, Nat.mul_zero] at hc
    exact absurd hc (Nat.ne_of_gt hpos)
  · rw [hc]
    calc p = p * 1 := by ring
      _ ≤ p * c := Nat.mul_le_mul (Nat.le_refl p) hcpos

/-- **THE NONZERO FRACTION ON THE CANONICAL SAMPLE.**  Item 1(a) of `policy.json`
`next_round_attack[0]`, computed:

```
jsp87NzFrac K p H (jsp87ProgFull n₀ D P)  =  jsp87NzResCard K p H / p
```

for every prime `p ∈ P` that does not divide the step `D`. -/
theorem jsp87ProgFull_nzFrac {K p H n0 D : ℕ} {P : Finset ℕ} (hD : 0 < D)
    (hpos : 0 < jsp87Prod P) (hp : p ∈ P) (hpc : p.Prime) (hDnd : ¬ p ∣ D)
    (hh : H + 2 ^ K - 1 < p) :
    jsp87NzFrac K p H (jsp87ProgFull n0 D P)
      = ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
  have hle : p ≤ jsp87Prod P := jsp87le_prod hpos hp hpc
  obtain ⟨c, hc⟩ := jsp87dvd_prod_mem (P := P) hp
  have hcpos : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with hcz | hcpos'
    · rw [hcz, Nat.mul_zero] at hc
      exact absurd hc (Nat.ne_of_gt hpos)
    · omega
  have h1 : jsp87Prod P - 1 = c * p - 1 := by rw [hc, Nat.mul_comm]
  rw [jsp87ProgFull, h1]
  exact jsp87_nzFrac_prog_blocks (K := K) hD hpc hDnd hcpos hh

/-- **THE TWO-CLASS HYPOTHESIS HOLDS ON THE CANONICAL SAMPLE**: for every `p ∈ P`
there is a sample point divisible by `p`, and a sample point active at level `1`.
This is the `hne` hypothesis of `jsp87_endgame_frac_of_5_21`, supplied
*unconditionally* for the structured sample. -/
theorem jsp87ProgFull_hne {K p H n0 D : ℕ} {P : Finset ℕ} (_hD : 0 < D)
    (hpos : 0 < jsp87Prod P) (hp : p ∈ P) (hpc : p.Prime) (hDnd : ¬ p ∣ D)
    (hH : 1 ≤ H) (hh : H + 2 ^ K - 1 < p) :
    (∃ n ∈ jsp87ProgFull n0 D P, p ∣ n) ∧ (∃ n ∈ jsp87ProgFull n0 D P, jsp87Active K p 1 n) := by
  have hle : p ≤ jsp87Prod P := jsp87le_prod hpos hp hpc
  have hmem : ∀ j < p, n0 + D * j ∈ jsp87ProgFull n0 D P := by
    intro j hj
    rw [jsp87ProgFull, jsp87Prog_mem_iff]
    refine ⟨j, ?_, rfl⟩
    have h1 : 0 < jsp87Prod P := hpos
    omega
  obtain ⟨j, hj, heq⟩ := jsp87Prog_res_surj (n0 := n0) (D := D) (r := 0) hpc hDnd
    hpc.pos
  refine ⟨⟨n0 + D * j, hmem j hj, ?_⟩, ?_⟩
  · rw [Nat.dvd_iff_mod_eq_zero]
    exact heq
  · obtain ⟨r, hr⟩ := jsp87ActiveRes_nonempty (K := K) (p := p) (h := 1) (by omega)
    have hh1 : 1 + 2 ^ K - 1 < p := by omega
    have hrIcc' : r ∈ Finset.Icc 0 (p - 1) :=
      jsp87ActiveRes_subset (K := K) (p := p) (h := 1) (by norm_num) hh1 hr
    have hrIcc : r ≤ p - 1 := (Finset.mem_Icc.mp hrIcc').2
    obtain ⟨j', hj', heq'⟩ := jsp87Prog_res_surj (n0 := n0) (D := D) (r := r) hpc hDnd
      (by omega)
    refine ⟨n0 + D * j', hmem j' hj', ?_⟩
    have h1 : jsp87Active K p 1 (n0 + D * j') ↔ jsp87Active K p 1 r := by
      apply jsp87Active_iff_of_mod
      have hmod : (n0 + D * j') % p = r % p := by
        calc (n0 + D * j') % p = r := heq'
          _ = r % p := (Nat.mod_eq_of_lt (by omega)).symm
      exact hmod
    have hract : jsp87Active K p 1 r := (jsp87Active_iff_activeRes (K := K) (h := 1)
      (by norm_num) hpc.pos hrIcc hh1).mpr hr
    exact h1.mpr hract

/-! ## §5  Candidate (b): the sieve sample is worth nothing -/

/-- **THE SIEVE SAMPLE**: the sample points up to `N` divisible by `p`.  Candidate
(b) of `policy.json` `next_round_attack[0]`. -/
def jsp87SieveSample (p N : ℕ) : Finset ℕ := (Finset.Icc 0 N).filter (fun n => p ∣ n)

attribute [reducible] jsp87SieveSample

/-- **A SAMPLE SUPPORTED ON THE MULTIPLES OF `p` HAS NONZERO FRACTION ZERO** —
`jsp87Xp0_eq_zero_of_dvd` says the cube sum vanishes on the whole class
`n ≡ 0 (mod p)`. -/
theorem jsp87_nzFrac_zero_of_dvdSample {K p H : ℕ} {s : Finset ℕ} (_hs : s.Nonempty)
    (hd : ∀ n ∈ s, p ∣ n) (hp : 0 < p) (hh : H + 2 ^ K - 1 < p) :
    jsp87NzFrac K p H s = 0 := by
  have hsub : jsp87NzRes K p H s = ∅ := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnmem, hne⟩
      exact (hne (jsp87Xp0_eq_zero_of_dvd (K := K) hp hh (hd _ hnmem))).elim
    · intro h
      exact absurd h (by simp)
  unfold jsp87NzFrac
  rw [hsub]
  simp

/-- **THE SIEVE SAMPLE HAS NONZERO FRACTION ZERO — CANDIDATE (b) IS DEAD.** -/
theorem jsp87_nzFrac_sieve_zero {K p H N : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p) :
    jsp87NzFrac K p H (jsp87SieveSample p N) = 0 := by
  refine jsp87_nzFrac_zero_of_dvdSample (K := K) (p := p) (H := H)
    (s := jsp87SieveSample p N) ?_ ?_ hp hh
  · refine ⟨0, ?_⟩
    rw [jsp87SieveSample, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩, Nat.dvd_zero p⟩
  · intro n hn
    rw [jsp87SieveSample, Finset.mem_filter] at hn
    exact hn.2

/-- **A FUNCTION VANISHING ON THE SAMPLE ITSELF HAS ZERO VARIANCE.**  This is
`jsp87Var_zero_of_zero` (`Xp.lean` §4) with the hypothesis weakened from "vanishes
everywhere" to "vanishes on the sample" — the sample-local version, which is what
§5 needs. -/
private theorem jsp87Var_zero_of_zeroOn {Ω : Type*} (s : Finset Ω) (f : Ω → ℝ)
    (hf : ∀ i ∈ s, f i = 0) : jsp87Var s f = 0 := by
  have hμ : jsp87FAvg s f = 0 := by
    unfold jsp87FAvg
    rw [Finset.sum_eq_zero fun i hi => hf i hi, zero_div]
  have hg : jsp87FAvg s (fun i => (f i - jsp87FAvg s f) ^ 2) = 0 := by
    rw [hμ]
    unfold jsp87FAvg
    rw [Finset.sum_eq_zero fun i hi => by rw [hf i hi]; norm_num, zero_div]
  unfold jsp87Var
  rw [hg]

/-- **THE SIEVE SAMPLE CONTRIBUTES EXACTLY NOTHING TO (5.21).**  Its variance term is
literally zero, so no endgame can be fired with it in place of a residue-spread
sample. -/
theorem jsp87Var_sieve_zero {K p H N : ℕ} (hp : 0 < p) (hh : H + 2 ^ K - 1 < p)
    (q : ℝ) :
    jsp87Var (jsp87SieveSample p N) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) = 0 := by
  refine jsp87Var_zero_of_zeroOn (jsp87SieveSample p N)
    (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) ?_
  intro i hi
  have hi' : i ∈ (Finset.Icc 0 N).filter (fun n => p ∣ n) := hi
  rcases Finset.mem_filter.mp hi' with ⟨_, hdv⟩
  show q * jsp87Xp0 (jsp87BinV K) p i H = 0
  rw [jsp87Xp0_eq_zero_of_dvd (K := K) hp hh hdv, mul_zero]

/-- **AND (5.21′) CANNOT BE SUPPLIED BY A SAMPLE SUPPORTED ON THE MULTIPLES OF
EVERY PRIME OF `S₁`.** -/
theorem jsp87_5_21_sieve_impossible {K : ℕ} {P : Finset ℕ} (q : ℝ) (H : ℕ) (N : ℕ)
    (hpmem : ∀ p ∈ P, 0 < p) (hh : ∀ p ∈ P, H + 2 ^ K - 1 < p) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H (jsp87SieveSample p N)
            * (1 - jsp87NzFrac K p H (jsp87SieveSample p N)))) := by
  intro h
  have hzero : ∀ p ∈ P, jsp87NzFrac K p H (jsp87SieveSample p N)
      * (1 - jsp87NzFrac K p H (jsp87SieveSample p N)) = 0 := by
    intro p hp
    have h1 := jsp87_nzFrac_sieve_zero (K := K) (p := p) (H := H) (N := N) (hpmem p hp) (hh p hp)
    rw [h1]
    ring
  have hsum0 : ∑ p ∈ P, (jsp87NzFrac K p H (jsp87SieveSample p N)
      * (1 - jsp87NzFrac K p H (jsp87SieveSample p N))) = 0 :=
    Finset.sum_eq_zero fun p hp => hzero p hp
  rw [hsum0] at h
  have hz0 : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * (0 : ℝ) = 0 := by ring
  rw [hz0] at h
  exact absurd h (by norm_num)

/-- **A SAMPLE IN ONE COMMON RESIDUE CLASS IS DEAD FOR EVERY PRIME OF `S₁`** — the
general form of §5, for any residue `r`, including `r = 0` (the sieve sample). -/
theorem jsp87_5_21_singleRes_any {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (r : ℕ) (hres : ∀ p ∈ P, ∀ n ∈ s, n % p = r % p) (q : ℝ) (H : ℕ) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :=
  jsp87_5_21_singleResP_impossible (K := K) (P := P) s hs
    (fun p hp => ⟨r, hres p hp⟩) q H

/-! ## §6  The endgame on the canonical sample -/

/-- **THE EXPLICIT ARITHMETIC CONDITION (5.21b)** produced by the canonical sample:
with `c_p = jsp87NzResCard K p H` the number of nonzero cube sums in a complete
residue system,

```
(5.21b)   1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ P} (c_p / p) (1 − c_p / p) .
```

This is (5.21′) *evaluated*: the sample geometry replaced by the residue
arithmetic. -/
def jsp87R521b (K : ℕ) (P : Finset ℕ) (q : ℝ) (H : ℕ) : Prop :=
  (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
    * ∑ p ∈ P, (((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
        * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)))

/-- **(5.21′) AND (5.21b) ARE EQUIVALENT FOR THE CANONICAL SAMPLE.** -/
theorem jsp87_5_21_progFull_iff {K : ℕ} {P : Finset ℕ} (n0 D : ℕ) (hD : 0 < D)
    (_hP : P.Nonempty) (hpc : ∀ p ∈ P, p.Prime) (hDp : ∀ p ∈ P, ¬ p ∣ D)
    (q : ℝ) (H : ℕ) (hh : ∀ p ∈ P, H + 2 ^ K - 1 < p) :
    ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H (jsp87ProgFull n0 D P)
            * (1 - jsp87NzFrac K p H (jsp87ProgFull n0 D P))))
      ↔ jsp87R521b K P q H := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hfr : ∀ p ∈ P, jsp87NzFrac K p H (jsp87ProgFull n0 D P)
      = ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
    intro p hp
    exact jsp87ProgFull_nzFrac (K := K) (p := p) (H := H) hD hpos hp (hpc p hp) (hDp p hp)
      (hh p hp)
  have hmul : ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2))
      * ∑ p ∈ P, (((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
          * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)))
      = ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2))
        * ∑ p ∈ P, (jsp87NzFrac K p H (jsp87ProgFull n0 D P)
            * (1 - jsp87NzFrac K p H (jsp87ProgFull n0 D P))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp' => by rw [hfr p hp']
  constructor
  · intro h
    unfold jsp87R521b
    exact h.trans hmul.ge
  · intro h
    exact h.trans hmul.le

/-- **THE ENDGAME ON THE CANONICAL SAMPLE.**  Everything of arXiv:2512.01739
§5.3–§5.14 — (5.15), (5.16)–(5.17), (5.19), the separation hypothesis and the
two-class hypothesis — is discharged for the explicit progression sample
`jsp87ProgFull n₀ D P`, with the single arithmetic input **(5.21b)**.  Hence the
`S₁`-variance hypothesis (5.21) of the published proof is **replaced by a
statement about the prime set alone**. -/
theorem jsp87_endgame_progFull {K : ℕ} {P : Finset ℕ} (n0 D : ℕ) (hD : 0 < D)
    (hP : P.Nonempty) (q : ℝ) (H : ℕ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hH : 1 ≤ H) (hpc : ∀ p ∈ P, p.Prime) (hDp : ∀ p ∈ P, ¬ p ∣ D)
    (hh : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (H15 : ‖jsp87CAvg (jsp87ProgFull n0 D P) (fun i => jsp87e (q * ∑ p' ∈ P,
          jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg (jsp87ProgFull n0 D P) (fun i => jsp87e (q * ∑ p' ∈ P,
          jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ P, jsp87CAvg (jsp87ProgFull n0 D P) (fun i =>
          jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5)
    (h521 : jsp87R521b K P q H) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hne : ∀ p ∈ P, (∃ n ∈ jsp87ProgFull n0 D P, p ∣ n)
      ∧ (∃ n ∈ jsp87ProgFull n0 D P, jsp87Active K p 1 n) := by
    intro p hp
    exact jsp87ProgFull_hne (K := K) (p := p) (H := H) hD hpos hp (hpc p hp) (hDp p hp)
      hH (hh p hp)
  have hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * ∑ p ∈ P, (jsp87NzFrac K p H (jsp87ProgFull n0 D P)
          * (1 - jsp87NzFrac K p H (jsp87ProgFull n0 D P))) :=
    (jsp87_5_21_progFull_iff (K := K) (n0 := n0) (D := D) hD hP hpc hDp q H hh).mpr h521
  exact jsp87_endgame_frac_of_5_21 (K := K) (P := P) (jsp87ProgFull n0 D P)
    (jsp87ProgFull_nonempty (n0 := n0) (D := D) P) q H κ1 κ2 κ3 κ4 κ5 hK hH hh hne H15
      H1617 hfrac

/-! ## §6.2  What (5.21b) needs from the prime set -/

/-- **SUBTRACTION LEMMAS FOR `ℝ`, STATED EXPLICITLY.**  This Mathlib tree's
`linarith` does not see through the `HSub` instance of `ℝ`, so goals of the form
`1 − x ≤ 1 − y` are discharged here once and for all. -/
private theorem jsp87sub_le_sub_one {x y : ℝ} (h : y ≤ x) : 1 - x ≤ 1 - y :=
  sub_le_sub (le_refl (1 : ℝ)) h

private theorem jsp87zero_le_sub_one {x : ℝ} (h : x ≤ 1) : 0 ≤ 1 - x := sub_nonneg.mpr h

private theorem jsp87sub_le_one {x : ℝ} (h0 : 0 ≤ x) (_h1 : x ≤ 1) : 1 - x ≤ 1 := by
  linarith

/-- **THE FRACTION PRODUCT IS AT MOST THE FRACTION** (`f (1 − f) ≤ f` for
`f ∈ [0,1]`). -/
theorem jsp87NzFrac_mul_le {K p H : ℕ} {s : Finset ℕ} (hs : s.Nonempty) :
    jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) ≤ jsp87NzFrac K p H s := by
  have h0 := jsp87NzFrac_nonneg (K := K) (p := p) (H := H) s
  have h1 := jsp87NzFrac_le_one (K := K) (p := p) (H := H) hs
  have h2 := (jsp87NzFrac_mul_one_sub (K := K) (p := p) (H := H) hs).2
  nlinarith [sq_nonneg (jsp87NzFrac K p H s)]

/-- **EACH SUMMAND OF (5.21b) IS BOUNDED BY `H · 2^K / p`**: the fraction is at
most `c_p / p` and the complement at most `1`. -/
theorem jsp87_5_21b_summand_le {K p H : ℕ} (hK : 2 ^ K ≤ p) (hpc : p.Prime)
    (hh : H + 2 ^ K - 1 < p) (hH : 1 ≤ H) :
    ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
        * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
      ≤ (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)) := by
  have h2 := jsp87NzResCard_bounds (K := K) hpc.pos hK hH hh
  have hb := jsp87NzResCard_le_p (K := K) hpc.pos hh
  have hcp : jsp87NzResCard K p H ≤ p := by omega
  have hc2 : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcp
  have hA0 : (0 : ℝ) ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by positivity
  have hfc : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) ≤ ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ) := by
    refine div_le_div_of_nonneg_right (by exact_mod_cast h2.2) (by positivity)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpc.pos
  have h1 : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hp0).2 hc2
  have hB : 1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) ≤ 1 := by linarith
  have hB0 : 0 ≤ 1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) :=
    jsp87zero_le_sub_one h1
  have hmul := mul_le_mul_of_nonneg_left hB
    (by positivity : (0 : ℝ) ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
  calc ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
        * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
      ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) * 1 := hmul
      _ ≤ (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)) := by rw [mul_one]; exact hfc

/-- **THE CUBE SQUARE TIMES `H · 2^K` IS THE INVERSE OF `4^{H+K}`.** -/
private theorem jsp87quarter_half (h : ℝ) (m K : ℕ) :
    (((1 / 2 : ℝ) ^ m) ^ 2) * (h * (2 : ℝ) ^ K) = ((4 : ℝ) ^ m)⁻¹ * (h * (2 : ℝ) ^ K) := by
  have hcore : ((1 / 2 : ℝ) ^ m) ^ 2 = ((4 : ℝ) ^ m)⁻¹ := by
    have hq2 : (1 / 2 : ℝ) ^ 2 = (1 / 4 : ℝ) := by norm_num
    have hq4 : (1 / 4 : ℝ) = ((4 : ℝ) : ℝ)⁻¹ := by norm_num
    calc ((1 / 2 : ℝ) ^ m) ^ 2 = (1 / 2 : ℝ) ^ (2 * m) := by rw [← pow_mul, Nat.mul_comm]
      _ = ((1 / 2 : ℝ) ^ 2) ^ m := by rw [← pow_mul]
      _ = (1 / 4 : ℝ) ^ m := by rw [hq2]
      _ = ((4 : ℝ) ^ m)⁻¹ := by rw [hq4, inv_pow]
  rw [hcore]

/-- **THE RECIPROCAL-SUM NECESSITY.**  If the canonical sample discharges hypothesis
(5.21) of the endgame, then the prime set `S₁` has harmonic mass

```
∑_{p ∈ S₁} 1/p  ≥  2^{2H+K} / (H q²) .
```

This is a statement about the *set of primes alone* — no sample, no cube, no
variance — and it is the exact arithmetic content that the endgame needs from
`S₁`.  Item 2 of `policy.json` `next_round_attack[0]`. -/
theorem jsp87_5_21_needs_recipSum {K : ℕ} {P : Finset ℕ} (_n0 _D : ℕ) (_hD : 0 < D)
    (q : ℝ) (H : ℕ) (_hP : P.Nonempty) (hpc : ∀ p ∈ P, p.Prime) (_hDp : ∀ p ∈ P, ¬ p ∣ D)
    (hK : ∀ p ∈ P, 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (h521 : jsp87R521b K P q H) :
    ((2 : ℝ) ^ (2 * H + K)) ≤ (q ^ 2) * ((H : ℕ) : ℝ) * ∑ p ∈ P, (1 / (p : ℝ)) := by
  have hstep : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * ∑ p ∈ P, (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)) := by
    refine le_trans h521 (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Finset.sum_le_sum fun p hp => ?_
    exact jsp87_5_21b_summand_le (hK p hp) (hpc p hp) (hh p hp) hH
  have hident : (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * ∑ p ∈ P, (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ))
      = ((4 : ℝ) ^ (H + K))⁻¹ * (((H : ℝ) * (2 : ℝ) ^ K))
          * ∑ p ∈ P, (1 / (p : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hq2 : (1 / 2 : ℝ) ^ 2 = (1 / 4 : ℝ) := by norm_num
    have hq4 : (1 / 4 : ℝ) = ((4 : ℝ) : ℝ)⁻¹ := by norm_num
    have h1 : ((1 / 2 : ℝ) ^ (H + K)) ^ 2 = (1 / 4 : ℝ) ^ (H + K) := by
      calc ((1 / 2 : ℝ) ^ (H + K)) ^ 2 = (1 / 2 : ℝ) ^ (2 * (H + K)) := by
            rw [← pow_mul, Nat.mul_comm]
        _ = ((1 / 2 : ℝ) ^ 2) ^ (H + K) := by rw [← pow_mul]
        _ = (1 / 4 : ℝ) ^ (H + K) := by rw [hq2]
    calc (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ))
        = (1 / 4 : ℝ) ^ (H + K) * ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ) := by
          rw [h1]
          ring
      _ = ((4 : ℝ) ^ (H + K))⁻¹ * ((H : ℝ) * (2 : ℝ) ^ K) * (1 / (p : ℝ)) := by
          rw [hq4, inv_pow]
          field_simp
  have hstep' : (1 : ℝ) ≤ (q ^ 2) * ((4 : ℝ) ^ (H + K))⁻¹ * ((H : ℝ) * (2 : ℝ) ^ K)
      * ∑ p ∈ P, (1 / (p : ℝ)) := by
    calc (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)) := hstep
      _ = (q ^ 2) * ((((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ))) := by ring
      _ = (q ^ 2) * ((4 : ℝ) ^ (H + K))⁻¹ * ((H : ℝ) * (2 : ℝ) ^ K)
        * ∑ p ∈ P, (1 / (p : ℝ)) := by rw [hident]; ring
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ (H + K) := by positivity
  have hA : (4 : ℝ) ^ (H + K) ≤ (q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K)
      * ∑ p ∈ P, (1 / (p : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hstep' (h4pos.le)
    have hinv : ((4 : ℝ) ^ (H + K))⁻¹ * (4 : ℝ) ^ (H + K) = 1 :=
      inv_mul_cancel₀ (ne_of_gt h4pos)
    calc (4 : ℝ) ^ (H + K) = (1 : ℝ) * (4 : ℝ) ^ (H + K) := by ring
      _ ≤ ((q ^ 2) * ((4 : ℝ) ^ (H + K))⁻¹ * ((H : ℝ) * (2 : ℝ) ^ K)
        * ∑ p ∈ P, (1 / (p : ℝ))) * (4 : ℝ) ^ (H + K) := hmul
      _ = (q ^ 2) * (((4 : ℝ) ^ (H + K))⁻¹ * (4 : ℝ) ^ (H + K))
        * ((H : ℝ) * (2 : ℝ) ^ K) * ∑ p ∈ P, (1 / (p : ℝ)) := by ring
      _ = (q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K) * ∑ p ∈ P, (1 / (p : ℝ)) := by
        rw [hinv]
        ring
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hB : (4 : ℝ) ^ (H + K) / (2 : ℝ) ^ K
      ≤ (q ^ 2) * ((H : ℕ) : ℝ) * ∑ p ∈ P, (1 / (p : ℝ)) := by
    refine (div_le_iff₀ h2pos).2 ?_
    have h1a : (q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K) * ∑ x ∈ P, (1 / (x : ℝ))
        = ∑ x ∈ P, ((q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K) * (1 / (x : ℝ))) := by
      rw [Finset.mul_sum]
    have h1b : (∑ x ∈ P, ((q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K) * (1 / (x : ℝ))))
        = ∑ x ∈ P, ((q ^ 2) * ((H : ℕ) : ℝ) * ((1 / (x : ℝ)) * (2 : ℝ) ^ K)) :=
      Finset.sum_congr rfl fun x _ => by ring
    have h1c : (∑ x ∈ P, ((q ^ 2) * ((H : ℕ) : ℝ) * ((1 / (x : ℝ)) * (2 : ℝ) ^ K)))
        = (q ^ 2) * ((H : ℕ) : ℝ) * ∑ x ∈ P, ((1 / (x : ℝ)) * (2 : ℝ) ^ K) := by
      rw [Finset.mul_sum]
    have h1 : (q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K) * ∑ p ∈ P, (1 / (p : ℝ))
        = (q ^ 2) * ((H : ℕ) : ℝ) * ∑ p ∈ P, (1 / (p : ℝ)) * (2 : ℝ) ^ K :=
      h1a.trans (h1b.trans h1c)
    calc (4 : ℝ) ^ (H + K) ≤ (q ^ 2) * ((H : ℝ) * (2 : ℝ) ^ K)
        * ∑ p ∈ P, (1 / (p : ℝ)) := hA
      _ = (q ^ 2) * ((H : ℕ) : ℝ) * ∑ p ∈ P, (1 / (p : ℝ)) * (2 : ℝ) ^ K := h1
      _ = ((q ^ 2) * ((H : ℕ) : ℝ) * ∑ p ∈ P, (1 / (p : ℝ))) * (2 : ℝ) ^ K := by
        have hsum : (∑ p ∈ P, ((1 / (p : ℝ)) * (2 : ℝ) ^ K))
            = (∑ p ∈ P, (1 / (p : ℝ))) * (2 : ℝ) ^ K := by
          rw [Finset.sum_mul]
        rw [hsum]
        ring
  have hp2 : (4 : ℝ) ^ (H + K) = ((2 : ℝ) ^ 2) ^ (H + K) := by norm_num
  have hid : (2 : ℝ) ^ (2 * H + K) = (4 : ℝ) ^ (H + K) / (2 : ℝ) ^ K := by
    have h2ne : ((2 : ℝ) ^ K) ≠ 0 := by positivity
    rw [eq_div_iff h2ne]
    rw [← pow_add, hp2, ← pow_mul]
    congr 1
    ring
  exact hid.le.trans hB

/-- **THE RECIPROCAL-SUM SUFFICIENCY.**  Conversely, an explicit condition on the
prime set alone suffices for (5.21b), and hence for the endgame: if every `p ∈ S₁`
satisfies `p ≥ H·2^K` (so the two-class fraction product is bounded below by
`(2^K/p)(1 − H 2^K/p)`) and

```
q² 2^{−2(H+K)} ∑_{p ∈ S₁} (2^K / p) (1 − H 2^K / p)  ≥  1 ,
```

then (5.21′) *holds* for the canonical progression sample and
`jsp87_endgame_progFull` fires. -/
theorem jsp87_5_21_prog_of_recipSum {K : ℕ} {P : Finset ℕ} (_n0 _D : ℕ) (_hD : 0 < D)
    (q : ℝ) (H : ℕ) (_hP : P.Nonempty) (hpc : ∀ p ∈ P, p.Prime) (_hDp : ∀ p ∈ P, ¬ p ∣ D)
    (hH : 1 ≤ H) (hh : ∀ p ∈ P, H + 2 ^ K - 1 < p) (hpH : ∀ p ∈ P, H * 2 ^ K ≤ p)
    (hrec : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (((2 : ℝ) ^ K) / (p : ℝ)
            * (1 - ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)))) :
    jsp87R521b K P q H := by
  have hper : ∀ p ∈ P, 2 ^ K ≤ p := by
    intro p hp
    have h1 : 2 ^ K ≤ H * 2 ^ K := by
      have h2 := Nat.mul_le_mul (Nat.le_refl (2 ^ K)) hH
      rw [Nat.mul_comm, Nat.one_mul] at h2
      exact le_trans h2 (by rw [Nat.mul_comm])
    exact le_trans h1 (hpH p hp)
  unfold jsp87R521b
  refine le_trans hrec (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Finset.sum_le_sum fun p hp => ?_
  have h2 := jsp87NzResCard_bounds (K := K) (hpc p hp).pos (hper p hp) hH (hh p hp)
  have hb := jsp87NzResCard_le_p (K := K) (hpc p hp).pos (hh p hp)
  have hcp : jsp87NzResCard K p H ≤ p := by omega
  have hc2 : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcp
  have hA : ((2 : ℝ) ^ K) / (p : ℝ)
      ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
    refine div_le_div_of_nonneg_right (by exact_mod_cast h2.1) (by positivity)
  have hB : 1 - ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)
      ≤ 1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
    have h3 : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
        ≤ ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ) := by
      have h1 : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ ((H : ℝ) * (2 : ℝ) ^ K) := by
        exact_mod_cast h2.2
      exact div_le_div_of_nonneg_right h1 (by positivity)
    exact jsp87sub_le_sub_one h3
  have hA0 : 0 ≤ ((2 : ℝ) ^ K) / (p : ℝ) := by positivity
  have h1 : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) ≤ 1 :=
    (div_le_one (by exact_mod_cast (hpc p hp).pos)).2 hc2
  have hB0 : 0 ≤ 1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) :=
    jsp87zero_le_sub_one h1
  calc ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
        * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
      ≥ ((2 : ℝ) ^ K) / (p : ℝ)
          * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hA hB0
    _ ≥ ((2 : ℝ) ^ K) / (p : ℝ) * (1 - ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hB hA0

/-- **THE SUMMARY OF ROUND 123.**  On the canonical progression sample
`jsp87ProgFull n₀ D P`:

1. the nonzero fraction is **computed exactly**, prime by prime, as
   `jsp87NzResCard K p H / p` (`jsp87ProgFull_nzFrac`), independently of `n₀`, of
   the step `D` (as long as `p ∤ D`), and of the sample length;
2. the two-class hypothesis holds **unconditionally** (`jsp87ProgFull_hne`);
3. the endgame of arXiv:2512.01739 fires from the **prime-set condition (5.21b)**
   (`jsp87_endgame_progFull`), which is *equivalent* to (5.21′) on this sample
   (`jsp87_5_21_progFull_iff`);
4. (5.21b) is **necessary** for `∑_{p ∈ S₁} 1/p ≥ 2^{2H+K}/(H q²)`
   (`jsp87_5_21_needs_recipSum`) and **sufficient**, under `p ≥ H·2^K`, for the
   explicit reciprocal sum `q² 2^{−2(H+K)} ∑ (2^K/p)(1 − H 2^K/p) ≥ 1`
   (`jsp87_5_21_prog_of_recipSum`);
5. the sieve sample is **worthless** — zero nonzero fraction and zero variance
   (`jsp87_nzFrac_sieve_zero`, `jsp87Var_sieve_zero`).

Together with round 122, the `S₁`-variance hypothesis (5.21) of the published proof
is now completely characterised: it is impossible for uniform samples (round 120)
and for any progression whose step is divisible by `S₁` (round 122), impossible
for the sieve sample (§5 here), and *equivalent* to a statement about the harmonic
mass of `S₁` for a progression coprime to `S₁` (§6 here). -/
theorem jsp87_prog_summary {K : ℕ} {P : Finset ℕ} (n0 D : ℕ) (hD : 0 < D)
    (q : ℝ) (H : ℕ) (_hP : P.Nonempty) (hpc : ∀ p ∈ P, p.Prime) (_hDp : ∀ p ∈ P, ¬ p ∣ D)
    (hH : 1 ≤ H) (hh : ∀ p ∈ P, H + 2 ^ K - 1 < p) (hpH : ∀ p ∈ P, H * 2 ^ K ≤ p)
    (hrec : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (((2 : ℝ) ^ K) / (p : ℝ)
            * (1 - ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)))) :
    jsp87R521b K P q H ∧
      (∀ p ∈ P, jsp87NzFrac K p H (jsp87ProgFull n0 D P)
          = ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
      ∧ (∀ p ∈ P, (∃ n ∈ jsp87ProgFull n0 D P, p ∣ n)
          ∧ (∃ n ∈ jsp87ProgFull n0 D P, jsp87Active K p 1 n)) := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  refine ⟨jsp87_5_21_prog_of_recipSum n0 D hD q H _hP hpc _hDp hH hh hpH hrec, ?_, ?_⟩
  · intro p hp
    exact jsp87ProgFull_nzFrac (K := K) (p := p) (H := H) hD hpos hp (hpc p hp) (_hDp p hp)
      (hh p hp)
  · intro p hp
    exact jsp87ProgFull_hne (K := K) (p := p) (H := H) (by omega) hpos hp (hpc p hp)
      (_hDp p hp) hH (hh p hp)

end JSP87
