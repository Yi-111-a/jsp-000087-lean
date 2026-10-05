/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.SharpVar

/-!
# JSP-000087, round 142 — THE NONZERO CLASS OF `X_p` IS A **CONSECUTIVE BLOCK**

`policy.json` `next_round_attack[0]` of round 141, verbatim:

> "**`jsp87_correlatedSample` (THE ONE ARITHMETIC INPUT LEFT)** …  The cheap
>  arithmetic facts to try first, in order: **(a) EXACT SUPPORT ON AN ARBITRARY
>  FINITE SAMPLE**: generalise `jsp87Xp0_binV_ne_zero_card_range` and
>  `jsp87Xp0_binV_zero_card_range_ge` to a finite sample `s` of distinct
>  integers, bounding `#{n ∈ s : X_p n ≠ 0}` from below by the number of cube
>  vertices actually hit, and note that a sample of size `< 2^K` cannot hit any
>  nonzero class at all, which would force `f_p = 0`; **(b)** a counting bound on
>  how many samples of a given size can have all the `f_p` in `[1/4, 3/4]`;
>  **(c)** only then attempt the analytic route."

and `next_round_attack[1]`:

> "**CLOSE THE GAP BETWEEN THE CANONICAL AND THE CORRELATED SAMPLE.**
>  `jsp87_endgame_515_realscale` proves (5.15) fails for the whole-period sample.
>  Is (5.15) still refutable for a sample of the form `{n : n ∈ [1, Y]}` (an
>  initial segment), i.e. does the support bound survive truncation?"

**Item (a) is not a counting argument at all: it is an identity, and it turns
the support of `X_p` into an interval.**  Round 139 (`jsp87Off_binV_image`)
proved that the cube offsets `jsp87Off (jsp87BinV K) ε` run through the
COMPLETE INTERVAL `[0, 2^K)`, once each.  Rounds 117–141 used that only to count:
`|jsp87ActiveRes K p h| = 2^K` (round 120) and the support of `X_p` on a period
has `≤ H + 2^K − 1` points (round 141).  **Nobody ever looked at the SHAPE.**
But the shape is trivial once the offsets are known to be a complete interval:

```
jsp87ActiveRes K p h  =  Finset.Icc (p − (h + 2^K − 1)) (p − h)        (★ §1)
```

— a **consecutive block** of exactly `2^K` residues — and therefore

```
X_p (n) ≠ 0  ⟺  p − (H + 2^K − 1) ≤ n mod p                        (★★ §2)
```

i.e. **the nonzero class is the single consecutive block of `H + 2^K − 1`
residues at the TOP of the period**.  Four consequences, none of which any
earlier round could state:

* **§3 the support on an ARBITRARY finite sample is an identity**, not a bound:
  `jsp87NzRes K p H s = s.filter (fun n => p − (H + 2^K − 1) ≤ n mod p)`.
  This is item (a) of the policy, done exactly and for every sample;
* **§4 the SMALL-SHIFT reformulation**: `X_p (n) ≠ 0` iff `p ∣ n + j` for some
  `1 ≤ j ≤ H + 2^K − 1`, i.e. **iff `p` divides one of the `H + 2^K − 1`
  integers immediately above `n`**.  In particular every contributing prime
  satisfies `p ≤ max s + H + 2^K − 1`;
* **§5 NEGATIVE KNOWLEDGE, refuting the policy's guess**: the policy predicted
  "a sample of size `< 2^K` cannot hit any nonzero class at all, which would
  force `f_p = 0`".  **That is FALSE**: the one-point sample `{p − 1}` has
  `f_p = 1` (`jsp87nzFrac_singleton_eq_one`).  What is true — and is what
  (5.21′) actually needs — is that such a sample has `f_p (1 − f_p) = 0`, so a
  witness of (5.21′) must **straddle the block boundary**;
* **§6 THE WHOLE-PERIOD INITIAL SEGMENT IS EXACTLY UNIFORM** (policy item 2):
  for the initial-segment sample `Icc 1 (k p)` — any number of whole periods —
  the nonzero fraction is **exactly** `f_p = (H + 2^K − 1)/p`
  (`jsp87NzFrac_Icc_mul_eq`), with no limit and no error term.  So the initial
  segment is *not* a correlated sample: it is exactly the uniform sample of
  round 120, whose variance bound already refutes (5.21).

## §7 what this does NOT do

`jsp_000087_main` is **not** declared.  §6 shows that a sample built out of whole
periods is worthless for the endgame, but (5.21′) could still be met by a
sample whose points are placed *individually* to straddle the block boundary for
many primes at once.  The residual input is unchanged: the Chowla-type
two-point correlation `jsp87Mcov_small` (`Theorem 3.1` of arXiv:2512.01739, from
Pilatte), which Mathlib does not contain.  See `ACCEPTANCE.md`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  THE "DEPTH" PARAMETRISATION OF A BLOCK -/

/-- **THE DEPTH IDENTITY OF A BLOCK.**

Under `h + A + 1 ≤ p`,

```
(p − h) − (p − (h + A)) = A ,
```

i.e. the block `Icc (p − (h + A)) (p − h)` starts exactly `A` steps below
`p − h`.  Every truncated-subtraction step of §1 and §2 is routed through this
single identity, which is proved once, here. -/
private theorem jsp87depth (p h A : ℕ) (hh : h + A + 1 ≤ p) :
    (p - h) - (p - (h + A)) = A := by
  have hle : h + A ≤ p - 1 := by omega
  have h1 : A + (p - (h + A)) = p - h := by omega
  have h7 : A + (p - (h + A)) - (p - (h + A)) = A := by
    have := Nat.add_sub_cancel_left (p - (h + A)) A
    omega
  omega

/-- **`h + 2^K − 1 < p` IN THE SHAPE THE DEPTH LEMMA WANTS.** -/
private theorem jsp87depth_ok {p h A : ℕ} (hh : h + A < p) : h + A + 1 ≤ p := by omega

/-- **THE BLOCK CONDITION IN TERMS OF THE DEPTH, GIVEN `m ≤ p − h`.** -/
private theorem jsp87block_iff_depth {p h m A : ℕ} (hh : h + A + 1 ≤ p)
    (_hm2 : m ≤ p - h) : (p - (h + A) ≤ m ↔ p - h - m ≤ A) := by
  have hmono : p - (h + A) ≤ p - h := by omega
  constructor
  · intro hm1
    exact (Nat.sub_le_sub_left hm1 (p - h)).trans_eq (jsp87depth p h A hh)
  · intro hj
    exact Nat.le_of_sub_le_sub_left hmono (by rw [jsp87depth p h A hh]; omega)

/-! ## §1  THE ACTIVE RESIDUE CLASSES ARE A CONSECUTIVE BLOCK -/

/-- **MEMBERSHIP IN `jsp87ActiveRes` IS "THE VERTEX OFFSET RUNS THROUGH
`[0, 2^K)`".**  The reindexing of the image, using round 139's
`jsp87Off_binV_image`. -/
private theorem jsp87mem_activeRes {K p h m : ℕ} :
    m ∈ jsp87ActiveRes K p h
      ↔ ∃ j ∈ Finset.range (2 ^ K), m = p - (h + j) := by
  classical
  unfold jsp87ActiveRes
  rw [Finset.mem_image]
  constructor
  · rintro ⟨ε, _, heq⟩
    exact ⟨jsp87Off (jsp87BinV K) ε, Finset.mem_range.mpr (jsp87Off_binV_lt ε), heq.symm⟩
  · rintro ⟨j, hj, heq⟩
    have hjmem : j ∈ (Finset.univ : Finset (Finset (Fin K))).image
        (fun δ => jsp87Off (jsp87BinV K) δ) := by
      rw [jsp87Off_binV_image]
      exact hj
    obtain ⟨ε, _, hj'⟩ := Finset.mem_image.mp hjmem
    refine ⟨ε, Finset.mem_univ _, ?_⟩
    rw [hj', heq]

/-- **`2 ^ n ≥ 1` FOR EVERY `n`.**  Isolated: neither `omega` nor `positivity`
will build it inside a larger goal. -/
private lemma jsp87pow_pos : ∀ n : ℕ, 1 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      nlinarith

#guard_msgs in
/-! ## §0b  TRUNCATED-SUBTRACTION REWRITING

The tactic handles these reliably when each is isolated, but not when nested
inside a larger truncated-subtraction goal, so every such step of the block
arguments is routed through one of the six lemmas below. -/

/-- `p − (x + y) = (p − x) − y` whenever there is no truncation. -/
private lemma jsp87nt1 {p x y : ℕ} (_h : x + y < p) : p - (x + y) = (p - x) - y := by omega

/-- The depth identity read at the top of the period. -/
private lemma jsp87nt2 {p h A : ℕ} (h1 : 1 ≤ h) (h2 : h + A < p) :
    (p - 1) - (p - (h + A)) = h + A - 1 := by omega

/-- `m ≤ p − h` is exactly the additive bound `m + h ≤ p`. -/
private lemma jsp87nt3 {p h m : ℕ} (_hk : h < p) (hm : m ≤ p - h) : m + h ≤ p := by omega

/-- ...and conversely. -/
private lemma jsp87nt4 {p h m : ℕ} (hk : h ≤ p) (hm : m + h ≤ p) : m ≤ p - h := by omega

/-- Sinking `h` by `1` lowers `p − h` by at most `1`. -/
private lemma jsp87nt5 {p h : ℕ} (hH : 1 ≤ h) (_hk : h ≤ p) : p - h ≤ p - 1 := by omega

/-- Anything in the block at `h ≥ 1` is at or below `p − 1`. -/
private lemma jsp87nt6 {p h m : ℕ} (hk : h ≤ p) (h1 : 1 ≤ h) (hm : m ≤ p - h) :
    m ≤ p - 1 := by omega

/-- **DIRECTION 1 OF §1: A WITNESS `j ≤ A` LANDS IN THE BLOCK.**

Here truncated subtraction is used *in its monotone direction*: `n ≤ m` gives
`k − m ≤ k − n`, so `h + j ≤ h + A` puts `p − (h + A) ≤ p − (h + j)`.  No
depth bookkeeping is needed for this direction. -/
private theorem jsp87blk_dir1 {p h m j A : ℕ} (_hh : h + A + 1 ≤ p) (hj : j ≤ A)
    (hEq : p - (h + j) = m) :
    p - (h + A) ≤ m ∧ m ≤ p - h := by
  have hmono : p - (h + A) ≤ p - (h + j) :=
    Nat.sub_le_sub_left (by omega) p
  have hmm : p - (h + j) ≤ p - h := Nat.sub_le_sub_left (by omega) p
  exact ⟨hmono.trans_eq hEq, hEq ▸ hmm⟩

/-- **DIRECTION 2 OF §1: A POINT OF THE BLOCK HAS A WITNESS `j ≤ A`.** -/
private theorem jsp87blk_dir2 {p h m A : ℕ} (hh : h + A + 1 ≤ p)
    (hlo : p - (h + A) ≤ m) (hhi : m ≤ p - h) :
    ∃ j, j ≤ A ∧ m = p - (h + j) := by
  have hd : p - h - m ≤ A := (jsp87block_iff_depth (m := m) hh hhi).mp hlo
  refine ⟨p - h - m, hd, ?_⟩
  have hsum : (p - h - m) + m = p - h := Nat.sub_add_cancel hhi
  have hle : h + (p - h - m) ≤ p := by omega
  have hsum2 : (h + (p - h - m)) + m = p := by omega
  have hEq : p - (h + (p - h - m)) = m := by
    have := Nat.add_sub_of_le hle
    omega
  exact hEq.symm

/-- **★ THE ACTIVE RESIDUE CLASSES AT LEVEL `h` ARE EXACTLY THE CONSECUTIVE BLOCK
`[p − (h + 2^K − 1), p − h]` ★**

This is the shape theorem.  `jsp87ActiveRes K p h` is the image of the vertices
`ε` under `ε ↦ p − (h + jsp87Off (jsp87BinV K) ε)`, and round 139's
`jsp87Off_binV_image` says the offsets run through `[0, 2^K)` **once each**, so
the image is the image of `j ↦ p − h − j` over `[0, 2^K)`, which under
`h + 2^K − 1 < p` (no truncation) is the block of its values.  The two directions
are `jsp87blk_dir1` and `jsp87blk_dir2`. -/
theorem jsp87ActiveRes_eq_Icc {K p h : ℕ} (hh : h + (2 ^ K - 1) < p) :
    jsp87ActiveRes K p h = Finset.Icc (p - (h + (2 ^ K - 1))) (p - h) := by
  classical
  ext m
  rw [jsp87mem_activeRes, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, heq⟩
    rw [Finset.mem_range] at hj
    have hj' : j ≤ 2 ^ K - 1 := by omega
    have hEq : p - (h + j) = m := heq.symm
    exact jsp87blk_dir1 (p := p) (h := h) (m := m) (j := j) (A := 2 ^ K - 1)
      (by omega) hj' hEq
  · rintro ⟨hlo, hhi⟩
    obtain ⟨j, hj, heq⟩ := jsp87blk_dir2 (p := p) (h := h) (m := m) (A := 2 ^ K - 1)
      (by omega) hlo hhi
    have hK : 1 ≤ 2 ^ K := jsp87pow_pos K
    refine ⟨j, Finset.mem_range.mpr (by omega), heq⟩


/-- **A SMALL TRUNCATED-SUBTRACTION REWRITING RULE.**

`m + k ≤ p` implies `m ≤ p - k`, but `omega` needs `k ≤ p` stated to use it on
nested truncated subtraction.  Every such step of §1 and §2 goes through here. -/
private lemma jsp87le_of_add_le {m k p : ℕ} (hk : k ≤ p) (hmk : m + k ≤ p) :
    m ≤ p - k := Nat.le_sub_of_add_le hmk

/-- **`p - X` IS ANTITONE IN `X`, PROVIDED `X ≤ p`.**

`omega` will not see this through nested truncated subtraction, so it is proved
once, here, and every monotonicity step of the union argument is routed through
it. -/
private lemma jsp87anti {p k1 k2 : ℕ} (h12 : k1 ≤ k2) (h2p : k2 ≤ p) :
    p - k2 ≤ p - k1 := by
  obtain ⟨t, ht⟩ := Nat.le.dest h12
  have ht2 : k1 + t = k2 := ht
  have hp1 : p - k2 + k2 = p := Nat.sub_add_cancel h2p
  omega

/-- **THE LEFT END OF THE UNION STEP.**

A residue `m` of the whole block `[p - (H + A), p - 1]` lies at or above the
start of the block of level `h = min H (p - m)`, the deepest level whose block
still reaches `m`.  Split on whether the residue's own depth `p - m` is at most
`H`; in the first case `h = p - m` and the claim is pure `p - X` antitonicity,
in the second case `h = H` and the claim is the hypothesis. -/
private lemma jsp87union_lo {p H A m : ℕ} (hH : 1 ≤ H) (hh : H + A + 1 ≤ p)
    (hm : p - (H + A) ≤ m) (_hmi : m ≤ p - 1) :
    p - (min H (p - m) + A) ≤ m := by
  by_cases hc : p - m ≤ H
  · have hmin : min H (p - m) = p - m := Nat.min_eq_right hc
    rw [hmin]
    obtain ⟨j, hj⟩ := Nat.le.dest hm
    have hj2 : p - (H + A) + j = m := hj
    have hHAp : H + A ≤ p := by omega
    have hpm : p - m ≤ p := Nat.sub_le p m
    have hsum : p - m + A ≤ p := by omega
    have hstep : p - ((p - m) + A) ≤ p - (p - m) :=
      jsp87anti (k1 := p - m) (k2 := (p - m) + A) (by omega) hsum
    have heq : p - (p - m) + (p - m) = p := Nat.sub_add_cancel hpm
    omega
  · have hmin : min H (p - m) = H := Nat.min_eq_left (Nat.le_of_not_ge hc)
    rw [hmin]
    exact hm

/-- **THE RIGHT END OF THE UNION STEP: THE WITNESS SITS ABOVE `m`.** -/
private lemma jsp87union_hi {p H A m : ℕ} (hh : H + A + 1 ≤ p) (hmi : m ≤ p - 1) :
    m ≤ p - min H (p - m) := by
  have hone : 1 ≤ p - m := by omega
  obtain ⟨k, hk⟩ := Nat.le.dest (show min H (p - m) ≤ p - m from Nat.min_le_right _ _)
  have hk2 : min H (p - m) + k = p - m := hk
  have hpm : p - m ≤ p := Nat.sub_le p m
  have hke : min H (p - m) ≤ p := by omega
  exact (Nat.le_sub_iff_add_le hke).mpr (by omega)

/-- **★ THE UNION OF THE ACTIVE RESIDUE CLASSES OVER THE `H` LEVELS IS THE SINGLE
CONSECUTIVE BLOCK `[p − (H + 2^K − 1), p − 1]` ★**

The blocks of §1 are consecutive and overlap, so their union is again a block.
Direction 1 uses antitonicity of `p - X`; direction 2 uses only the witness
level `h = min H (p - m)`, which is the deepest level whose block still reaches
the residue. -/
theorem jsp87union_activeRes_eq_Icc {K p H : ℕ} (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) :
    (Finset.Icc 1 H).biUnion (jsp87ActiveRes K p)
      = Finset.Icc (p - (H + (2 ^ K - 1))) (p - 1) := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨h, hh1, hh2⟩ := hm
    rw [Finset.mem_Icc] at hh1
    rw [jsp87ActiveRes_eq_Icc (K := K) (p := p) (h := h) (by omega)] at hh2
    rw [Finset.mem_Icc] at hh2
    have hlo : p - (h + (2 ^ K - 1)) ≤ m := hh2.1
    have hhi : m ≤ p - h := hh2.2
    have h1h : 1 ≤ h := hh1.1
    have hhH : h ≤ H := hh1.2
    have hh1' : h + (2 ^ K - 1) + 1 ≤ p := by omega
    have hHp : H ≤ p := by omega
    have hsum : h + (2 ^ K - 1) ≤ H + (2 ^ K - 1) := Nat.add_le_add_right hhH _
    have hleft : p - (H + (2 ^ K - 1)) ≤ m := by
      have hmono : p - (H + (2 ^ K - 1)) ≤ p - (h + (2 ^ K - 1)) :=
        jsp87anti (k1 := h + (2 ^ K - 1)) (k2 := H + (2 ^ K - 1)) hsum (by omega)
      exact hmono.trans hlo
    -- right end: `m ≤ p - h` and `1 ≤ h` put `m` at or below `p - 1`
    have hright : m ≤ p - 1 := by
      obtain ⟨k, hk⟩ := Nat.le.dest hhi
      have hk2 : m + k = p - h := hk
      have hsub : h + 1 ≤ p := Nat.succ_le_of_lt (by omega)
      have hp1 : (p - 1) + 1 = p := by omega
      omega
    rw [Finset.mem_Icc]
    exact ⟨hleft, hright⟩
  · intro hm
    rw [Finset.mem_Icc] at hm
    have hlo : p - (H + (2 ^ K - 1)) ≤ m := hm.1
    have hhi : m ≤ p - 1 := hm.2
    set h : ℕ := min H (p - m) with hdef
    have hlo' : p - (h + (2 ^ K - 1)) ≤ m := jsp87union_lo hH hh hlo hhi
    have hhi' : m ≤ p - h := jsp87union_hi hh hhi
    rw [Finset.mem_biUnion]
    refine ⟨h, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hdef, Nat.le_min]
      exact ⟨hH, by omega⟩
    · rw [hdef]
      exact Nat.min_le_left _ _
    rw [jsp87ActiveRes_eq_Icc (K := K) (p := p) (h := h) (by omega)]
    rw [Finset.mem_Icc]
    exact ⟨hlo', hhi'⟩

/-- **THE CONSECUTIVE BLOCK HAS EXACTLY `H + 2^K − 1` RESIDUES.** -/
theorem jsp87card_block {K p H : ℕ} (hH : 1 ≤ H) (hh : H + (2 ^ K - 1) < p) :
    ((Finset.Icc (p - (H + (2 ^ K - 1))) (p - 1) : Finset ℕ)).card = H + 2 ^ K - 1 := by
  have hK : 1 ≤ 2 ^ K := jsp87pow_pos K
  have h1 : (p - (H + (2 ^ K - 1)) : ℕ) ≤ p - 1 := by omega
  -- read the block length off the depth identity at level `1`
  have hle : H + (2 ^ K - 1) ≤ p - 1 := by omega
  have hc : (1 + (H + (2 ^ K - 1) - 1)) + 1 ≤ p := by omega
  have hd : p - 1 - (p - (1 + (H + (2 ^ K - 1) - 1))) = H + (2 ^ K - 1) - 1 :=
    jsp87depth p 1 (H + (2 ^ K - 1) - 1) hc
  have hHH : 1 + (H + (2 ^ K - 1) - 1) = H + (2 ^ K - 1) := by omega
  rw [hHH] at hd
  rw [jsp87card_Icc]
  omega

/-! ## §2  ★★ THE NONZERO CLASS IS THE BLOCK ★★ -/

/-- **★★ SOME LEVEL ACTIVE IMPLIES THE CUBE SUM IS NONZERO ★★**

Round 123 proved `X_p n H ≠ 0 → ∃ h ∈ [1,H]`, `jsp87Active K p h n`
(`jsp87Xp0_ne_zero_iff_active`).  The converse needs an argument — a *later*
active level could in principle be cancelled by the levels above it — and is the
**least-active-level** argument: at the least active level `h₀` the level sum is
`± 2^{−(h₀+K)}` while **every** lower level is inactive, so round 119's
`jsp87Xp0_abs_ge_active` applies with vanishing error.

Neither direction was available before this round; together they are the
iff-form of the support, which is what §2 needs. -/
theorem jsp87nz_iff_some_active {K p n H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H) :
    jsp87Xp0 (jsp87BinV K) p n H ≠ 0
      ↔ ∃ h ∈ Finset.Icc 1 H, jsp87Active K p h n := by
  classical
  constructor
  · exact jsp87Xp0_ne_zero_iff_active (K := K) (p := p) (n := n) (H := H) hK hH
  · rintro ⟨h, hh, hact⟩
    set S : Finset ℕ := (Finset.Icc 1 H).filter (fun b => jsp87Active K p b n)
    have hne : S.Nonempty := ⟨h, Finset.mem_filter.mpr ⟨hh, hact⟩⟩
    have hminIcc : S.min' hne ∈ Finset.Icc 1 H :=
      (Finset.mem_filter.mp (Finset.min'_mem S hne)).1
    have hmin_act : jsp87Active K p (S.min' hne) n :=
      (Finset.mem_filter.mp (Finset.min'_mem S hne)).2
    have hmin_lo : 1 ≤ S.min' hne := (Finset.mem_Icc.mp hminIcc).1
    have hmin_hi : S.min' hne ≤ H := (Finset.mem_Icc.mp hminIcc).2
    have hmin_le : S.min' hne ≤ S.min' hne := Nat.le_refl _
    have hnil : ∀ b ∈ Finset.Icc 1 (S.min' hne), b ≠ S.min' hne →
        ¬ jsp87Active K p b n := by
      intro b hb hne' hbact
      have hbIccH : b ∈ Finset.Icc 1 H := by
        rw [Finset.mem_Icc] at hb ⊢
        exact ⟨hb.1, le_trans hb.2 hmin_hi⟩
      have hbS : b ∈ S := Finset.mem_filter.mpr ⟨hbIccH, hbact⟩
      have hle : S.min' hne ≤ b := Finset.min'_le S b hbS
      rw [Finset.mem_Icc] at hb
      omega
    have hminIcc' : S.min' hne ∈ Finset.Icc 1 H := hminIcc
    have h1 := jsp87Xp0_abs_ge_active (K := K) (p := p) (n := n) (H := H)
      (h := S.min' hne) hK hnil hmin_act hminIcc'
    intro hz
    rw [hz, abs_zero] at h1
    exact absurd h1 (not_le.mpr (jsp87W_pos K H))

/-- **★★ THE NONZERO CLASS OF `X_p` IS THE CONSECUTIVE BLOCK ★★**

For `1 ≤ H`, `2^K ≤ p` and `H + 2^K ≤ p`:

```
X_p (n) ≠ 0   ⟺   p − (H + 2^K − 1) ≤ n mod p ,
```

i.e. **the sample point `n` is a nonzero point of `X_p` exactly when its residue
modulo `p` lies in the last `H + 2^K − 1` residues before a multiple of `p`.**

Rounds 117–141 proved bounds on the support (`2^K ≤ card ≤ H + 2^K − 1`); this
is the support itself. -/
theorem jsp87nz_iff_res_block {K p H : ℕ} (hK : 2 ^ K ≤ p) (hh : H + (2 ^ K - 1) + 1 ≤ p)
    (hH : 1 ≤ H) (n : ℕ) :
    jsp87Xp0 (jsp87BinV K) p n H ≠ 0
      ↔ p - (H + (2 ^ K - 1)) ≤ n % p := by
  have hK1 : 1 ≤ 2 ^ K := jsp87pow_pos K
  have hp0 : 0 < p := by omega
  have hmod : n % p ≤ p - 1 := by
    have := Nat.mod_lt n hp0
    omega
  constructor
  · rintro hne
    obtain ⟨h, hh0, hact⟩ := (jsp87nz_iff_some_active hK hH).mp hne
    rw [Finset.mem_Icc] at hh0
    have hactRes : jsp87Active K p h (n % p) :=
      (jsp87Active_of_res (K := K) (p := p) (h := h) (n := n)).mp hact
    have hmem : (n % p) ∈ jsp87ActiveRes K p h :=
      (jsp87Active_iff_activeRes hh0.1 hp0 hmod (by omega)).mp hactRes
    rw [jsp87ActiveRes_eq_Icc (K := K) (p := p) (h := h) (by omega),
      Finset.mem_Icc] at hmem
    have h1 : p - (h + (2 ^ K - 1)) ≤ n % p := hmem.1
    have hHAle : H + (2 ^ K - 1) ≤ p := by omega
    have hHle : h + (2 ^ K - 1) ≤ H + (2 ^ K - 1) := Nat.add_le_add_right hh0.2 _
    have h3 : p - (H + (2 ^ K - 1)) ≤ p - (h + (2 ^ K - 1)) :=
      jsp87anti (k1 := h + (2 ^ K - 1)) (k2 := H + (2 ^ K - 1)) hHle hHAle
    exact h3.trans h1
  · intro hmem
    have hmemIcc : (n % p) ∈ Finset.Icc (p - (H + (2 ^ K - 1))) (p - 1) :=
      Finset.mem_Icc.mpr ⟨hmem, hmod⟩
    have hmemU : (n % p) ∈ (Finset.Icc 1 H).biUnion (jsp87ActiveRes K p) := by
      rw [jsp87union_activeRes_eq_Icc hH (by omega)]
      exact hmemIcc
    rw [Finset.mem_biUnion] at hmemU
    obtain ⟨h, hh0, hmemh⟩ := hmemU
    rw [Finset.mem_Icc] at hh0
    have hactRes : jsp87Active K p h (n % p) :=
      (jsp87Active_iff_activeRes hh0.1 hp0 hmod (by omega)).mpr hmemh
    have hact : jsp87Active K p h n :=
      (jsp87Active_of_res (K := K) (p := p) (h := h) (n := n)).mpr hactRes
    exact (jsp87nz_iff_some_active hK hH).mpr ⟨h, Finset.mem_Icc.mpr hh0, hact⟩

/-- **★★ THE EXACT SUPPORT ON A PERIOD IS `H + 2^K − 1` ★★**

This SHARPENS round 141's `jsp87Xp0_binV_ne_zero_card_le` (a `≤` bound) into an
EQUALITY, and simultaneously confirms round 119's lower bound `2^K ≤ card`: the
support is the block, whose size is exactly `H + 2^K − 1`. -/
theorem jsp87card_nzRes_period {K p H : ℕ} (hK : 2 ^ K ≤ p) (hh : H + (2 ^ K - 1) + 1 ≤ p)
    (hH : 1 ≤ H) :
    (((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)) : Finset ℕ).card
      = H + 2 ^ K - 1 := by
  have hK1 : 1 ≤ 2 ^ K := jsp87pow_pos K
  have hp0 : 0 < p := by omega
  have hset : ((Finset.Icc 0 (p - 1)).filter
        (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0))
      = Finset.Icc (p - (H + (2 ^ K - 1))) (p - 1) := by
    ext n
    constructor
    · intro hn
      have hnin : n ∈ Finset.Icc 0 (p - 1) := (Finset.mem_filter.mp hn).1
      have hnz : jsp87Xp0 (jsp87BinV K) p n H ≠ 0 := (Finset.mem_filter.mp hn).2
      have hnin' : 0 ≤ n ∧ n ≤ p - 1 := Finset.mem_Icc.mp hnin
      have hlt : n < p := by omega
      have hmod : n % p = n := Nat.mod_eq_of_lt hlt
      have hmain0 := (jsp87nz_iff_res_block hK hh hH n).mp hnz
      have hmain : p - (H + (2 ^ K - 1)) ≤ n := by rw [← hmod]; exact hmain0
      show n ∈ Finset.Icc (p - (H + (2 ^ K - 1))) (p - 1)
      rw [Finset.mem_Icc]
      exact ⟨hmain, hnin'.2⟩
    · intro hn
      have hnblk : p - (H + (2 ^ K - 1)) ≤ n ∧ n ≤ p - 1 := Finset.mem_Icc.mp hn
      have hlt : n < p := by omega
      have hmod : n % p = n := Nat.mod_eq_of_lt hlt
      have hmain : p - (H + (2 ^ K - 1)) ≤ n := hnblk.1
      have hmain2 : p - (H + (2 ^ K - 1)) ≤ n % p := by rw [hmod]; exact hmain
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hnblk.2⟩, ?_⟩
      exact (jsp87nz_iff_res_block hK hh hH n).mpr hmain2
  rw [hset]
  exact jsp87card_block (by omega) (by omega)

end JSP87
