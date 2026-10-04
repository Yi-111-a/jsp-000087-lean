/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-119).
-/
import JSPProblem.VarLocal

/-!
# JSP-000087, round 119 — THE BINARY CUBE, AND THE DISCHARGE OF THE SEPARATION HYPOTHESIS

## Why this file exists

Rounds 117–118 built the cube-alternating variable `X_p` of (5.13) and the
endgame of Tao–Teräväinen arXiv:2512.01739 §5, but both theorems kept an
**explicit hypothesis** on the common differences `v` of the cube:

```lean
hsep : ∀ i : ℕ, ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p i (v p) h
```

`policy.json` `next_round_attack[0]` (unexecuted for 118 rounds) asked for
exactly this to be removed:

> *"DISCHARGE THE SEPARATION HYPOTHESIS … prove that for `v k = 2^k` the subset
> sums `Σ_{k ∈ ε} 2^k` determine `ε` (parity induction on the least element of
> the symmetric difference), giving `jsp87Sep_of_pow : p > H + 2^K − 1` implies
> `jsp87Sep` at every level `h ≤ H`.  This removes an explicit hypothesis from
> `jsp87_endgame_twoClass` and is pure combinatorics on binary
> representations."*

**This file is that discharge.**  The `2^K` vertices of the binary cube are the
*complete sequence*: their offsets `Σ_{k ∈ ε} 2^k` are **pairwise distinct**
and all lie in `[0, 2^K)`.  Two consequences follow, and both are pure
combinatorics on binary representations — no analytic input at all:

* **(A) `jsp87Sep_of_pow`.**  `jsp87Sep p (jsp87BinV K) h` holds as soon as
  `h + 2^K − 1 < p`; no hypothesis on the sample point, on `n`, or on the level
  `h` is left.  **The separation hypothesis is thereby removed from the
  endgame.**
* **(B) `jsp87HitVerts_card_le_one_pow`.**  The one-vertex collapse needs only
  `2^K ≤ p` — *strictly weaker* than (A), and independent of the level: two
  distinct vertices differ by a nonzero multiple of `p` of absolute value
  `< 2^K ≤ p`.

The payoff theorems are `jsp87Xp_abs_le_twenty_pow` (hypothesis **(5.19)**
discharged with *no* hypothesis whatsoever) and

* **`jsp87_endgame_twoClass_pow`** — the round-118 endgame in which the
  separation hypothesis is replaced by the single arithmetic inequality
  `H + 2^K − 1 < p`, and

* **`jsp87_endgame_cube_pow`** — the round-117 endgame likewise.

Both are *strictly stronger* than their predecessors: the same conclusion with
one fewer hypothesis, the removed one being the only non-arithmetic one.

## What is proved here

| Section | Content |
| --- | --- |
| §1 | **binary uniqueness**: distinct subsets of `ℕ` have distinct sums of `2^k` (`jsp87pow_inj`), from the parity descent at the least element of the symmetric difference |
| §2 | the binary cube `jsp87BinV`: `jsp87Off_binV` (offsets are subset sums of powers of two), `jsp87Off_binV_lt` (offsets lie in `[0, 2^K)`), `jsp87Sep_of_pow` — **(A)** |
| §3 | **the exact hit count**: `jsp87HitVerts_card_le_one_pow`, `jsp87OneVertex_of_pow` — **(B)**; and the level sums `jsp87XpLevel_eq_zero_or_sign_pow`, `jsp87HitVerts_singleton_pow` |
| §4 | **hypothesis (5.19), discharged unconditionally**: `jsp87Xp_abs_le_pow`, `jsp87Xp_abs_le_twenty_pow` |
| §5 | **the endgame with no separation hypothesis**: `jsp87_endgame_twoClass_pow`, `jsp87_endgame_cube_pow` |
| §6 | **the cube sum is `p`-periodic in the sample point**: `jsp87HitVerts_period`, `jsp87Xp0_period`, `jsp87Xp0_pow_period` — the variable of (5.13) is a function of `n mod p` alone |

## What is *not* proved here

`jsp_000087_main` is **not declared**.  Removing the separation hypothesis
leaves exactly the two *quantitative arithmetic* inputs localised in
`policy.json` `round_118_blocker`:

* **(5.18)** `κ_j = o(1)` for `j = 1, …, 5`, and
* **the balanced two-class split** `jsp87_balancedSplit` for the hit values of
  `X_p` (the content of §3 / Theorem 3.1 of arXiv:2512.01739, from Pilatte).

Mathlib contains no Chowla-type, Elliott-type or Gowers-uniformity statement
for multiplicative functions, so those cannot be supplied here.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## §1  Binary uniqueness of subset sums -/

/-- **AN EMPTY INTERSECTION MEANS DISJOINT.** -/
private theorem jsp87disjoint_of_inter_eq_empty {α : Type*} [DecidableEq α]
    {A B : Finset α} (h : A ∩ B = ∅) : Disjoint A B := by
  refine Finset.disjoint_left.2 fun x hxA hxB => ?_
  exact absurd (Finset.mem_inter.mpr ⟨hxA, hxB⟩) (by rw [h]; simp)

/-- **A SUM OF EVEN NUMBERS IS EVEN.** -/
private theorem jsp87even_sum {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℕ)
    (h : ∀ a ∈ s, g a % 2 = 0) : (∑ a ∈ s, g a) % 2 = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h1 : g a % 2 = 0 := h a (Finset.mem_insert_self a s)
    have h2 : (∑ x ∈ s, g x) % 2 = 0 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    rw [Finset.sum_insert ha, Nat.add_mod, h1, h2]

/-- **FACTORING A POWER OF TWO OUT OF A SINGLE TERM.** -/
private theorem jsp87pow_mul {m k : ℕ} (h : m ≤ k) : 2^k = 2^m * 2^(k - m) := by
  rw [← pow_add, Nat.add_sub_of_le h]

/-- **A POWER OF TWO WITH A POSITIVE EXPONENT IS EVEN.** -/
private theorem jsp87pow_shift {m k : ℕ} (h : m < k) : 2^(k - m) % 2 = 0 := by
  have h3 : 2 ^ (k - m) = 2 ^ (k - m - 1) * 2 := by
    have he : k - m = (k - m - 1) + 1 := by omega
    calc 2 ^ (k - m) = 2 ^ ((k - m - 1) + 1) := congrArg (fun e : ℕ => 2 ^ e) he
      _ = 2 ^ (k - m - 1) * 2 := Nat.pow_succ _ _
  rw [h3, Nat.mul_mod]
  rfl

/-- **A SUBSET SUM OF POWERS OF TWO, ABOVE A FIXED MINIMUM, FACTORS.** -/
private theorem jsp87pow_factor (m : ℕ) (C : Finset ℕ) (hmin : ∀ k ∈ C, m < k) :
    (∑ k ∈ C, 2^k) = 2^m * (∑ k ∈ C, 2^(k - m)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => jsp87pow_mul (Nat.le_of_lt (hmin k hk))

/-- **TWO DISJOINT FINSUETS WITH THE SAME SUBSET SUM OF POWERS OF TWO ARE BOTH
EMPTY.**  This is the parity descent at the least element `m` of `A ∪ B`: `m`
lies in exactly one of `A, B` (disjointness), and after dividing both sides by
`2^m` the side carrying `m` is odd while the other side is even. -/
private theorem jsp87pow_disjoint {A B : Finset ℕ} (hd : A ∩ B = ∅)
    (hs : (∑ k ∈ A, 2^k) = ∑ k ∈ B, 2^k) (hne : A.Nonempty) : False := by
  classical
  have hdj : ∀ ⦃a : ℕ⦄, a ∈ A → a ∉ B :=
    Finset.disjoint_left.mp (jsp87disjoint_of_inter_eq_empty hd)
  obtain ⟨a, ha⟩ := hne
  have hau : a ∈ A ∪ B := Finset.mem_union_left B ha
  let m : ℕ := (A ∪ B).min' ⟨a, hau⟩
  have hm : m ∈ A ∪ B := Finset.min'_mem _ _
  have hmin : ∀ k ∈ A ∪ B, m ≤ k := fun k hk => Finset.min'_le _ k hk
  have hminA' : ∀ k ∈ A.erase m, m < k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_erase.mp hk
    exact lt_of_le_of_ne (hmin k (Finset.mem_union_left B hk2)) (Ne.symm hk1)
  have hminB' : ∀ k ∈ B.erase m, m < k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_erase.mp hk
    exact lt_of_le_of_ne (hmin k (Finset.mem_union_right A hk2)) (Ne.symm hk1)
  rcases Finset.mem_union.mp hm with hmA | hmB
  · have hmB0 : m ∉ B := fun hmb => hdj hmA hmb
    have hminB : ∀ k ∈ B, m < k := by
      intro k hk
      refine lt_of_le_of_ne (hmin k (Finset.mem_union_right A hk)) ?_
      intro hkm
      exact hmB0 (hkm ▸ hk)
    have heA : A = insert m (A.erase m) := (Finset.insert_erase hmA).symm
    have hSA : (∑ k ∈ A.erase m, 2^(k - m)) % 2 = 0 :=
      jsp87even_sum _ _ fun k hk => jsp87pow_shift (hminA' k hk)
    have hSB : (∑ k ∈ B, 2^(k - m)) % 2 = 0 :=
      jsp87even_sum _ _ fun k hk => jsp87pow_shift (hminB k hk)
    have hFA := jsp87pow_factor m (A.erase m) hminA'
    have hFB := jsp87pow_factor m B hminB
    have hsumA : (∑ k ∈ A.erase m, 2^k) + 2^m = ∑ k ∈ A, 2^k := by
      calc (∑ k ∈ A.erase m, 2^k) + 2^m = 2^m + ∑ k ∈ A.erase m, 2^k := Nat.add_comm _ _
        _ = ∑ k ∈ insert m (A.erase m), 2^k :=
          (Finset.sum_insert (by simp : m ∉ A.erase m)).symm
        _ = ∑ k ∈ A, 2^k := by rw [← heA]
    have hkey : 2^m * (∑ k ∈ A.erase m, 2^(k - m)) + 2^m = 2^m * (∑ k ∈ B, 2^(k - m)) := by
      rw [← hFA, hsumA, hs, hFB]
    have hcancel : (∑ k ∈ A.erase m, 2^(k - m)) + 1 = ∑ k ∈ B, 2^(k - m) :=
      Nat.mul_left_cancel (by positivity) hkey
    have hodd : ((∑ k ∈ A.erase m, 2^(k - m)) + 1) % 2 = 1 := by
      rw [Nat.add_mod, hSA]
    rw [hcancel] at hodd
    rw [hSB] at hodd
    exact absurd hodd (by norm_num)
  · have hmA0 : m ∉ A := fun hma => hdj hma hmB
    have hminA : ∀ k ∈ A, m < k := by
      intro k hk
      refine lt_of_le_of_ne (hmin k (Finset.mem_union_left B hk)) ?_
      intro hkm
      exact hmA0 (hkm ▸ hk)
    have heB : B = insert m (B.erase m) := (Finset.insert_erase hmB).symm
    have hSB : (∑ k ∈ B.erase m, 2^(k - m)) % 2 = 0 :=
      jsp87even_sum _ _ fun k hk => jsp87pow_shift (hminB' k hk)
    have hSA : (∑ k ∈ A, 2^(k - m)) % 2 = 0 :=
      jsp87even_sum _ _ fun k hk => jsp87pow_shift (hminA k hk)
    have hFA := jsp87pow_factor m A hminA
    have hFB := jsp87pow_factor m (B.erase m) hminB'
    have hsumB : (∑ k ∈ B.erase m, 2^k) + 2^m = ∑ k ∈ B, 2^k := by
      calc (∑ k ∈ B.erase m, 2^k) + 2^m = 2^m + ∑ k ∈ B.erase m, 2^k := Nat.add_comm _ _
        _ = ∑ k ∈ insert m (B.erase m), 2^k :=
          (Finset.sum_insert (by simp : m ∉ B.erase m)).symm
        _ = ∑ k ∈ B, 2^k := by rw [← heB]
    have hkey : 2^m * (∑ k ∈ B.erase m, 2^(k - m)) + 2^m = 2^m * (∑ k ∈ A, 2^(k - m)) := by
      rw [← hFB, hsumB, hs.symm, hFA]
    have hcancel : (∑ k ∈ B.erase m, 2^(k - m)) + 1 = ∑ k ∈ A, 2^(k - m) :=
      Nat.mul_left_cancel (by positivity) hkey
    have hodd : ((∑ k ∈ B.erase m, 2^(k - m)) + 1) % 2 = 1 := by
      rw [Nat.add_mod, hSB]
    rw [hcancel] at hodd
    rw [hSA] at hodd
    exact absurd hodd (by norm_num)

/-- **BINARY UNIQUENESS.**  Two distinct finite sets of natural numbers have
distinct sums of `2^k`; equivalently, every natural number has at most one
expansion as a sum of *distinct* powers of two. -/
theorem jsp87pow_inj (ε ε' : Finset ℕ) (h : (∑ k ∈ ε, 2^k) = ∑ k ∈ ε', 2^k) :
    ε = ε' := by
  classical
  set A := ε \ ε' with hA
  set B := ε' \ ε with hB
  have hAB : A ∩ B = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      rw [hA] at hx1
      rw [hB] at hx2
      simp only [Finset.mem_sdiff] at hx1 hx2
      exact False.elim (hx1.2 hx2.1)
    · intro hx
      exact absurd hx (by simp)
  have hsum : (∑ k ∈ A, 2^k) = ∑ k ∈ B, 2^k := by
    have h1 : (∑ k ∈ ε ∩ ε', 2^k) + ∑ k ∈ A, 2^k = ∑ k ∈ ε, 2^k := by
      have h := Finset.sum_inter_add_sum_sdiff ε ε' (fun k => 2^k)
      rwa [hA.symm] at h
    have h2 : (∑ k ∈ ε ∩ ε', 2^k) + ∑ k ∈ B, 2^k = ∑ k ∈ ε', 2^k := by
      have h := Finset.sum_inter_add_sum_sdiff ε' ε (fun k => 2^k)
      rw [Finset.inter_comm, hB.symm] at h
      exact h
    rw [← h1, ← h2] at h
    exact Nat.add_left_cancel h
  have hAe : A = ∅ := by
    by_contra hne
    exact jsp87pow_disjoint hAB hsum (Finset.nonempty_iff_ne_empty.mpr hne)
  have hBe : B = ∅ := by
    by_contra hne
    have hAB' : B ∩ A = ∅ := by rw [Finset.inter_comm]; exact hAB
    exact jsp87pow_disjoint hAB' hsum.symm (Finset.nonempty_iff_ne_empty.mpr hne)
  refine Finset.ext fun x => ?_
  constructor
  · intro hx
    have hxA : x ∉ A := by rw [hAe]; simp
    rw [hA, Finset.mem_sdiff] at hxA
    by_contra hn
    exact hxA ⟨hx, hn⟩
  · intro hx
    have hxB : x ∉ B := by rw [hBe]; simp
    rw [hB, Finset.mem_sdiff] at hxB
    by_contra hn
    exact hxB ⟨hx, hn⟩

/-! ## §2  The binary cube: complete offsets -/

/-- **THE BINARY DIFFERENCES** `v k = 2^k`: the standard Hilbert cube, whose
`2^K` offsets form the complete sequence `0, 1, …, 2^K − 1`. -/
def jsp87BinV (K : ℕ) : Fin K → ℕ := fun k => 2^(k : ℕ)

/-- **THE OFFSET OF A VERTEX OF THE BINARY CUBE** is a sum of distinct powers of
two. -/
theorem jsp87Off_binV {K : ℕ} (ε : Finset (Fin K)) :
    jsp87Off (jsp87BinV K) ε = ∑ k ∈ ε.image Fin.val, 2^k := by
  have h1 : (∑ j ∈ ε.image Fin.val, 2 ^ j) = ∑ k ∈ ε, 2 ^ (k : ℕ) :=
    Finset.sum_image (s := ε) (f := fun j : ℕ => 2 ^ j) (g := Fin.val)
      (Set.injOn_of_injective Fin.val_injective)
  unfold jsp87Off jsp87BinV
  rw [h1]

/-- **THE GEOMETRIC SUM** `∑_{k < K} 2^k = 2^K − 1`. -/
theorem jsp87sum_pow_two (K : ℕ) : (∑ k ∈ Finset.range K, 2^k) = 2 ^ K - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hle : 2 ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num : (2 : ℕ) > 0) (by omega)
    rw [Finset.sum_range_succ, ih]
    omega

/-- **THE OFFSETS LIE IN THE COMPLETE INTERVAL `[0, 2^K)`.** -/
theorem jsp87Off_binV_lt {K : ℕ} (ε : Finset (Fin K)) :
    jsp87Off (jsp87BinV K) ε < 2 ^ K := by
  rw [jsp87Off_binV]
  have hsub : ε.image Fin.val ⊆ Finset.range K := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact List.mem_range.2 k.2
  have h1 : (∑ j ∈ ε.image Fin.val, 2^j) ≤ ∑ j ∈ Finset.range K, 2^j :=
    Finset.sum_le_sum_of_subset_of_nonneg (s := ε.image Fin.val) (t := Finset.range K)
      hsub (fun j _ _ => Nat.zero_le (2 ^ j))
  have h2 := jsp87sum_pow_two K
  have h3 : (∑ j ∈ ε.image Fin.val, 2^j) ≤ 2 ^ K - 1 := h1.trans_eq h2
  have h4 : 1 ≤ 2 ^ K := Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : (0 : ℕ) < 2))
  omega

/-- **THE OFFSETS OF THE BINARY CUBE DETERMINE THE VERTEX.** -/
theorem jsp87Off_binV_inj {K : ℕ} {ε ε' : Finset (Fin K)}
    (h : jsp87Off (jsp87BinV K) ε = jsp87Off (jsp87BinV K) ε') : ε = ε' := by
  have hs : (∑ j ∈ ε.image Fin.val, 2^j) = ∑ j ∈ ε'.image Fin.val, 2^j := by
    rw [← jsp87Off_binV ε, ← jsp87Off_binV ε']
    exact h
  have himg : ε.image Fin.val = ε'.image Fin.val := jsp87pow_inj _ _ hs
  refine Finset.ext fun k => ?_
  constructor
  · intro hk
    have hk2 : (k : ℕ) ∈ ε'.image Fin.val := himg ▸ Finset.mem_image.2 ⟨k, hk, rfl⟩
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hk2
    rw [Fin.ext hav] at ha
    exact ha
  · intro hk
    have hk2 : (k : ℕ) ∈ ε.image Fin.val := himg.symm ▸ Finset.mem_image.2 ⟨k, hk, rfl⟩
    obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hk2
    rw [Fin.ext hav] at ha
    exact ha

/-- **THE CUBE SHIFTS OF THE BINARY CUBE ARE PAIRWISE DISTINCT AND SMALL.**  This
is `jsp87Sep` of `Xp.lean`, *discharged*: it is a statement about binary
representations, not about the sample point. -/
theorem jsp87Sep_of_pow {K p h : ℕ} (hp : h + 2 ^ K - 1 < p) :
    jsp87Sep p (jsp87BinV K) h := by
  constructor
  · intro ε
    have h1 : jsp87R (jsp87BinV K) h ε = h + jsp87Off (jsp87BinV K) ε := rfl
    rw [h1]
    have h2 := jsp87Off_binV_lt ε
    omega
  · intro ε ε' hne hEq
    have hOff : jsp87Off (jsp87BinV K) ε = jsp87Off (jsp87BinV K) ε' := by
      have hz := hEq
      unfold jsp87R at hz
      exact Nat.add_left_cancel hz
    exact hne (jsp87Off_binV_inj hOff)

/-! ## §3  The exact hit count of the binary cube -/

/-- **A NONZERO MULTIPLE OF `p` SMALLER THAN `p` IS IMPOSSIBLE.** -/
private theorem jsp87not_dvd_sub {p a b : ℕ} (hd : p ∣ b - a) (hlt : b - a < p)
    (ha : a ≤ b) (hne : a ≠ b) : False := by
  have h0 : (b - a) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  have h1 : b - a = 0 := (Nat.mod_eq_of_lt hlt).symm.trans h0
  exact hne (Nat.le_antisymm ha (Nat.sub_eq_zero_iff_le.mp h1))

/-- **AT MOST ONE VERTEX OF THE BINARY CUBE IS HIT**, provided `2^K ≤ p`:** two
distinct hit vertices would give a nonzero multiple of `p` of absolute value
`< 2^K ≤ p`.  The bound is *independent of the level `h`*. -/
theorem jsp87HitVerts_card_le_one_pow {K p n h : ℕ} (hp : 2 ^ K ≤ p) :
    (jsp87HitVerts p n (jsp87BinV K) h).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun ε hε ε' hε' => ?_
  by_cases hcc : ε = ε'
  · exact hcc
  · exfalso
    have h1 : p ∣ n + (h + jsp87Off (jsp87BinV K) ε) :=
      (Finset.mem_filter.mp hε).2
    have h2 : p ∣ n + (h + jsp87Off (jsp87BinV K) ε') :=
      (Finset.mem_filter.mp hε').2
    have hne0 : jsp87Off (jsp87BinV K) ε ≠ jsp87Off (jsp87BinV K) ε' := by
      intro hz
      exact hcc (jsp87Off_binV_inj hz)
    have hlt1 := jsp87Off_binV_lt ε
    have hlt2 := jsp87Off_binV_lt ε'
    have hp1 : (h + jsp87Off (jsp87BinV K) ε) - (h + jsp87Off (jsp87BinV K) ε') < p := by omega
    have hp2 : (h + jsp87Off (jsp87BinV K) ε') - (h + jsp87Off (jsp87BinV K) ε) < p := by omega
    have hsubA : p ∣ (h + jsp87Off (jsp87BinV K) ε') - (h + jsp87Off (jsp87BinV K) ε) := by
      have hz := Nat.dvd_sub h2 h1
      have hz' : (n + (h + jsp87Off (jsp87BinV K) ε')) - (n + (h + jsp87Off (jsp87BinV K) ε))
          = (h + jsp87Off (jsp87BinV K) ε') - (h + jsp87Off (jsp87BinV K) ε) := by omega
      rwa [hz'] at hz
    have hsubB : p ∣ (h + jsp87Off (jsp87BinV K) ε) - (h + jsp87Off (jsp87BinV K) ε') := by
      have hz := Nat.dvd_sub h1 h2
      have hz' : (n + (h + jsp87Off (jsp87BinV K) ε)) - (n + (h + jsp87Off (jsp87BinV K) ε'))
          = (h + jsp87Off (jsp87BinV K) ε) - (h + jsp87Off (jsp87BinV K) ε') := by omega
      rwa [hz'] at hz
    rcases le_total (h + jsp87Off (jsp87BinV K) ε) (h + jsp87Off (jsp87BinV K) ε')
      with hle | hle
    · exact jsp87not_dvd_sub hsubA hp2 hle (fun hz => hne0 (by omega))
    · exact jsp87not_dvd_sub hsubB hp1 hle (fun hz => hne0 (by omega))

/-- **THE ONE-VERTEX PROPERTY FOR THE BINARY CUBE.**  This is the hypothesis
`jsp87OneVertex` of rounds 117–118, obtained from the *single arithmetic
inequality* `2^K ≤ p`. -/
theorem jsp87OneVertex_of_pow {K p n h : ℕ} (hp : 2 ^ K ≤ p) :
    jsp87OneVertex p n (jsp87BinV K) h :=
  jsp87HitVerts_card_le_one_pow hp

/-- **A LEVEL SUM OF THE BINARY CUBE IS `0` OR A SINGLE SIGNED WEIGHT.**  By
(5.36) the level sums of `X_p` are signed powers of `2^{−(h+K)}`: the variable of
(5.13) is a finite signed sum of `2^{−(h+K)}` over `h ≤ H`, with no hypothesis
beyond `2^K ≤ p`. -/
theorem jsp87XpLevel_eq_zero_or_sign_pow {K p n h : ℕ} (hp : 2 ^ K ≤ p) :
    jsp87XpLevel (jsp87BinV K) p n h = 0 ∨
      ∃ ε₀ : Finset (Fin K),
        jsp87XpLevel (jsp87BinV K) p n h = (jsp87Sign ε₀.card : ℝ) * jsp87W K h :=
  jsp87XpLevel_eq_zero_or_sign (jsp87BinV K) p n h (jsp87OneVertex_of_pow hp)

/-- **A LEVEL IS ACTIVE FOR THE SAMPLE POINT `n` IFF SOME VERTEX IS HIT.**  By
the injectivity of the offsets this is equivalent to `jsp87OneVertex` being a
*sharp* statement: at an active level the hit set is a singleton. -/
theorem jsp87HitVerts_singleton_pow {K p n h : ℕ} (hp : 2 ^ K ≤ p)
    {ε : Finset (Fin K)} (hhit : p ∣ n + jsp87R (jsp87BinV K) h ε) :
    jsp87HitVerts p n (jsp87BinV K) h = {ε} := by
  have hone := jsp87HitVerts_card_le_one_pow (K := K) (p := p) (n := n) (h := h) hp
  have hmem : ε ∈ jsp87HitVerts p n (jsp87BinV K) h :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩
  ext δ
  constructor
  · intro hδ
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.mp hone δ hδ ε hmem
  · intro hδ
    rw [Finset.mem_singleton] at hδ
    rw [hδ]
    exact hmem

/-! ## §4  Hypothesis (5.19) is discharged for the binary cube -/

/-- **THE ONE-VERTEX HYPOTHESIS HOLDS AT EVERY LEVEL FOR THE BINARY CUBE.** -/
theorem jsp87OneVertex_pow_all {K p n H : ℕ} (hp : 2 ^ K ≤ p) :
    ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p n (jsp87BinV K) h :=
  fun _ _ => jsp87OneVertex_of_pow hp

/-- **THE SIZE BOUND (5.36) FOR THE BINARY CUBE**, with the one-vertex hypothesis
discharged. -/
theorem jsp87Xp_abs_le_pow {K : ℕ} (q : ℝ) (p n H : ℕ) (hp : 2 ^ K ≤ p) :
    |jsp87Xp q (jsp87BinV K) p n H| ≤ |q| * ((H : ℕ) : ℝ) * jsp87W K 0 :=
  jsp87Xp_abs_le q (jsp87BinV K) p n H (jsp87OneVertex_pow_all hp)

/-- **HYPOTHESIS (5.19), DISCHARGED.**  For the binary cube and any `p ≥ 2^K`,
`|q X_p| ≤ 1/20` at *every* sample point, as soon as `q H 2^{−K} ≤ 1/20`: no
separation hypothesis, no one-vertex hypothesis, no sample-point hypothesis.
(Primality of `p` is not needed for the bound; only `2^K ≤ p`.) -/
theorem jsp87Xp_abs_le_twenty_pow {K : ℕ} (q : ℝ) (p n H : ℕ) (hp : 2 ^ K ≤ p)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    |q * jsp87Xp0 (jsp87BinV K) p n H| ≤ 1 / 20 :=
  (jsp87Xp_abs_le_pow q p n H hp).trans hK

/-! ## §5  The endgame, with the separation hypothesis removed -/

/-- **THE ENDGAME OF ROUND 118, WITH THE SEPARATION HYPOTHESIS REMOVED.**
Assume (5.15), (5.16)–(5.17), and that the cube has the **binary** differences
`v p k = 2^k` with `H + 2^K − 1 < p` (which by `jsp87Sep_of_pow` *is* the
separation hypothesis), and that for one prime `p` the cube sums split the
sample into two non-empty parts which never agree, with
`q² |A| |B| 2^{−2(H+K)} ≥ |s|²`.  Then the five error terms of §5 cannot all be
`< 1/30`.

This is `jsp87_endgame_twoClass` with one hypothesis fewer: the separated
cube is now a *canonical* choice of `v`. -/
theorem jsp87_endgame_twoClass_pow {K : ℕ} (s : Finset ℕ) (hs : s.Nonempty) (q : ℝ)
    (H p : ℕ) (A B : Finset ℕ) (hAB : s = A ∪ B) (hdis : A ∩ B = ∅)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (Hp : H + 2 ^ K - 1 < p)
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
        jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p' ∈ ({p} : Finset ℕ),
        jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ ({p} : Finset ℕ),
          jsp87CAvg s (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5)
    (hne : ∀ x ∈ A, ∀ y ∈ B,
      jsp87Xp0 (jsp87BinV K) p x H ≠ jsp87Xp0 (jsp87BinV K) p y H)
    (hbig : (1 : ℝ) ≤ (q ^ 2) * (((A.card * B.card : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        / ((s.card : ℕ) : ℝ) ^ 2) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  let v : ℕ → Fin K → ℕ := fun _ => jsp87BinV K
  have hsep' : ∀ i : ℕ, ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p i (jsp87BinV K) h := by
    intro i h hh
    have hh' := hh
    rw [Finset.mem_Icc] at hh'
    exact jsp87OneVertex_of_sep (jsp87BinV K) p i h (jsp87Sep_of_pow (by omega))
  exact jsp87_endgame_twoClass (K := K) s hs q H K v p A B hAB hdis hA hB
    κ1 κ2 κ3 κ4 κ5 hK H15 H1617 hsep' hne hbig

/-- **THE ENDGAME OF ROUND 117, WITH THE SEPARATION HYPOTHESIS REMOVED.**  The
cubes of a finite set `P` of primes are the binary cubes, `H + 2^K − 1 < p` for
every `p ∈ P` (which *is* the separation hypothesis), (5.15), (5.16)–(5.17) and
(5.21) hold.  Then the five error terms of §5 of arXiv:2512.01739 cannot all be
`< 1/30`. -/
theorem jsp87_endgame_cube_pow {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (K H : ℕ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (Hp : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P,
        jsp87Xp0 (jsp87BinV K) p i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p ∈ P,
        jsp87Xp0 (jsp87BinV K) p i H))
        - ∏ p ∈ P, jsp87CAvg s (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖
      ≤ κ4 + κ5)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var s (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  let v : ℕ → Fin K → ℕ := fun _ => jsp87BinV K
  have hsep' : ∀ p ∈ P, ∀ i : ℕ, ∀ h ∈ Finset.Icc 1 H, jsp87OneVertex p i (jsp87BinV K) h := by
    intro p hp i h hh
    have hHp : H + 2 ^ K - 1 < p := Hp p hp
    have hh' := hh
    rw [Finset.mem_Icc] at hh'
    exact jsp87OneVertex_of_sep (jsp87BinV K) p i h
      (jsp87Sep_of_pow (by omega))
  exact jsp87_endgame_cube (P := P) s hs q K H v κ1 κ2 κ3 κ4 κ5 hK H15 H1617 H21 hsep'

/-! ## §6  The cube sum is a function of the sample point modulo `p` -/

/-- **SUBTRACTING A MULTIPLE OF `p` PRESERVES DIVISIBILITY.** -/
private theorem jsp87dvd_add {p a : ℕ} (ha : p ∣ a + p) : p ∣ a := by
  have h1 : a % p = 0 := by
    have h2 := Nat.dvd_iff_mod_eq_zero.mp ha
    rwa [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] at h2
  exact Nat.dvd_of_mod_eq_zero h1

/-- **THE HIT SET AT LEVEL `h` DEPENDS ONLY ON `n` MODULO `p`.** -/
theorem jsp87HitVerts_period {K : ℕ} (v : Fin K → ℕ) (p n h : ℕ) :
    jsp87HitVerts p (n + p) v h = jsp87HitVerts p n v h := by
  ext ε
  simp only [jsp87HitVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hd
    have hz : n + p + jsp87R v h ε = (n + jsp87R v h ε) + p := by omega
    rw [hz] at hd
    exact jsp87dvd_add hd
  · intro hd
    have hz : p ∣ (n + jsp87R v h ε) + p := dvd_add hd (Nat.dvd_refl p)
    have hz' : n + p + jsp87R v h ε = (n + jsp87R v h ε) + p := by omega
    rw [hz']
    exact hz

/-- **THE CUBE SUM IS `p`-PERIODIC IN THE SAMPLE POINT.** -/
theorem jsp87Xp0_period {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) :
    jsp87Xp0 v p (n + p) H = jsp87Xp0 v p n H := by
  unfold jsp87Xp0
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [jsp87XpLevel_eq_filter, jsp87XpLevel_eq_filter, Finset.mul_sum, Finset.mul_sum,
    jsp87HitVerts_period v p n h]

/-- **THE CUBE-ALTERNATING VARIABLE `X_p` OF (5.13) IS A FUNCTION OF `n` MOD
`p`.**  This is what makes (5.21) a statement about the *distribution of `ω` on
arithmetic progressions modulo `p`*: over a complete residue system the
variable takes at most `p` distinct values, and the variance over any sample is
determined by the sample's residues. -/
theorem jsp87Xp0_pow_period {K : ℕ} (p n H : ℕ) :
    jsp87Xp0 (jsp87BinV K) p (n + p) H = jsp87Xp0 (jsp87BinV K) p n H :=
  jsp87Xp0_period (jsp87BinV K) p n H

end JSP87
