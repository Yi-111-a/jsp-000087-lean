/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.SubwordComplexity

/-!
# JSP-000087, round 76 : Morse–Hedlund proper — the PLATEAU theorem

## The new attack family

Rounds 37–72 attacked the Erdős series `S = ∑' n, ω(n) 2^{-(n+1)}` from
thirty-five angles; round 73 introduced the **subword complexity** of its binary
expansion, and round 75 added the growth side (monotonicity, the linear-growth
criterion, and the machine-checked exclusion of every *pure* digit period
`t ≤ 1023`).

**Both of those rounds worked with a finite window.**  The complexity was always
`Finset.card ((Finset.range K).filter (…).image (fun N => …))`: the number of
distinct `n`-digit blocks among the first `K` positions.  That is a *lower bound*
on the quantity that matters, and one cannot take differences of it, iterate it,
or apply the pigeonhole principle to it.

This round introduces the complexity of the **infinite** word itself

```
jsp87Compl n = card { B < 2^n | B is read off the binary expansion somewhere }
```

as a `Finset` (`jsp87Fac n`), and proves the theorem that combinatorics on words
is *about*:

> **`jsp87_compl_succ_eq_imp_digitPeriodic`** — if the complexity does **not**
> grow between `n` and `n+1`, the digit string is eventually periodic, with an
> explicit period `t ≤ p(n)` and an explicit start point `M ≥ 1`.

This is the **plateau form of Morse–Hedlund**, and it is new to the tree in
three separate ways: the object is the infinite-word complexity (not a window
count); the hypothesis is an **equality** of two complexities (the tree had only
inequalities, all of them upper bounds); and the conclusion carries a
**quantitative bound on the period**, `t ≤ p(n)`, which is what makes the
theorem usable arithmetically.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87Fac`, `jsp87Compl` | **the new objects**: the `n`-digit blocks occurring in the binary expansion of `jsp87Series`, and their number |
| `jsp87_compl_zero`, `jsp87_compl_pos`, `jsp87_compl_le` | `p(0) = 1`, `1 ≤ p(n)`, `p(n) ≤ 2^n` |
| `jsp87_compl_le_window` | **every certified window count lower-bounds the true complexity** |
| `jsp87_blockNat_succ`, `jsp87_blockNat_dropLast`, `jsp87_blockNat_dropFirst` | the block arithmetic: `B M (n+1) = 2 B M n + d (M+n)`, `B M (n+1) / 2 = B M n`, `B M (n+1) % 2^n = B (M+1) n` |
| `jsp87_compl_mono'` | **MORSE–HEDLUND MONOTONICITY FOR THE TRUE COMPLEXITY** |
| `jsp87_compl_succ_le_two` | **`p(n+1) ≤ 2 p(n)`** — a binary alphabet has only two right extensions |
| `jsp87_blockNat_split'`, `jsp87_compl_mul` | **SUBMULTIPLICATIVITY** `p(n + m) ≤ p(n) · p(m)` |
| `jsp87_ext_inj` | **UNIQUENESS OF THE RIGHT EXTENSION AT A PLATEAU** |
| **`jsp87_compl_succ_eq_imp_digitPeriodic`** | **THE PLATEAU THEOREM**: `p(n+1) = p(n)` and `0 < n` give a digit period `t` with `0 < t ≤ p(n)` from an explicit start `M ≥ 1` |
| `jsp87Series_rational_of_compl_succ_eq` | a plateau certifies **rationality**, with an explicit value `S = k / (2^M (2^t − 1))` |
| `jsp87_compl_le_of_digitPeriodic`, `jsp87Series_rational_imp_compl_bounded` | a periodic tail bounds the complexity: `p(n) ≤ M + t` |
| `jsp87_compl_stabilize_of_digitPeriodic`, `jsp87Series_rational_imp_compl_bounded` | and then `p` is **eventually constant** — a rational value has a finite staircase |
| `jsp87_compl_ge_of_minimalPeriod` | a *least* period `t` forces `p(n) ≥ t` for `n ≥ t` (round 73 proved the window version) |
| `jsp87Series_irrational_imp_compl_succ_gt` | **irrationality forces STRICT growth** `p(n+1) ≥ p(n)+1` at every level — the tree had only weak monotonicity |
| **`jsp87Series_irrational_imp_compl_ge`** | hence irrationality forces **linear growth** `p(n) ≥ n + 1` at every level, unconditionally, for the true complexity |
| **`jsp87Series_irrational_iff_compl_unbounded`** | **irrationality `↔` unbounded complexity** — the converse half of round 73's criterion |
| **`jsp87Series_irrational_iff_compl_ge`** | **irrationality `↔` `p(n) ≥ n + 1` for every `n`** — a complete criterion, in `iff` form |
| `jsp87Series_rational_of_compl_le` | **a finite certificate of rationality**: one `n` with `p(n) ≤ n` exhibits a digit period |
| `jsp87_compl_ge_2025` | **machine-checked**: `p(n) ≥ 2025` for every `n ≥ 20` — round 73's certified prefix bounds the *true* complexity |
| **`jsp87_compl_succ_eq_imp_ge_1012`** | **a plateau at level `n` forces `p(n) ≥ 1012`**: its period is `≤ p(n)` and its pre-period `≤ p(n)+1`, while `p(20) ≥ 2025` |
| `jsp87_compl_succ_ne_of_le_nine`, `jsp87_compl_ge_succ_of_le_nine`, `jsp87_compl_ge_of_le_ten` | hence **the complexity grows strictly at each of the first ten levels** |
| `jsp87Series_rational_imp_compl_ge_period_plus_start` | a hypothetical rational value has pre-period + period `≥ 2025` |
| `jsp87Series_rational_imp_compl_window` | and its complexity is trapped in `[t, M + t]` once `n ≥ t` |

## What this round does NOT do

`jsp_000087_main` remains undeclared, and no weakened statement is emitted under
that name.  The plateau theorem, the strict-growth theorem and the two criteria
are *all* unconditional, and together they say

> `jsp87Series` is irrational **iff** the subword complexity of its binary
> expansion grows by at least one at every level, i.e.
> `Irrational jsp87Series ↔ ∀ n, n + 1 ≤ p(n)`.

The *right* side remains the single arithmetic input: it is the aperiodicity
statement of rounds 41/64/73, now expressed for the complexity of the infinite
word, and it is the content of the uniform prime-`k`-tuples hypothesis in the
published conditional result (Pratt, arXiv:2409.15185).  Mathlib has no notion
of the binary expansion of a real number and hence no notion of subword
complexity: `jsp87Fac`, `jsp87_compl_succ_eq_imp_digitPeriodic` and
`jsp87_compl_mul` are from scratch.
-/

namespace JSP87

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## 1. The complexity of the infinite word -/

/-- **THE SET OF `n`-DIGIT BLOCKS OF THE BINARY EXPANSION OF `jsp87Series`.**
A block occurs when it is read off the digit string at *some* place, so this is
the factor set of the infinite word, not of a finite prefix. -/
noncomputable def jsp87Fac (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ n)).filter (fun B => ∃ M, jsp87BlockNat M n = B)

/-- **THE SUBWORD COMPLEXITY OF THE BINARY EXPANSION OF `jsp87Series`**:
the number of distinct `n`-digit blocks occurring anywhere in it. -/
noncomputable def jsp87Compl (n : ℕ) : ℕ := (jsp87Fac n).card

theorem jsp87_fac_spec {n B : ℕ} :
    B ∈ jsp87Fac n ↔ B < 2 ^ n ∧ ∃ M, jsp87BlockNat M n = B := by
  classical
  simp only [jsp87Fac, Finset.mem_filter, Finset.mem_range]

theorem jsp87_fac_lt {n B : ℕ} (hB : B ∈ jsp87Fac n) : B < 2 ^ n :=
  (jsp87_fac_spec.mp hB).1

theorem jsp87_fac_witness {n B : ℕ} (hB : B ∈ jsp87Fac n) :
    ∃ M, jsp87BlockNat M n = B := (jsp87_fac_spec.mp hB).2

theorem jsp87_fac_intro {n M : ℕ} : jsp87BlockNat M n ∈ jsp87Fac n :=
  jsp87_fac_spec.mpr ⟨jsp87_blockNat_lt M n, M, rfl⟩

/-- `p(n) ≤ 2^n`: a block of `n` binary digits is a number below `2^n`. -/
theorem jsp87_compl_le (n : ℕ) : jsp87Compl n ≤ 2 ^ n := by
  unfold jsp87Compl
  calc Finset.card (jsp87Fac n) ≤ Finset.card (Finset.range (2 ^ n)) :=
        Finset.card_le_card fun _ h => Finset.mem_range.mpr (jsp87_fac_lt h)
    _ = 2 ^ n := Finset.card_range _

theorem jsp87_compl_pos (n : ℕ) : 1 ≤ jsp87Compl n := by
  unfold jsp87Compl
  have hne : (jsp87Fac n).Nonempty := ⟨jsp87BlockNat 0 n, jsp87_fac_intro⟩
  have h : 0 < Finset.card (jsp87Fac n) := Finset.card_pos.mpr hne
  omega

/-- **THE EMPTY BLOCK IS UNIQUE**: `p(0) = 1`.  The base point of every growth
argument in the round. -/
theorem jsp87_compl_zero : jsp87Compl 0 = 1 := by
  have hzero : ∀ M, jsp87BlockNat M 0 = 0 := by
    intro M
    have hz : ∑ j ∈ Finset.range 0, jsp87DigitNat (M + j) * 2 ^ (0 - 1 - j) = 0 :=
      Finset.sum_range_zero _
    unfold jsp87BlockNat
    exact hz
  have hmem : 0 ∈ jsp87Fac 0 := jsp87_fac_spec.mpr ⟨by simp, 0, hzero 0⟩
  have hsub : jsp87Fac 0 ⊆ Finset.range 1 := by
    intro B hB
    have hlt := jsp87_fac_lt hB
    rw [show (2 : ℕ) ^ 0 = 1 by norm_num] at hlt
    have hB0 : B = 0 := by omega
    simp [hB0]
  have hcard : Finset.card (jsp87Fac 0) ≤ 1 := by
    calc Finset.card (jsp87Fac 0) ≤ Finset.card (Finset.range 1) :=
          Finset.card_le_card hsub
      _ = 1 := Finset.card_range 1
  have hge : 1 ≤ Finset.card (jsp87Fac 0) := jsp87_compl_pos 0
  unfold jsp87Compl
  omega

/-- **A CERTIFIED WINDOW COUNTS A LOWER BOUND FOR THE TRUE COMPLEXITY.**
Every block occurring in a finite window occurs in the infinite word. -/
theorem jsp87_compl_le_window {n K : ℕ} :
    Finset.card ((Finset.range K).image (fun M => jsp87BlockNat M n)) ≤ jsp87Compl n := by
  unfold jsp87Compl
  refine Finset.card_le_card fun B hB => ?_
  obtain ⟨M, hM, hBM⟩ := Finset.mem_image.mp hB
  exact jsp87_fac_spec.mpr ⟨by rw [← hBM]; exact jsp87_blockNat_lt M n, M, hBM⟩

/-! ## 2. The arithmetic of blocks -/

/-- **APPENDING A DIGIT.**  The block at `M` of length `n+1` is twice the block
of length `n` plus the new digit: the convention reads a window with the *first*
digit as the most significant one, so a new digit enters at the bottom. -/
theorem jsp87_blockNat_succ (M n : ℕ) :
    jsp87BlockNat M (n + 1) = 2 * jsp87BlockNat M n + jsp87DigitNat (M + n) := by
  have hexp : ∀ j : ℕ, n + 1 - 1 - j = n - j := by intro j; omega
  have hkey : ∑ j ∈ Finset.range n, jsp87DigitNat (M + j) * 2 ^ (n - j)
      = 2 * ∑ j ∈ Finset.range n, jsp87DigitNat (M + j) * 2 ^ (n - 1 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have e : n - j = (n - 1 - j) + 1 := by omega
    rw [e, pow_succ]
    ring
  unfold jsp87BlockNat
  calc (∑ j ∈ Finset.range (n + 1), jsp87DigitNat (M + j) * 2 ^ (n - j))
      = (∑ j ∈ Finset.range n, jsp87DigitNat (M + j) * 2 ^ (n - j))
        + jsp87DigitNat (M + n) := by
          rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.mul_one]
    _ = 2 * (∑ j ∈ Finset.range n, jsp87DigitNat (M + j) * 2 ^ (n - 1 - j))
        + jsp87DigitNat (M + n) := by rw [hkey]

/-- **DROPPING THE LAST DIGIT.** -/
theorem jsp87_blockNat_dropLast (M n : ℕ) :
    jsp87BlockNat M (n + 1) / 2 = jsp87BlockNat M n := by
  have hlt : jsp87DigitNat (M + n) < 2 := by
    have h := jsp87_digitNat_le (M + n)
    omega
  rw [jsp87_blockNat_succ, Nat.mul_add_div (m := 2) (by norm_num), Nat.div_eq_of_lt hlt,
    Nat.add_zero]

/-- **DROPPING THE FIRST DIGIT.**  The `n` digits read from `M+1` are the residue
of the `(n+1)`-block at `M` modulo `2^n`. -/
theorem jsp87_blockNat_dropFirst (M n : ℕ) :
    jsp87BlockNat M (n + 1) % 2 ^ n = jsp87BlockNat (M + 1) n := by
  rw [jsp87_blockNat_split, Nat.mul_comm _ (2 ^ n), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (jsp87_blockNat_lt (M + 1) n)]

/-- **MORSE–HEDLUND MONOTONICITY FOR THE TRUE COMPLEXITY**: `p(n) ≤ p(n+1)`.
Every occurring `n`-block is the truncation `B / 2` of the `(n+1)`-block read at
the same place, so the truncation map is onto. -/
theorem jsp87_compl_mono' (n : ℕ) : jsp87Compl n ≤ jsp87Compl (n + 1) := by
  have hsub : jsp87Fac n ⊆ (jsp87Fac (n + 1)).image (fun B => B / 2) := by
    intro C hC
    obtain ⟨M, hM⟩ := jsp87_fac_witness hC
    refine Finset.mem_image.mpr ⟨jsp87BlockNat M (n + 1), jsp87_fac_intro, ?_⟩
    rw [jsp87_blockNat_dropLast, ← hM]
  unfold jsp87Compl
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le)

/-- **THE COMPLEXITY AT MOST DOUBLES.**  A binary alphabet has only two right
extensions of an `n`-block, and an `(n+1)`-block is the pair
(first `n` digits, last digit). -/
theorem jsp87_compl_succ_le_two (n : ℕ) : jsp87Compl (n + 1) ≤ 2 * jsp87Compl n := by
  have hsub : (jsp87Fac (n + 1)).image (fun B => (B / 2, B % 2))
      ⊆ jsp87Fac n ×ˢ Finset.range 2 := by
    intro z hz
    obtain ⟨B, hB, hz'⟩ := Finset.mem_image.mp hz
    obtain ⟨M, hM⟩ := jsp87_fac_witness hB
    have hlt : jsp87BlockNat M (n + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hmem : jsp87BlockNat M n ∈ jsp87Fac n :=
      jsp87_fac_spec.mpr ⟨jsp87_blockNat_lt M n, M, rfl⟩
    rw [← hz', ← hM, jsp87_blockNat_dropLast]
    exact Finset.mem_product.mpr ⟨hmem, Finset.mem_range.mpr hlt⟩
  have hinj : Function.Injective (fun B : ℕ => (B / 2, B % 2)) := by
    intro B B' h
    have e1 : B / 2 = B' / 2 := congrArg Prod.fst h
    have e2 : B % 2 = B' % 2 := congrArg Prod.snd h
    have k1 := (Nat.div_add_mod B 2).symm
    have k2 := (Nat.div_add_mod B' 2).symm
    rw [e1, e2] at k1
    omega
  unfold jsp87Compl
  calc Finset.card (jsp87Fac (n + 1))
      = ((jsp87Fac (n + 1)).image (fun B => (B / 2, B % 2))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (jsp87Fac n ×ˢ Finset.range 2).card := Finset.card_le_card hsub
    _ = jsp87Compl n * 2 := Finset.card_product _ _
    _ = 2 * jsp87Compl n := Nat.mul_comm _ _

/-- **SPLITTING A BLOCK IN THE MIDDLE.** -/
theorem jsp87_blockNat_split' (M n : ℕ) :
    ∀ m, jsp87BlockNat M (n + m) = 2 ^ m * jsp87BlockNat M n + jsp87BlockNat (M + n) m := by
  intro m
  induction m with
  | zero => simp [jsp87BlockNat]
  | succ m ih =>
      have heq1 : n + (m + 1) = (n + m) + 1 := by omega
      have h1 := jsp87_blockNat_succ M (n + m)
      have h2 := jsp87_blockNat_succ (M + n) m
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
        rw [pow_succ]
        ring
      rw [heq1, h1, ih, hpow, h2]
      simp only [Nat.add_assoc]
      ring

/-- **SUBMULTIPLICATIVITY OF THE COMPLEXITY**: `p(n + m) ≤ p(n) · p(m)`, because
an `(n+m)`-block is determined by its first `n` digits together with its last
`m` digits. -/
theorem jsp87_compl_mul (n m : ℕ) : jsp87Compl (n + m) ≤ jsp87Compl n * jsp87Compl m := by
  have hlt : ∀ M, jsp87BlockNat (M + n) m < 2 ^ m := fun M => jsp87_blockNat_lt (M + n) m
  have hpos : 0 < 2 ^ m := by positivity
  have hsub : (jsp87Fac (n + m)).image (fun B => (B / 2 ^ m, B % 2 ^ m))
      ⊆ jsp87Fac n ×ˢ jsp87Fac m := by
    intro z hz
    obtain ⟨B, hB, hz'⟩ := Finset.mem_image.mp hz
    obtain ⟨M, hM⟩ := jsp87_fac_witness hB
    have hmem1 : jsp87BlockNat M n ∈ jsp87Fac n :=
      jsp87_fac_spec.mpr ⟨jsp87_blockNat_lt M n, M, rfl⟩
    have hmem2 : jsp87BlockNat (M + n) m ∈ jsp87Fac m :=
      jsp87_fac_spec.mpr ⟨hlt M, M + n, rfl⟩
    rw [← hz', ← hM, jsp87_blockNat_split']
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [Nat.mul_add_div (m := 2 ^ m) hpos, Nat.div_eq_of_lt (hlt M), Nat.add_zero]
      exact hmem1
    · have hmod : (2 ^ m * jsp87BlockNat M n + jsp87BlockNat (M + n) m) % 2 ^ m
          = jsp87BlockNat (M + n) m := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlt M)]
      rw [hmod]
      exact hmem2
  have hinj : Function.Injective (fun B : ℕ => (B / 2 ^ m, B % 2 ^ m)) := by
    intro B B' h
    have e1 : B / 2 ^ m = B' / 2 ^ m := congrArg Prod.fst h
    have e2 : B % 2 ^ m = B' % 2 ^ m := congrArg Prod.snd h
    have k1 := (Nat.div_add_mod B (2 ^ m)).symm
    have k2 := (Nat.div_add_mod B' (2 ^ m)).symm
    rw [e1, e2] at k1
    omega
  unfold jsp87Compl
  calc Finset.card (jsp87Fac (n + m))
      = ((jsp87Fac (n + m)).image (fun B => (B / 2 ^ m, B % 2 ^ m))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (jsp87Fac n ×ˢ jsp87Fac m).card := Finset.card_le_card hsub
    _ = jsp87Compl n * jsp87Compl m := Finset.card_product _ _

/-! ## 3. The plateau theorem -/

private theorem mem_erase_iff {α : Type _} [DecidableEq α] (s : Finset α) (a x : α) :
    x ∈ s.erase a ↔ x ∈ s ∧ x ≠ a := by
  rw [Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2⟩

private theorem card_image_lt_of_ne {α : Type _} {β : Type _} [DecidableEq α] [DecidableEq β]
    {s : Finset α} (f : α → β) {a a' : α} (ha : a ∈ s) (ha' : a' ∈ s) (hne : a ≠ a')
    (heq : f a = f a') : (s.image f).card < s.card := by
  have hmem : a' ∈ s.erase a := (mem_erase_iff s a a').mpr ⟨ha', Ne.symm hne⟩
  have hsub : (s.erase a').image f = s.image f := by
    ext b
    constructor
    · intro hb
      obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hb
      have hx' : x ∈ s ∧ x ≠ a' := (mem_erase_iff s a' x).mp hx
      refine Finset.mem_image.mpr ⟨x, hx'.1, hfx⟩
    · intro hb
      obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hb
      by_cases hxa : x = a'
      · have hmem' : a ∈ s.erase a' := (mem_erase_iff s a' a).mpr ⟨ha, hne⟩
        rw [hxa] at hfx
        exact Finset.mem_image.mpr ⟨a, hmem', heq.trans hfx⟩
      · exact Finset.mem_image.mpr ⟨x, (mem_erase_iff s a' x).mpr ⟨hx, hxa⟩, hfx⟩
  have hcard : ((s.erase a').image f).card ≤ (s.erase a').card := Finset.card_image_le
  have herase : (s.erase a').card = s.card - 1 := Finset.card_erase_of_mem ha'
  have hs : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  rw [← hsub]
  omega

/-- **AT A PLATEAU THE RIGHT EXTENSION IS UNIQUE.**  If `p(n+1) = p(n)`, the
truncation map `B ↦ B / 2` is a bijection from the `(n+1)`-blocks onto the
`n`-blocks, so no `n`-block extends to two different `(n+1)`-blocks. -/
theorem jsp87_ext_inj {n : ℕ} (hcard : (jsp87Fac (n + 1)).card = (jsp87Fac n).card)
    {Y Y' : ℕ} (hY : Y ∈ jsp87Fac (n + 1)) (hY' : Y' ∈ jsp87Fac (n + 1))
    (heq : Y / 2 = Y' / 2) : Y = Y' := by
  by_contra hne
  have hlt : ((jsp87Fac (n + 1)).image (fun B => B / 2)).card < (jsp87Fac (n + 1)).card :=
    card_image_lt_of_ne (fun B : ℕ => B / 2) hY hY' hne heq
  have hsub : jsp87Fac n ⊆ (jsp87Fac (n + 1)).image (fun B => B / 2) := by
    intro z hz
    obtain ⟨M, hM⟩ := jsp87_fac_witness hz
    refine Finset.mem_image.mpr ⟨jsp87BlockNat M (n + 1), jsp87_fac_intro, ?_⟩
    rw [jsp87_blockNat_dropLast, ← hM]
  have hle : Finset.card (jsp87Fac n)
      ≤ ((jsp87Fac (n + 1)).image (fun B => B / 2)).card := Finset.card_le_card hsub
  omega

/-- **THE RIGHT EXTENSION OF AN OCCURRING `n`-BLOCK EXISTS.** -/
theorem jsp87_fac_exists_ext {n B : ℕ} (hB : B ∈ jsp87Fac n) :
    ∃ Y ∈ jsp87Fac (n + 1), Y / 2 = B := by
  obtain ⟨M, hM⟩ := jsp87_fac_witness hB
  refine ⟨jsp87BlockNat M (n + 1), jsp87_fac_intro, ?_⟩
  rw [jsp87_blockNat_dropLast, ← hM]

/-- **THE DE BRUIJN SHIFT IS DETERMINISTIC AT A PLATEAU.**  Two occurrences of
the same `n`-block are followed by occurrences of the same `n`-block: at a
plateau the right extension is unique, so reading one place further is a
*function* of the block.  This is the step that makes the sequence of blocks an
orbit, and hence eventually periodic. -/
theorem jsp87_blockNat_succ_inj' {n : ℕ}
    (hcard : (jsp87Fac (n + 1)).card = (jsp87Fac n).card) {M M' : ℕ}
    (h : jsp87BlockNat M n = jsp87BlockNat M' n) :
    jsp87BlockNat (M + 1) n = jsp87BlockNat (M' + 1) n := by
  have hdiv : jsp87BlockNat M (n + 1) / 2 = jsp87BlockNat M' (n + 1) / 2 := by
    rw [jsp87_blockNat_dropLast, jsp87_blockNat_dropLast, h]
  have heq : jsp87BlockNat M (n + 1) = jsp87BlockNat M' (n + 1) :=
    jsp87_ext_inj hcard jsp87_fac_intro jsp87_fac_intro hdiv
  rw [← jsp87_blockNat_dropFirst, ← jsp87_blockNat_dropFirst, heq]

/-- **THE PLATEAU THEOREM (Morse–Hedlund).**  If the subword complexity of the
binary expansion of `jsp87Series` fails to grow between `n` and `n+1`, the digit
string is eventually periodic, with an explicit period `t ≤ p(n)` and an
explicit start point `M ≥ 1`.

The proof is the classical one, from scratch: at a plateau the truncation map is
a bijection, so each `n`-block has a unique right extension
(`jsp87_ext_inj`), so the sequence of blocks is the orbit of a *function* on a
finite set, hence eventually periodic by pigeonhole; and the first digit of a
block is read off by a single division (round 73's `jsp87_blockNat_top`). -/
theorem jsp87_compl_succ_eq_imp_digitPeriodic {n : ℕ} (hn : 0 < n)
    (hcard : (jsp87Fac (n + 1)).card = (jsp87Fac n).card) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M ∧ M ≤ (jsp87Fac n).card + 1 ∧ t ≤ (jsp87Fac n).card ∧
      ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = (jsp87Fac n).card := ⟨_, rfl⟩
  -- pigeonhole: the blocks at the `p+1` places `1, …, p+1` are not all distinct
  have hex : ∃ i j : ℕ, i < p + 1 ∧ j < p + 1 ∧ i ≠ j ∧
      jsp87BlockNat (i + 1) n = jsp87BlockNat (j + 1) n := by
    by_contra hcon
    push Not at hcon
    have hinj : ∀ i ∈ Finset.range (p + 1), jsp87BlockNat (i + 1) n
        = jsp87BlockNat (i + 1) n := fun _ _ => rfl
    have hcard' : ((Finset.range (p + 1)).image (fun i => jsp87BlockNat (i + 1) n)).card
        = p + 1 := by
      rw [Finset.card_image_of_injOn (s := Finset.range (p + 1))
        (f := fun i => jsp87BlockNat (i + 1) n) ?_, Finset.card_range]
      intro a ha b hb hab
      by_contra hne
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      exact (hcon a b ha' hb' hne) hab
    have hsub : (Finset.range (p + 1)).image (fun i => jsp87BlockNat (i + 1) n)
        ⊆ jsp87Fac n := by
      intro B hB
      obtain ⟨i, hi, hBi⟩ := Finset.mem_image.mp hB
      rw [← hBi]
      exact jsp87_fac_intro
    have hle : ((Finset.range (p + 1)).image (fun i => jsp87BlockNat (i + 1) n)).card
        ≤ (jsp87Fac n).card := Finset.card_le_card hsub
    rw [hcard'] at hle
    omega
  obtain ⟨i, j, hil, hjl, hne, hblocks⟩ := hex
  obtain ⟨i, j, hil, hjl, hlt, hblocks⟩ :
      ∃ i j : ℕ, i < p + 1 ∧ j < p + 1 ∧ i < j ∧
        jsp87BlockNat (i + 1) n = jsp87BlockNat (j + 1) n := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨i, j, hil, hjl, hlt, hblocks⟩
    · exact ⟨j, i, hjl, hil, hgt, hblocks.symm⟩
  have hstep : ∀ k : ℕ, jsp87BlockNat (i + 1 + k) n = jsp87BlockNat (j + 1 + k) n := by
    intro k
    induction k with
    | zero => simpa using hblocks
    | succ k ih =>
        have h' := jsp87_blockNat_succ_inj' hcard ih
        simpa only [Nat.add_assoc] using h'
  refine ⟨j - i, i + 1, by omega, by omega, by omega, by omega, ?_⟩
  intro x hx
  have hblocks' := hstep (x - (i + 1))
  have hq := congrArg (fun z : ℕ => z / 2 ^ (n - 1)) hblocks'
  rw [jsp87_blockNat_top _ _ hn, jsp87_blockNat_top _ _ hn] at hq
  have hcast := congrArg (fun z : ℕ => (z : ℤ)) hq
  rw [jsp87_digitNat_cast, jsp87_digitNat_cast] at hcast
  have e1 : i + 1 + (x - (i + 1)) = x := by omega
  have e2 : j + 1 + (x - (i + 1)) = x + (j - i) := by omega
  rw [e1, e2] at hcast
  exact hcast.symm

/-! ## 4. A plateau makes the series rational -/

/-- **A PLATEAU CERTIFIES RATIONALITY, WITH AN EXPLICIT VALUE.**  A single
plateau of the subword complexity at a level `n ≥ 1` determines the Erdős series
completely: it is `k / (2^M (2^t − 1))` for the period `t ≤ p(n)` and the start
point `M` supplied by the plateau theorem, because a rational base-`2` expansion
is always a rational of that shape (round 46,
`jsp87Series_eq_div_of_digitPeriodic`). -/
theorem jsp87Series_rational_of_compl_succ_eq {n : ℕ} (hn : 0 < n)
    (hcard : jsp87Compl (n + 1) = jsp87Compl n) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87Series = (a : ℝ) / (b : ℝ) := by
  obtain ⟨t, M, ht, hM, hMb0, htp, hper⟩ := jsp87_compl_succ_eq_imp_digitPeriodic hn hcard
  obtain ⟨k, hk⟩ := jsp87Series_eq_div_of_digitPeriodic ht hM hper
  have h3 : 1 < 2 ^ t := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
    rw [pow_succ]
    nlinarith [Nat.two_pow_pos t]
  have h2 : (0 : ℕ) < 2 ^ t - 1 := by omega
  refine ⟨k, 2 ^ M * (2 ^ t - 1), Nat.mul_pos (by positivity) h2, ?_⟩
  have hA : (2 : ℝ) ^ M = ((2 ^ M : ℕ) : ℝ) := (Nat.cast_pow (α := ℝ) 2 M).symm
  have hB : (2 : ℝ) ^ t = ((2 ^ t : ℕ) : ℝ) := (Nat.cast_pow (α := ℝ) 2 t).symm
  have hC : ((2 ^ t - 1 : ℕ) : ℝ) = (2 : ℝ) ^ t - 1 := by
    rw [Nat.cast_sub (m := 1) (n := 2 ^ t) (by omega), ← hB]
    push_cast
    ring
  have hcast : ((2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1) : ℝ) = ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) := by
    calc (2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1)
        = ((2 ^ M : ℕ) : ℝ) * ((2 ^ t - 1 : ℕ) : ℝ) := by rw [hA, hC]
      _ = ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) := (Nat.cast_mul (α := ℝ) (2 ^ M) (2 ^ t - 1)).symm
  rw [hk, hcast]

/-! ## 5. A periodic tail bounds and then freezes the complexity -/

/-- **PERIODICITY BOUNDS THE TRUE COMPLEXITY.**  If the digit string is
eventually `t`-periodic from `M`, then `p(n) ≤ M + t` for every `n`: a block
starting before `M` is one of at most `M` exceptional blocks, and a block
starting at or after `M` is determined by the position modulo `t`.  This is
round 73's `jsp87_blockCompl_total_le` for the *infinite* word. -/
theorem jsp87_compl_le_of_digitPeriodic {M t n : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    jsp87Compl n ≤ M + t := by
  have hsub : jsp87Fac n ⊆ (Finset.range (M + t)).image (fun i => jsp87BlockNat i n) := by
    intro B hB
    obtain ⟨m, hm⟩ := jsp87_fac_witness hB
    by_cases hmM : M ≤ m
    · have h := jsp87_block_eq_of_congr (M := M) (t := t) (n := n) (N := m)
        (N' := M + (m - M) % t) ht hper hmM (by omega)
        (by rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt (Nat.mod_lt _ ht)])
      have hmlt : (m - M) % t < t := Nat.mod_lt _ ht
      have hnat : jsp87BlockNat m n = jsp87BlockNat (M + (m - M) % t) n := by
        have hz := congrArg Int.toNat h
        rw [(jsp87_blockNat_cast m n).symm,
          (jsp87_blockNat_cast (M + (m - M) % t) n).symm] at hz
        simpa using hz
      refine Finset.mem_image.mpr ⟨M + (m - M) % t, Finset.mem_range.mpr (by omega), ?_⟩
      rw [← hnat, hm]
    · exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), hm⟩
  unfold jsp87Compl
  calc Finset.card (jsp87Fac n)
      ≤ Finset.card ((Finset.range (M + t)).image (fun i => jsp87BlockNat i n)) :=
        Finset.card_le_card hsub
    _ ≤ Finset.card (Finset.range (M + t)) := Finset.card_image_le
    _ = M + t := Finset.card_range _

private theorem nat_mono_stabilizes {f : ℕ → ℕ} (hf : Monotone f) (C : ℕ)
    (hC : ∀ n, f n ≤ C) : ∃ K, ∀ n, K ≤ n → f n = f K := by
  have key : ∀ d : ℕ, ∀ g : ℕ → ℕ, (∀ a b : ℕ, a ≤ b → g a ≤ g b) → (∀ n, g n ≤ C) →
      C - g 0 ≤ d → ∃ K, ∀ n, K ≤ n → g n = g K := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro g hg hgc hd
      by_cases hex : ∃ n, g (n + 1) > g n
      · obtain ⟨n0, hn0⟩ := hex
        have hmono0 : g 0 < g (n0 + 1) := lt_of_le_of_lt (hg 0 n0 (by omega)) hn0
        have hbig : g (n0 + 1) ≤ C := hgc (n0 + 1)
        have hlt : C - g (n0 + 1) < d := by omega
        obtain ⟨K', hK'⟩ := ih (C - g (n0 + 1)) hlt (fun k => g (n0 + 1 + k))
          (by intro a b hab; exact hg (n0 + 1 + a) (n0 + 1 + b) (by omega)) (fun k => hgc _)
          le_rfl
        refine ⟨n0 + 1 + K', fun n hn => ?_⟩
        have hn1 : K' ≤ n - (n0 + 1) :=
          Nat.le_sub_of_add_le (show K' + (n0 + 1) ≤ n by omega)
        have hkey := hK' (n - (n0 + 1)) hn1
        have h2 : n0 + 1 + (n - (n0 + 1)) = n := by omega
        rw [h2] at hkey
        exact hkey
      · have hflat : ∀ n, g (n + 1) ≤ g n := fun n => Nat.le_of_not_gt (fun hh => hex ⟨n, hh⟩)
        refine ⟨0, fun n _ => ?_⟩
        have key2 : ∀ n, g n = g 0 := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            have hstep : g (n + 1) = g n := Nat.le_antisymm (hflat n) (hg n (n + 1) (by omega))
            rw [hstep]
            exact ih
        exact key2 n
  exact key (C - f 0) f (fun a b h => hf h) hC (by omega)

/-- **A PERIODIC TAIL FREEZES THE COMPLEXITY.**  The complexity is non-decreasing
(round 76) and bounded (above), so it is eventually *constant*: a rational value
of `jsp87Series` has a finite staircase as its complexity function. -/
theorem jsp87_compl_stabilize_of_digitPeriodic {M t : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    ∃ K, ∀ n, K ≤ n → jsp87Compl n = jsp87Compl K := by
  have hmono : Monotone jsp87Compl := by
    intro a b hab
    induction b with
    | zero =>
        have h : a = 0 := by omega
        subst h
        exact le_rfl
    | succ b ih =>
        rcases Nat.eq_or_lt_of_le hab with h | h
        · subst h
          exact le_rfl
        · exact le_trans (ih (show a ≤ b by omega)) (jsp87_compl_mono' b)
  refine nat_mono_stabilizes hmono (M + t)
    (fun n => jsp87_compl_le_of_digitPeriodic ht hper)

/-- **A HYPOTHETICAL RATIONAL VALUE HAS BOUNDED, EVENTUALLY CONSTANT COMPLEXITY,
WITH THE BOUND EXHIBITED.** -/
theorem jsp87Series_rational_imp_compl_bounded {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M ∧ (∀ n, jsp87Compl n ≤ M + t) ∧
      (∃ K, ∀ n, K ≤ n → jsp87Compl n = jsp87Compl K) := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  exact ⟨t, M, ht, hM, fun n => jsp87_compl_le_of_digitPeriodic ht hper,
    jsp87_compl_stabilize_of_digitPeriodic ht hper⟩

/-- **A LEAST PERIOD IS A LOWER BOUND FOR THE COMPLEXITY.**  If `t` is the least
eventual period from `M`, the `t` blocks read at `M, …, M+t−1` are pairwise
distinct (round 73, `jsp87_minimalPeriod_blocks_distinct`), so `p(n) ≥ t` for
every `n ≥ t` — the infinite-word form. -/
theorem jsp87_compl_ge_of_minimalPeriod {M t n : ℕ} (ht : 0 < t) (htn : t ≤ n) (_hM : 1 ≤ M)
    (hmin : ∀ u : ℕ, 0 < u → (∀ x : ℕ, M ≤ x → jsp87Digit (x + u) = jsp87Digit x) → t ≤ u)
    (hper : ∀ x : ℕ, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    t ≤ jsp87Compl n := by
  have hinj : ∀ ⦃a b : ℕ⦄, a ∈ Finset.range t → b ∈ Finset.range t →
      jsp87BlockNat (M + a) n = jsp87BlockNat (M + b) n → a = b := by
    intro a b ha hb hab
    have hat : a < t := Finset.mem_range.mp ha
    have hbt : b < t := Finset.mem_range.mp hb
    by_contra hne
    have hz : jsp87DigitBlock (M + a) n = jsp87DigitBlock (M + b) n := by
      have h1 := congrArg (fun z : ℕ => (z : ℤ)) hab
      rwa [jsp87_blockNat_cast, jsp87_blockNat_cast] at h1
    have h := jsp87_minimalPeriod_blocks_distinct (M := M) (t := t) (n := n) (i := a) (j := b)
      ht htn _hM hmin hper hat hbt hz
    exact hne h
  have hsub : (Finset.range t).image (fun i => jsp87BlockNat (M + i) n) ⊆ jsp87Fac n := by
    intro B hB
    obtain ⟨i, hi, hBi⟩ := Finset.mem_image.mp hB
    rw [← hBi]
    exact jsp87_fac_intro
  unfold jsp87Compl
  have h1 := Finset.card_le_card hsub
  have h2 : Finset.card ((Finset.range t).image (fun i => jsp87BlockNat (M + i) n)) = t := by
    rw [Finset.card_image_of_injOn (s := Finset.range t)
      (f := fun i => jsp87BlockNat (M + i) n) ?_, Finset.card_range]
    intro a ha b hb hab
    exact hinj ha hb hab
  omega

/-- **A ONE-DIGIT BLOCK IS THE DIGIT ITSELF.** -/
theorem jsp87_blockNat_one (m : ℕ) : jsp87BlockNat m 1 = jsp87DigitNat m := by
  simp [jsp87BlockNat]

/-- **TWO DISTINCT DIGITS GIVE `p(1) ≥ 2`.** -/
theorem jsp87_compl_one_ge_two {M : ℕ} (hne : jsp87DigitNat 1 ≠ jsp87DigitNat M) :
    2 ≤ jsp87Compl 1 := by
  have hmem : jsp87BlockNat 1 1 ∈ jsp87Fac 1 := jsp87_fac_intro
  have hmem' : jsp87BlockNat M 1 ∈ jsp87Fac 1 := jsp87_fac_intro
  have hne' : jsp87BlockNat 1 1 ≠ jsp87BlockNat M 1 := by
    rw [jsp87_blockNat_one, jsp87_blockNat_one]
    exact hne
  have hsub : ({jsp87BlockNat 1 1, jsp87BlockNat M 1} : Finset ℕ) ⊆ jsp87Fac 1 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hmem
    · exact hmem'
  have htwo : Finset.card ({jsp87BlockNat 1 1, jsp87BlockNat M 1} : Finset ℕ) = 2 := by
    simp [hne']
  unfold jsp87Compl
  calc 2 = Finset.card ({jsp87BlockNat 1 1, jsp87BlockNat M 1} : Finset ℕ) := htwo.symm
    _ ≤ Finset.card (jsp87Fac 1) := Finset.card_le_card hsub

/-- **THE BINARY EXPANSION OF `jsp87Series` USES BOTH DIGITS**, so its
one-digit complexity is at least `2`.  Machine-checked from round 47's
`jsp87_digit_one` (`d 1 = 1`) and round 69's `jsp87_digit_window_4` (`d 4 = 0`). -/
theorem jsp87_compl_one : 2 ≤ jsp87Compl 1 := by
  have h1 : jsp87DigitNat 1 = 1 := by
    have hz := congrArg (fun z : ℤ => z.toNat) jsp87_digit_one
    have e1 : (jsp87Digit 1).toNat = jsp87DigitNat 1 := by
      rw [← jsp87_digitNat_cast, Int.toNat_natCast]
    rw [e1] at hz
    simpa using hz
  have h4 : jsp87DigitNat 4 = 0 := by
    have hz := congrArg (fun z : ℤ => z.toNat) jsp87_digit_window_4.1
    have e4 : (jsp87Digit 4).toNat = jsp87DigitNat 4 := by
      rw [← jsp87_digitNat_cast, Int.toNat_natCast]
    rw [e4] at hz
    simpa using hz
  have hne : jsp87DigitNat 1 ≠ jsp87DigitNat 4 := by
    rw [h1, h4]
    norm_num
  exact jsp87_compl_one_ge_two hne

private theorem cast_rat_div (a : ℤ) (b : ℕ) :
    (((a : ℚ) / b : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by
  rw [Rat.cast_div]
  norm_cast

/-! ## 6. Irrationality forces strict growth; the two complete criteria -/

/-- **A RATIONAL VALUE CANNOT HAVE A PLATEAU.**  The contrapositive of
`jsp87Series_rational_of_compl_succ_eq`: irrationality forces the complexity to
grow by at least one at every level.  Round 75 proved only the weak monotonicity
`p(n) ≤ p(n+1)`; this is the strict half of Morse–Hedlund, and it is new. -/
theorem jsp87Series_irrational_imp_compl_succ_gt :
    Irrational jsp87Series →
      ∀ n, 1 ≤ n → jsp87Compl n + 1 ≤ jsp87Compl (n + 1) := by
  intro hirr n hn
  by_contra hcon
  have hcard : jsp87Compl (n + 1) = jsp87Compl n := by
    have hle := jsp87_compl_mono' n
    omega
  obtain ⟨a, b, hb, hrat⟩ := jsp87Series_rational_of_compl_succ_eq hn hcard
  exact hirr (by
    show jsp87Series ∈ Set.range ((↑) : ℚ → ℝ)
    refine ⟨(a : ℚ) / b, ?_⟩
    rw [cast_rat_div a b]
    exact hrat.symm)

/-- **AND HENCE LINEAR GROWTH**: `p(n) ≥ n + 1` at every level, for the *true*
complexity of the binary expansion of the Erdős series.  This is the
Morse–Hedlund lower bound, proved unconditionally and in the `ℕ`-valued
(infinite-word) notation. -/
theorem jsp87Series_irrational_imp_compl_ge :
    Irrational jsp87Series → ∀ n, n + 1 ≤ jsp87Compl n := by
  intro hirr n
  induction n with
  | zero =>
      rw [jsp87_compl_zero]
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simpa using jsp87_compl_one
      · have h := jsp87Series_irrational_imp_compl_succ_gt hirr k hk
        omega

/-- **A SINGLE SMALL VALUE OF THE COMPLEXITY CERTIFIES RATIONALITY.**  If
`p(n) ≤ n` at even one level, the series is rational — a *finite* certificate,
because `p` is a definite number.  This is the contrapositive of the linear
growth theorem. -/
theorem jsp87Series_rational_of_compl_le {n : ℕ} (h : jsp87Compl n ≤ n) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87Series = (a : ℝ) / (b : ℝ) := by
  by_cases hex : ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87Series = (a : ℝ) / (b : ℝ)
  · obtain ⟨a, b, hb, heq⟩ := hex
    exact ⟨a, b, hb, heq⟩
  · exfalso
    have hirr : Irrational jsp87Series := by
      show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
      rintro ⟨q, hq⟩
      exact hex ⟨q.num, q.den, Rat.den_pos q, by rw [← hq, Rat.cast_def]⟩
    have hle := jsp87Series_irrational_imp_compl_ge hirr n
    omega

/-- **A UNIFORMLY SMALL COMPLEXITY CERTIFIES RATIONALITY.** -/
theorem jsp87Series_rational_of_compl_bounded {C : ℕ} (hC : ∀ n, jsp87Compl n ≤ C) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87Series = (a : ℝ) / (b : ℝ) :=
  jsp87Series_rational_of_compl_le (hC C)

/-- **CRITERION I — IRRATIONALITY `↔` UNBOUNDED COMPLEXITY.**  Round 73 proved
one half (`jsp87Series_irrational_of_compl_gt_period`); the other half is the
periodicity bound `p(n) ≤ M + t`. -/
theorem jsp87Series_irrational_iff_compl_unbounded :
    Irrational jsp87Series ↔ ¬ (∃ C : ℕ, ∀ n, jsp87Compl n ≤ C) := by
  constructor
  · intro hirr ⟨C, hC⟩
    obtain ⟨a, b, hb, hrat⟩ := jsp87Series_rational_of_compl_bounded hC
    exact hirr (by
      show jsp87Series ∈ Set.range ((↑) : ℚ → ℝ)
      refine ⟨(a : ℚ) / b, ?_⟩
      rw [cast_rat_div a b]
      exact hrat.symm)
  · intro h
    show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
    rintro ⟨q, hq⟩
    obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic (b := q.den)
      (Rat.den_pos q) (by rw [← hq, Rat.cast_def])
    exact h ⟨M + t, fun n => jsp87_compl_le_of_digitPeriodic ht hper⟩

/-- **CRITERION II — IRRATIONALITY `↔` LINEAR GROWTH OF THE COMPLEXITY.**
`Irrational jsp87Series ↔ ∀ n, n + 1 ≤ p(n)`, i.e. the subword complexity of the
binary expansion of the Erdős series grows by at least one at *every* level.  The
forward implication is the unconditional theorem
`jsp87Series_irrational_imp_compl_ge` (plateau theorem + monotonicity); the
converse is the periodicity bound. -/
theorem jsp87Series_irrational_iff_compl_ge :
    Irrational jsp87Series ↔ ∀ n, n + 1 ≤ jsp87Compl n := by
  constructor
  · exact jsp87Series_irrational_imp_compl_ge
  · intro h
    show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
    rintro ⟨q, hq⟩
    obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic (b := q.den)
      (Rat.den_pos q) (by rw [← hq, Rat.cast_def])
    have hle' : jsp87Compl (M + t) ≤ M + t := jsp87_compl_le_of_digitPeriodic ht hper
    have hge : M + t + 1 ≤ jsp87Compl (M + t) := h (M + t)
    omega

/-! ## 7. Machine-checked instances: the complexity below the certified
prefix -/

/-- **THE CERTIFIED PREFIX BOUNDS THE TRUE COMPLEXITY FROM BELOW.**  Round 73
computed `2025` distinct `20`-digit blocks among the first `2029` positions of
the certified expansion; every one of them occurs in the infinite word, and the
complexity is non-decreasing, so `p(n) ≥ 2025` for every `n ≥ 20`. -/
theorem jsp87_compl_ge_2025 {n : ℕ} (hn : 20 ≤ n) : 2025 ≤ jsp87Compl n := by
  have h20 := jsp87_compl_le_window (n := 20) (K := 2029)
  have h20' : 2025 ≤ jsp87Compl 20 := by
    rw [jsp87BlockCompl_20] at h20
    exact h20
  have hmono : jsp87Compl 20 ≤ jsp87Compl n := by
    refine Nat.le_induction (P := fun b _ => jsp87Compl 20 ≤ jsp87Compl b) ?_ ?_ n hn
    · exact le_rfl
    · intro b _ ih
      exact le_trans ih (jsp87_compl_mono' b)
  exact le_trans h20' hmono

/-- **A PLATEAU AT LEVEL `n` FORCES `p(n) ≥ 1012`.**  The plateau theorem gives a
period `t ≤ p(n)` valid from a start point `M ≤ p(n) + 1`; a periodic tail bounds
the complexity by `M + t`, while the certified prefix forces `p(20) ≥ 2025`.  So
`2025 ≤ M + t ≤ 2 p(n) + 1`.  This is the quantitative content of the plateau
theorem, and it is the reason a low-level plateau is arithmetically impossible. -/
theorem jsp87_compl_succ_eq_imp_ge_1012 {n : ℕ} (hn : 0 < n)
    (hcard : jsp87Compl (n + 1) = jsp87Compl n) : 1012 ≤ jsp87Compl n := by
  obtain ⟨t, M, ht, hM, hMb0, htp, hper⟩ := jsp87_compl_succ_eq_imp_digitPeriodic hn hcard
  have hle : jsp87Compl 20 ≤ M + t := jsp87_compl_le_of_digitPeriodic ht hper
  have hcert : 2025 ≤ jsp87Compl 20 := jsp87_compl_ge_2025 (by omega)
  have hMb : M ≤ (jsp87Fac n).card + 1 := hMb0
  have hsum : M + t ≤ (jsp87Fac n).card + 1 + (jsp87Fac n).card := by omega
  have h2 : 2025 ≤ 2 * (jsp87Fac n).card + 1 := by omega
  have hcard : 1012 ≤ (jsp87Fac n).card := by omega
  rwa [show jsp87Compl n = (jsp87Fac n).card from rfl]

/-- **NO PLATEAU BELOW LEVEL `10`.**  Since `p(n) ≤ 2^n ≤ 512 < 1012` for
`n ≤ 9`, the complexity strictly grows between `n` and `n+1` for every
`n ≤ 9`.  Machine-checked, and derived from the certified prefix. -/
theorem jsp87_compl_succ_ne_of_le_nine {n : ℕ} (hn : n ≤ 9) :
    jsp87Compl (n + 1) ≠ jsp87Compl n := by
  intro hcard
  rcases Nat.eq_zero_or_pos n with hz | hz
  · -- at level `0` the complexity is `1`, but the expansion uses both digits
    subst hz
    have h1 : 2 ≤ jsp87Compl 1 := jsp87_compl_one
    have h2 : jsp87Compl 1 = 1 := by rw [hcard, jsp87_compl_zero]
    omega
  · have h1 : 1012 ≤ jsp87Compl n := jsp87_compl_succ_eq_imp_ge_1012 hz hcard
    have h2 : jsp87Compl n ≤ 2 ^ n := jsp87_compl_le n
    have h3 : 2 ^ n ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : (2 : ℕ) ^ 9 = 512 := by norm_num
    omega

/-- **STRICT GROWTH AT THE FIRST TEN LEVELS**, in the quantitative form. -/
theorem jsp87_compl_ge_succ_of_le_nine {n : ℕ} (hn : n ≤ 9) :
    jsp87Compl n + 1 ≤ jsp87Compl (n + 1) := by
  have hne : jsp87Compl (n + 1) ≠ jsp87Compl n := jsp87_compl_succ_ne_of_le_nine hn
  have hlt : jsp87Compl n < jsp87Compl (n + 1) :=
    Nat.lt_of_le_of_ne (jsp87_compl_mono' n) (Ne.symm hne)
  omega

/-- **HENCE `p(n) ≥ n + 1` FOR EVERY `n ≤ 10`.**  A small unconditional piece of
the linear-growth criterion, obtained from the certified prefix. -/

theorem jsp87_compl_ge_of_le_ten {n : ℕ} (hn : n ≤ 10) : n + 1 ≤ jsp87Compl n := by
  induction n with
  | zero =>
      rw [jsp87_compl_zero]
  | succ k ih =>
      have hk9 : k ≤ 9 := by omega
      have h1 : k + 1 ≤ jsp87Compl k := by
        rcases Nat.eq_zero_or_pos k with hz | hz
        · subst hz
          rw [jsp87_compl_zero]
        · exact ih (by omega)
      have h2 := jsp87_compl_ge_succ_of_le_nine hk9
      omega

/-- **A HYPOTHETICAL RATIONAL VALUE HAS PRE-PERIOD PLUS PERIOD AT LEAST `2025`.**
Its digit string is eventually `t`-periodic from `M ≥ 1`, that bound is
`p(n) ≤ M + t`, and the certified prefix forces `p(20) ≥ 2025`. -/
theorem jsp87Series_rational_imp_compl_ge_period_plus_start {a : ℤ} {b : ℕ} (_hb : 0 < b)
    (_h : jsp87Series = (a : ℝ) / (b : ℝ)) {t M : ℕ} (ht : 0 < t) (_hM : 1 ≤ M)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) : 2025 ≤ M + t := by
  have hle : jsp87Compl 20 ≤ M + t := jsp87_compl_le_of_digitPeriodic ht hper
  have hcert : 2025 ≤ jsp87Compl 20 := jsp87_compl_ge_2025 (by omega)
  omega

/-- **AND THE LEAST PERIOD IS A LOWER BOUND FOR THE COMPLEXITY, TOO.**  If `t`
is the least eventual period from `M`, then `t ≤ p(n) ≤ M + t` for every
`n ≥ t` — the complexity of a rational value is trapped in a window of width
`M` at the two ends. -/
theorem jsp87Series_rational_imp_compl_window {a : ℤ} {b : ℕ} (_hb : 0 < b)
    (_h : jsp87Series = (a : ℝ) / (b : ℝ)) {t M n : ℕ} (ht : 0 < t) (htn : t ≤ n) (hM : 1 ≤ M)
    (hmin : ∀ u : ℕ, 0 < u → (∀ x : ℕ, M ≤ x → jsp87Digit (x + u) = jsp87Digit x) → t ≤ u)
    (hper : ∀ x : ℕ, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    t ≤ jsp87Compl n ∧ jsp87Compl n ≤ M + t :=
  ⟨jsp87_compl_ge_of_minimalPeriod ht htn hM hmin hper,
    jsp87_compl_le_of_digitPeriodic ht hper⟩

end JSP87
