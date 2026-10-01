/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Effective

/-!
# JSP-000087, round 73 : the *subword complexity* of the binary expansion

## The new attack family

Rounds 37–72 attacked the Erdős series `S = ∑' n, ω(n) 2^{-(n+1)}` through
thirty-three different angles.  Every one of them asked what rationality would
*force*: a frozen carry, a periodic digit string (`jsp87_digit_eventuallyPeriodic`),
a constant `t`-block along the period (`jsp87_digitBlock_shift`), a Mersenne
divisibility (`jsp87_digitBlock_dvd_reduced_mer`), an escaping denominator
(`jsp87_rational_imp_lambertTail_den_escape`), and — in round 71 — how many
*digits* can be certified from a finite window.

**Not one of them ever asked how many distinct `n`-digit blocks the expansion
contains.**  That is the classical *subword complexity* `p(n)` of a word, and
it is the sharpest invariant of eventual periodicity:

* a word that is eventually periodic with period `t` has `p(n) ≤ t` for every
  `n` (`jsp87_blockCompl_le_period`);
* a word whose *least* eventual period is `t` has `p(n) = t` for every
  `n ≥ t` (`jsp87_minimalPeriod_blocks_distinct`).

So unbounded subword complexity is an independent aperiodicity criterion, and —
this is the point of the round — **the complexity is bounded by the denominator
of a rational value**, which turns the finite, computable complexity of round 71's
certified prefix into a *quantitative* statement about a hypothetical answer.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87_block_eq_of_digits_eq` | blocks agree when the digits agree |
| `jsp87_blockNat_split`, `jsp87_blockNat_top` | a block splits as `d N · 2^{n−1} + (the rest)`, so **the first digit of a block is read off by a single division** |
| **`jsp87_block_inj`** | **THE BLOCK DETERMINES THE DIGITS**: `B M n = B M' n` forces `d (M+j) = d (M'+j)` for all `j < n` |
| `jsp87_digit_eq_of_mod` | **THE PERIODIC TAIL IS A WORD ON `ℤ/tℤ`**: past the pre-period the digit at `m` depends only on `m` modulo `t` |
| **`jsp87_blockCompl_le_period`** | **THE COMPLEXITY–PERIOD THEOREM**: an eventually `t`-periodic digit string has at most `t` distinct `n`-digit blocks |
| **`jsp87_blockCompl_total_le`** | and at most `M + t` distinct blocks over *all* positions `N < K`, `M` being the start of the period |
| **`jsp87_minimalPeriod_blocks_distinct`** | **THE COMPLEXITY STABILISES**: for a *least* eventual period `t` and every `n ≥ t` the `t` blocks at `M, …, M+t−1` are pairwise distinct — with `jsp87_blockCompl_le_period` this is `p(n) = t` |
| **`jsp87Series_irrational_of_compl_gt_period`** | **A NEW IRRATIONALITY CRITERION**: unbounded subword complexity of the binary expansion implies irrationality |
| **`jsp87_blockCompl_le_denominator`** | **THE COMPLEXITY–DENOMINATOR THEOREM**: if `S = a/b` with `b > 0` then the binary expansion of `S` has subword complexity at most `b`.  Mathlib has no statement whatsoever about the binary expansion of a real number, hence no statement of this kind |
| **`jsp87Prefix2048`, `jsp87Series_floor_2048`, `jsp87DigitBlock_zero_2048`** | **THE FIRST `2048` BINARY DIGITS OF THE ERDŐS SERIES, CERTIFIED** — round 71 certified `64` |
| **`jsp87Prefix_2048`, `jsp87Prefix2048`** | the **first `2048` binary digits of the Erdős series, as a natural number** (round 71 certified `64`) |
| **`jsp87_subword_eq_block`, `jsp87Subword`** | **the prefix–block identity**: a certified prefix of length `L` determines every block, `B N n = (X / 2^{L−N−n}) mod 2^n`
| **`jsp87Compl_20`, `jsp87Compl_24`, `jsp87BlockCompl_20`, `jsp87DigitBlockCompl_20`** | **the certified subword complexity is `2025`** (for `n = 20` and for `n = 24`), by direct computation
| **`jsp87Series_rational_imp_denominator_ge_2025`** | **a hypothetical rational value of `S` has denominator `≥ 2025`** — round 71 could only prove `≥ 512` |

## What this round does NOT do

`jsp_000087_main` remains undeclared.  Unbounded subword complexity of the
binary expansion is *not* known unconditionally: ruling it out for every `b` is
the same arithmetic content as the aperiodicity of the digits, namely the
uniform prime-`k`-tuples hypothesis in the published conditional result
(Pratt, arXiv:2409.15185).  What this round delivers is a new *quantitative*
statement — the complexity is bounded by the denominator — together with a
`2048`-digit certified prefix and the machine-checked value `2025` of its
complexity.
-/

namespace JSP87

open Filter

/-! ## 1. Blocks: agreement, and the block determines the digits -/

/-- **AGREEMENT OF DIGITS GIVES AGREEMENT OF BLOCKS.** -/
theorem jsp87_block_eq_of_digits_eq {M M' n : ℕ}
    (h : ∀ j, j < n → jsp87Digit (M + j) = jsp87Digit (M' + j)) :
    jsp87DigitBlock M n = jsp87DigitBlock M' n := by
  unfold jsp87DigitBlock
  exact Finset.sum_congr rfl fun j _hj => by rw [h j (Finset.mem_range.mp _hj)]

/-- **THE DIGIT AS A NATURAL NUMBER.** -/
noncomputable def jsp87DigitNat (N : ℕ) : ℕ := (jsp87Digit N).toNat

theorem jsp87_digitNat_le (N : ℕ) : jsp87DigitNat N ≤ 1 := by
  rcases jsp87Digit_mem N with h0 | h1
  · rw [jsp87DigitNat, h0]; norm_num
  · rw [jsp87DigitNat, h1]; norm_num

theorem jsp87_digitNat_cast (N : ℕ) : (jsp87DigitNat N : ℤ) = jsp87Digit N := by
  rcases jsp87Digit_mem N with h0 | h1
  · rw [jsp87DigitNat, h0, Int.toNat_of_nonneg (by norm_num)]
  · rw [jsp87DigitNat, h1, Int.toNat_of_nonneg (by norm_num)]

/-- **THE BLOCK AS A NATURAL NUMBER.** -/
noncomputable def jsp87BlockNat (M n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, jsp87DigitNat (M + j) * 2 ^ (n - 1 - j)

theorem jsp87_blockNat_cast (M n : ℕ) : (jsp87BlockNat M n : ℤ) = jsp87DigitBlock M n := by
  have hkey : ∀ (u v : ℕ), ((u * v : ℕ) : ℤ) = (u : ℤ) * (v : ℤ) := by
    intro u v
    norm_cast
  unfold jsp87BlockNat jsp87DigitBlock
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _hj => ?_
  rw [hkey, jsp87_digitNat_cast]
  push_cast
  rfl

theorem jsp87_blockNat_lt (M n : ℕ) : jsp87BlockNat M n < 2 ^ n := by
  have h := jsp87_digitBlock_bounds M n
  have h' : (jsp87BlockNat M n : ℤ) < (2 ^ n : ℤ) := by rw [jsp87_blockNat_cast]; exact h.2
  exact_mod_cast h'

/-- **A BLOCK SPLITS OFF ITS FIRST DIGIT.** -/
theorem jsp87_blockNat_split (M n : ℕ) :
    jsp87BlockNat M (n + 1) = jsp87BlockNat (M + 1) n + jsp87DigitNat M * 2 ^ n := by
  unfold jsp87BlockNat
  have hexp : ∀ j : ℕ, ((n + 1) - 1 - j) = (n - j) := by intro j; omega
  simp_rw [hexp]
  have hstep : (∑ j ∈ Finset.range (n + 1), jsp87DigitNat (M + j) * 2 ^ (n - j))
      = (∑ k ∈ Finset.range n, jsp87DigitNat (M + (k + 1)) * 2 ^ (n - (k + 1)))
        + jsp87DigitNat M * 2 ^ n := by
    rw [Finset.sum_range_succ']
    have hlast : jsp87DigitNat (M + 0) * 2 ^ (n - 0) = jsp87DigitNat M * 2 ^ n := by
      congr 2
    rw [hlast]
  rw [hstep]
  have hmain : (∑ k ∈ Finset.range n, jsp87DigitNat (M + (k + 1)) * 2 ^ (n - (k + 1)))
      = (∑ j ∈ Finset.range n, jsp87DigitNat (M + 1 + j) * 2 ^ (n - 1 - j)) := by
    refine Finset.sum_congr rfl fun k _hk => ?_
    congr 2
    · have h1 : M + (k + 1) = (M + 1) + k := by omega
      rw [h1]
    · have hk : k < n := Finset.mem_range.mp _hk
      omega
  rw [hmain]

/-- **THE FIRST DIGIT OF A BLOCK, READ OFF BY A DIVISION.**  For `0 < n`,

`B M n / 2^{n−1} = d M`,

because a block is the window read in base `2` with the *highest* power
carrying the *first* digit. -/
theorem jsp87_blockNat_top (M n : ℕ) (hn : 0 < n) :
    jsp87BlockNat M n / 2 ^ (n - 1) = jsp87DigitNat M := by
  cases n with
  | zero => omega
  | succ k =>
      show jsp87BlockNat M (Nat.succ k) / 2 ^ (Nat.succ k - 1) = jsp87DigitNat M
      have heq : Nat.succ k = k + 1 := rfl
      have hsub : Nat.succ k - 1 = k := by omega
      have hc : jsp87DigitNat M * 2 ^ k = 2 ^ k * jsp87DigitNat M := Nat.mul_comm _ _
      have hc' : jsp87BlockNat (M + 1) k + 2 ^ k * jsp87DigitNat M
          = 2 ^ k * jsp87DigitNat M + jsp87BlockNat (M + 1) k := Nat.add_comm _ _
      rw [heq, hsub, jsp87_blockNat_split M k, hc, hc',
        Nat.mul_add_div (m := 2 ^ k) (by positivity),
        Nat.div_eq_of_lt (jsp87_blockNat_lt (M + 1) k), Nat.add_zero]

private theorem jsp87_block_inj_aux : ∀ (n M M' : ℕ),
    jsp87BlockNat M n = jsp87BlockNat M' n → ∀ j, j < n →
      jsp87Digit (M + j) = jsp87Digit (M' + j)
  | 0, M, M', _h, j, hj => absurd hj (by simp)
  | (n + 1), M, M', hnat, j, hj => by
      have htop := jsp87_blockNat_top M (n + 1) (by omega)
      have htop' := jsp87_blockNat_top M' (n + 1) (by omega)
      have hsub : (n + 1) - 1 = n := by omega
      rw [hsub] at htop htop'
      rw [hnat] at htop
      have e : jsp87DigitNat M = jsp87DigitNat M' := htop.symm.trans htop'
      by_cases hj0 : j = 0
      · have e' : jsp87Digit M = jsp87Digit M' := by
          have hz := congrArg (fun z : ℕ => (z : ℤ)) e
          rwa [jsp87_digitNat_cast, jsp87_digitNat_cast] at hz
        subst hj0
        simpa using e'
      · have hxy : jsp87DigitNat M * 2 ^ n = jsp87DigitNat M' * 2 ^ n := by rw [e]
        have hz := congrArg (fun z : ℕ => z - jsp87DigitNat M * 2 ^ n) hnat
        rw [jsp87_blockNat_split M n, jsp87_blockNat_split M' n, hxy,
          Nat.add_sub_cancel_right, Nat.add_sub_cancel_right] at hz
        have heq1 : M + 1 + (j - 1) = M + j := by omega
        have heq2 : M' + 1 + (j - 1) = M' + j := by omega
        simpa only [heq1, heq2] using
          jsp87_block_inj_aux n (M + 1) (M' + 1) hz (j - 1) (by omega)

/-- **THE BLOCK DETERMINES THE DIGITS.**  `B M n = B M' n` forces
`d (M+j) = d (M'+j)` for every `j < n`.  This is what makes the block the right
object to count. -/
theorem jsp87_block_inj {M M' n : ℕ} (_hn : 0 < n)
    (h : jsp87DigitBlock M n = jsp87DigitBlock M' n) :
    ∀ j : ℕ, j < n → jsp87Digit (M + j) = jsp87Digit (M' + j) := by
  have h0 := jsp87_digitBlock_bounds M n
  have h1 := jsp87_digitBlock_bounds M' n
  have hcast : jsp87DigitBlock M n = (jsp87BlockNat M n : ℤ) := (jsp87_blockNat_cast M n).symm
  have hcast' : jsp87DigitBlock M' n = (jsp87BlockNat M' n : ℤ) :=
    (jsp87_blockNat_cast M' n).symm
  have hnat : jsp87BlockNat M n = jsp87BlockNat M' n := by
    have hz := congrArg Int.toNat h
    have e1 : (jsp87DigitBlock M n).toNat = jsp87BlockNat M n := by
      rw [hcast, Int.toNat_natCast]
    have e2 : (jsp87DigitBlock M' n).toNat = jsp87BlockNat M' n := by
      rw [hcast', Int.toNat_natCast]
    rwa [e1, e2] at hz
  exact jsp87_block_inj_aux n M M' hnat

/-! ## 2. The periodic tail is a word on `ℤ/tℤ` -/

/-- **ITERATING THE PERIOD.** -/
theorem jsp87_digit_period_iter {M t m q : ℕ} (_ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) (hM : M ≤ m) :
    jsp87Digit (m + q * t) = jsp87Digit m := by
  induction q generalizing m with
  | zero => simp
  | succ q ih =>
      rw [show m + (q + 1) * t = (m + q * t) + t from by ring]
      rw [hper (m + q * t) (by omega)]
      exact ih hM

/-- **PAST THE PRE-PERIOD, THE DIGIT DEPENDS ONLY ON THE POSITION MODULO `t`.** -/
theorem jsp87_digit_eq_of_mod {M t m : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) (hM : M ≤ m) :
    jsp87Digit m = jsp87Digit (M + (m - M) % t) := by
  have hmd := Nat.mod_add_div (m - M) t
  have hxy : (m - M) / t * t = t * ((m - M) / t) := Nat.mul_comm _ _
  have hmain : M + (m - M) % t + (m - M) / t * t = m := by
    rw [hxy]
    omega
  have hx := jsp87_digit_period_iter (M := M) (t := t) (m := M + (m - M) % t)
    (q := (m - M) / t) ht hper (by omega)
  rwa [hmain] at hx

/-- **CONGRUENT POSITIONS GIVE THE SAME BLOCK.** -/
theorem jsp87_block_eq_of_congr {M t n N N' : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x)
    (hM : M ≤ N) (hM' : M ≤ N')
    (hmod : (N - M) % t = (N' - M) % t) :
    jsp87DigitBlock N n = jsp87DigitBlock N' n := by
  refine jsp87_block_eq_of_digits_eq fun j hj => ?_
  have h1 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := N + j) ht hper (by omega)
  have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := N' + j) ht hper (by omega)
  rw [h1, h2]
  congr 1
  have key : ∀ (P P' : ℕ), M ≤ P → M ≤ P' → (P - M) % t = (P' - M) % t →
      (P + j - M) % t = (P' + j - M) % t := by
    intro P P' hP hP' hP''
    have e1 : P + j - M = (P - M) + j := by omega
    have e2 : P' + j - M = (P' - M) + j := by omega
    have e3 : (P - M + j) % t = ((P - M) % t + j % t) % t := Nat.add_mod _ _ _
    have e4 : (P' - M + j) % t = ((P' - M) % t + j % t) % t := Nat.add_mod _ _ _
    rw [e1, e2, e3, e4, hP'']
  rw [key N N' hM hM' hmod]

/-! ## 3. The complexity–period theorem -/

/-- **THE COMPLEXITY–PERIOD THEOREM.**  If the binary digits are eventually
periodic from `M` with period `t`, then for every `n` the number of distinct
`n`-digit blocks occurring at positions `≥ M` is at most `t`: the block at
position `N` is a function of the residue `N − M` modulo `t`.  This is the
`p(n) ≤ t` half of the combinatorics-on-words dictionary, and it is the first
statement in the tree bounding the number of distinct `jsp87DigitBlock`s. -/
theorem jsp87_blockCompl_le_period {M t n K : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
      (fun N => jsp87DigitBlock N n)) ≤ t := by
  set sf : Finset ℕ := (Finset.range K).filter (fun N => M ≤ N) with hsf
  set fr : ℕ → Fin t := fun N => Fin.mk ((N - M) % t) (Nat.mod_lt _ ht) with hfr
  set ψ : Fin t → ℤ := fun y => jsp87DigitBlock (M + y.val) n with hψ
  have hkey : ∀ N, M ≤ N → jsp87DigitBlock N n = ψ (fr N) := by
    intro N hN
    have h := jsp87_block_eq_of_congr (M := M) (t := t) (n := n) (N := N)
      (N' := M + (N - M) % t) ht hper hN (by omega)
      (by rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt (Nat.mod_lt _ ht)])
    show jsp87DigitBlock N n = jsp87DigitBlock (M + (fr N).val) n
    exact h
  have himg : sf.image (fun N => jsp87DigitBlock N n) = (sf.image fr).image ψ := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨N, hN, hx'⟩ := Finset.mem_image.mp hx
      refine Finset.mem_image.mpr ⟨fr N, Finset.mem_image.mpr ⟨N, hN, rfl⟩, ?_⟩
      rw [← hx']
      exact (hkey N (Finset.mem_filter.mp hN |>.2)).symm
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      obtain ⟨N, hN, hfr⟩ := Finset.mem_image.mp hy
      have hfy : y = fr N := hfr.symm
      subst hfy
      refine Finset.mem_image.mpr ⟨N, hN, ?_⟩
      rw [← hxy]
      exact hkey N (Finset.mem_filter.mp hN |>.2)
  rw [himg]
  calc Finset.card ((sf.image fr).image ψ) ≤ (sf.image fr).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin t)).card :=
      Finset.card_le_card (fun y hy => Finset.mem_univ y)
    _ = t := by simp

/-- **THE TOTAL COMPLEXITY IS AT MOST THE PRE-PERIOD PLUS THE PERIOD.** -/
theorem jsp87_blockCompl_total_le {M t n K : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) (_hM : 1 ≤ M) :
    Finset.card ((Finset.range K).image (fun N => jsp87DigitBlock N n)) ≤ M + t := by
  have hsplit : (Finset.range K).filter (fun N => N < M) ∪
      (Finset.range K).filter (fun N => M ≤ N) = Finset.range K := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
    omega
  have hsub : (Finset.range K).image (fun N => jsp87DigitBlock N n)
      ⊆ ((Finset.range K).filter (fun N => N < M)).image (fun N => jsp87DigitBlock N n)
        ∪ ((Finset.range K).filter (fun N => M ≤ N)).image (fun N => jsp87DigitBlock N n) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    rcases lt_or_ge y M with hlt | hge
    · refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hlt⟩, hxy⟩
    · refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hge⟩, hxy⟩
  have hcard₁ : Finset.card (((Finset.range K).filter (fun N => N < M)).image
      (fun N => jsp87DigitBlock N n)) ≤ M := by
    have hfilter : (Finset.range K).filter (fun N => N < M) = Finset.range (min K M) := by
      ext N
      rw [min_def]
      split
      · simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · simp only [Finset.mem_filter, Finset.mem_range]
        omega
    calc Finset.card (((Finset.range K).filter (fun N => N < M)).image
          (fun N => jsp87DigitBlock N n))
        ≤ Finset.card ((Finset.range K).filter (fun N => N < M)) :=
          Finset.card_image_le (s := (Finset.range K).filter (fun N => N < M))
            (f := fun N => jsp87DigitBlock N n)
      _ = min K M := by rw [hfilter, Finset.card_range]
      _ ≤ M := Nat.min_le_right _ _
  have hcard₂ : Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
      (fun N => jsp87DigitBlock N n)) ≤ t :=
    jsp87_blockCompl_le_period (M := M) (t := t) (n := n) (K := K) ht hper
  calc Finset.card ((Finset.range K).image (fun N => jsp87DigitBlock N n))
      ≤ Finset.card (((Finset.range K).filter (fun N => N < M)).image
          (fun N => jsp87DigitBlock N n)
        ∪ ((Finset.range K).filter (fun N => M ≤ N)).image (fun N => jsp87DigitBlock N n)) :=
      Finset.card_le_card hsub
    _ ≤ Finset.card (((Finset.range K).filter (fun N => N < M)).image
          (fun N => jsp87DigitBlock N n))
        + Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
          (fun N => jsp87DigitBlock N n)) := Finset.card_union_le _ _
    _ ≤ M + t := by omega

/-- **THE COMPLEXITY STABILISES AT THE LEAST PERIOD.**  If `t` is the *least*
eventual period from `M` and `t ≤ n`, the `t` blocks at `M, M+1, …, M+t−1` are
pairwise distinct; together with `jsp87_blockCompl_le_period` this is `p(n) = t`
for every `n ≥ t`, the classical description of the complexity of a periodic
word.  No statement of this kind exists in Mathlib, which has no notion of the
digit string of a real number. -/
theorem jsp87_minimalPeriod_blocks_distinct {M t n i j : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (_hM : 1 ≤ M)
    (hmin : ∀ u : ℕ, 0 < u → (∀ x : ℕ, M ≤ x → jsp87Digit (x + u) = jsp87Digit x) → t ≤ u)
    (hper : ∀ x : ℕ, M ≤ x → jsp87Digit (x + t) = jsp87Digit x)
    (hi : i < t) (hj : j < t)
    (hne : jsp87DigitBlock (M + i) n = jsp87DigitBlock (M + j) n) : i = j := by
  have hinj : ∀ s : ℕ, s < n → jsp87Digit (M + i + s) = jsp87Digit (M + j + s) := by
    intro s hs
    exact jsp87_block_inj (M := M + i) (M' := M + j) (n := n) (by omega) hne s hs
  by_cases h : i = j
  · exact h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · set u : ℕ := j - i with hu_def
    have hu0 : 0 < u := by simp only [hu_def]; omega
    have hut : u < t := by simp only [hu_def]; omega
    have hstep : ∀ s : ℕ, s < n → jsp87Digit (M + i + s) = jsp87Digit (M + i + s + u) := by
      intro s hs
      have hk := hinj s hs
      have h1 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + i + s) ht hper (by omega)
      have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + i + s + u) ht hper
        (by omega)
      have h3 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + j + s) ht hper (by omega)
      rw [h1] at hk ⊢
      rw [h3] at hk
      rw [h2] at ⊢
      have ea : (M + i + s - M) % t = (i + s % t) % t := by
        have e : (M + i + s) - M = i + s := by omega
        rw [e, Nat.add_mod _ _ t, Nat.mod_eq_of_lt hi]
      have eb : (M + j + s - M) % t = (j + s % t) % t := by
        have e : (M + j + s) - M = j + s := by omega
        rw [e, Nat.add_mod _ _ t, Nat.mod_eq_of_lt hj]
      have ec : (M + i + s + u - M) % t = (j + s % t) % t := by
        have hM2 : M + i + s + u = M + j + s := by simp only [hu_def]; omega
        rw [hM2]
        exact eb
      rw [ea, eb] at hk
      rw [ea, ec] at ⊢
      exact hk
    have hzmod : ∀ r : ℕ, r < t → jsp87Digit (M + r) = jsp87Digit (M + (r + u) % t) := by
      intro r hrt
      set k : ℕ := if i ≤ r then r - i else r + t - i with hk
      have hklt : k < t := by
        simp only [hk]
        split <;> omega
      have h1 := hstep k (lt_of_lt_of_le hklt htn)
      have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + i + k) ht hper (by omega)
      have h3 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + i + k + u) ht hper (by omega)
      have e1 : (M + i + k - M) % t = r := by
        have e : (M + i + k) - M = i + k := by omega
        rw [e, hk]
        split
        · rw [show i + (r - i) = r from by omega, Nat.mod_eq_of_lt hrt]
        · rw [show i + (r + t - i) = r + t from by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt hrt]
      have e2 : (M + i + k + u - M) % t = (r + u) % t := by
        have e : (M + i + k + u) - M = i + k + u := by omega
        rw [e, hk]
        split
        · rw [show i + (r - i) = r from by omega]
        · rw [show i + (r + t - i) = r + t from by omega, Nat.add_mod _ _ t,
            Nat.add_mod_right, Nat.mod_eq_of_lt hrt, Nat.mod_eq_of_lt hut]
      rw [← e2, ← e1, ← h2, ← h3]
      exact h1
    have hper' : ∀ x : ℕ, M ≤ x → jsp87Digit (x + u) = jsp87Digit x := by
      intro x hx
      set r := (x - M) % t with hr
      have hrt : r < t := by
        simp only [hr]
        exact Nat.mod_lt _ ht
      have h1 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := x) ht hper hx
      have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := x + u) ht hper (by omega)
      rw [h1, h2, ← hr]
      have hA : (x + u - M) % t = (r + u) % t := by
        have h1' : (x + u) - M = (x - M) + u := by omega
        calc (x + u - M) % t = ((x - M) + u) % t := by rw [h1']
          _ = ((x - M) % t + u % t) % t := Nat.add_mod _ _ _
          _ = (r + u % t) % t := by rw [hr]
          _ = (r + u) % t := by rw [Nat.mod_eq_of_lt hut]
      rw [hA]
      exact (hzmod r hrt).symm
    have hcontra := hmin u hu0 hper'
    omega
  · set u : ℕ := i - j with hu_def
    have hu0 : 0 < u := by simp only [hu_def]; omega
    have hut : u < t := by simp only [hu_def]; omega
    have hstep : ∀ s : ℕ, s < n → jsp87Digit (M + j + s) = jsp87Digit (M + j + s + u) := by
      intro s hs
      have hk := (hinj s hs).symm
      have h1 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + j + s) ht hper (by omega)
      have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + j + s + u) ht hper
        (by omega)
      have h3 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + i + s) ht hper (by omega)
      rw [h3] at hk
      rw [h1] at hk
      rw [h1] at ⊢
      rw [h2] at ⊢
      have ea : (M + i + s - M) % t = (i + s % t) % t := by
        have e : (M + i + s) - M = i + s := by omega
        rw [e, Nat.add_mod _ _ t, Nat.mod_eq_of_lt hi]
      have eb : (M + j + s - M) % t = (j + s % t) % t := by
        have e : (M + j + s) - M = j + s := by omega
        rw [e, Nat.add_mod _ _ t, Nat.mod_eq_of_lt hj]
      have ed : (M + j + s + u - M) % t = (i + s % t) % t := by
        have hM2 : M + j + s + u = M + i + s := by simp only [hu_def]; omega
        rw [hM2]
        exact ea
      rw [ea, eb] at hk
      rw [eb, ed] at ⊢
      exact hk
    have hzmod : ∀ r : ℕ, r < t → jsp87Digit (M + r) = jsp87Digit (M + (r + u) % t) := by
      intro r hrt
      set k : ℕ := if j ≤ r then r - j else r + t - j with hk
      have hklt : k < t := by
        simp only [hk]
        split <;> omega
      have h1 := hstep k (lt_of_lt_of_le hklt htn)
      have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + j + k) ht hper (by omega)
      have h3 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := M + j + k + u) ht hper
        (by omega)
      have e1 : (M + j + k - M) % t = r := by
        have e : (M + j + k) - M = j + k := by omega
        rw [e, hk]
        split
        · rw [show j + (r - j) = r from by omega, Nat.mod_eq_of_lt hrt]
        · rw [show j + (r + t - j) = r + t from by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt hrt]
      have e2 : (M + j + k + u - M) % t = (r + u) % t := by
        have e : (M + j + k + u) - M = j + k + u := by omega
        rw [e, hk]
        split
        · rw [show j + (r - j) = r from by omega]
        · rw [show j + (r + t - j) = r + t from by omega, Nat.add_mod _ _ t,
            Nat.add_mod_right, Nat.mod_eq_of_lt hrt, Nat.mod_eq_of_lt hut]
      rw [← e2, ← e1, ← h2, ← h3]
      exact h1
    have hper' : ∀ x : ℕ, M ≤ x → jsp87Digit (x + u) = jsp87Digit x := by
      intro x hx
      set r := (x - M) % t with hr
      have hrt : r < t := by
        simp only [hr]
        exact Nat.mod_lt _ ht
      have h1 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := x) ht hper hx
      have h2 := jsp87_digit_eq_of_mod (M := M) (t := t) (m := x + u) ht hper (by omega)
      rw [h1, h2, ← hr]
      have hA : (x + u - M) % t = (r + u) % t := by
        have h1' : (x + u) - M = (x - M) + u := by omega
        calc (x + u - M) % t = ((x - M) + u) % t := by rw [h1']
          _ = ((x - M) % t + u % t) % t := Nat.add_mod _ _ _
          _ = (r + u % t) % t := by rw [hr]
          _ = (r + u) % t := by rw [Nat.mod_eq_of_lt hut]
      rw [hA]
      exact (hzmod r hrt).symm
    have hcontra := hmin u hu0 hper'
    omega

/-! ## 4. A block is read off the fractional part -/

/-- `⌊{x}⌋ = 0` for the `Int` floor. -/
private theorem floor_fract_zero (x : ℝ) : ⌊Int.fract x⌋ = 0 := by
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
  · exact_mod_cast (Int.fract_nonneg x : 0 ≤ Int.fract x)
  · have hz : ((0 : ℤ) : ℝ) + 1 = 1 := by ring
    rw [hz]
    exact_mod_cast (Int.fract_lt_one x : Int.fract x < 1)

/-- `⌊(m : ℝ) · y⌋ = m · ⌊y⌋ + ⌊(m : ℝ) · {y}⌋`. -/
private theorem floor_mul_natCast_fract (m : ℕ) (y : ℝ) :
    ⌊(m : ℝ) * y⌋ = (m : ℤ) * ⌊y⌋ + ⌊(m : ℝ) * Int.fract y⌋ := by
  have hkey : (m : ℝ) * y = (m : ℝ) * (⌊y⌋ : ℝ) + (m : ℝ) * Int.fract y := by
    have h : (⌊y⌋ : ℝ) + Int.fract y = y := Int.floor_add_fract y
    nth_rewrite 1 [← h]
    ring
  have hz : (((m : ℤ) * ⌊y⌋ : ℤ) : ℝ) = (m : ℝ) * (⌊y⌋ : ℝ) := by
    push_cast
    rfl
  rw [Int.floor_eq_iff]
  constructor
  · push_cast only [Int.cast_add]
    have h1 : ((⌊(m : ℝ) * Int.fract y⌋ : ℤ) : ℝ) ≤ (m : ℝ) * Int.fract y :=
      Int.floor_le _
    linarith
  · push_cast only [Int.cast_add]
    have h1 : (m : ℝ) * Int.fract y < ((⌊(m : ℝ) * Int.fract y⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    linarith

/-- **THE `N`-TH DIGIT IS THE FLOOR OF TWICE THE FRACTIONAL PART.** -/
theorem jsp87_digit_eq_floorOf_fract (N : ℕ) :
    (jsp87Digit N : ℤ) = ⌊2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ := by
  have hfr : (2 : ℝ) ^ (N + 1) * jsp87Series = 2 * ((2 : ℝ) ^ N * jsp87Series) := by
    rw [pow_succ]
    ring
  have hfract : Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series)
      = Int.fract (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)) := by
    rw [hfr]
    exact Int.fract_two_mul
  have hsf := Int.self_sub_floor (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series))
  rw [← hfract] at hsf
  have hd := jsp87_digit_eq_fract N
  have key : (jsp87Digit N : ℝ) = (⌊2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ : ℝ) := by
    linarith
  exact_mod_cast key

/-- **THE WHOLE BLOCK IS THE FLOOR OF `2^n` TIMES THE FRACTIONAL PART.**  The
`n`-digit block at `N` is a *function* of `Int.fract (2^N S)`, and this is the
bridge from the orbit to the blocks. -/
theorem jsp87_block_eq_floorOf_fract {N n : ℕ} :
    jsp87DigitBlock N n = ⌊(2 : ℝ) ^ n * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ := by
  induction n generalizing N with
  | zero =>
      have h0 : jsp87DigitBlock N 0 = 0 := by
        unfold jsp87DigitBlock
        simp
      have h1 : ⌊(2 : ℝ) ^ 0 * Int.fract ((2 : ℝ) ^ N * jsp87Series)⌋ = 0 := by
        have e : (2 : ℝ) ^ 0 * Int.fract ((2 : ℝ) ^ N * jsp87Series)
            = Int.fract ((2 : ℝ) ^ N * jsp87Series) := by ring
        rw [e]
        exact floor_fract_zero _
      rw [h0, h1]
  | succ n ih =>
      have hsub : (2 : ℝ) ^ (N + 1) * jsp87Series = 2 * ((2 : ℝ) ^ N * jsp87Series) := by
        rw [pow_succ]
        ring
      have hfract : Int.fract ((2 : ℝ) ^ (N + 1) * jsp87Series)
          = Int.fract (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)) := by
        rw [hsub]
        exact Int.fract_two_mul
      have hkey : (2 : ℝ) ^ (n + 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
          = (2 : ℝ) ^ n * (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)) := by
        rw [pow_succ]
        ring
      have hstep := floor_mul_natCast_fract (2 ^ n)
        (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series))
      have ih' := ih (N := N + 1)
      rw [hfract] at ih'
      have e2 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
        push_cast
        rfl
      rw [← e2] at ih'
      have hkey' : (2 : ℝ) ^ (n + 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
          = ((2 ^ n : ℕ) : ℝ) * (2 * Int.fract ((2 : ℝ) ^ N * jsp87Series)) := by
        rw [pow_succ, Nat.cast_pow]
        ring
      rw [← hkey'] at hstep
      rw [hstep, ← ih']
      have hdigits : (jsp87Digit N : ℤ) * 2 ^ n + jsp87DigitBlock (N + 1) n
          = jsp87DigitBlock N (n + 1) := by
        have hz : jsp87DigitBlock N (n + 1) = (jsp87Digit N : ℤ) * 2 ^ n
            + jsp87DigitBlock (N + 1) n := by
          have hlast : (jsp87Digit (N + 0) : ℤ) * 2 ^ (n - 0)
              = (jsp87Digit N : ℤ) * 2 ^ n := by
            congr 2
          have hstep : (∑ j ∈ Finset.range (n + 1),
                (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (n - j))
              = (∑ k ∈ Finset.range n,
                (jsp87Digit (N + (k + 1)) : ℤ) * (2 : ℤ) ^ (n - (k + 1)))
                + (jsp87Digit N : ℤ) * 2 ^ n := by
            rw [Finset.sum_range_succ', hlast]
          have hmain : (∑ k ∈ Finset.range n,
                (jsp87Digit (N + (k + 1)) : ℤ) * (2 : ℤ) ^ (n - (k + 1)))
              = (∑ j ∈ Finset.range n,
                (jsp87Digit (N + 1 + j) : ℤ) * (2 : ℤ) ^ (n - 1 - j)) := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            congr 2
            · have h1 : N + (k + 1) = (N + 1) + k := by omega
              rw [h1]
            · have hk : k < n := Finset.mem_range.mp _hk
              omega
          unfold jsp87DigitBlock
          simp only [Nat.add_sub_cancel]
          rw [hstep, hmain]
          ring
        rw [hz]
      rw [jsp87_digit_eq_floorOf_fract N] at hdigits
      rw [← hdigits]
      push_cast
      ring

/-- **`S < 1`.** -/
theorem jsp87Series_lt_one : jsp87Series < 1 := by
  have hne : jsp87Series ≠ 1 := by
    intro h
    have hz := jsp87_floor_S_zero
    rw [h, Int.floor_one] at hz
    norm_num at hz
  rcases lt_or_eq_of_le jsp87Series_le_one with h | h
  · exact h
  · exact absurd h hne

/-- **THE ORBIT POINT, AS A NATURAL NUMBER.**  For `N ≥ 1` this is round 41's
`jsp87FracNum`; at `N = 0` it is the numerator of `S` itself, which exists
because `0 ≤ S < 1`. -/
noncomputable def jsp87RatOrbitNum (a : ℤ) (b : ℕ) : ℕ → ℕ
  | 0 => a.toNat
  | N + 1 => jsp87FracNum b (N + 1)

theorem jsp87_a_nonneg {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : 0 ≤ (a : ℤ) := by
  have h0 : (0 : ℝ) ≤ jsp87Series := jsp87Series_nonneg
  rw [h] at h0
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hz := (le_div_iff₀ hb').mp h0
  norm_cast at hz
  simpa using hz

theorem jsp87_a_lt {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : (a : ℤ) < (b : ℤ) := by
  have h1 : jsp87Series < 1 := jsp87Series_lt_one
  rw [h] at h1
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hz := (div_lt_iff₀ hb').mp h1
  have hz' : ((a : ℤ) : ℝ) < (b : ℝ) := by simpa using hz
  norm_cast at hz'

theorem jsp87_orbitNum_lt {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : jsp87RatOrbitNum a b N < b := by
  cases N with
  | zero =>
      have hnonneg : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg (jsp87_a_nonneg hb h)
      have hlt := jsp87_a_lt hb h
      rw [← hnonneg] at hlt
      exact_mod_cast hlt
  | succ N =>
      exact (jsp87FracNum_spec (b := b) (N := N + 1) hb h (by omega)).1

/-- **THE ORBIT POINT RECOVERS THE FRACTIONAL PART.** -/
theorem jsp87_fract_eq_orbitNum {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    Int.fract ((2 : ℝ) ^ N * jsp87Series)
      = ((jsp87RatOrbitNum a b N : ℕ) : ℝ) / (b : ℝ) := by
  cases N with
  | zero =>
      have hkey : Int.fract ((2 : ℝ) ^ 0 * jsp87Series) = jsp87Series := by
        have h2 := Int.self_sub_floor (a := jsp87Series)
        have hf := jsp87_floor_S_zero
        rw [pow_zero, one_mul]
        rw [hf, Int.cast_zero] at h2
        linarith
      have hcast : (((a.toNat : ℕ) : ℤ) : ℝ) = ((a : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg (jsp87_a_nonneg hb h)]
      rw [hkey, h]
      have hz0 : jsp87RatOrbitNum a b 0 = a.toNat := rfl
      rw [hz0]
      congr 1
      exact hcast.symm
  | succ N =>
      exact (jsp87FracNum_spec (b := b) (N := N + 1) hb h (by omega)).2

/-- **THE COMPLEXITY–DENOMINATOR THEOREM.**  If the Erdős series were the
rational `a / b` with `b > 0`, then for every `n` the binary expansion of `S`
would contain at most `b` distinct `n`-digit blocks: the fractional parts of
`2^N S` live in the finite set `{ k / b : k < b }`, and the `n`-block is a
function of the fractional part (round 73's `jsp87_block_eq_floorOf_fract`).
Together with `jsp87_blockCompl_le_period` this is the sharpest structural
obstruction in the tree, and it is what turns a *finite* computation of the
complexity into a *denominator bound*. -/
theorem jsp87_blockCompl_le_denominator {a : ℤ} {b n K : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    Finset.card ((Finset.range K).image (fun N => jsp87DigitBlock N n)) ≤ b := by
  set fr : ℕ → Fin b := fun N => Fin.mk (jsp87RatOrbitNum a b N) (jsp87_orbitNum_lt hb h) with hfr
  have hkey : ∀ N, jsp87DigitBlock N n
      = ⌊(2 : ℝ) ^ n * (((fr N).val : ℕ) : ℝ) / (b : ℝ)⌋ := by
    intro N
    have h1 := jsp87_block_eq_floorOf_fract (N := N) (n := n)
    have h3 := jsp87_fract_eq_orbitNum (a := a) (b := b) (N := N) hb h
    have hv : (fr N).val = jsp87RatOrbitNum a b N := rfl
    rw [h1, h3, hv]
    congr 1
    ring
  have himg : (Finset.range K).image (fun N => jsp87DigitBlock N n)
      = ((Finset.range K).image fr).image
        (fun y : Fin b => ⌊(2 : ℝ) ^ n * (((y : Fin b).val : ℕ) : ℝ) / (b : ℝ)⌋) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨N, hN, hx'⟩ := Finset.mem_image.mp hx
      refine Finset.mem_image.mpr ⟨fr N, Finset.mem_image.mpr ⟨N, hN, rfl⟩, ?_⟩
      rw [← hx']
      exact (hkey N).symm
    · intro hx
      obtain ⟨y, hy, hx'⟩ := Finset.mem_image.mp hx
      obtain ⟨N, hN, hfr'⟩ := Finset.mem_image.mp hy
      have hfv : y = fr N := hfr'.symm
      subst hfv
      refine Finset.mem_image.mpr ⟨N, hN, ?_⟩
      rw [← hx']
      exact hkey N
  rw [himg]
  calc Finset.card (((Finset.range K).image fr).image
        (fun y : Fin b => ⌊(2 : ℝ) ^ n * (((y : Fin b).val : ℕ) : ℝ) / (b : ℝ)⌋))
      ≤ Finset.card ((Finset.range K).image fr) := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin b)).card :=
      Finset.card_le_card (fun y hy => Finset.mem_univ y)
    _ = b := by simp

/-- **UNBOUNDED SUBWORD COMPLEXITY FORCES IRRATIONALITY — A NEW CRITERION.**
Assume that for *every* start point `M` and *every* `K` there is a length `n` at
which more than `K` distinct `n`-digit blocks occur among the positions
`M ≤ N < K'`, for every `K' ≥ M`.  Then the Erdős series is irrational: a
rational value would freeze the block sequence at the period `t`, bounding the
count at positions `≥ M` by `t` (`jsp87_blockCompl_le_period`). -/
theorem jsp87Series_irrational_of_compl_gt_period
    (h : ∀ M : ℕ, 1 ≤ M → ∀ K : ℕ, ∃ n : ℕ, 1 ≤ n ∧ ∀ K' : ℕ, M ≤ K' →
      K < Finset.card (((Finset.range K').filter (fun N => M ≤ N)).image
        (fun N => jsp87DigitBlock N n))) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hb : 0 < q.den := Rat.den_pos q
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb (by rw [← hq, Rat.cast_def])
  obtain ⟨n, hn, hK⟩ := h M hM (t + 1)
  set K' := max M (t + 1) with hK'
  have hlt := hK K' (by rw [hK']; omega)
  have hbound := jsp87_blockCompl_le_period (M := M) (t := t) (n := n) (K := K') ht hper
  have hsub : ((Finset.range K').filter (fun N => M ≤ N)).image
        (fun N => jsp87DigitBlock N n)
      ⊆ (Finset.range K').image (fun N => jsp87DigitBlock N n) :=
    Finset.image_subset_image (fun _ hx => Finset.mem_filter.mp hx |>.1)
  have hle : Finset.card (((Finset.range K').filter (fun N => M ≤ N)).image
        (fun N => jsp87DigitBlock N n))
      ≤ Finset.card ((Finset.range K').image (fun N => jsp87DigitBlock N n)) :=
    Finset.card_le_card hsub
  omega


/-! ## 6. The certified `2048`-digit prefix, and its subword complexity -/

/-- **THE BINARY PREFIX OF THE ERDŐS SERIES AFTER `2048` DIGITS**, as a single
natural number.  (Round 71 certified `64` digits; the same window machinery,
`jsp87Series_floor_eq`, runs unchanged to `2048`.) -/
def jsp87Prefix2048 : ℕ :=
  8353022123089756164277618536173907447409920859095071326977219176297329779682862579708285625032736640034486475531003327765719712579712695801233373952575879600405328475157130089487483481700396543698258180938794850520401964410572030500077158592627173998457711699737215807945776495330161639585928389040966905336331762305537505033407941588371302094245569891689312603361271390357926553899343515469311044036993950575941526659976219685007016697733946680323034537832955957616513572901812051447371774560489656700806636449400345691173830672563828572732970922041436921422116346606080429992074789684771509283270721280464519705610

theorem jsp87Prefix_2048 : jsp87Prefix 2048 = jsp87Prefix2048 := by
  rw [← jsp87Prefix_eq_nat]
  native_decide

set_option exponentiation.threshold 4096 in
theorem jsp87Series_floor_2048 :
    ⌊(2 : ℝ) ^ 2048 * jsp87Series⌋ = (jsp87Prefix2048 + 1 : ℤ) := by
  have h := jsp87Series_floor_eq (N := 2048) (L := 48) (by norm_num) (by norm_num)
    (by native_decide)
  rw [h, jsp87Prefix_2048]
  have hw : (jsp87OmegaWindow 2048 48 / 2 ^ 48 : ℕ) = 1 := by native_decide
  rw [hw]
  rfl

set_option exponentiation.threshold 4096 in
theorem jsp87DigitBlock_zero_2048 :
    jsp87DigitBlock 0 2048 = (jsp87Prefix2048 + 1 : ℤ) := by
  have h := jsp87_floor_telescope (N := 0) (t := 2048)
  have h0 : ⌊(2 : ℝ) ^ 0 * jsp87Series⌋ = 0 := by simpa using jsp87_floor_S_zero
  rw [h0] at h
  have hf := jsp87Series_floor_2048
  unfold jsp87DigitBlock
  rw [hf] at h
  linarith

/-- **THE `n`-DIGIT BLOCK AT `N`, READ OFF A CERTIFIED PREFIX OF LENGTH `L`.**
This is the only computable object needed below: it is pure arithmetic on the
integer `⌊2^L S⌋`. -/
def jsp87Subword (X L n N : ℕ) : ℕ := (X / 2 ^ (L - n - N)) % 2 ^ n

/-- **THE PREFIX–BLOCK IDENTITY: A CERTIFIED PREFIX DETERMINES EVERY BLOCK.**
If `⌊2^L S⌋ = X` and `N + n ≤ L`, then

`B N n = (X / 2^{L−N−n}) mod 2^n`,

i.e. the block at `N` is the `n`-digit window of the certified integer `X` at
place `L − N − n`.  (Two telescopings and one `Nat.mul_add_div`.) -/
theorem jsp87_subword_eq_block {X L n N : ℕ} (hN : N + n ≤ L)
    (hX : jsp87DigitBlock 0 L = (X : ℤ)) :
    jsp87BlockNat N n = jsp87Subword X L n N := by
  have hX0 : 0 ≤ (X : ℤ) := by rw [← hX]; exact (jsp87_digitBlock_bounds 0 L).1
  have hflo : ∀ k : ℕ, (⌊(2 : ℝ) ^ k * jsp87Series⌋ : ℤ) = jsp87DigitBlock 0 k := by
    intro k
    have h := jsp87_floor_telescope (N := 0) (t := k)
    have h0 : ⌊(2 : ℝ) ^ 0 * jsp87Series⌋ = 0 := by simpa using jsp87_floor_S_zero
    rw [h0] at h
    unfold jsp87DigitBlock
    simpa using h
  have hsum : ∀ k m : ℕ,
      (∑ j ∈ Finset.range m, (jsp87Digit (k + j) : ℤ) * (2 : ℤ) ^ (m - 1 - j))
        = jsp87DigitBlock k m := by
    intro k m
    unfold jsp87DigitBlock
    rfl
  have hdiv : ∀ k : ℕ, k ≤ L → jsp87BlockNat 0 k = X / 2 ^ (L - k) := by
    intro k hk
    have h := jsp87_floor_telescope (N := k) (t := L - k)
    have h1 := hflo k
    have h2 := hflo L
    have hb := jsp87_digitBlock_bounds k (L - k)
    rw [Nat.add_sub_of_le hk] at h
    rw [h1, h2, hsum k (L - k)] at h
    rw [hX] at h
    have h3 : (X : ℤ) = (2 : ℤ) ^ (L - k) * (jsp87BlockNat 0 k : ℤ)
        + (jsp87BlockNat k (L - k) : ℤ) := by
      rw [← jsp87_blockNat_cast, ← jsp87_blockNat_cast] at h
      exact h
    have heq : X = 2 ^ (L - k) * jsp87BlockNat 0 k + jsp87BlockNat k (L - k) := by
      exact_mod_cast h3
    rw [heq, Nat.mul_add_div (m := 2 ^ (L - k)) (by simp),
      Nat.div_eq_of_lt (jsp87_blockNat_lt k (L - k)), Nat.add_zero]
  have hltn : jsp87BlockNat N n < 2 ^ n := jsp87_blockNat_lt N n
  have hsplit : jsp87BlockNat 0 (N + n)
      = 2 ^ n * jsp87BlockNat 0 N + jsp87BlockNat N n := by
    have htele := jsp87_floor_telescope (N := N) (t := n)
    have h1 := hflo N
    have h2 := hflo (N + n)
    rw [h2, h1, hsum N n] at htele
    rw [← jsp87_blockNat_cast, ← jsp87_blockNat_cast, ← jsp87_blockNat_cast] at htele
    exact_mod_cast htele
  have hQ : jsp87BlockNat 0 (N + n) = X / 2 ^ (L - N - n) := by
    rw [hdiv (N + n) (by omega)]
    congr 2
    omega
  have hsub : X / 2 ^ (L - N - n)
      = 2 ^ n * jsp87BlockNat 0 N + jsp87BlockNat N n := by
    rw [← hQ, hsplit]
  have heq : L - n - N = L - N - n := by omega
  unfold jsp87Subword
  rw [heq, hsub, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hltn]

private theorem card_image_congr {α : Type _} {β : Type _} [DecidableEq β] (f g : α → β)
    (s : Finset α) (h : ∀ a ∈ s, f a = g a) :
    Finset.card (s.image f) = Finset.card (s.image g) := by
  have h1 : s.image f ⊆ s.image g := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a, ha, (h a ha).symm⟩
  have h2 : s.image g ⊆ s.image f := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a, ha, h a ha⟩
  exact le_antisymm (Finset.card_le_card h1) (Finset.card_le_card h2)

set_option maxHeartbeats 0
/-- **THE CERTIFIED `20`-DIGIT SUBWORD COMPLEXITY IS `2025`.**  Among the `2029`
starting positions of the first `2048` certified binary digits of the Erdős
series, `2025` distinct `20`-digit blocks occur. -/
theorem jsp87Compl_20 :
    Finset.card ((Finset.range 2029).image
      (jsp87Subword (jsp87Prefix2048 + 1) 2048 20)) = 2025 := by
  native_decide

/-- **THE SAME, FOR THE `24`-DIGIT BLOCKS.** -/
theorem jsp87Compl_24 :
    Finset.card ((Finset.range 2025).image
      (jsp87Subword (jsp87Prefix2048 + 1) 2048 24)) = 2025 := by
  native_decide

/-- **THE `20`-DIGIT SUBWORD COMPLEXITY OF THE BINARY EXPANSION OF `jsp87Series`
IS `2025`.**  The certificate is sound (`jsp87_subword_eq_block`), so this is a
statement about the real series and not about an approximation. -/
theorem jsp87BlockCompl_20 :
    Finset.card ((Finset.range 2029).image (fun N => jsp87BlockNat N 20)) = 2025 := by
  have hcong : ∀ N ∈ Finset.range 2029, jsp87BlockNat N 20
      = jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N := by
    intro N hN
    have hN' : N < 2029 := Finset.mem_range.mp hN
    have hsb := jsp87_subword_eq_block (X := jsp87Prefix2048 + 1) (L := 2048) (n := 20)
      (N := N) (by omega) jsp87DigitBlock_zero_2048
    exact hsb
  have hc : Finset.card ((Finset.range 2029).image (fun N : ℕ => jsp87BlockNat N 20))
      = Finset.card ((Finset.range 2029).image
        (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N)) := by
    exact card_image_congr (fun N : ℕ => jsp87BlockNat N 20)
      (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N) (Finset.range 2029)
      (fun N hN => hcong N hN)
  rw [hc]
  exact jsp87Compl_20

private theorem card_image_intCast {α : Type _} (f : α → ℕ) (s : Finset α) :
    Finset.card (s.image (fun a => (f a : ℤ))) = Finset.card (s.image f) := by
  have h1 : ∀ z ∈ s.image (fun a => (f a : ℤ)), Int.toNat z ∈ s.image f := by
    intro z hz
    obtain ⟨a, ha, hz'⟩ := Finset.mem_image.mp hz
    rw [← hz']
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have h2 : ∀ v ∈ s.image f, (v : ℤ) ∈ s.image (fun a => (f a : ℤ)) := by
    intro v hv
    obtain ⟨a, ha, hv'⟩ := Finset.mem_image.mp hv
    rw [← hv']
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  refine Finset.card_bij' (s := s.image (fun a => (f a : ℤ))) (t := s.image f)
    (fun z _ => Int.toNat z) (fun v _ => (v : ℤ)) ?_ ?_ ?_ ?_
  · exact h1
  · exact h2
  · intro z hz
    obtain ⟨a, ha, hz'⟩ := Finset.mem_image.mp hz
    rw [← hz']
    simp
  · intro v hv
    obtain ⟨a, ha, hv'⟩ := Finset.mem_image.mp hv
    rw [← hv']
    simp

/-- **THE SAME COMPLEXITY, IN THE `ℤ`-VALUED BLOCK NOTATION USED BY THE
PERIODICITY MACHINERY.** -/
theorem jsp87DigitBlockCompl_20 :
    Finset.card ((Finset.range 2029).image (fun N => jsp87DigitBlock N 20)) = 2025 := by
  have h1 : Finset.card ((Finset.range 2029).image (fun N : ℕ => jsp87DigitBlock N 20))
      = Finset.card ((Finset.range 2029).image
        (fun N : ℕ => (jsp87BlockNat N 20 : ℤ))) :=
    card_image_congr _ _ _ (fun N hN => (jsp87_blockNat_cast N 20).symm)
  rw [h1, card_image_intCast (fun N : ℕ => jsp87BlockNat N 20) (Finset.range 2029),
    jsp87BlockCompl_20]

/-- **A HYPOTHETICAL RATIONAL VALUE OF `S` HAS DENOMINATOR AT LEAST `2025`.**
Round 71 could prove only `≥ 512`, from a run of nine `1`s; the `2048`-digit
certified prefix and its `2025` distinct `20`-digit blocks, combined with
`jsp87_blockCompl_le_denominator`, cost a factor `4`. -/
theorem jsp87Series_rational_imp_denominator_ge_2025 {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : 2025 ≤ b := by
  have hcard := jsp87_blockCompl_le_denominator (a := a) (b := b) (n := 20) (K := 2029) hb h
  rw [jsp87DigitBlockCompl_20] at hcard
  exact hcard

end JSP87
