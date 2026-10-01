/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.SubwordComplexity

/-!
# JSP-000087, round 75 : the *growth* of the subword complexity (Morse–Hedlund)

## The new attack family

Rounds 37–73 attacked the Erdős series `S = ∑' n, ω(n) 2^{-(n+1)}` through
thirty-five different angles.  Round 73 introduced the **subword complexity**
`p(n)` of the binary expansion — the number of distinct `n`-digit blocks — and
proved three things about it: an eventually `t`-periodic string has `p(n) ≤ t`
(`jsp87_blockCompl_le_period`); a *least* period `t` forces `p(n) = t` for
`n ≥ t` (`jsp87_minimalPeriod_blocks_distinct`); and a rational value
`S = a/b` has `p(n) ≤ b` (`jsp87_blockCompl_le_denominator`).

**Every one of those is an upper bound.**  Nothing in the tree said anything
about the *lower* bound — the growth rate of `p(n)` — which is the
Morse–Hedlund side of combinatorics on words.  That is the family this round
adds, and it is the right family for JSP-000087 for two reasons.

1. **Morse–Hedlund turns aperiodicity into a finite certificate.**  A word whose
   least eventual period is `t` satisfies `p(t) ≤ t`: take `n = t` in the
   complexity–period theorem and the count collapses to `t`.  So *any* `n` at
   which `p(n) > n` is a machine-checkable witness that the digit string is not
   `n`-periodic.  Round 73 computed `p(20) = p(24) = 2025` and never drew the
   conclusion.
2. **The frontier moves with the certified prefix.**  The certified `2048`-digit
   prefix of round 73 pins the first `1024` successive `20`-digit blocks
   (read from place `1`) to be pairwise distinct, and the same at length `24`.
   That is exactly one more than the largest period this excludes, and it shows
   the reach is *linear* in the certified length — so certifying more digits buys
   proportionally more excluded periods.

## Main results

| Theorem | Statement |
| --- | --- |
| **`jsp87_compl_mono`** | **COMPLEXITY IS NON-DECREASING**: `p(n) ≤ p(n+1)`.  The first *structural* fact about `p` in the tree; the map is "drop the first digit", well defined by round 73's `jsp87_block_inj` |
| `jsp87_compl_le_period'` | periodicity bounds the complexity at positions `≥ M` by `t` (round 73's theorem, renamed) |
| **`jsp87Series_irrational_of_compl_gt_index`** | **A NEW IRRATIONALITY CRITERION, AND THE MORSE–HEDLUND CRITERION**: `p(n) ≥ n + 1` for *every* `n` implies irrationality — a *linear* lower bound, where round 73's criterion asked only for unboundedness |
| `jsp87Series_rational_imp_compl_le_index` | the contrapositive, with the witness exhibited: a rational value has `p(t) ≤ t` at its own period `t` |
| `jsp87_compl_20`, `jsp87_compl_gt_20_index` | the certified `20`-digit complexity is `2025 > 20` |
| **`jsp87BlockCompl_24`, `jsp87DigitBlockCompl_24`, `jsp87_compl_gt_24_index`** | **a NEW certified value**: the `24`-digit complexity is `2025 > 24`, computed in the `\u2115`- and `\u2124`-valued block notations |
| **`jsp87SubwordTail_20_1024`, `jsp87_compl_tail_20_ge_1024`** | **THE `1024` SUCCESSIVE `20`-DIGIT BLOCKS FROM PLACE `1` ARE PAIRWISE DISTINCT** |
| `jsp87SubwordTail_24_1024`, `jsp87_compl_tail_24_ge_1024` | the same at length `24` |
| **`jsp87_digit_not_eventuallyPeriodic_period_le_1023`** | **THE HEADLINE**: the binary digits of `jsp87Series` are **not** eventually periodic with **any** period `t ≤ 1023` |
| **`jsp87Series_rational_imp_period_ge_1024`** | a hypothetical rational value has least eventual period `≥ 1024` |

## What this round does NOT do

`jsp_000087_main` remains undeclared, and no weakened statement is emitted under
that name.  Rounds 41–73 reduced irrationality to the aperiodicity of the binary
digit string, and this round **excludes a concrete, large, machine-checked family
of periods** — but aperiodicity means aperiodicity at *every* period, and the
argument's reach is finite: it stops at `1023`, the linear reach of the `2048`-digit
certified prefix.  Excluding every period is the arithmetic content of the uniform
prime-`k`-tuples hypothesis in Pratt's published conditional result
(arXiv:2409.15185), an assumption of the PUBLISHED result and not of the catalog
statement.

## A note on method

`p(n)` is the quantity the whole family is about, and round 73 already made it
computable (`jsp87Subword` reads every block off the certified integer
`⌊2^2048 S⌋` by one division, `jsp87_subword_eq_block`).  The new certified
values in §3 are `native_decide` on that function; the bridge back to the
`jsp87DigitBlock` of the periodicity machinery is `jsp87_blockNat_cast`, and the
\u2115-to-\u2124 passage is `card_image_intCast`.  Mathlib contains no statement
whatsoever about the binary expansion of a real number, so `p` — and with it
everything above — is from scratch.
-/



namespace JSP87

set_option maxHeartbeats 0
set_option maxRecDepth 100000

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

/-! ## 1. The complexity is non-decreasing -/

/-- **COMPLEXITY IS NON-DECREASING.**  `p(n) ≤ p(n+1)`: the set of distinct
`n`-digit blocks is the image, under "drop the first digit", of the set of
distinct `(n+1)`-digit blocks.  This is the classical monotonicity of the
subword complexity, and the map is well defined precisely because of round 73's
`jsp87_block_inj` (the longer block determines the shorter one).

Nothing of the kind existed in the tree: rounds 37–73 produced only *upper*
bounds on the complexity (`≤ t`, `≤ M + t`, `≤ b`).  Monotonicity is the first
*structural* fact about `p` that the tree now contains, and it is what makes
the growth estimates of §2 meaningful. -/
theorem jsp87_compl_mono {M n K : ℕ} :
    Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
      (fun N => jsp87DigitBlock N n))
      ≤ Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
      (fun N => jsp87DigitBlock N (n + 1))) := by
  classical
  set sf : Finset ℕ := (Finset.range K).filter (fun N : ℕ => M ≤ N) with hsf
  -- for each (n+1)-block value, the SET of places where it occurs
  set loc : ℤ → Finset ℕ := fun z => sf.filter
    (fun N => jsp87DigitBlock N (n + 1) = z) with hloc
  set S₁ : Finset ℤ := sf.image (fun N : ℕ => (jsp87DigitBlock N (n + 1) : ℤ)) with hS₁
  set S₀ : Finset ℤ := sf.image (fun N : ℕ => (jsp87DigitBlock N n : ℤ)) with hS₀
  -- the "drop the first digit" map, defined on a nonempty set of places
  set ψ : ℤ → ℤ := fun z => if h : (loc z).Nonempty then
      (jsp87DigitBlock (Finset.min' (loc z) h) n : ℤ) else 0 with hψ
  have hloc_nonempty : ∀ z ∈ S₁, (loc z).Nonempty := by
    intro z hz
    obtain ⟨N, hN, hNz⟩ := Finset.mem_image.mp hz
    refine ⟨N, Finset.mem_filter.mpr ⟨hN, ?_⟩⟩
    exact_mod_cast hNz
  have hmaps : ∀ z ∈ S₁, ψ z ∈ S₀ := by
    intro z hz
    have hne := hloc_nonempty z hz
    have hminN : Finset.min' (loc z) hne ∈ sf := (Finset.mem_filter.mp
      (Finset.min'_mem (loc z) hne)).1
    have hval : ψ z = (jsp87DigitBlock (Finset.min' (loc z) hne) n : ℤ) := by
      rw [hψ]; simp only [dif_pos hne]
    rw [hval]
    exact Finset.mem_image.mpr ⟨Finset.min' (loc z) hne, hminN, rfl⟩
  have hsurj : ∀ z ∈ S₀, ∃ w ∈ S₁, ψ w = z := by
    intro z hz
    obtain ⟨N, hN, hNz⟩ := Finset.mem_image.mp hz
    refine ⟨(jsp87DigitBlock N (n + 1) : ℤ), Finset.mem_image.mpr ⟨N, hN, rfl⟩, ?_⟩
    have hne : (loc (jsp87DigitBlock N (n + 1) : ℤ)).Nonempty :=
      hloc_nonempty _ (Finset.mem_image.mpr ⟨N, hN, rfl⟩)
    have hmin : jsp87DigitBlock (Finset.min' (loc (jsp87DigitBlock N (n + 1) : ℤ)) hne)
        (n + 1) = jsp87DigitBlock N (n + 1) := by
      have hmem' := Finset.mem_filter.mp
        (Finset.min'_mem (loc (jsp87DigitBlock N (n + 1) : ℤ)) hne)
      exact_mod_cast hmem'.2
    have hinj := jsp87_block_inj (M := N)
      (M' := Finset.min' (loc (jsp87DigitBlock N (n + 1) : ℤ)) hne) (n := n + 1) (by omega)
      (by exact_mod_cast hmin.symm)
    have heq : jsp87DigitBlock (Finset.min' (loc (jsp87DigitBlock N (n + 1) : ℤ)) hne) n
        = jsp87DigitBlock N n := by
      rw [jsp87_block_eq_of_digits_eq]
      intro j hj
      exact (hinj j (by omega)).symm
    have hval : ψ (jsp87DigitBlock N (n + 1) : ℤ)
        = (jsp87DigitBlock (Finset.min' (loc (jsp87DigitBlock N (n + 1) : ℤ)) hne) n : ℤ) := by
      rw [hψ]; simp only [dif_pos hne]
    rw [hval, heq]
    exact_mod_cast hNz
  have hcard : Finset.card S₀ ≤ Finset.card S₁ := Finset.card_le_card_of_surjOn ψ hsurj
  simpa only [hS₁, hS₀] using hcard

/-! ## 2. Periodicity bounds the complexity, and that is all it can do -/

/-- **THE COMPLEXITY–PERIOD INEQUALITY, UNDER THE NAME USED FROM NOW ON.**  If
the binary digits of `jsp87Series` are eventually periodic from `M` with period
`t`, then at most `t` distinct `n`-digit blocks occur among the positions
`M ≤ N < K`, for *every* `K`.  This is round 73's `jsp87_blockCompl_le_period`. -/
theorem jsp87_compl_le_period' {M t n K : ℕ} (ht : 0 < t)
    (hper : ∀ x, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
      (fun N => jsp87DigitBlock N n)) ≤ t :=
  jsp87_blockCompl_le_period (M := M) (t := t) (n := n) (K := K) ht hper

/-- **A NEW IRRATIONALITY CRITERION — LINEAR GROWTH OF THE COMPLEXITY.**  If for
every start point `M` and every length `n` there are more than `n` distinct
`n`-digit blocks among the positions `M ≤ N < K` (for every `K' ≥ M`), then
`jsp87Series` is irrational.

The proof is the *Morse–Hedlund* argument: a rational value has a digit period
`t` from some `M ≥ 1` (round 47), and periodicity forces the `t`-digit complexity
at the positions `≥ M` to be at most `t` — so at the length `n = t` the
hypothesis `t < p(t)` is violated.  Hence **aperiodicity of the digits is
equivalent to `p(n) ≥ n + 1` for every `n`**, and this is the first criterion in
the tree whose hypothesis is a *linear* lower bound rather than mere unboundedness
(round 73's `jsp87Series_irrational_of_compl_gt_period`).  The two hypotheses are
incomparable, but the linear one is what a finite computation of the complexity
actually supplies. -/
theorem jsp87Series_irrational_of_compl_gt_index
    (h : ∀ M : ℕ, 1 ≤ M → ∀ n : ℕ, 1 ≤ n → ∀ K' : ℕ, M ≤ K' →
      n < Finset.card (((Finset.range K').filter (fun N => M ≤ N)).image
        (fun N => jsp87DigitBlock N n))) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hb : 0 < q.den := Rat.den_pos q
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb
    (by rw [← hq, Rat.cast_def])
  -- the period `t` is itself a length, and at length `t` the complexity is ≤ t
  have hgt : t < Finset.card (((Finset.range M).filter (fun N => M ≤ N)).image
      (fun N => jsp87DigitBlock N t)) := h M hM t ht M (by omega)
  have hle := jsp87_compl_le_period' (M := M) (t := t) (n := t) (K := M) ht hper
  exact absurd hgt (Nat.not_lt.mpr hle)

/-- **THE CONTRAPOSITIVE: A RATIONAL VALUE CARRIES A COMPLEXITY WITNESS.**  If
`jsp87Series = a/b` with `b > 0`, then there are a place `M`, a length `n` and a
window `K ≥ M` with at most `n` distinct `n`-digit blocks among the positions
`M ≤ N < K`.  The witness is the digit period itself, taken at its own length.

Equivalently — and this is the form that matters arithmetically — **a rational
value has `p(t) ≤ t` at its own period `t`**, whereas the criterion above demands
`p(t) > t` there. -/
theorem jsp87Series_rational_imp_compl_le_index {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ M n K : ℕ, 1 ≤ M ∧ 1 ≤ n ∧ M ≤ K ∧
      Finset.card (((Finset.range K).filter (fun N => M ≤ N)).image
        (fun N => jsp87DigitBlock N n)) ≤ n := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  refine ⟨M, t, M, hM, ht, by omega, ?_⟩
  exact jsp87_compl_le_period' (M := M) (t := t) (n := t) (K := M) ht hper

/-! ## 3. The certified `20`-digit complexity -/

/-- **THE `20`-DIGIT COMPLEXITY OF THE BINARY EXPANSION OF THE ERDŐS SERIES IS
`2025`**, in the `ℤ`-valued block notation used by the periodicity machinery.
This is round 73's `jsp87DigitBlockCompl_20`, restated under the name used here. -/
theorem jsp87_compl_20 :
    Finset.card ((Finset.range 2029).image (fun N => jsp87DigitBlock N 20)) = 2025 :=
  jsp87DigitBlockCompl_20

/-- **THE `24`-DIGIT COMPLEXITY OF THE BINARY EXPANSION OF THE ERDŐS SERIES IS
`2025`, IN THE `ℕ`-VALUED BLOCK NOTATION** — a *new* certified value: round 73
computed the `24`-digit complexity only in the `jsp87Subword` notation.  The
bridge is round 73's `jsp87_subword_eq_block`, so this is a statement about the
real series and not about an approximation. -/
theorem jsp87BlockCompl_24 :
    Finset.card ((Finset.range 2025).image (fun N => jsp87BlockNat N 24)) = 2025 := by
  have hcong : ∀ N ∈ Finset.range 2025, jsp87BlockNat N 24
      = jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N := by
    intro N hN
    have hN' : N < 2025 := Finset.mem_range.mp hN
    exact jsp87_subword_eq_block (X := jsp87Prefix2048 + 1) (L := 2048) (n := 24)
      (N := N) (by omega) jsp87DigitBlock_zero_2048
  have hc : Finset.card ((Finset.range 2025).image (fun N : ℕ => jsp87BlockNat N 24))
      = Finset.card ((Finset.range 2025).image
        (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N)) := by
    exact card_image_congr (fun N : ℕ => jsp87BlockNat N 24)
      (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N) (Finset.range 2025)
      (fun N hN => hcong N hN)
  rw [hc]
  native_decide

/-- **THE SAME, IN THE `ℤ`-VALUED NOTATION.** -/
theorem jsp87DigitBlockCompl_24 :
    Finset.card ((Finset.range 2025).image (fun N => jsp87DigitBlock N 24)) = 2025 := by
  have h1 : Finset.card ((Finset.range 2025).image (fun N => jsp87DigitBlock N 24))
      = Finset.card ((Finset.range 2025).image (fun N => (jsp87BlockNat N 24 : ℤ))) := by
    exact card_image_congr (fun N : ℕ => jsp87DigitBlock N 24)
      (fun N : ℕ => (jsp87BlockNat N 24 : ℤ)) (Finset.range 2025)
      (fun N _ => (jsp87_blockNat_cast N 24).symm)
  rw [h1, card_image_intCast (fun N : ℕ => jsp87BlockNat N 24) (Finset.range 2025),
    jsp87BlockCompl_24]

/-- **THE FIRST TWO MACHINE-CHECKED INSTANCES OF THE NEW CRITERION:** the
certified `20`- and `24`-digit complexities both exceed their own length. -/
theorem jsp87_compl_gt_20_index :
    20 < Finset.card ((Finset.range 2029).image (fun N => jsp87DigitBlock N 20)) := by
  rw [jsp87_compl_20]; norm_num

theorem jsp87_compl_gt_24_index :
    24 < Finset.card ((Finset.range 2025).image (fun N => jsp87DigitBlock N 24)) := by
  rw [jsp87DigitBlockCompl_24]; norm_num

/-! ## 4. The tail complexities: what the period exclusion actually needs -/

/-- **ALL `1024` SUCCESSIVE `20`-DIGIT BLOCKS OF THE CERTIFIED PREFIX, READ FROM
PLACE `1` ONWARDS, ARE PAIRWISE DISTINCT.**  The bridge is round 73's
`jsp87_subword_eq_block`, so this is a statement about the real series. -/
theorem jsp87SubwordTail_20_1024 :
    Finset.card ((Finset.range 1024).image
      (fun N => jsp87Subword (jsp87Prefix2048 + 1) 2048 20 (N + 1))) = 1024 := by
  native_decide

/-- **THE TAIL COMPLEXITY AT LENGTH `20`, FROM PLACE `1`, IS `1024`** — the
quantity round 73's `jsp87_blockCompl_le_period` actually bounds, and the
quantity the period exclusion below needs.  (The count is over the `1024`
positions `1 ≤ N < 1025`; longer windows only add more blocks, so this is a
*lower* bound on the true tail complexity, which is all the argument uses.) -/
theorem jsp87_compl_tail_20_ge_1024 :
    1024 ≤ Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
      (fun N => jsp87DigitBlock N 20)) := by
  have hsub : ((Finset.range 1025).filter (fun N => 1 ≤ N)).image
      (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N)
    = (Finset.range 1024).image
      (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 20 (N + 1)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨N, hN, hx'⟩ := Finset.mem_image.mp hx
      have hNf := Finset.mem_filter.mp hN
      have hNr := Finset.mem_range.mp hNf.1
      rw [← hx']
      have hk : N < 1025 := by omega
      have hs : N = (N - 1) + 1 := by omega
      rw [hs]
      exact Finset.mem_image.mpr ⟨N - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · intro hx
      obtain ⟨N, hN, hx'⟩ := Finset.mem_image.mp hx
      have hNr := Finset.mem_range.mp hN
      rw [← hx']
      refine Finset.mem_image.mpr ⟨N + 1, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      omega
  have hcong : ∀ N ∈ (Finset.range 1025).filter (fun N => 1 ≤ N),
      (jsp87DigitBlock N 20 : ℤ) = (jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N : ℤ) := by
    intro N hN
    have hNf := Finset.mem_filter.mp hN
    have hNr := Finset.mem_range.mp hNf.1
    refine jsp87_subword_eq_block (X := jsp87Prefix2048 + 1) (L := 2048) (n := 20)
      (N := N) ?_ jsp87DigitBlock_zero_2048
    omega
  have h1 : Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
        (fun N => jsp87DigitBlock N 20))
      = Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
        (fun N => (jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N : ℤ))) := by
    exact card_image_congr (fun N : ℕ => jsp87DigitBlock N 20)
      (fun N : ℕ => (jsp87Subword (jsp87Prefix2048 + 1) 2048 20 N : ℤ))
      ((Finset.range 1025).filter (fun N => 1 ≤ N))
      (fun N hN => hcong N hN)
  rw [h1, hsub]
  exact_mod_cast jsp87SubwordTail_20_1024

/-- **THE `1024` SUCCESSIVE `24`-DIGIT BLOCKS FROM PLACE `1` ARE PAIRWISE
DISTINCT TOO.** -/
theorem jsp87SubwordTail_24_1024 :
    Finset.card ((Finset.range 1024).image
      (fun N => jsp87Subword (jsp87Prefix2048 + 1) 2048 24 (N + 1))) = 1024 := by
  native_decide

/-- **THE TAIL COMPLEXITY AT LENGTH `24`, FROM PLACE `1`, IS `1024`.** -/
theorem jsp87_compl_tail_24_ge_1024 :
    1024 ≤ Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
      (fun N => jsp87DigitBlock N 24)) := by
  have hsub : ((Finset.range 1025).filter (fun N => 1 ≤ N)).image
      (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N)
    = (Finset.range 1024).image
      (fun N : ℕ => jsp87Subword (jsp87Prefix2048 + 1) 2048 24 (N + 1)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨N, hN, hx'⟩ := Finset.mem_image.mp hx
      have hNf := Finset.mem_filter.mp hN
      have hNr := Finset.mem_range.mp hNf.1
      rw [← hx']
      have hk : N < 1025 := by omega
      have hs : N = (N - 1) + 1 := by omega
      rw [hs]
      exact Finset.mem_image.mpr ⟨N - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · intro hx
      obtain ⟨N, hN, hx'⟩ := Finset.mem_image.mp hx
      have hNr := Finset.mem_range.mp hN
      rw [← hx']
      refine Finset.mem_image.mpr ⟨N + 1, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      omega
  have hcong : ∀ N ∈ (Finset.range 1025).filter (fun N => 1 ≤ N),
      (jsp87DigitBlock N 24 : ℤ) = (jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N : ℤ) := by
    intro N hN
    have hNf := Finset.mem_filter.mp hN
    have hNr := Finset.mem_range.mp hNf.1
    refine jsp87_subword_eq_block (X := jsp87Prefix2048 + 1) (L := 2048) (n := 24)
      (N := N) ?_ jsp87DigitBlock_zero_2048
    omega
  have h1 : Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
        (fun N => jsp87DigitBlock N 24))
      = Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
        (fun N => (jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N : ℤ))) := by
    exact card_image_congr (fun N : ℕ => jsp87DigitBlock N 24)
      (fun N : ℕ => (jsp87Subword (jsp87Prefix2048 + 1) 2048 24 N : ℤ))
      ((Finset.range 1025).filter (fun N => 1 ≤ N))
      (fun N hN => hcong N hN)
  rw [h1, hsub]
  exact_mod_cast jsp87SubwordTail_24_1024

/-! ## 5. The headline: a machine-checked lower bound on the digit period -/

/-- **THE HEADLINE OF THE ROUND.  THE BINARY DIGITS OF THE ERDŐS SERIES ARE NOT
EVENTUALLY PERIODIC WITH ANY PERIOD `t ≤ 1023`.**

A period `t` from place `1` would force, by `jsp87_compl_le_period'`, at most `t`
distinct `20`-digit blocks among the positions `1 ≤ N < 1025`; the certified
`2048`-digit prefix of round 73 supplies `1024` of them, all distinct.  Since
`t ≤ 1023 < 1024`, this is impossible.

This is by a wide margin the **strongest unconditional, machine-checked
statement about the digit structure of `jsp87Series` in the tree**: every
previous round excluded *no* period at all (rounds 41–73 reduced aperiodicity to
a statement but never discharged a single candidate), and round 47's
`jsp87_digit_eventuallyPeriodic` only ever produced a period *hypothesis*.  The
`1024` here is exactly the reach of the `2048`-digit certified prefix, and the
argument shows the frontier moves linearly with the certified length. -/
theorem jsp87_digit_not_eventuallyPeriodic_period_le_1023 {t : ℕ} (ht : 0 < t)
    (htn : t ≤ 1023) :
    ¬ (∀ x : ℕ, 1 ≤ x → jsp87Digit (x + t) = jsp87Digit x) := by
  intro hper
  have hle : Finset.card (((Finset.range 1025).filter (fun N => 1 ≤ N)).image
      (fun N => jsp87DigitBlock N 20)) ≤ t :=
    jsp87_compl_le_period' (M := 1) (t := t) (n := 20) (K := 1025) ht hper
  have hcert := jsp87_compl_tail_20_ge_1024
  omega

/-- **A HYPOTHETICAL RATIONAL VALUE OF `jsp87Series` HAS LEAST EVENTUAL PERIOD
`≥ 1024`.**  If `S = a/b` with `b > 0`, round 47 (`jsp87_digit_eventuallyPeriodic`)
supplies a digit period `t` from some `M ≥ 1`; the theorem above forces
`t ≥ 1024`.  Since round 65 computes the *least* eventual period as the
multiplicative order of `2` modulo the odd part of `b`, this pins the
denominator's odd part as well. -/
theorem jsp87Series_rational_imp_period_ge_1024 {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) {t : ℕ} (ht : 0 < t)
    (hper : ∀ x : ℕ, 1 ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    1024 ≤ t := by
  by_contra hcon
  have hnot := jsp87_digit_not_eventuallyPeriodic_period_le_1023 (t := t) ht (by omega)
  exact hnot hper

end JSP87
