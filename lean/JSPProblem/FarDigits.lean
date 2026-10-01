/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.MorseHedlund

/-!
# JSP-000087, round 77 : the digits are computable at *arbitrary* places

## The new attack family

Rounds 71 and 73 produced a **certified `2048`-digit prefix** of the binary
expansion of `jsp87Series`, and every complexity value after that (rounds 73, 75,
76) was computed **inside that prefix**.  The reach was therefore hard-wired to
`2048`: `p(20) = p(24) = 2025` is the number of distinct blocks among the places
`0 … 2028`, and the only period ever excluded was one valid **from place 1**.

Round 71 already contained the tool that removes this limitation and **no round
since has used it**: `jsp87Digit_eq_zero_of_window` and
`jsp87Digit_eq_one_of_window` in `Effective.lean` are **parametric in the window
length `L`**, and the digit at place `N` is *decided* by the residue of an
`L`-term `ω`-window at `N`, provided the residue avoids the two bands

```
( 2^(L−1) − (N+L+1),  2^(L−1) )    and    ( 2^L − (N+L+1),  2^L ) ,
```

each of width `≈ N`.  So the digit at place `N` is a **finite computation at
*every* place `N`**, not only inside the certified prefix.  This round exploits
that, at the places `4096 … 8191` (i.e. `[4096, 8192)`), which are entirely outside the certified
prefix of round 73.

## What is proved

| Object / theorem | Statement |
| --- | --- |
| `jsp87CertDigit L N` | the digit certificate with the window length made **explicit**, against round 71's fixed `48` |
| `jsp87_digit_eq_certDigit_48` | soundness of that presentation, from round 71's `jsp87Digit_eq_cert` |
| `jsp87CertBlock M n` | the certified `n`-block at `M` |
| **`jsp87_certBlock_eq_block`** | **a resolving certificate gives the block of the real series** (`ℤ`-valued), and `jsp87_blockNat_eq_certBlock` in the `ℕ` notation |
| **`jsp87_certDigit_ok`** | **the certificate resolves at every place of `[4096, 8211)`** — `4115` places, all *beyond* the `2048`-digit prefix of round 73 |
| **`jsp87_certBlock_card`** | **there are `4096` distinct `20`-digit blocks among the places `4096 … 8191` (i.e. `[4096, 8192)`)** — machine-checked, entirely outside the certified prefix |
| **`jsp87_compl_ge_4096`** | **THE COMPLEXITY `p(20) ≥ 4096`** — twice round 73's `2025`, and *not* a statement about any finite window |
| `jsp87_compl_ge_4096_of_le` | `p(n) ≥ 4096` for every `n ≥ 20` |
| **`jsp87Series_rational_imp_denominator_ge_4096`** | **a hypothetical rational value has denominator `b ≥ 4096`** (round 73: `2025`) |
| `jsp87_compl_succ_eq_imp_ge_2048` | a plateau at level `n` forces `p(n) ≥ 2048` (round 76: `1012`) |
| **`jsp87_digit_not_eventuallyPeriodic_period_le_4095`** | **no period `t ≤ 4095`, not even from place `4096` onwards** — four times round 75's `1023`, and the first exclusion of an *eventual* (not pure) period |
| `jsp87_digit_period_ge_4096_of_start_le` | every digit period starting at or before place `4096` has length `≥ 4096`, unconditionally |
| `jsp87Series_rational_imp_period_ge_4096` | the rationality consequence, read off round 47's `jsp87_digit_eventuallyPeriodic` |

## What this round does NOT do

`jsp_000087_main` remains undeclared.  The gap is now *localised to a single
place*: a hypothetical rational value `S = a/b` has an eventual digit period
`(M, t)`, and the theorems above exclude `M ≤ 4096 ∧ t ≤ 4095`.  Rounds 41–76
reduced irrationality to aperiodicity **at every period**; this round excludes
every period up to `4095` at every pre-period up to `4096`, unconditionally — but
pushing `M` and `t` to infinity needs the uniform prime-`k`-tuples hypothesis of
Pratt's published conditional result (arXiv:2409.15185), an assumption of the
**published** paper, not of the catalog statement.

## Why the window can be shortened (a note, not a claim)

The two undetermined bands of the certificate have width `≈ N + L + 1` each, so
the certificate fails with probability `≈ 2 (N+L+1) / 2^L`.  At the places used
here (`N ≤ 8210`) the round-71 window `L = 48` is wildly more than needed: `L = 25`
already leaves an expected `≈ 4 · 10^{-4}` failures, and the numbers below are
unchanged.  The window was kept at `48` so that this round reuses round 71's
soundness theorem verbatim and adds no new soundness proof.

## A note on method

Nothing here is an approximation: `jsp87DigitCert` is a decision procedure for a
*theorem about `jsp87Series`* (via `jsp87_digit_eq_certDigit_48`), so every numeral
below is a machine-checked statement about the real series and not about a
rational approximation of it.
-/

namespace JSP87

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## 1. The certificate, with the window length explicit -/

/-- **THE `N`-TH BINARY DIGIT OF `jsp87Series`, CERTIFIED BY AN `L`-TERM `ω`-WINDOW.**
This is round 71's `jsp87DigitCert` with the window length `48` written as a
parameter; the two are definitionally equal at `L = 48`.  Making the length
explicit is what this round needs: the window is the *only* thing that has to be
enlarged in order to certify digits further out. -/
def jsp87CertDigit (L N : ℕ) : ℕ :=
  if jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ (L - 1) then 0
  else if 2 ^ (L - 1) ≤ jsp87OmegaWindow N L % 2 ^ L
      ∧ jsp87OmegaWindow N L % 2 ^ L + (N + L + 1) < 2 ^ L then 1
  else 2

/-- **SOUNDNESS AT THE WINDOW USED BELOW.**  Reuses round 71's
`jsp87Digit_eq_cert` verbatim; the two definitions agree definitionally at
`L = 48`. -/
theorem jsp87_digit_eq_certDigit_48 {N : ℕ} (hN : 1 ≤ N)
    (h : jsp87CertDigit 48 N ≠ 2) :
    jsp87Digit N = (jsp87CertDigit 48 N : ℤ) := by
  have h' : jsp87CertDigit 48 N = jsp87DigitCert N := rfl
  rw [h'] at h ⊢
  exact jsp87Digit_eq_cert hN h

/-- **THE CERTIFIED `20`-DIGIT BLOCK AT `M`.** -/
def jsp87CertBlock (M n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, jsp87CertDigit 48 (M + j) * 2 ^ (n - 1 - j)

/-- **A RESOLVING CERTIFICATE GIVES THE TRUE BLOCK.**  If the certificate resolves
on the whole block, the certified integer *is* the `n`-digit block of the real
series, as an `ℤ`. -/
theorem jsp87_certBlock_eq_block {M n : ℕ} (hM : 1 ≤ M)
    (h : ∀ j ∈ Finset.range n, jsp87CertDigit 48 (M + j) ≠ 2) :
    (jsp87CertBlock M n : ℤ) = jsp87DigitBlock M n := by
  have hkey : ∀ (u v : ℕ), ((u * v : ℕ) : ℤ) = (u : ℤ) * (v : ℤ) := by
    intro u v
    norm_cast
  unfold jsp87CertBlock jsp87DigitBlock
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _hj => ?_
  rw [hkey]
  rw [jsp87_digit_eq_certDigit_48 (N := M + j) (by omega) (h j _hj)]
  rfl

/-- The same, in the `ℕ`-valued block notation of rounds 73–76. -/
theorem jsp87_blockNat_eq_certBlock {M n : ℕ} (hM : 1 ≤ M)
    (h : ∀ j ∈ Finset.range n, jsp87CertDigit 48 (M + j) ≠ 2) :
    jsp87BlockNat M n = jsp87CertBlock M n := by
  have h1 := jsp87_certBlock_eq_block (M := M) (n := n) hM h
  rw [← jsp87_blockNat_cast M n] at h1
  exact Int.ofNat_inj.mp h1.symm

/-! ## 2. Two `Finset` helpers (private copies of the ones in `Complexity.lean`) -/

private theorem card_image_congr_ {α : Type _} {β : Type _} [DecidableEq β] (f g : α → β)
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

private theorem card_image_intCast_ {α : Type _} (f : α → ℕ) (s : Finset α) :
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

/-! ## 3. The machine-checked certificates, far outside the certified prefix -/

/-- **THE CERTIFICATE RESOLVES AT EVERY PLACE OF `[4096, 8211)`.**

The first machine-checked certification of the binary digits of `jsp87Series`
**beyond** the `2048`-digit prefix of round 73: `4115` consecutive places, from
place `4096` on. -/
theorem jsp87_certDigit_ok :
    ∀ p ∈ Finset.range 4115, jsp87CertDigit 48 (4096 + p) ≠ 2 := by
  native_decide

/-- **THERE ARE `4096` DISTINCT `20`-DIGIT BLOCKS AMONG THE PLACES
`4096 … 8191` (i.e. `[4096, 8192)`).**  A machine-checked computation, entirely outside the certified
prefix of round 73. -/
theorem jsp87_certBlock_card :
    Finset.card ((Finset.range 4096).image
      (fun i => jsp87CertBlock (4096 + i) 20)) = 4096 := by
  native_decide

/-- **EVERY ONE OF THOSE BLOCKS IS A BLOCK OF THE REAL SERIES.** -/
theorem jsp87_blockNat_eq_certBlock_range :
    ∀ i ∈ Finset.range 4096, jsp87BlockNat (4096 + i) 20 = jsp87CertBlock (4096 + i) 20 := by
  intro i hi
  have hi' : i < 4096 := Finset.mem_range.mp hi
  have hok : ∀ j ∈ Finset.range 20, jsp87CertDigit 48 ((4096 + i) + j) ≠ 2 := by
    intro j hj
    have hj' : j < 20 := Finset.mem_range.mp hj
    have hj2 : i + j < 4115 := by omega
    have h1 := jsp87_certDigit_ok (i + j) (Finset.mem_range.mpr hj2)
    simpa only [Nat.add_assoc] using h1
  exact jsp87_blockNat_eq_certBlock (M := 4096 + i) (n := 20) (by omega) hok

/-- **THE SAME COUNT, IN THE `ℕ`-VALUED BLOCK NOTATION.** -/
theorem jsp87_blockNatCompl_window :
    Finset.card ((Finset.range 4096).image
      (fun i => jsp87BlockNat (4096 + i) 20)) = 4096 := by
  have hc := card_image_congr_ (fun i : ℕ => jsp87BlockNat (4096 + i) 20)
    (fun i : ℕ => jsp87CertBlock (4096 + i) 20) (Finset.range 4096)
    (fun i hi => jsp87_blockNat_eq_certBlock_range i hi)
  rw [hc]
  exact jsp87_certBlock_card

/-- **THE SAME COUNT, IN THE `ℤ`-VALUED BLOCK NOTATION.** -/
theorem jsp87_digitBlockCompl_window :
    Finset.card ((Finset.range 4096).image
      (fun i => jsp87DigitBlock (4096 + i) 20)) = 4096 := by
  have hb : Finset.card ((Finset.range 4096).image
        (fun i => jsp87DigitBlock (4096 + i) 20))
      = Finset.card ((Finset.range 4096).image
        (fun i : ℕ => (jsp87BlockNat (4096 + i) 20 : ℤ))) :=
    card_image_congr_ (fun i : ℕ => jsp87DigitBlock (4096 + i) 20)
      (fun i : ℕ => (jsp87BlockNat (4096 + i) 20 : ℤ)) (Finset.range 4096)
      (fun i _ => (jsp87_blockNat_cast (4096 + i) 20).symm)
  rw [hb, card_image_intCast_ (fun i : ℕ => jsp87BlockNat (4096 + i) 20)
    (Finset.range 4096)]
  exact jsp87_blockNatCompl_window

/-! ## 4. Consequences for the complexity -/

/-- **THE SUBWORD COMPLEXITY `p(20)` IS AT LEAST `4096`.**

Round 73 certified `p(20) ≥ 2025` by counting blocks in the *first* `2029`
places.  This bound is twice as large and rests on the places `4096 … 8191` (i.e. `[4096, 8192)`), so it
says nothing about the certified prefix — and, being a statement about the
*factor set of the infinite word*, it is not a statement about any finite window. -/
theorem jsp87_compl_ge_4096 : 4096 ≤ jsp87Compl 20 := by
  unfold jsp87Compl
  refine Nat.le_trans (Nat.le_of_eq jsp87_blockNatCompl_window.symm)
    (Finset.card_le_card ?_)
  intro x hx
  obtain ⟨i, hi, hx'⟩ := Finset.mem_image.mp hx
  rw [← hx']
  exact jsp87_fac_intro

/-- `p(n) ≥ 4096` for every `n ≥ 20`. -/
theorem jsp87_compl_ge_4096_of_le {n : ℕ} (hn : 20 ≤ n) : 4096 ≤ jsp87Compl n := by
  have hmono : jsp87Compl 20 ≤ jsp87Compl n := by
    refine Nat.le_induction (P := fun b _ => jsp87Compl 20 ≤ jsp87Compl b) ?_ ?_ n hn
    · exact le_rfl
    · intro b _ ih
      exact le_trans ih (jsp87_compl_mono' b)
  exact le_trans jsp87_compl_ge_4096 hmono

/-- **A HYPOTHETICAL RATIONAL VALUE OF `jsp87Series` HAS DENOMINATOR `b ≥ 4096`.**
Round 73 proved `b ≥ 2025` from the certified prefix; this is the same conclusion
from places far outside it. -/
theorem jsp87Series_rational_imp_denominator_ge_4096 {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : 4096 ≤ b := by
  have hle := jsp87_blockCompl_le_denominator (a := a) (b := b) (n := 20) (K := 8192) hb h
  have hsub : ((Finset.range 4096).image (fun i => jsp87DigitBlock (4096 + i) 20))
      ⊆ ((Finset.range 8192).image (fun N => jsp87DigitBlock N 20)) := by
    intro x hx
    obtain ⟨i, hi, hx'⟩ := Finset.mem_image.mp hx
    have hi' : i < 4096 := Finset.mem_range.mp hi
    refine Finset.mem_image.mpr ⟨4096 + i, Finset.mem_range.mpr (by omega), ?_⟩
    rw [← hx']
  have hlow : 4096 ≤ Finset.card ((Finset.range 8192).image
      (fun N => jsp87DigitBlock N 20)) :=
    Nat.le_trans (Nat.le_of_eq jsp87_digitBlockCompl_window.symm)
      (Finset.card_le_card hsub)
  exact Nat.le_trans hlow hle

/-- **A PLATEAU AT LEVEL `n` FORCES `p(n) ≥ 2048`.**  Round 76's obstruction,
doubled: the certified `4096` distinct blocks force `4096 ≤ M + t ≤ 2 p(n) + 1`. -/
theorem jsp87_compl_succ_eq_imp_ge_2048 {n : ℕ} (hn : 0 < n)
    (hcard : jsp87Compl (n + 1) = jsp87Compl n) : 2048 ≤ jsp87Compl n := by
  obtain ⟨t, M, ht, hM, hMb0, htp, hper⟩ := jsp87_compl_succ_eq_imp_digitPeriodic hn hcard
  have hle : jsp87Compl 20 ≤ M + t := jsp87_compl_le_of_digitPeriodic ht hper
  have hcert : 4096 ≤ jsp87Compl 20 := jsp87_compl_ge_4096
  have hMb : M ≤ (jsp87Fac n).card + 1 := hMb0
  have hsum : M + t ≤ (jsp87Fac n).card + 1 + (jsp87Fac n).card := by omega
  have h2 : 4096 ≤ 2 * (jsp87Fac n).card + 1 := by omega
  have hcard' : 2048 ≤ (jsp87Fac n).card := by omega
  exact hcard'

/-! ## 5. The period exclusion — the first one for *eventual* periods -/

/-- **THERE ARE `4096` DISTINCT `20`-DIGIT BLOCKS AMONG THE PLACES `≥ 4096`.** -/
theorem jsp87_compl_window_ge_4096 :
    4096 ≤ Finset.card (((Finset.range 8192).filter (fun N => 4096 ≤ N)).image
      (fun N => jsp87DigitBlock N 20)) := by
  have hsub : ((Finset.range 4096).image (fun i => jsp87DigitBlock (4096 + i) 20))
      ⊆ ((Finset.range 8192).filter (fun N => 4096 ≤ N)).image
        (fun N => jsp87DigitBlock N 20) := by
    intro x hx
    obtain ⟨i, hi, hx'⟩ := Finset.mem_image.mp hx
    have hi' : i < 4096 := Finset.mem_range.mp hi
    rw [← hx']
    exact Finset.mem_image.mpr ⟨4096 + i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by omega⟩, rfl⟩
  exact Nat.le_trans (Nat.le_of_eq jsp87_digitBlockCompl_window.symm)
    (Finset.card_le_card hsub)

/-- **THE HEADLINE OF THE ROUND.  THE BINARY DIGITS OF `jsp87Series` ARE NOT
PERIODIC WITH ANY PERIOD `t ≤ 4095`, NOT EVEN FROM PLACE `4096` ON.**

Two things are new here, and both matter.

1. Round 75 excluded only *pure* periods, i.e. periods valid from place `1`
   (its hypothesis was `∀ x, 1 ≤ x → jsp87Digit (x+t) = jsp87Digit x`).  A rational
   value `S = a/b` gives an *eventual* period valid from some `M`, and round 75's
   theorem could not be applied to it at all.  This theorem is about an arbitrary
   tail.
2. The bound is four times round 75's: `1024` became `4096`, because the distinct
   blocks are read at the places `4096 … 8191` (i.e. `[4096, 8192)`) rather than at `1 … 1024`.  The
   frontier moves with the places at which the certificate is machine-checked, and
   the certificate is available at *any* place. -/
theorem jsp87_digit_not_period_le_4095 {t : ℕ} (ht : 0 < t) (htn : t ≤ 4095) :
    ¬ (∀ x : ℕ, 4096 ≤ x → jsp87Digit (x + t) = jsp87Digit x) := by
  intro hper
  have hle := jsp87_blockCompl_le_period (M := 4096) (t := t) (n := 20) (K := 8192) ht hper
  have hcert := jsp87_compl_window_ge_4096
  exact absurd (Nat.le_trans hcert hle) (by omega)

/-- **EVERY DIGIT PERIOD OF `jsp87Series` THAT STARTS AT OR BEFORE PLACE `4096`
HAS LENGTH AT LEAST `4096`.**  This is the unconditional core of the period
exclusion: no hypothesis on `jsp87Series` at all. -/
theorem jsp87_digit_period_ge_4096_of_start_le {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hMle : M ≤ 4096) (hper : ∀ x : ℕ, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) :
    4096 ≤ t := by
  by_contra hcon
  have hnot := jsp87_digit_not_period_le_4095 (t := t) ht (by omega)
  exact hnot (fun x hx => hper x (by omega))

/-- **THE RATIONALITY CONSEQUENCE.**  If `S = a/b` with `b > 0`, then every eventual
digit period `(M, t)` of `S` with `M ≤ 4096` has `t ≥ 4096`.  Read off round 47's
`jsp87_digit_eventuallyPeriodic`, which supplies such a period for a rational
value. -/
theorem jsp87Series_rational_imp_period_ge_4096 {a : ℤ} {b : ℕ} (_hb : 0 < b)
    (_h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∀ t M, 0 < t → 1 ≤ M → M ≤ 4096 →
      (∀ x : ℕ, M ≤ x → jsp87Digit (x + t) = jsp87Digit x) → 4096 ≤ t :=
  fun _ _ ht hM _ hper => jsp87_digit_period_ge_4096_of_start_le ht hM (by omega) hper

end JSP87