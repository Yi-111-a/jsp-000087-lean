/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.BaseFamily
import JSPProblem.LambertGcd
import Mathlib.Tactic

/-!
# JSP-000087, round 85 : the rational shift — the multiplier family is one
# rational coset of `2 · S`, and its exact arithmetic

## The new attack family

Round 80 introduced the **multiplicative translations**

```
F m = ∑' n, ω (m * (n + 1)) · 2^-(n+1)          (jsp87Multiplier m)
```

and proved the flagship `jsp87_multiplier_eq`

```
F m = 2 · S + ω m − ∑_{p ∈ PF(m)} 1 / (2^p − 1) ,
```

so that every member of the family lies in the single rational coset
`2 · S + ℚ`.  Its policy record named two remaining pieces of arithmetic, and
this round supplies both.

1. **The shift, cleared.**  Round 80 deferred the irrationality transfer because
   "the shift is the image of a rational" needed cast bookkeeping.  Here the
   shift is *cleared*, i.e. written with natural coefficients only:
   `D m = ∏_{p ∈ PF(m)} (2^p − 1)` is round 39's `lambertDen`, and

   > **`jsp87LamNum`** — the new numerator `A s = ∑_{p ∈ s} D s / (2^p − 1)`;
   > **`jsp87LamSum_clear`** — THE CLEARED IDENTITY `(D s) · ∑_{p ∈ s} 1/(2^p − 1) = A s`;
   > **`jsp87_multiplier_clear`** — `(D m) · F m = 2 · S · D m + (ω m · D m − A m)`,
   > the last constant being a *natural* number (`jsp87LamNum_le`).

   `Irrational.of_add_intCast`, `Irrational.of_mul_ratCast` and
   `irrational_mul_intCast_iff` then give, with no `Rat` lemma and no truncated
   subtraction anywhere,

   > **`jsp87_multiplier_irrational_iff`** — **THE FLAGSHIP**
   > `Irrational jsp87Series ↔ Irrational (F m)` for every `m ≥ 1`,

   i.e. the headline is equivalent, term by term, to the irrationality of every
   member of a countable family of explicit series
   (`jsp87Series_irrational_iff_multiplier_all`,
   `jsp87Series_irrational_iff_exists_multiplier`,
   `jsp87_multiplier_irrational_iff_pow`,
   `jsp87_multiplier_irrational_two_pow` — the last at `m = 2^k`, where round 80
   computed the shift exactly as `2/3`).
2. **The shift is small, and rigid.**  `jsp87LamSum_lt_one` puts every finite
   Lambert sum of primes in `[0, 1)` (against the classical
   `∑'_p 1/(2^p − 1) = 2 S`), whence

   > **`jsp87_multiplier_eq_imp_card`**, **`jsp87_multiplier_eq_imp`** — two
   > translations coincide only if `ω m = ω n` **and** `lambertDen (PF m) =
   > lambertDen (PF n)`.

   For the second component one needs the **reduced** denominator, i.e.

   > **`jsp87LamNum_coprime`** — `gcd (A s) (D s) = 1` for every set of primes,

   proved from round 39's pairwise coprimality of the Mersenne numbers together
   with the new `lambertDen_erase` / `jsp87LamNum_erase` / `dvd_lamNum_erase`
   chain; and hence **`jsp87LamSum_eq_imp_den_eq`** (equal finite Lambert sums
   have equal clearing denominators) and
   **`jsp87_multiplier_imp_ne_den`** (distinct Mersenne products ⟹ distinct
   translations).

The one remaining input of the translation family is isolated as an explicit
hypothesis, not a gap: **`jsp87_multiplier_ne_iff_pf_ne`** and
**`jsp87_multiplier_ne_iff_den_ne`** state that the family is as big as the sets
of prime supports, *conditional on* `lambertDen` being injective on sets of
primes (a Zsigmondy-type statement, unknown, and not asserted anywhere in this
file).

## Why this still does not close the gate

Rationality of `S` transfers to the whole family, so the family is a *second
description* of the headline, not an independent route to it — exactly as round
80 recorded.  The missing statement is unchanged: the aperiodicity of the binary
digits of `S`, the content of the uniform prime-`k`-tuples hypothesis in Pratt's
published result (arXiv:2409.15185).
-/

namespace JSP87

open Filter

set_option maxHeartbeats 1000000

/-! ## 0. Two elementary finset lemmas -/

/-- A finite sum whose every term is divisible by `k` is divisible by `k`. -/
private theorem dvd_sum_of_div' (k : ℕ) : ∀ (s : Finset ℕ) (f : ℕ → ℕ),
    (∀ i ∈ s, k ∣ f i) → k ∣ ∑ i ∈ s, f i := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | @insert a t ha ih =>
    intro f hk
    rw [Finset.sum_insert ha]
    exact dvd_add (hk a (Finset.mem_insert_self a t))
      (ih f fun i hi => hk i (Finset.mem_insert_of_mem hi))

/-- A finite product whose every factor is coprime to `k` is coprime to `k`. -/
private theorem coprime_prod_left' (k : ℕ) : ∀ (s : Finset ℕ) (f : ℕ → ℕ),
    (∀ i ∈ s, Nat.Coprime (f i) k) → Nat.Coprime (∏ i ∈ s, f i) k := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | @insert a t ha ih =>
    intro f hk
    rw [Finset.prod_insert ha]
    exact Nat.Coprime.mul_left (hk a (Finset.mem_insert_self a t))
      (ih f fun i hi => hk i (Finset.mem_insert_of_mem hi))

/-- **A `ℕ`-cast of a Mersenne number is the corresponding `ℝ` difference.** -/
private theorem cast_pow_sub_one (p : ℕ) (hp : 1 ≤ p) :
    ((2 ^ p - 1 : ℕ) : ℝ) = (2 : ℝ) ^ p - 1 := by
  rw [Nat.cast_sub (by
    have := Nat.one_lt_two_pow (by omega : p ≠ 0)
    omega), Nat.cast_pow]
  push_cast
  ring

/-- `1 ≤ 2 ^ p - 1` for `p ≥ 1`. -/
private theorem one_le_pow_two_sub_one' {p : ℕ} (hp : p ≠ 0) : 1 ≤ 2 ^ p - 1 := by
  have h1 := Nat.one_lt_two_pow hp
  omega

/-- A Lambert summand at a prime is nonnegative. -/
private theorem lamTerm_nonneg {q : ℕ} (hq : 2 ≤ q) : 0 ≤ ((2 : ℝ) ^ q - 1)⁻¹ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ q - 1 := by linarith [two_pow_gt_one hq]
  exact (inv_pos.mpr hpos).le

/-- **A positive integer different from `1` has a nonempty prime support.** -/
private theorem primeFactors_nonempty_of_one_ne {m : ℕ} (hm : 1 ≤ m) (hne : m ≠ 1) :
    m.primeFactors.Nonempty := by
  obtain ⟨p, hp1, hp2⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hne
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp1, hp2, by omega⟩⟩

/-! ## 1. The cleared Lambert sum -/

/-- **The cleared numerator of the finite Lambert sum** `∑_{p ∈ s} 1/(2^p − 1)`:
the common denominator of the summands, divided term by term and summed. -/
noncomputable def jsp87LamNum (s : Finset ℕ) : ℕ :=
  ∑ p ∈ s, if p.Prime then lambertDen s / (2 ^ p - 1) else 0

/-- **THE ERASE IDENTITY.**  For a set of primes, `lambertDen` splits off any
one of its factors. -/
theorem lambertDen_erase {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {q : ℕ} (hq : q ∈ s) :
    lambertDen (s.erase q) * (2 ^ q - 1) = lambertDen s := by
  classical
  have h := Finset.prod_erase_mul s
    (f := fun p : ℕ => if p.Prime then 2 ^ p - 1 else 1) hq
  have h1 : (if q.Prime then 2 ^ q - 1 else 1) = 2 ^ q - 1 := ite_eq_left (hs q hq)
  simpa only [lambertDen, h1] using h

/-- **The `q`-th summand of the cleared numerator is the erase denominator.** -/
theorem jsp87LamTerm_eq_erase {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {q : ℕ} (hq : q ∈ s) :
    lambertDen s / (2 ^ q - 1) = lambertDen (s.erase q) := by
  have h := lambertDen_erase hs hq
  rw [← h, Nat.mul_div_cancel (lambertDen (s.erase q))
    (one_le_pow_two_sub_one' (hs q hq).ne_zero)]

/-- **THE CLEARED IDENTITY.**  Multiplying the finite Lambert sum of a set of
primes by the product of the Mersenne numbers gives an integer. -/
theorem jsp87LamSum_clear {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (lambertDen s : ℝ) * (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹) = (jsp87LamNum s : ℝ) := by
  classical
  have hstep : ∀ p ∈ s, (lambertDen s : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹
      = ((lambertDen s / (2 ^ p - 1) : ℕ) : ℝ) := by
    intro p hp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
      have h1 := two_pow_gt_one (hs p hp).two_le
      linarith
    have hp1 : 1 ≤ p := by have := (hs p hp).two_le; omega
    have hmem := lambertDen_mem_factor (hs p hp) hp
    have hmul : (lambertDen s / (2 ^ p - 1)) * (2 ^ p - 1) = lambertDen s :=
      Nat.div_mul_cancel hmem
    have hcast : ((lambertDen s / (2 ^ p - 1) : ℕ) : ℝ) * ((2 : ℝ) ^ p - 1)
        = (lambertDen s : ℝ) := by
      rw [← cast_pow_sub_one _ hp1, ← Nat.cast_mul, hmul]
    rw [← div_eq_mul_inv, (div_eq_iff (ne_of_gt hpos)).2 hcast.symm]
  calc (lambertDen s : ℝ) * (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹)
      = ∑ p ∈ s, (lambertDen s : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ := by rw [Finset.mul_sum]
  _ = ∑ p ∈ s, ((lambertDen s / (2 ^ p - 1) : ℕ) : ℝ) := Finset.sum_congr rfl hstep
  _ = ∑ p ∈ s, (if p.Prime then ((lambertDen s / (2 ^ p - 1) : ℕ) : ℝ) else 0) :=
    Finset.sum_congr rfl fun p hp => by rw [ite_eq_left (hs p hp)]
  _ = (jsp87LamNum s : ℝ) := by
    unfold jsp87LamNum
    exact_mod_cast Nat.cast_sum s _

/-- **THE CLEARED NUMERATOR IS SMALLER THAN THE SHIFT ITSELF:** `A s ≤ |s| · D s`,
with a strict inequality as soon as `s` is nonempty. -/
theorem jsp87LamNum_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    jsp87LamNum s ≤ s.card * lambertDen s := by
  classical
  have key : ∀ p ∈ s, lambertDen s / (2 ^ p - 1) ≤ lambertDen s := by
    intro p hp
    have hq : 1 ≤ 2 ^ p - 1 := one_le_pow_two_sub_one' (hs p hp).ne_zero
    have hmul : (lambertDen s / (2 ^ p - 1)) * (2 ^ p - 1) = lambertDen s :=
      Nat.div_mul_cancel (lambertDen_mem_factor (hs p hp) hp)
    have hDpos : 0 < lambertDen s / (2 ^ p - 1) := by
      rcases Nat.eq_zero_or_pos (lambertDen s / (2 ^ p - 1)) with hz | hpos
      · have hz1 : lambertDen s = 0 := by rw [← hmul, hz, Nat.zero_mul]
        linarith [lambertDen_pos s]
      · exact hpos
    calc lambertDen s / (2 ^ p - 1) ≤ lambertDen s / (2 ^ p - 1) * (2 ^ p - 1) :=
          Nat.le_mul_of_pos_right _ (by omega : 0 < 2 ^ p - 1)
      _ = lambertDen s := hmul
  have h1 : jsp87LamNum s ≤ ∑ p ∈ s, lambertDen s := by
    unfold jsp87LamNum
    refine Finset.sum_le_sum fun p hp => ?_
    rw [ite_eq_left (hs p hp)]
    exact key p hp
  have h2 : (∑ p ∈ s, lambertDen s : ℕ) = s.card * lambertDen s := by
    rw [Finset.sum_const]
    simp
  omega

/-! ## 2. The finite Lambert sum lives in `[0, 1)` -/

/-- **THE BRIDGE: the prime sum is the prime-restricted full Lambert sum.** -/
theorem jsp87LamSum_eq_primeSum {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹)
      = ∑ p ∈ s, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [ite_eq_left (hs p hp)]

/-- **A finite Lambert sum of primes is at most the full Lambert sum `2 · S`.** -/
theorem jsp87LamSum_le_primeSum {s : Finset ℕ} (_hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ 2 * jsp87Series := by
  have hsum : (∑ p ∈ s, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ ∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) :=
    Summable.sum_le_tsum s (fun p _ => by
      by_cases hpp : p.Prime
      · rw [ite_eq_left hpp]
        exact (inv_pos.mpr (by linarith [two_pow_gt_one hpp.two_le])).le
      · rw [ite_eq_right hpp])
      (summable_lambert_base 2 (by norm_num))
  exact hsum.trans_eq jsp87_lambert_classic

/-- **A finite Lambert sum of primes is at most `2 · S`.** -/
theorem jsp87LamSum_le_two_series {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹) ≤ 2 * jsp87Series :=
  le_trans (le_of_eq (jsp87LamSum_eq_primeSum hs)) (jsp87LamSum_le_primeSum hs)

/-- **THE SHIFT IS SMALL: every finite Lambert sum of primes is `< 1`.** -/
theorem jsp87LamSum_lt_one {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹) < 1 := by
  have h := jsp87LamSum_le_two_series hs
  have h2 := jsp87Series_lt_11_42
  linarith

/-- **A nonempty finite Lambert sum of primes is positive.** -/
theorem jsp87LamSum_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (hne : s ≠ ∅) :
    0 < ∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hne2 : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨p, hp⟩ := hne2
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ p - 1)⁻¹ := by
    apply inv_pos.mpr
    have h1 := two_pow_gt_one (hs p hp).two_le
    linarith
  have hn : 0 ≤ ∑ q ∈ s.erase p, ((2 : ℝ) ^ q - 1)⁻¹ :=
    Finset.sum_nonneg fun q hq' =>
      (inv_pos.mpr (by linarith [two_pow_gt_one (hs q (Finset.mem_of_mem_erase hq')).two_le])).le
  have h1 : (∑ q ∈ s.erase p, ((2 : ℝ) ^ q - 1)⁻¹) + ((2 : ℝ) ^ p - 1)⁻¹
      = ∑ q ∈ s, ((2 : ℝ) ^ q - 1)⁻¹ :=
    Finset.sum_erase_add s (f := fun q : ℕ => ((2 : ℝ) ^ q - 1)⁻¹) hp
  have hkey : (∑ q ∈ s, ((2 : ℝ) ^ q - 1)⁻¹)
      = ((2 : ℝ) ^ p - 1)⁻¹ + ∑ q ∈ s.erase p, ((2 : ℝ) ^ q - 1)⁻¹ := by
    rw [← h1, add_comm]
  rw [hkey]
  linarith

/-- **A finite Lambert sum of primes vanishes exactly at the empty set.** -/
theorem jsp87LamSum_zero_iff {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹) = 0 ↔ s = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact absurd (jsp87LamSum_pos hs hne) (by linarith)
  · intro h
    subst h
    simp

/-! ## 3. The cleared translation, and the transfer of irrationality -/

/-- **THE CLEARED TRANSLATION.**

`F m` multiplied by the product of the Mersenne numbers attached to the prime
support of `m` is the Erdős series multiplied by the same product, plus an
explicit natural number.  So the rational part of round 80's shift is a single
natural number, given by the cleared numerator and denominator of the Lambert
sum. -/
theorem jsp87_multiplier_clear (m : ℕ) (hm : 1 ≤ m) :
    (lambertDen m.primeFactors : ℝ) * jsp87Multiplier m
      = (2 : ℝ) * jsp87Series * (lambertDen m.primeFactors : ℝ)
        + ((omega m * lambertDen m.primeFactors - jsp87LamNum m.primeFactors : ℕ) : ℝ) := by
  have hprim : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hLam : (∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹)
      = ∑ p ∈ m.primeFactors, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) :=
    jsp87LamSum_eq_primeSum hprim
  have hclear := jsp87LamSum_clear hprim
  rw [hLam] at hclear
  have hFlm := jsp87_multiplier_eq m hm
  have hkey : (lambertDen m.primeFactors : ℝ) * jsp87Multiplier m
      = (2 : ℝ) * jsp87Series * (lambertDen m.primeFactors : ℝ)
        + (((omega m : ℕ) : ℝ) * (lambertDen m.primeFactors : ℝ)
            - (jsp87LamNum m.primeFactors : ℝ)) := by
    rw [hFlm, hLam, ← hclear]
    ring
  have hC : jsp87LamNum m.primeFactors ≤ omega m * lambertDen m.primeFactors :=
    jsp87LamNum_le hprim
  calc (lambertDen m.primeFactors : ℝ) * jsp87Multiplier m
      = (2 : ℝ) * jsp87Series * (lambertDen m.primeFactors : ℝ)
        + (((omega m : ℕ) : ℝ) * (lambertDen m.primeFactors : ℝ)
            - (jsp87LamNum m.primeFactors : ℝ)) := hkey
    _ = (2 : ℝ) * jsp87Series * (lambertDen m.primeFactors : ℝ)
        + ((omega m * lambertDen m.primeFactors
              - jsp87LamNum m.primeFactors : ℕ) : ℝ) := by
      rw [Nat.cast_sub hC, Nat.cast_mul]

/-- **THE LAMBERT KEY:** for equal translations the difference of the two prime
counts is the difference of the two finite Lambert sums. -/
theorem jsp87_multiplier_lambert_key {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : jsp87Multiplier m = jsp87Multiplier n) :
    (omega m : ℝ) - omega n
      = (∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹)
        - ∑ p ∈ n.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ := by
  have h1 := jsp87_multiplier_eq m hm
  have h2 := jsp87_multiplier_eq n hn
  rw [h] at h1
  linarith

/-- **TWO TRANSLATIONS THAT COINCIDE HAVE THE SAME NUMBER OF PRIME FACTORS.**
Both Lambert sums lie in `[0, 1)` (`jsp87LamSum_lt_one`), so their difference is
never an integer, while `F m = F n` forces that difference to be
`ω m − ω n`. -/
theorem jsp87_multiplier_eq_imp_card {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : jsp87Multiplier m = jsp87Multiplier n) : omega m = omega n := by
  have hprim : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprimn : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hkey := jsp87_multiplier_lambert_key hm hn h
  have hΘn : 0 ≤ ∑ p ∈ n.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ :=
    Finset.sum_nonneg fun p hp => lamTerm_nonneg (hprimn p hp).two_le
  have hΘm : 0 ≤ ∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ :=
    Finset.sum_nonneg fun p hp => lamTerm_nonneg (hprim p hp).two_le
  have h1 : (omega n : ℝ) < (omega m : ℝ) + 1 := by
    linarith [jsp87LamSum_lt_one hprimn]
  have h2 : (omega m : ℝ) < (omega n : ℝ) + 1 := by
    linarith [jsp87LamSum_lt_one hprim]
  have h1' : (omega n : ℝ) < ((omega m + 1 : ℕ) : ℝ) := by push_cast; exact h1
  have h2' : (omega m : ℝ) < ((omega n + 1 : ℕ) : ℝ) := by push_cast; exact h2
  have h1'' : omega n < omega m + 1 := Nat.cast_lt.mp h1'
  have h2'' : omega m < omega n + 1 := Nat.cast_lt.mp h2'
  have h3 : omega n ≤ omega m := by omega
  have h4 : omega m ≤ omega n := by omega
  omega

/-- **AND THE CONVERSE: equal prime supports give equal translations**
(round 80's `jsp87_multiplier_eq` read as an injectivity statement on the prime
support). -/
theorem jsp87_multiplier_eq_of_card {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : m.primeFactors = n.primeFactors) : jsp87Multiplier m = jsp87Multiplier n := by
  have h1 := jsp87_multiplier_eq m hm
  have h2 := jsp87_multiplier_eq n hn
  rw [h] at h1
  have h3 : omega m = omega n := by
    simp only [omega, h]
  rw [h3] at h1
  exact h1.trans h2.symm

/-- **THE FLAGSHIP: THE IRRATIONALITY TRANSFER.**

The Erdős series is irrational **if and only if** every one of its multiplicative
translations is irrational: rationality of `S` and rationality of `F m` are the
same statement. -/
theorem jsp87_multiplier_irrational_iff (m : ℕ) (hm : 1 ≤ m) :
    Irrational jsp87Series ↔ Irrational (jsp87Multiplier m) := by
  have hDpos : 0 < lambertDen m.primeFactors := lambertDen_pos _
  have hDne : ((lambertDen m.primeFactors : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hDpos)
  have hcastD : (lambertDen m.primeFactors : ℝ)
      = (((lambertDen m.primeFactors : ℕ) : ℚ) : ℝ) := by norm_cast
  have hkey : ((lambertDen m.primeFactors : ℕ) : ℝ) * jsp87Multiplier m
      = ↑((omega m * lambertDen m.primeFactors
          - jsp87LamNum m.primeFactors : ℕ) : ℤ)
        + jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℚ) * (2 : ℝ) := by
    have h := jsp87_multiplier_clear m hm
    rw [hcastD] at h
    have hmul : (2 : ℝ) * jsp87Series * (((lambertDen m.primeFactors : ℕ) : ℚ) : ℝ)
        = jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℚ) * (2 : ℝ) := by
      push_cast
      ring
    rw [← hmul]
    push_cast at h ⊢
    simpa only [add_comm] using h
  constructor
  · intro hS
    have h1 : Irrational (jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℚ)) :=
      hS.mul_ratCast hDne
    have h2 : Irrational (jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℝ)) := by
      simpa only [Rat.cast_natCast] using h1
    have h3 : Irrational (jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℝ) * (2 : ℝ)) := by
      exact (irrational_mul_intCast_iff
        (x := jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℝ)) (m := 2)).mpr
        ⟨by norm_num, h2⟩
    have h4 : Irrational (↑((omega m * lambertDen m.primeFactors
          - jsp87LamNum m.primeFactors : ℕ) : ℤ)
        + jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℚ) * (2 : ℝ)) := by
      have h := h3.intCast_add
        ((omega m * lambertDen m.primeFactors - jsp87LamNum m.primeFactors : ℕ) : ℤ)
      simpa only [Int.cast_ofNat, Rat.cast_natCast] using h
    have h5 : Irrational (jsp87Multiplier m * ((lambertDen m.primeFactors : ℕ) : ℝ)) := by
      rw [← hkey] at h4
      simpa only [mul_comm] using h4
    have h6 : Irrational (jsp87Multiplier m * ((lambertDen m.primeFactors : ℕ) : ℚ)) := by
      simpa only [Rat.cast_natCast] using h5
    exact h6.of_mul_ratCast _
  · intro hF
    have h6 : Irrational (jsp87Multiplier m * ((lambertDen m.primeFactors : ℕ) : ℚ)) :=
      hF.mul_ratCast hDne
    have h5 : Irrational (jsp87Multiplier m * ((lambertDen m.primeFactors : ℕ) : ℝ)) := by
      simpa only [Rat.cast_natCast] using h6
    have h4 : Irrational (↑((omega m * lambertDen m.primeFactors
          - jsp87LamNum m.primeFactors : ℕ) : ℤ)
        + jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℚ) * (2 : ℝ)) := by
      rw [← hkey]
      simpa only [mul_comm] using h5
    have h3 : Irrational (jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℝ) * (2 : ℝ)) := by
      have h := h4.of_intCast_add
        ((omega m * lambertDen m.primeFactors - jsp87LamNum m.primeFactors : ℕ) : ℤ)
      simpa only [Rat.cast_natCast] using h
    have h2 : Irrational (jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℝ)) := by
      have h := (irrational_mul_intCast_iff
        (x := jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℝ)) (m := 2)).mp h3
      simpa only [Int.cast_ofNat] using h.2
    have h1 : Irrational (jsp87Series * ((lambertDen m.primeFactors : ℕ) : ℚ)) := by
      simpa only [Rat.cast_natCast] using h2
    exact h1.of_mul_ratCast _

/-- **One irrational translation suffices.** -/
theorem jsp87Series_irrational_of_multiplier (m : ℕ) (hm : 1 ≤ m)
    (h : Irrational (jsp87Multiplier m)) : Irrational jsp87Series :=
  (jsp87_multiplier_irrational_iff m hm).mpr h

/-- **Every translation inherits irrationality.** -/
theorem jsp87_multiplier_irrational_of_series (m : ℕ) (hm : 1 ≤ m)
    (h : Irrational jsp87Series) : Irrational (jsp87Multiplier m) :=
  (jsp87_multiplier_irrational_iff m hm).mp h

/-- **THE WHOLE FAMILY AT ONCE: the headline is irrational exactly when the
entire countable family is.** -/
theorem jsp87Series_irrational_iff_multiplier_all :
    Irrational jsp87Series ↔ ∀ m : ℕ, 1 ≤ m → Irrational (jsp87Multiplier m) := by
  constructor
  · intro h m hm
    exact jsp87_multiplier_irrational_of_series m hm h
  · intro h
    exact (jsp87_multiplier_irrational_iff 1 (by norm_num)).mpr (h 1 (by norm_num))

/-- **... and exactly when a single member of it is.** -/
theorem jsp87Series_irrational_iff_exists_multiplier :
    Irrational jsp87Series ↔ ∃ m : ℕ, 1 ≤ m ∧ Irrational (jsp87Multiplier m) := by
  constructor
  · intro h
    exact ⟨1, by norm_num, jsp87_multiplier_irrational_of_series 1 (by norm_num) h⟩
  · rintro ⟨m, hm, h⟩
    exact jsp87Series_irrational_of_multiplier m hm h

/-- **The transfer holds along the powers of a multiplier** (round 80's
`F (m^k) = F m` re-read as an irrationality statement). -/
theorem jsp87_multiplier_irrational_iff_pow (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : 1 ≤ k) :
    Irrational (jsp87Multiplier (m ^ k)) ↔ Irrational (jsp87Multiplier m) := by
  rw [jsp87_multiplier_pow m k hm hk]

/-- The rational shift `2 / 3` of round 80, read as a `ℚ`-cast. -/
private theorem cast_rat_two_div_three : (((2 : ℚ) / 3 : ℚ) : ℝ) = (2 : ℝ) / 3 := by
  push_cast
  ring

/-- **In particular at the powers of two**, where round 80 computed the shift
exactly: `F (2^k) = 2 · S + 2/3`. -/
theorem jsp87_multiplier_irrational_two_pow (k : ℕ) (hk : 1 ≤ k) :
    Irrational (jsp87Multiplier (2 ^ k)) ↔ Irrational jsp87Series := by
  rw [jsp87_multiplier_two_pow k hk]
  constructor
  · intro h
    have h' : Irrational (2 * jsp87Series + (((2 : ℚ) / 3 : ℚ) : ℝ)) := by
      rw [cast_rat_two_div_three]
      exact h
    have h2 : Irrational (2 * jsp87Series) := h'.of_add_ratCast ((2 : ℚ) / 3)
    simpa only [Int.cast_ofNat] using h2.of_intCast_mul 2
  · intro h
    have h2 : Irrational (2 * jsp87Series) := by
      have h3 := h.intCast_mul (m := 2) (by norm_num)
      simpa only [Int.cast_ofNat] using h3
    have h3 : Irrational (2 * jsp87Series + (((2 : ℚ) / 3 : ℚ) : ℝ)) :=
      h2.add_ratCast ((2 : ℚ) / 3)
    rw [cast_rat_two_div_three] at h3
    exact h3

/-! ## 4. The Lambert sum determines the clearing denominator -/

/-- **The cleared numerator is the plain sum of the cleared summands.** -/
theorem jsp87LamNum_eq_sum {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    jsp87LamNum s = ∑ p ∈ s, lambertDen s / (2 ^ p - 1) := by
  unfold jsp87LamNum
  exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_left (hs p hp)]

/-- **THE ERASE FORM OF THE CLEARED NUMERATOR:**
`jsp87LamNum s = ∑_{p ∈ s.erase q} (D s / (2 ^ p - 1)) + D s / (2 ^ q - 1)`. -/
theorem jsp87LamNum_erase {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {q : ℕ} (hq : q ∈ s) :
    (∑ p ∈ s.erase q, lambertDen s / (2 ^ p - 1)) + lambertDen s / (2 ^ q - 1)
      = jsp87LamNum s := by
  rw [jsp87LamNum_eq_sum hs]
  exact Finset.sum_erase_add s (f := fun p => lambertDen s / (2 ^ p - 1)) hq

/-- **A cleared summand is divisible by every other Mersenne number.** -/
theorem dvd_lamTerm_of_mem_erase {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {q p : ℕ}
    (hq : q ∈ s) (hp : p ∈ s.erase q) : (2 ^ q - 1) ∣ lambertDen s / (2 ^ p - 1) := by
  rw [jsp87LamTerm_eq_erase hs (Finset.mem_of_mem_erase hp)]
  refine lambertDen_mem_factor (hs q hq) (Finset.mem_erase.mpr ⟨?_, hq⟩)
  rintro h
  exact absurd h.symm ((Finset.mem_erase.mp hp).1)

/-- **The rest of the cleared numerator is divisible by `2 ^ q - 1`.** -/
theorem dvd_lamNum_erase {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {q : ℕ} (hq : q ∈ s) :
    (2 ^ q - 1) ∣ ∑ p ∈ s.erase q, lambertDen s / (2 ^ p - 1) :=
  dvd_sum_of_div' (2 ^ q - 1) (s.erase q) (f := fun _ => lambertDen s / (2 ^ _ - 1))
    (fun _ hp => dvd_lamTerm_of_mem_erase hs hq hp)

/-- **The cleared numerator, minus the `q`-th cleared summand, is divisible by
`2 ^ q - 1`.** -/
theorem dvd_sub_lamNum_term {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {q : ℕ} (hq : q ∈ s) :
    (2 ^ q - 1) ∣ jsp87LamNum s - lambertDen s / (2 ^ q - 1) := by
  have hA := jsp87LamNum_erase hs hq
  have hnonneg : 0 ≤ lambertDen s / (2 ^ q - 1) := Nat.zero_le _
  have heq : jsp87LamNum s - lambertDen s / (2 ^ q - 1)
      = ∑ p ∈ s.erase q, lambertDen s / (2 ^ p - 1) := by
    rw [← hA]
    omega
  rw [heq]
  exact dvd_lamNum_erase hs hq

/-- **THE REDUCED DENOMINATOR: `lambertDen s` is the reduced denominator of the
finite Lambert sum of a set of primes.**

This is where the pairwise coprimality of the Mersenne numbers of *distinct*
primes (round 39) enters: the `q`-th cleared summand `lambertDen (s.erase q)` is
coprime to `2 ^ q - 1`, and the *rest* of the cleared numerator is a multiple of
`2 ^ q - 1`; so nothing cancels in `jsp87LamNum s / lambertDen s`. -/
theorem jsp87LamNum_coprime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Nat.Coprime (jsp87LamNum s) (lambertDen s) := by
  have key : ∀ q ∈ s, Nat.Coprime ((2 ^ q - 1 : ℕ)) (jsp87LamNum s) := by
    intro q hq
    refine (Nat.coprime_iff_gcd_eq_one).2 ?_
    rw [Nat.gcd_eq_one_iff]
    intro d hd1 hd2
    have hA := jsp87LamNum_erase hs hq
    have hdA : d ∣ ∑ p ∈ s.erase q, lambertDen s / (2 ^ p - 1) :=
      hd1.trans (dvd_lamNum_erase hs hq)
    have hd5 : d ∣ lambertDen s / (2 ^ q - 1)
        + ∑ p ∈ s.erase q, lambertDen s / (2 ^ p - 1) := by
      rw [← hA] at hd2
      simpa only [Nat.add_comm] using hd2
    have hd3 : d ∣ lambertDen (s.erase q) := by
      rw [← jsp87LamTerm_eq_erase hs hq]
      exact (Nat.dvd_add_iff_left (k := d) (m := lambertDen s / (2 ^ q - 1))
        (n := ∑ p ∈ s.erase q, lambertDen s / (2 ^ p - 1)) hdA).mpr hd5
    exact Nat.gcd_eq_one_iff.mp (lambert_den_coprime_finset s hs q hq).gcd_eq_one d hd1 hd3
  refine Nat.Coprime.prod_right ?_
  intro i hi
  by_cases h : i.Prime
  · rw [ite_eq_left h]
    exact (key i hi).symm
  · rw [ite_eq_right h]
    exact Nat.coprime_one_right _

/-! ## 5. Equal translations, equal denominators -/

/-- **THE DENOMINATOR IS DETERMINED BY THE LAMBERT SUM: equal finite Lambert sums
of primes have equal clearing denominators.**  This is the arithmetic content of
`jsp87LamNum_coprime` (the reduced-denominator theorem): the reduced denominator
of `A s / D s` is `D s`, so the value determines the denominator. -/
theorem jsp87LamSum_eq_imp_den_eq {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (ht : ∀ p ∈ t, p.Prime)
    (h : (∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹) = ∑ p ∈ t, ((2 : ℝ) ^ p - 1)⁻¹) :
    lambertDen s = lambertDen t := by
  have h1 := jsp87LamSum_clear hs
  have h2 := jsp87LamSum_clear ht
  have hx : (jsp87LamNum s : ℝ) = (lambertDen s : ℝ) * ∑ p ∈ s, ((2 : ℝ) ^ p - 1)⁻¹ := h1.symm
  have hy : (jsp87LamNum t : ℝ) = (lambertDen t : ℝ) * ∑ p ∈ t, ((2 : ℝ) ^ p - 1)⁻¹ := h2.symm
  rw [h] at hx
  have key : (jsp87LamNum s : ℝ) * (lambertDen t : ℝ)
      = (jsp87LamNum t : ℝ) * (lambertDen s : ℝ) := by
    rw [hx, hy]
    ring
  have key' : jsp87LamNum s * lambertDen t = jsp87LamNum t * lambertDen s := by
    exact_mod_cast key
  have hDs : lambertDen s ∣ lambertDen t := by
    refine Nat.Coprime.dvd_of_dvd_mul_left (jsp87LamNum_coprime hs).symm ?_
    rw [key']
    exact ⟨jsp87LamNum t, Nat.mul_comm _ _⟩
  have hDt : lambertDen t ∣ lambertDen s := by
    refine Nat.Coprime.dvd_of_dvd_mul_left (jsp87LamNum_coprime ht).symm ?_
    rw [← key']
    exact ⟨jsp87LamNum s, Nat.mul_comm _ _⟩
  exact Nat.le_antisymm (Nat.le_of_dvd (lambertDen_pos t) hDs)
    (Nat.le_of_dvd (lambertDen_pos s) hDt)

/-- **Equal translations have equal clearing denominators.** -/
theorem jsp87_multiplier_eq_imp_den {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : jsp87Multiplier m = jsp87Multiplier n) :
    lambertDen m.primeFactors = lambertDen n.primeFactors := by
  have hprim : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprimn : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hcard := jsp87_multiplier_eq_imp_card hm hn h
  have hkey : (∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹)
      = ∑ p ∈ n.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ := by
    have h3 := jsp87_multiplier_lambert_key hm hn h
    rw [hcard] at h3
    linarith
  exact jsp87LamSum_eq_imp_den_eq hprim hprimn hkey

/-- **THE FULL RIGIDITY OF THE TRANSLATIONS:** two multiplier series coincide only
if the integer parts and the Mersenne products agree. -/
theorem jsp87_multiplier_eq_imp {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : jsp87Multiplier m = jsp87Multiplier n) :
    omega m = omega n ∧ lambertDen m.primeFactors = lambertDen n.primeFactors :=
  ⟨jsp87_multiplier_eq_imp_card hm hn h, jsp87_multiplier_eq_imp_den hm hn h⟩

/-- **TWO TRANSLATIONS ARE DISTINCT WHENEVER THEIR MERSENNE PRODUCTS ARE.** -/
theorem jsp87_multiplier_imp_ne_den {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : lambertDen m.primeFactors ≠ lambertDen n.primeFactors) :
    jsp87Multiplier m ≠ jsp87Multiplier n := by
  intro h1
  exact h (jsp87_multiplier_eq_imp_den hm hn h1)

/-- **THE TRANSLATION FAMILY IS AS BIG AS ITS PRIME SUPPORTS.**

The equivalence holds as soon as `lambertDen` is injective on sets of primes —
a Zsigmondy-type statement, *not* known and *not* claimed here: it is an
explicit hypothesis of the theorem, so the theorem itself is proved with no
gap.  The *unconditional* half is `jsp87_multiplier_imp_ne_den`. -/
theorem jsp87_multiplier_ne_iff_pf_ne {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hinj : ∀ s t : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ t, p.Prime) →
      lambertDen s = lambertDen t → s = t) :
    jsp87Multiplier m ≠ jsp87Multiplier n ↔ m.primeFactors ≠ n.primeFactors := by
  have hprim : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprimn : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  constructor
  · intro h1 h2
    exact h1 (jsp87_multiplier_eq_of_card hm hn h2)
  · intro h1 h2
    exact h1 (hinj m.primeFactors n.primeFactors hprim hprimn
      (jsp87_multiplier_eq_imp_den hm hn h2))

/-- **... and hence the two readings of the family coincide.** -/
theorem jsp87_multiplier_ne_iff_den_ne {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hinj : ∀ s t : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ t, p.Prime) →
      lambertDen s = lambertDen t → s = t) :
    jsp87Multiplier m ≠ jsp87Multiplier n
      ↔ lambertDen m.primeFactors ≠ lambertDen n.primeFactors := by
  have hprim : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprimn : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  constructor
  · intro h1 h2
    exact h1 (jsp87_multiplier_eq_of_card hm hn
      (hinj m.primeFactors n.primeFactors hprim hprimn h2))
  · intro h1 h2
    exact h1 (jsp87_multiplier_eq_imp_den hm hn h2)

end JSP87
