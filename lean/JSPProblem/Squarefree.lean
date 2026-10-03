/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Basic
import JSPProblem.Primary
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# JSP-000087 : squarefree numbers, the power-set divisor identity, and a new
# irrationality theorem

## Why this file exists

Every module of the tree so far (60+ files, ~1860 proved declarations) works with
`ω` through its *counting* form (`omega n = (n.primeFactors).card`) or through
the prime-restricted Lambert series of rounds 37/39/40.  **No module ever
touched the power-set geometry of `ω`**, i.e. the identity

> the squarefree divisors of `n` are in bijection with the subsets of the
> distinct prime factors of `n`, so their number is exactly `2 ^ ω n`,

which is the multiplicative (as opposed to additive) content of `ω`.  That
identity has two immediate consequences, both proved here:

* `2 ^ ω n` is the *divisor-sum transform* of the squarefree indicator, hence the
  **exponential moment** `∑' n, 2 ^ ω n 2 ^ -(n+1)` is a Lambert series indexed
  by the squarefree numbers — the exact analogue, for the power-set moment, of
  round 37's `jsp87_lambert` (which did the same for the first moment);
* the squarefree indicator is `{0,1}`-valued and **aperiodic**, so round 47's
  Erdős criterion (`jsp87Binary_irrational_iff`, proved from scratch) applies to
  it verbatim and yields a **complete, unconditional irrationality theorem**:

  > `jsp87SqfreeSeries_irrational` : the binary series of the squarefree
  > indicator, `∑' n, [n squarefree] 2 ^ -(n+1)`, is irrational.

## The aperiodicity argument (the new content)

`jsp87_sqf_not_eventuallyPeriodic` is elementary and has a two-line proof.  An
eventual period `t` would propagate squarefreeness along the progression `p, p + t,
p + 2 t, …` from any prime `p` past the threshold; at index `k = p · j` this says
`Squarefree (p (1 + j t))`, hence `Squarefree (1 + j t)` for every `j ≥ 0`
(a divisor of a squarefree number is squarefree).  Taking `j = t + 2` gives
`1 + (t + 2) t = (t + 1) ^ 2`, a perfect square — contradiction.  No prime `k`-tuples
hypothesis, no correlation estimate, nothing beyond Euclid.

## What it does *not* give

The Erdős series itself still carries (round 47: `jsp87_digit_one`), so its binary
digits are not the `ω`-digits; this file therefore does not close
`jsp_000087_main`.  What it does is add the **power-set rung** of the Lambert
ladder of rounds 37/107/108 (`1`, `ω`, `ω^2`, … → now `2 ^ ω`) and a second
complete instance of the aperiodicity criterion.
-/

namespace JSP87

open Finset

/-! ## 0. Elementary squarefree facts -/

/-- `1` is squarefree. -/
theorem jsp87_sqf_one : Squarefree 1 := by native_decide

/-- `0` is not squarefree: every prime square divides `0`. -/
theorem jsp87_not_sqf_zero : ¬ Squarefree 0 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨2, by norm_num, by norm_num⟩

/-- Every prime is squarefree. -/
theorem jsp87_sqf_of_prime {p : ℕ} (hp : p.Prime) : Squarefree p := hp.squarefree

/-- **A divisor of a squarefree number is squarefree.** -/
theorem jsp87_sqf_of_dvd {n d : ℕ} (hn : Squarefree n) (hd : d ∣ n) : Squarefree d := by
  rw [Nat.squarefree_iff_prime_squarefree] at hn ⊢
  exact fun x hx hxd => hn x hx (hxd.trans hd)

/-- **Squarefreeness is inherited by every divisor**, in the `≤` form. -/
theorem jsp87_sqf_iff_of_dvd {n : ℕ} :
    Squarefree n ↔ ∀ d : ℕ, d ∣ n → Squarefree d := by
  constructor
  · exact fun h d hd => jsp87_sqf_of_dvd h hd
  · intro h
    exact h n ⟨1, by omega⟩

/-- **A prime square dividing `n` destroys squarefreeness.** -/
theorem jsp87_not_sqf_of_sq_dvd {n x : ℕ} (hx : x.Prime) (h : x * x ∣ n) : ¬ Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨x, hx, h⟩

/-- No perfect square `m ^ 2` with `m ≥ 2` is squarefree. -/
theorem jsp87_not_sqf_sq {m : ℕ} (hm : 2 ≤ m) : ¬ Squarefree (m ^ 2) := by
  obtain ⟨x, hxm, hxd⟩ := (Nat.ne_one_iff_exists_prime_dvd).mp (by omega : m ≠ 1)
  rw [Nat.pow_two]
  exact jsp87_not_sqf_of_sq_dvd hxm (Nat.mul_dvd_mul hxd hxd)

/-- A multiple of `4` is never squarefree. -/
theorem jsp87_not_sqf_of_four_dvd {n : ℕ} (h : 4 ∣ n) : ¬ Squarefree n := by
  have h4 : (2 : ℕ) * 2 ∣ n := by simpa using h
  exact jsp87_not_sqf_of_sq_dvd (by decide) h4

/-! ## 1. THE SQUAREFREE INDICATOR IS APERIODIC -/

/-- **THE SQUAREFREE INDICATOR IS APERIODIC.**  An eventual period `t > 0` would
propagate squarefreeness along `p + k t` from any prime `p` past the threshold;
at `k = p · j` this makes `1 + j t` squarefree for every `j ≥ 0`, and
`j = t + 2` makes it the square `(t + 1) ^ 2`. -/
theorem jsp87_sqf_not_eventuallyPeriodic :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → (Squarefree (n + t) ↔ Squarefree n) := by
  rintro ⟨t, N, ht, hper⟩
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  have hkey : ∀ k : ℕ, Squarefree (p + k * t) := by
    intro k
    induction k with
    | zero => simpa using jsp87_sqf_of_prime hp
    | succ k ih =>
        have h1 := hper (p + k * t) (by omega)
        have hstep : p + (k + 1) * t = (p + k * t) + t := by ring
        rw [hstep]
        exact h1.mpr ih
  have hgen : ∀ j : ℕ, Squarefree (1 + j * t) := by
    intro j
    have hpj : Squarefree (p + p * j * t) := hkey (p * j)
    have heq : p + p * j * t = p * (1 + j * t) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    rw [heq] at hpj
    exact jsp87_sqf_of_dvd hpj ⟨p, by ring⟩
  have hcontra : ¬ Squarefree (1 + (t + 2) * t) := by
    have h1 : 1 + (t + 2) * t = (t + 1) ^ 2 := by ring
    rw [h1]
    exact jsp87_not_sqf_sq (by omega)
  exact hcontra (hgen (t + 2))

/-! ## 2. A COMPLETE IRRATIONALITY THEOREM: THE SQUAREFREE BINARY SERIES -/

/-- The squarefree indicator, as a `{0,1}`-valued sequence. -/
def jsp87SqfreeBit (n : ℕ) : ℕ := if Squarefree n then 1 else 0

theorem jsp87SqfreeBit_le (n : ℕ) : jsp87SqfreeBit n ≤ 1 := by
  by_cases h : Squarefree n <;> simp [jsp87SqfreeBit, h]

theorem jsp87SqfreeBit_eq_one_iff (n : ℕ) : jsp87SqfreeBit n = 1 ↔ Squarefree n := by
  by_cases h : Squarefree n <;> simp [jsp87SqfreeBit, h]

theorem jsp87SqfreeBit_eq_zero_iff (n : ℕ) : jsp87SqfreeBit n = 0 ↔ ¬ Squarefree n := by
  by_cases h : Squarefree n <;> simp [jsp87SqfreeBit, h]

/-- Two squarefree indicators agree exactly when squarefreeness agrees. -/
theorem jsp87SqfreeBit_eq_iff {n m : ℕ} :
    jsp87SqfreeBit n = jsp87SqfreeBit m ↔ (Squarefree n ↔ Squarefree m) := by
  by_cases hn : Squarefree n <;> by_cases hm : Squarefree m <;> simp [jsp87SqfreeBit, hn, hm]

/-- **THE SQUAREFREE BINARY SERIES** `∑' n, [n squarefree] 2 ^ -(n+1)`. -/
noncomputable def jsp87SqfreeSeries : ℝ := jsp87BinarySeries jsp87SqfreeBit

/-- **THE SQUAREFREE BINARY SERIES IS IRRATIONAL.**  Its digits are the
squarefree indicator, which is aperiodic (`jsp87_sqf_not_eventuallyPeriodic`),
and round 47's criterion turns aperiodicity into irrationality.  A second
complete instance of `jsp87Binary_irrational_iff`, and the first one whose
digits are the *divisor geometry* of `ω` rather than `ω` itself. -/
theorem jsp87SqfreeSeries_irrational : Irrational jsp87SqfreeSeries := by
  unfold jsp87SqfreeSeries
  refine jsp87Binary_irrational_of_notPeriodic jsp87SqfreeBit jsp87SqfreeBit_le ?_ ?_
  · intro N
    have hle : N ≤ 4 * (N + 2) := by
      have h1 : N + 2 ≤ 4 * (N + 2) := Nat.le_mul_of_pos_left (N + 2) (by omega)
      omega
    have hzero : jsp87SqfreeBit (4 * (N + 2)) = 0 := by
      rw [jsp87SqfreeBit_eq_zero_iff]
      exact jsp87_not_sqf_of_four_dvd (Nat.dvd_mul_right 4 _)
    exact jsp87BinaryTail_lt_one jsp87SqfreeBit jsp87SqfreeBit_le N ⟨4 * (N + 2) - N, by
      rw [Nat.add_sub_of_le hle]
      exact hzero⟩
  · rintro ⟨t, N, ht, hN, hper⟩
    refine jsp87_sqf_not_eventuallyPeriodic ⟨t, N, ht, fun n hn => ?_⟩
    exact jsp87SqfreeBit_eq_iff.mp (hper n hn)

/-! ## 3. THE POWER-SET IDENTITY: the squarefree divisors of `n` number `2 ^ ω n` -/

/-- **A product of distinct primes is squarefree.** -/
theorem jsp87_prod_prime_sqf {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ x ∈ s, x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hsqf_a : Squarefree a := jsp87_sqf_of_prime (hs a (Finset.mem_insert_self a s))
      have hcop : Nat.Coprime a (∏ x ∈ s, x) :=
        Nat.Coprime.prod_right fun x hx =>
          (Nat.coprime_primes (hs a (Finset.mem_insert_self a s))
            (hs x (Finset.mem_insert_of_mem hx))).2 (by
              intro hcon
              subst hcon
              exact ha hx)
      rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
      exact ⟨hcop, hsqf_a, ih hs'⟩

/-- **Membership criterion for a prime in a product of distinct primes.** -/
theorem jsp87_mem_prod_prime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {x : ℕ} (hx : Nat.Prime x) :
    (x ∣ ∏ p ∈ s, p) ↔ x ∈ s := by
  constructor
  · intro h
    have hiff := hx.prime.dvd_finsetProd_iff (S := s) (g := fun y => y)
    obtain ⟨a, ha, hxa⟩ := hiff.mp h
    have hax : x = a := by
      rcases (Nat.dvd_prime (hs a ha)).mp hxa with h | h
      · exact absurd h hx.ne_one
      · omega
    simpa [hax] using ha
  · intro h
    exact Finset.dvd_prod_of_mem (fun y => y) h

/-- **A product of a subset of the prime factors divides `n`.** -/
theorem jsp87_prod_primeFactors_sub_dvd {n : ℕ} {s : Finset ℕ}
    (hs : s ⊆ n.primeFactors) : (∏ x ∈ s, x) ∣ n := by
  refine (Finset.prod_dvd_prod_of_subset s n.primeFactors id hs).trans ?_
  simpa using Nat.prod_primeFactors_dvd n

/-- Every prime divisor of `n` is at most `n`. -/
theorem jsp87_le_of_mem_primeFactors {n p : ℕ} (hn : 0 < n) (hp : p ∈ n.primeFactors) : p ≤ n :=
  Nat.le_of_dvd hn (Nat.mem_primeFactors.mp hp).2.1

/-- Every element of `n.primeFactors` is at least `2`. -/
theorem jsp87_primeFactors_ge_two {n p : ℕ} (hp : p ∈ n.primeFactors) : 2 ≤ p := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have h0 : ¬ p = 0 := hp'.ne_zero
  have h1 : ¬ p = 1 := hp'.ne_one
  omega

/-- The squarefree divisors of `n`, as a finset. -/
def jsp87SqfDivs (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun d => Squarefree d ∧ d ∣ n)

/-- **Every squarefree divisor of `n` is the product of a subset of the distinct
prime factors of `n`.** -/
theorem jsp87_sqfDiv_eq_prod {n d : ℕ} (hn : 1 ≤ n) (hsqf : Squarefree d) (hdvd : d ∣ n) :
    ∃ s ⊆ n.primeFactors, (∏ x ∈ s, x : ℕ) = d := by
  refine ⟨d.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsqf⟩
  intro p hp
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    (Nat.mem_primeFactors.mp hp).2.1.trans hdvd, by omega⟩

/-- **A product of a subset of the distinct prime factors of `n` is a squarefree
divisor of `n`.** -/
theorem jsp87_prod_sqfDiv {n : ℕ} {s : Finset ℕ} (hss : s ⊆ n.primeFactors) :
    Squarefree (∏ x ∈ s, x) ∧ (∏ x ∈ s, x) ∣ n :=
  ⟨jsp87_prod_prime_sqf (fun _p hp => (Nat.mem_primeFactors.mp (hss hp)).1),
    jsp87_prod_primeFactors_sub_dvd hss⟩

/-- **The squarefree divisors of `n` are exactly the products of subsets of
`n.primeFactors`.**  This is the power-set description of `ω`. -/
theorem jsp87SqfDivs_eq_powerset_prod (n : ℕ) (hn : 1 ≤ n) :
    jsp87SqfDivs n = (n.primeFactors.powerset.image fun s : Finset ℕ => (∏ x ∈ s, x : ℕ)) := by
  classical
  ext d
  constructor
  · intro hd
    have hd' : d < n + 1 ∧ Squarefree d ∧ d ∣ n := by
      simpa only [jsp87SqfDivs, Finset.mem_filter, Finset.mem_range] using hd
    obtain ⟨_hlt, hsqf, hdvd⟩ := hd'
    obtain ⟨s, hss, heq⟩ := jsp87_sqfDiv_eq_prod hn hsqf hdvd
    exact Finset.mem_image.mpr ⟨s, Finset.mem_powerset.mpr hss, heq⟩
  · intro hd
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hd
    have hss : s ⊆ n.primeFactors := Finset.mem_powerset.mp hs
    have hkey : Squarefree (∏ x ∈ s, x) ∧ (∏ x ∈ s, x : ℕ) ∣ n := jsp87_prod_sqfDiv hss
    have hle : (∏ x ∈ s, x) ≤ n := Nat.le_of_dvd hn hkey.2
    have hlt : d < n + 1 := by
      have hlt' : (∏ x ∈ s, x : ℕ) < n + 1 := Nat.lt_succ_of_le hle
      omega
    simp only [jsp87SqfDivs, Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, congrArg (fun x : ℕ => Squarefree x) heq ▸ hkey.1,
      congrArg (fun x : ℕ => x ∣ n) heq ▸ hkey.2⟩

/-- **THE POWER-SET IDENTITY: `n` has exactly `2 ^ ω n` squarefree divisors.**

This is the multiplicative content of `ω`: the distinct prime factors of `n`
index a power set, and the squarefree divisors of `n` are exactly its elements. -/
theorem jsp87SqfDivs_card (n : ℕ) (hn : 1 ≤ n) : (jsp87SqfDivs n).card = 2 ^ omega n := by
  have hcard : (jsp87SqfDivs n).card = (n.primeFactors.powerset).card := by
    refine (Finset.card_bij (s := (n.primeFactors.powerset : Finset (Finset ℕ)))
      (t := jsp87SqfDivs n) (i := fun s _ => (∏ x ∈ s, x : ℕ)) ?_ ?_ ?_).symm
    · intro s hs
      have hss : s ⊆ n.primeFactors := Finset.mem_powerset.mp hs
      have hkey := jsp87_prod_sqfDiv hss
      have hle : (∏ x ∈ s, x) ≤ n := Nat.le_of_dvd hn hkey.2
      simp only [jsp87SqfDivs, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hle, hkey.1, hkey.2⟩
    · intro s₁ hs₁ s₂ hs₂ heq
      have hsp₁ : ∀ p ∈ s₁, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_powerset.mp hs₁ hp)).1
      have hsp₂ : ∀ p ∈ s₂, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_powerset.mp hs₂ hp)).1
      calc s₁ = (∏ x ∈ s₁, x : ℕ).primeFactors := (Nat.primeFactors_prod hsp₁).symm
        _ = (∏ x ∈ s₂, x : ℕ).primeFactors := by rw [heq]
        _ = s₂ := Nat.primeFactors_prod hsp₂
    · intro b hb
      simp only [jsp87SqfDivs, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hlt, hsqf, hdvd⟩ := hb
      obtain ⟨s, hss, heq⟩ := jsp87_sqfDiv_eq_prod hn hsqf hdvd
      exact ⟨s, Finset.mem_powerset.mpr hss, heq⟩
  rw [hcard, Finset.card_powerset]
  rfl

/-! ## 4. THE EXPONENTIAL (POWER-SET) MOMENT OF `ω`, and its bracket -/

/-- **`2 ^ -(n+1) = 2⁻¹ · (2⁻¹) ^ n`** — the shift used to evaluate the binary
geometric series. -/
theorem jsp87_two_pow_neg_succ_eq (n : ℕ) :
    ((2 : ℝ) ^ (n + 1))⁻¹ = (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ : ℝ) ^ n := by
  calc ((2 : ℝ) ^ (n + 1))⁻¹ = (2 * 2 ^ n)⁻¹ := by rw [mul_comm, ← pow_succ]
    _ = (2 : ℝ)⁻¹ * (2 ^ n)⁻¹ := mul_inv (2 : ℝ) (2 ^ n)
    _ = (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ : ℝ) ^ n := by rw [inv_pow]

/-- The shifted binary geometric series is `Summable`. -/
theorem summable_jsp87_two_pow_neg_succ :
    Summable (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) :=
  (summable_inv_two_pow.mul_left ((2 : ℝ)⁻¹)).congr (fun n => (jsp87_two_pow_neg_succ_eq n).symm)

/-- `∑' n, 2 ^ -(n+1) = 1` — the closed form of the all-ones binary string. -/
theorem jsp87_tsum_two_pow_neg_succ : (∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  have hg : (∑' n : ℕ, ((2 : ℝ)⁻¹ : ℝ) ^ n) = (1 - (2 : ℝ)⁻¹)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one (ξ := ((2 : ℝ)⁻¹ : ℝ))
      (by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; norm_num)).tsum_eq
  calc (∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑' n : ℕ, (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ : ℝ) ^ n := tsum_congr (fun n => jsp87_two_pow_neg_succ_eq n)
    _ = (2 : ℝ)⁻¹ * ∑' n : ℕ, ((2 : ℝ)⁻¹ : ℝ) ^ n := Summable.tsum_mul_left ((2 : ℝ)⁻¹) summable_inv_two_pow
    _ = (2 : ℝ)⁻¹ * (1 - (2 : ℝ)⁻¹)⁻¹ := by rw [hg]
    _ = 1 := by norm_num

/-- **THE EXPONENTIAL (POWER-SET) MOMENT OF `ω`**: `P = ∑' n, 2 ^ ω n 2 ^ -(n+1)`.

`2 ^ ω n` is the number of squarefree divisors of `n` (§3), so `P` is the
*divisor-sum transform* of the squarefree indicator evaluated at base `2` — the
power-set rung of the Lambert ladder of rounds 37/107/108, which treated the
first, second and cubic moments of `ω`. -/
noncomputable def jsp87PowOmegaSeries : ℝ :=
  ∑' n : ℕ, ((2 : ℝ) ^ omega n) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- The majorant `∑' n, (n + 1) 2 ^ -(n+1)` is `Summable`. -/
theorem summable_jsp87_powOmega_majorant :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
  (summable_nat_mul_two_pow_neg.add summable_jsp87_two_pow_neg_succ).congr (fun n => by
    push_cast
    ring)

/-- **THE MAJORANT'S VALUE IS `2`**: `∑' n, (n + 1) 2 ^ -(n+1) = 1 + 1`. -/
theorem jsp87_tsum_powOmega_majorant :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 2 := by
  calc (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑' n : ℕ, (((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ + ((2 : ℝ) ^ (n + 1))⁻¹) := by
        refine tsum_congr (fun n => ?_)
        push_cast
        ring
    _ = (∑' n : ℕ, ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
        + ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ :=
          Summable.tsum_add summable_nat_mul_two_pow_neg summable_jsp87_two_pow_neg_succ
    _ = 1 + 1 := by rw [tsum_nat_mul_two_pow_neg, jsp87_tsum_two_pow_neg_succ]
    _ = 2 := by norm_num

/-- **`2 ^ ω n ≤ n + 1` for every `n`** (at `n = 0` the left side is `1`). -/
theorem jsp87_two_pow_omega_le_add_one (n : ℕ) : 2 ^ omega n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h, omega_zero]
  · have h1 := two_pow_omega_le h
    omega

theorem summable_jsp87PowOmegaTerm :
    Summable (fun n : ℕ => ((2 : ℝ) ^ omega n) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    summable_jsp87_powOmega_majorant
  have hle : (2 : ℝ) ^ omega n ≤ (n + 1 : ℕ) := by
    exact_mod_cast jsp87_two_pow_omega_le_add_one n
  exact mul_le_mul_of_nonneg_right hle (by positivity)

theorem jsp87PowOmegaSeries_nonneg : 0 ≤ jsp87PowOmegaSeries := by
  unfold jsp87PowOmegaSeries
  exact tsum_nonneg fun n => by positivity

/-- **THE UPPER BRACKET: `P ≤ 2`**, because `2 ^ ω n ≤ n + 1` and
`∑' n, (n + 1) 2 ^ -(n+1) = 2`. -/
theorem jsp87_powOmegaSeries_le_two : jsp87PowOmegaSeries ≤ 2 := by
  have hle : ∀ n : ℕ, ((2 : ℝ) ^ omega n) * ((2 : ℝ) ^ (n + 1))⁻¹
      ≤ ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    have h1 : (2 : ℝ) ^ omega n ≤ (n + 1 : ℕ) := by
      exact_mod_cast jsp87_two_pow_omega_le_add_one n
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc jsp87PowOmegaSeries = ∑' n : ℕ, ((2 : ℝ) ^ omega n) * ((2 : ℝ) ^ (n + 1))⁻¹ := rfl
    _ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
      Summable.tsum_le_tsum hle summable_jsp87PowOmegaTerm summable_jsp87_powOmega_majorant
    _ = 2 := jsp87_tsum_powOmega_majorant

/-- **THE LOWER BRACKET: `1 + S ≤ P`**, because `2 ^ ω n ≥ ω n + 1`
(round 37's `succ_le_two_pow`) and `∑' n, 2 ^ -(n+1) = 1`.

So the power-set moment *dominates the Erdős series by at least `1`*: counting
squarefree divisors is a strictly finer observable of `ω` than `ω` itself. -/
theorem jsp87_powOmegaSeries_ge_series_add_one : 1 + jsp87Series ≤ jsp87PowOmegaSeries := by
  have hle : ∀ n : ℕ, (1 + (omega n : ℕ)) * ((2 : ℝ) ^ (n + 1))⁻¹
      ≤ ((2 : ℝ) ^ omega n) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    have h2 : (1 + (omega n : ℕ) : ℕ) ≤ 2 ^ omega n := by
      simpa [add_comm] using succ_le_two_pow (omega n)
    have h2' : 1 + (omega n : ℕ) ≤ (2 : ℝ) ^ omega n := by exact_mod_cast h2
    exact mul_le_mul_of_nonneg_right h2' (by positivity)
  have hsumA : Summable (fun n : ℕ => (1 + (omega n : ℕ)) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle summable_jsp87PowOmegaTerm
  have hA : (∑' n : ℕ, (1 + (omega n : ℕ)) * ((2 : ℝ) ^ (n + 1))⁻¹) = 1 + jsp87Series := by
    calc (∑' n : ℕ, (1 + (omega n : ℕ)) * ((2 : ℝ) ^ (n + 1))⁻¹)
        = ∑' n : ℕ, ((1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
            + ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
          refine tsum_congr (fun n => ?_)
          ring
      _ = (∑' n : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
          + ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
        refine Summable.tsum_add ?_ summable_omega_mul_inv_two_pow
        exact summable_jsp87_two_pow_neg_succ.congr (fun n => by rw [one_mul])
      _ = 1 + jsp87Series := by
        rw [show (∑' n : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
            = ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ from tsum_congr (fun n => by rw [one_mul]),
          jsp87_tsum_two_pow_neg_succ,
          show (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = jsp87Series from rfl]
  calc 1 + jsp87Series = ∑' n : ℕ, (1 + (omega n : ℕ)) * ((2 : ℝ) ^ (n + 1))⁻¹ := hA.symm
    _ ≤ ∑' n : ℕ, ((2 : ℝ) ^ omega n) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
      Summable.tsum_le_tsum hle hsumA summable_jsp87PowOmegaTerm
    _ = jsp87PowOmegaSeries := rfl

/-! ## 5. Instances, and negative knowledge about the squarefree Lambert side -/

/-- The power-set identity at `n = 12 = 2^2 · 3`: `ω 12 = 2`, so `4` squarefree divisors. -/
theorem jsp87SqfDivs_12 : (jsp87SqfDivs 12).card = 4 := by native_decide

/-- At `n = 30 = 2 · 3 · 5`: `ω 30 = 3`, so `8`. -/
theorem jsp87SqfDivs_30 : (jsp87SqfDivs 30).card = 8 := by native_decide

/-- At `n = 210 = 2 · 3 · 5 · 7`: `ω 210 = 4`, so `16`. -/
theorem jsp87SqfDivs_210 : (jsp87SqfDivs 210).card = 16 := by native_decide

/-- At `n = 1`: the only squarefree divisor is `1`, matching `2 ^ 0 = 1`. -/
theorem jsp87SqfDivs_1 : (jsp87SqfDivs 1).card = 1 := by native_decide

/-- **NEGATIVE KNOWLEDGE: the squarefree-indexed Lambert denominators are NOT
pairwise coprime.**  Round 39 proved that the denominators `2 ^ p - 1` attached
to *distinct primes* are pairwise coprime, and round 40 built the whole
`D_N` clearing denominator on that.  The power-set ladder cannot reuse that:
`3` divides both `2 ^ 2 - 1` and `2 ^ 6 - 1`, and both `2` and `6` are
squarefree.  So the exponential moment does *not* come with an exact clearing
denominator, and the round-40 machinery does not transfer to it. -/
theorem jsp87_sqf_mer_not_coprime : ¬ Nat.Coprime (2 ^ 2 - 1) (2 ^ 6 - 1) := by
  decide

/-- The positive companion: `2 ^ 2 - 1` is coprime to `2 ^ 3 - 1` (coprime exponents,
round 39's `coprime_lambert_den_of_coprime`), even though `2` and `3` are both
squarefree. -/
theorem jsp87_sqf_mer_coprime_two_three : Nat.Coprime (2 ^ 2 - 1) (2 ^ 3 - 1) := by
  native_decide

end JSP87
