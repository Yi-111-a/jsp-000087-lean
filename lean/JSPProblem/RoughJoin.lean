/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.SieveModel
import JSPProblem.LambertTrunc
import JSPProblem.LambertTail
import JSPProblem.LambertIdentity
import JSPProblem.ProgressionOmega
import Mathlib.Tactic

/-!
# JSP-000087 : the rough part of the Erdős series, and the Mersenne roughness at `2p`

## Why this file exists

`JSPProblem/SieveModel.lean` (round 55) split `ω` into its two sieve halves,

`ω m = jsp87SieveCard m k + jsp87UnsievedCard m k`,

the *sieve content* (the prime divisors `≤ k`, which round 55 proved to be exactly
periodic modulo `k#`) and the *rough content* (the prime divisors `> k`, which
it proved to be logarithmically bounded).  `JSPProblem/LambertTrunc.lean` and
`JSPProblem/CutPeriod.lean` built the Lambert side: the prime-restricted
Lambert series `∑ p prime, 1 / (2^p - 1) = 2 · S`, its truncations, its
clearing denominators `lambertDen (range N)` and its tails.  **Nothing in the
tree ever related the two halves** (`rg jsp87UnsievedCard` finds only
`SieveModel.lean`).

This file supplies the join, and the join isolates the open part of the problem:

* `jsp87_two_mul_series_eq_add_sieve_rough` — the Erdős series splits at every
  sieve level `k` into a *sieve half* and a *rough half*;
* `jsp87SieveSeries_eq_lambertTrunc` — **the sieve half IS the truncated prime
  Lambert sum**, hence an explicit rational;
* `jsp87Series_irrational_iff_rough_irrational` — **THE FLAGSHIP**: the Erdős
  series is irrational **if and only if** the rough half is, for *every* sieve
  level `k`.  However the level is chosen, the primes below it cannot
  contribute any irrationality: it all sits in the primes exceeding `k`, and the
  rough half shrinks to `0` as `k → ∞` while keeping the status of `S`.

That is exactly the shape of the Erdős–Pratt argument: Pratt's hypothesis is a
correlation statement about the primes *above* a bound.

## The asymmetry

The two halves are not of the same nature, and the difference is machine
checked here:

* `jsp87_sieveCard_periodic` — the sieve coefficient is periodic with period
  `k#` (round 55's local model), so the sieve series is a rational;
* `jsp87UnsievedCard_unbounded`, `jsp87UnsievedCard_not_eventuallyPeriodic`,
  `jsp87UnsievedCard_not_eventually_bounded` — the rough coefficient is
  unbounded at every level (hence not eventually periodic, and not even
  eventually bounded), because `ω` is unbounded in every arithmetic progression
  (round 101) and the sieve half removes only a bounded number of primes.

## Mersenne roughness at `2p`

`JSPProblem/Diophantine.lean` (round 39) proved `dvd_sub_one_prime_gt`: every
prime `ℓ` dividing `2^p - 1` with `p` prime satisfies `p ∣ ℓ - 1`, hence
`ℓ > p`.  This file sharpens the threshold from `p` to `2p`
(`jsp87_dvd_sub_one_prime_ge`, `jsp87_coprime_two_pow_sub_one_of_le`): for an
odd prime `p`, `2^p - 1` is coprime to **every** integer `≤ 2p`, so its least
prime divisor is at least `2p + 1` and every divisor is either `1` or `≥ 2p+1`
(`jsp87_dvd_two_pow_sub_one_one_or_ge`).

Mathlib has nothing of this shape here (`Nat.pow_sub_one_gcd_pow_sub_one` is
about the `gcd` of two Mersenne numbers, not about the size of the prime
divisors of one), and no `Nat.Prime.not_coprime_iff_dvd` argument appears
anywhere in the tree.
-/

namespace JSP87

open Filter
open Topology

set_option maxHeartbeats 1000000

/-! ## 0. Basic real-valued helpers -/

/-- `2 · 2^-(n+1) = 2^-n`: the un-normalised weight used by the Lambert
reduction `jsp87_lambert_reduction`. -/
private theorem two_mul_inv_two_pow_succ (n : ℕ) :
    (2 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
  have hne : (2 : ℝ) * (2 : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
  calc (2 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      = (2 : ℝ) * (((2 : ℝ) ^ n)⁻¹ * (2 : ℝ)⁻¹) := by rw [pow_succ, mul_inv]
    _ = ((2 : ℝ) * (2 : ℝ)⁻¹) * ((2 : ℝ) ^ n)⁻¹ := by ring
    _ = ((2 : ℝ) ^ n)⁻¹ := by rw [hne, one_mul]

/-- The un-normalised Erdős summands `ω n · 2^-n` are summable. -/
theorem summable_omega_mul_two_pow_neg :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) :=
  (summable_omega_mul_inv_two_pow.mul_left 2).congr fun n => by
    calc (2 : ℝ) * (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
        = ((omega n : ℕ) : ℝ) * (2 * ((2 : ℝ) ^ (n + 1))⁻¹) := by ring
      _ = ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rw [two_mul_inv_two_pow_succ n]

/-- Summability of a weighted integer-valued sequence dominated by `ω`. -/
private theorem summable_cast_mul_two_pow_neg {f : ℕ → ℕ} (hf : ∀ n, f n ≤ omega n) :
    Summable (fun n : ℕ => ((f n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_omega_mul_two_pow_neg
  · exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hf n) (by positivity)

/-! ## 1. The two halves of the Erdős series as series -/

/-- The `m`-th term of the **sieve half** at level `k`: the number of prime
divisors of `m` that are `≤ k`, weighted by `2^-m`. -/
noncomputable def jsp87SieveTerm (m k : ℕ) : ℝ :=
  ((jsp87SieveCard m k : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹

/-- The `m`-th term of the **rough half** at level `k`: the number of prime
divisors of `m` that exceed `k`, weighted by `2^-m`. -/
noncomputable def jsp87RoughTerm (m k : ℕ) : ℝ :=
  ((jsp87UnsievedCard m k : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹

/-- **The sieve half of the Erdős series at level `k`. -/
noncomputable def jsp87SieveSeries (k : ℕ) : ℝ := ∑' m : ℕ, jsp87SieveTerm m k

/-- **The rough half of the Erdős series at level `k`. -/
noncomputable def jsp87RoughSeries (k : ℕ) : ℝ := ∑' m : ℕ, jsp87RoughTerm m k

theorem jsp87SieveTerm_zero (k : ℕ) : jsp87SieveTerm 0 k = 0 := by
  simp [jsp87SieveTerm, jsp87SieveCard, Nat.primeFactors_zero]

theorem jsp87RoughTerm_zero (k : ℕ) : jsp87RoughTerm 0 k = 0 := by
  simp [jsp87RoughTerm, jsp87UnsievedCard, Nat.primeFactors_zero]

theorem jsp87SieveTerm_nonneg (m k : ℕ) : 0 ≤ jsp87SieveTerm m k :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

theorem jsp87RoughTerm_nonneg (m k : ℕ) : 0 ≤ jsp87RoughTerm m k :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

theorem summable_jsp87SieveTerm (k : ℕ) : Summable (fun m => jsp87SieveTerm m k) := by
  simpa only [jsp87SieveTerm] using
    (summable_cast_mul_two_pow_neg (f := fun n => jsp87SieveCard n k)
      (fun n => sieveCard_le_omega n k))

theorem summable_jsp87RoughTerm (k : ℕ) : Summable (fun m => jsp87RoughTerm m k) := by
  simpa only [jsp87RoughTerm] using
    (summable_cast_mul_two_pow_neg (f := fun n => jsp87UnsievedCard n k)
      (fun n => unsievedCard_le_omega n k))

/-- **The two halves add up to the Erdős summand.** -/
theorem jsp87Term_add (m k : ℕ) :
    jsp87SieveTerm m k + jsp87RoughTerm m k = ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
  rw [jsp87SieveTerm, jsp87RoughTerm, omega_eq_sieve_add_unsieved m k, Nat.cast_add]
  ring

/-! ## 2. THE JOIN: the Erdős series splits into a sieve half and a rough half -/

/-- **THE SPLITTING OF THE ERDŐS SERIES AT A SIEVE LEVEL.**
`2 · S = sieve half + rough half`, for every `k`. -/
theorem jsp87_two_mul_series_eq_add_sieve_rough (k : ℕ) :
    2 * jsp87Series = jsp87SieveSeries k + jsp87RoughSeries k := by
  calc 2 * jsp87Series
      = ∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := jsp87_lambert_classic.symm
    _ = ∑' m : ℕ, ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ := jsp87_lambert_reduction.symm
    _ = ∑' m : ℕ, (jsp87SieveTerm m k + jsp87RoughTerm m k) :=
        tsum_congr fun m => (jsp87Term_add m k).symm
    _ = (∑' m : ℕ, jsp87SieveTerm m k) + ∑' m : ℕ, jsp87RoughTerm m k :=
        Summable.tsum_add (summable_jsp87SieveTerm k) (summable_jsp87RoughTerm k)
    _ = jsp87SieveSeries k + jsp87RoughSeries k := rfl

/-- The same splitting, solved for the rough half. -/
theorem jsp87_roughSeries_eq (k : ℕ) :
    jsp87RoughSeries k = 2 * jsp87Series - jsp87SieveSeries k := by
  linarith [jsp87_two_mul_series_eq_add_sieve_rough k]

/-- The rough half is at most the Erdős series. -/
theorem jsp87_sieveSeries_le (k : ℕ) : jsp87SieveSeries k ≤ 2 * jsp87Series := by
  have h1 : 0 ≤ jsp87RoughSeries k :=
    tsum_nonneg fun m => jsp87RoughTerm_nonneg m k
  linarith [jsp87_two_mul_series_eq_add_sieve_rough k]

/-! ## 3. THE SIEVE HALF IS THE TRUNCATED PRIME LAMBERT SUM -/

/-- **The sieve coefficient is a sum of indicators over the primes `≤ k`.**
`jsp87SieveCard m k = ∑ p ≤ k prime, [p ∣ m ∧ 1 ≤ m]`; the `1 ≤ m` is needed
because every prime divides `0` while `0` has no prime factors. -/
theorem jsp87_sieveCard_eq_sum (m k : ℕ) :
    jsp87SieveCard m k
      = ∑ p ∈ jsp87Primes k, (if p ∣ m ∧ 1 ≤ m then 1 else 0) := by
  rcases m with _ | m
  · simp [jsp87SieveCard, Nat.primeFactors_zero]
  · have hzero : ¬ (m + 1 = 0) := by omega
    have h2 : (m + 1).primeFactors.filter (fun p => p ≤ k ∧ p ∣ m + 1 ∧ 1 ≤ m + 1)
        = (jsp87Primes k).filter (fun p => p ∣ m + 1 ∧ 1 ≤ m + 1) := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp', hpk, hpd, hpos⟩ := Finset.mem_filter.mp hp
        obtain ⟨hprime, hpd', hne⟩ := Nat.mem_primeFactors.mp hp'
        exact Finset.mem_filter.mpr
          ⟨mem_jsp87Primes.mpr ⟨hprime.two_le, hpk, hprime⟩, hpd, hpos⟩
      · intro hp
        obtain ⟨hp', hpd, hpos⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hpk, hprime⟩ := mem_jsp87Primes.mp hp'
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hprime, hpd, hzero⟩, hpk, hpd, hpos⟩
    rw [jsp87SieveCard, Finset.card_eq_sum_ones]
    calc (∑ p ∈ (m + 1).primeFactors.filter (fun p => p ≤ k), (1 : ℕ))
        = ∑ p ∈ (m + 1).primeFactors, (if p ≤ k ∧ p ∣ m + 1 ∧ 1 ≤ m + 1 then 1 else 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨-, hpd, -⟩ := Nat.mem_primeFactors.mp hp
          by_cases h : p ≤ k
          · rw [if_pos h, if_pos ⟨h, hpd, by omega⟩]
          · rw [if_neg h, if_neg (by simp [h])]
      _ = ∑ p ∈ (m + 1).primeFactors.filter (fun p => p ≤ k ∧ p ∣ m + 1 ∧ 1 ≤ m + 1),
            (1 : ℕ) :=
          (Finset.sum_filter (fun p => p ≤ k ∧ p ∣ m + 1 ∧ 1 ≤ m + 1) (fun _ => (1 : ℕ))).symm
      _ = ∑ p ∈ (jsp87Primes k).filter (fun p => p ∣ m + 1 ∧ 1 ≤ m + 1), (1 : ℕ) := by
        rw [h2]
      _ = ∑ p ∈ jsp87Primes k, (if p ∣ m + 1 ∧ 1 ≤ m + 1 then 1 else 0) := by
        rw [Finset.sum_filter]

/-- The `m`-th sieve term, with the primes `≤ k` summed out. -/
theorem jsp87_sieveTerm_eq_sum (m k : ℕ) :
    jsp87SieveTerm m k
      = ∑ p ∈ jsp87Primes k,
          ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
  rw [jsp87SieveTerm, jsp87_sieveCard_eq_sum, Nat.cast_sum]
  exact Finset.sum_mul (s := jsp87Primes k)
    (fun p => ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ)) ((2 : ℝ) ^ m)⁻¹

private theorem summable_ind_two_pow_neg (p : ℕ) :
    Summable
      (fun m : ℕ => (((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹)) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) jsp87_summable_two_pow_neg
  · exact mul_nonneg (by split_ifs <;> norm_num)
      (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) m)).le
  · have h1 : ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ :=
      (inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) m)).le
    simpa using mul_le_mul_of_nonneg_right h1 h2

private theorem tsum_ind_two_pow_neg (p : ℕ) (hp : p.Prime) :
    (∑' m : ℕ, (((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹))
      = ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hs : Summable
      (fun m : ℕ => (((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹)) :=
    summable_ind_two_pow_neg p
  have h0 : (((if p ∣ 0 ∧ 1 ≤ 0 then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ 0)⁻¹) = 0 := by
    have hnd : ¬ (1 ≤ (0 : ℕ)) := by simp
    simp [hnd]
  have hid : ∀ m : ℕ, (1 : ℕ) ≤ m →
      (((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹)
        = jsp87Ind p m * ((2 : ℝ) ^ m)⁻¹ := by
    intro m hm
    have h1 : (((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ)) = jsp87Ind p m := by
      unfold jsp87Ind
      push_cast
      by_cases h : p ∣ m
      · rw [if_pos ⟨h, hm⟩, if_pos h]
      · rw [if_neg (by simp [h]), if_neg h]
    rw [h1]
  calc (∑' m : ℕ, (((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹))
      = 0 + ∑' n : ℕ, jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
        rw [hs.tsum_eq_zero_add, h0,
          tsum_congr fun n => hid (n + 1) (by omega)]
    _ = ((2 : ℝ) ^ p - 1)⁻¹ := by simpa using sum_indicator_shift_prime p hp

/-- `(range (k+1)).filter Nat.Prime = jsp87Primes k`: the primes at most `k`. -/
theorem jsp87_primes_range_eq (k : ℕ) :
    (Finset.range (k + 1)).filter Nat.Prime = jsp87Primes k := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp', hprime⟩ := Finset.mem_filter.mp hp
    have hpk : p ≤ k := by have := Finset.mem_range.mp hp'; omega
    exact mem_jsp87Primes.mpr ⟨hprime.two_le, hpk, hprime⟩
  · intro hp
    obtain ⟨hle, hpk, hprime⟩ := mem_jsp87Primes.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime⟩

/-- **THE SIEVE HALF, PRIME BY PRIME.**  The weighted count of the prime
divisors `≤ k` of the integers, read as a series, is
`∑ p ≤ k prime, 1 / (2^p - 1)`. -/
theorem jsp87SieveSeries_eq_sum_lambertTerms (k : ℕ) :
    jsp87SieveSeries k = ∑ p ∈ jsp87Primes k, ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hswap : (∑' m : ℕ, jsp87SieveTerm m k)
      = ∑ p ∈ jsp87Primes k, ∑' m : ℕ,
          ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
    calc (∑' m : ℕ, jsp87SieveTerm m k)
        = ∑' m : ℕ, ∑ p ∈ jsp87Primes k,
            ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ :=
          tsum_congr fun m => jsp87_sieveTerm_eq_sum m k
      _ = ∑ p ∈ jsp87Primes k, ∑' m : ℕ,
            ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ :=
          Summable.tsum_finsetSum (s := jsp87Primes k) (fun p _ => summable_ind_two_pow_neg p)
  calc jsp87SieveSeries k = ∑' m : ℕ, jsp87SieveTerm m k := rfl
    _ = ∑ p ∈ jsp87Primes k, ∑' m : ℕ,
          ((if p ∣ m ∧ 1 ≤ m then 1 else 0 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ := hswap
    _ = ∑ p ∈ jsp87Primes k, ((2 : ℝ) ^ p - 1)⁻¹ :=
      Finset.sum_congr rfl fun p hp => tsum_ind_two_pow_neg p (mem_jsp87Primes.mp hp).2.2

/-- **THE SIEVE HALF IS THE TRUNCATED PRIME LAMBERT SUM.** -/
theorem jsp87SieveSeries_eq_lambertTrunc (k : ℕ) :
    jsp87SieveSeries k = jsp87_lambertTrunc (k + 1) := by
  have hfin : (∑ p ∈ jsp87Primes k, ((2 : ℝ) ^ p - 1)⁻¹)
      = ∑ p ∈ Finset.range (k + 1), jsp87_lambertTerm p := by
    have h2 : (∑ p ∈ jsp87Primes k, ((2 : ℝ) ^ p - 1)⁻¹)
        = ∑ p ∈ (Finset.range (k + 1)).filter (fun p => p.Prime),
            ((2 : ℝ) ^ p - 1)⁻¹ := by
      rw [jsp87_primes_range_eq k]
    have h3 : (∑ p ∈ (Finset.range (k + 1)).filter (fun p => p.Prime),
            ((2 : ℝ) ^ p - 1)⁻¹)
        = ∑ p ∈ Finset.range (k + 1),
            (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
      rw [Finset.sum_filter]
    have h4 : (∑ p ∈ Finset.range (k + 1),
            (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0))
        = ∑ p ∈ Finset.range (k + 1), jsp87_lambertTerm p :=
      Finset.sum_congr rfl fun p _ => by simp [jsp87_lambertTerm]
    exact h2.trans (h3.trans h4)
  calc jsp87SieveSeries k = ∑ p ∈ jsp87Primes k, ((2 : ℝ) ^ p - 1)⁻¹ :=
        jsp87SieveSeries_eq_sum_lambertTerms k
    _ = ∑ p ∈ Finset.range (k + 1), jsp87_lambertTerm p := hfin
    _ = jsp87_lambertTrunc (k + 1) := rfl

/-- **The rough half is the Lambert tail beyond `k`.**  The whole open part of
the problem sits in `∑ p > k prime, 1 / (2^p - 1)`. -/
theorem jsp87RoughSeries_eq_lambertTail (k : ℕ) :
    jsp87RoughSeries k = jsp87_lambertTail (k + 1) := by
  have h1 := jsp87_two_mul_series_eq_add_sieve_rough k
  have h2 := jsp87SieveSeries_eq_lambertTrunc k
  have h3 := jsp87_lambert_decomp (k + 1)
  have h4 := jsp87_lambertAll_eq
  rw [h2] at h1
  linarith

/-! ## 4. THE SIEVE HALF IS A RATIONAL; THE ROUGH HALF IS WHERE `S` LIVES -/

/-- **The sieve half is an explicit rational**, with the clearing denominator
`lambertDen (range (k+1))` of round 66. -/
theorem jsp87_sieveSeries_rational (k : ℕ) :
    ∃ a : ℕ, ∃ b : ℕ, 0 < b ∧ jsp87SieveSeries k = (a : ℝ) / (b : ℝ) := by
  refine ⟨jsp87_lambertNumer (k + 1), lambertDen (Finset.range (k + 1)), ?_, ?_⟩
  · exact lambertDen_pos _
  · rw [jsp87SieveSeries_eq_lambertTrunc]
    exact jsp87_lambertTrunc_eq_div (k + 1)

/-- **THE FLAGSHIP: the Erdős series is irrational iff its rough half is, at
every sieve level.**  However the level is chosen, the primes below it cannot
contribute any irrationality: the sieve half is the rational
`∑ p ≤ k, 1/(2^p-1)`.  This is the shape of the Erdős–Pratt argument, whose
hypothesis is a correlation statement about the primes *above* a bound. -/
theorem jsp87Series_irrational_iff_rough_irrational (k : ℕ) :
    Irrational jsp87Series ↔ Irrational (jsp87RoughSeries k) := by
  obtain ⟨a, b, hb, hsb⟩ := jsp87_sieveSeries_rational k
  have hq : jsp87SieveSeries k = ((a : ℚ) / (b : ℚ) : ℚ) := by
    rw [hsb]
    push_cast
    ring
  have hdecomp := jsp87_two_mul_series_eq_add_sieve_rough k
  constructor
  · intro h
    have h2 : Irrational (2 * jsp87Series) := by
      have hx := h.ratCast_mul (q := (2 : ℚ)) (by norm_num : ((2 : ℚ)) ≠ 0)
      simpa using hx
    have h3 : Irrational (((a : ℚ) / (b : ℚ) : ℚ) + jsp87RoughSeries k) := by
      rw [← hq, ← hdecomp]
      exact h2
    exact Irrational.of_ratCast_add (q := (a : ℚ) / (b : ℚ)) (x := jsp87RoughSeries k) h3
  · intro h
    have h3 : Irrational (((a : ℚ) / (b : ℚ) : ℚ) + jsp87RoughSeries k) :=
      h.ratCast_add ((a : ℚ) / (b : ℚ))
    have h2 : Irrational (2 * jsp87Series) := by
      rw [hdecomp, hq]
      exact h3
    exact Irrational.of_intCast_mul (m := 2) h2

/-- **The rational form of the same statement.**  For every sieve level `k`,
the Erdős series is a rational number iff its rough half is. -/
theorem jsp87_rational_iff_rough_rational (k : ℕ) :
    (∃ q : ℚ, (q : ℝ) = jsp87Series) ↔ (∃ q : ℚ, (q : ℝ) = jsp87RoughSeries k) := by
  constructor
  · rintro ⟨q, hq⟩
    have hn : ¬ Irrational jsp87Series := by
      intro hirr
      exact absurd hq (fun h => hirr ⟨q, h⟩)
    have hn' : ¬ Irrational (jsp87RoughSeries k) :=
      (jsp87Series_irrational_iff_rough_irrational k).not.mp hn
    obtain ⟨q', hq'⟩ := exists_rat_of_not_irrational hn'
    exact ⟨q', hq'.symm⟩
  · rintro ⟨q, hq⟩
    have hn : ¬ Irrational (jsp87RoughSeries k) := by
      intro hirr
      exact absurd hq (fun h => hirr ⟨q, h⟩)
    have hn' : ¬ Irrational jsp87Series :=
      (jsp87Series_irrational_iff_rough_irrational k).not.mpr hn
    obtain ⟨q', hq'⟩ := exists_rat_of_not_irrational hn'
    exact ⟨q', hq'.symm⟩

/-- The `Irrational`-negated form, for symmetry with the level-series criteria
of rounds 83/107. -/
theorem jsp87_roughSeries_not_irrational_iff (k : ℕ) :
    (¬ Irrational (jsp87RoughSeries k)) ↔ ¬ Irrational jsp87Series := by
  constructor
  · intro h hs
    exact h ((jsp87Series_irrational_iff_rough_irrational k).mp hs)
  · intro h hr
    exact h ((jsp87Series_irrational_iff_rough_irrational k).mpr hr)

/-! ## 5. Quantitative facts about the two halves -/

theorem jsp87RoughSeries_nonneg (k : ℕ) : 0 ≤ jsp87RoughSeries k :=
  tsum_nonneg fun m => jsp87RoughTerm_nonneg m k

theorem jsp87SieveSeries_nonneg (k : ℕ) : 0 ≤ jsp87SieveSeries k :=
  tsum_nonneg fun m => jsp87SieveTerm_nonneg m k

theorem jsp87RoughSeries_pos (k : ℕ) : 0 < jsp87RoughSeries k := by
  rw [jsp87RoughSeries_eq_lambertTail]
  exact jsp87_lambertTail_pos (k + 1)

/-- **The rough half is exponentially small.** -/
theorem jsp87RoughSeries_le (k : ℕ) :
    jsp87RoughSeries k ≤ 4 * ((2 : ℝ) ^ (k + 1))⁻¹ := by
  rw [jsp87RoughSeries_eq_lambertTail]
  exact jsp87_lambertTail_le (k + 1)

/-- `k + 1 ≤ 2^(k+1)`. -/
private theorem two_pow_succ_ge (k : ℕ) : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => show (1 : ℕ) ≤ 2; exact one_le_two_pow 1
  | succ k ih =>
      rw [pow_succ]
      have := ih
      omega

/-- **A polynomial bound on the same error term:** the rough half decays at
least as fast as `4/(k+1)`, since `2^(k+1) ≥ k+1`. -/
theorem jsp87RoughSeries_le'' (k : ℕ) : jsp87RoughSeries k ≤ 4 * ((k : ℝ) + 1)⁻¹ := by
  have h2 : (k : ℝ) + 1 ≤ (2 : ℝ) ^ (k + 1) := by
    have hk := two_pow_succ_ge k
    exact_mod_cast hk
  have h3 : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ ((k : ℝ) + 1)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 h2
  exact le_trans (jsp87RoughSeries_le k) (mul_le_mul_of_nonneg_left h3 (by norm_num))

/-- `4/(k+1) → 0`, proved directly from `Metric.tendsto_atTop`. -/
theorem tendsto_four_over_nat_add_one :
    Tendsto (fun k : ℕ => 4 * ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / ε)
  refine ⟨K, ?_⟩
  intro k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * ((k : ℝ) + 1)⁻¹)]
  have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (k : ℝ) > 4 / ε := by linarith
  have h3 : (4 : ℝ) < ε * ((k : ℝ) + 1) := by
    have he : ε * (4 / ε : ℝ) = 4 := by field_simp
    have h4 := mul_lt_mul_of_pos_left h1 hε
    linarith [he]
  refine (div_lt_iff₀ (by positivity)).2 ?_
  nlinarith [h3]

/-- **THE ROUGH HALF IS THE APPROXIMATION ERROR OF THE TRUNCATED LAMBERT SUMS,
AND IT GOES TO ZERO.**  `2 · S` is the limit of the explicit rationals
`∑ p ≤ k prime, 1/(2^p-1)`, and the error is the rough half. -/
theorem tendsto_jsp87RoughSeries_zero : Tendsto jsp87RoughSeries atTop (𝓝 0) :=
  squeeze_zero' (Filter.Eventually.of_forall fun k => jsp87RoughSeries_nonneg k)
    (Filter.Eventually.of_forall fun k => jsp87RoughSeries_le'' k) (by
      exact tendsto_four_over_nat_add_one)

/-- The same statement for the sieve half. -/
theorem tendsto_jsp87SieveSeries :
    Tendsto jsp87SieveSeries atTop (𝓝 (2 * jsp87Series)) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => 2 * jsp87Series) atTop (𝓝 (2 * jsp87Series))).sub
    tendsto_jsp87RoughSeries_zero
  simpa [jsp87_roughSeries_eq] using h

/-- The sieve half is positive as soon as the level reaches the prime `2`. -/
theorem jsp87SieveSeries_pos_of_two_le (k : ℕ) (hk : 2 ≤ k) : 0 < jsp87SieveSeries k := by
  have hmem : (2 : ℕ) ∈ jsp87Primes k := mem_jsp87Primes.mpr ⟨by omega, hk, by norm_num⟩
  have hnonneg : ∀ p ∈ jsp87Primes k, (0 : ℝ) ≤ ((2 : ℝ) ^ p - 1)⁻¹ := by
    intro p hp
    have hp2 : 1 ≤ p := by have := (mem_jsp87Primes.mp hp).1; omega
    exact (inv_pos.mpr (two_pow_sub_one_pos hp2)).le
  have hle : ((2 : ℝ) ^ 2 - 1)⁻¹ ≤ jsp87SieveSeries k := by
    rw [jsp87SieveSeries_eq_sum_lambertTerms]
    exact Finset.single_le_sum hnonneg hmem
  have hval : ((2 : ℝ) ^ 2 - 1)⁻¹ = (1 / 3 : ℝ) := by norm_num
  rw [hval] at hle
  linarith

/-! ## 6. THE ASYMMETRY: periodic sieve coefficient, unbounded rough coefficient -/

theorem jsp87_primorial_pos (k : ℕ) : 0 < jsp87Primorial k := by
  have h1 : (1 : ℕ) ≤ jsp87Primorial k := one_le_primorial k
  have h2 : (0 : ℕ) < 1 := by omega
  omega

/-- **THE LOCAL MODEL AS A PERIOD:** the sieve coefficient of `m + k#` equals
that of `m`. -/
theorem jsp87_sieveCard_periodic {m k : ℕ} (hm : 1 ≤ m) :
    jsp87SieveCard (m + jsp87Primorial k) k = jsp87SieveCard m k := by
  refine sieveCard_congr (by omega) hm ?_
  refine Nat.ModEq.symm ?_
  refine (Nat.modEq_iff_dvd' (a := m) (b := m + jsp87Primorial k) (by omega)).mpr ?_
  have hsub : m + jsp87Primorial k - m = jsp87Primorial k := by omega
  rw [hsub]

/-- **The sieve coefficient is eventually periodic** — in fact periodic from
`1`, with period `k#`.  This is why the sieve half of the Erdős series has a
rigid digit string and is rational. -/
theorem jsp87_sieveCard_eventuallyPeriodic (k : ℕ) :
    ∃ N t : ℕ, 0 < t ∧ ∀ n, N ≤ n → jsp87SieveCard (n + t) k = jsp87SieveCard n k :=
  ⟨1, jsp87Primorial k, jsp87_primorial_pos k, fun _ hn => jsp87_sieveCard_periodic hn⟩

/-- **The sieve half removes only finitely many primes.** -/
theorem jsp87_sieveCard_le_card (m k : ℕ) :
    jsp87SieveCard m k ≤ (jsp87Primes k).card := by
  refine Finset.card_le_card_of_injOn (fun p => p) ?_ (fun _ _ _ _ h => h)
  intro p hp
  obtain ⟨hp', hpk⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprime, _, _⟩ := Nat.mem_primeFactors.mp hp'
  exact mem_jsp87Primes.mpr ⟨hprime.two_le, hpk, hprime⟩

/-- **THE ROUGH COEFFICIENT IS UNBOUNDED IN EVERY ARITHMETIC PROGRESSION.**
`ω` is unbounded in every progression (round 101) and the sieve half removes at
most `|{primes ≤ k}|` primes, so the rough content is unbounded too. -/
theorem jsp87UnsievedCard_unbounded_progression (k m a C N : ℕ) (hm : 0 < m) :
    ∃ n : ℕ, max a N ≤ n ∧ n % m = a % m ∧ C < jsp87UnsievedCard n k := by
  obtain ⟨n, h1, h2, h3⟩ :=
    omega_arith_unbounded (m := m) (a := a) (C := C + (jsp87Primes k).card) (N := max a N) hm
  refine ⟨n, le_trans (le_max_right _ _) h1, h2, ?_⟩
  have h4 := omega_eq_sieve_add_unsieved n k
  have h5 := jsp87_sieveCard_le_card n k
  omega

/-- Freezing a periodic coefficient along one arithmetic progression. -/
private theorem rough_frozen {k t N : ℕ} (hper : ∀ n, N ≤ n →
    jsp87UnsievedCard (n + t) k = jsp87UnsievedCard n k) {n : ℕ} (hn : N ≤ n) :
    ∀ q : ℕ, jsp87UnsievedCard (n + t * q) k = jsp87UnsievedCard n k := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      have hid : n + t * (q + 1) = n + t * q + t := by rw [Nat.mul_succ]; omega
      calc jsp87UnsievedCard (n + t * (q + 1)) k = jsp87UnsievedCard (n + t * q + t) k := by
            rw [hid]
        _ = jsp87UnsievedCard (n + t * q) k := hper _ (by omega)
        _ = jsp87UnsievedCard n k := ih

/-- **THE ROUGH COEFFICIENT IS NOT EVENTUALLY PERIODIC**, at any sieve level.
The proof is round 101's: eventual periodicity freezes the coefficient along one
residue class, while the rough content is unbounded in every residue class. -/
theorem jsp87UnsievedCard_not_eventuallyPeriodic (k : ℕ) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n →
      jsp87UnsievedCard (n + t) k = jsp87UnsievedCard n k := by
  rintro ⟨t, N, ht, hper⟩
  obtain ⟨n₀, hn₀, hmod, hu⟩ :=
    jsp87UnsievedCard_unbounded_progression (k := k) (m := t) (a := N)
      (C := jsp87UnsievedCard N k) (N := N) ht
  have hge : N ≤ n₀ := by omega
  have hmodEq : Nat.ModEq t N n₀ := by
    rw [Nat.ModEq]
    exact hmod.symm
  have hdvd : t ∣ n₀ - N :=
    (Nat.modEq_iff_dvd' (n := t) (a := N) (b := n₀) (by omega)).mp hmodEq
  obtain ⟨u, hu'⟩ := hdvd
  have hN0 : N ≤ N + t * u := by omega
  have heq : n₀ = N + t * u := by omega
  have hstep : jsp87UnsievedCard (N + t * u) k = jsp87UnsievedCard N k :=
    rough_frozen hper (n := N) (by omega) u
  rw [heq, hstep] at hu
  omega

/-- **THE ROUGH COEFFICIENT IS NOT EVENTUALLY BOUNDED**, at any sieve level. -/
theorem jsp87UnsievedCard_not_eventually_bounded (k : ℕ) :
    ¬ ∃ C N : ℕ, ∀ n, N ≤ n → jsp87UnsievedCard n k ≤ C := by
  rintro ⟨C, N, hC⟩
  obtain ⟨n, hn, hu⟩ :=
    jsp87UnsievedCard_unbounded_progression (k := k) (m := 1) (a := 0) (C := C)
      (N := N) (by omega)
  have hN : N ≤ n := by omega
  have hle := hC n hN
  omega

/-- **The rough content of `ω` is unbounded** at every sieve level. -/
theorem jsp87UnsievedCard_unbounded (k : ℕ) (C : ℕ) :
    ∃ n : ℕ, C ≤ jsp87UnsievedCard n k := by
  obtain ⟨n, -, -, hu⟩ :=
    jsp87UnsievedCard_unbounded_progression (k := k) (m := 1) (a := 0) (C := C)
      (N := 0) (by omega)
  exact ⟨n, le_of_lt hu⟩

/-! ## 7. MERSENNE ROUGHNESS AT `2p` -/

/-- **THE ORDER OF 2 AT A PRIME DIVISOR OF `2^p - 1`, SHARPENED.**
Round 39 proved `p ∣ ℓ - 1` (`dvd_sub_one_prime_gt`).  For an *odd* prime `p`
the divisor `ℓ` is odd as well, so `2 ∣ ℓ - 1` too, and Euclid gives `2p ∣ ℓ - 1`. -/
theorem jsp87_dvd_sub_one_prime_two_mul {p ℓ : ℕ} (hp : p.Prime) (hodd : ¬ p = 2)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hd : ℓ ∣ 2 ^ p - 1) : 2 * p ∣ ℓ - 1 := by
  have hd1 : p ∣ ℓ - 1 := dvd_sub_one_prime_gt hℓ hp hℓ2 hd
  have hpodd : Odd p := hp.odd_of_ne_two hodd
  have hcop : Nat.Coprime p 2 := (Nat.coprime_two_right (n := p)).mpr hpodd
  have hoddℓ : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  obtain ⟨u, hu⟩ := hoddℓ
  have hkey : ℓ - 1 = 2 * u := by rw [hu, Nat.add_sub_cancel]
  have hmul : p ∣ 2 * u := hkey ▸ hd1
  have hu' : p ∣ u := hcop.dvd_of_dvd_mul_left hmul
  obtain ⟨v, hv⟩ := hu'
  refine ⟨v, ?_⟩
  have h2 : 2 * p * v = 2 * u := by rw [Nat.mul_assoc, hv]
  rw [h2, hkey]

/-- **MERSENNE ROUGHNESS: every prime divisor of `2^p - 1` (`p` an odd prime)
is at least `2p + 1`. -/
theorem jsp87_dvd_sub_one_prime_ge {p ℓ : ℕ} (hp : p.Prime) (hodd : ¬ p = 2)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hd : ℓ ∣ 2 ^ p - 1) : 2 * p + 1 ≤ ℓ := by
  have h := jsp87_dvd_sub_one_prime_two_mul hp hodd hℓ hℓ2 hd
  have hℓ3 : 3 ≤ ℓ := by
    rcases Nat.lt_or_eq_of_le hℓ.two_le with h | h
    · omega
    · exact absurd h.symm hℓ2
  have hle : 2 * p ≤ ℓ - 1 := Nat.le_of_dvd (by omega) h
  omega

/-- **`2^p - 1` is coprime to every integer in `[1, 2p]`** for an odd prime `p`. -/
theorem jsp87_coprime_two_pow_sub_one_of_le {p m : ℕ} (hp : p.Prime) (hodd : ¬ p = 2)
    (hm : 1 ≤ m) (hmle : m ≤ 2 * p) : Nat.Coprime m (2 ^ p - 1) := by
  by_contra hcon
  obtain ⟨l, hl, hlm, hld⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_eq_of_le hp.two_le with h | h
    · omega
    · exact absurd h.symm hodd
  have hl2 : l ≠ 2 := by
    intro h2
    subst h2
    exact (two_not_dvd_two_pow_sub_one (p := p) (by omega)) hld
  have hge := jsp87_dvd_sub_one_prime_ge hp hodd hl hl2 hld
  have hlm' : l ≤ m := Nat.le_of_dvd (by omega) hlm
  have hle : 2 * p + 1 ≤ m := le_trans hge hlm'
  omega

/-- **Every divisor of `2^p - 1` (`p` an odd prime) is `1` or at least
`2p + 1`.**  So `2^p - 1` is a `(2p+1)`-rough number: all of its content lives
above `2p`. -/
theorem jsp87_dvd_two_pow_sub_one_one_or_ge {p d : ℕ} (hp : p.Prime) (hodd : ¬ p = 2)
    (hd : d ∣ 2 ^ p - 1) : d = 1 ∨ 2 * p + 1 ≤ d := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_eq_of_le hp.two_le with h | h
    · omega
    · exact absurd h.symm hodd
  have hpos : (0 : ℕ) < 2 ^ p - 1 := by
    have h := two_pow_sub_lt (a := 1) (b := p) (by norm_num) (by omega)
    omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hpos
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · right
    obtain ⟨l, hl, hld⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := d)).mp hd1
    have hl2 : l ≠ 2 := by
      intro h2
      subst h2
      exact (two_not_dvd_two_pow_sub_one (p := p) (by omega)) (hld.trans hd)
    have hge := jsp87_dvd_sub_one_prime_ge hp hodd hl hl2 (hld.trans hd)
    exact le_trans hge (Nat.le_of_dvd hdpos hld)

/-- **The sharpness of the threshold, at `2^11 - 1 = 23 · 89`:
`23 = 2 · 11 + 1` is its least prime divisor.** -/
theorem jsp87_mersenne_eleven_instances :
    (23 : ℕ) ∣ 2 ^ 11 - 1 ∧ (89 : ℕ) ∣ 2 ^ 11 - 1 ∧ (23 : ℕ) = 2 * 11 + 1 := by
  norm_num [show (11 : ℕ) = 11 from rfl]

/-- **MACHINE-CHECKED NEGATIVE:** no integer at most `22` divides
`2^11 - 1 = 2047`, i.e. the Mersenne roughness really begins at `2p + 1 = 23`. -/
theorem jsp87_two_pow_eleven_rough :
    ∀ m ∈ Finset.Icc 2 22, ¬ (m : ℕ) ∣ 2 ^ 11 - 1 := by
  decide

/-! ## 8. Summary of the split -/

/-- **THE TWO HALVES, IN ONE LINE.**  At every sieve level `k` the Erdős series
is the sum of an explicit rational (the primes `≤ k`) and a positive,
exponentially small number which is irrational exactly when the Erdős series
is. -/
theorem jsp87_series_sieve_rough_summary (k : ℕ) :
    ∃ a b : ℕ, 0 < b ∧
      2 * jsp87Series = (a : ℝ) / (b : ℝ) + jsp87RoughSeries k ∧
      0 < jsp87RoughSeries k ∧ jsp87RoughSeries k ≤ 4 * ((2 : ℝ) ^ (k + 1))⁻¹ := by
  obtain ⟨a, b, hb, h⟩ := jsp87_sieveSeries_rational k
  refine ⟨a, b, hb, ?_, jsp87RoughSeries_pos k, jsp87RoughSeries_le k⟩
  rw [← h]
  exact jsp87_two_mul_series_eq_add_sieve_rough k

end JSP87
