/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertTrunc
import Mathlib.Tactic

/-!
# JSP-000087 : the multiplicative translations of the Erdős series

For `m ≥ 1` put

```
F m = ∑' n, ω (m * (n + 1)) / 2 ^ (n + 1)      (jsp87Multiplier m)
```

i.e. the Erdős series `∑ k ≥ 1, ω(k) / 2 ^ k` read on the **multiples** of `m`.
Note `F 1 = 2 · jsp87Series` (`jsp87Series_shift`).

This module is a **new attack family**.  Rounds 37–79 of this development attacked
the Erdős series itself from thirty-odd directions (the Lambert reduction, the
carry scaffold, the `gcd` arithmetic of the Mersenne numbers, the doubling orbit
of the carries, the digit bookkeeping, the carry excess and sieve content, the
subword complexity of the binary expansion, certified digits, ...).  **No round
ever looked at the multiplicative translations** `n ↦ m * n` of `ω`, i.e. at the
series obtained by restricting the summands to the multiples of a fixed integer.
The family is natural because `ω` is multiplicative, so the multiples of `m`
behave like the integers themselves up to finitely many Lambert terms.

Main results.

* `omega_mul_eq_sum_indicator` : the arithmetic core —
  `ω (m * n) = ω n + ω m - #{p prime : p ∣ m, p ∣ n}`;
* `jsp87_multiplier_eq` (**the flagship**) —
  `F m = 2 · S + ω m - ∑_{p ∈ PF(m)} 1 / (2 ^ p - 1)`: **every multiplier series
  is the Erdős series plus an explicit rational**;
* `jsp87_multiplier_pow` : `F (m ^ k) = F m` — the multiplier series is
  **invariant under taking powers of the multiplier**;
* `jsp87_multiplier_prime`, `jsp87_multiplier_two_pow` : the shift at a prime `q`
  is `1 - 1 / (2 ^ q - 1)` and at a power of `2` is the constant `2 / 3`;
* `jsp87_multiplier_le` : `F m ≤ 2 · S + ω m`, i.e. every translation lies in the
  bounded interval `[S, 2 S + ω m]`;
* `sum_multiples_prime`, `sum_indicator_shift_prime` : the Lambert sum over the
  multiples of a prime, computed **exactly**, at the place `n + 1`.

### What this does *not* give

Every member of the family `{F m}` is `S` plus an *explicit rational*, so the
family transfers rationality but does not create a new route to irrationality: it
localises the headline rather than attacking it.  The one arithmetic input still
missing is unchanged, namely `jsp87_digit_not_eventuallyPeriodic` (the aperiodicity
of the binary digits of `S`), which is the content of the uniform prime-`k`-tuples
hypothesis in Pratt's *published* result (arXiv:2409.15185) and not of the catalog
statement.
-/

namespace JSP87

open Filter

set_option maxHeartbeats 1000000

/-! ## 1. The arithmetic of `ω` under multiplication -/

/-- The prime support of a product is the union of the two prime supports. -/
theorem primeFactors_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).primeFactors = m.primeFactors ∪ n.primeFactors := by
  ext q
  rw [Finset.mem_union]
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hqd, -⟩
    rcases hq.dvd_mul.mp hqd with h1 | h2
    · exact Or.inl ⟨hq, h1, hm⟩
    · exact Or.inr ⟨hq, h2, hn⟩
  · rintro (⟨hq, hqd, -⟩ | ⟨hq, hqd, -⟩)
    · exact ⟨hq, dvd_mul_of_dvd_left hqd n, Nat.mul_ne_zero hm hn⟩
    · exact ⟨hq, dvd_mul_of_dvd_right hqd m, Nat.mul_ne_zero hm hn⟩

/-- **`ω (m * n)` is the sum of the two `ω`'s minus the overlap of the prime
supports.** -/
theorem omega_mul_eq_card_inter {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    omega (m * n) = omega n + omega m - (m.primeFactors ∩ n.primeFactors).card := by
  simp only [omega]
  rw [primeFactors_mul hm hn]
  have h := Finset.card_union_add_card_inter (m.primeFactors) (n.primeFactors)
  omega

/-- The overlap of the two prime supports, read as a divisibility count. -/
theorem card_inter_primeFactors_eq_sum_indicator {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    (m.primeFactors ∩ n.primeFactors).card
      = ∑ p ∈ m.primeFactors, (if p ∣ n then (1 : ℕ) else 0) := by
  have hset : m.primeFactors.filter (fun p => p ∣ n) = m.primeFactors ∩ n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hp, hpn⟩
      exact ⟨hp, Nat.Prime.mem_primeFactors (Nat.prime_of_mem_primeFactors hp) hpn hn⟩
    · rintro ⟨hp, hmem⟩
      exact ⟨hp, (Nat.mem_primeFactors.mp hmem).2.1⟩
  rw [← hset, Finset.card_filter]

/-- **THE ARITHMETIC CORE: `ω` on multiples.**

`ω (m * n) = ω n + ω m - ∑_{p ∈ PF(m)} [p ∣ n]`.  The identity holds for *every*
`n`, including `n = 0`, because every prime divides `0`. -/
theorem omega_mul_eq_sum_indicator {m n : ℕ} (hm : m ≠ 0) :
    omega (m * n) = omega n + omega m
      - ∑ p ∈ m.primeFactors, (if p ∣ n then (1 : ℕ) else 0) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have hcard : ∑ p ∈ m.primeFactors, (if p ∣ 0 then (1 : ℕ) else 0) = omega m := by
      simp [omega]
    simp [hcard, omega]
  · have h := omega_mul_eq_card_inter hm (by omega : n ≠ 0)
    rw [card_inter_primeFactors_eq_sum_indicator hm (by omega : n ≠ 0)] at h
    omega

/-- **Counting lemma:** an `if`-sum of ones over a finset is at most its
cardinality. -/
theorem sum_ite_one_le_card (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ p ∈ s, (if P p then (1 : ℕ) else 0)) ≤ s.card := by
  rw [← Finset.card_filter]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Multiplying by a divisor of `m` does not change `ω`. -/
theorem omega_mul_eq_omega_of_dvd {m n : ℕ} (hdvd : n ∣ m) (hm : m ≠ 0) :
    omega (m * n) = omega m := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · have hz : m = 0 := by rw [hn0] at hdvd; simpa using hdvd
    exact (hm hz).elim
  · have h1 : n.primeFactors ⊆ m.primeFactors := Nat.primeFactors_mono hdvd hm
    have h2 : (m.primeFactors ∩ n.primeFactors) = n.primeFactors := by
      ext p
      simp only [Finset.mem_inter]
      constructor
      · intro hp; exact hp.2
      · intro hp; exact ⟨h1 hp, hp⟩
    have h := omega_mul_eq_card_inter hm (by omega : n ≠ 0)
    rw [h2] at h
    simp only [omega] at h ⊢
    omega

/-- **The prime support of a power is the prime support of the base.** -/
theorem primeFactors_pow {m : ℕ} {k : ℕ} (hk : 1 ≤ k) :
    (m ^ k).primeFactors = m.primeFactors := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have h0 : 0 ^ k = 0 := by rw [Nat.pow_eq_zero]; constructor <;> omega
    rw [h0]
  · have hmk : m ^ k ≠ 0 := by
      intro hz
      have h3 := Nat.pow_eq_zero.mp hz
      omega
    ext p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, -⟩
      exact ⟨hp, (prime_dvd_pow_iff hp k hk).mp hpd, Nat.ne_of_gt hm0⟩
    · rintro ⟨hp, hpd, -⟩
      exact ⟨hp, dvd_pow hpd (by omega : k ≠ 0), hmk⟩

/-- **`ω (m ^ k) = ω m`.** -/
theorem omega_pow {m : ℕ} {k : ℕ} (hk : 1 ≤ k) : omega (m ^ k) = omega m := by
  simp [omega, primeFactors_pow hk]

/-! ## 2. Elementary series facts -/

/-- A shift of the index in a `tsum` drops the zeroth term. -/
theorem jsp87_tsum_shift {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n, f (n + 1)) = (∑' n, f n) - f 0 := by
  have h := hf.tsum_eq_zero_add
  linarith

/-- A `Summable` function has a `HasSum` at its own `tsum`. -/
theorem summable_hasSum {f : ℕ → ℝ} (hf : Summable f) : HasSum f (∑' k, f k) :=
  (hf.hasSum_iff).mpr rfl

/-- The geometric tail `∑' n, 2 ^ -(n + K)` converges. -/
theorem summable_two_pow_negK (K : ℕ) : Summable (fun n : ℕ => ((2 : ℝ) ^ (n + K))⁻¹) := by
  have hs : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have h1 : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ K * ((2 : ℝ)⁻¹) ^ n) := hs.mul_left _
  refine h1.congr fun n => ?_
  rw [mul_comm, ← pow_add, inv_pow]

/-- A constant multiple of the geometric tail converges. -/
theorem summable_const_mul_two_pow_negK (c : ℝ) :
    Summable (fun n : ℕ => c * ((2 : ℝ) ^ (n + 1))⁻¹) :=
  (summable_two_pow_negK 1).mul_left c

/-- **The geometric tail in closed form: `∑' n, 2 ^ -(n + K) = 2 ^ -K * 2`.** -/
theorem tsum_two_pow_negK (K : ℕ) :
    (∑' n : ℕ, ((2 : ℝ) ^ (n + K))⁻¹) = ((2 : ℝ)⁻¹) ^ K * 2 := by
  have hs : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have h1 : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ K * ((2 : ℝ)⁻¹) ^ n) := hs.mul_left _
  have hval : (∑' n : ℕ, ((2 : ℝ)⁻¹) ^ n) = 2 := by
    have h := (hasSum_geometric_of_norm_lt_one (ξ := ((2 : ℝ)⁻¹))
      (by norm_num : ‖((2 : ℝ)⁻¹)‖ < 1)).tsum_eq
    rw [h]
    norm_num
  have key : (∑' n : ℕ, ((2 : ℝ)⁻¹) ^ K * ((2 : ℝ)⁻¹) ^ n)
      = ((2 : ℝ)⁻¹) ^ K * (∑' n : ℕ, ((2 : ℝ)⁻¹) ^ n) := by
    rw [tsum_mul_left]
  have hfun : (fun n : ℕ => ((2 : ℝ) ^ (n + K))⁻¹)
      = fun n => ((2 : ℝ)⁻¹) ^ K * ((2 : ℝ)⁻¹) ^ n := by
    funext n
    rw [mul_comm, ← pow_add, inv_pow]
  rw [hfun, key, hval]

/-- In particular `∑' n, 2 ^ -(n + 1) = 1`. -/
theorem tsum_two_pow_neg_one : (∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  rw [tsum_two_pow_negK 1]
  norm_num

/-- **The Lambert sum over the positive multiples of a prime.** -/
theorem sum_multiples_prime (p : ℕ) (hp : p.Prime) :
    (∑' n : ℕ, (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ n)⁻¹ else 0)) = ((2 : ℝ) ^ p - 1)⁻¹ := by
  have h2 := (hasSum_lamF_fst p).mul_left (2 : ℝ)
  have hfun : (fun n : ℕ => 2 * lamF (n, p))
      = fun n => (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ n)⁻¹ else 0) := by
    funext n
    by_cases h1 : 1 ≤ n
    · by_cases h3 : p ∣ n
      · have hlam : lamF (n, p) = ((2 : ℝ) ^ (n + 1))⁻¹ := by simp [lamF, hp, h1, h3]
        have h13 : 1 ≤ n ∧ p ∣ n := ⟨h1, h3⟩
        rw [hlam, if_pos h13]
        have h2 : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by rw [pow_succ]
        rw [h2]
        field_simp
      · have h13 : ¬ (1 ≤ n ∧ p ∣ n) := by simp [h3]
        have hlam0 : lamF (n, p) = 0 := by simp [lamF, hp, h13]
        rw [hlam0, if_neg h13]
        norm_num
    · simp [lamF, hp, h1]
  have hA : (2 : ℝ) ^ p - 1 ≠ 0 := by
    have h2p : 2 ≤ p := hp.two_le
    have hge : 2 ≤ (2 : ℝ) ^ p := two_pow_ge_two (by omega)
    linarith
  have hval : 2 * ((2 : ℝ) ^ (p + 1) - 2)⁻¹ = ((2 : ℝ) ^ p - 1)⁻¹ := by
    rw [pow_succ]
    field_simp
  rw [hfun, if_pos hp, hval] at h2
  exact h2.tsum_eq

/-- The divisibility indicator `[p | n]`, as a real number. -/
noncomputable def jsp87Ind (p n : ℕ) : ℝ := if p ∣ n then 1 else 0

/-- The same, at the place `n + 1` and with the indicator form. -/
theorem sum_indicator_shift_prime (p : ℕ) (hp : p.Prime) :
    (∑' n : ℕ, jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hgS : Summable (fun k : ℕ =>
      (if p ∣ k then (1 : ℝ) else 0) * ((2 : ℝ) ^ k)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_)
      (summable_two_pow_negK 0)
    by_cases hk : p ∣ k
    · rw [if_pos hk]
      simp
    · rw [if_neg hk]
      simp
  -- the decomposition `g = (multiples of p) + (the zeroth term)`
  have hstep : ∀ k : ℕ, (if p ∣ k then (1 : ℝ) else 0) * ((2 : ℝ) ^ k)⁻¹
      = (if 1 ≤ k ∧ p ∣ k then ((2 : ℝ) ^ k)⁻¹ else 0) + (if k = 0 then (1 : ℝ) else 0) := by
    intro k
    by_cases h0 : k = 0
    · subst h0
      have hnot : ¬ (1 ≤ (0 : ℕ) ∧ p ∣ 0) := by omega
      have hdz : p ∣ 0 := dvd_zero p
      rw [if_pos rfl, if_neg hnot, if_pos hdz]
      ring
    · by_cases hk : p ∣ k
      · have h1 : 1 ≤ k := by omega
        rw [if_pos hk, if_pos ⟨h1, hk⟩, if_neg h0]
        ring
      · have h1 : ¬ (1 ≤ k ∧ p ∣ k) := by omega
        rw [if_neg hk, if_neg h1, if_neg h0]
        ring
  have hdeltaS : Summable (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_)
      (summable_two_pow_negK 0)
    by_cases h : k = 0
    · simp [h]
    · rw [if_neg h]
      simp
  have hdelta : (∑' k : ℕ, (if k = 0 then (1 : ℝ) else 0)) = 1 := by
    have hthis := (summable_hasSum hdeltaS).tsum_eq
    rw [tsum_eq_sum (s := ({0} : Finset ℕ)) (fun b hb => by
      have hne : b ≠ 0 := by simpa using hb
      rw [if_neg hne])] at hthis
    simpa using hthis
  have hgmultiples : Summable (fun n : ℕ =>
      if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ n)⁻¹ else 0) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (summable_two_pow_negK 0)
    by_cases h1 : 1 ≤ n
    · by_cases h2 : p ∣ n
      · rw [if_pos ⟨h1, h2⟩]
        simp
      · have h12 : ¬ (1 ≤ n ∧ p ∣ n) := by simp [h2]
        rw [if_neg h12]
        simp
    · have h12 : ¬ (1 ≤ n ∧ p ∣ n) := by simp [h1]
      rw [if_neg h12]
      simp
  have hHS : HasSum (fun n : ℕ => if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ n)⁻¹ else 0)
      ((2 : ℝ) ^ p - 1)⁻¹ := (hgmultiples.hasSum_iff).mpr (sum_multiples_prime p hp)
  have hS := Summable.tsum_add hHS.summable hdeltaS
  have hval : (∑' k : ℕ, (if p ∣ k then (1 : ℝ) else 0) * ((2 : ℝ) ^ k)⁻¹)
      = ((2 : ℝ) ^ p - 1)⁻¹ + 1 := calc
    (∑' k : ℕ, (if p ∣ k then (1 : ℝ) else 0) * ((2 : ℝ) ^ k)⁻¹)
        = ∑' k : ℕ,
            ((if 1 ≤ k ∧ p ∣ k then ((2 : ℝ) ^ k)⁻¹ else 0) + (if k = 0 then (1 : ℝ) else 0)) :=
      tsum_congr fun k => hstep k
    _ = (∑' k : ℕ, (if 1 ≤ k ∧ p ∣ k then ((2 : ℝ) ^ k)⁻¹ else 0))
        + ∑' k : ℕ, (if k = 0 then (1 : ℝ) else 0) := hS
    _ = ((2 : ℝ) ^ p - 1)⁻¹ + 1 := by rw [hHS.tsum_eq, hdelta]
  have hg0 : (if p ∣ 0 then (1 : ℝ) else 0) * ((2 : ℝ) ^ 0)⁻¹ = 1 := by simp
  have hshift := jsp87_tsum_shift hgS
  rw [hval, hg0] at hshift
  have hbeta : (fun n : ℕ => (if p ∣ n + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = fun n : ℕ =>
          ((fun k : ℕ => (if p ∣ k then (1 : ℝ) else 0) * ((2 : ℝ) ^ k)⁻¹) (n + 1)) := by
    funext k
    rfl
  have hfinal : (∑' n : ℕ, (if p ∣ n + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ((2 : ℝ) ^ p - 1)⁻¹ := by
    rw [hbeta]
    linarith [hshift]
  simpa only [jsp87Ind] using hfinal

/-- The majorant `∑' n, (n + 1) * 2 ^ -(n + 1)` converges. -/
theorem summable_mul_two_pow_neg_succ :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  have hs : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hn : Summable (fun n : ℕ => (n : ℝ) * ((2 : ℝ)⁻¹) ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 : ℝ)⁻¹) (by norm_num))
  have keypt : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      = (2 : ℝ)⁻¹ * ((n : ℝ) * ((2 : ℝ)⁻¹) ^ n) + (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ n := by
    intro n
    push_cast
    rw [two_pow_neg_eq, pow_succ]
    ring
  have key : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (fun n : ℕ => (2 : ℝ)⁻¹ * ((n : ℝ) * ((2 : ℝ)⁻¹) ^ n))
        + (fun n : ℕ => (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ n) := by
    funext n
    exact keypt n
  rw [key]
  exact (hn.mul_left (2 : ℝ)⁻¹).add (hs.mul_left (2 : ℝ)⁻¹)

/-- **The Erdős series with the classical weights `2 ^ -n`, `n ≥ 1`, is
`2 · jsp87Series`.** -/
theorem jsp87Series_shift :
    (∑' n : ℕ, ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 2 * jsp87Series := by
  have hf : Summable (fun k : ℕ => ((omega k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) :=
    summable_omega_mul_inv_two_pow
  have hf' : Summable (fun n : ℕ =>
      ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ ((n + 1) + 1))⁻¹) :=
    summable_nat_add_iff 1 |>.mpr hf
  have hkey : ∀ n : ℕ, ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      = 2 * (((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ ((n + 1) + 1))⁻¹) := by
    intro n
    have h2 : 2 * ((2 : ℝ) ^ (n + 2))⁻¹ = ((2 : ℝ) ^ (n + 1))⁻¹ := by
      have h3 : (2 : ℝ) ^ (n + 2) = (2 : ℝ) ^ (n + 1) * 2 := by rw [pow_succ]
      rw [h3]
      field_simp
    calc ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
        = ((omega (n + 1) : ℕ) : ℝ) * (2 * ((2 : ℝ) ^ (n + 2))⁻¹) := by rw [← h2]
      _ = 2 * (((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 2))⁻¹) := by ring
      _ = 2 * (((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ ((n + 1) + 1))⁻¹) := by
        rw [show n + 2 = n + 1 + 1 by omega]
  rw [tsum_congr fun n => hkey n, Summable.tsum_mul_left (2 : ℝ) hf']
  have h := jsp87_tsum_shift hf
  have hf0 : ((omega 0 : ℕ) : ℝ) * ((2 : ℝ) ^ (0 + 1))⁻¹ = 0 := by simp
  unfold jsp87Series at h ⊢
  linarith

/-! ## 3. The multiplier series -/

/-- **The Erdős series read on the multiples of `m`.** -/
noncomputable def jsp87Multiplier (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((omega (m * (n + 1)) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- **The multiplier series converges.** -/
theorem summable_jsp87Multiplier (m : ℕ) :
    Summable (fun n : ℕ => ((omega (m * (n + 1)) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  have hB : Summable (fun n : ℕ => ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (fun n => ?_) (summable_mul_two_pow_neg_succ)
    have h1 : ((omega (n + 1) : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by
      have h := omega_le_self (n + 1)
      exact_mod_cast h
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hsplit : Summable (fun n : ℕ =>
      ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
        + ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
    (summable_const_mul_two_pow_negK ((omega m : ℕ) : ℝ)).add hB
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)) (fun n => ?_) hsplit
  have h1 : ((omega (m * (n + 1)) : ℕ) : ℝ) ≤ (omega m : ℕ) + omega (n + 1) := by
    have h := omega_mul_le (m := m) (n := n + 1)
    exact_mod_cast h
  have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  linarith [mul_le_mul_of_nonneg_right h1 h2]

/-- The multiplier series is nonnegative. -/
theorem jsp87Multiplier_nonneg (m : ℕ) : 0 ≤ jsp87Multiplier m :=
  tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE FLAGSHIP: a multiplier series is the Erdős series plus an explicit
rational.**

`F m = 2 · S + ω m - ∑_{p ∈ PF(m)} 1 / (2 ^ p - 1)`. -/
theorem jsp87_multiplier_eq (m : ℕ) (hm : 1 ≤ m) :
    jsp87Multiplier m = 2 * jsp87Series + (omega m : ℝ)
      - ∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hpt : ∀ k : ℕ,
      ((omega (m * (k + 1)) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
        = ((omega (k + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
          + ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
          - ∑ p ∈ m.primeFactors, jsp87Ind p (k + 1) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    intro k
    rw [← Finset.sum_mul]
    have hInd : (∑ p ∈ m.primeFactors, jsp87Ind p (k + 1))
        = ((∑ p ∈ m.primeFactors, (if p ∣ k + 1 then (1 : ℕ) else 0) : ℕ) : ℝ) := by
      unfold jsp87Ind
      push_cast
      simp
    rw [hInd]
    have hnat := omega_mul_eq_sum_indicator (m := m) (n := k + 1) (by omega : m ≠ 0)
    have h3 : omega (m * (k + 1))
        + ∑ p ∈ m.primeFactors, (if p ∣ k + 1 then (1 : ℕ) else 0)
        = omega (k + 1) + omega m := by
      have hle : ∑ p ∈ m.primeFactors, (if p ∣ k + 1 then (1 : ℕ) else 0) ≤ omega m := by
        simpa only [omega] using
          (sum_ite_one_le_card m.primeFactors (fun p => p ∣ k + 1))
      omega
    have h1 : ((omega (m * (k + 1)) : ℕ) : ℝ)
        + ((∑ p ∈ m.primeFactors, (if p ∣ k + 1 then (1 : ℕ) else 0) : ℕ) : ℝ)
        = ((omega (k + 1) : ℕ) : ℝ) + ((omega m : ℕ) : ℝ) := by
      rw [← Nat.cast_add, ← Nat.cast_add]
      exact_mod_cast h3
    have h2 : (0 : ℝ)
        ≤ ((∑ p ∈ m.primeFactors, (if p ∣ k + 1 then (1 : ℕ) else 0) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linear_combination ((2 : ℝ) ^ (k + 1))⁻¹ * h1
  -- summability of the three pieces
  have hA := summable_jsp87Multiplier m
  have hB : Summable (fun n : ℕ => ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (fun n => ?_) (summable_mul_two_pow_neg_succ)
    have h1 : ((omega (n + 1) : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by
      have h := omega_le_self (n + 1)
      exact_mod_cast h
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hC : Summable (fun n : ℕ => ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
    summable_const_mul_two_pow_negK ((omega m : ℕ) : ℝ)
  have hD : ∀ p ∈ m.primeFactors,
      Summable (fun n : ℕ => jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    intro p hp
    refine Summable.of_nonneg_of_le (fun n => by unfold jsp87Ind; split_ifs <;> positivity)
      (fun n => ?_) (summable_two_pow_negK 1)
    by_cases h : p ∣ n + 1
    · rw [jsp87Ind, if_pos h]
      simp
    · rw [jsp87Ind, if_neg h]
      simp
  have hE : Summable (fun n : ℕ =>
      ∑ p ∈ m.primeFactors, jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    have hcardS : Summable (fun n : ℕ =>
        ((m.primeFactors.card : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
      summable_const_mul_two_pow_negK ((m.primeFactors.card : ℕ) : ℝ)
    refine Summable.of_nonneg_of_le
      (fun n => Finset.sum_nonneg fun p _ => by unfold jsp87Ind; split_ifs <;> positivity)
      (fun n => ?_) hcardS
    · calc ∑ p ∈ m.primeFactors,
          jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹
          ≤ ∑ _p ∈ m.primeFactors, ((1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
            refine Finset.sum_le_sum fun p _ => ?_
            by_cases h : p ∣ n + 1
            · rw [jsp87Ind, if_pos h, one_mul]
            · rw [jsp87Ind, if_neg h]
              have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
              rw [zero_mul, one_mul]
              exact hpos
          _ = ((m.primeFactors.card : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
            rw [Finset.sum_const, Finset.card_eq_sum_ones, nsmul_eq_mul]
            ring
  have hsplitS : Summable (fun n : ℕ => ((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      + ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := hB.add hC
  have hsplit := Summable.tsum_add hC hB
  have hsum := Summable.tsum_finsetSum hD
  have htsum : (∑' n : ℕ, ∑ p ∈ m.primeFactors,
        jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑ p ∈ m.primeFactors,
        ((if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) : ℝ) := by
    rw [hsum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [sum_indicator_shift_prime p hp', if_pos hp']
  have htsum2 : (∑' n : ℕ, ∑ p ∈ m.primeFactors,
        jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ := by
    rw [htsum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [if_pos hp']
  have h3 := (summable_hasSum hE).tsum_eq
  have h4 : (∑' n : ℕ, (((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      + ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹))
      = 2 * jsp87Series + (omega m : ℝ) := by
    rw [Summable.tsum_add hB hC, jsp87Series_shift]
    rw [tsum_mul_left, tsum_two_pow_neg_one]
    ring
  unfold jsp87Multiplier
  calc (∑' n : ℕ, ((omega (m * (n + 1)) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑' n : ℕ, (((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
          + ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
          - Finset.sum m.primeFactors
              (fun p => jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹)) :=
      tsum_congr fun n => hpt n
    _ = (∑' n : ℕ, (((omega (n + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
          + ((omega m : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹))
        - ∑' n : ℕ, Finset.sum m.primeFactors
            (fun p => jsp87Ind p (n + 1) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
      rw [Summable.tsum_sub hsplitS hE]
    _ = (2 * jsp87Series + (omega m : ℝ))
        - ∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ := by
      rw [h4]
      rw [h3]
      rw [htsum2]

/-- **The prime support of a prime is the singleton.** -/
theorem primeFactors_prime (q : ℕ) (hq : q.Prime) : q.primeFactors = {q} := by
  have hsub : q.primeFactors ⊆ {q} := by
    intro p hp
    obtain ⟨hp', hpd, -⟩ := Nat.mem_primeFactors.mp hp
    exact Finset.mem_singleton.mpr (prime_eq_of_prime_dvd hp' hq hpd)
  have hsup : {q} ⊆ q.primeFactors := by
    intro p hp
    have hpq : p = q := Finset.mem_singleton.mp hp
    rw [hpq]
    refine hq.mem_primeFactors (Nat.dvd_refl q) ?_
    intro hz
    exact hq.ne_zero (by simpa using hz)
  exact Finset.Subset.antisymm hsub hsup

/-- **The multiplier series is invariant under taking powers of the multiplier.** -/
theorem jsp87_multiplier_pow (m : ℕ) (k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    jsp87Multiplier (m ^ k) = jsp87Multiplier m := by
  have hmk : 1 ≤ m ^ k := Nat.pow_pos (Nat.zero_lt_one.trans_le hm)
  rw [jsp87_multiplier_eq (m ^ k) hmk, jsp87_multiplier_eq m hm]
  rw [omega_pow hk, primeFactors_pow hk]

/-- **At a prime the shift is `1 - 1 / (2 ^ q - 1)`.** -/
theorem jsp87_multiplier_prime (q : ℕ) (hq : q.Prime) :
    jsp87Multiplier q = 2 * jsp87Series + 1 - ((2 : ℝ) ^ q - 1)⁻¹ := by
  have hq2 : 2 ≤ q := hq.two_le
  have hq1 : (1 : ℕ) ≤ q := by omega
  rw [jsp87_multiplier_eq q hq1]
  simp only [omega, primeFactors_prime q hq, Finset.card_singleton, Finset.sum_singleton,
    Nat.cast_one]

/-- **At a power of `2` the shift is the constant `2 / 3`.** -/
theorem jsp87_multiplier_two_pow (k : ℕ) (hk : 1 ≤ k) :
    jsp87Multiplier (2 ^ k) = 2 * jsp87Series + 2 / 3 := by
  rw [jsp87_multiplier_pow 2 k (by norm_num) hk]
  rw [jsp87_multiplier_prime 2 (by norm_num : (2 : ℕ).Prime)]
  rw [show ((2 : ℝ) ^ 2 - 1)⁻¹ = (1 / 3 : ℝ) by norm_num]
  ring_nf

/-- **Every translation is at most `2 · S + ω m`** (the shift is a rational). -/
theorem jsp87_multiplier_le (m : ℕ) (hm : 1 ≤ m) :
    jsp87Multiplier m ≤ 2 * jsp87Series + (omega m : ℝ) := by
  rw [jsp87_multiplier_eq m hm]
  have hnonneg : 0 ≤ ∑ p ∈ m.primeFactors, ((2 : ℝ) ^ p - 1)⁻¹ :=
    Finset.sum_nonneg fun p hp => by
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have h2 : 2 ≤ p := hp'.two_le
      have hge : 2 ≤ (2 : ℝ) ^ p := two_pow_ge_two (by omega)
      have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by linarith
      exact (inv_pos.mpr hpos).le
  linarith

end JSP87
