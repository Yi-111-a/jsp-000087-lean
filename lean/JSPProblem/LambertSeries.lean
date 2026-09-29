/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Lambert
import JSPProblem.Convergence
import Mathlib.Tactic

/-!
# JSP-000087 : the Lambert rearrangement, at finite truncation

Erdős' question (JSP-000087) is whether `∑ n ≥ 1, ω(n) / 2 ^ n` is irrational.
Because `ω n = #{ p prime : p ∣ n }`, the generating series of `ω` is the
**prime-restricted Lambert series**

```
∑ n ≥ 0, ω(n) x ^ (n+1)  =  ∑ p prime, x ^ (p+1) / (1 - x ^ p),
```

and at `x = 1/2` this becomes `∑ p prime, 1 / (2 ^ (p+1) - 2)`.

The rearrangement is a *reindexing of a double sum*, and its combinatorial heart
is the bijection

```
(n, p)  ↦  (p, n / p)      for p ∣ n,  p prime
```

which exchanges the index `n` with the prime `p`.  This file formalises exactly
that bijection at a finite truncation `n < N`, which is the form in which it is
actually used; the infinite version additionally requires passing to a limit.

Main results:

* `omega_eq_sum_indicator_dvd` : `ω n = ∑ p < N, [p prime ∧ p ∣ n]` for `0 < n < N`;
* `sum_multiples_reindex` : the positive multiples of a prime `p` below `N` are
  exactly `p * k` with `k < N` and `k ≥ 1`, and the weighted sums agree;
* `jsp87_finset_eq_prime_lambert` : the truncated Erdős series
  `∑ n < N, ω(n) / 2^(n+1)` is *exactly* the truncated prime-restricted Lambert
  series `∑ p prime, ∑ { k ≥ 1 : p k < N } 2^(p k + 1)⁻¹`;
* `jsp87_finset_eq_prime_lambert_ten` : that common value at `N = 10` is
  `263 / 1024`.

Together with `JSPProblem/Convergence.lean` (which proves that the series is a
well-defined real number) this is the full formal content of the reduction
`∑ ω(n) x^n = ∑_p x^p/(1-x^p)` from which Erdős (1948) and Pratt (arXiv:2409.15185)
start.
-/

namespace JSP87

/-- The summand of the Erdős series, named. -/
noncomputable def jsp87Term (n : ℕ) : ℝ := ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

@[simp] theorem jsp87Term_zero : jsp87Term 0 = 0 := by simp [jsp87Term]

/-- **The indicator form of `ω` over an arbitrary finite range.**

If `0 < n < N` then every prime factor of `n` is `< N`, so `ω n` is the number of
`p < N` that are prime and divide `n`. -/
theorem omega_eq_sum_indicator_dvd (n N : ℕ) (hn : 0 < n) (hnN : n < N) :
    (∑ p ∈ Finset.range N, if p.Prime ∧ p ∣ n then (1 : ℕ) else 0) = omega n := by
  have key : (Finset.range N).filter (fun p => p.Prime ∧ p ∣ n) = n.primeFactors := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro p hpmem
      rcases Finset.mem_filter.mp hpmem with ⟨hpN, hq', hqd⟩
      exact Nat.mem_primeFactors.mpr ⟨hq', hqd, Nat.ne_of_gt hn⟩
    · intro p hpmem
      rcases Nat.mem_primeFactors.mp hpmem with ⟨hq', hqd, hn0⟩
      have hq1 : 1 ≤ n := by omega
      have hle : p ≤ n := Nat.le_of_dvd hn hqd
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hq', hqd⟩
  rw [← Finset.sum_filter, key, ← Finset.card_eq_sum_ones]
  rfl

/-- **Reindexing the positive multiples of a prime.**

For a prime `p` and any `N`, the map `k ↦ p * k` is a bijection from
`{ k < N : k ≥ 1, p * k < N }` onto `{ n < N : p ∣ n, n ≥ 1 }`; in particular the
two corresponding `Finset` sums of the same weight agree. -/
theorem sum_multiples_reindex (p N : ℕ) (hp : p.Prime) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, (if 1 ≤ n ∧ p ∣ n then w n else 0) : ℝ)
      = ∑ k ∈ Finset.range N, (if 1 ≤ k ∧ p * k < N then w (p * k) else 0) := by
  have hp0 : 0 < p := hp.pos
  set A : Finset ℕ := Finset.range N with hA
  set S : Finset ℕ := A.filter (fun n => 1 ≤ n ∧ p ∣ n) with hS
  set T : Finset ℕ := A.filter (fun k => 1 ≤ k ∧ p * k < N) with hT
  have hleft : (∑ n ∈ A, (if 1 ≤ n ∧ p ∣ n then w n else 0) : ℝ) = ∑ n ∈ S, w n := by
    rw [hS, Finset.sum_filter]
  have hright : (∑ k ∈ A, (if 1 ≤ k ∧ p * k < N then w (p * k) else 0) : ℝ)
      = ∑ k ∈ T, w (p * k) := by
    rw [hT, Finset.sum_filter]
  have hmem : ∀ k ∈ T, p * k ∈ S := by
    intro k hk
    rw [hT, Finset.mem_filter, hA, Finset.mem_range] at hk
    obtain ⟨hkN, hk1, hk2⟩ := hk
    have hk0 : 0 < k := by omega
    have h1pk : 1 ≤ p * k := by
      have hpos : 0 < p * k := Nat.mul_pos hp0 hk0
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hk2, ⟨h1pk, dvd_mul_of_dvd_left (dvd_refl p) k⟩⟩
  have hinj : ∀ a ∈ T, ∀ b ∈ T, p * a = p * b → a = b := by
    intro a _ b _ heq
    exact Nat.mul_left_cancel hp0 heq
  have hsurj : ∀ b : ℕ, b ∈ S →
      Exists fun a : ℕ => Exists fun (_ha : a ∈ T) => p * a = b := by
    intro m hm
    rw [hS, Finset.mem_filter, hA, Finset.mem_range] at hm
    obtain ⟨hmN, hm1, ⟨k, hk⟩⟩ := hm
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hz | hk'
      · rw [hz, Nat.mul_zero] at hk
        omega
      · exact hk'
    have hkk : k ≤ p * k := Nat.le_mul_of_pos_left k hp0
    have hpklt : p * k < N := by rw [← hk]; exact hmN
    have hklt : k < N := by omega
    have hk1 : 1 ≤ k := by omega
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, ⟨hk1, hpklt⟩⟩, hk.symm⟩
  have hbij : (∑ k ∈ T, w (p * k) : ℝ) = ∑ n ∈ S, w n :=
    Finset.sum_bij (fun k (_ : k ∈ T) => p * k) hmem hinj hsurj (fun _ _ => rfl)
  rw [hleft, hright]
  exact hbij.symm

/-- **Casting the count of prime divisors from `ℕ` to `ℝ`.** -/
theorem sum_indicator_cast (n : ℕ) (s : Finset ℕ) :
    (∑ p ∈ s, (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
      = ((∑ p ∈ s, (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℕ) else 0) : ℕ) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha _ => by_cases hc : a.Prime ∧ 1 ≤ n ∧ a ∣ n <;> simp [hc]

/-- A non-prime `p` contributes nothing: the guarded sum over the divisors of `n` is `0`. -/
theorem guarded_dvd_sum_eq_zero (N p : ℕ) (hp : ¬p.Prime) :
    ((∑ n ∈ Finset.range N,
      (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) : ℝ) = 0 :=
  Finset.sum_eq_zero fun i _ => by
    by_cases h : p.Prime ∧ 1 ≤ i ∧ p ∣ i
    · exact absurd h.1 hp
    · simp [h]

/-- A non-prime `p` contributes nothing: the guarded Lambert tail is `0`. -/
theorem guarded_lambert_sum_eq_zero (N p : ℕ) (hp : ¬p.Prime) :
    ((∑ k ∈ Finset.range N,
      (if p.Prime ∧ 1 ≤ k ∧ p * k < N then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0)) : ℝ) = 0 :=
  Finset.sum_eq_zero fun k _ => by
    by_cases h : p.Prime ∧ 1 ≤ k ∧ p * k < N
    · exact absurd h.1 hp
    · simp [h]

/-- **The truncated Erdős series is the truncated prime-restricted Lambert series.**

For every `N`, the sum of `ω(n) / 2^(n+1)` over `1 ≤ n < N` equals the sum over
primes `p` of the geometric tails `∑ { k ≥ 1 : p k < N } 2^(p k + 1)⁻¹`.

(The hypothesis `1 ≤ N` is not needed by the proof — the identity also holds
trivially at `N = 0` — but is kept because it is the range in which the identity
is used.) -/
theorem jsp87_finset_eq_prime_lambert (N : ℕ) (_hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, jsp87Term n)
      = ∑ p ∈ Finset.range N, ∑ k ∈ Finset.range N,
          (if p.Prime ∧ 1 ≤ k ∧ p * k < N then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
  -- Step 1: expand `ω n` as a sum of indicators; the weight does not depend on `p`.
  have hstep1 : (∑ n ∈ Finset.range N, jsp87Term n)
      = ∑ n ∈ Finset.range N, ∑ p ∈ Finset.range N,
          (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · -- the `n = 0` row: `jsp87Term 0 = 0` and every term on the right is killed
        -- by the guard `1 ≤ n`, so both sides vanish
      rw [jsp87Term_zero]
      exact (Finset.sum_eq_zero fun p _ => by simp).symm
    · have h1 : (∑ p ∈ Finset.range N, (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℕ) else 0) : ℕ)
          = omega n := by
        calc (∑ p ∈ Finset.range N, (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℕ) else 0) : ℕ)
            = ∑ p ∈ Finset.range N, (if p.Prime ∧ p ∣ n then (1 : ℕ) else 0) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              have h1n : 1 ≤ n := by omega
              simp [h1n]
          _ = omega n := omega_eq_sum_indicator_dvd n N hnpos (Finset.mem_range.mp hn)
      have hcast : (∑ p ∈ Finset.range N,
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) : ℝ)
          = ((omega n : ℕ) : ℝ) := by rw [sum_indicator_cast, h1]
      have hmul : (∑ p ∈ Finset.range N,
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0)) * ((2 : ℝ) ^ (n + 1))⁻¹
          = ∑ p ∈ Finset.range N,
              ((if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
        Finset.sum_mul _ _ _
      simp only [jsp87Term]
      calc ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
          = (∑ p ∈ Finset.range N, (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
              * ((2 : ℝ) ^ (n + 1))⁻¹ := by rw [hcast]
        _ = ∑ p ∈ Finset.range N,
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) * ((2 : ℝ) ^ (n + 1))⁻¹ := hmul
        _ = ∑ p ∈ Finset.range N,
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            by_cases h : p.Prime ∧ 1 ≤ n ∧ p ∣ n <;> simp [h]

  -- Step 2: swap the two indices (the double sum is over a product of finsets).
  have hstep2 : ((∑ n ∈ Finset.range N, ∑ p ∈ Finset.range N,
          (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) : ℝ)
      = ∑ p ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) :=
    Finset.sum_comm (s := Finset.range N) (t := Finset.range N)
      (f := fun n p : ℕ => (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0))

  -- Step 3: for each prime `p`, reindex the positive multiples of `p` as `p * k`.
  have hstep3 : ((∑ p ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) : ℝ)
      = ∑ p ∈ Finset.range N, ∑ k ∈ Finset.range N,
          (if p.Prime ∧ 1 ≤ k ∧ p * k < N then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime
    · have hdrop : ((∑ n ∈ Finset.range N,
            (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) : ℝ)
          = ∑ n ∈ Finset.range N,
              (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases h2 : p.Prime ∧ 1 ≤ n ∧ p ∣ n <;>
          by_cases h3 : 1 ≤ n ∧ p ∣ n <;> simp [h2, h3, hp]
      have hre := sum_multiples_reindex p N hp (fun m => ((2 : ℝ) ^ (m + 1))⁻¹)
      rw [hdrop, hre]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h2 : 1 ≤ k ∧ p * k < N <;>
        by_cases h3 : p.Prime ∧ 1 ≤ k ∧ p * k < N <;> simp [h2, h3, hp]
    · exact (guarded_dvd_sum_eq_zero N p hp).trans (guarded_lambert_sum_eq_zero N p hp).symm
  rw [hstep1, hstep2, hstep3]

/-- **A sanity check of the Lambert rearrangement at `N = 10`.**

At `N = 10` the truncated Erdős series is
`1/8 + 1/16 + 1/32 + 1/64 + 2/128 + 1/256 + 1/512 + 2/1024 = 263/1024`, and the
Lambert side groups the same terms prime-by-prime:
`p = 2` contributes `1/8 + 1/32 + 1/128 + 1/512` (from `k = 1, 2, 3, 4`),
`p = 3` contributes `1/16 + 1/128 + 1/1024` (`k = 1, 2, 3`),
`p = 5` contributes `1/64`, and `p = 7` contributes `1/256`; the total is
`263 / 1024`. -/
theorem jsp87_finset_eq_prime_lambert_ten :
    (∑ n ∈ Finset.range 10, jsp87Term n) = 263 / 1024 := by
  have h := jsp87_finset_eq_prime_lambert (N := 10) (by omega)
  rw [h]
  norm_num [Finset.sum_range_succ, jsp87Term]

end JSP87
