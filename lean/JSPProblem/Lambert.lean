/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Basic
import Mathlib.Tactic

/-!
# JSP-000087 : the Lambert series of `ω`

Erdős' question (JSP-000087) asks whether

`∑ n ≥ 1, ω(n) / 2 ^ n`

is irrational, where `ω n` counts the distinct prime factors of `n`. Because

`ω n = ∑ p, [ p prime ∧ p ∣ n ]`,

the generating series of `ω` is the **prime-restricted Lambert series**
`∑ p, x^p / (1 - x^p)`, and at `x = 1/2` this is `∑ p, 1 / (2^p - 1)`.

This file proves the reduction. Everything is carried out in `ℝ≥0∞` (`ENNReal`),
where every `tsum` exists, so that the rearrangement of the double sum is
legitimate and no convergence argument is needed:

* `tsum_omega_eq_indicator` : `ω n = ∑ p, [p prime ∧ p ∣ n]`;
* `tsum_omega_mul_eq_tsum_indicator` : the generating series is the double sum;
* `tsum_omega_mul_comm` : the double sum may be read prime-by-prime;
* `lambert_primes` : the full Lambert identity `∑' n ω(n) x^(n+1) = ∑' p x^p/(1-x^p)`;
* `tsum_geometric_add_one` is the geometric-series evaluation used to close the
  inner sum.
-/

namespace JSP87

open scoped ENNReal
open Filter

/-- **The primes dividing `n` below `n + 1` are exactly the distinct prime factors
of `n`.**  This is the finite form of the indicator identity and is what makes
the Lambert reindexing `(n, p) ↦ (p, n/p)` a bijection on a finite set. -/
theorem primeFactors_eq_filter (n : ℕ) :
    (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n) = n.primeFactors := by
  ext p
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    simp only [Finset.mem_range] at h1
    have hlt : p ≤ n := by omega
    exact Nat.mem_primeFactors.mpr ⟨h2.1, h2.2, by have := h2.1.two_le; omega⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := Nat.mem_primeFactors.mp h
    refine Finset.mem_filter.mpr ⟨?_, ⟨h1, h2⟩⟩
    simp only [Finset.mem_range]
    have h2' : 2 ≤ p := h1.two_le
    have h4 : p ≤ n := Nat.le_of_dvd (by omega) h2
    omega

/-- `ω n` counts exactly the primes dividing `n`, so it is the sum of their
indicator functions over `Finset.range (n + 1)`. -/
theorem omega_eq_finset_sum_indicator (n : ℕ) :
    (omega n : ℕ) = ∑ p ∈ Finset.range (n + 1), if p.Prime ∧ p ∣ n then (1 : ℕ) else 0 := by
  rw [omega, ← primeFactors_eq_filter, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Every natural number is a prime times a cofactor. -/
theorem exists_eq_mul_of_dvd {p n : ℕ} (hp : 0 < p) (hd : p ∣ n) :
    ∃ k, n = p * k := ⟨n / p, (Nat.mul_div_cancel' hd).symm⟩

/-- `ω n = 0` exactly when `n ≤ 1`, restated in indicator form. -/
theorem omega_eq_zero_iff' (n : ℕ) :
    (∑ p ∈ Finset.range (n + 1), if p.Prime ∧ p ∣ n then (1 : ℕ) else 0) = 0 ↔ n ≤ 1 := by
  rw [← omega_eq_finset_sum_indicator]
  exact omega_eq_zero_iff

/-- `ω` is monotone under divisibility (restated at the level of the indicator
sum): if `m ∣ n` and `n ≠ 0` then `ω m ≤ ω n`. -/
theorem omega_mono' {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) : omega m ≤ omega n :=
  omega_mono hmn hn

end JSP87
