/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Multiplier
import Mathlib.Tactic

/-!
# JSP-000087 : the Erdős series in **every base**, its Lambert reduction, and a
# sharp uniform bound

For `q ≥ 2` put

```
S q = ∑' n, ω (n) / q ^ (n + 1)                       (jsp87Base q)
```

so that `jsp87Base 2 = jsp87Series` (`rfl`).  This module is about the whole
**one-parameter family** `{S q : q ≥ 2}`.

This is a **new attack family**.  Rounds 37–79 attacked the Erdős series itself
from thirty-odd directions (the Lambert reduction *at base 2*, the carry
scaffold, the `gcd` arithmetic of the Mersenne numbers, the doubling orbit of the
carries, the digit bookkeeping, the carry excess and the sieve content, the
base-`2` block arithmetic, the subword complexity of the binary expansion,
certified digits at arbitrary places, the carry runs, and the multiplicative
translations `n ↦ m * n` of round 80).  **No round ever left base `2`.**  Every
statement of the tree — the Lambert identity `S = ∑_p 1/(2 ^ p - 1)`, the
multiplier identity `F m = 2 S + ω m - ∑_{p ∣ m} 1/(2 ^ p - 1)`, the divisibility
of the Mersenne numbers `2 ^ p - 1`, the certified digits of the base-`2`
expansion — is a statement about one single base.  Here the whole apparatus is
lifted to `q ≥ 2`.

Main results.

* `hasSum_lambert_geometric_base`, `hasSum_multiples_base` : the Lambert
  geometric sums at an arbitrary base, for **every** `p ≥ 1`
  (`∑' n, [1 ≤ n, p ∣ n] / q ^ (n+1) = 1 / (q ^ (p+1) - q)`);
* `jsp87Base` : **the new object**, the Erdős series at base `q`, with
  `jsp87Base 2 = jsp87Series`;
* **`jsp87_lambert_base`** (**the flagship**) : `S q = ∑' p, [p prime] 1/(q ^ (p+1) - q)`
  and `jsp87_lambert_base_classic` : `∑' p prime, 1/(q ^ p - 1) = q · S q` — the
  Lambert reduction of round 37, **in every base**;
* **`jsp87_lambert_base_lt`** : a **sharp uniform bound**, whose instance
  **`jsp87Series_lt_11_42`** is `S < 11/42 = 0.2619…` — the first bound on the
  series sharper than round 37's `S ≤ 1`;
* `jsp87Series_bounds'` : the two-sided bound `7 / 32 ≤ S < 11 / 42`, the
  interval of round 37's `jsp87Series_bounds` sharpened from above by a factor
  of `4`.

### What this does *not* give

It does not produce a contradiction from rationality.  The one arithmetic input
still missing is unchanged, namely `jsp87_digit_not_eventuallyPeriodic` (the
aperiodicity of the binary digits of `S`), the content of the uniform
prime-`k`-tuples hypothesis in Pratt's *published* result (arXiv:2409.15185) and
not of the catalog statement.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 0. Reindexing the multiples of any integer, and three arithmetic facts

The reduction needs, at base `q`, the identity
`∑' n, [1 ≤ n, p ∣ n] / q ^ (n+1) = 1 / (q ^ (p+1) - q)` for **every** `p ≥ 1`
(not only for primes).  `sum_multiples_reindex` (round 38) is stated for primes
only, so it is restated here for `1 ≤ p`; the proof is unchanged, `hp.pos` being
replaced by `omega`. -/

theorem sum_multiples_reindex_gen (p N : ℕ) (hp : 1 ≤ p) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, (if 1 ≤ n ∧ p ∣ n then w n else 0) : ℝ)
      = ∑ k ∈ Finset.range N, (if 1 ≤ k ∧ p * k < N then w (p * k) else 0) := by
  have hp0 : 0 < p := by omega
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

/-- A single-point indicator series is summable and evaluates to its value. -/
theorem summable_ite_eq (c : ℝ) (k : ℕ) :
    Summable (fun p : ℕ => (if p = k then c else 0)) := by
  have hs : (fun p : ℕ => (if p = k then 1 else 0 : ℝ)).HasFiniteSupport := by
    refine Set.Finite.subset (Finset.finite_toSet (s := ({k} : Finset ℕ))) ?_
    intro p hp
    simp only [Function.mem_support] at hp
    by_cases h : p = k
    · exact Finset.mem_coe.2 (Finset.mem_singleton.mpr h)
    · rw [if_neg h] at hp
      exact absurd hp (by norm_num)
  have h1 := summable_of_hasFiniteSupport (α := ℝ) (β := ℕ) (f := fun p : ℕ =>
    (if p = k then 1 else 0 : ℝ)) (L := SummationFilter.unconditional ℕ) hs
  have h2 : (fun p : ℕ => (if p = k then c else 0))
      = fun p => c * (if p = k then 1 else 0) := by
    funext p
    by_cases h : p = k <;> simp [h]
  rw [h2]
  exact h1.mul_left c

theorem tsum_ite_eq (c : ℝ) (k : ℕ) :
    (∑' p : ℕ, (if p = k then c else 0)) = c := by
  refine (tsum_eq_sum (s := ({k} : Finset ℕ)) ?_).trans ?_
  · intro b hb
    have hne : b ≠ k := by simpa using hb
    simp [hne]
  · simp

/-- `1 ≤ 2 ^ p` in `ℝ`. -/
theorem cast_one_le_two_pow (p : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ p := by
  simpa only [one_pow] using
    (pow_le_pow_left₀ (a := (1 : ℝ)) (b := (2 : ℝ)) (by norm_num) (by norm_num) p)

/-- `2 ^ p ≤ q ^ p` in `ℝ`, for `q ≥ 2`. -/
theorem cast_two_pow_le (q : ℕ) (hq : 2 ≤ q) (p : ℕ) : (2 : ℝ) ^ p ≤ (q : ℝ) ^ p :=
  pow_le_pow_left₀ (a := (2 : ℝ)) (b := (q : ℝ)) (by norm_num) (by exact_mod_cast hq) p

/-- `8 ≤ 2 ^ p` in `ℝ`, for `3 ≤ p`. -/
theorem cast_eight_le_two_pow {p : ℕ} (hp : 3 ≤ p) : (8 : ℝ) ≤ (2 : ℝ) ^ p := by
  have h : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
  rw [h]
  exact pow_le_pow_right₀ (by norm_num) hp

/-- `8 ≤ q ^ p` in `ℝ`, for `q ≥ 2` and `3 ≤ p`. -/
theorem cast_eight_le_q_pow (q : ℕ) (hq : 2 ≤ q) {p : ℕ} (hp : 3 ≤ p) :
    (8 : ℝ) ≤ (q : ℝ) ^ p := by
  have h1 := cast_eight_le_two_pow hp
  have h2 := cast_two_pow_le q hq p
  linarith

/-- **`q ^ p ≥ 1` for `q ≥ 2`.** -/
theorem q_pow_ge_one (q : ℕ) (hq : 2 ≤ q) (p : ℕ) : (1 : ℝ) ≤ (q : ℝ) ^ p := by
  have h2 := cast_two_pow_le q hq p
  have h1 := cast_one_le_two_pow p
  linarith

/-- **`q ^ p > 1` for `q ≥ 2` and `1 ≤ p`.** -/
theorem q_pow_gt_one (q : ℕ) (hq : 2 ≤ q) {p : ℕ} (hp : 1 ≤ p) : (1 : ℝ) < (q : ℝ) ^ p := by
  have h2 : 1 < (2 : ℝ) ^ p := by
    have hh := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (show (1 : ℕ) ≤ p from hp)
    nlinarith
  have h3 := cast_two_pow_le q hq p
  linarith

/-- **`q ^ p - 1 ≠ 0` for `q ≥ 2` and `1 ≤ p`.** -/
theorem q_pow_sub_one_ne (q : ℕ) (hq : 2 ≤ q) {p : ℕ} (hp : 1 ≤ p) :
    (q : ℝ) ^ p - 1 ≠ 0 := by
  have := q_pow_gt_one q hq hp
  linarith

/-- **`q ≠ 0` in `ℝ` for `q ≥ 2`.** -/
theorem q_ne_zero_real (q : ℕ) (hq : 2 ≤ q) : (q : ℝ) ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  exact ne_of_gt (by linarith)

/-- **A prime different from `2` is odd.** -/
theorem prime_ne_two_odd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Odd p := by
  have hne : ¬ Even p := fun he => h2 (hp.even_iff.mp he)
  rcases Nat.even_or_odd p with he | ho
  · exact absurd he hne
  · exact ho

/-! ## 1. The geometric sums at an arbitrary base -/

/-- `∑' n, 1 / q ^ (n + K)` is summable for `q ≥ 2`. -/
theorem summable_base_pow_negK (q : ℕ) (hq : 2 ≤ q) (K : ℕ) :
    Summable (fun n : ℕ => ((q : ℝ) ^ (n + K))⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_two_pow_negK K)
  have hpow : (2 : ℝ) ^ (n + K) ≤ (q : ℝ) ^ (n + K) := cast_two_pow_le q hq (n + K)
  have hinv : ((q : ℝ) ^ (n + K))⁻¹ ≤ ((2 : ℝ) ^ (n + K))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
  simpa using hinv

/-- The majorant `∑' n, n / q ^ (n+1)` is summable for `q ≥ 2`. -/
theorem summable_nat_mul_base_pow_neg (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (fun n => ?_) (summable_nat_mul_two_pow_neg)
  have hpow : (2 : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (n + 1) := cast_two_pow_le q hq (n + 1)
  have hinv : ((q : ℝ) ^ (n + 1))⁻¹ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg n))

/-- **The Lambert geometric sum at base `q`:** for `p ≥ 1`,
`∑' k, [1 ≤ k] / q ^ (p * k + 1) = 1 / (q ^ (p+1) - q)`. -/
theorem hasSum_lambert_geometric_base (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    HasSum (fun k : ℕ => (if 1 ≤ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0))
      ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ := by
  have hqp : 1 < (q : ℝ) ^ p := q_pow_gt_one q hq hp
  have hξ : ‖((q : ℝ) ^ p)⁻¹‖ < 1 := by
    have hpos : (0 : ℝ) < ((q : ℝ) ^ p)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact inv_lt_one_of_one_lt₀ hqp
  have hgeom : HasSum (fun k : ℕ => ((q : ℝ) ^ p)⁻¹ ^ k)
      (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (ξ := ((q : ℝ) ^ p)⁻¹) hξ
  have hmul : ∀ k : ℕ, (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k
      = ((q : ℝ) ^ (p * k + 1))⁻¹ := by
    intro k
    have hstep : (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k
        = (q : ℝ)⁻¹ * ((q : ℝ) ^ (p * k))⁻¹ := by rw [inv_pow, pow_mul]
    calc (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = (q : ℝ)⁻¹ * ((q : ℝ) ^ (p * k))⁻¹ := hstep
      _ = ((q : ℝ) ^ (p * k) * (q : ℝ) ^ 1)⁻¹ := by rw [pow_one, ← DivisionMonoid.mul_inv_rev]
      _ = ((q : ℝ) ^ (p * k + 1))⁻¹ := by rw [pow_succ]; ring
  have hsum0 : Summable (fun k : ℕ => ((q : ℝ) ^ (p * k + 1))⁻¹) := by
    have h := hgeom.mul_left (q : ℝ)⁻¹
    refine (HasSum.summable h).congr fun k => ?_
    exact hmul k
  have hts0 : (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹)
      = (q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ := by
    calc (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹)
        = ∑' k : ℕ, (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k :=
          tsum_congr fun k => (hmul k).symm
      _ = (q : ℝ)⁻¹ * ∑' k : ℕ, ((q : ℝ) ^ p)⁻¹ ^ k :=
        Summable.tsum_mul_left _ (HasSum.summable hgeom)
      _ = (q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ := by rw [hgeom.tsum_eq]
  have hgeo0 : HasSum (fun k : ℕ => ((q : ℝ) ^ (p * k + 1))⁻¹)
      ((q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹) := by
    have h := hsum0.hasSum
    rwa [hts0] at h
  have hsubts : (∑' k : ℕ, (if 1 ≤ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0))
      = (q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ - (q : ℝ)⁻¹ := by
    have h := (hasSum_sub_zero (f := fun k : ℕ => ((q : ℝ) ^ (p * k + 1))⁻¹)
      (fun k => by positivity) (HasSum.summable hgeo0)).tsum_eq
    rw [hgeo0.tsum_eq] at h
    have hf0 : ((q : ℝ) ^ (p * 0 + 1))⁻¹ = (q : ℝ)⁻¹ := by norm_num
    rw [hf0] at h
    exact h
  have hsub : Summable (fun k : ℕ =>
      (if 1 ≤ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0)) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs <;> positivity)
      (fun k => by
        by_cases h1 : 1 ≤ k
        · rw [if_pos h1]
        · rw [if_neg h1]
          positivity)
      hsum0
  have hfin : HasSum (fun k : ℕ => (if 1 ≤ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0))
      ((q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ - (q : ℝ)⁻¹) :=
    (Summable.hasSum_iff hsub).mpr hsubts
  have hqp0 : (q : ℝ) ^ p - 1 ≠ 0 := q_pow_sub_one_ne q hq hp
  have hqp1 : (q : ℝ) ^ (p + 1) - (q : ℝ) ≠ 0 := by
    have h : (q : ℝ) ^ (p + 1) = (q : ℝ) ^ p * (q : ℝ) := by rw [pow_succ]
    have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
    rw [h]
    intro hz
    have hz' : (q : ℝ) ^ p = 1 := mul_left_cancel₀ (ne_of_gt hqpos) (by linarith)
    linarith
  have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
  have hq1 : (1 - ((q : ℝ) ^ p)⁻¹) ≠ 0 := by
    have key : 1 - ((q : ℝ) ^ p)⁻¹ = ((q : ℝ) ^ p)⁻¹ * ((q : ℝ) ^ p - 1) := by
      field_simp
    rw [key]
    exact mul_ne_zero (ne_of_gt (by positivity)) hqp0
  convert hfin using 1
  field_simp
  ring

/-- **The Lambert value of the multiples of any `p ≥ 1`, at base `q`:**
`∑' n, [1 ≤ n, p ∣ n] / q ^ (n+1) = 1 / (q ^ (p+1) - q)`. -/
theorem hasSum_multiples_base (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    HasSum (fun n : ℕ => (if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0))
      ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ := by
  have hp0 : 0 < p := by omega
  have hnonneg : ∀ n : ℕ, 0 ≤ (if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
    intro n
    split_ifs <;> positivity
  have hle : ∀ n : ℕ, (if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)
      ≤ ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    by_cases h1 : 1 ≤ n
    · by_cases h2 : p ∣ n
      · rw [if_pos ⟨h1, h2⟩]
        have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        have hkey : 1 * ((q : ℝ) ^ (n + 1))⁻¹ ≤ (n : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hcast (show (0 : ℝ) ≤ ((q : ℝ) ^ (n + 1))⁻¹ by positivity)
        rwa [one_mul] at hkey
      · rw [if_neg (fun h => h2 h.2)]
        positivity
    · rw [if_neg (fun h => h1 h.1)]
      positivity
  have hsum : Summable (fun n : ℕ => if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) :=
    Summable.of_nonneg_of_le hnonneg hle (summable_nat_mul_base_pow_neg q hq)
  have hterm : ∀ n : ℕ, ‖(if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)‖
      ≤ ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
    exact hle n
  have hnorm : Summable fun n : ℕ =>
      ‖(if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (summable_nat_mul_base_pow_neg q hq)
  -- the truncation at `n < p * M` is enough: it is a cofinal subsequence
  have htend1 : Filter.Tendsto (fun M : ℕ => Finset.range (p * M)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone
      (f := fun M : ℕ => Finset.range (p * M)) ?_ ?_
    · intro M N hMN
      have hMN' : p * M ≤ p * N := Nat.mul_le_mul_left p hMN
      intro x hx
      simp only [Finset.mem_range] at *
      omega
    · intro x
      have hx : x + 1 ≤ p * (x + 1) := Nat.le_mul_of_pos_left (x + 1) hp0
      exact ⟨x + 1, Finset.mem_range.mpr (by omega)⟩
  have hseq : ∀ M : ℕ,
      (∑ i ∈ Finset.range (p * M), (if 1 ≤ i ∧ p ∣ i then ((q : ℝ) ^ (i + 1))⁻¹ else 0) : ℝ)
        = ∑ k ∈ Finset.range M, (if 1 ≤ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
    intro M
    have hre := sum_multiples_reindex_gen p (p * M) hp (fun m => ((q : ℝ) ^ (m + 1))⁻¹)
    have hre' : ((∑ n ∈ Finset.range (p * M),
          (if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) : ℝ)
        = ∑ k ∈ Finset.range M, (if 1 ≤ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
      rw [hre]
      have hle' : M ≤ p * M := Nat.le_mul_of_pos_left M hp0
      have hM : Finset.range M ⊆ Finset.range (p * M) := by
        intro k hk
        simp only [Finset.mem_range] at *
        omega
      have hzero : ∀ k ∈ Finset.range (p * M), k ∉ Finset.range M →
          (if 1 ≤ k ∧ p * k < p * M then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0) = 0 := by
        intro k hk1 hk2
        simp only [Finset.mem_range] at hk1 hk2
        have hkn : M ≤ k := by omega
        have hnot : ¬(p * k < p * M) := by
          simp only [Nat.mul_lt_mul_left hp0]
          omega
        rw [if_neg (fun h => hnot h.2)]
      rw [← Finset.sum_subset
        (f := fun k => (if 1 ≤ k ∧ p * k < p * M then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0))
        hM hzero]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      simp only [Nat.mul_lt_mul_left hp0, hk, and_true]
    exact hre'
  have htend2 : Filter.Tendsto
      (fun M : ℕ => ∑ i ∈ Finset.range (p * M),
        (if 1 ≤ i ∧ p ∣ i then ((q : ℝ) ^ (i + 1))⁻¹ else 0))
      Filter.atTop (nhds ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹) := by
    refine (hasSum_lambert_geometric_base q p hq hp).tendsto_sum_nat.congr
      (f₂ := fun M : ℕ => ∑ i ∈ Finset.range (p * M),
        (if 1 ≤ i ∧ p ∣ i then ((q : ℝ) ^ (i + 1))⁻¹ else 0)) ?_
    exact fun M => (hseq M).symm
  exact hasSum_of_subseq_of_summable hnorm htend1 htend2

/-! ## 2. The Erdős series at an arbitrary base -/

/-- **The Erdős series at base `q`**: `S q = ∑' n, ω (n) / q ^ (n+1)`. -/
noncomputable def jsp87Base (q : ℕ) : ℝ :=
  ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹

/-- **At base `2` this is the Erdős series of JSP-000087.** -/
theorem jsp87Base_two : jsp87Base 2 = jsp87Series := rfl

/-- The base-`q` series is summable for `q ≥ 2`. -/
theorem summable_jsp87Base (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (fun n => ?_) (summable_nat_mul_base_pow_neg q hq)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (omega_le_self n)) (by positivity)

/-- The base-`q` series is nonnegative. -/
theorem jsp87Base_nonneg (q : ℕ) : 0 ≤ jsp87Base q :=
  tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-! ## 3. The Lambert reduction in every base -/

/-- The summand of the double sum `(n, p) ↦ q ^ -(n+1) · [p prime, 1 ≤ n, p ∣ n]`. -/
noncomputable def jsp87LamF (q : ℕ) (c : ℕ × ℕ) : ℝ :=
  if c.2.Prime ∧ 1 ≤ c.1 ∧ c.2 ∣ c.1 then ((q : ℝ) ^ (c.1 + 1))⁻¹ else 0

theorem jsp87LamF_nonneg (q : ℕ) (c : ℕ × ℕ) : 0 ≤ jsp87LamF q c := by
  unfold jsp87LamF
  split_ifs <;> positivity

/-- **The Lambert value of a single prime at base `q`.** -/
theorem hasSum_jsp87LamF_snd (q : ℕ) (hq : 2 ≤ q) (p : ℕ) :
    HasSum (fun n : ℕ => jsp87LamF q (n, p))
      (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0) := by
  by_cases hp : p.Prime
  · have h1p : 1 ≤ p := by
      have := hp.two_le
      omega
    have hfun : (fun n : ℕ => jsp87LamF q (n, p))
        = fun n => (if 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      funext n
      simp [jsp87LamF, hp]
    rw [hfun, if_pos hp]
    exact hasSum_multiples_base q p hq h1p
  · rw [if_neg hp]
    have hzero : (fun n : ℕ => jsp87LamF q (n, p)) = fun _ => (0 : ℝ) := by
      funext n
      simp [jsp87LamF, hp]
    rw [hzero]
    simpa using (Summable.zero : Summable (fun _ : ℕ => (0 : ℝ))).hasSum

/-- For each `n`, the prime-indexed row of the double sum is summable. -/
theorem summable_jsp87LamF_snd (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    Summable (fun p : ℕ => jsp87LamF q (n, p)) := by
  have hs : (fun p : ℕ => jsp87LamF q (n, p)).HasFiniteSupport := by
    refine Set.Finite.subset (Finset.finite_toSet (s := (Finset.range (n + 1) : Finset ℕ))) ?_
    intro p hp
    simp only [Function.mem_support] at hp
    by_cases hn0 : n = 0
    · simp [jsp87LamF, hn0] at hp
    · have hguard : p.Prime ∧ 1 ≤ n ∧ p ∣ n := by
        by_contra hcon
        simp [jsp87LamF, hcon] at hp
      have hle : p ≤ n := Nat.le_of_dvd (by omega) hguard.2.2
      exact Finset.mem_coe.2 (Finset.mem_range.mpr (by omega))
  exact summable_of_hasFiniteSupport hs

/-- For each `n`, summing over the primes gives the Erdős summand at base `q`. -/
theorem tsum_jsp87LamF_snd (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    (∑' p : ℕ, jsp87LamF q (n, p)) = ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
  have key : ∀ p ∉ Finset.range (n + 1), jsp87LamF q (n, p) = 0 := by
    intro p hp
    have hpn : n + 1 ≤ p := by simpa using hp
    by_cases hn0 : n = 0
    · simp [jsp87LamF, hn0]
    · have hnpos : 1 ≤ n := by omega
      have : ¬p ∣ n := by
        intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      simp [jsp87LamF, this]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) key]
  simp only [jsp87LamF]
  by_cases hn0 : n = 0
  · simp [hn0, omega_zero]
  · have hnpos : 1 ≤ n := by omega
    have hnlt : n < n + 1 := by omega
    have hmul := Finset.sum_mul (s := Finset.range (n + 1))
      (f := fun p => (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
      (a := ((q : ℝ) ^ (n + 1))⁻¹)
    have hsplit : (∑ p ∈ Finset.range (n + 1),
            (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) : ℝ)
        = (∑ p ∈ Finset.range (n + 1), (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
            * ((q : ℝ) ^ (n + 1))⁻¹ := by
      calc (∑ p ∈ Finset.range (n + 1),
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) : ℝ)
          = ∑ p ∈ Finset.range (n + 1),
              ((if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) * ((q : ℝ) ^ (n + 1))⁻¹) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            by_cases h : p.Prime ∧ 1 ≤ n ∧ p ∣ n <;> simp [h]
        _ = (∑ p ∈ Finset.range (n + 1), (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
            * ((q : ℝ) ^ (n + 1))⁻¹ := hmul.symm
    have hnat : (∑ p ∈ Finset.range (n + 1),
            (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℕ) else 0) : ℕ) = omega n := by
      simp only [hnpos, true_and]
      exact omega_eq_sum_indicator_dvd n (n + 1) hnpos hnlt
    have hcastR : (∑ p ∈ Finset.range (n + 1),
            (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) : ℝ) = ((omega n : ℕ) : ℝ) := by
      rw [sum_indicator_cast, hnat]
    rw [hsplit, hcastR]

/-- The double sum is summable at every base. -/
theorem summable_jsp87LamF (q : ℕ) (hq : 2 ≤ q) : Summable (jsp87LamF q) := by
  refine (summable_prod_of_nonneg (fun c => jsp87LamF_nonneg q c)).2
    ⟨fun n => summable_jsp87LamF_snd q hq n, ?_⟩
  have h1 : (fun n : ℕ => ∑' p : ℕ, jsp87LamF q (n, p))
      = fun n => ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ :=
    funext (tsum_jsp87LamF_snd q hq)
  rw [h1]
  exact summable_jsp87Base q hq

/-- **The double sum telescopes to the Erdős series at base `q`.** -/
theorem tsum_jsp87LamF_eq_base (q : ℕ) (hq : 2 ≤ q) :
    (∑' c : ℕ × ℕ, jsp87LamF q c) = jsp87Base q := by
  rw [(summable_jsp87LamF q hq).tsum_prod]
  rw [tsum_congr fun n => tsum_jsp87LamF_snd q hq n]
  rfl

/-- **THE LAMBERT REDUCTION IN EVERY BASE.**
`S q = ∑' p prime, 1 / (q ^ (p+1) - q)`. -/
theorem jsp87_lambert_base (q : ℕ) (hq : 2 ≤ q) :
    jsp87Base q = ∑' p : ℕ, (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0) := by
  have hswap : (∑' (c : ℕ × ℕ), jsp87LamF q c) = ∑' p : ℕ, ∑' n : ℕ, jsp87LamF q (n, p) := by
    rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) (jsp87LamF q)]
    simpa [Function.swap] using ((summable_jsp87LamF q hq).prod_symm).tsum_prod
  rw [← tsum_jsp87LamF_eq_base q hq, hswap]
  refine tsum_congr fun p => (hasSum_jsp87LamF_snd q hq p).tsum_eq

/-- **Rescaling a Lambert term.** -/
theorem lambert_scale (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    (q : ℝ) * ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ = ((q : ℝ) ^ p - 1)⁻¹ := by
  have hp1 : (q : ℝ) ^ (p + 1) - (q : ℝ) = (q : ℝ) * ((q : ℝ) ^ p - 1) := by
    rw [pow_succ]
    ring
  rw [hp1]
  have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
  have hB : ((q : ℝ) ^ p - 1) ≠ 0 := q_pow_sub_one_ne q hq hp
  have hA : (q : ℝ) * ((q : ℝ) ^ p - 1) ≠ 0 := mul_ne_zero hq0 hB
  field_simp

/-- **A Lambert term in the `p+1` form, rescaled.** -/
theorem lambert_term_scale (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ = (q : ℝ)⁻¹ * ((q : ℝ) ^ p - 1)⁻¹ := by
  have hp1 : (q : ℝ) ^ (p + 1) - (q : ℝ) = (q : ℝ) * ((q : ℝ) ^ p - 1) := by
    rw [pow_succ]
    ring
  rw [hp1]
  have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
  have hB : ((q : ℝ) ^ p - 1) ≠ 0 := q_pow_sub_one_ne q hq hp
  have hA : (q : ℝ) * ((q : ℝ) ^ p - 1) ≠ 0 := mul_ne_zero hq0 hB
  field_simp

/-- The geometric series `∑' n, q ^ (-n)` is summable for `q ≥ 2`. -/
theorem summable_base_geom (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => (q : ℝ)⁻¹ ^ n) := by
  refine summable_geometric_of_norm_lt_one ?_
  have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1 < q by omega))

/-- **A Lambert term is at most `2 / q ^ p`.** -/
theorem lambert_term_le_two (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    ((q : ℝ) ^ p - 1)⁻¹ ≤ 2 * ((q : ℝ)⁻¹ ^ p) := by
  have hA : (0 : ℝ) < (q : ℝ) ^ p - 1 := by
    have := q_pow_gt_one q hq hp
    linarith
  have hB : (0 : ℝ) < (q : ℝ) ^ p := by positivity
  have hx2 : (2 : ℝ) ≤ (q : ℝ) ^ p := by
    have h2 := cast_two_pow_le q hq p
    have h1' : 2 ≤ (2 : ℝ) ^ p := by
      have hh := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (show (1 : ℕ) ≤ p from hp)
      nlinarith
    linarith
  have hkey : (1 : ℝ) / ((q : ℝ) ^ p - 1) ≤ 2 / (q : ℝ) ^ p := by
    rw [div_le_div_iff₀ hA hB]
    linarith
  have heq1 : ((q : ℝ) ^ p - 1)⁻¹ = (1 : ℝ) / ((q : ℝ) ^ p - 1) := by
    rw [inv_eq_one_div]
  have heq2 : 2 * ((q : ℝ)⁻¹ ^ p) = 2 / (q : ℝ) ^ p := by
    rw [inv_pow, div_eq_mul_inv]
  rw [← heq1, ← heq2] at hkey
  exact hkey

/-- **The classical Lambert form in every base:**
`∑' p prime, 1 / (q ^ p - 1) = q · S q`. -/
theorem jsp87_lambert_base_classic (q : ℕ) (hq : 2 ≤ q) :
    (∑' p : ℕ, (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0)) = (q : ℝ) * jsp87Base q := by
  have hpt : ∀ p : ℕ, (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0)
      = (q : ℝ) * (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · have hp2 : 1 ≤ p := by
        have := hp.two_le
        omega
      rw [if_pos hp, if_pos hp, lambert_scale q p hq hp2]
    · simp [hp]
  have hM : Summable (fun p : ℕ => 2 * ((q : ℝ)⁻¹ ^ (p + 1))) := by
    have h0 := summable_base_geom q hq
    have hfun : (fun p : ℕ => 2 * ((q : ℝ)⁻¹ ^ (p + 1)))
        = fun p => (2 * (q : ℝ)⁻¹) * (q : ℝ)⁻¹ ^ p := by
      funext p
      rw [show (q : ℝ)⁻¹ ^ (p + 1) = (q : ℝ)⁻¹ ^ p * (q : ℝ)⁻¹ by rw [pow_succ]]
      ring
    rw [hfun]
    exact h0.mul_left (2 * (q : ℝ)⁻¹)
  have hsA : Summable (fun p : ℕ => (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0)) := by
    have h0 : ∀ p : ℕ, 0 ≤ (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0) := by
      intro p
      by_cases hp : p.Prime
      · rw [if_pos hp]
        have hp2 : 1 ≤ p := by
          have := hp.two_le
          omega
        have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
        have hq1 : (0 : ℝ) < (q : ℝ) ^ p - 1 := by linarith [q_pow_gt_one q hq (p := p) hp2]
        have hkey : (q : ℝ) ^ (p + 1) - (q : ℝ) = (q : ℝ) * ((q : ℝ) ^ p - 1) := by
          rw [pow_succ]
          ring
        rw [hkey]
        exact (inv_pos.mpr (mul_pos hqpos hq1)).le
      · rw [if_neg hp]
    have h1 : ∀ p : ℕ, (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0)
        ≤ 2 * ((q : ℝ)⁻¹ ^ (p + 1)) := by
      intro p
      by_cases hp : p.Prime
      · rw [if_pos hp]
        have hp2 : 1 ≤ p := by
          have := hp.two_le
          omega
        have hle := lambert_term_le_two q p hq hp2
        calc ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ = (q : ℝ)⁻¹ * ((q : ℝ) ^ p - 1)⁻¹ :=
              lambert_term_scale q p hq hp2
          _ ≤ (q : ℝ)⁻¹ * (2 * ((q : ℝ)⁻¹ ^ p)) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ = 2 * ((q : ℝ)⁻¹ ^ (p + 1)) := by rw [pow_succ]; ring
      · rw [if_neg hp]
        positivity
    exact Summable.of_nonneg_of_le h0 h1 hM
  have hstep1 : (∑' p : ℕ, (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0))
      = ∑' p : ℕ, (q : ℝ) * (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0) :=
    tsum_congr fun p => hpt p
  have hstep2 : ∑' p : ℕ, (q : ℝ) * (if p.Prime then ((q : ℝ) ^ (p + 1) - (q : ℝ))⁻¹ else 0)
      = (q : ℝ) * jsp87Base q := by
    rw [Summable.tsum_mul_left _ hsA, jsp87_lambert_base q hq]
  rw [hstep1, hstep2]

/-- The classical Lambert series over the primes is summable at every base. -/
theorem summable_lambert_base (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun p : ℕ => (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0)) := by
  have h0 : ∀ p : ℕ, 0 ≤ (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      have hp2 : 1 ≤ p := by
        have := hp.two_le
        omega
      exact (inv_pos.mpr (by linarith [q_pow_gt_one q hq hp2])).le
    · rw [if_neg hp]
  have h1 : ∀ p : ℕ, (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0)
      ≤ 2 * ((q : ℝ)⁻¹ ^ p) := by
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      have hp2 : 1 ≤ p := by
        have := hp.two_le
        omega
      exact lambert_term_le_two q p hq hp2
    · simp [hp]
  exact Summable.of_nonneg_of_le h0 h1 ((summable_base_geom q hq).mul_left 2)

/-! ## 4. A sharp uniform bound for the whole family -/

/-- **For `3 ≤ p` the Lambert term is at most `(8/7) / q ^ p`.** -/
theorem lambert_term_le (q p : ℕ) (hq : 2 ≤ q) (hp : 3 ≤ p) :
    ((q : ℝ) ^ p - 1)⁻¹ ≤ (8 / 7 : ℝ) * ((q : ℝ) ^ p)⁻¹ := by
  have h8 : (8 : ℝ) ≤ (q : ℝ) ^ p := cast_eight_le_q_pow q hq hp
  have hA : (0 : ℝ) < (q : ℝ) ^ p - 1 := by
    have := q_pow_gt_one q hq (p := p) (by omega)
    linarith
  have hB : (0 : ℝ) < (q : ℝ) ^ p := by positivity
  have hkey : (1 : ℝ) / ((q : ℝ) ^ p - 1) ≤ (8 / 7 : ℝ) / (q : ℝ) ^ p := by
    rw [div_le_div_iff₀ hA hB]
    linarith
  have heq1 : (1 : ℝ) / ((q : ℝ) ^ p - 1) = ((q : ℝ) ^ p - 1)⁻¹ := by
    rw [inv_eq_one_div]
  have heq3 : (8 / 7 : ℝ) / (q : ℝ) ^ p = (8 / 7 : ℝ) * ((q : ℝ) ^ p)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [heq1, heq3] at hkey
  exact hkey

/-- **For `4 ≤ p` the Lambert term is *strictly* less than `(8/7) / q ^ p`** (the
equality case of `lambert_term_le` is `q = 2, p = 3` only). -/
theorem lambert_term_lt (q p : ℕ) (hq : 2 ≤ q) (hp : 4 ≤ p) :
    ((q : ℝ) ^ p - 1)⁻¹ < (8 / 7 : ℝ) * ((q : ℝ) ^ p)⁻¹ := by
  have hA : (0 : ℝ) < (q : ℝ) ^ p - 1 := by
    have := q_pow_gt_one q hq (p := p) (by omega)
    linarith
  have hB : (0 : ℝ) < (q : ℝ) ^ p := by positivity
  have h9 : (8 : ℝ) < (q : ℝ) ^ p := by
    have h1 := cast_two_pow_le q hq p
    have h4 : (2 : ℝ) ^ 4 = 16 := by norm_num
    have h3 : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ p :=
      pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (show (4 : ℕ) ≤ p from hp)
    linarith
  have hkey : (1 : ℝ) / ((q : ℝ) ^ p - 1) < (8 / 7 : ℝ) / (q : ℝ) ^ p := by
    rw [div_lt_div_iff₀ hA hB]
    linarith
  have heq1 : (1 : ℝ) / ((q : ℝ) ^ p - 1) = ((q : ℝ) ^ p - 1)⁻¹ := by
    rw [inv_eq_one_div]
  have heq3 : (8 / 7 : ℝ) / (q : ℝ) ^ p = (8 / 7 : ℝ) * ((q : ℝ) ^ p)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [heq1, heq3] at hkey
  exact hkey

/-- **The odd-place geometric sum at base `q`:**
`∑' n, [n odd] / q ^ (n+1) = 1/(q² - q) - 1/(q³ - q)`. -/
theorem sum_odd_base (q : ℕ) (hq : 2 ≤ q) :
    (∑' n : ℕ, (if Odd n then ((q : ℝ) ^ (n + 1))⁻¹ else 0))
      = ((q : ℝ)^2 - (q : ℝ))⁻¹ - ((q : ℝ)^3 - (q : ℝ))⁻¹ := by
  have hA : Summable (fun n : ℕ => (if 1 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    have h := (hasSum_lambert_geometric_base q 1 hq (by omega)).summable
    refine h.congr fun n => ?_
    have he : (if 1 ≤ n then ((q : ℝ) ^ (1 * n + 1))⁻¹ else 0)
        = (if 1 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      by_cases hn : 1 ≤ n <;> simp [hn]
    exact he
  have hB : Summable (fun n : ℕ => (if 1 ≤ n ∧ 2 ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) :=
    (hasSum_multiples_base q 2 hq (by omega)).summable
  have hsub := Summable.tsum_sub hA hB
  have hpt : ∀ n : ℕ, (if 1 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)
      - (if 1 ≤ n ∧ 2 ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)
      = (if Odd n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
    intro n
    rcases Nat.even_or_odd n with he | ho
    · rcases he with ⟨k, rfl⟩
      rcases Nat.eq_zero_or_pos k with hz | hk'
      · subst hz
        simp
      · have h2 : 2 ∣ (k + k) := by exact ⟨k, by ring⟩
        have h1 : 1 ≤ k + k := by omega
        simp [h1, h2]
    · rcases ho with ⟨k, rfl⟩
      have h1 : 1 ≤ 2 * k + 1 := by omega
      have h2 : ¬ (2 ∣ 2 * k + 1) := by
        rintro ⟨a, ha⟩
        omega
      simp [h1, h2]
  rw [tsum_congr fun n => hpt n] at hsub
  have hA' : (∑' k : ℕ, (if 1 ≤ k then ((q : ℝ) ^ (k + 1))⁻¹ else 0))
      = ((q : ℝ)^2 - (q : ℝ))⁻¹ := by
    have hh := (hasSum_lambert_geometric_base q 1 hq (by omega)).tsum_eq
    simpa only [Nat.one_mul] using hh
  have hB' : (∑' k : ℕ, (if 1 ≤ k ∧ 2 ∣ k then ((q : ℝ) ^ (k + 1))⁻¹ else 0))
      = ((q : ℝ)^3 - (q : ℝ))⁻¹ := (hasSum_multiples_base q 2 hq (by omega)).tsum_eq
  rw [hA', hB'] at hsub
  exact hsub

/-- **The odd places `≥ 3` at base `q`.** -/
theorem sum_odd_ge_three_base (q : ℕ) (hq : 2 ≤ q) :
    (∑' n : ℕ, (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0))
      = ((q : ℝ)^2 - (q : ℝ))⁻¹ - ((q : ℝ)^3 - (q : ℝ))⁻¹ - ((q : ℝ)^2)⁻¹ := by
  have hO : Summable (fun n : ℕ => (if Odd n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    have h0 : ∀ n : ℕ, 0 ≤ (if Odd n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      intro n
      by_cases ho : Odd n
      · rw [if_pos ho]
        positivity
      · rw [if_neg ho]
    have h1 : ∀ n : ℕ, (if Odd n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)
        ≤ ((q : ℝ) ^ (n + 1))⁻¹ := by
      intro n
      by_cases ho : Odd n
      · rw [if_pos ho]
      · rw [if_neg ho]
        positivity
    exact Summable.of_nonneg_of_le h0 h1 (summable_base_pow_negK q hq 1)
  have hs : Summable (fun n : ℕ => (if n = 1 then ((q : ℝ)^2)⁻¹ else 0)) :=
    summable_ite_eq ((q : ℝ)^2)⁻¹ 1
  have hsub := Summable.tsum_sub hO hs
  have hpt : ∀ n : ℕ, (if Odd n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)
      - (if n = 1 then ((q : ℝ)^2)⁻¹ else 0)
      = (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
    intro n
    by_cases h1 : n = 1
    · simp [h1]
    · by_cases ho : Odd n
      · have h3 : 3 ≤ n := by
          rcases ho with ⟨k, hk⟩
          omega
        simp [h1, ho, h3]
      · simp [h1, ho]
  rw [tsum_congr fun n => hpt n] at hsub
  rw [tsum_ite_eq] at hsub
  rw [sum_odd_base q hq] at hsub
  linarith

/-- **THE LAMBERT SERIES OVER THE PRIMES, SPLIT OFF AT `p = 2`.** -/
theorem jsp87_lambert_base_split_two (q : ℕ) (hq : 2 ≤ q) :
    (∑' p : ℕ, (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0))
      = ((q : ℝ)^2 - 1)⁻¹
        + (∑' p : ℕ, (if Odd p ∧ 3 ≤ p ∧ p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0)) := by
  have hL := summable_lambert_base q hq
  have hR := summable_ite_eq ((q : ℝ)^2 - 1)⁻¹ 2
  have hsub := Summable.tsum_sub hL hR
  rw [tsum_ite_eq] at hsub
  have hpt : ∀ p : ℕ, (if p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0)
      - (if p = 2 then ((q : ℝ)^2 - 1)⁻¹ else 0)
      = (if Odd p ∧ 3 ≤ p ∧ p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p
    by_cases hp2 : p = 2
    · have hp2' : (2 : ℕ).Prime := by norm_num
      simp [hp2, hp2']
    · by_cases hp : p.Prime
      · have hodd : Odd p := prime_ne_two_odd hp hp2
        have hp3 : 3 ≤ p := by
          have h2le : 2 ≤ p := hp.two_le
          omega
        simp [hp2, hp, hodd, hp3]
      · have hn : ¬ (Odd p ∧ 3 ≤ p ∧ p.Prime) := fun h => hp h.2.2
        simp [hp2, hp, hn]
  rw [tsum_congr fun p => hpt p] at hsub
  linarith

/-- **A SHARP UNIFORM BOUND FOR THE WHOLE FAMILY.**
`q · S q < 1/(q²-1) + (8/7) · q · (1/(q²-q) - 1/(q³-q) - 1/q²)`. -/
theorem jsp87_lambert_base_lt (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) * jsp87Base q
      < ((q : ℝ)^2 - 1)⁻¹
        + (8 / 7 : ℝ) * (q : ℝ) * (((q : ℝ)^2 - (q : ℝ))⁻¹ - ((q : ℝ)^3 - (q : ℝ))⁻¹
          - ((q : ℝ)^2)⁻¹) := by
  have hsplit := jsp87_lambert_base_split_two q hq
  rw [(jsp87_lambert_base_classic q hq)] at hsplit
  have hguard : Summable (fun n : ℕ => (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    have h0 : ∀ n : ℕ, 0 ≤ (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      intro n
      by_cases h : Odd n ∧ 3 ≤ n
      · rw [if_pos h]
        positivity
      · rw [if_neg h]
    have h1 : ∀ n : ℕ, (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)
        ≤ ((q : ℝ) ^ (n + 1))⁻¹ := by
      intro n
      by_cases h : Odd n ∧ 3 ≤ n
      · rw [if_pos h]
      · rw [if_neg h]
        positivity
    exact Summable.of_nonneg_of_le h0 h1 (summable_base_pow_negK q hq 1)
  have hM : Summable (fun n : ℕ => (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_base_pow_negK q hq 1).mul_left ((8 / 7 : ℝ) * (q : ℝ)))
    exact le_of_eq (by ring)
  have hstep : (∑' n : ℕ,
        (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0))
      = ∑' n : ℕ, ((8 / 7 : ℝ) * (q : ℝ))
          * (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
    refine tsum_congr fun n => ?_
    by_cases h : Odd n ∧ 3 ≤ n
    · rw [if_pos h, if_pos h] <;> ring
    · rw [if_neg h, if_neg h] <;> ring
  have hlt : (∑' n : ℕ,
        (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0))
      = (8 / 7 : ℝ) * (q : ℝ)
        * (∑' n : ℕ, (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    calc _ = ∑' n : ℕ, ((8 / 7 : ℝ) * (q : ℝ))
            * (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := hstep
      _ = ((8 / 7 : ℝ) * (q : ℝ))
          * (∑' n : ℕ, (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) :=
        Summable.tsum_mul_left _ hguard
  have hf : Summable (fun n : ℕ =>
      (if Odd n ∧ 3 ≤ n ∧ n.Prime then ((q : ℝ) ^ n - 1)⁻¹ else 0)) := by
    have h0 : ∀ n : ℕ, 0 ≤ (if Odd n ∧ 3 ≤ n ∧ n.Prime then ((q : ℝ) ^ n - 1)⁻¹ else 0) := by
      intro n
      by_cases h : Odd n ∧ 3 ≤ n ∧ n.Prime
      · rw [if_pos h]
        have := q_pow_gt_one q hq (p := n) (by omega)
        exact (inv_pos.mpr (by linarith)).le
      · rw [if_neg h]
    have h1 : ∀ n : ℕ, (if Odd n ∧ 3 ≤ n ∧ n.Prime then ((q : ℝ) ^ n - 1)⁻¹ else 0)
        ≤ (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
      intro n
      by_cases h : Odd n ∧ 3 ≤ n ∧ n.Prime
      · rw [if_pos h]
        have hle := lambert_term_le q n hq h.2.1
        calc ((q : ℝ) ^ n - 1)⁻¹ ≤ (8 / 7 : ℝ) * ((q : ℝ) ^ n)⁻¹ := hle
          _ = (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
            have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
            field_simp
            rw [pow_succ]
      · rw [if_neg h]
        positivity
    exact Summable.of_nonneg_of_le h0 h1 hM
  have hg : Summable (fun n : ℕ =>
      (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    have h0 : ∀ n : ℕ,
        0 ≤ (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      intro n
      by_cases h : Odd n ∧ 3 ≤ n
      · rw [if_pos h]
        positivity
      · rw [if_neg h]
    have h1 : ∀ n : ℕ,
        (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)
        ≤ (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
      intro n
      by_cases h : Odd n ∧ 3 ≤ n
      · rw [if_pos h]
      · rw [if_neg h]
        positivity
    exact Summable.of_nonneg_of_le h0 h1 hM
  have hpt : ∀ n : ℕ,
      (if Odd n ∧ 3 ≤ n ∧ n.Prime then ((q : ℝ) ^ n - 1)⁻¹ else 0)
      ≤ (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
    intro n
    by_cases h : Odd n ∧ 3 ≤ n ∧ n.Prime
    · rw [if_pos h, if_pos ⟨h.1, h.2.1⟩]
      have hle := lambert_term_le q n hq h.2.1
      calc ((q : ℝ) ^ n - 1)⁻¹ ≤ (8 / 7 : ℝ) * ((q : ℝ) ^ n)⁻¹ := hle
        _ = (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
          have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
          field_simp
          rw [pow_succ]
    · rw [if_neg h]
      by_cases h2 : Odd n ∧ 3 ≤ n
      · rw [if_pos h2] <;> positivity
      · rw [if_neg h2] <;> positivity
  have hpt5 : (if Odd 5 ∧ 3 ≤ 5 ∧ (5 : ℕ).Prime then ((q : ℝ) ^ 5 - 1)⁻¹ else 0)
      < (if Odd 5 ∧ 3 ≤ 5 then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (5 + 1))⁻¹ else 0) := by
    have hp5 : (5 : ℕ).Prime := by norm_num
    rw [if_pos ⟨by norm_num, by norm_num, hp5⟩, if_pos ⟨by norm_num, by norm_num⟩]
    have hlt5 := lambert_term_lt q 5 hq (by norm_num)
    calc ((q : ℝ) ^ 5 - 1)⁻¹ < (8 / 7 : ℝ) * ((q : ℝ) ^ 5)⁻¹ := hlt5
      _ = (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (5 + 1))⁻¹ := by
        have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
        field_simp
  have htailA : (∑' p : ℕ, (if Odd p ∧ 3 ≤ p ∧ p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0))
      < ∑' n : ℕ, (if Odd n ∧ 3 ≤ n then (8 / 7 : ℝ) * (q : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) :=
    Summable.tsum_lt_tsum hpt hpt5 hf hg
  have htailB : (∑' p : ℕ, (if Odd p ∧ 3 ≤ p ∧ p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0))
      < (8 / 7 : ℝ) * (q : ℝ)
          * (∑' n : ℕ, (if Odd n ∧ 3 ≤ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    rwa [hlt] at htailA
  have hodd := sum_odd_ge_three_base q hq
  have htailC : (∑' p : ℕ, (if Odd p ∧ 3 ≤ p ∧ p.Prime then ((q : ℝ) ^ p - 1)⁻¹ else 0))
      < (8 / 7 : ℝ) * (q : ℝ)
        * (((q : ℝ)^2 - (q : ℝ))⁻¹ - ((q : ℝ)^3 - (q : ℝ))⁻¹ - ((q : ℝ)^2)⁻¹) := by
    rwa [hodd] at htailB
  linarith [hsplit, htailC]

/-- **THE FIRST SHARP BOUND ON THE SERIES: `jsp87Series < 11 / 42`.**
Round 37 only knew `jsp87Series ≤ 1`. -/
theorem jsp87Series_lt_11_42 : jsp87Series < 11 / 42 := by
  rw [← jsp87Base_two]
  have h := jsp87_lambert_base_lt 2 (by omega)
  norm_num at h ⊢
  linarith

/-- `jsp87Series < 1 / 3`, a strict form of round 37's `≤ 1`. -/
theorem jsp87Series_lt_one_third : jsp87Series < 1 / 3 := by
  have h := jsp87Series_lt_11_42
  linarith

/-- **The two-sided bound `7 / 32 ≤ jsp87Series < 11 / 42`** — the interval of
round 37's `jsp87Series_bounds` sharpened from above by a factor of `4`. -/
theorem jsp87Series_bounds' : 7 / 32 ≤ jsp87Series ∧ jsp87Series < 11 / 42 :=
  ⟨jsp87Series_bounds.1, jsp87Series_lt_11_42⟩
/-! ## 5. The odd and even halves of the family, and the decimation data

Splitting `S q` by the parity of the place gives the *odd-index sub-series*
`jsp87Odd q` and the *even-index sub-series* `jsp87Even q`:

```
S q = jsp87Odd q + jsp87Even q                             (jsp87Series_split)
```

The even half is *again a Lambert double sum*, computed in every base
(`tsum_jsp87LamF_even_eq`), and for each prime `p` the even half of the
Lambert sum is available in closed form (`tsum_jsp87LamF_even_snd`): for
`p = 2` it is `1/(q³ - q)` and for an odd prime `p` it is `1/(q^(2p+1) - q)`.

The arithmetic core of the *decimation identity* — the relation between `S q`,
its even half, and the series at base `q ^ 2` — is `omega_two_mul`:

```
ω (2 n) = ω n + [n odd]
```

which yields (reindexing the even places, `2 j ↦ j`)

```
jsp87Even q = q · jsp87Base (q ^ 2)
              + q · ( 1/(q⁴ - q²) - 1/(q⁶ - q²) )                (open)
```

and hence `S q = jsp87Odd q + q · S (q ^ 2) + q/(q⁴ - q)`.  The only missing
ingredient is the **even-index reindexing of a `tsum`**
(`∑' n, [2 ∣ n] f n = ∑' j, f (2 j)` for nonnegative `f`); that is left as the
next attack, and no part of the identity above is claimed here. -/

/-- **The odd-index sub-series of the Erdős series at base `q`.** -/
noncomputable def jsp87Odd (q : ℕ) : ℝ :=
  ∑' n : ℕ, (if Odd n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)

/-- **The even-index sub-series of the Erdős series at base `q`.** -/
noncomputable def jsp87Even (q : ℕ) : ℝ :=
  ∑' n : ℕ, (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)

theorem jsp87Odd_nonneg (q : ℕ) : 0 ≤ jsp87Odd q :=
  tsum_nonneg fun n => by
    by_cases h : Odd n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]

theorem jsp87Even_nonneg (q : ℕ) : 0 ≤ jsp87Even q :=
  tsum_nonneg fun n => by
    by_cases h : 2 ∣ n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]

/-- The summand of the double sum restricted to the **even** places. -/
noncomputable def jsp87LamF_even (q : ℕ) (c : ℕ × ℕ) : ℝ :=
  if 2 ∣ c.1 ∧ 1 ≤ c.1 then jsp87LamF q c else 0

theorem jsp87LamF_even_nonneg (q : ℕ) (c : ℕ × ℕ) : 0 ≤ jsp87LamF_even q c := by
  by_cases h : 2 ∣ c.1 ∧ 1 ≤ c.1
  · rw [jsp87LamF_even, if_pos h]
    exact jsp87LamF_nonneg q c
  · rw [jsp87LamF_even, if_neg h]

/-- The even-place row is the ordinary row restricted to the even places. -/
theorem jsp87LamF_even_eq (q : ℕ) (c : ℕ × ℕ) :
    jsp87LamF_even q c = (if 2 ∣ c.1 ∧ 1 ≤ c.1 then jsp87LamF q c else 0) := rfl

/-- **The Lambert value at the even places, for a fixed prime `p`.** -/
theorem tsum_jsp87LamF_even_snd (q : ℕ) (hq : 2 ≤ q) (p : ℕ) :
    (∑' n : ℕ, jsp87LamF_even q (n, p))
      = (if p.Prime then
        (if p = 2 then ((q : ℝ)^3 - (q : ℝ))⁻¹ else ((q : ℝ) ^ (2 * p + 1) - (q : ℝ))⁻¹)
      else 0) := by
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · rw [if_pos hp, if_pos hp2]
      subst hp2
      have hpt : ∀ n : ℕ, jsp87LamF_even q (n, 2)
          = (if 1 ≤ n ∧ 2 ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
        intro n
        by_cases hb : 2 ∣ n
        · by_cases h1n : 1 ≤ n
          · have hA : 2 ∣ n ∧ 1 ≤ n ∧ (2 : ℕ).Prime ∧ 1 ≤ n ∧ 2 ∣ n := ⟨hb, h1n, hp, h1n, hb⟩
            have hB : 1 ≤ n ∧ 2 ∣ n := ⟨h1n, hb⟩
            simp [jsp87LamF_even, jsp87LamF, hA, hB]
          · have hC : ¬ (2 ∣ n ∧ 1 ≤ n) := by simp [hb, h1n]
            have hB : ¬ (1 ≤ n ∧ 2 ∣ n) := by simp [hb, h1n]
            simp only [jsp87LamF_even, Prod.fst, Prod.snd, if_neg hC, if_neg hB]
        · have hC : ¬ (2 ∣ n ∧ 1 ≤ n) := by simp [hb]
          have hB : ¬ (1 ≤ n ∧ 2 ∣ n) := by simp [hb]
          simp only [jsp87LamF_even, Prod.fst, Prod.snd, if_neg hC, if_neg hB]
      rw [tsum_congr fun n => hpt n]
      exact (hasSum_multiples_base q 2 hq (by omega)).tsum_eq
    · rw [if_pos hp, if_neg hp2]
      have hp2le : 2 ≤ p := hp.two_le
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes (by norm_num) hp).2 (by omega)
      have hpt : ∀ n : ℕ, jsp87LamF_even q (n, p)
          = (if 1 ≤ n ∧ 2 * p ∣ n then ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
        intro n
        by_cases hb : 2 ∣ n
        · by_cases h1n : 1 ≤ n
          · by_cases hpd : p ∣ n
            · have hA : 2 ∣ n ∧ 1 ≤ n ∧ p.Prime ∧ 1 ≤ n ∧ p ∣ n := ⟨hb, h1n, hp, h1n, hpd⟩
              have hB : 1 ≤ n ∧ 2 * p ∣ n :=
                ⟨h1n, Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hb hpd⟩
              simp [jsp87LamF_even, jsp87LamF, hA, hB]
            · have hC : 2 ∣ n ∧ 1 ≤ n := ⟨hb, h1n⟩
              have hA : ¬ (p.Prime ∧ 1 ≤ n ∧ p ∣ n) := by
                rintro ⟨_, _, h⟩
                exact hpd h
              have hB : ¬ (1 ≤ n ∧ 2 * p ∣ n) := by
                rintro ⟨_, h⟩
                obtain ⟨k, hk⟩ := h
                exact hpd ⟨2 * k, by simpa [mul_comm, mul_left_comm, mul_assoc] using hk⟩
              simp only [jsp87LamF_even, jsp87LamF, Prod.fst, Prod.snd, if_pos hC, if_neg hA,
                if_neg hB]
          · have hC : ¬ (2 ∣ n ∧ 1 ≤ n) := fun h => h1n h.2
            have hB : ¬ (1 ≤ n ∧ 2 * p ∣ n) := fun h => h1n h.1
            simp only [jsp87LamF_even, Prod.fst, Prod.snd, if_neg hC, if_neg hB]
        · have hC : ¬ (2 ∣ n ∧ 1 ≤ n) := fun h => hb h.1
          have hB : ¬ (1 ≤ n ∧ 2 * p ∣ n) := by
            rintro ⟨_, h⟩
            obtain ⟨k, hk⟩ := h
            exact hb ⟨p * k, by simpa [mul_assoc] using hk⟩
          simp only [jsp87LamF_even, Prod.fst, Prod.snd, if_neg hC, if_neg hB]
      rw [tsum_congr fun n => hpt n]
      exact (hasSum_multiples_base q (2 * p) hq (by omega)).tsum_eq
  · rw [if_neg hp]
    have hzero : (fun n : ℕ => jsp87LamF_even q (n, p)) = fun _ => (0 : ℝ) := by
      funext n
      simp [jsp87LamF_even, jsp87LamF, hp]
    rw [hzero]
    simp

/-- For each `p`, the even-place row is summable. -/
theorem summable_jsp87LamF_even_snd (q : ℕ) (hq : 2 ≤ q) (p : ℕ) :
    Summable (fun n : ℕ => jsp87LamF_even q (n, p)) := by
  have h0 : ∀ n : ℕ, 0 ≤ (if 2 ∣ n ∧ 1 ≤ n then jsp87LamF q (n, p) else 0) := by
    intro n
    by_cases h : 2 ∣ n ∧ 1 ≤ n
    · rw [if_pos h]
      exact jsp87LamF_nonneg q (n, p)
    · rw [if_neg h]
  have h1 : ∀ n : ℕ, (if 2 ∣ n ∧ 1 ≤ n then jsp87LamF q (n, p) else 0)
      ≤ jsp87LamF q (n, p) := by
    intro n
    by_cases h : 2 ∣ n ∧ 1 ≤ n
    · rw [if_pos h]
    · rw [if_neg h]
      exact jsp87LamF_nonneg q (n, p)
  have hs := (hasSum_jsp87LamF_snd q hq p).summable
  exact Summable.of_nonneg_of_le h0 h1 hs

/-- For each `n`, summing the even-place row over `p` picks out the even places. -/
theorem tsum_jsp87LamF_even_fst (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    (∑' p : ℕ, jsp87LamF_even q (n, p))
      = (if 2 ∣ n ∧ 1 ≤ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
  have hc : (fun p : ℕ => jsp87LamF_even q (n, p))
      = fun p => (if 2 ∣ n ∧ 1 ≤ n then jsp87LamF q (n, p) else 0) := by
    funext p
    exact jsp87LamF_even_eq q (n, p)
  rw [hc]
  by_cases h : 2 ∣ n ∧ 1 ≤ n
  · simp only [if_pos h, tsum_jsp87LamF_snd q hq n]
  · simp only [if_neg h]
    simp

/-- For each `n`, the prime-indexed even-place row is summable. -/
theorem summable_jsp87LamF_even_fst (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    Summable (fun p : ℕ => jsp87LamF_even q (n, p)) := by
  have hc : (fun p : ℕ => jsp87LamF_even q (n, p))
      = fun p => (if 2 ∣ n ∧ 1 ≤ n then jsp87LamF q (n, p) else 0) := by
    funext p
    exact jsp87LamF_even_eq q (n, p)
  rw [hc]
  have h0 : ∀ p : ℕ, 0 ≤ (if 2 ∣ n ∧ 1 ≤ n then jsp87LamF q (n, p) else 0) := by
    intro p
    by_cases h : 2 ∣ n ∧ 1 ≤ n
    · rw [if_pos h]
      exact jsp87LamF_nonneg q (n, p)
    · rw [if_neg h]
  have h1 : ∀ p : ℕ, (if 2 ∣ n ∧ 1 ≤ n then jsp87LamF q (n, p) else 0)
      ≤ jsp87LamF q (n, p) := by
    intro p
    by_cases h : 2 ∣ n ∧ 1 ≤ n
    · rw [if_pos h]
    · rw [if_neg h]
      exact jsp87LamF_nonneg q (n, p)
  exact Summable.of_nonneg_of_le h0 h1 (summable_jsp87LamF_snd q hq n)

/-- **The even sub-series is summable at every base.** -/
theorem summable_jsp87Even (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_jsp87Base q hq)
  · by_cases h2 : 2 ∣ n
    · rw [if_pos h2]
      positivity
    · rw [if_neg h2]
  · by_cases h2 : 2 ∣ n
    · rw [if_pos h2]
    · rw [if_neg h2]
      positivity

/-- **THE EVEN-PLACE DOUBLE SUM IS THE EVEN-INDEX SUB-SERIES:**
`∑' (n, p), [2 ∣ n] / q^(n+1) = ∑' n, [2 ∣ n] ω n / q^(n+1)`,
i.e. the even part of the Erdős series is again a Lambert-type double sum. -/
theorem tsum_jsp87LamF_even_eq (q : ℕ) (hq : 2 ≤ q) :
    (∑' c : ℕ × ℕ, jsp87LamF_even q c) = jsp87Even q := by
  have hsnd : ∀ n : ℕ, Summable (fun p : ℕ => jsp87LamF_even q (n, p)) :=
    fun n => summable_jsp87LamF_even_fst q hq n
  have hprod : Summable (jsp87LamF_even q) := by
    refine (summable_prod_of_nonneg (fun c => jsp87LamF_even_nonneg q c)).2 ⟨hsnd, ?_⟩
    have h1 : (fun n : ℕ => ∑' p : ℕ, jsp87LamF_even q (n, p))
        = fun n => (if 2 ∣ n ∧ 1 ≤ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) :=
      funext (tsum_jsp87LamF_even_fst q hq)
    rw [h1]
    have h1' : (fun n : ℕ => (if 2 ∣ n ∧ 1 ≤ n
        then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0))
        = fun n => (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      funext n
      by_cases h2 : 2 ∣ n
      · by_cases h1n : 1 ≤ n
        · have hA : 2 ∣ n ∧ 1 ≤ n := ⟨h2, h1n⟩
          simp only [if_pos hA, if_pos h2]
        · have hn0 : n = 0 := by omega
          have hA : ¬ (2 ∣ n ∧ 1 ≤ n) := fun h => h1n h.2
          simp only [if_neg hA, if_pos h2]
          simp [hn0, omega_zero]
      · have hA : ¬ (2 ∣ n ∧ 1 ≤ n) := fun h => h2 h.1
        simp only [if_neg hA, if_neg h2]
    rw [h1']
    exact summable_jsp87Even q hq
  rw [hprod.tsum_prod]
  have h2 : (∑' n : ℕ, ∑' p : ℕ, jsp87LamF_even q (n, p))
      = ∑' n : ℕ, (if 2 ∣ n ∧ 1 ≤ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) :=
    tsum_congr fun n => tsum_jsp87LamF_even_fst q hq n
  rw [h2]
  have h3 : (∑' n : ℕ, (if 2 ∣ n ∧ 1 ≤ n
        then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0))
      = ∑' n : ℕ, (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
    have hpt : ∀ n : ℕ,
        (if 2 ∣ n ∧ 1 ≤ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)
        = (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0) := by
      intro n
      by_cases h2 : 2 ∣ n
      · by_cases h1n : 1 ≤ n
        · have hA : 2 ∣ n ∧ 1 ≤ n := ⟨h2, h1n⟩
          simp only [if_pos hA, if_pos h2]
        · have hn0 : n = 0 := by omega
          have hA : ¬ (2 ∣ n ∧ 1 ≤ n) := fun h => h1n h.2
          simp only [if_neg hA, if_pos h2]
          simp [hn0, omega_zero]
      · have hA : ¬ (2 ∣ n ∧ 1 ≤ n) := fun h => h2 h.1
        simp only [if_neg hA, if_neg h2]
    rw [tsum_congr fun n => hpt n]
  rw [h3]
  rfl

/-- **THE ERDŐS SERIES SPLITS INTO ITS ODD AND EVEN PARTS.** -/
theorem jsp87Series_split (q : ℕ) (hq : 2 ≤ q) :
    jsp87Base q = jsp87Odd q + jsp87Even q := by
  have hO : Summable (fun n : ℕ => (if Odd n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_jsp87Base q hq)
    · by_cases h3 : Odd n
      · rw [if_pos h3]
        positivity
      · rw [if_neg h3]
    · by_cases h3 : Odd n
      · rw [if_pos h3]
      · rw [if_neg h3]
        positivity
  have hE := summable_jsp87Even q hq
  have hsub := Summable.tsum_add hO hE
  have hpt : ∀ n : ℕ,
      (if Odd n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)
      + (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0)
      = ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    rcases Nat.even_or_odd n with h2 | h3
    · obtain ⟨k, hk⟩ := h2
      rw [hk]
      have hB : (2 : ℕ) ∣ k + k := ⟨k, by ring⟩
      have hA : ¬ Odd (k + k) := by rintro ⟨j, hj⟩; omega
      simp only [if_neg hA, if_pos hB, zero_add]
    · obtain ⟨k, hk⟩ := h3
      rw [hk]
      have hB : ¬ (2 ∣ 2 * k + 1) := by rintro ⟨j, hj⟩; omega
      have hA : Odd (2 * k + 1) := ⟨k, rfl⟩
      simp only [if_pos hA, if_neg hB, add_zero]
  rw [tsum_congr fun n => hpt n] at hsub
  simpa [jsp87Base, jsp87Odd, jsp87Even] using hsub

/-- **THE SPLIT AT THE BASE `2` SERIES OF JSP-000087.** -/
theorem jsp87Series_split_even_odd :
    jsp87Series = jsp87Odd 2 + jsp87Even 2 := jsp87Series_split 2 (by omega)

/-- **THE ARITHMETIC CORE OF THE DECIMATION:** `ω (2 n) = ω n + [n odd]`. -/
theorem omega_two_mul (n : ℕ) :
    omega (2 * n) = omega n + (if Odd n then (1 : ℕ) else 0) := by
  have h := omega_mul_eq_sum_indicator (m := 2) (n := n) (by omega : 2 ≠ 0)
  have h2 : omega 2 = 1 := by native_decide
  have hpf : (2 : ℕ).primeFactors = {2} := by native_decide
  have hsum : (∑ p ∈ (2 : ℕ).primeFactors, (if p ∣ n then (1 : ℕ) else 0))
      = (if 2 ∣ n then (1 : ℕ) else 0) := by
    rw [hpf, Finset.sum_singleton]
  rw [h2, hsum] at h
  rcases Nat.even_or_odd n with hne | hno
  · obtain ⟨k, hk⟩ := hne
    have h2n : 2 ∣ n := by rw [hk]; exact ⟨k, by ring⟩
    have hnodd : ¬ Odd n := by
      rintro ⟨j, hj⟩
      rw [hk] at hj
      omega
    rw [if_neg hnodd]
    rw [if_pos h2n] at h
    omega
  · obtain ⟨k, hk⟩ := hno
    have hno2 : Odd n := ⟨k, hk⟩
    have h2n : ¬ (2 ∣ n) := by
      rw [hk]
      rintro ⟨j, hj⟩
      omega
    rw [if_pos hno2]
    rw [if_neg h2n] at h
    omega

/-- **A single term of a summable nonnegative series is a lower bound for it.** -/
theorem tsum_ge_term {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (a : ℕ) :
    f a ≤ ∑' n, f n := by
  have hfz : Summable (fun n => if n = a then (0 : ℝ) else f n) := by
    refine Summable.of_nonneg_of_le (f := f) (g := fun n => if n = a then (0 : ℝ) else f n)
      (fun n => ?_) (fun n => ?_) hf
    · by_cases h : n = a
      · rw [if_pos h]
      · rw [if_neg h]
        exact h0 n
    · by_cases h : n = a
      · rw [if_pos h]
        exact h0 n
      · rw [if_neg h]
  have hsub := Summable.tsum_sub hf hfz
  have hpt : ∀ n : ℕ, f n - (if n = a then (0 : ℝ) else f n)
      = (if n = a then f n else 0) := by
    intro n
    by_cases h : n = a
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [tsum_congr fun n => hpt n] at hsub
  have hz : (fun n : ℕ => (if n = a then f n else 0))
      = fun n => (if n = a then f a else 0) := by
    funext n
    by_cases h : n = a <;> simp [h]
  rw [hz, tsum_ite_eq (f a) a] at hsub
  have hnonneg : 0 ≤ ∑' n, (if n = a then (0 : ℝ) else f n) :=
    tsum_nonneg (fun n => by
      by_cases h : n = a
      · rw [if_pos h]
      · rw [if_neg h]
        exact h0 n)
  linarith

/-- **The odd half of the series of JSP-000087 is at least `1 / 16`** (the place
`n = 3` alone contributes `ω 3 / 2 ^ 4 = 1 / 16`). -/
theorem jsp87Odd_two_ge : (1 / 16 : ℝ) ≤ jsp87Odd 2 := by
  have hs : Summable (fun n : ℕ =>
      (if Odd n then ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (g := fun n : ℕ => (if Odd n then ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ else 0))
      (fun n => ?_) (fun n => ?_) (summable_jsp87Base 2 (by omega))
    · by_cases h : Odd n
      · rw [if_pos h]
        positivity
      · rw [if_neg h]
    · by_cases h : Odd n
      · rw [if_pos h]
      · rw [if_neg h]
        positivity
  have h0 : ∀ n : ℕ, 0 ≤ (if Odd n then ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
    intro n
    by_cases h : Odd n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  have h := tsum_ge_term hs h0 3
  have h3 : Odd 3 := ⟨1, rfl⟩
  have hω3 : omega 3 = 1 := by native_decide
  unfold jsp87Odd
  rw [if_pos h3, hω3] at h
  norm_num at h
  exact h

/-- **The even half of the series of JSP-000087 is at least `1 / 8`** (the place
`n = 2` alone contributes `ω 2 / 2 ^ 3 = 1 / 8`). -/
theorem jsp87Even_two_ge : (1 / 8 : ℝ) ≤ jsp87Even 2 := by
  have hs := summable_jsp87Even 2 (by omega)
  have h0 : ∀ n : ℕ, 0 ≤ (if 2 ∣ n then ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
    intro n
    by_cases h : 2 ∣ n
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  have h := tsum_ge_term hs h0 2
  have h2 : (2 : ℕ) ∣ 2 := ⟨1, by norm_num⟩
  have hω2 : omega 2 = 1 := by native_decide
  unfold jsp87Even
  rw [if_pos h2, hω2] at h
  norm_num at h
  exact h

/-- **A RATIONALITY TRANSFER:** the odd half of JSP-000087 is the series minus a
rational, as soon as the even half is rational. -/
theorem jsp87Odd_two_sub (r : ℝ) (hr : jsp87Even 2 = r) : jsp87Odd 2 = jsp87Series - r := by
  have h := jsp87Series_split_even_odd
  rw [hr] at h
  linarith

end JSP87

