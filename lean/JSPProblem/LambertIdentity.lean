/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Main
import JSPProblem.LambertSeries
import Mathlib.Tactic

/-!
# JSP-000087 : the Lambert rearrangement of the Erdős series

Because `ω n = #{ p prime : p ∣ n }`, the generating series of `ω` is the
**prime-restricted Lambert series**

```
∑ n ≥ 0, ω(n) x^(n+1)  =  ∑ p prime, ∑ k ≥ 1, x^(p k + 1)
                        =  ∑ p prime, x^(p+1) / (1 - x ^ p)
```

and at `x = 1 / 2` this is `∑ p prime, 1 / (2 ^ (p+1) - 2)`, i.e. the classical
form `∑ n ≥ 1, ω(n) / 2 ^ n = ∑ p prime, 1 / (2 ^ p - 1)`.

`JSPProblem/LambertSeries.lean` proved the identity for a *finite truncation*.
This file lifts it to the infinite series.  The swap of the two indices of the
double sum is `Summable.tsum_prod` / `Summable.prod_symm`, the reindexing of the
multiples of a prime uses `sum_multiples_reindex` together with
`hasSum_of_subseq_of_summable` (a cofinal subsequence of partial sums), and the
inner geometric series is `hasSum_geometric_of_norm_lt_one`.

Main results:

* `hasSum_sub_zero` : dropping the `k = 0` term of a nonneg series;
* `hasSum_lambert_geometric` : `∑' k, (if 1 ≤ k then 2 ^ -(p k + 1) else 0)
  = 1 / (2 ^ (p+1) - 2)`;
* `hasSum_lamF_fst` : the multiples of a prime contribute exactly the Lambert
  term `1 / (2 ^ (p+1) - 2)`;
* `jsp87_lambert` : **`jsp87Series = ∑' p, (if p.Prime then 1 / (2 ^ (p+1) - 2)
  else 0)`** — the full Lambert reduction of Erdős' series;
* `jsp87_lambert_classic` : the classical form
  `∑' p, (if p.Prime then 1 / (2 ^ p - 1) else 0) = 2 * jsp87Series`.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-- The summand of the double sum `(n, p) ↦ 2 ^ -(n+1) · [p prime, 1 ≤ n, p ∣ n]`. -/
noncomputable def lamF (c : ℕ × ℕ) : ℝ :=
  if c.2.Prime ∧ 1 ≤ c.1 ∧ c.2 ∣ c.1 then ((2 : ℝ) ^ (c.1 + 1))⁻¹ else 0

theorem lamF_nonneg (c : ℕ × ℕ) : 0 ≤ lamF c := by
  unfold lamF
  split_ifs <;> positivity

/-- **Dropping the zeroth term of a nonnegative series.** -/
theorem hasSum_sub_zero {f : ℕ → ℝ} (hpos : ∀ k, 0 ≤ f k) (hf : Summable f) :
    HasSum (fun k : ℕ => if 1 ≤ k then f k else 0) ((∑' k, f k) - f 0) := by
  have hgle : ∀ k, (if 1 ≤ k then f k else 0) ≤ f k := by
    intro k
    by_cases h : 1 ≤ k
    · simp only [if_pos h]
      exact le_rfl
    · simp only [if_neg h]
      exact hpos k
  have hgn : ∀ k, 0 ≤ (if 1 ≤ k then f k else 0) := by
    intro k
    by_cases h : 1 ≤ k
    · simp only [if_pos h]
      exact hpos k
    · simp only [if_neg h]
      exact le_rfl
  have hg : Summable (fun k : ℕ => if 1 ≤ k then f k else 0) :=
    Summable.of_nonneg_of_le hgn hgle hf
  have hzero : (∑' k, (f k - (if 1 ≤ k then f k else 0))) = f 0 := by
    rw [tsum_eq_sum (s := ({0} : Finset ℕ)) (fun b hb => by
      have hb0 : b ≠ 0 := by simpa using hb
      have h1 : 1 ≤ b := by omega
      simp only [if_pos h1, sub_self])
      ]
    simp
  have hsub := Summable.tsum_sub hf hg
  rw [hzero] at hsub
  have key : (∑' k, (if 1 ≤ k then f k else 0)) = (∑' k, f k) - f 0 := by
    linarith [hsub]
  rw [← key]
  exact hg.hasSum

/-- **The Lambert value of a single prime.**

For `1 ≤ p`, the geometric tail of the positive multiples of `p` is
`1 / (2 ^ (p+1) - 2)`. -/
theorem hasSum_lambert_geometric (p : ℕ) (hp : 1 ≤ p) :
    HasSum (fun k : ℕ => (if 1 ≤ k then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0))
      ((2 : ℝ) ^ (p + 1) - 2)⁻¹ := by
  have h2p : 1 < (2 : ℝ) ^ p := by
    have htwo : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
      calc (2 : ℝ) ^ p = (2 : ℝ) ^ ((p - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (p - 1) * 2 := pow_succ _ _
        _ = 2 * 2 ^ (p - 1) := by ring
    have h1 : (1 : ℝ) ≤ 2 ^ (p - 1) := by
      rw [← pow_one (2 : ℝ)]
      exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
    rw [htwo]
    nlinarith
  -- the geometric series with ratio `(2 ^ p)⁻¹`
  have hξ : ‖((2 : ℝ) ^ p)⁻¹‖ < 1 := by
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ p)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact inv_lt_one_of_one_lt₀ h2p
  have hgeom : HasSum (fun k : ℕ => ((2 : ℝ) ^ p)⁻¹ ^ k)
      (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (ξ := ((2 : ℝ) ^ p)⁻¹) hξ
  have hmul : ∀ k : ℕ, (2 : ℝ)⁻¹ * ((2 : ℝ) ^ p)⁻¹ ^ k
      = ((2 : ℝ) ^ (p * k + 1))⁻¹ := by
    intro k
    calc (2 : ℝ)⁻¹ * ((2 : ℝ) ^ p)⁻¹ ^ k = (2 : ℝ)⁻¹ * ((2 : ℝ) ^ (p * k))⁻¹ := by rw [inv_pow, pow_mul]
      _ = ((2 : ℝ) ^ (p * k) * (2 : ℝ) ^ 1)⁻¹ := by rw [pow_one, ← DivisionMonoid.mul_inv_rev]
      _ = ((2 : ℝ) ^ (p * k + 1))⁻¹ := by rw [pow_succ]; ring
  have hsum0 : Summable (fun k : ℕ => ((2 : ℝ) ^ (p * k + 1))⁻¹) := by
    have h := hgeom.mul_left (2 : ℝ)⁻¹
    refine (HasSum.summable h).congr fun k => ?_
    exact hmul k
  have hts0 : (∑' k : ℕ, ((2 : ℝ) ^ (p * k + 1))⁻¹)
      = (2 : ℝ)⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ := by
    calc (∑' k : ℕ, ((2 : ℝ) ^ (p * k + 1))⁻¹)
        = ∑' k : ℕ, (2 : ℝ)⁻¹ * ((2 : ℝ) ^ p)⁻¹ ^ k := tsum_congr fun k => (hmul k).symm
      _ = (2 : ℝ)⁻¹ * ∑' k : ℕ, ((2 : ℝ) ^ p)⁻¹ ^ k :=
        Summable.tsum_mul_left _ (HasSum.summable hgeom)
      _ = (2 : ℝ)⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ := by rw [hgeom.tsum_eq]
  have hgeo0 : HasSum (fun k : ℕ => ((2 : ℝ) ^ (p * k + 1))⁻¹)
      ((2 : ℝ)⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹) := by
    have h := hsum0.hasSum
    rwa [hts0] at h
  -- drop the `k = 0` term
  have hsubts : (∑' k : ℕ, (if 1 ≤ k then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0))
      = (2 : ℝ)⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ - 2⁻¹ := by
    have h := (hasSum_sub_zero (f := fun k : ℕ => ((2 : ℝ) ^ (p * k + 1))⁻¹)
      (fun k => by positivity) (HasSum.summable hgeo0)).tsum_eq
    rw [hgeo0.tsum_eq] at h
    have hf0 : ((2 : ℝ) ^ (p * 0 + 1))⁻¹ = (2 : ℝ)⁻¹ := by norm_num
    rw [hf0] at h
    exact h
  have hsub : Summable (fun k : ℕ =>
      (if 1 ≤ k then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0)) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs <;> positivity)
      (fun k => by
        by_cases h1 : 1 ≤ k
        · rw [if_pos h1]
        · rw [if_neg h1]
          positivity)
      hsum0
  have hfin : HasSum (fun k : ℕ => (if 1 ≤ k then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0))
      ((2 : ℝ)⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ - 2⁻¹) :=
    (Summable.hasSum_iff hsub).mpr hsubts
  -- the closed form
  have h2p' : (2 : ℝ) ^ p - 1 ≠ 0 := by nlinarith
  have h2p1 : (2 : ℝ) ^ (p + 1) - 2 ≠ 0 := by
    have h2p1' : (2 : ℝ) ^ (p + 1) = (2 : ℝ) ^ p * 2 := by rw [pow_succ]
    rw [h2p1']
    intro h
    nlinarith [h2p]
  convert hfin using 1
  field_simp
  ring

/-- **The multiples of a prime `p` contribute exactly the Lambert term.** -/
theorem hasSum_lamF_fst (p : ℕ) :
    HasSum (fun n : ℕ => lamF (n, p))
      (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0) := by
  by_cases hp : p.Prime
  · have hp0 : 0 < p := hp.pos
    have h1p : 1 ≤ p := by omega
    have hfun : (fun n : ℕ => lamF (n, p))
        = fun n => (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
      funext n
      simp [lamF, hp]
    rw [hfun, if_pos hp]
    have hnonneg : ∀ n : ℕ, 0 ≤ (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
      intro n
      split_ifs <;> positivity
    have hle : ∀ n : ℕ, (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)
        ≤ ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      intro n
      by_cases h1 : 1 ≤ n
      · by_cases h2 : p ∣ n
        · rw [if_pos ⟨h1, h2⟩]
          have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
          have hkey : 1 * ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (n : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
            mul_le_mul_of_nonneg_right hcast
              (show (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹ by positivity)
          rwa [one_mul] at hkey
        · rw [if_neg (fun h => h2 h.2)]
          positivity
      · rw [if_neg (fun h => h1 h.1)]
        positivity
    have hsum : Summable (fun n : ℕ => if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) :=
      Summable.of_nonneg_of_le hnonneg hle summable_nat_mul_two_pow_neg
    have hterm : ∀ n : ℕ, ‖(if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)‖
        ≤ ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
      exact hle n
    have hnorm : Summable fun n : ℕ =>
        ‖(if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm summable_nat_mul_two_pow_neg
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
        (∑ i ∈ Finset.range (p * M), (if 1 ≤ i ∧ p ∣ i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0) : ℝ)
          = ∑ k ∈ Finset.range M, (if 1 ≤ k then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
      intro M
      have hre := sum_multiples_reindex p (p * M) hp (fun m => ((2 : ℝ) ^ (m + 1))⁻¹)
      have hre' : ((∑ n ∈ Finset.range (p * M),
            (if 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) : ℝ)
          = ∑ k ∈ Finset.range M, (if 1 ≤ k then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
        rw [hre]
        have hle' : M ≤ p * M := Nat.le_mul_of_pos_left M hp0
        have hM : Finset.range M ⊆ Finset.range (p * M) := by
          intro k hk
          simp only [Finset.mem_range] at *
          omega
        have hzero : ∀ k ∈ Finset.range (p * M), k ∉ Finset.range M →
            (if 1 ≤ k ∧ p * k < p * M then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0) = 0 := by
          intro k hk1 hk2
          simp only [Finset.mem_range] at hk1 hk2
          have hkn : M ≤ k := by omega
          have hnot : ¬(p * k < p * M) := by
            simp only [Nat.mul_lt_mul_left hp0]
            omega
          rw [if_neg (fun h => hnot h.2)]
        rw [← Finset.sum_subset
          (f := fun k => (if 1 ≤ k ∧ p * k < p * M then ((2 : ℝ) ^ (p * k + 1))⁻¹ else 0))
          hM hzero]
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_range] at hk
        simp only [Nat.mul_lt_mul_left hp0, hk, and_true]
      exact hre'
    have htend2 : Filter.Tendsto
        (fun M : ℕ => ∑ i ∈ Finset.range (p * M),
          (if 1 ≤ i ∧ p ∣ i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0))
        Filter.atTop (nhds ((2 : ℝ) ^ (p + 1) - 2)⁻¹) := by
      refine (hasSum_lambert_geometric p h1p).tendsto_sum_nat.congr
        (f₂ := fun M : ℕ => ∑ i ∈ Finset.range (p * M),
          (if 1 ≤ i ∧ p ∣ i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0)) ?_
      exact fun M => (hseq M).symm
    exact hasSum_of_subseq_of_summable hnorm htend1 htend2
  · rw [if_neg hp]
    have hzero : (fun n : ℕ => lamF (n, p)) = fun _ => (0 : ℝ) := by
      funext n
      simp [lamF, hp]
    rw [hzero]
    simpa using (Summable.zero : Summable (fun _ : ℕ => (0 : ℝ))).hasSum

/-- For each `n`, summing `lamF` over the primes gives the Erdős summand. -/
theorem tsum_lamF_snd (n : ℕ) : (∑' p : ℕ, lamF (n, p)) = jsp87Term n := by
  have key : ∀ p ∉ Finset.range (n + 1), lamF (n, p) = 0 := by
    intro p hp
    have hpn : n + 1 ≤ p := by simpa using hp
    by_cases hn0 : n = 0
    · simp [lamF, hn0]
    · have hnpos : 1 ≤ n := by omega
      have hle : p ≤ n → (p : ℕ) ≤ n := id
      have : ¬p ∣ n := by
        intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      simp [lamF, this]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) key]
  simp only [lamF]
  by_cases hn0 : n = 0
  · simp [lamF, hn0, jsp87Term, omega_zero]
  · have hnpos : 1 ≤ n := by omega
    have hnlt : n < n + 1 := by omega
    have hmul := Finset.sum_mul (s := Finset.range (n + 1))
      (f := fun p => (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
      (a := ((2 : ℝ) ^ (n + 1))⁻¹)
    have hsplit : (∑ p ∈ Finset.range (n + 1),
            (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) : ℝ)
        = (∑ p ∈ Finset.range (n + 1), (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0))
            * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      calc (∑ p ∈ Finset.range (n + 1),
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) : ℝ)
          = ∑ p ∈ Finset.range (n + 1),
              ((if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            by_cases h : p.Prime ∧ 1 ≤ n ∧ p ∣ n <;> simp [h]
        _ = (∑ p ∈ Finset.range (n + 1),
              (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0)) * ((2 : ℝ) ^ (n + 1))⁻¹ := hmul.symm
    have hn1 : 1 ≤ n := by omega
    have hnat : (∑ p ∈ Finset.range (n + 1), (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℕ) else 0) : ℕ)
        = omega n := by
      simp only [hn1, true_and]
      exact omega_eq_sum_indicator_dvd n (n + 1) hnpos hnlt
    have hcast : ((∑ p ∈ Finset.range (n + 1), (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℕ) else 0)
          : ℕ) : ℝ) = ((omega n : ℕ) : ℝ) := by rw [hnat]
    have hcastR : (∑ p ∈ Finset.range (n + 1),
            (if p.Prime ∧ 1 ≤ n ∧ p ∣ n then (1 : ℝ) else 0) : ℝ) = ((omega n : ℕ) : ℝ) := by
      rw [sum_indicator_cast, hnat]
    rw [hsplit, hcastR]
    simp [jsp87Term]

/-- The double sum is summable. -/
theorem summable_lamF : Summable lamF := by
  refine (summable_prod_of_nonneg lamF_nonneg).2 ⟨?_, ?_⟩
  · intro n
    have hs : (fun p : ℕ => lamF (n, p)).HasFiniteSupport := by
      refine Set.Finite.subset (Finset.finite_toSet (s := (Finset.range (n + 1) : Finset ℕ))) ?_
      intro p hp
      simp only [Function.mem_support] at hp
      by_cases hn0 : n = 0
      · simp [lamF, hn0] at hp
      · have hguard : p.Prime ∧ 1 ≤ n ∧ p ∣ n := by
          by_contra hcon
          simp [lamF, hcon] at hp
        have hle : p ≤ n := Nat.le_of_dvd (by omega) hguard.2.2
        exact Finset.mem_coe.2 (Finset.mem_range.mpr (by omega))
    exact summable_of_hasFiniteSupport hs
  · have h1 : (fun n : ℕ => ∑' p : ℕ, lamF (n, p)) = jsp87Term := funext tsum_lamF_snd
    rw [h1]
    show Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
    exact summable_omega_mul_inv_two_pow

/-- **The double sum telescopes to the Erdős series.** -/
theorem tsum_lamF_eq_jsp87Series : (∑' c : ℕ × ℕ, lamF c) = jsp87Series := by
  rw [summable_lamF.tsum_prod]
  rw [tsum_congr fun n => tsum_lamF_snd n]
  rfl

/-- **THE LAMBERT REDUCTION (sub-step B of the ACCEPTANCE blocker list).**
`jsp87Series = ∑' p, (if p.Prime then 1 / (2 ^ (p+1) - 2) else 0)`. -/
theorem jsp87_lambert :
    jsp87Series = ∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0) := by
  have hswap : (∑' (c : ℕ × ℕ), lamF c) = ∑' p : ℕ, ∑' n : ℕ, lamF (n, p) := by
    rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) lamF]
    simpa [Function.swap] using (summable_lamF.prod_symm).tsum_prod
  rw [← tsum_lamF_eq_jsp87Series, hswap]
  refine tsum_congr fun p => (hasSum_lamF_fst p).tsum_eq

/-- **`1 < 2 ^ p` whenever `2 ≤ p`.** -/
theorem two_pow_gt_one (hp : 2 ≤ p) : 1 < (2 : ℝ) ^ p := by
  have htwo : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
    calc (2 : ℝ) ^ p = (2 : ℝ) ^ ((p - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (p - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (p - 1) := by ring
  have h1 : (1 : ℝ) ≤ 2 ^ (p - 1) := by
    rw [← pow_one (2 : ℝ)]
    exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  rw [htwo]
  nlinarith

/-- **`2 ≤ 2 ^ p` whenever `1 ≤ p`.** -/
theorem two_pow_ge_two (hp : 1 ≤ p) : 2 ≤ (2 : ℝ) ^ p := by
  have htwo : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
    calc (2 : ℝ) ^ p = (2 : ℝ) ^ ((p - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (p - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (p - 1) := by ring
  have h1 : (1 : ℝ) ≤ 2 ^ (p - 1) := by
    rw [← pow_one (2 : ℝ)]
    exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  rw [htwo]
  nlinarith

/-- **`2 ^ (p - 1) ≤ 2 ^ p - 1` whenever `1 ≤ p`.** -/
theorem two_pow_succ_le (hp : 1 ≤ p) : (2 : ℝ) ^ (p - 1) ≤ (2 : ℝ) ^ p - 1 := by
  have htwo : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
    calc (2 : ℝ) ^ p = (2 : ℝ) ^ ((p - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (p - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (p - 1) := by ring
  have h1 : (1 : ℝ) ≤ 2 ^ (p - 1) := by
    rw [← pow_one (2 : ℝ)]
    exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  rw [htwo]
  nlinarith

/-- **The classical form of the Lambert reduction:**
`∑' p prime, 1 / (2 ^ p - 1) = 2 * jsp87Series`, i.e.
`∑ n ≥ 1, ω(n) / 2 ^ n = ∑ p prime, 1 / (2 ^ p - 1)`. -/
theorem jsp87_lambert_classic :
    (∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0)) = 2 * jsp87Series := by
  have hnonneg : ∀ p : ℕ, 0 ≤ (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      have h2ple : 2 ≤ p := hp.two_le
      have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by nlinarith [two_pow_gt_one h2ple]
      exact (inv_pos.mpr hpos).le
    · rw [if_neg hp]
  have hle : ∀ p : ℕ, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) ≤ 2 * (2 : ℝ)⁻¹ ^ p := by
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp]
      have h2ple : 2 ≤ p := hp.two_le
      have h1p : 1 ≤ p := by omega
      have hposA : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by nlinarith [two_pow_gt_one h2ple]
      have hposB : (0 : ℝ) < (2 : ℝ) ^ (p - 1) := by positivity
      have hR : 2 * ((2 : ℝ) ^ p)⁻¹ = ((2 : ℝ) ^ (p - 1))⁻¹ := by
        have h2p' : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
          calc (2 : ℝ) ^ p = (2 : ℝ) ^ ((p - 1) + 1) := by congr 1 <;> omega
            _ = 2 ^ (p - 1) * 2 := pow_succ _ _
        rw [h2p']
        field_simp
      rw [inv_pow, hR]
      exact (inv_le_inv₀ hposA hposB).mpr (two_pow_succ_le h1p)
    · simp [hp]
  have hs : Summable (fun p : ℕ => (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0)) :=
    Summable.of_nonneg_of_le hnonneg hle
      (Summable.mul_left 2 (summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)))
  have hkey : ∀ p : ℕ,
      (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0)
        = 2 * (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · simp only [hp, ↓reduceIte]
      have h2ple : 2 ≤ p := hp.two_le
      have h2p' : (2 : ℝ) ^ p - 1 ≠ 0 := by nlinarith [two_pow_gt_one h2ple]
      have h2p1 : (2 : ℝ) ^ (p + 1) - 2 ≠ 0 := by
        have hgt : 1 < (2 : ℝ) ^ p := two_pow_gt_one h2ple
        have htwo : (2 : ℝ) ^ (p + 1) = (2 : ℝ) ^ p * 2 := by rw [pow_succ]
        rw [htwo]
        intro hh
        nlinarith
      field_simp
      rw [pow_succ]
      ring
    · simp only [hp, ↓reduceIte]
      rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst p
        norm_num
      · have h1p : 1 ≤ p := by omega
        have hne : (2 : ℝ) ^ (p + 1) - 2 ≠ 0 := by
          have htwo : (2 : ℝ) ^ (p + 1) = (2 : ℝ) ^ p * 2 := by rw [pow_succ]
          rw [htwo]
          intro hh
          have h1 : 2 ≤ (2 : ℝ) ^ p := two_pow_ge_two h1p
          linarith
        field_simp
        ring
  have hLambert : Summable (fun p : ℕ => (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le
      (g := fun p : ℕ => (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0))
      (f := fun p : ℕ => 2 * (2 : ℝ)⁻¹ ^ p) ?_ ?_ ?_
    · intro p
      by_cases hp : p.Prime
      · rw [if_pos hp]
        have h2ple : 2 ≤ p := hp.two_le
        have hge : 2 ≤ (2 : ℝ) ^ p := two_pow_ge_two (by omega)
        have hkey : (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (p + 1) - 2 := by
          have htwo : (2 : ℝ) ^ (p + 1) = (2 : ℝ) ^ p * 2 := by rw [pow_succ]
          rw [htwo]
          linarith
        have hpos : 0 < (2 : ℝ) ^ (p + 1) - 2 := by nlinarith
        exact (inv_pos.mpr hpos).le
      · rw [if_neg hp]
    · intro p
      by_cases hp : p.Prime
      · rw [if_pos hp, inv_pow]
        have h2ple : 2 ≤ p := hp.two_le
        have hge : 2 ≤ (2 : ℝ) ^ p := two_pow_ge_two (by omega)
        have hkey : (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (p + 1) - 2 := by
          have htwo : (2 : ℝ) ^ (p + 1) = (2 : ℝ) ^ p * 2 := by rw [pow_succ]
          rw [htwo]
          linarith
        have hposA : (0 : ℝ) < (2 : ℝ) ^ (p + 1) - 2 := by nlinarith
        have hposB : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
        have hmul : ((2 : ℝ) ^ p)⁻¹ ≤ 2 * ((2 : ℝ) ^ p)⁻¹ := by
          have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 by norm_num) (le_of_lt hposB)
          simpa using h
        exact ((inv_le_inv₀ hposA hposB).mpr hkey).trans hmul
      · rw [if_neg hp]
        exact mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (by positivity)
    · exact (Summable.mul_left 2
        (summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)))
  calc (∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = ∑' p : ℕ, (2 * (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0)) :=
        tsum_congr fun p => hkey p
    _ = 2 * ∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ (p + 1) - 2)⁻¹ else 0) :=
      Summable.tsum_mul_left (2 : ℝ) hLambert
    _ = 2 * jsp87Series := by rw [jsp87_lambert]

/-- **THE CLASSICAL LAMBERT IDENTITY of JSP-000087, in the exact form of the
catalog statement:**

```
∑' n, ω(n) / 2 ^ n  =  ∑' p prime, 1 / (2 ^ p - 1).
```

This is the reduction from which Erdős (1948) and Pratt (arXiv:2409.15185) start;
the Erdős series of JSP-000087 is *half* of the left-hand side by definition. -/
theorem jsp87_lambert_reduction :
    (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹)
      = ∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  have h : HasSum (fun n : ℕ => 2 * ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (2 * jsp87Series) := by
    simpa [jsp87Series, mul_assoc] using (jsp87_convergence.mul_left 2)
  rw [← (jsp87_lambert_classic).symm]
  rw [tsum_congr (f := fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹)
      (g := fun n : ℕ => 2 * ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (fun n => by
        have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
        field_simp
        ring)]
  exact h.tsum_eq

end JSP87
