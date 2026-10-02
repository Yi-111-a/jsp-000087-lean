/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.BaseFamily
import JSPProblem.Periodicity
import JSPProblem.ResidueCarry
import Mathlib.Tactic

/-!
# JSP-000087 : the **stride decomposition** of the Erdős series

This module attacks the Erdős series `S = ∑' n, ω (n) 2 ^ -(n+1)` from a
direction **no earlier round had taken**: the decomposition of the series by the
**residue class of the summation index**, together with the exact self-similarity
that the dilation `n ↦ p * n` produces.

The single arithmetic observation is

```
ω (p * m) = ω m + 1 - [p ∣ m]                                (omega_mul_prime)
```

i.e. *multiplying by a prime adds exactly one new prime factor, unless that
prime is already present*.  Since `{p * k}` is the set of indices of the stride
`p`, this converts the `p`-divisible part of the series into **the same series at
the coarser base `q ^ p`, up to a rational**.

### What this does *not* give

It does not close the gap.  The blocker is unchanged: the aperiodicity of the
binary digits of `jsp87Series` (`jsp87_digit_not_eventuallyPeriodic`), i.e. the
arithmetic content of the uniform prime-`k`-tuples hypothesis in Pratt's
published result (arXiv:2409.15185).
-/

namespace JSP87

open Filter

set_option maxHeartbeats 1000000

/-! ## 0. Reindexing a nonnegative series over the multiples of `p`

The whole module rests on one piece of machinery: a nonnegative series can be
restricted to the multiples of any `p ≥ 1` and reindexed by `n = p * k`.  The
truncation at `n < p * M` is a cofinal subsequence of the partial sums, and the
finite reindexing is the `sum_multiples_reindex_gen` of `BaseFamily`. -/

/-- **REINDEXING OVER THE MULTIPLES.**  For `f ≥ 0` summable and `p ≥ 1`,

`∑' n, [p ∣ n] f n = ∑' k, f (p * k)`.

Note that `0` divides `0`, so the index `n = 0` is matched on both sides and no
hypothesis on `f 0` is needed. -/
theorem hasSum_stride_gen {f : ℕ → ℝ} {p : ℕ} (hp : 1 ≤ p) (hf : ∀ n, 0 ≤ f n)
    (hsum : Summable f) :
    HasSum (fun n : ℕ => (if p ∣ n then f n else 0)) (∑' k : ℕ, f (p * k)) := by
  have hp0 : 0 < p := by omega
  have hnonneg : ∀ n : ℕ, 0 ≤ (if p ∣ n then f n else 0) := by
    intro n
    split_ifs <;> first | exact hf n | positivity
  have hle : ∀ n : ℕ, (if p ∣ n then f n else 0) ≤ f n := by
    intro n
    by_cases h : p ∣ n
    · rw [if_pos h]
    · rw [if_neg h]
      exact hf _
  have hsub : Summable (fun n : ℕ => (if p ∣ n then f n else 0)) :=
    Summable.of_nonneg_of_le hnonneg hle hsum
  have hterm : ∀ n : ℕ, ‖(if p ∣ n then f n else 0)‖ ≤ f n := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
    exact hle n
  have hnorm : Summable (fun n : ℕ => ‖(if p ∣ n then f n else 0)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum
  have htend1 : Filter.Tendsto (fun M : ℕ => p * M) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun M hM =>
      (show b ≤ p * M from le_trans hM (Nat.le_mul_of_pos_left M hp0))⟩
  have htend1F : Filter.Tendsto (fun M : ℕ => Finset.range (p * M))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_finset_of_monotone (fun _ _ h => by
      have : p * _ ≤ p * _ := Nat.mul_le_mul_left p h
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega) (fun x => ⟨x + 1, by
        have : x + 1 ≤ p * (x + 1) := Nat.le_mul_of_pos_left (x + 1) hp0
        simp only [Finset.mem_range]; omega⟩)
  have hseq : ∀ M : ℕ,
      (∑ i ∈ Finset.range (p * M), (if p ∣ i then f i else 0) : ℝ)
        = ∑ k ∈ Finset.range M, f (p * k) := by
    intro M
    have hleft : (∑ i ∈ Finset.range (p * M), (if p ∣ i then f i else 0) : ℝ)
        = ∑ i ∈ (Finset.range (p * M)).filter (fun n => p ∣ n), f i := by
      rw [Finset.sum_filter]
    have hmem : ∀ k ∈ Finset.range M, p * k
        ∈ (Finset.range (p * M)).filter (fun n => p ∣ n) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨Nat.mul_lt_mul_of_pos_left hk hp0, dvd_mul_of_dvd_left (dvd_refl p) k⟩
    have hinj : ∀ a ∈ Finset.range M, ∀ b ∈ Finset.range M, p * a = p * b → a = b := by
      intro a _ b _ hab
      exact Nat.mul_left_cancel hp0 hab
    have hsurj : ∀ b : ℕ, b ∈ (Finset.range (p * M)).filter (fun n => p ∣ n) →
        ∃ a : ℕ, ∃ (_ : a ∈ Finset.range M), p * a = b := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨hmN, hm1⟩ := hm
      obtain ⟨k, hk⟩ := exists_eq_mul_left_of_dvd hm1
      have hmpk : p * k = m := (Nat.mul_comm k p).symm.trans hk.symm
      refine ⟨k, ⟨?_, hmpk⟩⟩
      refine Finset.mem_range.mpr ?_
      have hlt : p * k < p * M := by rw [hmpk]; exact hmN
      exact (Nat.mul_lt_mul_left hp0).mp hlt
    have hright : (∑ k ∈ Finset.range M, f (p * k) : ℝ)
        = ∑ i ∈ (Finset.range (p * M)).filter (fun n => p ∣ n), f i := by
      rw [Finset.sum_bij (fun k (_ : k ∈ Finset.range M) => p * k) hmem hinj hsurj
        (fun _ _ => rfl)]
    rw [hleft, hright]
  have htendA : Filter.Tendsto
      (fun M : ℕ => ∑ i ∈ Finset.range (p * M), (if p ∣ i then f i else 0))
      Filter.atTop (nhds (∑' n : ℕ, (if p ∣ n then f n else 0))) :=
    (hsub.hasSum.tendsto_sum_nat).comp htend1
  have htend2 : Filter.Tendsto
      (fun M : ℕ => ∑ i ∈ Finset.range (p * M), (if p ∣ i then f i else 0))
      Filter.atTop (nhds (∑' k : ℕ, f (p * k))) := by
    have hHS : HasSum (fun k : ℕ => f (p * k)) (∑' n : ℕ, (if p ∣ n then f n else 0)) := by
      refine (hasSum_iff_tendsto_nat_of_nonneg (fun k => hf _) _).mpr ?_
      exact htendA.congr (fun M => hseq M)
    have h3 := hHS.tendsto_sum_nat.congr (fun M => (hseq M).symm)
    rw [← hHS.tsum_eq] at h3
    exact h3
  exact hasSum_of_subseq_of_summable hnorm htend1F htend2

/-- **The multiples version, in evaluated form.** -/
theorem tsum_stride_gen {f : ℕ → ℝ} {p : ℕ} (hp : 1 ≤ p) (hf : ∀ n, 0 ≤ f n)
    (hsum : Summable f) :
    (∑' n : ℕ, (if p ∣ n then f n else 0)) = ∑' k : ℕ, f (p * k) :=
  (hasSum_stride_gen hp hf hsum).tsum_eq

/-- The exponent bookkeeping of the stride identity. -/
private theorem stride_exp (p k : ℕ) (hp1 : 1 ≤ p) :
    p * (k + 1) = (p * k + 1) + (p - 1) := by
  have h2 : (1 : ℕ) + (p - 1) = p := (Nat.add_comm 1 (p - 1)).trans (Nat.sub_add_cancel hp1)
  rw [Nat.mul_succ]
  omega

/-! ## 1. The arithmetic core: `ω` at a dilated index -/

/-- **THE ARITHMETIC CORE OF THE STRIDE DECOMPOSITION.**

For a prime `p` and any `m`, `ω (p * m) = ω m + 1 - [p ∣ m]`: multiplying by a
prime adds one new prime factor unless `p` already divides `m`, in which case it
adds none.  (Round 96's `omega_two_mul` is the case `p = 2`.) -/
theorem omega_mul_prime_add (p m : ℕ) (hp : p.Prime) :
    omega (p * m) = omega m + (if p ∣ m then (0 : ℕ) else 1) := by
  have h := omega_mul_eq_sum_indicator (m := p) (n := m) (Nat.ne_of_gt hp.pos)
  have hpf : p.primeFactors = {p} := primeFactors_prime p hp
  have hop : omega p = 1 := by simp [omega, hpf]
  rw [hpf, Finset.sum_singleton, hop] at h
  by_cases hpm : p ∣ m
  · have h1 : (if p ∣ m then (1 : ℕ) else 0) = 1 := if_pos hpm
    rw [h1, Nat.succ_sub_one] at h
    simpa [if_pos hpm] using h
  · have h1 : (if p ∣ m then (1 : ℕ) else 0) = 0 := if_neg hpm
    rw [h1, Nat.sub_zero] at h
    simpa [if_neg hpm] using h

/-- `ω (p * m) = ω m + 1` as soon as `p` is a prime not dividing `m`. -/
theorem omega_mul_prime_of_not_dvd (p m : ℕ) (hp : p.Prime) (hnd : ¬ p ∣ m) :
    omega (p * m) = omega m + 1 := by
  rw [omega_mul_prime_add p m hp, if_neg hnd]

/-- `ω (p * m) = ω m` as soon as `p` is a prime dividing `m`. -/
theorem omega_mul_prime_of_dvd (p m : ℕ) (hp : p.Prime) (hpd : p ∣ m) :
    omega (p * m) = omega m := by
  rw [omega_mul_prime_add p m hp, if_pos hpd, Nat.add_zero]

/-- **Dilation is subadditive in `ω`.**  For every `m, p`,
`ω (m * p) ≤ ω m + ω p`. -/
theorem omega_mul_le_add (m p : ℕ) (hm : m ≠ 0) : omega (m * p) ≤ omega m + omega p := by
  have h := omega_mul_eq_sum_indicator (m := m) (n := p) hm
  have hle : ∑ q ∈ m.primeFactors, (if q ∣ p then (1 : ℕ) else 0) ≤ omega m :=
    sum_ite_one_le_card (m.primeFactors) (fun q => q ∣ p)
  simp only [omega] at hle
  omega

/-- **THE PRIME-POWER VERSION.**  For a prime `p`, `k ≥ 1` and any `m`,
`ω (p ^ k * m) = ω m + (if p ∣ m then 0 else 1)`: a whole prime power is a
*single* new prime factor, however large the power. -/
theorem omega_mul_pow_prime {p m : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    omega (p ^ k * m) = omega m + (if p ∣ m then (0 : ℕ) else 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
      have h1 := omega_mul_prime_add p m hp
      simpa only [Nat.pow_one] using h1
  | succ k hk ih =>
      have hstep : omega (p * (p ^ k * m))
          = omega (p ^ k * m) + (if p ∣ p ^ k * m then (0 : ℕ) else 1) :=
        omega_mul_prime_add p (p ^ k * m) hp
      have hkey : p * (p ^ k * m) = p ^ (k + 1) * m := by
        rw [pow_succ]
        ring
      by_cases hk0 : k = 0
      · subst hk0
        have h1 := omega_mul_prime_add p m hp
        simpa only [Nat.zero_add, Nat.pow_one] using h1
      · have hk1 : 1 ≤ k := by omega
        have hpow : p ∣ p ^ k := by
          have h := Nat.pow_dvd_pow p (m := 1) (n := k) hk1
          rwa [Nat.pow_one] at h
        have hdiv : p ∣ p ^ k * m := dvd_mul_of_dvd_left hpow m
        calc omega (p ^ (k + 1) * m) = omega (p * (p ^ k * m)) := by rw [hkey]
          _ = omega (p ^ k * m) + (if p ∣ p ^ k * m then (0 : ℕ) else 1) := hstep
          _ = omega (p ^ k * m) + (0 : ℕ) := by rw [if_pos hdiv]
          _ = omega (p ^ k * m) := by rw [Nat.add_zero]
          _ = omega m + (if p ∣ m then (0 : ℕ) else 1) := ih
          _ = omega m + (if p ∣ m then (0 : ℕ) else 1) := rfl

/-- `ω n ≤ n`. -/
theorem omega_le (n : ℕ) : omega n ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [omega, h]
  · exact le_trans (omega_lt (by omega)) (by omega)

/-- **THE PRIME-POWER VERSION, `p = 2`.**  `ω (2 ^ k * m) = ω m + [Odd m]` for
`k ≥ 1`: this is the general theorem `omega_mul_pow_prime` specialised. -/
theorem omega_two_pow_mul {m k : ℕ} (hk : 1 ≤ k) :
    omega (2 ^ k * m) = omega m + (if Odd m then (1 : ℕ) else 0) := by
  have h := omega_mul_pow_prime (p := 2) (m := m) (by norm_num) hk
  have hiff : ((2 : ℕ) ∣ m) ↔ ¬ Odd m := by
    constructor
    · intro h2m ho
      obtain ⟨k, hk⟩ := ho
      obtain ⟨j, hj⟩ := h2m
      have he : 2 * k + 1 = j * 2 := by omega
      omega
    · intro hno
      rcases Nat.even_or_odd m with hne | hmo
      · obtain ⟨k, hk⟩ := hne
        rw [hk]
        exact ⟨k, by ring⟩
      · exact absurd hmo hno
  have hone : (if (2 : ℕ) ∣ m then (0 : ℕ) else 1) = (if Odd m then (1 : ℕ) else 0) := by
    by_cases ho : Odd m
    · have hnd : ¬ (2 : ℕ) ∣ m := fun h => absurd ho (hiff.mp h)
      rw [if_neg hnd, if_pos ho]
    · have hd : (2 : ℕ) ∣ m := hiff.mpr ho
      rw [if_pos hd, if_neg ho]
  rwa [hone] at h

/-! ## 2. The stride subsum of the Erdős series, and its closed form -/

/-- **The stride summand**: `[p | n] ω n / q ^ (n+1)`. -/
noncomputable def jsp87StrideTerm (p n q : ℕ) : ℝ :=
  if p ∣ n then ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ else 0

/-- **The `p`-stride subsum of the Erdős series at base `q`**:
`∑' n, [p | n] ω n / q ^ (n+1)`.  For `p = 2` this is the even part `jsp87Even q`
(the object of round 100, `BaseFamily`); for `p = 0` and `p = 1` it is the whole
series `jsp87Base q`. -/
noncomputable def jsp87Stride (p q : ℕ) : ℝ := ∑' n : ℕ, jsp87StrideTerm p n q

/-- A summable majorant transfers summability downwards. -/
private theorem summable_of_le (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (h : ∀ n, f n ≤ g n)
    (hg : Summable g) : Summable f :=
  Summable.of_nonneg_of_le hf h hg

/-- The stride summand is nonnegative. -/
theorem jsp87StrideTerm_nonneg (p n q : ℕ) : 0 ≤ jsp87StrideTerm p n q := by
  unfold jsp87StrideTerm
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · positivity

/-- **The stride series is summable**, by domination with the Erdős series. -/
theorem summable_strideTerm (p q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => jsp87StrideTerm p n q) := by
  have hle : ∀ n : ℕ, jsp87StrideTerm p n q
      ≤ ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    by_cases h : p ∣ n
    · rw [jsp87StrideTerm, if_pos h]
      exact mul_le_mul_of_nonneg_right (show (omega n : ℝ) ≤ (n : ℝ) by
        exact_mod_cast (omega_le n)) (by positivity)
    · rw [jsp87StrideTerm, if_neg h]
      positivity
  exact summable_of_le (fun n => jsp87StrideTerm p n q)
    (fun n => ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹)
    (fun n => jsp87StrideTerm_nonneg p n q) hle (summable_nat_mul_base_pow_neg q hq)

/-- A stride subsum is nonnegative. -/
theorem jsp87Stride_nonneg (p q : ℕ) : 0 ≤ jsp87Stride p q :=
  tsum_nonneg fun n => jsp87StrideTerm_nonneg p n q

/-- **A stride subsum is bounded by the whole series.** -/
theorem jsp87Stride_le_base (p q : ℕ) (hq : 2 ≤ q) : jsp87Stride p q ≤ jsp87Base q := by
  have hle : (∑' n : ℕ, jsp87StrideTerm p n q)
      ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    refine Summable.tsum_le_tsum (f := fun n => jsp87StrideTerm p n q) (fun n => ?_)
      (summable_strideTerm p q hq) (summable_jsp87Base q hq)
    unfold jsp87StrideTerm
    split_ifs
    · exact le_rfl
    · positivity
  simpa [jsp87Stride, jsp87Base] using hle

/-- **THE STRIDE-`0` SUBSUM VANISHES.**  `0` divides only the index `0`, whose
`ω`-value is `0`; this is the sense in which the stride family interpolates
between the stride `1` (the whole series) and the stride `0` (nothing). -/
theorem jsp87Stride_zero (q : ℕ) : jsp87Stride 0 q = 0 := by
  have hz : ∀ n : ℕ, jsp87StrideTerm 0 n q = 0 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [jsp87StrideTerm, if_pos (show (0 : ℕ) ∣ 0 from ⟨0, rfl⟩)]
      simp
    · rw [jsp87StrideTerm, if_neg (show ¬((0 : ℕ) ∣ n) from fun h => hn
        ((zero_dvd_iff : (0 : ℕ) ∣ n ↔ n = 0).mp h))]
  unfold jsp87Stride
  rw [tsum_congr hz]
  exact tsum_zero

/-- **THE STRIDE-`1` SUBSUM IS THE WHOLE SERIES.** -/
theorem jsp87Stride_one (q : ℕ) : jsp87Stride 1 q = jsp87Base q := by
  unfold jsp87Stride jsp87Base
  refine tsum_congr fun n => ?_
  unfold jsp87StrideTerm
  rw [if_pos (show (1 : ℕ) ∣ n from ⟨n, by ring⟩)]

/-- **THE STRIDE-`2` SUBSUM IS THE EVEN PART.**  `jsp87Stride 2 q = jsp87Even q`
(`rfl`): the "even part" of round 100 (`BaseFamily`) is exactly the stride-`2`
part of the series. -/
theorem jsp87Stride_two (q : ℕ) : jsp87Stride 2 q = jsp87Even q := rfl

/-- `ω n ≥ 1` for every `n ≥ 2`. -/
theorem omega_ge_one (n : ℕ) (hn : 2 ≤ n) : 1 ≤ omega n := by
  by_contra h
  have h0 : omega n = 0 := by omega
  have := (omega_eq_zero_iff).mp h0
  omega

/-- **A stride subsum is strictly positive** as soon as `p ≥ 1`: the single term
at the index `n = 2 p` is `ω (2 p) / q ^ (2 p + 1)`. -/
theorem jsp87Stride_pos (p q : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) : 0 < jsp87Stride p q := by
  have hge := tsum_ge_term (summable_strideTerm p q hq)
    (fun n => jsp87StrideTerm_nonneg p n q) (2 * p)
  have hω : 0 < omega (2 * p) := by
    rw [omega_two_mul]
    by_cases ho : Odd p
    · rw [if_pos ho]
      omega
    · rw [if_neg ho]
      have h2 : 2 ≤ p := by
        rcases Nat.even_or_odd p with ⟨k, hk⟩ | ho2
        · rw [hk]; omega
        · exact absurd ho2 ho
      have h1 := omega_ge_one p h2
      omega
  have hcast : (0 : ℝ) < (omega (2 * p) : ℝ) := by exact_mod_cast hω
  have hpow : (0 : ℝ) < ((q : ℝ) ^ (2 * p + 1))⁻¹ := by positivity
  unfold jsp87StrideTerm at hge
  rw [if_pos (by simp [Nat.mul_comm])] at hge
  unfold jsp87Stride
  exact lt_of_lt_of_le (mul_pos hcast hpow) hge

/-- **The geometric sum along a stride is summable.** -/
theorem summable_stride_geom (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    Summable (fun k : ℕ => ((q : ℝ) ^ (p * k + 1))⁻¹) := by
  have hqp : 1 < (q : ℝ) ^ p := q_pow_gt_one q hq hp
  have hξ : ‖((q : ℝ) ^ p)⁻¹‖ < 1 := by
    have hpos : (0 : ℝ) < ((q : ℝ) ^ p)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact inv_lt_one_of_one_lt₀ hqp
  have hgeom : HasSum (fun k : ℕ => ((q : ℝ) ^ p)⁻¹ ^ k) (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (ξ := ((q : ℝ) ^ p)⁻¹) hξ
  have hmul (k : ℕ) : (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = ((q : ℝ) ^ (p * k + 1))⁻¹ := by
    have hstep : (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = (q : ℝ)⁻¹ * ((q : ℝ) ^ (p * k))⁻¹ := by
      rw [inv_pow, pow_mul]
    calc (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = (q : ℝ)⁻¹ * ((q : ℝ) ^ (p * k))⁻¹ := hstep
      _ = ((q : ℝ) ^ (p * k) * (q : ℝ) ^ 1)⁻¹ := by
        rw [pow_one, ← DivisionMonoid.mul_inv_rev]
      _ = ((q : ℝ) ^ (p * k + 1))⁻¹ := by rw [pow_succ]; ring
  exact (hgeom.mul_left (q : ℝ)⁻¹).summable.congr fun k => hmul k

/-- **THE GEOMETRIC SUM OVER A STRIDE, IN EVALUATED FORM.**  For `q ≥ 2`, `p ≥ 1`,

`∑' k, 1 / q ^ (p * k + 1) = q ^ (p-1) / (q ^ p - 1)`,

i.e. the *whole* geometric series along the stride `p`, including its `k = 0`
term `1 / q`. -/
theorem tsum_geom_stride (q p : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ p) :
    (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹)
      = (q : ℝ) ^ (p - 1) / ((q : ℝ) ^ p - 1) := by
  have hξ : ‖((q : ℝ) ^ p)⁻¹‖ < 1 := by
    have hpos : (0 : ℝ) < ((q : ℝ) ^ p)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact inv_lt_one_of_one_lt₀ (q_pow_gt_one q hq hp)
  have hgeom : HasSum (fun k : ℕ => ((q : ℝ) ^ p)⁻¹ ^ k) (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (ξ := ((q : ℝ) ^ p)⁻¹) hξ
  have hmul (k : ℕ) : (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = ((q : ℝ) ^ (p * k + 1))⁻¹ := by
    have hstep : (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = (q : ℝ)⁻¹ * ((q : ℝ) ^ (p * k))⁻¹ := by
      rw [inv_pow, pow_mul]
    calc (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k = (q : ℝ)⁻¹ * ((q : ℝ) ^ (p * k))⁻¹ := hstep
      _ = ((q : ℝ) ^ (p * k) * (q : ℝ) ^ 1)⁻¹ := by
        rw [pow_one, ← DivisionMonoid.mul_inv_rev]
      _ = ((q : ℝ) ^ (p * k + 1))⁻¹ := by rw [pow_succ]; ring
  have hqp0 : (q : ℝ) ^ p - 1 ≠ 0 := q_pow_sub_one_ne q hq hp
  have hq0 : (q : ℝ) ≠ 0 := q_ne_zero_real q hq
  have hinv : (q : ℝ) ^ (p - 1) = (q : ℝ)⁻¹ * (q : ℝ) ^ p := by
    have h1 : (p - 1 : ℕ) + 1 = p := by omega
    calc (q : ℝ) ^ (p - 1) = (q : ℝ) ^ (p - 1) * (q : ℝ) ^ 1 * (q : ℝ)⁻¹ := by
          field_simp [hq0]
      _ = (q : ℝ) ^ ((p - 1 : ℕ) + 1) * (q : ℝ)⁻¹ := by rw [← pow_add]
      _ = (q : ℝ) ^ p * (q : ℝ)⁻¹ := by rw [h1]
      _ = (q : ℝ)⁻¹ * (q : ℝ) ^ p := by rw [mul_comm]
  have hts' : (∑' k : ℕ, (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k)
      = ∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹ := by
    refine ?_
    exact tsum_congr fun k => hmul k
  have hts : (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹)
      = ∑' k : ℕ, (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k := hts'.symm
  have key : (q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹
      = (q : ℝ) ^ (p - 1) * ((q : ℝ) ^ p - 1)⁻¹ := by
    have h2 : (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ = (q : ℝ) ^ p * ((q : ℝ) ^ p - 1)⁻¹ := by
      field_simp [hq0, hqp0]
    rw [h2, hinv]
    ring
  calc (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹)
      = ∑' k : ℕ, (q : ℝ)⁻¹ * ((q : ℝ) ^ p)⁻¹ ^ k := hts
    _ = (q : ℝ)⁻¹ * (∑' k : ℕ, ((q : ℝ) ^ p)⁻¹ ^ k) :=
      Summable.tsum_mul_left _ hgeom.summable
    _ = (q : ℝ)⁻¹ * (1 - ((q : ℝ) ^ p)⁻¹)⁻¹ := by rw [hgeom.tsum_eq]
    _ = (q : ℝ) ^ (p - 1) * ((q : ℝ) ^ p - 1)⁻¹ := key
    _ = (q : ℝ) ^ (p - 1) / ((q : ℝ) ^ p - 1) := by rw [div_eq_mul_inv]

/-- **THE FLAGSHIP OF THE ROUND: THE CLOSED FORM OF A STRIDE SUBSUM.**

For `q ≥ 2` and `p ≥ 1`,

```
∑' n, [p | n] ω n / q ^ (n+1)
    = q ^ (p-1) * S (q ^ p)  +  q ^ (p-1) / (q ^ p - 1)  -  q ^ (p^2-1) / (q ^ (p^2) - 1)
```

where `S r = jsp87Base r` is the Erdős series at base `r`.  In words: **the
`p`-divisible part of the Erdős series at base `q` is the *same* series at the
coarser base `q ^ p`, up to an explicit rational.**  The two rational corrections
are (i) the geometric sum along the stride, and (ii) the geometric sum along the
stride *squared*, which is what the indicator `[p | k]` in the correction term
`1 / q ^ (p k + 1)` costs. -/
theorem jsp87Stride_prime_eq_base (q p : ℕ) (hq : 2 ≤ q) (hp : p.Prime) :
    jsp87Stride p q
      = (q : ℝ) ^ (p - 1) * jsp87Base (q ^ p)
        + (q : ℝ) ^ (p - 1) / ((q : ℝ) ^ p - 1)
        - (q : ℝ) ^ (p ^ 2 - 1) / ((q : ℝ) ^ (p ^ 2) - 1) := by
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 ≤ p := by omega
  have hqbig : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (show (1 : ℕ) ≤ q by omega)
  have hkle : ∀ k : ℕ, k ≤ p * k := fun k => by
    simpa using (Nat.mul_le_mul_right k hp1)
  have hinv_pow (k : ℕ) : ((q : ℝ) ^ (p * k + 1))⁻¹ ≤ ((q : ℝ) ^ (k + 1))⁻¹ := by
    have hk1 : k ≤ p * k := hkle k
    have hk2 : k + 1 ≤ p * k + 1 := by omega
    have hp1pos : (0 : ℝ) < ((q : ℝ) ^ (p * k + 1)) := by positivity
    have hk1pos : (0 : ℝ) < ((q : ℝ) ^ (k + 1)) := by positivity
    exact ((inv_le_inv₀ hp1pos hk1pos)).2 (pow_le_pow_nat hqbig hk2)
  -- 1. reindex `n = p * k`
  have hre : (∑' n : ℕ, jsp87StrideTerm p n q)
      = ∑' k : ℕ, ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹ :=
    tsum_stride_gen (f := fun n : ℕ => ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹)
      (p := p) hp1 (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (summable_jsp87Base q hq)
  -- 2. split the summand by `omega_mul_prime_add`
  have hsplit (k : ℕ) :
      ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹
        = ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹
          + (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹ := by
    rw [omega_mul_prime_add p k hp]
    push_cast
    ring
  have e1 : Summable (fun k : ℕ => ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹) := by
    have emaj : Summable (fun k : ℕ => (p : ℝ) * ((k : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) := by
      simpa [mul_assoc] using (summable_nat_mul_base_pow_neg q hq).mul_left (p : ℝ)
    refine summable_of_le (fun k => ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
      (fun k => (p : ℝ) * ((k : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹)
      (fun k => mul_nonneg (Nat.cast_nonneg _)
        (by positivity : (0 : ℝ) ≤ ((q : ℝ) ^ (p * k + 1))⁻¹)) (fun k => ?_) emaj
    calc ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹
        ≤ ((p * k : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ :=
          mul_le_mul (by exact_mod_cast (omega_le (p * k))) (hinv_pow k)
            (by positivity) (Nat.cast_nonneg _)
      _ ≤ (p : ℝ) * ((k : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := by
        have hA : ((p * k : ℕ) : ℝ) = (p : ℝ) * ((k : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hA]
  have e2 : Summable (fun k : ℕ =>
      (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹) := by
    refine summable_of_le (fun k => (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹)
      (fun k => ((q : ℝ) ^ (k + 1))⁻¹)
      (fun k => mul_nonneg (by
          by_cases hk : p ∣ k
          · rw [if_pos hk]
          · rw [if_neg hk]
            positivity)
        (by positivity : (0 : ℝ) ≤ ((q : ℝ) ^ (p * k + 1))⁻¹)) (fun k => ?_)
      (summable_base_pow_negK q hq 1)
    by_cases hk : p ∣ k
    · rw [if_pos hk, zero_mul]
      positivity
    · rw [if_neg hk, one_mul]
      simpa using hinv_pow k
  have e1' : Summable (fun k : ℕ =>
      ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹) := by
    have emaj : Summable (fun k : ℕ => (p : ℝ) * ((k : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) := by
      simpa [mul_assoc] using (summable_nat_mul_base_pow_neg q hq).mul_left (p : ℝ)
    refine summable_of_le (fun k => ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
      (fun k => ((k : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹)
      (fun k => mul_nonneg (Nat.cast_nonneg _)
        (by positivity : (0 : ℝ) ≤ ((q : ℝ) ^ (p * k + 1))⁻¹)) (fun k => ?_)
      (summable_nat_mul_base_pow_neg q hq)
    exact mul_le_mul (show (omega k : ℝ) ≤ (k : ℝ) by exact_mod_cast (omega_le k))
      (hinv_pow k) (by positivity) (Nat.cast_nonneg _)
  have hsum2 : (∑' k : ℕ, ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
      = (∑' k : ℕ, ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
        + ∑' k : ℕ, (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹ := by
    have hAdd : (∑' k : ℕ, (((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹
            + (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹))
        = (∑' k : ℕ, ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
          + ∑' k : ℕ, (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹ :=
      Summable.tsum_add e1' e2
    have hcong : (∑' k : ℕ, (((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹
            + (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹))
        = ∑' k : ℕ, ((omega (p * k) : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹ := by
      refine ?_
      exact tsum_congr fun k => (hsplit k).symm
    exact hcong.symm.trans hAdd
  -- 3. the `ω`-part is the Erdős series at the coarser base `q ^ p`
  have hqp2 : 2 ≤ q ^ p := by
    have h1 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : (2 : ℝ) ≤ (q : ℝ) ^ p := by
      calc (2 : ℝ) ≤ (q : ℝ) ^ 1 := by rw [pow_one]; exact h1
        _ ≤ (q : ℝ) ^ p := pow_le_pow_nat (by
          have hqbig2 := q_pow_gt_one q hq hp1
          linarith) hp1
    exact_mod_cast h2
  have eB : Summable (fun k : ℕ => ((omega k : ℕ) : ℝ) * (((q ^ p : ℕ) : ℝ) ^ (k + 1))⁻¹) :=
    summable_jsp87Base (q ^ p) hqp2
  have hkey (k : ℕ) : ((q : ℝ) ^ (p * k + 1))⁻¹
      = (q : ℝ) ^ (p - 1) * (((q ^ p : ℕ) : ℝ) ^ (k + 1))⁻¹ := by
    have h2 : ((q ^ p : ℕ) : ℝ) ^ (k + 1) = q ^ (p * (k + 1)) := by
      rw [Nat.cast_pow, ← pow_mul]
    rw [h2]
    have hexp : p * (k + 1) = (p * k + 1) + (p - 1) := stride_exp p k hp1
    have heq : (q : ℝ) ^ (p * (k + 1)) = (q : ℝ) ^ (p * k + 1) * (q : ℝ) ^ (p - 1) := by
      rw [← pow_add]
      exact congrArg (fun m : ℕ => (q : ℝ) ^ m) hexp
    rw [heq, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel₀ (by positivity : ((q : ℝ) ^ (p - 1)) ≠ 0), one_mul]
  have hrw' : (∑' k : ℕ, ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
      = (q : ℝ) ^ (p - 1) * jsp87Base (q ^ p) := by
    have hts' : (∑' k : ℕ, ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
        = ∑' k : ℕ, (q : ℝ) ^ (p - 1)
          * (((omega k : ℕ) : ℝ) * (((q ^ p : ℕ) : ℝ) ^ (k + 1))⁻¹) := by
      refine tsum_congr (f := fun k => ((omega k : ℕ) : ℝ) * ((q : ℝ) ^ (p * k + 1))⁻¹)
        (g := fun k => (q : ℝ) ^ (p - 1)
          * (((omega k : ℕ) : ℝ) * (((q ^ p : ℕ) : ℝ) ^ (k + 1))⁻¹)) ?_
      exact fun k => by
        rw [congrArg (fun x : ℝ => ((omega k : ℕ) : ℝ) * x) (hkey k)]
        ring
    rw [hts', Summable.tsum_mul_left _ eB]
    rfl
  -- 4. the geometric part: the stride minus the stride squared
  have hp2 : 1 ≤ p * p := by
    have h1' : 1 ≤ p := hp1
    nlinarith [Nat.succ_le_succ (Nat.mul_le_mul h1' h1')]
  have hB : (∑' k : ℕ, (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹)
      = (q : ℝ) ^ (p - 1) / ((q : ℝ) ^ p - 1)
        - (q : ℝ) ^ (p ^ 2 - 1) / ((q : ℝ) ^ (p ^ 2) - 1) := by
    have hpt (k : ℕ) : (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹
        = ((q : ℝ) ^ (p * k + 1))⁻¹
          - (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
      by_cases hk : p ∣ k
      · rw [if_pos hk, if_pos hk, zero_mul, sub_self]
      · rw [if_neg hk, if_neg hk, one_mul]
        ring
    have eS1 : Summable (fun k : ℕ => ((q : ℝ) ^ (p * k + 1))⁻¹) :=
      summable_stride_geom q p hq hp1
    have eS2 : Summable (fun k : ℕ =>
        (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0)) := by
      refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
        (fun k => ?_) eS1
      by_cases hk : p ∣ k
      · rw [if_pos hk]
      · rw [if_neg hk]; positivity
    have hS2 : (∑' k : ℕ, (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0))
        = (q : ℝ) ^ (p ^ 2 - 1) / ((q : ℝ) ^ (p ^ 2) - 1) := by
      have h := tsum_stride_gen (f := fun n : ℕ => ((q : ℝ) ^ (p * n + 1))⁻¹)
        (p := p) hp1 (fun n => by positivity) (summable_stride_geom q p hq hp1)
      rw [h]
      simpa [mul_assoc, pow_two] using (tsum_geom_stride q (p * p) hq hp2)
    have hsub : (∑' k : ℕ, (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹)
        = (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹) - ∑' k : ℕ,
          (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0) := by
      have hHS : HasSum (fun k : ℕ => ((q : ℝ) ^ (p * k + 1))⁻¹
          - (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0))
          ((∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹) - ∑' k : ℕ,
            (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0)) :=
        eS1.hasSum.sub eS2.hasSum
      rw [← hHS.tsum_eq]
      exact tsum_congr hpt
    calc (∑' k : ℕ, (if p ∣ k then (0 : ℝ) else 1) * ((q : ℝ) ^ (p * k + 1))⁻¹)
        = (∑' k : ℕ, ((q : ℝ) ^ (p * k + 1))⁻¹) - ∑' k : ℕ,
            (if p ∣ k then ((q : ℝ) ^ (p * k + 1))⁻¹ else 0) := hsub
      _ = (q : ℝ) ^ (p - 1) / ((q : ℝ) ^ p - 1)
          - (q : ℝ) ^ (p ^ 2 - 1) / ((q : ℝ) ^ (p ^ 2) - 1) := by
          rw [tsum_geom_stride q p hq hp1, hS2]
  unfold jsp87Stride
  rw [hre, hsum2, hrw', hB]
  ring

/-- **THE STRIDE-`2` INSTANCE AT BASE `2`: the even part of the binary Erdős series
is twice the Erdős series in base `4`, up to the rational `2/15`.** -/
theorem jsp87Stride_two_two : jsp87Even 2 = 2 * jsp87Base 4 + (2 / 15 : ℝ) := by
  have h := jsp87Stride_prime_eq_base 2 2 (by omega) (by norm_num)
  rw [jsp87Stride_two] at h
  rw [h]
  norm_num
  ring

/-! ## 3. What the stride identity transfers: rationality and the `4`-adic reduction -/

/-- **THE DIOPHANTINE TRANSFER, EVEN PART → BASE `4`.**  If the Erdős series in
base `4` is the rational `c / d` with `d > 0`, then the even part of the binary
Erdős series is the rational `(30 c + 2 d) / (15 d)`. -/
theorem jsp87Even_two_rat_of_base_four_rat {c d : ℤ} (hd : 0 < d)
    (h : jsp87Base 4 = (c : ℝ) / (d : ℝ)) :
    ∃ a b : ℤ, 0 < b ∧ jsp87Even 2 = (a : ℝ) / (b : ℝ) := by
  refine ⟨30 * c + 2 * d, 15 * d, by positivity, ?_⟩
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  rw [jsp87Stride_two_two, h]
  field_simp
  push_cast
  ring

/-- **THE DIOPHANTINE TRANSFER, BASE `4` → EVEN PART.**  Conversely: if the even
part is the rational `a / b` with `b > 0`, then the Erdős series in base `4` is
the rational `(15 a - 2 b) / (30 b)`.  **Rationality of the Erdős series at base
`2` and rationality of the Erdős series at base `4` are therefore the same
statement** (via `jsp87Series = jsp87Even 2 + jsp87Odd 2` and the rationality of
`jsp87Odd 2`). -/
theorem jsp87Base_four_of_even_two : jsp87Base 4 = (jsp87Even 2 - 2 / 15) / 2 := by
  rw [jsp87Stride_two_two]
  field_simp
  ring

theorem jsp87Base_four_eq_of_even_two_rat {a b : ℤ} (_hb : 0 < b)
    (h : jsp87Even 2 = (a : ℝ) / (b : ℝ)) :
    jsp87Base 4 = ((a : ℝ) / (b : ℝ) - 2 / 15) / 2 := by
  rw [jsp87Base_four_of_even_two, h]

theorem jsp87Base_four_rat_of_even_two_rat {a b : ℤ} (hb : 0 < b)
    (h : jsp87Even 2 = (a : ℝ) / (b : ℝ)) :
    ∃ c d : ℤ, 0 < d ∧ jsp87Base 4 = (c : ℝ) / (d : ℝ) := by
  refine ⟨15 * a - 2 * b, 30 * b, by positivity, ?_⟩
  rw [jsp87Base_four_eq_of_even_two_rat hb h]
  field_simp
  push_cast
  ring

/-- **THE STRIDE-`2` SUBSUM IS STRICTLY BELOW THE SERIES:** the even part misses
the odd part, which is at least `1/16`. -/
theorem jsp87Stride_two_two_lt_base : jsp87Even 2 < jsp87Series := by
  have ho : jsp87Odd 2 = jsp87Series - jsp87Even 2 := jsp87Odd_two_sub _ rfl
  have h1 : (1 / 16 : ℝ) ≤ jsp87Odd 2 := jsp87Odd_two_ge
  rw [ho] at h1
  have h2 : (0 : ℝ) < 1 / 16 := by norm_num
  linarith

/-- **THE STRIDE-`p` SUBSUM IS NONZERO AND BELOW THE SERIES** for every prime
stride `p`: a prime stride detects a rational value of the series only through
the coarser-base series `S (q ^ p)`, never through the stride subsum alone. -/
theorem jsp87Stride_prime_pos_lt_base (p : ℕ) (hp : p.Prime) :
    0 < jsp87Stride p 2 ∧ jsp87Stride p 2 ≤ jsp87Base 2 := by
  refine ⟨jsp87Stride_pos p 2 (by omega) ((Nat.succ_le_iff).mpr hp.pos), ?_⟩
  exact jsp87Stride_le_base p 2 (by omega)

end JSP87
