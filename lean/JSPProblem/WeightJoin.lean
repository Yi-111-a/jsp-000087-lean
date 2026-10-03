/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.RowJoin
import Mathlib.Tactic

/-!
# JSP-000087 : the WEIGHTED level reflection of the Erdős series

Round 83 (`LevelSets.lean`) built the **level series**
`L k = ∑' n, [ω n = k] · 2^-(n+1)` and proved them irrational for every `k ≥ 1`;
rounds 103/104 built the **layer-cake join** between the Erdős series
`S = jsp87Series` and the round-83 families, in column form and in row form.  But the
join that the round log had recorded as "numerical commentary" —

```
S = ∑' k, k · L k                                              (the reflection)
```

— had **never been written down as a theorem**: `LevelSets.lean` §3 mentions it
only in prose ("`jsp87Series = ∑ k, k · L k` numerically").  This module proves it,
together with its unweighted mirror image

```
∑' k, L k = 1                                                  (the partition of unity)
```

and the quantitative decay that makes the reflection a *doubly exponential*
recombination of an explicitly classified family of irrationals.

## 1. The level series decay doubly exponentially (§1)

A level-`k` digit is `1` only at integers with exactly `k` distinct prime factors,
and `ω n = k` forces `2^k ≤ n` (`two_pow_omega_le`).  Hence the primary series of
the level indicator vanishes below `n = 2^k`, so its prefix at that cut point is
*zero*, and the "no carrying" split `2^N · T f = A f N + U f N` gives the sharp
bound

```
2^(2^k) · L k ≤ 1        jsp87LevelSeries_mul_two_pow_two_pow
```

i.e. `L k ≤ 2^-(2^k)`.  Round 83 could only prove `L k < 1` and `L k ≤ 1/4`; the
double-exponential bound is new, and it is the quantitative reason the weighted
reflection of §4 converges.  The same argument gives the bound for the "at least"
family (`jsp87AtLeastSeries_mul_two_pow_two_pow`).

## 2. The weighted columns (§2)

* `jsp87_weightCount` : `∑_{k<M} k · [ω n = k] = if ω n < M then ω n else 0` — the
  weighted layer count at the single cut point `n`;
* `jsp87WeightColumn M n` : that count, weighted by `2^-(n+1)`;
* `jsp87WeightColumn_eq_term` : **the weighted saturation point** —
  `n < 2^M ⟹ the weighted column is the `n`-th term of the Erdős series itself`;
* `jsp87WeightColumn_le_term`, `summable_jsp87WeightColumn`.

## 3-4. The finite interchange, the gap, and the reflection (§3, §4)

* `jsp87_weightPartial_eq_tsum` : the weighted rows at height `M` are the `tsum` of
  the weighted columns — exact, by the finite `Summable.tsum_finsetSum` interchange;
* `jsp87_weightPartial_le_series`, `jsp87_colPartial_le_weightPartial` : the weighted
  rows never overshoot `S`, and they dominate the columns below `n = 2^M`;
* `jsp87_weightGap_le_tail`, `tendsto_jsp87_weightGap`, `tendsto_jsp87_weightPartial`;
* **`jsp87Series_eq_tsum_weightedLevels`** — **THE REFLECTION**, `S = ∑' k, k · L k`,
  the identity round 83 only recorded numerically.

## 5. The weighted levels are irrational (§5)

* `jsp87_weightedLevel_irrational` : for every `k ≥ 1` the summand `k · L k` is
  irrational, so the reflection writes `S` as a convergent sum of *provably
  irrational* numbers;
* `jsp87Series_eq_tsum_weightedLevels_onzero` : the same with the `k = 0` member
  removed;
* `jsp87_weightPartial_le_sub` : the weighted rows miss at least the `K`-th weighted
  level.

## 6. The level series partition the unit interval (§6)

* `jsp87_levelCount`, `jsp87LevelColumn M n = [ω n < M] · 2^-(n+1)` — the
  *unweighted* columns are indicators;
* `jsp87_levelPartial_le_one`, `jsp87_levelPartial_ge_colPartial`,
  `tendsto_jsp87_levelPartial`;
* **`jsp87_tsum_levelSeries_eq_one`** — `∑' k, L k = 1`: the level sets partition the
  integers, so the level series partition the interval `[0,1]`;
* `jsp87_levelPartial_le_sub_one`, `jsp87_tsum_levelSeries_tail_eq_quarter` : the
  partition is *nested* — `∑_{k<K} L k ≤ 1 − L K` — and its `k ≥ 1` part is `1/4`.

## Why this still does not close the gate

As in round 104: a countable sum of irrational numbers need not be irrational
(`jsp87Series_rational_of_atLeast_periodic`), so neither the row form nor the
weighted reflection transfers irrationality to `S`.  The gate still waits on round
41's `jsp87_digit_not_eventuallyPeriodic`, the aperiodicity of the binary digits of
the **carried** series, equivalently round 64's aperiodicity of the doubling orbit
`Int.fract (θ N)`.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. A level digit vanishes below `2^k` — the doubly exponential decay -/

/-- **A LEVEL DIGIT VANISHES BELOW `2^k`.**  `ω n = k` with `k ≥ 1` forces
`2^k ≤ n` by `two_pow_omega_le`. -/
theorem jsp87Level_eq_zero_of_lt_two_pow {k n : ℕ} (hk : 1 ≤ k) (hn : n < 2 ^ k) :
    jsp87Level k n = 0 := by
  by_cases hω : omega n = k
  · rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, omega_zero] at hω
      exact absurd hω (by omega)
    · have h1 := two_pow_omega_le hn0
      rw [hω] at h1
      exact absurd (Nat.lt_of_le_of_lt h1 hn) (Nat.lt_irrefl _)
  · exact jsp87Level_eq_zero_of_omega_ne hω

/-- **AN "AT LEAST" DIGIT VANISHES BELOW `2^k`.**  `k ≤ ω n` with `k ≥ 1` forces
`2^k ≤ n`. -/
theorem jsp87AtLeast_eq_zero_of_lt_two_pow {k n : ℕ} (hk : 1 ≤ k) (hn : n < 2 ^ k) :
    jsp87AtLeast k n = 0 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have hne : ¬ (k ≤ 0) := by omega
    simp only [jsp87AtLeast, omega_zero, hne, ite_false]
  · have h1 := two_pow_omega_le hn0
    have hlt : (2 : ℕ) ^ omega n < 2 ^ k := lt_of_le_of_lt h1 hn
    exact (jsp87AtLeast_eq_zero_iff k n).2
      ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 hlt)

/-- **THE LEVEL PREFIX AT `2^k` VANISHES.** -/
theorem jsp87BinaryInt_level_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    jsp87BinaryInt (fun n => jsp87Level k n) (2 ^ k) = 0 := by
  refine Finset.sum_eq_zero fun n hn => ?_
  dsimp only
  have hn' := Finset.mem_range.mp hn
  rw [jsp87Level_eq_zero_of_lt_two_pow hk hn']
  norm_num

/-- The same for the "at least" indicators. -/
theorem jsp87BinaryInt_atLeast_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    jsp87BinaryInt (fun n => jsp87AtLeast k n) (2 ^ k) = 0 := by
  refine Finset.sum_eq_zero fun n hn => ?_
  dsimp only
  have hn' := Finset.mem_range.mp hn
  rw [jsp87AtLeast_eq_zero_of_lt_two_pow hk hn']
  norm_num

/-- **DOUBLE-EXPONENTIAL DECAY OF THE LEVEL SERIES.**
`2^(2^k) · L k ≤ 1`: the level-`k` digit string vanishes below `n = 2^k`, so its
prefix at that cut point is `0`, and the primary tail never exceeds `1`. -/
theorem jsp87LevelSeries_mul_two_pow_two_pow (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ (2 ^ k) * jsp87LevelSeries k ≤ 1 := by
  have hsplit := jsp87Binary_split (fun n => jsp87Level k n) (fun n => jsp87Level_le k n)
    (2 ^ k) (one_le_two_pow k)
  have hz : jsp87BinaryInt (fun n => jsp87Level k n) (2 ^ k) = 0 :=
    jsp87BinaryInt_level_eq_zero k hk
  rw [hz, Nat.cast_zero, zero_add] at hsplit
  have htail := jsp87BinaryTail_le_one (fun n => jsp87Level k n) (fun n => jsp87Level_le k n)
    (2 ^ k)
  calc (2 : ℝ) ^ (2 ^ k) * jsp87LevelSeries k
      = (2 : ℝ) ^ (2 ^ k) * jsp87BinarySeries (fun n => jsp87Level k n) := rfl
    _ = jsp87BinaryTail (fun n => jsp87Level k n) (2 ^ k) := by rw [← hsplit]
    _ ≤ 1 := htail

private theorem inv_eq_one_div' (x : ℝ) : x⁻¹ = 1 / x := by
  rw [div_eq_mul_inv, one_mul]

/-- The same, in the closed form `L k ≤ 2^-(2^k)`. -/
theorem jsp87LevelSeries_le_two_pow_sharp (k : ℕ) (hk : 1 ≤ k) :
    jsp87LevelSeries k ≤ ((2 : ℝ) ^ (2 ^ k))⁻¹ := by
  have hP : 0 < (2 : ℝ) ^ (2 ^ k) := by positivity
  have h1 : jsp87LevelSeries k ≤ (1 : ℝ) / (2 : ℝ) ^ (2 ^ k) := by
    apply (le_div_iff₀ hP).2
    simpa only [mul_comm] using jsp87LevelSeries_mul_two_pow_two_pow k hk
  rw [← inv_eq_one_div'] at h1
  exact h1

/-- `2^k · L k ≤ 1` — the geometric majorant in the index `k`. -/
theorem jsp87LevelSeries_mul_two_pow (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * jsp87LevelSeries k ≤ 1 := by
  have h0 : 0 ≤ jsp87LevelSeries k := jsp87LevelSeries_nonneg k
  have h1 : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  have hlt : k < 2 ^ k := by omega
  have htwo : ((2 : ℕ) ^ k) ≤ ((2 : ℕ) ^ (2 ^ k)) :=
    ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mpr hlt).le
  calc (2 : ℝ) ^ k * jsp87LevelSeries k ≤ ((2 : ℕ) ^ (2 ^ k) : ℝ) * jsp87LevelSeries k := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast htwo) h0
    _ ≤ 1 := jsp87LevelSeries_mul_two_pow_two_pow k hk

/-- Hence `L k ≤ 2^-k`. -/
theorem jsp87LevelSeries_le_two_pow (k : ℕ) (hk : 1 ≤ k) :
    jsp87LevelSeries k ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hP : 0 < (2 : ℝ) ^ k := by positivity
  have h1 : jsp87LevelSeries k ≤ (1 : ℝ) / (2 : ℝ) ^ k := by
    apply (le_div_iff₀ hP).2
    simpa only [mul_comm] using jsp87LevelSeries_mul_two_pow k hk
  rw [← inv_eq_one_div'] at h1
  exact h1

/-- **INSTANCE: `4 · L 1 ≤ 1`.**  The level-`1` indicator is the prime-power
indicator, and prime powers are sparse, so a quarter of a binary weight follows
immediately from the general bound. -/
theorem jsp87LevelSeries_one_le : (4 : ℝ) * jsp87LevelSeries 1 ≤ 1 := by
  have h := jsp87LevelSeries_mul_two_pow_two_pow 1 (by norm_num)
  convert h using 1; norm_num

/-- The double-exponential decay of the "at least" family. -/
theorem jsp87AtLeastSeries_mul_two_pow_two_pow (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ (2 ^ k) * jsp87AtLeastSeries k ≤ 1 := by
  have hsplit := jsp87Binary_split (fun n => jsp87AtLeast k n) (fun n => jsp87AtLeast_le k n)
    (2 ^ k) (one_le_two_pow k)
  have hz : jsp87BinaryInt (fun n => jsp87AtLeast k n) (2 ^ k) = 0 :=
    jsp87BinaryInt_atLeast_eq_zero k hk
  rw [hz, Nat.cast_zero, zero_add] at hsplit
  have htail := jsp87BinaryTail_le_one (fun n => jsp87AtLeast k n) (fun n => jsp87AtLeast_le k n)
    (2 ^ k)
  calc (2 : ℝ) ^ (2 ^ k) * jsp87AtLeastSeries k
      = (2 : ℝ) ^ (2 ^ k) * jsp87BinarySeries (fun n => jsp87AtLeast k n) := rfl
    _ = jsp87BinaryTail (fun n => jsp87AtLeast k n) (2 ^ k) := by rw [← hsplit]
    _ ≤ 1 := htail

/-- The geometric majorant for the "at least" family. -/
theorem jsp87AtLeastSeries_mul_two_pow (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * jsp87AtLeastSeries k ≤ 1 := by
  have h0 : 0 ≤ jsp87AtLeastSeries k := jsp87AtLeastSeries_nonneg k
  have h1 : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  have hlt : k < 2 ^ k := by omega
  have htwo : ((2 : ℕ) ^ k) ≤ ((2 : ℕ) ^ (2 ^ k)) :=
    ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mpr hlt).le
  calc (2 : ℝ) ^ k * jsp87AtLeastSeries k ≤ ((2 : ℕ) ^ (2 ^ k) : ℝ) * jsp87AtLeastSeries k := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast htwo) h0
    _ ≤ 1 := jsp87AtLeastSeries_mul_two_pow_two_pow k hk

/-! ## 2. The weighted layer columns -/

/-- **THE WEIGHTED LAYER COUNT AT `n`.**  Only the layer of index `k = ω n`
contributes, and it carries weight `ω n`; it is visible exactly when `ω n < M`. -/
theorem jsp87_weightCount (M n : ℕ) :
    ∑ k ∈ Finset.range M, k * jsp87Level k n = if omega n < M then omega n else 0 := by
  rcases Nat.lt_or_ge (omega n) M with hM | hM
  · have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
      intro a ha
      exact Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_of_lt hM))
    have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range (omega n + 1) →
        k * jsp87Level k n = 0 := by
      intro k _ hna
      have hna' : ¬ (k < omega n + 1) := fun hh => hna (Finset.mem_range.mpr hh)
      have hstep : omega n + 1 ≤ k := Nat.le_of_not_gt hna'
      have hne : omega n ≠ k := by
        intro hk
        have : omega n + 1 ≤ omega n := by rwa [← hk] at hstep
        exact (Nat.lt_irrefl (omega n)) (Nat.lt_succ_self _ |>.trans_le this)
      rw [jsp87Level_eq_zero_of_omega_ne hne]
      norm_num
    have hswap : (∑ k ∈ Finset.range (omega n + 1), k * jsp87Level k n)
        = ∑ k ∈ Finset.range M, k * jsp87Level k n :=
      Finset.sum_subset hsub hzero
    have hinner : (∑ k ∈ Finset.range (omega n + 1), k * jsp87Level k n) = omega n := by
      rw [Finset.sum_eq_single (omega n) (by
            intro b _ hb
            rw [jsp87Level_eq_zero_of_omega_ne (Ne.symm hb)]
            norm_num) (by simp [Finset.mem_range])]
      have hone : omega n * jsp87Level (omega n) n = omega n := by
        rw [jsp87Level_eq_one_of_omega_eq rfl]
        ring
      exact hone
    rw [← hswap, hinner, ite_eq_left hM]
  · have hzero : ∀ k ∈ Finset.range M, k * jsp87Level k n = 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hne : omega n ≠ k := by
        intro hkeq
        have hlt' : k < omega n := hk'.trans_le hM
        exact (Nat.lt_irrefl k) (hkeq ▸ hlt')
      rw [jsp87Level_eq_zero_of_omega_ne hne]
      norm_num
    rw [Finset.sum_eq_zero hzero, ite_eq_right (Nat.not_lt.mpr hM)]

/-- The weighted count, read in `ℝ`. -/
theorem jsp87_weightCount_cast (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k * jsp87Level k n : ℕ) : ℝ))
      = ((if omega n < M then omega n else 0 : ℕ) : ℝ) := by
  rw [← Nat.cast_sum, jsp87_weightCount]

/-- **THE WEIGHTED COLUMN AT `n`.** -/
noncomputable def jsp87WeightColumn (M n : ℕ) : ℝ :=
  ((∑ k ∈ Finset.range M, k * jsp87Level k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

private theorem cast_sum_weight (M n : ℕ) :
    ((∑ k ∈ Finset.range M, k * jsp87Level k n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range M, ((k * jsp87Level k n : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]

/-- The `M` weighted layers, read off at the single cut point `n`, are the weighted
column. -/
theorem jsp87_weightedLevel_sum_eq (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n))
      = jsp87WeightColumn M n := by
  unfold jsp87WeightColumn
  calc (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑ k ∈ Finset.range M, (((k * jsp87Level k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [jsp87BitTerm, Nat.cast_mul]
        ring
    _ = ((∑ k ∈ Finset.range M, (k * jsp87Level k n : ℕ) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [cast_sum_weight, Finset.sum_mul]

theorem jsp87WeightColumn_nonneg (M n : ℕ) : 0 ≤ jsp87WeightColumn M n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE WEIGHTED COLUMNS ARE DOMINATED BY THE ERDŐS SERIES.** -/
theorem jsp87WeightColumn_le_term (M n : ℕ) :
    jsp87WeightColumn M n ≤ jsp87Term n := by
  unfold jsp87WeightColumn
  rw [cast_sum_weight, jsp87_weightCount_cast, jsp87Term]
  rcases Nat.lt_or_ge (omega n) M with hM | hM
  · rw [ite_eq_left hM]
  · rw [ite_eq_right (Nat.not_lt.mpr hM)]
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE WEIGHTED SATURATION POINT.**  Below `n = 2^M` the weighted column *is* the
`n`-th term of the Erdős series: every level of `n` has index `< M`. -/
theorem jsp87WeightColumn_eq_term {M n : ℕ} (hM : 1 ≤ M) (hn : n < 2 ^ M) :
    jsp87WeightColumn M n = jsp87Term n := by
  have hωlt : omega n < M := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, omega_zero]
      have : 0 < M := hM
      omega
    · exact omega_lt_of_lt_two_pow hn0 hn
  unfold jsp87WeightColumn
  rw [cast_sum_weight, jsp87_weightCount_cast, ite_eq_left hωlt, jsp87Term]

theorem summable_jsp87WeightColumn (M : ℕ) : Summable (jsp87WeightColumn M) :=
  Summable.of_nonneg_of_le (fun n => jsp87WeightColumn_nonneg M n)
    (fun n => jsp87WeightColumn_le_term M n) (summable_omega_mul_inv_two_pow)

/-! ## 3. The finite weighted interchange -/

/-- **THE WEIGHTED ROW PARTIAL SUM** `W M = ∑_{k<M} k · L k`. -/
noncomputable def jsp87WeightPartial (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87LevelSeries k)

/-- **THE FINITE WEIGHTED INTERCHANGE.**  The `M` weighted rows are the `tsum` of the
weighted columns — exact, with no limit argument. -/
theorem jsp87_weightPartial_eq_tsum (M : ℕ) :
    (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87LevelSeries k)) = ∑' (n : ℕ), jsp87WeightColumn M n := by
  have hfin : (∑' (n : ℕ), ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑ k ∈ Finset.range M, ∑' (n : ℕ), ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n) := by
    refine Summable.tsum_finsetSum fun i _ => ?_
    exact (summable_jsp87BitTerm (fun m => jsp87Level i m)
      (fun m => jsp87Level_le i m)).mul_left ((i : ℝ))
  have hrhs : (∑ k ∈ Finset.range M, ∑' (n : ℕ), ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87LevelSeries k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold jsp87LevelSeries jsp87BinarySeries
    exact Summable.tsum_mul_left (k : ℝ)
      (summable_jsp87BitTerm (fun m => jsp87Level k m) (fun m => jsp87Level_le k m))
  have hlhs : (∑' (n : ℕ), ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n))
      = ∑' (n : ℕ), jsp87WeightColumn M n := by
    refine tsum_congr fun n => ?_
    exact jsp87_weightedLevel_sum_eq M n
  calc (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87LevelSeries k))
      = ∑ k ∈ Finset.range M, ∑' (n : ℕ), ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n) :=
        hrhs.symm
    _ = ∑' (n : ℕ), ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87Level k m) n) :=
      hfin.symm
    _ = ∑' (n : ℕ), jsp87WeightColumn M n := hlhs

/-- **THE WEIGHTED ROWS NEVER OVERSHOOT `S`.** -/
theorem jsp87_weightPartial_le_series (M : ℕ) : jsp87WeightPartial M ≤ jsp87Series := by
  have h' := Summable.tsum_le_tsum (fun n => jsp87WeightColumn_le_term M n)
    (summable_jsp87WeightColumn M) summable_omega_mul_inv_two_pow
  have h'' : ∑' (n : ℕ), jsp87WeightColumn M n ≤ jsp87Series := h'.trans_eq jsp87_convergence.tsum_eq.symm
  exact (jsp87_weightPartial_eq_tsum M).trans_le h''

/-- **THE WEIGHTED ROWS DOMINATE THE COLUMNS BELOW `n = 2^M`.** -/
theorem jsp87_colPartial_le_weightPartial {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (2 ^ M), jsp87Term n) ≤ jsp87WeightPartial M := by
  have hmin : ∀ n ∈ Finset.range (2 ^ M), jsp87WeightColumn M n = jsp87Term n :=
    fun n hn => jsp87WeightColumn_eq_term hM (Finset.mem_range.mp hn)
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ M))
    (fun i _ => jsp87WeightColumn_nonneg M i) (summable_jsp87WeightColumn M)
  calc (∑ n ∈ Finset.range (2 ^ M), jsp87Term n)
      = ∑ n ∈ Finset.range (2 ^ M), jsp87WeightColumn M n := (Finset.sum_congr rfl hmin).symm
    _ ≤ ∑' (n : ℕ), jsp87WeightColumn M n := hsum
    _ = jsp87WeightPartial M := (jsp87_weightPartial_eq_tsum M).symm

/-! ## 4. The gap, and the reflection -/

/-- The weighted gap is nonnegative. -/
theorem jsp87_weightGap_nonneg (M : ℕ) : 0 ≤ jsp87Series - jsp87WeightPartial M := by
  have h := jsp87_weightPartial_le_series M
  linarith

/-- The weighted gap is bounded by the column tail beyond the saturation point. -/
theorem jsp87_weightGap_le_tail {M : ℕ} (hM : 1 ≤ M) :
    jsp87Series - jsp87WeightPartial M
      ≤ jsp87Series - ∑ n ∈ Finset.range (2 ^ M), jsp87Term n := by
  have hle := jsp87_colPartial_le_weightPartial hM
  linarith

private theorem dist_zero_eq (x : ℝ) : dist x 0 = |x| := by
  rw [dist_eq_norm, Real.norm_eq_abs]
  simp

/-- **EVERY PARTIAL SUM OF THE ERDŐS SERIES IS BELOW `S`.** -/
theorem jsp87_colPartial_le_series (N : ℕ) :
    (∑ n ∈ Finset.range N, jsp87Term n) ≤ jsp87Series :=
  (Summable.sum_le_tsum (Finset.range N)
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))
    summable_omega_mul_inv_two_pow).trans_eq jsp87_convergence.tsum_eq.symm

/-- The tail of the Erdős series is nonnegative. -/
theorem jsp87_termTail_nonneg (N : ℕ) : 0 ≤ jsp87Series - ∑ n ∈ Finset.range N, jsp87Term n :=
  sub_nonneg.mpr (jsp87_colPartial_le_series N)

private theorem pow_two_tendsto_top : Tendsto (fun M : ℕ => 2 ^ M) atTop atTop :=
  Filter.tendsto_atTop.2 fun M => by
    filter_upwards [eventually_ge_atTop M] with x hx
    exact Nat.le_trans hx (Nat.le_of_lt (Nat.lt_two_pow_self (n := x)))

/-- **THE WEIGHTED GAP TENDSSTO `0`.** -/
theorem tendsto_jsp87_weightGap :
    Tendsto (fun M => jsp87Series - jsp87WeightPartial M) atTop (nhds 0) := by
  have h1 : Tendsto (fun _ : ℕ => jsp87Series) atTop (nhds jsp87Series) := tendsto_const_nhds
  have h2 : Tendsto (fun N => ∑ n ∈ Finset.range N, jsp87Term n) atTop (nhds jsp87Series) :=
    jsp87_convergence.tendsto_sum_nat
  have hcol : Tendsto (fun N => jsp87Series - ∑ n ∈ Finset.range N, jsp87Term n)
      atTop (nhds 0) := by
    simpa only [sub_self] using h1.sub h2
  have htail : Tendsto
      (fun M => jsp87Series - ∑ n ∈ Finset.range (2 ^ M), jsp87Term n) atTop (nhds 0) :=
    hcol.comp pow_two_tendsto_top
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail ε hε
  refine ⟨N + 1, ?_⟩
  intro M hM
  have hM1 : 1 ≤ M := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le N)) hM
  have hMN : N ≤ M := Nat.le_trans (Nat.le_add_right N 1) hM
  have hlt := jsp87_weightGap_le_tail hM1
  have hg0 := jsp87_weightGap_nonneg M
  have hdist := hN _ hMN
  have ht0 := jsp87_termTail_nonneg (2 ^ M)
  rw [dist_zero_eq, abs_of_nonneg ht0] at hdist
  rw [dist_zero_eq, abs_of_nonneg hg0]
  exact lt_of_le_of_lt hlt hdist

/-- **THE WEIGHTED ROWS CONVERGE TO `S`.** -/
theorem tendsto_jsp87_weightPartial :
    Tendsto jsp87WeightPartial atTop (nhds jsp87Series) := by
  have h3 : Tendsto (fun M => (jsp87Series)
        - (jsp87Series - jsp87WeightPartial M)) atTop (nhds jsp87Series) := by
    simpa only [sub_zero] using tendsto_jsp87_weightGap.const_sub (jsp87Series)
  refine h3.congr' (f₂ := jsp87WeightPartial) (Filter.Eventually.of_forall fun M => ?_)
  unfold jsp87WeightPartial
  ring

/-- **THE WEIGHTED LEVEL SERIES IS A `HasSum` FOR `S`.** -/
theorem hasSum_weightedLevels :
    HasSum (fun k : ℕ => ((k : ℝ) * jsp87LevelSeries k)) jsp87Series := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (f := fun k : ℕ => ((k : ℝ) * jsp87LevelSeries k))
    (fun k => mul_nonneg (Nat.cast_nonneg _) (jsp87LevelSeries_nonneg k)) _).2 ?_
  exact tendsto_jsp87_weightPartial

/-- **THE WEIGHTED LEVEL SERIES IS SUMMABLE.** -/
theorem summable_weightedLevels : Summable (fun k : ℕ => ((k : ℝ) * jsp87LevelSeries k)) :=
  ⟨jsp87Series, hasSum_weightedLevels⟩

/-- **THE REFLECTION — THE HEADLINE OF THIS ROUND.**

```
jsp87Series = ∑' k, k · jsp87LevelSeries k
```

The Erdős series *is* the integer-weighted sum of the round-83 level series: each
integer `n`, with its `ω n` distinct prime factors, contributes `2^-(n+1)` to every
level `0, …, ω n`, and the total weight of the level-`k` copies is exactly
`k · 2^-(n+1)`.  Round 83 recorded this identity only as numerical commentary; here
it is proved, with convergence supplied by the weighted saturation point
`n < 2^M ⟹ jsp87WeightColumn M n = jsp87Term n`. -/
theorem jsp87Series_eq_tsum_weightedLevels :
    jsp87Series = ∑' (k : ℕ), ((k : ℝ) * jsp87LevelSeries k) :=
  hasSum_weightedLevels.tsum_eq.symm

/-! ## 5. Each weighted level is irrational -/

theorem jsp87_weightedLevel_nonneg (k : ℕ) : 0 ≤ ((k : ℝ) * jsp87LevelSeries k) :=
  mul_nonneg (Nat.cast_nonneg _) (jsp87LevelSeries_nonneg k)

theorem jsp87_weightedLevel_pos {k : ℕ} (hk : 1 ≤ k) : 0 < ((k : ℝ) * jsp87LevelSeries k) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  exact mul_pos h1 (jsp87LevelSeries_pos k hk)

/-- **EVERY WEIGHTED LEVEL IS IRRATIONAL.**  So the reflection writes `S` as a
convergent sum of *provably irrational* numbers. -/
theorem jsp87_weightedLevel_irrational {k : ℕ} (hk : 1 ≤ k) :
    Irrational ((k : ℝ) * jsp87LevelSeries k) :=
  (jsp87LevelSeries_irrational k hk).natCast_mul (m := k) (Nat.ne_of_gt (by omega))

/-- The same, with the rational member `k = 0` (whose summand is `0`) removed. -/
theorem jsp87Series_eq_tsum_weightedLevels_onzero :
    jsp87Series = ∑' (k : ℕ), (if 1 ≤ k then ((k : ℝ) * jsp87LevelSeries k) else 0) := by
  refine jsp87Series_eq_tsum_weightedLevels.trans (tsum_congr fun (k : ℕ) => ?_)
  by_cases hk : 1 ≤ k
  · rw [ite_eq_left hk]
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0, ite_eq_right (by norm_num : ¬ (1 ≤ 0))]
    simp only [Nat.cast_zero, zero_mul]

private theorem summable_ite_zero_weighted (M : ℕ) :
    Summable (fun k : ℕ => if k = M then 0 else ((k : ℝ) * jsp87LevelSeries k)) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_weightedLevels
  · intro k
    show 0 ≤ (if k = M then (0 : ℝ) else ((k : ℝ) * jsp87LevelSeries k))
    by_cases h : k = M
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact jsp87_weightedLevel_nonneg k
  · intro k
    show (if k = M then (0 : ℝ) else ((k : ℝ) * jsp87LevelSeries k))
        ≤ ((k : ℝ) * jsp87LevelSeries k)
    by_cases h : k = M
    · rw [ite_eq_left h]
      exact jsp87_weightedLevel_nonneg k
    · rw [ite_eq_right h]

/-- **THE WEIGHTED PARTIAL SUM MISSES AT LEAST THE `K`-TH WEIGHTED LEVEL.** -/
theorem jsp87_weightPartial_le_sub (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k : ℝ) * jsp87LevelSeries k))
      ≤ jsp87Series - ((K : ℝ) * jsp87LevelSeries K) := by
  have h2 := Summable.tsum_eq_add_tsum_ite summable_weightedLevels K
  rw [← jsp87Series_eq_tsum_weightedLevels] at h2
  have h3 : ∑' (k : ℕ), (if k = K then 0 else ((k : ℝ) * jsp87LevelSeries k))
      ≥ ∑ k ∈ Finset.range K, ((k : ℝ) * jsp87LevelSeries k) := by
    have hle := Summable.sum_le_tsum (Finset.range K)
      (fun i _ => by
        by_cases h : i = K
        · rw [ite_eq_left h]
        · rw [ite_eq_right h]
          exact jsp87_weightedLevel_nonneg i)
      (summable_ite_zero_weighted K)
    refine le_trans ?_ hle
    refine Finset.sum_le_sum fun k hk => ?_
    have hkK : k ≠ K := by
      have hlt : k < K := Finset.mem_range.mp hk
      intro h
      rw [h] at hlt
      exact (Nat.lt_irrefl K) hlt
    rw [ite_eq_right hkK]
  linarith

/-- **ONE STEP OF THE WEIGHTED ROWS IS STRICTLY INCREASING** (`M ≥ 1`, where the
added weight `M` is nonzero). -/
theorem jsp87_weightPartial_succ {M : ℕ} (hM : 1 ≤ M) :
    jsp87WeightPartial M < jsp87WeightPartial (M + 1) := by
  have hpos := jsp87_weightedLevel_pos (k := M) hM
  simp only [jsp87WeightPartial, Finset.sum_range_succ]
  linarith

/-- The weighted rows are monotone in the height. -/
theorem jsp87_weightPartial_mono {M N : ℕ} (hMN : M ≤ N) :
    jsp87WeightPartial M ≤ jsp87WeightPartial N := by
  simp only [jsp87WeightPartial]
  have hsub : ∀ k ∈ Finset.range M, k ∈ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (by
      have hk' := Finset.mem_range.mp hk
      omega)
  have hle : (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87LevelSeries k))
      ≤ ∑ k ∈ Finset.range N, ((k : ℝ) * jsp87LevelSeries k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => ?_)
    exact jsp87_weightedLevel_nonneg k
  exact hle

/-- **THE WEIGHTED ROWS ARE STRICTLY INCREASING FROM `M = 1` ON.** -/
theorem jsp87_weightPartial_strictMono' {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N) :
    jsp87WeightPartial M < jsp87WeightPartial N :=
  (jsp87_weightPartial_succ hM).trans_le (jsp87_weightPartial_mono (by omega))

/-- Every weighted partial sum past `M = 2` is positive. -/
theorem jsp87_weightPartial_pos {M : ℕ} (hM : 2 ≤ M) : 0 < jsp87WeightPartial M := by
  simp only [jsp87WeightPartial]
  refine lt_of_lt_of_le (jsp87_weightedLevel_pos (k := 1) (by norm_num)) ?_
  exact Finset.single_le_sum (s := Finset.range M)
    (f := fun k : ℕ => ((k : ℝ) * jsp87LevelSeries k))
    (fun i _ => jsp87_weightedLevel_nonneg i) (Finset.mem_range.mpr (by omega))

/-! ## 6. The level series partition the unit interval -/

/-- **THE LEVEL COUNT AT `n`.**  Exactly one level contains `n`, so the truncated
level count is the indicator `[ω n < M]`. -/
theorem jsp87_levelCount (M n : ℕ) :
    ∑ k ∈ Finset.range M, jsp87Level k n = if omega n < M then 1 else 0 := by
  rcases Nat.lt_or_ge (omega n) M with hM | hM
  · have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
      intro a ha
      exact Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_of_lt hM))
    have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range (omega n + 1) →
        jsp87Level k n = 0 := by
      intro k _ hna
      have hna' : ¬ (k < omega n + 1) := fun hh => hna (Finset.mem_range.mpr hh)
      have hstep : omega n + 1 ≤ k := Nat.le_of_not_gt hna'
      have hne : omega n ≠ k := by
        intro hk
        have : omega n + 1 ≤ omega n := by rwa [← hk] at hstep
        exact (Nat.lt_irrefl (omega n)) (Nat.lt_succ_self _ |>.trans_le this)
      exact jsp87Level_eq_zero_of_omega_ne hne
    have hswap : (∑ k ∈ Finset.range (omega n + 1), jsp87Level k n)
        = ∑ k ∈ Finset.range M, jsp87Level k n :=
      Finset.sum_subset hsub hzero
    have hinner : (∑ k ∈ Finset.range (omega n + 1), jsp87Level k n) = 1 := by
      rw [Finset.sum_eq_single (omega n) (by
            intro b _ hb
            exact jsp87Level_eq_zero_of_omega_ne (Ne.symm hb)) (by simp [Finset.mem_range])]
      exact jsp87Level_eq_one_of_omega_eq rfl
    rw [← hswap, hinner, ite_eq_left hM]
  · have hzero : ∀ k ∈ Finset.range M, jsp87Level k n = 0 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hne : omega n ≠ k := by
        intro hkeq
        have hlt' : k < omega n := hk'.trans_le hM
        exact (Nat.lt_irrefl k) (hkeq ▸ hlt')
      exact jsp87Level_eq_zero_of_omega_ne hne
    rw [Finset.sum_eq_zero hzero, ite_eq_right (Nat.not_lt.mpr hM)]

/-- **THE UNWEIGHTED COLUMN AT `n`.**  It is an indicator, weighted by `2^-(n+1)`. -/
noncomputable def jsp87LevelColumn (M n : ℕ) : ℝ :=
  ((∑ k ∈ Finset.range M, jsp87Level k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

private theorem cast_sum_level (M n : ℕ) :
    ((∑ k ∈ Finset.range M, jsp87Level k n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range M, ((jsp87Level k n : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]

/-- The level count, read in `ℝ`. -/
theorem jsp87_levelCount_cast (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((jsp87Level k n : ℕ) : ℝ))
      = ((if omega n < M then 1 else 0 : ℕ) : ℝ) := by
  rw [← Nat.cast_sum, jsp87_levelCount]

theorem jsp87LevelColumn_nonneg (M n : ℕ) : 0 ≤ jsp87LevelColumn M n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

theorem jsp87LevelColumn_le_bit (M n : ℕ) :
    jsp87LevelColumn M n ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
  unfold jsp87LevelColumn
  rw [cast_sum_level, jsp87_levelCount_cast]
  rcases Nat.lt_or_ge (omega n) M with hM | hM
  · rw [ite_eq_left hM, Nat.cast_one, one_mul]
  · rw [ite_eq_right (Nat.not_lt.mpr hM)]
    simp only [Nat.cast_zero, zero_mul]
    positivity

theorem jsp87LevelColumn_eq_bit {M n : ℕ} (hM : 1 ≤ M) (hn : n < 2 ^ M) :
    jsp87LevelColumn M n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hωlt : omega n < M := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, omega_zero]
      have : 0 < M := hM
      omega
    · exact omega_lt_of_lt_two_pow hn0 hn
  unfold jsp87LevelColumn
  rw [cast_sum_level, jsp87_levelCount_cast, ite_eq_left hωlt, Nat.cast_one, one_mul]

private theorem summable_bit_two_pow : Summable (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) :=
  (summable_bitTerm_one 0).congr fun n => by simp

private theorem tsum_bit_two_pow : (∑' (n : ℕ), ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  simpa only [one_mul] using tsum_bitTerm_one_zero

theorem summable_jsp87LevelColumn (M : ℕ) : Summable (jsp87LevelColumn M) :=
  Summable.of_nonneg_of_le (fun n => jsp87LevelColumn_nonneg M n)
    (fun n => jsp87LevelColumn_le_bit M n) summable_bit_two_pow

/-- **THE UNWEIGHTED ROW PARTIAL SUM.** -/
noncomputable def jsp87LevelPartial (M : ℕ) : ℝ := ∑ k ∈ Finset.range M, jsp87LevelSeries k

/-- **THE UNWEIGHTED FINITE INTERCHANGE.** -/
theorem jsp87_levelPartial_eq_tsum (M : ℕ) :
    (∑ k ∈ Finset.range M, jsp87LevelSeries k) = ∑' (n : ℕ), jsp87LevelColumn M n := by
  have hfin : (∑' (n : ℕ), ∑ k ∈ Finset.range M, jsp87BitTerm (fun m => jsp87Level k m) n)
      = ∑ k ∈ Finset.range M, ∑' (n : ℕ), jsp87BitTerm (fun m => jsp87Level k m) n := by
    refine Summable.tsum_finsetSum fun i _ => ?_
    exact summable_jsp87BitTerm (fun m => jsp87Level i m) (fun m => jsp87Level_le i m)
  have hrhs : (∑ k ∈ Finset.range M, ∑' (n : ℕ), jsp87BitTerm (fun m => jsp87Level k m) n)
      = ∑ k ∈ Finset.range M, jsp87LevelSeries k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold jsp87LevelSeries jsp87BinarySeries
    exact rfl
  have hlhs : (∑' (n : ℕ), ∑ k ∈ Finset.range M, jsp87BitTerm (fun m => jsp87Level k m) n)
      = ∑' (n : ℕ), jsp87LevelColumn M n := by
    refine tsum_congr fun n => ?_
    unfold jsp87LevelColumn
    calc (∑ k ∈ Finset.range M, jsp87BitTerm (fun m => jsp87Level k m) n)
        = ∑ k ∈ Finset.range M, (((jsp87Level k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := rfl
      _ = ((∑ k ∈ Finset.range M, (jsp87Level k n : ℕ) : ℕ) : ℝ)
          * ((2 : ℝ) ^ (n + 1))⁻¹ := by
        rw [cast_sum_level, Finset.sum_mul]
  calc (∑ k ∈ Finset.range M, jsp87LevelSeries k)
      = ∑ k ∈ Finset.range M, ∑' (n : ℕ), jsp87BitTerm (fun m => jsp87Level k m) n := hrhs.symm
    _ = ∑' (n : ℕ), ∑ k ∈ Finset.range M, jsp87BitTerm (fun m => jsp87Level k m) n := hfin.symm
    _ = ∑' (n : ℕ), jsp87LevelColumn M n := hlhs

/-- **THE LEVEL PARTIAL SUMS NEVER OVERSHOOT `1`.** -/
theorem jsp87_levelPartial_le_one (M : ℕ) : jsp87LevelPartial M ≤ 1 := by
  have h' := Summable.tsum_le_tsum (fun n => jsp87LevelColumn_le_bit M n)
    (summable_jsp87LevelColumn M) summable_bit_two_pow
  rw [tsum_bit_two_pow] at h'
  exact (jsp87_levelPartial_eq_tsum M).trans_le h'

/-- **THE LEVEL PARTIAL SUM DOMINATES THE GEOMETRIC PARTIAL SUM BELOW `n = 2^M`.** -/
theorem jsp87_levelPartial_ge_colPartial {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (2 ^ M), ((2 : ℝ) ^ (n + 1))⁻¹) ≤ jsp87LevelPartial M := by
  have hmin : ∀ n ∈ Finset.range (2 ^ M), jsp87LevelColumn M n = ((2 : ℝ) ^ (n + 1))⁻¹ :=
    fun n hn => jsp87LevelColumn_eq_bit hM (Finset.mem_range.mp hn)
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ M))
    (fun i _ => jsp87LevelColumn_nonneg M i) (summable_jsp87LevelColumn M)
  calc (∑ n ∈ Finset.range (2 ^ M), ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑ n ∈ Finset.range (2 ^ M), jsp87LevelColumn M n := (Finset.sum_congr rfl hmin).symm
    _ ≤ ∑' (n : ℕ), jsp87LevelColumn M n := hsum
    _ = jsp87LevelPartial M := (jsp87_levelPartial_eq_tsum M).symm

private theorem dist_one_eq (x : ℝ) : dist x 1 = |x - 1| :=
  by rw [dist_eq_norm, Real.norm_eq_abs]

/-- **THE LEVEL PARTIAL SUMS CONVERGE TO `1`.**  They are squeezed between the
geometric partial sums below `n = 2^M` (which tend to `1`) and `1` itself. -/
theorem tendsto_jsp87_levelPartial :
    Tendsto jsp87LevelPartial atTop (nhds 1) := by
  have hge : Tendsto (fun M => ∑ n ∈ Finset.range (2 ^ M), ((2 : ℝ) ^ (n + 1))⁻¹)
      atTop (nhds 1) := by
    have hg0 : Tendsto (fun N => ∑ n ∈ Finset.range N, ((2 : ℝ) ^ (n + 1))⁻¹)
        atTop (nhds 1) := by
      have hval : (1 : ℝ) = ∑' (n : ℕ), ((2 : ℝ) ^ (n + 1))⁻¹ := tsum_bit_two_pow.symm
      rw [hval]
      exact summable_bit_two_pow.hasSum.tendsto_sum_nat
    exact hg0.comp pow_two_tendsto_top
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hge ε hε
  refine ⟨N + 1, ?_⟩
  intro M hM
  have hM1 : 1 ≤ M := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le N)) hM
  have hMN : N ≤ M := Nat.le_trans (Nat.le_add_right N 1) hM
  have hlo := jsp87_levelPartial_ge_colPartial hM1
  have hhi := jsp87_levelPartial_le_one M
  have hdist := hN _ hMN
  rw [dist_one_eq] at hdist
  have hhi' : jsp87LevelPartial M - 1 ≤ 0 := by linarith
  have hge' : (∑ n ∈ Finset.range (2 ^ M), ((2 : ℝ) ^ (n + 1))⁻¹) - 1 ≤ 0 := by linarith
  rw [abs_of_nonpos hge'] at hdist
  rw [dist_one_eq, abs_of_nonpos hhi']
  linarith

/-- **THE LEVEL SERIES IS A `HasSum` FOR `1`.** -/
theorem hasSum_jsp87LevelSeries : HasSum jsp87LevelSeries 1 := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (f := jsp87LevelSeries)
    (fun k => jsp87LevelSeries_nonneg k) 1).2 ?_
  exact tendsto_jsp87_levelPartial

/-- **THE LEVEL SERIES IS SUMMABLE.** -/
theorem summable_jsp87LevelSeries : Summable jsp87LevelSeries :=
  ⟨1, hasSum_jsp87LevelSeries⟩

/-- **THE PARTITION OF UNITY — THE SECOND HEADLINE OF THIS ROUND.**

```
∑' k, jsp87LevelSeries k = 1
```

Every positive integer lies in exactly one level set of `ω`, so the level
indicators sum to `1` pointwise; reading that identity in base `2` says that the
countable family `{L k}` **partitions the interval `[0,1]`**.  This is the
unweighted mirror image of `jsp87Series_eq_tsum_weightedLevels`, and it is the
first time the level series have been proved to sum to anything at all. -/
theorem jsp87_tsum_levelSeries_eq_one : (∑' (k : ℕ), jsp87LevelSeries k) = 1 :=
  hasSum_jsp87LevelSeries.tsum_eq

private theorem summable_ite_zero_level (M : ℕ) :
    Summable (fun k : ℕ => if k = M then 0 else jsp87LevelSeries k) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_jsp87LevelSeries
  · intro k
    show 0 ≤ (if k = M then (0 : ℝ) else jsp87LevelSeries k)
    by_cases h : k = M
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact jsp87LevelSeries_nonneg k
  · intro k
    show (if k = M then (0 : ℝ) else jsp87LevelSeries k) ≤ jsp87LevelSeries k
    by_cases h : k = M
    · rw [ite_eq_left h]
      exact jsp87LevelSeries_nonneg k
    · rw [ite_eq_right h]

/-- **THE PARTITION IS NESTED**: the first `K` levels miss at least the whole `K`-th
level. -/
theorem jsp87_levelPartial_le_sub_one (K : ℕ) :
    (∑ k ∈ Finset.range K, jsp87LevelSeries k) ≤ 1 - jsp87LevelSeries K := by
  have h2 : (1 : ℝ) = jsp87LevelSeries K + ∑' (k : ℕ), (if k = K then 0 else jsp87LevelSeries k) := by
    rw [← jsp87_tsum_levelSeries_eq_one]
    exact Summable.tsum_eq_add_tsum_ite summable_jsp87LevelSeries K
  have h3 : ∑' (k : ℕ), (if k = K then 0 else jsp87LevelSeries k)
      ≥ ∑ k ∈ Finset.range K, jsp87LevelSeries k := by
    have hle := Summable.sum_le_tsum (Finset.range K)
      (fun i _ => by
        by_cases h : i = K
        · rw [ite_eq_left h]
        · rw [ite_eq_right h]
          exact jsp87LevelSeries_nonneg i)
      (summable_ite_zero_level K)
    refine le_trans ?_ hle
    refine Finset.sum_le_sum fun k hk => ?_
    have hkK : k ≠ K := by
      have hlt : k < K := Finset.mem_range.mp hk
      intro h
      rw [h] at hlt
      exact (Nat.lt_irrefl K) hlt
    rw [ite_eq_right hkK]
  linarith

/-- **THE `k ≥ 1` PART OF THE PARTITION IS EXACTLY `1/4`**: the level `k = 0`
(`ω n = 0`, i.e. `n = 0, 1`) carries the remaining three quarters. -/
theorem jsp87_tsum_levelSeries_tail_eq_quarter :
    (∑' (k : ℕ), (if 1 ≤ k then jsp87LevelSeries k else 0)) = 1 / 4 := by
  have h0 : (∑' (k : ℕ), jsp87LevelSeries k)
      = jsp87LevelSeries 0 + ∑' (k : ℕ), (if k = 0 then 0 else jsp87LevelSeries k) :=
    Summable.tsum_eq_add_tsum_ite summable_jsp87LevelSeries 0
  have h1 : (∑' (k : ℕ), (if k = 0 then 0 else jsp87LevelSeries k))
      = ∑' (k : ℕ), (if 1 ≤ k then jsp87LevelSeries k else 0) := by
    refine tsum_congr fun (k : ℕ) => ?_
    by_cases hk : 1 ≤ k
    · have hk0 : ¬ (k = 0) := by omega
      rw [ite_eq_right hk0, ite_eq_left hk]
    · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      rw [hk0, ite_eq_left rfl, ite_eq_right (by norm_num : ¬ (1 ≤ 0))]
  have hsum := h0
  rw [jsp87_tsum_levelSeries_eq_one, h1, jsp87LevelSeries_zero] at hsum
  linarith

end JSP87