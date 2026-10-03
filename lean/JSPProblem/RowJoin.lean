/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LevelSeries
import Mathlib.Tactic

/-!
# JSP-000087 : the row form of the layer-cake join, and the convergence rate of the rows

Round 103 (`LevelSeries.lean`) proved the **column** half of the layer-cake join

```
jsp87Series + 1 = ∑' n, (ω n + 1) · 2^-(n+1)                     jsp87Series_add_one_eq_tsum_columns
```

and left the **row** half as an open step, on the (incorrect) ground that "this Mathlib
version has **no** Fubini lemma for `ℝ`".  That is false: `Summable.tsum_finsetSum`

```
(∀ i ∈ s, Summable (f i)) → ∑' b, ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' b, f i b
```

interchanges a *finite* outer sum with a `tsum` over ℝ unconditionally, and
`Summable.sum_le_tsum`, `Summable.tsum_le_tsum`, `Summable.subtype` and
`hasSum_iff_tendsto_nat_of_nonneg` supply the rest of the machinery.  (A full Fubini
for two *infinite* sums over ℝ really is absent — `Summable.tsum_comm` does not exist
here, only the `ENNReal` version — but the row form needs only the finite version.)

This module closes the gap and delivers the row form

```
jsp87Series + 1 = ∑' k, jsp87AtLeastSeries k                     jsp87Series_add_one_eq_tsum_rows
```

together with its quantitative content.

## 1. The truncated layer count (§1)

* `jsp87_cumul_count` : `∑_{k<M} [k ≤ ω n] = min (ω n + 1) M` — the number of layers
  of `n` retained by truncation at `M` (the `+ 1` is the layer `k = 0`);
* `jsp87MinColumn M n` : the `M`-truncated column, `= min (ω n + 1) M · 2^-(n+1)`;
* `jsp87_layerSum_min` : the `M` rows, read at the single cut point `n`, sum to the
  truncated column;
* `jsp87MinColumn_eq_column` : **the saturation point** — for `M ≥ 1`, every column
  with `n < 2 ^ M` is already complete at height `M`.

## 2. The finite interchange (§2)

* `jsp87_rowPartial_eq_tsum` : **the row form at finite height**
  `∑_{k<M} A k = ∑' n, jsp87MinColumn M n` — exact, no limit argument;
* `jsp87_rowPartial_le_add_one` : `∑_{k<M} A k ≤ S + 1`;
* `jsp87_colPartial_le_rowPartial` : `∑_{n<2^M} column n ≤ ∑_{k<M} A k`.

## 3. The convergence rate (§3)

* `jsp87_rowGap_nonneg`, `jsp87_rowGap_le_tail` : the gap `S + 1 − ∑_{k<M} A k` lies
  between `0` and the column tail beyond `n = 2^M`;
* `tendsto_jsp87_rowGap`, `tendsto_jsp87_rowPartial` : the gap tends to `0`, so the
  rows converge to `S + 1`;
* `hasSum_jsp87AtLeastSeries`, `summable_jsp87AtLeastSeries` : the row series is a
  `HasSum` (hence a `Summable`) with value `S + 1`.

## 4. The row form, and the irrational part of the rows (§4)

* `jsp87Series_add_one_eq_tsum_rows` : **THE ROW FORM**, the headline of this round;
* `jsp87_rowPartial_strictMono`, `jsp87_rowPartial_pos` : the rows are strictly
  increasing (every `A k` is positive, `jsp87AtLeastSeries_pos`), so the row series
  is a sum of strictly positive terms;
* `jsp87Series_sub_quarter_eq_tsum_rows` : **`S − 1/4 = ∑' k, (2 ≤ k) → A k`** — the
  Erdős series is the quarter `A 1 = 1/4` plus a convergent sum of numbers that are
  *each* provably irrational (`jsp87AtLeastSeries_irrational`), the two rational rows
  `A 0 = 1`, `A 1 = 1/4` being exactly the exceptions.

## Why this does not close the gate

As documented in round 83, a countable sum of irrational numbers need not be
irrational (`jsp87Series_rational_of_atLeast_periodic`), and only `k ≥ 2` gives an
irrational row.  The row form therefore *sharpens the shape* of the problem — `S` is
now literally the `k`-indexed sum of the round-83 families, with the two trivial rows
peeled off — but the gate still waits on the aperiodicity of the binary digits of `S`
(round 41's `jsp87_digit_not_eventuallyPeriodic`, equivalently round 64's aperiodicity
of the doubling orbit `Int.fract (θ N)`).
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. Counting the layers that survive truncation -/

private theorem sum_range_one (K : ℕ) : ∑ _k ∈ Finset.range K, (1 : ℕ) = K := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]

/-- **THE TRUNCATED LAYER COUNT.**  `∑_{k<M} [k ≤ ω n]` — the number of layers at `n`
retained when the layer index is cut at `M` — equals `min (ω n + 1) M`.

There are `ω n + 1` layers at `n` in total (indices `0, …, ω n`), so truncating at
`M` keeps the first `M` of them. -/
theorem jsp87_cumul_count (M n : ℕ) :
    ∑ k ∈ Finset.range M, jsp87AtLeast k n = min (omega n + 1) M := by
  by_cases hM : omega n + 1 ≤ M
  · -- the window `M` contains every layer of `n`: count them all
    have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
      intro a ha
      exact Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) hM)
    have hzero : ∀ a ∈ Finset.range M, a ∉ Finset.range (omega n + 1) →
        jsp87AtLeast a n = 0 := by
      intro a _ hna
      have hna' : ¬ (a < omega n + 1) := fun hh => hna (Finset.mem_range.mpr hh)
      have hstep : omega n + 1 ≤ a := Nat.le_of_not_gt hna'
      exact (jsp87AtLeast_eq_zero_iff a n).mpr
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hstep)
    have hall : ∀ k ∈ Finset.range (omega n + 1), jsp87AtLeast k n = 1 := by
      intro k hk
      have hk' : k < omega n + 1 := Finset.mem_range.mp hk
      have hle : k ≤ omega n := Nat.le_of_lt_succ hk'
      simp only [jsp87AtLeast, hle, ↓reduceIte]
    rw [← Finset.sum_subset hsub hzero]
    calc (∑ k ∈ Finset.range (omega n + 1), jsp87AtLeast k n)
        = ∑ _k ∈ Finset.range (omega n + 1), (1 : ℕ) := Finset.sum_congr rfl hall
      _ = omega n + 1 := sum_range_one _
      _ = min (omega n + 1) M := (Nat.min_eq_left hM).symm
  · -- the window `M` is short of the layers of `n`: every layer of `n` counts
    have hM2 : M < omega n + 1 := Nat.lt_of_not_ge hM
    have hall : ∀ k ∈ Finset.range M, jsp87AtLeast k n = 1 := by
      intro k hk
      have hk' : k < M := Finset.mem_range.mp hk
      have hle : k ≤ omega n :=
        Nat.le_trans (Nat.le_of_lt hk') (Nat.lt_succ_iff.mp hM2)
      simp only [jsp87AtLeast, hle, ↓reduceIte]
    calc (∑ k ∈ Finset.range M, jsp87AtLeast k n)
        = ∑ _k ∈ Finset.range M, (1 : ℕ) := Finset.sum_congr rfl hall
      _ = M := sum_range_one _
      _ = min (omega n + 1) M := (Nat.min_eq_right (Nat.le_of_lt hM2)).symm

/-- The same count, cast to ℝ — the form the columns use. -/
theorem jsp87_cumul_count_cast (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((jsp87AtLeast k n : ℕ) : ℝ)) = ((min (omega n + 1) M : ℕ) : ℝ) := by
  have h : (∑ k ∈ Finset.range M, ((jsp87AtLeast k n : ℕ) : ℝ))
      = ((∑ k ∈ Finset.range M, jsp87AtLeast k n : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
  rw [h, jsp87_cumul_count]

/-! ## 2. The truncated column -/

/-- **THE `M`-TRUNCATED COLUMN AT `n`**: the surviving `min (ω n + 1) M` layers of `n`,
each of weight `2^-(n+1)`.  Once `M ≥ ω n + 1` this is the whole column
`jsp87LayerColumn n`. -/
noncomputable def jsp87MinColumn (M n : ℕ) : ℝ :=
  ((min (omega n + 1) M : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

theorem jsp87MinColumn_nonneg (M n : ℕ) : 0 ≤ jsp87MinColumn M n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE TRUNCATED LAYER SUM AT `n`.**  The `M` rows, read off at the single cut point
`n`, are exactly the truncated column. -/
theorem jsp87_layerSum_min (M n : ℕ) :
    ∑ k ∈ Finset.range M, jsp87LayerTerm k n = jsp87MinColumn M n := by
  unfold jsp87MinColumn
  calc (∑ k ∈ Finset.range M, jsp87LayerTerm k n)
      = ∑ k ∈ Finset.range M, ((jsp87AtLeast k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
        Finset.sum_congr rfl (fun k _ => rfl)
    _ = ((∑ k ∈ Finset.range M, ((jsp87AtLeast k n : ℕ) : ℝ))) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
        (Finset.sum_mul _ _ _).symm
    _ = ((min (omega n + 1) M : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
        rw [jsp87_cumul_count_cast]

/-- Truncation only removes layers. -/
theorem jsp87MinColumn_le_column (M n : ℕ) :
    jsp87MinColumn M n ≤ jsp87LayerColumn n := by
  have h1 : ((min (omega n + 1) M : ℕ) : ℝ) ≤ ((omega n + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.min_le_left _ _)
  have h2 : 0 ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  have h3 : jsp87MinColumn M n
      = ((min (omega n + 1) M : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := rfl
  have h4 : jsp87LayerColumn n = ((omega n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := rfl
  rw [h3, h4]
  exact mul_le_mul_of_nonneg_right h1 h2

/-- `ω n < M` as soon as `0 < n < 2 ^ M`: every layer of `n` has index below `M`. -/
theorem omega_lt_of_lt_two_pow {n M : ℕ} (hn : 0 < n) (hM : n < 2 ^ M) : omega n < M := by
  have h1 : 2 ^ omega n ≤ n := two_pow_omega_le hn
  have h2 : 2 ^ omega n < 2 ^ M := Nat.lt_of_le_of_lt h1 hM
  rwa [pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)] at h2

/-- **THE SATURATION POINT.**  For `M ≥ 1`, every column with `n < 2 ^ M` is already
*complete* at height `M`: all of its `ω n + 1` layers have index `≤ ω n < M`.  Equently,
everything the truncation can delete lies beyond `n = 2 ^ M`. -/
theorem jsp87MinColumn_eq_column (M n : ℕ) (hM : 1 ≤ M) (hn : n < 2 ^ M) :
    jsp87MinColumn M n = jsp87LayerColumn n := by
  have hmin : min (omega n + 1) M = omega n + 1 := by
    rcases Nat.lt_or_ge n 1 with h | hn1
    · have hn0 : n = 0 := Nat.lt_one_iff.mp h
      subst hn0
      simp only [omega_zero, Nat.zero_add]
      exact Nat.min_eq_left hM
    · exact Nat.min_eq_left (Nat.succ_le_of_lt (omega_lt_of_lt_two_pow hn1 hn))
  unfold jsp87MinColumn
  rw [hmin]
  rfl

/-- Each truncated column is dominated by the full column series, hence summable. -/
theorem summable_jsp87MinColumn (M : ℕ) : Summable (jsp87MinColumn M) :=
  Summable.of_nonneg_of_le (fun n => jsp87MinColumn_nonneg M n)
    (fun n => jsp87MinColumn_le_column M n) (summable_jsp87LayerColumn)

/-! ## 3. The finite interchange: the rows are one column series -/

/-- **THE ROW PARTIAL SUM** `P M = ∑_{k<M} A k`, with `A k = jsp87AtLeastSeries k`. -/
noncomputable def jsp87RowPartial (M : ℕ) : ℝ := ∑ k ∈ Finset.range M, jsp87AtLeastSeries k

/-- **THE FINITE INTERCHANGE.**  `∑_{k<M} A k`, the sum of the first `M` rows, is the
`tsum` of the truncated columns: the row form of the join holds *exactly*, at every
finite height, with no limit argument.  This is the step `LevelSeries.lean` §4 believed
unavailable. -/
theorem jsp87_rowPartial_eq_tsum (M : ℕ) :
    (∑ k ∈ Finset.range M, jsp87AtLeastSeries k) = ∑' n, jsp87MinColumn M n := by
  have hfin : (∑' n, ∑ k ∈ Finset.range M, jsp87LayerTerm k n)
      = ∑ k ∈ Finset.range M, ∑' n, jsp87LayerTerm k n := by
    refine Summable.tsum_finsetSum fun i _ => ?_
    exact summable_jsp87BitTerm (fun n => jsp87AtLeast i n) (fun n => jsp87AtLeast_le i n)
  have hrhs : (∑ k ∈ Finset.range M, ∑' n, jsp87LayerTerm k n)
      = ∑ k ∈ Finset.range M, jsp87AtLeastSeries k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold jsp87AtLeastSeries jsp87BinarySeries
    exact tsum_congr fun n => rfl
  have hlhs : (∑' n, ∑ k ∈ Finset.range M, jsp87LayerTerm k n)
      = ∑' n, jsp87MinColumn M n := by
    refine tsum_congr fun n => ?_
    exact jsp87_layerSum_min M n
  calc (∑ k ∈ Finset.range M, jsp87AtLeastSeries k)
      = ∑ k ∈ Finset.range M, ∑' n, jsp87LayerTerm k n := hrhs.symm
    _ = ∑' n, ∑ k ∈ Finset.range M, jsp87LayerTerm k n := hfin.symm
    _ = ∑' n, jsp87MinColumn M n := hlhs

/-- **THE ROWS NEVER OVERSHOOT.**  `∑_{k<M} A k ≤ S + 1` for every `M`. -/
theorem jsp87_rowPartial_le_add_one (M : ℕ) :
    (∑ k ∈ Finset.range M, jsp87AtLeastSeries k) ≤ jsp87Series + 1 := by
  rw [jsp87_rowPartial_eq_tsum]
  have h := Summable.tsum_le_tsum (fun n => jsp87MinColumn_le_column M n)
    (summable_jsp87MinColumn M) (summable_jsp87LayerColumn)
  rw [← jsp87Series_add_one_eq_tsum_columns] at h
  exact h

/-- **THE COLUMN SERIES IS PARTIALLY SUMMED BY THE ROWS.**  Every partial sum of the
column series is at most `S + 1`. -/
theorem jsp87_colPartial_le_add_one (N : ℕ) :
    (∑ n ∈ Finset.range N, jsp87LayerColumn n) ≤ jsp87Series + 1 := by
  have h := Summable.sum_le_tsum (Finset.range N) (fun i _ => jsp87LayerColumn_nonneg i)
    (summable_jsp87LayerColumn)
  rwa [← jsp87Series_add_one_eq_tsum_columns] at h

/-- **THE EXACT COMPARISON AT THE SATURATION POINT.**  The columns below `n = 2^M` are
*complete*, so their sum is bounded by the first `M` rows. -/
theorem jsp87_colPartial_le_rowPartial (M : ℕ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (2 ^ M), jsp87LayerColumn n)
      ≤ ∑ k ∈ Finset.range M, jsp87AtLeastSeries k := by
  have hmin : ∀ n ∈ Finset.range (2 ^ M), jsp87MinColumn M n = jsp87LayerColumn n :=
    fun n hn => jsp87MinColumn_eq_column M n hM (Finset.mem_range.mp hn)
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ M))
    (fun i _ => jsp87MinColumn_nonneg M i) (summable_jsp87MinColumn M)
  calc (∑ n ∈ Finset.range (2 ^ M), jsp87LayerColumn n)
      = ∑ n ∈ Finset.range (2 ^ M), jsp87MinColumn M n := (Finset.sum_congr rfl hmin).symm
    _ ≤ ∑' n, jsp87MinColumn M n := hsum
    _ = ∑ k ∈ Finset.range M, jsp87AtLeastSeries k := (jsp87_rowPartial_eq_tsum M).symm

/-! ## 4. The gap, and its convergence -/

/-- **THE COLUMN TAIL IS NONNEGATIVE.** -/
theorem jsp87_colTail_nonneg (N : ℕ) :
    0 ≤ jsp87Series + 1 - ∑ n ∈ Finset.range N, jsp87LayerColumn n :=
  le_trans (le_refl _) (by
    have h := jsp87_colPartial_le_add_one N
    linarith)

/-- **THE GAP IS NONNEGATIVE.**  `P M ≤ S + 1` again, phrased as a gap. -/
theorem jsp87_rowGap_nonneg (M : ℕ) :
    0 ≤ jsp87Series + 1 - ∑ k ∈ Finset.range M, jsp87AtLeastSeries k := by
  have h := jsp87_rowPartial_le_add_one M
  linarith

/-- **THE GAP IS BOUNDED BY THE COLUMN TAIL BEYOND THE SATURATION POINT.**  The rows
miss at most what the columns have not contributed past `n = 2 ^ M`. -/
theorem jsp87_rowGap_le_tail (M : ℕ) (hM : 1 ≤ M) :
    jsp87Series + 1 - ∑ k ∈ Finset.range M, jsp87AtLeastSeries k
      ≤ jsp87Series + 1 - ∑ n ∈ Finset.range (2 ^ M), jsp87LayerColumn n := by
  have hle := jsp87_colPartial_le_rowPartial M hM
  linarith

private theorem dist_zero_eq (x : ℝ) : dist x 0 = |x| := by
  rw [dist_eq_norm, Real.norm_eq_abs]
  simp

/-- **THE GAP TENDSTO `0`.**  Hence the rows are a `HasSum` for the value `S + 1`. -/
theorem tendsto_jsp87_rowGap :
    Tendsto (fun M => jsp87Series + 1 - ∑ k ∈ Finset.range M, jsp87AtLeastSeries k)
      atTop (nhds 0) := by
  have h1 : Tendsto (fun _ : ℕ => jsp87Series + 1) atTop (nhds (jsp87Series + 1)) :=
    tendsto_const_nhds
  have h2 : Tendsto (fun N => ∑ n ∈ Finset.range N, jsp87LayerColumn n)
      atTop (nhds (jsp87Series + 1)) := hasSum_jsp87LayerColumn.tendsto_sum_nat
  have hcol : Tendsto (fun N => jsp87Series + 1 - ∑ n ∈ Finset.range N, jsp87LayerColumn n)
      atTop (nhds 0) := by
    simpa only [sub_self] using h1.sub h2
  have htail : Tendsto
      (fun M => jsp87Series + 1 - ∑ n ∈ Finset.range (2 ^ M), jsp87LayerColumn n)
      atTop (nhds 0) := by
    have hpow : Tendsto (fun M : ℕ => 2 ^ M) atTop atTop :=
      Filter.tendsto_atTop.2 fun M => by
        filter_upwards [eventually_ge_atTop M] with x hx
        exact Nat.le_trans hx (Nat.le_of_lt (Nat.lt_two_pow_self (n := x)))
    exact hcol.comp hpow
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail ε hε
  refine ⟨N + 1, ?_⟩
  intro M hM
  have hM1 : 1 ≤ M := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le N)) hM
  have hMN : N ≤ M := Nat.le_trans (Nat.le_add_right N 1) hM
  have hlt := jsp87_rowGap_le_tail M hM1
  have hg0 := jsp87_rowGap_nonneg M
  have ht0 := jsp87_colTail_nonneg (2 ^ M)
  have hdist := hN _ hMN
  rw [dist_zero_eq] at hdist
  rw [abs_of_nonneg ht0] at hdist
  rw [dist_zero_eq, abs_of_nonneg hg0]
  exact lt_of_le_of_lt hlt hdist

/-- **THE ROW PARTIAL SUMS CONVERGE TO `S + 1`.** -/
theorem tendsto_jsp87_rowPartial :
    Tendsto jsp87RowPartial atTop (nhds (jsp87Series + 1)) := by
  have h3 : Tendsto (fun M => (jsp87Series + 1)
        - (jsp87Series + 1 - ∑ k ∈ Finset.range M, jsp87AtLeastSeries k))
      atTop (nhds (jsp87Series + 1)) := by
    simpa only [sub_zero] using tendsto_jsp87_rowGap.const_sub (jsp87Series + 1)
  refine h3.congr' (f₂ := jsp87RowPartial) (Filter.Eventually.of_forall fun M => ?_)
  unfold jsp87RowPartial
  ring

/-- **THE ROW SERIES IS A `HasSum` FOR `S + 1`.** -/
theorem hasSum_jsp87AtLeastSeries : HasSum jsp87AtLeastSeries (jsp87Series + 1) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun k => jsp87AtLeastSeries_nonneg k) _).2 ?_
  exact tendsto_jsp87_rowPartial

/-- **THE ROW SERIES IS SUMMABLE.** -/
theorem summable_jsp87AtLeastSeries : Summable jsp87AtLeastSeries :=
  ⟨jsp87Series + 1, hasSum_jsp87AtLeastSeries⟩

/-- **THE ROWS CONVERGE UPWARD, STRICTLY.**  Every `A k` is positive
(`jsp87AtLeastSeries_pos`), so the row partial sums strictly increase. -/
theorem jsp87_rowPartial_succ (M : ℕ) : jsp87RowPartial M < jsp87RowPartial (M + 1) := by
  have hpos := jsp87AtLeastSeries_pos M
  simp only [jsp87RowPartial, Finset.sum_range_succ]
  linarith

theorem jsp87_rowPartial_strictMono : StrictMono jsp87RowPartial :=
  strictMono_of_lt_succ fun M _ => jsp87_rowPartial_succ M

/-- Every row partial sum with at least one row is positive. -/
theorem jsp87_rowPartial_pos (M : ℕ) (hM : 1 ≤ M) : 0 < jsp87RowPartial M := by
  simp only [jsp87RowPartial]
  refine lt_of_lt_of_le (jsp87AtLeastSeries_pos 0) ?_
  exact Finset.single_le_sum (s := Finset.range M) (f := jsp87AtLeastSeries)
    (fun i _ => jsp87AtLeastSeries_nonneg i) (Finset.mem_range.mpr (Nat.zero_lt_of_lt hM))

/-! ## 5. THE ROW FORM -/

/-- **THE ROW FORM OF THE LAYER-CAKE JOIN — THE HEADLINE OF THIS ROUND.**

`jsp87Series + 1 = ∑' k, jsp87AtLeastSeries k`, i.e. the Erdős series *plus one* is the
sum of the round-83 "at least `k`" series over the layer index.  Together with
`jsp87Series_add_one_eq_tsum_columns` (round 103) this identifies `S + 1` with the
double series `∑' n ∑' k [k ≤ ω n] 2^-(n+1)` in *both* orders, and shows the Erdős
series is a countable, convergent, integer-weighted combination of the level series
of round 83. -/
theorem jsp87Series_add_one_eq_tsum_rows :
    jsp87Series + 1 = ∑' k, jsp87AtLeastSeries k :=
  hasSum_jsp87AtLeastSeries.tsum_eq.symm

/-- The same statement with the row index shifted, in `HasSum` form. -/
theorem hasSum_jsp87AtLeastRows : HasSum jsp87AtLeastSeries (jsp87Series + 1) :=
  hasSum_jsp87AtLeastSeries

/-! ## 6. The irrational part of the rows -/

private theorem summable_ite_zero (M : ℕ) :
    Summable (fun k : ℕ => if k = M then 0 else jsp87AtLeastSeries k) := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_jsp87AtLeastSeries
  · intro k
    show 0 ≤ (if k = M then (0 : ℝ) else jsp87AtLeastSeries k)
    by_cases h : k = M
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact jsp87AtLeastSeries_nonneg k
  · intro k
    show (if k = M then (0 : ℝ) else jsp87AtLeastSeries k) ≤ jsp87AtLeastSeries k
    by_cases h : k = M
    · rw [ite_eq_left h]
      exact jsp87AtLeastSeries_nonneg k
    · rw [ite_eq_right h]

/-- **THE IRRATIONAL PART OF THE ROW SERIES.**  Peeling off the two rational rows
`A 0 = 1` and `A 1 = 1/4` from the row form leaves

`jsp87Series − 1/4 = ∑' k, if 2 ≤ k then A k else 0`,

a convergent sum of numbers each of which is provably irrational
(`jsp87AtLeastSeries_irrational`).  So the Erdős series is a rational quarter plus a
sum of irrationals, and the two exceptions are exactly `k = 0, 1`. -/
theorem jsp87Series_sub_quarter_eq_tsum_rows :
    jsp87Series - 1 / 4 = ∑' k, (if 2 ≤ k then jsp87AtLeastSeries k else 0) := by
  have hA := summable_jsp87AtLeastSeries
  have h0 : (∑' k, jsp87AtLeastSeries k)
      = jsp87AtLeastSeries 0 + ∑' k, (if k = 0 then 0 else jsp87AtLeastSeries k) :=
    Summable.tsum_eq_add_tsum_ite hA 0
  have h1 : (∑' k, (if k = 0 then 0 else jsp87AtLeastSeries k))
      = (if 1 = 0 then 0 else jsp87AtLeastSeries 1)
        + ∑' k, (if k = 1 then 0 else (if k = 0 then 0 else jsp87AtLeastSeries k)) :=
    Summable.tsum_eq_add_tsum_ite (summable_ite_zero 0) 1
  have h2 : (∑' k, (if k = 1 then 0 else (if k = 0 then 0 else jsp87AtLeastSeries k)))
      = ∑' k, (if 2 ≤ k then jsp87AtLeastSeries k else 0) := by
    refine tsum_congr fun k => ?_
    rcases Nat.lt_or_ge k 2 with h | h
    · rcases Nat.lt_or_ge k 1 with h0 | h1
      · have hk0 : k = 0 := Nat.lt_one_iff.mp h0
        rw [hk0, ite_eq_right (by norm_num : ¬ (0 = 1))]
        rw [ite_eq_left (by norm_num : (0 : ℕ) = 0)]
        rw [ite_eq_right (by norm_num : ¬ (2 ≤ 0))]
      · have hk1 : k = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h) h1
        rw [hk1, ite_eq_right (by norm_num : ¬ (1 = 0))]
        rw [ite_eq_left (by norm_num : (1 : ℕ) = 1)]
        rw [ite_eq_right (by norm_num : ¬ (2 ≤ 1))]
    · have hne1 : ¬ (k = 1) := by
        intro hk1
        rw [hk1] at h
        exact absurd h (by decide)
      have hne0 : ¬ (k = 0) := by
        intro hk0
        rw [hk0] at h
        exact absurd h (by decide)
      rw [ite_eq_right hne1, ite_eq_right hne0]
      rw [ite_eq_left h]
  rw [h1, h2] at h0
  have hA1 : (if 1 = 0 then (0 : ℝ) else jsp87AtLeastSeries 1) = 1 / 4 := by
    simp only [jsp87AtLeastSeries_one]
    norm_num
  have hS : jsp87Series - 1 / 4 = (jsp87Series + 1) - 5 / 4 := by ring
  rw [hS, jsp87Series_add_one_eq_tsum_rows, h0, jsp87AtLeastSeries_zero, hA1]
  ring

/-- Every member of the irrational part of the row series really is irrational — the
row form is a sum of provably irrational numbers, not merely of reals. -/
theorem jsp87_rowPart_irrational (k : ℕ) (hk : 2 ≤ k) :
    Irrational (jsp87AtLeastSeries k) :=
  jsp87AtLeastSeries_irrational k hk

end JSP87