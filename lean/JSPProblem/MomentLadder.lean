/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.WeightJoin
import Mathlib.Tactic

/-!
# JSP-000087 : the moment ladder of the Erdős series

Round 83 (`LevelSets.lean`) built the **level series** `L k = ∑' n, [ω n = k] · 2^-(n+1)`
and the **"at least" series** `A k = ∑' n, [k ≤ ω n] · 2^-(n+1)`, and classified both
(rounds 83, 104, 106 then supplied the joins).  Two facts about that pair were
never written down as theorems, and both are needed to see the *structure* of the
pair rather than the members of it:

* **§1 — the two families are one family and its tails.**  The exact complement
  `L 0 + L 1 + … + L (M−1) + A M = 1`, the finite tail-sum relation
  `A M − A (M+t) = ∑_{j<t} L (M+j)`, and the infinite form
  `A k = ∑' j, (if k ≤ j then L j else 0)`.  So the partition of unity
  `∑' k, L k = 1` (round 106) and the row sum `∑' k, A k = S + 1` (round 104) are
  the *same* statement read at the two ends of one sequence.  Consequences: the
  unweighted row partial sums `∑_{k<M} L k` are **irrational exactly for
  `M ≥ 2`** (round 83 classified `L k` and `A k`, never the partial sums), and
  `1 − ∑_{k<M} L k = A M` is **doubly exponentially small** (§2).

* **§3–§4 — the second-moment ladder.**  Round 106 proved `S = ∑' k, k · L k` by
  weighting the *level* indicators against the layer index.  Weighting the
  *"at least"* indicators against the same index gives the triangular numbers and
  hence the second moment:

  ```
  ∑' k, k · A k = ∑' n, (ω n (ω n + 1) / 2) · 2^-(n+1)          (the second moment)
  ∑' n, ω n ^ 2 · 2^-(n+1) + S = ∑' k, 2k · A k                 (the pure square moment)
  ```

  Because `∑_{k<M} k [k ≤ ω n]` is the truncated triangular number
  `tri (min (ω n + 1) M)`, the triangular column *saturates* at the same cut point
  `n = 2^M` as round 106's linear column, and the second-moment reflection
  converges for the same reason.  With `jsp87TriSeries_le_two` and
  `jsp87TriSeries_ge_thirtyThree` this is the first **closed-form two-sided
  bracket of a moment of `ω`** in the development.

* **§5 — sharp error terms.**  Both reflections lose only the column tail beyond
  `n = 2^M`, and round 38's `jsp87Tail_le` evaluates it: for every `M ≥ 1`

  ```
  0 ≤ S − ∑_{k<M} k L k ≤ (2^M + 1) · 2^-(2^M)
  0 ≤ S^(2) − ∑_{k<M} k A k ≤ (2^M + 1) · 2^-(2^M)
  ```

  i.e. **explicit doubly-exponential convergence rates** for the whole ladder —
  the quantitative form of what rounds 104 and 106 only proved by squeezing.

Nothing here moves the gate.  The headline `jsp_000087_main` is the irrationality
of `S`, which is *conditional* in the published literature (Pratt, arXiv:2409.15185,
under a uniform prime `k`-tuples hypothesis); the blocker is unchanged, namely
`jsp87_digit_not_eventuallyPeriodic` (aperiodicity of the binary digit string of
`S`, equivalently of the doubling orbit `Int.fract (θ N)` of the carries).
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 0. The geometric weight, reused -/

private theorem summable_bit_two_pow : Summable (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) :=
  (summable_bitTerm_one 0).congr fun n => by simp

private theorem pow_two_tendsto_top : Tendsto (fun M : ℕ => 2 ^ M) atTop atTop :=
  Filter.tendsto_atTop.2 fun M => by
    filter_upwards [eventually_ge_atTop M] with x hx
    exact Nat.le_trans hx (Nat.le_of_lt (Nat.lt_two_pow_self (n := x)))

private theorem inv_eq_one_div (x : ℝ) : x⁻¹ = 1 / x := by
  rw [div_eq_mul_inv, one_mul]

private theorem dist_zero_eq (x : ℝ) : dist x 0 = |x| := by
  rw [dist_eq_norm, Real.norm_eq_abs]
  simp

private theorem dist_one_eq (x : ℝ) : dist x 1 = |x - 1| :=
  by rw [dist_eq_norm, Real.norm_eq_abs]

private theorem jsp87AtLeastSeries_le_two_pow (k : ℕ) (hk : 1 ≤ k) :
    jsp87AtLeastSeries k ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hP : 0 < (2 : ℝ) ^ k := by positivity
  have h1 : jsp87AtLeastSeries k ≤ (1 : ℝ) / (2 : ℝ) ^ k := by
    apply (le_div_iff₀ hP).2
    simpa only [mul_comm] using jsp87AtLeastSeries_mul_two_pow k hk
  rw [← inv_eq_one_div] at h1
  exact h1

private theorem irrational_one_sub {x : ℝ} (h : Irrational x) : Irrational (1 - x) := by
  rintro ⟨q, hq⟩
  refine h ⟨1 - q, ?_⟩
  push_cast
  linarith [hq]

private theorem inv_two_pow_succ_mul (n : ℕ) :
    ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ)⁻¹) * ((2 : ℝ) ^ n)⁻¹ := by
  rw [two_pow_neg_eq, pow_succ, ← inv_pow]
  ring

private theorem telescope_range (g : ℕ → ℝ) : ∀ M : ℕ,
    (∑ k ∈ Finset.range M, (g k - g (k + 1))) = g 0 - g M
  | 0 => by simp
  | (M + 1) => by
      rw [Finset.sum_range_succ_comm, telescope_range g M]
      ring

/-! ## 1. The level family and its tails are one sequence -/

/-- **THE FINITE TAIL-SUM RELATION.**  Summing `L j = A j − A (j+1)` over the
window `[M, M+t)` gives `A M − A (M+t)`: the "at least" series of height `M` is
the *tail* of the level series, up to the truncation at `M + t`. -/
theorem jsp87_tailLevel_sum : ∀ (M t : ℕ),
    (∑ j ∈ Finset.range t, jsp87LevelSeries (M + j))
      = jsp87AtLeastSeries M - jsp87AtLeastSeries (M + t)
  | _, 0 => by simp
  | M, t + 1 => by
      rw [Finset.sum_range_succ_comm, jsp87_tailLevel_sum M t]
      have h := jsp87LevelSeries_sub (M + t)
      rw [Nat.add_succ] at h ⊢
      linarith

/-- **THE EXACT COMPLEMENT OF THE ROW PARTIAL SUMS.**  The levels
`L 0, …, L (M−1)` and the single level `A M` add up to `1`, for every height `M`.
Round 106's partition of unity `∑' k, L k = 1` is the *limit* of this identity. -/
theorem jsp87_levelPartial_add_atLeast (M : ℕ) :
    jsp87LevelPartial M + jsp87AtLeastSeries M = 1 := by
  have hstep : ∀ k, jsp87LevelSeries k = jsp87AtLeastSeries k - jsp87AtLeastSeries (k + 1) :=
    fun k => jsp87LevelSeries_sub k
  have hmain : (∑ k ∈ Finset.range M, jsp87LevelSeries k)
      = ∑ k ∈ Finset.range M, (jsp87AtLeastSeries k - jsp87AtLeastSeries (k + 1)) :=
    Finset.sum_congr rfl fun k _ => hstep k
  calc jsp87LevelPartial M + jsp87AtLeastSeries M
      = (∑ k ∈ Finset.range M, jsp87LevelSeries k) + jsp87AtLeastSeries M := rfl
    _ = (∑ k ∈ Finset.range M, (jsp87AtLeastSeries k - jsp87AtLeastSeries (k + 1)))
          + jsp87AtLeastSeries M := by
        rw [hmain]
    _ = jsp87AtLeastSeries 0 := by rw [telescope_range]; ring
    _ = 1 := jsp87AtLeastSeries_zero

/-- The same identity oriented: **the complement of the row partial sum is the
"at least" series of the same height.** -/
theorem jsp87_levelPartial_eq_one_sub_atLeast (M : ℕ) :
    jsp87LevelPartial M = 1 - jsp87AtLeastSeries M := by
  have h := jsp87_levelPartial_add_atLeast M
  linarith

/-- `M = 0`: the empty sum. -/
theorem jsp87_levelPartial_zero : jsp87LevelPartial 0 = 0 := by
  simp [jsp87LevelPartial]

/-- `M = 1`: the level-`0` series, i.e. the two places `n = 0, 1`. -/
theorem jsp87_levelPartial_one : jsp87LevelPartial 1 = 3 / 4 := by
  show (∑ k ∈ Finset.range 1, jsp87LevelSeries k) = 3 / 4
  rw [Finset.sum_range_succ_comm, Finset.sum_range_zero, add_zero]
  exact jsp87LevelSeries_zero

/-- **THE ROW PARTIAL SUMS ARE POSITIVE EXACTLY FROM HEIGHT `1`.** -/
theorem jsp87_levelPartial_pos_iff (M : ℕ) : 0 < jsp87LevelPartial M ↔ 1 ≤ M := by
  constructor
  · intro h
    have hne : M ≠ 0 := by
      intro hEq
      rw [hEq, jsp87_levelPartial_zero] at h
      exact absurd h (by norm_num)
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.zero_le M) (Ne.symm hne))
  · intro hM
    have h1 := jsp87_levelPartial_add_atLeast M
    have h2 := jsp87AtLeastSeries_le_one_quot M hM
    linarith

/-- **THE ROW PARTIAL SUM OF THE LEVEL FAMILY IS IRRATIONAL EXACTLY FOR `M ≥ 2`.**
This closes the classification begun in round 83: that file proved `L k` and
`A k` irrational exactly for `k ≥ 1` and `k ≥ 2` respectively; the *partial sums*
`∑_{k<M} L k` are irrational exactly for `M ≥ 2`, because they are `1 − A M`. -/
theorem jsp87_levelPartial_irrational_iff (M : ℕ) :
    Irrational (jsp87LevelPartial M) ↔ 2 ≤ M := by
  constructor
  · intro h
    by_cases hM1 : M ≤ 1
    · rcases Nat.eq_zero_or_pos M with hM0 | hM0
      · rw [hM0, jsp87_levelPartial_zero] at h
        exact (h ⟨(0 : ℚ), by norm_num⟩).elim
      · have h1 : M = 1 := by omega
        rw [h1, jsp87_levelPartial_one] at h
        exact (h ⟨(3 / 4 : ℚ), by norm_num⟩).elim
    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hM1)
  · intro hM
    have h2 : Irrational (jsp87AtLeastSeries M) := jsp87AtLeastSeries_irrational M hM
    rw [jsp87_levelPartial_eq_one_sub_atLeast M]
    exact irrational_one_sub h2

/-! ## 2. The complement decays doubly exponentially -/

/-- **THE "AT LEAST" SERIES DECAY DOUBLY EXPONENTIALLY** — the closed form of
`jsp87AtLeastSeries_mul_two_pow_two_pow`. -/
theorem jsp87AtLeastSeries_le_two_pow_sharp (k : ℕ) (hk : 1 ≤ k) :
    jsp87AtLeastSeries k ≤ ((2 : ℝ) ^ (2 ^ k))⁻¹ := by
  have hP : 0 < (2 : ℝ) ^ (2 ^ k) := by positivity
  have h1 : jsp87AtLeastSeries k ≤ (1 : ℝ) / (2 : ℝ) ^ (2 ^ k) := by
    apply (le_div_iff₀ hP).2
    simpa only [mul_comm] using jsp87AtLeastSeries_mul_two_pow_two_pow k hk
  rw [← inv_eq_one_div] at h1
  exact h1

/-- **AN EXPLICIT, DOUBLY EXPONENTIAL ERROR FOR THE PARTITION OF UNITY.**
`∑_{k<M} L k` is within `2^-(2^M)` of `1`: the leftover mass is exactly the
"at least" series `A M`, whose digit string vanishes below `n = 2^M`. -/
theorem jsp87_levelPartial_ge_two_pow_sharp (M : ℕ) (hM : 1 ≤ M) :
    1 - ((2 : ℝ) ^ (2 ^ M))⁻¹ ≤ jsp87LevelPartial M := by
  have h1 : jsp87AtLeastSeries M ≤ ((2 : ℝ) ^ (2 ^ M))⁻¹ :=
    jsp87AtLeastSeries_le_two_pow_sharp M hM
  have h2 := jsp87_levelPartial_eq_one_sub_atLeast M
  linarith

/-- The metric form: `|∑_{k<M} L k − 1| ≤ 2^-(2^M)`.  Together with
`jsp87_levelPartial_le_one` this is a convergence *rate* for round 106's
partition of unity. -/
theorem jsp87_levelPartial_dist_one_le (M : ℕ) (hM : 1 ≤ M) :
    dist (jsp87LevelPartial M) 1 ≤ ((2 : ℝ) ^ (2 ^ M))⁻¹ := by
  have h1 := jsp87_levelPartial_ge_two_pow_sharp M hM
  have h2 := jsp87_levelPartial_le_one M
  rw [dist_one_eq, abs_of_nonpos (by linarith : jsp87LevelPartial M - 1 ≤ 0)]
  linarith

/-- The concrete consequence at height `1`: every row partial sum from height `1`
on is at least `3/4`. -/
theorem jsp87_levelPartial_ge_three_quarters (M : ℕ) (hM : 1 ≤ M) :
    (3 / 4 : ℝ) ≤ jsp87LevelPartial M := by
  have h1 := jsp87_levelPartial_add_atLeast M
  have h2 := jsp87AtLeastSeries_le_one_quot M hM
  linarith

/-! ## 3. The triangular (second-moment) layer cake -/

/-- **THE TRIANGULAR NUMBERS.** -/
def jsp87_tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- **THE TRIANGULAR NUMBER IS A PARTIAL SUM**: `∑_{k < m+1} k = tri m`. -/
theorem jsp87_tri_sum_range (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), k) = jsp87_tri m := by
  have h := Finset.sum_range_id (m + 1)
  rw [Nat.succ_sub_one] at h
  unfold jsp87_tri
  simpa only [Nat.mul_comm] using h

/-- **THE WEIGHTED CUMULATIVE COUNT, IN THE SATURATED RANGE.**  If every layer of
`ω n` is present (`ω n + 1 ≤ M`), the weighted cumulative count is the triangular
number of `ω n`. -/
theorem jsp87_weightCumCount_sat {M n : ℕ} (h : omega n + 1 ≤ M) :
    (∑ k ∈ Finset.range M, k * jsp87AtLeast k n) = jsp87_tri (omega n) := by
  have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
    intro a ha
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) h)
  have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range (omega n + 1) →
      k * jsp87AtLeast k n = 0 := by
    intro k _ hna
    have hk : omega n + 1 ≤ k := by
      rcases Nat.lt_or_ge k (omega n + 1) with hlt | hge
      · exact absurd hlt (fun hh => hna (Finset.mem_range.mpr hh))
      · exact hge
    have hne : omega n < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self (omega n)) hk
    have h1 : jsp87AtLeast k n = 0 := (jsp87AtLeast_eq_zero_iff k n).2 hne
    rw [h1]
    norm_num
  have hswap := Finset.sum_subset hsub hzero
  have hone : (∑ k ∈ Finset.range (omega n + 1), k * jsp87AtLeast k n)
      = ∑ k ∈ Finset.range (omega n + 1), k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hle : k ≤ omega n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [(jsp87AtLeast_eq_one_iff k n).2 hle, mul_one]
  rw [← hswap, hone]
  exact jsp87_tri_sum_range (omega n)

/-- **THE WEIGHTED CUMULATIVE COUNT, IN THE UNSATURATED RANGE.**  Every layer
present has index `< M`, so all indicators are `1`. -/
theorem jsp87_weightCumCount_unsat {M n : ℕ} (h : M ≤ omega n) :
    (∑ k ∈ Finset.range M, k * jsp87AtLeast k n) = ∑ k ∈ Finset.range M, k := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hle : k ≤ omega n := Nat.le_of_lt (hk'.trans_le h)
  have h1 : jsp87AtLeast k n = 1 := (jsp87AtLeast_eq_one_iff k n).2 hle
  rw [h1]
  norm_num

/-- **THE TRIANGULAR NUMBER DOMINATES THE WEIGHTED CUMULATIVE COUNT.**  The
truncation at height `M` never overcounts the `ω n + 1` layers of `n`. -/
theorem jsp87_weightCumCount_le (M n : ℕ) :
    (∑ k ∈ Finset.range M, k * jsp87AtLeast k n) ≤ jsp87_tri (omega n) := by
  rcases Nat.lt_or_ge (omega n + 1) M with h | h
  · rw [jsp87_weightCumCount_sat
      (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self (omega n)) h))]
  · have hsub : Finset.range M ⊆ Finset.range (omega n + 1) := by
      intro a ha
      exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp ha) h)
    calc (∑ k ∈ Finset.range M, k * jsp87AtLeast k n)
        = ∑ k ∈ Finset.range M, k := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hle : k ≤ omega n :=
            Nat.lt_succ_iff.mp (show k < omega n + 1 from
              Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) (show M ≤ omega n + 1 from h))
          rw [(jsp87AtLeast_eq_one_iff k n).2 hle, mul_one]
      _ ≤ ∑ k ∈ Finset.range (omega n + 1), k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => Nat.zero_le k
      _ = jsp87_tri (omega n) := jsp87_tri_sum_range (omega n)

/-- The same, in `ℝ`. -/
theorem jsp87_weightCumCount_cast (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k * jsp87AtLeast k n : ℕ) : ℝ))
      ≤ ((jsp87_tri (omega n) : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]
  exact_mod_cast jsp87_weightCumCount_le M n

/-- **THE TRIANGULAR COLUMN AT `n`.** -/
noncomputable def jsp87CumWeightColumn (M n : ℕ) : ℝ :=
  ((∑ k ∈ Finset.range M, k * jsp87AtLeast k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

private theorem cast_sum_cum (M n : ℕ) :
    ((∑ k ∈ Finset.range M, k * jsp87AtLeast k n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range M, ((k * jsp87AtLeast k n : ℕ) : ℝ) := by
  rw [← Nat.cast_sum]

/-- The `M` weighted cumulative layers, read off at the single cut point `n`. -/
theorem jsp87_weightedCum_sum_eq (M n : ℕ) :
    (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n))
      = jsp87CumWeightColumn M n := by
  unfold jsp87CumWeightColumn
  calc (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n))
      = ∑ k ∈ Finset.range M, (((k * jsp87AtLeast k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [jsp87BitTerm, Nat.cast_mul]
        ring
    _ = ((∑ k ∈ Finset.range M, (k * jsp87AtLeast k n : ℕ) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [cast_sum_cum, Finset.sum_mul]

theorem jsp87CumWeightColumn_nonneg (M n : ℕ) : 0 ≤ jsp87CumWeightColumn M n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE TRIANGULAR COLUMN AT `n` IS AT MOST THE `n`-TH TRIANGULAR MOMENT.** -/
theorem jsp87CumWeightColumn_le_triTerm (M n : ℕ) :
    jsp87CumWeightColumn M n ≤ ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  unfold jsp87CumWeightColumn
  rw [cast_sum_cum]
  exact mul_le_mul_of_nonneg_right (jsp87_weightCumCount_cast M n) (by positivity)

/-- **THE TRIANGULAR SATURATION POINT.**  The triangular column is *complete*
below `n = 2^M`: all `ω n + 1` layers are present, with weight `k`. -/
theorem jsp87CumWeightColumn_eq_triTerm {M n : ℕ} (hM : 1 ≤ M) (hn : n < 2 ^ M) :
    jsp87CumWeightColumn M n = ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hωlt : omega n + 1 ≤ M := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, omega_zero]
      have : 0 < M := hM
      omega
    · exact Nat.succ_le_iff.mpr (omega_lt_of_lt_two_pow hn0 hn)
  unfold jsp87CumWeightColumn
  rw [cast_sum_cum, ← Nat.cast_sum, jsp87_weightCumCount_sat hωlt]

/-- **THE SECOND-MOMENT TERM.** -/
noncomputable def jsp87TriTerm (n : ℕ) : ℝ :=
  ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

theorem jsp87TriTerm_nonneg (n : ℕ) : 0 ≤ jsp87TriTerm n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **THE SECOND MOMENT OF `ω`.** -/
noncomputable def jsp87TriSeries : ℝ := ∑' (n : ℕ), jsp87TriTerm n

/-- **THE TRIANGULAR NUMBER IS BOUNDED BY THE FIRST MOMENT TIMES THE INDEX**:
`tri (ω n) ≤ ω n (n + 1)`, because `ω n ≤ n` and halving only helps. -/
theorem jsp87_tri_le_mul_omega_add_one (n : ℕ) :
    jsp87_tri (omega n) ≤ omega n * (n + 1) := by
  unfold jsp87_tri
  refine Nat.le_trans (Nat.div_le_of_le_mul (m := omega n * (omega n + 1))
      (n := omega n * (omega n + 1)) (k := 2) ?_)
    (Nat.mul_le_mul_left (omega n) (n := omega n + 1) ?_)
  · exact Nat.le_mul_of_pos_left _ (by norm_num : (0 : ℕ) < 2)
  · exact Nat.add_le_add_right (omega_le_self n) 1

/-- **A QUADRATIC MAJORANT IS SUMMABLE** — the closed-form geometric-with-weight
series `∑ n, (n² + n) · 2^-(n+1)`.  Mathlib supplies the square part
(`summable_pow_mul_geometric_of_norm_lt_one 2`); the linear part is round 37's
`summable_nat_mul_two_pow_neg`.  (This Mathlib has no instance for the pointwise
product of two `Summable` series, so the majorant is built additively.) -/
private theorem summable_poly_mul_two_pow_neg :
    Summable (fun n : ℕ => (((n * n + n : ℕ) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  have hraw : Summable (fun n : ℕ => (n : ℝ) ^ 2 * ((2 : ℝ) ^ n)⁻¹) := by
    refine (summable_pow_mul_geometric_of_norm_lt_one 2 (r := (2 : ℝ)⁻¹) (by norm_num)).congr
      fun n => ?_
    rw [← inv_pow]
  have hsq : Summable (fun n : ℕ => ((n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    refine hraw.mul_left ((2 : ℝ)⁻¹) |>.congr fun n => ?_
    rw [inv_two_pow_succ_mul]
    simp only [Nat.cast_pow]
    ring
  have hlin : Summable (fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
    summable_nat_mul_two_pow_neg
  have h := Summable.add hsq hlin
  refine h.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring

/-- **`ω n · (n + 1) ≤ n² + n`** — the quadratic majorant, in `ℕ`. -/
theorem jsp87_mul_omega_add_one_le_poly (n : ℕ) :
    omega n * (n + 1) ≤ n * n + n := by
  have h1 : omega n * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul (omega_le_self n) (le_refl _)
  rw [Nat.mul_add, Nat.mul_one] at h1
  exact h1

/-- **THE SECOND MOMENT CONVERGES.** -/
theorem summable_jsp87TriTerm : Summable jsp87TriTerm :=
  Summable.of_nonneg_of_le (fun n => jsp87TriTerm_nonneg n)
    (fun n => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.le_trans (jsp87_tri_le_mul_omega_add_one n)
        (jsp87_mul_omega_add_one_le_poly n))) (by positivity))
    summable_poly_mul_two_pow_neg

theorem jsp87TriSeries_nonneg : 0 ≤ jsp87TriSeries :=
  tsum_nonneg fun n => jsp87TriTerm_nonneg n

/-- **THE WEIGHTED CUMULATIVE ROW PARTIAL SUM** `V M = ∑_{k<M} k · A k`. -/
noncomputable def jsp87CumWeightPartial (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87AtLeastSeries k)

/-- **THE FINITE WEIGHTED-CUMULATIVE INTERCHANGE.** -/
theorem jsp87_cumWeightPartial_eq_tsum (M : ℕ) :
    (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87AtLeastSeries k))
      = ∑' (n : ℕ), jsp87CumWeightColumn M n := by
  have hfin : (∑' (n : ℕ),
        ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n))
      = ∑ k ∈ Finset.range M,
        ∑' (n : ℕ), ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n) := by
    refine Summable.tsum_finsetSum fun i _ => ?_
    exact (summable_jsp87AtLeast i).mul_left ((i : ℝ))
  have hrhs : (∑ k ∈ Finset.range M,
        ∑' (n : ℕ), ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n))
      = ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87AtLeastSeries k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold jsp87AtLeastSeries jsp87BinarySeries
    exact Summable.tsum_mul_left (k : ℝ) (summable_jsp87AtLeast k)
  have hlhs : (∑' (n : ℕ),
        ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n))
      = ∑' (n : ℕ), jsp87CumWeightColumn M n := by
    refine tsum_congr fun n => ?_
    exact jsp87_weightedCum_sum_eq M n
  calc (∑ k ∈ Finset.range M, ((k : ℝ) * jsp87AtLeastSeries k))
      = ∑ k ∈ Finset.range M,
          ∑' (n : ℕ), ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n) := hrhs.symm
    _ = ∑' (n : ℕ),
          ∑ k ∈ Finset.range M, ((k : ℝ) * jsp87BitTerm (fun m => jsp87AtLeast k m) n) :=
        hfin.symm
    _ = ∑' (n : ℕ), jsp87CumWeightColumn M n := hlhs

theorem summable_jsp87CumWeightColumn (M : ℕ) : Summable (jsp87CumWeightColumn M) :=
  Summable.of_nonneg_of_le (fun n => jsp87CumWeightColumn_nonneg M n)
    (fun n => jsp87CumWeightColumn_le_triTerm M n) summable_jsp87TriTerm

/-- **THE WEIGHTED CUMULATIVE ROWS NEVER OVERSHOOT THE SECOND MOMENT.** -/
theorem jsp87_cumWeightPartial_le_triSeries (M : ℕ) :
    jsp87CumWeightPartial M ≤ jsp87TriSeries := by
  have h' := Summable.tsum_le_tsum (fun n => jsp87CumWeightColumn_le_triTerm M n)
    (summable_jsp87CumWeightColumn M) summable_jsp87TriTerm
  exact (jsp87_cumWeightPartial_eq_tsum M).trans_le h'

/-- **THE WEIGHTED CUMULATIVE ROWS DOMINATE THE COLUMNS BELOW `n = 2^M`.** -/
theorem jsp87_colPartial_le_cumWeightPartial {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range (2 ^ M), ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      ≤ jsp87CumWeightPartial M := by
  have hmin : ∀ n ∈ Finset.range (2 ^ M),
      jsp87CumWeightColumn M n = ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
    fun n hn => jsp87CumWeightColumn_eq_triTerm hM (Finset.mem_range.mp hn)
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ M))
    (fun i _ => jsp87CumWeightColumn_nonneg M i) (summable_jsp87CumWeightColumn M)
  calc (∑ n ∈ Finset.range (2 ^ M), ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑ n ∈ Finset.range (2 ^ M), jsp87CumWeightColumn M n :=
        (Finset.sum_congr rfl hmin).symm
    _ ≤ ∑' (n : ℕ), jsp87CumWeightColumn M n := hsum
    _ = jsp87CumWeightPartial M := (jsp87_cumWeightPartial_eq_tsum M).symm

/-! ## 4. The gap, the closed form, and the second-moment reflection -/

theorem jsp87_cumWeightGap_nonneg (M : ℕ) : 0 ≤ jsp87TriSeries - jsp87CumWeightPartial M := by
  have h := jsp87_cumWeightPartial_le_triSeries M
  linarith

theorem jsp87_cumWeightGap_le_tail {M : ℕ} (hM : 1 ≤ M) :
    jsp87TriSeries - jsp87CumWeightPartial M
      ≤ jsp87TriSeries - ∑ n ∈ Finset.range (2 ^ M),
          ((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hle := jsp87_colPartial_le_cumWeightPartial hM
  linarith

/-- **THE TRIANGULAR TAIL IS THE SHIFTED SECOND MOMENT** — the mirror of round 38's
`jsp87_series_eq_sum_add_tail`. -/
theorem jsp87TriSeries_sub_colPartial (N : ℕ) :
    jsp87TriSeries - (∑ n ∈ Finset.range N, jsp87TriTerm n)
      = ∑' (k : ℕ), jsp87TriTerm (N + k) := by
  have h := summable_jsp87TriTerm.sum_add_tsum_nat_add N
  have h2 : (∑' (i : ℕ), jsp87TriTerm (i + N)) = ∑' (k : ℕ), jsp87TriTerm (N + k) :=
    tsum_congr fun i => by rw [Nat.add_comm]
  unfold jsp87TriSeries
  linarith

/-- **THE SHARP, CLOSED-FORM ERROR TERM OF ROUND 106'S REFLECTION**, obtained the
same way.  This closes the quantitative item left open by round 106. -/
theorem jsp87_weightGap_le_closed {M : ℕ} (hM : 1 ≤ M) :
    jsp87Series - jsp87WeightPartial M ≤ ((2 ^ M + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 ^ M))⁻¹ := by
  have h1 := jsp87_weightGap_le_tail hM
  have h2 := jsp87_series_eq_sum_add_tail (2 ^ M)
  have h3 := jsp87Tail_le (2 ^ M)
  have h4 : 1 ≤ 2 ^ M := one_le_two_pow M
  linarith

theorem tendsto_jsp87_cumWeightGap :
    Tendsto (fun M => jsp87TriSeries - jsp87CumWeightPartial M) atTop (nhds 0) := by
  have h1 : Tendsto (fun _ : ℕ => jsp87TriSeries) atTop (nhds jsp87TriSeries) := tendsto_const_nhds
  have htri : Tendsto (fun N => ∑ n ∈ Finset.range N, jsp87TriTerm n)
      atTop (nhds jsp87TriSeries) := summable_jsp87TriTerm.hasSum.tendsto_sum_nat
  have hcol : Tendsto (fun N => jsp87TriSeries - ∑ n ∈ Finset.range N, jsp87TriTerm n)
      atTop (nhds 0) := by
    simpa only [sub_self] using h1.sub htri
  have htail : Tendsto (fun M => jsp87TriSeries - ∑ n ∈ Finset.range (2 ^ M), jsp87TriTerm n)
      atTop (nhds 0) := hcol.comp pow_two_tendsto_top
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail ε hε
  refine ⟨N + 1, ?_⟩
  intro M hM
  have hM1 : 1 ≤ M := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le N)) hM
  have hMN : N ≤ M := Nat.le_trans (Nat.le_add_right N 1) hM
  have hlt := jsp87_cumWeightGap_le_tail hM1
  have hg0 := jsp87_cumWeightGap_nonneg M
  have hdist := hN _ hMN
  have ht0 : 0 ≤ jsp87TriSeries - ∑ n ∈ Finset.range (2 ^ M), jsp87TriTerm n := by
    have h := Summable.sum_le_tsum (Finset.range (2 ^ M))
      (fun i _ => jsp87TriTerm_nonneg i) summable_jsp87TriTerm
    unfold jsp87TriSeries
    linarith
  rw [dist_zero_eq, abs_of_nonneg ht0] at hdist
  rw [dist_zero_eq, abs_of_nonneg hg0]
  exact lt_of_le_of_lt hlt hdist

theorem tendsto_jsp87_cumWeightPartial :
    Tendsto jsp87CumWeightPartial atTop (nhds jsp87TriSeries) := by
  have h3 : Tendsto (fun M => (jsp87TriSeries)
        - (jsp87TriSeries - jsp87CumWeightPartial M)) atTop (nhds jsp87TriSeries) := by
    simpa only [sub_zero] using tendsto_jsp87_cumWeightGap.const_sub (jsp87TriSeries)
  refine h3.congr' (f₂ := jsp87CumWeightPartial) (Filter.Eventually.of_forall fun M => ?_)
  unfold jsp87CumWeightPartial
  ring

/-- The second-moment reflection, as a `HasSum`. -/
theorem hasSum_weightedAtLeast :
    HasSum (fun k : ℕ => ((k : ℝ) * jsp87AtLeastSeries k)) jsp87TriSeries := by
  refine (hasSum_iff_tendsto_nat_of_nonneg
    (f := fun k : ℕ => ((k : ℝ) * jsp87AtLeastSeries k))
    (fun k => mul_nonneg (Nat.cast_nonneg _) (jsp87AtLeastSeries_nonneg k)) _).2 ?_
  exact tendsto_jsp87_cumWeightPartial

/-- **THE WEIGHTED "AT LEAST" FAMILY IS SUMMABLE.** -/
theorem summable_weightedAtLeast : Summable (fun k : ℕ => ((k : ℝ) * jsp87AtLeastSeries k)) :=
  ⟨jsp87TriSeries, hasSum_weightedAtLeast⟩

/-- **THE SECOND-MOMENT REFLECTION — THE HEADLINE OF THIS ROUND.**

```
jsp87TriSeries = ∑' k, k · jsp87AtLeastSeries k
```

Weighting the *"at least"* layers against their index reproduces the triangular
number `ω n (ω n + 1) / 2` at each cut point `n`, i.e. the second moment of `ω`,
because `∑_{k<ω n+1} k = 1 + 2 + … + ω n`.  Round 106 proved the companion
identity for the *level* layers (`S = ∑' k, k L k`, the first moment); together
the two are the first two members of the power-sum ladder

```
S^(1) = ∑' k, k L k          (round 106)
S^(2) = ∑' k, k A k          (this round)
```

and convergence is supplied by the triangular saturation point
`n < 2^M ⟹ jsp87CumWeightColumn M n = jsp87TriTerm n`. -/
theorem jsp87TriSeries_eq_tsum_weightedAtLeast :
    jsp87TriSeries = ∑' (k : ℕ), ((k : ℝ) * jsp87AtLeastSeries k) :=
  hasSum_weightedAtLeast.tsum_eq.symm

/-- **EVERY WEIGHTED "AT LEAST" LEVEL IS IRRATIONAL** (from height `2` up; the row
`A 1 = 1/4` is rational, exactly as round 83 found). -/
theorem jsp87_weightedAtLeast_irrational {k : ℕ} (hk : 2 ≤ k) :
    Irrational ((k : ℝ) * jsp87AtLeastSeries k) :=
  (jsp87AtLeastSeries_irrational k hk).natCast_mul (m := k) (Nat.ne_of_gt (by omega))

/-! ## 5. The pure square moment -/

/-- **THE SQUARE MOMENT TERM.** -/
noncomputable def jsp87SqTerm (n : ℕ) : ℝ := ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- **THE SQUARE MOMENT OF `ω`.** -/
noncomputable def jsp87SquareSeries : ℝ := ∑' (n : ℕ), jsp87SqTerm n

theorem jsp87SqTerm_nonneg (n : ℕ) : 0 ≤ jsp87SqTerm n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **`2 · tri (ω n) = ω n² + ω n`** — the triangular number is half the second
moment plus the first. -/
theorem jsp87_tri_mul_two (n : ℕ) : 2 * jsp87_tri (omega n) = omega n ^ 2 + omega n := by
  have h1 : 2 * (omega n * (omega n + 1) / 2) = omega n * (omega n + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (omega n))
  have h2 : omega n * (omega n + 1) = omega n ^ 2 + omega n := by
    rw [Nat.mul_add, Nat.mul_one, ← pow_two]
  unfold jsp87_tri
  rw [h1, h2]

/-- **THE SQUARE MOMENT IS BOUNDED BY THE FIRST MOMENT TIMES THE INDEX.** -/
theorem jsp87_sq_le_mul_omega_add_one (n : ℕ) : omega n ^ 2 ≤ omega n * (n + 1) := by
  have h1 : omega n ^ 2 = omega n * omega n := pow_two (omega n)
  rw [h1]
  exact Nat.mul_le_mul (le_refl _) (Nat.le_trans (omega_le_self n) (Nat.le_succ _))

/-- **THE SQUARE MOMENT CONVERGES.** -/
theorem summable_jsp87SqTerm : Summable jsp87SqTerm :=
  Summable.of_nonneg_of_le (fun n => jsp87SqTerm_nonneg n)
    (fun n => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.le_trans (jsp87_sq_le_mul_omega_add_one n)
        (jsp87_mul_omega_add_one_le_poly n))) (by positivity))
    summable_poly_mul_two_pow_neg

/-- `2 ·` the triangular moment term is the square moment plus the Erdős term. -/
theorem jsp87TriTerm_two_eq (n : ℕ) :
    2 * jsp87TriTerm n = jsp87SqTerm n + jsp87Term n := by
  have h : 2 * ((jsp87_tri (omega n) : ℕ) : ℝ)
      = ((omega n ^ 2 : ℕ) : ℝ) + ((omega n : ℕ) : ℝ) := by
    rw [← Nat.cast_add]
    exact_mod_cast jsp87_tri_mul_two n
  unfold jsp87TriTerm jsp87SqTerm jsp87Term
  calc 2 * (((jsp87_tri (omega n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (2 * ((jsp87_tri (omega n) : ℕ) : ℝ)) * ((2 : ℝ) ^ (n + 1))⁻¹ := by ring
    _ = (((omega n ^ 2 : ℕ) : ℝ) + ((omega n : ℕ) : ℝ)) * ((2 : ℝ) ^ (n + 1))⁻¹ := by rw [h]
    _ = ((omega n ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
        + ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by ring

/-- **THE SECOND MOMENT IS THE SUM OF THE SQUARE MOMENT AND THE ERDŐS SERIES**:
`2 S^(2) = ∑' n, ω n² · 2^-(n+1) + S`. -/
theorem jsp87TriSeries_two_eq_add_sq :
    2 * jsp87TriSeries = jsp87SquareSeries + jsp87Series := by
  have h1 : 2 * jsp87TriSeries = ∑' (n : ℕ), (2 * jsp87TriTerm n) :=
    (Summable.tsum_mul_left 2 summable_jsp87TriTerm).symm
  calc 2 * jsp87TriSeries = ∑' (n : ℕ), (2 * jsp87TriTerm n) := h1
    _ = ∑' (n : ℕ), (jsp87SqTerm n + jsp87Term n) :=
      tsum_congr fun n => jsp87TriTerm_two_eq n
    _ = jsp87SquareSeries + jsp87Series :=
      Summable.tsum_add summable_jsp87SqTerm summable_omega_mul_inv_two_pow

/-- **THE PURE SQUARE MOMENT, IN THE WEIGHTED-"AT LEAST" FORM.**  Putting the two
reflections together:

```
∑' n, ω n ^ 2 · 2^-(n+1)  +  S  =  ∑' k, 2k · A k
```

so the second moment of `ω` is a doubled copy of the same weighted family. -/
theorem jsp87SquareSeries_add_eq_tsum_two_weightedAtLeast :
    jsp87SquareSeries + jsp87Series
      = ∑' (k : ℕ), ((2 : ℝ) * ((k : ℝ) * jsp87AtLeastSeries k)) := by
  calc jsp87SquareSeries + jsp87Series = 2 * jsp87TriSeries :=
        (jsp87TriSeries_two_eq_add_sq).symm
    _ = 2 * ∑' (k : ℕ), ((k : ℝ) * jsp87AtLeastSeries k) := by
        rw [jsp87TriSeries_eq_tsum_weightedAtLeast]
    _ = ∑' (k : ℕ), ((2 : ℝ) * ((k : ℝ) * jsp87AtLeastSeries k)) :=
        (Summable.tsum_mul_left 2 summable_weightedAtLeast).symm

theorem jsp87SquareSeries_nonneg : 0 ≤ jsp87SquareSeries :=
  tsum_nonneg fun n => jsp87SqTerm_nonneg n

theorem jsp87SquareSeries_le_two_triSeries : jsp87SquareSeries ≤ 2 * jsp87TriSeries := by
  have h1 := jsp87TriSeries_two_eq_add_sq
  have h2 := jsp87Series_nonneg
  linarith

/-- **THE SECOND MOMENT IS THE FIRST MOMENT PLUS A SHIFTED FIRST MOMENT.**
Using `L k = A k − A (k+1)`,

```
S^(2) = S + ∑' k, k · A (k+1)
```

i.e. the ladder `S^(1), S^(2)` are related by a single index shift of the same
weighted family — and with `jsp87TriSeries_two_eq_add_sq` this identifies `S^(2)`
with `(square moment + S)/2`. -/
theorem jsp87TriSeries_eq_add_shiftedWeight :
    jsp87TriSeries = jsp87Series
      + ∑' (k : ℕ), ((k : ℕ) : ℝ) * jsp87AtLeastSeries (k + 1) := by
  have hsub : (∑' (k : ℕ), (((k : ℝ) * jsp87AtLeastSeries k)
        - ((k : ℝ) * jsp87LevelSeries k)))
      = jsp87TriSeries - jsp87Series :=
    (Summable.tsum_sub summable_weightedAtLeast summable_weightedLevels).trans
      (congrArg₂ (· - ·) jsp87TriSeries_eq_tsum_weightedAtLeast.symm
        jsp87Series_eq_tsum_weightedLevels.symm)
  have hshift : (∑' (k : ℕ), (((k : ℝ) * jsp87AtLeastSeries k)
        - ((k : ℝ) * jsp87LevelSeries k)))
      = ∑' (k : ℕ), ((k : ℕ) : ℝ) * jsp87AtLeastSeries (k + 1) := by
    refine tsum_congr fun k => ?_
    have h := jsp87LevelSeries_sub k
    rw [h]
    ring
  calc jsp87TriSeries = (jsp87TriSeries - jsp87Series) + jsp87Series := by ring
    _ = (∑' (k : ℕ), (((k : ℝ) * jsp87AtLeastSeries k)
          - ((k : ℝ) * jsp87LevelSeries k))) + jsp87Series := by rw [hsub]
    _ = jsp87Series + ∑' (k : ℕ), ((k : ℕ) : ℝ) * jsp87AtLeastSeries (k + 1) :=
      (add_comm _ _).trans (by rw [hshift])

/-! ## 6. Closed-form brackets of the moments -/

private theorem summable_nat_mul_two_pow_inv :
    Summable (fun k : ℕ => ((k : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹) := by
  have h : Summable (fun n : ℕ => (n : ℝ) * (2 : ℝ)⁻¹ ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 : ℝ)⁻¹) (by norm_num))
  refine h.congr fun n => ?_
  rw [inv_pow]

private theorem tsum_nat_mul_two_pow_inv :
    (∑' (k : ℕ), ((k : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹) = 2 := by
  have hconv : Summable (fun n : ℕ => (n : ℝ) * (2 : ℝ)⁻¹ ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 : ℝ)⁻¹) (by norm_num))
  have hval : (∑' (n : ℕ), (n : ℝ) * (2 : ℝ)⁻¹ ^ n) = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)]
    norm_num
  have hmain : (∑' (k : ℕ), ((k : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹)
      = ∑' (n : ℕ), (n : ℝ) * (2 : ℝ) ⁻¹ ^ n := by
    congr 1
    funext n
    rw [inv_pow]
  rw [hmain, hval]

/-- **THE WEIGHTED ROWS ARE DOMINATED BY THE GEOMETRIC MAJORANT `k 2^-k`.** -/
theorem jsp87_weightedAtLeast_le_two_pow (k : ℕ) :
    ((k : ℝ) * jsp87AtLeastSeries k) ≤ ((k : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0]
    simp [jsp87AtLeastSeries_zero]
  · have h1 : jsp87AtLeastSeries k ≤ ((2 : ℝ) ^ k)⁻¹ :=
      jsp87AtLeastSeries_le_two_pow k (Nat.succ_le_of_lt hk0)
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)

/-- **THE SECOND MOMENT IS AT MOST `2`** — the mirror of `jsp87Series ≤ 1`: the
`k`-th row of the "at least" family is at most `2^-k` (round 106), so the weighted
ladder is dominated by `∑' k, k 2^-k = 2`. -/
theorem jsp87TriSeries_le_two : jsp87TriSeries ≤ 2 := by
  have h' := Summable.tsum_le_tsum (fun k => jsp87_weightedAtLeast_le_two_pow k)
    summable_weightedAtLeast summable_nat_mul_two_pow_inv
  rw [tsum_nat_mul_two_pow_inv] at h'
  rw [jsp87TriSeries_eq_tsum_weightedAtLeast]
  exact h'

/-- **A CLOSED-FORM LOWER BOUND FOR THE SECOND MOMENT.**  The seven places
`n < 7` already contribute `33/128`. -/
theorem jsp87TriSeries_ge_thirtyThree : (33 / 128 : ℝ) ≤ jsp87TriSeries := by
  have hnonneg : ∀ i : ℕ, 0 ≤ jsp87TriTerm i := jsp87TriTerm_nonneg
  have hsum := Summable.sum_le_tsum (Finset.range 7) (fun i _ => hnonneg i)
    summable_jsp87TriTerm
  have hval : (∑ i ∈ Finset.range 7, jsp87TriTerm i) = 33 / 128 := by
    have h0 : omega 0 = 0 := omega_zero
    have h1 : omega 1 = 0 := omega_one
    have h2 : omega 2 = 1 := by native_decide
    have h3 : omega 3 = 1 := by native_decide
    have h4 : omega 4 = 1 := by native_decide
    have h5 : omega 5 = 1 := by native_decide
    have h6 : omega 6 = 2 := by native_decide
    simp only [Finset.sum_range_succ_comm]
    norm_num [jsp87TriTerm, jsp87_tri, h0, h1, h2, h3, h4, h5, h6]
  rwa [hval] at hsum

/-- **A CLOSED-FORM LOWER BOUND FOR THE SQUARE MOMENT.**  The six places
`n < 6` all have `ω n = 1` and contribute `15/64`. -/
theorem jsp87SquareSeries_ge_fifteen : (15 / 64 : ℝ) ≤ jsp87SquareSeries := by
  have hnonneg : ∀ i : ℕ, 0 ≤ jsp87SqTerm i := jsp87SqTerm_nonneg
  have hsum := Summable.sum_le_tsum (Finset.range 6) (fun i _ => hnonneg i)
    summable_jsp87SqTerm
  have hval : (∑ i ∈ Finset.range 6, jsp87SqTerm i) = 15 / 64 := by
    have h0 : omega 0 = 0 := omega_zero
    have h1 : omega 1 = 0 := omega_one
    have h2 : omega 2 = 1 := by native_decide
    have h3 : omega 3 = 1 := by native_decide
    have h4 : omega 4 = 1 := by native_decide
    have h5 : omega 5 = 1 := by native_decide
    simp only [Finset.sum_range_succ_comm]
    norm_num [jsp87SqTerm, h0, h1, h2, h3, h4, h5]
  rwa [hval] at hsum

theorem jsp87TriSeries_pos : 0 < jsp87TriSeries := by
  linarith [jsp87TriSeries_ge_thirtyThree, show (0 : ℝ) < 33 / 128 by norm_num]

theorem jsp87SquareSeries_pos : 0 < jsp87SquareSeries := by
  linarith [jsp87SquareSeries_ge_fifteen, show (0 : ℝ) < 15 / 64 by norm_num]

/-- **THE SECOND MOMENT DOMINATES THE ERDŐS SERIES**: the layer `k ≤ ω n` is
counted `ω n` times in `∑_{k} k A k` and once in `S`, so `S ≤ S^(2)`. -/
theorem jsp87TriSeries_ge_series : jsp87Series ≤ jsp87TriSeries := by
  rw [jsp87TriSeries_eq_tsum_weightedAtLeast, jsp87Series_eq_tsum_weightedLevels]
  exact Summable.tsum_le_tsum (fun k =>
      mul_le_mul_of_nonneg_left (jsp87LevelSeries_le_atLeast k) (Nat.cast_nonneg _))
    summable_weightedLevels summable_weightedAtLeast

end JSP87
