/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LevelSets
import Mathlib.Tactic

/-!
# JSP-000087 : the layer-cake decomposition of the Erdős series, and the join with
# the level-set series of round 83

Round 83 (`LevelSets.lean`) decomposed `ω` into its **level sets** and proved the
complete classification of the two carry-free families

```
jsp87LevelSeries k = ∑' n, [ω n = k] · 2^-(n+1)      irrational ⟺ 1 ≤ k
jsp87AtLeastSeries k = ∑' n, [k ≤ ω n] · 2^-(n+1)    irrational ⟺ 2 ≤ k
```

Round 37+ built the Erdős series itself, `S = jsp87Series = ∑' n, ω n · 2^-(n+1)`,
together with its carry scaffold, Lambert reduction, carry dynamics, digit
bookkeeping and aperiodicity endgame.  **The two halves had never been joined.**

This module is the join.  The layer-cake identity

```
ω n = #{ k : k ≤ ω n } = ∑_{k} [k ≤ ω n]
```

says that `ω n` *is the number of layers at `n`*, so

```
S + 1 = ∑' n, (ω n + 1) · 2^-(n+1)                       (the "column" form, §3)
      = ∑' k, jsp87AtLeastSeries k                       (the "row" form — §5)
```

where the `+ 1` is the *layer `k = 0`*, i.e. the geometric series `∑' n, 2^-(n+1) = 1`
(which round 83 computed: `jsp87AtLeastSeries 0 = 1`).

## 1. The layer-cake identity (§1)

* `omega_eq_sum_atLeastBit` : `∑_{k < ω n} [k ≤ ω n] = ω n`, in `ℕ`.

## 2. The real summands, and the finite join (§2)

* `jsp87LayerTerm k n = [k ≤ ω n] · 2^-(n+1)`;
* `jsp87LayerTerm_sum_eq` : `∑_{k < ω n} jsp87LayerTerm k n = jsp87Term n`;
* `jsp87_layerSum_range` : at a cut point `M > n`, the truncated layer sum is
  `jsp87Term n + 2^-(n+1)` — the extra term is exactly the layer `k = ω n`;
* `jsp87_partial_eq_sum_level` : **THE FINITE JOIN**
  `∑_{n<M} ω n 2^-(n+1) + ∑_{n<M} 2^-(n+1) = ∑_{k<M} ∑_{n<M} [k ≤ ω n] 2^-(n+1)`.

## 3. The infinite join, in column form (§3)

* `jsp87Series_add_one_eq_tsum_columns` : **`S + 1 = ∑' n, (ω n + 1) 2^-(n+1)`** —
  the Erdős series *plus one* is the sum over the cut points of the number of
  layers at that cut point.  No Fubini is needed: both sides are single `tsum`s
  over `n`.

## 4. The infinite join, in row form (§5) — the one missing step

The row form `S + 1 = ∑' k, jsp87AtLeastSeries k` needs to interchange a
*countable* double sum, and this Mathlib version has **no** Fubini lemma for `ℝ`
(`Summable.tsum_finset_sum`, `tsum_comm` for `ℝ`: all absent — only the `ℝ≥0∞`
version `ENNReal.tsum_comm` exists), and no
`Filter.Tendsto.le_of_tendsto_of_tendsto_of_le_of_le'` to pass an inequality
through a limit.  The exact three-step plan for the next round is recorded at the
end of this file; the finite form `jsp87_partial_eq_sum_level` above is what the
first step delivers.

## 5. Why the join does not close the gate

Every `jsp87AtLeastSeries k` with `k ≥ 2` is **irrational** (round 83), and so is
every `jsp87LevelSeries k` with `k ≥ 1`.  The Erdős series is an (infinite)
integer-weighted combination of them.  A countable combination of irrational
numbers need not be irrational — and the two exceptional members of the family are
exactly the trivial ones (`jsp87AtLeastSeries 0 = 1`, `jsp87AtLeastSeries 1 = 1/4`,
`jsp87LevelSeries 0 = 3/4`).  So the join sharpens the *shape* of the problem
without touching the blocker, which remains round 41's
`jsp87_digit_not_eventuallyPeriodic`, equivalently round 64's aperiodicity of the
doubling orbit `Int.fract (θ N)`.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The layer-cake identity -/

private theorem sum_range_one (K : ℕ) : ∑ _k ∈ Finset.range K, (1 : ℕ) = K := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]

/-- A constant summand over `range K` has value `K · c`. -/
private theorem sum_range_const (K : ℕ) (c : ℝ) :
    ∑ _k ∈ Finset.range K, c = (K : ℝ) * c := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **THE LAYER-CAKE IDENTITY.**  `ω n` is the number of layers `k` with `ω n ≥ k`. -/
theorem omega_eq_sum_cumulBit (n : ℕ) :
    (∑ k ∈ Finset.range (omega n), jsp87AtLeast k n) = omega n := by
  have h1 : ∀ k ∈ Finset.range (omega n), jsp87AtLeast k n = 1 := by
    intro k hk
    have hk' : k < omega n := Finset.mem_range.mp hk
    have hle : k ≤ omega n := Nat.le_of_lt hk'
    simp only [jsp87AtLeast, hle, ↓reduceIte]
  calc (∑ k ∈ Finset.range (omega n), jsp87AtLeast k n)
      = ∑ _k ∈ Finset.range (omega n), (1 : ℕ) := Finset.sum_congr rfl h1
    _ = omega n := sum_range_one _

/-- **The real summand of the `k`-th layer.** -/
noncomputable def jsp87LayerTerm (k n : ℕ) : ℝ :=
  ((jsp87AtLeast k n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- Each term of the series is nonnegative. -/
theorem jsp87LayerTerm_nonneg (k n : ℕ) : 0 ≤ jsp87LayerTerm k n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **The real layer-cake identity**: the `ω n` layers of index `n` sum to the
`n`-th term of the Erdős series. -/
theorem jsp87LayerTerm_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range (omega n), jsp87LayerTerm k n) = jsp87Term n := by
  have h1 : ∀ k ∈ Finset.range (omega n), jsp87LayerTerm k n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro k hk
    have hk' : k < omega n := Finset.mem_range.mp hk
    have hle : k ≤ omega n := Nat.le_of_lt hk'
    simp only [jsp87LayerTerm, jsp87AtLeast, hle, ↓reduceIte, Nat.cast_one, one_mul]
  calc (∑ k ∈ Finset.range (omega n), jsp87LayerTerm k n)
      = ∑ _k ∈ Finset.range (omega n), ((2 : ℝ) ^ (n + 1))⁻¹ := Finset.sum_congr rfl h1
    _ = omega n * ((2 : ℝ) ^ (n + 1))⁻¹ :=
      sum_range_const (omega n) ((2 : ℝ) ^ (n + 1))⁻¹
    _ = jsp87Term n := rfl

/-- **`ω n` is bounded by the size of `n`** — the fact that makes the finite layer
decomposition below an identity rather than an inequality. -/
theorem omega_lt_of_lt {n k : ℕ} (h : n < k) : omega n < k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have h1 : omega 0 = 0 := (omega_eq_zero_iff).mpr (by omega)
    rw [hn, h1]
    exact Nat.zero_lt_of_lt h
  · have h1 : omega n ≤ n - 1 := omega_lt (Nat.succ_le_iff.mpr hn)
    have h2 : omega n < n := Nat.lt_of_le_of_lt h1 (Nat.sub_lt (by omega) (by omega))
    exact Nat.lt_trans h2 h

/-- **THE LAYER SUM AT A CUT POINT.**  For `n < M`, the truncation of the `n`-th
term of the Erdős series at the cut point `M` is `jsp87Term n` *plus one extra
layer*, namely the layer `k = ω n`, which is `1` because `ω n ≥ ω n`.  That single
term is the only obstruction to turning §7 into an identity, and it is exactly the
layer `k = 0` of the cumulative series (`jsp87CumulSeries 0 = 1`, rational). -/
theorem jsp87_levelSum_range (n M : ℕ) (h : n < M) :
    (∑ k ∈ Finset.range M, jsp87LayerTerm k n) = jsp87Term n + ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hle : omega n + 1 ≤ M := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]
      have hM : 1 ≤ M := by
        rw [hn] at h
        omega
      simpa using hM
    · have h2 : omega n ≤ n - 1 := omega_lt (Nat.succ_le_iff.mpr hn)
      have h3 : n - 1 < n := Nat.sub_lt (by omega) (by omega)
      have h4 : omega n + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt h2 h3)
      exact le_trans h4 (Nat.le_of_lt h)
  have hsub : Finset.range (omega n + 1) ⊆ Finset.range M := by
    intro k hk
    have hk' : k < omega n + 1 := Finset.mem_range.mp hk
    have hle' : omega n + 1 ≤ M := hle
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le hk' hle')
  have hzero : ∀ k ∈ Finset.range M, k ∉ Finset.range (omega n + 1) →
      jsp87LayerTerm k n = 0 := by
    intro k _ hknot
    have hknot' : ¬ (k < omega n + 1) := fun hlt => hknot (Finset.mem_range.mpr hlt)
    have hk' : omega n + 1 ≤ k := Nat.le_of_not_gt hknot'
    have hge : omega n ≤ k := le_trans (Nat.le_of_lt (Nat.lt_succ_self (omega n))) hk'
    have hlt : omega n < k := by
      rcases Nat.lt_or_ge k (omega n) with h0 | h0
      · exact absurd (Nat.lt_of_lt_of_le h0 hge) (Nat.lt_irrefl _)
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (omega n)) hk'
    have hbit : jsp87AtLeast k n = 0 := (jsp87AtLeast_eq_zero_iff k n).mpr hlt
    simp only [jsp87LayerTerm, hbit, Nat.cast_zero, zero_mul]
  have hbit0 : jsp87AtLeast (omega n) n = 1 :=
    (jsp87AtLeast_eq_one_iff (omega n) n).mpr (Nat.le_refl _)
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ,
    jsp87LayerTerm_sum_eq n]
  have hone : jsp87LayerTerm (omega n) n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
    simp only [jsp87LayerTerm, hbit0, Nat.cast_one, one_mul]
  rw [hone]

/-- **THE FINITE LAYER DECOMPOSITION.**  At every cut point `M`, the truncation of
the Erdős series, *plus the all-ones geometric sum* (the contribution of the
layer `k = ω n`, summed over `n < M`), is exactly the sum of the truncations of
the cumulative layer series:

`∑_{n<M} ω n · 2^-(n+1) + ∑_{n<M} 2^-(n+1) = ∑_{k<M} ∑_{n<M} [ω n ≥ k] · 2^-(n+1)`.

This is the finite form of the identity `jsp87Series + 1 = ∑' k, jsp87CumulSeries k`;
the infinite form needs a Fubini argument for a countable sum, which Mathlib does
not have for `ℝ`, and which would not settle the headline anyway (a countable sum
of provably irrational numbers may well be rational — and that is exactly why the
headline needs the digit aperiodicity of round 41/46, not a decomposition). -/
theorem jsp87_partial_eq_sum_level (M : ℕ) :
    (∑ n ∈ Finset.range M, jsp87Term n) + ∑ n ∈ Finset.range M, ((2 : ℝ) ^ (n + 1))⁻¹
      = ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range M, jsp87LayerTerm k n := by
  calc (∑ n ∈ Finset.range M, jsp87Term n) + ∑ n ∈ Finset.range M, ((2 : ℝ) ^ (n + 1))⁻¹
      = ∑ n ∈ Finset.range M, (jsp87Term n + ((2 : ℝ) ^ (n + 1))⁻¹) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ n ∈ Finset.range M, ∑ k ∈ Finset.range M, jsp87LayerTerm k n := by
      rw [Finset.sum_congr rfl (fun n hn =>
        (jsp87_levelSum_range n M (Finset.mem_range.mp hn)).symm)]
    _ = ∑ k ∈ Finset.range M, ∑ n ∈ Finset.range M, jsp87LayerTerm k n := by
      rw [Finset.sum_comm]

/-! ## 3. The infinite join, in column form -/

/-- **THE COLUMN AT `n`.**  The number of layers at `n`, weighted by `2^-(n+1)`:
`jsp87LayerColumn n = (ω n + 1) · 2^-(n+1)`, i.e. `jsp87Term n` plus the layer
`k = 0`. -/
noncomputable def jsp87LayerColumn (n : ℕ) : ℝ :=
  ((omega n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

theorem jsp87LayerColumn_eq (n : ℕ) :
    jsp87LayerColumn n = jsp87Term n + (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hcast : ((omega n + 1 : ℕ) : ℝ) = ((omega n : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  unfold jsp87LayerColumn
  rw [hcast]
  simp only [jsp87Term]
  ring

theorem jsp87LayerColumn_nonneg (n : ℕ) : 0 ≤ jsp87LayerColumn n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The column series is summable, because it is the termwise sum of two
summable series (the Erdős series and the geometric series). -/
theorem summable_jsp87LayerColumn : Summable jsp87LayerColumn := by
  have h1 : Summable jsp87Term := summable_omega_mul_inv_two_pow
  have h2 : Summable (fun n : ℕ => (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    simpa using (summable_bitTerm_one 0)
  have h3 := h1.add h2
  refine h3.congr fun n => (jsp87LayerColumn_eq n).symm

/-- **THE INFINITE JOIN, COLUMN FORM.**  The Erdős series *plus one* is the sum
over the cut points of the *number of layers* at that cut point:

`jsp87Series + 1 = ∑' n, (ω n + 1) · 2^-(n+1)`.

This is the layer-cake identity summed over `n`, and it is what makes the Erdős
series a **countable integer-weighted combination of the level series of round
83**: the column at `n` carries `ω n + 1` unit layers, and the extra `1` is the
layer `k = 0`, whose total weight is `∑' n, 2^-(n+1) = 1`.  No Fubini is needed
here: both sides are single `tsum`s indexed by `n`. -/
theorem jsp87Series_add_one_eq_tsum_columns :
    jsp87Series + 1 = ∑' n, jsp87LayerColumn n := by
  have h1 : HasSum jsp87Term jsp87Series := jsp87_convergence
  have h2 : HasSum (fun n : ℕ => (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (∑' (k : ℕ), (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
    simpa only [one_mul, Nat.zero_add] using (summable_bitTerm_one 0).hasSum
  have h3 : HasSum (fun n : ℕ => jsp87Term n + (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (jsp87Series + ∑' (k : ℕ), (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := h1.add h2
  have hcol : ∀ (n : ℕ), jsp87Term n + (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ = jsp87LayerColumn n :=
    fun n => (jsp87LayerColumn_eq n).symm
  rw [← tsum_congr hcol, h3.tsum_eq, tsum_bitTerm_one_zero]

/-- The same identity with the column written out. -/
theorem jsp87Series_add_one_eq_tsum :
    jsp87Series + 1 = ∑' n, ((omega n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  rw [jsp87Series_add_one_eq_tsum_columns]
  exact tsum_congr fun _ => rfl

/-- **THE COLUMN SERIES HAS SUM `S + 1`** — the same statement in `HasSum` form. -/
theorem hasSum_jsp87LayerColumn : HasSum jsp87LayerColumn (jsp87Series + 1) := by
  rw [jsp87Series_add_one_eq_tsum_columns]
  exact summable_jsp87LayerColumn.hasSum

/-! ## 4. The infinite join, in row form -/

/-! ## 5. The missing row form: an exact plan

To prove `jsp87Series + 1 = ∑' k, jsp87AtLeastSeries k` one needs, writing
`T M = ∑_{k<M} jsp87AtLeastSeries k`:

1. `Summable (fun k => jsp87AtLeastSeries k)`.  Available route: each row is
   `≤ 2^-(2^k - 1)` (because `ω n ≥ k` forces `n ≥ 2^k`, by `two_pow_omega_le`),
   and `2^-(2^k-1) ≤ 2^-k`; then `Summable.of_nonneg_of_le` against
   `summable_two_pow_negK` (as in `BaseFamily.lean:207`).
2. `T M ≤ S + 1` and `S + 1 ≤ T M + M · 2^-M` for every `M`.  The first needs the
   *finite* interchange `∑_{k<M} ∑' n, … = ∑' n, ∑_{k<M} …`, obtainable from
   `hasProd_iff_tendsto_nat` (`Multipliable`/`Summable`) plus
   `Filter.Tendsto.le_of_tendsto_of_tendsto_of_le_of_le'` — which does not exist
   in this Mathlib; the workaround is to prove both sides equal by a `calc` with
   `Summable.tsum_add` instead of by comparison.  The second follows from
   `jsp87_partial_eq_sum_level` plus `jsp87LevelTerm k n = 0` for `k ≥ ω n + 1`.
3. `M · 2^-M → 0`: `Tendsto (fun M => (M : ℝ) * 2^-M) atTop (nhds 0)`, proved from
   `exists_pow_lt_of_lt_one` (already in `BlockPeriod.lean`) as
   `Filter.tendsto_atTop.2 ⟨ε, hε, fun M hM => …⟩`.  Then the `≤` passes to the
   limit *without* any limit-comparison lemma, using the fact that for every
   `ε > 0` there is `M` with `S + 1 < T M + ε`.

Alternatively: prove the row form by exhibiting the double sum as a
`tsum_sigma`/`Fintype`-sum over `ℕ × ℕ` in a `HasProd` form, where Mathlib's
`Equiv.swap`-based lemmas for products of series *do* exist for unconditionally
convergent families. -/

end JSP87
