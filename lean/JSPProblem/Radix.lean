/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Primary

set_option maxHeartbeats 800000

/-!
# JSP-000087 : the Erdős digit criterion in ARBITRARY RADIX

Every previous round of this formalization worked in **base `2`**: the Lambert
reduction (`JSPProblem/Lambert*.lean`), the carry scaffold
(`JSPProblem/Diophantine.lean`), the gcd arithmetic (`JSPProblem/LambertGcd.lean`),
the carry dynamics (`JSPProblem/Periodicity.lean`), the digit bookkeeping
(`JSPProblem/DigitCarry.lean`), the carry-excess/sieve content
(`JSPProblem/CarryExcess.lean`), the block arithmetic (`JSPProblem/BlockPeriod.lean`),
the primary (carry-free) expansion (`JSPProblem/Primary.lean`) and the doubling map
on the carries (`JSPProblem/CarryDoubling.lean`).  This file changes the one
parameter none of them varied: **the radix**.

The reason the radix matters is the *no-carry condition*.  Round 47 proved that a
`{0,1}`-valued digit string is irrational iff it is aperiodic, and that the
parity string `ω n mod 2` is aperiodic, whence `∑' n, (ω n mod 2) 2^-(n+1)` is
irrational.  In radix `q` the digit strings that never carry are exactly those
with `f n ≤ q − 2`, and in *every* radix there is a carry-free digit string built
from `ω`: the reduction `ω n mod (q − 1)`.  So this file

* generalises the whole criterion to arbitrary `q ≥ 3` (`jsp87Radix_irrational_iff`);
* proves that `ω` is aperiodic **modulo every `m ≥ 2`**
  (`omega_mod_not_eventuallyPeriodic`), not just modulo `2`;
* obtains **three new complete irrationality theorems**, one per radix:
  the reduced-`ω` series (`jsp87OmegaModSeries_irrational`), Erdős' prime constant
  in every radix (`jsp87RadixPrimeSeries_irrational`), and the square-indicator
  series in every radix (`jsp87RadixSquareSeries_irrational`);
* and records, as a *theorem*, the precise reason none of this reaches
  `jsp_000087_main`: the Erdős digit string itself violates the no-carry
  condition in **every** radix (`jsp87_noCarry_fails_any_radix`), because `ω` is
  unbounded — so the method which decides the reduced series provably cannot be
  applied to `ω` itself.
-/

namespace JSP87

/-! ## 0.  The radix-`q` digit series -/

/-- The `n`-th digit place of the radix-`q` expansion of `f`. -/
noncomputable def jsp87RadixTerm (f : ℕ → ℕ) (q n : ℕ) : ℝ :=
  ((f n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹

/-- **`T_q f = ∑' n, f n q^-(n+1)`**: the real number whose base-`q` digits
are `f`.  For `q = 2` this is `jsp87BinarySeries` of round 47. -/
noncomputable def jsp87RadixSeries (f : ℕ → ℕ) (q : ℕ) : ℝ :=
  ∑' n : ℕ, jsp87RadixTerm f q n

/-- The no-carry hypothesis, in a convenient form. -/
def jsp87NoCarry (f : ℕ → ℕ) (q : ℕ) : Prop := ∀ n, f n ≤ q - 2

theorem natCast_le_real {m d : ℕ} (h : m ≤ d) : ((m : ℕ) : ℝ) ≤ (d : ℕ) := Nat.cast_le.mpr h

theorem jsp87RadixTerm_nonneg (f : ℕ → ℕ) (q n : ℕ) : 0 ≤ jsp87RadixTerm f q n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- `q^-(n+1) = (q⁻¹)^(n+1)`: the general analogue of `two_pow_neg_eq`. -/
theorem radix_neg_eq (q n : ℕ) : ((q : ℝ) ^ (n + 1))⁻¹ = (q : ℝ)⁻¹ ^ (n + 1) := by
  rw [inv_pow]

/-- `|q⁻¹| < 1` as soon as `q ≥ 2`. -/
theorem radix_inv_abs_lt_one (q : ℕ) (hq : 2 ≤ q) : |(q : ℝ)⁻¹| < 1 := by
  have hq0 : 0 < q := by omega
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  rw [abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ)⁻¹)]
  exact (inv_lt_one₀ (by exact_mod_cast hq0)).mpr hq1

theorem summable_jsp87RadixTerm_geom (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => (1 : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
  have h : Summable (fun n : ℕ => (q : ℝ)⁻¹ ^ n) :=
    summable_geometric_of_abs_lt_one (r := (q : ℝ)⁻¹) (radix_inv_abs_lt_one q hq)
  have h2 : Summable (fun n : ℕ => (q : ℝ)⁻¹ * (q : ℝ)⁻¹ ^ n) := h.mul_left (q : ℝ)⁻¹
  have h3 : Summable (fun n : ℕ => (q : ℝ)⁻¹ ^ (n + 1)) := by
    refine h2.congr fun n => ?_
    rw [pow_succ]
    ring
  exact h3.congr (fun n => by rw [radix_neg_eq q n, one_mul])

/-- **The value of the geometric majorant**: `∑' n, q^-(n+1) = (q − 1)⁻¹`. -/
theorem tsum_jsp87RadixTerm_geom (q : ℕ) (hq : 2 ≤ q) :
    (∑' n : ℕ, (1 : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) = ((q : ℝ) - 1)⁻¹ := by
  have hr : |(q : ℝ)⁻¹| < 1 := radix_inv_abs_lt_one q hq
  have hv := tsum_geometric_of_abs_lt_one (r := (q : ℝ)⁻¹) hr
  have hstep : ∀ n : ℕ, (1 : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ = (q : ℝ)⁻¹ * ((q : ℝ)⁻¹) ^ n := by
    intro n
    calc (1 : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ = (1 : ℝ) * ((q : ℝ)⁻¹) ^ (n + 1) := by rw [radix_neg_eq q n]
      _ = (1 : ℝ) * (((q : ℝ)⁻¹) ^ n * (q : ℝ)⁻¹) := by rw [pow_succ]
      _ = (q : ℝ)⁻¹ * ((q : ℝ)⁻¹) ^ n := by rw [one_mul, mul_comm]
  calc (∑' n : ℕ, (1 : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) = ∑' n : ℕ, (q : ℝ)⁻¹ * ((q : ℝ)⁻¹) ^ n :=
        tsum_congr hstep
    _ = (q : ℝ)⁻¹ * (∑' n : ℕ, ((q : ℝ)⁻¹) ^ n) :=
      Summable.tsum_mul_left (q : ℝ)⁻¹ (summable_geometric_of_abs_lt_one hr)
    _ = (q : ℝ)⁻¹ * (1 - (q : ℝ)⁻¹)⁻¹ := by rw [hv]
    _ = ((q : ℝ) - 1)⁻¹ := by
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hkey : (1 - (q : ℝ)⁻¹)⁻¹ = ((q : ℝ) - 1)⁻¹ * (q : ℝ) := by field_simp
      rw [hkey]
      field_simp

/-- `∑' n, d q^-(n+1)` is summable for every constant digit `d`. -/
theorem summable_radix_const (q d : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => ((d : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
  simpa using (summable_jsp87RadixTerm_geom q hq).mul_left ((d : ℕ) : ℝ)

/-- **A digit string with no carrying gives a summable series.** -/
theorem summable_jsp87RadixTerm (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) :
    Summable (jsp87RadixTerm f q) := by
  have hle : ∀ n : ℕ, jsp87RadixTerm f q n ≤ ((q - 2 : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    rw [jsp87RadixTerm]
    exact mul_le_mul_of_nonneg_right (natCast_le_real (hf n)) (by positivity)
  have h1 : Summable (fun n : ℕ => ((q - 2 : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) :=
    summable_radix_const q (q - 2) (by omega)
  exact Summable.of_nonneg_of_le (jsp87RadixTerm_nonneg f q) hle h1

/-! ## 1.  The prefix integer, the tail, and the split -/

/-- The radix-`q` prefix `A f q N = ∑_{n<N} f n q^{N-n-1}`. -/
def jsp87RadixInt (f : ℕ → ℕ) (q N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, f n * q ^ (N - n - 1)

theorem jsp87RadixInt_cast (f : ℕ → ℕ) (q N : ℕ) :
    (jsp87RadixInt f q N : ℝ) = ∑ i ∈ Finset.range N, (f i : ℝ) * (q : ℝ) ^ (N - i - 1) := by
  simp only [jsp87RadixInt, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

/-- **THE RADIX-`q` TAIL** `U f q N = ∑' k, f (N+k) q^-(k+1)`. -/
noncomputable def jsp87RadixTail (f : ℕ → ℕ) (q N : ℕ) : ℝ :=
  ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹

theorem summable_jsp87RadixTail (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ) :
    Summable (fun k : ℕ => ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) := by
  have hge : Summable (fun k : ℕ => ((q - 2 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) :=
    summable_radix_const q (q - 2) (by omega)
  refine Summable.of_nonneg_of_le ?_ ?_ hge
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro k
    exact mul_le_mul_of_nonneg_right (natCast_le_real (hf (N + k))) (by positivity)

theorem jsp87RadixTail_nonneg (f : ℕ → ℕ) (q N : ℕ) : 0 ≤ jsp87RadixTail f q N :=
  tsum_nonneg fun k => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **NO CARRYING IN RADIX `q`.**  If every digit satisfies `f n ≤ q − 2` then the
rescaled tail is *strictly* below `1` at every cut point, uniformly in `N`:
`U f q N ≤ (q−2)/(q−1) < 1`.  The digit string of `T_q f` is therefore exactly
`f`, with no carrying at any place. -/
theorem jsp87RadixTail_lt_one (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ) :
    jsp87RadixTail f q N < 1 := by
  have hge : Summable (fun k : ℕ => ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) :=
    summable_radix_const q (q - 1) (by omega)
  have hle : ∀ k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹
      ≤ ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := by
    intro k
    have h2 := hf (N + k)
    have h1 : f (N + k) ≤ q - 1 := by omega
    exact mul_le_mul_of_nonneg_right (natCast_le_real h1) (by positivity)
  have hlt : ((f (N + 0) : ℕ) : ℝ) * ((q : ℝ) ^ (0 + 1))⁻¹
      < ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (0 + 1))⁻¹ := by
    have h2 := hf N
    have h1 : f N + 1 ≤ q - 1 := by omega
    exact mul_lt_mul_of_pos_right (by exact_mod_cast h1) (by positivity)
  have hsum := Summable.tsum_lt_tsum hle hlt (summable_jsp87RadixTail f hq hf N) hge
  have hA : (∑' k : ℕ, ((q - 1 : ℕ) : ℝ) * ((1 : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹))
      = ((q - 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := by
    rw [Summable.tsum_mul_left ((q - 1 : ℕ) : ℝ) (summable_jsp87RadixTerm_geom q (by omega)),
      tsum_jsp87RadixTerm_geom q (by omega)]
  have hcancel : ((q - 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ = 1 := by
    have hq1 : (1 : ℕ) ≤ q := by omega
    have hsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub hq1]
      norm_num
    have hqpos : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    have hz : ((q : ℝ) - 1) ≠ 0 := by linarith
    rw [hsub, mul_inv_cancel₀ hz]
  have hB : (∑' k : ℕ, ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹)
      = ((q - 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := by
    calc (∑' k : ℕ, ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹)
        = ∑' k : ℕ, ((q - 1 : ℕ) : ℝ) * ((1 : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) :=
          tsum_congr fun k => by rw [one_mul]
      _ = ((q - 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := hA
  have h2 : (∑' k : ℕ, ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) = 1 := by
    rw [hB, hcancel]
  calc jsp87RadixTail f q N = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := rfl
    _ < ∑' k : ℕ, ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := hsum
    _ = 1 := h2

theorem jsp87Radix_series_eq_sum_add_tail (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    (N : ℕ) :
    jsp87RadixSeries f q = (∑ i ∈ Finset.range N, jsp87RadixTerm f q i)
      + ∑' k : ℕ, jsp87RadixTerm f q (k + N) :=
  (Summable.sum_add_tsum_nat_add N (summable_jsp87RadixTerm f hq hf)).symm

/-- `q^-(i+1) = q^-N · q^{N-i-1}`: the rescaling identity at the prefix. -/
theorem radix_neg_eq_scaled (q N i : ℕ) (hi : i < N) (hq0 : q ≠ 0) :
    ((q : ℝ) ^ (i + 1))⁻¹ = ((q : ℝ) ^ N)⁻¹ * (q : ℝ) ^ (N - i - 1) := by
  have hN : N = (N - i - 1) + (i + 1) := by omega
  have hA : (q : ℝ) ^ N = (q : ℝ) ^ (N - i - 1) * (q : ℝ) ^ (i + 1) :=
    (congrArg (fun m : ℕ => (q : ℝ) ^ m) hN).trans (pow_add (q : ℝ) (N - i - 1) (i + 1))
  have hz : (q : ℝ) ^ (N - i - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq0)
  calc ((q : ℝ) ^ (i + 1))⁻¹
      = ((q : ℝ) ^ (i + 1))⁻¹ * ((q : ℝ) ^ (N - i - 1))⁻¹ * (q : ℝ) ^ (N - i - 1) := by
        rw [mul_assoc]
        simp [hz]
    _ = (((q : ℝ) ^ (N - i - 1) * (q : ℝ) ^ (i + 1))⁻¹) * (q : ℝ) ^ (N - i - 1) :=
        by rw [DivisionMonoid.mul_inv_rev]
    _ = ((q : ℝ) ^ N)⁻¹ * (q : ℝ) ^ (N - i - 1) := by rw [← hA]

theorem jsp87Radix_sum_range (f : ℕ → ℕ) (q : ℕ) (N : ℕ) (_hN : 1 ≤ N) (hq0 : q ≠ 0) :
    (∑ i ∈ Finset.range N, jsp87RadixTerm f q i)
      = ((q : ℝ) ^ N)⁻¹ * (jsp87RadixInt f q N : ℝ) := by
  have hterm : ∀ i ∈ Finset.range N,
      jsp87RadixTerm f q i = ((q : ℝ) ^ N)⁻¹ * ((f i : ℝ) * (q : ℝ) ^ (N - i - 1)) := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    rw [jsp87RadixTerm, radix_neg_eq_scaled q N i hi' hq0]
    ring
  calc (∑ i ∈ Finset.range N, jsp87RadixTerm f q i)
      = ((q : ℝ) ^ N)⁻¹ * ∑ i ∈ Finset.range N, (f i : ℝ) * (q : ℝ) ^ (N - i - 1) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    _ = ((q : ℝ) ^ N)⁻¹ * (jsp87RadixInt f q N : ℝ) := by rw [jsp87RadixInt_cast]

/-- Rescaling the digit place at `N + k` by `q^N` erases `N`. -/
theorem q_pow_mul_radixTerm_shift (f : ℕ → ℕ) (q N k : ℕ) (hq0 : q ≠ 0) :
    (q : ℝ) ^ N * jsp87RadixTerm f q (N + k)
      = ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := by
  simp only [jsp87RadixTerm]
  have hb : (q : ℝ) ^ N * (q : ℝ) ^ (k + 1) = (q : ℝ) ^ (N + k + 1) := by
    rw [← pow_add]
    congr 1
  have hz : (q : ℝ) ^ N ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq0)
  have hD : (q : ℝ) ^ N * ((q : ℝ) ^ (N + k + 1))⁻¹ = ((q : ℝ) ^ (k + 1))⁻¹ := by
    rw [← hb]
    calc (q : ℝ) ^ N * ((q : ℝ) ^ N * (q : ℝ) ^ (k + 1))⁻¹
        = (q : ℝ) ^ N * (((q : ℝ) ^ (k + 1))⁻¹ * ((q : ℝ) ^ N)⁻¹) := by
          rw [DivisionMonoid.mul_inv_rev]
      _ = (q : ℝ) ^ N * ((q : ℝ) ^ N)⁻¹ * ((q : ℝ) ^ (k + 1))⁻¹ := by ring
      _ = ((q : ℝ) ^ (k + 1))⁻¹ := by rw [mul_inv_cancel₀ hz, one_mul]
  calc (q : ℝ) ^ N * (((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (N + k + 1))⁻¹)
      = ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ N * ((q : ℝ) ^ (N + k + 1))⁻¹) := by ring
    _ = ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := by rw [hD]

/-- **THE SPLIT, IN RADIX `q`.**  `q^N · T_q f = A f q N + U f q N`, with the
prefix a natural number and the tail carrying no factor of `q^N`. -/
theorem jsp87Radix_split (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ)
    (hN : 1 ≤ N) :
    (q : ℝ) ^ N * jsp87RadixSeries f q = (jsp87RadixInt f q N : ℝ) + jsp87RadixTail f q N := by
  rw [jsp87Radix_series_eq_sum_add_tail f hq hf N, jsp87Radix_sum_range f q N hN (by omega)]
  have h1 : (q : ℝ) ^ N * ((q : ℝ) ^ N)⁻¹ = (1 : ℝ) := by field_simp
  rw [mul_add, ← mul_assoc, h1, one_mul]
  congr 1
  unfold jsp87RadixTail
  have hs : Summable (fun k : ℕ => jsp87RadixTerm f q (k + N)) :=
    (summable_nat_add_iff (f := jsp87RadixTerm f q) N).2 (summable_jsp87RadixTerm f hq hf)
  calc (q : ℝ) ^ N * (∑' k : ℕ, jsp87RadixTerm f q (k + N))
      = ∑' k : ℕ, (q : ℝ) ^ N * jsp87RadixTerm f q (k + N) :=
        (Summable.tsum_mul_left _ hs).symm
    _ = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹ := by
        refine tsum_congr fun k => ?_
        rw [Nat.add_comm k N, q_pow_mul_radixTerm_shift f q N k (by omega)]

/-! ## 2.  The tail recurrence, and the digits -/

/-- `a · (a⁻¹)^{n+1} = (a⁻¹)^n`: shifting the exponent by the prefactor. -/
theorem mul_inv_pow_succ (a : ℝ) (ha : a ≠ 0) (n : ℕ) : a * a⁻¹ ^ (n + 1) = a⁻¹ ^ n := by
  induction n with
  | zero => rw [pow_succ, pow_zero, one_mul, mul_inv_cancel₀ ha]
  | succ n ih =>
      calc a * a⁻¹ ^ (Nat.succ n + 1) = a * (a⁻¹ ^ (n + 1) * a⁻¹) := by rw [pow_succ]
        _ = (a * a⁻¹ ^ (n + 1)) * a⁻¹ := by ring
        _ = a⁻¹ ^ n * a⁻¹ := by rw [ih]
        _ = a⁻¹ ^ (n + 1) := (pow_succ a⁻¹ n).symm

/-- `∑' n, d (q⁻¹)^n` is summable for every constant `d`. -/
theorem summable_mul_inv_pow (q d : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => ((d : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ n) :=
  (summable_geometric_of_abs_lt_one (r := (q : ℝ)⁻¹) (radix_inv_abs_lt_one q hq)).mul_left
    ((d : ℕ) : ℝ)

/-- **THE TAIL RECURRENCE IN RADIX `q`.**  `U f q (N+1) = q · U f q N − f N`. -/
theorem jsp87RadixTail_succ (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ) :
    jsp87RadixTail f q (N + 1) = (q : ℝ) * jsp87RadixTail f q N - (f N : ℝ) := by
  have hs : Summable (fun k : ℕ => ((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ k) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (summable_mul_inv_pow q (q - 2) (by omega))
    · intro k
      exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
    · intro k
      exact mul_le_mul_of_nonneg_right (natCast_le_real (hf (N + k))) (by positivity)
  have hsplit : (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ k)
      = (f N : ℝ) + ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ (k + 1) := by
    have h := Summable.sum_add_tsum_nat_add 1 hs
    calc (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ k)
        = (∑ i ∈ Finset.range 1, ((f (N + i) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ i)
            + ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ (k + 1) := h.symm
      _ = ((f N : ℕ) : ℝ) + ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ (k + 1) := by
        rw [Finset.sum_range_one, Nat.add_zero, pow_zero, mul_one]
  have htwo : (q : ℝ) * jsp87RadixTail f q N
      = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ k := by
    unfold jsp87RadixTail
    calc (q : ℝ) * (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹)
        = ∑' k : ℕ, (q : ℝ) * (((f (N + k) : ℕ) : ℝ) * ((q : ℝ) ^ (k + 1))⁻¹) :=
          (Summable.tsum_mul_left (q : ℝ) (summable_jsp87RadixTail f hq hf N)).symm
      _ = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ k := by
          refine tsum_congr fun k => ?_
          rw [radix_neg_eq q k]
          calc (q : ℝ) * (((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ (k + 1))
              = ((f (N + k) : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ)⁻¹ ^ (k + 1)) := by ring
            _ = ((f (N + k) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ k := by
              rw [mul_inv_pow_succ (q : ℝ) (by exact_mod_cast (ne_of_gt (by omega : 0 < q))) k]
  have htail : jsp87RadixTail f q (N + 1)
      = ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ (k + 1) := by
    unfold jsp87RadixTail
    refine tsum_congr fun k => ?_
    have h1 : N + 1 + k = N + (k + 1) := by omega
    rw [h1, radix_neg_eq q k]
  rw [htail, htwo, hsplit]
  ring

/-- **THE `q`-ARY DIGITAL EXTRACTION.**  `⌊q · x⌋ − q ⌊x⌋ = ⌊q · fract x⌋`: the `q`-ary
digit of `x` is the `q`-ary digit of its fractional part.  (Note that
`⌊q · x⌋ = q ⌊x⌋` is *false* in general, e.g. `x = 3/5`, `q = 2`; Mathlib has no
lemma of this shape for `ℤ`-scalars.) -/
theorem floor_natCast_mul_sub (q : ℕ) (x : ℝ) :
    ⌊(q : ℝ) * x⌋ - (q : ℤ) * ⌊x⌋ = ⌊(q : ℝ) * Int.fract x⌋ := by
  have h1 : (q : ℝ) * x = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) + (q : ℝ) * Int.fract x := by
    calc (q : ℝ) * x = (q : ℝ) * ((((⌊x⌋ : ℤ) : ℝ)) + Int.fract x) := by rw [Int.floor_add_fract x]
      _ = (q : ℝ) * ((⌊x⌋ : ℤ) : ℝ) + (q : ℝ) * Int.fract x := by rw [(mul_add _ _ _).symm]
      _ = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) + (q : ℝ) * Int.fract x := by push_cast; ring
  rw [h1, Int.floor_intCast_add]
  ring

/-- **THE `q`-ARY MULTIPLICATION MAP ON FRACTIONAL PARTS.**
`fract (q · x) = fract (q · fract x)`. -/
theorem Int.fract_natCast_mul (q : ℕ) (x : ℝ) :
    Int.fract ((q : ℝ) * x) = Int.fract ((q : ℝ) * Int.fract x) := by
  have h1 : (q : ℝ) * x = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) + (q : ℝ) * Int.fract x := by
    calc (q : ℝ) * x = (q : ℝ) * ((((⌊x⌋ : ℤ) : ℝ)) + Int.fract x) := by rw [Int.floor_add_fract x]
      _ = (q : ℝ) * ((⌊x⌋ : ℤ) : ℝ) + (q : ℝ) * Int.fract x := by rw [(mul_add _ _ _).symm]
      _ = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) + (q : ℝ) * Int.fract x := by push_cast; ring
  rw [h1, Int.fract_intCast_add]

/-- **NO CARRYING, IN FLOORS, IN RADIX `q`.**  The `q`-ary floor of `q^N T_q f` is
*exactly* the prefix integer `A f q N`. -/
theorem jsp87Radix_floor (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ)
    (hN : 1 ≤ N) : ⌊(q : ℝ) ^ N * jsp87RadixSeries f q⌋ = (jsp87RadixInt f q N : ℤ) := by
  have hd := jsp87Radix_split f hq hf N hN
  rw [hd, Int.floor_eq_iff]
  have hbridge : (((jsp87RadixInt f q N : ℕ) : ℤ) : ℝ) = (jsp87RadixInt f q N : ℝ) := by
    norm_cast
  rw [hbridge]
  constructor
  · linarith [jsp87RadixTail_nonneg f q N]
  · linarith [jsp87RadixTail_lt_one f hq hf N]

/-- **The fractional part of the rescaled radix-`q` series is the radix tail.** -/
theorem jsp87Radix_fract (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ)
    (hN : 1 ≤ N) :
    Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q) = jsp87RadixTail f q N := by
  have hfloor := jsp87Radix_floor f hq hf N hN
  have hfr := Int.self_sub_floor ((q : ℝ) ^ N * jsp87RadixSeries f q)
  have hd := jsp87Radix_split f hq hf N hN
  have hcast : ((jsp87RadixInt f q N : ℤ) : ℝ) = (jsp87RadixInt f q N : ℝ) := by norm_cast
  rw [hfloor] at hfr
  rw [hcast] at hfr
  linarith

/-- **THE RADIX-`q` DIGIT THEOREM.**  Under the no-carry hypothesis, the `N`-th
base-`q` digit of `T_q f` *is* the digit `f N`:

`f N = ⌊q^{N+1} T_q f⌋ − q ⌊q^N T_q f⌋`.

For `q = 2` this is `jsp87Binary_digit` of round 47. -/
theorem jsp87Radix_digit (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N : ℕ)
    (hN : 1 ≤ N) :
    (f N : ℤ) = ⌊(q : ℝ) ^ (N + 1) * jsp87RadixSeries f q⌋
      - (q : ℤ) * ⌊(q : ℝ) ^ N * jsp87RadixSeries f q⌋ := by
  have hfrac := jsp87Radix_fract f hq hf N hN
  have hrec := jsp87RadixTail_succ f hq hf N
  have hkey : (q : ℝ) * jsp87RadixTail f q N = ((f N : ℕ) : ℝ) + jsp87RadixTail f q (N + 1) := by
    linarith
  have hfloor2 : ⌊(q : ℝ) * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q)⌋ = (f N : ℤ) := by
    rw [hfrac, hkey]
    have hc1 : (((f N : ℤ)) : ℝ) = ((f N : ℕ) : ℝ) := by norm_cast
    have hc2 : (((f N + 1 : ℤ)) : ℝ) = ((f N : ℕ) : ℝ) + 1 := by norm_cast
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · linarith [jsp87RadixTail_nonneg f q (N + 1)]
    · linarith [jsp87RadixTail_lt_one f hq hf (N + 1)]
  have hdig : ⌊(q : ℝ) ^ (N + 1) * jsp87RadixSeries f q⌋
        - (q : ℤ) * ⌊(q : ℝ) ^ N * jsp87RadixSeries f q⌋
      = ⌊(q : ℝ) * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q)⌋ := by
    convert floor_natCast_mul_sub q ((q : ℝ) ^ N * jsp87RadixSeries f q) using 1
    rw [pow_succ]
    ring
  rw [hdig, hfloor2]

/-! ## 3.  Rationality forces an eventually periodic radix digit string -/

/-- **The `q`-ary doubling map on fractional parts.** -/
theorem Int.fract_radix_pow_mul (q : ℕ) (x : ℝ) (N : ℕ) :
    Int.fract ((q : ℝ) ^ (N + 1) * x) = Int.fract ((q : ℝ) * Int.fract ((q : ℝ) ^ N * x)) := by
  have hpow : (q : ℝ) ^ (N + 1) = (q : ℝ) * (q : ℝ) ^ N := by rw [pow_succ]; ring
  rw [hpow]
  convert Int.fract_natCast_mul q ((q : ℝ) ^ N * x) using 1 <;> ring

/-- **Rationality quantises the fractional parts of a radix-`q` series.**  If
`T_q f = a / b` with `b > 0` then `fract (q^N T_q f) = c / b` with `0 ≤ c < b`. -/
theorem jsp87Radix_fract_eq_div {f : ℕ → ℕ} {q : ℕ} {N : ℕ} {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ)) (_hN : 1 ≤ N) :
    ∃ c : ℤ, 0 ≤ c ∧ c < (b : ℤ)
      ∧ Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q) = (c : ℝ) / (b : ℝ) :=
  Int.fract_eq_div_of_mul_natCast (b := b) hb (x := (q : ℝ) ^ N * jsp87RadixSeries f q)
    (m := ((q : ℕ) ^ N * a : ℤ)) (by
      have hcast : (q : ℝ) ^ N * (a : ℝ) = ((q : ℕ) ^ N * a : ℤ) := by norm_cast
      have hbnz : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
      rw [h]
      calc (b : ℝ) * ((q : ℝ) ^ N * ((a : ℝ) / (b : ℝ)))
          = ((b : ℝ) * (q : ℝ) ^ N * (a : ℝ)) / (b : ℝ) := by ring
        _ = (q : ℝ) ^ N * (a : ℝ) := by field_simp
        _ = ((q : ℕ) ^ N * a : ℤ) := hcast)

/-- **The numerator of `fract (q^N T_q f)`** under the rationality hypothesis. -/
noncomputable def jsp87RadixFracNum (f : ℕ → ℕ) (b q : ℕ) (N : ℕ) : ℕ :=
  (⌊(b : ℝ) * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q)⌋ : ℤ).toNat

theorem jsp87RadixFracNum_spec (f : ℕ → ℕ) {q : ℕ} (_hq : 3 ≤ q) (_hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ)) {N : ℕ}
    (hN : 1 ≤ N) :
    jsp87RadixFracNum f b q N < b
      ∧ Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q) = (jsp87RadixFracNum f b q N : ℝ) / (b : ℝ) := by
  obtain ⟨c, hc0, hc1, hc2⟩ := jsp87Radix_fract_eq_div (b := b) hb h hN
  have hmul : (b : ℝ) * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q) = (c : ℝ) := by
    rw [hc2]
    field_simp
  have hfloor : ⌊(b : ℝ) * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q)⌋ = c := by
    rw [hmul, Int.floor_intCast]
  have hcast : ((jsp87RadixFracNum f b q N : ℕ) : ℤ) = c := by
    show (↑((⌊(b : ℝ) * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q)⌋ : ℤ).toNat : ℕ) : ℤ) = c
    rw [Int.toNat_of_nonneg (by rw [hfloor]; exact hc0), hfloor]
  have hltN : jsp87RadixFracNum f b q N < b := by
    have hz' : ((jsp87RadixFracNum f b q N : ℕ) : ℤ) < (b : ℕ) := by rw [hcast]; exact hc1
    exact_mod_cast hz'
  refine ⟨hltN, ?_⟩
  have hR : ((jsp87RadixFracNum f b q N : ℕ) : ℝ) = (c : ℝ) := by norm_cast
  calc Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q) = (c : ℝ) / (b : ℝ) := hc2
    _ = (jsp87RadixFracNum f b q N : ℝ) / (b : ℝ) := by rw [hR]

/-- **Equal fractional parts have equal successors.** -/
theorem jsp87RadixFracNum_succ (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h' : jsp87RadixFracNum f b q i = jsp87RadixFracNum f b q j) :
    jsp87RadixFracNum f b q (i + 1) = jsp87RadixFracNum f b q (j + 1) := by
  have hs := jsp87RadixFracNum_spec f hq hf hb h hi
  have hs' := jsp87RadixFracNum_spec f hq hf hb h hj
  have hfrac : Int.fract ((q : ℝ) ^ (i + 1) * jsp87RadixSeries f q)
      = Int.fract ((q : ℝ) ^ (j + 1) * jsp87RadixSeries f q) := by
    rw [Int.fract_radix_pow_mul, Int.fract_radix_pow_mul, hs.2, hs'.2, h']
  have h1 := (jsp87RadixFracNum_spec f hq hf hb h (by omega : 1 ≤ i + 1)).2
  have h1' := (jsp87RadixFracNum_spec f hq hf hb h (by omega : 1 ≤ j + 1)).2
  rw [← hfrac] at h1'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have key : ((jsp87RadixFracNum f b q (i + 1) : ℕ) : ℝ) / (b : ℝ)
      = ((jsp87RadixFracNum f b q (j + 1) : ℕ) : ℝ) / (b : ℝ) := by
    rw [← h1, ← h1']
  have key' : ((jsp87RadixFracNum f b q (i + 1) : ℕ) : ℝ)
      = ((jsp87RadixFracNum f b q (j + 1) : ℕ) : ℝ) := (div_left_inj' hb0).mp key
  exact_mod_cast key'

theorem jsp87RadixFracNum_period_aux (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (h0 : jsp87RadixFracNum f b q i = jsp87RadixFracNum f b q j) (k : ℕ) :
    jsp87RadixFracNum f b q (i + k) = jsp87RadixFracNum f b q (j + k) := by
  induction k with
  | zero => rw [Nat.add_zero]; exact h0
  | succ k ih =>
      have h1 : jsp87RadixFracNum f b q (i + Nat.succ k)
          = jsp87RadixFracNum f b q (j + Nat.succ k) := by
        have hstep := jsp87RadixFracNum_succ f hq hf hb h (by omega) (by omega) ih
        convert hstep using 1
      exact h1

/-- **THE FINITE-RANGE ARGUMENT.**  The numerators of the fractional parts of
`q^N T_q f` live in `range b`, and the `q`-ary multiplication map is
deterministic, so they are eventually periodic. -/
theorem jsp87RadixFracNum_period (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧
      ∀ n, N ≤ n → jsp87RadixFracNum f b q (n + t) = jsp87RadixFracNum f b q n := by
  have hlt : ∀ i : ℕ, jsp87RadixFracNum f b q (i + 1) < b :=
    fun i => (jsp87RadixFracNum_spec f hq hf hb h (by omega)).1
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (b + 1) => (⟨jsp87RadixFracNum f b q (i.val + 1), hlt i.val⟩ : Fin b)) (by simp)
  have hne' : x.1 ≠ y.1 := fun hh => hne (Fin.ext hh)
  have h0 : jsp87RadixFracNum f b q (x.1 + 1) = jsp87RadixFracNum f b q (y.1 + 1) :=
    congrArg Fin.val heq
  rcases lt_trichotomy x.1 y.1 with hxy | hxy | hxy
  · have ht : 0 < y.1 - x.1 := by omega
    refine ⟨y.1 - x.1, x.1 + 1, ht, by omega, ?_⟩
    intro n hn
    have hk := jsp87RadixFracNum_period_aux f hq hf hb h (by omega) (by omega) h0
      (n - (x.1 + 1))
    rw [Nat.add_sub_of_le hn] at hk
    have hkey : n + (y.1 - x.1) = (y.1 + 1) + (n - (x.1 + 1)) := by omega
    rw [← hkey] at hk
    exact hk.symm
  · exact (hne' hxy).elim
  · have ht : 0 < x.1 - y.1 := by omega
    refine ⟨x.1 - y.1, y.1 + 1, ht, by omega, ?_⟩
    intro n hn
    have hk := jsp87RadixFracNum_period_aux f hq hf hb h (by omega) (by omega) h0.symm
      (n - (y.1 + 1))
    rw [Nat.add_sub_of_le hn] at hk
    have hkey : n + (x.1 - y.1) = (x.1 + 1) + (n - (y.1 + 1)) := by omega
    rw [← hkey] at hk
    exact hk.symm

/-- **`b · f N = q c(N) − c(N+1)`**: the radix digit is recovered from two
consecutive numerators of the fractional parts. -/
theorem jsp87Radix_digit_fracNum (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ)) {N : ℕ}
    (hN : 1 ≤ N) :
    (b : ℝ) * ((f N : ℕ) : ℝ)
      = (q : ℝ) * (jsp87RadixFracNum f b q N : ℝ)
        - (jsp87RadixFracNum f b q (N + 1) : ℝ) := by
  have hfrac : ∀ m (hm : 1 ≤ m), (b : ℝ) * Int.fract ((q : ℝ) ^ m * jsp87RadixSeries f q)
      = (jsp87RadixFracNum f b q m : ℝ) := by
    intro m hm
    have h2 := (jsp87RadixFracNum_spec f hq hf hb h hm).2
    rw [h2]
    field_simp
  have hfloor : ∀ m (hm : 1 ≤ m), (b : ℝ) * ⌊(q : ℝ) ^ m * jsp87RadixSeries f q⌋
      = (q : ℝ) ^ m * (a : ℝ) - (b : ℝ) * Int.fract ((q : ℝ) ^ m * jsp87RadixSeries f q) := by
    intro m hm
    have hx : (b : ℝ) * ((q : ℝ) ^ m * jsp87RadixSeries f q) = (q : ℝ) ^ m * (a : ℝ) := by
      have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
      rw [h]
      field_simp
    have hfr := Int.self_sub_floor ((q : ℝ) ^ m * jsp87RadixSeries f q)
    have hfr' : ((⌊(q : ℝ) ^ m * jsp87RadixSeries f q⌋ : ℤ) : ℝ)
        = (q : ℝ) ^ m * jsp87RadixSeries f q
            - Int.fract ((q : ℝ) ^ m * jsp87RadixSeries f q) := by
      linarith
    calc (b : ℝ) * ⌊(q : ℝ) ^ m * jsp87RadixSeries f q⌋
        = (b : ℝ) * ((q : ℝ) ^ m * jsp87RadixSeries f q
            - Int.fract ((q : ℝ) ^ m * jsp87RadixSeries f q)) := by rw [hfr']
      _ = (q : ℝ) ^ m * (a : ℝ) - (b : ℝ) * Int.fract ((q : ℝ) ^ m * jsp87RadixSeries f q) := by
        rw [mul_sub, hx]
  have hdig : ((f N : ℕ) : ℝ)
      = (((⌊(q : ℝ) ^ (N + 1) * jsp87RadixSeries f q⌋
          - (q : ℤ) * ⌊(q : ℝ) ^ N * jsp87RadixSeries f q⌋ : ℤ) : ℝ)) := by
    have hd := jsp87Radix_digit f hq hf N hN
    push_cast at hd ⊢
    exact_mod_cast hd
  have hpow : (q : ℝ) ^ (N + 1) = (q : ℝ) * (q : ℝ) ^ N := by rw [pow_succ]; ring
  calc (b : ℝ) * ((f N : ℕ) : ℝ)
      = (b : ℝ) * (((⌊(q : ℝ) ^ (N + 1) * jsp87RadixSeries f q⌋
          - (q : ℤ) * ⌊(q : ℝ) ^ N * jsp87RadixSeries f q⌋ : ℤ) : ℝ)) := by rw [hdig]
    _ = (b : ℝ) * ⌊(q : ℝ) ^ (N + 1) * jsp87RadixSeries f q⌋
          - (q : ℝ) * ((b : ℝ) * ⌊(q : ℝ) ^ N * jsp87RadixSeries f q⌋) := by
        push_cast
        ring
    _ = ((q : ℝ) ^ (N + 1) * (a : ℝ) - (b : ℝ)
          * Int.fract ((q : ℝ) ^ (N + 1) * jsp87RadixSeries f q))
          - (q : ℝ) * ((q : ℝ) ^ N * (a : ℝ) - (b : ℝ)
          * Int.fract ((q : ℝ) ^ N * jsp87RadixSeries f q)) := by
        rw [hfloor (N + 1) (by omega), hfloor N hN]
    _ = (q : ℝ) * (jsp87RadixFracNum f b q N : ℝ)
          - (jsp87RadixFracNum f b q (N + 1) : ℝ) := by
        rw [hfrac (N + 1) (by omega), hfrac N hN, hpow]
        ring

/-- **Equal numerators give equal digits.** -/
theorem jsp87Radix_digit_of_fracNum (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hc : jsp87RadixFracNum f b q i = jsp87RadixFracNum f b q j) :
    f i = f j := by
  have h1 := jsp87Radix_digit_fracNum f hq hf hb h hi
  have h2 := jsp87Radix_digit_fracNum f hq hf hb h hj
  have hsucc := jsp87RadixFracNum_succ f hq hf hb h hi hj hc
  have hkey : (b : ℝ) * ((f i : ℕ) : ℝ) = (b : ℝ) * ((f j : ℕ) : ℝ) := by
    rw [h1, h2, hsucc, hc]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  exact_mod_cast (mul_left_cancel₀ hb0 hkey)

/-- **THE CRITERION, FORWARD DIRECTION, IN RADIX `q`.**  If `T_q f = a / b` with
`b > 0` then the digit string `f` is eventually periodic.  Proved from scratch:
Mathlib has no statement about the base-`q` expansion of a real number. -/
theorem jsp87Radix_rational_imp_periodic (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87RadixSeries f q = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → f (n + t) = f n := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87RadixFracNum_period f hq hf hb h
  refine ⟨t, M, ht, hM, ?_⟩
  intro n hn
  exact jsp87Radix_digit_of_fracNum f hq hf hb h (by omega) (by omega) (hper n hn)

/-- **A radix-`q` digit string that is not eventually periodic gives an
irrational series.** -/
theorem jsp87Radix_irrational_of_notPeriodic (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q)
    (hf : jsp87NoCarry f q)
    (haper : ¬ ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → f (n + t) = f n) :
    Irrational (jsp87RadixSeries f q) := by
  show jsp87RadixSeries f q ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨r, hr⟩
  obtain ⟨t, N, ht, hN, hper⟩ := jsp87Radix_rational_imp_periodic f hq hf (Rat.den_pos r)
    (by rw [← hr, Rat.cast_def])
  exact haper ⟨t, N, ht, hN, hper⟩

/-! ## 4.  The exact value of a periodic radix-`q` series -/

/-- The `t`-digit block of `T_q f`, read as a real:
`β f q N t = ∑_{j<t} f (N+j) q^{t-1-j}`. -/
noncomputable def jsp87RadixBlock (f : ℕ → ℕ) (q N t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, ((f (N + j) : ℕ) : ℝ) * (q : ℝ) ^ (t - 1 - j)

/-- The block, read as a natural number. -/
def jsp87RadixBlockNat (f : ℕ → ℕ) (q N t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, f (N + j) * q ^ (t - j - 1)

theorem jsp87RadixBlockNat_cast (f : ℕ → ℕ) (q N t : ℕ) :
    (jsp87RadixBlockNat f q N t : ℝ) = jsp87RadixBlock f q N t := by
  simp only [jsp87RadixBlockNat, jsp87RadixBlock, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < t := Finset.mem_range.mp hj
  have hkey : t - j - 1 = t - 1 - j := by rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm 1 j]
  rw [hkey]

/-- **ITERATION OF THE TAIL RECURRENCE ALONG A BLOCK.**
`U f q (N + t) = q^t U f q N − β f q N t`. -/
theorem jsp87RadixTail_iter (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) (N t : ℕ) :
    jsp87RadixTail f q (N + t) = (q : ℝ) ^ t * jsp87RadixTail f q N - jsp87RadixBlock f q N t := by
  induction t with
  | zero =>
      have hb : jsp87RadixBlock f q N 0 = 0 := by simp [jsp87RadixBlock]
      rw [Nat.add_zero, hb, sub_zero]
      ring
  | succ t ih =>
      have hstep : ∀ j ∈ Finset.range t,
          ((f (N + j) : ℕ) : ℝ) * (q : ℝ) ^ (t - j)
            = (q : ℝ) * (((f (N + j) : ℕ) : ℝ) * (q : ℝ) ^ (t - 1 - j)) := by
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        have hkey : t - j = (t - 1 - j) + 1 := by omega
        rw [hkey, pow_succ]
        ring
      have hblock : jsp87RadixBlock f q N (t + 1)
          = (q : ℝ) * jsp87RadixBlock f q N t + (f (N + t) : ℝ) := by
        unfold jsp87RadixBlock
        have hkey : ∀ j ∈ Finset.range (t + 1),
            ((f (N + j) : ℕ) : ℝ) * (q : ℝ) ^ (t + 1 - 1 - j)
              = ((f (N + j) : ℕ) : ℝ) * (q : ℝ) ^ (t - j) := by
          intro j _
          congr 1
        rw [Finset.sum_congr rfl hkey, Finset.sum_range_succ, Finset.mul_sum,
          Finset.sum_congr rfl hstep, Nat.sub_self, pow_zero, mul_one]
      have h2 := jsp87RadixTail_succ f hq hf (N + t)
      have hsucc : (q : ℝ) ^ (t + 1) = (q : ℝ) * (q : ℝ) ^ t := by rw [pow_succ]; ring
      have hN : N + t + 1 = N + (t + 1) := by omega
      rw [hN] at h2
      rw [hblock, h2, hsucc, ih]
      ring

/-- `(q : ℝ)^t − 1 ≠ 0` for `2 ≤ q` and `1 ≤ t`: the period denominator of radix
`q` never vanishes. -/
theorem radix_pow_sub_one_ne_zero {q t : ℕ} (hq : 2 ≤ q) (ht : 1 ≤ t) :
    (q : ℝ) ^ t - 1 ≠ 0 := by
  have h2t : (2 : ℕ) ≤ 2 ^ t := by
    have := Nat.one_lt_two_pow (by omega : t ≠ 0)
    omega
  have hqt : (2 : ℕ) ≤ q ^ t := Nat.le_trans h2t (pow_le_pow_left' hq t)
  have hR : (2 : ℝ) ≤ (q : ℝ) ^ t := by exact_mod_cast hqt
  linarith

/-- **THE EXACT VALUE OF AN EVENTUALLY PERIODIC RADIX SERIES.**  If `f` is periodic
with period `t > 0` from `N` on, then

`q^N · T_q f = A f q N + β f q N t / (q^t − 1)`,

so a periodic `q`-ary digit string is a rational with denominator exactly
`(q^t − 1) · q^N`. -/
theorem jsp87Radix_series_eq_block (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {N t : ℕ} (ht : 0 < t) (hper : ∀ n, N ≤ n → f (n + t) = f n) (hN : 1 ≤ N) :
    (q : ℝ) ^ N * jsp87RadixSeries f q
      = (jsp87RadixInt f q N : ℝ) + jsp87RadixBlock f q N t / ((q : ℝ) ^ t - 1) := by
  have hU : jsp87RadixTail f q (N + t) = jsp87RadixTail f q N := by
    unfold jsp87RadixTail
    refine tsum_congr fun k => ?_
    have hk := hper (N + k) (by omega)
    have heq : N + t + k = (N + k) + t := by omega
    rw [heq, hk]
  have hiter := jsp87RadixTail_iter f hq hf N t
  rw [hU] at hiter
  have hkey : jsp87RadixBlock f q N t = jsp87RadixTail f q N * ((q : ℝ) ^ t - 1) := by
    linear_combination hiter
  have hne : (q : ℝ) ^ t - 1 ≠ 0 := radix_pow_sub_one_ne_zero (by omega) (by omega)
  have hval : jsp87RadixTail f q N = jsp87RadixBlock f q N t / ((q : ℝ) ^ t - 1) := by
    symm
    exact (div_eq_iff hne).mpr hkey
  have hd := jsp87Radix_split f hq hf N hN
  rw [hd, hval]

/-- **AN EVENTUALLY PERIODIC RADIX SERIES IS RATIONAL.** -/
theorem jsp87Radix_rational_of_periodic (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q)
    {N t : ℕ} (ht : 0 < t) (hper : ∀ n, N ≤ n → f (n + t) = f n) (hN : 1 ≤ N) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87RadixSeries f q = (a : ℝ) / (b : ℝ) := by
  have hval := jsp87Radix_series_eq_block f hq hf ht hper hN
  have h2t : (2 : ℕ) ≤ 2 ^ t := by
    have := Nat.one_lt_two_pow (by omega : t ≠ 0)
    omega
  have hqt : (2 : ℕ) ≤ q ^ t := Nat.le_trans h2t (pow_le_pow_left' (by omega : 2 ≤ q) t)
  have hqm1 : ((q : ℕ) ^ t - 1 : ℕ) ≠ 0 := Nat.ne_of_gt (by omega)
  have h1t : (1 : ℕ) ≤ q ^ t := by omega
  have hsub : ((q : ℕ) ^ t - 1 : ℕ) = ((q : ℝ) ^ t - 1 : ℝ) := by
    rw [Nat.cast_sub h1t]
    norm_num
  have hnum : ((jsp87RadixInt f q N * (q ^ t - 1) + jsp87RadixBlockNat f q N t : ℕ) : ℝ)
      = (jsp87RadixInt f q N : ℝ) * ((q : ℝ) ^ t - 1) + jsp87RadixBlock f q N t := by
    rw [Nat.cast_add, Nat.cast_mul, hsub, jsp87RadixBlockNat_cast]
  have hdenR : (((q : ℕ) ^ t - 1) * q ^ N : ℕ) = ((q : ℝ) ^ t - 1) * (q : ℝ) ^ N := by
    rw [Nat.cast_mul, Nat.cast_pow, hsub]
  have heq' : ((jsp87RadixInt f q N : ℝ) * ((q : ℝ) ^ t - 1) + jsp87RadixBlock f q N t)
          / (((q : ℝ) ^ t - 1) * (q : ℝ) ^ N) = jsp87RadixSeries f q := by
    have hX : ((q : ℝ) ^ t - 1) ≠ 0 := radix_pow_sub_one_ne_zero (by omega) (by omega)
    have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : (0 : ℕ) < q))
    apply (div_eq_iff (mul_ne_zero hX (pow_ne_zero _ hq0))).mpr
    calc (jsp87RadixInt f q N : ℝ) * ((q : ℝ) ^ t - 1) + jsp87RadixBlock f q N t
        = ((q : ℝ) ^ N * jsp87RadixSeries f q) * ((q : ℝ) ^ t - 1) := by rw [hval]; field_simp
      _ = jsp87RadixSeries f q * (((q : ℝ) ^ t - 1) * (q : ℝ) ^ N) := by ring
  have heq : jsp87RadixSeries f q
      = ((jsp87RadixInt f q N : ℝ) * ((q : ℝ) ^ t - 1) + jsp87RadixBlock f q N t)
          / (((q : ℝ) ^ t - 1) * (q : ℝ) ^ N) := heq'.symm
  refine ⟨(jsp87RadixInt f q N * (q ^ t - 1) + jsp87RadixBlockNat f q N t : ℕ),
    (q ^ t - 1) * q ^ N, mul_pos (Nat.sub_pos_iff_lt.mpr (by omega)) (by positivity), ?_⟩
  calc jsp87RadixSeries f q
      = ((jsp87RadixInt f q N : ℝ) * ((q : ℝ) ^ t - 1) + jsp87RadixBlock f q N t)
          / (((q : ℝ) ^ t - 1) * (q : ℝ) ^ N) := heq
    _ = ((jsp87RadixInt f q N * (q ^ t - 1) + jsp87RadixBlockNat f q N t : ℕ) : ℝ)
          / (((q : ℕ) ^ t - 1) * q ^ N : ℕ) := by rw [hnum, hdenR]

/-- **THE COMPLETE ERDŐS CRITERION IN ARBITRARY RADIX (both directions).**  For
`q ≥ 3` and a digit string satisfying `∀ n, f n ≤ q − 2`,

`Irrational (∑' n, f n q^-(n+1)) ↔ f` is not eventually periodic.

Mathlib has no statement about the base-`q` expansion of a real number at all, so
both directions are from scratch; for `q = 2` the corresponding statement is round
47's `jsp87Binary_irrational_iff`. -/
theorem jsp87Radix_irrational_iff (f : ℕ → ℕ) {q : ℕ} (hq : 3 ≤ q) (hf : jsp87NoCarry f q) :
    Irrational (jsp87RadixSeries f q) ↔
      ¬ ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → f (n + t) = f n := by
  constructor
  · intro hI ⟨t, N, ht, hN, hper⟩
    obtain ⟨a, b, hb, hval⟩ := jsp87Radix_rational_of_periodic f hq hf ht hper hN
    refine hI (show jsp87RadixSeries f q ∈ Set.range ((↑) : ℚ → ℝ) from ?_)
    exact ⟨(a : ℚ) / b, by rw [hval]; push_cast; rfl⟩
  · exact jsp87Radix_irrational_of_notPeriodic f hq hf

/-! ## 5.  `ω` is aperiodic modulo every `m ≥ 2` -/

/-- **Consecutive residues differ modulo `m ≥ 2`.**  `x mod m ≠ (x+1) mod m`
whenever `m ≥ 2`: the two residues differ because a common residue would force
`m ∣ 1`. -/
theorem mod_succ_ne_of_two_le {m x : ℕ} (hm : 2 ≤ m) : (x + 1) % m ≠ x % m := by
  intro h
  have h1 := Nat.mod_add_div x m
  have h2 := Nat.mod_add_div (x + 1) m
  rw [h] at h2
  have key : m * ((x + 1) / m) = m * (x / m) + 1 := by linarith
  rcases lt_or_ge (x / m) ((x + 1) / m) with hlt | hge
  · have hle' : x / m + 1 ≤ (x + 1) / m := by omega
    have hmul := Nat.mul_le_mul_left m hle'
    linarith
  · have hmul := Nat.mul_le_mul_left m hge
    linarith

/-- **An eventual period freezes `n ↦ ω n mod m` along the multiples of `t`.** -/
theorem omega_mod_eventuallyPeriodic_const_mul {m N t M : ℕ} (ht : 0 < t) (hN : N ≤ t * M)
    (hp : ∀ n, N ≤ n → omega (n + t) % m = omega n % m) (j : ℕ) :
    omega (t * M + t * j) % m = omega (t * M) % m := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : t * M + t * Nat.succ j = (t * M + t * j) + t := by
        rw [Nat.succ_eq_add_one]
        ring
      rw [hstep]
      have hM : M ≤ t * M := Nat.le_mul_of_pos_left M ht
      rw [hp (t * M + t * j) (by omega)]
      exact ih

/-- **`ω` IS APERIODIC MODULO EVERY `m ≥ 2`.**  There is no eventual period of
`n ↦ ω n mod m`, for any modulus `m ≥ 2`.

This is round 47's `omega_parity_not_eventuallyPeriodic` in full generality: an
eventual period `t` freezes `n ↦ ω (t·n) mod m` past `N`; but for a prime `p ∣ t`
one has `ω (t·p^k) = ω t` while for a prime `q ∤ t` one has `ω (t·q^k) = ω t + 1`,
and `ω t` and `ω t + 1` are distinct modulo any `m ≥ 2`. -/
theorem omega_mod_not_eventuallyPeriodic {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → omega (n + t) % m = omega n % m := by
  rintro ⟨t, N, ht, hp⟩
  set M := N + 1 with hMdef
  have hNM : N ≤ t * M := by
    have h1 : 1 ≤ t := by omega
    have h2 := Nat.le_mul_of_pos_left M h1
    omega
  by_cases ht1 : t = 1
  · subst ht1
    obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (max (N + 1) 3)
    have hqM : M ≤ q := by rw [hMdef]; omega
    have hq3 : 3 ≤ q := by have := hq; omega
    have hiff : (2 : ℕ) ∣ q ↔ 2 = 1 ∨ 2 = q := Nat.dvd_prime hqp
    have h2nd : (2 : ℕ) ∉ q.primeFactors := by
      intro hmem
      obtain ⟨h2p, h2d, _⟩ := Nat.mem_primeFactors.mp hmem
      rcases hiff.mp h2d with h | h <;> omega
    have h1' : omega (2 * q) = omega q + 1 := by
      rw [Nat.mul_comm 2 q]
      exact omega_mul_of_not_dvd (n := q) (p := 2) (by omega) (by norm_num : Nat.Prime 2) h2nd
    have hone : omega q = 1 := by
      rw [show q = q ^ 1 by rw [pow_one]]
      exact omega_prime_pow hqp (by omega)
    have hA : omega (1 * q) % m = omega (1 * M) % m := by
      have hstep := omega_mod_eventuallyPeriodic_const_mul (m := m) (N := N) (t := 1) (M := M)
        (by omega) hNM hp (q - M)
      have heq : 1 * M + 1 * (q - M) = 1 * q := by
        simp only [one_mul]
        rw [Nat.add_sub_of_le hqM]
      rw [heq] at hstep
      exact hstep
    have hB : omega (1 * (2 * q)) % m = omega (1 * M) % m := by
      have h2qM : M ≤ 2 * q := by omega
      have hstep := omega_mod_eventuallyPeriodic_const_mul (m := m) (N := N) (t := 1) (M := M)
        (by omega) hNM hp (2 * q - M)
      have heq : 1 * M + 1 * (2 * q - M) = 1 * (2 * q) := by
        simp only [one_mul]
        rw [Nat.add_sub_of_le h2qM]
      rw [heq] at hstep
      exact hstep
    have hA' : omega q % m = omega (1 * M) % m := by rwa [Nat.one_mul] at hA
    have hB' : omega (2 * q) % m = omega (1 * M) % m := by rwa [Nat.one_mul] at hB
    rw [h1'] at hB'
    have hcontra : ((omega q + 1 : ℕ)) % m = omega q % m := hB'.trans hA'.symm
    exact (mod_succ_ne_of_two_le hm) hcontra
  · obtain ⟨p, hp', hpd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp ht1
    obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (t * (N + 1) + 1)
    have hqnd : ¬ q ∣ t := by
      intro h
      have hle : q ≤ t := Nat.le_of_dvd (by omega) h
      have hqbig : t < q := by
        have h1 : 1 ≤ t := by omega
        have h2 : t ≤ t * (N + 1) := by
          have := Nat.le_mul_of_pos_left t (by omega : 0 < N + 1)
          simpa [Nat.mul_comm] using this
        omega
      omega
    obtain ⟨k1, hk1, hk1'⟩ := exists_pow_two_ge (t * (N + 1))
    obtain ⟨k2, hk2, hk2'⟩ := exists_pow_two_ge (t * (N + 1))
    have h1 : omega (t * p ^ k1) = omega t := omega_mul_pow_of_dvd (by omega) hp' hpd k1
    have hqbig : 1 ≤ q ^ k2 := Nat.one_le_pow k2 q (by omega)
    have h2 : omega (t * q ^ k2) = omega t + 1 :=
      omega_mul_pow_of_coprime (by omega) hqp hqnd hk2
    have hpow_le : 2 ^ k1 ≤ p ^ k1 := two_pow_le_pow p hp'.two_le k1
    have hqpow_le : 2 ^ k2 ≤ q ^ k2 := two_pow_le_pow q hqp.two_le k2
    have hM1 : M ≤ t * (N + 1) := by
      have h1 : 1 ≤ t := by omega
      have h3 := Nat.le_mul_of_pos_left (N + 1) h1
      rwa [hMdef]
    have hM2 : M ≤ 2 ^ k1 := Nat.le_trans hM1 hk1'
    have hA : omega (t * p ^ k1) % m = omega (t * M) % m := by
      have hM' : M ≤ p ^ k1 := Nat.le_trans hM2 hpow_le
      have hle : t * M ≤ t * p ^ k1 := Nat.mul_le_mul_left t hM'
      have hrec : t * M + t * (p ^ k1 - M) = t * p ^ k1 := by
        rw [Nat.mul_sub, Nat.add_sub_of_le hle]
      have hstep := omega_mod_eventuallyPeriodic_const_mul (m := m) (N := N) (t := t) (M := M)
        ht hNM hp (p ^ k1 - M)
      rwa [hrec] at hstep
    have hB : omega (t * q ^ k2) % m = omega (t * M) % m := by
      have hM' : M ≤ q ^ k2 := Nat.le_trans hM1 (Nat.le_trans hk2' hqpow_le)
      have hle : t * M ≤ t * q ^ k2 := Nat.mul_le_mul_left t hM'
      have hrec : t * M + t * (q ^ k2 - M) = t * q ^ k2 := by
        rw [Nat.mul_sub, Nat.add_sub_of_le hle]
      have hstep := omega_mod_eventuallyPeriodic_const_mul (m := m) (N := N) (t := t) (M := M)
        ht hNM hp (q ^ k2 - M)
      rwa [hrec] at hstep
    have hA' : omega t % m = omega (t * M) % m := by rwa [h1] at hA
    have hB' : (omega t + 1) % m = omega (t * M) % m := by rwa [h2] at hB
    exact (mod_succ_ne_of_two_le hm) (hB'.trans hA'.symm)

/-- `ω n mod m ≤ m − 1` for `1 ≤ m`: the reduction is a digit. -/
theorem omega_mod_lt {m : ℕ} (hm : 0 < m) (n : ℕ) : omega n % m < m :=
  Nat.mod_lt _ hm

/-! ## 6.  Three new complete irrationality theorems, one per radix -/

/-- **THE REDUCED-`ω` SERIES**: `∑' n, (ω n mod (q−1)) q^-(n+1)`. -/
noncomputable def jsp87OmegaModSeries (q : ℕ) : ℝ :=
  jsp87RadixSeries (fun n => omega n % (q - 1)) q

/-- The reduced digits of `ω` never carry in radix `q`. -/
theorem jsp87OmegaMod_noCarry (q : ℕ) (hq : 3 ≤ q) : jsp87NoCarry (fun n => omega n % (q - 1)) q := by
  intro n
  have hlt : omega n % (q - 1) < q - 1 := Nat.mod_lt _ (by omega)
  have h1 : omega n % (q - 1) ≤ (q - 1) - 1 := Nat.le_pred_of_lt hlt
  have h2 : (q - 1) - 1 = q - 2 := by omega
  have h3 : omega n % (q - 1) ≤ q - 2 := by rw [← h2]; exact h1
  exact h3

/-- **THE REDUCED-`ω` SERIES IS IRRATIONAL IN EVERY RADIX `q ≥ 3`.**  For every
`q ≥ 3`, the series

`∑' n, (ω n mod (q−1)) q^-(n+1)`

is irrational.  Its digits are carry-free by `jsp87OmegaMod_noCarry` and aperiodic
by `omega_mod_not_eventuallyPeriodic` with `m = q − 1`, and the radix criterion
turns aperiodicity into irrationality.

For `q = 3` this is round 47's parity theorem `jsp87ParitySeries_irrational`
(`ω n mod 2` at radix `3` is `2` whenever `ω n` is odd, so the two series are
different numbers); the statement here is the whole family. -/
theorem jsp87OmegaModSeries_irrational (q : ℕ) (hq : 3 ≤ q) :
    Irrational (jsp87OmegaModSeries q) := by
  refine jsp87Radix_irrational_of_notPeriodic (fun n => omega n % (q - 1)) hq
    (jsp87OmegaMod_noCarry q hq) ?_
  rintro ⟨t, N, ht, hN, hper⟩
  exact omega_mod_not_eventuallyPeriodic (m := q - 1) (by omega) ⟨t, N, ht, fun n hn => hper n hn⟩

/-- **ERDŐS' PRIME CONSTANT IS IRRATIONAL IN EVERY RADIX.**  For every `q ≥ 3`, the
number `∑' n, [n prime] q^-(n+1)` — the base-`q` prime constant — is irrational.
Round 47 proved the base-`2` instance. -/
theorem jsp87RadixPrimeSeries_irrational (q : ℕ) (hq : 3 ≤ q) :
    Irrational (jsp87RadixSeries jsp87PrimeBit q) := by
  refine jsp87Radix_irrational_of_notPeriodic jsp87PrimeBit hq ?_ ?_
  · intro n
    have h1 : jsp87PrimeBit n ≤ 1 := jsp87PrimeBit_le n
    omega
  · rintro ⟨t, N, ht, hN, hper⟩
    exact jsp87PrimeBit_not_eventuallyPeriodic ⟨t, N, ht, fun n hn => hper n hn⟩

/-- The indicator of "is a perfect square". -/
noncomputable def jsp87SquareBit (n : ℕ) : ℕ := by
  classical
  exact if ∃ m, m ^ 2 = n then 1 else 0

theorem jsp87SquareBit_le (n : ℕ) : jsp87SquareBit n ≤ 1 := by
  classical
  by_cases h : ∃ m, m ^ 2 = n <;> simp [jsp87SquareBit, h]

/-- **THE SQUARE INDICATOR IS APERIODIC.**  An eventual period `t` would make
`M² + t` a square whenever `M²` is one and `M` is large, but `M² < M² + t < (M+1)²`. -/
theorem jsp87SquareBit_not_eventuallyPeriodic :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → jsp87SquareBit (n + t) = jsp87SquareBit n := by
  classical
  rintro ⟨t, N, ht, hp⟩
  set M := max (max N t) 1 + 1 with hMdef
  have hMN : N ≤ M := by rw [hMdef]; omega
  have hMt : t ≤ M := by rw [hMdef]; omega
  have hM1 : 1 ≤ M := by rw [hMdef]; omega
  have h3 : M ≤ M * M := by
    calc M = 1 * M := by ring
      _ ≤ M * M := Nat.mul_le_mul hM1 (le_refl M)
  have hMN2 : N ≤ M ^ 2 := by
    calc N ≤ M := hMN
      _ ≤ M * M := h3
      _ = M ^ 2 := (pow_two M).symm
  have hs : jsp87SquareBit (M ^ 2) = 1 := by simp [jsp87SquareBit]
  have hp2 := hp (M ^ 2) hMN2
  rw [hs] at hp2
  have hcontra : ¬ ∃ m, m ^ 2 = M ^ 2 + t := by
    rintro ⟨m, hm⟩
    have h1 : M ^ 2 < M ^ 2 + t := by omega
    have hle : M ^ 2 + t ≤ M ^ 2 + M := by omega
    have hlt : M ^ 2 + M < M ^ 2 + 2 * M + 1 := by
      have hM2 : M ≤ 2 * M := by omega
      omega
    have h2 : M ^ 2 + t < (M + 1) ^ 2 := by
      calc M ^ 2 + t ≤ M ^ 2 + M := hle
        _ < M ^ 2 + 2 * M + 1 := hlt
        _ = (M + 1) ^ 2 := by rw [pow_two]; ring
    rw [← hm] at h1 h2
    rw [pow_two M] at h1
    have hMm : M < m := by
      by_contra hcon
      push Not at hcon
      have hle' : m ^ 2 ≤ M ^ 2 := pow_le_pow_left' hcon 2
      omega
    have hMm2 : m < M + 1 := by
      by_contra hcon
      push Not at hcon
      have hle' : (M + 1) ^ 2 ≤ m ^ 2 := pow_le_pow_left' hcon 2
      omega
    omega
  simp only [jsp87SquareBit] at hp2
  have hn2 : ¬ ∃ m, m ^ 2 = M ^ 2 + t := hcontra
  simp [hn2] at hp2

/-- **THE SQUARE-INDICATOR SERIES IS IRRATIONAL IN EVERY RADIX.**  For every
`q ≥ 3`, the number `∑' n, [n is a square] q^-(n+1)` — whose value is
`∑' m, q^-(m²+1)`, a Liouville-type constant — is irrational. -/
theorem jsp87RadixSquareSeries_irrational (q : ℕ) (hq : 3 ≤ q) :
    Irrational (jsp87RadixSeries jsp87SquareBit q) := by
  refine jsp87Radix_irrational_of_notPeriodic jsp87SquareBit hq ?_ ?_
  · intro n
    have h1 : jsp87SquareBit n ≤ 1 := jsp87SquareBit_le n
    omega
  · rintro ⟨t, N, ht, hN, hper⟩
    exact jsp87SquareBit_not_eventuallyPeriodic ⟨t, N, ht, fun n hn => hper n hn⟩

/-! ## 7.  Why the criterion does not reach `jsp_000087_main` -/

/-- **THE NO-CARRY CONDITION FAILS FOR `ω` IN EVERY RADIX.**  For every radix `q`
the digit function `ω` violates `jsp87NoCarry`, because `ω` is unbounded.  This
is the formal reason the method which decides the reduced series
`jsp87OmegaModSeries` (three irrationality theorems above) provably *cannot* be
applied to `jsp87Series` itself: in every radix the Erdős series carries. -/
theorem jsp87_noCarry_fails_any_radix (q : ℕ) :
    ¬ jsp87NoCarry omega q := by
  obtain ⟨n, hn1, hn2⟩ := omega_unbounded (k := q + 1)
  intro h
  have h3 := h n
  omega

/-- The reduced digits never exceed `ω` itself. -/
theorem omega_mod_le_omega {m : ℕ} (_hm : 0 < m) (n : ℕ) : omega n % m ≤ omega n :=
  Nat.mod_le _ _

/-- Where the reduction does not change anything: below the modulus. -/
theorem omega_mod_eq_omega {m : ℕ} (n : ℕ) (h : omega n < m) : omega n % m = omega n :=
  Nat.mod_eq_of_lt h

/-- **THE ERDŐS SERIES IN RADIX `q`** `E_q = ∑' n, ω n q^-(n+1)`.  For `q = 2` this
is the catalog's `jsp87Series`. -/
noncomputable def jsp87ErdosRadixSeries (q : ℕ) : ℝ :=
  ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹

/-- `∑' n, n q^-(n+1)` is summable: a polynomial majorant of a geometric series. -/
theorem summable_nat_mul_radixGeom (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
  have hr : |(q : ℝ)⁻¹| < 1 := radix_inv_abs_lt_one q hq
  have h := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 1) (r := (q : ℝ)⁻¹) hr
  have h1 : Summable (fun n : ℕ => (((n : ℕ) : ℝ) ^ 1) * (q : ℝ)⁻¹ ^ n) := by
    refine h.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, pow_one, abs_of_nonneg (Nat.cast_nonneg (n : ℕ)),
      abs_of_nonneg (by positivity)]
  have h2 : Summable (fun n : ℕ => (q : ℝ)⁻¹ * ((((n : ℕ) : ℝ) ^ 1) * (q : ℝ)⁻¹ ^ n)) :=
    h1.mul_left (q : ℝ)⁻¹
  refine h2.congr fun n => ?_
  calc (q : ℝ)⁻¹ * ((((n : ℕ) : ℝ) ^ 1) * (q : ℝ)⁻¹ ^ n)
      = ((n : ℕ) : ℝ) * ((q : ℝ)⁻¹ * (q : ℝ)⁻¹ ^ n) := by
        rw [pow_one, ← mul_assoc, mul_comm (q : ℝ)⁻¹ ((n : ℕ) : ℝ), mul_assoc]
    _ = ((n : ℕ) : ℝ) * (q : ℝ)⁻¹ ^ (n + 1) := by
        rw [mul_comm (q : ℝ)⁻¹ ((q : ℝ)⁻¹ ^ n), ← pow_succ]
    _ = ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by rw [radix_neg_eq q n]

/-- **THE ERDŐS SERIES CONVERGES IN EVERY RADIX.**  `ω n ≤ n − 1` for `n ≥ 1`, so
the series is dominated by a polynomial times a geometric series. -/
theorem summable_jsp87ErdosRadix (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹) := by
  have hle : ∀ n : ℕ, ((omega n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹
      ≤ ((n : ℕ) : ℝ) * ((q : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    refine mul_le_mul_of_nonneg_right (natCast_le_real ?_) (by positivity)
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]
      simp [omega]
    · have := omega_lt h
      omega
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)) hle
    (summable_nat_mul_radixGeom q hq)

/-- **In radix `2` the Erdős series is the catalog's series.** -/
theorem jsp87ErdosRadixSeries_eq_two (q : ℕ) (hq : 2 ≤ q) (h : q = 2) :
    jsp87ErdosRadixSeries q = jsp87Series := by
  subst h
  rfl

end JSP87
