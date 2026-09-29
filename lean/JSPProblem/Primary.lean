/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.BlockPeriod

/-!
# JSP-000087 : the primary (carry-free) binary expansion, and its irrationality criterion

Rounds 41 and 46 formalised the *binary digits* of the Erdős series
`S = ∑' n, ω(n) 2^-(n+1)`.  Those digits are

`d N = ⌊2^{N+1} S⌋ − 2 ⌊2^N S⌋`,   `d N = ω N + c(N+1) − 2 c N`,   `c N = ⌊θ N⌋`,

so they are **not** the `ω`-digits: the series genuinely *carries*, and the carry
excess `c N` is an extra integer sequence.  That is the precise reason the
round-41/46 reductions stop one lemma short of `jsp_000087_main`.

This file removes the carry and proves the resulting criterion in **both**
directions.  It is a new attack family: no previous round considered the
*primary* (carry-free) expansion, i.e. a base-`2` series whose digits are
already `0` or `1`.

## 1. The primary series

For `f : ℕ → ℕ` with `f n ≤ 1` put

`T f = ∑' n, f n 2^-(n+1)`,   `A f N = ∑_{n<N} f n 2^{N-n-1}`,   `U f N = ∑' k, f (N+k) 2^-(k+1)`.

* `jsp87Binary_split` : `2^N · T f = A f N + U f N` — the carry decomposition of
  round 38 **with no carry term**: the integer `A f N` is the whole prefix.
* `jsp87BinaryTail_succ` : `U f (N+1) = 2 U f N − f N` — the tail recurrence,
  the primary analogue of `jsp87Carry_succ`, `θ (N+1) = 2 θ N − ω N`.
* `jsp87BinaryTail_le_one` / `jsp87BinaryTail_lt_one` : `0 ≤ U f N ≤ 1`, strictly
  `< 1` as soon as one digit at or after `N` vanishes.

## 2. NO CARRYING: the digits are exactly `f`

Under the no-carry hypothesis `∀ N, U f N < 1`:

* `jsp87Binary_floor` : `⌊2^N · T f⌋ = A f N` — the binary floor is *exactly* the
  prefix integer, in contrast with round 41's `jsp87_floor_scaled`,
  `⌊2^N S⌋ = I N + ⌊θ N⌋`;
* `jsp87Binary_fract` : `Int.fract (2^N · T f) = U f N`;
* `jsp87Binary_digit` : **`f N = ⌊2^{N+1} T f⌋ − 2 ⌊2^N T f⌋`** — the binary digit
  of `T f` *is* the digit `f N`.  This is the identity that fails for the Erdős
  series, and `jsp87_digit_ne_omega` below exhibits the failure.

## 3. The criterion, in both directions

* `jsp87Binary_series_eq_block` : **the exact value.**  If `f` is eventually
  periodic from `N` with period `t > 0` then

  `2^N · T f = A f N + β f N t / (2^t − 1)`,  `β f N t = ∑_{j<t} f (N+j) 2^{t-1-j}`,

  the primary analogue of round 46's `jsp87_frac_scaled_eq_block`, but now for the
  *value* rather than the fractional part.  Hence `jsp87Binary_rational_of_periodic`.
* `jsp87Binary_rational_imp_periodic` : conversely, if `T f = a/b` with `b > 0`
  then the fractional parts of `2^N T f` are `c(N)/b` with `c(N) < b`, they obey
  the doubling map, and the pigeonhole principle makes them eventually periodic;
  since the digit is `2 · fract − fract`, the digit sequence `f` is eventually
  periodic.

Consequently `jsp87Binary_irrational_iff` is the **complete criterion**
(`Irrational ↔ aperiodicity`), proved from scratch — Mathlib has no statement
about the base-`2` expansion of a real number at all.

## 4. Two complete irrationality theorems

* `jsp87ParitySeries_irrational` : **the series `∑' n, (ω n % 2) 2^-(n+1)` is
  irrational.**  Its digits are the parities of `ω`, and
  `omega_parity_not_eventuallyPeriodic` proves *from scratch* that the parity
  sequence of `ω` is aperiodic: an eventual period freezes
  `n ↦ ω (t·n) mod 2`, whereas `ω (t·p^k) = ω t` for a prime `p ∣ t` while
  `ω (t·q^k) = ω t + 1` for a prime `q ∤ t`.  This is the closest provable
  sibling of `jsp_000087_main`: the same function `ω`, the same method, the same
  digit criterion, with the carry dropped.
* `jsp87PrimeSeries_irrational` : **the series `∑' n, [n prime] 2^-(n+1)` is
  irrational** (Erdős' prime constant), since the primality indicator is not
  eventually periodic: a period would make `p + j t` prime for all `j ≥ 0`, hence
  `p (1 + t)` prime.

## 5. Why this does not (yet) close JSP-000087

`jsp87_digit_one : jsp87Digit 1 = 1` while `ω 1 = 0`: the Erdős series carries at
`N = 1`, and `jsp87_digit_ne_omega_parity` shows its binary digits are neither the
`ω`-digits nor the parities of `ω`.  So the aperiodicity of `ω mod 2` proved here
does *not* transfer to the digits of `S`, and the headline statement is still
withheld.  What is missing remains exactly round 46's lemma: aperiodicity of
`jsp87Digit`.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 0. The primary binary series -/

/-- The `n`-th summand of the primary binary series of `f`. -/
noncomputable def jsp87BitTerm (f : ℕ → ℕ) (n : ℕ) : ℝ := ((f n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- **The primary (carry-free) binary series** `T f = ∑' n, f n 2^-(n+1)`, for a
`{0,1}`-valued `f`. -/
noncomputable def jsp87BinarySeries (f : ℕ → ℕ) : ℝ := ∑' n : ℕ, jsp87BitTerm f n

/-- A `{0,1}`-valued sequence stays `{0,1}`-valued in `ℝ`. -/
theorem natCast_le_one_of_le {m : ℕ} (h : m ≤ 1) : ((m : ℕ) : ℝ) ≤ 1 := by
  rw [← Nat.cast_one]
  exact_mod_cast h

/-- Each summand is nonnegative. -/
theorem jsp87BitTerm_nonneg (f : ℕ → ℕ) (n : ℕ) : 0 ≤ jsp87BitTerm f n :=
  mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The majorant is summable: `∑' k, 2^-(N+k+1)` is a shifted geometric series. -/
theorem summable_bitTerm_one (N : ℕ) :
    Summable (fun k : ℕ => (1 : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹) := by
  have h : Summable (fun k : ℕ => ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ k) :=
    (summable_inv_two_pow.mul_left ((2 : ℝ) ^ (N + 1))⁻¹)
  refine h.congr fun k => ?_
  have hpow : (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ k = (2 : ℝ) ^ (N + k + 1) := by
    rw [← pow_add]
    congr 1 <;> omega
  rw [one_mul, inv_pow, ← DivisionMonoid.mul_inv_rev,
    mul_comm ((2 : ℝ) ^ k) ((2 : ℝ) ^ (N + 1)), ← hpow]

/-- The majorant's value: `∑' k, 2^-(N+k+1) = 2^-N`. -/
theorem tsum_bitTerm_one (N : ℕ) :
    (∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹) = ((2 : ℝ) ^ N)⁻¹ := by
  have h1 : (∑' k : ℕ, ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ k)
      = ((2 : ℝ) ^ (N + 1))⁻¹ * (∑' k : ℕ, (2 : ℝ)⁻¹ ^ k) :=
    Summable.tsum_mul_left ((2 : ℝ) ^ (N + 1))⁻¹ summable_inv_two_pow
  have hstep : ∀ k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹
      = ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ k := by
    intro k
    have hpow : (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ k = (2 : ℝ) ^ (N + k + 1) := by
      rw [← pow_add]
      congr 1 <;> omega
    rw [one_mul, inv_pow, ← DivisionMonoid.mul_inv_rev,
      mul_comm ((2 : ℝ) ^ k) ((2 : ℝ) ^ (N + 1)), ← hpow]
  have hcongr : (∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹)
      = ∑' k : ℕ, ((2 : ℝ) ^ (N + 1))⁻¹ * (2 : ℝ)⁻¹ ^ k := by
    refine tsum_congr fun k => hstep k
  rw [hcongr, h1, tsum_inv_two_pow]
  have hpow : (2 : ℝ) ^ (N + 1) = (2 : ℝ) * (2 : ℝ) ^ N :=
    (pow_succ (2 : ℝ) N).trans (mul_comm ((2 : ℝ) ^ N) 2)
  have hnonzero : (2 : ℝ) ^ N ≠ 0 := by positivity
  rw [hpow]
  field_simp

/-- `∑' k, 2^-(k+1) = 1`: the value of the all-ones digit string. -/
theorem tsum_bitTerm_one_zero : (∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) = 1 := by
  have hcongr : (∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      = ∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (0 + k + 1))⁻¹ := by
    refine tsum_congr fun k => ?_
    rw [show k + 1 = 0 + k + 1 by omega]
  rw [hcongr, tsum_bitTerm_one 0, pow_zero, inv_one]

/-- **The primary series of a `{0,1}`-valued sequence is summable**, dominated by
the geometric series. -/
theorem summable_jsp87BitTerm (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) : Summable (jsp87BitTerm f) := by
  have hle : ∀ n : ℕ, jsp87BitTerm f n ≤ (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    rw [jsp87BitTerm]
    exact mul_le_mul_of_nonneg_right (natCast_le_one_of_le (hf n)) (by positivity)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
    simpa only [Nat.zero_add] using (summable_bitTerm_one 0)
  exact Summable.of_nonneg_of_le (jsp87BitTerm_nonneg f) hle h1

/-! ## 1. The prefix integer, the tail, and the split -/

/-- A nonzero natural number stays nonzero in `ℝ`. -/
theorem cast_ne_zero_of_ne_zero {m : ℕ} (h : m ≠ 0) : ((m : ℕ) : ℝ) ≠ 0 := by
  intro hh
  exact h (Nat.cast_eq_zero.mp hh)

/-- `(2 : ℝ)^t − 1 ≠ 0` for `1 ≤ t`: the period denominator never vanishes. -/
theorem two_pow_sub_one_ne_zero (t : ℕ) (ht : 1 ≤ t) : (2 : ℝ) ^ t - 1 ≠ 0 := by
  have h4 : (((2 : ℕ) ^ t - 1 : ℕ) : ℝ) = (2 : ℝ) ^ t - 1 := by
    rw [Nat.cast_sub (one_le_two_pow t)]
    norm_num
  rw [← h4]
  have h1 := one_le_two_pow t
  have h2 := two_pow_ge_two_of_pos (p := t) (by omega)
  have h3 : ((2 : ℕ) ^ t - 1 : ℕ) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr (by omega))
  exact cast_ne_zero_of_ne_zero h3

/-- `∑_{n<N} 2^{N-n-1} = 2^N - 1`: the binary value of `N` successive `1`-digits. -/
theorem sum_pow_two_desc (N : ℕ) : (∑ n ∈ Finset.range N, (2 : ℕ) ^ (N - n - 1)) = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep : ∀ i ∈ Finset.range N, 2 ^ (N - i) = 2 * 2 ^ (N - i - 1) := by
        intro i hi
        have hi' : i < N := Finset.mem_range.mp hi
        have hexp : N - i = (N - i - 1) + 1 := by omega
        calc 2 ^ (N - i) = 2 ^ ((N - i - 1) + 1) := congrArg (fun m : ℕ => (2 : ℕ) ^ m) hexp
          _ = 2 ^ (N - i - 1) * 2 := pow_succ _ _
          _ = 2 * 2 ^ (N - i - 1) := by ring
      have hlast : 2 ^ (N - N) = 1 := by
        rw [Nat.sub_self]
        norm_num
      have hsum : (∑ n ∈ Finset.range (N + 1), 2 ^ (N + 1 - n - 1))
          = ∑ n ∈ Finset.range (N + 1), 2 ^ (N - n) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        congr 1 <;> omega
      rw [hsum, Finset.sum_range_succ, Finset.sum_congr rfl hstep, ← Finset.mul_sum, hlast]
      have hone : 1 ≤ 2 ^ N := one_le_two_pow N
      calc 2 * (∑ n ∈ Finset.range N, 2 ^ (N - n - 1)) + 1 = 2 * (2 ^ N - 1) + 1 := by rw [ih]
        _ = 2 * 2 ^ N - 1 := by omega
        _ = 2 ^ (N + 1) - 1 := by rw [pow_succ, Nat.mul_comm]

/-- **The binary prefix, as an integer**: `A f N = ∑_{n<N} f n 2^{N-n-1}`. -/
def jsp87BinaryInt (f : ℕ → ℕ) (N : ℕ) : ℕ := ∑ n ∈ Finset.range N, f n * 2 ^ (N - n - 1)

/-- **A prefix is a genuine `N`-bit integer**: `A f N ≤ 2^N - 1`. -/
theorem jsp87BinaryInt_bounds (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) :
    jsp87BinaryInt f N ≤ 2 ^ N - 1 := by
  have hstep : ∀ n ∈ Finset.range N, f n * 2 ^ (N - n - 1) ≤ 2 ^ (N - n - 1) :=
    fun n _ => by simpa using (Nat.mul_le_mul_right (2 ^ (N - n - 1)) (hf n))
  calc jsp87BinaryInt f N = ∑ n ∈ Finset.range N, f n * 2 ^ (N - n - 1) := rfl
    _ ≤ ∑ n ∈ Finset.range N, 2 ^ (N - n - 1) := Finset.sum_le_sum hstep
    _ = 2 ^ N - 1 := sum_pow_two_desc N

/-- The prefix integer, read in `ℝ`. -/
theorem jsp87BinaryInt_cast (f : ℕ → ℕ) (N : ℕ) :
    (jsp87BinaryInt f N : ℝ) = ∑ i ∈ Finset.range N, (f i : ℝ) * (2 : ℝ) ^ (N - i - 1) := by
  simp only [jsp87BinaryInt, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- **THE PRIMARY TAIL** `U f N = ∑' k, f (N+k) 2^-(k+1)`: the *rescaled* remainder
of the series past the cut point `N`.  Compare `jsp87Carry`, which is `2^N` times
the tail of the Erdős series. -/
noncomputable def jsp87BinaryTail (f : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹

/-- The primary tail is summable. -/
theorem summable_jsp87BinaryTail (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) :
    Summable (fun k : ℕ => ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
  have hj : Summable (jsp87BitTerm f) := summable_jsp87BitTerm f hf
  have h1 : Summable (fun k : ℕ => jsp87BitTerm f (k + N)) :=
    (summable_nat_add_iff (f := jsp87BitTerm f) N).2 hj
  have h2 : Summable (fun k : ℕ => (2 : ℝ) ^ N * jsp87BitTerm f (k + N)) := h1.mul_left _
  refine h2.congr fun k => ?_
  rw [jsp87BitTerm, Nat.add_comm k N]
  have hpow : N + k + 1 = (k + 1) + N := by omega
  have hpow2 : (2 : ℝ) ^ N = ((2 : ℝ)⁻¹ ^ N)⁻¹ := by rw [← inv_pow, inv_inv]
  rw [two_pow_neg_eq, hpow2, hpow, pow_add]
  field_simp
  rw [mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow, mul_one]

/-- `0 ≤ U f N`. -/
theorem jsp87BinaryTail_nonneg (f : ℕ → ℕ) (N : ℕ) : 0 ≤ jsp87BinaryTail f N :=
  tsum_nonneg fun k => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- **The primary tail never exceeds `1`**: a `{0,1}`-valued digit string carries
nothing, so the rescaled tail stays inside `[0,1]`. -/
theorem jsp87BinaryTail_le_one (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) :
    jsp87BinaryTail f N ≤ 1 := by
  have hle : (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      ≤ ∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    refine Summable.tsum_le_tsum ?_ (summable_jsp87BinaryTail f hf N) ?_
    · intro k
      exact mul_le_mul_of_nonneg_right (natCast_le_one_of_le (hf (N + k))) (by positivity)
    · simpa only [Nat.zero_add] using (summable_bitTerm_one 0)
  calc jsp87BinaryTail f N = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := rfl
    _ ≤ ∑' k : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := hle
    _ = 1 := tsum_bitTerm_one_zero

/-- **NO CARRYING, quantitatively.**  As soon as one digit at or after `N` is `0`,
the rescaled tail is *strictly* below `1`: the binary expansion of the primary
series never carries at the cut point `N`. -/
theorem jsp87BinaryTail_lt_one (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ)
    (hz : ∃ k, f (N + k) = 0) : jsp87BinaryTail f N < 1 := by
  obtain ⟨k, hk⟩ := hz
  have hzero : ((f (N + k) : ℕ) : ℝ) = 0 := by rw [Nat.cast_eq_zero.mpr hk]
  have hge : ∀ j : ℕ, ((f (N + j) : ℕ) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹
      ≤ (1 : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹ := by
    intro j
    exact mul_le_mul_of_nonneg_right (natCast_le_one_of_le (hf (N + j))) (by positivity)
  have hlt : ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
      < (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    rw [hzero]
    norm_num
  have hsum := Summable.tsum_lt_tsum hge hlt (summable_jsp87BinaryTail f hf N)
    (by simpa only [Nat.zero_add] using (summable_bitTerm_one 0))
  calc jsp87BinaryTail f N = ∑' j : ℕ, ((f (N + j) : ℕ) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹ := rfl
    _ < ∑' j : ℕ, (1 : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹ := hsum
    _ = 1 := tsum_bitTerm_one_zero

/-- The primary tail is positive as soon as one digit at or after `N` is `1`. -/
theorem jsp87BinaryTail_pos (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ)
    (h : ∃ k, 1 ≤ f (N + k)) : 0 < jsp87BinaryTail f N := by
  obtain ⟨k, hk⟩ := h
  have hpos : 0 < f (N + k) := by omega
  unfold jsp87BinaryTail
  refine Summable.tsum_pos (summable_jsp87BinaryTail f hf N) ?_ k ?_
  · intro m
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · exact mul_pos (by exact_mod_cast hpos) (by positivity)

/-- The primary series splits into its partial sums and its tail. -/
theorem jsp87Binary_series_eq_sum_add_tail (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) :
    jsp87BinarySeries f = (∑ i ∈ Finset.range N, jsp87BitTerm f i)
      + ∑' k : ℕ, jsp87BitTerm f (k + N) :=
  (Summable.sum_add_tsum_nat_add N (summable_jsp87BitTerm f hf)).symm

/-- The partial sums of the primary series are the prefix integer divided by `2^N`. -/
theorem jsp87Binary_sum_range (f : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range N, jsp87BitTerm f i) = ((2 : ℝ) ^ N)⁻¹ * (jsp87BinaryInt f N : ℝ) := by
  have hterm : ∀ i ∈ Finset.range N,
      jsp87BitTerm f i = ((2 : ℝ) ^ N)⁻¹ * ((f i : ℝ) * (2 : ℝ) ^ (N - i - 1)) := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    rw [jsp87BitTerm, two_pow_neg_eq_scaled N i hi']
    ring
  calc (∑ i ∈ Finset.range N, jsp87BitTerm f i)
      = ((2 : ℝ) ^ N)⁻¹ * ∑ i ∈ Finset.range N, (f i : ℝ) * (2 : ℝ) ^ (N - i - 1) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    _ = ((2 : ℝ) ^ N)⁻¹ * (jsp87BinaryInt f N : ℝ) := by rw [jsp87BinaryInt_cast]

/-- Rescaling the summand at `N + k` by `2^N` erases `N`. -/
theorem two_pow_mul_bitTerm_shift (f : ℕ → ℕ) (N k : ℕ) :
    (2 : ℝ) ^ N * jsp87BitTerm f (N + k) = ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
  simp only [jsp87BitTerm]
  have hD : (2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
    have hb : (2 : ℝ) ^ N * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (N + k + 1) := by
      rw [← pow_add]
      congr 1 <;> omega
    rw [← hb]
    calc (2 : ℝ) ^ N * ((2 : ℝ) ^ N * (2 : ℝ) ^ (k + 1))⁻¹
        = (2 : ℝ) ^ N * (((2 : ℝ) ^ (k + 1))⁻¹ * ((2 : ℝ) ^ N)⁻¹) := by
          rw [DivisionMonoid.mul_inv_rev]
      _ = (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ * ((2 : ℝ) ^ (k + 1))⁻¹ := by ring
      _ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ N) ≠ 0), one_mul]
  calc (2 : ℝ) ^ N * (((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹)
      = ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹) := by ring
    _ = ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by rw [hD]

/-- **THE SPLIT, WITHOUT A CARRY TERM.**  For `1 ≤ N`,

`2^N · T f = A f N + U f N`

with `A f N` a natural number.  This is the carry decomposition of round 38 for
the primary series: the integer part is the *whole* prefix and the tail enters
with no factor `2^N`, because a `{0,1}` digit string never carries. -/
theorem jsp87Binary_split (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N * jsp87BinarySeries f = (jsp87BinaryInt f N : ℝ) + jsp87BinaryTail f N := by
  rw [jsp87Binary_series_eq_sum_add_tail f hf N, jsp87Binary_sum_range f N hN]
  have h1 : (2 : ℝ) ^ N * ((2 : ℝ) ^ N)⁻¹ = (1 : ℝ) := by field_simp
  rw [mul_add, ← mul_assoc, h1, one_mul]
  congr 1
  unfold jsp87BinaryTail
  have hs : Summable (fun k : ℕ => jsp87BitTerm f (k + N)) :=
    (summable_nat_add_iff (f := jsp87BitTerm f) N).2 (summable_jsp87BitTerm f hf)
  calc (2 : ℝ) ^ N * (∑' k : ℕ, jsp87BitTerm f (k + N))
      = ∑' k : ℕ, (2 : ℝ) ^ N * jsp87BitTerm f (k + N) := (Summable.tsum_mul_left _ hs).symm
    _ = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
        refine tsum_congr fun k => ?_
        rw [Nat.add_comm k N, two_pow_mul_bitTerm_shift]

/-! ## 2. The tail recurrence -/

/-- **THE PRIMARY TAIL RECURRENCE.**  `U f (N+1) = 2 · U f N − f N`: the primary
analogue of `jsp87Carry_succ`, `θ (N+1) = 2 θ N − ω N`. -/
theorem jsp87BinaryTail_succ (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) :
    jsp87BinaryTail f (N + 1) = 2 * jsp87BinaryTail f N - (f N : ℝ) := by
  have hs : Summable (fun k : ℕ => ((f (N + k) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k) := by
    refine (summable_jsp87BinaryTail f hf N).mul_left 2 |>.congr fun k => ?_
    rw [two_pow_neg_eq, pow_succ (2 : ℝ)⁻¹ k]
    ring_nf
  have hsplit : (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k)
      = (f N : ℝ) + ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (k + 1) := by
    have h := Summable.sum_add_tsum_nat_add 1 hs
    calc (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k)
        = (∑ i ∈ Finset.range 1, ((f (N + i) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ i)
            + ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (k + 1) := h.symm
      _ = ((f N : ℕ) : ℝ) + ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (k + 1) := by
        rw [Finset.sum_range_one, Nat.add_zero, pow_zero, mul_one]
  have htwo : 2 * jsp87BinaryTail f N = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k := by
    unfold jsp87BinaryTail
    calc 2 * (∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        = ∑' k : ℕ, 2 * (((f (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) :=
          (Summable.tsum_mul_left 2 (summable_jsp87BinaryTail f hf N)).symm
      _ = ∑' k : ℕ, ((f (N + k) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k := by
          refine tsum_congr fun k => ?_
          rw [two_pow_neg_eq, pow_succ (2 : ℝ)⁻¹ k]
          ring_nf
  have htail : jsp87BinaryTail f (N + 1)
      = ∑' k : ℕ, ((f (N + (k + 1)) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (k + 1) := by
    unfold jsp87BinaryTail
    refine tsum_congr fun k => ?_
    have h1 : N + 1 + k = N + (k + 1) := by omega
    rw [h1, two_pow_neg_eq]
  rw [htail, htwo, hsplit]
  ring

/-- **THE DIGIT, from two consecutive primary tails:**
`f N = 2 U f N − U f (N+1)`. -/
theorem jsp87BinaryTail_digit (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N : ℕ) :
    (f N : ℝ) = 2 * jsp87BinaryTail f N - jsp87BinaryTail f (N + 1) := by
  have h := jsp87BinaryTail_succ f hf N
  linarith

/-! ## 3. No carrying: the digits of the primary series are exactly `f` -/

/-- `⌊2 x⌋ − 2 ⌊x⌋ = ⌊2 · fract x⌋`: the digit is the doubling of the fractional
part.  Mathlib has no such statement. -/
theorem floor_two_mul_sub_two_floor (x : ℝ) : ⌊2 * x⌋ - 2 * ⌊x⌋ = ⌊2 * Int.fract x⌋ := by
  have h1 : 2 * x = 2 * ((⌊x⌋ : ℤ) : ℝ) + 2 * Int.fract x := by
    calc 2 * x = 2 * (((⌊x⌋ : ℤ) : ℝ) + Int.fract x) := by rw [Int.floor_add_fract x]
      _ = 2 * ((⌊x⌋ : ℤ) : ℝ) + 2 * Int.fract x := by ring
  have h2 : (2 : ℝ) * ((⌊x⌋ : ℤ) : ℝ) = ((2 * ⌊x⌋ : ℤ) : ℝ) := by norm_cast
  rw [h1, h2, Int.floor_intCast_add]
  ring

/-- **NO CARRYING, in floors.**  If the rescaled tail is `< 1` at every cut point
then the binary floor of `2^N T f` is *exactly* the prefix integer `A f N`.  This
is the sharp contrast with round 41's `jsp87_floor_scaled`, where the binary floor
is `I N + ⌊θ N⌋` — the carry excess is the whole obstruction. -/
theorem jsp87Binary_floor (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1)
    (hz : ∀ N, jsp87BinaryTail f N < 1) (N : ℕ) (hN : 1 ≤ N) :
    ⌊(2 : ℝ) ^ N * jsp87BinarySeries f⌋ = (jsp87BinaryInt f N : ℤ) := by
  have hd := jsp87Binary_split f hf N hN
  rw [hd, Int.floor_eq_iff]
  have hbridge : (((jsp87BinaryInt f N : ℕ) : ℤ) : ℝ) = (jsp87BinaryInt f N : ℝ) := by
    norm_cast
  rw [hbridge]
  have hA : (0 : ℝ) ≤ (jsp87BinaryInt f N : ℝ) := Nat.cast_nonneg _
  constructor
  · linarith [jsp87BinaryTail_nonneg f N]
  · linarith [hz N]

/-- **The fractional part of the rescaled primary series is the primary tail.** -/
theorem jsp87Binary_fract (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1)
    (hz : ∀ N, jsp87BinaryTail f N < 1) (N : ℕ) (hN : 1 ≤ N) :
    Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f) = jsp87BinaryTail f N := by
  have hfloor := jsp87Binary_floor f hf hz N hN
  have hfr := Int.self_sub_floor ((2 : ℝ) ^ N * jsp87BinarySeries f)
  have hd := jsp87Binary_split f hf N hN
  have hcast : ((jsp87BinaryInt f N : ℤ) : ℝ) = (jsp87BinaryInt f N : ℝ) := by norm_cast
  rw [hfloor] at hfr
  rw [hcast] at hfr
  linarith

/-- **THE PRIMARY DIGIT THEOREM.**  Under the no-carry hypothesis, the `N`-th
binary digit of `T f` is the digit `f N` itself:

`f N = ⌊2^{N+1} T f⌋ − 2 ⌊2^N T f⌋`.

This is exactly the identity that fails for the Erdős series, where the digit is
`ω N + c(N+1) − 2 c N` (round 41). -/
theorem jsp87Binary_digit (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1)
    (hz : ∀ N, jsp87BinaryTail f N < 1) (N : ℕ) (hN : 1 ≤ N) :
    (f N : ℤ) = ⌊(2 : ℝ) ^ (N + 1) * jsp87BinarySeries f⌋
      - 2 * ⌊(2 : ℝ) ^ N * jsp87BinarySeries f⌋ := by
  have hfrac := jsp87Binary_fract f hf hz N hN
  have hrw : (2 : ℝ) ^ (N + 1) * jsp87BinarySeries f
      = 2 * ((2 : ℝ) ^ N * jsp87BinarySeries f) := by
    rw [pow_succ]
    ring
  rw [hrw, floor_two_mul_sub_two_floor, hfrac]
  have hrec := jsp87BinaryTail_digit f hf N
  have h2 : 2 * jsp87BinaryTail f N = (f N : ℝ) + jsp87BinaryTail f (N + 1) := by linarith
  have hb : (((f N : ℕ) : ℤ) : ℝ) = (f N : ℝ) := by norm_cast
  have key : ⌊((f N : ℕ) : ℝ) + jsp87BinaryTail f (N + 1)⌋ = ((f N : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · linarith [jsp87BinaryTail_nonneg f (N + 1)]
    · linarith [hz (N + 1)]
  rw [h2]
  rw [← hb] at key
  symm
  exact key

/-! ## 4. The block arithmetic, and the exact value of a periodic primary series -/

/-- The `t`-digit block of the primary series, as a real:
`β f N t = ∑_{j<t} f (N+j) 2^{t-1-j}`. -/
noncomputable def jsp87BinaryBlock (f : ℕ → ℕ) (N t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, ((f (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (t - 1 - j)

/-- The real form of the all-ones block: `∑_{j<t} 2^{t-1-j} = 2^t − 1`. -/
theorem tsum_pow_two_desc (t : ℕ) :
    (∑ j ∈ Finset.range t, (2 : ℝ) ^ (t - j - 1)) = (2 : ℝ) ^ t - 1 := by
  have hkey : ((2 : ℕ) ^ t - 1 : ℕ) = ((2 : ℝ) ^ t - 1 : ℝ) := by
    rw [Nat.cast_sub (one_le_two_pow t)]
    norm_num
  calc (∑ j ∈ Finset.range t, (2 : ℝ) ^ (t - j - 1))
      = ((∑ j ∈ Finset.range t, (2 : ℕ) ^ (t - j - 1) : ℕ) : ℝ) := by
        symm
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        norm_cast
    _ = ((2 : ℕ) ^ t - 1 : ℕ) := by rw [sum_pow_two_desc t]
    _ = (2 : ℝ) ^ t - 1 := hkey

/-- **A block is a genuine `t`-digit window**: `0 ≤ β f N t ≤ 2^t − 1`. -/
theorem jsp87BinaryBlock_bounds (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N t : ℕ) :
    0 ≤ jsp87BinaryBlock f N t ∧ jsp87BinaryBlock f N t ≤ (2 : ℝ) ^ t - 1 := by
  constructor
  · refine Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (by exact pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (t - 1 - j))
  · have hstep : ∀ j ∈ Finset.range t,
        ((f (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (t - 1 - j) ≤ (2 : ℝ) ^ (t - 1 - j) := by
      intro j _
      have hmul := mul_le_mul_of_nonneg_right (natCast_le_one_of_le (hf (N + j)))
        (by exact pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (t - 1 - j))
      rwa [one_mul] at hmul
    have hle := Finset.sum_le_sum hstep
    have hle' : (∑ j ∈ Finset.range t, (2 : ℝ) ^ (t - 1 - j)) ≤ (2 : ℝ) ^ t - 1 := by
      have hkey : ∀ j ∈ Finset.range t, (2 : ℝ) ^ (t - 1 - j) = (2 : ℝ) ^ (t - j - 1) := by
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        congr 1 <;> omega
      rw [Finset.sum_congr rfl hkey, tsum_pow_two_desc t]
    unfold jsp87BinaryBlock
    linarith

/-- The `t`-digit block, as a natural number. -/
def jsp87BinaryBlockNat (f : ℕ → ℕ) (N t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, f (N + j) * 2 ^ (t - j - 1)

/-- The block, read in `ℝ`. -/
theorem jsp87BinaryBlockNat_cast (f : ℕ → ℕ) (N t : ℕ) :
    (jsp87BinaryBlockNat f N t : ℝ) = jsp87BinaryBlock f N t := by
  simp only [jsp87BinaryBlockNat, jsp87BinaryBlock, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < t := Finset.mem_range.mp hj
  have hkey : t - j - 1 = t - 1 - j := by rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm 1 j]
  rw [hkey]
  norm_cast

/-- **ITERATION OF THE TAIL RECURRENCE ALONG A BLOCK.**  For every `t ≥ 0`,

`U f (N + t) = 2^t U f N − β f N t`. -/
theorem jsp87BinaryTail_iter (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (N t : ℕ) :
    jsp87BinaryTail f (N + t) = 2 ^ t * jsp87BinaryTail f N - jsp87BinaryBlock f N t := by
  induction t with
  | zero =>
      have hb : jsp87BinaryBlock f N 0 = 0 := by simp [jsp87BinaryBlock]
      rw [Nat.add_zero, hb, sub_zero]
      ring
  | succ t ih =>
      have hstep : ∀ j ∈ Finset.range t,
          ((f (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (t - j)
            = 2 * (((f (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (t - 1 - j)) := by
        intro j hj
        have hj' : j < t := Finset.mem_range.mp hj
        have hkey : t - j = (t - 1 - j) + 1 := by omega
        rw [hkey, pow_succ]
        ring
      have hblock : jsp87BinaryBlock f N (t + 1)
          = 2 * jsp87BinaryBlock f N t + (f (N + t) : ℝ) := by
        unfold jsp87BinaryBlock
        have hkey : ∀ j ∈ Finset.range (t + 1),
            ((f (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (t + 1 - 1 - j)
              = ((f (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (t - j) := by
          intro j _
          congr 1 <;> omega
        rw [Finset.sum_congr rfl hkey, Finset.sum_range_succ, Finset.mul_sum,
          Finset.sum_congr rfl hstep, Nat.sub_self, pow_zero, mul_one]
      have h2 := jsp87BinaryTail_succ f hf (N + t)
      have hsucc : (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := (pow_succ (2 : ℝ) t).trans (by ring)
      have hN : N + t + 1 = N + (t + 1) := by rfl
      rw [hN] at h2
      rw [hblock, h2, hsucc, ih]
      ring

/-- **THE EXACT VALUE OF AN EVENTUALLY PERIODIC PRIMARY SERIES.**  If `f` is
periodic with period `t > 0` from `N` on, then the tail `U f N` is constant along
the period, hence `U f N = β f N t / (2^t − 1)`, and therefore

`2^N · T f = A f N + β f N t / (2^t − 1)`.

This is the primary analogue of round 46's `jsp87_frac_scaled_eq_block`, but for
the *value* rather than the fractional part: a periodic `{0,1}`-string is a
*rational* with denominator exactly `(2^t − 1) · 2^N`. -/
theorem jsp87Binary_series_eq_block (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) {N t : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → f (n + t) = f n) (hN : 1 ≤ N) :
    (2 : ℝ) ^ N * jsp87BinarySeries f = (jsp87BinaryInt f N : ℝ) + jsp87BinaryBlock f N t / (2 ^ t - 1) := by
  have hU : jsp87BinaryTail f (N + t) = jsp87BinaryTail f N := by
    unfold jsp87BinaryTail
    refine tsum_congr fun k => ?_
    have hk := hper (N + k) (by omega)
    have heq : N + t + k = (N + k) + t := by ac_rfl
    rw [heq, hk]
  have hiter := jsp87BinaryTail_iter f hf N t
  rw [hU] at hiter
  have hkey : jsp87BinaryBlock f N t = jsp87BinaryTail f N * ((2 : ℝ) ^ t - 1) := by
    linear_combination hiter
  have hne : (2 : ℝ) ^ t - 1 ≠ 0 := two_pow_sub_one_ne_zero t (by omega)
  have hval : jsp87BinaryTail f N = jsp87BinaryBlock f N t / ((2 : ℝ) ^ t - 1) := by
    symm
    apply (div_eq_iff hne).mpr
    exact hkey
  have hd := jsp87Binary_split f hf N hN
  rw [hd, hval]

/-- **AN EVENTUALLY PERIODIC PRIMARY SERIES IS RATIONAL.** -/
theorem jsp87Binary_rational_of_periodic (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) {N t : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → f (n + t) = f n) (hN : 1 ≤ N) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87BinarySeries f = (a : ℝ) / (b : ℝ) := by
  have hval := jsp87Binary_series_eq_block f hf ht hper hN
  refine ⟨(jsp87BinaryInt f N * (2 ^ t - 1) + jsp87BinaryBlockNat f N t),
    (2 ^ t - 1) * 2 ^ N, by
      have h3 : 0 < 2 ^ t - 1 := Nat.sub_pos_iff_lt.mpr (by
        have h1 := two_pow_ge_two_of_pos (p := t) (by omega)
        omega)
      exact mul_pos h3 (by positivity), ?_⟩
  have hsub : ((2 : ℕ) ^ t - 1 : ℕ) = ((2 : ℝ) ^ t - 1 : ℝ) := by
    rw [Nat.cast_sub (one_le_two_pow t)]
    norm_num
  have hA : ((jsp87BinaryInt f N * (2 ^ t - 1) : ℕ) : ℝ)
      = (jsp87BinaryInt f N : ℝ) * ((2 : ℝ) ^ t - 1) := by
    rw [Nat.cast_mul, hsub]
  have hB : (jsp87BinaryBlockNat f N t : ℝ) = jsp87BinaryBlock f N t :=
    jsp87BinaryBlockNat_cast f N t
  have hcast : ((jsp87BinaryInt f N * (2 ^ t - 1) + jsp87BinaryBlockNat f N t : ℕ) : ℝ)
      = (jsp87BinaryInt f N : ℝ) * ((2 : ℝ) ^ t - 1) + jsp87BinaryBlock f N t := by
    calc (↑(jsp87BinaryInt f N * (2 ^ t - 1) + jsp87BinaryBlockNat f N t) : ℝ)
        = (↑(jsp87BinaryInt f N * (2 ^ t - 1)) : ℝ) + (↑(jsp87BinaryBlockNat f N t) : ℝ) := by
          rw [Nat.cast_add]
      _ = (jsp87BinaryInt f N : ℝ) * ((2 : ℝ) ^ t - 1) + jsp87BinaryBlock f N t := by
          rw [hA, hB]
  have hne : (2 : ℝ) ^ t - 1 ≠ 0 := two_pow_sub_one_ne_zero t (by omega)
  have h3 : ((2 : ℕ) ^ t - 1 : ℕ) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr (by
      have h1 := two_pow_ge_two_of_pos (p := t) (by omega)
      omega))
  have hne' : (((2 : ℕ) ^ t - 1) * 2 ^ N : ℕ) ≠ (0 : ℝ) := by
    have hz : (2 : ℕ) ^ N ≠ 0 := Nat.ne_of_gt (one_le_two_pow N)
    rw [Nat.cast_mul, Nat.cast_pow]
    have hz' : ((2 : ℕ) : ℝ) ^ N ≠ 0 := ne_of_gt (pow_pos (by norm_num) N)
    exact mul_ne_zero (cast_ne_zero_of_ne_zero h3) hz'
  symm
  rw [div_eq_iff hne']
  push_cast
  rw [hB, hsub]
  calc (jsp87BinaryInt f N : ℝ) * ((2 : ℝ) ^ t - 1) + jsp87BinaryBlock f N t
      = ((2 : ℝ) ^ N * jsp87BinarySeries f) * ((2 : ℝ) ^ t - 1) := by
        rw [hval]
        field_simp
    _ = jsp87BinarySeries f * (((2 : ℝ) ^ t - 1) * 2 ^ N) := by ring

/-! ## 5. Rationality forces an eventually periodic digit sequence -/

/-- **The doubling map on the fractional parts of a general rescaling.** -/
theorem Int.fract_two_pow_mul (x : ℝ) (N : ℕ) :
    Int.fract ((2 : ℝ) ^ (N + 1) * x) = Int.fract (2 * Int.fract ((2 : ℝ) ^ N * x)) := by
  have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  rw [hpow]
  convert Int.fract_two_mul (x := (2 : ℝ) ^ N * x) using 1 <;> ring

/-- **Rationality quantises the fractional parts of a primary series.**  If
`T f = a / b` with `b > 0` then the fractional part of `2^N T f` is `c / b` for an
integer `c` with `0 ≤ c < b`: the fractional parts live in a *finite* set of
size `b`, uniformly in `N`. -/
theorem jsp87Binary_fract_eq_div {f : ℕ → ℕ} {N : ℕ} {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ)) (hN : 1 ≤ N) :
    ∃ c : ℤ, 0 ≤ c ∧ c < (b : ℤ) ∧ Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f) = (c : ℝ) / (b : ℝ) :=
  Int.fract_eq_div_of_mul_natCast (b := b) hb (x := (2 : ℝ) ^ N * jsp87BinarySeries f)
    (m := ((2 : ℕ) ^ N * a : ℤ)) (by
      have hcast : (2 : ℝ) ^ N * (a : ℝ) = ((2 : ℕ) ^ N * a : ℤ) := by norm_cast
      have hbnz : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
      rw [h]
      calc (b : ℝ) * ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)))
          = ((b : ℝ) * (2 : ℝ) ^ N * (a : ℝ)) / (b : ℝ) := by ring
        _ = (2 : ℝ) ^ N * (a : ℝ) := by field_simp
        _ = ((2 : ℕ) ^ N * a : ℤ) := hcast)

/-- **The numerator of the fractional part of `2^N T f`** under the rationality
hypothesis `T f = a / b`. -/
noncomputable def jsp87BinaryFracNum (f : ℕ → ℕ) (b : ℕ) (N : ℕ) : ℕ :=
  (⌊(b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f)⌋ : ℤ).toNat

/-- **The numerators are bounded by `b` and recover the fractional parts.** -/
theorem jsp87BinaryFracNum_spec (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (hz : ∀ N, jsp87BinaryTail f N < 1)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ)) {N : ℕ} (hN : 1 ≤ N) :
    jsp87BinaryFracNum f b N < b
      ∧ Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f) = (jsp87BinaryFracNum f b N : ℝ) / (b : ℝ) := by
  obtain ⟨c, hc0, hc1, hc2⟩ := jsp87Binary_fract_eq_div (b := b) hb h hN
  have hmul : (b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f) = (c : ℝ) := by
    rw [hc2]
    field_simp
  have hfloor : ⌊(b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f)⌋ = c := by
    rw [hmul, Int.floor_intCast]
  have hcast : ((jsp87BinaryFracNum f b N : ℕ) : ℤ) = c := by
    show (↑((⌊(b : ℝ) * Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f)⌋ : ℤ).toNat : ℕ) : ℤ) = c
    rw [Int.toNat_of_nonneg (by rw [hfloor]; exact hc0), hfloor]
  have hltN : jsp87BinaryFracNum f b N < b := by
    have hz' : ((jsp87BinaryFracNum f b N : ℕ) : ℤ) < (b : ℕ) := by rw [hcast]; exact hc1
    exact_mod_cast hz'
  refine ⟨hltN, ?_⟩
  have hR : ((jsp87BinaryFracNum f b N : ℕ) : ℝ) = (c : ℝ) := by norm_cast
  calc Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f) = (c : ℝ) / (b : ℝ) := hc2
    _ = (jsp87BinaryFracNum f b N : ℝ) / (b : ℝ) := by rw [hR]

/-- **Equal fractional parts have equal successors** (the doubling map is a
function of the fractional part alone). -/
theorem jsp87BinaryFracNum_succ (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (hz : ∀ N, jsp87BinaryTail f N < 1)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h' : jsp87BinaryFracNum f b i = jsp87BinaryFracNum f b j) :
    jsp87BinaryFracNum f b (i + 1) = jsp87BinaryFracNum f b (j + 1) := by
  have hs : jsp87BinaryFracNum f b i < b
      ∧ Int.fract ((2 : ℝ) ^ i * jsp87BinarySeries f) = (jsp87BinaryFracNum f b i : ℝ) / (b : ℝ) :=
    jsp87BinaryFracNum_spec f hf hz hb h hi
  have hs' : jsp87BinaryFracNum f b j < b
      ∧ Int.fract ((2 : ℝ) ^ j * jsp87BinarySeries f) = (jsp87BinaryFracNum f b j : ℝ) / (b : ℝ) :=
    jsp87BinaryFracNum_spec f hf hz hb h hj
  have hfrac : Int.fract ((2 : ℝ) ^ (i + 1) * jsp87BinarySeries f)
      = Int.fract ((2 : ℝ) ^ (j + 1) * jsp87BinarySeries f) := by
    rw [Int.fract_two_pow_mul, Int.fract_two_pow_mul, hs.2, hs'.2, h']
  have h1 := (jsp87BinaryFracNum_spec f hf hz hb h (by omega : 1 ≤ i + 1)).2
  have h1' := (jsp87BinaryFracNum_spec f hf hz hb h (by omega : 1 ≤ j + 1)).2
  rw [← hfrac] at h1'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have key : ((jsp87BinaryFracNum f b (i + 1) : ℕ) : ℝ) / (b : ℝ)
      = ((jsp87BinaryFracNum f b (j + 1) : ℕ) : ℝ) / (b : ℝ) := by
    rw [← h1, ← h1']
  have key' : ((jsp87BinaryFracNum f b (i + 1) : ℕ) : ℝ)
      = ((jsp87BinaryFracNum f b (j + 1) : ℕ) : ℝ) := (div_left_inj' hb0).mp key
  exact_mod_cast key'

/-- The numerator sequence propagates along the doubling map. -/
theorem jsp87BinaryFracNum_period_aux (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1)
    (hz : ∀ N, jsp87BinaryTail f N < 1) {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (h0 : jsp87BinaryFracNum f b i = jsp87BinaryFracNum f b j) (k : ℕ) :
    jsp87BinaryFracNum f b (i + k) = jsp87BinaryFracNum f b (j + k) := by
  induction k with
  | zero => rw [Nat.add_zero]; exact h0
  | succ k ih =>
      have h1 : jsp87BinaryFracNum f b (i + Nat.succ k) = jsp87BinaryFracNum f b (j + Nat.succ k) := by
        have hstep := jsp87BinaryFracNum_succ f hf hz hb h (by omega) (by omega) ih
        convert hstep using 1 <;> omega
      exact h1

/-- **THE FINITE-RANGE ARGUMENT (for a primary series).**  A sequence of `b+1`
numerators taking values in `range b` has two equal entries, and the doubling map
then propagates the equality forever: the fractional parts of the rescaled series
are *eventually periodic*. -/
theorem jsp87BinaryFracNum_period (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (hz : ∀ N, jsp87BinaryTail f N < 1)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → jsp87BinaryFracNum f b (n + t) = jsp87BinaryFracNum f b n := by
  have hlt : ∀ i : ℕ, jsp87BinaryFracNum f b (i + 1) < b :=
    fun i => (jsp87BinaryFracNum_spec f hf hz hb h (by omega)).1
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (b + 1) => (⟨jsp87BinaryFracNum f b (i.val + 1), hlt i.val⟩ : Fin b)) (by simp)
  have hne' : x.1 ≠ y.1 := fun hh => hne (Fin.ext hh)
  have h0 : jsp87BinaryFracNum f b (x.1 + 1) = jsp87BinaryFracNum f b (y.1 + 1) := congrArg Fin.val heq
  rcases lt_trichotomy x.1 y.1 with hxy | hxy | hxy
  · have ht : 0 < y.1 - x.1 := by omega
    have hN : 1 ≤ x.1 + 1 := by omega
    refine ⟨y.1 - x.1, x.1 + 1, ht, hN, ?_⟩
    intro n hn
    have hk := jsp87BinaryFracNum_period_aux f hf hz hb h (by omega) (by omega) h0 (n - (x.1 + 1))
    rw [Nat.add_sub_of_le hn] at hk
    have hkey : n + (y.1 - x.1) = (y.1 + 1) + (n - (x.1 + 1)) := by omega
    rw [← hkey] at hk
    exact hk.symm
  · exact (hne' hxy).elim
  · have ht : 0 < x.1 - y.1 := by omega
    have hN : 1 ≤ y.1 + 1 := by omega
    refine ⟨x.1 - y.1, y.1 + 1, ht, hN, ?_⟩
    intro n hn
    have hk := jsp87BinaryFracNum_period_aux f hf hz hb h (by omega) (by omega) h0.symm (n - (y.1 + 1))
    rw [Nat.add_sub_of_le hn] at hk
    have hkey : n + (x.1 - y.1) = (x.1 + 1) + (n - (y.1 + 1)) := by omega
    rw [← hkey] at hk
    exact hk.symm

/-- **`b · f N = 2 c(N) − c(N+1)`**: the digit is recovered from two consecutive
numerators of the fractional parts. -/
theorem jsp87Binary_digit_fracNum (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (hz : ∀ N, jsp87BinaryTail f N < 1)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ)) {N : ℕ} (hN : 1 ≤ N) :
    (b : ℝ) * ((f N : ℕ) : ℝ)
      = 2 * (jsp87BinaryFracNum f b N : ℝ) - (jsp87BinaryFracNum f b (N + 1) : ℝ) := by
  have hfrac : ∀ m (hm : 1 ≤ m), (b : ℝ) * Int.fract ((2 : ℝ) ^ m * jsp87BinarySeries f)
      = (jsp87BinaryFracNum f b m : ℝ) := by
    intro m hm
    have h2 := (jsp87BinaryFracNum_spec f hf hz hb h hm).2
    rw [h2]
    field_simp
  have hfloor : ∀ m (hm : 1 ≤ m), (b : ℝ) * ⌊(2 : ℝ) ^ m * jsp87BinarySeries f⌋
      = (2 : ℝ) ^ m * (a : ℝ) - (b : ℝ) * Int.fract ((2 : ℝ) ^ m * jsp87BinarySeries f) := by
    intro m hm
    have hx : (b : ℝ) * ((2 : ℝ) ^ m * jsp87BinarySeries f) = (2 : ℝ) ^ m * (a : ℝ) := by
      have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
      rw [h]
      field_simp
    have hfr := Int.self_sub_floor ((2 : ℝ) ^ m * jsp87BinarySeries f)
    have hfr' : ((⌊(2 : ℝ) ^ m * jsp87BinarySeries f⌋ : ℤ) : ℝ)
        = (2 : ℝ) ^ m * jsp87BinarySeries f - Int.fract ((2 : ℝ) ^ m * jsp87BinarySeries f) := by
      linarith
    calc (b : ℝ) * ⌊(2 : ℝ) ^ m * jsp87BinarySeries f⌋
        = (b : ℝ) * ((2 : ℝ) ^ m * jsp87BinarySeries f
            - Int.fract ((2 : ℝ) ^ m * jsp87BinarySeries f)) := by rw [hfr']
      _ = (2 : ℝ) ^ m * (a : ℝ) - (b : ℝ) * Int.fract ((2 : ℝ) ^ m * jsp87BinarySeries f) := by
          rw [mul_sub, hx]
  have hdig : ((f N : ℕ) : ℝ)
      = ⌊(2 : ℝ) ^ (N + 1) * jsp87BinarySeries f⌋ - 2 * ⌊(2 : ℝ) ^ N * jsp87BinarySeries f⌋ := by
    have hd := jsp87Binary_digit f hf hz N hN
    push_cast at hd ⊢
    exact_mod_cast hd
  have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  calc (b : ℝ) * ((f N : ℕ) : ℝ)
      = (b : ℝ) * (⌊(2 : ℝ) ^ (N + 1) * jsp87BinarySeries f⌋
          - 2 * ⌊(2 : ℝ) ^ N * jsp87BinarySeries f⌋) := by rw [hdig]
    _ = (b : ℝ) * ⌊(2 : ℝ) ^ (N + 1) * jsp87BinarySeries f⌋
          - 2 * (b : ℝ) * ⌊(2 : ℝ) ^ N * jsp87BinarySeries f⌋ := by ring
    _ = ((2 : ℝ) ^ (N + 1) * (a : ℝ) - (b : ℝ)
          * Int.fract ((2 : ℝ) ^ (N + 1) * jsp87BinarySeries f))
          - 2 * ((2 : ℝ) ^ N * (a : ℝ) - (b : ℝ)
          * Int.fract ((2 : ℝ) ^ N * jsp87BinarySeries f)) := by
        rw [hfloor (N + 1) (by omega), mul_assoc (2 : ℝ) (b : ℝ)
          ((⌊(2 : ℝ) ^ N * jsp87BinarySeries f⌋ : ℤ) : ℝ), hfloor N hN]
    _ = 2 * (jsp87BinaryFracNum f b N : ℝ) - (jsp87BinaryFracNum f b (N + 1) : ℝ) := by
        rw [hfrac (N + 1) (by omega), hfrac N hN, hpow]
        ring

/-- **Equal numerators give equal digits.** -/
theorem jsp87Binary_digit_of_fracNum (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (hz : ∀ N, jsp87BinaryTail f N < 1)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hc : jsp87BinaryFracNum f b i = jsp87BinaryFracNum f b j) :
    f i = f j := by
  have h1 := jsp87Binary_digit_fracNum f hf hz hb h hi
  have h2 := jsp87Binary_digit_fracNum f hf hz hb h hj
  have hs := jsp87BinaryFracNum_succ f hf hz hb h hi hj hc
  have hsucc : jsp87BinaryFracNum f b (i + 1) = jsp87BinaryFracNum f b (j + 1) := hs
  have hkey : (b : ℝ) * ((f i : ℕ) : ℝ) = (b : ℝ) * ((f j : ℕ) : ℝ) := by
    rw [h1, h2, hsucc, hc]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  exact_mod_cast (mul_left_cancel₀ hb0 hkey)

/-- **THE CRITERION, FORWARD DIRECTION.**  If `T f = a / b` with `b > 0` then the
digit sequence `f` is eventually periodic: the digit at `N` is
`2 · fract (2^N T f) − fract (2^{N+1} T f)`, the numerators of the fractional
parts live in `range b`, and the doubling map is deterministic.  Proved from
scratch; Mathlib has no statement about the base-`2` expansion of a real. -/
theorem jsp87Binary_rational_imp_periodic (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1)
    (hz : ∀ N, jsp87BinaryTail f N < 1) {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87BinarySeries f = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → f (n + t) = f n := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87BinaryFracNum_period f hf hz hb h
  refine ⟨t, M, ht, hM, ?_⟩
  intro n hn
  exact jsp87Binary_digit_of_fracNum f hf hz hb h (by omega) (by omega) (hper n hn)

/-- **THE CRITERION.**  A `{0,1}`-valued digit string whose binary series is
irrational — equivalently, whose digit string is not eventually periodic.
This is the complete Erdős criterion for `∑ f(n) 2^-(n+1)`, proved in both
directions and entirely from scratch. -/
theorem jsp87Binary_irrational_of_notPeriodic (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1)
    (hz : ∀ N, jsp87BinaryTail f N < 1)
    (haper : ¬ ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → f (n + t) = f n) :
    Irrational (jsp87BinarySeries f) := by
  show jsp87BinarySeries f ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  obtain ⟨t, N, ht, hN, hper⟩ := jsp87Binary_rational_imp_periodic f hf hz (Rat.den_pos q)
    (by rw [← hq, Rat.cast_def])
  exact haper ⟨t, N, ht, hN, hper⟩

/-- Every `a / b` with `b > 0` is the value of some rational. -/
theorem exists_rat_eq_div (a : ℤ) (b : ℕ) (hb : 0 < b) : ∃ q : ℚ, (q : ℝ) = (a : ℝ) / (b : ℝ) :=
  ⟨(a : ℚ) / b, by push_cast; rfl⟩

/-- **THE COMPLETE CRITERION (both directions).**  For a `{0,1}`-valued sequence
`f`, the series `∑' n, f n 2^-(n+1)` is irrational **iff** the digit sequence `f`
is not eventually periodic. -/
theorem jsp87Binary_irrational_iff (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) (hz : ∀ N, jsp87BinaryTail f N < 1) :
    Irrational (jsp87BinarySeries f) ↔
      ¬ ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → f (n + t) = f n := by
  constructor
  · intro hI ⟨t, N, ht, hN, hper⟩
    obtain ⟨a, b, hb, hval⟩ := jsp87Binary_rational_of_periodic f hf ht hper hN
    refine hI (show jsp87BinarySeries f ∈ Set.range ((↑) : ℚ → ℝ) from ?_)
    exact ⟨(a : ℚ) / b, by
      rw [hval]
      push_cast
      rfl⟩
  · intro haper
    exact jsp87Binary_irrational_of_notPeriodic f hf hz haper

/-- **A periodic digit string gives a rational series** (the converse of the
criterion, on the arithmetic side). -/
theorem jsp87Binary_rational_of_periodic' (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 1) {N t : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → f (n + t) = f n) (hN : 1 ≤ N) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ jsp87BinarySeries f = (a : ℝ) / (b : ℝ) :=
  jsp87Binary_rational_of_periodic f hf ht hper hN

/-! ## 6. `ω` modulo `2`: a complete irrationality theorem for the parity series -/

/-- **Multiplication by a fresh prime adds exactly one to `ω`.**  If `p` is prime
and `p` is not a prime factor of `n`, then `ω (n·p) = ω n + 1`. -/
theorem omega_mul_of_not_dvd {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hnd : p ∉ n.primeFactors) :
    omega (n * p) = omega n + 1 := by
  have hdiv : (n * p) / p = n := by
    have h2 := hp.two_le
    exact Nat.mul_div_cancel n (n := p) (by omega)
  have hins : (n * p).primeFactors = insert p n.primeFactors := by
    have hpd : p ∣ n * p := ⟨n, by ring⟩
    have h1 := primeFactors_div_prime (mul_ne_zero hn.ne' hp.ne_zero) hp hpd
    rw [hdiv] at h1
    exact h1
  have hcard : (insert p n.primeFactors).card = n.primeFactors.card + 1 :=
    Finset.card_insert_of_notMem hnd
  simp only [omega]
  rw [hins, hcard]

/-- A prime already dividing `t` contributes no new prime factor to `t·p^k`. -/
theorem primeFactors_mul_pow_of_dvd {t p : ℕ} (ht : 0 < t) (hp : p.Prime) (hpd : p ∣ t) (k : ℕ) :
    (t * p ^ k).primeFactors = t.primeFactors := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · have hk0 : k = 0 := by omega
    subst hk0
    simp
  · ext q
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hq, hqd, _⟩
      rcases hq.dvd_mul.mp hqd with h1 | h2
      · have hmem : q.Prime ∧ q ∣ t ∧ t ≠ 0 := ⟨hq, h1, ht.ne'⟩
        exact hmem
      · have hpk : (q : ℕ) ∣ p := by
          have hq2 : (q : ℕ) ∣ p ^ k := h2
          exact (prime_dvd_pow_iff hq k hk).mp hq2
        have hiff : q ∣ p ^ k ↔ q ∣ p := prime_dvd_pow_iff hq k hk
        have hmem : q.Prime ∧ q ∣ t ∧ t ≠ 0 :=
          ⟨hq, Nat.dvd_trans (hiff.mp h2) hpd, ht.ne'⟩
        exact hmem
    · rintro ⟨hq, hqd, _⟩
      have hpk : (p : ℕ) ^ k ≠ 0 := by
        intro hz
        rw [Nat.pow_eq_zero] at hz
        exact hp.ne_zero hz.1
      have hmem : q.Prime ∧ q ∣ t * p ^ k ∧ t * p ^ k ≠ 0 := by
        refine ⟨hq, dvd_mul_of_dvd_left hqd (p ^ k), mul_ne_zero ht.ne' hpk⟩
      exact hmem

/-- **`ω (t·p^k) = ω t` for a prime `p ∣ t`.** -/
theorem omega_mul_pow_of_dvd {t p : ℕ} (ht : 0 < t) (hp : p.Prime) (hpd : p ∣ t) (k : ℕ) :
    omega (t * p ^ k) = omega t := by
  have h := primeFactors_mul_pow_of_dvd ht hp hpd k
  simp only [omega]
  rw [h]

/-- **`ω (t·q^k) = ω t + 1` for a prime `q ∤ t` and `1 ≤ k`.** -/
theorem omega_mul_pow_of_coprime {t q k : ℕ} (ht : 0 < t) (hq : q.Prime) (hqd : ¬ q ∣ t)
    (hk : 1 ≤ k) : omega (t * q ^ k) = omega t + 1 := by
  have hcop : Nat.Coprime t q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd |>.symm
  have hcop' : Nat.Coprime t (q ^ k) := hcop.pow_right k
  have h1 := omega_mul_of_coprime hcop'
  have h2 := omega_prime_pow hq hk
  calc omega (t * q ^ k) = omega t + omega (q ^ k) := h1
    _ = omega t + 1 := by rw [h2]

/-- `2^k ≤ p^k` whenever `2 ≤ p`. -/
theorem two_pow_le_pow (p : ℕ) (hp : 2 ≤ p) (k : ℕ) : 2 ^ k ≤ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ]; exact Nat.mul_le_mul ih hp

/-- `N ≤ 2^N + 1` for every `N`. -/
theorem le_two_pow_self (N : ℕ) : N ≤ 2 ^ N + 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h2 := one_le_two_pow N
      rw [pow_succ]
      omega

/-- For every `b` there is `k ≥ 1` with `b ≤ 2^k`. -/
theorem exists_pow_two_ge (b : ℕ) : ∃ k : ℕ, 1 ≤ k ∧ b ≤ 2 ^ k := by
  have h := le_two_pow_self b
  have h2 := one_le_two_pow b
  refine ⟨b + 1, by omega, ?_⟩
  rw [pow_succ]
  omega

/-- An eventual period freezes the parity of `ω` along the multiples of `t`. -/
theorem omega_parity_eventuallyPeriodic_const_mul {N t M : ℕ} (ht : 0 < t) (hN : N ≤ t * M)
    (hp : ∀ n, N ≤ n → omega (n + t) % 2 = omega n % 2) (j : ℕ) :
    omega (t * M + t * j) % 2 = omega (t * M) % 2 := by
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

/-- **THE PARITY SEQUENCE OF `ω` IS APERIODIC.**  There is no eventual period of
the sequence `n ↦ ω n mod 2`.

Indeed, an eventual period `t` freezes `n ↦ ω (t·n) mod 2` past `N`; but for a
prime `p ∣ t` one has `ω (t·p^k) = ω t` while for a prime `q ∤ t` one has
`ω (t·q^k) = ω t + 1`, so the frozen values differ.  (For `t = 1` the same
contradiction comes from a prime `q` and `2q`.) -/
theorem omega_parity_not_eventuallyPeriodic :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → omega (n + t) % 2 = omega n % 2 := by
  rintro ⟨t, N, ht, hp⟩
  set M := N + 1 with hMdef
  have hNM : N ≤ t * M := by
    have h1 : 1 ≤ t := by omega
    have h2 := Nat.le_mul_of_pos_left M h1
    omega
  by_cases ht1 : t = 1
  · subst ht1
    obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (max (N + 1) 3)
    have hqM : M ≤ q := by
      rw [hMdef]
      omega
    have hq3 : 3 ≤ q := by have := hq; omega
    have hq2 : q ≠ 2 := by omega
    have hiff : (2 : ℕ) ∣ q ↔ 2 = 1 ∨ 2 = q := Nat.dvd_prime hqp
    have h2nd : (2 : ℕ) ∉ q.primeFactors := by
      intro hmem
      obtain ⟨h2p, h2d, _⟩ := Nat.mem_primeFactors.mp hmem
      rcases hiff.mp h2d with h | h
      · omega
      · omega
    have h1 : omega (2 * q) = omega q + 1 := by
      rw [Nat.mul_comm 2 q]
      exact omega_mul_of_not_dvd (n := q) (p := 2) (by omega) (by norm_num : Nat.Prime 2) h2nd
    have hone : omega q = 1 := by
      rw [show q = q ^ 1 by rw [pow_one]]
      exact omega_prime_pow hqp (by omega)
    have hA : omega (1 * q) % 2 = omega (1 * M) % 2 := by
      have := omega_parity_eventuallyPeriodic_const_mul (N := N) (t := 1) (M := M) (by omega) hNM hp (q - M)
      have heq : 1 * M + 1 * (q - M) = 1 * q := by
        simp only [one_mul]
        rw [Nat.add_sub_of_le hqM]
      rw [heq] at this
      exact this
    have hB : omega (1 * (2 * q)) % 2 = omega (1 * M) % 2 := by
      have h2qM : M ≤ 2 * q := by omega
      have := omega_parity_eventuallyPeriodic_const_mul (N := N) (t := 1) (M := M) (by omega) hNM hp
        (2 * q - M)
      have heq : 1 * M + 1 * (2 * q - M) = 1 * (2 * q) := by
        simp only [one_mul]
        rw [Nat.add_sub_of_le h2qM]
      rw [heq] at this
      exact this
    have hA' : omega q % 2 = omega (1 * M) % 2 := by
      have hq1 : omega (1 * q) % 2 = omega q % 2 := by rw [Nat.one_mul]
      rwa [hq1] at hA
    have hB' : omega (2 * q) % 2 = omega (1 * M) % 2 := by
      have hq2 : omega (1 * (2 * q)) % 2 = omega (2 * q) % 2 := by rw [Nat.one_mul]
      rwa [hq2] at hB
    rw [h1, hone] at hB'
    omega
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
    have hM1' : M ≤ t * (N + 1) := hM1
    have hM2' : M ≤ 2 ^ k2 := Nat.le_trans hM1' hk2'
    have hA : omega (t * p ^ k1) % 2 = omega (t * M) % 2 := by
      have hM' : M ≤ p ^ k1 := Nat.le_trans hM2 hpow_le
      have hle : t * M ≤ t * p ^ k1 := Nat.mul_le_mul_left t hM'
      have hrec : t * M + t * (p ^ k1 - M) = t * p ^ k1 := by
        rw [Nat.mul_sub, Nat.add_sub_of_le hle]
      have h1' := omega_parity_eventuallyPeriodic_const_mul (N := N) (t := t) (M := M) ht hNM hp (p ^ k1 - M)
      rwa [hrec] at h1'
    have hB : omega (t * q ^ k2) % 2 = omega (t * M) % 2 := by
      have hM' : M ≤ q ^ k2 := Nat.le_trans hM2' hqpow_le
      have hle : t * M ≤ t * q ^ k2 := Nat.mul_le_mul_left t hM'
      have hrec : t * M + t * (q ^ k2 - M) = t * q ^ k2 := by
        rw [Nat.mul_sub, Nat.add_sub_of_le hle]
      have h1' := omega_parity_eventuallyPeriodic_const_mul (N := N) (t := t) (M := M) ht hNM hp (q ^ k2 - M)
      rwa [hrec] at h1'
    have hA' : omega t % 2 = omega (t * M) % 2 := by rwa [h1] at hA
    have hB' : (omega t + 1) % 2 = omega (t * M) % 2 := by rwa [h2] at hB
    have hcontra : omega t % 2 ≠ (omega t + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one (omega t) with h | h
      · rcases Nat.mod_two_eq_zero_or_one (omega t + 1) with h' | h'
        · omega
        · omega
      · rcases Nat.mod_two_eq_zero_or_one (omega t + 1) with h' | h'
        · omega
        · omega
    exact hcontra (hA'.trans hB'.symm)

/-- `ω n mod 2 ≤ 1`: the parity of `ω` is a `{0,1}`-valued sequence. -/
theorem omega_mod_two_le (n : ℕ) : omega n % 2 ≤ 1 := by
  have : omega n % 2 = 0 ∨ omega n % 2 = 1 := Nat.mod_two_eq_zero_or_one (omega n)
  rcases this with h | h <;> rw [h] <;> omega

/-- **`ω (6^k) = 2` for `1 ≤ k`.** -/
theorem omega_six_pow (k : ℕ) (hk : 1 ≤ k) : omega (6 ^ k) = 2 := by
  have hcop : Nat.Coprime (2 : ℕ) 3 := by decide
  have hcop' : Nat.Coprime (2 ^ k) (3 ^ k) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]
      simp
    · rw [Nat.coprime_pow_right_iff (n := k) hk (a := 2 ^ k) (b := 3), Nat.coprime_comm,
        Nat.coprime_pow_right_iff (n := k) hk (a := 3) (b := 2), Nat.coprime_comm]
      exact hcop
  have h1 := omega_mul_of_coprime hcop'
  have h2 := omega_prime_pow (p := 2) (k := k) (by norm_num) hk
  have h3 := omega_prime_pow (p := 3) (k := k) (by norm_num) hk
  have h6 : (6 : ℕ) ^ k = 2 ^ k * 3 ^ k := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.mul_pow]
  rw [h6, h1, h2, h3]

/-- **THE PARITY SERIES OF `ω`**: `∑' n, (ω n mod 2) 2^-(n+1)`. -/
noncomputable def jsp87ParitySeries : ℝ := jsp87BinarySeries (fun n => omega n % 2)

/-- **THE PARITY SERIES OF `ω` IS IRRATIONAL.**  Its binary digits are the
parities of `ω`, which are aperiodic (`omega_parity_not_eventuallyPeriodic`),
and the Erdős criterion (`jsp87Binary_irrational_iff`, proved from scratch in
this file) turns aperiodicity into irrationality.

This is the closest provable sibling of `jsp_000087_main`: the same function `ω`,
the same binary method, the same criterion, with the carry dropped. -/
theorem jsp87ParitySeries_irrational : Irrational jsp87ParitySeries := by
  unfold jsp87ParitySeries
  refine jsp87Binary_irrational_of_notPeriodic (fun n => omega n % 2) omega_mod_two_le ?_ ?_
  · intro N
    obtain ⟨k, hk1, hk2⟩ := exists_pow_two_ge N
    have h6 : omega (6 ^ k) = 2 := omega_six_pow k hk1
    have hzero : omega (6 ^ k) % 2 = 0 := by
      rw [h6]
    have hk2' : N ≤ 6 ^ k := by
      have h6 : (6 : ℕ) ^ k = 2 ^ k * 3 ^ k := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.mul_pow]
      rw [h6]
      have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
      have h2 : 2 ^ k ≤ 2 ^ k * 3 ^ k := by
        have := Nat.le_mul_of_pos_left (2 ^ k) h1
        simpa [Nat.mul_comm] using this
      omega
    have hadd : N + (6 ^ k - N) = 6 ^ k := Nat.add_sub_of_le hk2'
    exact jsp87BinaryTail_lt_one (fun n => omega n % 2) omega_mod_two_le N ⟨6 ^ k - N, by
      rw [hadd]
      exact hzero⟩
  · rintro ⟨t, N, ht, hN, hper⟩
    exact omega_parity_not_eventuallyPeriodic ⟨t, N, ht, fun n hn => hper n hn⟩

/-! ## 7. Erdős' prime constant: a second complete instance -/

/-- The primality indicator as a `{0,1}`-valued sequence. -/
def jsp87PrimeBit (n : ℕ) : ℕ := if n.Prime then 1 else 0

theorem jsp87PrimeBit_le (n : ℕ) : jsp87PrimeBit n ≤ 1 := by
  by_cases h : n.Prime
  · simp [jsp87PrimeBit, h]
  · simp [jsp87PrimeBit, h]

/-- The primality indicator is `1` exactly at the primes. -/
theorem jsp87PrimeBit_eq_iff (n m : ℕ) : jsp87PrimeBit n = jsp87PrimeBit m ↔ (n.Prime ↔ m.Prime) := by
  by_cases h1 : n.Prime <;> by_cases h2 : m.Prime <;> simp [jsp87PrimeBit, h1, h2]

/-- `2 * m` is not prime whenever `2 ≤ m`. -/
theorem not_prime_two_mul (m : ℕ) (hm : 2 ≤ m) : ¬ Nat.Prime (2 * m) := by
  intro hp
  have hdvd : (2 : ℕ) ∣ 2 * m := ⟨m, by ring⟩
  have hiff : 2 = 1 ∨ 2 = 2 * m := (Nat.dvd_prime hp).mp hdvd
  rcases hiff with h | h
  · omega
  · omega

/-- **THE PRIMALITY INDICATOR IS APERIODIC.**  An eventual period `t > 0` would make
`p + j t` prime for every `j ≥ 0` once `p` is a prime past the threshold, but
`p + p t = p (1 + t)` is not prime. -/
theorem jsp87PrimeBit_not_eventuallyPeriodic :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → jsp87PrimeBit (n + t) = jsp87PrimeBit n := by
  rintro ⟨t, N, ht, hp⟩
  obtain ⟨p, hNle, hp'⟩ := Nat.exists_infinite_primes N
  have hkey : ∀ j : ℕ, Nat.Prime (p + j * t) := by
    intro j
    induction j with
    | zero => simpa using hp'
    | succ j ih =>
        have hstep : p + Nat.succ j * t = (p + j * t) + t := by
          rw [Nat.succ_eq_add_one]
          ring
        have h1 := hp (p + j * t) (by omega)
        rw [← hstep] at h1
        have heq : jsp87PrimeBit (p + Nat.succ j * t) = 1 ↔ jsp87PrimeBit (p + j * t) = 1 := by
          rw [h1]
        have hres : jsp87PrimeBit (p + Nat.succ j * t) = 1 := heq.mpr (by
          rw [jsp87PrimeBit, if_pos ih])
        by_cases hp : Nat.Prime (p + Nat.succ j * t)
        · exact hp
        · rw [jsp87PrimeBit, if_neg hp] at hres
          omega
  have hfinal := hkey p
  have hcontra : ¬ Nat.Prime (p + p * t) := by
    have hdvd : p ∣ p + p * t := ⟨1 + t, by ring⟩
    have hiff : p = 1 ∨ p = p + p * t := (Nat.dvd_prime hfinal).mp hdvd
    rcases hiff with h | h
    · exact absurd h hp'.ne_one
    · have hz : p * t = 0 := by omega
      rcases Nat.mul_eq_zero.mp hz with h1 | h1
      · exact absurd h1 hp'.ne_zero
      · omega
  exact hcontra hfinal

/-- **ERDŐS' PRIME CONSTANT IS IRRATIONAL.**  The series `∑' n, [n prime] 2^-(n+1)`
is irrational, by the criterion of this file: its digits are the primality
indicator, which is aperiodic.  (Erdős 1948 proved this classical fact; here it
is a complete Lean proof from scratch.) -/
noncomputable def jsp87PrimeSeries : ℝ := jsp87BinarySeries jsp87PrimeBit

theorem jsp87PrimeSeries_irrational : Irrational jsp87PrimeSeries := by
  unfold jsp87PrimeSeries
  refine jsp87Binary_irrational_of_notPeriodic jsp87PrimeBit jsp87PrimeBit_le ?_ ?_
  · intro N
    have hle : N ≤ 2 * (N + 2) := by
      have h1 : N + 2 ≤ 2 * (N + 2) := Nat.le_mul_of_pos_left (N + 2) (by omega)
      omega
    have hzero : jsp87PrimeBit (2 * (N + 2)) = 0 := by
      rw [jsp87PrimeBit]
      exact if_neg (not_prime_two_mul (N + 2) (by omega))
    exact jsp87BinaryTail_lt_one jsp87PrimeBit jsp87PrimeBit_le N ⟨2 * (N + 2) - N, by
      rw [Nat.add_sub_of_le hle]
      exact hzero⟩
  · rintro ⟨t, N, ht, hN, hper⟩
    exact jsp87PrimeBit_not_eventuallyPeriodic ⟨t, N, ht, fun n hn => hper n hn⟩

/-! ## 8. Why this does not close JSP-000087: the Erdős series really carries -/

/-- The partial sum of the Erdős series over `n < 7` is exactly `1/4`. -/
theorem jsp87Series_partial_sum_seven :
    (∑ n ∈ Finset.range 7, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 1 / 4 := by
  have h2 : omega 2 = 1 := by native_decide
  have h3 : omega 3 = 1 := by native_decide
  have h4 : omega 4 = 1 := by native_decide
  have h5 : omega 5 = 1 := by native_decide
  have h6 : omega 6 = 2 := by native_decide
  norm_num [h2, h3, h4, h5, h6, omega_zero, omega_one, Finset.sum_range_succ]

/-- **`1/4 ≤ S`.**  The six nonzero terms of the series already sum to `1/4`. -/
theorem jsp87Series_ge_quarter : 1 / 4 ≤ jsp87Series := by
  refine (sum_range_le_jsp87Series 7 (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (by positivity))).trans' ?_
  rw [jsp87Series_partial_sum_seven]

/-- **`S < 1/2`.**  The tail past `N = 5` is at most `(5+1) · 2^-5 = 3/16`, and the
partial sum over `n < 5` is `7/32`, so `S ≤ 13/32 < 1/2`. -/
theorem jsp87Series_lt_half : jsp87Series < 1 / 2 := by
  have h1 := jsp87_series_eq_sum_add_tail 5
  have h2 : (∑ i ∈ Finset.range 5, jsp87Term i) = 7 / 32 := by
    simp only [jsp87Term]
    exact jsp87Series_partial_sum_five
  have h3 := jsp87Tail_le 5
  rw [h1, h2]
  rw [show (5 + 1 : ℕ) = 6 by rfl] at h3
  norm_num at h3
  linarith

/-- **THE ERDŐS SERIES CARRIES AT `N = 1`.**  `⌊2S⌋ = 0` and `⌊4S⌋ = 1`. -/
theorem jsp87_floor_two_S : ⌊(2 : ℝ) * jsp87Series⌋ = 0 := by
  have h0 := jsp87Series_nonneg
  have h1 := jsp87Series_ge_quarter
  have h2 := jsp87Series_lt_half
  rw [Int.floor_eq_iff]
  constructor
  · norm_num
    linarith
  · norm_num
    linarith

theorem jsp87_floor_four_S : ⌊(2 : ℝ) ^ 2 * jsp87Series⌋ = 1 := by
  have hfour : (2 : ℝ) ^ 2 = 4 := by norm_num
  have h1 := jsp87Series_ge_quarter
  have h2 := jsp87Series_lt_half
  rw [hfour, Int.floor_eq_iff]
  constructor
  · norm_num
    linarith
  · norm_num
    linarith

/-- **THE FIRST BINARY DIGIT OF THE ERDŐS SERIES IS `1`, ALTHOUGH `ω 1 = 0`.**
The Erdős series carries: its digits are *not* the `ω`-digits, so the primary
(aperiodicity) criterion cannot be applied to `ω` itself.  This is exactly the
obstruction that `jsp87_digit_bookkeeping` (round 41) exhibits symbolically, and
it is the reason the headline statement `jsp_000087_main` remains unproved. -/
theorem jsp87_digit_one : jsp87Digit 1 = 1 := by
  have h1 := jsp87_floor_digit (M := 1)
  have h2 := jsp87_floor_two_S
  have h3 := jsp87_floor_four_S
  rw [show (1 + 1 : ℕ) = 2 by rfl, show (2 : ℝ) ^ 1 = 2 by norm_num, h3, h2] at h1
  omega

/-- **The digits of the Erdős series are not the `ω`-digits.** -/
theorem jsp87_digit_ne_omega_one : ¬ ((jsp87Digit 1 : ℤ) = (omega 1 : ℤ)) := by
  rw [jsp87_digit_one, omega_one]
  norm_num

/-- **The digits of the Erdős series are not even the parities of `ω`.**  So the
aperiodicity of `ω mod 2` proved in this file does not transfer to the digits of
`S`: the missing step of `jsp_000087_main` is the aperiodicity of the *binary
digits*, exactly as in round 46's blocker `jsp87Series_irrational_of_blockNotPeriodic`. -/
theorem jsp87_digit_ne_parity_one : ¬ ((jsp87Digit 1 : ℤ) = (omega 1 % 2 : ℤ)) := by
  rw [jsp87_digit_one, omega_one]
  norm_num

end JSP87
