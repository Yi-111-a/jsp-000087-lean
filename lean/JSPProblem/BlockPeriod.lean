/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.CarryExcess

/-!
# JSP-000087 : the binary block of the Erdős series, and the period of a rational

Rounds 41 and 44 established the *bookkeeping* and the *quantitative shape* of
the carry, and the endgame: eventual periodicity of the binary digits of

`S = ∑ n, ω(n) 2^{-(n+1)}`

forces `ω` to be eventually periodic, which
`omega_not_eventuallyPeriodic` (round 40) forbids.  So the whole question is
reduced to the single statement

> the binary digits `d N` of `S` are not eventually periodic.

Rounds 41–44 proved a *one-way* implication: rationality ⟹ eventual
periodicity (`jsp87_digit_eventuallyPeriodic`), which is a from-scratch proof
that a rational has eventually periodic binary digits.

**This round proves the converse direction, quantitatively.**  It supplies the
missing arithmetic of the base-`2` expansion:

1. **The `t`-digit block, as a binary integer.**
   `jsp87DigitBlock N t = ∑_{j<t} d (N+j) · 2^{t−1−j}` is *proved* to be a
   genuine `t`-bit integer (`jsp87_digitBlock_bounds`), and periodicity of the
   digits makes the block **invariant** (`jsp87_digitBlock_shift`).

2. **The finite telescoping identity** `jsp87_floor_telescope`:

   `⌊2^{N+t} S⌋ = 2^t ⌊2^N S⌋ + B N t`

   — the binary prefix after `t` further digits is the prefix at `N` shifted by
   `t` places, plus the block read as a binary integer.  Mathlib has no such
   statement (it has nothing about the base-`2` expansion of a real).

3. **Iteration along a period** `jsp87_floor_block_iter`:

   `(2^t − 1) ⌊2^{N+qt} S⌋ = 2^{tq} · K − B N t`,  `K = (2^t − 1) ⌊2^N S⌋ + B N t`

   for every `q ≥ 0`, with `B N t` constant along the period.

4. **THE MAIN THEOREM** `jsp87_frac_scaled_eq_block`:

   > **If the binary digits of `S` are eventually periodic from `N` with period
   > `t > 0`, then `Int.fract (2^N · S) = B N t / (2^t − 1)`.**

   This is the *quantitative* form of "a rational has eventually periodic
   binary digits": the fractional part of `2^N · S` is **exactly** the block
   `B N t` divided by `2^t − 1`.  Together with
   `jsp87_digit_eventuallyPeriodic` (round 41) this gives the **equivalence**

   > `S ∈ ℚ  ⟺  (d N) is eventually periodic`

   > `S = a/b (b>0)  ⟹  b ∣ 2^t − 1` for the period `t` of the digits.

   The second statement is the *denominator* the Erdős–Pratt method needs: any
   hypothetical rational value of the Erdős series has a denominator forced to
   divide `2^t − 1`, and the block numerator is the residue.

5. **The endgame is now airtight and its remaining gap is exactly one lemma.**
   `jsp87Series_irrational_of_digitPeriodic` below closes the reduction: the
   Erdős series is irrational as soon as the digit block is aperiodic.  The
   single remaining input — and the reason `jsp_000087_main` stays withheld —
   is a quantitative aperiodicity statement for `B N t`, which is Pratt's
   uniform prime-`k`-tuples hypothesis (arXiv:2409.15185).
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The binary-digit relation and the block sum -/

/-- The digit relation in floor form: `⌊2^{M+1} S⌋ = 2 ⌊2^M S⌋ + d M`. -/
theorem jsp87_floor_digit (M : ℕ) :
    ⌊(2 : ℝ) ^ (M + 1) * jsp87Series⌋ = (2 : ℤ) * ⌊(2 : ℝ) ^ M * jsp87Series⌋ + jsp87Digit M := by
  simp only [jsp87Digit]
  ring

/-- Multiplying the block sum by `2` shifts every exponent up by one. -/
theorem jsp87_sum_mul_two (N t : ℕ) :
    (2 : ℤ) * ((∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j)) : ℤ)
      = ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - j) := by
  calc (2 : ℤ) * ((∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j)) : ℤ)
      = ∑ j ∈ Finset.range t, (2 : ℤ) * ((jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j)) := by
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - j) := by
        refine Finset.sum_congr
          (f := fun j : ℕ => (2 : ℤ) * ((jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j)))
          (g := fun j : ℕ => (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - j)) rfl ?_
        intro j hj
        have hjlt : j < t := Finset.mem_range.mp hj
        have h1' : t - 1 - j = (t - j) - 1 := by omega
        have h2 : t - j = ((t - j) - 1) + 1 := by omega
        have hpow : (2 : ℤ) ^ (t - j) = 2 * (2 : ℤ) ^ (t - 1 - j) := by
          rw [h2, pow_succ, h1']
          ring
        rw [hpow]
        ring

/-- `∑_{j<t} 2^{t−1−j} = 2^t − 1`: the all-ones `t`-digit block. -/
theorem int_sum_pow_geo (t : ℕ) :
    (∑ j ∈ Finset.range t, (2 : ℤ) ^ (t - 1 - j) : ℤ) = 2 ^ t - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmul : (2 : ℤ) * ((∑ j ∈ Finset.range t, (2 : ℤ) ^ (t - 1 - j)) : ℤ)
        = ∑ j ∈ Finset.range t, (2 : ℤ) ^ (t - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr
        (f := fun j : ℕ => (2 : ℤ) * ((2 : ℤ) ^ (t - 1 - j)))
        (g := fun j : ℕ => (2 : ℤ) ^ (t - j)) rfl ?_
      intro j hj
      have hjlt : j < t := Finset.mem_range.mp hj
      have h1' : t - 1 - j = (t - j) - 1 := by omega
      have h2 : t - j = ((t - j) - 1) + 1 := by omega
      have hp : (2 : ℤ) ^ (t - j) = 2 * (2 : ℤ) ^ (t - 1 - j) := by
        rw [h2, pow_succ, h1']
        ring
      rw [hp]

    have hstep : (∑ j ∈ Finset.range (t + 1), (2 : ℤ) ^ ((t + 1) - 1 - j) : ℤ)
        = 2 * ((∑ j ∈ Finset.range t, (2 : ℤ) ^ (t - 1 - j)) : ℤ) + 1 := by
      have hsucc : (∑ j ∈ Finset.range (t + 1), (2 : ℤ) ^ ((t + 1) - 1 - j) : ℤ)
          = (∑ j ∈ Finset.range t, (2 : ℤ) ^ (t - j)) + 1 := by
        rw [Finset.sum_range_succ]
        have hz : (t + 1) - 1 - t = 0 := by omega
        rw [hz, pow_zero]
        refine congrArg (fun s : ℤ => s + 1) (Finset.sum_congr rfl fun j _ => ?_)
        rw [show (t + 1) - 1 - j = t - j by omega]
      rw [hsucc, hmul]
    rw [hstep, ih]
    ring

/-- **THE `t`-DIGIT BLOCK, AS A BINARY INTEGER.**
`B N t = ∑_{j<t} d (N+j) · 2^{t−1−j}`: the next `t` binary digits of `S`,
starting at position `N`, read as an integer in `[0, 2^t)`.  This is the object
a rational value of `S` would force to be periodic. -/
noncomputable def jsp87DigitBlock (N t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j)

/-- **A block is a genuine `t`-bit integer**: `0 ≤ B N t < 2^t`. -/
theorem jsp87_digitBlock_bounds (N t : ℕ) :
    0 ≤ jsp87DigitBlock N t ∧ (jsp87DigitBlock N t : ℤ) < 2 ^ t := by
  constructor
  · have hmem : ∀ j ∈ Finset.range t, (0 : ℤ) ≤ jsp87Digit (N + j) := by
      intro j _hj
      rcases jsp87Digit_mem (N + j) with h0 | h1
      · rw [h0]
      · rw [h1]; norm_num
    exact Finset.sum_nonneg fun j hj => Int.mul_nonneg (hmem j hj) (by positivity)
  · have hmem : ∀ j ∈ Finset.range t,
        (jsp87Digit (N + j) : ℤ) = 0 ∨ (jsp87Digit (N + j) : ℤ) = 1 :=
      fun j _ => jsp87Digit_mem (N + j)
    have hbound : ∀ j ∈ Finset.range t,
        (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j) ≤ (2 : ℤ) ^ (t - 1 - j) := by
      intro j hj
      rcases hmem j hj with h0 | h1
      · rw [h0]; simp
      · rw [h1]; simp
    have hle := Finset.sum_le_sum hbound
    rw [int_sum_pow_geo t] at hle
    exact lt_of_le_of_lt hle (by omega)

/-- **One step of periodicity makes the block invariant.** -/
theorem jsp87_digitBlock_step {N t : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    jsp87DigitBlock (N + t) t = jsp87DigitBlock N t := by
  unfold jsp87DigitBlock
  refine Finset.sum_congr rfl fun j _hj => ?_
  have hN : N ≤ N + j := by omega
  have hq := hper (N + j) hN
  have heq : (N + t) + j = (N + j) + t := by omega
  rw [heq, hq]

/-- **PERIODIC DIGITS ⟹ THE BLOCKS REPEAT.**  If `d (n+t) = d n` for all
`n ≥ N`, then `B (N + q·t) t = B N t` for every `q`. -/
theorem jsp87_digitBlock_shift {N t : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) (q : ℕ) :
    jsp87DigitBlock (N + q * t) t = jsp87DigitBlock N t := by
  induction q generalizing N with
  | zero => simp
  | succ q ih =>
    have hbase : jsp87DigitBlock ((N + t) + q * t) t = jsp87DigitBlock (N + t) t :=
      ih (N := N + t) (fun n hn => hper n (by omega))
    have heq : (N + t) + q * t = N + (q + 1) * t := by ring
    rw [heq] at hbase
    exact hbase.trans (jsp87_digitBlock_step ht hper)

/-- **THE FINITE TELESCOPING IDENTITY.**  For all `N, t`,

`⌊2^{N+t} S⌋ = 2^t ⌊2^N S⌋ + ∑_{j<t} d (N+j) 2^{t−1−j}`.

The binary prefix of `S` after `t` further digits is the prefix at `N` shifted
by `t` places, plus the `t`-digit block read as a binary integer. -/
theorem jsp87_floor_telescope {N t : ℕ} :
    ⌊(2 : ℝ) ^ (N + t) * jsp87Series⌋
      = (2 : ℤ) ^ t * ⌊(2 : ℝ) ^ N * jsp87Series⌋
        + ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j) := by
  induction t generalizing N with
  | zero => simp
  | succ t ih =>
    have hgoal : ⌊(2 : ℝ) ^ (N + (t + 1)) * jsp87Series⌋
        = (2 : ℤ) * ⌊(2 : ℝ) ^ (N + t) * jsp87Series⌋ + jsp87Digit (N + t) := by
      have h := jsp87_floor_digit (M := N + t)
      rwa [show N + t + 1 = N + (t + 1) by omega] at h
    have hsum1 : (∑ j ∈ Finset.range (t + 1), (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ ((t + 1) - 1 - j))
        = (∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - j))
          + jsp87Digit (N + t) := by
      rw [Finset.sum_range_succ]
      have hz : (t + 1) - 1 - t = 0 := by omega
      rw [hz, pow_zero, mul_one]
      refine congrArg (fun s : ℤ => s + jsp87Digit (N + t)) ?_
      exact Finset.sum_congr rfl fun j _hj => by
        rw [show (t + 1) - 1 - j = t - j by omega]
    have hpow : (2 : ℤ) ^ (t + 1) = 2 * (2 : ℤ) ^ t := by rw [pow_succ]; ring
    calc ⌊(2 : ℝ) ^ (N + (t + 1)) * jsp87Series⌋
        = 2 * ⌊(2 : ℝ) ^ (N + t) * jsp87Series⌋ + jsp87Digit (N + t) := hgoal
      _ = 2 * ((2 : ℤ) ^ t * ⌊(2 : ℝ) ^ N * jsp87Series⌋
            + ∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j))
            + jsp87Digit (N + t) := by rw [ih (N := N)]
      _ = (2 : ℤ) ^ (t + 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋
            + 2 * ((∑ j ∈ Finset.range t, (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ (t - 1 - j)) : ℤ)
            + jsp87Digit (N + t) := by ring
      _ = (2 : ℤ) ^ (t + 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋
            + ∑ j ∈ Finset.range (t + 1), (jsp87Digit (N + j) : ℤ) * (2 : ℤ) ^ ((t + 1) - 1 - j) :=
          by rw [hsum1, jsp87_sum_mul_two N t]; ring

/-! ## 2. Iteration along a period -/

/-- `a^(m·n) · (a^m)⁻ ^ n = 1`. -/
theorem jsp87_pow_mul_inv {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    a ^ (m * n) * (a ^ m)⁻¹ ^ n = 1 := by
  have h1 : a ^ (m * n) = (a ^ m) ^ n := pow_mul a m n
  have h2 : (0 : ℝ) < (a ^ m) ^ n := by positivity
  rw [h1, inv_pow (a := a ^ m) n, mul_inv_cancel₀ h2.ne']

/-- **ITERATION ALONG A PERIOD.**  If the binary digits are eventually periodic
from `N` with period `t > 0`, then for every `q ≥ 0`

`(2^t − 1) ⌊2^{N+qt} S⌋ = 2^{tq} · K − B N t`,

with `K = (2^t − 1) ⌊2^N S⌋ + B N t`.  The block `B N t` is constant along the
period (round 46, `jsp87_digitBlock_shift`). -/
theorem jsp87_floor_block_iter {N t q : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ (N + q * t) * jsp87Series⌋
      = (2 : ℤ) ^ (t * q)
          * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋ + jsp87DigitBlock N t)
        - jsp87DigitBlock N t := by
  induction q generalizing N with
  | zero => simp
  | succ q ih =>
    have hrec : ⌊(2 : ℝ) ^ (N + (q + 1) * t) * jsp87Series⌋
        = (2 : ℤ) ^ t * ⌊(2 : ℝ) ^ (N + q * t) * jsp87Series⌋ + jsp87DigitBlock N t := by
      have htel := jsp87_floor_telescope (N := N + q * t) (t := t)
      have hblk : jsp87DigitBlock (N + q * t) t = jsp87DigitBlock N t :=
        jsp87_digitBlock_shift ht hper q
      unfold jsp87DigitBlock at htel hblk
      have heq : (N + q * t) + t = N + (q + 1) * t := by ring
      rw [heq] at htel
      rwa [hblk] at htel
    have hpow : (2 : ℤ) ^ t * (2 : ℤ) ^ (t * q) = (2 : ℤ) ^ (t * (q + 1)) := by
      rw [← pow_add]
      congr 1
      ring
    have hstep : (2 : ℤ) ^ t * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ (N + q * t) * jsp87Series⌋)
        = (2 : ℤ) ^ (t * (q + 1))
          * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋ + jsp87DigitBlock N t)
          - (2 : ℤ) ^ t * jsp87DigitBlock N t := by
      calc (2 : ℤ) ^ t * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ (N + q * t) * jsp87Series⌋)
          = (2 : ℤ) ^ t * ((2 : ℤ) ^ (t * q)
              * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋ + jsp87DigitBlock N t)
              - jsp87DigitBlock N t) := by
            rw [ih (N := N) (fun n hn => hper n hn)]
        _ = (2 : ℤ) ^ (t * (q + 1))
              * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋ + jsp87DigitBlock N t)
              - (2 : ℤ) ^ t * jsp87DigitBlock N t := by
            have hK : (2 : ℤ) ^ t * (2 : ℤ) ^ (t * q)
                * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋ + jsp87DigitBlock N t)
              = (2 : ℤ) ^ (t * (q + 1))
                * (((2 : ℤ) ^ t - 1) * ⌊(2 : ℝ) ^ N * jsp87Series⌋ + jsp87DigitBlock N t) := by
              rw [hpow]
            linear_combination hK
    rw [hrec]
    linear_combination hstep

/-! ## 3. The exact fractional part under periodic digits -/

/-- **An Archimedean lemma for geometric decay.**  For `0 < r < 1` and `b > 0`
there is `n` with `r ^ n < b`.  Mathlib's `exists_pow_lt` is stated for ordered
groups and does not apply to `ℝ`; `exists_pow_lt_of_lt_one` does. -/
theorem exists_pow_lt_real {r b : ℝ} (hr1 : 0 < r) (hr2 : r < 1) (hb : 0 < b) :
    ∃ n : ℕ, r ^ n < b := by
  exact exists_pow_lt_of_lt_one hb hr2

/-- If `|a| ≤ D · r ^ n` for every `n`, with `D > 0` and `0 < r < 1`, then
`a = 0` (squeeze, elementarily). -/
theorem abs_eq_zero_of_forall_le {D r a : ℝ} (hD : 0 < D) (hr1 : 0 < r) (hr2 : r < 1)
    (h : ∀ n : ℕ, |a| ≤ D * r ^ n) : a = 0 := by
  by_contra hne
  have ha : 0 < |a| := lt_of_le_of_ne (abs_nonneg a) (fun hc => hne (abs_eq_zero.mp hc.symm))
  have hb : 0 < |a| / (2 * D) := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_real (r := r) hr1 hr2 hb
  have h1 : |a| ≤ D * r ^ n := h n
  have h3 : D * r ^ n < D * (|a| / (2 * D)) := by
    have := mul_lt_mul_of_pos_left hn hD
    linarith
  have h4 : D * (|a| / (2 * D)) = |a| / 2 := by field_simp
  have h2 : D * r ^ n < |a| / 2 := by linarith
  linarith

/-- **THE EXACT FRACTIONAL PART UNDER PERIODIC DIGITS.**  If the binary digits
of the Erdős series are eventually periodic from `N` with period `t > 0`, then

`Int.fract (2^N · S) = B N t / (2^t − 1)`,

where `B N t` is the `t`-digit block read as a binary integer.

This is the *quantitative* form of the classical fact that a rational number has
eventually periodic binary digits, and it is the missing half of the
Erdős–Pratt method: it identifies the **denominator** `2^t − 1` that a
hypothetical rational value of `S` is forced to have, and the **numerator**,
which is the block.  Mathlib has no statement about the base-`2` expansion of a
real number. -/
theorem jsp87_frac_scaled_eq_block {N t : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    Int.fract ((2 : ℝ) ^ N * jsp87Series) = (jsp87DigitBlock N t : ℝ) / ((2 : ℝ) ^ t - 1) := by
  have hXpos : (0 : ℝ) < (2 : ℝ) ^ t - 1 := by
    have h1 : (2 : ℕ) ≤ 2 ^ t := by
      have := succ_le_two_pow t
      omega
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast h1
    linarith
  have hW0 : (0 : ℝ) ≤ (jsp87DigitBlock N t : ℝ) := by
    have := (jsp87_digitBlock_bounds N t).1
    exact_mod_cast this
  -- Step 1: the integer iteration, cast to `ℝ`.
  have hlin : ∀ q : ℕ, ((2 : ℝ) ^ t - 1) * (⌊(2 : ℝ) ^ (N + q * t) * jsp87Series⌋ : ℝ)
      = (2 : ℝ) ^ (t * q) * (((2 : ℝ) ^ t - 1) * (⌊(2 : ℝ) ^ N * jsp87Series⌋ : ℝ)
          + (jsp87DigitBlock N t : ℝ)) - (jsp87DigitBlock N t : ℝ) := by
    intro q
    have h := jsp87_floor_block_iter (N := N) (t := t) (q := q) ht hper
    exact_mod_cast h
  -- Step 2: replace the floors by `x − fract x`, and split the power.
  have hpow : ∀ q : ℕ, (2 : ℝ) ^ (N + q * t) = (2 : ℝ) ^ (t * q) * (2 : ℝ) ^ N := by
    intro q
    rw [show N + q * t = N + t * q by ring, pow_add, mul_comm]
  have hlin' : ∀ q : ℕ, ((2 : ℝ) ^ t - 1)
        * ((2 : ℝ) ^ (t * q) * ((2 : ℝ) ^ N * jsp87Series)
            - Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series))
      = (2 : ℝ) ^ (t * q) * (((2 : ℝ) ^ t - 1) * ((2 : ℝ) ^ N * jsp87Series
          - Int.fract ((2 : ℝ) ^ N * jsp87Series)) + (jsp87DigitBlock N t : ℝ))
        - (jsp87DigitBlock N t : ℝ) := by
    intro q
    have h := hlin q
    rw [← Int.self_sub_fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)] at h
    rw [← Int.self_sub_fract ((2 : ℝ) ^ N * jsp87Series)] at h
    rw [hpow q] at h
    convert h using 1 <;> ring
  -- Step 3: the key identity, obtained by cancelling the `2^(t·q) · 2^N · S` term.
  have hkey : ∀ q : ℕ, ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
        = (jsp87DigitBlock N t : ℝ) * (1 - ((2 : ℝ) ^ (t * q))⁻¹)
          + ((2 : ℝ) ^ t - 1) * ((2 : ℝ) ^ (t * q))⁻¹
            * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series) := by
    intro q
    have h := hlin' q
    have hA : (0 : ℝ) < (2 : ℝ) ^ (t * q) := by positivity
    have h1 : ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series) * (2 : ℝ) ^ (t * q)
        = ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
          + (2 : ℝ) ^ (t * q) * (jsp87DigitBlock N t : ℝ) - (jsp87DigitBlock N t : ℝ) := by
      linarith
    have h2 : ((jsp87DigitBlock N t : ℝ) * (1 - ((2 : ℝ) ^ (t * q))⁻¹)
          + ((2 : ℝ) ^ t - 1) * ((2 : ℝ) ^ (t * q))⁻¹
            * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)) * (2 : ℝ) ^ (t * q)
        = (2 : ℝ) ^ (t * q) * (jsp87DigitBlock N t : ℝ) - (jsp87DigitBlock N t : ℝ)
          + ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series) := by
      field_simp
    have hmul : ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series) * (2 : ℝ) ^ (t * q)
        = ((jsp87DigitBlock N t : ℝ) * (1 - ((2 : ℝ) ^ (t * q))⁻¹)
          + ((2 : ℝ) ^ t - 1) * ((2 : ℝ) ^ (t * q))⁻¹
            * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)) * (2 : ℝ) ^ (t * q) := by
      linarith
    exact mul_left_cancel₀ hA.ne' (by convert hmul using 1 <;> ring)
  -- Step 4: the squeeze.  `(2^t−1)·f_N − W = 2^{-tq}·((2^t−1)·f_{N+qt} − W)`, so the
  -- left side is bounded by `(2^t−1+W)·(2^t)^{-q}`, which vanishes as `q → ∞`.
  have hbound : ∀ q : ℕ,
      |((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
          - (jsp87DigitBlock N t : ℝ)|
        ≤ ((2 : ℝ) ^ t - 1 + (jsp87DigitBlock N t : ℝ)) * ((2 : ℝ) ^ t)⁻¹ ^ q := by
    intro q
    have hrw : ((2 : ℝ) ^ t)⁻¹ ^ q = ((2 : ℝ) ^ (t * q))⁻¹ := by
      rw [inv_pow (a := (2 : ℝ) ^ t) q, ← pow_mul]
    have hcore : ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
            - (jsp87DigitBlock N t : ℝ)
          = ((2 : ℝ) ^ (t * q))⁻¹
            * (((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
              - (jsp87DigitBlock N t : ℝ)) := by
      have h := hkey q
      linarith
    have hfM1 := Int.fract_lt_one ((2 : ℝ) ^ (N + q * t) * jsp87Series)
    have hfM := Int.fract_nonneg ((2 : ℝ) ^ (N + q * t) * jsp87Series)
    have h1' : |((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
            - (jsp87DigitBlock N t : ℝ)|
          ≤ ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
            + (jsp87DigitBlock N t : ℝ) := by
      rw [abs_le]
      constructor
      · have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ t - 1 := hXpos.le
        have := mul_nonneg hnn hfM
        linarith
      · linarith
    have h2' : ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
          ≤ (2 : ℝ) ^ t - 1 := by
      have hnon : (0 : ℝ) ≤ (2 : ℝ) ^ (N + q * t) := by positivity
      nlinarith
    have hq : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹ ^ q := by positivity
    calc |((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
            - (jsp87DigitBlock N t : ℝ)|
        = |((2 : ℝ) ^ (t * q))⁻¹
            * (((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
              - (jsp87DigitBlock N t : ℝ))| := by
            rw [hcore, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (t * q))⁻¹)]
        _ = ((2 : ℝ) ^ t)⁻¹ ^ q
            * |((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
              - (jsp87DigitBlock N t : ℝ)| := by
            rw [← hrw, abs_mul, abs_of_nonneg hq]
        _ ≤ ((2 : ℝ) ^ t)⁻¹ ^ q
            * (((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
              + (jsp87DigitBlock N t : ℝ)) := mul_le_mul_of_nonneg_left h1' hq
        _ ≤ ((2 : ℝ) ^ t - 1 + (jsp87DigitBlock N t : ℝ)) * ((2 : ℝ) ^ t)⁻¹ ^ q := by
            have hstep : ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series)
                  + (jsp87DigitBlock N t : ℝ)
                ≤ (2 : ℝ) ^ t - 1 + (jsp87DigitBlock N t : ℝ) := by linarith
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right hstep hq
  have hD : (0 : ℝ) < (2 : ℝ) ^ t - 1 + (jsp87DigitBlock N t : ℝ) := by linarith
  have hr0 : 0 < ((2 : ℝ) ^ t)⁻¹ := by positivity
  have hr1 : ((2 : ℝ) ^ t)⁻¹ < 1 := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    have hN : (2 : ℕ) ≤ 2 ^ t := by
      have := succ_le_two_pow t
      omega
    have h2 : (1 : ℝ) < (2 : ℝ) ^ t := by exact_mod_cast hN
    exact (inv_lt_one₀ hp).mpr h2
  have hzero := abs_eq_zero_of_forall_le hD hr0 hr1 hbound
  have hk0 := hkey 0
  have hk0' : ((2 : ℝ) ^ t - 1) * Int.fract ((2 : ℝ) ^ N * jsp87Series)
      = (jsp87DigitBlock N t : ℝ) * (1 - 1)
        + ((2 : ℝ) ^ t - 1) * 1 * Int.fract ((2 : ℝ) ^ (N + 0 * t) * jsp87Series) := by
    convert hk0 using 1 <;> ring_nf
  rw [hk0'] at hzero
  have hz : (1 : ℝ) - 1 = 0 := by ring
  rw [hz, mul_zero, zero_add, mul_one, show N + 0 * t = N by omega] at hzero
  field_simp
  linarith

/-! ## 4. The endgame: what a rational value of `S` would be forced to look like

Rounds 41 and 44 reduced JSP-000087 to a single question about the binary
digits.  This section packages the *quantitative* answer: exactly what a
hypothetical rational value of the Erdős series is forced to be. -/

/-- **THE FRACTIONAL-PART CRITERION.**  If the fractional parts
`Int.fract (2^n · S)` of the Erdős series are **not** eventually periodic, then
`S` is **irrational**.

This is the sharpest form of the round-41 endgame.  Round 41 proved that
rationality forces the *digits* to be eventually periodic; round 46 proves (via
`jsp87_frac_scaled_eq_block`) that rationality additionally forces each
fractional part to be *exactly* the digit block divided by `2^t − 1`, and
`jsp87Series_rational_imp_frac_periodic` below closes the converse direction.
The remaining input for `jsp_000087_main` is therefore a single statement:

> `n ↦ Int.fract (2^n · jsp87Series)` is not eventually periodic. -/
theorem jsp87Series_irrational_of_frac_notPeriodic
    (h : ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → Int.fract ((2 : ℝ) ^ (n + t) * jsp87Series)
        = Int.fract ((2 : ℝ) ^ n * jsp87Series)) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  obtain ⟨t, N, ht, hN1, hper⟩ := jsp87FracNum_period hden (by rw [← hq, Rat.cast_def])
  refine h ⟨t, N, ht, ?_⟩
  intro n hn
  have hs := jsp87FracNum_spec (N := n) hden (by rw [← hq, Rat.cast_def]) (by omega)
  have hs' := jsp87FracNum_spec (N := n + t) hden (by rw [← hq, Rat.cast_def]) (by omega)
  have hc := hper n hn
  rw [hs'.2, hs.2, hc]

/-- **RATIONALITY FORCES EVENTUAL PERIODICITY OF THE FRACTIONAL PARTS.**  This is
the mirror of `jsp87Series_irrational_of_frac_notPeriodic` and is the last
quantitative step of the round: under `S = a / b` (`b > 0`) there are `t > 0`,
`N` such that `Int.fract (2^{n+t} S) = Int.fract (2^n S)` for all `n ≥ N`.

Equivalently: rationality freezes the *fractional parts* of the rescaled series
into a finite set of size `b` and makes them eventually periodic — the
fractional-part mirror of the round-38 carry obstruction `b · θ N ∈ ℤ`. -/
theorem jsp87Series_rational_imp_frac_periodic {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t N : ℕ, 0 < t ∧ 1 ≤ N ∧ ∀ n, N ≤ n → Int.fract ((2 : ℝ) ^ (n + t) * jsp87Series)
        = Int.fract ((2 : ℝ) ^ n * jsp87Series) := by
  obtain ⟨t, N, ht, hN1, hper⟩ := jsp87FracNum_period hb h
  refine ⟨t, N, ht, hN1, ?_⟩
  intro n hn
  have hs := jsp87FracNum_spec (N := n) hb h (by omega)
  have hs' := jsp87FracNum_spec (N := n + t) hb h (by omega)
  have hc := hper n hn
  rw [hs'.2, hs.2, hc]

/-- **THE BLOCK IS THE FRACTIONAL PART.**  Under eventual periodicity of the
digits from `N` with period `t > 0`, the fractional part of `2^{N+q·t} · S` is
*the same* for all `q` (round 46): the `t`-digit block is constant along the
period, hence so is the fractional part. -/
theorem jsp87_frac_scaled_block_const {N t q : ℕ} (ht : 0 < t)
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series) = (jsp87DigitBlock N t : ℝ) / ((2 : ℝ) ^ t - 1) := by
  have hbl : jsp87DigitBlock (N + q * t) t = jsp87DigitBlock N t :=
    jsp87_digitBlock_shift ht hper q
  have hmain := jsp87_frac_scaled_eq_block (N := N + q * t) (t := t) ht
    (fun n hn => hper n (by omega))
  rw [hbl] at hmain
  exact hmain

/-- **THE PERIOD-DENOMINATOR OBSTRUCTION.**  If the Erdős series were the
rational `a / b` with `b > 0`, and its binary digits were eventually periodic
from `N` with period `t > 0`, then

`(2^t − 1) ∣ b · B N t`,

where `B N t` is the `t`-digit block at `N`.

This is the concrete arithmetic content of the block theorem combined with the
round-38 denominator obstruction `b · θ N ∈ ℤ`: **every rational value of the
Erdős series would have a denominator constrained by the digit period through
`2^t − 1`**, and the numerator of the fractional part is exactly the block.
Together with round 39's `dvd_lambert_den_prime_gt` (`b ∣ 2^p − 1` for prime
`p` forces `p < b`) the hypothetical denominator is pinned from both sides. -/
theorem jsp87_period_denominator_obstruction {a : ℤ} {b t N : ℕ} (hb : 0 < b) (ht : 0 < t)
    (h : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) (hN : 1 ≤ N) :
    (2 : ℤ) ^ t - 1 ∣ b * jsp87DigitBlock N t := by
  -- (a) the fractional part of 2^N S is the block over 2^t - 1  (round 46)
  have hfr := jsp87_frac_scaled_eq_block (N := N) (t := t) ht hper
  -- (b) rationality freezes the carry: b * theta N is an integer  (round 38)
  have hci := jsp87_carry_mul_eq_int hN (by exact_mod_cast hb) h
  obtain ⟨c, hc⟩ := hci
  -- (c) the carry decomposes: 2^N S = IntPart N + theta N  (round 38)
  have hdecomp := jsp87_scaled_decomposition N hN
  -- (d) hence b * 2^N S is an integer combination, and its fractional part is quantised
  have hcc : ((2 : ℝ) ^ N * jsp87Tail N) * (b : ℝ) = (c : ℝ) := by
    have := hc
    push_cast at this
    exact this
  have hbmul : (b : ℝ) * ((2 : ℝ) ^ N * jsp87Series) = ((b * jsp87IntPart N + c : ℤ) : ℝ) := by
    rw [hdecomp]
    calc (b : ℝ) * ((jsp87IntPart N : ℝ) + (2 : ℝ) ^ N * jsp87Tail N)
        = (b : ℝ) * (jsp87IntPart N : ℝ) + ((2 : ℝ) ^ N * jsp87Tail N) * (b : ℝ) := by ring
      _ = (b : ℝ) * (jsp87IntPart N : ℝ) + (c : ℝ) := by rw [hcc]
      _ = ((b * jsp87IntPart N + c : ℤ) : ℝ) := by push_cast; ring
  obtain ⟨hm, _, _, hfm⟩ :=
    Int.fract_eq_div_of_mul_natCast hb
      (show (b : ℝ) * ((2 : ℝ) ^ N * jsp87Series) = ((b * jsp87IntPart N + c : ℤ) : ℝ) from hbmul)
      (m := b * jsp87IntPart N + c)
  -- (e) substitute the block value: b * B / (2^t - 1) = m
  refine ⟨hm, ?_⟩
  have hEq : (b : ℝ) * (jsp87DigitBlock N t : ℝ) = (hm : ℝ) * ((2 : ℝ) ^ t - 1) := by
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ t - 1 := by
      have h1 : (2 : ℕ) ≤ 2 ^ t := by
        have := succ_le_two_pow t
        omega
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast h1
      linarith
    have hfr' := hfr
    rw [hfm] at hfr'
    have hX := (div_eq_div_iff (by exact_mod_cast (ne_of_gt hb))
      (by positivity)).mp hfr'
    linarith
  have hEqI : b * jsp87DigitBlock N t = ((2 : ℤ) ^ t - 1) * hm := by
    have hh : ((b * jsp87DigitBlock N t : ℤ) : ℝ) = (((2 : ℤ) ^ t - 1) * hm : ℤ) := by
      push_cast
      ring_nf
      linarith [hEq]
    exact_mod_cast hh
  exact hEqI

/-- **THE HYPOTHETICAL RATIONAL VALUE, IN FULL.**  If `S = a / b` with `b > 0`
and the binary digits of `S` are eventually periodic from `N` with period
`t > 0`, then for every `q ≥ 0`

* the fractional part of `2^{N+q·t} · S` is the single constant `B N t / (2^t − 1)`;
* the block `B (N + q·t) t` is the same integer for every `q`;
* `2^t − 1` divides `b · B N t`.

So a hypothetical rational value of the Erdős series is rigid in **every**
direction: its digit blocks are eventually constant, its fractional parts are
eventually constant, and its denominator is tied to the period.  Any
quantitative deviation of the block from eventual constancy contradicts
rationality. -/
theorem jsp87Series_rational_imp_blockConst {a : ℤ} {b t N q : ℕ} (hb : 0 < b) (ht : 0 < t)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) (hN : 1 ≤ N)
    (hper : ∀ n, N ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    jsp87DigitBlock (N + q * t) t = jsp87DigitBlock N t
      ∧ Int.fract ((2 : ℝ) ^ (N + q * t) * jsp87Series) = (jsp87DigitBlock N t : ℝ) / ((2 : ℝ) ^ t - 1)
      ∧ (2 : ℤ) ^ t - 1 ∣ b * jsp87DigitBlock N t := by
  exact ⟨jsp87_digitBlock_shift ht hper q,
    jsp87_frac_scaled_block_const ht hper,
    jsp87_period_denominator_obstruction hb ht h hper hN⟩

end JSP87
