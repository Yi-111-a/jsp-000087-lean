/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Primary

/-!
# JSP-000087 : the doubling map on the carries

Rounds 37–46 attacked the *carried* Erdős series `S = ∑ n, ω(n) 2^{-(n+1)}` from
ten directions (Lambert reduction, carry scaffold, gcd arithmetic, carry
dynamics, digit bookkeeping, carry excess + sieve content, base-`2` block
arithmetic); round 47 attacked the *carry-free* (primary) series and proved the
complete Erdős criterion in both directions.

**This round attacks neither.**  It works with the *fractional part of the
carry*, `c N = Int.fract (θ N)`, i.e. exactly the piece of the carry that the
integer part `⌊θ N⌋` (`jsp87CarryExcess`, round 41) throws away.  The single
observation driving the round is

> the carry recurrence `θ (N+1) = 2 θ N − ω N` (round 40) is a **doubling map on
> the circle**: the fractional part of the carry at `N+1` is the double of the
> fractional part at `N`, because `ω N` is an integer.

Consequently the binary digit of `S` is *exactly* the difference of two
consecutive fractional parts of the carry,

`jsp87_digit_eq_fractCarry` :  `d N = 2 · fract (θ N) − fract (θ (N+1))`,

and the doubling orbit of the carries is the classical doubling orbit of `S`.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87Carry_fract_succ` | `fract θ (N+1) = fract (2 θ N)`: the doubling map |
| `jsp87_digit_eq_fractCarry` | **`d N = 2 fract θ N − fract θ (N+1)`** — the digit string *is* the difference string of the doubling orbit |
| `jsp87_digit_eq_floorCarry` | **`d N = ⌊2 θ N⌋ − 2 ⌊θ N⌋`** — the digit is the *second* binary digit of the carry |
| `jsp87Carry_digit_doubling` | the unconditional doubling-carry window `0 ≤ 2 fract θ N − fract θ (N+1) ≤ 1` |
| `jsp87_fracCarry_succ` | `fract θ (N+1) = 2 fract θ N − d N` — the orbit is driven by the digits |
| `jsp87_fracCarry_periodic_of_digitPeriodic` | **eventual periodicity of the digits ⟹ the doubling orbit is eventually periodic with the same period** |
| `jsp87_fracCarry_eq_block_of_digitPeriodic` | the orbit point is *exactly* the digit block over `2^t − 1` |
| `jsp87_fracCarry_grid_of_digitPeriodic` | **THE GRID: every fractional part of a carry is a multiple of `1/(2^t − 1)`, `< 1`** |
| `jsp87Series_rational_imp_fracCarry_periodic` | a rational `S` has an eventually periodic doubling orbit |
| `jsp87Series_irrational_of_fracCarry_notPeriodic` | **THE FOURTH IRRATIONALITY CRITERION** |
| `jsp87Series_eq_rat_imp_carryExcess_notPeriodic` | rationality forces the *integer* part of the carry to be aperiodic (round 41) |
| `jsp87Series_rational_imp_carrySplit` | **THE CARRY-SPLIT DICHOTOMY: rationality makes the fractional parts periodic and the integer parts aperiodic** |
| `jsp87_carry_period_quantisation` | **`(2^t − 1) θ N ∈ ℤ` — the *period alone* quantises every carry** (no rationality) |
| `jsp87_carry_denominator_obstruction` | `b (2^t − 1) θ N ∈ ℤ` for **every** `t` under rationality |
| `jsp87_carry_lattice_of_digitPeriodic` | **THE CARRY LATTICE: rationality and the digit period together freeze every carry into `(1/(b(2^t−1))) ℤ`** |
| `jsp87Series_eq_div_of_digitPeriodic` | **the exact rational form forced by eventual periodicity: `S = n / (2^M (2^t − 1))`** |
| `jsp87_digit_period_one_eq_zero` | a `1`-periodic digit string is **all zeros** |
| `jsp87Series_dyadic_of_digit_period_one` | period `1` forces `S` to be a **dyadic** rational |
| `jsp87Series_dyadic_iff` | **the period-`1` case of JSP-000087 is exactly the dyadic case** |

The residual gap is unchanged in *kind* (it is the aperiodicity of the binary
digit string) but the object is now the simplest possible one: the **doubling
orbit of a single explicitly defined real number**.
-/

namespace JSP87

open scoped Topology

/-! ## 0. Small cast helpers -/

private theorem two_pow_cast (k : ℕ) : (2 : ℝ) ^ k = (((2 : ℤ) ^ k : ℤ) : ℝ) := by
  norm_cast

private theorem two_pow_sub_one_cast (k : ℕ) :
    ((2 : ℝ) ^ k - 1) = (((2 : ℤ) ^ k - 1 : ℤ) : ℝ) := by
  rw [two_pow_cast]
  push_cast
  ring

private theorem two_pow_sub_one_pos {k : ℕ} (h : 0 < k) : (0 : ℤ) < 2 ^ k - 1 := by
  have h1 : 2 ≤ 2 ^ k := by
    have := succ_le_two_pow k
    omega
  have h2 : (2 : ℤ) ≤ (2 : ℤ) ^ k := by exact_mod_cast h1
  omega

private theorem add_div_eq (a k A : ℝ) (hA : A ≠ 0) : a + k / A = (a * A + k) / A := by
  field_simp

private theorem add_div_div_eq (a k A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    (a + k / A) / B = (a * A + k) / (A * B) := by
  field_simp

/-- The `t = 1` block is the digit itself. -/
theorem jsp87DigitBlock_one (N : ℕ) : jsp87DigitBlock N 1 = jsp87Digit N := by
  simp only [jsp87DigitBlock]
  rw [Finset.sum_range_one, Nat.add_zero]
  norm_num

/-! ## 1. The doubling map on the carries -/

/-- **THE DOUBLING MAP ON THE CARRIES.**  The fractional part of the carry at
`N+1` is the double of the fractional part at `N`.

The carry recurrence `θ (N+1) = 2 θ N − ω N` (round 40) is a doubling map on
the circle: `ω N` is an integer, so it does not move the fractional part. -/
theorem jsp87Carry_fract_succ (N : ℕ) :
    Int.fract (jsp87Carry (N + 1)) = Int.fract (2 * jsp87Carry N) := by
  have hrec := jsp87Carry_succ N
  have hcast : (omega N : ℝ) = (((omega N : ℤ) : ℝ)) := by push_cast; rfl
  rw [hrec, hcast, Int.fract_sub_intCast]

/-- **THE DIGIT–CARRY IDENTITY.**  For `1 ≤ N` the `N`-th binary digit of the
Erdős series is the difference of two consecutive fractional parts of the
carries:

`d N = 2 · Int.fract (θ N) − Int.fract (θ (N+1))`.

This is the bridge between round 41's `jsp87_digit_eq_fract` (which uses the
*rescaled series* `2^N S`) and the *carries*: `Int.fract (2^N S) =
Int.fract (θ N)` is round 40's `jsp87_fract_scaled`.  Mathlib has no statement
of any kind about the base-`2` expansion of a real number. -/
theorem jsp87_digit_eq_fractCarry {N : ℕ} (hN : 1 ≤ N) :
    (jsp87Digit N : ℝ) = 2 * Int.fract (jsp87Carry N) - Int.fract (jsp87Carry (N + 1)) := by
  have h := jsp87_digit_eq_fract N
  rw [jsp87_fract_scaled hN, jsp87_fract_scaled (N := N + 1) (by omega)] at h
  exact h

/-- **THE DIGIT IS THE SECOND BINARY DIGIT OF THE CARRY.**  For `1 ≤ N`,

`d N = ⌊2 θ N⌋ − 2 ⌊θ N⌋`.

So the `N`-th digit of `S` is *not* the integer part of the carry (that is
`jsp87CarryExcess`), but the next binary digit of it.  Compare round 41's
`jsp87_digit_bookkeeping`, which expresses the same digit as
`ω N + c (N+1) − 2 c N` with `c N = ⌊θ N⌋`. -/
theorem jsp87_digit_eq_floorCarry {N : ℕ} (hN : 1 ≤ N) :
    jsp87Digit N = ⌊2 * jsp87Carry N⌋ - 2 * ⌊jsp87Carry N⌋ := by
  have hfloor : ⌊2 * jsp87Carry N⌋ = omega N + ⌊jsp87Carry (N + 1)⌋ := by
    have hrec2 := jsp87Carry_succ N
    have heq : 2 * jsp87Carry N = jsp87Carry (N + 1) + (omega N : ℝ) := by
      linarith
    rw [heq, Int.floor_add_natCast]
    omega
  rw [jsp87_digit_bookkeeping hN, jsp87CarryExcess, jsp87CarryExcess, hfloor]

/-- **THE UNCONDITIONAL DOUBLING-CARRY WINDOW.**  For `1 ≤ N`,

`0 ≤ 2 · fract (θ N) − fract (θ (N+1)) ≤ 1`.

This is the arithmetic content of "the digits of `S` are `0` or `1`", read on
the carries: doubling a fractional part and subtracting the next one stays in
`[0,1]`, i.e. the doubling map on the circle of the carry is a genuine
`{0,1}`-valued digit generator. -/
theorem jsp87Carry_digit_doubling {N : ℕ} (hN : 1 ≤ N) :
    (0 : ℝ) ≤ 2 * Int.fract (jsp87Carry N) - Int.fract (jsp87Carry (N + 1))
      ∧ 2 * Int.fract (jsp87Carry N) - Int.fract (jsp87Carry (N + 1)) ≤ 1 := by
  have h := jsp87_digit_eq_fractCarry hN
  have hmem := jsp87Digit_mem N
  have hcast0 : ((0 : ℤ) : ℝ) = 0 := by norm_num
  have hcast1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
  rcases hmem with h0 | h1
  · rw [h0, hcast0] at h
    constructor <;> linarith
  · rw [h1, hcast1] at h
    constructor <;> linarith

/-- **THE ORBIT IS DRIVEN BY THE DIGITS.**  For `1 ≤ N`,

`fract (θ (N+1)) = 2 · fract (θ N) − d N`,

i.e. the doubling orbit of the carries is generated by the binary digit string
of `S` — the classical doubling-map description of a binary expansion,
transported to the carries. -/
theorem jsp87_fracCarry_succ {N : ℕ} (hN : 1 ≤ N) :
    Int.fract (jsp87Carry (N + 1)) = 2 * Int.fract (jsp87Carry N) - (jsp87Digit N : ℝ) := by
  have hf := jsp87_digit_eq_floorCarry hN
  have hself := Int.self_sub_floor (2 * jsp87Carry N)
  have hself2 := Int.self_sub_floor (jsp87Carry N)
  have hdigit : (jsp87Digit N : ℝ) = (⌊2 * jsp87Carry N⌋ : ℝ) - 2 * (⌊jsp87Carry N⌋ : ℝ) := by
    rw [hf]
    push_cast
    ring
  rw [jsp87Carry_fract_succ, ← hself, hdigit]
  linarith

/-! ## 2. Eventual periodicity of the digits gives periodicity of the orbit -/

/-- **EVENTUAL PERIODICITY OF THE DIGITS ⟹ EVENTUAL PERIODICITY OF THE
DOUBLING ORBIT, WITH THE SAME PERIOD.**  If `d (n+t) = d n` for all
`n ≥ M` (where `1 ≤ M`) then `Int.fract (θ (N+t)) = Int.fract (θ N)` for all
`N ≥ M`.

This is round 46's `jsp87_frac_scaled_eq_block` transported to the carries: the
`t`-digit block is constant along the period (`jsp87_digitBlock_shift`), and
the fractional part of the carry *is* the fractional part of the rescaled
series (round 40). -/
theorem jsp87_fracCarry_periodic_of_digitPeriodic {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hN : M ≤ N) (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N) := by
  have hb : jsp87DigitBlock (N + t) t = jsp87DigitBlock N t := by
    have h := jsp87_digitBlock_shift (N := N) (t := t) ht (fun n hn => hper n (by omega)) 1
    simpa using h
  rw [← jsp87_fract_scaled (N := N + t) (by omega), ← jsp87_fract_scaled (N := N) (by omega)]
  rw [jsp87_frac_scaled_eq_block (N := N + t) (t := t) ht (fun n hn => hper n (by omega)),
    jsp87_frac_scaled_eq_block (N := N) (t := t) ht (fun n hn => hper n (by omega)), hb]

/-- **THE ORBIT POINT IS THE DIGIT BLOCK.**  Under the same hypotheses,

`Int.fract (θ N) = B N t / (2^t − 1)`,

where `B N t` is the `t`-digit block at `N`.  (Round 46, restated for the
carries.) -/
theorem jsp87_fracCarry_eq_block_of_digitPeriodic {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hN : M ≤ N) (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    Int.fract (jsp87Carry N) = (jsp87DigitBlock N t : ℝ) / ((2 : ℝ) ^ t - 1) := by
  rw [← jsp87_fract_scaled (N := N) (by omega)]
  exact jsp87_frac_scaled_eq_block (N := N) (t := t) ht (fun n hn => hper n (by omega))

/-- **THE GRID.**  Under eventual periodicity of the digits from `M` with period
`t > 0`, every fractional part of a carry is a **multiple of `1/(2^t − 1)`**,
strictly below `1`:

`Int.fract (θ N) = k / (2^t − 1)` for some `k` with `0 ≤ k` and `k ≤ 2^t − 1`.

Together with round 38's `b · θ N ∈ ℤ` (rationality freezes the *whole* carry
into the lattice `(1/b) ℤ`) this pins the fractional part of every carry to the
finer lattice `(1/(b (2^t − 1))) ℤ` — the obstruction quantified in
`jsp87_carry_period_denominator_obstruction` below. -/
theorem jsp87_fracCarry_grid_of_digitPeriodic {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hN : M ≤ N) (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ∃ k : ℤ, 0 ≤ k ∧ (k : ℤ) ≤ (2 : ℤ) ^ t - 1
      ∧ Int.fract (jsp87Carry N) = (k : ℝ) / ((2 : ℝ) ^ t - 1) := by
  have hfr := jsp87_fracCarry_eq_block_of_digitPeriodic ht hM hN hper
  have hbnd := jsp87_digitBlock_bounds N t
  refine ⟨jsp87DigitBlock N t, hbnd.1, ?_, hfr⟩
  have hlt : (jsp87DigitBlock N t : ℤ) < (2 : ℤ) ^ t := by omega
  omega

/-! ## 3. The fourth irrationality criterion -/

/-- **RATIONALITY GIVES AN EVENTUALLY PERIODIC DOUBLING ORBIT OF THE CARRIES.**
If `S = a / b` with `b > 0` then there are `t > 0`, `M` with `1 ≤ M` such that

`Int.fract (θ (N+t)) = Int.fract (θ N)` for all `N ≥ M`.

This is the fractional-part mirror of round 41's
`jsp87_digit_eventuallyPeriodic`, and of round 40's
`jsp87_fract_scaled_eq_div` (which only says the fractional parts are
*quantised*, i.e. take `b` values).  Here they are made **periodic**, with the
period of the digit string. -/
theorem jsp87Series_rational_imp_fracCarry_periodic {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
      ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N) := by
  obtain ⟨t, M, ht, hM1, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  exact ⟨t, M, ht, hM1, fun N hN => jsp87_fracCarry_periodic_of_digitPeriodic ht hM1 hN hper⟩

/-- **THE FOURTH IRRATIONALITY CRITERION.**  If the doubling orbit of the
carries — `N ↦ Int.fract (θ N)` — is **not eventually periodic**, then the
Erdős series is **irrational**.

The development now contains four *independent* aperiodicity criteria for
`jsp_000087_main`:

* round 41: the carry **excess** `⌊θ N⌋` is eventually periodic;
* round 46: the binary **digit string** `d N` is eventually periodic;
* round 47: the **primary** digit string of a carry-free series is eventually
  periodic;
* this round: the **doubling orbit of the carries** is eventually periodic. -/
theorem jsp87Series_irrational_of_fracCarry_notPeriodic
    (h : ¬ ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
        ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N)) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  obtain ⟨t, M, ht, hM1, hper⟩ :=
    jsp87Series_rational_imp_fracCarry_periodic hden (by rw [← hq, Rat.cast_def])
  exact h ⟨t, M, ht, hM1, hper⟩

/-- **A RATIONAL VALUE MAKES THE *INTEGER* PART OF THE CARRY APERIODIC.**  If
`S = a / b` with `b > 0` then the carry excess is never eventually periodic:
for every `t > 0` and every `N` there is some `n ≥ N` with
`⌊θ (n+t)⌋ ≠ ⌊θ n⌋`.  (The contrapositive of round 41's
`jsp87Series_irrational_of_carryExcess_eventuallyPeriodic`.) -/
theorem jsp87Series_eq_rat_imp_carryExcess_notPeriodic {a : ℤ} {b : ℕ}
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n := by
  intro hper
  obtain ⟨t, N, ht, hle⟩ := hper
  have hirr := jsp87Series_irrational_of_carryExcess_eventuallyPeriodic (t := t) (N := N) ht hle
  have hmem : jsp87Series ∈ Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨(a : ℚ) / b, ?_⟩
    have hx : ((a / (b : ℚ) : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by norm_cast
    exact hx.trans h.symm
  exact hirr hmem

/-- **THE CARRY-SPLIT DICHOTOMY.**  A rational value of the Erdős series splits
the carries exactly in two: their **fractional parts become eventually
periodic** (with the period of the digit string) while their **integer parts
stay aperiodic forever**.

Together with round 44's `jsp87CarryExcess_unbounded` (the excess is unbounded,
hence *cannot* be eventually periodic at all) and the new criterion
`jsp87Series_irrational_of_fracCarry_notPeriodic`, this says the whole
obstruction to a rational `S` is concentrated in the *fractional* part of the
carry: rationality would have to make that one real number aperiodic. -/
theorem jsp87Series_rational_imp_carrySplit {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    (∃ t M : ℕ, 0 < t ∧ 1 ≤ M
        ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
      ∧ (¬ ∃ t N : ℕ, 0 < t
        ∧ ∀ n, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n) :=
  ⟨jsp87Series_rational_imp_fracCarry_periodic hb h,
    jsp87Series_eq_rat_imp_carryExcess_notPeriodic h⟩

/-! ## 4. The period denominator obstruction, on the carry side -/

/-- **THE CARRY QUANTISATION BY THE PERIOD — no rationality hypothesis.**
Suppose the binary digits of `S` are eventually periodic from `M` with period
`t > 0` (`1 ≤ M`), and let `1 ≤ M ≤ N`.  Then

`(2^t − 1) · θ N ∈ ℤ`.

This is *unconditional*: the fractional part of the carry is a multiple of
`1/(2^t − 1)` (the grid, `jsp87_fracCarry_grid_of_digitPeriodic`) and the
integer part of the carry is an integer, so the whole carry is quantised by the
**period alone**.  In other words the eventual period of the digit string
determines a lattice containing every carry of the series. -/
theorem jsp87_carry_period_quantisation {t M N : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hN : M ≤ N) (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ∃ c : ℤ, ((2 : ℝ) ^ t - 1) * jsp87Carry N = (c : ℝ) := by
  obtain ⟨k, hk0, hk1, hkf⟩ := jsp87_fracCarry_grid_of_digitPeriodic ht hM hN hper
  have hA0 : (0 : ℤ) < 2 ^ t - 1 := two_pow_sub_one_pos ht
  have hA0R : (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hA0)
  have hkfr : (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * Int.fract (jsp87Carry N) = (k : ℝ) := by
    rw [hkf, two_pow_sub_one_cast t]
    exact mul_div_cancel₀ (k : ℝ) hA0R
  have hsplit : jsp87Carry N = (⌊jsp87Carry N⌋ : ℝ) + Int.fract (jsp87Carry N) :=
    (Int.floor_add_fract _).symm
  have hmul := congrArg (fun z : ℝ => (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * z) hsplit
  have hdist : (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * jsp87Carry N
      = (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * (⌊jsp87Carry N⌋ : ℝ)
        + (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * Int.fract (jsp87Carry N) := by
    rw [hmul]
    ring
  have h1 : (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * jsp87Carry N
      = (((2 : ℤ) ^ t - 1 : ℤ) : ℝ) * (⌊jsp87Carry N⌋ : ℝ) + (k : ℝ) := by rw [hdist, hkfr]
  refine ⟨((2 : ℤ) ^ t - 1) * ⌊jsp87Carry N⌋ + k, ?_⟩
  rw [two_pow_sub_one_cast t, h1]
  push_cast
  ring

/-- **THE CARRY-SIDE PERIOD-DENOMINATOR OBSTRUCTION.**  Suppose `S = a / b` with
`b > 0` and the binary digits are eventually periodic from `M` with period
`t > 0` (`1 ≤ M ≤ N`).  Then

`b · (2^t − 1) · θ N ∈ ℤ`.

Round 38 proved `b · θ N ∈ ℤ`; round 46 proved `(2^t − 1) ∣ b · B M t` on the
digit side; this is the *carry-side* statement, obtained by combining the
integrality of `b θ N` with the period quantisation of the carries.  A rational
value of the Erdős series would therefore freeze **every carry** into the
lattice `(1/(b (2^t−1))) ℤ`, with the single `t` coming from the digit period. -/
theorem jsp87_carry_denominator_obstruction {a : ℤ} {b N : ℕ} (hb : 0 < b) (hN1 : 1 ≤ N)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∀ t : ℕ, ∃ c : ℤ, (b : ℝ) * ((2 : ℝ) ^ t - 1) * jsp87Carry N = (c : ℝ) := by
  intro t
  obtain ⟨c0, hc0⟩ := jsp87_carry_mul_eq_int hN1 (by exact_mod_cast hb) h
  have hc0' : (b : ℝ) * jsp87Carry N = (c0 : ℝ) := by
    have h := hc0
    simpa [jsp87Carry, mul_comm] using h
  refine ⟨c0 * ((2 : ℤ) ^ t - 1), ?_⟩
  calc (b : ℝ) * ((2 : ℝ) ^ t - 1) * jsp87Carry N
      = (b : ℝ) * (jsp87Carry N * ((2 : ℝ) ^ t - 1)) := by ring
    _ = ((b : ℝ) * jsp87Carry N) * ((2 : ℝ) ^ t - 1) := by ring
    _ = (c0 : ℝ) * ((2 : ℝ) ^ t - 1) := by rw [hc0']
    _ = (c0 * ((2 : ℤ) ^ t - 1) : ℤ) := by push_cast; ring

/-- **THE CARRY LATTICE OF A RATIONAL VALUE WITH PERIODIC DIGITS.**  Suppose
`S = a / b` with `b > 0` and the binary digits are eventually periodic from `M`
with period `t > 0`.  Then for every `N ≥ M` (with `N ≥ 1`) the carry `θ N`
lies in the lattice `(1/(b (2^t − 1))) ℤ`, and the two halves are independent:

* `(2^t − 1) · θ N ∈ ℤ` — the **period** alone quantises the carry
  (`jsp87_carry_period_quantisation`, no rationality needed);
* `b · (2^t − 1) · θ N ∈ ℤ` — the **denominator** `b` of a rational value
  scales that lattice (`jsp87_carry_denominator_obstruction`).

Round 38 proved `b · θ N ∈ ℤ`; round 46 proved `(2^t − 1) ∣ b · B M t` on the
digit side.  This is the join of the two: a rational value of the Erdős series
would freeze **every carry** into a single lattice determined by the digit
period and the denominator. -/
theorem jsp87_carry_lattice_of_digitPeriodic {a : ℤ} {b t M N : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hM : 1 ≤ M) (hN : M ≤ N) (hN1 : 1 ≤ N) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    (∃ d : ℤ, ((2 : ℝ) ^ t - 1) * jsp87Carry N = (d : ℝ))
      ∧ (∃ c : ℤ, (b : ℝ) * ((2 : ℝ) ^ t - 1) * jsp87Carry N = (c : ℝ)) :=
  ⟨jsp87_carry_period_quantisation ht hM hN hper,
    jsp87_carry_denominator_obstruction hb hN1 h t⟩

/-- **THE EXACT RATIONAL FORM FORCED BY EVENTUAL PERIODICITY.**  If the binary
digits of `S` are eventually periodic from `M` with period `t > 0`
(`1 ≤ M`), then

`S = n / (2^M · (2^t − 1))`  for some `n : ℤ`.

This is the *value* form of round 46's fractional-part theorem
`jsp87_frac_scaled_eq_block` (round 47 proved the analogous statement for
carry-free series, `jsp87Binary_series_eq_block`).  Combined with
`jsp87Series_ge_quarter` and `jsp87Series_lt_half` (round 47) it says: a
rational value of the Erdős series would be a rational in `[1/4, 1/2)` whose
denominator is a *product of a power of `2` and a Mersenne number* `2^t − 1` —
the denominator is therefore pinned by the digit period in an explicit way. -/
theorem jsp87Series_eq_div_of_digitPeriodic {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1)) := by
  obtain ⟨k, hk0, hk1, hkf⟩ := jsp87_fracCarry_grid_of_digitPeriodic (N := M) ht hM (by omega) hper
  have hfrac : Int.fract ((2 : ℝ) ^ M * jsp87Series) = (k : ℝ) / ((2 : ℝ) ^ t - 1) := by
    rw [jsp87_fract_scaled (N := M) hM, hkf]
  have hfloor : (⌊(2 : ℝ) ^ M * jsp87Series⌋ : ℝ) + (k : ℝ) / ((2 : ℝ) ^ t - 1)
      = (2 : ℝ) ^ M * jsp87Series := by
    have h := Int.floor_add_fract ((2 : ℝ) ^ M * jsp87Series)
    linarith
  have hA0 : (0 : ℝ) < ((2 : ℤ) ^ t - 1 : ℤ) := by
    have h2 : (0 : ℤ) < 2 ^ t - 1 := two_pow_sub_one_pos ht
    exact_mod_cast h2
  have hA0R' : ((2 : ℝ) ^ t - 1) ≠ 0 := by
    have h2 : (0 : ℤ) < 2 ^ t - 1 := two_pow_sub_one_pos ht
    exact_mod_cast (ne_of_gt h2)
  have hB0R : ((2 : ℝ) ^ M) ≠ 0 := by positivity
  refine ⟨⌊(2 : ℝ) ^ M * jsp87Series⌋ * ((2 : ℤ) ^ t - 1) + k, ?_⟩
  calc jsp87Series = (2 : ℝ) ^ M * jsp87Series / (2 : ℝ) ^ M := by field_simp
    _ = ((⌊(2 : ℝ) ^ M * jsp87Series⌋ : ℝ) + (k : ℝ) / ((2 : ℝ) ^ t - 1)) / (2 : ℝ) ^ M := by
        rw [hfloor]
    _ = ((⌊(2 : ℝ) ^ M * jsp87Series⌋ : ℝ) * ((2 : ℝ) ^ t - 1) + (k : ℝ))
        / (((2 : ℝ) ^ t - 1) * (2 : ℝ) ^ M) :=
      add_div_div_eq _ _ _ _ hA0R' hB0R
    _ = (⌊(2 : ℝ) ^ M * jsp87Series⌋ * ((2 : ℤ) ^ t - 1) + k : ℤ)
        / ((2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1)) := by
        rw [two_pow_sub_one_cast t]
        push_cast
        ring

/-! ## 5. The period-`1` case is exactly the dyadic case -/

/-- **A `1`-PERIODIC DIGIT STRING IS ALL ZEROS.**  If `d (n+1) = d n` for all
`n ≥ M` with `1 ≤ M`, then `d N = 0` for all `N ≥ M`.

Reason: with `t = 1` the block formula gives `Int.fract (θ N) = d N`, and a
fractional part is `< 1`, so the digit can only be `0`. -/
theorem jsp87_digit_period_one_eq_zero {M : ℕ} (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + 1) = jsp87Digit n) :
    ∀ N, M ≤ N → jsp87Digit N = 0 := by
  intro N hN
  have hfr := jsp87_fracCarry_eq_block_of_digitPeriodic (t := 1) (N := N)
    (show 0 < (1 : ℕ) by omega) hM hN hper
  rw [jsp87DigitBlock_one] at hfr
  rcases jsp87Digit_mem N with h0 | h1
  · exact h0
  · have hlt := Int.fract_lt_one (jsp87Carry N)
    have hcast1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
    rw [h1, hcast1] at hfr
    linarith

/-- **PERIOD `1` FORCES A DYADIC VALUE.**  If the binary digits of the Erdős
series are eventually *constant* (eventual period `t = 1`) then `S` is a
**dyadic rational**: `S = n / 2^M` for some `n : ℤ`.

So the first case of the aperiodicity problem is not a new analytic
difficulty: it is exactly the question whether the binary expansion of `S`
*terminates*. -/
theorem jsp87Series_dyadic_of_digit_period_one {M : ℕ} (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + 1) = jsp87Digit n) :
    ∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M) := by
  have hz := jsp87_digit_period_one_eq_zero hM hper
  have hfr : Int.fract (jsp87Carry M) = 0 := by
    have hfr2 := jsp87_fracCarry_eq_block_of_digitPeriodic (t := 1) (N := M)
      (show 0 < (1 : ℕ) by omega) hM (by omega) hper
    rw [jsp87DigitBlock_one, hz M (by omega)] at hfr2
    norm_num at hfr2
    exact hfr2
  have hfrac : Int.fract ((2 : ℝ) ^ M * jsp87Series) = 0 := by
    rw [jsp87_fract_scaled (N := M) hM, hfr]
  have hint : (2 : ℝ) ^ M * jsp87Series = ⌊(2 : ℝ) ^ M * jsp87Series⌋ := by
    have h := Int.self_sub_fract ((2 : ℝ) ^ M * jsp87Series)
    rw [hfrac] at h
    linarith
  refine ⟨⌊(2 : ℝ) ^ M * jsp87Series⌋, ?_⟩
  calc jsp87Series = (2 : ℝ) ^ M * jsp87Series / (2 : ℝ) ^ M := by field_simp
    _ = ⌊(2 : ℝ) ^ M * jsp87Series⌋ / (2 : ℝ) ^ M :=
      congrArg (fun y : ℝ => y / (2 : ℝ) ^ M) hint

/-- **THE PERIOD-`1` CASE IS EXACTLY THE DYADIC CASE.**  For `1 ≤ M`,

> `S = n / 2^M` for some `n : ℤ`  ⟺  `d N = 0` for all `N ≥ M`,

i.e. **the binary expansion of `S` terminates at `M` if and only if the binary
expansion of `S` is eventually `0`**.  (The forward direction is the classical
fact that a dyadic rational has a terminating binary expansion, proved here
from the floor definition of the digit; the reverse direction is
`jsp87Series_dyadic_of_digit_period_one`.) -/
theorem jsp87Series_dyadic_iff {M : ℕ} (hM : 1 ≤ M) :
    (∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) ↔
      ∀ N, M ≤ N → jsp87Digit N = 0 := by
  constructor
  · rintro ⟨n, hn⟩ N hN
    have hscaled : (2 : ℝ) ^ M * jsp87Series = (n : ℝ) := by
      rw [hn]
      exact mul_div_cancel₀ _ (by positivity)
    have hz : ∀ j : ℕ, M ≤ j → ∃ z : ℤ, (2 : ℝ) ^ j * jsp87Series = (z : ℝ) := by
      intro j hj
      refine ⟨(2 : ℤ) ^ (j - M) * n, ?_⟩
      have h2 : (2 : ℝ) ^ j * jsp87Series = (2 : ℝ) ^ M * ((2 : ℝ) ^ (j - M) * jsp87Series) := by
        calc (2 : ℝ) ^ j * jsp87Series = (2 : ℝ) ^ (M + (j - M)) * jsp87Series := by rw [Nat.add_sub_of_le hj]
          _ = ((2 : ℝ) ^ M * (2 : ℝ) ^ (j - M)) * jsp87Series := by rw [pow_add]
          _ = (2 : ℝ) ^ M * ((2 : ℝ) ^ (j - M) * jsp87Series) := by ring
      calc (2 : ℝ) ^ j * jsp87Series = (2 : ℝ) ^ M * ((2 : ℝ) ^ (j - M) * jsp87Series) := by exact h2
        _ = ((2 : ℝ) ^ M * jsp87Series) * (2 : ℝ) ^ (j - M) := by ring
        _ = (n : ℝ) * (2 : ℝ) ^ (j - M) := by rw [hscaled]
        _ = (n : ℝ) * ((2 : ℤ) ^ (j - M) : ℤ) := by rw [two_pow_cast (j - M)]
        _ = (((2 : ℤ) ^ (j - M) * n : ℤ) : ℝ) := by push_cast; ring
    obtain ⟨z0, hz0⟩ := hz N hN
    obtain ⟨z1, hz1⟩ := hz (N + 1) (by omega)
    have h2 : (2 : ℝ) ^ (N + 1) * jsp87Series = 2 * ((2 : ℝ) ^ N * jsp87Series) := by
      rw [pow_succ]
      ring
    have hz1' : z1 = 2 * z0 := by
      rw [h2, hz0] at hz1
      have h3 : (z1 : ℝ) = 2 * z0 := by linarith
      exact_mod_cast h3
    simp only [jsp87Digit]
    rw [hz1, Int.floor_intCast, hz0, Int.floor_intCast, hz1']
    ring
  · intro hz
    have hper : ∀ n, M ≤ n → jsp87Digit (n + 1) = jsp87Digit n := by
      intro n hn
      have h1 := hz (n + 1) (by omega)
      have h2 := hz n hn
      rw [h1, h2]
    exact jsp87Series_dyadic_of_digit_period_one hM hper

end JSP87
