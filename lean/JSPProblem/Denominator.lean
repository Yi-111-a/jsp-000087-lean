/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.WindowProduct
import JSPProblem.LambertTrunc

/-!
# JSP-000087, round 57 : the denominator side

## The new attack family

Rounds 37–56 attacked the Erdős series `S = ∑ n, ω(n) 2^{-(n+1)}` through
twenty families: the Lambert reduction (37), the carry scaffold (38), the gcd of
the Lambert denominators (39), the carry dynamics (40), the digit bookkeeping
(41), the carry excess and the sieve content (44), the base-`2` block arithmetic
(46), the carry-free primary expansion (47), the doubling map on the carries
(48), the criterion in arbitrary radix (49), the asymptotics of the carry (50),
the period equation (51), the `2`-adic binary prefix (52), runs of `ω` (53), the
sieve local model (55) and the product of a window (56).

**Every one of those rounds worked with the *numerators***: the binary digits,
the blocks, the carries, the windows, the prefixes.  Not one of them ever asked
the *other* question — the classical one, the one Erdős' own 1948 paper asks:

> **what is the denominator of the number?**

Rounds 39, 40 and 46 each produced a *one-sided* divisibility statement about a
hypothetical denominator `b` (`b ∣ 2^p − 1` forces `p < b`;
`b (2^t−1) θ N ∈ ℤ`; `(2^t−1) ∣ b B N t`).  None of them ever turned those
one-sided statements into an *exact criterion*.  This round does, in three
steps.

### 1. The binary expansion of an arbitrary real

`digitAt x N` generalises `jsp87Digit` (round 41) from `jsp87Series` to *any*
real number, and the whole digit apparatus is rebuilt from scratch in that
generality: `digitAt_eq_floor_two_fract` (the digit is the second binary digit of
the fractional part), `digitAt_mem` (the digits are `0` or `1`),
`digitAt_fract_succ'` (the orbit recursion), `digitAt_fract_periodic`
(periodicity of the digits forces periodicity of the doubling orbit — proved here
from the *doubling* of the defect, not from the telescoping identity), and
`digitAt_no_allOnes` (**no real number has an eventually-all-ones binary
expansion**).  Mathlib has no statement about the base-`2` expansion of a real
number at all.

### 2. THE COMPLETE PERIOD–DENOMINATOR CORRESPONDENCE

> `jsp87_digitPeriod_iff_den_dvd` : for `jsp87Series = a/b` **in lowest terms**,
> `1 ≤ M`, `0 < t`,
> `(∀ n ≥ M, d (n+t) = d n)  ↔  b ∣ 2^M (2^t − 1)`.

Round 46 gave the *value* of a periodic expansion (`S = n/(2^M(2^t−1))`); this
is the arithmetic converse, and it is the first time in this development that a
hypothesis about the **binary digits** of `jsp87Series` is *equivalent* to a
hypothesis about the **denominator** of a hypothetical rational value.

### 3. THE COMPLETE PERIOD–ORDER CORRESPONDENCE

With `jsp87OddPart b` the `2`-free part of the denominator (built from round
52's `jsp87Val2`),

> `jsp87_digitPeriod_iff_oddPart_dvd_mer` : for `M ≥ v_2(b)`,
> `(∀ n ≥ M, d (n+t) = d n)  ↔  jsp87OddPart b ∣ 2^t − 1`.

So **the eventual periods of the binary expansion of a rational, past the
`2`-adic threshold, are exactly the exponents for which `2^t ≡ 1` modulo the odd
part of the denominator**: the minimal eventual period *is* the multiplicative
order of `2` mod `oddPart b`.  Consequences proved here: the eventual periods are
**gcd-closed** (`jsp87_period_gcd`, hence a principal ideal, so the minimal
period divides every period, `jsp87_minimalPeriod_dvd`), and closed under `lcm`
and under multiples.

### 4. The run dichotomy, which closes the round-53 route quantitatively

* `digitAt_periodic_oneRun_lt` : **a `t`-periodic digit string never contains `t`
  consecutive ones at or after the periodic point** (a run of `t` ones would
  force the whole tail to be ones, i.e. `f = 1`, impossible).  So the one-runs
  after the periodic point are shorter than the period.
* `digitAt_periodic_zeroRun_dyadic` : a run of `t` zeros at or after the
  periodic point forces the expansion to **terminate** — the value is dyadic.
* `digitAt_oneRun_gap` / `jsp87_oneRun_two_pow_le` : the one-run inequality
  `2^L · (b − c) ≤ b` where `c` is the numerator of the fractional part, hence
  `2^L ≤ b`.  Round 53 recorded `2^L ≤ b` for the series only; the new content
  is that the **period `t` enters the same inequality**, and `t` is the order of
  `2` modulo `oddPart b`.

Read together: a hypothetical rational value of the Erdős series, in lowest
terms with denominator `b`, has a binary expansion which is eventually periodic
with period `t = ord_{oddPart b}(2)`, whose one-runs are shorter than `t`, whose
zero-runs of length `t` would make the value dyadic, and every one-run of length
`L` forces `2^L ≤ b`.  The remaining gap is unchanged in kind — the aperiodicity
of the binary digit string — but the *period* is now pinned arithmetically.
-/

namespace JSP87

/-! ## 0. The binary expansion of an arbitrary real number -/

/-- **A positive real is eventually exceeded by a power of `2`.**  The
elementary Archimedean step behind `digitAt_no_allOnes`. -/
private theorem exists_two_pow_mul_gt_one {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, 1 < (2 : ℝ) ^ k * c := by
  obtain ⟨n, hn⟩ := exists_pow_lt_real (r := ((1 : ℝ) / 2)) (by norm_num) (by norm_num) hc
  refine ⟨n, ?_⟩
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h3 := mul_lt_mul_of_pos_left hn h2
  have h4 : ((1 : ℝ) / 2) ^ n * (2 : ℝ) ^ n = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀ _ (by norm_num)]
  linarith

/-- The `N`-th binary digit of an **arbitrary** real number,
`digitAt x N = ⌊2^{N+1} x⌋ − 2 ⌊2^N x⌋`.  Round 41 introduced `jsp87Digit` for
`jsp87Series` only; every statement below is in this generality. -/
noncomputable def digitAt (x : ℝ) (N : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (N + 1) * x⌋ - 2 * ⌊(2 : ℝ) ^ N * x⌋

/-- **THE DIGIT IS THE SECOND BINARY DIGIT OF THE FRACTIONAL PART.**
`digitAt x N = ⌊2 · fract (2^N x)⌋`: the basic bridge between the *floor*
description (round 41) and the *doubling orbit* description (round 48), in full
generality. -/
theorem digitAt_eq_floor_two_fract (x : ℝ) (N : ℕ) :
    ⌊2 * Int.fract ((2 : ℝ) ^ N * x)⌋ = digitAt x N := by
  have hstep : ((2 : ℝ) ^ (N + 1) * x : ℝ)
      = ((2 * ⌊(2 : ℝ) ^ N * x⌋ : ℤ) : ℝ) + (2 * Int.fract ((2 : ℝ) ^ N * x) : ℝ) := by
    calc (2 : ℝ) ^ (N + 1) * x = 2 * ((2 : ℝ) ^ N * x) := by rw [pow_succ]; ring
      _ = 2 * (((⌊(2 : ℝ) ^ N * x⌋ : ℤ) : ℝ) + Int.fract ((2 : ℝ) ^ N * x)) := by
          rw [Int.floor_add_fract]
      _ = ((2 * ⌊(2 : ℝ) ^ N * x⌋ : ℤ) : ℝ) + (2 * Int.fract ((2 : ℝ) ^ N * x) : ℝ) := by
          push_cast; ring
  simp only [digitAt, hstep, Int.floor_intCast_add]
  ring

/-- **THE BINARY DIGITS OF A REAL ARE `0` OR `1`** — for *every* real number
(round 41 proved it for `jsp87Series` only). -/
theorem digitAt_mem (x : ℝ) (N : ℕ) : digitAt x N = 0 ∨ digitAt x N = 1 := by
  have hf0 : 0 ≤ Int.fract ((2 : ℝ) ^ N * x) := Int.fract_nonneg _
  have hf1 : Int.fract ((2 : ℝ) ^ N * x) < 1 := Int.fract_lt_one _
  have h0 : (0 : ℤ) ≤ ⌊2 * Int.fract ((2 : ℝ) ^ N * x)⌋ :=
    Int.floor_nonneg.mpr (by linarith)
  have h2 := Int.self_sub_floor (2 * Int.fract ((2 : ℝ) ^ N * x))
  have hfn := Int.fract_nonneg (2 * Int.fract ((2 : ℝ) ^ N * x))
  have h1 : ⌊2 * Int.fract ((2 : ℝ) ^ N * x)⌋ < 2 := by
    have hfl : (⌊2 * Int.fract ((2 : ℝ) ^ N * x)⌋ : ℝ) ≤ 2 * Int.fract ((2 : ℝ) ^ N * x) := by
      linarith
    have hlt : (⌊2 * Int.fract ((2 : ℝ) ^ N * x)⌋ : ℝ) < 2 := lt_of_le_of_lt hfl (by linarith)
    exact_mod_cast hlt
  have key := (digitAt_eq_floor_two_fract x N).symm
  rw [key]
  by_cases hz : (⌊2 * Int.fract ((2 : ℝ) ^ N * x)⌋ : ℤ) = 0
  · exact Or.inl hz
  · exact Or.inr (by omega)

/-- **THE DOUBLING MAP ON THE FRACTAL PARTS** (general real, general index). -/
theorem digitAt_fract_succ (x : ℝ) (N : ℕ) :
    Int.fract ((2 : ℝ) ^ (N + 1) * x) = Int.fract (2 * Int.fract ((2 : ℝ) ^ N * x)) := by
  have hpow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  rw [hpow]
  convert Int.fract_two_mul (x := (2 : ℝ) ^ N * x) using 1 <;> ring

/-- **THE ORBIT RECURSION.**  `fract (2^{N+1} x) = 2 · fract (2^N x) −
digitAt x N`: the fractional part at `N+1` is generated from the one at `N` by
*subtracting the digit*.  This is the engine of the whole round. -/
theorem digitAt_fract_succ' (x : ℝ) (N : ℕ) :
    Int.fract ((2 : ℝ) ^ (N + 1) * x)
      = 2 * Int.fract ((2 : ℝ) ^ N * x) - digitAt x N := by
  have h1 := digitAt_fract_succ x N
  have h2 : Int.fract (2 * Int.fract ((2 : ℝ) ^ N * x))
      = 2 * Int.fract ((2 : ℝ) ^ N * x) - digitAt x N := by
    rw [← digitAt_eq_floor_two_fract x N]
    linarith [Int.self_sub_fract (2 * Int.fract ((2 : ℝ) ^ N * x))]
  linarith

/-- **A DIGIT IS DETERMINED BY THE FRACTIONAL PART.** -/
theorem digitAt_eq_of_fract_eq {x : ℝ} {M N : ℕ}
    (h : Int.fract ((2 : ℝ) ^ M * x) = Int.fract ((2 : ℝ) ^ N * x)) :
    digitAt x M = digitAt x N := by
  have hM := (digitAt_eq_floor_two_fract x M).symm
  have hN := (digitAt_eq_floor_two_fract x N).symm
  rw [hM, hN, h]

/-- **AN INTEGER DIFFERENCE OF TWO RESCALINGS GIVES EQUAL FRACTIONAL PARTS.** -/
theorem fract_eq_of_intCast_sub {x : ℝ} {N t : ℕ} {k : ℤ}
    (h : (2 : ℝ) ^ (N + t) * x - (2 : ℝ) ^ N * x = (k : ℝ)) :
    Int.fract ((2 : ℝ) ^ (N + t) * x) = Int.fract ((2 : ℝ) ^ N * x) := by
  have hx : (2 : ℝ) ^ (N + t) * x = (2 : ℝ) ^ N * x + (k : ℝ) := by linarith
  rw [hx, Int.fract_add_intCast]

/-- **PERIODICITY OF THE ORBIT IMPLIES PERIODICITY OF THE DIGITS.** -/
theorem digitAt_periodic_of_fractPeriod {x : ℝ} {t M : ℕ}
    (hper : ∀ n, M ≤ n →
      Int.fract ((2 : ℝ) ^ (n + t) * x) = Int.fract ((2 : ℝ) ^ n * x)) :
    ∀ n, M ≤ n → digitAt x (n + t) = digitAt x n :=
  fun n hn => digitAt_eq_of_fract_eq (hper n hn)

/-- **PERIODICITY OF THE DIGITS FORCES PERIODICITY OF THE DOUBLING ORBIT.**
The proof does not use the telescoping identity of round 46: if the digits are
`t`-periodic from `M`, then the *defect* `δ n = fract (2^{n+t} x) − fract (2^n x)`
satisfies `δ (n+1) = 2 δ n`; since all fractional parts lie in `[0,1)` the
defect is bounded, and a doubling sequence that is bounded must vanish. -/
theorem digitAt_fract_periodic {x : ℝ} {t M : ℕ} (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → digitAt x (n + t) = digitAt x n) :
    ∀ n, M ≤ n → Int.fract ((2 : ℝ) ^ (n + t) * x) = Int.fract ((2 : ℝ) ^ n * x) := by
  have key : ∀ j, ∀ n, M ≤ n →
      Int.fract ((2 : ℝ) ^ (n + t + j) * x) - Int.fract ((2 : ℝ) ^ (n + j) * x)
        = (2 : ℝ) ^ j * (Int.fract ((2 : ℝ) ^ (n + t) * x) - Int.fract ((2 : ℝ) ^ n * x)) := by
    intro j
    induction j with
    | zero => intro n _; simp
    | succ j ih =>
      intro n hn
      have h1 := digitAt_fract_succ' x (n + t + j)
      have h2 := digitAt_fract_succ' x (n + j)
      have hd' : digitAt x (n + t + j) = digitAt x (n + j) := by
        rw [show n + t + j = n + j + t by omega]
        exact hper (n + j) (by omega)
      have hprev := ih n hn
      have he1 : n + t + (j + 1) = (n + t + j) + 1 := by omega
      have he2 : n + (j + 1) = (n + j) + 1 := by omega
      rw [he1, h1, he2, h2, hd']
      calc (2 * Int.fract ((2 : ℝ) ^ (n + t + j) * x) - (digitAt x (n + j) : ℤ))
          - (2 * Int.fract ((2 : ℝ) ^ (n + j) * x) - (digitAt x (n + j) : ℤ))
          = 2 * (Int.fract ((2 : ℝ) ^ (n + t + j) * x) - Int.fract ((2 : ℝ) ^ (n + j) * x)) := by
            ring
        _ = 2 * ((2 : ℝ) ^ j
            * (Int.fract ((2 : ℝ) ^ (n + t) * x) - Int.fract ((2 : ℝ) ^ n * x))) := by rw [hprev]
        _ = (2 : ℝ) ^ (j + 1)
            * (Int.fract ((2 : ℝ) ^ (n + t) * x) - Int.fract ((2 : ℝ) ^ n * x)) := by
            rw [pow_succ]; ring
  intro n hn
  have hbnd : ∀ j, -1 < Int.fract ((2 : ℝ) ^ (n + t + j) * x)
        - Int.fract ((2 : ℝ) ^ (n + j) * x)
      ∧ Int.fract ((2 : ℝ) ^ (n + t + j) * x)
        - Int.fract ((2 : ℝ) ^ (n + j) * x) < 1 := by
    intro j
    have h0 := Int.fract_nonneg ((2 : ℝ) ^ (n + t + j) * x)
    have h1 := Int.fract_lt_one ((2 : ℝ) ^ (n + t + j) * x)
    have h2 := Int.fract_nonneg ((2 : ℝ) ^ (n + j) * x)
    have h3 := Int.fract_lt_one ((2 : ℝ) ^ (n + j) * x)
    constructor <;> linarith
  have hzero : Int.fract ((2 : ℝ) ^ (n + t) * x) - Int.fract ((2 : ℝ) ^ n * x) = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · obtain ⟨k, hk⟩ := exists_two_pow_mul_gt_one
        (c := -(Int.fract ((2 : ℝ) ^ (n + t) * x) - Int.fract ((2 : ℝ) ^ n * x)))
        (by linarith)
      obtain ⟨hlo, hhi⟩ := hbnd k
      rw [key k n hn] at hlo hhi
      linarith
    · obtain ⟨k, hk⟩ := exists_two_pow_mul_gt_one
        (c := (Int.fract ((2 : ℝ) ^ (n + t) * x) - Int.fract ((2 : ℝ) ^ n * x)))
        (by linarith)
      obtain ⟨hlo, hhi⟩ := hbnd k
      rw [key k n hn] at hlo hhi
      linarith
  linarith

/-- `digitAt jsp87Series = jsp87Digit`: the general digit of round 57 restricted
to the Erdős series is the digit of round 41. -/
theorem jsp87Digit_eq_digitAt (N : ℕ) : jsp87Digit N = digitAt jsp87Series N := rfl

private theorem pow_two_dvd_pow_two {a b : ℕ} (h : a ≤ b) : 2 ^ a ∣ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, Nat.mul_comm]
  exact Nat.dvd_mul_left _ _

/-- **NO REAL NUMBER HAS AN EVENTUALLY-ALL-ONES BINARY EXPANSION.**  If the
digits of `x` are all `1` from `N` on, then `fract (2^{N+j} x) = 1 − 2^j (1 −
fract (2^N x))`, which is `< 0` for large `j`, contradicting `fract ≥ 0`. -/
theorem digitAt_no_allOnes (x : ℝ) (N : ℕ) : ∃ j, digitAt x (N + j) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hfr : ∀ j, Int.fract ((2 : ℝ) ^ (N + j) * x)
      = 1 - (2 : ℝ) ^ j * (1 - Int.fract ((2 : ℝ) ^ N * x)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep := digitAt_fract_succ' x (N + j)
      have heq : N + (j + 1) = (N + j) + 1 := by omega
      rw [heq, hstep, hcon j, ih, pow_succ]
      ring
  have hnn := Int.fract_nonneg ((2 : ℝ) ^ N * x)
  have hlt := Int.fract_lt_one ((2 : ℝ) ^ N * x)
  obtain ⟨k, hk⟩ := exists_two_pow_mul_gt_one
    (c := (1 - Int.fract ((2 : ℝ) ^ N * x))) (by linarith)
  have hfr' := hfr k
  have hnn' := Int.fract_nonneg ((2 : ℝ) ^ (N + k) * x)
  linarith

/-- **A RUN OF `t` EQUAL DIGITS IS THE WHOLE TAIL.**  If the digits of `x` are
all equal to `v` on `N .. N+t−1` then they are `v` at every index `≥ N`. -/
private theorem digitAt_const_of_run {x : ℝ} {t M N : ℕ} (ht : 0 < t) (v : ℤ)
    (hrun : ∀ j, j < t → digitAt x (N + j) = v) (hM : 1 ≤ M) (hNM : M ≤ N)
    (hper : ∀ n, M ≤ n → digitAt x (n + t) = digitAt x n) :
    ∀ n, N ≤ n → digitAt x n = v := by
  intro n hn
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hn
  have htn : t ≠ 0 := Nat.ne_of_gt ht
  have hq' : q = q % t + (q / t) * t := by
    have h := (Nat.div_add_mod q t).symm
    rwa [Nat.mul_comm, Nat.add_comm] at h
  have hr : q % t < t := Nat.mod_lt _ (Nat.pos_of_ne_zero htn)
  have hqr : q % t ≤ q := by
    have h := Nat.div_add_mod q t
    omega
  have hmul : ∀ k, ∀ m, M ≤ m → digitAt x (m + k * t) = digitAt x m :=
    fun k m hm => eventuallyPeriodic_mul ht hper k m hm
  have hkey : digitAt x n = digitAt x (N + q % t) := by
    have heq : n = (N + q % t) + (q / t) * t := by
      calc n = N + q := hq
        _ = N + (q % t + (q / t) * t) := by rw [← hq']
        _ = (N + q % t) + (q / t) * t := by ring
    rw [heq]
    have h2 : M ≤ N + q % t := by omega
    exact hmul (q / t) (N + q % t) h2
  rw [hkey]
  exact hrun (q % t) hr

/-! ## 1. Divisibility forces periodicity, and periodicity forces divisibility -/

private theorem rescale_sub_eq_intCast {a b k M c t : ℕ} (hb : 0 < b)
    (hk : 2 ^ M * (2 ^ t - 1) = b * k) :
    (2 : ℝ) ^ (M + c) * ((2 : ℝ) ^ t - 1) * ((a : ℝ) / (b : ℝ)) = (2 : ℝ) ^ c * (k : ℝ) * (a : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hkR : (2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1) = (b : ℝ) * (k : ℝ) := by
    have h : ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) = (b : ℝ) * (k : ℝ) := by exact_mod_cast hk
    convert h using 1
    norm_num
  calc (2 : ℝ) ^ (M + c) * ((2 : ℝ) ^ t - 1) * ((a : ℝ) / (b : ℝ))
      = (2 : ℝ) ^ c * ((2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1)) * ((a : ℝ) / (b : ℝ)) := by
        rw [pow_add]; ring
    _ = (2 : ℝ) ^ c * ((b : ℝ) * (k : ℝ)) * ((a : ℝ) / (b : ℝ)) := by rw [hkR]
    _ = (2 : ℝ) ^ c * (k : ℝ) * (a : ℝ) := by field_simp

/-- **DIVISIBILITY FORCES PERIODICITY (for an arbitrary rational).**  If
`b ∣ 2^M (2^t − 1)` with `0 < t` then the binary digits of `a/b` are
`M`-periodic with period `t`.  This is the *arithmetic* half of the classical
characterisation of eventually periodic binary expansions. -/
theorem digitAt_periodic_of_den_dvd {a b t M : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hd : b ∣ 2 ^ M * (2 ^ t - 1)) :
    ∀ n, M ≤ n → digitAt ((a : ℝ) / (b : ℝ)) (n + t) = digitAt ((a : ℝ) / (b : ℝ)) n := by
  obtain ⟨k, hk⟩ := hd
  have hfr : ∀ n, M ≤ n →
      Int.fract ((2 : ℝ) ^ (n + t) * ((a : ℝ) / (b : ℝ)))
        = Int.fract ((2 : ℝ) ^ n * ((a : ℝ) / (b : ℝ))) := by
    intro n hn
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hn
    refine fract_eq_of_intCast_sub (k := ((2 : ℤ) ^ c * k * a : ℤ)) ?_
    have hsplit : (2 : ℝ) ^ (n + t) * ((a : ℝ) / (b : ℝ))
          - (2 : ℝ) ^ n * ((a : ℝ) / (b : ℝ))
        = (2 : ℝ) ^ n * ((2 : ℝ) ^ t - 1) * ((a : ℝ) / (b : ℝ)) := by
      rw [pow_add]; ring
    rw [hsplit, hc]
    calc (2 : ℝ) ^ (M + c) * ((2 : ℝ) ^ t - 1) * ((a : ℝ) / (b : ℝ))
        = (2 : ℝ) ^ c * (k : ℝ) * (a : ℝ) :=
          rescale_sub_eq_intCast (a := a) (b := b) (k := k) (M := M) (c := c) (t := t) hb hk
      _ = _ := by norm_cast
  exact digitAt_periodic_of_fractPeriod hfr

/-- The `M = 0` case: `b ∣ 2^t − 1` makes the binary expansion of `a/b`
*purely* periodic, from the very first digit. -/
theorem digitAt_periodic_of_den_dvd_odd {a b t : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hd : b ∣ 2 ^ t - 1) :
    ∀ n : ℕ, digitAt ((a : ℝ) / (b : ℝ)) (n + t) = digitAt ((a : ℝ) / (b : ℝ)) n := by
  intro n
  have h1 : b ∣ 2 ^ 0 * (2 ^ t - 1) := by simpa using hd
  exact digitAt_periodic_of_den_dvd hb ht h1 n (Nat.zero_le n)

/-- **THE SUFFICIENCY DIRECTION FOR THE ERDŐS SERIES.** -/
theorem jsp87_digitPeriod_of_den_dvd {a b t M : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) (hd : b ∣ 2 ^ M * (2 ^ t - 1)) :
    ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n := by
  intro n hn
  rw [jsp87Digit_eq_digitAt (n + t), jsp87Digit_eq_digitAt n, hS]
  exact digitAt_periodic_of_den_dvd hb ht hd n hn

/-- **PERIODICITY FORCES THE DENOMINATOR INTO A MERSEENNE NUMBER.**  If
`jsp87Series = a/b` in lowest terms and the binary digits are `M`-periodic with
period `t > 0` (`1 ≤ M`), then `b ∣ 2^M (2^t − 1)`.  The input is round 48's
`jsp87Series_eq_div_of_digitPeriodic`; the output is its arithmetic content. -/
theorem jsp87_den_dvd_mer_of_period {a b t M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    b ∣ 2 ^ M * (2 ^ t - 1) := by
  obtain ⟨n₀, hn₀⟩ := jsp87Series_eq_div_of_digitPeriodic ht hM hper
  have h1 : 0 < (2 : ℝ) ^ M := by positivity
  have h2 : 0 < (2 : ℝ) ^ t - 1 := two_pow_sub_one_pos (by omega)
  have hD : 0 < (2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1) := by positivity
  have hbnz : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hdiv : (a : ℝ) * ((2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1)) = (n₀ : ℝ) * (b : ℝ) := by
    have h1 := hS.symm.trans hn₀
    field_simp at h1
    linarith [h1]
  have hn0 : 0 ≤ n₀ := by
    have hnn : (0 : ℝ) ≤ (b : ℝ) * (n₀ : ℝ) := by
      rw [mul_comm, ← hdiv]
      positivity
    have hnn' := (mul_nonneg_iff_of_pos_left (show (0 : ℝ) < b by exact_mod_cast hb)).mp hnn
    exact_mod_cast hnn'
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = n₀ := ⟨n₀.toNat, by exact_mod_cast (by omega)⟩
  have hmR : (m : ℝ) = (n₀ : ℝ) := by exact_mod_cast hm
  have hcastR : (2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1) = ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) := by
    push_cast
    norm_num
  have heq : a * (2 ^ M * (2 ^ t - 1)) = m * b := by
    have hh := hdiv
    rw [← hmR] at hh
    rw [hcastR] at hh
    rw [← Nat.cast_mul, ← Nat.cast_mul] at hh
    exact Nat.cast_injective hh
  have hdvd : b ∣ a * (2 ^ M * (2 ^ t - 1)) := ⟨m, heq.trans (Nat.mul_comm _ _)⟩
  exact (Nat.Coprime.dvd_mul_left ha.symm).mp hdvd

/-- **THE COMPLETE PERIOD–DENOMINATOR CORRESPONDENCE.**  For
`jsp87Series = a/b` **in lowest terms**, `1 ≤ M` and `0 < t`:

`(∀ n ≥ M, d (n+t) = d n)  ↔  b ∣ 2^M (2^t − 1)`.

Both directions: the binary digits of the Erdős series are `M`-periodic with
period `t` exactly when the denominator of a hypothetical rational value divides
the Mersenne number `2^t − 1` times the power `2^M`. -/
theorem jsp87_digitPeriod_iff_den_dvd {a b t M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    (∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) ↔ b ∣ 2 ^ M * (2 ^ t - 1) := by
  constructor
  · intro hper
    exact jsp87_den_dvd_mer_of_period ha hb ht hM hS hper
  · intro hd
    exact jsp87_digitPeriod_of_den_dvd hb ht hS hd

/-! ## 2. The `2`-free part of the denominator, and the order of `2` -/

theorem jsp87Val2_le {b : ℕ} (hb : 0 < b) : jsp87Val2 b ≤ b := by
  have hne : b ≠ 0 := ne_of_gt hb
  have hspec := (jsp87Val2_spec hne).mp rfl
  have hle : 2 ^ jsp87Val2 b ≤ b := Nat.le_of_dvd hb hspec.1
  have h2 : jsp87Val2 b ≤ 2 ^ jsp87Val2 b := by
    by_cases hk : jsp87Val2 b = 0
    · omega
    · have hsucc := succ_le_two_pow (jsp87Val2 b - 1)
      have h3 : 2 ^ (jsp87Val2 b - 1) ∣ 2 ^ jsp87Val2 b := by
        apply pow_two_dvd_pow_two
        omega
      have h4 : 2 ^ (jsp87Val2 b - 1) ≤ 2 ^ jsp87Val2 b := Nat.le_of_dvd (by positivity) h3
      omega
  exact le_trans h2 hle

/-- **THE `2`-FREE PART OF THE DENOMINATOR**, `b / 2^{v_2(b)}`.  Built from
round 52's `jsp87Val2`, so the only new object is the odd part. -/
noncomputable def jsp87OddPart (b : ℕ) : ℕ := b / 2 ^ jsp87Val2 b

/-- **THE DECOMPOSITION `b = 2^{v_2(b)} · jsp87OddPart b`.** -/
theorem jsp87_pow_mul_oddPart (b : ℕ) : 2 ^ jsp87Val2 b * jsp87OddPart b = b := by
  rw [jsp87OddPart]
  by_cases hb0 : b = 0
  · rw [hb0, jsp87Val2_zero]; simp
  · calc 2 ^ jsp87Val2 b * (b / 2 ^ jsp87Val2 b) = b / 2 ^ jsp87Val2 b * 2 ^ jsp87Val2 b :=
        Nat.mul_comm _ _
      _ = b := Nat.div_mul_cancel (jsp87Val2_dvd hb0)

/-- The `2`-free part divides `b`. -/
theorem jsp87OddPart_dvd (b : ℕ) : jsp87OddPart b ∣ b := by
  refine ⟨2 ^ jsp87Val2 b, ?_⟩
  have h := jsp87_pow_mul_oddPart b
  rw [Nat.mul_comm] at h
  exact h.symm

/-- The `2`-free part of a positive `b` is positive. -/
theorem jsp87OddPart_pos {b : ℕ} (hb : 0 < b) : 0 < jsp87OddPart b :=
  Nat.pos_of_dvd_of_pos (m := jsp87OddPart b) (n := b) (jsp87OddPart_dvd b) hb

/-- **THE `2`-FREE PART IS NOT DIVISIBLE BY `2`.** -/
theorem not_two_dvd_oddPart {b : ℕ} (hne : b ≠ 0) : ¬ 2 ∣ jsp87OddPart b := by
  intro h2
  obtain ⟨c, hc⟩ := h2
  have hkey : 2 ^ (jsp87Val2 b + 1) * c = b := by
    have h := jsp87_pow_mul_oddPart b
    rw [hc] at h
    have e : 2 ^ (jsp87Val2 b + 1) = 2 ^ jsp87Val2 b * 2 := by rw [pow_succ]
    calc 2 ^ (jsp87Val2 b + 1) * c = (2 ^ jsp87Val2 b * 2) * c := by rw [e]
      _ = 2 ^ jsp87Val2 b * (2 * c) := by ring
      _ = b := h
  exact jsp87Val2_not_succ hne ⟨c, hkey.symm⟩

/-- **THE `2`-FREE PART IS ODD**, i.e. coprime to `2`. -/
theorem jsp87_coprime_two_oddPart {b : ℕ} (hb : 0 < b) : Nat.Coprime 2 (jsp87OddPart b) := by
  have hne : b ≠ 0 := ne_of_gt hb
  have hpos : 0 < Nat.gcd 2 (jsp87OddPart b) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left 2 _) (by omega)
  have h1 : Nat.gcd 2 (jsp87OddPart b) ∣ 2 := Nat.gcd_dvd_left 2 _
  have h3 : Nat.gcd 2 (jsp87OddPart b) = 1 ∨ Nat.gcd 2 (jsp87OddPart b) = 2 := by
    have hle : Nat.gcd 2 (jsp87OddPart b) ≤ 2 := by
      refine Nat.le_of_dvd (show (0 : ℕ) < 2 by omega) h1
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl (by omega)
    · rw [heq]; exact Or.inr rfl
  rcases h3 with h | h
  · rw [Nat.Coprime, h]
  · exfalso
    have h4 : 2 ∣ jsp87OddPart b := by
      have hh := Nat.gcd_dvd_right 2 (jsp87OddPart b)
      rw [h] at hh
      simpa using hh
    exact not_two_dvd_oddPart hne h4

/-- **THE `2`-FREE PART DIVIDES NO LARGER POWER OF `2` THAN `b` ITSELF.** -/
theorem pow_two_dvd_of_dvd_oddPart {b k : ℕ} (hk : jsp87Val2 b ≤ k) (hb : 0 < b)
    (h2 : 2 ^ k ∣ jsp87OddPart b) : 2 ^ k ∣ b := by
  obtain ⟨c, hc⟩ := h2
  have hkey : 2 ^ k * c * 2 ^ jsp87Val2 b = b := by
    have h := jsp87_pow_mul_oddPart b
    rw [hc] at h
    calc 2 ^ k * c * 2 ^ jsp87Val2 b = 2 ^ jsp87Val2 b * (2 ^ k * c) := by ring
      _ = b := h
  rw [← hkey]
  have hr : 2 ^ k * c * 2 ^ jsp87Val2 b = 2 ^ k * (c * 2 ^ jsp87Val2 b) := by ring
  rw [hr]
  exact dvd_mul_of_dvd_left (Nat.dvd_refl (2 ^ k)) (c * 2 ^ jsp87Val2 b)

/-- **A HYPOTHETICAL PERIOD FORCES THE `2`-FREE PART OF THE DENOMINATOR INTO
`2^t − 1`.** -/
theorem jsp87_oddPart_dvd_mer_of_period {a b t M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    jsp87OddPart b ∣ 2 ^ t - 1 := by
  have hd := jsp87_den_dvd_mer_of_period ha hb ht hM hS hper
  have h1 : jsp87OddPart b ∣ 2 ^ M * (2 ^ t - 1) := (jsp87OddPart_dvd b).trans hd
  have hc : Nat.Coprime (jsp87OddPart b) (2 ^ M) :=
    (Nat.coprime_pow_right_iff (a := jsp87OddPart b) (b := (2 : ℕ)) (by omega)).mpr
      (jsp87_coprime_two_oddPart hb).symm
  exact (hc.dvd_mul_left).mp h1

/-- **THE CONVERSE: `oddPart b ∣ 2^t − 1` MAKES `t` A PERIOD.** -/
theorem jsp87_den_dvd_mer_of_oddPart {b t M : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hval : jsp87Val2 b ≤ M) (hd : jsp87OddPart b ∣ 2 ^ t - 1) :
    b ∣ 2 ^ M * (2 ^ t - 1) := by
  obtain ⟨c, hc⟩ := hd
  have hv : 2 ^ jsp87Val2 b ∣ 2 ^ M := pow_two_dvd_pow_two hval
  obtain ⟨e, he⟩ := hv
  have hkey : 2 ^ M * (2 ^ t - 1) = b * (e * c) := by
    calc 2 ^ M * (2 ^ t - 1) = 2 ^ M * (jsp87OddPart b * c) := by rw [hc]
      _ = 2 ^ M * jsp87OddPart b * c := by ring
      _ = (2 ^ jsp87Val2 b * e) * jsp87OddPart b * c := by rw [he]
      _ = (2 ^ jsp87Val2 b * jsp87OddPart b) * (e * c) := by ring
      _ = b * (e * c) := by rw [jsp87_pow_mul_oddPart b]
  rw [hkey]
  exact dvd_mul_right _ _

/-- **THE COMPLETE PERIOD–ORDER CORRESPONDENCE — THE HEADLINE OF THE ROUND.**
For `jsp87Series = a/b` in lowest terms, `1 ≤ M` with `v_2(b) ≤ M`, and
`0 < t`:

`(∀ n ≥ M, d (n+t) = d n)  ↔  jsp87OddPart b ∣ 2^t − 1`.

In words: **the eventual periods of the binary expansion of a rational, past the
`2`-adic threshold, are exactly the exponents `t` for which `2^t ≡ 1` modulo
the odd part of the denominator.**  Equivalently, the minimal eventual period is
the multiplicative order of `2` modulo `jsp87OddPart b`.  Mathlib contains no
statement about the base-`2` expansion of a real number, hence no statement of
this kind. -/
theorem jsp87_digitPeriod_iff_oddPart_dvd_mer {a b t M : ℕ} (ha : Nat.Coprime a b)
    (hb : 0 < b) (ht : 0 < t) (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    (∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) ↔ jsp87OddPart b ∣ 2 ^ t - 1 := by
  constructor
  · intro hper
    exact jsp87_oddPart_dvd_mer_of_period ha hb ht hM hS hper
  · intro hd
    have hd' := jsp87_den_dvd_mer_of_oddPart hb ht hval hd
    exact jsp87_digitPeriod_of_den_dvd hb ht hS hd'

/-- **TWO PERIODS HAVE A COMMON PERIOD: their `lcm`.** -/
theorem jsp87_period_lcm {a b t t' M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (ht' : 0 < t') (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hper' : ∀ n, M ≤ n → jsp87Digit (n + t') = jsp87Digit n) :
    ∀ n, M ≤ n → jsp87Digit (n + Nat.lcm t t') = jsp87Digit n := by
  have h1 := jsp87_oddPart_dvd_mer_of_period ha hb ht hM hS hper
  have h2 := dvd_pow_sub_one_of_dvd (Nat.dvd_lcm_left t t')
  have h3 : jsp87OddPart b ∣ 2 ^ Nat.lcm t t' - 1 := h1.trans h2
  have hlcm : 0 < Nat.lcm t t' := Nat.lcm_pos ht ht'
  have hd := jsp87_den_dvd_mer_of_oddPart hb hlcm hval h3
  exact jsp87_digitPeriod_of_den_dvd hb hlcm hS hd

/-- **THE EVENTUAL PERIODS ARE GCD-CLOSED** (from round 39's exact
`gcd_two_pow_sub_one`).  Together with the existence of a period this makes the
set of eventual periods a principal ideal of `ℕ`. -/
theorem jsp87_period_gcd {a b t t' M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (ht' : 0 < t') (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hper' : ∀ n, M ≤ n → jsp87Digit (n + t') = jsp87Digit n) :
    ∀ n, M ≤ n → jsp87Digit (n + Nat.gcd t t') = jsp87Digit n := by
  have h1 := jsp87_oddPart_dvd_mer_of_period ha hb ht hM hS hper
  have h2 := jsp87_oddPart_dvd_mer_of_period ha hb ht' hM hS hper'
  have h3 : jsp87OddPart b ∣ Nat.gcd (2 ^ t - 1) (2 ^ t' - 1) := Nat.dvd_gcd h1 h2
  rw [gcd_two_pow_sub_one] at h3
  have hg : 0 < Nat.gcd t t' := Nat.gcd_pos_of_pos_left t' ht
  have hd := jsp87_den_dvd_mer_of_oddPart hb hg hval h3
  exact jsp87_digitPeriod_of_den_dvd hb hg hS hd

/-- **THE MINIMAL EVENTUAL PERIOD DIVIDES EVERY EVENTUAL PERIOD.**  Hence the
eventual periods form `t₀ ℕ` for a single `t₀`, the order of `2` modulo the odd
part of the denominator. -/
theorem jsp87_minimalPeriod_dvd {a b t t₀ M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (ht₀ : 0 < t₀) (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hmin : ∀ t' : ℕ, 0 < t' → (∀ n, M ≤ n → jsp87Digit (n + t') = jsp87Digit n) → t₀ ≤ t')
    (hper₀ : ∀ n, M ≤ n → jsp87Digit (n + t₀) = jsp87Digit n)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) : t₀ ∣ t := by
  have hg := jsp87_period_gcd (ha := ha) (hb := hb) (ht := ht₀) (ht' := ht) (hM := hM)
    (hval := hval) (hS := hS) hper₀ hper
  have hgpos : 0 < Nat.gcd t₀ t := Nat.gcd_pos_of_pos_left (m := t₀) (n := t) ht₀
  have hperG : ∀ n, M ≤ n → jsp87Digit (n + Nat.gcd t₀ t) = jsp87Digit n :=
    fun n hn => hg n hn
  have hgt : t₀ ≤ Nat.gcd t₀ t := hmin (Nat.gcd t₀ t) hgpos hperG
  have hgl : Nat.gcd t₀ t ≤ t₀ := by
    refine Nat.le_of_dvd (show (0 : ℕ) < t₀ by omega) (Nat.gcd_dvd_left _ _)
  have heq : Nat.gcd t₀ t = t₀ := by omega
  exact (Nat.gcd_eq_left_iff_dvd).mp heq

/-- **EVERY ODD PRIME DIVISOR OF THE DENOMINATOR DIVIDES THE MERSEENNE NUMBER OF
EVERY EVENTUAL PERIOD.** -/
theorem jsp87_prime_den_dvd_mer {a b t M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqb : q ∣ b) : q ∣ 2 ^ t - 1 := by
  have h1 : q ∣ 2 ^ M * (2 ^ t - 1) :=
    hqb.trans (jsp87_den_dvd_mer_of_period ha hb ht hM hS hper)
  have hc : Nat.Coprime q (2 ^ M) := by
    refine (Nat.coprime_pow_right_iff (a := q) (b := (2 : ℕ)) (by omega)).mpr ?_
    exact (Nat.coprime_comm).mpr
      ((Nat.coprime_primes (by norm_num : (2 : ℕ).Prime) hq).mpr hq2.symm)
  exact (hc.dvd_mul_left).mp h1

/-- **A PRIME PERIOD IS SMALLER THAN EVERY ODD PRIME OF THE DENOMINATOR** (round
39's Fermat step, `dvd_sub_one_prime_gt`, applied to the period). -/
theorem jsp87_prime_period_lt_den {a b t M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : t.Prime) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqb : q ∣ b) : t < q ∧ q ∣ 2 ^ t - 1 := by
  have h2 : 2 ≤ q := by
    by_cases hq2' : q = 2
    · exact absurd hq2' hq2
    · have := hq.two_le
      omega
  have hq' : t ∣ q - 1 := dvd_sub_one_prime_gt hq ht hq2
    (jsp87_prime_den_dvd_mer ha hb (t := t) (Nat.Prime.pos ht) hM hS hper hq hq2 hqb)
  refine ⟨by
    have hle := Nat.le_of_dvd (show (0 : ℕ) < q - 1 by omega) hq'
    omega,
    jsp87_prime_den_dvd_mer ha hb (t := t) (Nat.Prime.pos ht) hM hS hper hq hq2 hqb⟩

/-! ## 3. Runs of digits in a periodic expansion -/

/-- **THE FRACTIONAL PART OF A RATIONAL IS A MULTIPLE OF `1/b`.** -/
theorem digitAt_fract_fracNum {a b : ℕ} (hb : 0 < b) (N : ℕ) :
    ∃ c : ℤ, 0 ≤ c ∧ c < (b : ℤ) ∧
      Int.fract ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))) = (c : ℝ) / (b : ℝ) := by
  obtain ⟨c, h0, h1, h2⟩ := Int.fract_eq_div_of_mul_natCast hb
    (x := (2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))) (m := ((2 : ℕ) ^ N * a : ℤ)) (by
      have hcast : (2 : ℝ) ^ N * (a : ℝ) = ((2 : ℕ) ^ N * a : ℤ) := by norm_cast
      have hbnz : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
      calc (b : ℝ) * ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)))
          = (b : ℝ) * (2 : ℝ) ^ N * (a : ℝ) / (b : ℝ) := by ring
        _ = (2 : ℝ) ^ N * (a : ℝ) := by field_simp
        _ = ((2 : ℕ) ^ N * a : ℤ) := hcast)
  exact ⟨c, h0, h1, h2⟩

/-- **A RUN OF ONES IS A BINARY TAIL IN THE ORBIT.**  If the digits of `a/b` at
`N .. N+L−1` are all `1`, then `fract (2^{N+j} (a/b)) = 1 − 2^j (1 − fract
(2^N (a/b)))`. -/
private theorem digitAt_fract_oneRun {a b N L : ℕ} (hL : 0 < L)
    (hrun : ∀ j, j < L → digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 1) :
    ∀ j, j ≤ L → Int.fract ((2 : ℝ) ^ (N + j) * ((a : ℝ) / (b : ℝ)))
      = 1 - (2 : ℝ) ^ j * (1 - Int.fract ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)))) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ L := by omega
    have hrun' : digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 1 := hrun j (by omega)
    have hstep := digitAt_fract_succ' ((a : ℝ) / (b : ℝ)) (N + j)
    have heq : N + (j + 1) = (N + j) + 1 := by omega
    rw [heq, hstep, hrun']
    rw [ih hj', pow_succ]
    ring

/-- **THE GAP INEQUALITY OF A ONE-RUN.**  If the digits of `a/b` at
`N .. N+L−1` are all `1` and the fractional part of `2^N (a/b)` is `c/b`, then

`2^L · (b − c) ≤ b`.

This is the sharp form of round 53's `2^L ≤ b`: the numerator `c` of the
fractional part measures how much "room" the run has left. -/
theorem digitAt_oneRun_gap {a b N L : ℕ} (hb : 0 < b) (hL : 0 < L)
    (hrun : ∀ j, j < L → digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 1) :
    ∃ c : ℕ, c < b ∧ 2 ^ L * (b - c) ≤ b := by
  obtain ⟨c, hc0, hc1, hfrac⟩ := digitAt_fract_fracNum (a := a) (b := b) hb N
  have hfj := digitAt_fract_oneRun (a := a) (b := b) (N := N) (L := L) hL hrun L le_rfl
  have hnn := Int.fract_nonneg ((2 : ℝ) ^ (N + L) * ((a : ℝ) / (b : ℝ)))
  have hcn : (c.toNat : ℝ) = (c : ℝ) := by
    have h0 : (0 : ℕ) ≤ c := by exact_mod_cast hc0
    have h1 : c.toNat = c := Int.toNat_of_nonneg h0
    exact_mod_cast h1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : 0 ≤ 1 - (2 : ℝ) ^ L * (1 - (c : ℝ) / (b : ℝ)) := by
    have h2 := hfj
    rw [hfrac] at h2
    linarith
  have h2 : (b : ℝ) - (2 : ℝ) ^ L * ((b : ℝ) - (c : ℝ))
      = (b : ℝ) * (1 - (2 : ℝ) ^ L * (1 - (c : ℝ) / (b : ℝ))) := by field_simp
  have h3 : 0 ≤ (b : ℝ) - (2 : ℝ) ^ L * ((b : ℝ) - (c : ℝ)) :=
    h2 ▸ mul_nonneg (le_of_lt hbR) h1
  have hlt : (c : ℝ) < b := by exact_mod_cast hc1
  have hlt' : (c.toNat : ℝ) < (b : ℝ) := by rw [hcn]; exact hlt
  have hltN : c.toNat < b := by exact_mod_cast hlt'
  refine ⟨c.toNat, hltN, ?_⟩
  have h3' : (2 : ℝ) ^ L * ((b - c.toNat : ℕ) : ℝ) ≤ (b : ℝ) := by
    have hle : c.toNat ≤ b := by omega
    have hsub : ((b - c.toNat : ℕ) : ℝ) = (b : ℝ) - c.toNat := by
      rw [Nat.cast_sub hle]
    rw [hsub, hcn]
    linarith
  exact_mod_cast h3'

/-- **A RUN OF `L` ONES FORCES `2^L ≤ b`** — for an arbitrary rational, in
lowest terms (round 53 proved the analogous statement for the Erdős series
only). -/
theorem jsp87_oneRun_two_pow_le {a b N L : ℕ} (hb : 0 < b) (hL : 0 < L)
    (hrun : ∀ j, j < L → digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 1) : 2 ^ L ≤ b := by
  obtain ⟨c, hc, hgap⟩ := digitAt_oneRun_gap hb hL hrun
  have h1 : 0 < b - c := (Nat.sub_pos_iff_lt).mpr hc
  have h2 : 1 ≤ b - c := by omega
  have h3 : 2 ^ L ≤ 2 ^ L * (b - c) := by
    have := Nat.mul_le_mul_left (2 ^ L) (show (1 : ℕ) ≤ b - c by omega)
    simpa using this
  omega

/-- **A `t`-PERIODIC DIGIT STRING NEVER CONTAINS `t` CONSECUTIVE ONES** at or
after the periodic point.  Indeed a run of `t` ones is the whole tail
(`digitAt_const_of_run`), and then the fractional part would have to be `1`
(`digitAt_no_allOnes`). -/
theorem digitAt_periodic_oneRun_lt {x : ℝ} {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → digitAt x (n + t) = digitAt x n) (N : ℕ) (hN : M ≤ N) :
    ∃ j, j < t ∧ digitAt x (N + j) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ n, N ≤ n → digitAt x n = 1 := digitAt_const_of_run ht 1 hcon hM hN hper
  obtain ⟨j, hj⟩ := digitAt_no_allOnes x N
  exact hj (hall (N + j) (by omega))

/-- **A RUN OF `t` ZEROS AT OR AFTER THE PERIODIC POINT MAKES THE VALUE
DYADIC.**  A run of `t` zeros is the whole tail, so the fractional part of
`2^N x` is `0` and the binary expansion terminates at `N`. -/
theorem digitAt_periodic_zeroRun_dyadic {a b t M N : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → digitAt ((a : ℝ) / (b : ℝ)) (n + t) = digitAt ((a : ℝ) / (b : ℝ)) n)
    (hN : M ≤ N) (hz : ∀ j, j < t → digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 0) :
    ∃ n : ℤ, ((a : ℝ) / (b : ℝ)) = (n : ℝ) / ((2 : ℝ) ^ N) := by
  have hall : ∀ n, N ≤ n → digitAt ((a : ℝ) / (b : ℝ)) n = 0 :=
    digitAt_const_of_run ht 0 hz hM hN hper
  have hfr : ∀ j, Int.fract ((2 : ℝ) ^ (N + j) * ((a : ℝ) / (b : ℝ)))
      = (2 : ℝ) ^ j * Int.fract ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep := digitAt_fract_succ' ((a : ℝ) / (b : ℝ)) (N + j)
      have heq : N + (j + 1) = (N + j) + 1 := by omega
      rw [heq, hstep, hall (N + j) (by omega), ih, pow_succ]
      ring
  have hpt := digitAt_fract_periodic (x := ((a : ℝ) / (b : ℝ))) hM hper N hN
  have hk := hfr t
  have hne : (2 : ℝ) ^ t ≠ 1 := by
    have h1 := succ_le_two_pow t
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ t := by
      have h2 : (2 : ℕ) ≤ t + 1 := by omega
      have h2' : (2 : ℝ) ≤ (t + 1 : ℝ) := by exact_mod_cast h2
      have h1' : (t + 1 : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast h1
      linarith
    linarith
  have hfN : Int.fract ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))) = 0 := by
    rw [← hpt] at hk
    have hnn := Int.fract_nonneg ((2 : ℝ) ^ (N + t) * ((a : ℝ) / (b : ℝ)))
    have hkk : (1 - (2 : ℝ) ^ t) * Int.fract ((2 : ℝ) ^ (N + t) * ((a : ℝ) / (b : ℝ))) = 0 := by
      linarith
    rcases mul_eq_zero.mp hkk with h1 | h2
    · exact absurd (sub_eq_zero.mp h1).symm hne
    · rw [← hpt, h2]
  have hkey : (2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)) = ⌊(2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))⌋ := by
    have h := Int.self_sub_fract ((2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)))
    rw [hfN] at h
    linarith
  refine ⟨⌊(2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))⌋, ?_⟩
  calc (a : ℝ) / (b : ℝ) = (2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)) / (2 : ℝ) ^ N := by field_simp
    _ = ⌊(2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ))⌋ / (2 : ℝ) ^ N := by nth_rewrite 1 [hkey] <;> rfl

/-- **THE ONE-RUNS AFTER THE PERIODIC POINT ARE SHORTER THAN THE PERIOD.**
Rationality pins the period to the order of `2` modulo the odd part of the
denominator (`jsp87_digitPeriod_iff_oddPart_dvd_mer`), and then no one-run
reaches its length. -/
theorem jsp87_digitPeriod_oneRun_lt {a b t M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) (N : ℕ) (hN : M ≤ N) :
    ∃ j, j < t ∧ jsp87Digit (N + j) ≠ 1 := by
  have hper' : ∀ n, M ≤ n → digitAt ((a : ℝ) / (b : ℝ)) (n + t) = digitAt ((a : ℝ) / (b : ℝ)) n := by
    intro n hn
    have h := hper n hn
    rw [jsp87Digit_eq_digitAt (n + t), jsp87Digit_eq_digitAt n, hS] at h
    exact h
  obtain ⟨j, hj, hne⟩ := digitAt_periodic_oneRun_lt (x := ((a : ℝ) / (b : ℝ))) ht hM hper' N hN
  have hne' : jsp87Digit (N + j) ≠ 1 := by
    rw [jsp87Digit_eq_digitAt (N + j), hS]
    exact hne
  exact ⟨j, hj, hne'⟩

/-- **THE ZERO-RUNS AFTER THE PERIODIC POINT ARE DYADIC OR SHORTER THAN THE
PERIOD.** -/
theorem jsp87_digitPeriod_zeroRun_dyadic {a b t M N : ℕ} (ha : Nat.Coprime a b)
    (hb : 0 < b) (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) (hN : M ≤ N)
    (hz : ∀ j, j < t → jsp87Digit (N + j) = 0) :
    ∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ N) := by
  have hper' : ∀ n, M ≤ n → digitAt ((a : ℝ) / (b : ℝ)) (n + t) = digitAt ((a : ℝ) / (b : ℝ)) n := by
    intro n hn
    have h := hper n hn
    rw [jsp87Digit_eq_digitAt (n + t), jsp87Digit_eq_digitAt n, hS] at h
    exact h
  have hz' : ∀ j, j < t → digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 0 := by
    intro j hj
    have h := hz j hj
    rw [jsp87Digit_eq_digitAt (N + j), hS] at h
    exact h
  obtain ⟨n, hn⟩ := digitAt_periodic_zeroRun_dyadic hb ht hM hper' hN hz'
  exact ⟨n, hS.trans hn⟩

/-- **THE ERDŐS SERIES AT A ONE-RUN: `2^L ≤ b`.**  The version of
`jsp87_oneRun_two_pow_le` for the series itself. -/
theorem jsp87_oneRun_two_pow_le_series {a b t M N L : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) (hN : M ≤ N) (hL : 0 < L)
    (hrun : ∀ j, j < L → jsp87Digit (N + j) = 1) : 2 ^ L ≤ b := by
  have hrun' : ∀ j, j < L → digitAt ((a : ℝ) / (b : ℝ)) (N + j) = 1 := by
    intro j hj
    have h := hrun j hj
    rw [jsp87Digit_eq_digitAt (N + j), hS] at h
    exact h
  exact jsp87_oneRun_two_pow_le hb hL hrun'

/-! ## 4. Machine-checked instances -/

private theorem fract_eq_self_of_lt_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Int.fract x = x := by
  have hfl : ⌊x⌋ = 0 := (Int.floor_eq_iff).mpr ⟨by simpa using h0, by simpa using h1⟩
  have h := Int.self_sub_fract x
  rw [hfl] at h
  have h' : x - Int.fract x = 0 := by exact_mod_cast h
  linarith

private theorem fract_sub_natCast {x : ℝ} {n : ℕ} (h : (n : ℝ) ≤ x) (h' : x < (n : ℕ) + 1) :
    Int.fract x = x - (n : ℝ) := by
  have hfl : ⌊x⌋ = n := (Int.floor_eq_iff).mpr ⟨by simpa using h, by simpa using h'⟩
  have h := Int.self_sub_fract x
  rw [hfl] at h
  have h'' : x - Int.fract x = (n : ℝ) := by exact_mod_cast h
  linarith

/-- `5/7 = 0.101 101 101 …` in base `2`: the binary expansion of `5/7` is
`3`-periodic **from the first digit**, because `7 ∣ 2^3 − 1`. -/
theorem digitAt_five_sevens (N : ℕ) :
    digitAt ((5 : ℝ) / 7) (N + 3) = digitAt ((5 : ℝ) / 7) N :=
  digitAt_periodic_of_den_dvd_odd (a := 5) (b := 7) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) N

/-- The three digits of the period, exactly. -/
theorem digitAt_five_sevens_digits :
    digitAt ((5 : ℝ) / 7) 0 = 1 ∧ digitAt ((5 : ℝ) / 7) 1 = 0 ∧ digitAt ((5 : ℝ) / 7) 2 = 1 := by
  have h0 : Int.fract ((1 : ℝ) * ((5 : ℝ) / 7)) = 5 / 7 := by
    have heq : ((1 : ℝ) * ((5 : ℝ) / 7)) = (5 / 7 : ℝ) := by norm_num
    rw [heq]
    have h := fract_sub_natCast (x := (5 / 7 : ℝ)) (n := 0) (by norm_num) (by norm_num)
    linarith
  have h1 : Int.fract ((2 : ℝ) ^ 1 * ((5 : ℝ) / 7)) = 3 / 7 := by
    have heq : ((2 : ℝ) ^ 1 * ((5 : ℝ) / 7)) = (10 / 7 : ℝ) := by norm_num
    rw [heq]
    have h := fract_sub_natCast (x := (10 / 7 : ℝ)) (n := 1) (by norm_num) (by norm_num)
    have h3 : (3 / 7 : ℝ) = 10 / 7 - 1 := by norm_num
    linarith
  have h2 : Int.fract ((2 : ℝ) ^ 2 * ((5 : ℝ) / 7)) = 6 / 7 := by
    have heq : ((2 : ℝ) ^ 2 * ((5 : ℝ) / 7)) = (20 / 7 : ℝ) := by norm_num
    rw [heq]
    have h := fract_sub_natCast (x := (20 / 7 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    have h3 : (6 / 7 : ℝ) = 20 / 7 - 2 := by norm_num
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have key := (digitAt_eq_floor_two_fract ((5 : ℝ) / 7) 0).symm
    have heq : ((2 : ℝ) ^ 0 * ((5 : ℝ) / 7)) = (1 : ℝ) * ((5 : ℝ) / 7) := by norm_num
    rw [key, heq, h0]
    rw [Int.floor_eq_iff]; constructor <;> norm_num
  · have key := (digitAt_eq_floor_two_fract ((5 : ℝ) / 7) 1).symm
    have heq : ((2 : ℝ) ^ 1 * ((5 : ℝ) / 7)) = (2 : ℝ) ^ 1 * ((5 : ℝ) / 7) := rfl
    rw [key, heq, h1]
    rw [Int.floor_eq_iff]; constructor <;> norm_num
  · have key := (digitAt_eq_floor_two_fract ((5 : ℝ) / 7) 2).symm
    have heq : ((2 : ℝ) ^ 2 * ((5 : ℝ) / 7)) = (2 : ℝ) ^ 2 * ((5 : ℝ) / 7) := rfl
    rw [key, heq, h2]
    rw [Int.floor_eq_iff]; constructor <;> norm_num

/-- The `3` above is the *order* of `2` modulo `7`: it is the least exponent
with `7 ∣ 2^t − 1`.  Together with `jsp87_digitPeriod_iff_oddPart_dvd_mer` this
says the minimal eventual period of the binary expansion of `a/7` (in lowest
terms) is exactly `3`. -/
theorem jsp87_ord_seven : jsp87Val2 7 = 0 ∧ jsp87OddPart 7 = 7 ∧
    7 ∣ 2 ^ 3 - 1 ∧ ¬ 7 ∣ 2 ^ 1 - 1 ∧ ¬ 7 ∣ 2 ^ 2 - 1 := by
  refine ⟨(jsp87Val2_spec (k := 0) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩, ?_,
    by norm_num, by norm_num, by norm_num⟩
  rw [jsp87OddPart, (jsp87Val2_spec (k := 0) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩]
  norm_num

/-- `12 = 2^2 · 3`, so the `2`-free part of `12` is `3` and the order of `2`
modulo `3` is `2`: the binary expansion of `7/12` is `2`-periodic **from index
`2` onwards** — the threshold `M ≥ v_2(b)` of
`jsp87_digitPeriod_iff_oddPart_dvd_mer` is exactly right. -/
theorem digitAt_seven_twelve_period_two (N : ℕ) (hN : 2 ≤ N) :
    digitAt ((7 : ℝ) / 12) (N + 2) = digitAt ((7 : ℝ) / 12) N :=
  digitAt_periodic_of_den_dvd (a := 7) (b := 12) (t := 2) (M := 2) (by norm_num) (by norm_num)
    (by norm_num) N hN

/-- The `2`-free part of `12` is `3`, and `3 ∣ 2^2 − 1` while `3 ∤ 2 − 1`. -/
theorem jsp87_ord_twelve : jsp87Val2 12 = 2 ∧ jsp87OddPart 12 = 3 ∧
    3 ∣ 2 ^ 2 - 1 ∧ ¬ 3 ∣ 2 ^ 1 - 1 := by
  refine ⟨(jsp87Val2_spec (k := 2) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩, ?_,
    by norm_num, by norm_num⟩
  rw [jsp87OddPart, (jsp87Val2_spec (k := 2) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩]
  norm_num

/-- **THE PERIOD-`1` CASE, IN DENOMINATOR FORM: the reduced denominator of a
hypothetical rational value of the Erdős series with eventually *constant*
digits is a power of `2` dividing `2^M`; equivalently the `2`-free part of the
denominator is `1`.  (Round 48 proved the weaker statement `S = n/2^M`; here the
denominator itself is pinned.) -/
theorem jsp87_digitPeriod_one_pow_two_den {a b M : ℕ} (ha : Nat.Coprime a b) (hb : 0 < b)
    (hM : 1 ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + 1) = jsp87Digit n) :
    b ∣ 2 ^ M ∧ jsp87OddPart b = 1 := by
  have h := jsp87_den_dvd_mer_of_period (t := 1) ha hb (by norm_num) hM hS hper
  have h2 : b ∣ 2 ^ M := by
    have h' : b ∣ 2 ^ M * (2 ^ 1 - 1) := h
    rw [show (2 : ℕ) ^ 1 - 1 = 1 by norm_num] at h'
    simpa using h'
  have h3 : jsp87OddPart b = 1 := by
    have hd : jsp87OddPart b ∣ 2 ^ M := Nat.dvd_trans (jsp87OddPart_dvd b) h2
    have hc : Nat.Coprime (jsp87OddPart b) (2 ^ M) :=
      (Nat.coprime_pow_right_iff (a := jsp87OddPart b) (b := (2 : ℕ)) (by omega)).mpr
        (jsp87_coprime_two_oddPart hb).symm
    have h5 : jsp87OddPart b ∣ 1 := hc.dvd_of_dvd_mul_left (by
      show jsp87OddPart b ∣ 2 ^ M * 1
      simpa using hd)
    have h6 : 0 < jsp87OddPart b := jsp87OddPart_pos hb
    have h7 : jsp87OddPart b ≤ 1 := by
      refine Nat.le_of_dvd (by omega) h5
    omega
  exact ⟨h2, h3⟩

end JSP87
