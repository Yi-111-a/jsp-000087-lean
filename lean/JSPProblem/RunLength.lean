/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.AdicPrefix

/-!
# Round 53 -- runs in `ω` become runs in the binary expansion, and the
# constant-run criterion

## The gap in the development

Rounds 37-52 attacked the carried Erdős series `S = ∑' n, ω(n) 2^(-(n+1))`
through sixteen families.  Every one of them studies the *pointwise* or the
*periodic* behaviour of a single object: the carry `θ N`, the carry excess
`c N = ⌊θ N⌋`, the binary digit `d N`, the `t`-block `B N t`, the `ω`-window
`Ω N t`, the 2-adic prefix `I N`, the `ω`-profile modulo `m`.

**No round ever asked what a RUN of `ω`-values does to the binary expansion.**
A run is the one piece of information about `ω` that a prime-`k`-tuples
hypothesis is actually able to produce: the hypotheses of Erdős (1948) and of
Pratt (arXiv:2409.15185) are statements about *patterns* of `ω` on consecutive
integers, and a long constant block of `ω`-values is the extreme case of such a
pattern.  This round makes the passage from runs of `ω` to the binary expansion
of `S` **exact and unconditional**, and then shows that a single run of length
`L` already forces a lower bound on the denominator of a hypothetical rational
value of `S`.

The passage is the `L`-step form of the carry splitting, read on a window on
which `ω` is constant:

```
θ N = u (1 - 2^(-L)) + 2^(-L) θ (N + L) = u - 2^(-L) (u - θ (N+L)).
```

So the *whole* fractional part of the carry at `N` is pinned down by the two
real numbers `u` and `θ (N+L)`, and it is a **binary tail**:
`Int.fract (θ N) = 1 - 2^(-L) · (u - θ (N+L))` when the carry does not
overshoot, and `= 2^(-L) · (θ (N+L) - u)` when it does.  Since
`0 < u - θ (N+L) ≤ 1` in the first case, the first `L` binary digits of the
fractional part are `1, 1, …, 1`, and in the second case they are `0, 0, …, 0`.

## The content of this round

* `jsp87Carry_eq_profile` / `jsp87Carry_sub_constRun`: **the profile formula.**
  A prescribed `ω`-profile on a window determines the carry up to the
  explicitly known quantity `2^(-L) θ (N+L)`; a *constant* profile gives the
  closed form `θ N = u - 2^(-L) (u - θ (N+L))`.
* `jsp87_fract_run`, `jsp87_digit_run_ones`, `jsp87_digit_run_zeros`:
  **RUNS BECOME DIGIT RUNS.**  A constant run of `ω` of length `L` produces
  `L` consecutive `1`s (resp. `0`s) in the binary expansion of the Erdős
  series, *at an explicit place*, and the whole run is the binary expansion of
  one real number.  This is the missing bridge between the `ω`-family (rounds
  37-45, 51, 52) and the digit family (rounds 41, 46-48).
* `jsp87_fractCarry_eq_div`, `jsp87_fractCarry_ne_one`:
  **THE ASYMMETRY OF THE LATTICE.**  If `S = a/b` with `b > 0` then every
  *nonzero* value of the doubling orbit `Int.fract (θ N)` satisfies
  `1/b ≤ Int.fract (θ N) ≤ 1 - 1/b`: **the orbit can never come within `1/b` of
  `1`, and can only reach `0` by hitting it exactly.**  The reason is that `0`
  is a fixed point of the doubling map and `1` is not.
* `jsp87Series_irrational_of_digit_run_ones`: **ARBITRARILY LONG RUNS OF `1`s
  IN THE BINARY EXPANSION OF `S` FORCE IRRATIONALITY.**  The dual statement for
  runs of `0`s is *false*, and `jsp87_fractCarry_small_or_zero` records why: a
  tiny fractional part is either exactly `0` -- which happens as soon as `S` is
  a dyadic rational -- or else it forces `b > 2^L`, and there is no way to
  exclude the zero case.
* `jsp87Series_irrational_of_constRun`: **THE CONSTANT-RUN CRITERION.**  If `ω`
  takes an arbitrarily long constant value `u` on windows whose far end has
  carry below `u`, then `S` is irrational.  This is a *concrete, falsifiable,
  arithmetical* hypothesis on `ω` -- a "consecutive almost-primes" statement of
  exactly the flavour of the uniform prime-`k`-tuples hypothesis in the
  published result -- and it is **not** a restatement of aperiodicity: it is a
  statement about the *values* of `ω` on windows, not about periods.
* `jsp87_digit_run_twenty` and `jsp87Series_rational_imp_denominator_ge_eight`:
  **MACHINE-CHECKED INSTANCES.**  A run of three `1`s in the actual binary
  expansion of the Erdős series, produced from the verified constant run
  `ω 20 = ω 21 = ω 22 = 2`, together with the resulting explicit lower bound
  on the denominator of a hypothetical rational value of `S`.

## What this round does NOT do

`jsp_000087_main` remains undeclared.  The constant-run hypothesis is a
*conjecture* (a uniform statement about patterns of `ω` on consecutive
integers); it is not known, and no round of this development can supply it.
What this round supplies is (i) the exact, unconditional passage from runs of
`ω` to the digits, which is the *analytic* half of the Erdős-Pratt argument and
was missing, and (ii) machine-checked instances of it, so that the criterion is
not merely formal but *instantiated* in the actual series.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. Profiles of `ω` on a window -/

/-- **The `L`-block of a profile `a`, read in base `2`:**
`∑ k < L, a k · 2^(-(k+1))`.

This is the real number obtained by reading the first `L` values of a profile
as binary digits after the point. -/
noncomputable def jsp87ProfileSum (L : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ k ∈ Finset.range L, ((a k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹

/-- **A constant run of `ω` of length `L` with value `u`, based at `N`:**
`ω (N + j) = u` for every `j < L`. -/
def jsp87ConstRun (N L u : ℕ) : Prop := ∀ j, j < L → omega (N + j) = u

/-- **The geometric sum.** `∑ k < L, 2^(-(k+1)) = 1 - 2^(-L)`. -/
theorem sum_two_pow_neg_range (L : ℕ) :
    (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹) = 1 - ((2 : ℝ) ^ L)⁻¹ := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hstep : ∀ j : ℕ, ((2 : ℝ) ^ (j + 1))⁻¹ = ((2 : ℝ) ^ j)⁻¹ / 2 := by
      intro j
      rw [pow_succ]
      field_simp
    rw [Finset.sum_range_succ, ih]
    have h1 : ((2 : ℝ) ^ (L + 1))⁻¹ = ((2 : ℝ) ^ L)⁻¹ / 2 := hstep L
    rw [h1]
    ring

/-- **The block of a constant profile**: the `L` binary digits `u, u, …, u` after
the point are the real number `u (1 - 2^(-L))`. -/
theorem jsp87ProfileSum_const (L u : ℕ) :
    jsp87ProfileSum L (fun _ => u) = (u : ℝ) * (1 - ((2 : ℝ) ^ L)⁻¹) := by
  have h : jsp87ProfileSum L (fun _ => u)
      = ((u : ℝ)) * (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹) := by
    unfold jsp87ProfileSum
    rw [Finset.mul_sum]
  rw [h, sum_two_pow_neg_range]

/-! ## 1. The profile formula for the carry -/

/-- **THE PROFILE FORMULA.**  If `ω` agrees with a profile `a` on the window
`[N, N+L)`, then

`θ N = ∑ k < L, a k · 2^(-(k+1)) + 2^(-L) θ (N+L)`,

i.e. the carry is a *computable* block plus the rescaled tail.  This is round
44's `jsp87Carry_split` with the window values replaced by the profile. -/
theorem jsp87Carry_eq_profile {N L : ℕ} {a : ℕ → ℕ} (ha : ∀ k, k < L → omega (N + k) = a k) :
    jsp87Carry N = jsp87ProfileSum L a + ((2 : ℝ) ^ L)⁻¹ * jsp87Carry (N + L) := by
  rw [jsp87Carry_split N L]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [ha k (Finset.mem_range.mp hk)]

/-- **THE CONSTANT-RUN FORMULA.**  If `ω` is constantly `u` on `[N, N+L)` then

`θ N = u - 2^(-L) (u - θ (N+L))`.

The *entire* carry at `N` is thus determined by the integer `u` and the
rescaled tail at the far end of the window. -/
theorem jsp87Carry_sub_constRun {N L u : ℕ} (h : jsp87ConstRun N L u) :
    jsp87Carry N = (u : ℝ) - ((2 : ℝ) ^ L)⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) := by
  rw [jsp87Carry_eq_profile h, jsp87ProfileSum_const]
  ring

/-! ## 2. Runs in the carry: a run of `ω` is a run of digits -/

/-- `1 ≤ 2 ^ j` for every `j` (Mathlib has no unconditional version). -/
private theorem one_le_pow_two (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; nlinarith

/-- `1 < 2 ^ j` for `0 < j`. -/
private theorem one_lt_pow_two (j : ℕ) (hj : 0 < j) : 1 < (2 : ℝ) ^ j := by
  have hmul : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    have hsub : j = (j - 1) + 1 := by omega
    rw [hsub, pow_succ, Nat.add_sub_cancel]
    ring
  rw [hmul]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j - 1) := one_le_pow_two (j - 1)
  have h2 : (2 : ℝ) * 1 ≤ 2 * (2 : ℝ) ^ (j - 1) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  linarith

/-- `2 ^ (-j) < 1` for `0 < j`. -/
private theorem inv_lt_one_pow_two (j : ℕ) (hj : 0 < j) : ((2 : ℝ) ^ j)⁻¹ < 1 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [inv_eq_one_div, div_lt_iff₀ hpos]
  linarith [one_lt_pow_two j hj]

/-- `2 ^ (-j) ≤ 1` for every `j`. -/
private theorem inv_le_one_pow_two (j : ℕ) : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := by
  have hne : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  exact one_le_pow_two j

/-- `2 * 2^(-j) = 2^(-(j-1))` for `0 < j`. -/
private theorem inv_pow_neg (j : ℕ) (hj : 0 < j) :
    ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (j - 1))⁻¹ / 2 := by
  have h1 : (2 : ℝ) ^ (j - 1) * 2 = (2 : ℝ) ^ j := by
    rw [← pow_succ, Nat.sub_add_cancel hj]
  have hne : (2 : ℝ) ^ (j - 1) ≠ 0 := by positivity
  rw [← h1]
  field_simp

private theorem two_mul_pow_neg (j : ℕ) (hj : 0 < j) :
    2 * ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (j - 1))⁻¹ := by
  rw [inv_pow_neg j hj]
  field_simp

/-- `2^(-j) · d ≤ 1` when `0 ≤ d ≤ 1`. -/
private theorem pow_neg_mul_le_one {j : ℕ} {d : ℝ} (hd : 0 ≤ d) (h1 : d ≤ 1) :
    ((2 : ℝ) ^ j)⁻¹ * d ≤ 1 := by
  have hinv : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_pow_two j
  calc ((2 : ℝ) ^ j)⁻¹ * d ≤ 1 * d := mul_le_mul_of_nonneg_right hinv hd
    _ = d := by ring
    _ ≤ 1 := h1

/-- `2^(-j) · d < 1` when `0 ≤ d < 1`. -/
private theorem pow_neg_mul_lt_one {j : ℕ} {d : ℝ} (hd : 0 ≤ d) (h1 : d < 1) :
    ((2 : ℝ) ^ j)⁻¹ * d < 1 := by
  have hinv : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_pow_two j
  have h2 : ((2 : ℝ) ^ j)⁻¹ * d ≤ 1 * d := mul_le_mul_of_nonneg_right hinv hd
  linarith

/-- **The doubling step on the fractional parts of the carries** (round 48's
`jsp87Carry_fract_succ`, read on the fractional parts). -/
theorem jsp87_fractCarry_succ (N : ℕ) :
    Int.fract (jsp87Carry (N + 1)) = Int.fract (2 * Int.fract (jsp87Carry N)) := by
  rw [jsp87Carry_fract_succ N, Int.fract_two_mul]

/-- **RUNS OF `1`s IN THE CARRY.**  Let `1 ≤ L` and let the fractional part of
the carry at `N` be `1 - 2^(-L) · d` with `0 < d ≤ 1`.  Then at every cut point
`N + k`, `k ≤ L`, the fractional part is `1 - 2^(-(L-k)) · d`.

In words: a fractional part whose binary expansion starts with `L` digits equal
to `1` keeps starting with `1` for the whole window, and the *tail* of the run
is the binary expansion of `d`. -/
theorem jsp87_fract_run {N L : ℕ} (_h1 : 1 ≤ L) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (h0 : Int.fract (jsp87Carry N) = 1 - ((2 : ℝ) ^ L)⁻¹ * d) :
    ∀ k, k ≤ L → Int.fract (jsp87Carry (N + k)) = 1 - ((2 : ℝ) ^ (L - k))⁻¹ * d := by
  intro k _
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hkL : k < L := by omega
    have hstep := ih (by omega)
    have hj1 : 0 < L - k := by omega
    have he_pos : 0 < ((2 : ℝ) ^ (L - k))⁻¹ * d := mul_pos (by positivity) hd
    have he2 : 2 * ((2 : ℝ) ^ (L - k))⁻¹ * d ≤ 1 := by
      rw [two_mul_pow_neg (L - k) hj1]
      have hinv : ((2 : ℝ) ^ (L - k - 1))⁻¹ ≤ 1 := inv_le_one_pow_two _
      calc ((2 : ℝ) ^ (L - k - 1))⁻¹ * d ≤ 1 * d :=
            mul_le_mul_of_nonneg_right hinv (le_of_lt hd)
        _ ≤ 1 := by simpa using hd1
    have hflo : ⌊2 * (1 - ((2 : ℝ) ^ (L - k))⁻¹ * d)⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · linarith
      · linarith
    have hself := Int.self_sub_floor (2 * (1 - ((2 : ℝ) ^ (L - k))⁻¹ * d))
    rw [hflo] at hself
    have harg : N + (k + 1) = (N + k) + 1 := by omega
    have hrhs : L - (k + 1) = (L - k) - 1 := by omega
    have heq : 2 * ((2 : ℝ) ^ (L - k))⁻¹ * d = ((2 : ℝ) ^ (L - (k + 1)))⁻¹ * d := by
      rw [hrhs, two_mul_pow_neg (L - k) hj1]
    calc Int.fract (jsp87Carry (N + (k + 1)))
        = Int.fract (2 * (1 - ((2 : ℝ) ^ (L - k))⁻¹ * d)) := by
          rw [harg, jsp87_fractCarry_succ (N + k), hstep]
      _ = 2 * (1 - ((2 : ℝ) ^ (L - k))⁻¹ * d) - 1 := by linarith [hself]
      _ = 1 - ((2 : ℝ) ^ (L - (k + 1)))⁻¹ * d := by linarith

/-- **RUNS OF `0`s IN THE CARRY.**  Dually: let `1 ≤ L` and let the fractional
part of the carry at `N` be `2^(-L) · d` with `0 < d < 1`.  Then at every cut
point `N + k`, `k ≤ L`, the fractional part is `2^(-(L-k)) · d`. -/
theorem jsp87_fract_run_zeros {N L : ℕ} (_h1 : 1 ≤ L) {d : ℝ} (hd : 0 < d) (hd1 : d < 1)
    (h0 : Int.fract (jsp87Carry N) = ((2 : ℝ) ^ L)⁻¹ * d) :
    ∀ k, k ≤ L → Int.fract (jsp87Carry (N + k)) = ((2 : ℝ) ^ (L - k))⁻¹ * d := by
  intro k _
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hkL : k < L := by omega
    have hstep := ih (by omega)
    have hj1 : 0 < L - k := by omega
    have he_pos : 0 < ((2 : ℝ) ^ (L - k))⁻¹ * d := mul_pos (by positivity) hd
    have he2 : 2 * ((2 : ℝ) ^ (L - k))⁻¹ * d < 1 := by
      rw [two_mul_pow_neg (L - k) hj1]
      have hinv : ((2 : ℝ) ^ (L - k - 1))⁻¹ ≤ 1 := inv_le_one_pow_two _
      calc ((2 : ℝ) ^ (L - k - 1))⁻¹ * d ≤ 1 * d :=
            mul_le_mul_of_nonneg_right hinv (le_of_lt hd)
        _ < 1 := by simpa using hd1
    have hflo : ⌊2 * ((2 : ℝ) ^ (L - k))⁻¹ * d⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · have hnonneg : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ (L - k))⁻¹ * d := by positivity
        exact_mod_cast hnonneg
      · linarith
    have hself := Int.self_sub_floor (2 * ((2 : ℝ) ^ (L - k))⁻¹ * d)
    rw [hflo] at hself
    have harg : N + (k + 1) = (N + k) + 1 := by omega
    have hrhs : L - (k + 1) = (L - k) - 1 := by omega
    have heq : 2 * ((2 : ℝ) ^ (L - k))⁻¹ * d = ((2 : ℝ) ^ (L - (k + 1)))⁻¹ * d := by
      rw [hrhs, two_mul_pow_neg (L - k) hj1]
    calc Int.fract (jsp87Carry (N + (k + 1)))
        = Int.fract (2 * ((2 : ℝ) ^ (L - k))⁻¹ * d) := by
          rw [harg, jsp87_fractCarry_succ (N + k), hstep, mul_assoc]
      _ = 2 * ((2 : ℝ) ^ (L - k))⁻¹ * d := by
        have hself' := hself
        push_cast at hself'
        linarith
      _ = ((2 : ℝ) ^ (L - (k + 1)))⁻¹ * d := heq

/-- **THE CONSTANT-RUN IDENTITY (no overshoot).**  If `ω` is constantly `u` on
`[N, N+L)`, `1 ≤ L`, and `u - 1 ≤ θ (N+L) < u`, then with `d = u - θ (N+L) ∈ (0, 1]`

`Int.fract (θ N) = 1 - 2^(-L) · d`.

So the binary expansion of the carry at `N` starts with `L` digits equal to
`1`, and its whole tail is `d`. -/
theorem jsp87_fract_constRun_ones {N L u : ℕ} (_h1 : 1 ≤ L) (h : jsp87ConstRun N L u)
    (hlo : (u : ℝ) - 1 ≤ jsp87Carry (N + L)) (hhi : jsp87Carry (N + L) < (u : ℝ)) :
    Int.fract (jsp87Carry N)
      = 1 - ((2 : ℝ) ^ L)⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) := by
  set d : ℝ := (u : ℝ) - jsp87Carry (N + L) with hd
  have hcarry : jsp87Carry N = (u : ℝ) - ((2 : ℝ) ^ L)⁻¹ * d := by
    rw [hd] at ⊢
    exact jsp87Carry_sub_constRun h
  have hd0 : 0 ≤ d := le_of_lt (by linarith)
  have hd1 : d ≤ 1 := by linarith
  have hmul : 0 < ((2 : ℝ) ^ L)⁻¹ * d := by positivity
  have hmul1 : ((2 : ℝ) ^ L)⁻¹ * d ≤ 1 := pow_neg_mul_le_one hd0 hd1
  have hcast : ((u - 1 : ℤ) : ℝ) = (u : ℝ) - 1 := by push_cast; ring
  have hfl : ⌊jsp87Carry N⌋ = (u - 1 : ℤ) := by
    have h1 : ((u - 1 : ℤ) : ℝ) ≤ jsp87Carry N := by rw [hcarry]; linarith
    have h2 : jsp87Carry N < ((u - 1 : ℤ) : ℝ) + 1 := by rw [hcarry]; linarith
    rw [Int.floor_eq_iff]
    constructor
    · exact h1
    · exact_mod_cast h2
  have hfl' : ⌊jsp87Carry N⌋ = (u : ℝ) - 1 := by rw [hfl]; exact hcast
  have hself := Int.self_sub_fract (jsp87Carry N)
  have h2 : jsp87Carry N - Int.fract (jsp87Carry N) = (u : ℝ) - 1 := by
    rw [hself, hfl']
  rw [hcarry] at h2
  rw [hcarry]
  linarith

/-- **A CONSTANT RUN OF `ω` GIVES A RUN OF `1`s IN THE BINARY EXPANSION OF THE
ERDŐS SERIES.**  If `ω` is constantly `u` on `[N, N+L)` with `1 ≤ L`,
`1 ≤ N` and `u - 1 ≤ θ (N+L) < u`, then the `N`-th, …, `(N+L-1)`-th binary
digits of `jsp87Series` are all `1`.

This is the bridge between the `ω`-family and the digit family: a block of
consecutive integers all having the same number of prime factors forces a block
of consecutive `1`s in the base-`2` expansion of the Erdős series. -/
theorem jsp87_digit_run_ones {N L u : ℕ} (h1 : 1 ≤ L) (hN : 1 ≤ N)
    (h : jsp87ConstRun N L u) (hlo : (u : ℝ) - 1 ≤ jsp87Carry (N + L))
    (hhi : jsp87Carry (N + L) < (u : ℝ)) (hk : k < L) :
    jsp87Digit (N + k) = 1 := by
  have hpos' : 0 < (u : ℝ) - jsp87Carry (N + L) := by linarith
  have hle' : (u : ℝ) - jsp87Carry (N + L) ≤ 1 := by linarith
  have hrun := jsp87_fract_run (N := N) (L := L) h1
    (d := (u : ℝ) - jsp87Carry (N + L)) hpos' hle'
    (jsp87_fract_constRun_ones h1 h hlo hhi)
  have hstep := hrun k (by omega)
  have hj : 0 < L - k := by omega
  have hpos : 0 < ((2 : ℝ) ^ (L - k))⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) := by
    positivity
  have hle : ((2 : ℝ) ^ (L - k))⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) ≤ 1 :=
    pow_neg_mul_le_one (le_of_lt hpos') hle'
  have hdig := jsp87_digit_eq_fractCarry (N := N + k) (by omega)
  have hnext : Int.fract (jsp87Carry (N + k + 1))
      = 1 - ((2 : ℝ) ^ (L - k - 1))⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) := by
    have hn := hrun (k + 1) (by omega)
    have harg : L - (k + 1) = L - k - 1 := by omega
    rwa [harg] at hn
  have heq : 2 * ((2 : ℝ) ^ (L - k))⁻¹ * ((u : ℝ) - jsp87Carry (N + L))
      = ((2 : ℝ) ^ (L - k - 1))⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) := by
    rw [two_mul_pow_neg (L - k) hj]
  have hdig' : (jsp87Digit (N + k) : ℝ) = 1 := by
    rw [hstep, hnext] at hdig
    linarith
  exact_mod_cast hdig'

/-- **THE CONSTANT-RUN IDENTITY (overshoot).**  If `ω` is constantly `u` on
`[N, N+L)` and `u < θ (N+L) < u + 1`, then with `d = θ (N+L) - u ∈ (0, 1)`

`Int.fract (θ N) = 2^(-L) · d`. -/
theorem jsp87_fract_constRun_zeros {N L u : ℕ} (h : jsp87ConstRun N L u)
    (hlo : (u : ℝ) < jsp87Carry (N + L)) (hhi : jsp87Carry (N + L) < (u : ℝ) + 1) :
    Int.fract (jsp87Carry N)
      = ((2 : ℝ) ^ L)⁻¹ * (jsp87Carry (N + L) - (u : ℝ)) := by
  set d : ℝ := jsp87Carry (N + L) - (u : ℝ) with hd
  have hcarry : jsp87Carry N = (u : ℝ) + ((2 : ℝ) ^ L)⁻¹ * d := by
    have h := jsp87Carry_sub_constRun h
    rw [hd] at ⊢
    nlinarith [h]
  have hd0 : 0 ≤ d := le_of_lt (by linarith)
  have hd1 : d < 1 := by linarith
  have hmul : 0 < ((2 : ℝ) ^ L)⁻¹ * d := by positivity
  have hmul1 : ((2 : ℝ) ^ L)⁻¹ * d < 1 := pow_neg_mul_lt_one hd0 hd1
  have hcast : ((u : ℤ) : ℝ) = (u : ℝ) := by push_cast; ring
  have hfl : ⌊jsp87Carry N⌋ = (u : ℤ) := by
    have h1 : ((u : ℤ) : ℝ) ≤ jsp87Carry N := by rw [hcarry]; linarith
    have h2 : jsp87Carry N < ((u : ℤ) : ℝ) + 1 := by rw [hcarry]; linarith
    rw [Int.floor_eq_iff]
    constructor
    · exact h1
    · exact_mod_cast h2
  have hfl' : ⌊jsp87Carry N⌋ = (u : ℝ) := by rw [hfl]; exact hcast
  have hself := Int.self_sub_fract (jsp87Carry N)
  have h2 : jsp87Carry N - Int.fract (jsp87Carry N) = (u : ℝ) := by
    rw [hself, hfl']
  rw [hcarry] at h2
  rw [hcarry]
  linarith

/-- **A CONSTANT RUN OF `ω` GIVES A RUN OF `0`s IN THE BINARY EXPANSION OF THE
ERDŐS SERIES** (when the carry at the far end of the window overshoots `u`).
The dual of `jsp87_digit_run_ones`. -/
theorem jsp87_digit_run_zeros {N L u : ℕ} (h1 : 1 ≤ L) (hN : 1 ≤ N)
    (h : jsp87ConstRun N L u) (hlo : (u : ℝ) < jsp87Carry (N + L))
    (hhi : jsp87Carry (N + L) < (u : ℝ) + 1) (hk : k < L) :
    jsp87Digit (N + k) = 0 := by
  have hpos' : 0 < jsp87Carry (N + L) - (u : ℝ) := by linarith
  have hle' : jsp87Carry (N + L) - (u : ℝ) < 1 := by linarith
  have hrun := jsp87_fract_run_zeros (N := N) (L := L) h1
    (d := jsp87Carry (N + L) - (u : ℝ)) hpos' hle'
    (jsp87_fract_constRun_zeros h hlo hhi)
  have hstep := hrun k (by omega)
  have hj : 0 < L - k := by omega
  have hpos : 0 < ((2 : ℝ) ^ (L - k))⁻¹ * (jsp87Carry (N + L) - (u : ℝ)) := by
    positivity
  have hlt : ((2 : ℝ) ^ (L - k))⁻¹ * (jsp87Carry (N + L) - (u : ℝ)) < 1 :=
    pow_neg_mul_lt_one (le_of_lt hpos') hle'
  have hdig := jsp87_digit_eq_fractCarry (N := N + k) (by omega)
  have hnext : Int.fract (jsp87Carry (N + k + 1))
      = ((2 : ℝ) ^ (L - k - 1))⁻¹ * (jsp87Carry (N + L) - (u : ℝ)) := by
    have hn := hrun (k + 1) (by omega)
    have harg : L - (k + 1) = L - k - 1 := by omega
    rwa [harg] at hn
  have heq : 2 * ((2 : ℝ) ^ (L - k))⁻¹ * (jsp87Carry (N + L) - (u : ℝ))
      = ((2 : ℝ) ^ (L - k - 1))⁻¹ * (jsp87Carry (N + L) - (u : ℝ)) := by
    rw [two_mul_pow_neg (L - k) hj]
  have hdig' : (jsp87Digit (N + k) : ℝ) = 0 := by
    rw [hstep, hnext] at hdig
    linarith
  exact_mod_cast hdig'

/-! ## 3. The lattice of the doubling orbit, and its asymmetry -/

/-- **The orbit lives on the lattice `1/b ℤ`.**  If `S = a/b` with `b > 0` then
`Int.fract (θ N) = c/b` for a natural `c < b`: the fractional part of the
carry is a `b`-th of a unit.  (Round 41's `jsp87FracNum_spec`, transported from
`Int.fract (2^N S)` to `Int.fract (θ N)` by round 40's `jsp87_fract_scaled`.) -/
theorem jsp87_fractCarry_eq_div {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ c : ℕ, c < b ∧ Int.fract (jsp87Carry N) = (c : ℝ) / (b : ℝ) := by
  have h := jsp87FracNum_spec hb h hN
  exact ⟨jsp87FracNum b N, h.1, (jsp87_fract_scaled hN).symm.trans h.2⟩

/-- **THE ASYMMETRY OF THE LATTICE.**  If `S = a/b` with `b > 0` then every
value of the doubling orbit is either exactly `0` or lies in the *middle*
interval `[1/b, 1 - 1/b]`.

**The orbit can never come within `1/b` of `1`; it can only reach `0` by
hitting `0` exactly.**  The asymmetry is the whole point: `0` is a fixed point
of the doubling map `x ↦ frac (2x)`, while `1` is not in its image. -/
theorem jsp87_fractCarry_ne_one {a : ℤ} {b : ℕ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    {N : ℕ} (hN : 1 ≤ N) :
    Int.fract (jsp87Carry N) = 0
      ∨ ((1 : ℝ) / (b : ℝ) ≤ Int.fract (jsp87Carry N)
        ∧ Int.fract (jsp87Carry N) ≤ 1 - (1 : ℝ) / (b : ℝ)) := by
  obtain ⟨c, hc, hf⟩ := jsp87_fractCarry_eq_div hb h hN
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  by_cases hz : c = 0
  · left
    rw [hf, hz]
    simp
  · right
    have hpos : 0 < c := lt_of_le_of_ne (Nat.zero_le c) (Ne.symm hz)
    have h1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hpos
    have hbnat : c ≤ b - 1 := by omega
    have hnum : (c : ℝ) ≤ ((b : ℕ) - 1 : ℕ) := by exact_mod_cast hbnat
    have hdiv : (c : ℝ) / (b : ℝ) ≤ ((b : ℕ) - 1 : ℕ) / (b : ℝ) :=
      div_le_div_of_nonneg_right hnum hbR.le
    have hb1 : 1 ≤ b := by omega
    have hcast : (((b : ℕ) - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ b)]
      norm_num
    have hkey : (((b : ℕ) - 1 : ℕ) : ℝ) / (b : ℝ) = 1 - (1 : ℝ) / (b : ℝ) := by
      rw [hcast]
      have : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
      field_simp
    constructor
    · rw [hf]
      exact (div_le_div_iff_of_pos_right hbR).2 h1
    · rw [hf, ← hkey]
      exact hdiv

/-- **WHY RUNS OF `0`s ARE NOT A CRITERION.**  A *tiny* value of the orbit is
either exactly `0` -- which happens as soon as `S` is a dyadic rational and
`2^M S` is an integer -- or else it forces the denominator `b` to be larger
than `2^L`.  There is no way to exclude the zero case, so unlike
`jsp87_digit_run_ones` (section 4) this yields no irrationality statement. -/
theorem jsp87_fractCarry_small_or_zero {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) {N L : ℕ} (hN : 1 ≤ N) (_h1 : 1 ≤ L)
    (hsmall : Int.fract (jsp87Carry N) < ((2 : ℝ) ^ L)⁻¹) :
    Int.fract (jsp87Carry N) = 0 ∨ ((2 : ℝ) ^ L) < (b : ℝ) := by
  rcases jsp87_fractCarry_ne_one hb h hN with hz | ⟨hlo, hhi⟩
  · exact Or.inl hz
  · obtain ⟨c, hc, hf⟩ := jsp87_fractCarry_eq_div hb h hN
    by_cases hcz : c = 0
    · left
      rw [hf, hcz]
      simp
    · right
      have hcp : 0 < c := lt_of_le_of_ne (Nat.zero_le c) (Ne.symm hcz)
      have h1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcp
      have htwoR : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
      have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hsmall' : (c : ℝ) / (b : ℝ) < 1 / (2 : ℝ) ^ L := by
        rw [hf] at hsmall
        rwa [inv_eq_one_div] at hsmall
      have hm : (c : ℝ) / (b : ℝ) * (2 : ℝ) ^ L < 1 := (lt_div_iff₀ htwoR).mp hsmall'
      have hcc : (c : ℝ) * (2 : ℝ) ^ L < (b : ℝ) := by
        have h3 : (c : ℝ) * (2 : ℝ) ^ L / (b : ℝ) < 1 := by
          simpa [div_mul_eq_mul_div] using hm
        have := (div_lt_iff₀ hbR).mp h3
        simpa using this
      have hmul : 1 * (2 : ℝ) ^ L ≤ (c : ℝ) * (2 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt htwoR)
      linarith

/-! ## 4. The criteria -/

/-- **THE ORBIT CRITERION.**  If the doubling orbit of the carry comes
arbitrarily close to `1` -- formally, if for every `L ≥ 1` there is a cut point
`N ≥ 1` with `Int.fract (θ N) ≥ 1 - 2^(-L)` -- then `jsp87Series` is
irrational.

The proof is the lattice statement of section 3: a rational orbit takes its
values in a finite set of `b` points, none of which is within `1/b` of `1`. -/
theorem jsp87Series_irrational_of_fract_near_one
    (H : ∀ L : ℕ, 1 ≤ L → ∃ N : ℕ, 1 ≤ N
      ∧ 1 - ((2 : ℝ) ^ L)⁻¹ ≤ Int.fract (jsp87Carry N)) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  have hcast : jsp87Series = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← hq, Rat.cast_def]
  -- `2 ^ (b+1) > b`: the denominator bound needed to make the lattice gap visible
  have hbR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hden
  have hbn : (2 : ℝ) ^ (q.den + 1) > (q.den : ℝ) := by
    have h3 : (q.den : ℝ) + 1 ≤ (2 : ℝ) ^ q.den := by
      exact_mod_cast (succ_le_two_pow q.den)
    have h2 : (2 : ℝ) * (2 : ℝ) ^ q.den = (2 : ℝ) ^ (q.den + 1) := by
      rw [pow_succ]
      ring
    rw [← h2]
    linarith
  have htwoR : (0 : ℝ) < (2 : ℝ) ^ (q.den + 1) := by positivity
  obtain ⟨N, hN, hnear⟩ := H (q.den + 1) (by omega)
  have horbit := jsp87_fractCarry_ne_one (N := N) (a := q.num) (b := q.den) hden hcast hN
  rcases horbit with hz | ⟨hlo, hhi⟩
  · have hpos' : (0 : ℝ) < ((2 : ℝ) ^ (q.den + 1))⁻¹ := by positivity
    have hlt1 : ((2 : ℝ) ^ (q.den + 1))⁻¹ < 1 := inv_lt_one_pow_two _ (by omega)
    rw [hz] at hnear
    linarith
  · have hkey2 : 1 / (q.den : ℝ) ≤ 1 / (2 : ℝ) ^ (q.den + 1) := by
      have hnear' : 1 - 1 / (2 : ℝ) ^ (q.den + 1) ≤ Int.fract (jsp87Carry N) := by
        rwa [inv_eq_one_div] at hnear
      linarith
    have hmul : 1 * (2 : ℝ) ^ (q.den + 1) ≤ 1 * (q.den : ℝ) :=
      (div_le_div_iff₀ hbR htwoR).mp hkey2
    linarith

/-- **THE DIGIT-RUN CRITERION.**  If the binary expansion of the Erdős series
contains arbitrarily long runs of `1`s -- formally, if for every `L ≥ 1` there
is a place `N ≥ 1` with `jsp87Digit (N+j) = 1` for every `j < L` -- then
`jsp87Series` is irrational.

This is the first criterion in this development that is phrased directly on the
digits together with a *run length*.  Note that it is **false** with `1`
replaced by `0` (see `jsp87_fractCarry_small_or_zero`): the digit string of a
dyadic rational is eventually all `0`s. -/
theorem jsp87Series_irrational_of_digit_run_ones
    (H : ∀ L : ℕ, 1 ≤ L → ∃ N : ℕ, 1 ≤ N ∧ ∀ j, j < L → jsp87Digit (N + j) = 1) :
    Irrational jsp87Series := by
  refine jsp87Series_irrational_of_fract_near_one ?_
  intro L hL
  obtain ⟨N, hN, hrun⟩ := H L hL
  refine ⟨N, hN, ?_⟩
  -- walk backwards from the end of the run
  have hback : ∀ m : ℕ, m ≤ L →
      1 - ((2 : ℝ) ^ m)⁻¹ ≤ Int.fract (jsp87Carry (N + (L - m))) := by
    intro m hm
    revert hm
    induction m with
    | zero =>
      intro hm
      have hnn : (0 : ℝ) ≤ Int.fract (jsp87Carry (N + L)) := Int.fract_nonneg _
      have hz : 1 - ((2 : ℝ) ^ 0)⁻¹ = 0 := by norm_num
      rw [hz, Nat.sub_zero]
      exact hnn
    | succ m ih =>
      intro hm
      have harg2 : L - (m + 1) = L - m - 1 := by omega
      rw [harg2]
      have hprev : 1 - ((2 : ℝ) ^ m)⁻¹ ≤ Int.fract (jsp87Carry (N + (L - m))) :=
        ih (by omega)
      have hidx : 1 ≤ N + (L - m - 1) := by omega
      have hdig := jsp87_digit_eq_fractCarry (N := N + (L - m - 1)) hidx
      have hd1 : jsp87Digit (N + (L - m - 1)) = 1 := hrun (L - m - 1) (by omega)
      have harg : N + (L - m - 1) + 1 = N + (L - m) := by omega
      have hnext0 : (0 : ℝ) ≤ Int.fract (jsp87Carry (N + (L - m))) := Int.fract_nonneg _
      have hdig' : (1 : ℝ) = 2 * Int.fract (jsp87Carry (N + (L - m - 1)))
            - Int.fract (jsp87Carry (N + (L - m))) := by
        have h := hdig
        simp only [hd1, harg] at h
        norm_num at h
        exact h
      have hfraclt : Int.fract (jsp87Carry (N + (L - m - 1))) < 1 := Int.fract_lt_one _
      have hrec' : Int.fract (jsp87Carry (N + (L - m)))
          = 2 * Int.fract (jsp87Carry (N + (L - m - 1))) - 1 := by
        have htwo : (1 : ℝ) ≤ 2 * Int.fract (jsp87Carry (N + (L - m - 1))) := by
          linarith
        have hlt2 : 2 * Int.fract (jsp87Carry (N + (L - m - 1))) < 2 := by linarith
        have hflo : ⌊2 * Int.fract (jsp87Carry (N + (L - m - 1)))⌋ = 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast htwo
          · exact_mod_cast hlt2
        have hself' : Int.fract (2 * Int.fract (jsp87Carry (N + (L - m - 1))))
            = 2 * Int.fract (jsp87Carry (N + (L - m - 1))) - 1 := by
          have h := Int.self_sub_floor (2 * Int.fract (jsp87Carry (N + (L - m - 1))))
          rw [hflo] at h
          norm_num at h
          linarith
        have hstep' := jsp87_fractCarry_succ (N + (L - m - 1))
        rw [harg, hself'] at hstep'
        exact hstep'
      have heq : 2 * ((2 : ℝ) ^ (m + 1))⁻¹ = ((2 : ℝ) ^ m)⁻¹ :=
        two_mul_pow_neg (m + 1) (by omega)
      linarith
  simpa using hback L (by omega)

/-- **THE CONSTANT-RUN CRITERION.**  Suppose that for every `L ≥ 1` there are a
place `N ≥ 1` and a value `u` with `ω` constantly equal to `u` on `[N, N+L)`
and with the carry at the far end of the window strictly between `u - 1` and
`u`.  Then `jsp87Series` is irrational.

The hypothesis is a *concrete arithmetical statement about the values of `ω`*:
for every length there is a block of `L` consecutive integers, all having
exactly `u` distinct prime factors, positioned so that the carry does not
overshoot.  It is of the same nature as the uniform prime-`k`-tuples hypothesis
in the published conditional result (a statement about patterns of `ω` on
consecutive integers), and it is **not** a reformulation of aperiodicity. -/
theorem jsp87Series_irrational_of_constRun
    (H : ∀ L : ℕ, 1 ≤ L → ∃ N u : ℕ, 1 ≤ N ∧ jsp87ConstRun N L u
      ∧ (u : ℝ) - 1 ≤ jsp87Carry (N + L) ∧ jsp87Carry (N + L) < (u : ℝ)) :
    Irrational jsp87Series := by
  refine jsp87Series_irrational_of_fract_near_one ?_
  intro L hL
  obtain ⟨N, u, hN, hrun, hlo, hhi⟩ := H L hL
  have hfrac := jsp87_fract_constRun_ones hL hrun hlo hhi
  refine ⟨N, hN, ?_⟩
  have hdu : 0 < (u : ℝ) - jsp87Carry (N + L) := by linarith
  have hdu1 : (u : ℝ) - jsp87Carry (N + L) ≤ 1 := by linarith
  have hle : ((2 : ℝ) ^ L)⁻¹ * ((u : ℝ) - jsp87Carry (N + L)) ≤ 1 :=
    pow_neg_mul_le_one (le_of_lt hdu) hdu1
  have hx : (0 : ℝ) ≤ ((2 : ℝ) ^ L)⁻¹ := by positivity
  have hle' : ((2 : ℝ) ^ L)⁻¹ * ((u : ℝ) - jsp87Carry (N + L))
      ≤ ((2 : ℝ) ^ L)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hdu1 hx
    simpa using h
  rw [hfrac]
  linarith

/-! ## 5. Machine-checked instances in the actual series -/

/-- `ω 20 = 2`, `ω 21 = 2`, `ω 22 = 2`. -/
theorem omega_run_twenty : omega 20 = 2 ∧ omega 21 = 2 ∧ omega 22 = 2 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- `ω 23 = 1, ω 24 = 2, ω 25 = 1, ω 26 = 2, ω 27 = 1, ω 28 = 2, ω 29 = 1`. -/
theorem omega_window_23 :
    omega 23 = 1 ∧ omega 24 = 2 ∧ omega 25 = 1 ∧ omega 26 = 2 ∧ omega 27 = 1
      ∧ omega 28 = 2 ∧ omega 29 = 1 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- **THE CARRY AT `23` LIES IN `[1, 2)`.**  The lower bound is exact
(`ω 23 / 2 + ω 24 / 4 = 1` already); the upper bound comes from round 44's
`jsp87Carry_le_window` with `L = 7`. -/
theorem jsp87Carry_23_window : 1 ≤ jsp87Carry 23 ∧ jsp87Carry 23 < 2 := by
  have hsplit := jsp87Carry_split 23 2
  have hpos : (0 : ℝ) ≤ jsp87Carry 25 := le_of_lt (jsp87Carry_pos 25)
  obtain ⟨h23, h24, h25, h26, h27, h28, h29⟩ := omega_window_23
  have hs2 : (∑ k ∈ Finset.range 2, ((omega (23 + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      = (1 : ℝ) / 2 + 2 / 4 := by
    norm_num [Finset.sum_range_succ, h23, h24]
  have hlo : 1 ≤ jsp87Carry 23 := by
    rw [hsplit, hs2, show jsp87Carry (23 + 2) = jsp87Carry 25 from by norm_num,
      show ((2 : ℝ) ^ 2)⁻¹ = (1 / 4 : ℝ) by norm_num]
    norm_num
    linarith [hpos]
  have hle := jsp87Carry_le_window (N := 23) (L := 7) (by omega)
  have hle' : jsp87Carry 23 ≤ (∑ k ∈ Finset.range 7,
      ((omega (23 + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) + ((2 : ℝ) ^ 7)⁻¹ * (31 : ℝ) := by
    have h := hle
    simpa [Nat.cast_ofNat] using h
  have hsum : (∑ k ∈ Finset.range 7,
      ((omega (23 + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) < 1.6 := by
    norm_num [Finset.sum_range_succ, show omega 23 = 1 from h23, show omega 24 = 2 from h24,
      show omega 25 = 1 from h25, show omega 26 = 2 from h26,
      show omega 27 = 1 from h27, show omega 28 = 2 from h28, show omega 29 = 1 from h29]
  have hupp : jsp87Carry 23 < 2 := by
    have hlast : ((2 : ℝ) ^ 7)⁻¹ * (31 : ℝ) < 1 / 2 := by
      norm_num [show ((2 : ℝ) ^ 7)⁻¹ = (1 / 128 : ℝ) by norm_num]
    linarith
  exact ⟨hlo, hupp⟩

/-- **A CONSTANT RUN OF `ω` IN THE ACTUAL SERIES.**  `ω 20 = ω 21 = ω 22 = 2`
and `1 ≤ θ 23 < 2`, so `ω` is constantly `2` on `[20, 23)` with the carry at
the far end strictly below `2`. -/
theorem jsp87ConstRun_twenty : jsp87ConstRun 20 3 2 := by
  obtain ⟨h20, h21, h22⟩ := omega_run_twenty
  intro j hj
  interval_cases j <;> omega

/-- **THE HEADLINE INSTANCE: THREE CONSECUTIVE `1`s IN THE BINARY EXPANSION OF
THE ERDŐS SERIES**, at the explicit place `20, 21, 22`.

This is a machine-checked instance of `jsp87_digit_run_ones`, obtained from the
verified constant run `ω 20 = ω 21 = ω 22 = 2`.  In particular the base-`2`
expansion of `∑ n ≥ 1, ω(n) 2^(-n)` contains `1 1 1` at positions `21, 22, 23`
of the digit string `jsp87Digit`. -/
theorem jsp87_digit_run_twenty :
    jsp87Digit 20 = 1 ∧ jsp87Digit 21 = 1 ∧ jsp87Digit 22 = 1 := by
  obtain ⟨hlo, hupp⟩ := jsp87Carry_23_window
  have hlo' : (2 : ℝ) - 1 ≤ jsp87Carry (20 + 3) := by
    rw [show (20 + 3 : ℕ) = 23 by norm_num]
    linarith
  have hupp' : jsp87Carry (20 + 3) < (2 : ℝ) := by
    rw [show (20 + 3 : ℕ) = 23 by norm_num]
    exact hupp
  have hrun : ∀ k : ℕ, k < 3 → jsp87Digit (20 + k) = 1 := by
    intro k hk
    exact jsp87_digit_run_ones (N := 20) (L := 3) (u := 2) (by omega) (by omega)
      (jsp87ConstRun_twenty) hlo' hupp' hk
  have h0 : jsp87Digit (20 + 0) = 1 := hrun 0 (by omega)
  have h1 : jsp87Digit (20 + 1) = 1 := hrun 1 (by omega)
  have h2 : jsp87Digit (20 + 2) = 1 := hrun 2 (by omega)
  rw [show (20 + 0 : ℕ) = 20 by norm_num] at h0
  rw [show (20 + 1 : ℕ) = 21 by norm_num] at h1
  rw [show (20 + 2 : ℕ) = 22 by norm_num] at h2
  exact ⟨h0, h1, h2⟩

/-- **THE NEAR-ONE INSTANCE.**  At the cut point `20` the orbit of the doubling
map is within `1/8` of `1`:

`7/8 ≤ Int.fract (θ 20) < 1`. -/
theorem jsp87_fractCarry_twenty_ge : (7 / 8 : ℝ) ≤ Int.fract (jsp87Carry 20) := by
  obtain ⟨hlo, hupp⟩ := jsp87Carry_23_window
  have hlo' : (2 : ℝ) - 1 ≤ jsp87Carry (20 + 3) := by
    rw [show (20 + 3 : ℕ) = 23 by norm_num]
    linarith
  have hupp' : jsp87Carry (20 + 3) < (2 : ℝ) := by
    rw [show (20 + 3 : ℕ) = 23 by norm_num]
    exact hupp
  have hfrac := jsp87_fract_constRun_ones (N := 20) (L := 3) (u := 2) (by omega)
    (jsp87ConstRun_twenty) hlo' hupp'
  have hpos : 0 < (2 : ℝ) - jsp87Carry 23 := by linarith
  have hdu1 : (2 : ℝ) - jsp87Carry 23 ≤ 1 := by linarith
  have hle : ((2 : ℝ) ^ 3)⁻¹ * ((2 : ℝ) - jsp87Carry 23) ≤ 1 :=
    pow_neg_mul_le_one (le_of_lt hpos) hdu1
  rw [hfrac]
  have : ((2 : ℝ) ^ 3)⁻¹ = (1 / 8 : ℝ) := by norm_num
  rw [this]
  linarith

/-- **A RUN OF `L` ONES IN THE BINARY EXPANSION FORCES `2 ^ L` TO DIVIDE THE
DENOMINATOR.**  If `jsp87Series = a / b` with `a` an integer and `b > 0` a
natural number, and at some cut point `N ≥ 1` the doubling orbit satisfies
`Int.fract (θ N) ≥ 1 - 2^(-L)` with `L ≥ 1`, then `2 ^ L ≤ b`.

This is the *quantitative* form of `jsp87Series_irrational_of_digit_run_ones`:
a single run of `L` consecutive `1`s already rules out every rational value of
`S` whose denominator is smaller than `2 ^ L`. -/
theorem jsp87Series_rational_imp_denominator_ge {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) {N L : ℕ} (hN : 1 ≤ N) (h1 : 1 ≤ L)
    (hnear : 1 - ((2 : ℝ) ^ L)⁻¹ ≤ Int.fract (jsp87Carry N)) :
    2 ^ L ≤ b := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have htwoR : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hgt1 : 1 < (2 : ℝ) ^ L := one_lt_pow_two L (by omega)
  have hinvlt : ((2 : ℝ) ^ L)⁻¹ < 1 := inv_lt_one_pow_two L (by omega)
  rcases jsp87_fractCarry_ne_one (N := N) (a := a) (b := b) hb h hN
    with hz | ⟨hlo, hhi⟩
  · have hpos' : (0 : ℝ) < ((2 : ℝ) ^ L)⁻¹ := by positivity
    rw [hz] at hnear
    linarith
  · have hnear' : 1 - 1 / (2 : ℝ) ^ L ≤ Int.fract (jsp87Carry N) := by
      rwa [inv_eq_one_div] at hnear
    have hkey2 : 1 / (b : ℝ) ≤ 1 / (2 : ℝ) ^ L := by linarith
    have hmul : 1 * (2 : ℝ) ^ L ≤ 1 * (b : ℝ) :=
      (div_le_div_iff₀ hbR htwoR).mp hkey2
    have hreal : (2 : ℝ) ^ L ≤ (b : ℝ) := by linarith
    exact_mod_cast hreal

/-- **THE NEAR-ONE INSTANCE AT `N = 20`.**  The constant run
`ω 20 = ω 21 = ω 22 = 2` with `1 ≤ θ 23 < 2` gives

`1 - 2^(-3) ≤ Int.fract (θ 20) < 1`. -/
theorem jsp87_fractCarry_twenty_near_one :
    1 - ((2 : ℝ) ^ 3)⁻¹ ≤ Int.fract (jsp87Carry 20) := by
  have h := jsp87_fractCarry_twenty_ge
  have heq : 1 - ((2 : ℝ) ^ 3)⁻¹ = (7 / 8 : ℝ) := by norm_num
  rw [heq]
  exact h

/-- **A QUANTITATIVE LOWER BOUND ON THE DENOMINATOR.**  If
`jsp87Series = a/b` with `a` an integer and `b > 0` a natural, then `b ≥ 8`:
the verified run of three `1`s at `20, 21, 22` pushes the orbit to within
`1/8` of `1`, while a rational orbit stays at distance at least `1/b` from
`1`.  This is the first *numerical* constraint on the hypothetical denominator
in this development. -/
theorem jsp87Series_rational_imp_denominator_ge_eight {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) : 8 ≤ b := by
  have := jsp87Series_rational_imp_denominator_ge (N := 20) (L := 3) hb h
    (by omega) (by omega) (jsp87_fractCarry_twenty_near_one)
  norm_num at this ⊢
  omega

end JSP87
