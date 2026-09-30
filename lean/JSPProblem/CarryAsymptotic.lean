/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Radix

/-!
# JSP-000087 : asymptotic carry theory — the logarithmic window, the mean
# identity, and the digit-density criterion

Rounds 37–46 attacked the *carried* Erdős series `S = ∑ n, ω(n) 2^{-(n+1)}` from
ten directions; rounds 47, 48, 49 attacked the *carry-free* (primary) expansion,
the *doubling map on the carries*, and the criterion in *arbitrary radix* — and
round 49 closed the radix escape route with `jsp87_noCarry_fails_any_radix`.

**This round is asymptotic.**  Every earlier round attacked the carry through
*periodicity*: prove (or refute) that `d N`, `⌊θ N⌋`, `Int.fract (θ N)` or
`jsp87DigitBlock N t` is eventually periodic.  This round instead asks **how
fast the carry excess `c N = ⌊θ N⌋` can grow**, and what a rational value of `S`
would force about the *rate* of the binary digit string.

The single observation driving the round is that the carry is a **geometrically
weighted average of the `ω`-values after the cut point**, so the logarithmic
bound `ω m ≤ log₂ m` (round 44) makes the carry *sublinear*:

> `jsp87Carry_le_logb` :  `1 ≤ N → θ N ≤ (log N + 1) / log 2`.

This is the **first sublinear upper bound on the carry**: rounds 38–40 only had
the linear `θ N ≤ N + 1`.  Together with round 44's `1 ≤ ⌊θ N⌋` for `2 ≤ N` it
gives a **logarithmic window** — the carry excess of the Erdős series lives in
`[1, log₂ N + log₂ e]` at every cut point, while round 44 proved it is
*unbounded*.  So the carry excess is neither small nor bounded, but it is
**at most logarithmic**, and it is *below every fixed level on exponentially
long scales*.

## Main results

| Theorem | Statement |
| --- | --- |
| `two_pow_rescale` | `2^N / 2^{N+k+1} = 1/2^{k+1}`: the rescaling behind everything |
| `omega_le_logb_real` | **the `ℝ` form of round 44's `omega_le_log2`**: `ω n ≤ log n / log 2` |
| `jsp87Carry_eq_tsum` | **the carry as a series: `θ N = ∑' k, ω(N+k)·2^{-(k+1)}`** |
| **`jsp87Carry_le_logb_sharp`** | **THE LOGARITHMIC BOUND ON THE CARRY: `θ N ≤ log₂ N + log₂ e / N`** — the first sublinear upper bound on the carry |
| `jsp87Carry_le_logb` | `θ N ≤ (log N + 1)/log 2 = log₂ N + log₂ e` |
| `jsp87CarryExcess_le_logb` | the same for `c N = ⌊θ N⌋` |
| **`jsp87CarryExcess_le_of_le_pow_two`** | **`N ≤ 2^{k+1} → c N ≤ k + 3`: on the whole range `[0, 2^{k+1}]` the carry excess is `< k+3`** |
| `jsp87CarryExcess_unbounded_beyond` | the (round-44-unbounded) carry excess escapes every such range: `∃ N, 2^{k+1} < N ∧ k+4 ≤ c N` |
| **`jsp87CarryExcess_window`** | **THE LOGARITHMIC WINDOW: `1 ≤ c N ≤ k+3` for `2 ≤ N ≤ 2^{k+1}`** |
| **`jsp87_sum_carry`** | **THE MEAN IDENTITY: `∑_{M<N} θ M = W N + θ N − S`**, `W N = ∑_{M<N} ω M` |
| `jsp87_sum_carryExcess_le` / `_ge` / `_le_logb` | the carry excess is the mean identity up to `N`, and logarithmically bounded on average |
| **`jsp87_digitCount_eq`** | **THE DIGIT-COUNT IDENTITY: `D N = W N + c N − ∑_{M<N} c M`** — the first exact formula relating the binary digit string to `ω` and to the carries |
| **`jsp87_digitCount_eq_fractSum`** | **`D N + fract (2^N S) = S + ∑_{M<N} fract (2^M S)`** — the digit count *is* the partial sum of the doubling orbit |
| `jsp87_digitCount_le`, `jsp87_digitCount_ge_sub_fract` | `D N ≤ N`; `S − fract (2^N S) ≤ D N` |
| `jsp87_digit_eq_of_periodic` | a `t`-periodic digit string is `t`-constant after `M`: `d (M + q t + j) = d (M+j)` |
| `jsp87PeriodOnes`, `jsp87PeriodOnes_bounds` | the number of `1`s in one period, `0 ≤ s ≤ t` |
| `jsp87_sum_digit_period_block` | a full period contributes exactly `s` ones |
| **`jsp87_digitCount_split`** | **`D (M + q t + r) = D M + q·s + ρ` with `ρ = ∑_{j<r} d (M+j)`, `0 ≤ ρ ≤ r < t`** |
| **`jsp87_digitCount_periodic_bounds`** | **an eventually periodic digit string has `D M ≤ D N ≤ D M + N + t` for `N ≥ M`** |
| **`jsp87Series_rational_imp_digitCount_linear`** | **RATIONALITY ⇒ the digit count grows exactly linearly** (the *rate* companion of round 41's period statement) |
| **`jsp87Series_irrational_of_digitDensity_not_bounded`** | **THE RATE CRITERION: if the digit count is not bounded by any linear function of `N` along an unbounded sequence, `S` is irrational** |

The residual gap is unchanged in *kind* — it is the aperiodicity of the binary
digit string — but this round shows that the gap is a statement about
**asymptotics**, not merely about periods: a rational `S` would have to make the
mean of its own doubling orbit converge to a rational of the form `s/t`.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. Tools -/

/-- **Rescaling a power of two.**  For all `N, k`,
`2^N / 2^{N+k+1} = 1 / 2^{k+1}`: the rescaling that turns the carry tail into
the geometric weighting of the `ω`-values after the cut point. -/
theorem two_pow_rescale (N k : ℕ) :
    (2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
  induction N with
  | zero =>
      have h1 : 0 + k + 1 = k + 1 := by omega
      rw [pow_zero, one_mul, h1]
  | succ N ih =>
      have h1 : N + 1 + k + 1 = N + k + 2 := by omega
      have hpow : (2 : ℝ) ^ (N + k + 2) = (2 : ℝ) ^ (N + k + 1) * (2 : ℝ) := by
        have h2 : N + k + 2 = (N + k + 1) + 1 := by omega
        rw [h2, pow_succ]
      have hstep : ((2 : ℝ) ^ (N + k + 2))⁻¹ = ((2 : ℝ) ^ (N + k + 1))⁻¹ * (2 : ℝ)⁻¹ := by
        rw [hpow, mul_inv_rev, mul_comm]
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hsplit : (2 : ℝ) ^ (N + 1) = (2 : ℝ) * (2 : ℝ) ^ N := by
        rw [pow_succ]; ring
      have hkey : (2 : ℝ) ^ (N + 1) * (((2 : ℝ) ^ (N + k + 1))⁻¹ * (2 : ℝ)⁻¹)
          = ((2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹) * ((2 : ℝ) * (2 : ℝ)⁻¹) := by
        rw [hsplit]
        ac_rfl
      rw [h1, hstep, hkey, ih, mul_inv_cancel₀ h2, mul_one]

/-- `2^{-(k+1)} = (1/2)^{k+1}`. -/
theorem two_pow_inv_eq_half_pow (k : ℕ) :
    ((2 : ℝ) ^ (k + 1))⁻¹ = (1 / 2 : ℝ) ^ (k + 1) := by
  calc ((2 : ℝ) ^ (k + 1))⁻¹ = (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by rw [inv_eq_one_div]
    _ = (1 / 2 : ℝ) ^ (k + 1) := by
        have h := div_pow (1 : ℝ) 2 (k + 1)
        rw [one_pow] at h
        exact h.symm

/-- **The logarithmic bound `log (1 + x) ≤ x`**, for `1 + x` positive. -/
theorem Real.log_add_one_le {x : ℝ} (hx : 0 < 1 + x) : Real.log (1 + x) ≤ x := by
  have h2 : 0 < Real.exp x := Real.exp_pos x
  have h3 : (1 : ℝ) + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have h := Real.strictMonoOn_log.monotoneOn hx h2 h3
  rwa [Real.log_exp] at h

/-- **`log 2 ≥ 1/2`**, from `Real.one_sub_inv_le_log_of_pos` at `x = 2`. -/
theorem Real.log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
  norm_num at h
  linarith

/-- The geometric weight of the `k`-th place, in half-powers. -/
theorem omega_pow_half (k : ℕ) :
    ((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
      = (1 / 2 : ℝ) * (((k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
  rw [two_pow_inv_eq_half_pow, pow_succ]
  ring

/-- `∑' n, n · (1/2)^n = 2` (Mathlib's
`hasSum_coe_mul_geometric_of_norm_lt_one` at the ratio `1/2`). -/
theorem tsum_nat_mul_half_pow :
    (∑' n : ℕ, ((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) = 2 := by
  have h := tsum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  norm_num at h ⊢
  linarith

/-- `∑' n, n · (1/2)^n` is summable. -/
theorem summable_nat_mul_half_pow :
    Summable (fun n : ℕ => ((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) :=
  (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).summable

/-- `(1/2)^{n+1} = (1/2) · (1/2)^n`. -/
theorem half_pow_succ_eq (n : ℕ) : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) * (1 / 2) ^ n := by
  rw [pow_succ]; ring

/-- `∑' n, (1/2)^{n+1}` is summable. -/
theorem summable_half_pow_succ : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
  have hg := summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  rw [show (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = (fun n => (1 / 2) * (1 / 2) ^ n) by
        funext n; exact half_pow_succ_eq n]
  exact hg.mul_left (1 / 2)

/-- **`∑' n, (1/2)^{n+1} = 1`.** -/
theorem tsum_half_pow_succ : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
  rw [show (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = (fun n => (1 / 2) * (1 / 2) ^ n) by
        funext n; exact half_pow_succ_eq n,
      Summable.tsum_mul_left (1 / 2)
        (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)),
      tsum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)]
  have hne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  rw [show ((1 : ℝ) - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by ring]
  have : (1 / 2 : ℝ) * (1 / 2)⁻¹ = 1 := mul_inv_cancel₀ hne
  linarith

/-- **`∑' n, 2^{-(n+1)} = 1`.** -/
theorem tsum_two_pow_neg : (∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  rw [show (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) = (fun n => (1 / 2) ^ (n + 1)) by
        funext n; exact two_pow_inv_eq_half_pow n,
      tsum_half_pow_succ]

/-- `∑' n, 2^{-(n+1)}` is summable. -/
theorem summable_two_pow_neg : Summable (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) := by
  rw [show (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) = (fun n => (1 / 2) ^ (n + 1)) by
        funext n; exact two_pow_inv_eq_half_pow n]
  exact summable_half_pow_succ

/-- `∑' n, c · 2^{-(n+1)}` is summable for every real `c`. -/
theorem summable_const_mul_two_pow_neg (c : ℝ) :
    Summable (fun n : ℕ => c * ((2 : ℝ) ^ (n + 1))⁻¹) :=
  (summable_two_pow_neg.mul_left c)

/-- `∑' n, ((k : ℕ) : ℝ) · 2^{-(n+1)} = k`. -/
theorem tsum_natconst_two_pow_neg (k : ℕ) :
    (∑' n : ℕ, ((k : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = ((k : ℕ) : ℝ) := by
  rw [show (fun n : ℕ => ((k : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (fun n : ℕ => ((k : ℕ) : ℝ) * (1 / 2) ^ (n + 1)) by
        funext n; rw [two_pow_inv_eq_half_pow]]
  rw [Summable.tsum_mul_left ((k : ℕ) : ℝ) summable_half_pow_succ, tsum_half_pow_succ]
  ring

/-- **`∑' n, n · 2^{-(n+1)} = 1`.** -/
theorem tsum_natmul_self_two_pow_neg :
    (∑' n : ℕ, ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 1 := by
  rw [show (fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (fun n : ℕ => (1 / 2) * (((n : ℕ) : ℝ) * (1 / 2) ^ n)) by
        funext n; rw [omega_pow_half],
      Summable.tsum_mul_left (1 / 2) summable_nat_mul_half_pow, tsum_nat_mul_half_pow]
  ring

/-- `∑' n, n · 2^{-(n+1)}` is summable. -/
theorem summable_natmul_self_two_pow_neg :
    Summable (fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
  rw [show (fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = (fun n : ℕ => (1 / 2) * (((n : ℕ) : ℝ) * (1 / 2) ^ n)) by
        funext n; rw [omega_pow_half]]
  exact summable_nat_mul_half_pow.mul_left (1 / 2)

/-- **THE WEIGHTED GEOMETRIC SUM.**  For all real `C, B`,

`∑' k, C · 2^{-(k+1)} + B · k · 2^{-(k+1)} = C + B`,

i.e. `∑' k, 2^{-(k+1)} = 1` and `∑' k, k·2^{-(k+1)} = 1` in one stroke. -/
theorem tsum_weighted (C B : ℝ) :
    (∑' k : ℕ, (C * ((2 : ℝ) ^ (k + 1))⁻¹ + B * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)))
      = C + B := by
  have h1 : Summable (fun k : ℕ => C * ((2 : ℝ) ^ (k + 1))⁻¹) :=
    summable_const_mul_two_pow_neg C
  have h2 : Summable (fun k : ℕ => B * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)) :=
    summable_natmul_self_two_pow_neg.mul_left B
  have hsplit : (∑' k : ℕ, (C * ((2 : ℝ) ^ (k + 1))⁻¹
        + B * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)))
      = (∑' k : ℕ, C * ((2 : ℝ) ^ (k + 1))⁻¹)
        + (∑' k : ℕ, B * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)) :=
    Summable.tsum_add h1 h2
  have hmul1 : (∑' k : ℕ, C * ((2 : ℝ) ^ (k + 1))⁻¹)
      = C * (∑' k : ℕ, ((2 : ℝ) ^ (k + 1))⁻¹) :=
    Summable.tsum_mul_left C summable_two_pow_neg
  have hmul2 : (∑' k : ℕ, B * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹))
      = B * (∑' k : ℕ, ((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) :=
    Summable.tsum_mul_left B summable_natmul_self_two_pow_neg
  rw [hsplit, hmul1, hmul2, tsum_two_pow_neg, tsum_natmul_self_two_pow_neg]
  ring

/-- **THE REAL LOGARITHMIC BOUND ON `ω`.**  For `0 < n`,
`ω n ≤ log n / log 2`, the `ℝ` version of round 44's `omega_le_log2`. -/
theorem omega_le_logb_real {n : ℕ} (hn : 0 < n) :
    (omega n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((2 : ℝ) ^ omega n) ≤ (n : ℝ) := by
    have h2 : ((2 ^ omega n : ℕ) : ℝ) ≤ (n : ℝ) := by
      have hn2 := two_pow_omega_le hn
      exact_mod_cast hn2
    rwa [Nat.cast_pow] at h2
  have hexp : (2 : ℝ) ^ omega n = Real.exp (((omega n : ℕ) : ℝ) * Real.log 2) := by
    have h := (Real.exp_nat_mul (Real.log 2) (omega n)).symm
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  have hpos1 : 0 < Real.exp (((omega n : ℕ) : ℝ) * Real.log 2) := Real.exp_pos _
  have hpos2 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkey : (((omega n : ℕ) : ℝ) * Real.log 2) ≤ Real.log n := by
    have hh := Real.strictMonoOn_log.monotoneOn hpos1 hpos2
      (by simpa [hexp] using hcast)
    rw [Real.log_exp] at hh
    exact hh
  exact (le_div_iff₀ hlog2).2 hkey

/-! ## 1. The carry as a series, and the logarithmic window -/

/-- The summability of the rescaled carry tail. -/
theorem summable_omegaShift (N : ℕ) :
    Summable (fun k : ℕ => ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
  have hle : ∀ k : ℕ,
      ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
        ≤ (((N + k : ℕ) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    intro k
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (omega_le_self (N + k))) (by positivity)
  have hsplit : (fun k : ℕ => (((N + k : ℕ) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      = fun k => (((N : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
          + ((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
    funext k
    push_cast
    ring
  refine Summable.of_nonneg_of_le ?_ hle ?_
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  · rw [hsplit]
    exact (summable_const_mul_two_pow_neg ((N : ℕ) : ℝ)).add summable_natmul_self_two_pow_neg

/-- **THE CARRY AS A SERIES.**  `θ N = ∑' k, ω(N+k) · 2^{-(k+1)}`: the carry at
the cut point `N` is the geometrically weighted average of the `ω`-values
after `N`. -/
theorem jsp87Carry_eq_tsum (N : ℕ) :
    jsp87Carry N = ∑' k : ℕ, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
  have hs : Summable (fun k : ℕ => jsp87Term (N + k)) := hasSum_jsp87Tail N |>.summable
  have htm : jsp87Tail N
      = ∑' k : ℕ, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹ := by
    rw [jsp87Tail]
    exact tsum_congr fun k => rfl
  have hs2 : Summable (fun k : ℕ => ((omega (N + k) : ℕ) : ℝ)
      * ((2 : ℝ) ^ (N + k + 1))⁻¹) := hs
  rw [jsp87Carry, htm, ← Summable.tsum_mul_left ((2 : ℝ) ^ N) hs2]
  refine tsum_congr fun k => ?_
  calc (2 : ℝ) ^ N * (((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (N + k + 1))⁻¹)
      = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹) := by ring
    _ = ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [two_pow_rescale N k]

/-- **`log (N + k) ≤ log N + k/N`** for `1 ≤ N`. -/
theorem log_add_le_log_add_div {N k : ℕ} (hN : 1 ≤ N) :
    Real.log ((N + k : ℕ) : ℝ) ≤ Real.log N + (k : ℝ) / N := by
  have hpos1 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hposL : 0 < ((N + k : ℕ) : ℝ) := by
    have : (0 : ℕ) < N + k := by omega
    exact_mod_cast this
  have hposM : 0 < (N : ℝ) * (1 + (k : ℝ) / N) := mul_pos hpos1 (by positivity)
  have hle : ((N + k : ℕ) : ℝ) ≤ (N : ℝ) * (1 + (k : ℝ) / N) := by
    push_cast
    field_simp <;> norm_num
  have hmono : Real.log ((N + k : ℕ) : ℝ) ≤ Real.log ((N : ℝ) * (1 + (k : ℝ) / N)) :=
    Real.strictMonoOn_log.monotoneOn hposL hposM hle
  calc Real.log ((N + k : ℕ) : ℝ) ≤ Real.log ((N : ℝ) * (1 + (k : ℝ) / N)) := hmono
    _ = Real.log N + Real.log (1 + (k : ℝ) / N) := by
        rw [Real.log_mul (by exact_mod_cast (show (N : ℕ) ≠ 0 by omega))
          (by positivity : ((1 : ℝ) + (k : ℝ) / N) ≠ 0)]
    _ ≤ Real.log N + (k : ℝ) / N := by
        linarith [Real.log_add_one_le (x := (k : ℝ) / N) (by positivity)]

/-- **THE LOGARITHMIC BOUND ON THE CARRY (sharp form).**  For `1 ≤ N`,

`θ N ≤ log N / log 2 + 1 / (N · log 2)`,

i.e. `⌊θ N⌋ ≤ log₂ N + log₂ e / N`.  This is the **first sublinear upper
bound on the carry** of the Erdős series: rounds 38–40 only had the linear
`θ N ≤ N + 1`. -/
theorem jsp87Carry_le_logb_sharp {N : ℕ} (hN : 1 ≤ N) :
    jsp87Carry N ≤ Real.log N / Real.log 2 + 1 / (N * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ k : ℕ, ((omega (N + k) : ℕ) : ℝ) ≤ Real.log N / Real.log 2
      + (k : ℝ) / (N * Real.log 2) := by
    intro k
    have h1 := omega_le_logb_real (n := N + k) (by omega)
    have h2 := log_add_le_log_add_div (N := N) (k := k) hN
    have h3 : (0 : ℝ) < N * Real.log 2 := mul_pos hNr hlog2
    have h1' : ((omega (N + k) : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((N + k : ℕ) : ℝ) :=
      (le_div_iff₀ hlog2).mp h1
    have hcomb : Real.log N / Real.log 2 + (k : ℝ) / (N * Real.log 2)
        = (Real.log N + (k : ℝ) / N) / Real.log 2 := by field_simp <;> ring
    rw [hcomb, le_div_iff₀ hlog2]
    exact h1'.trans h2
  have hg : Summable (fun k : ℕ => Real.log N / Real.log 2 * ((2 : ℝ) ^ (k + 1))⁻¹
      + (1 / (N * Real.log 2)) * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)) := by
    exact (summable_const_mul_two_pow_neg (Real.log N / Real.log 2)).add
      (summable_natmul_self_two_pow_neg.mul_left (1 / (N * Real.log 2)))
  have hptw : ∀ k : ℕ, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
      ≤ Real.log N / Real.log 2 * ((2 : ℝ) ^ (k + 1))⁻¹
        + (1 / (N * Real.log 2)) * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
    intro k
    calc ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
        ≤ (Real.log N / Real.log 2 + (k : ℝ) / (N * Real.log 2))
            * ((2 : ℝ) ^ (k + 1))⁻¹ := mul_le_mul_of_nonneg_right (hpt k) (by positivity)
      _ = Real.log N / Real.log 2 * ((2 : ℝ) ^ (k + 1))⁻¹
            + (1 / (N * Real.log 2)) * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by ring
  have hle : (∑' k : ℕ, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      ≤ Real.log N / Real.log 2 + 1 / (N * Real.log 2) := by
    calc (∑' k : ℕ, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        ≤ ∑' k : ℕ, (Real.log N / Real.log 2 * ((2 : ℝ) ^ (k + 1))⁻¹
            + (1 / (N * Real.log 2)) * (((k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)) :=
          Summable.tsum_le_tsum hptw (summable_omegaShift N) hg
      _ = Real.log N / Real.log 2 + 1 / (N * Real.log 2) :=
        tsum_weighted (Real.log N / Real.log 2) (1 / (N * Real.log 2))
  rw [jsp87Carry_eq_tsum]
  exact hle

/-- **THE LOGARITHMIC BOUND ON THE CARRY.**  For `1 ≤ N`,
`θ N ≤ (log N + 1) / log 2 = log₂ N + log₂ e`. -/
theorem jsp87Carry_le_logb {N : ℕ} (hN : 1 ≤ N) :
    jsp87Carry N ≤ (Real.log N + 1) / Real.log 2 := by
  have h1 := jsp87Carry_le_logb_sharp hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [le_div_iff₀ hlog2]
  calc jsp87Carry N * Real.log 2
      ≤ (Real.log N / Real.log 2 + 1 / (N * Real.log 2)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right h1 hlog2.le
    _ = Real.log N + (N : ℝ)⁻¹ := by field_simp <;> ring
    _ ≤ Real.log N + 1 := by
        have hNpos : (0 : ℝ) < N := by linarith
        have hinv : (N : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hNpos).mpr hNr
        linarith

/-- **THE LOGARITHMIC BOUND ON THE CARRY EXCESS.** -/
theorem jsp87CarryExcess_le_logb {N : ℕ} (hN : 1 ≤ N) :
    (jsp87CarryExcess N : ℝ) ≤ (Real.log N + 1) / Real.log 2 := by
  have h := Int.floor_le (jsp87Carry N)
  rw [jsp87CarryExcess]
  exact h.trans (jsp87Carry_le_logb hN)

/-- `τ 0 = S`. -/
theorem jsp87Tail_zero : jsp87Tail 0 = jsp87Series := by
  have h := jsp87_series_eq_sum_add_tail 0
  simpa using h.symm

/-- `τ 1 = S` (because `ω 0 = 0`). -/
theorem jsp87Tail_one : jsp87Tail 1 = jsp87Series := by
  have h := jsp87_series_eq_sum_add_tail 1
  simp only [Finset.sum_range_one, jsp87Term_zero, add_zero] at h
  simpa using h.symm

/-- `θ 0 = S`. -/
theorem jsp87Carry_zero : jsp87Carry 0 = jsp87Series := by
  rw [jsp87Carry, pow_zero, one_mul, jsp87Tail_zero]

/-- `θ 1 = 2 S`. -/
theorem jsp87Carry_one : jsp87Carry 1 = 2 * jsp87Series := by
  rw [jsp87Carry, pow_one, jsp87Tail_one]

theorem jsp87Carry_zero_lt_one : jsp87Carry 0 < 1 := by
  rw [jsp87Carry_zero]
  have := jsp87Series_lt_half
  linarith

theorem jsp87Carry_one_lt_one : jsp87Carry 1 < 1 := by
  rw [jsp87Carry_one]
  have := jsp87Series_lt_half
  linarith

/-- `⌊S⌋ = 0`. -/
theorem jsp87_floor_S_zero : ⌊jsp87Series⌋ = 0 := by
  have h1 := jsp87Series_ge_quarter
  have h2 := jsp87Series_lt_half
  rw [Int.floor_eq_iff]
  simp only [Int.cast_zero, zero_add]
  constructor <;> linarith

/-- `⌊θ 0⌋ = 0`, i.e. the carry excess vanishes at the origin. -/
theorem jsp87CarryExcess_zero : jsp87CarryExcess 0 = 0 :=
  (jsp87CarryExcess_eq_zero_iff.mpr jsp87Carry_zero_lt_one)

/-- `log N ≤ (k+1) · log 2` when `N ≤ 2^{k+1}`. -/
theorem log_le_mul_log_two {k N : ℕ} (hN : 1 ≤ N) (h : N ≤ 2 ^ (k + 1)) :
    Real.log N ≤ (k + 1) * Real.log 2 := by
  have hposN : 0 < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hcast : (N : ℝ) ≤ (((2 : ℕ) ^ (k + 1) : ℕ) : ℝ) := by
    have hh : N ≤ 2 ^ (k + 1) := h
    exact_mod_cast hh
  have hpos2 : 0 < (((2 : ℕ) ^ (k + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    positivity
  have h6 : Real.log ((N : ℕ) : ℝ) ≤ Real.log (((2 : ℕ) ^ (k + 1) : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hposN hpos2 hcast
  have h7 : Real.log (((2 : ℕ) ^ (k + 1) : ℕ) : ℝ) = (k + 1) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    push_cast
    ring
  rw [h7] at h6
  exact h6

/-- **THE CARRY EXCESS IS LOGARITHMIC.**  For `N ≤ 2^{k+1}` the carry excess of
the Erdős series is `< k + 3`: the first sublinear upper bound on
`jsp87CarryExcess`. -/
theorem jsp87CarryExcess_le_of_le_pow_two {k N : ℕ} (h : N ≤ 2 ^ (k + 1)) :
    (jsp87CarryExcess N : ℝ) ≤ k + 3 := by
  by_cases hN : 2 ≤ N
  · have h1 := jsp87CarryExcess_le_logb (N := N) (by omega)
    have h2 := log_le_mul_log_two (by omega) h
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (1 / 2 : ℝ) ≤ Real.log 2 := Real.log_two_ge_half
    rw [le_div_iff₀ hlog2] at h1
    have hmul : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    have h2' : Real.log N ≤ (k : ℝ) * Real.log 2 + Real.log 2 := by linarith
    have hA : ((jsp87CarryExcess N : ℝ)) * Real.log 2
        ≤ (k : ℝ) * Real.log 2 + Real.log 2 + 1 := by linarith
    refine le_of_mul_le_mul_right ?_ hlog2
    linarith
  · rcases Nat.eq_zero_or_pos N with h0 | h1
    · subst h0
      rw [jsp87CarryExcess_zero]
      exact_mod_cast (Nat.zero_le (k + 3))
    · have hN1 : N = 1 := by omega
      subst hN1
      rw [jsp87CarryExcess_eq_zero_iff.mpr jsp87Carry_one_lt_one]
      exact_mod_cast (Nat.zero_le (k + 3))

/-- **On the scale `N = 2^{k+1}` the carry excess is `< k + 3`.** -/
theorem jsp87CarryExcess_le_pow_two (k : ℕ) :
    (jsp87CarryExcess (2 ^ (k + 1)) : ℝ) ≤ k + 3 :=
  jsp87CarryExcess_le_of_le_pow_two (N := 2 ^ (k + 1)) (by omega)

/-- **THE CARRY EXCESS ESCAPES EVERY SUCH RANGE.**  Combining the
unconditional unboundedness of round 44 with the logarithmic bound: for every
`k` the carry excess exceeds `k` somewhere strictly beyond `2^{k+1}`. -/
theorem jsp87CarryExcess_unbounded_beyond (k : ℕ) :
    ∃ N : ℕ, 2 ^ (k + 1) < N ∧ k + 4 ≤ jsp87CarryExcess N := by
  obtain ⟨N, hN1, hle⟩ := jsp87CarryExcess_unbounded (k := k + 4)
  refine ⟨N, ?_, hle⟩
  by_contra hcon
  have h1 := jsp87CarryExcess_le_of_le_pow_two (k := k) (N := N) (by omega)
  have hle' : ((k + 4 : ℕ) : ℝ) ≤ jsp87CarryExcess N := by exact_mod_cast hle
  have hle'' : (k : ℝ) + 4 ≤ (jsp87CarryExcess N : ℝ) := by push_cast at hle'; linarith
  linarith

/-- **THE LOGARITHMIC WINDOW.**  For `2 ≤ N` the carry excess is at least `1`
(round 44) and at most `log₂ N + log₂ e`; and on the whole range
`[0, 2^{k+1}]` it is `< k + 3`.  So the carry excess of the Erdős series is
unbounded (round 44) yet never larger than logarithmic, and it *escapes* every
bounded range. -/
theorem jsp87CarryExcess_window {k N : ℕ} (hN : 2 ≤ N) (h : N ≤ 2 ^ (k + 1)) :
    1 ≤ jsp87CarryExcess N ∧ (jsp87CarryExcess N : ℝ) ≤ k + 3 :=
  ⟨jsp87CarryExcess_ge_one hN, jsp87CarryExcess_le_of_le_pow_two h⟩


/-! ## 2. The mean identity: the carries, the `ω`-prefix, and the digit count -/

/-- A `Finset.sum_congr` wrapper for sums over `Finset.range`. -/
theorem sum_congr_range {M : Type*} [AddCommMonoid M] {f g : ℕ → M} (h : ∀ n, f n = g n) (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range N, g n := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact h n

/-- **THE `ω`-PREFIX** `W N = ∑_{M<N} ω M`. -/
noncomputable def jsp87OmegaSum (N : ℕ) : ℤ := ∑ M ∈ Finset.range N, omega M

theorem jsp87OmegaSum_cast (N : ℕ) :
    (jsp87OmegaSum N : ℝ) = ∑ M ∈ Finset.range N, ((omega M : ℕ) : ℝ) := by
  simp only [jsp87OmegaSum, Int.cast_sum]
  push_cast
  rfl

theorem jsp87OmegaSum_zero : jsp87OmegaSum 0 = 0 := by simp [jsp87OmegaSum]

theorem jsp87OmegaSum_succ (N : ℕ) : jsp87OmegaSum (N + 1) = jsp87OmegaSum N + omega N := by
  simp only [jsp87OmegaSum, Finset.sum_range_succ]

theorem jsp87IntPart_zero : jsp87IntPart 0 = 0 := by simp [jsp87IntPart]

/-- **THE MEAN IDENTITY FOR THE 2-ADIC PREFIX.**  `∑_{M<N} I M = I N − W N`:
the sum of all the short prefixes is the long prefix minus the plain `ω`-sum.
This is the discrete integration-by-parts companion of
`jsp87IntPart_succ`. -/
theorem jsp87_sum_intPart (N : ℕ) :
    (∑ M ∈ Finset.range N, (jsp87IntPart M : ℝ)) = (jsp87IntPart N : ℝ) - (jsp87OmegaSum N : ℝ) := by
  induction N with
  | zero => simp [jsp87IntPart_zero, jsp87OmegaSum_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, jsp87IntPart_succ, jsp87OmegaSum_succ]
    push_cast
    ring

/-- `2^N · S − I N = θ N`, for every `N ≥ 0`. -/
theorem scaled_sub_intPart_eq_carry (N : ℕ) :
    (2 : ℝ) ^ N * jsp87Series - (jsp87IntPart N : ℝ) = jsp87Carry N := by
  rcases Nat.eq_zero_or_pos N with h0 | h1
  · subst h0
    rw [pow_zero, one_mul, jsp87IntPart_zero, jsp87Carry_zero]
    simp
  · have hd := jsp87_scaled_decomposition N (by omega)
    rw [jsp87Carry]
    linarith

/-- **THE MEAN IDENTITY.**  For every `N`,

`∑_{M<N} θ M = W N + θ N − S`,

i.e. the mean of the carries up to `N` is the `ω`-prefix plus the last carry
minus the series.  This is the exact quantitative bridge between the
`ω`-digits and the carries, and it is the *only* place the two families meet. -/
theorem jsp87_sum_carry (N : ℕ) :
    (∑ M ∈ Finset.range N, (jsp87Carry M : ℝ)) = (jsp87OmegaSum N : ℝ) + jsp87Carry N
      - jsp87Series := by
  have hkey : ∀ M : ℕ, (jsp87Carry M : ℝ) = (2 : ℝ) ^ M * jsp87Series
      - (jsp87IntPart M : ℝ) := by
    intro M
    have ht : jsp87Tail M = jsp87Series - ∑ i ∈ Finset.range M, jsp87Term i := by
      have h := jsp87_series_eq_sum_add_tail M
      linarith
    rcases Nat.eq_zero_or_pos M with h0 | h1
    · subst h0
      rw [jsp87Carry, pow_zero, one_mul, ht, jsp87IntPart_zero]
      ring
    · have h2 := jsp87_sum_range_eq_intPart M (by omega)
      have h3 : (2 : ℝ) ^ M * (∑ i ∈ Finset.range M, jsp87Term i) = (jsp87IntPart M : ℝ) := by
        rw [h2]
        field_simp
      rw [jsp87Carry, ht, ← h3]
      ring
  have hgeo : (∑ M ∈ Finset.range N, (2 : ℝ) ^ M) = (2 : ℝ) ^ N - 1 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [sum_congr_range hkey N]
  have hmul : (∑ M ∈ Finset.range N, ((2 : ℝ) ^ M * jsp87Series) : ℝ)
      = (∑ M ∈ Finset.range N, (2 : ℝ) ^ M) * jsp87Series :=
    (Finset.sum_mul (s := Finset.range N) (f := fun M => (2 : ℝ) ^ M)
      (a := jsp87Series)).symm
  calc (∑ M ∈ Finset.range N, ((2 : ℝ) ^ M * jsp87Series - (jsp87IntPart M : ℝ)))
      = jsp87Series * (∑ M ∈ Finset.range N, (2 : ℝ) ^ M)
          - (∑ M ∈ Finset.range N, (jsp87IntPart M : ℝ)) := by
        rw [Finset.sum_sub_distrib, hmul, mul_comm]
    _ = jsp87Series * ((2 : ℝ) ^ N - 1) - ((jsp87IntPart N : ℝ) - (jsp87OmegaSum N : ℝ)) := by
        rw [hgeo, jsp87_sum_intPart]
    _ = (jsp87OmegaSum N : ℝ) + jsp87Carry N - jsp87Series := by
        have hsc := scaled_sub_intPart_eq_carry N
        linarith

/-- **The sum of the carry excesses is at most the mean identity.** -/
theorem jsp87_sum_carryExcess_le (N : ℕ) :
    (∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ)) ≤ (jsp87OmegaSum N : ℝ) + jsp87Carry N
      - jsp87Series := by
  have h := jsp87_sum_carry N
  have hstep : ∀ M : ℕ, (jsp87Carry M : ℝ) = (jsp87CarryExcess M : ℝ)
      + Int.fract (jsp87Carry M) := by
    intro M
    have := jsp87Carry_excess_fract M
    linarith
  have h2 : (∑ M ∈ Finset.range N, (jsp87Carry M : ℝ))
      = ∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ)
        + ∑ M ∈ Finset.range N, Int.fract (jsp87Carry M) :=
    (sum_congr_range hstep N).trans Finset.sum_add_distrib
  rw [h2] at h
  have h3 : (0 : ℝ) ≤ ∑ M ∈ Finset.range N, Int.fract (jsp87Carry M) := by
    positivity
  linarith

/-- **... and at least the mean identity minus `N`.** -/
theorem jsp87_sum_carryExcess_ge (N : ℕ) :
    (jsp87OmegaSum N : ℝ) + jsp87Carry N - jsp87Series - (N : ℝ)
      ≤ ∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ) := by
  have h := jsp87_sum_carry N
  have hstep : ∀ M : ℕ, (jsp87Carry M : ℝ) = (jsp87CarryExcess M : ℝ)
      + Int.fract (jsp87Carry M) := by
    intro M
    have := jsp87Carry_excess_fract M
    linarith
  have h2 : (∑ M ∈ Finset.range N, (jsp87Carry M : ℝ))
      = ∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ)
        + ∑ M ∈ Finset.range N, Int.fract (jsp87Carry M) :=
    (sum_congr_range hstep N).trans Finset.sum_add_distrib
  rw [h2] at h
  have hlt : ∀ M ∈ Finset.range N, Int.fract (jsp87Carry M) < 1 := by
    intro M _
    have := jsp87Carry_excess_fract M
    have := jsp87Carry_excess_lt_one M
    linarith
  have hsum : (∑ M ∈ Finset.range N, Int.fract (jsp87Carry M) : ℝ)
      ≤ ∑ _M ∈ Finset.range N, (1 : ℝ) :=
    Finset.sum_le_sum fun M hM => (hlt M hM).le
  rw [Finset.sum_const, Finset.card_range] at hsum
  norm_num at hsum
  linarith

/-- **THE CARRY EXCESS IS LOGARITHMIC ON AVERAGE.**  For `1 ≤ N`,

`∑_{M<N} ⌊θ M⌋ ≤ W N + log₂ N + log₂ e`. -/
theorem jsp87_sum_carryExcess_le_logb {N : ℕ} (hN : 1 ≤ N) :
    (∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ)) ≤ (jsp87OmegaSum N : ℝ)
      + (Real.log N + 1) / Real.log 2 := by
  have h := jsp87_sum_carryExcess_le N
  have h2 := jsp87Carry_le_logb hN
  have h0 := jsp87Series_nonneg
  linarith

/-! ## 3. The digit count -/

/-- **The bookkeeping also holds at `N = 0`.** -/
theorem jsp87_digit_bookkeeping_zero :
    jsp87Digit 0 = omega 0 + jsp87CarryExcess 1 - 2 * jsp87CarryExcess 0 := by
  have hz0 : jsp87CarryExcess 0 = 0 :=
    (jsp87CarryExcess_eq_zero_iff.mpr jsp87Carry_zero_lt_one)
  have hp0 : (2 : ℝ) ^ (0 + 1) = 2 := by norm_num
  have hp1 : (2 : ℝ) ^ 0 = 1 := by norm_num
  simp only [jsp87Digit, jsp87CarryExcess, hz0, jsp87Carry_zero, jsp87Carry_one, hp0, hp1,
    omega_zero]
  ring

theorem jsp87_digit_bookkeeping' (M : ℕ) :
    jsp87Digit M = omega M + jsp87CarryExcess (M + 1) - 2 * jsp87CarryExcess M := by
  rcases Nat.eq_zero_or_pos M with h0 | h1
  · exact h0 ▸ jsp87_digit_bookkeeping_zero
  · exact jsp87_digit_bookkeeping (by omega)

theorem jsp87_digit_nonneg (M : ℕ) : 0 ≤ jsp87Digit M := by
  rcases jsp87Digit_mem M with h | h
  · rw [h]
  · rw [h]; norm_num

theorem jsp87_digit_toNat_cast (M : ℕ) : ((jsp87Digit M).toNat : ℤ) = jsp87Digit M := by
  rcases jsp87Digit_mem M with h | h <;> rw [h] <;> rfl

/-- **THE DIGIT COUNT** `D N = ∑_{M<N} d M`: how many `1`s occur in the first
`N` binary digits of the Erdős series. -/
noncomputable def jsp87DigitCount (N : ℕ) : ℕ := ∑ M ∈ Finset.range N, (jsp87Digit M).toNat

theorem jsp87_digitCount_cast (N : ℕ) :
    (jsp87DigitCount N : ℝ) = ∑ M ∈ Finset.range N, (jsp87Digit M : ℝ) := by
  rw [jsp87DigitCount, Nat.cast_sum]
  refine sum_congr_range (fun M => ?_) N
  exact congrArg (fun z : ℤ => (z : ℝ)) (jsp87_digit_toNat_cast M)

/-- **A digit count is at most the number of digits.** -/
theorem jsp87_digitCount_le (N : ℕ) : jsp87DigitCount N ≤ N := by
  rw [jsp87DigitCount]
  have hbound : ∀ M ∈ Finset.range N, (jsp87Digit M).toNat ≤ 1 := by
    intro M _
    rcases jsp87Digit_mem M with h | h <;> rw [h] <;> norm_num
  have h := Finset.sum_le_sum hbound
  rw [Finset.sum_const, Finset.card_range] at h
  norm_num at h
  exact h

/-- **THE DIGIT-COUNT IDENTITY.**  For every `N`,

`(jsp87DigitCount N : ℝ) = W N + c N − ∑_{M<N} c M`,

i.e. the number of `1`s in the first `N` binary digits of the series is the
`ω`-prefix, plus the carry excess at `N`, minus the accumulated carry excess.
**This is the first exact formula relating the binary digit string to the
`ω`-values and to the carries.** -/
theorem jsp87_digitCount_eq (N : ℕ) :
    (jsp87DigitCount N : ℝ) = (jsp87OmegaSum N : ℝ) + (jsp87CarryExcess N : ℝ)
      - ∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ) := by
  have hnz : (jsp87DigitCount N : ℝ) = ∑ M ∈ Finset.range N, (jsp87Digit M : ℝ) :=
    jsp87_digitCount_cast N
  have hsumR : (∑ M ∈ Finset.range N, (jsp87Digit M : ℝ))
      = (jsp87OmegaSum N : ℝ) + (∑ M ∈ Finset.range N, (jsp87CarryExcess (M + 1) : ℝ))
        - 2 * (∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ)) := by
    have h1 : (∑ M ∈ Finset.range N, (jsp87Digit M : ℝ))
        = ∑ M ∈ Finset.range N, (((omega M : ℕ) : ℝ) + (jsp87CarryExcess (M + 1) : ℝ)
            - 2 * (jsp87CarryExcess M : ℝ)) := by
      refine sum_congr_range (M := ℝ) (fun M => ?_) N
      rw [jsp87_digit_bookkeeping' M]
      push_cast
      ring
    have h2 : (∑ M ∈ Finset.range N, (2 * (jsp87CarryExcess M : ℝ)) : ℝ)
        = 2 * (∑ M ∈ Finset.range N, (jsp87CarryExcess M : ℝ)) := by
      rw [Finset.mul_sum]
    rw [h1, jsp87OmegaSum_cast, Finset.sum_sub_distrib, Finset.sum_add_distrib, h2] <;> ring
  have hsucc' : (∑ M ∈ Finset.range N, (jsp87CarryExcess (M + 1) : ℝ))
      = (∑ M ∈ Finset.range (N + 1), (jsp87CarryExcess M : ℝ))
        - (jsp87CarryExcess 0 : ℝ) := by
    have h := Finset.sum_range_succ' (fun k : ℕ => (jsp87CarryExcess k : ℝ)) N
    linarith
  have hz0 : jsp87CarryExcess 0 = 0 :=
    (jsp87CarryExcess_eq_zero_iff.mpr jsp87Carry_zero_lt_one)
  rw [hnz, hsumR, hsucc', hz0, Finset.sum_range_succ]
  ring

/-- **THE DIGIT COUNT AS THE PARTIAL SUM OF THE DOUBLING ORBIT.**  For every
`N`,

`D N + fract (2^N S) = S + ∑_{M<N} fract (2^M S)`,

i.e. the number of `1`s in the first `N` binary digits of the series is, up to
`S` and the last fractional part, the *partial sum of the fractional parts of
the rescaled series* — the classical "binary digits are the differences of the
doubling orbit", summed.  Mathlib has no statement about the base-`2`
expansion of a real, so this is from scratch. -/
theorem jsp87_digitCount_eq_fractSum (N : ℕ) :
    (jsp87DigitCount N : ℝ) + Int.fract ((2 : ℝ) ^ N * jsp87Series)
      = jsp87Series + ∑ M ∈ Finset.range N, Int.fract ((2 : ℝ) ^ M * jsp87Series) := by
  have h0f : Int.fract jsp87Series = jsp87Series := by
    have h := Int.self_sub_fract jsp87Series
    rw [jsp87_floor_S_zero, Int.cast_zero] at h
    linarith
  have hsucc' : (∑ M ∈ Finset.range N, Int.fract ((2 : ℝ) ^ (M + 1) * jsp87Series) : ℝ)
      = (∑ M ∈ Finset.range (N + 1), Int.fract ((2 : ℝ) ^ M * jsp87Series) : ℝ)
        - Int.fract jsp87Series := by
    have h := Finset.sum_range_succ' (fun k : ℕ => Int.fract ((2 : ℝ) ^ k * jsp87Series)) N
    norm_num at h
    linarith
  have hmul : (∑ M ∈ Finset.range N, ((2 : ℝ) * Int.fract ((2 : ℝ) ^ M * jsp87Series)) : ℝ)
      = 2 * (∑ M ∈ Finset.range N, Int.fract ((2 : ℝ) ^ M * jsp87Series) : ℝ) :=
    (Finset.mul_sum (s := Finset.range N) (f := fun M => Int.fract ((2 : ℝ) ^ M * jsp87Series))
      (a := (2 : ℝ))).symm
  rw [jsp87_digitCount_cast, sum_congr_range (fun M => jsp87_digit_eq_fract M) N,
    Finset.sum_sub_distrib, hmul, hsucc', h0f, Finset.sum_range_succ]
  ring

/-- **The digit count is bounded below by `S − fract (2^N S)`.** -/
theorem jsp87_digitCount_ge_sub_fract (N : ℕ) :
    jsp87Series - Int.fract ((2 : ℝ) ^ N * jsp87Series) ≤ (jsp87DigitCount N : ℝ) := by
  have h := jsp87_digitCount_eq_fractSum N
  have h1 : Int.fract ((2 : ℝ) ^ N * jsp87Series) < 1 := by
    have h := Int.self_sub_fract ((2 : ℝ) ^ N * jsp87Series)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ N * jsp87Series)
    linarith
  have h2 : (0 : ℝ) ≤ ∑ M ∈ Finset.range N, Int.fract ((2 : ℝ) ^ M * jsp87Series) := by
    positivity
  linarith

/-! ## 4. Eventual periodicity forces a linear digit count -/

/-- **Periodicity makes the digit string `t`-constant after `M`.** -/
theorem jsp87_digit_eq_of_periodic {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) (q j : ℕ) :
    jsp87Digit (M + q * t + j) = jsp87Digit (M + j) := by
  induction q generalizing j with
  | zero => simp
  | succ q ih =>
    calc jsp87Digit (M + (q + 1) * t + j) = jsp87Digit ((M + q * t + j) + t) := by
          have hq : M + (q + 1) * t + j = (M + q * t + j) + t := by ring
          rw [hq]
      _ = jsp87Digit (M + q * t + j) := hper _ (by omega)
      _ = jsp87Digit (M + j) := ih j

/-- **The number of `1`-digits in one period,** `s = ∑_{j<t} d (M+j)`. -/
noncomputable def jsp87PeriodOnes (M t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, (jsp87Digit (M + j) : ℝ)

/-- A generic bound of a digit sum over `Finset.range n` by a constant `1`. -/
theorem jsp87_sum_digit_le (n : ℕ) :
    (∑ j ∈ Finset.range n, (jsp87Digit j : ℝ)) ≤ (n : ℝ) := by
  have hlt : ∀ j ∈ Finset.range n, (jsp87Digit j : ℝ) ≤ 1 := by
    intro j _
    rcases jsp87Digit_mem j with h | h <;> rw [h] <;> norm_num
  have h := Finset.sum_le_sum hlt
  rw [Finset.sum_const, Finset.card_range] at h
  norm_num at h
  exact h

/-- A digit sum over a *shifted* range is still bounded by the number of terms. -/
theorem jsp87_sum_digit_shift_le (M n : ℕ) :
    (∑ j ∈ Finset.range n, (jsp87Digit (M + j) : ℝ)) ≤ (n : ℝ) := by
  have hlt : ∀ j ∈ Finset.range n, (jsp87Digit (M + j) : ℝ) ≤ 1 := by
    intro j _
    rcases jsp87Digit_mem (M + j) with h | h <;> rw [h] <;> norm_num
  have h := Finset.sum_le_sum hlt
  rw [Finset.sum_const, Finset.card_range] at h
  norm_num at h
  exact h

theorem jsp87PeriodOnes_bounds (M t : ℕ) :
    0 ≤ jsp87PeriodOnes M t ∧ jsp87PeriodOnes M t ≤ (t : ℝ) := by
  have hmem : ∀ j ∈ Finset.range t, (0 : ℝ) ≤ (jsp87Digit (M + j) : ℝ) := by
    intro j _
    exact_mod_cast jsp87_digit_nonneg _
  have h1 : (0 : ℝ) ≤ ∑ j ∈ Finset.range t, (jsp87Digit (M + j) : ℝ) :=
    Finset.sum_nonneg hmem
  have hlt : ∀ j ∈ Finset.range t, (jsp87Digit (M + j) : ℝ) ≤ 1 := by
    intro j _
    rcases jsp87Digit_mem (M + j) with h | h <;> rw [h] <;> norm_num
  have h2 : (∑ j ∈ Finset.range t, (jsp87Digit (M + j) : ℝ)) ≤ (t : ℝ) := by
    have h := Finset.sum_le_sum hlt
    rw [Finset.sum_const, Finset.card_range] at h
    norm_num at h
    exact h
  exact ⟨h1, h2⟩


/-- **A full period contributes exactly `s` ones.** -/
theorem jsp87_sum_digit_period_block {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) (q : ℕ) :
    (∑ j ∈ Finset.range (q * t), (jsp87Digit (M + j) : ℝ)) = (q : ℝ) * jsp87PeriodOnes M t := by
  induction q with
  | zero => simp [jsp87PeriodOnes]
  | succ q ih =>
    have hsplit : (∑ j ∈ Finset.range ((q + 1) * t), (jsp87Digit (M + j) : ℝ))
        = (∑ j ∈ Finset.range (q * t), (jsp87Digit (M + j) : ℝ))
          + (∑ i ∈ Finset.range t, (jsp87Digit (M + (q * t + i)) : ℝ)) := by
      have h : (q + 1) * t = q * t + t := by ring
      rw [h, Finset.sum_range_add]
    have hblk : (∑ i ∈ Finset.range t, (jsp87Digit (M + (q * t + i)) : ℝ))
        = ∑ i ∈ Finset.range t, (jsp87Digit (M + i) : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hh := jsp87_digit_eq_of_periodic ht hM hper q i
      rw [Nat.add_assoc] at hh
      exact congrArg (fun z : ℤ => (z : ℝ)) hh
    rw [hsplit, hblk, ih]
    simp only [jsp87PeriodOnes]
    have he : (q : ℝ) * (∑ x ∈ Finset.range t, (jsp87Digit (M + x) : ℝ))
        + (∑ x ∈ Finset.range t, (jsp87Digit (M + x) : ℝ))
        = ((q + 1 : ℕ) : ℝ) * (∑ x ∈ Finset.range t, (jsp87Digit (M + x) : ℝ)) := by
      push_cast
      ring
    rw [he]

/-- **THE DIGIT COUNT SPLITS INTO FULL PERIODS PLUS A REMAINDER.** -/
theorem jsp87_digitCount_split {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) (q r : ℕ) :
    (∑ n ∈ Finset.range (M + q * t + r), (jsp87Digit n : ℝ))
      = (jsp87DigitCount M : ℝ) + (q : ℝ) * jsp87PeriodOnes M t
        + ∑ j ∈ Finset.range r, (jsp87Digit (M + j) : ℝ) := by
  have h1 : (∑ n ∈ Finset.range (M + q * t + r), (jsp87Digit n : ℝ))
      = (∑ n ∈ Finset.range M, (jsp87Digit n : ℝ))
        + ∑ j ∈ Finset.range (q * t + r), (jsp87Digit (M + j) : ℝ) := by
    have h : M + q * t + r = M + (q * t + r) := by ring
    rw [h, Finset.sum_range_add]
  have h2 : (∑ j ∈ Finset.range (q * t + r), (jsp87Digit (M + j) : ℝ))
      = (∑ j ∈ Finset.range (q * t), (jsp87Digit (M + j) : ℝ))
        + ∑ j ∈ Finset.range r, (jsp87Digit (M + (q * t + j)) : ℝ) :=
    Finset.sum_range_add _ _ _
  have h3 : (∑ j ∈ Finset.range r, (jsp87Digit (M + (q * t + j)) : ℝ))
      = ∑ j ∈ Finset.range r, (jsp87Digit (M + j) : ℝ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hh := jsp87_digit_eq_of_periodic ht hM hper q j
    rw [Nat.add_assoc] at hh
    exact congrArg (fun z : ℤ => (z : ℝ)) hh
  have h4 : (jsp87DigitCount M : ℝ) = ∑ n ∈ Finset.range M, (jsp87Digit n : ℝ) :=
    jsp87_digitCount_cast M
  rw [h1, h2, h3, ← h4, jsp87_sum_digit_period_block ht hM hper] <;> try ring

/-- **THE DIGIT-COUNT PERIODICITY THEOREM.**  If the binary digit string of the
Erdős series is `t`-periodic from `M` (`t > 0`), then for every `N ≥ M`

`D N = D M + q·s + ρ`,  with `N = M + q·t + r`, `r < t`,
`s = ∑_{j<t} d (M+j)` the number of `1`s in one period, and `0 ≤ ρ ≤ r`; in
particular

**`D M ≤ D N ≤ D M + (N − M) + t`.**

So an eventually periodic digit string has a digit count of *exactly* linear
growth rate, with a density in `[0, 1]`.  Mathlib has no statement about the
base-`2` expansion of a real at all. -/
theorem jsp87_digitCount_periodic_bounds {t M : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ∀ N, M ≤ N → (jsp87DigitCount M : ℝ) ≤ (jsp87DigitCount N : ℝ)
      ∧ (jsp87DigitCount N : ℝ) ≤ (jsp87DigitCount M : ℝ) + (N : ℝ) + (t : ℝ) := by
  intro N hN
  obtain ⟨q, r, hr, hN'⟩ : ∃ q r : ℕ, r < t ∧ N = M + q * t + r :=
    ⟨(N - M) / t, (N - M) % t, Nat.mod_lt _ ht, by
      have hback : (N : ℕ) = M + (N - M) := (Nat.add_sub_of_le hN).symm
      have hediv : (N - M : ℕ) = (N - M) / t * t + (N - M) % t := by
        have h := Nat.mod_add_div (N - M) t
        linarith
      calc (N : ℕ) = M + (N - M) := hback
        _ = M + (N - M) / t * t + (N - M) % t := by omega⟩
  have hfull := jsp87_digitCount_split ht hM hper q r
  have hs := jsp87PeriodOnes_bounds M t
  have hρ0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range r, (jsp87Digit (M + j) : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro j _
    exact_mod_cast jsp87_digit_nonneg _
  have hρle : (∑ j ∈ Finset.range r, (jsp87Digit (M + j) : ℝ)) ≤ (r : ℝ) :=
    jsp87_sum_digit_shift_le M r
  have hrt : (r : ℝ) ≤ (t : ℝ) := by
    have hrr : r ≤ t := by omega
    exact_mod_cast hrr
  have hq0 : (0 : ℕ) ≤ q * t := Nat.zero_le _
  have hNsplit : (N : ℝ) = (M : ℝ) + (q : ℝ) * (t : ℝ) + (r : ℝ) := by
    rw [hN']
    push_cast
    ring
  have hmain : (jsp87DigitCount N : ℝ) = (jsp87DigitCount M : ℝ) + (q : ℝ) * jsp87PeriodOnes M t
      + ∑ j ∈ Finset.range r, (jsp87Digit (M + j) : ℝ) := by
    rw [jsp87_digitCount_cast, hN', hfull]
  have hqpos : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hqs0 : (0 : ℝ) ≤ (q : ℝ) * jsp87PeriodOnes M t := mul_nonneg hqpos hs.1
  rw [hmain]
  constructor
  · linarith
  · have hqr : (N : ℝ) - (M : ℝ) = (q : ℝ) * (t : ℝ) + (r : ℝ) := by linarith [hNsplit]
    have hqs : (q : ℝ) * jsp87PeriodOnes M t ≤ (q : ℝ) * (t : ℝ) :=
      mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg q)
    linarith

/-- **RATIONALITY FORCES A DIGIT COUNT OF LINEAR GROWTH.**  If `S = a/b` with
`b > 0` then for some `M` and some `t ≥ 1`,

`D M ≤ D N ≤ D M + N + t` for every `N ≥ M`:

**the binary digit string of a rational has a digit count growing exactly
linearly.**  This is the *rate* companion of round 41's
`jsp87_digit_eventuallyPeriodic` (a *period* statement) and of round 46's
`jsp87_frac_scaled_eq_block` (a *value* statement). -/
theorem jsp87Series_rational_imp_digitCount_linear {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ (M t : ℕ), 1 ≤ M ∧ 0 < t ∧ (∀ n : ℕ, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
      ∧ (∀ N : ℕ, M ≤ N → (jsp87DigitCount M : ℝ) ≤ (jsp87DigitCount N : ℝ)
          ∧ (jsp87DigitCount N : ℝ) ≤ (jsp87DigitCount M : ℝ) + (N : ℝ) + (t : ℝ)) := by
  obtain ⟨t, M, ht, hM1, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  exact ⟨M, t, hM1, ht, hper, jsp87_digitCount_periodic_bounds ht hM1 hper⟩

/-- **THE DIGIT-DENSITY CRITERION.**  If the digit count of the Erdős series
is bounded by no linear function of `N` along an unbounded sequence — the
formal statement being that `∀ C > 0, ∀ K, ∃ N ≥ K, D N > C · N` — then `S` is
irrational.  This is the *fifth* aperiodicity criterion of the development,
phrased in terms of the **rate** of the digit string rather than its periods. -/
theorem jsp87Series_irrational_of_digitDensity_not_bounded
    (h : ∀ (C : ℝ), 0 < C → ∀ (K : ℕ), ∃ N : ℕ, K ≤ N ∧ (jsp87DigitCount N : ℝ) > C * (N : ℝ)) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  obtain ⟨M, t, hM1, ht, hper, hbounds⟩ :=
    jsp87Series_rational_imp_digitCount_linear hden (by rw [← hq, Rat.cast_def])
  have htwo : (2 : ℝ) > 0 := by norm_num
  obtain ⟨N, hN1, hNbig⟩ := h 2 htwo (M + t)
  have hN1' : M ≤ N := le_trans (Nat.le_add_right M t) hN1
  have hN2 : t ≤ N := le_trans (Nat.le_add_left t M) hN1
  obtain ⟨hlo, hhi⟩ := hbounds N hN1'
  have hDM : (0 : ℝ) ≤ (jsp87DigitCount M : ℝ) := by
    have hx : (0 : ℕ) ≤ jsp87DigitCount M := Nat.zero_le _
    exact_mod_cast hx
  have hDMle : (jsp87DigitCount M : ℝ) ≤ (M : ℝ) := by
    have hx := jsp87_digitCount_le M
    exact_mod_cast hx
  have h1 : (0 : ℝ) < (N : ℝ) := by
    have hNpos : (0 : ℕ) < N := lt_of_lt_of_le hM1 hN1'
    exact_mod_cast hNpos
  have h2 : (jsp87DigitCount M : ℝ) + (N : ℝ) + (t : ℝ) ≤ 2 * (N : ℝ) := by
    have h3 : (M : ℝ) + (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  linarith

end JSP87
