/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Basic
import JSPProblem.Lambert
import JSPProblem.Convergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# JSP-000087 : the Erdős series of the `ω`-function

## The problem

`ω n` is the number of *distinct* prime factors of `n`.  Erdős
(*On arithmetical properties of Lambert series*, J. Indian Math. Soc. **12**
(1948), 63–66) asked whether the generating series

`∑ n ≥ 1, ω(n) / 2 ^ n`

is irrational.  K. Pratt (*The irrationality of a prime factor series under a
prime tuples conjecture*, arXiv:2409.15185) settles it **conditionally**, under a
suitably uniform form of the prime `k`-tuples conjecture.  The catalog record for
JSP-000087 lists the status as *Solved* with *Lean proof: No*.

## What is formalised here

`JSPProblem/Basic.lean` proves the arithmetic core of `ω` (monotonicity, the
`±1` behaviour of dividing out a prime, additivity on coprime products, and the
growth bound `2 ^ ω n ≤ n`).

`JSPProblem/Lambert.lean` proves the identity `ω n = ∑_{p ≤ n} [p prime ∧ p ∣ n]`
that is the first step of the Lambert-series reduction
`∑_n ω(n) x^{n+1} = ∑_p x^p / (1 - x^p)`.

`JSPProblem/Convergence.lean` proves that the series exists (sub-step A of the
acceptance blocker list), `JSPProblem/LambertSeries.lean` proves the Lambert
rearrangement at a finite truncation, and `JSPProblem/LambertIdentity.lean`
completes the reduction in the limit (sub-step B):

* `jsp87_lambert` : `jsp87Series = ∑' p, (if p.Prime then 1 / (2^(p+1) - 2) else 0)`;
* `jsp87_lambert_classic` : `∑' p, (if p.Prime then 1 / (2^p - 1) else 0) = 2 * jsp87Series`;
* `jsp87_lambert_reduction` : `∑' n, ω(n) / 2^n = ∑' p prime, 1 / (2^p - 1)`.

This file fixes the *statement* of the headline theorem and records, as proved
lemmas, the parts of the reduction that are within reach of Mathlib.

## What is still missing

The irrationality of `jsp87Series` is **not** proved here.  It is a research-level
result (conditional on a uniform prime-`k`-tuples conjecture in the published
literature), far beyond a Mathlib formalization at this time.  `jsp_000087_main`
is therefore deliberately *not* declared: the acceptance gate requires it to be a
proved theorem, and emitting a weakened statement under that name would
misrepresent the headline result.
-/

namespace JSP87

/-- The Erdős series of JSP-000087: `∑ n ≥ 1, ω(n) / 2 ^ n`. -/
noncomputable def jsp87Series : ℝ := ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- Each summand of `jsp87Series` is nonnegative. -/
theorem jsp87Series_nonneg : 0 ≤ jsp87Series := by
  refine tsum_nonneg fun n => ?_
  positivity

open scoped ENNReal
open Filter

/-- The first terms of the Erdős series, checked exactly:
`ω 0 = ω 1 = 0` and `ω 2 = ω 3 = ω 4 = 1`, so the partial sum over `n < 5` is
`1/8 + 1/16 + 1/32 = 7/32`. -/
theorem jsp87Series_partial_sum_five :
    (∑ n ∈ Finset.range 5, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) = 7 / 32 := by
  have h2 : omega 2 = 1 := by native_decide
  have h3 : omega 3 = 1 := by native_decide
  have h4 : omega 4 = 1 := by native_decide
  norm_num [h2, h3, h4, omega_zero, omega_one, Finset.sum_range_succ]

/-- **The Erdős series is bracketed: `7/32 ≤ jsp87Series ≤ 1`.**

The lower endpoint is the exact partial sum over `n < 5`; the upper endpoint
comes from dominating the summand by `n * 2^{-(n+1)}`, whose sum is `1`. -/
theorem jsp87Series_bounds : 7 / 32 ≤ jsp87Series ∧ jsp87Series ≤ 1 := by
  constructor
  · refine (sum_range_le_jsp87Series 5 (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))).trans' ?_
    rw [jsp87Series_partial_sum_five]
  · exact jsp87Series_le_one

end JSP87
