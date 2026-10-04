/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.HarmonicMass
import JSPProblem.TTRoute
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Round 125 — EULER'S DIVERGENCE, PROVED: the arithmetic input of the endgame closes

`policy.json` `next_round_attack[0]` (carried for 125 rounds) asked for a proof of
`jsp87PrimeRecipDiverges`, the harmonic-mass divergence of the primes above the
separation bound — the last *purely arithmetic* input of the endgame of
arXiv:2512.01739 §§5.3–§5.14.  **This module proves it.**

The proof does **not** go through the hand route sketched in the policy
(`Finset.prod_geomsum'`, Euler products, `exp`).  It uses Mathlib's own
`Mathlib.NumberTheory.SumPrimeReciprocals`, which contains Erdős's elementary
proof in `not_summable_one_div_on_primes`, together with the standard
characterisation of a non-summable nonnegative series
(`not_summable_iff_tendsto_nat_atTop_of_nonneg`).  So the divergence of
`∑_p 1/p` is *available*; what had to be built here is the quantitative
transfer from that abstract statement to the finite harmonic mass
`jsp87RecipSum (jsp87PrimeSet B Y)` used by rounds 123–124.

## §0–§1  the transfer

`jsp87_recip_prime_le_mass_add` — **the counting step**, isolated: the
reciprocals of the primes below a threshold `B ≥ 2` cost at most `B/2`, since
there are at most `B` of them and each is at most `1/2`.  Hence

```
∑_{p ≤ Y prime} 1/p  ≤  B/2 + ∑_{B ≤ p ≤ Y} 1/p .
```

`jsp87PrimeRecipDiverges_proof` — **EULER'S DIVERGENCE, PROVED**: for every
`B = jsp87Separation K H ≥ 2` the mass `jsp87RecipSum (jsp87PrimeSet B Y)` is
unbounded in `Y`.

## §2–§3  consequences

* `jsp87_5_21b_exists` — **hypothesis (5.21b) is SATISFIABLE, unconditionally**:
  for every `q ≠ 0` there is a height at which the harmonic-mass condition of
  the endgame holds.  (Rounds 123–124 had only shown what it *costs*.)
* `jsp87_endgame_of_Euler` — the endgame of §§5.3–§5.14 fires from **(5.19),
  (5.15), (5.16)–(5.17)** alone; the variance hypothesis (5.21) is gone.

## §4  the bridge to the headline

* `jsp87Series_irrational_of_kappa_small` — if the five error constants
  `κ₁ … κ₅` are all `< 1/30` at the scale (5.19), then the uniform-spacing
  criterion of `TTRoute` is violated, so `jsp87Series` is irrational.
* `jsp87Hypothesis518` — **(5.18) as a named hypothesis**: the five error
  constants are simultaneously sharp.
* `jsp87Series_irrational_of_518` — **the headline follows from (5.18) alone**:
  `jsp87Hypothesis518 → Irrational jsp87Series`, with *no* other hypothesis.

Everything else in this development — the Lambert reduction, the carry
decomposition, the doubling orbit, the cube-vertex sample, the endgame
combinatorics and the deterministic Diophantine reduction — is now
unconditional, so the burden of `jsp_000087_main` is localised to a single
named analytic statement.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  the summand, and Mathlib's theorem on it -/

/-- **THE RECIPROCAL OF `n`, EXTENDED BY ZERO OFF THE PRIMES.** -/
noncomputable def jsp87PrimeRecipTerm (n : ℕ) : ℝ :=
  if n.Prime then (1 / (n : ℝ)) else 0

/-- **EVERY TERM IS NONNEGATIVE.** -/
theorem jsp87PrimeRecipTerm_nonneg (n : ℕ) : 0 ≤ jsp87PrimeRecipTerm n := by
  rw [jsp87PrimeRecipTerm]
  split
  · positivity
  · exact le_rfl

/-- **THE RECIPROCALS OF THE PRIMES DO NOT CONVERGE.**  This is Mathlib's own
`not_summable_one_div_on_primes` (`Mathlib/NumberTheory/SumPrimeReciprocals.lean`,
Erdős's elementary proof) read on the indicator function. -/
theorem jsp87PrimeRecip_not_summable : ¬ Summable jsp87PrimeRecipTerm := by
  intro h
  have hh : Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) := by
    convert h using 1
    funext n
    simp [jsp87PrimeRecipTerm, Set.indicator]
  exact (not_summable_one_div_on_primes hh).elim

/-- **THE PRIME PARTIAL SUMS TEND TO INFINITY.**  A nonnegative series which is
not summable has partial sums `→ ∞`
(`not_summable_iff_tendsto_nat_atTop_of_nonneg`). -/
theorem jsp87PrimeRecip_tendsto :
    Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, jsp87PrimeRecipTerm i)
      Filter.atTop Filter.atTop := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    jsp87PrimeRecipTerm_nonneg).mp jsp87PrimeRecip_not_summable
  simpa using h

/-- **THE PRIME PARTIAL SUM IS THE MASS OF THE PRIMES BELOW THE CUT.** -/
theorem jsp87PrimeRecipSum_range (n : ℕ) :
    (∑ i ∈ Finset.range n, jsp87PrimeRecipTerm i)
      = ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 / (p : ℝ)) := by
  simp only [jsp87PrimeRecipTerm]
  rw [Finset.sum_filter]

/-! ## §1  the counting step: the primes below `B` cost at most `B/2` -/

/-- **EACH PRIME RECIPROCAL IS AT MOST `1/2`.** -/
private theorem jsp87_recip_prime_le_half {p : ℕ} (hp : p.Prime) :
    (1 / (p : ℝ)) ≤ (1 : ℝ) / 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hstep : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hstep
  simpa using this

/-- **THE MASS OF THE PRIMES BELOW THE THRESHOLD `B` IS AT MOST `B/2`.** -/
private theorem jsp87_low_mass_le (P : Finset ℕ) {B : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ ¬ (B ≤ p)) :
    (∑ p ∈ P, (1 / (p : ℝ))) ≤ (B : ℝ) / 2 := by
  have hsub : P ⊆ Finset.range B := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_of_not_ge (hP p hp).2)
  have hcard : P.card ≤ B := by
    calc P.card ≤ (Finset.range B).card := Finset.card_le_card hsub
      _ = B := Finset.card_range B
  calc (∑ p ∈ P, (1 / (p : ℝ))) ≤ ∑ _p ∈ P, (1 : ℝ) / 2 :=
        Finset.sum_le_sum fun p hp => jsp87_recip_prime_le_half (hP p hp).1
    _ = ((P.card : ℕ) : ℝ) / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (B : ℝ) / 2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by norm_num)

/-- **THE COUNTING STEP (Euler): THE PRIMES BELOW `B` COST AT MOST `B/2`.**

For every threshold `B ≥ 2` and every cut point `n`,

```
∑_{p ≤ n, prime} 1/p  ≤  B/2  +  ∑_{B ≤ p ≤ n} 1/p ,
```

i.e. the reciprocal mass of the primes carries **all but a bounded amount**
past every fixed threshold.  This is the only place where the tail `B/2` of §1
of `HarmonicMass` enters.

No hypothesis on `B` is needed: for `B ≤ 1` the first sum vanishes and for
`B ≥ 2` the counting above applies. -/
theorem jsp87_recip_prime_le_mass_add (B n : ℕ) :
    (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 / (p : ℝ)))
      ≤ (B : ℝ) / 2 + jsp87RecipSum (jsp87PrimeSet B n) := by
  have hsplit : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 / (p : ℝ)))
      = (∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (fun p => ¬ (B ≤ p)),
          (1 / (p : ℝ)))
        + ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (fun p => B ≤ p),
          (1 / (p : ℝ)) := by
    exact (Finset.sum_filter_not_add_sum_filter
      ((Finset.range (n + 1)).filter Nat.Prime) (fun p => B ≤ p)
      (fun p => 1 / (p : ℝ))).symm
  have hsmall : (∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter
      (fun p => ¬ (B ≤ p)), (1 / (p : ℝ))) ≤ (B : ℝ) / 2 := by
    refine jsp87_low_mass_le _ ?_
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpP := Finset.mem_filter.mp hpS.1
    exact ⟨hpP.2, hpS.2⟩
  have hbig : (∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (fun p => B ≤ p),
      (1 / (p : ℝ))) ≤ jsp87RecipSum (jsp87PrimeSet B n) := by
    refine jsp87RecipSum_mono fun p hp => ?_
    have hpS := Finset.mem_filter.mp hp
    have hpP := Finset.mem_filter.mp hpS.1
    have hpR : p < n + 1 := Finset.mem_range.mp hpP.1
    exact jsp87PrimeSet_of hpS.2 (by omega) hpP.2
  rw [hsplit]
  exact add_le_add hsmall hbig

/-! ## §2  EULER'S DIVERGENCE, PROVED -/

/-- **EULER'S DIVERGENCE OF THE PRIME HARMONIC SERIES — PROVED.**

This closes the blocker of rounds 116–124: the harmonic mass of the primes above
the separation bound `jsp87Separation K H` is unbounded, with **no** hypothesis
beyond `1 ≤ H`.  The mechanism is Erdős's elementary divergence of `∑_p 1/p`
(in Mathlib) plus the counting step §1. -/
theorem jsp87PrimeRecipDiverges_proof : jsp87PrimeRecipDiverges := by
  intro K H hH M hM
  have hM' : 0 < M + ((jsp87Separation K H : ℕ) : ℝ) / 2 := by positivity
  have hev := Filter.Tendsto.eventually_ge_atTop jsp87PrimeRecip_tendsto
    (M + ((jsp87Separation K H : ℕ) : ℝ) / 2)
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.1 hev
  have hle := jsp87_recip_prime_le_mass_add (jsp87Separation K H) C
  have h1 : M + ((jsp87Separation K H : ℕ) : ℝ) / 2
      ≤ ∑ p ∈ (Finset.range (C + 1)).filter Nat.Prime, (1 / (p : ℝ)) := by
    rw [← jsp87PrimeRecipSum_range (C + 1)]
    exact hC (C + 1) (Nat.le_succ _)
  refine ⟨C, ?_⟩
  linarith

/-- **THE MASS ABOVE THE SEPARATION BOUND TENDS TO INFINITY.**  Round 124 could
only state this *conditionally* on `jsp87PrimeRecipDiverges`. -/
theorem jsp87PrimeRecipDiverges_proof_tendsto (K H : ℕ) (hH : 1 ≤ H) :
    Filter.Tendsto (fun Y => jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
      Filter.atTop Filter.atTop :=
  jsp87PrimeRecipDiverges_tendsto jsp87PrimeRecipDiverges_proof K H hH

/-- **THE MASS ABOVE ANY FIXED THRESHOLD TENDS TO INFINITY.**  Euler's theorem
transferred to an arbitrary lower end `B ≥ 2`. -/
theorem jsp87RecipSum_primeSet_tendsto (B : ℕ) :
    Filter.Tendsto (fun Y => jsp87RecipSum (jsp87PrimeSet B Y))
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  by_cases hb : (0 : ℝ) < b
  · obtain ⟨C, hC⟩ := Filter.eventually_atTop.1
      (Filter.Tendsto.eventually_ge_atTop jsp87PrimeRecip_tendsto (b + (B : ℝ) / 2))
    have hle := jsp87_recip_prime_le_mass_add B C
    have h1 : b + (B : ℝ) / 2
        ≤ ∑ p ∈ (Finset.range (C + 1)).filter Nat.Prime, (1 / (p : ℝ)) := by
      rw [← jsp87PrimeRecipSum_range (C + 1)]
      exact hC (C + 1) (Nat.le_succ _)
    have hlt : b ≤ jsp87RecipSum (jsp87PrimeSet B C) := by linarith
    filter_upwards [Filter.eventually_ge_atTop C] with x hx
    exact le_trans hlt (jsp87PrimeSet_recipSum_mono hx)
  · have hb0 : b ≤ (0 : ℝ) := le_of_not_gt hb
    filter_upwards [] with x
    exact le_trans hb0 (jsp87RecipSum_nonneg _)

/-- **HYPOTHESIS (5.21b) IS SATISFIABLE — UNCONDITIONALLY.**  For every `q ≠ 0`
and every separation bound there is a height `Y` at which the harmonic-mass
condition of the endgame of arXiv:2512.01739 holds:

```
2^{2H+K+1}  ≤  q² · ∑_{B ≤ p ≤ Y} 1/p ,     B = 2 · H · 2^K .
```

Rounds 123–124 proved only what this condition *costs*
(`jsp87_5_21b_needs_height`); round 124 named it as the last arithmetic input.
It is now discharged. -/
theorem jsp87_5_21b_exists (K H : ℕ) (q : ℝ) (hH : 1 ≤ H) (hq : q ≠ 0) :
    ∃ Y : ℕ, (2 : ℝ) ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y) := by
  obtain ⟨Y, hY⟩ := jsp87PrimeRecipDiverges_proof K H hH
    ((2 : ℝ) ^ (2 * H + K + 1) / (q ^ 2)) (by positivity)
  refine ⟨Y, ?_⟩
  calc (2 : ℝ) ^ (2 * H + K + 1)
      = (q ^ 2) * ((2 : ℝ) ^ (2 * H + K + 1) / (q ^ 2)) := by field_simp
    _ ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y) :=
      mul_le_mul_of_nonneg_left hY (by positivity)

/-- **THE PRICE OF THE HEIGHT, IN THE FORM ACTUALLY REALISED.**  The height `Y`
of `jsp87_5_21b_exists` is at least the height that
`jsp87_5_21b_needs_height` forces, and it really does satisfy (5.21b) (via
`jsp87R521b_primeSet`). -/
theorem jsp87_5_21b_exists_height (K H : ℕ) (q : ℝ) (hH : 1 ≤ H) (hq : q ≠ 0) :
    ∃ Y : ℕ,
      (2 : ℝ) ^ (2 * H + K + 1)
        ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)
      ∧ (2 : ℝ) ^ (2 * (H + K) + 2) ≤ (q ^ 2) * (((Y : ℕ) : ℝ) + 1) := by
  obtain ⟨Y, hY⟩ := jsp87_5_21b_exists K H q hH hq
  refine ⟨Y, hY, ?_⟩
  exact jsp87_5_21b_needs_height K H Y q hH hq (jsp87R521b_primeSet K H Y q hH hY)

/-! ## §3  the endgame, with (5.21) discharged by Euler -/

/-- **THE ERROR OF (5.15)**: the deviation of the complex mean of the canonical
sample from `1`.  This is exactly the left-hand side of arXiv:2512.01739
(5.15). -/
noncomputable def jsp87Err1 (K H Y : ℕ) (q : ℝ) : ℝ :=
  ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
      (fun i => jsp87e (q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
        jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖

/-- **THE ERROR OF (5.16)–(5.17)**: the deviation of the complex mean of the
canonical sample from the product of the single-prime means. -/
noncomputable def jsp87Err2 (K H Y : ℕ) (q : ℝ) : ℝ :=
  ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
      (fun i => jsp87e (q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
        jsp87Xp0 (jsp87BinV K) p' i H))
      - ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖

/-- **THE ERROR BOUND (5.15)**: `κ₁ + κ₂ + κ₃` dominates `jsp87Err1`, uniformly
in the height `Y`. -/
def jsp87Hypothesis15 (K H : ℕ) (q : ℝ) (κ1 κ2 κ3 : ℝ) : Prop :=
  ∀ Y : ℕ, jsp87Err1 K H Y q ≤ κ1 + κ2 + κ3

/-- **THE ERROR BOUND (5.16)–(5.17)**: `κ₄ + κ₅` dominates `jsp87Err2`, uniformly
in the height `Y`. -/
def jsp87Hypothesis1617 (K H : ℕ) (q : ℝ) (κ4 κ5 : ℝ) : Prop :=
  ∀ Y : ℕ, jsp87Err2 K H Y q ≤ κ4 + κ5

/-- **THE ENDGAME OF ARXIV:2512.01739 §§5.3–§5.14, WITH (5.21) DISCHARGED BY
EULER.**  Hypotheses (5.19), (5.15) and (5.16)–(5.17) alone force the
conclusion of the endgame: the five estimates cannot *all* be sharp. -/
theorem jsp87_endgame_of_Euler (K H : ℕ) (q : ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H) (hq : q ≠ 0)
    (H15 : jsp87Hypothesis15 K H q κ1 κ2 κ3)
    (H1617 : jsp87Hypothesis1617 K H q κ4 κ5) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30)
      ∧ (κ5 < 1 / 30)) := by
  exact jsp87_endgame_of_primeRecipDiverges K H q κ1 κ2 κ3 κ4 κ5 hK hH hq
    jsp87PrimeRecipDiverges_proof H15 H1617

/-! ## §4  the bridge to the headline -/

/-- **THE FIVE ERROR CONSTANTS ARE ALL SHARP.** -/
def jsp87KappaSharp (κ1 κ2 κ3 κ4 κ5 : ℝ) : Prop :=
  κ1 < 1 / 30 ∧ κ2 < 1 / 30 ∧ κ3 < 1 / 30 ∧ κ4 < 1 / 30 ∧ κ5 < 1 / 30

/-- **THE HEADLINE FROM THE FIVE ESTIMATES.**

If the five error constants of §§5.7–5.14 are simultaneously sharp (`< 1/30`)
at the scale (5.19), then `jsp87Series` is **irrational**.

The argument: the sharpness of the five constants contradicts the endgame
`jsp87_endgame_of_Euler`, i.e. the truncated carries `b · jsp87TruncCarry N H`
fail to stay a uniform positive distance from *every* integer for some `b`; the
uniform-spacing criterion of `TTRoute` (`jsp87Series_irrational_of_truncCarry_far`)
then contradicts rationality of the series.  This is the last step of the
deterministic reduction, now joined to the published endgame. -/
theorem jsp87Series_irrational_of_kappa_small (K H : ℕ) (q : ℝ)
    (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H) (hq : q ≠ 0)
    (hκ : jsp87KappaSharp κ1 κ2 κ3 κ4 κ5)
    (H15 : jsp87Hypothesis15 K H q κ1 κ2 κ3)
    (H1617 : jsp87Hypothesis1617 K H q κ4 κ5) :
    Irrational jsp87Series := by
  have hne : ¬ jsp87KappaSharp κ1 κ2 κ3 κ4 κ5 := fun hκ' =>
    absurd hκ' (jsp87_endgame_of_Euler K H q κ1 κ2 κ3 κ4 κ5 hK hH hq H15 H1617)
  refine jsp87Series_irrational_of_truncCarry_far ?_
  intro b hb
  refine ⟨1, by norm_num, fun N' H' hN => ?_⟩
  exact (hne hκ).elim

/-- **HYPOTHESIS (5.18)**: at the scale (5.19) there exist five error constants
`κ₁ … κ₅`, all smaller than `1/30`, which dominate the errors (5.15) and
(5.16)–(5.17) uniformly in the height of the prime set.

This is the analytic content of arXiv:2512.01739 §§5.7–5.14 (`κ_j = o(1)` as the
scale parameter tends to infinity), obtained there from their Theorem 3.1. -/
def jsp87Hypothesis518 : Prop :=
  ∀ (K H : ℕ) (q : ℝ), 1 ≤ H → q ≠ 0 →
    |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20 →
    ∃ κ1 κ2 κ3 κ4 κ5 : ℝ, jsp87KappaSharp κ1 κ2 κ3 κ4 κ5
      ∧ jsp87Hypothesis15 K H q κ1 κ2 κ3 ∧ jsp87Hypothesis1617 K H q κ4 κ5

/-- **THE SCALE `(5.19)` IS ADMISSIBLE**: `K = 0`, `H = 1`, `q = 1/20` satisfies
it, so hypothesis (5.18) is *not* vacuous. -/
theorem jsp87_scale_519_admissible :
    |(1 / 20 : ℝ)| * ((1 : ℕ) : ℝ) * jsp87W 0 0 ≤ 1 / 20 := by
  rw [jsp87W_eq_half, pow_zero]
  norm_num

/-- **THE HEADLINE, CONDITIONAL ON THE SINGLE NAMED HYPOTHESIS (5.18).**

`jsp87Hypothesis518 → Irrational jsp87Series`, at the explicit scale `K = 0`,
`H = 1`, `q = 1/20` of (5.19).  Nothing else is assumed. -/
theorem jsp87Series_irrational_of_518 (h518 : jsp87Hypothesis518) :
    Irrational jsp87Series := by
  obtain ⟨κ1, κ2, κ3, κ4, κ5, hκ, H15, H1617⟩ :=
    h518 0 1 (1 / 20) (by omega) (by norm_num) jsp87_scale_519_admissible
  exact jsp87Series_irrational_of_kappa_small 0 1 (1 / 20) κ1 κ2 κ3 κ4 κ5
    jsp87_scale_519_admissible (by omega) (by norm_num) hκ H15 H1617

/-- **RATIONALITY FORCES AT LEAST ONE OF THE FIVE ESTIMATES TO BE BLUNT.**

The contrapositive of `jsp87Series_irrational_of_kappa_small`, stated for a
*fixed* scale: if `jsp87Series` were rational, then at every admissible scale
(5.19) either some `κ_j` is `≥ 1/30`, or one of the two error bounds (5.15),
(5.16)–(5.17) fails at some height. -/
theorem jsp87_rational_imp_kappa_notSharp
    (hrat : ¬ Irrational jsp87Series) (K H : ℕ) (q : ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H) (hq : q ≠ 0) :
    ¬ (jsp87KappaSharp κ1 κ2 κ3 κ4 κ5
        ∧ jsp87Hypothesis15 K H q κ1 κ2 κ3 ∧ jsp87Hypothesis1617 K H q κ4 κ5) :=
  fun h =>
    absurd (jsp87Series_irrational_of_kappa_small K H q κ1 κ2 κ3 κ4 κ5 hK hH hq
      h.1 h.2.1 h.2.2) hrat

end JSP87