/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.CharFun

/-!
# Round 129 — THE MEAN OVER AN **ARBITRARY** FINITE SAMPLE: EQUIDISTRIBUTION IS
# EXACTLY THE CLOSED FORM, AND NO UNIFORM SAMPLE CAN RUN THE ENDGAME

`policy.json` `next_round_attack[0]`–`[1]` asked two questions about the sample
of the endgame of arXiv:2512.01739 §§5.3–5.14:

* attack `[0]`: *for a general finite `S` (not a whole period), what is the exact
  mean of `e (θ · cnt P (i+1))`, and hence of (5.15) and (5.21)?*
* attack `[1]`: *is the closed form of round 128 invariant under replacing the
  canonical sample `jsp87ProgFull 0 1 P` by another sample?*

Round 128 computed the closed form for the canonical sample and, with it, the
sharp negative result `jsp87Hypothesis15_ground_false`: on that sample (5.15) is
refuted at every large height for every total constant `< 1`.  This round
answers both questions, in the strongest form that is *provable*: the closed
form is the mean of **every equidistributed sample**, and no equidistributed
sample family can run the endgame.

## §0  the objects

`jsp87CFgen S P θ` is the mean of the phase over **any** finite sample `S`;
`jsp87Hits S Q a` counts the sample points in one residue class `a (mod Q)`,
`jsp87Uniform S Q` says the sample is **equidistributed** modulo `Q`, and
`jsp87MassC S Q a` is the corresponding mass.  `jsp87Err1gen`,
`jsp87Hypothesis15fam`, `jsp87UniformFam` are (5.15) and equidistribution for a
*family* of samples `Y ↦ 𝕊 Y`.

## §1–§2  THE RESIDUE-CLASS DECOMPOSITION

`jsp87card_res_total`, `jsp87sum_res_total`: a cardinality or a sum over a
sample splits **exactly** into its residue classes.  `jsp87CAvg_uniform`: for an
equidistributed sample the mean is the mean over one complete residue system —
the sample itself disappears.  (`jsp87Cnt_period`, `jsp87CFfun_period`: the
phase depends only on `i mod ∏ P`.)

## §3  THE CLOSED FORM IS EXACTLY EQUIDISTRIBUTION

* `jsp87CFgen_uniform_eq_charFun` — **★** an equidistributed sample has the
  canonical mean of round 128, for **arbitrary** `S`, `P`, `θ`;
* `jsp87CFgen_uniform_eq_prod` — hence the finite product, for an arbitrary
  equidistributed sample;
* `jsp87CFgen_uniform_norm`, `jsp87Err1gen_sub_one` — the modulus and the (5.15)
  error are the canonical ones.

## §4  WHICH SAMPLES ARE EQUIDISTRIBUTED

`jsp87Hits_range_dvd`, `jsp87Uniform_range`, `jsp87CFgen_range_eq_prod`: **any
number of whole periods, read as an initial segment, has exactly the mean of one
period** (`∏ P ∣ N`).  This is the exact answer to attack `[1]` for whole-period
samples; the general `jsp87ProgFull n₀ D P` with `Nat.Coprime D (∏ P)` reduces
to it via the still-open counting lemma `jsp87Hits (jsp87ProgFull n₀ D P) Q a = 1`
(recorded verbatim in `policy.json` `round129_blocker`).

## §5  THE DECISIVE NEGATIVE RESULT, IN FULL GENERALITY

`jsp87Hypothesis15fam_uniform_false`: **★ no family of equidistributed samples
can run (5.15)**, for any three constants with sum `< 1`.  Round 128 proved this
for the single canonical sample; the obstruction is a property of *uniformity*,
not of the sample.  Consequently

* `jsp87_sample_must_break_equidistribution` — the endgame sample must provably
  **break equidistribution modulo the product of its own primes** at some
  height, i.e. it must be a genuinely prime-correlated set of integers;
* `jsp87_endgame_uniformfam_blocked` — for every choice of the five sharp
  constants `κ_j < 1/30`, §§5.3–5.14 are unsatisfiable on every equidistributed
  family.

## §6  THE SHAPE OF WHAT REMAINS: THE MEAN IS A PROFILE–PHASE PAIRING

* `jsp87CFgen_eq_mass` — the mean over **any** sample is the mass-weighted
  average of the phase values `jsp87CFfun P θ a`, `a < ∏ P`;
* `jsp87CFgen_sub_charFun_eq_profile` — **★** the deviation of the sample mean
  from the closed form is exactly the pairing
  `∑_a (mass a − 1/Q) · (g a − 1)` of the *residue-profile deviation* with the
  *phase deviations*;
* `jsp87CFgen_sub_charFun_norm_le` and `jsp87Err1gen_lower_profile` — the
  quantitative form: the (5.15) error is at least `1 − ‖canonical mean‖` minus
  the total variation of the residue profile.  For an equidistributed sample the
  profile term vanishes (`jsp87MassC_uniform`,
  `jsp87CFgen_sub_charFun_eq_zero_uniform`) and one recovers exactly round 128's
  obstruction, `jsp87Err1gen_sub_one`.

So the endgame sample must be **non-uniform** (§5) *and* the profile–phase
pairing must be small: a quantitative, machine-checked constraint on the sample
choice that no choice of constants can evade.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  the objects -/

/-- **THE PHASE FUNCTION OF THE PRIME-DIVISOR COUNT**, as a function of the
sample index: the summand whose mean is the endgame's mean. -/
noncomputable def jsp87CFfun (P : Finset ℕ) (θ : ℝ) (i : ℕ) : ℂ :=
  jsp87e (θ * (jsp87Cnt P (i + 1)))

/-- **THE MEAN OF THE PHASE OVER AN ARBITRARY FINITE SAMPLE.**

This is (5.15)'s mean, `jsp87CharFun` of round 128 being the case
`S = jsp87ProgFull 0 1 P`. -/
noncomputable def jsp87CFgen (S : Finset ℕ) (P : Finset ℕ) (θ : ℝ) : ℂ :=
  jsp87CAvg S (jsp87CFfun P θ)

/-- **THE NUMBER OF SAMPLE POINTS IN THE RESIDUE CLASS `a (mod Q)`.** -/
def jsp87Hits (S : Finset ℕ) (Q a : ℕ) : ℕ := (S.filter (fun i => i % Q = a)).card

/-- **A SAMPLE IS EQUIDISTRIBUTED MODULO `Q`** if it meets every residue class of
`Z / QZ` equally often. -/
def jsp87Uniform (S : Finset ℕ) (Q : ℕ) : Prop :=
  ∀ a : ℕ, a < Q → ∀ b : ℕ, b < Q → jsp87Hits S Q a = jsp87Hits S Q b

/-- **THE `a`-TH MASS OF THE SAMPLE**, i.e. the fraction of the sample lying in
the residue class `a (mod Q)`. -/
noncomputable def jsp87MassC (S : Finset ℕ) (Q a : ℕ) : ℂ :=
  ((jsp87Hits S Q a : ℕ) : ℂ) / ((S.card : ℕ) : ℂ)

/-- **THE ERROR OF (5.15) FOR AN ARBITRARY SAMPLE.** -/
noncomputable def jsp87Err1gen (S : Finset ℕ) (P : Finset ℕ) (q : ℝ) : ℝ :=
  ‖jsp87CFgen S P (q / 2) - 1‖

/-- **(5.15) FOR A FAMILY OF SAMPLES `Y ↦ 𝕊 Y`** at the ground-truth scale
`B` (the primes in `[B, Y]`): the (5.15) error is bounded at every height. -/
def jsp87Hypothesis15fam (Ss : ℕ → Finset ℕ) (B : ℕ) (q κ1 κ2 κ3 : ℝ) : Prop :=
  ∀ Y : ℕ, 0 < (Ss Y).card →
    jsp87Err1gen (Ss Y) (jsp87PrimeSet B Y) q ≤ κ1 + κ2 + κ3

/-- **A FAMILY OF SAMPLES, EACH EQUIDISTRIBUTED MODULO THE PRODUCT OF ITS OWN
PRIMES.** -/
def jsp87UniformFam (Ss : ℕ → Finset ℕ) (B : ℕ) : Prop :=
  ∀ Y : ℕ, 0 < jsp87Prod (jsp87PrimeSet B Y) →
    jsp87Uniform (Ss Y) (jsp87Prod (jsp87PrimeSet B Y))

/-! ## §1  the residue-class decomposition -/

/-- **A CARDINALITY SPLITS INTO ITS RESIDUE CLASSES.** -/
private theorem jsp87card_res_total (S : Finset ℕ) (Q : ℕ) (hQ : 0 < Q) :
    S.card = ∑ a ∈ Finset.range Q, jsp87Hits S Q a := by
  have hkey : ∀ i : ℕ, (∑ a ∈ Finset.range Q, (if i % Q = a then (1 : ℕ) else 0)) = 1 := by
    intro i
    simpa using (Finset.sum_eq_single (M := ℕ) (s := Finset.range Q)
      (f := fun b => (if i % Q = b then (1 : ℕ) else 0)) (i % Q)
      (fun b _ hne => by
        by_cases h : i % Q = b
        · exact absurd h hne.symm
        · simp [h])
      (fun h => (h (Finset.mem_range.2 (Nat.mod_lt i hQ))).elim))
  calc S.card = ∑ i ∈ S, (1 : ℕ) := Finset.card_eq_sum_ones S
    _ = ∑ i ∈ S, ∑ a ∈ Finset.range Q, (if i % Q = a then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (hkey i).symm
    _ = ∑ a ∈ Finset.range Q, ∑ i ∈ S, (if i % Q = a then (1 : ℕ) else 0) := Finset.sum_comm
    _ = ∑ a ∈ Finset.range Q, jsp87Hits S Q a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have h3 : (∑ i ∈ S, (if i % Q = a then (1 : ℕ) else 0))
            = ∑ k ∈ S.filter (fun k => k % Q = a), (1 : ℕ) := by
          rw [← Finset.sum_filter]
        rw [h3, Finset.sum_const (1 : ℕ), nsmul_eq_mul, mul_one]
        rfl

/-- **THE SUM OVER ONE RESIDUE CLASS.** -/
private theorem jsp87sum_res_class (S : Finset ℕ) (Q a : ℕ) (g : ℕ → ℂ)
    (hg : ∀ i, g i = g (i % Q)) :
    (∑ i ∈ S, if i % Q = a then g i else 0) = ((jsp87Hits S Q a : ℕ) : ℂ) * g a := by
  have h1 : (∑ i ∈ S, if i % Q = a then g i else 0)
      = ∑ k ∈ S.filter (fun k => k % Q = a), g k := by rw [← Finset.sum_filter]
  have h2 : (∑ k ∈ S.filter (fun k => k % Q = a), g k)
      = ∑ _k ∈ S.filter (fun k => k % Q = a), g a := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨_, hk'⟩ := Finset.mem_filter.mp hk
    rw [hg k, hk']
  have h3 : (∑ _k ∈ S.filter (fun k => k % Q = a), g a)
      = ((S.filter (fun k => k % Q = a)).card : ℂ) * g a := by
    rw [Finset.sum_const (g a : ℂ), nsmul_eq_mul]
  rw [h1, h2, h3]
  rfl

/-- **★ A SUM OVER A SAMPLE SPLITS INTO ITS RESIDUE CLASSES ★**

For a function of period `Q`, the mean over a sample is the residue-weighted
average of its values on one complete residue system. -/
theorem jsp87sum_res_total (S : Finset ℕ) (Q : ℕ) (g : ℕ → ℂ) (hQ : 0 < Q)
    (hg : ∀ i, g i = g (i % Q)) :
    (∑ i ∈ S, g i) = ∑ a ∈ Finset.range Q, ((jsp87Hits S Q a : ℕ) : ℂ) * g a := by
  have hkey : ∀ i : ℕ, (∑ a ∈ Finset.range Q, (if i % Q = a then g i else 0)) = g i := by
    intro i
    simpa using (Finset.sum_eq_single (M := ℂ) (s := Finset.range Q)
      (f := fun b => (if i % Q = b then g i else 0)) (i % Q)
      (fun b _ hne => by
        by_cases h : i % Q = b
        · exact absurd h hne.symm
        · simp [h])
      (fun h => (h (Finset.mem_range.2 (Nat.mod_lt i hQ))).elim))
  calc (∑ i ∈ S, g i)
      = ∑ i ∈ S, ∑ a ∈ Finset.range Q, (if i % Q = a then g i else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (hkey i).symm
    _ = ∑ a ∈ Finset.range Q, ∑ i ∈ S, (if i % Q = a then g i else 0) :=
        Finset.sum_comm
    _ = ∑ a ∈ Finset.range Q, ((jsp87Hits S Q a : ℕ) : ℂ) * g a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact jsp87sum_res_class S Q a g hg

/-- **THE HITS OF AN EQUIDISTRIBUTED SAMPLE ARE ALL EQUAL.** -/
private theorem jsp87hits_uniform (S : Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hu : jsp87Uniform S Q) : ∀ a : ℕ, a < Q → jsp87Hits S Q a = jsp87Hits S Q 0 := by
  intro a ha
  have h1 := hu a ha 0 hQ
  omega

/-- **THE CARDINALITY OF AN EQUIDISTRIBUTED SAMPLE.** -/
private theorem jsp87card_uniform (S : Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hu : jsp87Uniform S Q) : S.card = Q * jsp87Hits S Q 0 := by
  have hm : ∀ a : ℕ, a < Q → jsp87Hits S Q a = jsp87Hits S Q 0 :=
    jsp87hits_uniform S Q hQ hu
  have h1 := jsp87card_res_total S Q hQ
  have hkey : ∀ a ∈ Finset.range Q, jsp87Hits S Q a = jsp87Hits S Q 0 := by
    intro a ha
    rw [hm a (Finset.mem_range.mp ha)]
  have hconv : (∑ a ∈ Finset.range Q, jsp87Hits S Q a)
      = (∑ _a ∈ Finset.range Q, jsp87Hits S Q 0) := Finset.sum_congr rfl hkey
  rw [hconv] at h1
  have h2 : (∑ _a ∈ Finset.range Q, jsp87Hits S Q 0)
      = Q * jsp87Hits S Q 0 := by
    rw [Finset.sum_const (jsp87Hits S Q 0), nsmul_eq_mul, Finset.card_range]
    rfl
  rw [h2] at h1
  exact h1

/-- **★ THE MEAN OVER AN EQUIDISTRIBUTED SAMPLE IS THE MEAN OVER ONE PERIOD ★**

The sample itself disappears: only its equidistribution modulo `Q` matters. -/
theorem jsp87CAvg_uniform (S : Finset ℕ) (Q : ℕ) (g : ℕ → ℂ) (hQ : 0 < Q)
    (hg : ∀ i, g i = g (i % Q)) (hcard : 0 < S.card) (hu : jsp87Uniform S Q) :
    jsp87CAvg S g = (∑ a ∈ Finset.range Q, g a) / ((Q : ℕ) : ℂ) := by
  have hm : ∀ a : ℕ, a < Q → jsp87Hits S Q a = jsp87Hits S Q 0 :=
    jsp87hits_uniform S Q hQ hu
  have hcard' : S.card = Q * jsp87Hits S Q 0 := jsp87card_uniform S Q hQ hu
  have hcardC : ((S.card : ℕ) : ℂ)
      = ((Q : ℕ) : ℂ) * ((jsp87Hits S Q 0 : ℕ) : ℂ) := by
    have hx := congrArg (fun n : ℕ => (n : ℂ)) hcard'
    rw [Nat.cast_mul] at hx
    exact hx
  have hN0 : ((S.card : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard)
  have hm0 : jsp87Hits S Q 0 ≠ 0 := by
    intro hc0
    have h2 : S.card = 0 := by rw [hcard', hc0]; simp
    omega
  have hQ' : ((Q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmC : ((jsp87Hits S Q 0 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hsum := jsp87sum_res_total S Q g hQ hg
  have hkey : ∀ a ∈ Finset.range Q,
      ((jsp87Hits S Q a : ℕ) : ℂ) * g a = ((jsp87Hits S Q 0 : ℕ) : ℂ) * g a := by
    intro a ha
    rw [hm a (Finset.mem_range.mp ha)]
  have hconv : (∑ a ∈ Finset.range Q, ((jsp87Hits S Q a : ℕ) : ℂ) * g a)
      = (∑ a ∈ Finset.range Q, ((jsp87Hits S Q 0 : ℕ) : ℂ) * g a) :=
    Finset.sum_congr rfl hkey
  rw [hconv] at hsum
  unfold jsp87CAvg
  rw [hsum, hcardC]
  apply (div_eq_div_iff (mul_ne_zero hQ' hmC) hQ').mpr
  calc (∑ x ∈ Finset.range Q, (((jsp87Hits S Q 0 : ℕ) : ℂ) * g x)) * ((Q : ℕ) : ℂ)
      = (((jsp87Hits S Q 0 : ℕ) : ℂ) * (∑ x ∈ Finset.range Q, g x)) * ((Q : ℕ) : ℂ) := by
        rw [Finset.mul_sum]
    _ = (∑ a ∈ Finset.range Q, g a)
        * (((Q : ℕ) : ℂ) * ((jsp87Hits S Q 0 : ℕ) : ℂ)) := by ring

/-! ## §2  divisibility modulo the product of the primes -/

/-- **EVERY PRIME OF `P` DIVIDES `∏ P`.** -/
private theorem jsp87dvd_prod_mem' {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) :
    p ∣ jsp87Prod P := by
  obtain ⟨c, hc⟩ := (Finset.dvd_prod_of_mem (f := id) (s := P) (a := p) hp)
  refine ⟨c, ?_⟩
  unfold jsp87Prod
  simpa only [id_eq] using hc

/-- **A DIVISOR OF A FACTOR IS A DIVISOR OF THE PRODUCT.** -/
private theorem jsp87mul_dvd {p b x : ℕ} (h : p ∣ b) : p ∣ b * x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * x, ?_⟩
  rw [hc]
  ring

/-- **SUBTRACTING A MULTIPLE OF A DIVISOR.** -/
private theorem jsp87dvd_of_dvd_add {p n k : ℕ} (hn : p ∣ n) (hk : p ∣ k)
    (hle : k ≤ n) : p ∣ (n - k) := by
  have hsub : n - k + k = n := Nat.sub_add_cancel hle
  have key : (p ∣ (n - k) ↔ p ∣ n) :=
    (Nat.dvd_add_iff_left hk).trans (by rw [hsub])
  exact key.mpr hn

/-- **A DIVISOR OF `d` DIVIDES `n` IFF IT DIVIDES `n mod d`.** -/
private theorem jsp87dvd_mod_iff {p d n : ℕ} (hd : p ∣ d) : p ∣ n ↔ p ∣ n % d := by
  have hkey : n % d + d * (n / d) = n := Nat.mod_add_div n d
  have hdk : p ∣ d * (n / d) := jsp87mul_dvd hd
  have hle : d * (n / d) ≤ n := by
    have h1 := Nat.le_add_right (n % d) (d * (n / d))
    omega
  constructor
  · intro h
    have h1 := jsp87dvd_of_dvd_add h hdk hle
    have h2 : n - d * (n / d) = n % d := by
      have h3 : n = d * (n / d) + n % d := by omega
      exact (Nat.sub_eq_iff_eq_add' hle).mpr h3
    rw [h2] at h1
    exact h1
  · intro h
    have h1 : p ∣ n % d + d * (n / d) := by
      refine ((Nat.dvd_add_iff_left hdk
        : (p ∣ (n % d) ↔ p ∣ (n % d) + d * (n / d))).mp h)
    rw [hkey] at h1
    exact h1

/-- **DIVISIBILITY OF A SUCCESSOR IS A FUNCTION OF THE INDEX MODULO A MULTIPLE OF
THE DIVISOR.** -/
private theorem jsp87dvd_succ_mod {p Q i : ℕ} (hd : p ∣ Q) :
    p ∣ i + 1 ↔ p ∣ (i % Q) + 1 := by
  have hkey : i + 1 = (i % Q) + 1 + Q * (i / Q) := by
    have h1 := Nat.mod_add_div i Q
    omega
  have hQ : p ∣ Q * (i / Q) := jsp87mul_dvd hd
  have hle : Q * (i / Q) ≤ i + 1 := by
    have h1 := Nat.mod_add_div i Q
    omega
  constructor
  · intro h
    have h1 := jsp87dvd_of_dvd_add h hQ hle
    have h2 : (i + 1) - Q * (i / Q) = (i % Q) + 1 := by
      apply (Nat.sub_eq_iff_eq_add' hle).mpr
      omega
    rw [h2] at h1
    exact h1
  · intro h
    rw [hkey]
    exact ((Nat.dvd_add_iff_left hQ
      : (p ∣ ((i % Q) + 1) ↔ p ∣ ((i % Q) + 1) + Q * (i / Q))).mp h)

/-- **THE COUNT OF DIVISORS OF `P` DEPENDS ONLY ON THE ARGUMENT MODULO `∏ P`.** -/
theorem jsp87Cnt_period (P : Finset ℕ) (i : ℕ) :
    jsp87Cnt P (i + 1) = jsp87Cnt P ((i % jsp87Prod P) + 1) := by
  have hkey : (P.filter (fun p => p ∣ i + 1))
      = P.filter (fun p => p ∣ (i % jsp87Prod P) + 1) := by
    refine Finset.filter_congr fun p hp => ?_
    exact jsp87dvd_succ_mod (jsp87dvd_prod_mem' hp)
  rw [jsp87Cnt, jsp87Cnt, hkey]

/-- **THE PHASE FUNCTION IS PERIODIC WITH PERIOD `∏ P`.** -/
theorem jsp87CFfun_period (P : Finset ℕ) (θ : ℝ)
    (i : ℕ) : jsp87CFfun P θ i = jsp87CFfun P θ (i % jsp87Prod P) := by
  unfold jsp87CFfun
  rw [jsp87Cnt_period P i]

/-! ## §3  THE CLOSED FORM IS EXACTLY EQUIDISTRIBUTION -/

/-- **★ THE MEAN OVER AN ARBITRARY SAMPLE, IN RESIDUE FORM ★**

The mean over *any* finite sample is the residue-weighted average of the phase
values `jsp87CFfun P θ a`, `a < ∏ P`: no periodicity of the sample is assumed
anywhere. -/
theorem jsp87CFgen_eq_resAvg (S : Finset ℕ) (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime)
    (θ : ℝ) :
    jsp87CFgen S P θ
      = (∑ a ∈ Finset.range (jsp87Prod P),
          ((jsp87Hits S (jsp87Prod P) a : ℕ) : ℂ) * jsp87CFfun P θ a)
          / ((S.card : ℕ) : ℂ) := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hsum := jsp87sum_res_total S (jsp87Prod P) (jsp87CFfun P θ) hQ
    (fun i => jsp87CFfun_period P θ i)
  rw [jsp87CFgen, jsp87CAvg, hsum]

/-- **★ EQUIDISTRIBUTION GIVES THE CANONICAL MEAN, FOR AN ARBITRARY SAMPLE ★**

The closed form of round 128 is not a property of the canonical sample: it is
the closed form of *every* equidistributed sample. -/
theorem jsp87CFgen_uniform_eq_charFun (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) (hcard : 0 < S.card)
    (hu : jsp87Uniform S (jsp87Prod P)) : jsp87CFgen S P θ = jsp87CharFun P θ := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have havg : jsp87CFgen S P θ
      = (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
          / ((jsp87Prod P : ℕ) : ℂ) :=
    jsp87CAvg_uniform S (jsp87Prod P) (jsp87CFfun P θ) hQ
      (fun i => jsp87CFfun_period P θ i) hcard hu
  have hIcc : (Finset.Icc 0 (jsp87Prod P - 1) : Finset ℕ) = Finset.range (jsp87Prod P) := by
    ext x
    rw [Finset.mem_Icc, Finset.mem_range]
    omega
  have hchar : (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
      / ((jsp87Prod P : ℕ) : ℂ) = jsp87CharFun P θ := by
    calc (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
        / ((jsp87Prod P : ℕ) : ℂ)
        = jsp87CAvg (Finset.range (jsp87Prod P)) (jsp87CFfun P θ) := by
          unfold jsp87CAvg
          rw [Finset.card_range]
      _ = jsp87CAvg (Finset.range (jsp87Prod P))
          (fun i => jsp87e (θ * (jsp87Cnt P (i + 1)))) := by
          rfl
      _ = jsp87CharFun P θ := by
          unfold jsp87CharFun
          rw [jsp87ProgFull_eq_Icc hQ, hIcc]
  rw [havg, hchar]

/-- **★ THE CLOSED FORM, FOR AN ARBITRARY EQUIDISTRIBUTED SAMPLE ★** -/
theorem jsp87CFgen_uniform_eq_prod (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) (hcard : 0 < S.card)
    (hu : jsp87Uniform S (jsp87Prod P)) :
    jsp87CFgen S P θ
      = ∏ p ∈ P, (1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ) := by
  rw [jsp87CFgen_uniform_eq_charFun S P hpc θ hcard hu]
  exact jsp87CharFun_eq_prod P hpc θ

/-- **THE MODULUS OF THE MEAN OF AN EQUIDISTRIBUTED SAMPLE IS THE MODULUS OF THE
CANONICAL MEAN.** -/
theorem jsp87CFgen_uniform_norm (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) (hcard : 0 < S.card)
    (hu : jsp87Uniform S (jsp87Prod P)) :
    ‖jsp87CFgen S P θ‖ = ‖jsp87CharFun P θ‖ :=
  congrArg (fun z : ℂ => ‖z‖) (jsp87CFgen_uniform_eq_charFun S P hpc θ hcard hu)

/-- **THE (5.15) ERROR OF *EVERY* SAMPLE IS AT LEAST `1` MINUS THE MODULUS OF THE
MEAN.**

No hypothesis on the sample: this is the triangle inequality, and it is what
turns `‖mean‖ → 0` into `jsp87Err1gen → 1`. -/
theorem jsp87Err1gen_sub_one (S : Finset ℕ) (P : Finset ℕ) (q : ℝ) :
    1 - ‖jsp87CFgen S P (q / 2)‖ ≤ jsp87Err1gen S P q := by
  have h3 := dist_triangle (1 : ℂ) (jsp87CFgen S P (q / 2)) 0
  have h5 : dist (1 : ℂ) (jsp87CFgen S P (q / 2))
      = ‖1 - jsp87CFgen S P (q / 2)‖ :=
    dist_eq_norm (a := (1 : ℂ)) (jsp87CFgen S P (q / 2))
  have h6 : dist (1 : ℂ) 0 = 1 := by norm_num [dist_eq_norm]
  have h7 : dist (jsp87CFgen S P (q / 2)) 0
      = ‖jsp87CFgen S P (q / 2)‖ :=
    (dist_eq_norm (a := jsp87CFgen S P (q / 2)) (0 : ℂ)).trans (by rw [sub_zero])
  rw [h6, h5, h7] at h3
  unfold jsp87Err1gen
  rw [norm_sub_rev]
  linarith

/-! ## §4  WHICH SAMPLES ARE EQUIDISTRIBUTED -/

/-- **A `Q`-DIVISION OF A SUM.** -/
private theorem jsp87div_add_mul_eq {Q a k : ℕ} (hQ : 0 < Q) (ha : a < Q) :
    (a + Q * k) / Q = k := by
  have h0 : a / Q = 0 := Nat.div_eq_of_lt ha
  have h1 : (a + Q * k) / Q = a / Q + k := Nat.add_mul_div_left a k hQ
  rw [h0, Nat.zero_add] at h1
  exact h1

/-- **A WHOLE NUMBER OF PERIODS, SHIFTED BY A RESIDUE, IS THAT RESIDUE.** -/
private theorem jsp87mod_add_mul_eq {Q a k : ℕ} (hQ : 0 < Q) (ha : a < Q) :
    (a + Q * k) % Q = a := by
  have h1 := Nat.div_add_mod (a + Q * k) Q
  rw [jsp87div_add_mul_eq hQ ha] at h1
  have h2 : Q * k + (a + Q * k) % Q = Q * k + a := by
    calc Q * k + (a + Q * k) % Q = a + Q * k := h1
      _ = Q * k + a := Nat.add_comm _ _
  exact Nat.add_left_cancel_iff.mp h2

/-- **THE RESIDUE CLASSES OF `N` CONSECUTIVE INTEGERS ARE HIT EQUALLY OFTEN WHEN
`Q ∣ N`.** -/
theorem jsp87Hits_range_dvd {Q N a : ℕ} (hQ : 0 < Q) (hN : Q ∣ N) (ha : a < Q) :
    jsp87Hits (Finset.range N) Q a = N / Q := by
  have hNQ : N = Q * (N / Q) := (Nat.mul_div_cancel' hN).symm
  have hmod : ∀ k : ℕ, (a + Q * k) % Q = a := fun k => jsp87mod_add_mul_eq hQ ha
  have hlt : ∀ k : ℕ, k < N / Q → a + Q * k < N := by
    intro k hk
    have h1 : k * Q + Q ≤ (N / Q) * Q := by
      have h1' := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt hk)
      rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at h1'
      simpa [Nat.mul_comm] using h1'
    have h2 : k * Q + Q ≤ N := by
      calc k * Q + Q ≤ (N / Q) * Q := h1
        _ = N := by
          calc (N / Q) * Q = Q * (N / Q) := Nat.mul_comm _ _
            _ = N := hNQ.symm
    have h3 : Q * k + Q ≤ N := by simpa [Nat.mul_comm] using h2
    omega
  have hcard0 : (Finset.range (N / Q)).card
      = ((Finset.range N).filter (fun i => i % Q = a)).card := by
    refine Finset.card_nbij' (s := Finset.range (N / Q))
      (t := (Finset.range N).filter (fun i => i % Q = a))
      (fun k : ℕ => a + Q * k) (fun i : ℕ => i / Q) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k < N / Q := Finset.mem_range.mp hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt k hk'), ?_⟩
      show (a + Q * k) % Q = a
      exact hmod k
    · intro i hi
      have hi' : i < N := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have h1 : Q * (i / Q) ≤ i := by
        have h2 := Nat.div_add_mod i Q
        omega
      have h2 : Q * (i / Q) < Q * (N / Q) := by
        calc Q * (i / Q) ≤ i := h1
          _ < N := hi'
          _ = Q * (N / Q) := hNQ
      have h3 : i / Q < N / Q := (Nat.mul_lt_mul_left hQ).mp h2
      exact Finset.mem_range.mpr h3
    · intro k hk
      have hk' : k < N / Q := Finset.mem_range.mp hk
      exact jsp87div_add_mul_eq hQ ha
    · intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
      have h3 := Nat.mod_add_div i Q
      show a + Q * (i / Q) = i
      omega
  rw [Finset.card_range] at hcard0
  exact hcard0.symm

/-- **THE INITIAL SEGMENT OF A WHOLE NUMBER OF PERIODS IS EQUIDISTRIBUTED.** -/
theorem jsp87Uniform_range {Q N : ℕ} (hQ : 0 < Q) (hN : Q ∣ N) :
    jsp87Uniform (Finset.range N) Q := by
  intro a ha b hb
  rw [jsp87Hits_range_dvd hQ hN ha, jsp87Hits_range_dvd hQ hN hb]

/-- **★ ANY NUMBER OF WHOLE PERIODS HAS THE SAME MEAN AS ONE PERIOD ★** -/
theorem jsp87CFgen_range_eq_prod (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ)
    {N : ℕ} (hN : 0 < N) (hd : jsp87Prod P ∣ N) :
    jsp87CFgen (Finset.range N) P θ
      = ∏ p ∈ P, (1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ) := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  exact jsp87CFgen_uniform_eq_prod (Finset.range N) P hpc θ
    (by rw [Finset.card_range]; exact hN) (jsp87Uniform_range hQ hd)

/-! ## §5  THE DECISIVE NEGATIVE RESULT, IN FULL GENERALITY -/

/-- **THE PRODUCT OF THE PRIMES OF ANY INTERVAL IS POSITIVE.** -/
private theorem jsp87prod_primeset_pos (B Y : ℕ) : 0 < jsp87Prod (jsp87PrimeSet B Y) := by
  rcases Finset.eq_empty_or_nonempty (jsp87PrimeSet B Y) with h | h
  · rw [h]
    unfold jsp87Prod
    simp
  · obtain ⟨p, hp⟩ := h
    have _ := jsp87dvd_prod_mem' (P := jsp87PrimeSet B Y) hp
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (jsp87PrimeSet_prime hi).pos

/-- **★ NO FAMILY OF EQUIDISTRIBUTED SAMPLES CAN RUN (5.15) ★**

Round 128 proved this for the single canonical sample
`jsp87Hypothesis15_ground_false`.  Here it is proved for **every** family of
samples each of which is equidistributed modulo the product of its own primes:
the obstruction of round 128 is a property of *uniformity*, not of the
particular sample. -/
theorem jsp87Hypothesis15fam_uniform_false (Ss : ℕ → Finset ℕ) (q : ℝ)
    (hcos : Real.cos (2 * Real.pi * (q / 2)) < 1) (κ1 κ2 κ3 : ℝ)
    (hκ : κ1 + κ2 + κ3 < 1) (hne : ∀ Y : ℕ, 0 < (Ss Y).card)
    (hu : jsp87UniformFam Ss 2) :
    ¬ jsp87Hypothesis15fam Ss 2 q κ1 κ2 κ3 := by
  intro h15
  obtain ⟨Y, hY⟩ := jsp87CharFun_norm_small (q / 2) hcos
    ((1 - (κ1 + κ2 + κ3)) / 2) (by linarith)
  have hQ : 0 < jsp87Prod (jsp87PrimeSet 2 Y) := jsp87prod_primeset_pos 2 Y
  have hun : jsp87Uniform (Ss Y) (jsp87Prod (jsp87PrimeSet 2 Y)) := hu Y hQ
  have hcard : 0 < (Ss Y).card := hne Y
  have hjoin : jsp87CFgen (Ss Y) (jsp87PrimeSet 2 Y) (q / 2)
      = jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2) :=
    jsp87CFgen_uniform_eq_charFun (Ss Y) (jsp87PrimeSet 2 Y)
      (fun r hr => jsp87PrimeSet_prime hr) (q / 2) hcard hun
  have hlow : 1 - ‖jsp87CFgen (Ss Y) (jsp87PrimeSet 2 Y) (q / 2)‖
      ≤ jsp87Err1gen (Ss Y) (jsp87PrimeSet 2 Y) q :=
    jsp87Err1gen_sub_one _ _ _
  rw [hjoin] at hlow
  have h15' := h15 Y hcard
  unfold jsp87Err1gen at h15' hlow
  rw [hjoin] at h15' hlow
  linarith

/-- **★ THE ENDGAME SAMPLE MUST BREAK EQUIDISTRIBUTION ★**

If (5.15) holds for the family `Ss` at the ground-truth scale with a total
constant `< 1`, then at some height the sample is **not** equidistributed
modulo the product of its own primes.  Together with §3 this says: the
published endgame of arXiv:2512.01739 cannot be run on any *uniform* sample,
so its sample must be a genuinely prime-correlated, non-uniform set of
integers. -/
theorem jsp87_sample_must_break_equidistribution (Ss : ℕ → Finset ℕ) (q : ℝ)
    (hcos : Real.cos (2 * Real.pi * (q / 2)) < 1) (κ1 κ2 κ3 : ℝ)
    (hκ : κ1 + κ2 + κ3 < 1) (hne : ∀ Y : ℕ, 0 < (Ss Y).card)
    (h15 : jsp87Hypothesis15fam Ss 2 q κ1 κ2 κ3) :
    ∃ Y : ℕ, ¬ jsp87Uniform (Ss Y) (jsp87Prod (jsp87PrimeSet 2 Y)) := by
  by_contra hcon
  push Not at hcon
  exact jsp87Hypothesis15fam_uniform_false Ss q hcos κ1 κ2 κ3 hκ hne
    (fun Y _ => hcon Y) h15

/-- **THE ENDGAME OF §§5.3–§5.14 IS UNSATISFIABLE ON EVERY EQUIDISTRIBUTED
FAMILY**: for every choice of the five sharp constants `κ_j < 1/30`, the
conjunction of (5.15) and (5.16)–(5.17) fails for all equidistributed sample
families. -/
theorem jsp87_endgame_uniformfam_blocked (Ss : ℕ → Finset ℕ) (q : ℝ)
    (hcos : Real.cos (2 * Real.pi * (q / 2)) < 1) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hne : ∀ Y : ℕ, 0 < (Ss Y).card) (hu : jsp87UniformFam Ss 2)
    (hκ : jsp87KappaSharp κ1 κ2 κ3 κ4 κ5) :
    ¬ ((jsp87Hypothesis15fam Ss 2 q κ1 κ2 κ3) ∧ (jsp87Hypothesis1617 0 1 q κ4 κ5)) := by
  rintro ⟨h15, _⟩
  have hsum : κ1 + κ2 + κ3 < 1 := by linarith [hκ.1, hκ.2.1, hκ.2.2.1]
  exact jsp87Hypothesis15fam_uniform_false Ss q hcos κ1 κ2 κ3 hsum hne hu h15

/-! ## §6  THE SHAPE OF WHAT REMAINS: THE MEAN IS A PROFILE–PHASE PAIRING -/

/-- **THE MEAN OVER A SAMPLE IS THE MASS-WEIGHTED AVERAGE OF THE PHASE
VALUES.**  This is `jsp87CFgen_eq_resAvg` with the masses spelled out, and it
holds for *every* finite sample. -/
theorem jsp87CFgen_eq_mass (S : Finset ℕ) (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime)
    (θ : ℝ) :
    jsp87CFgen S P θ
      = ∑ a ∈ Finset.range (jsp87Prod P),
          jsp87MassC S (jsp87Prod P) a * jsp87CFfun P θ a := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  rw [jsp87CFgen_eq_resAvg S P hpc θ, Finset.sum_div]
  refine Finset.sum_congr (M := ℂ) (s₁ := Finset.range (jsp87Prod P))
    (s₂ := Finset.range (jsp87Prod P)) rfl
      (fun a _ => by unfold jsp87MassC jsp87CFfun; ring)

/-- **THE MASSES OF AN EQUIDISTRIBUTED SAMPLE ARE ALL `1/Q`.** -/
theorem jsp87MassC_uniform (S : Finset ℕ) (Q : ℕ) (hQ : 0 < Q) (hcard : 0 < S.card)
    (hu : jsp87Uniform S Q) (a : ℕ) (ha : a < Q) :
    jsp87MassC S Q a = ((Q : ℕ) : ℂ)⁻¹ := by
  have hm : jsp87Hits S Q a = jsp87Hits S Q 0 :=
    jsp87hits_uniform S Q hQ hu a ha
  have hcard' : S.card = Q * jsp87Hits S Q a := by
    rw [hm]
    exact jsp87card_uniform S Q hQ hu
  have hN0 : ((S.card : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard)
  have hQ' : ((Q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmul : ((jsp87Hits S Q a : ℕ) : ℂ) * ((Q : ℕ) : ℂ) = ((S.card : ℕ) : ℂ) := by
    calc ((jsp87Hits S Q a : ℕ) : ℂ) * ((Q : ℕ) : ℂ)
        = ((jsp87Hits S Q a * Q : ℕ) : ℂ) := by rw [Nat.cast_mul]
      _ = ((Q * jsp87Hits S Q a : ℕ) : ℂ) := by rw [Nat.mul_comm]
      _ = ((S.card : ℕ) : ℂ) := by rw [hcard']
  have hne : ((jsp87Hits S Q a : ℕ) : ℂ) ≠ 0 := by
    intro hc0
    have hz : ((S.card : ℕ) : ℂ) = 0 := by
      rw [← hmul, hc0, zero_mul]
    exact hN0 hz
  unfold jsp87MassC
  rw [← hmul]
  field_simp

/-- **★ THE MEAN IS THE MASS–PHASE PAIRING, AND THE DEVIATION FROM THE CLOSED
FORM IS THE DEVIATION OF THAT PAIRING FROM THE UNIFORM ONE ★**

For **any** sample, the deviation of its complex mean from the canonical
(whole-period) mean is exactly

`∑_a (mass a − 1/Q) · (g a − 1)`,

the pairing of the *residue-profile deviation* (how far the sample is from
equidistributed modulo `∏ P`) with the *phase deviations* (how far the phase
`e (θ · cnt P (a+1))` is from `1`).  By §3 the profile deviations vanish exactly
on equidistributed samples, and by §5 those are precisely the samples on which
the endgame of arXiv:2512.01739 cannot run. -/
theorem jsp87CFgen_sub_charFun_eq_profile (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) (hcard : 0 < S.card) :
    jsp87CFgen S P θ - jsp87CharFun P θ
      = ∑ a ∈ Finset.range (jsp87Prod P),
          (jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹)
            * (jsp87CFfun P θ a - 1) := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hmass : (∑ a ∈ Finset.range (jsp87Prod P), jsp87MassC S (jsp87Prod P) a) = 1 := by
    have hsumC : (∑ a ∈ Finset.range (jsp87Prod P),
          ((jsp87Hits S (jsp87Prod P) a : ℕ) : ℂ)) = ((S.card : ℕ) : ℂ) := by
        calc (∑ a ∈ Finset.range (jsp87Prod P),
            ((jsp87Hits S (jsp87Prod P) a : ℕ) : ℂ))
            = ((∑ a ∈ Finset.range (jsp87Prod P), jsp87Hits S (jsp87Prod P) a : ℕ) : ℂ) :=
              (Nat.cast_sum (s := Finset.range (jsp87Prod P))
                (f := fun a => jsp87Hits S (jsp87Prod P) a)).symm
        _ = ((S.card : ℕ) : ℂ) :=
          congrArg (fun m : ℕ => (m : ℂ)) (jsp87card_res_total S (jsp87Prod P) hQ).symm
    unfold jsp87MassC
    rw [← Finset.sum_div, hsumC]
    exact div_self (by exact_mod_cast (ne_of_gt hcard))
  have hchar : (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
      / ((jsp87Prod P : ℕ) : ℂ) = jsp87CharFun P θ := by
    calc (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
        / ((jsp87Prod P : ℕ) : ℂ)
        = jsp87CAvg (Finset.range (jsp87Prod P)) (jsp87CFfun P θ) := by
          unfold jsp87CAvg
          rw [Finset.card_range]
      _ = jsp87CharFun P θ := by
          unfold jsp87CharFun
          rw [jsp87ProgFull_eq_Icc hQ]
          have hIcc : (Finset.Icc 0 (jsp87Prod P - 1) : Finset ℕ)
              = Finset.range (jsp87Prod P) := by
            ext x
            rw [Finset.mem_Icc, Finset.mem_range]
            omega
          rw [hIcc]
          rfl
  have hQ' : ((jsp87Prod P : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have key : ∀ a ∈ Finset.range (jsp87Prod P),
      (jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹)
          * (jsp87CFfun P θ a - 1)
        = jsp87MassC S (jsp87Prod P) a * jsp87CFfun P θ a
          - jsp87MassC S (jsp87Prod P) a
          - jsp87CFfun P θ a * ((jsp87Prod P : ℕ) : ℂ)⁻¹
          + ((jsp87Prod P : ℕ) : ℂ)⁻¹ := by
    intro a ha
    ring
  rw [jsp87CFgen_eq_mass S P hpc θ]
  rw [Finset.sum_congr (M := ℂ) (s₁ := Finset.range (jsp87Prod P))
    (s₂ := Finset.range (jsp87Prod P)) rfl key]
  rw [div_eq_mul_inv] at hchar
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hmass]
  have key2 : ∀ a ∈ Finset.range (jsp87Prod P),
      jsp87CFfun P θ a * ((jsp87Prod P : ℕ) : ℂ)⁻¹
        = ((jsp87Prod P : ℕ) : ℂ)⁻¹ * jsp87CFfun P θ a := by
    intro a ha
    ring
  rw [Finset.sum_congr (M := ℂ) (s₁ := Finset.range (jsp87Prod P))
    (s₂ := Finset.range (jsp87Prod P)) rfl key2]
  rw [← Finset.mul_sum]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hchar' : ((jsp87Prod P : ℕ) : ℂ)⁻¹
        * (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a) = jsp87CharFun P θ := by
      calc ((jsp87Prod P : ℕ) : ℂ)⁻¹
            * (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
          = (∑ a ∈ Finset.range (jsp87Prod P), jsp87CFfun P θ a)
              * ((jsp87Prod P : ℕ) : ℂ)⁻¹ := by ring
      _ = jsp87CharFun P θ := hchar
  rw [hchar']
  have hQQ : ((jsp87Prod P : ℕ) : ℂ) * ((jsp87Prod P : ℕ) : ℂ)⁻¹ = (1 : ℂ) :=
    mul_inv_cancel₀ hQ'
  rw [hQQ]
  ring

/-- **THE PROFILE–PHASE PAIRING IS BOUNDED BY THE TOTAL VARIATION OF THE
RESIDUE PROFILE.** -/
theorem jsp87CFgen_sub_charFun_norm_le (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) (hcard : 0 < S.card) :
    ‖jsp87CFgen S P θ - jsp87CharFun P θ‖
      ≤ ∑ a ∈ Finset.range (jsp87Prod P),
          ‖jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹‖
            * ‖jsp87CFfun P θ a - 1‖ := by
  have h := jsp87CFgen_sub_charFun_eq_profile S P hpc θ hcard
  rw [h]
  calc ‖∑ a ∈ Finset.range (jsp87Prod P),
      (jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹)
        * (jsp87CFfun P θ a - 1)‖
      ≤ ∑ _a ∈ Finset.range (jsp87Prod P),
          ‖(jsp87MassC S (jsp87Prod P) _a - ((jsp87Prod P : ℕ) : ℂ)⁻¹)
            * (jsp87CFfun P θ _a - 1)‖ := norm_sum_le ..
    _ = ∑ a ∈ Finset.range (jsp87Prod P),
          ‖jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹‖
            * ‖jsp87CFfun P θ a - 1‖ := by
        refine Finset.sum_congr (M := ℝ) (s₁ := Finset.range (jsp87Prod P))
          (s₂ := Finset.range (jsp87Prod P)) rfl (fun a _ => by rw [norm_mul])

/-- **★ THE (5.15) ERROR IS AT LEAST `1` MINUS THE MODULUS OF THE CANONICAL MEAN,
MINUS THE PROFILE–PHASE PAIRING ★**

This is the quantitative form of "the endgame sample must be prime-correlated".
For an equidistributed sample the profile term vanishes and this is exactly
`jsp87Err1gen_sub_one`, i.e. round 128's obstruction. -/
theorem jsp87Err1gen_lower_profile (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (q : ℝ) (hcard : 0 < S.card) :
    1 - ‖jsp87CharFun P (q / 2)‖
        - (∑ a ∈ Finset.range (jsp87Prod P),
            ‖jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹‖
              * ‖jsp87CFfun P (q / 2) a - 1‖)
      ≤ jsp87Err1gen S P q := by
  have h1 := jsp87Err1gen_sub_one S P q
  have h2 := jsp87CFgen_sub_charFun_norm_le S P hpc (q / 2) hcard
  have ha : (1 : ℂ) = (1 - jsp87CFgen S P (q / 2)) + jsp87CFgen S P (q / 2) := by ring
  have hb : jsp87CFgen S P (q / 2) - jsp87CharFun P (q / 2)
      + jsp87CharFun P (q / 2) = jsp87CFgen S P (q / 2) := by ring
  have h3 : ‖(1 : ℂ)‖ ≤ ‖1 - jsp87CFgen S P (q / 2)‖
      + ‖jsp87CFgen S P (q / 2) - jsp87CharFun P (q / 2)‖ + ‖jsp87CharFun P (q / 2)‖ := by
    calc ‖(1 : ℂ)‖
        = ‖(1 - jsp87CFgen S P (q / 2)) + jsp87CFgen S P (q / 2)‖ := by
          rw [show (1 : ℂ) - jsp87CFgen S P (q / 2) + jsp87CFgen S P (q / 2) = 1 by ring]
      _ ≤ ‖1 - jsp87CFgen S P (q / 2)‖ + ‖jsp87CFgen S P (q / 2)‖ :=
        norm_add_le (a := 1 - jsp87CFgen S P (q / 2)) (b := jsp87CFgen S P (q / 2))
      _ = ‖1 - jsp87CFgen S P (q / 2)‖
          + ‖(jsp87CFgen S P (q / 2) - jsp87CharFun P (q / 2)) + jsp87CharFun P (q / 2)‖ := by
          rw [show jsp87CFgen S P (q / 2) - jsp87CharFun P (q / 2)
              + jsp87CharFun P (q / 2) = jsp87CFgen S P (q / 2) from by ring]
      _ ≤ ‖1 - jsp87CFgen S P (q / 2)‖
          + ‖jsp87CFgen S P (q / 2) - jsp87CharFun P (q / 2)‖ + ‖jsp87CharFun P (q / 2)‖ := by
        have h9 := norm_add_le
          (a := jsp87CFgen S P (q / 2) - jsp87CharFun P (q / 2))
          (b := jsp87CharFun P (q / 2))
        linarith
  have h5 : ‖(1 : ℂ)‖ = 1 := by norm_num
  unfold jsp87Err1gen at h1
  rw [norm_sub_rev] at h1
  unfold jsp87Err1gen
  rw [norm_sub_rev]
  linarith

/-- **AN EQUIDISTRIBUTED SAMPLE HAS NO PROFILE DEVIATION.** -/
theorem jsp87CFgen_sub_charFun_zero_uniform (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (hcard : 0 < S.card)
    (hu : jsp87Uniform S (jsp87Prod P)) :
    ∀ a ∈ Finset.range (jsp87Prod P),
      jsp87MassC S (jsp87Prod P) a = ((jsp87Prod P : ℕ) : ℂ)⁻¹ := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  intro a ha
  exact jsp87MassC_uniform S (jsp87Prod P) hQ hcard hu a (Finset.mem_range.mp ha)

/-- **★ THE PAIRING VANISHES ON AN EQUIDISTRIBUTED SAMPLE ★**

so the sample mean equals the closed form — (5.15)'s error is then entirely
accounted for by the canonical mean, and the endgame is blocked. -/
theorem jsp87CFgen_sub_charFun_eq_zero_uniform (S : Finset ℕ) (P : Finset ℕ)
    (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) (hcard : 0 < S.card)
    (hu : jsp87Uniform S (jsp87Prod P)) :
    ∑ a ∈ Finset.range (jsp87Prod P),
        (jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹)
          * (jsp87CFfun P θ a - 1) = 0 := by
  have hQ : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hkey : ∀ a ∈ Finset.range (jsp87Prod P),
      (jsp87MassC S (jsp87Prod P) a - ((jsp87Prod P : ℕ) : ℂ)⁻¹)
        * (jsp87CFfun P θ a - 1) = (0 : ℂ) := by
    intro a ha
    rw [jsp87MassC_uniform S (jsp87Prod P) hQ hcard hu a (Finset.mem_range.mp ha)]
    ring
  rw [Finset.sum_congr (M := ℂ) (s₁ := Finset.range (jsp87Prod P))
    (s₂ := Finset.range (jsp87Prod P)) rfl hkey]
  exact Finset.sum_const_zero

end JSP87
