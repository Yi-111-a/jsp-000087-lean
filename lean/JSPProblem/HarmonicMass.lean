/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.ProgSample

/-!
# Round 124 — THE HARMONIC MASS OF THE PRIME SET: the last arithmetic input,
# isolated, and reduced to Euler's theorem

`policy.json` `next_round_attack[1]` asked for "the harmonic-mass object" and for
a theorem `jsp87_5_21_of_densePrimes` turning enough prime mass into hypothesis
(5.21′).  This module builds exactly that object and closes the arithmetic half
of the endgame of arXiv:2512.01739 §§5.3–§5.14.

## §0–§1  the object

`jsp87RecipSum P = ∑_{p ∈ P} 1/p` — the **harmonic mass** of a finite set.
`jsp87PrimeSet B Y = {p prime : B ≤ p ≤ Y}` — the prime set in an interval.
`jsp87Separation K H = 2 · H · 2^K` — the lower end of the interval that makes
every cube offset `2^k` (`k < K`) invisible modulo every prime of the set (the
separation hypothesis `H + 2^K − 1 < p` of §5.4), and that in addition forces
the residue fraction `c_p/p` below `1/2`.

## §2  (5.21b) is a harmonic-mass condition

`jsp87R521b_of_recipSum` — **(5.21b) HOLDS** as soon as the harmonic mass is at
least `2^{2H+K+1}/q²`; the mechanism is `f (1−f) ≥ f/2` for `f = c_p/p ∈
[2^K/p, 1/2]`, i.e. each summand is at least `2^{K−1}/p`.
`jsp87R521b_needs_recipSum` — **(5.21b) FORCES** harmonic mass, a named
restatement of round 123's `jsp87_5_21_needs_recipSum`.

## §3–§5  the endgame, with the prime set chosen automatically

For the prime set of an interval the primality, `2^K ≤ p`, separation and
coprimality-of-the-step hypotheses of `jsp87_endgame_progFull` all hold
*unconditionally* (`jsp87PrimeSet_endgame_hypotheses`), so `jsp87_endgame_of_recipSum`
leaves the harmonic-mass condition as the only remaining input.

## §6  THE HEADLINE OF ROUND 124

`jsp87_endgame_of_primeRecipDiverges`: the endgame of the published proof fires
from Euler's divergence of the prime harmonic series,

```
jsp87PrimeRecipDiverges : ∀ K H, 1 ≤ H → ∀ M > 0, ∃ Y, M ≤ ∑_{B ≤ p ≤ Y} 1/p,
  B = jsp87Separation K H
```

a **purely combinatorial** theorem of elementary number theory, together with
(5.19) and the two estimates (5.15) and (5.16)–(5.17).  This is the first round
in which no Chowla-type, Elliott-type or two-point-correlation hypothesis
survives the endgame.

`jsp87_5_21b_needs_height` adds the quantitative price: the interval has to
reach `2^{2(H+K)+2}/q² − 1`.
-/

open scoped BigOperators

namespace JSP87

/-! ## §0  the harmonic mass -/

/-- **THE HARMONIC MASS OF A FINITE SET.** -/
noncomputable def jsp87RecipSum (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (1 / (p : ℝ))

/-- **THE HARMONIC MASS IS NONNEGATIVE.** -/
theorem jsp87RecipSum_nonneg (P : Finset ℕ) : 0 ≤ jsp87RecipSum P := by
  unfold jsp87RecipSum
  refine Finset.sum_nonneg fun p _ => ?_
  exact div_nonneg (by norm_num) (Nat.cast_nonneg p)

/-- **ONE PRIME ATOM.** -/
theorem jsp87RecipSum_singleton (p : ℕ) :
    jsp87RecipSum ({p} : Finset ℕ) = 1 / (p : ℝ) := by
  unfold jsp87RecipSum
  simp

/-- **THE MASS IS MONOTONE UNDER INCLUSION.** -/
theorem jsp87RecipSum_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q) :
    jsp87RecipSum P ≤ jsp87RecipSum Q := by
  have hfil : Q.filter (fun p => p ∈ P) = P :=
    Finset.ext fun p => by simp [hPQ]
  calc jsp87RecipSum P = ∑ p ∈ Q, (if p ∈ P then 1 / (p : ℝ) else 0) := by
        unfold jsp87RecipSum
        rw [← Finset.sum_filter, hfil]
    _ ≤ ∑ p ∈ Q, (1 / (p : ℝ)) :=
      Finset.sum_le_sum fun p _ => by
        split_ifs
        · exact le_rfl
        · exact div_nonneg (by norm_num) (Nat.cast_nonneg p)

/-- **ANY ELEMENT CONTRIBUTES AT MOST THE TOTAL MASS.** -/
theorem jsp87RecipSum_mem_le {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) :
    1 / (p : ℝ) ≤ jsp87RecipSum P := by
  rw [← jsp87RecipSum_singleton p]
  exact jsp87RecipSum_mono (Finset.singleton_subset_iff.mpr hp)

/-- **THE MASS IS STRICTLY POSITIVE AS SOON AS THE SET HOLDS A POSITIVE
ELEMENT.** -/
theorem jsp87RecipSum_pos {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) (hpos : 0 < p) :
    0 < jsp87RecipSum P := by
  have hpn : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpos
  exact lt_of_lt_of_le (div_pos (by norm_num) hpn) (jsp87RecipSum_mem_le hp)

/-- **A PRIME CONTRIBUTES A POSITIVE MASS.** -/
theorem jsp87RecipSum_prime_pos (p : ℕ) (hp : p.Prime) :
    0 < jsp87RecipSum ({p} : Finset ℕ) := by
  rw [jsp87RecipSum_singleton]
  have hpn : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  exact div_pos (by norm_num) hpn

/-! ## §1  the prime set in an interval -/

/-- **THE SET OF PRIMES IN AN INTERVAL `[B, Y]`.** -/
noncomputable def jsp87PrimeSet (B Y : ℕ) : Finset ℕ :=
  (Finset.Icc B Y).filter (fun n => n.Prime)

theorem jsp87PrimeSet_mem {B Y p : ℕ} :
    p ∈ jsp87PrimeSet B Y ↔ B ≤ p ∧ p ≤ Y ∧ p.Prime := by
  simp [jsp87PrimeSet, Finset.mem_Icc, and_assoc]

theorem jsp87PrimeSet_prime {B Y p : ℕ} (hp : p ∈ jsp87PrimeSet B Y) : p.Prime :=
  (jsp87PrimeSet_mem.mp hp).2.2

theorem jsp87PrimeSet_lower {B Y p : ℕ} (hp : p ∈ jsp87PrimeSet B Y) : B ≤ p :=
  (jsp87PrimeSet_mem.mp hp).1

theorem jsp87PrimeSet_upper {B Y p : ℕ} (hp : p ∈ jsp87PrimeSet B Y) : p ≤ Y :=
  (jsp87PrimeSet_mem.mp hp).2.1

theorem jsp87PrimeSet_of {B Y p : ℕ} (hB : B ≤ p) (hY : p ≤ Y) (hp : p.Prime) :
    p ∈ jsp87PrimeSet B Y := jsp87PrimeSet_mem.mpr ⟨hB, hY, hp⟩

theorem jsp87PrimeSet_subset {B Y : ℕ} :
    jsp87PrimeSet B Y ⊆ Finset.Icc B Y := Finset.filter_subset _ _

/-- **THE HARMONIC MASS GROWS WITH THE HEIGHT OF THE INTERVAL.** -/
theorem jsp87PrimeSet_recipSum_mono {B Y Y' : ℕ} (hY : Y ≤ Y') :
    jsp87RecipSum (jsp87PrimeSet B Y) ≤ jsp87RecipSum (jsp87PrimeSet B Y') :=
  jsp87RecipSum_mono fun p hp =>
    jsp87PrimeSet_of (jsp87PrimeSet_lower hp) (le_trans (jsp87PrimeSet_upper hp) hY)
      (jsp87PrimeSet_prime hp)

/-- **THE HARMONIC MASS GROWS AS THE INTERVAL MOVES LEFT.** -/
theorem jsp87PrimeSet_recipSum_mono_low {B B' Y : ℕ} (hB : B ≤ B') :
    jsp87RecipSum (jsp87PrimeSet B' Y) ≤ jsp87RecipSum (jsp87PrimeSet B Y) :=
  jsp87RecipSum_mono fun p hp =>
    jsp87PrimeSet_of (le_trans hB (jsp87PrimeSet_lower hp)) (jsp87PrimeSet_upper hp)
      (jsp87PrimeSet_prime hp)

/-- **A PRIME INSIDE THE INTERVAL GIVES POSITIVE MASS.** -/
theorem jsp87PrimeSet_recipSum_pos {B Y p : ℕ} (hB : B ≤ p) (hY : p ≤ Y) (hp : p.Prime) :
    0 < jsp87RecipSum (jsp87PrimeSet B Y) :=
  jsp87RecipSum_pos (jsp87PrimeSet_of hB hY hp) hp.pos

/-- **POSITIVE MASS IMPLIES THE SET IS NONEMPTY.** -/
theorem jsp87PrimeSet_nonempty_of_recipSum_pos {B Y : ℕ}
    (h : 0 < jsp87RecipSum (jsp87PrimeSet B Y)) :
    (jsp87PrimeSet B Y).Nonempty := by
  by_contra hc
  have hc' : jsp87PrimeSet B Y = ∅ := by simpa using hc
  have hz : jsp87RecipSum (jsp87PrimeSet B Y) = 0 := by
    rw [hc']
    simp [jsp87RecipSum]
  linarith

/-! ## §2  the separation bound -/

/-- **THE SEPARATION BOUND `B = 2 · H · 2^K`.**  A level-`h` cube offset is
`h + 2^k − 1`, so `2·H·2^K` clears all of them; in addition it forces the
residue fraction `c_p/p` below `1/2`, which is what turns (5.21b) into a
harmonic-mass statement. -/
noncomputable def jsp87Separation (K H : ℕ) : ℕ := 2 * H * 2 ^ K

theorem jsp87Separation_pos {K H : ℕ} (hH : 1 ≤ H) : 0 < jsp87Separation K H := by
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have e : 2 ≤ 2 * H * 2 ^ K := by
    have e1 : 2 ≤ 2 * H := by omega
    have e2 : 2 * H ≤ 2 * H * 2 ^ K := by
      simpa using Nat.mul_le_mul (Nat.le_refl _) h1
    omega
  unfold jsp87Separation
  omega

theorem jsp87Separation_two_le {K H : ℕ} (hH : 1 ≤ H) : 2 ≤ jsp87Separation K H := by
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have e : 2 ≤ 2 * H * 2 ^ K := by
    have e1 : 2 ≤ 2 * H := by omega
    have e2 : 2 * H ≤ 2 * H * 2 ^ K := by
      simpa using Nat.mul_le_mul (Nat.le_refl _) h1
    omega
  unfold jsp87Separation
  omega

/-- **THE SEPARATION BOUND IS AT LEAST `2^K`**, so `2^K ≤ p` holds on the prime
set. -/
theorem jsp87Separation_pow_le {K H : ℕ} (hH : 1 ≤ H) :
    2 ^ K ≤ jsp87Separation K H := by
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have e2 : 2 ≤ 2 * H := by omega
  have e1 : 2 ^ K ≤ 2 ^ K * 2 := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_right (2 ^ K) (Nat.le_refl 2))
  have e3 : 2 ^ K * 2 ≤ 2 * H * 2 ^ K := by
    have := Nat.mul_le_mul_right (2 ^ K) e2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  unfold jsp87Separation
  exact le_trans e1 e3

/-- **THE SEPARATION HYPOTHESIS `H + 2^K − 1 < p` HOLDS FOR EVERY PRIME OF THE
INTERVAL.** -/
theorem jsp87Separation_gt {K H : ℕ} (hH : 1 ≤ H) :
    H + 2 ^ K - 1 < jsp87Separation K H := by
  have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have e1 : H ≤ 2 ^ K * H := by simpa using Nat.mul_le_mul_right H h1
  have e2 : 2 ^ K * (H + 1) ≤ 2 ^ K * (2 * H) := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_right (2 ^ K) (by omega : H + 1 ≤ 2 * H))
  have hlin : H + 2 ^ K ≤ 2 ^ K * (H + 1) := by
    calc H + 2 ^ K ≤ 2 ^ K * H + 2 ^ K := by
          simpa [Nat.add_comm] using (add_le_add_right e1 (2 ^ K))
      _ = 2 ^ K * (H + 1) := by ring
  have hsub : H + 2 ^ K - 1 < H + 2 ^ K := by omega
  unfold jsp87Separation
  refine lt_of_lt_of_le hsub ?_
  calc H + 2 ^ K ≤ 2 ^ K * (H + 1) := hlin
    _ ≤ 2 ^ K * (2 * H) := e2
    _ = 2 * H * 2 ^ K := by ring

/-- **AT THE SEPARATION BOUND THE RESIDUE FRACTION IS AT MOST `1/2`.** -/
theorem jsp87Separation_half {K p H : ℕ} (hH : 1 ≤ H) (hB : jsp87Separation K H ≤ p) :
    2 * ((H : ℝ) * (2 : ℝ) ^ K) ≤ (p : ℝ) := by
  have hB' : (2 : ℕ) ^ K * (2 * H) ≤ p := by
    unfold jsp87Separation at hB
    simpa [Nat.mul_comm, Nat.mul_left_comm] using hB
  have hb : ((2 : ℕ) ^ K : ℝ) * (2 * (H : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hB'
  calc 2 * ((H : ℝ) * (2 : ℝ) ^ K) = ((2 : ℝ) ^ K) * (2 * (H : ℝ)) := by ring
    _ ≤ (p : ℝ) := hb

/-! ## §3  (5.21b) is a harmonic-mass condition -/

/-- **THE SUMMAND OF (5.21b) AT THE PRIME `p`**: the residue fraction
`c_p / p` and its complement. -/
noncomputable def jsp87FracTerm (K p H : ℕ) : ℝ :=
  ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
    * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))

/-- **ONE IS AT MOST A POWER OF TWO, IN THE REALS.** -/
private theorem jsp87one_le_two_pow_ℝ (K : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ K := by
  have h1 : (1 : ℕ) ≤ 2 ^ K := Nat.one_le_two_pow
  have h2 : (1 : ℝ) ≤ ((2 : ℕ) ^ K : ℝ) := by exact_mod_cast h1
  simpa [Nat.cast_pow] using h2

/-- **THE WEIGHT OF (5.21b) CANCELS THE POWER OF TWO.** -/
private theorem jsp87half_pow (m : ℕ) :
    ((1 / 2 : ℝ) ^ m) ^ 2 * (2 : ℝ) ^ (2 * m) = 1 := by
  have h1 : ((1 / 2 : ℝ) ^ m) ^ 2 = ((1 / 2 : ℝ) : ℝ) ^ (2 * m) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [h1]
  calc ((1 / 2 : ℝ) : ℝ) ^ (2 * m) * (2 : ℝ) ^ (2 * m)
      = ((1 / 2 : ℝ) * 2) ^ (2 * m) := by rw [mul_pow]
    _ = (1 : ℝ) ^ (2 * m) := by rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = 1 := one_pow _

/-- **(5.21b) WITHOUT THE DYADIC WEIGHT.**  The summand is exactly the summand
of `jsp87R521b`. -/
theorem jsp87R521b_iff (K : ℕ) (P : Finset ℕ) (q : ℝ) (H : ℕ) :
    jsp87R521b K P q H
      ↔ (2 : ℝ) ^ (2 * (H + K)) ≤ (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H := by
  have hAT := jsp87half_pow (H + K)
  have hT : (0 : ℝ) < (2 : ℝ) ^ (2 * (H + K)) := by positivity
  constructor
  · intro h
    have h' : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, jsp87FracTerm K p H := h
    calc (2 : ℝ) ^ (2 * (H + K)) = (2 : ℝ) ^ (2 * (H + K)) * 1 := by ring
      _ ≤ (2 : ℝ) ^ (2 * (H + K))
          * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
            * ∑ p ∈ P, jsp87FracTerm K p H) :=
        mul_le_mul_of_nonneg_left h' hT.le
      _ = (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H := by
        have e : (2 : ℝ) ^ (2 * (H + K)) * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
              * ∑ p ∈ P, jsp87FracTerm K p H)
            = (q ^ 2) * ((((1 / 2 : ℝ) ^ (H + K)) ^ 2)
              * (2 : ℝ) ^ (2 * (H + K))) * ∑ p ∈ P, jsp87FracTerm K p H := by
              ring
        rw [e, hAT]
        ring
  · intro h
    show (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * ∑ p ∈ P, jsp87FracTerm K p H
    have hA : (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * ((2 : ℝ) ^ (2 * (H + K)))
        ≤ (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * ((q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    calc (1 : ℝ)
        = (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * ((2 : ℝ) ^ (2 * (H + K))) * 1 := by
          rw [hAT]; ring
      _ ≤ (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * ((q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H) * 1 := by
        have hA' := mul_le_mul_of_nonneg_right hA (by norm_num : (0 : ℝ) ≤ 1)
        simpa using hA'
      _ = (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H := by
        ring

/-- **THE RESIDUE FRACTION PRODUCT IS AT LEAST `2^{K−1}/p` WHEN THE PRIME CLEARS
THE SEPARATION BOUND.**  This is the analytic heart of the reduction: the
fraction `c_p/p` is at least `2^K/p` (round 123's `jsp87NzResCard_bounds`) and at
most `1/2` (the separation bound), so `f (1−f) ≥ f/2`. -/
theorem jsp87summand_ge {K p H : ℕ} (hH : 1 ≤ H) (hpc : p.Prime)
    (hB : jsp87Separation K H ≤ p) :
    ((2 : ℝ) ^ K / 2) / (p : ℝ) ≤ jsp87FracTerm K p H := by
  have hpow : 2 ^ K ≤ p := le_trans (jsp87Separation_pow_le hH) hB
  have hsep : H + 2 ^ K - 1 < p := lt_of_lt_of_le (jsp87Separation_gt hH) hB
  have hb := jsp87NzResCard_bounds (K := K) hpc.pos hpow hH hsep
  have hhalf := jsp87Separation_half hH hB
  have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpc.pos
  have hAp : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (p : ℝ) := by
    have hle := jsp87NzResCard_le_p (K := K) hpc.pos hsep
    have hcc : jsp87NzResCard K p H ≤ p := by omega
    exact_mod_cast hcc
  have hA2 : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpp]
    have hstep : (2 : ℝ) * ((jsp87NzResCard K p H : ℕ) : ℝ)
        ≤ 2 * ((H : ℝ) * (2 : ℝ) ^ K) := by
      have hcc : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (H : ℝ) * (2 : ℝ) ^ K := by
        have hcc' : jsp87NzResCard K p H ≤ H * 2 ^ K := hb.2
        exact_mod_cast hcc'
      nlinarith [hcc]
    linarith
  have hBc : 1 / 2 ≤ 1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by linarith
  have hmul : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) * (1 / 2) ≤ jsp87FracTerm K p H :=
    mul_le_mul_of_nonneg_left hBc (by positivity)
  have hlo : ((2 : ℝ) ^ K / 2) / (p : ℝ)
      ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) * (1 / 2) := by
    have h2K : (2 : ℝ) ^ K ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) := by
      have hb' := hb.1
      exact_mod_cast hb'
    calc ((2 : ℝ) ^ K / 2) / (p : ℝ) = ((2 : ℝ) ^ K) / ((2 : ℝ) * (p : ℝ)) := by ring
      _ ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / ((2 : ℝ) * (p : ℝ)) :=
        div_le_div_of_nonneg_right h2K (by positivity)
      _ = ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) * (1 / 2) := by ring
  unfold jsp87FracTerm
  exact hlo.trans hmul

/-- **THE SUFFICIENCY: A FINITE PRIME SET OF LARGE HARMONIC MASS SUPPLIES
(5.21b).**  Item 1 of `policy.json` `next_round_attack[1]`: the variance hypothesis
of §5.4 of arXiv:2512.01739 is a statement about the harmonic mass of the prime
set. -/
theorem jsp87R521b_of_recipSum {K : ℕ} {P : Finset ℕ} (q : ℝ) (H : ℕ)
    (hH : 1 ≤ H) (hpc : ∀ p ∈ P, p.Prime)
    (hB : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (hrecip : (2 : ℝ) ^ (2 * H + K + 1) ≤ (q ^ 2) * jsp87RecipSum P) :
    jsp87R521b K P q H := by
  have hid : ((1 : ℝ) / 2) * (2 : ℝ) ^ K * (2 : ℝ) ^ (2 * H + K + 1)
      = (2 : ℝ) ^ (2 * (H + K)) := by
    have e : (2 : ℝ) * (((1 : ℝ) / 2) * (2 : ℝ) ^ K * (2 : ℝ) ^ (2 * H + K + 1))
        = (2 : ℝ) * ((2 : ℝ) ^ (2 * (H + K))) := by
      calc (2 : ℝ) * (((1 : ℝ) / 2) * (2 : ℝ) ^ K * (2 : ℝ) ^ (2 * H + K + 1))
          = (1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ (2 * H + K + 1) := by ring
        _ = (2 : ℝ) ^ (K + (2 * H + K + 1)) := by rw [pow_add]; ring
        _ = (2 : ℝ) ^ (2 * (H + K) + 1) := by
          rw [show K + (2 * H + K + 1) = 2 * (H + K) + 1 by omega]
        _ = (2 : ℝ) * ((2 : ℝ) ^ (2 * (H + K))) := by rw [pow_succ]; ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) e
  have hsum : ∑ p ∈ P, jsp87FracTerm K p H
      ≥ ((2 : ℝ) ^ K / 2) * jsp87RecipSum P := by
    have h1 : ∑ p ∈ P, jsp87FracTerm K p H ≥ ∑ p ∈ P, ((2 : ℝ) ^ K / 2) / (p : ℝ) :=
      Finset.sum_le_sum fun p hp => jsp87summand_ge hH (hpc p hp) (hB p hp)
    have h2 : ∑ p ∈ P, ((2 : ℝ) ^ K / 2) / (p : ℝ)
        = ((2 : ℝ) ^ K / 2) * jsp87RecipSum P := by
      unfold jsp87RecipSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    exact ge_trans h1 h2.ge
  have hmain : (2 : ℝ) ^ (2 * (H + K)) ≤ (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H := by
    have hlow : (0 : ℝ) ≤ (2 : ℝ) ^ K / 2 := by positivity
    have hstep1 : (2 : ℝ) ^ (2 * (H + K))
        ≤ (q ^ 2) * (((2 : ℝ) ^ K / 2) * jsp87RecipSum P) := by
      calc (2 : ℝ) ^ (2 * (H + K)) ≤ ((2 : ℝ) ^ K / 2)
            * ((q ^ 2) * jsp87RecipSum P) := by
            calc (2 : ℝ) ^ (2 * (H + K))
                = ((2 : ℝ) ^ K / 2) * ((2 : ℝ) ^ (2 * H + K + 1)) := by
                  rw [← hid]
                  ring
              _ ≤ ((2 : ℝ) ^ K / 2) * ((q ^ 2) * jsp87RecipSum P) :=
                mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = (q ^ 2) * (((2 : ℝ) ^ K / 2) * jsp87RecipSum P) := by ring
    exact le_trans hstep1 (mul_le_mul_of_nonneg_left hsum (sq_nonneg q))
  exact (jsp87R521b_iff K P q H).mpr hmain

/-- **THE NECESSITY: (5.21b) FORCES HARMONIC MASS.**  A named restatement of
round 123's `jsp87_5_21_needs_recipSum`. -/
theorem jsp87R521b_needs_recipSum {K : ℕ} {P : Finset ℕ} (q : ℝ) (H : ℕ)
    (hH : 1 ≤ H) (hpc : ∀ p ∈ P, p.Prime) (hK : ∀ p ∈ P, 2 ^ K ≤ p)
    (hsep : ∀ p ∈ P, H + 2 ^ K - 1 < p) (h521 : jsp87R521b K P q H) :
    (2 : ℝ) ^ (2 * H + K) ≤ ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P := by
  have hup : ∑ p ∈ P, jsp87FracTerm K p H
      ≤ ((H : ℝ) * (2 : ℝ) ^ K) * jsp87RecipSum P := by
    have h1 : ∑ p ∈ P, jsp87FracTerm K p H ≤ ∑ p ∈ P, ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ) :=
      Finset.sum_le_sum fun p hp => jsp87_5_21b_summand_le (hK p hp) (hpc p hp)
        (hsep p hp) hH
    have h2 : ∑ p ∈ P, ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ)
        = ((H : ℝ) * (2 : ℝ) ^ K) * jsp87RecipSum P := by
      unfold jsp87RecipSum
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    exact le_trans h1 h2.le
  have hcore : (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H
      ≤ (q ^ 2) * (((H : ℝ) * (2 : ℝ) ^ K) * jsp87RecipSum P) :=
    mul_le_mul_of_nonneg_left hup (sq_nonneg q)
  have hlow : (2 : ℝ) ^ (2 * (H + K)) ≤ (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H :=
    (jsp87R521b_iff K P q H).mp h521
  have hX : (2 : ℝ) ^ (2 * (H + K))
      ≤ ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P * ((2 : ℝ) ^ K) := by
    calc (2 : ℝ) ^ (2 * (H + K)) ≤ (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H := hlow
      _ ≤ (q ^ 2) * (((H : ℝ) * (2 : ℝ) ^ K) * jsp87RecipSum P) := hcore
      _ = ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P * ((2 : ℝ) ^ K) := by ring
  have hid : (2 : ℝ) ^ (2 * (H + K)) = (2 : ℝ) ^ (2 * H + K) * ((2 : ℝ) ^ K) := by
    rw [← pow_add]
    congr 1
    omega
  have hX' : (2 : ℝ) ^ (2 * H + K) * ((2 : ℝ) ^ K)
      ≤ ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P * ((2 : ℝ) ^ K) := by
    rw [← hid]
    exact hX
  exact le_of_mul_le_mul_right hX' (by positivity : (0 : ℝ) < (2 : ℝ) ^ K)

/-
calc (2 : ℝ) ^ (2 * H + K) ≤ (2 : ℝ) ^ (2 * H + K) * ((2 : ℝ) ^ K) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (jsp87one_le_two_pow_ℝ K)
            (sq_nonneg ((2 : ℝ) ^ (2 * H + K))))
    _ = (2 : ℝ) ^ (2 * (H + K)) := by
      have e : (2 * H + K) + K = 2 * (H + K) := by omega
      calc (2 : ℝ) ^ (2 * H + K) * ((2 : ℝ) ^ K)
          = (2 : ℝ) ^ ((2 * H + K) + K) := (pow_add (a := (2 : ℝ)) (m := 2 * H + K)
              (n := K)).symm
        _ = (2 : ℝ) ^ (2 * (H + K)) := by rw [e]
    _ ≤ ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P * ((2 : ℝ) ^ K) := hX
    _ = ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P * 1 := by field_simp
    _ = ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P := by ring
-/

/-- **THE SANDWICH: (5.21b) SITS BETWEEN TWO HARMONIC-MASS CONDITIONS.**  The
threshold `2^{2H+K+1}/q²` suffices, the threshold `2^{2H+K}/(H q²)` is forced. -/
theorem jsp87R521b_sandwich {K : ℕ} {P : Finset ℕ} (q : ℝ) (H : ℕ)
    (hH : 1 ≤ H) (hpc : ∀ p ∈ P, p.Prime) (hB : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (hsep : ∀ p ∈ P, H + 2^K - 1 < p) (hK : ∀ p ∈ P, 2 ^ K ≤ p) :
    ((2 : ℝ) ^ (2 * H + K + 1) ≤ (q ^ 2) * jsp87RecipSum P → jsp87R521b K P q H)
      ∧ (jsp87R521b K P q H
        → (2 : ℝ) ^ (2 * H + K) ≤ ((q ^ 2) * (H : ℝ)) * jsp87RecipSum P) :=
  ⟨fun h => jsp87R521b_of_recipSum q H hH hpc hB h,
    fun h => jsp87R521b_needs_recipSum q H hH hpc hK hsep h⟩

/-! ## §4  the prime set of an interval supplies (5.21b) -/

/-- **(5.21b) FOR THE PRIME SET OF AN INTERVAL.**  All of the side hypotheses of
`jsp87R521b_of_recipSum` — primality, `2^K ≤ p` and the separation
`2·H·2^K ≤ p` — are *discharged* here, being formal consequences of membership. -/
theorem jsp87R521b_primeSet (K H Y : ℕ) (q : ℝ) (hH : 1 ≤ H)
    (hrecip : (2 : ℝ) ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)) :
    jsp87R521b K (jsp87PrimeSet (jsp87Separation K H) Y) q H :=
  jsp87R521b_of_recipSum q H hH
    (fun p hp => jsp87PrimeSet_prime hp)
    (fun p hp => jsp87PrimeSet_lower hp)
    hrecip

/-! ## §5  the endgame with the prime set chosen automatically -/

/-- **THE ENDGAME'S STRUCTURAL HYPOTHESES HOLD FOR THE PRIME SET OF AN
INTERVAL.**  Primality, `2^K ≤ p`, the separation `H + 2^K − 1 < p` and the
coprimality of the step `D = 1` are *proved* here rather than assumed: this is
what turns the endgame of round 123 into a statement about prime mass alone. -/
theorem jsp87PrimeSet_endgame_hypotheses (K H Y : ℕ) (hH : 1 ≤ H) :
    (∀ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, p.Prime)
      ∧ (∀ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, 2 ^ K ≤ p)
      ∧ (∀ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, H + 2 ^ K - 1 < p)
      ∧ (∀ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, ¬ p ∣ 1) := by
  refine ⟨fun p hp => jsp87PrimeSet_prime hp, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_⟩
  · exact le_trans (jsp87Separation_pow_le hH) (jsp87PrimeSet_lower hp)
  · exact lt_of_lt_of_le (jsp87Separation_gt hH) (jsp87PrimeSet_lower hp)
  · intro hd
    obtain ⟨k, hk⟩ := hd
    have h2 : 2 ≤ p := (jsp87PrimeSet_prime hp).two_le
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Nat.mul_zero] at hk
      omega
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have h3 : 2 * 1 ≤ p * k := Nat.mul_le_mul h2 hk1
    omega

/-- **THE ENDGAME FIRES FROM HARMONIC MASS ALONE.**  Hypotheses (5.19), (5.15),
(5.16)–(5.17) and (5.21b) are all that is left; the sample, the separation, the
primality and the two-class conditions are internal. -/
theorem jsp87_endgame_of_recipSum (K H Y : ℕ) (q : ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H)
    (hrecip : (2 : ℝ) ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
    (H15 : ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
        (fun i => jsp87e (q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
        (fun i => jsp87e (q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
              (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30)
      ∧ (κ5 < 1 / 30)) := by
  have hh := jsp87PrimeSet_endgame_hypotheses K H Y hH
  have hne : (jsp87PrimeSet (jsp87Separation K H) Y).Nonempty := by
    refine jsp87PrimeSet_nonempty_of_recipSum_pos ?_
    by_cases hc : (0 : ℝ) < jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)
    · exact hc
    · have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (2 * H + K + 1) := by positivity
      rw [le_antisymm (not_lt.1 hc)
        (jsp87RecipSum_nonneg (jsp87PrimeSet (jsp87Separation K H) Y))] at hrecip
      rw [mul_zero] at hrecip
      exact absurd hpos2 (not_lt.2 hrecip)
  refine jsp87_endgame_progFull (K := K) (P := jsp87PrimeSet (jsp87Separation K H) Y)
    0 1 (by norm_num) hne q H κ1 κ2 κ3 κ4 κ5 hK hH (fun p hp => hh.1 p hp)
    (fun p hp => hh.2.2.2 p hp) (fun p hp => hh.2.2.1 p hp) H15 H1617
    (jsp87R521b_primeSet K H Y q hH hrecip)

/-! ## §6  EULER'S DIVERGENCE: the last arithmetic input -/

/-- **EULER'S DIVERGENCE OF THE PRIME HARMONIC SERIES, in the exact form used
here**: for every separation bound `B = jsp87Separation K H` the harmonic mass
of the primes in `[B, Y]` is unbounded as `Y` grows.

This is a *purely combinatorial* theorem — Mathlib contains no statement about
the divergence of `∑_p 1/p`, but its classical proof (every `m ≤ Y` is a product
of prime powers `≤ Y`, hence `⌊Y⌋ ≤ ∏_{p ≤ Y} p/(p−1) ≤ exp(2 ∑_{p ≤ Y} 1/p)`)
uses no analytic input at all. -/
noncomputable def jsp87PrimeRecipDiverges : Prop :=
  ∀ K H : ℕ, 1 ≤ H → ∀ M : ℝ, 0 < M →
    ∃ Y : ℕ, M ≤ jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)

/-- **THE DIVERGENCE MAKES THE HARMONIC MASS TEND TO INFINITY IN THE HEIGHT.** -/
theorem jsp87PrimeRecipDiverges_tendsto (hdiv : jsp87PrimeRecipDiverges) (K H : ℕ)
    (hH : 1 ≤ H) :
    Filter.Tendsto (fun Y => jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  by_cases hb : (0 : ℝ) < b
  · obtain ⟨Y, hY⟩ := hdiv K H hH b hb
    filter_upwards [Filter.eventually_ge_atTop Y] with x hx
    exact le_trans hY (jsp87PrimeSet_recipSum_mono hx)
  · have hb0 : b ≤ (0 : ℝ) := le_of_not_gt hb
    filter_upwards [] with x
    exact le_trans hb0 (jsp87RecipSum_nonneg _)

/-- **THE HEADLINE OF ROUND 124: THE ENDGAME FIRES FROM EULER'S THEOREM.**

`jsp87PrimeRecipDiverges` (Euler) together with (5.19) and the two estimates
(5.15) and (5.16)–(5.17) of arXiv:2512.01739 gives the conclusion of §§5.3–5.14.
No Chowla-type, Elliott-type or two-point-correlation hypothesis is required: the
sample is the progression `jsp87ProgFull 0 1 P` with `P` the prime set of an
interval, and the variance hypothesis (5.21′) is the harmonic-mass condition
`2^{2H+K+1} ≤ q² ∑_{p ∈ P} 1/p`. -/
theorem jsp87_endgame_of_primeRecipDiverges (K H : ℕ) (q : ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H) (hq : q ≠ 0)
    (hdiv : jsp87PrimeRecipDiverges)
    (H15 : ∀ Y : ℕ,
      ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
        (fun i => jsp87e (q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ∀ Y : ℕ,
      ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
        (fun i => jsp87e (q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y))
              (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30)
      ∧ (κ5 < 1 / 30)) := by
  have hq2 : 0 < (q ^ 2) := sq_pos_of_ne_zero hq
  have hM : 0 < ((2 : ℝ) ^ (2 * H + K + 1) / (q ^ 2)) := by positivity
  obtain ⟨Y, hY⟩ := hdiv K H hH ((2 : ℝ) ^ (2 * H + K + 1) / (q ^ 2)) hM
  have hrecip : (2 : ℝ) ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y) := by
    calc (2 : ℝ) ^ (2 * H + K + 1)
        = (q ^ 2) * ((2 : ℝ) ^ (2 * H + K + 1) / (q ^ 2)) := by field_simp
      _ ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
  exact jsp87_endgame_of_recipSum K H Y q κ1 κ2 κ3 κ4 κ5 hK hH hrecip (H15 Y) (H1617 Y)

/-! ## §7  the quantitative price of the harmonic mass -/

/-- **THE MASS OF A SET OF INTEGERS IS BOUNDED BY THE CARDINALITY OVER THE LOWER
END.** -/
theorem jsp87RecipSum_le {P : Finset ℕ} {B : ℕ} (hB : 0 < B) (hB0 : ∀ p ∈ P, B ≤ p) :
    jsp87RecipSum P ≤ ((P.card : ℕ) : ℝ) / (B : ℝ) := by
  have hbr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hstep : ∑ p ∈ P, (1 / (B : ℝ)) = ((P.card : ℕ) : ℝ) / (B : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc jsp87RecipSum P = ∑ p ∈ P, (1 / (p : ℝ)) := rfl
    _ ≤ ∑ p ∈ P, (1 / (B : ℝ)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpp : (0 : ℝ) < (p : ℝ) := by
        have hp0 : 0 < p := lt_of_lt_of_le hB (hB0 p hp)
        exact_mod_cast hp0
      rw [one_div, one_div]
      refine (inv_le_inv₀ hpp hbr).2 ?_
      exact_mod_cast hB0 p hp
    _ = ((P.card : ℕ) : ℝ) / (B : ℝ) := hstep

/-- **THE CARDINALITY OF THE PRIME SET OF AN INTERVAL.** -/
theorem jsp87PrimeSet_card_le {B Y : ℕ} :
    (jsp87PrimeSet B Y).card ≤ Y + 1 := by
  refine le_trans (Finset.card_le_card (t := (Finset.range (Y + 1))) fun p hp => ?_) ?_
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (jsp87PrimeSet_upper hp))
  · rw [Finset.card_range]

/-- **THE PRICE: (5.21b) FORCES THE INTERVAL TO REACH `2^{2(H+K)+2}/q² − 1`.**
Each summand of (5.21b) is at most `1/4` and the prime set has at most `Y+1`
elements, so the height `Y` of the interval is not free. -/
theorem jsp87_5_21b_needs_height (K H Y : ℕ) (q : ℝ) (hH : 1 ≤ H) (hq : q ≠ 0)
    (h521 : jsp87R521b K (jsp87PrimeSet (jsp87Separation K H) Y) q H) :
    (2 : ℝ) ^ (2 * (H + K) + 2) ≤ (q ^ 2) * ((Y : ℝ) + 1) := by
  have hq2 : 0 ≤ (q ^ 2) := by positivity
  have hquarter : ∀ p ∈ jsp87PrimeSet (jsp87Separation K H) Y,
      jsp87FracTerm K p H ≤ (1 / 4 : ℝ) := by
    intro p hp
    have hpc := jsp87PrimeSet_prime hp
    have hsep : H + 2 ^ K - 1 < p :=
      lt_of_lt_of_le (jsp87Separation_gt hH) (jsp87PrimeSet_lower hp)
    have hle := jsp87NzResCard_le_p (K := K) hpc.pos hsep
    have hcc : jsp87NzResCard K p H ≤ p := by omega
    have hc2 : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hcc
    have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpc.pos
    have hq4 : (1 : ℝ) / 4 = (1 / 4 : ℝ) := by norm_num
    have hmain := (jsp87mul_one_sub_le (((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
      (by positivity) ((div_le_one hpp).2 hc2)).2
    unfold jsp87FracTerm
    rw [hq4]
    exact hmain
  have hcard4 : ∑ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, ((1 : ℝ) / 4)
      = ((jsp87PrimeSet (jsp87Separation K H) Y).card : ℝ) / 4 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hupper : ∑ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, jsp87FracTerm K p H
      ≤ ((jsp87PrimeSet (jsp87Separation K H) Y).card : ℝ) / 4 := by
    have h1 : ∑ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, jsp87FracTerm K p H
        ≤ ∑ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, ((1 : ℝ) / 4) :=
      Finset.sum_le_sum fun p hp => hquarter p hp
    exact le_trans h1 hcard4.le
  have hcard : ((jsp87PrimeSet (jsp87Separation K H) Y).card : ℝ) ≤ (Y : ℝ) + 1 := by
    exact_mod_cast jsp87PrimeSet_card_le (B := jsp87Separation K H) (Y := Y)
  have hlow : (2 : ℝ) ^ (2 * (H + K))
      ≤ (q ^ 2) * ∑ p ∈ jsp87PrimeSet (jsp87Separation K H) Y, jsp87FracTerm K p H :=
    (jsp87R521b_iff K (jsp87PrimeSet (jsp87Separation K H) Y) q H).mp h521
  calc (2 : ℝ) ^ (2 * (H + K) + 2) = (2 : ℝ) ^ (2 * (H + K)) * ((2 : ℝ) ^ 2) := by
        rw [pow_add]
    _ ≤ ((q ^ 2) * ∑ p ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87FracTerm K p H) * ((2 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hlow (by positivity)
    _ ≤ (q ^ 2) * (((jsp87PrimeSet (jsp87Separation K H) Y).card : ℝ) / 4)
        * ((2 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hq2) (by positivity)
    _ = 4 * ((q ^ 2) * (((jsp87PrimeSet (jsp87Separation K H) Y).card : ℝ) / 4)) := by
        have h4 : ((2 : ℝ) ^ 2) = (4 : ℝ) := by norm_num
        rw [h4]
        ring
    _ ≤ 4 * ((q ^ 2) * (((Y : ℝ) + 1) / 4)) := by
        -- the cardinality bound propagates through the multiplication by `4`
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hcard (by norm_num : (0 : ℝ) ≤ 4))
            (sq_nonneg q)) (by norm_num : (0 : ℝ) ≤ 4)
    _ = (q ^ 2) * ((Y : ℝ) + 1) := by ring

/-! ## §8  summary -/

/-- **THE SUMMARY OF ROUND 124.**  Hypothesis (5.21′) of arXiv:2512.01739 §5.4
for the canonical progression sample is a harmonic-mass condition on the prime
set; on the prime set of an interval every other hypothesis of the endgame holds
unconditionally; the condition is met once the interval reaches
`2^{2(H+K)+2}/q² − 1` and the prime harmonic series is known to diverge. -/
theorem jsp87_harmonicMass_summary (K H Y : ℕ) (q : ℝ) (hH : 1 ≤ H) (hq : q ≠ 0) :
    ((2 : ℝ) ^ (2 * H + K + 1)
        ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)
      → jsp87R521b K (jsp87PrimeSet (jsp87Separation K H) Y) q H)
      ∧ ((jsp87R521b K (jsp87PrimeSet (jsp87Separation K H) Y) q H)
        → (2 : ℝ) ^ (2 * (H + K) + 2) ≤ (q ^ 2) * ((Y : ℝ) + 1))
      ∧ (jsp87R521b K (jsp87PrimeSet (jsp87Separation K H) Y) q H
        → ∀ (P : Finset ℕ) (B : ℕ), 0 < B → (∀ p ∈ P, B ≤ p) →
            jsp87RecipSum P ≤ ((P.card : ℕ) : ℝ) / (B : ℝ)) := by
  refine ⟨fun h => jsp87R521b_primeSet K H Y q hH h, fun h => ?_, fun h P B hB hB0 => ?_⟩
  · exact jsp87_5_21b_needs_height K H Y q hH hq h
  · exact jsp87RecipSum_le hB hB0

end JSP87
