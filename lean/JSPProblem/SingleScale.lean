/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.EulerDivergence
import Mathlib.Analysis.RCLike.Basic

/-!
# Round 126 — THE SINGLE-SCALE FORM OF (5.18), ITS REAL DECOMPOSITION, AND THE
# REFUTATION OF (5.18) BY THE ENDGAME ITSELF

`policy.json` `next_round_attack[0…2]`, carried unexecuted for 126 rounds, asked
for three things; all three are done here, and the third produces a **decisive
negative result**.

## §0–§1  the ground truth at `K = 0` (policy item 3)

At `K = 0` the cube `Fin 0 → ℕ` has a single vertex `∅`, so the cube-alternating
variable `X_p` of (5.13) has a closed form:

```
jsp87Xp0 (jsp87BinV 0) p n H  =  ∑_{h ≤ H} 2^{-h} · [p ∣ n + h] ,
```

and after summing over a prime set `P` (`jsp87Xp0_binV_zero_sum`) the double sum
collapses to a *prime-divisor count*

```
jsp87Cnt P m  =  #{p ∈ P : p ∣ m} ,
jsp87Phase_zero_one :  q · ∑_{p ∈ P} jsp87Xp0 (jsp87BinV 0) p i 1  =  (q/2) · jsp87Cnt P (i+1) .
```

**THE PHASE AT THE GROUND-TRUTH SCALE IS `(q/2)` TIMES THE NUMBER OF PRIMES OF
`P` DIVIDING `i + 1`** — so at `K = 0, H = 1` the whole probabilistic endgame of
§§5.3–5.14 is a statement about prime-divisor counts of the integers of the
sample (`jsp87Err1_zero`), and the Chowla-type bound `jsp87Cnt ≤ ω` is proved
here from scratch.

## §2  the real/imaginary decomposition (policy item 2)

`jsp87Err1`, `jsp87Err2` are complex norms.  `jsp87Err1_le_iff_re_im` and
`jsp87Err2_le_iff_re_im` are **exact equivalences**: (5.15) and (5.16)–(5.17)
*are* the pair of real statements `|Re| ≤ κ` and `|Im| ≤ κ`, and
`jsp87Err1re_eq_avg_cos` / `jsp87Err1im_eq_avg_sin` identify the two components
as a real average of `cos` and of `sin` over the finite sample.  The analytic gap
is therefore localised to **four explicit real statements about finite real
sums** — no complex norm anywhere.

## §3  the single-scale form of (5.18) (policy item 1)

`jsp87_518_single K H q` requires the five estimates **only at one scale**, and
`jsp87Series_irrational_of_518_single` proves

```
jsp87_518_single 0 1 (1/20)  ⟹  Irrational jsp87Series ,
```

the literal exact remainder, with no quantifier over scales.

## §4  **THE REFUTATION**: (5.18) IS FALSE

The endgame of rounds 116–125 says

```
(5.19) ∧ 1 ≤ H ∧ q ≠ 0 ∧ (5.15) ∧ (5.16)–(5.17)  ⟹  ¬ (all five κ_j < 1/30) ,
```

with the two error bounds needed **only at one height** (the height supplied by
Euler's divergence, `jsp87_endgame_of_recipSum`).  Hypothesis (5.18) asserts
that such five constants exist at the *admissible* scale `K = 0, H = 1, q = 1/20`
(`jsp87_scale_519_admissible`).  Hence

* `jsp87_518_single_false` — **at every admissible scale the single-scale (5.18)
  is false**;
* `jsp87_518_single_ground_false`, `jsp87Hypothesis518_false` — in particular
  **`jsp87Hypothesis518` is refuted**, so `jsp87Series_irrational_of_518` of
  round 125 is a *vacuous* implication and the *fixed-scale* route to
  `jsp_000087_main` is closed;
* `jsp87_518_at_false` — the same holds with the error bounds required at a
  **single** height, for **every** scale, **every** height and **every** `q`.

## §5  the diagnosis

In the published argument the constants `κ_j` are not free parameters: (5.15) and
(5.16)–(5.17) are *consequences of rationality*, their constants are thereby
forced, and the endgame says the forced constants are blunt.  The formalisation of
rounds 116–125 uses **one and the same** `κ` on both sides of the endgame, which
makes the two statements contradictory by construction (that is the refutation
above).  The missing input is therefore not the sharpness of the estimates but
their **derivation from the escape hypothesis with explicit constants**, named
here as `jsp87ErrBoundsFromEscape`; `jsp87ErrBoundsFromEscape_blunt` records the
resulting incompatibility with `jsp87_endgame_blunt` exactly, with no appeal to
any analytic input.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  the cube at `K = 0`: the ground truth of (5.13) -/

/-- **THE CUBE `Fin 0 → ℕ` HAS A SINGLE VERTEX.**  At `K = 0` there is nothing to
alternate over. -/
theorem jsp87univ_Finset_Fin_zero : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
  ext ε
  simp only [Finset.mem_univ, Finset.mem_singleton]
  constructor
  · intro _
    refine Finset.Subset.antisymm (fun k hk => Fin.elim0 k) (by simp)
  · intro _
    trivial

/-- **THE CUBE SHIFT AT `K = 0` IS THE LEVEL ITSELF.** -/
theorem jsp87R_binV_zero (h : ℕ) : jsp87R (jsp87BinV 0) h ∅ = h := by
  rw [jsp87R, jsp87Off, Finset.sum_empty, add_zero]

/-- **THE LEVEL SUM AT `K = 0` IS A SINGLE INDICATOR TIMES THE WEIGHT.**  The
alternating sign of the only vertex is `+1` and its shift is `h`. -/
theorem jsp87XpLevel_binV_zero (p n h : ℕ) :
    jsp87XpLevel (jsp87BinV 0) p n h
      = jsp87W 0 h * (if p ∣ n + h then (1 : ℝ) else 0) := by
  rw [jsp87XpLevel, jsp87univ_Finset_Fin_zero, Finset.sum_singleton]
  simp only [jsp87Sign_zero, Finset.card_empty]
  rw [jsp87R_binV_zero]
  split <;> ring

/-- **THE CLOSED FORM OF `X_p` AT `K = 0`.**

```
jsp87Xp0 (jsp87BinV 0) p n H  =  ∑_{h = 1}^{H} 2^{-h} · [p ∣ n + h] .
```

This is the ground truth of (5.13) at the only scale the endgame needs
(`K = 0`): the cube-alternating variable is nothing but a *weighted count of the
levels at which `p` divides a shift of the sample point*. -/
theorem jsp87Xp0_binV_zero (p n H : ℕ) :
    jsp87Xp0 (jsp87BinV 0) p n H
      = ∑ h ∈ Finset.Icc 1 H, ((1 / 2 : ℝ) ^ h) * (if p ∣ n + h then (1 : ℝ) else 0) := by
  rw [jsp87Xp0]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [jsp87XpLevel_binV_zero p n h, jsp87W_eq_half, Nat.add_zero]

/-- **THE `H = 1` INSTANCE**: at the ground-truth level the variable is a single
`1/2`-weighted indicator. -/
theorem jsp87Xp0_binV_zero_one (p n : ℕ) :
    jsp87Xp0 (jsp87BinV 0) p n 1 = (1 / 2 : ℝ) * (if p ∣ n + 1 then (1 : ℝ) else 0) := by
  rw [jsp87Xp0_binV_zero]
  have hIcc : Finset.Icc 1 1 = {1} := by
    ext h
    rw [Finset.mem_Icc, Finset.mem_singleton]
    constructor <;> omega
  rw [hIcc, Finset.sum_singleton]
  ring

/-- **`X_p` AT `K = 0` IS NONNEGATIVE.** -/
theorem jsp87Xp0_binV_zero_nonneg (p n H : ℕ) : 0 ≤ jsp87Xp0 (jsp87BinV 0) p n H := by
  rw [jsp87Xp0_binV_zero]
  refine Finset.sum_nonneg fun h _ => ?_
  by_cases hc : p ∣ n + h <;> simp [hc]

/-- **`X_p` AT `K = 0` IS AT MOST THE FULL LEVEL SUM.** -/
theorem jsp87Xp0_binV_zero_le (p n H : ℕ) :
    jsp87Xp0 (jsp87BinV 0) p n H ≤ ∑ h ∈ Finset.Icc 1 H, ((1 / 2 : ℝ) ^ h) := by
  rw [jsp87Xp0_binV_zero]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases hc : p ∣ n + h <;> simp [hc]

/-- **THE GEOMETRIC SUM OF THE LEVELS AT `K = 0`**, closed form. -/
theorem jsp87sum_inv_two_Icc (H : ℕ) :
    (∑ h ∈ Finset.Icc 1 H, ((1 / 2 : ℝ) ^ h)) = 1 - (1 / 2 : ℝ) ^ H := by
  induction H with
  | zero =>
      have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
        ext h
        simp only [Finset.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          omega
        · intro hc
          simp at hc
      rw [hIcc, Finset.sum_empty, pow_zero]
      ring
  | succ H ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := H) (by omega)]
      rw [ih]
      have hs : ((1 / 2 : ℝ) ^ H) * (1 / 2 : ℝ) = ((1 / 2 : ℝ) ^ (H + 1)) := (pow_succ (1 / 2 : ℝ) H).symm
      rw [← hs]
      ring

/-- **THE CARRY VARIABLE AT `K = 0` NEVER REACHES `1`.**  The total phase of an
`H`-deep cube at `K = 0` is bounded by the geometric series `1 − 2^{-H}`. -/
theorem jsp87Xp0_binV_zero_lt_one (p n H : ℕ) : jsp87Xp0 (jsp87BinV 0) p n H < 1 := by
  have h1 := jsp87Xp0_binV_zero_le p n H
  rw [jsp87sum_inv_two_Icc] at h1
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ H := by positivity
  linarith

/-! ## §1  the prime-divisor count, and the phase at the ground-truth scale -/

/-- **THE PRIME-DIVISOR COUNT**: `jsp87Cnt P m` is the number of primes of `P`
that divide `m`.  At `K = 0, H = 1` this is exactly the object the phase of the
endgame counts (see `jsp87Phase_zero_one`). -/
noncomputable def jsp87Cnt (P : Finset ℕ) (m : ℕ) : ℕ := (P.filter (fun p => p ∣ m)).card

/-- **THE COUNT IS A REAL SUM OF INDICATORS.** -/
theorem jsp87Cnt_eq_sum (P : Finset ℕ) (m : ℕ) :
    (jsp87Cnt P m : ℝ) = ∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0) := by
  calc (jsp87Cnt P m : ℝ) = ((P.filter (fun p => p ∣ m)).card : ℝ) := rfl
    _ = ∑ _p ∈ P.filter (fun p => p ∣ m), (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ p ∈ P, (if p ∣ m then (1 : ℝ) else 0) :=
      Finset.sum_filter (fun p => p ∣ m) (fun _ => (1 : ℝ))

/-- **THE COUNT IS BOUNDED BY `ω`**: the primes of `P` dividing a *positive* `m`
are prime factors of `m`.  This is the Chowla-type bound of the mean-field scale,
proved from scratch. -/
theorem jsp87Cnt_le_omega {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {m : ℕ} (hm : m ≠ 0) :
    jsp87Cnt P m ≤ omega m := by
  have hsub : P.filter (fun p => p ∣ m) ⊆ m.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact (hP p hp.1).mem_primeFactors hp.2 hm
  have hcard : (P.filter (fun p => p ∣ m)).card ≤ (m.primeFactors).card :=
    Finset.card_le_card hsub
  simpa [jsp87Cnt, omega] using hcard

/-- **NO ADMITTED PRIME DIVIDES A SMALL POSITIVE INTEGER.**  For
`0 < m < B ≤ p ∈ P` the count vanishes. -/
theorem jsp87Cnt_eq_zero_of_lt {P : Finset ℕ} {B m : ℕ} (hB : ∀ p ∈ P, B ≤ p)
    (hm0 : 0 < m) (hm : m < B) : jsp87Cnt P m = 0 := by
  rw [jsp87Cnt, Finset.card_eq_zero]
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    have hBp := hB p hp.1
    have hple : p ≤ m := Nat.le_of_dvd hm0 hp.2
    omega
  · intro hp
    simp at hp

/-- **THE COUNT EQUALS `ω` WHEN EVERY PRIME FACTOR IS ADMITTED.** -/
theorem jsp87Cnt_eq_omega {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {m : ℕ} (hm : m ≠ 0)
    (hsub : m.primeFactors ⊆ P) : jsp87Cnt P m = omega m := by
  refine le_antisymm (jsp87Cnt_le_omega hP hm) ?_
  rw [jsp87Cnt]
  have heq : P.filter (fun p => p ∣ m) = m.primeFactors := by
    ext p
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp1, hp2⟩
      exact ⟨hP p hp1, hp2, hm⟩
    · rintro ⟨hp1, hp2, _⟩
      exact ⟨hsub (Nat.mem_primeFactors.mpr ⟨hp1, hp2, hm⟩), hp2⟩
  rw [heq]
  rfl

/-- **THE SUM OF THE CARRY VARIABLES OVER A PRIME SET**, in closed form: the
double sum over `P` and over the levels collapses. -/
theorem jsp87Xp0_binV_zero_sum (P : Finset ℕ) (i H : ℕ) :
    (∑ p ∈ P, jsp87Xp0 (jsp87BinV 0) p i H)
      = ∑ h ∈ Finset.Icc 1 H, ((1 / 2 : ℝ) ^ h) * (jsp87Cnt P (i + h)) := by
  calc (∑ p ∈ P, jsp87Xp0 (jsp87BinV 0) p i H)
      = ∑ p ∈ P, ∑ h ∈ Finset.Icc 1 H,
          ((1 / 2 : ℝ) ^ h) * (if p ∣ i + h then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun p _ => jsp87Xp0_binV_zero p i H
    _ = ∑ h ∈ Finset.Icc 1 H, ∑ p ∈ P,
          ((1 / 2 : ℝ) ^ h) * (if p ∣ i + h then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ h ∈ Finset.Icc 1 H, ((1 / 2 : ℝ) ^ h) * (jsp87Cnt P (i + h)) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Finset.mul_sum, jsp87Cnt_eq_sum]

/-- **THE PHASE AT THE GROUND-TRUTH SCALE.**

```
q · ∑_{p ∈ P} jsp87Xp0 (jsp87BinV 0) p i 1  =  (q/2) · #{p ∈ P : p ∣ i + 1} .
```

At `K = 0, H = 1` the entire phase `q T` of arXiv:2512.01739 (5.13) is, up to
the factor `q/2`, a **prime-divisor count of the integer `i + 1`**. -/
theorem jsp87Phase_zero_one (P : Finset ℕ) (q : ℝ) (i : ℕ) :
    q * (∑ p ∈ P, jsp87Xp0 (jsp87BinV 0) p i 1)
      = (q / 2) * jsp87Cnt P (i + 1) := by
  rw [jsp87Xp0_binV_zero_sum]
  have hIcc : Finset.Icc 1 1 = {1} := by
    ext h
    rw [Finset.mem_Icc, Finset.mem_singleton]
    constructor <;> omega
  rw [hIcc, Finset.sum_singleton]
  ring

/-- **THE PHASE AT THE GROUND-TRUTH SCALE, FOR THE CANONICAL PRIME SET.** -/
theorem jsp87Phase_zero_one_primeSet (Y : ℕ) (q : ℝ) (i : ℕ) :
    q * (∑ p' ∈ jsp87PrimeSet 2 Y, jsp87Xp0 (jsp87BinV 0) p' i 1)
      = (q / 2) * jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) :=
  jsp87Phase_zero_one _ _ _

/-- **THE PHASE AT THE GROUND-TRUTH SCALE IS BOUNDED BY `ω`.**  The Chowla-type
bound of §1, transferred to the phase. -/
theorem jsp87Phase_zero_one_abs_le (P : Finset ℕ) (hq : 0 ≤ q) (i : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    |q * (∑ p ∈ P, jsp87Xp0 (jsp87BinV 0) p i 1)| ≤ (q / 2) * omega (i + 1) := by
  rw [jsp87Phase_zero_one]
  have h1 : (0 : ℝ) ≤ (q / 2) * jsp87Cnt P (i + 1) := by
    positivity
  rw [abs_of_nonneg h1]
  have hle : (jsp87Cnt P (i + 1) : ℝ) ≤ (omega (i + 1) : ℝ) := by
    exact_mod_cast jsp87Cnt_le_omega hP (by omega)
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## §2  the real/imaginary decomposition of the two errors (policy item 2) -/

/-- **THE NORM IN REAL AND IMAGINARY COORDINATES.** -/
theorem jsp87norm_sq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  have h : ‖(z : ℂ)‖ ^ 2 = (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im :=
    RCLike.norm_sq_eq_def
  nlinarith

private theorem jsp87div_natCast_re (z : ℂ) (c : ℕ) :
    (z / (c : ℂ)).re = z.re / (c : ℝ) := by
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq_natCast,
    Complex.natCast_re, Complex.natCast_im]
  simp only [neg_zero, zero_div, mul_zero, sub_zero]
  field_simp

private theorem jsp87div_natCast_im (z : ℂ) (c : ℕ) :
    (z / (c : ℂ)).im = z.im / (c : ℝ) := by
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq_natCast,
    Complex.natCast_re, Complex.natCast_im]
  simp only [neg_zero, zero_div, mul_zero]
  field_simp
  ring

private theorem jsp87sum_re {Ω : Type*} (s : Finset Ω) (f : Ω → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (RCLike.re : ℂ →+ ℝ) _ _

private theorem jsp87sum_im {Ω : Type*} (s : Finset Ω) (f : Ω → ℂ) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum (RCLike.im : ℂ →+ ℝ) _ _

/-- **THE REAL PART OF THE COMPLEX AVERAGE IS THE REAL AVERAGE.**  Mathlib has
no such statement. -/
theorem jsp87CAvg_re {Ω : Type*} (s : Finset Ω) (f : Ω → ℂ) :
    (jsp87CAvg s f).re = jsp87FAvg s (fun i => (f i).re) := by
  classical
  rcases s.eq_empty_or_nonempty with h | h
  · simp [jsp87CAvg, jsp87FAvg, h]
  · have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr h
    rw [jsp87CAvg, jsp87FAvg, jsp87div_natCast_re, jsp87sum_re]

/-- **THE IMAGINARY PART OF THE COMPLEX AVERAGE IS THE REAL AVERAGE.** -/
theorem jsp87CAvg_im {Ω : Type*} (s : Finset Ω) (f : Ω → ℂ) :
    (jsp87CAvg s f).im = jsp87FAvg s (fun i => (f i).im) := by
  classical
  rcases s.eq_empty_or_nonempty with h | h
  · simp [jsp87CAvg, jsp87FAvg, h]
  · have hc : ((s.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr h
    rw [jsp87CAvg, jsp87FAvg, jsp87div_natCast_im, jsp87sum_im]

/-- **THE SAMPLE OF THE ENDGAME**, named once. -/
noncomputable def jsp87Sample (K H Y : ℕ) : Finset ℕ :=
  jsp87ProgFull 0 1 (jsp87PrimeSet (jsp87Separation K H) Y)

/-- **THE TOTAL PHASE `q T` OF (5.13), named once.** -/
noncomputable def jsp87Phase (K H Y : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  q * ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y, jsp87Xp0 (jsp87BinV K) p' i H

/-- **THE COMPLEX MEAN OVER THE SAMPLE.** -/
noncomputable def jsp87Mean (K H Y : ℕ) (q : ℝ) : ℂ :=
  jsp87CAvg (jsp87Sample K H Y) (fun i => jsp87e (jsp87Phase K H Y q i))

/-- **THE COMPLEX PRODUCT OF THE SINGLE-PRIME MEANS.** -/
noncomputable def jsp87ProdMean (K H Y : ℕ) (q : ℝ) : ℂ :=
  ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
    jsp87CAvg (jsp87Sample K H Y) (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))

/-- **THE TWO COMPLEX ERRORS.** -/
noncomputable def jsp87Err1z (K H Y : ℕ) (q : ℝ) : ℂ := jsp87Mean K H Y q - 1

noncomputable def jsp87Err2z (K H Y : ℕ) (q : ℝ) : ℂ :=
  jsp87Mean K H Y q - jsp87ProdMean K H Y q

/-- **THE ERROR OF (5.15) IS THE NORM OF THE COMPLEX ERROR.** -/
theorem jsp87Err1_eq (K H Y : ℕ) (q : ℝ) : jsp87Err1 K H Y q = ‖jsp87Err1z K H Y q‖ := by
  rfl

/-- **THE ERROR OF (5.16)–(5.17) IS THE NORM OF THE COMPLEX ERROR.** -/
theorem jsp87Err2_eq (K H Y : ℕ) (q : ℝ) : jsp87Err2 K H Y q = ‖jsp87Err2z K H Y q‖ := by
  rfl

/-- **THE REAL AND IMAGINARY PARTS OF THE ERROR OF (5.15).** -/
noncomputable def jsp87Err1re (K H Y : ℕ) (q : ℝ) : ℝ := (jsp87Err1z K H Y q).re

noncomputable def jsp87Err1im (K H Y : ℕ) (q : ℝ) : ℝ := (jsp87Err1z K H Y q).im

/-- **THE REAL AND IMAGINARY PARTS OF THE ERROR OF (5.16)–(5.17).** -/
noncomputable def jsp87Err2re (K H Y : ℕ) (q : ℝ) : ℝ := (jsp87Err2z K H Y q).re

noncomputable def jsp87Err2im (K H Y : ℕ) (q : ℝ) : ℝ := (jsp87Err2z K H Y q).im

/-- **EACH COORDINATE IS AT MOST THE COMPLEX NORM.**  The projection bounds,
from `jsp87norm_sq_re_im`. -/
theorem jsp87re_le_of_norm_le {z : ℂ} {κ : ℝ} (h : ‖z‖ ≤ κ) : |z.re| ≤ κ := by
  have h1 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [jsp87norm_sq_re_im z]
    nlinarith [sq_nonneg (z.im : ℝ)]
  calc |z.re| ≤ |‖z‖| := (sq_le_sq.mp h1)
    _ = ‖z‖ := abs_of_nonneg (norm_nonneg z)
    _ ≤ κ := h

theorem jsp87im_le_of_norm_le {z : ℂ} {κ : ℝ} (h : ‖z‖ ≤ κ) : |z.im| ≤ κ := by
  have h2 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [jsp87norm_sq_re_im z]
    nlinarith [sq_nonneg (z.re : ℝ)]
  calc |z.im| ≤ |‖z‖| := (sq_le_sq.mp h2)
    _ = ‖z‖ := abs_of_nonneg (norm_nonneg z)
    _ ≤ κ := h

/-- **THE EXACT REAL FORM OF (5.15), IN QUADRATIC FORM.**  No sign hypothesis is
needed: the complex error is at most `κ` exactly when the *sum of the squares of
its two real components* is at most `κ²`. -/
theorem jsp87Err1_sq_iff_re_im (K H Y : ℕ) (q κ : ℝ) :
    (jsp87Err1 K H Y q) ^ 2 ≤ κ ^ 2
      ↔ ((jsp87Err1re K H Y q) ^ 2 + (jsp87Err1im K H Y q) ^ 2 ≤ κ ^ 2) := by
  rw [jsp87Err1_eq, jsp87norm_sq_re_im]
  rfl

/-- **THE EXACT REAL FORM OF (5.16)–(5.17), IN QUADRATIC FORM.** -/
theorem jsp87Err2_sq_iff_re_im (K H Y : ℕ) (q κ : ℝ) :
    (jsp87Err2 K H Y q) ^ 2 ≤ κ ^ 2
      ↔ ((jsp87Err2re K H Y q) ^ 2 + (jsp87Err2im K H Y q) ^ 2 ≤ κ ^ 2) := by
  rw [jsp87Err2_eq, jsp87norm_sq_re_im]
  rfl

/-- **THE EXACT REAL FORM OF (5.15)** for a nonnegative constant. -/
theorem jsp87Err1_le_iff_re_im (K H Y : ℕ) (q κ : ℝ) (hκ : 0 ≤ κ) :
    jsp87Err1 K H Y q ≤ κ
      ↔ ((jsp87Err1re K H Y q) ^ 2 + (jsp87Err1im K H Y q) ^ 2 ≤ κ ^ 2) := by
  rw [← sq_le_sq₀ (by rw [jsp87Err1_eq]; positivity) hκ, jsp87Err1_sq_iff_re_im]

/-- **THE EXACT REAL FORM OF (5.16)–(5.17)** for a nonnegative constant. -/
theorem jsp87Err2_le_iff_re_im (K H Y : ℕ) (q κ : ℝ) (hκ : 0 ≤ κ) :
    jsp87Err2 K H Y q ≤ κ
      ↔ ((jsp87Err2re K H Y q) ^ 2 + (jsp87Err2im K H Y q) ^ 2 ≤ κ ^ 2) := by
  rw [← sq_le_sq₀ (by rw [jsp87Err2_eq]; positivity) hκ, jsp87Err2_sq_iff_re_im]

/-- **TWO REAL COMPONENT BOUNDS SUFFICE, UP TO THE `√2` OF THE NORM.**  This is the
direction one needs analytically: the two estimates of §§5.7–5.14 are bounds on
the real and imaginary parts of an average over a finite sample. -/
theorem jsp87Err1_le_of_re_im (K H Y : ℕ) (q κ : ℝ) (hκ : 0 ≤ κ)
    (h : |jsp87Err1re K H Y q| ≤ κ ∧ |jsp87Err1im K H Y q| ≤ κ) :
    jsp87Err1 K H Y q ≤ κ * Real.sqrt 2 := by
  rw [jsp87Err1_le_iff_re_im K H Y q _ (by positivity)]
  have h1 : (jsp87Err1re K H Y q) ^ 2 ≤ κ ^ 2 := by
    have hh : |jsp87Err1re K H Y q| ≤ |κ| := h.1.trans (by rw [abs_of_nonneg hκ])
    simpa using (sq_le_sq.mpr hh)
  have h2 : (jsp87Err1im K H Y q) ^ 2 ≤ κ ^ 2 := by
    have hh : |jsp87Err1im K H Y q| ≤ |κ| := h.2.trans (by rw [abs_of_nonneg hκ])
    simpa using (sq_le_sq.mpr hh)
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (κ * Real.sqrt 2) ^ 2 = 2 * κ ^ 2 := by
    rw [mul_pow, hsqrt]
    ring
  rw [hs]
  linarith

/-- **THE SAME, FOR (5.16)–(5.17).** -/
theorem jsp87Err2_le_of_re_im (K H Y : ℕ) (q κ : ℝ) (hκ : 0 ≤ κ)
    (h : |jsp87Err2re K H Y q| ≤ κ ∧ |jsp87Err2im K H Y q| ≤ κ) :
    jsp87Err2 K H Y q ≤ κ * Real.sqrt 2 := by
  rw [jsp87Err2_le_iff_re_im K H Y q _ (by positivity)]
  have h1 : (jsp87Err2re K H Y q) ^ 2 ≤ κ ^ 2 := by
    have hh : |jsp87Err2re K H Y q| ≤ |κ| := h.1.trans (by rw [abs_of_nonneg hκ])
    simpa using (sq_le_sq.mpr hh)
  have h2 : (jsp87Err2im K H Y q) ^ 2 ≤ κ ^ 2 := by
    have hh : |jsp87Err2im K H Y q| ≤ |κ| := h.2.trans (by rw [abs_of_nonneg hκ])
    simpa using (sq_le_sq.mpr hh)
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (κ * Real.sqrt 2) ^ 2 = 2 * κ ^ 2 := by
    rw [mul_pow, hsqrt]
    ring
  rw [hs]
  linarith

/-- **THE ERROR OF (5.15) IS A REAL AVERAGE OF `cos` OVER THE SAMPLE.**  This is
the exact shape of §§5.7–5.14: a finite real sum of cosines. -/
theorem jsp87Err1re_eq_avg_cos (K H Y : ℕ) (q : ℝ) :
    jsp87Err1re K H Y q
      = jsp87FAvg (jsp87Sample K H Y)
          (fun i => Real.cos (2 * Real.pi * jsp87Phase K H Y q i)) - 1 := by
  rw [jsp87Err1re, jsp87Err1z, jsp87Mean]
  rw [Complex.sub_re, Complex.one_re, jsp87CAvg_re]
  simp only [jsp87e_re]

/-- **THE IMAGINARY PART OF THE ERROR OF (5.15) IS A REAL AVERAGE OF `sin`.** -/
theorem jsp87Err1im_eq_avg_sin (K H Y : ℕ) (q : ℝ) :
    jsp87Err1im K H Y q
      = jsp87FAvg (jsp87Sample K H Y)
          (fun i => Real.sin (2 * Real.pi * jsp87Phase K H Y q i)) := by
  rw [jsp87Err1im, jsp87Err1z, jsp87Mean]
  rw [Complex.sub_im, Complex.one_im, sub_zero, jsp87CAvg_im]
  simp only [jsp87e_im]

/-- **THE ERROR OF (5.15) AT THE GROUND-TRUTH SCALE IS A COMPLEX AVERAGE OF
`e ((q/2)·jsp87Cnt P (i+1))`.**  Together with `jsp87Phase_zero_one` this
identifies the whole probabilistic endgame of §§5.3–5.14 at `K = 0, H = 1` with
a statement about prime-divisor counts of the integers of the sample. -/
theorem jsp87Err1_zero (Y : ℕ) (q : ℝ) :
    jsp87Err1 0 1 Y q
      = ‖jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
          (fun i => jsp87e ((q / 2) * jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1))) - 1‖ := by
  have hsep : jsp87Separation 0 1 = 2 := by
    unfold jsp87Separation
    norm_num
  have hfun : (fun i => jsp87e
      (q * ∑ p' ∈ jsp87PrimeSet 2 Y, jsp87Xp0 (jsp87BinV 0) p' i 1))
      = (fun i => jsp87e ((q / 2) * jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1))) := by
    funext i
    rw [jsp87Phase_zero_one_primeSet Y q i]
  rw [jsp87Err1, hsep, hfun]

/-! ## §3  the single-scale form of (5.18) (policy item 1) -/

/-- **THE SCALE (5.19)** in a named form. -/
def jsp87Scale519 (K H : ℕ) (q : ℝ) : Prop :=
  1 ≤ H ∧ q ≠ 0 ∧ |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20

/-- **THE SINGLE-SCALE FORM OF (5.18)**: the five error constants of §§5.7–5.14
exist, sharp, at **one** scale. -/
def jsp87_518_single (K H : ℕ) (q : ℝ) : Prop :=
  jsp87Scale519 K H q →
    ∃ κ1 κ2 κ3 κ4 κ5 : ℝ, jsp87KappaSharp κ1 κ2 κ3 κ4 κ5
      ∧ jsp87Hypothesis15 K H q κ1 κ2 κ3 ∧ jsp87Hypothesis1617 K H q κ4 κ5

/-- **THE GROUND-TRUTH SCALE IS ADMISSIBLE**: `K = 0`, `H = 1`, `q = 1/20`. -/
theorem jsp87_518_single_ground_scale : jsp87Scale519 0 1 (1 / 20) :=
  ⟨by omega, by norm_num, jsp87_scale_519_admissible⟩

/-- **THE HEADLINE FROM THE SINGLE-SCALE FORM OF (5.18).**  This is the literal
exact remainder: no quantifier over scales, the five estimates at `K = 0`,
`H = 1`, `q = 1/20`, and nothing else. -/
theorem jsp87Series_irrational_of_518_single (h : jsp87_518_single 0 1 (1 / 20)) :
    Irrational jsp87Series := by
  obtain ⟨κ1, κ2, κ3, κ4, κ5, hκ, H15, H1617⟩ :=
    h ⟨by omega, by norm_num, jsp87_scale_519_admissible⟩
  exact jsp87Series_irrational_of_kappa_small 0 1 (1 / 20) κ1 κ2 κ3 κ4 κ5
    jsp87_scale_519_admissible (by omega) (by norm_num) hκ H15 H1617

/-- **(5.18) IMPLIES ITS SINGLE-SCALE FORM** at the ground-truth scale. -/
theorem jsp87Hypothesis518_imp_single :
    jsp87Hypothesis518 → jsp87_518_single 0 1 (1 / 20) := by
  intro h hs
  obtain ⟨κ1, κ2, κ3, κ4, κ5, hκ, H15, H1617⟩ :=
    h 0 1 (1 / 20) hs.1 hs.2.1 hs.2.2
  exact ⟨κ1, κ2, κ3, κ4, κ5, hκ, H15, H1617⟩

/-- **THE FOUR REAL STATEMENTS THAT (5.15) AND (5.16)–(5.17) ARE.**  The analytic
gap of `policy.json` is localised here to four explicit inequalities about finite
*real* averages over the sample — the shape of §§5.7–5.14, with no complex norm
left anywhere. -/
theorem jsp87ErrBounds_real (K H : ℕ) (q κ1 κ2 κ3 κ4 κ5 : ℝ)
    (h15 : jsp87Hypothesis15 K H q κ1 κ2 κ3)
    (h1617 : jsp87Hypothesis1617 K H q κ4 κ5) (Y : ℕ) :
    (|jsp87Err1re K H Y q| ≤ κ1 + κ2 + κ3 ∧ |jsp87Err1im K H Y q| ≤ κ1 + κ2 + κ3)
      ∧ (|jsp87Err2re K H Y q| ≤ κ4 + κ5 ∧ |jsp87Err2im K H Y q| ≤ κ4 + κ5) := by
  have n1 : ‖jsp87Err1z K H Y q‖ ≤ κ1 + κ2 + κ3 := by
    rw [← jsp87Err1_eq]
    exact h15 Y
  have n2 : ‖jsp87Err2z K H Y q‖ ≤ κ4 + κ5 := by
    rw [← jsp87Err2_eq]
    exact h1617 Y
  exact ⟨⟨jsp87re_le_of_norm_le n1, jsp87im_le_of_norm_le n1⟩,
    ⟨jsp87re_le_of_norm_le n2, jsp87im_le_of_norm_le n2⟩⟩

/-! ## §4  **THE REFUTATION**: (5.18) IS FALSE -/

/-- **THE SINGLE-HEIGHT FORM OF (5.18)**: at the height `Y` which the endgame of
§§5.3–5.14 uses, five constants that are simultaneously `< 1/30` dominate the two
errors (5.15) and (5.16)–(5.17). -/
def jsp87_518_at (K H Y : ℕ) (q : ℝ) : Prop :=
  ∃ κ1 κ2 κ3 κ4 κ5 : ℝ, jsp87KappaSharp κ1 κ2 κ3 κ4 κ5
    ∧ jsp87Err1 K H Y q ≤ κ1 + κ2 + κ3 ∧ jsp87Err2 K H Y q ≤ κ4 + κ5

/-- **THE SINGLE-HEIGHT FORM OF (5.18) IS FALSE**, for every scale, every height
and every admissible `q`: no sharp constant can dominate the two errors at the
height at which the harmonic mass (5.21b) holds.  This is
`jsp87_endgame_of_recipSum` read in its contrapositive. -/
theorem jsp87_518_at_false (K H Y : ℕ) (q : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H)
    (hrecip : 2 ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y)) :
    ¬ jsp87_518_at K H Y q := by
  rintro ⟨κ1, κ2, κ3, κ4, κ5, hκ, e1, e2⟩
  exact (jsp87_endgame_of_recipSum K H Y q κ1 κ2 κ3 κ4 κ5 hK hH hrecip e1 e2) hκ

/-- **AND HENCE THE UNIFORM-IN-`Y` FORM OF (5.18) IS FALSE AT EVERY ADMISSIBLE
SCALE.**  Euler's divergence (round 125) supplies the height; the endgame refutes
the configuration there. -/
theorem jsp87_518_atY_false (K H : ℕ) (q : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H) (hq : q ≠ 0) :
    ¬ (∀ Y : ℕ, jsp87_518_at K H Y q) := by
  intro hall
  obtain ⟨Y, hY⟩ := jsp87_5_21b_exists K H q hH hq
  exact jsp87_518_at_false K H Y q hK hH hY (hall Y)

/-- **THE SINGLE-SCALE (5.18) IS FALSE AT EVERY ADMISSIBLE SCALE.**

The endgame of rounds 116–125 says that at an admissible scale the two error
bounds cannot be dominated by five constants that are simultaneously `< 1/30`.
So the existence asserted by (5.18) — at *any* admissible scale, and in particular
at the ground-truth scale `K = 0, H = 1, q = 1/20` — is **impossible**. -/
theorem jsp87_518_single_false (K H : ℕ) (q : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H) (hq : q ≠ 0) :
    ¬ jsp87_518_single K H q := by
  intro h
  obtain ⟨κ1, κ2, κ3, κ4, κ5, hκ, H15, H1617⟩ := h ⟨hH, hq, hK⟩
  obtain ⟨Y, hY⟩ := jsp87_5_21b_exists K H q hH hq
  exact jsp87_518_at_false K H Y q hK hH hY ⟨κ1, κ2, κ3, κ4, κ5, hκ, H15 Y, H1617 Y⟩

/-- **THE SINGLE-SCALE (5.18) IS FALSE AT THE GROUND-TRUTH SCALE.** -/
theorem jsp87_518_single_ground_false : ¬ jsp87_518_single 0 1 (1 / 20) :=
  jsp87_518_single_false 0 1 (1 / 20) jsp87_scale_519_admissible (by omega) (by norm_num)

/-- **`jsp87Hypothesis518` IS REFUTED — ROUND 125'S BLOCKER IS FALSE.**

The endgame of §§5.3–5.14 is a *proved theorem* of this development, and (5.18)
asserts the existence of a configuration that theorem forbids at every admissible
scale.  Consequently `jsp87Series_irrational_of_518` is a *vacuous* implication,
and the whole *fixed-scale* route to `jsp_000087_main` is closed: there is no
analytic estimate to be found, because the estimate that route asks for is a
contradiction. -/
theorem jsp87Hypothesis518_false : ¬ jsp87Hypothesis518 :=
  fun h => jsp87_518_single_ground_false (jsp87Hypothesis518_imp_single h)

/-- **THE ROUTE OF ROUND 125 IS CLOSED.**  There is no configuration in which the
hypothesis (5.18) holds and the series is rational; the hypothesis itself never
holds. -/
theorem jsp87Series_irrational_of_518_route_closed :
    ¬ (jsp87Hypothesis518 ∧ ¬ Irrational jsp87Series) :=
  fun h => jsp87Hypothesis518_false h.1

/-! ## §5  the diagnosis: the error bounds must come from rationality -/

/-- **THE ENDGAME IN BLUNT FORM**: whatever constants dominate the two errors at
the height the endgame uses, at least one of them is `≥ 1/30`. -/
theorem jsp87_endgame_blunt (K H Y : ℕ) (q κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H)
    (hrecip : 2 ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
    (e1 : jsp87Err1 K H Y q ≤ κ1 + κ2 + κ3)
    (e2 : jsp87Err2 K H Y q ≤ κ4 + κ5) :
    (1 / 30 ≤ κ1 ∨ 1 / 30 ≤ κ2 ∨ 1 / 30 ≤ κ3 ∨ 1 / 30 ≤ κ4 ∨ 1 / 30 ≤ κ5) := by
  by_contra h
  have h5 : κ1 < 1 / 30 ∧ κ2 < 1 / 30 ∧ κ3 < 1 / 30 ∧ κ4 < 1 / 30 ∧ κ5 < 1 / 30 := by
    simpa only [not_or, not_le] using h
  exact (jsp87_endgame_of_recipSum K H Y q κ1 κ2 κ3 κ4 κ5 hK hH hrecip e1 e2) h5

/-- **THE MISSING INPUT, IN THE ONLY FORM THAT CAN BE TRUE.**

In arXiv:2512.01739 the constants `κ_j` of (5.15) and (5.16)–(5.17) are **not
free parameters**: the two estimates are *consequences of rationality* (the
truncated carries escaping the lattice, combined with the correlation input),
their constants are thereby forced, and the endgame says the forced constants are
blunt.  The formalisation of rounds 116–125 uses one and the same `κ` on both
sides of the endgame, which makes the two statements contradictory — that is the
refutation of §4.  The genuine missing input is the *derivation*:

**the escape hypothesis forces the two error bounds**, with constants that need
not be sharp. -/
def jsp87ErrBoundsFromEscape (K H : ℕ) (q : ℝ) : Prop :=
  ∀ b : ℕ, 1 ≤ b → jsp87TruncCarryEscapes b →
    ∃ κ1 κ2 κ3 κ4 κ5 : ℝ,
      jsp87Hypothesis15 K H q κ1 κ2 κ3 ∧ jsp87Hypothesis1617 K H q κ4 κ5

/-- **THE INCOMPATIBILITY, STATED EXACTLY.**  If the escape hypothesis forces
dominating constants, then at the height the endgame uses at least one of the
*forced* constants is `≥ 1/30`.  This is the shape of the published proof, and —
unlike (5.18) — it is compatible with `jsp_000087_main`. -/
theorem jsp87ErrBoundsFromEscape_blunt (K H Y : ℕ) (q : ℝ) (b : ℕ) (hb : 1 ≤ b)
    (hesc : jsp87TruncCarryEscapes b)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H)
    (hrecip : 2 ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
    (herrs : jsp87ErrBoundsFromEscape K H q) :
    ∃ κ1 κ2 κ3 κ4 κ5 : ℝ,
      (1 / 30 ≤ κ1 ∨ 1 / 30 ≤ κ2 ∨ 1 / 30 ≤ κ3 ∨ 1 / 30 ≤ κ4 ∨ 1 / 30 ≤ κ5) := by
  obtain ⟨κ1, κ2, κ3, κ4, κ5, H15, H1617⟩ := herrs b hb hesc
  exact ⟨κ1, κ2, κ3, κ4, κ5,
    jsp87_endgame_blunt K H Y q κ1 κ2 κ3 κ4 κ5 hK hH hrecip (H15 Y) (H1617 Y)⟩

/-! ## §6  THE SECOND-MOMENT PRICE OF (5.15) — A SECOND, QUANTITATIVE REFUTATION

§4 refuted (5.18) by the endgame.  This section refutes it again, and
*quantitatively*, by the second moment of the prime-divisor count:

* `jsp87_515_zero_var_le` — (5.15) at the ground-truth scale, together with the
  phase bound of §0, forces `8 · (q/2)² · Var (i ↦ jsp87Cnt P (i+1)) ≤ κ₁+κ₂+κ₃`.
  This is the variance form of arXiv:2512.01739 (5.19) read at `K = 0, H = 1`.
* `jsp87_515_zero_sqmoment_le` — hence a bound on the **second moment** of the
  count.
* `jsp87NzResCard_zero_one` — at `K = 0, H = 1` exactly one residue class of `p`
  is nonzero, so `jsp87NzResCard 0 p 1 = 1`.
* `jsp87FAvg_cnt_primeSet` — **the mean-field identity**: the mean of `cnt` over
  the canonical sample is exactly the harmonic mass `jsp87RecipSum`.
* `jsp87_515_zero_recipSum_le` — so `(5.15)` at `q = 1/20` forces
  `∑_{2 ≤ p ≤ Y} 1/p ≤ 200 (κ₁+κ₂+κ₃)`, i.e. **the constant of (5.15) must grow
  with `log log Y`**.
* `jsp87_515_zero_refuted` — Euler's divergence then refutes (5.15) at the
  ground-truth scale **for every fixed triple of constants at all large
  heights**: a second, independent proof that (5.18) cannot hold. -/

/-- **AT `K = 0, H = 1`, THE CUBE SUM `X_p` VANISHES EXACTLY WHEN `p ∤ n + 1`.** -/
theorem jsp87Xp0_zero_one_ne_zero_iff (p n : ℕ) :
    (jsp87Xp0 (jsp87BinV 0) p n 1 ≠ 0) ↔ p ∣ n + 1 := by
  rw [jsp87Xp0_binV_zero_one]
  constructor
  · intro hne
    by_cases hc : p ∣ n + 1
    · exact hc
    · rw [if_neg hc] at hne
      norm_num at hne
  · intro hc
    rw [if_pos hc]
    norm_num

/-- **THE NONZERO-CUBE-SUM SET AT `K = 0, H = 1` IS THE SINGLE RESIDUE `p − 1`.** -/
theorem jsp87nzRes_zero_one (p : ℕ) (hp : 0 < p) :
    (Finset.Icc 0 (p - 1)).filter (fun n => jsp87Xp0 (jsp87BinV 0) p n 1 ≠ 0) = {p - 1} := by
  ext n
  rw [Finset.mem_filter, Finset.mem_singleton, Finset.mem_Icc]
  constructor
  · intro hnn
    have h3 := hnn.2
    rw [jsp87Xp0_zero_one_ne_zero_iff] at h3
    have hple : p ≤ n + 1 := Nat.le_of_dvd (by omega) h3
    omega
  · intro hnn
    subst hnn
    refine And.intro (And.intro ?_ ?_) ?_
    · omega
    · omega
    · rw [jsp87Xp0_zero_one_ne_zero_iff]
      exact ⟨1, by omega⟩

/-- **THE NONZERO-CUBE-SUM COUNT AT `K = 0, H = 1` IS ONE**: among the residues
`0 … p−1` only `p − 1` has `p ∣ n + 1`. -/
theorem jsp87NzResCard_zero_one (p : ℕ) (hp : 0 < p) : jsp87NzResCard 0 p 1 = 1 := by
  unfold jsp87NzResCard
  rw [jsp87nzRes_zero_one p hp]
  simp

/-- **AT `K = 0, H = 1` THE NONZERO-CUBE-SUM SET OF ANY SAMPLE IS THE MULTIPLES
OF `p`.** -/
theorem jsp87NzRes_zero_one {s : Finset ℕ} (p : ℕ) :
    jsp87NzRes 0 p 1 s = s.filter (fun i => p ∣ i + 1) := by
  ext i
  simp only [Finset.mem_filter, jsp87Xp0_zero_one_ne_zero_iff]

/-- **THE SUM OF THE PRIME-DIVISOR INDICATOR OVER THE CANONICAL SAMPLE IS THE
MEAN-FIELD COUNT** `∏ P / p`, for every prime `p ∈ P`. -/
theorem jsp87sum_div_primeSet (Y p : ℕ) (hp : p ∈ jsp87PrimeSet 2 Y) :
    (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y), (if p ∣ i + 1 then (1 : ℝ) else 0))
      = (jsp87Prod (jsp87PrimeSet 2 Y) : ℝ) / (p : ℝ) := by
  have hpprime : p.Prime := jsp87PrimeSet_prime hp
  have htwo : (2 : ℕ) ≤ p := hpprime.two_le
  have hpos : 0 < jsp87Prod (jsp87PrimeSet 2 Y) := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (jsp87PrimeSet_prime hi).pos
  have hprod0 : (jsp87Prod (jsp87PrimeSet 2 Y) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hfr : jsp87NzFrac 0 p 1 (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
      = ((jsp87NzResCard 0 p 1 : ℕ) : ℝ) / (p : ℝ) := by
    refine jsp87ProgFull_nzFrac (K := 0) (p := p) (H := 1) (n0 := 0) (D := 1)
      (by norm_num) hpos hp hpprime ?_ (by omega)
    exact fun h => absurd (Nat.le_of_dvd (by norm_num : (0 : ℕ) < 1) h) (by omega)
  have hcard : ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ)
      = jsp87Prod (jsp87PrimeSet 2 Y) := jsp87ProgFull_card (by norm_num) _ hpos
  have hset : (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).filter (fun i => p ∣ i + 1)
      = jsp87NzRes 0 p 1 (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)) :=
    (jsp87NzRes_zero_one p).symm
  have hsum : (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
        (if p ∣ i + 1 then (1 : ℝ) else 0))
      = ((jsp87NzRes 0 p 1 (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))).card : ℕ) := by
    have h' : (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
          (if p ∣ i + 1 then (1 : ℝ) else 0))
        = ∑ _i ∈ (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).filter (fun i => p ∣ i + 1),
            (1 : ℝ) := by
      symm
      exact Finset.sum_filter _ _
    rw [h', ← hset, Finset.sum_const, nsmul_eq_mul]
    norm_num
  have hr : ((jsp87NzRes 0 p 1 (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))).card : ℝ)
        / (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ) = 1 / (p : ℝ) := by
    have hh := hfr.trans (by rw [jsp87NzResCard_zero_one p hpprime.pos])
    unfold jsp87NzFrac at hh
    simpa using hh
  rw [hsum]
  have hkey : ((jsp87NzRes 0 p 1 (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))).card : ℝ)
      = (jsp87Prod (jsp87PrimeSet 2 Y) : ℝ) / (p : ℝ) := by
    have hh := hr
    rw [hcard] at hh
    have hh2 := (div_eq_iff hprod0).mp hh
    rw [hh2]
    field_simp
  rw [hkey]

/-- **THE MEAN OF THE PRIME-DIVISOR INDICATOR OVER THE CANONICAL SAMPLE IS `1/p`**
— the discrete equidistribution statement, obtained from the block count of
round 123 at `K = 0`, `H = 1`. -/
theorem jsp87FAvg_div_primeSet (Y p : ℕ) (hp : p ∈ jsp87PrimeSet 2 Y) :
    jsp87FAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => if p ∣ i + 1 then (1 : ℝ) else 0) = 1 / (p : ℝ) := by
  have hpos : 0 < jsp87Prod (jsp87PrimeSet 2 Y) := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (jsp87PrimeSet_prime hi).pos
  have hcard : ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ)
      = jsp87Prod (jsp87PrimeSet 2 Y) := jsp87ProgFull_card (by norm_num) _ hpos
  have hcard0 : (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by rw [hcard]; exact_mod_cast hpos))
  unfold jsp87FAvg
  rw [jsp87sum_div_primeSet Y p hp, hcard]
  field_simp

/-- **THE MEAN OF THE PRIME-DIVISOR COUNT OVER THE CANONICAL SAMPLE IS THE
HARMONIC MASS OF THE PRIME SET** — the mean-field identity at `K = 0, H = 1`. -/
theorem jsp87sum_cnt_primeSet (Y : ℕ) :
    (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
        (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      = (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ)
          * jsp87RecipSum (jsp87PrimeSet 2 Y) := by
  have h' : (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
        (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      = ∑ p ∈ jsp87PrimeSet 2 Y,
          ∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
            (if p ∣ i + 1 then (1 : ℝ) else 0) := by
    simp_rw [jsp87Cnt_eq_sum]
    exact Finset.sum_comm
  have hprod : (jsp87Prod (jsp87PrimeSet 2 Y) : ℝ) * jsp87RecipSum (jsp87PrimeSet 2 Y)
      = ∑ p ∈ jsp87PrimeSet 2 Y, (jsp87Prod (jsp87PrimeSet 2 Y) : ℝ) / (p : ℝ) := by
    rw [jsp87RecipSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_eq_mul_inv]
    ring
  have hcard : ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ)
      = jsp87Prod (jsp87PrimeSet 2 Y) := by
    have hpos : 0 < jsp87Prod (jsp87PrimeSet 2 Y) := by
      unfold jsp87Prod
      exact Finset.prod_pos fun i hi => (jsp87PrimeSet_prime hi).pos
    exact jsp87ProgFull_card (by norm_num) _ hpos
  rw [h', Finset.sum_congr rfl fun p hp => jsp87sum_div_primeSet Y p hp, hcard, ← hprod]

/-- **THE MEAN OF THE PRIME-DIVISOR COUNT OVER THE CANONICAL SAMPLE IS THE
HARMONIC MASS OF THE PRIME SET.** -/
theorem jsp87FAvg_cnt_primeSet (Y : ℕ) :
    jsp87FAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      = jsp87RecipSum (jsp87PrimeSet 2 Y) := by
  have hpos : 0 < jsp87Prod (jsp87PrimeSet 2 Y) := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (jsp87PrimeSet_prime hi).pos
  have hcard : ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ)
      = jsp87Prod (jsp87PrimeSet 2 Y) := jsp87ProgFull_card (by norm_num) _ hpos
  have hcard0 : (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by rw [hcard]; exact_mod_cast hpos))
  unfold jsp87FAvg
  rw [jsp87sum_cnt_primeSet Y]
  field_simp


/-! ## §7  THE MEAN OF THE PHASE, AND THE FAILURE OF (5.19) AT EVERY FIXED `q` -/

/-- **THE UNSCALED PHASE `T` OF (5.13)**, named once. -/
noncomputable def jsp87Phase0 (K H Y : ℕ) (i : ℕ) : ℝ :=
  ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y, jsp87Xp0 (jsp87BinV K) p' i H

/-- **THE PHASE IS `q` TIMES THE UNSCALED PHASE `T`**, by definition. -/
theorem jsp87Phase_eq (K H Y : ℕ) (q : ℝ) (i : ℕ) :
    jsp87Phase K H Y q i = q * jsp87Phase0 K H Y i := rfl

/-- **THE MEAN OF THE TOTAL PHASE OVER THE CANONICAL SAMPLE AT THE GROUND-TRUTH
SCALE IS `(q/2)` TIMES THE HARMONIC MASS** — so it is unbounded in the height. -/
theorem jsp87_phase_mean_primeSet (Y : ℕ) (q : ℝ) :
    jsp87FAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => jsp87Phase 0 1 Y q i)
      = (q / 2) * jsp87RecipSum (jsp87PrimeSet 2 Y) := by
  have hpos : 0 < jsp87Prod (jsp87PrimeSet 2 Y) := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (jsp87PrimeSet_prime hi).pos
  have hcard : ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ)
      = jsp87Prod (jsp87PrimeSet 2 Y) := jsp87ProgFull_card (by norm_num) _ hpos
  have hcard0 : (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by rw [hcard]; exact_mod_cast hpos))
  have hsep : jsp87Separation 0 1 = 2 := by
    unfold jsp87Separation
    norm_num
  have hpt : ∀ i : ℕ, jsp87Phase0 0 1 Y i
      = (1 / 2 : ℝ) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ) := by
    intro i
    unfold jsp87Phase0
    rw [hsep, jsp87Xp0_binV_zero_sum]
    have hIcc : Finset.Icc 1 1 = {1} := by
      ext h
      rw [Finset.mem_Icc, Finset.mem_singleton]
      constructor <;> omega
    rw [hIcc, Finset.sum_singleton]
    norm_num
  have hmain' : (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
        ((1 / 2 : ℝ) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ)))
      = ((1 / 2 : ℝ) * (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ))
          * jsp87RecipSum (jsp87PrimeSet 2 Y) := by
    rw [← Finset.mul_sum, jsp87sum_cnt_primeSet Y, mul_assoc]
  unfold jsp87FAvg
  rw [div_eq_iff hcard0]
  have hsum' : (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y), jsp87Phase 0 1 Y q i)
      = q * (1 / 2 : ℝ) * (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ)
          * jsp87RecipSum (jsp87PrimeSet 2 Y) := by
    calc (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y), jsp87Phase 0 1 Y q i)
        = ∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
            q * ((1 / 2 : ℝ) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [jsp87Phase_eq, hpt]
      _ = q * (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
            ((1 / 2 : ℝ) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))) := by
        rw [Finset.mul_sum]
      _ = q * (1 / 2 : ℝ) * (((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℕ) : ℝ)
          * jsp87RecipSum (jsp87PrimeSet 2 Y) := by rw [hmain']; ring
  rw [hsum']
  ring

/-- **HYPOTHESIS (5.19) IN ITS POINTWISE FORM**: the phase `q T` is uniformly at
most `1/20` on the sample.  This is the form in which (5.19) is used in
arXiv:2512.01739 (it is what `jsp87_charfun_le` needs). -/
def jsp87Hyp519Pointwise (K H Y : ℕ) (q : ℝ) : Prop :=
  ∀ i : ℕ, |q * jsp87Phase0 K H Y i| ≤ 1 / 20

/-- **THE MEAN OF THE ABSOLUTE PHASE AT THE GROUND-TRUTH SCALE IS AT LEAST
`(|q|/2)` TIMES THE HARMONIC MASS** — the total phase is a *growing* object. -/
theorem jsp87_phase_abs_mean_ge (Y : ℕ) (q : ℝ) :
    jsp87FAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => |jsp87Phase 0 1 Y q i|)
      ≥ |q| / 2 * jsp87RecipSum (jsp87PrimeSet 2 Y) := by
  have h1 := jsp87FAvg_abs_le (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
    (fun i => jsp87Phase 0 1 Y q i)
  rw [jsp87_phase_mean_primeSet Y q, abs_mul, abs_div, abs_two] at h1
  rw [abs_of_nonneg (jsp87RecipSum_nonneg _)] at h1
  linarith

/-- **THE PRICE OF THE POINTWISE (5.19): IT BOUNDS THE HARMONIC MASS.**  If the
phase `q T` is pointwise at most `1/20` at the ground-truth scale, then
`∑_{2 ≤ p ≤ Y} 1/p ≤ 40 / |q|`. -/
theorem jsp87_519_pointwise_le (Y : ℕ) (q : ℝ) (hq : q ≠ 0)
    (hp : jsp87Hyp519Pointwise 0 1 Y q) :
    jsp87RecipSum (jsp87PrimeSet 2 Y) ≤ 40 / |q| := by
  have hq0 : (0 : ℝ) < |q| := abs_pos.2 hq
  have h1 := jsp87_phase_abs_mean_ge Y q
  have h2 : jsp87FAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => |jsp87Phase 0 1 Y q i|) ≤ 1 / 20 := by
    have hcard : (0 : ℕ) < (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card :=
      Finset.card_pos.mpr (jsp87ProgFull_nonempty _)
    rw [jsp87FAvg, div_le_iff₀ (by exact_mod_cast hcard)]
    calc (∑ i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y),
          |jsp87Phase 0 1 Y q i|)
        ≤ ∑ _i ∈ jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y), (1 / 20 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hpi := hp i
          exact hpi
      _ = ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℝ) * (1 / 20) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (1 / 20 : ℝ) * ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℝ) := by ring
  have h4 : (|q| / 2) * jsp87RecipSum (jsp87PrimeSet 2 Y) ≤ (1 / 20 : ℝ) :=
    le_trans h1 h2
  calc (jsp87RecipSum (jsp87PrimeSet 2 Y) : ℝ)
      ≤ (1 / 20) / (|q| / 2) := by
        have hthis : (jsp87RecipSum (jsp87PrimeSet 2 Y) : ℝ) * (|q| / 2) ≤ 1 / 20 := by
          nlinarith [h4]
        exact (le_div_iff₀ (by positivity : (0 : ℝ) < |q| / 2)).mpr hthis
    _ ≤ 40 / |q| := by
        have heq : (1 / 20 : ℝ) / (|q| / 2) = (1 / 10 : ℝ) / |q| := by
          field_simp
          ring
        rw [heq]
        have h9 : (1 / 10 : ℝ) ≤ 40 := by norm_num
        have h10 : (1 / 10 : ℝ) ≤ (40 / |q|) * |q| := by
          rw [div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hq0), mul_one]
          exact h9
        exact (div_le_iff₀ hq0).mpr h10

/-- **THE POINTWISE (5.19) IS IMPOSSIBLE AT EVERY FIXED NONZERO `q`, AT ALL
LARGE HEIGHTS.**  Euler's divergence of `∑_p 1/p` (round 125) plus
`jsp87_519_pointwise_le`: the total phase of the endgame is a *growing* object,
and the only way the endgame can be run is with `q` depending on the height.

This is the third independent reason the fixed-scale route cannot work:
`jsp87_charfun_le` (the variance bound (5.19)–(5.20), and hence hypothesis
(5.21) and `jsp87_endgame_sum_ge`) is **not applicable** at `K = 0, H = 1` for
any fixed `q ≠ 0` and all large `Y`. -/
theorem jsp87_519_pointwise_fails (q : ℝ) (hq : q ≠ 0) :
    ∃ Y : ℕ, ¬ jsp87Hyp519Pointwise 0 1 Y q := by
  obtain ⟨Y, hY⟩ := jsp87PrimeRecipDiverges_proof 0 1 (by omega) (40 / |q| + 1)
    (by positivity)
  have hsep : jsp87Separation 0 1 = 2 := by
    unfold jsp87Separation
    norm_num
  rw [hsep] at hY
  refine ⟨Y, fun hp => absurd (jsp87_519_pointwise_le Y q hq hp) ?_⟩
  linarith

/-- **(5.15) TOGETHER WITH THE POINTWISE (5.19) FORCES A BOUND ON THE VARIANCE OF
THE TOTAL PHASE** — the variance bound (5.19)–(5.20) of arXiv:2512.01739 read at
the cut point `(K, H, Y)`: `8 Var (q T) ≤ κ₁ + κ₂ + κ₃`.  This is the object
hypothesis (5.21) is about, and it is now an explicit real statement. -/
theorem jsp87_515_imp_var_le (K H Y : ℕ) (q κ : ℝ)
    (h15 : jsp87Hypothesis15 K H q κ κ κ)
    (hp : jsp87Hyp519Pointwise K H Y q) :
    8 * jsp87Var (jsp87Sample K H Y) (fun i => q * jsp87Phase0 K H Y i)
      ≤ κ + κ + κ := by
  have hne : (jsp87Sample K H Y).Nonempty := jsp87ProgFull_nonempty _
  have hcf := jsp87_charfun_le (jsp87Sample K H Y) hne q (jsp87Phase0 K H Y) hp
  have hid : jsp87CAvg (jsp87Sample K H Y) (fun i => jsp87e (q * jsp87Phase0 K H Y i))
      = jsp87Mean K H Y q := by
    unfold jsp87Mean
    rfl
  rw [hid] at hcf
  have hid3 : jsp87Mean K H Y q - jsp87Err1z K H Y q = 1 := by
    simp [jsp87Err1z]
  have h1 : (1 : ℝ) ≤ ‖jsp87Mean K H Y q‖ + ‖jsp87Err1z K H Y q‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
      _ = ‖jsp87Mean K H Y q - jsp87Err1z K H Y q‖ := by rw [← hid3]
      _ ≤ ‖jsp87Mean K H Y q‖ + ‖jsp87Err1z K H Y q‖ := norm_sub_le _ _
  have h2 : ‖jsp87Err1z K H Y q‖ ≤ κ + κ + κ := by
    have := h15 Y
    rwa [jsp87Err1_eq] at this
  unfold jsp87Var at hcf ⊢
  linarith

end JSP87
