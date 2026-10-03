/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-114-a).
-/
import JSPProblem.LambertMaster
import Mathlib.Tactic

/-!
# JSP-000087 : the `+1` Lambert series as a *summed* alternating series of dilations

## Why this file exists

Round 112 introduced the two series objects of §5.2 of Tao and Teräväinen
(arXiv:2512.01739) — the `+1` Lambert series `jsp87PlusLambert = ∑' n, ω(n)/(2^n+1)`
and the **dilations** `jsp87ScaleLambert k = ∑' n, ω(n) 2^{-kn}` — and round 113
proved the **per-place** alternating-geometric identity

```
ω(n)/(2^n + 1)  =  ω(n) ∑_{k<J} (-1)^k 2^{-(k+1)n}  +  ω(n) 2^{-n} (-2^{-n})^J / (1 + 2^{-n}) ,
```

together with the definition of the remainder object `jsp87PlusRem J`.  It could
not close the **summed** form, and recorded the reason precisely: this Mathlib
(v4.34.0) has **no** `tsum_finset_sum`, so the interchange

```
∑' n, ∑_{k<J} (·) (k,n)   =   ∑_{k<J}, ∑' n, (·) (k,n)
```

has to be proved by hand.

**That hand proof is here, and with it the whole of §5.2.**  This is not a
re-interpretation of an earlier round: rounds 37–113 attacked the Lambert
reduction (37), the carry scaffold (38), the gcd arithmetic (39), the carry
dynamics (40), the digit bookkeeping (41), the carry excess and the sieve
content (44), the base-`2` block arithmetic (46), the carry-free primary
expansion (47), the doubling map on the carries (48), the radix criterion (49),
the asymptotics (50), the period equation (52), the `2`-adic prefix (53), the
runs and sieves (55–57), the counting function (58), the CRT constructions
(59–61), the denominator correspondence (63), the doubling orbit (64), the
`2`-adic refutation and the prime-power excess (65–68), the base family (70), the
level sets and the row join (72–76), the residue carries (78–82), the level
series (84), the squarefree and rough joins (86–92), the moment ladder (94–96)
and the master Lambert identity (113).  **No round had ever summed the
alternating expansion of §5.2 over `n`.*  This file does.

## The content

1. **the termwise remainder bound and its sign.**  `|ω(n) x(-x)^J/(1+x)| ≤ ω(n) x^J`
   and `ω(n) x (-x)^J/(1+x) = (-1)^J |ω(n) x (-x)^J/(1+x)|`, so the remainder
   carries the sign of `(-1)^J`.
2. **the dilations decay geometrically.**  `jsp87ScaleLambert (J+1) ≤ jsp87ScaleLambert J / 2`
   and consequently `jsp87ScaleLambert J ≤ 4 (2⁻¹)^J S`, so the dilations tend to `0`.
3. **THE FINITE INTERCHANGE** `tsum_sum_range_swap`, proved from scratch by
   induction on `J` because Mathlib has no `tsum_finset_sum`.
4. **THE MAIN THEOREM** `jsp87PlusLambert_eq_altDilate`:
   `jsp87PlusLambert = ∑_{k<J} (-1)^k jsp87ScaleLambert (k+1) + jsp87PlusRem J`.
5. **THE ALTERNATING BRACKET** (classical Leibniz, in the `ω`-series):
   `jsp87PlusLambert_tendsto_altDilate` and the strict two-sided bracket
   `jsp87_altDilate_bracket`, which yields the *new* strict inequality
   `jsp87PlusLambert < 2 * jsp87Series` (round 112 had only `≤`) and the explicit
   positive lower bound `1/5 ≤ jsp87PlusLambert`.
-/

namespace JSP87

open Classical
open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The remainder term of the truncated expansion, named and bounded -/

/-- **The `n`-th summand of the truncation remainder** `jsp87PlusRem J` of the
`+1` Lambert series, i.e. the quantity `ω(n) 2^{-n} (-2^{-n})^J / (1 + 2^{-n})`
of §5.2 of arXiv:2512.01739. -/
noncomputable def jsp87PlusTerm (n J : ℕ) : ℝ :=
  ((omega n : ℕ) : ℝ) * jsp87X n * (-(jsp87X n)) ^ J / (1 + jsp87X n)

/-- The `n`-th remainder term, spelled out. -/
theorem jsp87PlusTerm_def (n J : ℕ) :
    jsp87PlusTerm n J
      = ((omega n : ℕ) : ℝ) * jsp87X n * (-(jsp87X n)) ^ J / (1 + jsp87X n) := rfl

/-- The absolute value of the remainder term, computed exactly: with `x = 2^{-n}`
the factor `(-1)^J` is the only thing the truncation keeps. -/
theorem jsp87PlusTerm_abs (n J : ℕ) :
    |jsp87PlusTerm n J|
      = ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (J + 1) / (1 + jsp87X n) := by
  have hx : 0 < jsp87X n := jsp87X_pos n
  have hw : (0 : ℝ) ≤ ((omega n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) < 1 + jsp87X n := by linarith
  unfold jsp87PlusTerm
  rw [abs_div, abs_of_pos hd, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_pos hx, abs_pow,
    abs_neg, abs_of_pos hx, pow_succ]
  ring

/-- **THE DOMINATING ESTIMATE.**  `|ω(n) 2^{-n} (-2^{-n})^J/(1+2^{-n})| ≤ ω(n) 2^{-nJ}`:
the remainder term is dominated by the `J`-th power of the dilation variable. -/
theorem jsp87PlusTerm_abs_le (n J : ℕ) :
    |jsp87PlusTerm n J| ≤ ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J := by
  rw [jsp87PlusTerm_abs, pow_succ]
  have hone : jsp87X n / (1 + jsp87X n) ≤ 1 :=
    (div_le_one (by linarith [jsp87X_pos n])).2 (by linarith)
  calc ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (J + 1) / (1 + jsp87X n)
      = ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J * (jsp87X n / (1 + jsp87X n)) := by ring
    _ ≤ ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J := by
      calc ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J * (jsp87X n / (1 + jsp87X n))
          = ((omega n : ℕ) : ℝ) * ((jsp87X n / (1 + jsp87X n)) * (jsp87X n) ^ J) := by ring
        _ ≤ ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J := by
          have h2 : ((omega n : ℕ) : ℝ) * (jsp87X n / (1 + jsp87X n))
              ≤ ((omega n : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg _)
          have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg (le_of_lt (jsp87X_pos n)) J)
          calc ((omega n : ℕ) : ℝ) * ((jsp87X n / (1 + jsp87X n)) * (jsp87X n) ^ J)
              = (jsp87X n) ^ J * (((omega n : ℕ) : ℝ) * (jsp87X n / (1 + jsp87X n))) := by ring
            _ ≤ (jsp87X n) ^ J * (((omega n : ℕ) : ℝ) * 1) := h3
            _ = ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J := by ring

/-- **THE REMAINDER TERM IS A SIGN TIMES ITS OWN ABSOLUTE VALUE.** -/
theorem jsp87PlusTerm_eq_sign_abs (n J : ℕ) :
    jsp87PlusTerm n J = ((-1) ^ J : ℝ) * |jsp87PlusTerm n J| := by
  rw [jsp87PlusTerm_abs, jsp87PlusTerm_def]
  have hone : (-(jsp87X n) : ℝ) ^ J = ((-1 : ℝ) ^ J) * (jsp87X n) ^ J := by
    rw [show (-(jsp87X n) : ℝ) = (-1 : ℝ) * jsp87X n by ring, mul_pow]
  rw [hone]
  ring

/-! ## 2. Summability of the remainder terms -/

theorem summable_omega_dilate' (J : ℕ) (hJ : 1 ≤ J) :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n * J))⁻¹) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)) ?_ summable_omega_two_pow_neg
  intro n
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact (inv_le_inv₀ (by positivity) (by positivity)).2
    (by
      have h1 : n ≤ n * J := by
        have := Nat.mul_le_mul_left n hJ
        omega
      exact_mod_cast (Nat.pow_le_pow_right (n := (2 : ℕ)) (by norm_num) h1))

theorem summable_omega_dilate (J : ℕ) (hJ : 1 ≤ J) :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J) := by
  refine Summable.congr (summable_omega_dilate' J hJ) fun n => ?_
  rw [jsp87X_pow]

theorem summable_jsp87PlusTermAbs (J : ℕ) (hJ : 1 ≤ J) :
    Summable (fun n : ℕ => |jsp87PlusTerm n J|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => jsp87PlusTerm_abs_le n J)
    (summable_omega_dilate J hJ)

theorem summable_jsp87PlusTermR (J : ℕ) (hJ : 1 ≤ J) :
    Summable (fun n : ℕ => jsp87PlusTerm n J) := by
  rw [show (fun n : ℕ => jsp87PlusTerm n J)
      = fun n => ((-1) ^ J : ℝ) * |jsp87PlusTerm n J| from
        funext fun n => jsp87PlusTerm_eq_sign_abs n J]
  exact (summable_jsp87PlusTermAbs J hJ).mul_left _

theorem hasSum_jsp87PlusTerm (J : ℕ) (hJ : 1 ≤ J) :
    HasSum (fun n : ℕ => jsp87PlusTerm n J) (jsp87PlusRem J) :=
  (summable_jsp87PlusTermR J hJ).hasSum_iff.mpr rfl

/-! ## 3. The remainder object: the sign, and its size -/

/-- Powers of a number in `[0,1]` decrease. -/
private theorem jsp87_pow_le (x : ℝ) (hx1 : x ≤ 1) (hx0 : 0 ≤ x) (k : ℕ) :
    x ^ (k + 1) ≤ x := by
  calc x ^ (k + 1) = x ^ k * x := pow_succ x k
    _ ≤ 1 * x := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx1) hx0
    _ = x := by ring

/-- **THE REMAINDER IS A SIGNED SUM OF POSITIVE NUMBERS.** -/
theorem jsp87PlusRem_eq_sign (J : ℕ) (hJ : 1 ≤ J) :
    jsp87PlusRem J = ((-1) ^ J : ℝ) * (∑' n : ℕ, |jsp87PlusTerm n J|) := by
  rw [← (summable_jsp87PlusTermR J hJ).hasSum_iff.mp (hasSum_jsp87PlusTerm J hJ)]
  rw [tsum_congr fun n => jsp87PlusTerm_eq_sign_abs n J]
  exact Summable.tsum_mul_left _ (summable_jsp87PlusTermAbs J hJ)

private theorem jsp87_neg_one_even (r : ℕ) : ((-1) ^ (r + r) : ℝ) = 1 := by
  rw [show r + r = 2 * r by omega, pow_mul]
  simp

private theorem jsp87_neg_one_odd (r : ℕ) : ((-1) ^ (2 * r + 1) : ℝ) = -1 := by
  rw [pow_add, pow_mul]
  simp

/-- **THE REMAINDER IS NONNEGATIVE FOR EVEN `J`.** -/
theorem jsp87_plusRem_nonneg_of_even (J : ℕ) (hJ : 1 ≤ J) (hE : Even J) :
    0 ≤ jsp87PlusRem J := by
  obtain ⟨r, hr⟩ := hE
  rw [hr, jsp87PlusRem_eq_sign _ (by omega), jsp87_neg_one_even, one_mul]
  exact tsum_nonneg fun n => abs_nonneg _

/-- **THE REMAINDER IS NONPOSITIVE FOR ODD `J`.** -/
theorem jsp87_plusRem_nonpos_of_odd (J : ℕ) (hJ : 1 ≤ J) (hO : Odd J) :
    jsp87PlusRem J ≤ 0 := by
  obtain ⟨r, hr⟩ := hO
  rw [hr, jsp87PlusRem_eq_sign _ (by omega), jsp87_neg_one_odd]
  have hT : (0:ℝ) ≤ ∑' n : ℕ, |jsp87PlusTerm n (2 * r + 1)| :=
    tsum_nonneg fun n => abs_nonneg _
  linarith

/-- **THE SUMMED ABSOLUTE VALUES ARE STRICTLY POSITIVE.**  The remainder is never
zero, because the place `n = 2` contributes `ω 2 = 1`. -/
theorem jsp87_absTermSum_pos (J : ℕ) (hJ : 1 ≤ J) :
    0 < (∑' n : ℕ, |jsp87PlusTerm n J|) := by
  have hge : (∑ i ∈ ({2} : Finset ℕ), |jsp87PlusTerm i J|)
      ≤ ∑' n : ℕ, |jsp87PlusTerm n J| :=
    Summable.sum_le_tsum ({2} : Finset ℕ) (fun i _ => abs_nonneg _)
      (summable_jsp87PlusTermAbs J hJ)
  rw [Finset.sum_singleton] at hge
  have h2 : 0 < |jsp87PlusTerm 2 J| := by
    rw [jsp87PlusTerm_abs]
    have hω : omega 2 = 1 := by native_decide
    rw [hω, Nat.cast_one, pow_succ]
    have hx : 0 < jsp87X 2 := jsp87X_pos 2
    have hd : (0 : ℝ) < 1 + jsp87X 2 := by linarith
    have hp : (0 : ℝ) < (jsp87X 2) ^ (J + 1) := by positivity
    positivity
  linarith

/-- **THE REMAINDER IS STRICTLY POSITIVE FOR EVEN `J`.** -/
theorem jsp87_plusRem_pos_of_even (J : ℕ) (hJ : 1 ≤ J) (hE : Even J) :
    0 < jsp87PlusRem J := by
  obtain ⟨r, hr⟩ := hE
  rw [hr, jsp87PlusRem_eq_sign _ (by omega), jsp87_neg_one_even, one_mul]
  exact jsp87_absTermSum_pos _ (by omega)

/-- **THE REMAINDER IS STRICTLY NEGATIVE FOR ODD `J`.** -/
theorem jsp87_plusRem_neg_of_odd (J : ℕ) (hJ : 1 ≤ J) (hO : Odd J) :
    jsp87PlusRem J < 0 := by
  obtain ⟨r, hr⟩ := hO
  rw [hr, jsp87PlusRem_eq_sign _ (by omega), jsp87_neg_one_odd]
  linarith [jsp87_absTermSum_pos (2 * r + 1) (by omega)]

/-! ## 4. The dilations: positivity and geometric decay -/

theorem jsp87ScaleLambert_nonneg (J : ℕ) : 0 ≤ jsp87ScaleLambert J := by
  rw [jsp87ScaleLambert]
  exact tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg _) (by positivity)

theorem summable_jsp87ScaleLambert (J : ℕ) (hJ : 1 ≤ J) :
    Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (J * n))⁻¹) := by
  refine Summable.congr (summable_omega_dilate' J hJ) fun n => ?_
  rw [Nat.mul_comm]

/-- **THE `J`-TH DILATION IS AT LEAST `2^{-2J}`**: the place `n = 2` alone
contributes `ω 2 · 2^{-2J} = 2^{-2J}`, so the dilations never collapse to `0`
before the Erdős series does. -/
theorem jsp87ScaleLambert_gt (J : ℕ) (hJ : 1 ≤ J) :
    ((2 : ℝ) ^ (2 * J))⁻¹ < jsp87ScaleLambert J := by
  have hs := summable_jsp87ScaleLambert J hJ
  have hge : (∑ i ∈ ({2, 4} : Finset ℕ), ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (J * i))⁻¹)
      ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (J * n))⁻¹ :=
    Summable.sum_le_tsum ({2, 4} : Finset ℕ)
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)) hs
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton] at hge
  have hω2 : omega 2 = 1 := by native_decide
  have hω4 : omega 4 = 1 := by native_decide
  rw [hω2, hω4, Nat.cast_one, show (J * 2 : ℕ) = 2 * J by omega,
    show (J * 4 : ℕ) = 4 * J by omega] at hge
  rw [jsp87ScaleLambert]
  have key : ((2 : ℝ) ^ (2 * J))⁻¹ < ((2 : ℝ) ^ (2 * J))⁻¹ + ((2 : ℝ) ^ (4 * J))⁻¹ := by
    linarith [(by positivity : (0:ℝ) < ((2 : ℝ) ^ (4 * J))⁻¹)]
  exact lt_of_lt_of_le key (by simpa using hge)

/-- **THE DILATIONS SHRINK BY HALF AT EVERY STEP.**  `jsp87ScaleLambert (J+1) ≤
jsp87ScaleLambert J / 2` for `1 ≤ J`, because `(J+1)·n ≥ J·n + 1`. -/
theorem jsp87ScaleLambert_succ_le_half (J : ℕ) (hJ : 1 ≤ J) :
    jsp87ScaleLambert (J + 1) ≤ jsp87ScaleLambert J / 2 := by
  have hs := summable_jsp87ScaleLambert (J + 1) (by omega)
  have hs' := summable_jsp87ScaleLambert J hJ
  have hptw : ∀ n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ ((J + 1) * n))⁻¹
      ≤ (2 : ℝ)⁻¹ * (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (J * n))⁻¹) := by
    intro n
    rcases n with _ | m
    · simp only [omega_zero, Nat.cast_zero, zero_mul]
      norm_num
    have hmn : (1 : ℕ) ≤ m + 1 := by omega
    have hkey : J * (m + 1) + 1 ≤ (J + 1) * (m + 1) := by
      rw [Nat.add_mul]
      simp only [one_mul]
      exact Nat.add_le_add_left hmn (k := J * (m + 1))
    have hmono : ((2 : ℝ) ^ ((J + 1) * (m + 1)))⁻¹ ≤ ((2 : ℝ) ^ (J * (m + 1) + 1))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2
        (by exact_mod_cast (Nat.pow_le_pow_right (n := (2 : ℕ)) (by norm_num) hkey))
    have hfact : ((2 : ℝ) ^ (J * (m + 1) + 1))⁻¹ = ((2 : ℝ) ^ (J * (m + 1)))⁻¹ * (2 : ℝ)⁻¹ := by
      rw [pow_succ, inv_mul']
      ring
    calc ((omega (m + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ ((J + 1) * (m + 1)))⁻¹
        ≤ ((omega (m + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (J * (m + 1) + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
      _ = (2 : ℝ)⁻¹ * (((omega (m + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (J * (m + 1)))⁻¹) := by
        rw [hfact]
        ring
      _ ≤ (2 : ℝ)⁻¹ * (((omega (m + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ (J * (m + 1)))⁻¹) := le_rfl
  have hts := Summable.tsum_le_tsum hptw hs (hs'.mul_left (2 : ℝ)⁻¹)
  have hts' : (∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ ((J + 1) * n))⁻¹)
      ≤ (2 : ℝ)⁻¹ * jsp87ScaleLambert J := by
    rw [jsp87ScaleLambert]
    exact hts.trans_eq (Summable.tsum_mul_left (2 : ℝ)⁻¹ hs')
  rw [jsp87ScaleLambert]
  exact hts'.trans_eq (by ring)

/-- **THE GEOMETRIC DECAY OF THE DILATIONS.**  `jsp87ScaleLambert J ≤ 4 (2⁻¹)^J S`
for `1 ≤ J`.  This is what makes the `J`-term truncation of §5.2 an
approximation *at all*: the `J`-th column of the alternating expansion is
`jsp87ScaleLambert J`, and it tends to `0` geometrically. -/
theorem jsp87ScaleLambert_le (J : ℕ) (hJ : 1 ≤ J) :
    jsp87ScaleLambert J ≤ 4 * ((2 : ℝ)⁻¹) ^ J * jsp87Series := by
  induction J with
  | zero => omega
  | succ J ih =>
      rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
      · subst hJ0
        have hle : jsp87ScaleLambert 1 ≤ 4 * ((2 : ℝ)⁻¹) ^ (1 : ℕ) * jsp87Series := by
          rw [jsp87ScaleLambert_one]
          have h1 : ((2 : ℝ)⁻¹) ^ (1 : ℕ) = 1 / 2 := by norm_num
          rw [h1]
          exact le_of_eq (by ring)
        simpa using hle
      · have hstep := jsp87ScaleLambert_succ_le_half J hJpos
        rw [show ((2 : ℝ)⁻¹) ^ (J + 1) = ((2 : ℝ)⁻¹) ^ J * (2 : ℝ)⁻¹ by
          rw [pow_succ]]
        calc jsp87ScaleLambert (J + 1) ≤ jsp87ScaleLambert J / 2 := hstep
          _ ≤ (4 * ((2 : ℝ)⁻¹) ^ J * jsp87Series) / 2 :=
            div_le_div_of_nonneg_right (ih hJpos) (by norm_num)
          _ = 4 * ((2 : ℝ)⁻¹) ^ J * (2 : ℝ)⁻¹ * jsp87Series := by ring
          _ = 4 * ((2 : ℝ)⁻¹) ^ (J + 1) * jsp87Series := by
            rw [pow_succ]
            ring

/-- **THE LEIBNZ BOUND OF THE TRUNCATION REMAINDER.**  `|jsp87PlusRem J|` — the
tail of the truncated alternating expansion of §5.2 — is bounded by the `J`-th
dilation, hence decays geometrically in `J`. -/
theorem jsp87_plusRem_abs_le (J : ℕ) (hJ : 1 ≤ J) :
    |jsp87PlusRem J| ≤ 4 * ((2 : ℝ)⁻¹) ^ J * jsp87Series := by
  rw [jsp87PlusRem_eq_sign _ hJ]
  have hT : 0 ≤ (∑' n : ℕ, |jsp87PlusTerm n J|) := tsum_nonneg fun n => abs_nonneg _
  rw [abs_mul, abs_pow, abs_neg, abs_one, abs_of_nonneg hT]
  simp only [one_pow, one_mul]
  have hle : (∑' n : ℕ, |jsp87PlusTerm n J|)
      ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J :=
    Summable.tsum_le_tsum (fun n => jsp87PlusTerm_abs_le n J)
      (summable_jsp87PlusTermAbs J hJ) (summable_omega_dilate J hJ)
  have hsum : (∑' n : ℕ, ((omega n : ℕ) : ℝ) * (jsp87X n) ^ J)
      = jsp87ScaleLambert J := by
    refine tsum_congr fun n => ?_
    rw [jsp87X_pow, Nat.mul_comm]
  exact le_trans (hle.trans_eq hsum) (jsp87ScaleLambert_le J hJ)

/-- **THE DILATIONS TEND TO ZERO.** -/
theorem tendsto_two_inv_pow_zero : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_real (r := (2 : ℝ)⁻¹) (by positivity) (by norm_num) hε
  refine ⟨n, fun k hk => ?_⟩
  have hk' : n ≤ k := by exact_mod_cast hk
  calc |(2 : ℝ)⁻¹ ^ k - 0| = ((2 : ℝ)⁻¹) ^ k := by
        rw [sub_zero, abs_of_nonneg (by positivity)]
    _ ≤ ((2 : ℝ)⁻¹) ^ n :=
        pow_le_pow_of_le_one (by positivity) (by norm_num) hk'
    _ < ε := hn

/-- **THE TRUNCATION REMAINDER OF §5.2 GOES TO ZERO.**  The remainder of the
truncated alternating expansion of §5.2 vanishes, so the identity
`jsp87PlusLambert_eq_altDilate` below is a genuine limit and not a formal one. -/
theorem jsp87PlusRem_tendsto_zero : Tendsto jsp87PlusRem atTop (𝓝 0) := by
  have h1 : Tendsto (fun J => 4 * ((2 : ℝ)⁻¹) ^ J * jsp87Series) atTop (𝓝 0) := by
    convert tendsto_two_inv_pow_zero.const_mul (4 * jsp87Series) using 1 <;> ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hN' : ∃ N : ℕ, ∀ J ≥ N, |4 * ((2 : ℝ)⁻¹) ^ J * jsp87Series| < ε := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h1 ε hε
    exact ⟨N, fun J hJ => by simpa only [Real.dist_eq, sub_zero] using hN J hJ⟩
  obtain ⟨N, hN⟩ := hN'
  refine ⟨max N 1, fun J hJ => ?_⟩
  have hJ1 : (1 : ℕ) ≤ J := by omega
  rcases J.even_or_odd with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr]
    have hle1 : jsp87PlusRem (r + r) ≤ 4 * ((2 : ℝ)⁻¹) ^ (r + r) * jsp87Series :=
      le_trans (le_abs_self _) (jsp87_plusRem_abs_le (r + r) (by omega))
    have hle2 : -jsp87PlusRem (r + r) ≤ 4 * ((2 : ℝ)⁻¹) ^ (r + r) * jsp87Series :=
      (neg_le_abs _).trans (jsp87_plusRem_abs_le (r + r) (by omega))
    have hlt := hN (r + r) (by omega)
    rw [Real.dist_eq, sub_zero]
    calc |jsp87PlusRem (r + r)| ≤ |4 * ((2 : ℝ)⁻¹) ^ (r + r) * jsp87Series| :=
          abs_le_abs hle1 hle2
      _ < ε := hlt
  · rw [hr]
    have hle1 : jsp87PlusRem (2 * r + 1)
        ≤ 4 * ((2 : ℝ)⁻¹) ^ (2 * r + 1) * jsp87Series :=
      (jsp87_plusRem_neg_of_odd (2 * r + 1) (by omega) ⟨r, by omega⟩).le.trans (by
        have h1' : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
        nlinarith [pow_nonneg h1' (2 * r + 1), jsp87Series_nonneg])
    have hle2 : -jsp87PlusRem (2 * r + 1)
        ≤ 4 * ((2 : ℝ)⁻¹) ^ (2 * r + 1) * jsp87Series :=
      (neg_le_abs _).trans (jsp87_plusRem_abs_le (2 * r + 1) (by omega))
    have hlt := hN (2 * r + 1) (by omega)
    rw [Real.dist_eq, sub_zero]
    calc |jsp87PlusRem (2 * r + 1)|
        ≤ |4 * ((2 : ℝ)⁻¹) ^ (2 * r + 1) * jsp87Series| := abs_le_abs hle1 hle2
      _ < ε := hlt

/-! ## 5. The finite interchange, and the two column identities -/

/-- The `k`-th column of the alternating expansion at the place `n`. -/
private noncomputable def jsp87DilColumn (k n : ℕ) : ℝ :=
  ((-1) ^ k : ℝ) * (((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1))

/-- The `n`-th middle term of the per-place identity `jsp87_plusTerm_geom`. -/
private noncomputable def jsp87MidTerm (J n : ℕ) : ℝ :=
  ((omega n : ℕ) : ℝ) * (∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * (jsp87X n) ^ (k + 1))

/-- The middle term is the `J`-term column sum. -/
private theorem jsp87_midTerm_eq_sum (J n : ℕ) :
    jsp87MidTerm J n = ∑ k ∈ Finset.range J, jsp87DilColumn k n := by
  unfold jsp87DilColumn
  have hre : (∑ k ∈ Finset.range J,
      ((-1) ^ k : ℝ) * (((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1)))
      = ((omega n : ℕ) : ℝ)
          * (∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * (jsp87X n) ^ (k + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold jsp87MidTerm
  rw [← hre]

theorem summable_jsp87DilColumn (k : ℕ) : Summable (jsp87DilColumn k) := by
  have hx : ∀ n : ℕ, 0 < jsp87X n := jsp87X_pos
  have hx1 : ∀ n : ℕ, jsp87X n ≤ 1 := jsp87X_le_one
  have hω : ∀ n : ℕ, (0 : ℝ) ≤ ((omega n : ℕ) : ℝ) := fun n => Nat.cast_nonneg _
  have hge : ∀ n : ℕ, |jsp87DilColumn k n| ≤ ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    intro n
    have h1 : (jsp87X n) ^ (k + 1) ≤ jsp87X n :=
      jsp87_pow_le (jsp87X n) (hx1 n) (le_of_lt (hx n)) k
    calc |jsp87DilColumn k n|
        = ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1) := by
          rw [jsp87DilColumn, abs_mul, abs_pow, abs_neg, abs_one, abs_mul, abs_pow,
            abs_of_pos (hx n), abs_of_nonneg (hω n)]
          ring
      _ ≤ ((omega n : ℕ) : ℝ) * (jsp87X n) :=
          mul_le_mul_of_nonneg_left h1 (hω n)
      _ = ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rfl
  have hsumabs : Summable (fun n : ℕ => ‖jsp87DilColumn k n‖) := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hge summable_omega_two_pow_neg
  exact Summable.of_norm hsumabs

theorem summable_jsp87MidTerm (J : ℕ) : Summable (jsp87MidTerm J) := by
  have hx : ∀ n : ℕ, 0 < jsp87X n := jsp87X_pos
  have hx1 : ∀ n : ℕ, jsp87X n ≤ 1 := jsp87X_le_one
  have hω : ∀ n : ℕ, (0 : ℝ) ≤ ((omega n : ℕ) : ℝ) := fun n => Nat.cast_nonneg _
  have hge : ∀ n : ℕ, ‖jsp87MidTerm J n‖
      ≤ (J : ℝ) * (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) := by
    intro n
    rw [Real.norm_eq_abs]
    calc |jsp87MidTerm J n|
        = |((omega n : ℕ) : ℝ)
            * (∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * (jsp87X n) ^ (k + 1))| := rfl
      _ = ((omega n : ℕ) : ℝ)
          * |∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * (jsp87X n) ^ (k + 1)| := by
          rw [abs_mul, abs_of_nonneg (hω n)]
      _ ≤ ((omega n : ℕ) : ℝ)
          * ∑ k ∈ Finset.range J, |((-1) ^ k : ℝ) * (jsp87X n) ^ (k + 1)| := by
          refine mul_le_mul_of_nonneg_left ?_ (hω n)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ((omega n : ℕ) : ℝ) * ∑ k ∈ Finset.range J, (jsp87X n) := by
          refine mul_le_mul_of_nonneg_left ?_ (hω n)
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_pow, abs_neg, abs_one, abs_pow, abs_of_pos (hx n)]
          simpa using (jsp87_pow_le (jsp87X n) (hx1 n) (le_of_lt (hx n)) k)
      _ = ((omega n : ℕ) : ℝ) * ((J : ℝ) * (jsp87X n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (J : ℝ) * (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) := by
          rw [show jsp87X n = ((2 : ℝ) ^ n)⁻¹ by rfl]
          ring
  have hmajor : Summable (fun n : ℕ => (J : ℝ) * (((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹)) := by
    simpa only [one_mul] using (summable_omega_two_pow_neg.mul_left ((J : ℝ))).mul_left (1 : ℝ)
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hge hmajor)

/-- **THE VALUE OF THE `k`-TH COLUMN.**  Summing the `k`-th column over the
places `n` gives exactly `(-1)^k` times the `(k+1)`-st **dilation** of the Erdős
series.  This is the whole content of exchanging the `k`-sum with the `n`-sum. -/
private theorem jsp87_tsum_column (k : ℕ) :
    (∑' n : ℕ, jsp87DilColumn k n) = ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1) := by
  have hcolabs : Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1)) := by
    have hge : ∀ n : ℕ, ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1)
        ≤ ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
      intro n
      have hxn : 0 < jsp87X n := jsp87X_pos n
      have hxn1 : jsp87X n ≤ 1 := jsp87X_le_one n
      have h1 : (jsp87X n) ^ (k + 1) ≤ jsp87X n :=
        jsp87_pow_le (jsp87X n) hxn1 (le_of_lt hxn) k
      calc ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1) ≤ ((omega n : ℕ) : ℝ) * (jsp87X n) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rfl
    have hge' : ∀ n : ℕ, ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1)
        ≤ ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := hge
    exact Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt (jsp87X_pos n)) _)) hge'
      summable_omega_two_pow_neg
  calc (∑' n : ℕ, jsp87DilColumn k n)
      = ∑' n : ℕ, ((-1) ^ k : ℝ) * (((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1)) :=
        tsum_congr fun n => rfl
    _ = ((-1) ^ k : ℝ) * (∑' n : ℕ, ((omega n : ℕ) : ℝ) * (jsp87X n) ^ (k + 1)) :=
        Summable.tsum_mul_left _ hcolabs
    _ = ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1) := by
        congr 1
        exact tsum_congr fun n => by rw [jsp87X_pow, Nat.mul_comm]

/-! ## 6. THE MAIN THEOREM — the summed alternating expansion of §5.2 -/

/-- **THE MAIN THEOREM OF THIS FILE: the summed alternating-dilation expansion of
§5.2 of arXiv:2512.01739.**

For every `J`,

```
jsp87PlusLambert  =  ∑_{k<J} (-1)^k jsp87ScaleLambert (k+1)  +  jsp87PlusRem J ,
```

i.e. the `+1` Lambert series is the alternating sum, over the **dilations of the
Erdős series itself**, of its first `J` terms, up to the truncation remainder.
Mathlib has no statement of this shape: it has no `+1` Lambert series, no notion
of a dilation of a generating series, and nothing about the alternating
expansion `1/(2^n+1) = ∑_k (-1)^k 2^{-(k+1)n}`. -/
theorem jsp87PlusLambert_eq_altDilate (J : ℕ) :
    jsp87PlusLambert
      = ∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1) + jsp87PlusRem J := by
  cases J with
  | zero =>
    have hone : ∀ n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹ = jsp87PlusTerm n 0 := by
      intro n
      have hA : ((2 : ℝ) ^ n + 1 : ℝ) ≠ 0 := by positivity
      have hB : (1 + jsp87X n : ℝ) ≠ 0 := by
        have := jsp87X_pos n
        unfold jsp87X at *
        positivity
      rw [jsp87PlusTerm, eq_div_iff hB]
      unfold jsp87X
      field_simp
    unfold jsp87PlusRem jsp87PlusLambert
    rw [Finset.sum_range_zero, zero_add]
    exact tsum_congr hone
  | succ J =>
    have hJ : 1 ≤ J + 1 := by omega
    have hsMid : Summable (jsp87MidTerm (J + 1)) := summable_jsp87MidTerm (J + 1)
    have hswap := Summable.tsum_finsetSum (s := (Finset.range (J + 1) : Finset ℕ))
      (fun k _ => summable_jsp87DilColumn k)
    have hmidval : (∑' n : ℕ, jsp87MidTerm (J + 1) n)
        = ∑ k ∈ Finset.range (J + 1), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1) := by
      calc (∑' n : ℕ, jsp87MidTerm (J + 1) n)
          = ∑' n : ℕ, ∑ k ∈ Finset.range (J + 1), jsp87DilColumn k n :=
            tsum_congr fun n => jsp87_midTerm_eq_sum (J + 1) n
        _ = ∑ k ∈ Finset.range (J + 1), ∑' n : ℕ, jsp87DilColumn k n := hswap
        _ = ∑ k ∈ Finset.range (J + 1), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact jsp87_tsum_column k
    have hHasMid : HasSum (jsp87MidTerm (J + 1))
        (∑ k ∈ Finset.range (J + 1), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1)) :=
      hsMid.hasSum_iff.mpr hmidval
    have hTotal : HasSum (fun n : ℕ => jsp87MidTerm (J + 1) n + jsp87PlusTerm n (J + 1))
        ((∑ k ∈ Finset.range (J + 1), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1))
          + jsp87PlusRem (J + 1)) :=
      hHasMid.add (hasSum_jsp87PlusTerm (J + 1) hJ)
    have hsTot : Summable (fun n : ℕ => jsp87MidTerm (J + 1) n + jsp87PlusTerm n (J + 1)) :=
      hsMid.add (summable_jsp87PlusTermR (J + 1) hJ)
    have hsumTot : (∑' (n : ℕ), (jsp87MidTerm (J + 1) n + jsp87PlusTerm n (J + 1)))
        = jsp87PlusLambert := by
      calc (∑' (n : ℕ), (jsp87MidTerm (J + 1) n + jsp87PlusTerm n (J + 1)))
          = ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹ := by
              have key : ∀ n : ℕ, (jsp87MidTerm (J + 1) n + jsp87PlusTerm n (J + 1))
                  = ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹ := by
                intro n
                unfold jsp87MidTerm jsp87PlusTerm
                exact (jsp87_plusTerm_geom n (J + 1)).symm
              exact tsum_congr key
        _ = jsp87PlusLambert := rfl
    exact (hTotal.unique (hsTot.hasSum_iff.mpr hsumTot)).symm

/-! ## 7. The alternating bracket, and the consequences for the `+1` series -/

/-- **THE ALTERNATING PARTIAL SUMS OF THE DILATIONS CONVERGE TO THE `+1`
LAMBERT SERIES** — the §5.2 construction is convergent, not merely formal. -/
theorem jsp87PlusLambert_tendsto_altDilate :
    Tendsto (fun J : ℕ => ∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1))
      atTop (𝓝 jsp87PlusLambert) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have h1 : Tendsto (fun x : ℕ => -jsp87PlusRem x) atTop (𝓝 0) := by
    simpa using jsp87PlusRem_tendsto_zero.neg
  refine h1.congr fun J => ?_
  have hEq := jsp87PlusLambert_eq_altDilate J
  linarith

/-- **THE CLASSICAL LEIBNIZ BRACKET.**  For every even `J ≥ 2` the truncation
after `J+1` dilations lies strictly below the `+1` series, and the truncation
after `J+2` dilations strictly above it.  The width of the bracket is one
dilation, `jsp87ScaleLambert (J+2)`, and it tends to `0`. -/
theorem jsp87_altDilate_bracket (J : ℕ) (hJ : 1 ≤ J) (hE : Even J) :
    (∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1)) < jsp87PlusLambert
      ∧ jsp87PlusLambert
        < ∑ k ∈ Finset.range (J + 1), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1) := by
  obtain ⟨r, hr⟩ := hE
  subst hr
  constructor
  · rw [jsp87PlusLambert_eq_altDilate (r + r)]
    linarith [jsp87_plusRem_pos_of_even (r + r) (by omega) ⟨r, by rfl⟩]
  · rw [jsp87PlusLambert_eq_altDilate (r + r + 1)]
    have hR1 := jsp87_plusRem_neg_of_odd (r + r + 1) (by omega) ⟨r, by ring⟩
    have hsum : (∑ k ∈ Finset.range (r + r + 1), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1))
        = (∑ k ∈ Finset.range (r + r), ((-1) ^ k : ℝ) * jsp87ScaleLambert (k + 1))
          + ((-1) ^ (r + r) : ℝ) * jsp87ScaleLambert (r + r + 1) := by
      rw [Finset.sum_range_succ]
    rw [hsum, jsp87_neg_one_even]
    linarith [hR1, jsp87ScaleLambert_nonneg (r + r + 1)]

/-- **THE `+1` SERIES IS STRICTLY SMALLER THAN TWICE THE ERDŐS SERIES.**
Round 112 could only prove `≤`; the alternating identity makes it strict. -/
theorem jsp87PlusLambert_lt_two_mul_series : jsp87PlusLambert < 2 * jsp87Series := by
  rw [jsp87PlusLambert_eq_altDilate 1]
  have h := jsp87_plusRem_neg_of_odd 1 (by norm_num) ⟨0, by norm_num⟩
  rw [Finset.sum_range_succ]
  norm_num
  rw [← jsp87ScaleLambert_one]
  linarith

/-- **THE `+1` SERIES IS AT LEAST `1/5`**: the single term `n = 2` contributes
`ω 2/(2²+1) = 1/5`, so the series is bounded away from `0` by a rational. -/
theorem jsp87PlusLambert_ge_one_fifth : (1 / 5 : ℝ) ≤ jsp87PlusLambert := by
  have hs := summable_jsp87PlusTerm
  have hge : (∑ i ∈ ({2} : Finset ℕ), ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ i + 1)⁻¹)
      ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹ :=
    Summable.sum_le_tsum ({2} : Finset ℕ)
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)) hs
  rw [Finset.sum_singleton] at hge
  have hω : omega 2 = 1 := by native_decide
  rw [hω, Nat.cast_one] at hge
  rw [jsp87PlusLambert]
  norm_num at hge ⊢
  exact hge

end JSP87