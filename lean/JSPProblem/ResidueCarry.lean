/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertIdentity
import JSPProblem.Periodicity
import JSPProblem.Multiplier
import Mathlib.Data.Nat.Prime.Infinite
import JSPProblem.CarryAsymptotic
import JSPProblem.Diophantine
import Mathlib.Tactic

/-!
# JSP-000087 : the prime-residue form of the Erdős carry

## The new attack family

For a cut point `M ≥ 1` and a **prime** `p`, the summand `ω (M + k)` counts the
primes dividing `M + k`, and the multiples of `p` lying above `M` form an
arithmetic progression whose first element is `M + j` with `j = 0` if `p ∣ M` and
`j = p - (M % p)` otherwise.  Equivalently, if

```
jsp87ResExp M p = p      if p ∣ M
jsp87ResExp M p = M % p  otherwise          ( 1 ≤ jsp87ResExp M p ≤ p )
```

then `p` contributes `2 ^ (jsp87ResExp M p - M - 1) / (2 ^ p - 1)` to
`jsp87Tail M`.  Hence the Erdős carry admits the **exact Lambert-type
expansion**

```
2 ^ (M + 1) * jsp87Tail M = ∑' p prime, 2 ^ (jsp87ResExp M p) / (2 ^ p - 1)
```

(`jsp87Carry_eq_residueLambert`), i.e. **the carry at `M` is a prime-residue Lambert
sum**.  This is a genuinely new object: rounds 37–83 attacked the series from
the `ω`-side (tails, carries, digit bookkeeping, subword complexity, block
periods, sieve models, base families, level sets, multiplicative translations),
and the Lambert side only for the *whole* series
(`∑' p, 1 / (2 ^ p - 1) = 2 · jsp87Series`).  **No round ever read the carry at
a single cut point prime by prime.**

## What it gives

* `jsp87C_eq_resExp` : the whole rescaled Lambert column at cut point `M` is a
  single monomial, `2 ^ (M + 1) * ∑' k, lamF (M + k, p) = 2 ^ (jsp87ResExp M p) / (2 ^ p - 1)`.
* `jsp87Carry_eq_residueLambert` : **the carry at `M` is a prime-residue Lambert
  sum**, `2 * jsp87Carry M = ∑' p prime, 2 ^ (jsp87ResExp M p) / (2 ^ p - 1)`.
* `jsp87Carry_one_eq` : `jsp87Carry 1 = 2 * jsp87Series`, and
  `jsp87ResidueGap_eq` : the residue sum at `M` minus the residue sum at `1` is
  exactly `2 * (jsp87Carry M - 2 * jsp87Series)`.
* `jsp87Carry_ge_carry_one` / `jsp87Carry_gt_carry_one` : **the carry sequence
  attains its unique minimum at the cut point `M = 1`**, and the minimum is
  `2 * jsp87Series`.
* `jsp87ResidueGap_ge_term` / `jsp87Carry_ge_residue` : a single prime term of the
  residue sum already bounds the gap, and hence the carry.
* `jsp87Carry_ge_dvd` : for a prime `p ∣ M`,
  `jsp87Carry M ≥ 2 * jsp87Series + (2 ^ p - 2) / (2 ^ p - 1) / 2`.
* `jsp87Carry_ge_series_add_omega` : **the wheel bound**
  `jsp87Carry M ≥ 2 * jsp87Series + ω M / 3` for every `M ≥ 1`, obtained by
  summing the prime-divisor gap over `M.primeFactors`.

## What it does *not* give

The headline `jsp_000087_main` is still out of reach: the published result is
**conditional** (Pratt, arXiv:2409.15185, uniform prime `k`-tuples) and the
blocker `jsp87_digit_not_eventuallyPeriodic` (aperiodicity of the binary digits
of the series) is unchanged.  What is new here is a *third* exact handle on the
same number — the carry, the Lambert value, and now the prime-residue
representation — which reduces the search for a rationality obstruction to a
search over the residue vector `(M % p)` of the cut point.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 8000000

/-! ## 1. The shifted prime slices are summable -/

theorem summable_lamF_add (M p : ℕ) : Summable (fun k : ℕ => lamF (M + k, p)) := by
  have h1 : Summable (fun k : ℕ => ((2 : ℝ) ^ (M + k + 1))⁻¹) := by
    refine (summable_two_pow_negK (M + 1)).congr fun k => ?_
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  refine Summable.of_nonneg_of_le (fun k => lamF_nonneg _) (fun k => ?_) h1
  simp only [lamF]
  split_ifs <;> first | exact le_rfl | positivity

/-- **The prime column at a fixed index is a finite sum.** -/
theorem summable_lamF_col (n : ℕ) : Summable (fun q : ℕ => lamF (n, q)) := by
  refine summable_of_hasFiniteSupport ?_
  refine Set.Finite.subset (Finset.finite_toSet (s := (Finset.range (n + 1) : Finset ℕ))) ?_
  intro q hq
  have hne0 : lamF (n, q) ≠ 0 := hq
  have hne : ¬((if q.Prime ∧ 1 ≤ n ∧ q ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) = 0) := by
    intro hcon
    exact hne0 (by rw [lamF]; exact hcon)
  by_cases h : q.Prime ∧ 1 ≤ n ∧ q ∣ n
  · have hq2 : q ≤ n := Nat.le_of_dvd (by omega) h.2.2
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
  · rw [if_neg h] at hne
    exact absurd hne (by simp)

/-- `2 ^ (M+1)` kills the `2 ^ -(M+1)` factor of the prime slice. -/
theorem two_pow_mul_lamF (M p : ℕ) :
    ((2 : ℝ) ^ (M + 1)) * lamF (M, p) = (if p.Prime ∧ 1 ≤ M ∧ p ∣ M then (1 : ℝ) else 0) := by
  have hz : ((2 : ℝ) ^ (M + 1)) ≠ 0 := by positivity
  by_cases h : p.Prime ∧ 1 ≤ M ∧ p ∣ M
  · simp [lamF, h, hz]
  · simp [lamF, h]

/-! ## 2. The residue exponent -/

/-- **The residue exponent.**  For `M` and a prime `p`, `jsp87ResExp M p` is the
unique element of `1, …, p` congruent to `M` modulo `p`: it equals `p` when
`p ∣ M` and `M % p` otherwise.  It measures how far the cut point `M` sits behind
the next multiple of `p`, and it is the weight with which `p` contributes to the
carry at `M`. -/
noncomputable def jsp87ResExp (M p : ℕ) : ℕ := if M % p = 0 then p else M % p

theorem jsp87ResExp_le {M p : ℕ} (hp : 1 ≤ p) : jsp87ResExp M p ≤ p := by
  unfold jsp87ResExp
  split_ifs
  · rfl
  · exact (Nat.mod_lt _ hp).le

theorem jsp87ResExp_pos {M p : ℕ} (hp : 1 ≤ p) : 1 ≤ jsp87ResExp M p := by
  unfold jsp87ResExp
  split_ifs with h
  · exact hp
  · exact Nat.pos_of_ne_zero h

theorem jsp87ResExp_eq_dvd {M p : ℕ} (hp : 2 ≤ p) :
    jsp87ResExp M p = p ↔ p ∣ M := by
  unfold jsp87ResExp
  constructor
  · intro h
    by_cases hm : M % p = 0
    · exact Nat.dvd_iff_mod_eq_zero.mpr hm
    · rw [if_neg hm] at h
      exact absurd h (Nat.ne_of_lt (Nat.mod_lt _ (by omega)))
  · intro h
    have hm : M % p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [if_pos hm]

/-- **Successor rule for the residue exponent.** -/
theorem jsp87ResExp_succ (M p : ℕ) (hp : 2 ≤ p) :
    jsp87ResExp (M + 1) p = if jsp87ResExp M p = p then 1 else jsp87ResExp M p + 1 := by
  have hrlt : M % p < p := Nat.mod_lt _ (by omega)
  by_cases h0 : M % p = 0
  · have hdiv : p * (M / p) = M := by
      have hcd := Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr h0)
      exact (Nat.mul_comm (M / p) p).symm.trans hcd
    have hmod : (M + 1) % p = 1 := by
      have hM : M + 1 = 1 + p * (M / p) := by rw [hdiv]; ring
      rw [hM, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hself : jsp87ResExp M p = p := by simp [jsp87ResExp, h0]
    rw [hself, if_pos rfl]
    simp [jsp87ResExp, hmod]
  · have hre : jsp87ResExp M p = M % p := by simp [jsp87ResExp, h0]
    have hne : jsp87ResExp M p ≠ p := by rw [hre]; exact Nat.ne_of_lt hrlt
    rw [if_neg hne, hre]
    by_cases hr1 : M % p + 1 < p
    · have hM : M + 1 = (M % p + 1) + p * (M / p) := by
        have h := (Nat.mod_add_div M p).symm
        omega
      have hmod : (M + 1) % p = M % p + 1 := by
        rw [hM, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
      simp only [jsp87ResExp]
      rw [if_neg (by omega)]
      exact hmod
    · have hle : M % p + 1 = p := by omega
      have hM : M + 1 = p + p * (M / p) := by
        have h := (Nat.mod_add_div M p).symm
        omega
      have hmod : (M + 1) % p = 0 := by
        rw [hM, Nat.add_mul_mod_self_left, ← hle, Nat.mod_self]
      simp only [jsp87ResExp]
      rw [if_pos hmod]
      exact hle.symm

/-- **The two-step arithmetic of the residue exponent.**  Moving the cut point by
one multiplies the residue weight by `2`, except at the multiples of `p` where it
drops from `2 ^ p` back to `2`. -/
theorem two_pow_resExp_step (M p : ℕ) (hp : 2 ≤ p) :
    (2 : ℝ) ^ jsp87ResExp M p - (2 : ℝ) ^ jsp87ResExp (M + 1) p / 2
      = if jsp87ResExp M p = p then (2 : ℝ) ^ p - 1 else 0 := by
  rw [jsp87ResExp_succ M p hp]
  split_ifs with h
  · rw [h]
    norm_num
  · rw [pow_succ]
    ring

/-! ## 3. The prime-residue inner sum -/

/-- `lamF` read at the translated cut point `M`. -/
noncomputable def lamF' (M : ℕ) (c : ℕ × ℕ) : ℝ := lamF (M + c.1, c.2)

theorem lamF'_nonneg (M : ℕ) (c : ℕ × ℕ) : 0 ≤ lamF' M c := lamF_nonneg _

theorem summable_lamF' (M : ℕ) : Summable (lamF' M) := by
  have hid : ∀ k : ℕ, ∑' p : ℕ, lamF' M (k, p) = jsp87Term (M + k) := by
    intro k
    simp only [lamF']
    exact tsum_lamF_snd (M + k)
  have hs : Summable (fun k : ℕ => jsp87Term (M + k)) :=
    ((summable_nat_add_iff (f := jsp87Term) M).2 summable_omega_mul_inv_two_pow).congr
      fun k => by rw [Nat.add_comm]
  refine (summable_prod_of_nonneg (f := lamF' M) (lamF'_nonneg M)).2 ⟨?_, ?_⟩
  · intro k
    exact summable_lamF_col (M + k)
  · refine Summable.of_nonneg_of_le (f := fun k => ∑' p : ℕ, lamF' M (k, p))
      (fun k => ?_) (fun k => ?_) ?_
    · exact tsum_nonneg fun p => lamF_nonneg _
    · rw [hid k]
    · exact hs.congr fun k => (hid k).symm

/-- The `2 ^ (M+1)`-rescaled prime slice of the carry at `M`. -/
noncomputable def jsp87C (M p : ℕ) : ℝ := ((2 : ℝ) ^ (M + 1)) * ∑' k : ℕ, lamF (M + k, p)

theorem tsum_lamF_add_eq (M p : ℕ) :
    (∑' k : ℕ, lamF (M + k, p)) - lamF (M, p)
      = ∑' k : ℕ, lamF (M + 1 + k, p) := by
  have hf : Summable (fun k : ℕ => lamF (M + k, p)) := summable_lamF_add M p
  have hid : (∑' i : ℕ, lamF (M + (i + 1), p)) = ∑' i : ℕ, lamF (M + 1 + i, p) := by
    refine tsum_congr fun i => ?_
    simp only [Nat.add_comm, Nat.add_left_comm]
  have hh := hf.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, hid] at hh
  have heq : lamF (M + 0, p) = lamF (M, p) := by
    have hzz : M + 0 = M := by omega
    rw [hzz]
  rw [heq] at hh
  linarith

theorem jsp87C_succ (M p : ℕ) :
    jsp87C (M + 1) p = 2 * (jsp87C M p - ((2 : ℝ) ^ (M + 1)) * lamF (M, p)) := by
  have hts := tsum_lamF_add_eq M p
  simp only [jsp87C]
  rw [← hts]
  rw [pow_succ]
  ring

theorem jsp87C_zero (p : ℕ) (hp : p.Prime) :
    jsp87C 0 p = (1 : ℝ) / ((2 : ℝ) ^ p - 1) := by
  have hts := (hasSum_lamF_fst p).tsum_eq
  rw [if_pos hp] at hts
  have hfun : (fun k : ℕ => lamF (0 + k, p)) = fun k => lamF (k, p) := by
    funext k
    simp only [Nat.zero_add]
  simp only [jsp87C]
  rw [hfun, hts]
  have hpw : (2 : ℝ) ^ (p + 1) - 2 = 2 * ((2 : ℝ) ^ p - 1) := by
    rw [pow_succ]
    ring
  rw [← one_div, hpw]
  field_simp
  ring

/-- **The prime slice at the first cut point.** -/
theorem jsp87C_one (p : ℕ) (hp : p.Prime) :
    jsp87C 1 p = 2 * ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hlam0 : lamF (0, p) = 0 := by simp [lamF]
  have hrec := jsp87C_succ 0 p
  rw [hlam0, mul_zero, sub_zero] at hrec
  rw [hrec, jsp87C_zero p hp, div_eq_mul_inv]
  ring

/-- **THE FLAGSHIP INNER SUM.**  For `M ≥ 1` and a prime `p`,

`2 ^ (M+1) · ∑' k, lamF (M + k, p) = 2 ^ (jsp87ResExp M p) / (2 ^ p - 1)`:

the prime slice of the carry is the Lambert term `1 / (2 ^ p - 1)` reweighted by
the residue of the cut point. -/
theorem jsp87C_eq_resExp (M p : ℕ) (hp : p.Prime) (hM : 1 ≤ M) :
    ((2 : ℝ) ^ (M + 1)) * ∑' k : ℕ, lamF (M + k, p)
      = ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hz : ((2 : ℝ) ^ p - 1) ≠ 0 := by
    have hge : (2 : ℝ) ≤ (2 : ℝ) ^ p := two_pow_ge_two (p := p) (by omega)
    linarith
  induction M, hM using Nat.le_induction with
  | base =>
    have hre : jsp87ResExp 1 p = 1 := by
      have hlt : (1 : ℕ) < p := by omega
      have hne : ¬((1 : ℕ) % p = 0) := by
        intro hh
        have : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hlt
        rw [this] at hh
        exact absurd hh (by norm_num)
      unfold jsp87ResExp
      rw [if_neg hne]
      exact Nat.mod_eq_of_lt hlt
    rw [hre]
    have hself : ((2 : ℝ) ^ (1 + 1)) * ∑' k : ℕ, lamF (1 + k, p) = jsp87C 1 p := rfl
    rw [hself]
    simpa using (jsp87C_one p hp)
  | @succ n _ ih =>
    have hts := tsum_lamF_add_eq n p
    have hA : ((2 : ℝ) ^ (n + 2)) * ∑' k : ℕ, lamF (n + 1 + k, p)
        = ((2 : ℝ) ^ (n + 2)) * (∑' k : ℕ, lamF (n + k, p) - lamF (n, p)) := by
      rw [← hts]
    have hlam : ((2 : ℝ) ^ (n + 1)) * lamF (n, p)
        = (if jsp87ResExp n p = p then (1 : ℝ) else 0) := by
      rw [two_pow_mul_lamF]
      have heq : (p.Prime ∧ 1 ≤ n ∧ p ∣ n) ↔ (jsp87ResExp n p = p) := by
        constructor
        · intro h
          exact jsp87ResExp_eq_dvd hp2 |>.2 h.2.2
        · intro h
          have h1n : 1 ≤ n := by omega
          exact ⟨hp, h1n, jsp87ResExp_eq_dvd hp2 |>.1 h⟩
      by_cases h1 : jsp87ResExp n p = p
      · rw [if_pos h1, if_pos (heq.mpr h1)]
      · rw [if_neg h1, if_neg (heq.not.mpr h1)]
    have hR : ((2 : ℝ) ^ jsp87ResExp (n + 1) p) * ((2 : ℝ) ^ p - 1)⁻¹
        = 2 * (((2 : ℝ) ^ jsp87ResExp n p) * ((2 : ℝ) ^ p - 1)⁻¹
            - (if jsp87ResExp n p = p then (1 : ℝ) else 0)) := by
      rw [jsp87ResExp_succ n p hp2]
      split_ifs with h
      · rw [h]
        field_simp
        ring
      · rw [pow_succ]
        field_simp
        ring
    have hs : (∑' k : ℕ, lamF (n + k, p) - lamF (n, p))
        = ((2 : ℝ) ^ (n + 1))⁻¹
          * (((2 : ℝ) ^ jsp87ResExp n p) * ((2 : ℝ) ^ p - 1)⁻¹
            - (if jsp87ResExp n p = p then (1 : ℝ) else 0)) := by
      rw [← ih, ← hlam]
      field_simp
    have hfin2 : ((2 : ℝ) ^ (n + 2)) * ((2 : ℝ) ^ (n + 1))⁻¹ = 2 := by
      rw [pow_succ, mul_comm ((2 : ℝ) ^ (n + 1)) (2 : ℝ), mul_assoc,
        mul_inv_cancel₀ (by positivity), mul_one]
    rw [hA, hs, ← mul_assoc, hfin2]
    exact hR.symm

/-- A power-of-two monotonicity helper (for `2`). -/
theorem pow_le_pow_nat {a : ℝ} {m n : ℕ} (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := by
  induction n generalizing m with
  | zero =>
      have : m = 0 := by omega
      subst this
      simp
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq
        exact le_of_eq (pow_succ _ _)
      · have h1 : m ≤ k := by omega
        have h2 : a ^ k ≤ a ^ (k + 1) := by
          rw [pow_succ]
          have hnon : (0 : ℝ) ≤ a := by linarith
          simpa using (mul_le_mul_of_nonneg_left ha (pow_nonneg hnon k))
        linarith [ih h1]

/-! ## 4. Elementary analytic helpers -/

/-- The Mersenne number `2 ^ p - 1` is positive for `p ≥ 2`. -/
theorem mer_pos {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
  have hge : (2 : ℝ) ≤ (2 : ℝ) ^ p := two_pow_ge_two (p := p) (by omega)
  linarith

/-- `1 / (2 ^ p - 1) ≤ 2 / 2 ^ p` for `p ≥ 2`. -/
theorem inv_mer_le_two_inv {p : ℕ} (hp : 2 ≤ p) :
    ((2 : ℝ) ^ p - 1)⁻¹ ≤ 2 * ((2 : ℝ) ^ p)⁻¹ := by
  have hz1 : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp
  rw [show ((2 : ℝ) ^ p - 1)⁻¹ = (1 : ℝ) / ((2 : ℝ) ^ p - 1) by rw [inv_eq_one_div],
    div_le_iff₀ hz1]
  field_simp
  nlinarith [two_pow_ge_two (p := p) (by omega)]

/-- A residue weight at most `2 ^ p`, divided by `2 ^ p - 1`, is at most `2`. -/
theorem le_mer (a : ℝ) {p : ℕ} (hp : 2 ≤ p) (hnum : a ≤ (2 : ℝ) ^ p) :
    a * ((2 : ℝ) ^ p - 1)⁻¹ ≤ 2 := by
  have hz1 : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp
  rw [show a * ((2 : ℝ) ^ p - 1)⁻¹ = a / ((2 : ℝ) ^ p - 1) by rw [div_eq_mul_inv],
    div_le_iff₀ hz1]
  linarith [two_pow_ge_two (p := p) (by omega)]

/-- **The Mersenne denominator is at most twice the Mersenne power:** for
`p ≥ 2`, `2 ^ M / (2 ^ p - 1) ≤ 2 ^ (M+1) / 2 ^ p`. -/
theorem le_mer_shift (M p : ℕ) (hp2 : 2 ≤ p) :
    ((2 : ℝ) ^ M) * ((2 : ℝ) ^ p - 1)⁻¹ ≤ ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ p)⁻¹ := by
  have hr : ((2 : ℝ) ^ p - 1) ≠ 0 := ne_of_gt (mer_pos hp2)
  field_simp
  rw [div_le_iff₀ (mer_pos hp2)]
  rw [← pow_add, mul_sub, ← pow_add]
  have hyx : (2 : ℝ) ^ (M + 1) ≤ (2 : ℝ) ^ (M + p) := pow_le_pow_nat (by norm_num) (by omega)
  have hz : (2 : ℝ) ^ (M + 1 + p) = 2 * (2 : ℝ) ^ (M + p) := by
    conv_rhs =>
      rw [mul_comm (2 : ℝ) ((2 : ℝ) ^ (M + p)), ← pow_succ,
        show M + p + 1 = M + 1 + p by omega]
  nlinarith

/-- **A `Finset` sum of nonnegative terms is bounded by the full `tsum`.** -/
theorem sum_le_tsum_nonneg' {f : ℕ → ℝ} (hf : ∀ i, (0 : ℝ) ≤ f i) (hf' : Summable f)
    (s : Finset ℕ) :
    (∑ i ∈ s, f i) ≤ ∑' i, f i := by
  have h1 : ∀ i, (0 : ℝ) ≤ ((s : Set ℕ).indicator f i) := by
    intro i
    by_cases hi : i ∈ (s : Set ℕ)
    · rw [Set.indicator_of_mem hi f]; exact hf i
    · rw [Set.indicator_apply, if_neg hi]
  have h2 : ∀ i, ((s : Set ℕ).indicator f i) ≤ f i := by
    intro i
    by_cases hi : i ∈ (s : Set ℕ)
    · rw [Set.indicator_of_mem hi f]
    · rw [Set.indicator_apply, if_neg hi]; exact hf i
  have hs : Summable ((s : Set ℕ).indicator f) := Summable.of_nonneg_of_le h1 h2 hf'
  have hle := Summable.tsum_le_tsum h2 hs hf'
  rw [← sum_eq_tsum_indicator f s] at hle
  exact hle

/-! ## 5. The prime-residue Lambert expansion of the carry -/

/-- **THE PRIME-RESIDUE LAMBERT SUM.**  For the cut point `M`, the sum over the
primes of the residue weight `2 ^ (jsp87ResExp M p)` divided by the Mersenne
number `2 ^ p - 1`. -/
noncomputable def jsp87ResidueLambert (M : ℕ) : ℝ :=
  ∑' p : ℕ,
    (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)

/-- **THE PRIME-RESIDUE GAP.**  The difference between the prime-residue Lambert
sum at `M` and the same sum at the cut point `1`. -/
noncomputable def jsp87ResidueGap (M : ℕ) : ℝ :=
  ∑' p : ℕ,
    (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)

theorem summable_jsp87ResidueLambert {M : ℕ} (hM : 1 ≤ M) :
    Summable (fun p : ℕ =>
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
  have hgeom : Summable (fun p : ℕ => ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ p)⁻¹) := by
    have h1 := (summable_two_pow_negK 0).mul_left ((2 : ℝ) ^ (M + 1))
    refine h1.congr fun p => ?_
    have hp0 : p + 0 = p := by omega
    rw [hp0]
  have hfin : Summable (fun p : ℕ => (if p ≤ M then (2 : ℝ) else 0)) := by
    refine summable_of_hasFiniteSupport (f := fun p => (if p ≤ M then (2 : ℝ) else 0)) ?_
    refine Set.Finite.subset (Finset.finite_toSet
      (s := (Finset.range (M + 1) : Finset ℕ))) ?_
    intro p hp
    by_cases h : p ≤ M
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    · have hne : (if p ≤ M then (2 : ℝ) else 0) ≠ 0 := hp
      rw [if_neg h] at hne
      exact absurd hne (by simp)
  have hgeom : Summable (fun p : ℕ => ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ p)⁻¹) := by
    have h1 := (summable_two_pow_negK 0).mul_left ((2 : ℝ) ^ (M + 1))
    refine h1.congr fun p => ?_
    have hp0 : p + 0 = p := by omega
    rw [hp0]
  have htail : Summable (fun p : ℕ => (if p ≤ M then (0 : ℝ)
      else ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ p)⁻¹)) := by
    have hc1 : ∀ q : ℕ, (0 : ℝ) ≤ (if q ≤ M then (0 : ℝ)
        else ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ q)⁻¹) := by
      intro q
      split_ifs <;> positivity
    have hc2 : ∀ q : ℕ, (if q ≤ M then (0 : ℝ)
        else ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ q)⁻¹)
        ≤ ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ q)⁻¹ := by
      intro q
      split_ifs <;> first | exact le_rfl | positivity
    exact Summable.of_nonneg_of_le hc1 hc2 hgeom
  have hmaj : Summable (fun p : ℕ => (if p ≤ M then (2 : ℝ)
      else ((2 : ℝ) ^ (M + 1)) * ((2 : ℝ) ^ p)⁻¹)) := by
    refine (hfin.add htail).congr fun p => ?_
    by_cases h : p ≤ M <;> simp [h] <;> ring
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
  · by_cases hp : p.Prime
    · have hden : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp.two_le
      split_ifs <;> positivity
    · split_ifs <;> positivity
  · by_cases hp : p.Prime
    · by_cases hle : p ≤ M
      · have hp2 : 2 ≤ p := hp.two_le
        have hexp : jsp87ResExp M p ≤ p := jsp87ResExp_le (by omega)
        rw [if_pos hp, if_pos hle]
        have h1 := le_mer _ hp2 (pow_le_pow_nat (by norm_num) hexp)
        linarith
      · rw [if_pos hp, if_neg hle]
        have hre : jsp87ResExp M p = M := by
          have hcases : jsp87ResExp M p = M % p ∨ jsp87ResExp M p = p := by
            unfold jsp87ResExp
            split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
          rcases hcases with hc | hc
          · rw [hc, Nat.mod_eq_of_lt (by omega)]
          · rw [hc]
            exact absurd (Nat.le_of_dvd (Nat.succ_le_iff.mp (by omega : 0 < M))
              (jsp87ResExp_eq_dvd (M := M) (p := p) hp.two_le |>.1 hc)) hle
        rw [hre]
        exact le_mer_shift M p hp.two_le
    · rw [if_neg hp]
      split_ifs <;> positivity

theorem jsp87ResidueGap_nonneg_term (M p : ℕ) :
    0 ≤ (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
  by_cases hp : p.Prime
  · rw [if_pos hp]
    have hpos : (1 : ℕ) ≤ jsp87ResExp M p := jsp87ResExp_pos (Nat.succ_le_of_lt hp.pos)
    have hden : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp.two_le
    have hnum : (0 : ℝ) ≤ (2 : ℝ) ^ jsp87ResExp M p - 2 := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 1 := by norm_num
      have h2 := pow_le_pow_nat h1 hpos
      norm_num at h2 ⊢
      exact h2
    have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ p - 1)⁻¹ := inv_nonneg.mpr hden.le
    exact mul_nonneg hnum hinv
  · rw [if_neg hp]

theorem jsp87GapTerm_le_lambertTerm (M q : ℕ) :
    (if q.Prime then ((2 : ℝ) ^ jsp87ResExp M q - 2) * ((2 : ℝ) ^ q - 1)⁻¹ else 0)
      ≤ (if q.Prime then ((2 : ℝ) ^ jsp87ResExp M q) * ((2 : ℝ) ^ q - 1)⁻¹ else 0) := by
  by_cases hq : q.Prime
  · rw [if_pos hq, if_pos hq]
    have hkey : (2 : ℝ) ^ jsp87ResExp M q - 2 ≤ (2 : ℝ) ^ jsp87ResExp M q := by
      have hpos : (1 : ℕ) ≤ jsp87ResExp M q := jsp87ResExp_pos (Nat.succ_le_of_lt hq.pos)
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 1 := by norm_num
      have h2 := pow_le_pow_nat h1 hpos
      norm_num at h2 ⊢
    exact mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (mer_pos hq.two_le).le)
  · rw [if_neg hq, if_neg hq]


theorem summable_jsp87ResidueGap {M : ℕ} (hM : 1 ≤ M) :
    Summable (fun p : ℕ =>
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
  refine Summable.of_nonneg_of_le (fun p => jsp87ResidueGap_nonneg_term M p)
    (fun p => jsp87GapTerm_le_lambertTerm M p)
    (summable_jsp87ResidueLambert (M := M) hM)

theorem summable_gapTerm (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun q : ℕ => (if q.Prime then ((2 : ℝ) ^ jsp87ResExp M q - 2)
      * ((2 : ℝ) ^ q - 1)⁻¹ else 0)) :=
  Summable.of_nonneg_of_le (f := fun q : ℕ => (if q.Prime then
      ((2 : ℝ) ^ jsp87ResExp M q) * ((2 : ℝ) ^ q - 1)⁻¹ else 0))
    (fun q => jsp87ResidueGap_nonneg_term M q) (fun q => jsp87GapTerm_le_lambertTerm M q)
    (summable_jsp87ResidueLambert (M := M) hM)

/-- The residue term of a single prime is nonnegative. -/
theorem jsp87GapTerm_nonneg (M : ℕ) {q : ℕ} (hq : q.Prime) :
    (0 : ℝ) ≤ ((2 : ℝ) ^ jsp87ResExp M q - 2) * ((2 : ℝ) ^ q - 1)⁻¹ := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ q - 1 := mer_pos hq.two_le
  have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ q - 1)⁻¹ := inv_nonneg.mpr (le_of_lt hden)
  have hnum : (0 : ℝ) ≤ (2 : ℝ) ^ jsp87ResExp M q - 2 :=
    sub_nonneg.mpr (by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ jsp87ResExp M q :=
        two_pow_ge_two (p := jsp87ResExp M q) (jsp87ResExp_pos (M := M) hq.one_le)
      linarith)
  exact mul_nonneg hnum hinv

/-- The residue term of a single prime is at most its Lambert term. -/
theorem jsp87GapTerm_le' (M : ℕ) {q : ℕ} (hq : q.Prime) :
    ((2 : ℝ) ^ jsp87ResExp M q - 2) * ((2 : ℝ) ^ q - 1)⁻¹
      ≤ ((2 : ℝ) ^ jsp87ResExp M q) * ((2 : ℝ) ^ q - 1)⁻¹ :=
  mul_le_mul_of_nonneg_right (by norm_num)
    (inv_nonneg.mpr (le_of_lt (mer_pos hq.two_le)))

/-- The Lambert (non-gap) residue term of a single prime is nonnegative. -/
theorem jsp87LambertTerm_nonneg (M : ℕ) {q : ℕ} (hq : q.Prime) :
    (0 : ℝ) ≤ ((2 : ℝ) ^ jsp87ResExp M q) * ((2 : ℝ) ^ q - 1)⁻¹ :=
  mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt (mer_pos hq.two_le)))

/-- **THE RESIDUE TERM OF A SINGLE PRIME BOUNDS THE GAP.** -/
theorem jsp87ResidueGap_ge_term (M : ℕ) {p : ℕ} (hp : p.Prime) (hM : 1 ≤ M) :
    (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
      ≤ jsp87ResidueGap M := by
  have hs : Summable (fun j : ℕ => if j = p then
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M j - 2) * ((2 : ℝ) ^ j - 1)⁻¹ else 0) else 0) := by
    refine Summable.of_nonneg_of_le (f := fun j : ℕ => (if j.Prime then
        ((2 : ℝ) ^ jsp87ResExp M j) * ((2 : ℝ) ^ j - 1)⁻¹ else 0))
      (fun j => ?_) (fun j => ?_) (summable_jsp87ResidueLambert (M := M) hM)
    · by_cases hjp : j = p
      · subst hjp
        rw [if_pos rfl, if_pos hp]
        exact jsp87GapTerm_nonneg M hp
      · rw [if_neg hjp]
    · by_cases hjp : j = p
      · subst hjp
        rw [if_pos rfl, if_pos hp, if_pos hp]
        exact jsp87GapTerm_le' M hp
      · rw [if_neg hjp]
        by_cases hq : j.Prime
        · rw [if_pos hq]
          exact jsp87LambertTerm_nonneg M hq
        · rw [if_neg hq]
  have hle : (∑' j : ℕ, (if j = p then
        (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M j - 2) * ((2 : ℝ) ^ j - 1)⁻¹ else 0) else 0))
      ≤ ∑' j : ℕ, (if j.Prime then ((2 : ℝ) ^ jsp87ResExp M j - 2) * ((2 : ℝ) ^ j - 1)⁻¹ else 0) :=
    Summable.tsum_le_tsum (fun j => by
      by_cases hjp : j = p
      · subst hjp
        rw [if_pos rfl, if_pos hp]
      · rw [if_neg hjp]
        exact jsp87ResidueGap_nonneg_term M j) hs (summable_gapTerm M hM)
  have hval : (∑' j : ℕ, (if j = p then
        (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M j - 2) * ((2 : ℝ) ^ j - 1)⁻¹ else 0) else 0))
      = ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ := by
    rw [tsum_eq_single p (fun b h => by rw [if_neg h])]
    simp [hp]
  rw [jsp87ResidueGap]
  rw [if_pos hp]
  rw [← hval]
  exact hle

theorem jsp87ResidueLambert_nonneg (M : ℕ) : 0 ≤ jsp87ResidueLambert M :=
  tsum_nonneg fun p => by
    by_cases hp : p.Prime
    · rw [if_pos hp]
      have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ p - 1)⁻¹ := inv_nonneg.mpr (mer_pos hp.two_le).le
      exact mul_nonneg (by positivity) hinv
    · rw [if_neg hp]

/-- **THE FLAGSHIP: the prime-residue Lambert expansion of the Erdős carry.**

For every cut point `M ≥ 1`, the Erdős carry is *exactly* the prime-residue
Lambert sum `∑' p prime, 2 ^ (jsp87ResExp M p) / (2 ^ p - 1)`. -/
theorem jsp87Carry_eq_residueLambert (M : ℕ) (hM : 1 ≤ M) :
    2 * jsp87Carry M = jsp87ResidueLambert M := by
  have h2 : ∀ k : ℕ, (∑' p : ℕ, lamF' M (k, p)) = jsp87Term (M + k) := by
    intro k
    simp only [lamF']
    exact tsum_lamF_snd (M + k)
  have htail : jsp87Tail M = ∑' c : ℕ × ℕ, lamF' M c := by
    calc jsp87Tail M = ∑' k : ℕ, jsp87Term (M + k) := rfl
      _ = ∑' k : ℕ, ∑' p : ℕ, lamF' M (k, p) := tsum_congr fun k => by rw [h2 k]
      _ = ∑' c : ℕ × ℕ, lamF' M c := ((summable_lamF' M).tsum_prod).symm
  have hmul : ∀ p : ℕ, ((2 : ℝ) ^ (M + 1)) * (∑' k : ℕ, lamF (M + k, p))
      = (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · simpa [lamF', hp] using (jsp87C_eq_resExp M p hp hM)
    · have hz0 : (fun k : ℕ => lamF (M + k, p)) = fun _ => (0 : ℝ) := by
        funext k
        simp [lamF, hp]
      rw [hz0]
      simp [hp]
  have hscaled : Summable (fun c : ℕ × ℕ => ((2 : ℝ) ^ (M + 1)) * lamF' M c) :=
    Summable.mul_left ((2 : ℝ) ^ (M + 1)) (summable_lamF' M)
  have hswap2 := Summable.tsum_comm'
    (f := fun k p => ((2 : ℝ) ^ (M + 1)) * lamF' M (k, p)) hscaled
    (fun k => by
      refine (Summable.mul_left (f := fun p => lamF (M + k, p)) ((2 : ℝ) ^ (M + 1))
        (summable_lamF_col (M + k))).congr fun p => ?_
      simp [lamF', mul_left_comm, mul_assoc])
    (fun p => by
      refine (Summable.mul_left (f := fun k => lamF (M + k, p)) ((2 : ℝ) ^ (M + 1))
        (summable_lamF_add M p)).congr fun k => ?_
      simp [lamF', mul_left_comm, mul_assoc])
  have hstep1 : 2 * jsp87Carry M = ((2 : ℝ) ^ (M + 1)) * jsp87Tail M := by
    simp only [jsp87Carry]
    rw [pow_succ, ← mul_assoc]
    ring
  have hfinal : (∑' p : ℕ, ∑' k : ℕ, ((2 : ℝ) ^ (M + 1)) * lamF' M (k, p))
      = jsp87ResidueLambert M := by
    refine tsum_congr fun p => ?_
    have h1 : (∑' k : ℕ, ((2 : ℝ) ^ (M + 1)) * lamF' M (k, p))
        = (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
      have hpt : ∀ k, ((2 : ℝ) ^ (M + 1)) * lamF' M (k, p)
          = ((2 : ℝ) ^ (M + 1)) * lamF (M + k, p) := by
        intro k
        simp [lamF']
      rw [tsum_congr hpt]
      rw [Summable.tsum_mul_left ((2 : ℝ) ^ (M + 1)) (summable_lamF_add M p)]
      exact hmul p
    rw [h1]
  calc 2 * jsp87Carry M = ((2 : ℝ) ^ (M + 1)) * jsp87Tail M := hstep1
    _ = ((2 : ℝ) ^ (M + 1)) * ∑' c : ℕ × ℕ, lamF' M c := by rw [htail]
    _ = ∑' c : ℕ × ℕ, ((2 : ℝ) ^ (M + 1)) * lamF' M c := by
        symm
        exact Summable.tsum_mul_left ((2 : ℝ) ^ (M + 1)) (summable_lamF' M)
    _ = ∑' p : ℕ, ∑' k : ℕ, ((2 : ℝ) ^ (M + 1)) * lamF' M (k, p) :=
        (hscaled.tsum_prod).trans hswap2.symm
    _ = jsp87ResidueLambert M := hfinal

/-! ## 6. The gap is nonnegative, and vanishes only at the first cut -/

/-- `jsp87Carry 1 = 2 · S`. -/
theorem jsp87Carry_one_eq : jsp87Carry 1 = 2 * jsp87Series := by
  simp only [jsp87Carry, pow_one]
  rw [jsp87Tail_one]

/-- **THE GAP IDENTITY.**  `jsp87ResidueGap M = 2 · (jsp87Carry M - 2 · S)`. -/
theorem jsp87ResidueGap_eq (M : ℕ) (hM : 1 ≤ M) :
    jsp87ResidueGap M = 2 * (jsp87Carry M - 2 * jsp87Series) := by
  have hf2 : Summable (fun p : ℕ =>
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) :=
    summable_jsp87ResidueLambert (M := M) hM
  have hg : Summable (fun p : ℕ =>
      (if p.Prime then (2 : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (summable_jsp87ResidueLambert (M := 1) (by norm_num))
    · by_cases hp : p.Prime
      · rw [if_pos hp]
        have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ p - 1)⁻¹ := inv_nonneg.mpr (le_of_lt (mer_pos hp.two_le))
        exact mul_nonneg (by positivity) hinv
      · rw [if_neg hp]
    · by_cases hp : p.Prime
      · rw [if_pos hp, if_pos hp]
        have hre : jsp87ResExp 1 p = 1 := by
          have hp2 : 2 ≤ p := hp.two_le
          have hlt : (1 : ℕ) < p := by omega
          simp [jsp87ResExp, Nat.mod_eq_of_lt hlt]
        rw [hre]
        norm_num
      · rw [if_neg hp, if_neg hp]
  have hpt : ∀ p : ℕ,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
        = (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
          - (if p.Prime then (2 : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    intro p
    by_cases hp : p.Prime
    · simp [hp]
      ring
    · simp [hp]
  have hsplit : ((∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p) * ((2 : ℝ) ^ p - 1)⁻¹
          else 0))
        - ∑' p : ℕ, (if p.Prime then (2 : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = ∑' p : ℕ,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) :=
    (Summable.tsum_sub hf2 hg).symm.trans (tsum_congr fun p => (hpt p).symm)
  have hconst : (∑' p : ℕ, (if p.Prime then (2 : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = jsp87ResidueLambert 1 := by
    have hpt : ∀ p : ℕ, (if p.Prime then (2 : ℝ) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
        = (if p.Prime then ((2 : ℝ) ^ jsp87ResExp 1 p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
      intro p
      by_cases hp : p.Prime
      · have hre : jsp87ResExp 1 p = 1 := by
          have hp2 : 2 ≤ p := hp.two_le
          have hlt : (1 : ℕ) < p := by omega
          simp [jsp87ResExp, Nat.mod_eq_of_lt hlt]
        simp [hp, hre]
      · simp [hp]
    simp only [jsp87ResidueLambert]
    exact (tsum_congr fun p => (hpt p).symm).symm
  have hLamU : (∑' p : ℕ, (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p)
        * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) = 2 * jsp87Carry M :=
    (jsp87Carry_eq_residueLambert M hM).symm
  have hone : jsp87ResidueLambert 1 = 4 * jsp87Series := by
    have hx := jsp87Carry_eq_residueLambert 1 (by norm_num)
    simp only [jsp87ResidueLambert] at hx
    rw [jsp87Carry_one_eq] at hx
    simp only [jsp87ResidueLambert]
    linarith
  simp only [jsp87ResidueGap]
  rw [← hsplit, mul_sub, ← hLamU, hconst, hone]
  ring

theorem jsp87ResidueGap_nonneg (M : ℕ) : 0 ≤ jsp87ResidueGap M :=
  tsum_nonneg fun p => jsp87ResidueGap_nonneg_term M p

/-- **THE CARRY SEQUENCE HAS ITS UNIQUE MINIMUM AT THE CUT POINT `1`.** -/
theorem jsp87Carry_ge_carry_one (M : ℕ) (hM : 1 ≤ M) : jsp87Carry 1 ≤ jsp87Carry M := by
  have h1 := jsp87ResidueGap_nonneg M
  have h2 := jsp87ResidueGap_eq M hM
  rw [h2] at h1
  rw [jsp87Carry_one_eq]
  linarith

theorem jsp87Carry_gt_carry_one (M : ℕ) (hM : 2 ≤ M) : jsp87Carry 1 < jsp87Carry M := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (M + 2)
  have hterm : (0 : ℝ)
      < (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    rw [if_pos hp]
    have hre : jsp87ResExp M p = M := by
      have hcases : jsp87ResExp M p = M % p ∨ jsp87ResExp M p = p := by
        unfold jsp87ResExp
        split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
      rcases hcases with hc | hc
      · rw [hc, Nat.mod_eq_of_lt (by omega)]
      · rw [hc]
        exact absurd (Nat.le_of_dvd (by omega : 0 < M)
          (jsp87ResExp_eq_dvd (M := M) (p := p) hp.two_le |>.1 hc)) (by omega)
    rw [hre]
    have hden : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp.two_le
    have hnum : (2 : ℝ) ≤ (2 : ℝ) ^ M - 2 := by
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ 2 := two_pow_ge_two (p := 2) (by omega)
      have h2 := pow_le_pow_nat (by norm_num : (1 : ℝ) ≤ 2) hM
      norm_num at h1 h2 ⊢
      linarith
    exact div_pos (by linarith) hden
  have hle : (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
      ≤ jsp87ResidueGap M := jsp87ResidueGap_ge_term M hp (by omega)
  have hpos : 0 < jsp87ResidueGap M := lt_of_lt_of_le hterm hle
  rw [jsp87ResidueGap_eq M (by omega)] at hpos
  rw [jsp87Carry_one_eq]
  linarith

/-! ## 7. Pointwise bounds on the carry -/

/-- **THE POINTWISE RESIDUE BOUND ON THE CARRY.** -/
theorem jsp87Carry_ge_residue (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) :
    2 * jsp87Series
        + ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ / 2
      ≤ jsp87Carry M := by
  have hle := jsp87ResidueGap_ge_term M hp hM
  have h1 := jsp87ResidueGap_eq M hM
  rw [if_pos hp] at hle
  rw [h1] at hle
  linarith

/-- **THE GAP OF A PRIME DIVISOR.** -/
theorem jsp87Carry_ge_dvd (M : ℕ) (hM : 1 ≤ M) {p : ℕ} (hp : p.Prime) (hd : p ∣ M) :
    2 * jsp87Series + ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ / 2 ≤ jsp87Carry M := by
  have hre : jsp87ResExp M p = p := jsp87ResExp_eq_dvd hp.two_le |>.2 hd
  have h := jsp87Carry_ge_residue M hM p hp
  rw [hre] at h
  exact h

/-- The plain prime term `(2 ^ p - 2) / (2 ^ p - 1)` is nonnegative, and at
least `2 / 3` in size. -/
theorem jsp87PlainTerm_bounds (p : ℕ) (hp : p.Prime) :
    (0 : ℝ) ≤ ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹
      ∧ (2 : ℝ) / 3 ≤ ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ p - 1 := mer_pos hp.two_le
  have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ p - 1)⁻¹ := inv_nonneg.mpr (le_of_lt hden)
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ p := two_pow_ge_two (p := p) hp.one_le
  have hnonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ :=
    mul_nonneg (by linarith) hinv
  refine ⟨hnonneg, ?_⟩
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ p := by
    have h := pow_le_pow_nat (by norm_num : (1 : ℝ) ≤ 2) hp.two_le
    norm_num at h
    exact h
  have hkey' : (2 : ℝ) / 3 ≤ ((2 : ℝ) ^ p - 2) / ((2 : ℝ) ^ p - 1) :=
    (le_div_iff₀ hden).mpr (by linarith [h4])
  rwa [div_eq_mul_inv] at hkey'

/-- **THE WHEEL BOUND ON THE GAP: the prime divisors of `M` are counted.** -/
theorem jsp87ResidueGap_ge_primeFactors_sum (M : ℕ) (hM : 1 ≤ M) :
    (∑ p ∈ M.primeFactors,
      (if p.Prime then ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ jsp87ResidueGap M := by
  have hgated := sum_le_tsum_nonneg'
    (f := fun q : ℕ => (if q.Prime then ((2 : ℝ) ^ jsp87ResExp M q - 2)
      * ((2 : ℝ) ^ q - 1)⁻¹ else 0))
    (fun q => jsp87ResidueGap_nonneg_term M q) (summable_gapTerm M hM) M.primeFactors
  have hA : (∑ p ∈ M.primeFactors,
      (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ jsp87ResidueGap M := by
    have h' : (∑ i ∈ M.primeFactors,
        (if i.Prime then ((2 : ℝ) ^ jsp87ResExp M i - 2) * ((2 : ℝ) ^ i - 1)⁻¹ else 0))
        ≤ ∑' (i : ℕ), (if i.Prime then ((2 : ℝ) ^ jsp87ResExp M i - 2)
          * ((2 : ℝ) ^ i - 1)⁻¹ else 0) := hgated
    rwa [show (∑' (i : ℕ), (if i.Prime then ((2 : ℝ) ^ jsp87ResExp M i - 2)
        * ((2 : ℝ) ^ i - 1)⁻¹ else 0)) = jsp87ResidueGap M from rfl] at h'
  have heq : (∑ p ∈ M.primeFactors,
        (if p.Prime then ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = ∑ p ∈ M.primeFactors,
        (if p.Prime then ((2 : ℝ) ^ jsp87ResExp M p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hd : p ∣ M := (Nat.mem_primeFactors.mp hp).2.1
    have hre : jsp87ResExp M p = p := jsp87ResExp_eq_dvd hp'.two_le |>.2 hd
    rw [hre, if_pos hp']
  rw [heq]
  exact hA

/-- **THE CARRY DOMINATES `ω M / 3` ABOVE ITS MINIMUM.** -/
theorem jsp87Carry_ge_series_add_omega (M : ℕ) (hM : 1 ≤ M) :
    2 * jsp87Series + (omega M : ℝ) / 3 ≤ jsp87Carry M := by
  have hsum := jsp87ResidueGap_ge_primeFactors_sum M hM
  have hcard : ((omega M : ℝ)) = (M.primeFactors.card : ℝ) := by
    simp only [omega, Nat.cast_ofNat]
  have h3 : (2 / 3) * ((M.primeFactors.card : ℝ))
      ≤ ∑ p ∈ M.primeFactors,
        (if p.Prime then ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    have heq : (2 / 3) * ((M.primeFactors.card : ℝ))
        = ∑ _p ∈ M.primeFactors, ((2 : ℝ) / 3 * 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [heq]
    exact Finset.sum_le_sum (fun p hp => by
      have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
      rw [if_pos hp']
      have hb := (jsp87PlainTerm_bounds p hp').2
      norm_num
      exact hb)
  have h3' : (2 / 3) * ((omega M : ℝ))
      ≤ ∑ p ∈ M.primeFactors,
        (if p.Prime then ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    rwa [← hcard] at h3
  have h1 := jsp87ResidueGap_eq M hM
  have h4 : (∑ p ∈ M.primeFactors,
      (if p.Prime then ((2 : ℝ) ^ p - 2) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      ≤ 2 * (jsp87Carry M - 2 * jsp87Series) := by
    rwa [h1] at hsum
  linarith

end JSP87
