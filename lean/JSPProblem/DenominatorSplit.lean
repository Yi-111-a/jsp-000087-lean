/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertTrunc
import Mathlib.Data.Nat.GCD.Basic

/-!
# JSP-000087 : the denominator split between the Lambert tail and the Erdős carry

`JSPProblem/Diophantine.lean` built the **Erdős side** of the argument: the binary
prefix `I N ∈ ℤ` and the carry `θ N = 2^N τ N` satisfy `2^N S = I N + θ N`, and a
hypothetical rational `S = a/b` freezes the carries into `(1/b) ℤ`.

`JSPProblem/LambertGcd.lean` and `JSPProblem/LambertTrunc.lean` built the
**Lambert side**: the clearing denominator `D_N = ∏_{p<N, prime} (2^p - 1)` of the
truncation `T N`, with `2 S = T N + R N`, and a rational value of `2 S` freezing
`b · D_N · R N` into `ℤ`.

**The two halves had never been *compared*.**  This file supplies the join.

## The join

Rescaling the Lambert splitting by `2^{N-1}` and substituting `2^N S = I N + θ N`
gives, for every `1 ≤ N`, the identity

```
2^{N-1} · T N  =  I N  +  θ N  -  2^{N-1} · R N ,
```

i.e. **`jsp87NormLambert N = θ N - 2^{N-1} R N`** where `jsp87NormLambert N` is
the *normalised* truncation.  The Erdős carry and the Lambert tail are the **two
summands of a single rational number**, and the content of the Erdős–Pratt
method is precisely the competition between them.

## The denominator of the join

Because `A_N` is coprime to `D_N` (`jsp87_lambertNumer_coprime_den`), the
normalised truncation has *exact* denominator `D_N`:

* `jsp87_normLambert_mul_int` — `D_N` clears it into `ℤ`;
* `jsp87_normLambert_den_exact` — **no smaller positive denominator works**.

`D_N` is odd (`jsp87LambertQ_odd`), so the powers of `2` in the rescaling do not
cancel.

## What a rational value of `S` would force

Assume `2 · S = a / b` with `b > 0` and let `2^{N-1} · R N = m / c` with `c > 0`.
Then

* `jsp87_rational_imp_lambertTail_den` — **`D_N ∣ c · b`**: the denominator of the
  rescaled Lambert tail, multiplied by the hypothetical denominator of the series,
  is a multiple of the whole product of Lambert denominators below `N`.  Nothing
  below `N` can cancel;
* `jsp87_rational_imp_den_prime_gt` — **for every prime `p < N` the integer `c · b`
  has a prime divisor exceeding `p`**, because every prime factor of `2^p - 1`
  exceeds `p` (`Diophantine.primeFactors_sub_one_gt`);
* `jsp87_rational_imp_lambertTail_den_escape` — **for every `K` there is a cut
  point at which the rescaled Lambert tail admits no denominator `≤ K`.**

This is the Lambert half of the Erdős–Pratt obstruction, now at the level of
*exact reduced denominators* rather than inequalities.  It is sharp but, exactly
as before, it is not enough: `D_N` grows super-exponentially in `N`, so the
quantitative window `1/(b D_N) ≤ R N ≤ 4 · 2^{-N}` of
`JSPProblem/LambertTrunc.lean` is never contradicted by it.  The remaining gap is
unchanged: `jsp_000087_main`.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The clearing denominators form a divisibility chain -/

/-- **The clearing denominator of the Lambert truncation at `N`**:
`∏_{p < N, prime} (2^p - 1)`.  This is `lambertDen (range N)` of
`JSPProblem/LambertGcd.lean`, given a short name. -/
noncomputable def jsp87LambertQ (N : ℕ) : ℕ := lambertDen (Finset.range N)

/-- `D_0 = 1`. -/
theorem jsp87LambertQ_zero : jsp87LambertQ 0 = 1 := by
  simp [jsp87LambertQ, lambertDen]

/-- Every clearing denominator is positive. -/
theorem jsp87LambertQ_pos (N : ℕ) : 0 < jsp87LambertQ N := lambertDen_pos _

/-- **The step law.**  Inserting the new index `N` multiplies the clearing
denominator by the new Lambert denominator `2^N - 1`, and by nothing at all when
`N` is not prime. -/
theorem jsp87LambertQ_succ (N : ℕ) :
    jsp87LambertQ (N + 1) = (if (N).Prime then 2 ^ N - 1 else 1) * jsp87LambertQ N := by
  have hgen : ∀ (s : Finset ℕ) (a : ℕ), a ∉ s →
      lambertDen (insert a s) = (if a.Prime then 2 ^ a - 1 else 1) * lambertDen s := by
    intro s a ha
    have h1 : lambertDen (insert a s)
        = (if a.Prime then 2 ^ a - 1 else 1) * lambertDen s := by
      unfold lambertDen
      rw [Finset.prod_insert ha]
    exact h1
  rw [jsp87LambertQ, Finset.range_add_one]
  exact hgen _ _ (by simp [Finset.mem_range])

/-- **THE CHAIN: the clearing denominators divide each other.**  `D_N ∣ D_M` for
`N ≤ M`: the clearing denominators of the truncations form a divisibility chain,
the setting in which a "Cantor series" reading of the Lambert sum is meaningful. -/
theorem jsp87LambertQ_dvd {N M : ℕ} (h : N ≤ M) : jsp87LambertQ N ∣ jsp87LambertQ M := by
  induction M with
  | zero =>
    have h0 : N = 0 := by omega
    subst h0
    exact dvd_refl _
  | succ M ih =>
    rcases h.eq_or_lt with rfl | hlt
    · exact dvd_refl _
    · have h1 : jsp87LambertQ N ∣ jsp87LambertQ M := ih (by omega)
      have hs := jsp87LambertQ_succ M
      rw [hs]
      exact h1.trans (Nat.dvd_mul_left _ _)

/-- `2^k - 1` is odd whenever `1 ≤ k`. -/
private lemma odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  refine ⟨2 ^ (k - 1) - 1, ?_⟩
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have h := pow_succ 2 (k - 1)
    calc 2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 2 ^ (k - 1) * 2 := h
      _ = 2 * 2 ^ (k - 1) := by ring
  have h1le : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  rw [hpow]
  omega

/-- Every clearing denominator is **odd**: the `2`-part of a truncation is
invisible to the Lambert denominators. -/
theorem jsp87LambertQ_odd (N : ℕ) : Odd (jsp87LambertQ N) := by
  induction N with
  | zero => exact odd_one
  | succ N ih =>
    have h1 := jsp87LambertQ_succ N
    by_cases hp : (N).Prime
    · rw [h1, if_pos hp]
      have hodd : Odd (2 ^ N - 1) := odd_two_pow_sub_one hp.one_lt.le
      rcases ih with ⟨i, hi⟩
      rcases hodd with ⟨j, hj⟩
      rw [hi, hj]
      exact ⟨2 * i * j + i + j, by ring⟩
    · rw [h1, if_neg hp]
      simpa using ih

/-- A power of `2` is coprime to any odd number. -/
private lemma coprime_two_pow_of_odd {Q k : ℕ} (hQ : Odd Q) : Nat.Coprime (2 ^ k) Q := by
  induction k with
  | zero => exact Nat.coprime_one_left Q
  | succ k ih =>
    rw [pow_succ]
    exact Nat.Coprime.mul_left ih (Nat.coprime_two_left.mpr hQ)

/-- **`D_N` is coprime to every power of `2`.** -/
theorem coprime_two_pow_lambertQ {k N : ℕ} : Nat.Coprime (2 ^ k) (jsp87LambertQ N) :=
  coprime_two_pow_of_odd (jsp87LambertQ_odd N)

/-- **THE CHAIN IS UNBOUNDED.**  For every `K` there is a cut point `N` whose
clearing denominator exceeds `K`: pick a prime `p > K` and use the single factor
`2^p - 1 ≥ p`. -/
theorem jsp87LambertQ_unbounded (K : ℕ) : ∃ N, K < jsp87LambertQ N := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (K + 1)
  refine ⟨p + 1, ?_⟩
  have hmem : p ∈ Finset.range (p + 1) := Finset.mem_range.mpr p.lt_succ_self
  have hdvd : 2 ^ p - 1 ∣ jsp87LambertQ (p + 1) := by
    show 2 ^ p - 1 ∣ lambertDen (Finset.range (p + 1))
    exact lambertDen_mem_factor hp hmem
  have hge : p ≤ 2 ^ p - 1 := by
    have h1 := succ_le_two_pow p
    omega
  have hle : 2 ^ p - 1 ≤ jsp87LambertQ (p + 1) := Nat.le_of_dvd (jsp87LambertQ_pos (p + 1)) hdvd
  omega

/-! ## 2. The numerators are coprime to the denominators -/

/-- **THE NUMERATOR RECURSION.**  Passing from `N` to `N+1` multiplies the old
numerator by the new Lambert denominator and adds one fresh unit `D_N` when `N`
is prime. -/
theorem jsp87_lambertNumer_succ (N : ℕ) :
    jsp87_lambertNumer (N + 1)
      = (if (N).Prime then 2 ^ N - 1 else 1) * jsp87_lambertNumer N
        + (if (N).Prime then jsp87LambertQ N else 0) := by
  classical
  have hkey : ∀ (p : ℕ) (hps : p < N) (hp : p.Prime),
      jsp87LambertQ (N + 1) / (2 ^ p - 1)
        = (if (N).Prime then 2 ^ N - 1 else 1) * (jsp87LambertQ N / (2 ^ p - 1)) := by
    intro p hps hp
    have hmem : p ∈ Finset.range N := Finset.mem_range.mpr hps
    have hfact : 2 ^ p - 1 ∣ jsp87LambertQ N := by
      show 2 ^ p - 1 ∣ lambertDen (Finset.range N)
      exact lambertDen_mem_factor hp hmem
    have h2p : 2 ≤ p := hp.two_le
    have hqpos : 0 < 2 ^ p - 1 := by
      rw [Nat.sub_pos_iff_lt]
      exact Nat.one_lt_two_pow (by omega)
    obtain ⟨k, hk⟩ := dvd_def.mp hfact
    have hc := jsp87LambertQ_succ N
    have hdiv : ∀ (a : ℕ), (a * ((2 ^ p - 1) * k)) / (2 ^ p - 1) = a * k := by
      intro a
      have hk2 : (2 ^ p - 1) * k = k * (2 ^ p - 1) := Nat.mul_comm _ _
      rw [hk2, ← Nat.mul_assoc, Nat.mul_div_cancel (a * k) hqpos]
    have hdiv' : ∀ (a : ℕ), a * (((2 ^ p - 1) * k) / (2 ^ p - 1)) = a * k := by
      intro a
      have hq : ((2 ^ p - 1) * k) / (2 ^ p - 1) = k := by
        rw [Nat.mul_comm (2 ^ p - 1) k, Nat.mul_div_cancel k hqpos]
      rw [hq]
    rw [hc, hk, hdiv, hdiv']
  have hsingle (hp : (N).Prime) : jsp87LambertQ (N + 1) / (2 ^ N - 1) = jsp87LambertQ N := by
    have hc := jsp87LambertQ_succ N
    have h2N : 2 ≤ N := hp.two_le
    have hqpos : 0 < 2 ^ N - 1 := by
      rw [Nat.sub_pos_iff_lt]
      exact Nat.one_lt_two_pow (by omega)
    rw [hc, if_pos hp]
    have h2 := Nat.mul_div_cancel (jsp87LambertQ N) hqpos
    rw [Nat.mul_comm (2 ^ N - 1) (jsp87LambertQ N)]
    exact h2
  have hsum' : (∑ p ∈ Finset.range N,
        (if p.Prime then jsp87LambertQ (N + 1) / (2 ^ p - 1) else 0))
      = (if (N).Prime then 2 ^ N - 1 else 1)
          * ∑ p ∈ Finset.range N, (if p.Prime then jsp87LambertQ N / (2 ^ p - 1) else 0) := by
    calc (∑ p ∈ Finset.range N, (if p.Prime then jsp87LambertQ (N + 1) / (2 ^ p - 1) else 0))
        = ∑ p ∈ Finset.range N,
            ((if p.Prime then jsp87LambertQ N / (2 ^ p - 1) else 0)
              * (if (N).Prime then 2 ^ N - 1 else 1)) := by
              refine Finset.sum_congr rfl fun p hp' => ?_
              by_cases hpp : p.Prime
              · rw [if_pos hpp, if_pos hpp, hkey p (Finset.mem_range.mp hp') hpp]
                ring
              · rw [if_neg hpp, if_neg hpp]
                ring
      _ = (∑ p ∈ Finset.range N, (if p.Prime then jsp87LambertQ N / (2 ^ p - 1) else 0))
          * (if (N).Prime then 2 ^ N - 1 else 1) := by
            rw [← Finset.sum_mul]
      _ = (if (N).Prime then 2 ^ N - 1 else 1)
          * ∑ p ∈ Finset.range N, (if p.Prime then jsp87LambertQ N / (2 ^ p - 1) else 0) := by
          rw [Nat.mul_comm]
  have hlhs : jsp87_lambertNumer (N + 1)
      = (if (N).Prime then jsp87LambertQ (N + 1) / (2 ^ N - 1) else 0)
        + ∑ p ∈ Finset.range N,
          (if p.Prime then jsp87LambertQ (N + 1) / (2 ^ p - 1) else 0) := by
    unfold jsp87_lambertNumer
    rw [Finset.range_add_one, Finset.sum_insert (by simp [Finset.mem_range]),
      ← Finset.range_add_one]
    rfl
  have hexpl : (∑ p ∈ Finset.range N, (if p.Prime then jsp87LambertQ N / (2 ^ p - 1) else 0))
      = jsp87_lambertNumer N := rfl
  rw [hlhs, hsum', ← hexpl]
  by_cases hp : (N).Prime
  · rw [if_pos hp, if_pos hp, hsingle hp, if_pos hp]
    ring
  · rw [if_neg hp, if_neg hp, if_neg hp]
    ring

/-- **A NEW LAMBERT DENOMINATOR IS COPRIME TO THE OLD ONES.**  For a prime `N`,
`2^N - 1` is coprime to `D_N`. -/
theorem coprime_new_lambert_den (N : ℕ) (hp : (N).Prime) :
    Nat.Coprime (2 ^ N - 1) (jsp87LambertQ N) := by
  unfold jsp87LambertQ
  have key : ∀ q ∈ Finset.range N,
      Nat.Coprime (2 ^ N - 1) (if q.Prime then 2 ^ q - 1 else 1) := by
    intro q hq
    have hq' : q < N := Finset.mem_range.mp hq
    by_cases hqp : q.Prime
    · rw [if_pos hqp]
      exact coprime_lambert_den_of_distinct_prime hp hqp (by omega)
    · rw [if_neg hqp]
      exact Nat.coprime_one_right _
  exact Nat.Coprime.prod_right key

/-- **NOTHING CANCELS IN THE TRUNCATION.**  The numerator of `T N` over the
clearing denominator `D_N` is coprime to `D_N`, so `D_N` is the *exact* reduced
denominator of `T N`.

Rounds 39 and 40 proved that the *factors* `2^p - 1` are mutually coprime and that
`D_N · T N ∈ ℤ`, but neither showed that `gcd (numer N, D_N) = 1`. -/
theorem jsp87_lambertNumer_coprime_den (N : ℕ) :
    Nat.Coprime (jsp87_lambertNumer N) (jsp87LambertQ N) := by
  induction N with
  | zero =>
    rw [show jsp87_lambertNumer 0 = 0 by simp [jsp87_lambertNumer]]
    exact Nat.coprime_one_right _
  | succ N ih =>
    by_cases hp : (N).Prime
    · have hnum' : jsp87_lambertNumer (N + 1)
          = (2 ^ N - 1) * jsp87_lambertNumer N + jsp87LambertQ N := by
        rw [jsp87_lambertNumer_succ, if_pos hp, if_pos hp]
      have hden' : jsp87LambertQ (N + 1) = (2 ^ N - 1) * jsp87LambertQ N := by
        rw [jsp87LambertQ_succ, if_pos hp]
      rw [hnum', hden']
      have hA : Nat.Coprime (jsp87_lambertNumer N) (jsp87LambertQ N) := ih
      have hB : Nat.Coprime (2 ^ N - 1) (jsp87LambertQ N) := coprime_new_lambert_den N hp
      have h1 : Nat.Coprime (2 ^ N - 1)
          ((2 ^ N - 1) * jsp87_lambertNumer N + jsp87LambertQ N) := by
        rw [Nat.mul_comm (2 ^ N - 1) (jsp87_lambertNumer N)]
        exact (show Nat.Coprime (jsp87_lambertNumer N * (2 ^ N - 1) + jsp87LambertQ N)
          (2 ^ N - 1) by rw [Nat.coprime_mul_right_add_left]; exact hB.symm).symm
      have h2 : Nat.Coprime ((2 ^ N - 1) * jsp87_lambertNumer N + jsp87LambertQ N)
          (jsp87LambertQ N) := by
        rw [Nat.coprime_add_self_left]
        exact Nat.Coprime.mul_left hB hA
      exact (h1.mul_left h2.symm).symm
    · have hnum' : jsp87_lambertNumer (N + 1) = jsp87_lambertNumer N := by
        rw [jsp87_lambertNumer_succ, if_neg hp, if_neg hp]
        ring
      have hden' : jsp87LambertQ (N + 1) = jsp87LambertQ N := by
        rw [jsp87LambertQ_succ, if_neg hp]
        ring
      rw [hnum', hden']
      exact ih

/-! ## 3. The join: the normalised Lambert truncation -/

/-- **THE NORMALISED TRUNCATION.**  `jsp87NormLambert N = 2^{N-1} · T N - I N`:
the Lambert truncation rescaled so that its denominator is exactly `D_N` and its
numerator an integer. -/
noncomputable def jsp87NormLambert (N : ℕ) : ℝ :=
  ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTrunc N - (jsp87IntPart N : ℝ)

/-- **THE JOIN.**  The normalised Lambert truncation is the Erdős carry minus the
rescaled Lambert tail:

```
jsp87NormLambert N  =  θ N  -  2^{N-1} · R N ,
```

equivalently `2^{N-1} · T N = I N + θ N - 2^{N-1} R N`.  The integer prefix `I N`
is the common part, and the two halves of the Erdős–Pratt argument — the carry of
the binary expansion (Erdős side) and the tail of the Lambert series (Lambert
side) — are the two summands of the remainder.  No previous file compared them. -/
theorem jsp87_normLambert_eq_carry (N : ℕ) (hN : 1 ≤ N) :
    jsp87NormLambert N
      = ((2 : ℝ) ^ N) * jsp87Tail N - ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N := by
  have hdec := jsp87_lambert_decomp N
  have h2S := jsp87_lambertAll_eq
  have hscaled := jsp87_scaled_decomposition N hN
  have hP : ((2 : ℕ) ^ (N - 1) : ℝ) = (2 : ℝ) ^ (N - 1) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Nat.cast_pow 2 (N - 1))
  have hP2' : (2 : ℝ) ^ (N - 1) * 2 = (2 : ℝ) ^ N := by
    calc (2 : ℝ) ^ (N - 1) * 2 = 2 ^ ((N - 1) + 1) := by
          symm
          exact pow_succ (2 : ℝ) (N - 1)
      _ = 2 ^ N := by congr 1; omega
  have hP2 : ((2 : ℕ) ^ (N - 1) : ℝ) * 2 = (2 : ℝ) ^ N := by
    rw [hP]
    exact hP2'
  have hT : jsp87_lambertTrunc N = 2 * jsp87Series - jsp87_lambertTail N := by
    linarith [hdec, h2S]
  rw [jsp87NormLambert, hT]
  calc ((2 : ℕ) ^ (N - 1) : ℝ) * (2 * jsp87Series - jsp87_lambertTail N)
        - (jsp87IntPart N : ℝ)
      = (2 : ℝ) ^ (N - 1) * (2 * jsp87Series - jsp87_lambertTail N)
        - (jsp87IntPart N : ℝ) := by rw [hP]
    _ = ((2 : ℝ) ^ (N - 1) * 2) * jsp87Series
          - ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N
        - (jsp87IntPart N : ℝ) := by ring
    _ = ((2 : ℝ) ^ N) * jsp87Series - ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N
        - (jsp87IntPart N : ℝ) := by rw [hP2']
    _ = ((2 : ℝ) ^ N) * jsp87Tail N
        - ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N := by rw [hscaled]; ring

/-- **`D_N` clears the normalised truncation into an integer.** -/
theorem jsp87_normLambert_mul_int (N : ℕ) :
    ∃ m : ℤ, (jsp87LambertQ N : ℝ) * jsp87NormLambert N = (m : ℝ) := by
  have hnum := jsp87_lambertTrunc_mul_num N
  have h1 : jsp87_lambertTrunc N * (jsp87LambertQ N : ℝ)
      = ((jsp87_lambertNumer N : ℕ) : ℝ) := by
    simpa [jsp87LambertQ] using hnum
  refine ⟨((jsp87_lambertNumer N : ℕ) : ℤ) * ((2 : ℕ) ^ (N - 1) : ℤ)
      - ((jsp87LambertQ N : ℕ) : ℤ) * jsp87IntPart N, ?_⟩
  rw [jsp87NormLambert]
  push_cast
  linear_combination ((2 : ℕ) ^ (N - 1) : ℝ) * h1

/-- An equality `X = D · z` with `X, D ∈ ℕ`, `0 < D`, and `z` an integer
cast, is a divisibility statement. -/
private lemma dvd_of_natCast_eq' {D X : ℕ} {z : ℝ} (h : (X : ℝ) = (D : ℝ) * z)
    (hz : ∃ k : ℤ, (k : ℝ) = z) : D ∣ X := by
  obtain ⟨k, hk⟩ := hz
  have hzR : ((X : ℤ) : ℝ) = ((D : ℤ) * k : ℝ) := by
    calc ((X : ℤ) : ℝ) = (X : ℝ) := by exact_mod_cast rfl
      _ = (D : ℝ) * z := h
      _ = (D : ℝ) * (k : ℝ) := by rw [← hk]
      _ = ((D : ℤ) * k : ℝ) := by simp only [Int.cast_natCast]
  have hz : (X : ℤ) = (D : ℤ) * k := by
    refine Int.cast_injective (α := ℝ) ?_
    rw [Int.cast_mul]
    exact hzR
  have hdvdZ : (((D : ℤ) * k) ∣ ((X : ℤ))) := dvd_of_eq hz.symm
  have hD : (((D : ℕ) : ℤ) ∣ ((X : ℕ) : ℤ)) := dvd_trans (dvd_mul_right _ _) hdvdZ
  rw [← Int.natCast_dvd_natCast]
  exact hD

/-- The product form of the previous lemma. -/
private lemma dvd_of_natCast_eq {D X : ℕ} {k : ℤ} (h : (X : ℝ) = (D : ℝ) * (k : ℝ)) :
    D ∣ X :=
  dvd_of_natCast_eq' h ⟨k, rfl⟩

/-- **THE EXACT DENOMINATOR OF THE JOIN.**  For every cut point `N ≥ 1` and every
`0 < c < D_N`, the number `c · jsp87NormLambert N` is *not* an integer: the
normalised truncation has reduced denominator exactly `D_N`. -/
theorem jsp87_normLambert_den_exact (N : ℕ) {c : ℕ}
    (hc : 0 < c) (hlt : c < jsp87LambertQ N) :
    ¬ ∃ m : ℤ, (c : ℝ) * jsp87NormLambert N = (m : ℝ) := by
  rintro ⟨m, hm⟩
  have hsplit : (c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTrunc N
      = (m : ℝ) + (c : ℝ) * (jsp87IntPart N : ℝ) := by
    rw [jsp87NormLambert] at hm
    linarith
  have hnum := jsp87_lambertTrunc_mul_num N
  have h1 : jsp87_lambertTrunc N * (jsp87LambertQ N : ℝ)
      = ((jsp87_lambertNumer N : ℕ) : ℝ) := by
    simpa [jsp87LambertQ] using hnum
  have hmul : ((c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertNumer N)
      = (jsp87LambertQ N : ℝ) * ((m : ℝ) + (c : ℝ) * (jsp87IntPart N : ℝ)) := by
    calc (c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertNumer N
        = (c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ)
            * (jsp87_lambertTrunc N * (jsp87LambertQ N : ℝ)) := by rw [← h1]
      _ = (jsp87LambertQ N : ℝ)
          * ((c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTrunc N) := by ring
      _ = (jsp87LambertQ N : ℝ) * ((m : ℝ) + (c : ℝ) * (jsp87IntPart N : ℝ)) := by
        rw [hsplit]
  obtain ⟨K, hK⟩ : ∃ K : ℤ, (K : ℝ) = (m : ℝ) + (c : ℝ) * (jsp87IntPart N : ℝ) := by
    refine ⟨(m : ℤ) + (c : ℤ) * jsp87IntPart N, ?_⟩
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hZ : ((c * 2 ^ (N - 1) * jsp87_lambertNumer N : ℕ) : ℝ)
      = (jsp87LambertQ N : ℝ) * (K : ℝ) := by
    rw [hK]
    simpa only [Nat.cast_mul, Nat.cast_pow] using hmul
  have hdiv : jsp87LambertQ N ∣ c * 2 ^ (N - 1) * jsp87_lambertNumer N :=
    dvd_of_natCast_eq (k := K) hZ
  have hcopA : Nat.Coprime (jsp87_lambertNumer N) (jsp87LambertQ N) :=
    jsp87_lambertNumer_coprime_den N
  have hcopB : Nat.Coprime (2 ^ (N - 1)) (jsp87LambertQ N) :=
    coprime_two_pow_lambertQ (k := N - 1)
  have hcop : Nat.Coprime (jsp87_lambertNumer N * 2 ^ (N - 1)) (jsp87LambertQ N) :=
    (Nat.Coprime.mul_right (k := jsp87LambertQ N) (m := jsp87_lambertNumer N)
      (n := 2 ^ (N - 1)) hcopA.symm hcopB.symm).symm
  have hdiv' : jsp87LambertQ N ∣ c :=
    (Nat.Coprime.dvd_mul_right (k := jsp87LambertQ N) (m := c)
      (n := jsp87_lambertNumer N * 2 ^ (N - 1)) hcop.symm).mp
      (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdiv)
  have hge : jsp87LambertQ N ≤ c := Nat.le_of_dvd hc hdiv'
  omega

/-! ## 4. What a rational value of `S` would force -/

/-- **THE DENOMINATOR SPLIT.**  Assume `2 · S = a / b` with `b > 0`, and let
`2^{N-1} · R N = m / c` with `c > 0`.  Then

```
D_N  ∣  c · b ,
```

i.e. *the denominator of the rescaled Lambert tail, multiplied by the
hypothetical denominator of the series, is a multiple of the whole product of
Lambert denominators below `N`*.  Nothing below `N` cancels.

This is the exact-denominator form of `jsp87_lambert_rat_obstruction`: that
theorem says `b · D_N · R N` is a positive integer; this one says the *reduced*
denominator of the rescaled tail still contains every Lambert denominator below
`N`, up to the factors shared with `b`. -/
theorem jsp87_rational_imp_lambertTail_den {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) {N : ℕ} (hN : 1 ≤ N)
    {m : ℤ} {c : ℕ} (hc : 0 < c)
    (ht : ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N = (m : ℝ) / (c : ℝ)) :
    jsp87LambertQ N ∣ c * b := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    exact this.ne'
  have hc0 : (c : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    exact this.ne'
  have hSc : jsp87Series = ((a : ℤ) : ℝ) / ((2 * b : ℕ) : ℤ) := by
    have h2 : (2 : ℝ) * jsp87Series = (a : ℝ) / (b : ℝ) := by linarith [h]
    have h3 : (b : ℝ) * ((2 : ℝ) * jsp87Series) = (a : ℝ) := by
      rw [h2]
      field_simp
    push_cast
    field_simp
    linear_combination h3
  have hb' : 0 < ((2 * b : ℕ) : ℤ) := by
    have : (0 : ℕ) < 2 * b := Nat.mul_pos (by norm_num) hb
    exact_mod_cast this
  obtain ⟨c₀, hc₀⟩ := jsp87_carry_mul_eq_int hN hb' hSc
  have hcarry : ((2 : ℝ) ^ N) * jsp87Tail N = (c₀ : ℝ) / ((2 * b : ℕ) : ℝ) := by
    have hz : (((2 * b : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((2 * b : ℕ) : ℝ) := by exact_mod_cast hb'
      exact this.ne'
    field_simp
    exact hc₀
  have ht' : (c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N = (m : ℝ) := by
    have h1 : ((c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ)) * jsp87_lambertTail N
        = (c : ℝ) * (((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N) := by ring
    rw [h1, ht]
    field_simp
  have hjoin := jsp87_normLambert_eq_carry N hN
  have key1 : (b : ℝ) * (((2 : ℝ) ^ N) * jsp87Tail N) = (c₀ : ℝ) / 2 := by
    rw [hcarry]
    push_cast
    field_simp
  have key2 : (c : ℝ) * (((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N) = (m : ℝ) := by
    calc (c : ℝ) * (((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N)
        = (c : ℝ) * ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N := by ring
      _ = (m : ℝ) := ht'
  have hkey : (c : ℝ) * (b : ℝ) * jsp87NormLambert N
      = (c : ℝ) * ((c₀ : ℝ) / 2) - (m : ℝ) * (b : ℝ) := by
    rw [hjoin]
    calc (c : ℝ) * (b : ℝ) * (((2 : ℝ) ^ N) * jsp87Tail N
            - ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N)
        = (c : ℝ) * ((b : ℝ) * (((2 : ℝ) ^ N) * jsp87Tail N))
            - (c : ℝ) * (((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N) * (b : ℝ) := by ring
      _ = (c : ℝ) * ((c₀ : ℝ) / 2) - (m : ℝ) * (b : ℝ) := by rw [key1, key2]
      _ = _ := by ring
  have hnum := jsp87_lambertTrunc_mul_num N
  have hZ : ((2 * (c * b * 2 ^ (N - 1) * jsp87_lambertNumer N : ℕ) : ℕ) : ℝ)
      = (jsp87LambertQ N : ℝ) * ((2 : ℝ) * ((c : ℝ) * (b : ℝ) * jsp87NormLambert N
          + (c : ℝ) * (b : ℝ) * (jsp87IntPart N : ℝ))) := by
    have h1 : jsp87_lambertTrunc N * (jsp87LambertQ N : ℝ)
        = ((jsp87_lambertNumer N : ℕ) : ℝ) := by
      simpa [jsp87LambertQ] using hnum
    have hnorm : (2 : ℝ) ^ (N - 1) * ((jsp87_lambertNumer N : ℕ) : ℝ)
        = (jsp87LambertQ N : ℝ) * jsp87NormLambert N
          + (jsp87LambertQ N : ℝ) * (jsp87IntPart N : ℝ) := by
      rw [jsp87NormLambert, ← h1]
      ring
    calc ((2 * (c * b * 2 ^ (N - 1) * jsp87_lambertNumer N : ℕ) : ℕ) : ℝ)
        = 2 * ((c : ℝ) * (b : ℝ) * ((2 : ℝ) ^ (N - 1))
            * ((jsp87_lambertNumer N : ℕ) : ℝ)) := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ = _ := by linear_combination (2 : ℝ) * (c : ℝ) * (b : ℝ) * hnorm
  obtain ⟨K, hK⟩ : ∃ K : ℤ, (K : ℝ) = (2 : ℝ) * ((c : ℝ) * (b : ℝ) * jsp87NormLambert N
      + (c : ℝ) * (b : ℝ) * (jsp87IntPart N : ℝ)) := by
    refine ⟨c₀ * c - 2 * m * b + 2 * ((c : ℤ) * b) * jsp87IntPart N, ?_⟩
    calc ((c₀ * c - 2 * m * b + 2 * ((c : ℤ) * b) * jsp87IntPart N : ℤ) : ℝ)
        = 2 * ((c : ℝ) * ((c₀ : ℝ) / 2) - (m : ℝ) * (b : ℝ)
            + (c : ℝ) * (b : ℝ) * (jsp87IntPart N : ℝ)) := by
          push_cast
          ring
      _ = 2 * ((c : ℝ) * (b : ℝ) * jsp87NormLambert N
            + (c : ℝ) * (b : ℝ) * (jsp87IntPart N : ℝ)) := by
          have hkey' : (c : ℝ) * (b : ℝ) * jsp87NormLambert N
              = (c : ℝ) * ((c₀ : ℝ) / 2) - (m : ℝ) * (b : ℝ) := hkey
          rw [hkey']
  have hZ' : ((2 * (c * b * 2 ^ (N - 1) * jsp87_lambertNumer N : ℕ) : ℕ) : ℝ)
      = (jsp87LambertQ N : ℝ) * (K : ℝ) := by
    rw [hK]
    simpa only [Nat.cast_mul, Nat.cast_pow] using hZ
  have hdiv : jsp87LambertQ N ∣ 2 * (c * b * 2 ^ (N - 1) * jsp87_lambertNumer N) :=
    dvd_of_natCast_eq (k := K) hZ'
  have hcopA : Nat.Coprime (jsp87_lambertNumer N) (jsp87LambertQ N) :=
    jsp87_lambertNumer_coprime_den N
  have hcopB : Nat.Coprime (2 ^ (N - 1)) (jsp87LambertQ N) :=
    coprime_two_pow_lambertQ (k := N - 1)
  have hcopC : Nat.Coprime 2 (jsp87LambertQ N) :=
    Nat.coprime_two_left.mpr (jsp87LambertQ_odd N)
  have hcop : Nat.Coprime (jsp87LambertQ N)
      (2 * (2 ^ (N - 1) * jsp87_lambertNumer N)) :=
    Nat.Coprime.mul_right (k := jsp87LambertQ N) (m := 2) (n := 2 ^ (N - 1)
        * jsp87_lambertNumer N) hcopC.symm
      (Nat.Coprime.mul_right (k := jsp87LambertQ N) (m := 2 ^ (N - 1))
        (n := jsp87_lambertNumer N) hcopB.symm hcopA.symm)
  exact (Nat.Coprime.dvd_mul_right (k := jsp87LambertQ N) (m := c * b) (n := 2
      * (2 ^ (N - 1) * jsp87_lambertNumer N)) hcop).mp
    (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdiv)

/-! ## 5. The exact consequence: the tail keeps demanding new denominators -/

/-- **EVERY LAMBERT DENOMINATOR BELOW THE CUT POINT DIVIDES `c · b`.**  Under a
rationality assumption the clearing denominators of the whole truncation are
absorbed by the single integer `c · b`. -/
theorem jsp87_rational_imp_den_dvd_mer {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) {p N : ℕ} (hp : p.Prime) (hps : p < N)
    {m : ℤ} {c : ℕ} (hc : 0 < c)
    (ht : ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N = (m : ℝ) / (c : ℝ)) :
    2 ^ p - 1 ∣ c * b := by
  have hdiv := jsp87_rational_imp_lambertTail_den hb h hN1 hc ht
  exact (dvd_trans (lambertDen_mem_factor hp (Finset.mem_range.mpr hps)) hdiv)
where
  hN1 : 1 ≤ N := by omega

/-- **THE DENOMINATORS KEEP ACQUIRING PRIME FACTORS PAST `p`.**  Under a
rationality assumption, every prime factor of `2^p - 1` divides `c · b`, and by
`Diophantine.primeFactors_sub_one_gt` every such prime *exceeds* `p`.  This is
the Erdős step of the argument, in exact-denominator form. -/
theorem jsp87_rational_imp_den_prime_gt {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) {p N : ℕ} (hp : p.Prime) (hps : p < N)
    {m : ℤ} {c : ℕ} (hc : 0 < c)
    (ht : ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N = (m : ℝ) / (c : ℝ))
    {q : ℕ} (hq : q ∈ (2 ^ p - 1).primeFactors) : q.Prime ∧ q ∣ c * b ∧ p < q := by
  obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp hq
  have hdvd := jsp87_rational_imp_den_dvd_mer hb h hp hps hc ht
  exact ⟨hqp, dvd_trans hqd hdvd, primeFactors_sub_one_gt hp q hq⟩

/-- **THE ESCAPE: past some cut point no denominator `≤ K` can occur.**  For every
`K` there is `M` such that for all `N ≥ M` the rescaled Lambert tail
`2^{N-1} · R N` is *not* a rational with denominator at most `K`.

Together with `jsp87_rational_imp_den_prime_gt` this says that a hypothetical
rational value of `S` forces the denominators of its own Lambert tails to escape
every finite set — the sharpest unconditional form of the Erdős–Pratt denominator
obstruction available in this tree. -/
theorem jsp87_rational_imp_lambertTail_den_escape {a b : ℕ} (hb : 0 < b)
    (h : 2 * jsp87Series = (a : ℝ) / (b : ℝ)) (K : ℕ) :
    ∃ M, ∀ N ≥ M, ¬ ∃ (m : ℤ) (c : ℕ), 0 < c ∧ c ≤ K
      ∧ ((2 : ℕ) ^ (N - 1) : ℝ) * jsp87_lambertTail N = (m : ℝ) / (c : ℝ) := by
  obtain ⟨N', hN'⟩ := jsp87LambertQ_unbounded (K * b)
  refine ⟨N' + 1, fun N hN => ?_⟩
  rintro ⟨m, c, hc, hck, ht⟩
  have hN1 : 1 ≤ N := by omega
  have hdiv := jsp87_rational_imp_lambertTail_den hb h hN1 hc ht
  have hle1 : jsp87LambertQ N ≤ c * b := Nat.le_of_dvd (Nat.mul_pos hc hb) hdiv
  have hle3 : c * b ≤ K * b := Nat.mul_le_mul_right b hck
  have hle2 : K * b < jsp87LambertQ N' := hN'
  have hNM : N' ≤ N := by omega
  have hdvd'' : jsp87LambertQ N' ∣ jsp87LambertQ N := jsp87LambertQ_dvd (h := hNM)
  have hle : jsp87LambertQ N' ≤ jsp87LambertQ N :=
    Nat.le_of_dvd (jsp87LambertQ_pos N) hdvd''
  omega

/-! ## 6. Machine-checked instances of the chain -/

/-- `D_3 = 2^2 - 1 = 3`. -/
theorem jsp87LambertQ_three : jsp87LambertQ 3 = 3 := by decide

/-- `D_4 = (2^2-1)(2^3-1) = 21`. -/
theorem jsp87LambertQ_four : jsp87LambertQ 4 = 21 := by decide

/-- `D_6 = (2^2-1)(2^3-1)(2^5-1) = 651`. -/
theorem jsp87LambertQ_six : jsp87LambertQ 6 = 651 := by decide

end JSP87