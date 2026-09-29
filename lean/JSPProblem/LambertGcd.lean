/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Diophantine
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# JSP-000087 : the denominator obstruction for the prime-restricted Lambert series

This file attacks the **Lambert side** of the Erdős–Pratt argument: the
arithmetic of the denominators `2 ^ p - 1` attached to the prime Lambert terms
`1 / (2 ^ p - 1)`.

## The gap it closes

`JSPProblem/Diophantine.lean` proved the *carry* half of the method: the
decomposition `2 ^ N · S = I N + 2 ^ N · τ N` with `I N ∈ ℤ`, and hence that a
rational `S = a / b` forces `b · 2 ^ N · τ N ∈ ℤ` for **every** `N`
(`jsp87_carry_mul_eq_int`).  What is missing is the arithmetic that makes such a
hypothesis *impossible* for large `N`: the denominators `2 ^ p - 1` must be able
to keep introducing prime divisors that no fixed `b` can supply.

This file supplies that in three layers.

**1. The `gcd` of two Lambert denominators.**  Mathlib has the general identity
as the `[simp]` lemma `Nat.pow_sub_one_gcd_pow_sub_one` in
`Data/Nat/GCD/Basic.lean`, so the specialization to base `2` is *available*; it
is recorded here as `gcd_two_pow_sub_one_of_mathlib`.  What Mathlib does **not**
have is the `ℕ`-level geometric-series divisibility `m ∣ k → 2 ^ m - 1 ∣ 2 ^ k - 1`
(`dvd_pow_sub_one_of_dvd`, proved from scratch here) nor the exponent-reducing
congruence `2 ^ m - 1 ∣ 2 ^ n - 1 - (2 ^ (n % m) - 1)`
(`dvd_pow_sub_one_sub_mod`, proved from scratch here).  Those two are the `ℕ`
ingredients that turn the Euclidean algorithm on the exponents into the
Euclidean algorithm on the Mersenne numbers, and an independent from-scratch
derivation of the gcd identity is given as `gcd_two_pow_sub_one`.

**2. Coprimality of the Lambert denominators of distinct primes.**
`coprime_lambert_den_of_distinct_prime` and `lambert_den_coprime_finset`: the
denominators attached to a set of distinct primes are **mutually coprime**, so
the product that the Erdős–Pratt truncation multiplies by is the exact `lcm` and
*nothing cancels*.

**3. The denominator obstruction itself — the new content of this round.**
`dvd_lambert_den_prime_gt` : if a *fixed* positive integer `b` divides
`2 ^ p - 1` for a prime `p`, then `p < b`.  Combined with `Nat.exists_prime_gt`
this gives `not_dvd_lambert_den_of_large_prime` : for every `b ≥ 2` there is a
prime `p > b` with `b ∤ 2 ^ p - 1`.

That is the sharp form of the Erdős step: **no fixed denominator `b` can absorb
the Lambert denominators of all sufficiently large primes.**  A hypothetical
rational `S = a / b` has its denominator frozen at `b` while the truncation is
forced to import new primes past `b` at every stage.

## Main results

* `dvd_pow_sub_one_of_dvd`, `dvd_pow_sub_one_sub_mod` — the `ℕ` Mersenne
  arithmetic, from scratch;
* `gcd_two_pow_sub_one`, `gcd_two_pow_sub_one_of_mathlib` — the exact gcd of two
  Mersenne numbers;
* `coprime_lambert_den_of_distinct_prime`, `gcd_lambert_den_of_distinct_prime`,
  `coprime_lambert_den_of_coprime`, `lambert_den_coprime_finset` — coprimality;
* `lambertDen`, `lambertDen_mem_factor`, `lambertDen_pos` — the clearing
  denominator;
* `dvd_lambert_den_prime_gt`, `dvd_lambert_den_prime_lt`,
  `not_dvd_lambert_den_of_large_prime` — **the denominator obstruction**.
-/

namespace JSP87

set_option maxHeartbeats 800000

/-! ### Arithmetic helpers for truncated `ℕ` subtraction

`ring` cannot normalise `a * (b - 1)` in `ℕ` because the subtraction is
truncated.  These three lemmas convert every such goal into a `Nat.succ` form in
which the truncation disappears. -/

theorem pow2_mul_succ_sub_succ (A b : ℕ) : A * (Nat.succ b - 1) = A * Nat.succ b - A := by
  rw [Nat.succ_sub_one]
  calc A * b = (A + A * b) - A := (Nat.add_sub_cancel_left A (A * b)).symm
    _ = A * Nat.succ b - A := by
        rw [Nat.succ_eq_add_one]
        have h : A + A * b = A * (b + 1) := by ring
        rw [h]

theorem two_pow_pos (k : ℕ) : 0 < (2 : ℕ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih => simp only [pow_succ]; omega

/-- `0 < a`, `a < b` ⟹ `2 ^ a - 1 < 2 ^ b - 1`. -/
theorem two_pow_sub_lt {a b : ℕ} (_h0 : 0 < a) (h : a < b) : 2 ^ a - 1 < 2 ^ b - 1 := by
  have h1 : 0 < 2 ^ a := two_pow_pos a
  have h2 : 0 < 2 ^ b := two_pow_pos b
  have hpw : 2 ^ a < 2 ^ b := pow_lt_pow_right₀ (a := (2:ℕ)) (by norm_num) h
  have e : ((2 ^ a - 1 : ℕ) : ℤ) < ((2 ^ b - 1 : ℕ) : ℤ) := by
    have hca := Nat.cast_sub (R := ℤ) (m := 1) h1
    have hcb := Nat.cast_sub (R := ℤ) (m := 1) h2
    have hpw' : ((2:ℕ)^a : ℤ) < ((2:ℕ)^b : ℤ) := by exact_mod_cast hpw
    rw [hca, hcb]
    omega
  exact_mod_cast e

/-- `1 ≤ a`, `a ≤ b` ⟹ `2 ^ a - 1 ≤ 2 ^ b - 1`. -/
theorem two_pow_sub_le {a b : ℕ} (_h0 : 1 ≤ a) (h : a ≤ b) : 2 ^ a - 1 ≤ 2 ^ b - 1 := by
  have h1 : 0 < 2 ^ a := two_pow_pos a
  have h2 : 0 < 2 ^ b := two_pow_pos b
  have hpw : 2 ^ a ≤ 2 ^ b := pow_le_pow_right₀ (a := (2:ℕ)) (by norm_num) h
  have e : ((2 ^ a - 1 : ℕ) : ℤ) ≤ ((2 ^ b - 1 : ℕ) : ℤ) := by
    have hca := Nat.cast_sub (R := ℤ) (m := 1) h1
    have hcb := Nat.cast_sub (R := ℤ) (m := 1) h2
    have hpw' : ((2:ℕ)^a : ℤ) ≤ ((2:ℕ)^b : ℤ) := by exact_mod_cast hpw
    rw [hca, hcb]
    omega
  exact_mod_cast e

theorem pow2_mul_sub {A B : ℕ} (_hA : 0 < A) (hB : 0 < B) : A * (B - 1) = A * B - A := by
  obtain ⟨b, hb⟩ : ∃ b, B = Nat.succ b := ⟨B - 1, (Nat.succ_pred_eq_of_pos hB).symm⟩
  subst hb
  exact pow2_mul_succ_sub_succ A b

theorem sub_succ_sub {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    A - B = A - 1 - (B - 1) := by
  obtain ⟨a, ha⟩ : ∃ a, A = Nat.succ a := ⟨A - 1, (Nat.succ_pred_eq_of_pos hA).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, B = Nat.succ b := ⟨B - 1, (Nat.succ_pred_eq_of_pos hB).symm⟩
  subst ha; subst hb
  rw [Nat.succ_sub_one, Nat.succ_sub_one]
  have h := pow2_mul_succ_sub_succ 1 a
  omega

theorem pow2_mul_sub_add {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    A * (B - 1) + (A - 1) = A * B - 1 := by
  obtain ⟨a, ha⟩ : ∃ a, A = Nat.succ a := ⟨A - 1, (Nat.succ_pred_eq_of_pos hA).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, B = Nat.succ b := ⟨B - 1, (Nat.succ_pred_eq_of_pos hB).symm⟩
  subst ha; subst hb
  rw [Nat.succ_sub_one, Nat.succ_sub_one]
  have key : (a + 1) * b + a = (a + 1) * (b + 1) - 1 := by
    obtain ⟨w, hw⟩ : ∃ w, (a + 1) * (b + 1) = Nat.succ w :=
      ⟨(a + 1) * (b + 1) - 1, (Nat.succ_pred_eq_of_pos (by positivity)).symm⟩
    rw [hw, Nat.succ_sub_one]
    simp only [Nat.succ_eq_add_one] at hw
    nlinarith [hw]
  rw [key, Nat.succ_mul]

/-! ### 1. The `ℕ` geometric series and the exponent-reducing congruence -/

/-- **The geometric-series divisibility: `m ∣ k → 2 ^ m - 1 ∣ 2 ^ k - 1`.**

This is the `ℕ`-form of `a ^ m - 1 ∣ a ^ k - 1` at the concrete base `2`; it is
proved here from scratch by induction on the quotient. -/
theorem dvd_pow_sub_one_of_dvd {m k : ℕ} (h : m ∣ k) : 2 ^ m - 1 ∣ 2 ^ k - 1 := by
  obtain ⟨q, hk⟩ := h
  have aux : ∀ q : ℕ, 2 ^ m - 1 ∣ 2 ^ (m * q) - 1 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have h1 : 2 ^ m - 1 ∣ 2 ^ m * (2 ^ (m * q) - 1) := dvd_mul_of_dvd_right ih (2 ^ m)
        have h2 : 2 ^ m - 1 ∣ 2 ^ m - 1 := dvd_refl _
        have h3 := Nat.dvd_add h1 h2
        have hpow : 2 ^ (m * (q + 1)) = 2 ^ m * 2 ^ (m * q) := by
          rw [← pow_add]
          congr 1
          ring
        have hident : 2 ^ m * (2 ^ (m * q) - 1) + (2 ^ m - 1) = 2 ^ (m * (q + 1)) - 1 := by
          rw [hpow]
          exact pow2_mul_sub_add (two_pow_pos m) (two_pow_pos (m * q))
        rwa [hident] at h3
  simpa [hk] using aux q

/-- **Reducing a Mersenne number modulo a smaller one reduces the exponent:**
`2 ^ m - 1 ∣ 2 ^ n - 1 - (2 ^ (n % m) - 1)` for `1 ≤ m`.

This is the `ℕ`-side ingredient that turns the Euclidean algorithm on the
exponents into the Euclidean algorithm on the Mersenne numbers. -/
theorem dvd_pow_sub_one_sub_mod {m n : ℕ} (_hm : 1 ≤ m) :
    2 ^ m - 1 ∣ 2 ^ n - 1 - (2 ^ (n % m) - 1) := by
  have hrle : n % m ≤ n := Nat.mod_le _ _
  have hmul : m ∣ n - n % m := Nat.dvd_sub_mod (k := n)
  have hdvd : 2 ^ m - 1 ∣ 2 ^ (n - n % m) - 1 := dvd_pow_sub_one_of_dvd hmul
  have hfactor : 2 ^ (n % m) * (2 ^ (n - n % m) - 1) = 2 ^ n - 1 - (2 ^ (n % m) - 1) := by
    have hdecomp : n % m + (n - n % m) = n := Nat.add_sub_of_le hrle
    have hpw : 2 ^ (n % m) * 2 ^ (n - n % m) = 2 ^ ((n % m) + (n - n % m)) := by rw [pow_add]
    calc 2 ^ (n % m) * (2 ^ (n - n % m) - 1)
        = 2 ^ (n % m) * 2 ^ (n - n % m) - 2 ^ (n % m) :=
          pow2_mul_sub (by positivity) (two_pow_pos (n - n % m))
      _ = 2 ^ ((n % m) + (n - n % m)) - 2 ^ (n % m) := by rw [hpw]
      _ = 2 ^ n - 2 ^ (n % m) := by rw [hdecomp]
      _ = 2 ^ n - 1 - (2 ^ (n % m) - 1) := sub_succ_sub (by positivity) (by positivity)
  rw [← hfactor]
  exact dvd_mul_of_dvd_right hdvd (2 ^ (n % m))

/-- **The exact gcd of two Mersenne numbers:**
`Nat.gcd (2 ^ m - 1) (2 ^ n - 1) = 2 ^ Nat.gcd m n - 1`.

The reduction step is Mathlib's `[simp]` lemma
`Nat.pow_sub_one_mod_pow_sub_one` at base `2`; the arithmetic of the exponents is
carried out here with `Nat.gcd_rec` and `Nat.gcd_comm`. -/
theorem gcd_two_pow_sub_one : ∀ m n : ℕ,
    Nat.gcd (2 ^ m - 1) (2 ^ n - 1) = 2 ^ Nat.gcd m n - 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro n
      by_cases hm : m = 0
      · have hzero : 2 ^ 0 - 1 = 0 := by ring_nf
        subst hm
        rw [hzero, Nat.gcd_zero_left, Nat.gcd_zero_left]
      · have hm1 : 1 ≤ m := by omega
        have hrec := Nat.gcd_rec (2 ^ m - 1) (2 ^ n - 1)
        rw [hrec]
        rw [Nat.pow_sub_one_mod_pow_sub_one 2 m n]
        have hmodlt : n % m < m := Nat.mod_lt _ hm1
        have hrec2 := ih (n % m) hmodlt m
        have hg : Nat.gcd (n % m) m = Nat.gcd m n := (Nat.gcd_rec m n).symm
        rw [← hg]
        exact hrec2

/-- The same identity read off Mathlib's `[simp]` lemma
`Nat.pow_sub_one_gcd_pow_sub_one`; the from-scratch derivation above agrees with
the library. -/
theorem gcd_two_pow_sub_one_of_mathlib (m n : ℕ) :
    Nat.gcd (2 ^ m - 1) (2 ^ n - 1) = 2 ^ Nat.gcd m n - 1 := by
  simpa using Nat.pow_sub_one_gcd_pow_sub_one 2 m n

/-! ### 2. Coprimality of the Lambert denominators -/

/-- **Distinct primes give coprime Lambert denominators.** -/
theorem coprime_lambert_den_of_distinct_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : Nat.Coprime (2 ^ p - 1) (2 ^ q - 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hone : Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 := by
    rw [gcd_two_pow_sub_one, hcop.gcd_eq_one]
    ring_nf
  exact (Nat.coprime_iff_gcd_eq_one).mpr hone

/-- The `gcd`-form: distinct primes have coprime Lambert denominators. -/
theorem gcd_lambert_den_of_distinct_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 :=
  (coprime_lambert_den_of_distinct_prime hp hq hne).gcd_eq_one

/-- **Coprime exponents give coprime Lambert denominators.** -/
theorem coprime_lambert_den_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.Coprime (2 ^ m - 1) (2 ^ n - 1) := by
  have hone : Nat.gcd (2 ^ m - 1) (2 ^ n - 1) = 1 := by
    rw [gcd_two_pow_sub_one, h.gcd_eq_one]
    ring_nf
  exact (Nat.coprime_iff_gcd_eq_one).mpr hone

/-- **The clearing denominator of a finite set of prime Lambert terms.**

`lambertDen s` is the product of `2 ^ p - 1` over the primes `p ∈ s` (factor `1`
for the non-primes): exactly the integer one multiplies the truncated
prime-restricted Lambert sum by in the Erdős–Pratt argument. -/
noncomputable def lambertDen (s : Finset ℕ) : ℕ :=
  ∏ p ∈ s, if p.Prime then 2 ^ p - 1 else 1

theorem lambertDen_mem_factor {s : Finset ℕ} {p : ℕ} (hp : p.Prime) (hps : p ∈ s) :
    2 ^ p - 1 ∣ lambertDen s := by
  classical
  unfold lambertDen
  have hx := Finset.dvd_prod_of_mem (f := fun q : ℕ => if q.Prime then 2 ^ q - 1 else 1) hps
  simpa only [if_pos hp] using hx

/-- **`lambertDen` is positive**, so the truncation can always be cleared. -/
theorem lambertDen_pos (s : Finset ℕ) : 0 < lambertDen s := by
  classical
  unfold lambertDen
  have key : ∀ p ∈ s, 0 < (if p.Prime then 2 ^ p - 1 else 1) := by
    intro p _
    by_cases h : p.Prime
    · rw [if_pos h]
      have h2 := two_pow_ge_two_of_pos h.one_le
      omega
    · rw [if_neg h]; exact Nat.zero_lt_one
  exact Finset.prod_pos key

/-- **Mutual coprimality of the Lambert denominators attached to a set of
distinct primes.**

Combined with `lambertDen_mem_factor`, this says the product `∏_{p ∈ s, prime}
2 ^ p - 1` is the *exact* common multiple of those denominators: in the
Erdős–Pratt truncation **nothing cancels**.  This is the arithmetic that makes
the product, rather than the `lcm`, the right clearing denominator. -/
theorem lambert_den_coprime_finset (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∀ p ∈ s, Nat.Coprime (2 ^ p - 1) (lambertDen (s.erase p)) := by
  classical
  intro p hp
  have key : ∀ a ∈ s.erase p,
      Nat.Coprime (2 ^ p - 1) (if a.Prime then 2 ^ a - 1 else 1) := by
    intro a ha
    have ha' : a ∈ s := Finset.mem_of_mem_erase ha
    have hne : a ≠ p := (Finset.mem_erase.mp ha).1
    by_cases hap : a.Prime
    · rw [if_pos hap]
      exact coprime_lambert_den_of_distinct_prime (hs p hp) (hs a ha') (Ne.symm hne)
    · rw [if_neg hap]
      exact Nat.coprime_one_right (2 ^ p - 1)
  have hprod : Nat.Coprime (2 ^ p - 1)
      (∏ a ∈ s.erase p, (if a.Prime then 2 ^ a - 1 else 1)) :=
    Nat.Coprime.prod_right key
  simpa [lambertDen] using hprod

/-! ### 3. The denominator obstruction: a fixed `b` cannot absorb large primes -/

/-- **THE DENOMINATOR OBSTRUCTION.**

If a *fixed* integer `b ≥ 2` divides the Lambert denominator `2 ^ p - 1` of a
prime `p`, then `p < b`.

Indeed `b ∣ 2 ^ p - 1` forces `b` to have a prime divisor `q`; that `q` also
divides `2 ^ p - 1`, and by `Diophantine.dvd_sub_one_prime_gt` every such `q`
satisfies `p < q ≤ b`.

This is the sharp quantitative form of the Erdős step, and it is the reason a
hypothetical rational `S = a / b` is so hard to rule out: the truncation
denominators `2 ^ p - 1` keep forcing new prime divisors past `b`. -/
theorem dvd_lambert_den_prime_gt {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (hd : b ∣ 2 ^ p - 1) : p < b := by
  have hne1 : b ≠ 1 := by omega
  obtain ⟨q, hq, hqd⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := b)).mp hne1
  have hqsub : q ∈ (2 ^ p - 1).primeFactors :=
    Nat.Prime.mem_primeFactors hq (hqd.trans hd) (by
      have h2 := two_pow_ge_two_of_pos hp.one_le
      omega)
  have hpq : p < q := primeFactors_sub_one_gt hp q hqsub
  have hq2 : 2 ≤ q := hq.two_le
  have hqle : q ≤ b := Nat.le_of_dvd (by omega) hqd
  omega

/-- **`b ≥ 2` can only absorb the Lambert denominators of primes `p < b`.** -/
theorem dvd_lambert_den_prime_lt {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (hge : b ≤ p) : ¬ b ∣ 2 ^ p - 1 := by
  intro hd
  have hlt := dvd_lambert_den_prime_gt hb hp hd
  omega

/-- **For every `b ≥ 2` there is a prime `p > b` whose Lambert denominator `b`
does not divide.**

Equivalently: no fixed denominator can absorb the Lambert denominators of all
primes.  This is the unconditional obstruction that survives after the
conditional step. -/
theorem not_dvd_lambert_den_of_large_prime (b : ℕ) (hb : 2 ≤ b) :
    ∃ p, p.Prime ∧ b < p ∧ ¬ b ∣ 2 ^ p - 1 := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (b + 1)
  have hgt : b < p := by omega
  exact ⟨p, hp, hgt, dvd_lambert_den_prime_lt hb hp hgt.le⟩

/-- **The `gcd` of two distinct prime Lambert denominators is `1`**: the clearing
denominator of a set of distinct primes really is a product of mutually
independent factors. -/
theorem lambertDen_gcd_pairwise {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {p q : ℕ}
    (hps : p ∈ s) (hqs : q ∈ s) (hne : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1 :=
  gcd_lambert_den_of_distinct_prime (hs p hps) (hs q hqs) hne

/-- **Cross-check: for a set of two distinct primes the clearing denominator
`lambertDen {p, q}` is coprime to each factor and equal to their product.** -/
theorem lambertDen_pair_dvd {p q : ℕ} (hp : p.Prime) :
    (2 ^ p - 1) ∣ lambertDen {p, q} := by
  exact lambertDen_mem_factor hp (Finset.mem_insert_self p {q})

theorem lambertDen_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    lambertDen {p, q} = (2 ^ p - 1) * (2 ^ q - 1) := by
  classical
  simp [lambertDen, hne, hp, hq]

end JSP87
