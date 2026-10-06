/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertTrunc
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# JSP-000087 : WHICH PRIMES APPEAR IN THE LAMBERT DENOMINATORS

`JSPProblem/LambertGcd.lean` proved that the Lambert denominators attached to
*distinct* primes are mutually coprime, and `JSPProblem/LambertTrunc.lean`
proved that their product is an exact clearing denominator of the truncated
prime-restricted Lambert series.  Both statements are *internal* to the family
`2 ^ p - 1`, `p` prime: they never ask **which primes occur in the
denominators at all**.

That question has a complete and sharp answer.  Write

```
jsp87Order2 ℓ  =  the multiplicative order of 2 modulo the prime ℓ .
```

Then

* `ℓ ∣ 2 ^ k - 1  ↔  jsp87Order2 ℓ ∣ k`, and for a *prime* index `p`,
  `ℓ ∣ 2 ^ p - 1  ↔  jsp87Order2 ℓ = p`;
* hence **a prime `ℓ` divides some Lambert denominator if and only if the
  order of `2` modulo `ℓ` is prime**.  The primes `3, 5, 11, 73, …` have
  composite order and therefore **never** occur;
* there are **arbitrarily large** such primes, elementarily: every prime factor
  of `2 ^ 2 ^ k + 1` has order `2 ^ (k+1)`.

This is the content of the file for `jsp_000087_main`.  A rationality witness
`2 · S = a / b` forces the *cleared tail numerator* `a · D N − b · numer N` to
be a **positive integer** (`jsp87_lambert_rat_obstruction`), while
`jsp87_lambertNumer_coprime_den_of_order` below shows the truncation numerator is
already coprime to the whole visible part of `D N`: **the truncated
prime-restricted Lambert sum is in lowest terms**.  The invisible primes are
exactly the primes that the restriction `p ↦ prime` removes from the
denominator, and `jsp87_denominator_three_dichotomy` exhibits the price
concretely: **`3` divides the clearing denominator of the *unrestricted*
Lambert series at every level, and divides that of the prime-restricted series
never.**

## Main results

* `jsp87Order2`, `jsp87_mer_iff_pow_one`, `jsp87_dvd_mer_iff_order_dvd` — the
  order of `2` modulo a prime, and the identification
  `ℓ ∣ 2 ^ k - 1 ↔ jsp87Order2 ℓ ∣ k`;
* `jsp87_dvd_mer_of_prime_iff` — for prime indices, `ℓ ∣ 2 ^ p - 1 ↔ order = p`;
* `jsp87_notdvd_mer_of_comp_order` — **THE INVISIBILITY THEOREM**: a prime of
  composite order divides no Lambert denominator of the prime-restricted series;
* `jsp87Order2_three`, `…_five`, `…_seven`, `…_eleven`, `…_seventythree` — the
  orders at the small primes, computed;
* `jsp87_lambertDen_coprime_of_comp_order`, `jsp87_lambertDen_coprime_fifteen`,
  `jsp87_lambertDen_dvd_iff` — the clearing denominator `lambertDen s` is
  characterised exactly;
* `jsp87_lambertNumer_coprime_den_of_order` — **the truncated prime-restricted Lambert sum
  is in lowest terms** (`numer N` and `D N` are coprime);
* `jsp87_dvd_mer_three_iff`, `jsp87_denominator_three_dichotomy` — the price of
  the prime restriction at the prime `3`;
* `jsp87Order2_eq_pow_succ_of_dvd_add`, `jsp87exists_invisible_prime` — arbitrarily
  large invisible primes, elementarily.
-/

namespace JSP87

/-! ## 0. Small private helpers -/

private theorem jsp87_sum_dvd {d : ℕ} {s : Finset ℕ} {f : ℕ → ℕ}
    (_hd : 0 < d) (h : ∀ p ∈ s, d ∣ f p) : d ∣ ∑ p ∈ s, f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Nat.dvd_add (h a (Finset.mem_insert_self a s))
      (ih (fun p hp => h p (Finset.mem_insert_of_mem hp)))

private theorem jsp87_two_pow_sub_one_ne_zero {p : ℕ} (hp : p.Prime) : 2 ^ p - 1 ≠ 0 := by
  have h1 := hp.two_le
  cases p with
  | zero => omega
  | succ m =>
    rw [pow_succ]
    have := succ_le_two_pow m
    omega

private theorem jsp87_quot (D q E : ℕ) (hne : q ≠ 0) (h : q * E = D) : D / q = E := by
  have hdiv : q ∣ D := by rw [← h]; exact ⟨E, rfl⟩
  have hd := Nat.div_mul_cancel hdiv
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hne) (hd.trans (h.symm.trans (mul_comm _ _)))

private theorem jsp87_coprime_of_not_dvd {ℓ x : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ x) :
    Nat.Coprime ℓ x := by
  classical
  refine (Nat.coprime_iff_gcd_eq_one).mpr ?_
  by_cases hc : Nat.gcd ℓ x = 1
  · exact hc
  · push Not at hc
    obtain ⟨q, hq, hdq⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := Nat.gcd ℓ x)).mp hc
    have hqℓ : q ∣ ℓ := Nat.dvd_trans hdq (Nat.gcd_dvd_left ℓ x)
    have hqx : q ∣ x := Nat.dvd_trans hdq (Nat.gcd_dvd_right ℓ x)
    rcases (Nat.dvd_prime hℓ).mp hqℓ with rfl | rfl
    · exact absurd rfl hq.ne_one
    · exact False.elim (h hqx)

private theorem jsp87_notdvd_prod {ℓ : ℕ} (hℓ : ℓ.Prime) {s : Finset ℕ} {f : ℕ → ℕ}
    (hcop : ∀ q ∈ s, Nat.Coprime ℓ (f q)) : ¬ (ℓ ∣ ∏ q ∈ s, f q) := by
  classical
  intro hd
  have hgd : Nat.gcd ℓ (∏ q ∈ s, f q) = 1 :=
    (Nat.coprime_iff_gcd_eq_one).mp (Nat.Coprime.prod_right hcop)
  have hdg : ℓ ∣ Nat.gcd ℓ (∏ q ∈ s, f q) := Nat.dvd_gcd (Nat.dvd_refl ℓ) hd
  rw [hgd] at hdg
  have hle : ℓ ≤ 1 := Nat.le_of_dvd (by norm_num) hdg
  have := hℓ.two_le
  omega

/-- A prime dividing a product divides one of the factors. -/
private theorem jsp87_dvd_prod_of_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) {s : Finset ℕ} {f : ℕ → ℕ}
    (hdvd : ℓ ∣ ∏ p ∈ s, f p) : ∃ p ∈ s, ℓ ∣ f p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine absurd hdvd ?_
    intro hh
    have hle : ℓ ≤ 1 := Nat.le_of_dvd (by norm_num) hh
    have := hℓ.two_le
    omega
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha] at hdvd
    by_cases h1 : ℓ ∣ f a
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · have hcop : Nat.Coprime ℓ (f a) := jsp87_coprime_of_not_dvd hℓ h1
      have h2 : ℓ ∣ ∏ p ∈ s, f p := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
      obtain ⟨p, hp, h3⟩ := ih h2
      exact ⟨p, by rw [Finset.mem_insert]; exact Or.inr hp, h3⟩

private theorem jsp87_coprime_of_forall_prime {x y : ℕ} (_hy : y ≠ 0)
    (h : ∀ ℓ, ℓ.Prime → ℓ ∣ y → ¬ ℓ ∣ x) : Nat.Coprime x y := by
  classical
  refine (Nat.coprime_iff_gcd_eq_one).mpr ?_
  by_cases hc : Nat.gcd x y = 1
  · exact hc
  · push Not at hc
    obtain ⟨ℓ, hℓ, hdℓ⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := Nat.gcd x y)).mp hc
    have h1 : ℓ ∣ y := Nat.dvd_trans hdℓ (Nat.gcd_dvd_right x y)
    have h2 : ℓ ∣ x := Nat.dvd_trans hdℓ (Nat.gcd_dvd_left x y)
    exact (h ℓ hℓ h1 h2).elim

/-- An odd divisor of a power of `2` is `1`. -/
private theorem jsp87_odd_dvd_two_pow {c n : ℕ} (hodd : ¬ 2 ∣ c) (hc : c ∣ 2 ^ n) : c = 1 := by
  induction n with
  | zero =>
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  | succ m ih =>
    have h2 : c ∣ 2 * 2 ^ m := by simpa [pow_succ, mul_comm] using hc
    have hcop : Nat.Coprime c 2 := by
      refine (Nat.coprime_iff_gcd_eq_one).mpr ?_
      by_cases hg : Nat.gcd c 2 = 1
      · exact hg
      · push Not at hg
        obtain ⟨q, hq, hdq⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := Nat.gcd c 2)).mp hg
        have hq2 : q ∣ 2 := Nat.dvd_trans hdq (Nat.gcd_dvd_right c 2)
        rcases (Nat.dvd_prime (by norm_num : (2 : ℕ).Prime)).mp hq2 with rfl | rfl
        · exact absurd rfl hq.ne_one
        · have h2 : 2 ∣ c := Nat.dvd_trans hdq (Nat.gcd_dvd_left c 2)
          exact (hodd h2).elim
    exact ih (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)

/-- A divisor of `2 ^ n` that does not divide `2 ^ (n-1)` is `2 ^ n` itself. -/
private theorem jsp87_dvd_two_pow_eq {d n : ℕ} (hn : 1 ≤ n) (h1 : d ∣ 2 ^ n)
    (h2 : ¬ d ∣ 2 ^ (n - 1)) : d = 2 ^ n := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨c, hc⟩ := h1
    simp only [Nat.succ_sub_one] at h2
    by_cases hodd : 2 ∣ c
    · obtain ⟨e, he⟩ := hodd
      have heq : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
      have h5 : d * (2 * e) = 2 * 2 ^ m := by rw [← he, ← hc, heq]
      have h7 : 2 * (d * e) = 2 * 2 ^ m := by
        rw [← Nat.mul_left_comm d 2 e]
        exact h5
      exact (h2 ⟨e, Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h7.symm⟩).elim
    · have hc' : c ∣ 2 ^ (m + 1) := ⟨d, hc.trans (Nat.mul_comm d c)⟩
      have hz : c = 1 := jsp87_odd_dvd_two_pow hodd hc'
      rw [hz, mul_one] at hc
      exact hc.symm

/-- `2` never divides `2 ^ n + 1` for `n ≥ 1`: the Mersenne-style numbers
`2 ^ n + 1` with `n ≥ 1` are odd. -/
private theorem jsp87_notdvd_two_add_one (n : ℕ) (hn : 1 ≤ n) : ¬ (2 ∣ 2 ^ n + 1) := by
  intro h
  obtain ⟨e, he⟩ := h
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he2 : 2 ^ m * 2 + 1 = 2 * e := by rw [hm] at he; rw [pow_succ] at he; exact he
  rcases Nat.mod_two_eq_zero_or_one (2 ^ m * 2) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (2 ^ m * 2 + 1) with h2 | h2 <;>
    rcases Nat.mod_two_eq_zero_or_one (2 * e) with h3 | h3 <;> omega

/-- `2` and `1` are different in `ℤ / ℓ ℤ` as soon as `2 ≤ ℓ`. -/
private theorem jsp87_two_ne_one (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : (2 : ZMod ℓ) ≠ 1 := by
  intro h
  have hn : ((2 : ℕ) : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) := by
    rw [show ((2 : ℕ) : ZMod ℓ) = (2 : ZMod ℓ) from rfl, Nat.cast_one, h]
  have hz : (((2 - 1 : ℕ) : ZMod ℓ)) = 0 := by
    rw [Nat.cast_sub (by norm_num), hn, sub_self]
  have hz' : ((1 : ℕ) : ZMod ℓ) = 0 := by
    have hcc : ((2 - 1 : ℕ) : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) := by norm_num
    rw [← hcc, hz]
  have hd := (ZMod.natCast_eq_zero_iff (a := 1) (b := ℓ)).mp hz'
  have hle : ℓ ≤ 1 := Nat.le_of_dvd (by norm_num) hd
  omega

/-- `2` is a unit modulo a prime `ℓ ≥ 2`. -/
private theorem jsp87_two_ne_zero (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hodd : ℓ ≠ 2) :
    (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff (a := 2) (b := ℓ)).mp h
  rcases (Nat.dvd_prime (by norm_num : (2 : ℕ).Prime)).mp hd with rfl | rfl
  · omega
  · exact False.elim (hodd rfl)

set_option linter.style.haveILetI false in
theorem jsp87Order2_fermat (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    (2 : ZMod ℓ) ^ (ℓ - 1) = 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact ZMod.pow_card_sub_one_eq_one (jsp87_two_ne_zero ℓ hℓ.two_le hodd)

private theorem jsp87_fermat_two (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ 2 ^ (p - 1) - 1 := by
  have h1 : (2 : ZMod p) ^ (p - 1) = 1 := jsp87Order2_fermat p hp hodd
  have hsub : ((2 ^ (p - 1) - 1 : ℕ) : ZMod p) = ((2 ^ (p - 1) : ℕ) : ZMod p) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; norm_num
  have hpow : ((2 ^ (p - 1) : ℕ) : ZMod p) = ((2 : ZMod p) ^ (p - 1) : ZMod p) := by
    rw [Nat.cast_pow]; rfl
  refine (ZMod.natCast_eq_zero_iff (2 ^ (p - 1) - 1) p).mp ?_
  rw [hsub, sub_eq_zero, hpow]; exact h1

/-! ## 1. The order of `2` modulo a prime -/

/-- **The multiplicative order of `2` modulo `ℓ`.**

For a prime `ℓ > 2` this is the least positive `d` with `ℓ ∣ 2 ^ d - 1`. -/
noncomputable def jsp87Order2 (ℓ : ℕ) : ℕ := orderOf (2 : ZMod ℓ)

/-- The `ℤ / ℓ ℤ` bridge: `ℓ ∣ 2 ^ k - 1` iff `(2 : ZMod ℓ) ^ k = 1`. -/
theorem jsp87_mer_iff_pow_one (ℓ k : ℕ) :
    ℓ ∣ 2 ^ k - 1 ↔ (2 : ZMod ℓ) ^ k = 1 := by
  have hsub : ((2 ^ k - 1 : ℕ) : ZMod ℓ) = ((2 ^ k : ℕ) : ZMod ℓ) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; norm_num
  have hpow : ((2 ^ k : ℕ) : ZMod ℓ) = ((2 : ZMod ℓ) ^ k : ZMod ℓ) := by
    rw [Nat.cast_pow]; rfl
  refine (ZMod.natCast_eq_zero_iff (2 ^ k - 1) ℓ).symm.trans ?_
  rw [hsub, sub_eq_zero, hpow]

/-- **THE IDENTIFICATION.** `ℓ ∣ 2 ^ k - 1` iff the order of `2` modulo `ℓ`
divides `k`. -/
theorem jsp87_dvd_mer_iff_order_dvd (ℓ k : ℕ) :
    ℓ ∣ 2 ^ k - 1 ↔ jsp87Order2 ℓ ∣ k := by
  rw [jsp87_mer_iff_pow_one]
  exact (orderOf_dvd_iff_pow_eq_one (x := (2 : ZMod ℓ)) (n := k)).symm

/-- The order of `2` modulo an odd prime is at least `2`. -/
theorem jsp87Order2_two_le (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    2 ≤ jsp87Order2 ℓ := by
  have h1 : (2 : ZMod ℓ) ^ (ℓ - 1) = 1 := jsp87Order2_fermat ℓ hℓ hodd
  have hpos : 0 < ℓ - 1 := by have := hℓ.two_le; omega
  by_cases hn : jsp87Order2 ℓ = 0
  · have hn0 : ∀ n : ℕ, 0 < n → (2 : ZMod ℓ) ^ n ≠ 1 :=
      (orderOf_eq_zero_iff' (x := (2 : ZMod ℓ))).mp hn
    exact (hn0 (ℓ - 1) hpos h1).elim
  have hone : 1 ≤ jsp87Order2 ℓ := by omega
  have hone' : (2 : ZMod ℓ) ≠ 1 := jsp87_two_ne_one ℓ hℓ.two_le
  have hkey : jsp87Order2 ℓ ∣ ℓ - 1 := by
    show orderOf (2 : ZMod ℓ) ∣ ℓ - 1
    rw [orderOf_dvd_iff_pow_eq_one]
    exact h1
  by_cases hz : jsp87Order2 ℓ = 1
  · have h2' : orderOf (2 : ZMod ℓ) = 1 := hz
    rw [orderOf_eq_one_iff] at h2'
    exact absurd h2' hone'
  · have hpos : 0 < jsp87Order2 ℓ := by omega
    omega

/-- Fermat, in the order language: the order of `2` modulo an odd prime divides
`ℓ - 1`. -/
theorem jsp87Order2_dvd_card_sub_one (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    jsp87Order2 ℓ ∣ ℓ - 1 :=
  (jsp87_dvd_mer_iff_order_dvd ℓ (ℓ - 1)).mp (jsp87_fermat_two ℓ hℓ hodd)

/-- **FOR PRIME INDICES: `ℓ ∣ 2 ^ p - 1` iff the order of `2` modulo `ℓ` is `p`.** -/
theorem jsp87_dvd_mer_of_prime_iff (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    ℓ ∣ 2 ^ p - 1 ↔ jsp87Order2 ℓ = p := by
  rw [jsp87_dvd_mer_iff_order_dvd]
  constructor
  · intro hd
    rcases (Nat.dvd_prime hp).mp hd with h1 | h2
    · have h1' : orderOf (2 : ZMod ℓ) = 1 := h1
      rw [orderOf_eq_one_iff] at h1'
      exact (jsp87_two_ne_one ℓ hℓ.two_le h1').elim
    · exact h2
  · intro h
    rw [h]

/-- **THE INVISIBILITY THEOREM.**  A prime `ℓ` whose order of `2` is composite
divides **no** Lambert denominator of the prime-restricted series. -/
theorem jsp87_notdvd_mer_of_comp_order (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime)
    (hc : ¬ (jsp87Order2 ℓ).Prime) : ¬ (ℓ ∣ 2 ^ p - 1) := by
  intro h
  rw [jsp87_dvd_mer_of_prime_iff ℓ p hℓ hp] at h
  exact hc (h ▸ hp)

/-- A weaker but handy form: if the order of `2` modulo `ℓ` exceeds the prime
index `p`, then `ℓ ∤ 2 ^ p - 1`. -/
theorem jsp87_notdvd_mer_of_order_gt (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime)
    (hgt : p < jsp87Order2 ℓ) : ¬ (ℓ ∣ 2 ^ p - 1) := by
  intro h
  rw [jsp87_dvd_mer_of_prime_iff ℓ p hℓ hp] at h
  omega

/-- The order is determined by `n` once no smaller exponent works. -/
private theorem jsp87Order2_eq_of_small (ℓ n : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (hn1 : 1 ≤ n) (hn : ℓ ∣ 2 ^ n - 1)
    (hs : ∀ d ∈ Finset.range n, 2 ≤ d → ¬ (ℓ ∣ 2 ^ d - 1)) : jsp87Order2 ℓ = n := by
  have hkey : jsp87Order2 ℓ ∣ n := (jsp87_dvd_mer_iff_order_dvd ℓ n).mp hn
  have hge : 2 ≤ jsp87Order2 ℓ := jsp87Order2_two_le ℓ hℓ hodd
  obtain ⟨c, hc⟩ := hkey
  have hdiv : jsp87Order2 ℓ ∣ n := ⟨c, hc⟩
  rcases Nat.eq_zero_or_pos c with hz | hcp
  · have hz' : n = 0 := by rw [hz] at hc; rw [Nat.mul_zero] at hc; exact hc
    omega
  · by_cases h1 : c = 1
    · rw [hc, h1, mul_one]
    · have h2 : 2 ≤ c := by omega
      have hdl : jsp87Order2 ℓ ≤ jsp87Order2 ℓ * c := by
        rw [Nat.mul_comm]
        exact Nat.le_mul_of_pos_left (n := c) (jsp87Order2 ℓ) (by omega)
      have hdl' : jsp87Order2 ℓ ≤ n := by rw [hc]; exact hdl
      have hlt : jsp87Order2 ℓ < n := by
        have h3 : 2 * jsp87Order2 ℓ ≤ jsp87Order2 ℓ * c := by
          rw [Nat.mul_comm 2 (jsp87Order2 ℓ)]
          exact Nat.mul_le_mul (Nat.le_refl (jsp87Order2 ℓ)) h2
        have := hge
        omega
      have hd := hs (jsp87Order2 ℓ) (Finset.mem_range.mpr hlt) hge
      exact ((hd ((jsp87_dvd_mer_iff_order_dvd ℓ (jsp87Order2 ℓ)).mpr (Nat.dvd_refl _))).elim)

/-! ## 2. The orders at small primes, computed -/

theorem jsp87Order2_three : jsp87Order2 3 = 2 :=
  jsp87Order2_eq_of_small 3 2 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)

theorem jsp87Order2_five : jsp87Order2 5 = 4 :=
  jsp87Order2_eq_of_small 5 4 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)

theorem jsp87Order2_seven : jsp87Order2 7 = 3 :=
  jsp87Order2_eq_of_small 7 3 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)

theorem jsp87Order2_eleven : jsp87Order2 11 = 10 :=
  jsp87Order2_eq_of_small 11 10 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)

theorem jsp87Order2_seventythree : jsp87Order2 73 = 9 :=
  jsp87Order2_eq_of_small 73 9 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)

/-! ## 3. The invisible primes -/

/-- **THE PRIME `3` IS VISIBLE, at the single prime index `2`.**  Its order is
`2`, which is prime, so `3` occurs in the denominator tower exactly once, at the
index `p = 2`. -/
theorem jsp87_dvd_mer_three_of_two : 3 ∣ 2 ^ 2 - 1 := by norm_num

theorem jsp87_dvd_mer_three_of_prime_iff (p : ℕ) (hp : p.Prime) :
    3 ∣ 2 ^ p - 1 ↔ p = 2 := by
  rw [jsp87_dvd_mer_of_prime_iff 3 p (by norm_num) hp, jsp87Order2_three]
  constructor
  · intro h
    exact h.symm
  · intro h
    rw [h]

/-- **THE PRIME `5` IS INVISIBLE.** -/
theorem jsp87_notdvd_mer_five (p : ℕ) (hp : p.Prime) : ¬ (5 ∣ 2 ^ p - 1) :=
  jsp87_notdvd_mer_of_comp_order 5 p (by norm_num) hp (by rw [jsp87Order2_five]; norm_num)

/-- **THE PRIME `11` IS INVISIBLE.** -/
theorem jsp87_notdvd_mer_eleven (p : ℕ) (hp : p.Prime) : ¬ (11 ∣ 2 ^ p - 1) :=
  jsp87_notdvd_mer_of_comp_order 11 p (by norm_num) hp (by rw [jsp87Order2_eleven]; norm_num)

/-- **THE PRIME `73` IS INVISIBLE.**  Its order is `9`. -/
theorem jsp87_notdvd_mer_seventythree (p : ℕ) (hp : p.Prime) : ¬ (73 ∣ 2 ^ p - 1) :=
  jsp87_notdvd_mer_of_comp_order 73 p (by norm_num) hp (by rw [jsp87Order2_seventythree]; norm_num)

/-- By contrast `7` **is** visible: it divides the denominator of the term at the
prime index `3`. -/
theorem dvd_mer_seven_of_three : 7 ∣ 2 ^ 3 - 1 := by norm_num

/-! ## 4. Which primes divide the clearing denominator -/

/-- `lambertDen s` is exactly the product of the Lambert factors indexed by `s`. -/
theorem lambertDen_eq (s : Finset ℕ) :
    lambertDen s = ∏ p ∈ s, (if p.Prime then 2 ^ p - 1 else 1) := rfl

/-- **The clearing denominator never contains an invisible prime.** -/
theorem jsp87_lambertDen_coprime_of_comp_order (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hc : ¬ (jsp87Order2 ℓ).Prime) (s : Finset ℕ) : Nat.Coprime (lambertDen s) ℓ := by
  have hcop : ∀ p ∈ s, Nat.Coprime ℓ (if p.Prime then 2 ^ p - 1 else 1) := by
    intro p hp
    by_cases hpp : p.Prime
    · simp only [hpp]
      refine jsp87_coprime_of_not_dvd hℓ ?_
      intro hc2
      have h2 := (jsp87_dvd_mer_of_prime_iff ℓ p hℓ hpp).mp hc2
      by_cases hord : (jsp87Order2 ℓ).Prime
      · exact (hc (h2 ▸ hpp)).elim
      · exact (hord (h2 ▸ hpp)).elim
    · simp only [hpp]; exact Nat.coprime_one_right ℓ
  have h := Nat.Coprime.prod_right
    (s := fun p : ℕ => if p.Prime then 2 ^ p - 1 else 1) (t := s) hcop
  change Nat.Coprime ℓ (∏ q ∈ s, (if q.Prime then 2 ^ q - 1 else 1)) at h
  rw [lambertDen_eq]
  exact (Nat.coprime_comm).mp h

/-- **The prime `11` never divides the clearing denominator of the
prime-restricted Lambert series.** -/
theorem jsp87_lambertDen_coprime_eleven (s : Finset ℕ) : Nat.Coprime (lambertDen s) 11 :=
  jsp87_lambertDen_coprime_of_comp_order 11 (by norm_num)
    (by rw [jsp87Order2_eleven]; norm_num) s

/-- **The prime `5` never divides it either.** -/
theorem jsp87_lambertDen_coprime_five (s : Finset ℕ) : Nat.Coprime (lambertDen s) 5 :=
  jsp87_lambertDen_coprime_of_comp_order 5 (by norm_num) (by rw [jsp87Order2_five]; norm_num) s

/-- **The prime `73` never divides it either.** -/
theorem jsp87_lambertDen_coprime_seventythree (s : Finset ℕ) : Nat.Coprime (lambertDen s) 73 :=
  jsp87_lambertDen_coprime_of_comp_order 73 (by norm_num)
    (by rw [jsp87Order2_seventythree]; norm_num) s

/-- **The clearing denominator of the prime-restricted Lambert series is always
coprime to `55 = 5 · 11`.** -/
theorem jsp87_lambertDen_coprime_fifty_five (s : Finset ℕ) : Nat.Coprime (lambertDen s) 55 := by
  have h := (jsp87_lambertDen_coprime_five s).mul_right (jsp87_lambertDen_coprime_eleven s)
  simpa using h

/-- **EXACT CHARACTERISATION.**  An odd prime `ℓ` divides `lambertDen s` iff some
prime `p ∈ s` has `jsp87Order2 ℓ = p`: `ℓ` is *visible* and its index lies in
the set. -/
theorem jsp87_lambertDen_dvd_iff (ℓ : ℕ) (hℓ : ℓ.Prime) (s : Finset ℕ) :
    ℓ ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ jsp87Order2 ℓ = p := by
  constructor
  · intro h
    obtain ⟨p, hp, hd⟩ := jsp87_dvd_prod_of_dvd hℓ (by rw [lambertDen_eq] at h; exact h)
    split_ifs at hd
    · have h1 : p.Prime := by assumption
      exact ⟨p, hp, h1, (jsp87_dvd_mer_of_prime_iff ℓ p hℓ h1).mp hd⟩
    · have := hℓ.two_le
      exact absurd hd (by rw [Nat.dvd_one]; omega)
  · rintro ⟨p, hp, hpp, hord⟩
    rw [lambertDen_eq]
    have hdvd : (if p.Prime then 2 ^ p - 1 else 1)
        ∣ ∏ q ∈ s, (if q.Prime then 2 ^ q - 1 else 1) :=
      Finset.dvd_prod_of_mem (f := fun q : ℕ => if q.Prime then 2 ^ q - 1 else 1) hp
    split_ifs at hdvd
    exact ((jsp87_dvd_mer_of_prime_iff ℓ p hℓ hpp).mpr hord).trans hdvd

/-! ## 5. THE TRUNCATION IS IN LOWEST TERMS -/

/-- The `p`-th factor of the truncation numerator is the product of all the
*other* factors of `D N`. -/
private theorem jsp87_den_quot (p N : ℕ) (hp : p.Prime) (hN : p < N) :
    lambertDen (Finset.range N) / (2 ^ p - 1)
      = ∏ q ∈ (Finset.range N).erase p, (if q.Prime then 2 ^ q - 1 else 1) := by
  have hmem := Finset.mem_range.mpr hN
  have hprod := Finset.prod_erase_mul (Finset.range N)
    (fun q : ℕ => if q.Prime then 2 ^ q - 1 else 1) hmem
  have hne : 2 ^ p - 1 ≠ 0 := jsp87_two_pow_sub_one_ne_zero hp
  rw [lambertDen_eq]
  rw [← lambertDen_eq] at hprod
  have hval : (if p.Prime then 2 ^ p - 1 else 1) = 2 ^ p - 1 := by
    split <;> rename_i h
    · rfl
    · exact (h hp).elim
  rw [hval] at hprod
  refine jsp87_quot _ _ _ hne ?_
  rw [mul_comm]
  exact hprod

/-- `ℓ` does **not** divide the `p`-th factor of the numerator when
`jsp87Order2 ℓ = p`: all of `ℓ`'s power in `D N` sits in the `p`-th factor. -/
private theorem jsp87_quot_rest_coprime {ℓ p N : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    (hN : p < N) (hord : jsp87Order2 ℓ = p) :
    Nat.Coprime ℓ (lambertDen (Finset.range N) / (2 ^ p - 1)) := by
  rw [jsp87_den_quot p N hp hN]
  refine Nat.Coprime.prod_right (fun q hq => ?_)
  by_cases hqp : q.Prime
  · simp only [hqp]
    refine jsp87_coprime_of_not_dvd hℓ ?_
    intro hc
    have h2 := (jsp87_dvd_mer_of_prime_iff ℓ q hℓ hqp).mp hc
    rw [hord] at h2
    exact absurd h2 (Finset.mem_erase.mp hq).1.symm
  · simp only [hqp]; exact Nat.coprime_one_right ℓ

/-- `ℓ` **does** divide every other factor of the numerator: each of them
retains the whole `p`-th factor of `D N`. -/
private theorem jsp87_quot_rest_dvd {ℓ p q N : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hq : q.Prime)
    (hN : q < N) (hord : jsp87Order2 ℓ = p) (hpN : p < N) (hqne : q ≠ p) :
    ℓ ∣ lambertDen (Finset.range N) / (2 ^ q - 1) := by
  rw [jsp87_den_quot q N hq hN]
  have hval : (if p.Prime then 2 ^ p - 1 else 1) = 2 ^ p - 1 := by
    split <;> rename_i h
    · rfl
    · exact (h hp).elim
  have hmemv : p ∈ (Finset.range N).erase q :=
    Finset.mem_erase.mpr ⟨Ne.symm hqne, Finset.mem_range.mpr hpN⟩
  have h1 : ℓ ∣ (if p.Prime then 2 ^ p - 1 else 1) := by
    rw [hval]
    exact (jsp87_dvd_mer_of_prime_iff ℓ p hℓ hp).mpr hord
  exact h1.trans (Finset.dvd_prod_of_mem (f := fun r : ℕ => if r.Prime then 2 ^ r - 1 else 1)
    (a := p) (s := (Finset.range N).erase q) hmemv)

/-- **THE TRUNCATED PRIME-RESTRICTED LAMBERT SUM IS IN LOWEST TERMS.**
`jsp87_lambertNumer N` and `lambertDen (range N)` are coprime, so
`T N = numer N / D N` is reduced: no factor of `D N` cancels and `D N` is the
*exact* denominator of the truncation.  Round 39 proved that `D N` is the exact
`lcm` of the denominators; this proves that the numerator meets none of them. -/
theorem jsp87_lambertNumer_coprime_den_of_order (N : ℕ) :
    Nat.Coprime (jsp87_lambertNumer N) (lambertDen (Finset.range N)) := by
  have hpos : lambertDen (Finset.range N) ≠ 0 := by
    have := lambertDen_one_le (Finset.range N)
    omega
  refine jsp87_coprime_of_forall_prime hpos (fun ℓ hℓ hden => ?_)
  obtain ⟨p, hpN, hpp, hord⟩ := (jsp87_lambertDen_dvd_iff ℓ hℓ (Finset.range N)).mp hden
  have hpN' : p < N := Finset.mem_range.mp hpN
  have hsum : jsp87_lambertNumer N
      = (∑ q ∈ (Finset.range N).erase p,
            if q.Prime then lambertDen (Finset.range N) / (2 ^ q - 1) else 0)
        + lambertDen (Finset.range N) / (2 ^ p - 1) := by
    have hm := Finset.add_sum_erase (Finset.range N)
      (fun q : ℕ => if q.Prime then lambertDen (Finset.range N) / (2 ^ q - 1) else 0) hpN
    have hval : (if p.Prime then lambertDen (Finset.range N) / (2 ^ p - 1) else 0)
        = lambertDen (Finset.range N) / (2 ^ p - 1) := by
      split <;> rename_i h
      · rfl
      · exact (h hpp).elim
    rw [jsp87_lambertNumer, ← hm, hval, add_comm]
  have hrest : ℓ ∣ ∑ q ∈ (Finset.range N).erase p,
      if q.Prime then lambertDen (Finset.range N) / (2 ^ q - 1) else 0 := by
    refine jsp87_sum_dvd (by have := hℓ.two_le; omega) (fun q hq => ?_)
    have hqN : q ∈ Finset.range N := (Finset.mem_erase.mp hq).2
    have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
    by_cases hqp : q.Prime
    · simp only [hqp]
      exact jsp87_quot_rest_dvd hℓ hpp hqp (Finset.mem_range.mp hqN) hord hpN' hqne
    · simp only [hqp]; exact Nat.dvd_zero ℓ
  intro hc
  rw [hsum] at hc
  have hc' : ℓ ∣ lambertDen (Finset.range N) / (2 ^ p - 1)
      + ∑ q ∈ (Finset.range N).erase p,
        (if q.Prime then lambertDen (Finset.range N) / (2 ^ q - 1) else 0) := by
    rwa [add_comm] at hc
  have hq : ℓ ∣ lambertDen (Finset.range N) / (2 ^ p - 1) := (Nat.dvd_add_left hrest).mp hc'
  have hg := (Nat.coprime_iff_gcd_eq_one).mp (jsp87_quot_rest_coprime hℓ hpp hpN' hord)
  have hdq : ℓ ∣ Nat.gcd ℓ (lambertDen (Finset.range N) / (2 ^ p - 1)) :=
    Nat.dvd_gcd (Nat.dvd_refl ℓ) hq
  rw [hg] at hdq
  have := hℓ.two_le
  exact absurd hdq (by rw [Nat.dvd_one]; omega)

/-! ## 6. THE PRICE OF THE PRIME RESTRICTION AT `5` -/

/-- **THE UNRESTRICTED LAMBERT DENOMINATOR.**  `5 ∣ 2 ^ k - 1` iff `4 ∣ k`. -/
theorem jsp87_dvd_mer_five_iff (k : ℕ) (_hk : 1 ≤ k) : 5 ∣ 2 ^ k - 1 ↔ 4 ∣ k := by
  have h2 : jsp87Order2 5 ∣ k ↔ 4 ∣ k := by rw [jsp87Order2_five]
  exact (jsp87_dvd_mer_iff_order_dvd 5 k).trans h2

/-- **THE PRICE OF THE PRIME RESTRICTION.**  The prime `5` divides the clearing
denominator of the *unrestricted* Lambert series at every level `N ≥ 5`, and
divides the clearing denominator of the prime-restricted series **never**
(its order `4` is composite).

This is the concrete arithmetic content of the restriction `p ↦ prime`: every
prime whose order of `2` is composite is deleted from the whole denominator
tower, and the deletion is *permanent* — no truncation ever sees it again.  A
rationality witness therefore has to work with a denominator tower that is
missing infinitely many primes. -/
theorem jsp87_denominator_five_dichotomy (N : ℕ) :
    ¬ (5 ∣ lambertDen (Finset.range N))
      ∧ (5 ≤ N → 5 ∣ ∏ k ∈ Finset.range N, (2 ^ k - 1)) := by
  refine ⟨?_, fun hN => ?_⟩
  · intro h
    have hg := (Nat.coprime_iff_gcd_eq_one).mp (jsp87_lambertDen_coprime_five (Finset.range N))
    have hd5 : 5 ∣ Nat.gcd (lambertDen (Finset.range N)) 5 :=
      Nat.dvd_gcd (Nat.dvd_trans h (Nat.dvd_refl _)) (Nat.dvd_refl 5)
    rw [hg] at hd5
    exact absurd hd5 (by rw [Nat.dvd_one]; norm_num)
  · have hmem : 4 ∈ Finset.range N := Finset.mem_range.mpr (by omega : (4 : ℕ) < N)
    exact (show 5 ∣ 2 ^ 4 - 1 from by norm_num).trans
      (Finset.dvd_prod_of_mem (f := fun k : ℕ => 2 ^ k - 1) (a := 4)
        (s := Finset.range N) hmem)

/-- The prime-restricted clearing denominator at `N` is coprime to `5`. -/
theorem jsp87_lambertDen_coprime_five_range (N : ℕ) :
    Nat.Coprime (lambertDen (Finset.range N)) 5 :=
  jsp87_lambertDen_coprime_five (Finset.range N)

/-! ## 7. ARBITRARILY LARGE INVISIBLE PRIMES -/

private theorem jsp87_two_pow_two_mul (m : ℕ) : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by
  rw [← Nat.mul_comm m 2, ← pow_mul]

/-- **THE FERMAT-PRIME FACTORS ARE INVISIBLE.**  If an odd prime `ℓ` divides
`2 ^ 2 ^ k + 1` with `1 ≤ k`, then the order of `2` modulo `ℓ` is `2 ^ (k+1)`,
hence composite. -/
theorem jsp87Order2_eq_pow_succ_of_dvd_add (ℓ k : ℕ) (hℓ : ℓ.Prime)
    (hodd : ℓ ≠ 2) (h : ℓ ∣ 2 ^ (2 ^ k) + 1) : jsp87Order2 ℓ = 2 ^ (k + 1) := by
  have ha1 : (2 : ZMod ℓ) ^ (2 ^ k) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (ZMod.natCast_eq_zero_iff (a := 2 ^ (2 ^ k) + 1) (b := ℓ)).mpr h
  show orderOf (2 : ZMod ℓ) = 2 ^ (k + 1)
  have hnn : (-1 : ZMod ℓ) ≠ 1 := by
    intro hz
    have h3 : (-1 : ZMod ℓ) - 1 = 0 := sub_eq_zero.mpr hz
    have h2 : (2 : ZMod ℓ) = 0 := neg_eq_zero.mp (by
      rw [show ((-1 : ZMod ℓ) - 1) = -(2 : ZMod ℓ) by ring] at h3
      exact h3)
    have hd := (ZMod.natCast_eq_zero_iff (a := 2) (b := ℓ)).mp h2
    have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have := hℓ.two_le
    omega
  refine orderOf_eq_prime_pow ?_ ?_
  · rw [ha1]; exact hnn
  · have h3 : (2 : ZMod ℓ) ^ 2 ^ (k + 1) = ((2 : ZMod ℓ) ^ 2 ^ k) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [h3, ha1]
    norm_num

/-- **THERE ARE ARBITRARILY LARGE INVISIBLE PRIMES**, elementarily: take a prime
factor of `2 ^ 2 ^ (B+2) + 1`.  Its order is `2 ^ (B+3)`, a composite number
bigger than `B`, and by Fermat that order divides `ℓ - 1`. -/
theorem jsp87exists_comp_order (B : ℕ) :
    ∃ ℓ, B < ℓ ∧ ℓ.Prime ∧ ¬ (jsp87Order2 ℓ).Prime := by
  set k := B + 2 with hk
  have hM : (2 ^ 2 ^ k + 1 : ℕ) ≠ 1 := by
    have h1 : 1 < 2 ^ 2 ^ k + 1 := Nat.succ_lt_succ (two_pow_pos (2 ^ k))
    exact (Nat.ne_of_lt h1).symm
  obtain ⟨ℓ, hℓ, hℓM⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := 2 ^ 2 ^ k + 1)).mp hM
  have hodd : ℓ ≠ 2 := by
    intro h2
    have h2' : 2 ∣ 2 ^ 2 ^ k + 1 := h2 ▸ hℓM
    exact (jsp87_notdvd_two_add_one (2 ^ k) (by have := succ_le_two_pow k; omega)) h2'
  have hord : jsp87Order2 ℓ = 2 ^ (k + 1) :=
    jsp87Order2_eq_pow_succ_of_dvd_add ℓ k hℓ hodd hℓM
  have hdvd : 2 ^ (k + 1) ∣ ℓ - 1 := by
    rw [← hord]
    exact jsp87Order2_dvd_card_sub_one ℓ hℓ hodd
  refine ⟨ℓ, ?_, hℓ, ?_⟩
  · have h2 : 2 ^ (k + 1) ≤ ℓ - 1 := by
      have := hℓ.two_le
      exact Nat.le_of_dvd (by omega) hdvd
    have h1 := succ_le_two_pow (k + 1)
    have hlt : ℓ - 1 < ℓ := by omega
    omega
  · rw [hord]
    exact Nat.Prime.not_prime_pow (by omega)

/-- **ARBITRARILY LARGE INVISIBLE PRIMES, in the denominator language:** for every
`B` there is an odd prime `ℓ > B` dividing **no** Lambert denominator of the
prime-restricted Lambert series. -/
theorem jsp87exists_invisible_prime (B : ℕ) :
    ∃ ℓ, B < ℓ ∧ ℓ.Prime ∧ ∀ p : ℕ, p.Prime → ¬ (ℓ ∣ 2 ^ p - 1) := by
  obtain ⟨ℓ, h1, h2, h3⟩ := jsp87exists_comp_order B
  exact ⟨ℓ, h1, h2, fun p hp => jsp87_notdvd_mer_of_comp_order ℓ p h2 hp h3⟩

/-- **SUMMARY OF ROUND 147.**  The prime `5` is invisible, so it never enters the
denominator tower of the prime-restricted series, while it enters the
unrestricted one at every level; there are arbitrarily large primes which
never enter the prime-restricted tower at all; and the truncation numerator
meets none of the visible denominators. -/
theorem jsp87_lambert_order_summary (N : ℕ) :
    Nat.Coprime (lambertDen (Finset.range N)) 5
      ∧ (5 ≤ N → 5 ∣ ∏ k ∈ Finset.range N, (2 ^ k - 1))
      ∧ Nat.Coprime (jsp87_lambertNumer N) (lambertDen (Finset.range N)) := by
  exact ⟨jsp87_lambertDen_coprime_five_range N,
    (jsp87_denominator_five_dichotomy N).2,
    jsp87_lambertNumer_coprime_den_of_order N⟩

end JSP87