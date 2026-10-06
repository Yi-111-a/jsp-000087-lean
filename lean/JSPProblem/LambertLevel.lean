/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertOrder
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# JSP-000087 : HOW DEEP EACH PRIME SITS IN THE LAMBERT DENOMINATORS

`JSPProblem/LambertOrder.lean` answered *which primes* occur in the clearing
denominator `lambertDen s = ∏_{p ∈ s, prime} (2 ^ p - 1)` of the
prime-restricted Lambert series, and it answered that question completely:

```
ℓ ∣ lambertDen s   ↔   ∃ p ∈ s, p prime ∧ jsp87Order2 ℓ = p ,
```

where `jsp87Order2 ℓ` is the multiplicative order of `2` modulo the prime `ℓ`.
Every question about the *support* of the tower is therefore closed.

This file asks the next question, which round 147 never asked: **how deep does
each prime sit in the tower?**  Support tells you *whether* `ℓ` occurs; it says
nothing about `ℓ ^ 2`, `ℓ ^ 3`, … .  The answer is governed by a *single
integer*, the order of `2` modulo a prime power:

```
jsp87Order (q ^ e) = orderOf (2 : ZMod (q ^ e)) .
```

Three results, in order of increasing depth.

## 1. The level ladder (`jsp87_lift_pow`, `jsp87_levelLadder`)

**THE LIFT.**  `q ^ e ∣ 2 ^ k - 1` forces `q ^ (e+1) ∣ 2 ^ (q * k) - 1`
(`jsp87_lift_pow`).  One level of divisibility is bought with one factor `q` in
the exponent.  Iterating (`jsp87_dvd_pow_mer_lift_iter`) and combining with
monotonicity of the order in the modulus (`jsp87Order_mono`) gives **THE LEVEL
LADDER** `jsp87_levelLadder`:

```
jsp87Order2 q  ∣  jsp87Order (q ^ (c+1))  ∣  q ^ c * jsp87Order2 q .
```

The order at every prime-power level `q ^ (c+1)` is a multiple of the order at
level `q` and divides `q ^ c` times that order.  The whole prime-power hierarchy
of the Lambert denominators is squeezed between two explicit integers.

## 2. THE WIEFERICH DICHOTOMY (`jsp87_lift_dichotomy`)

At the first step of the ladder there is **no choice**: for an odd prime `q`,

```
jsp87Order (q ^ 2) = jsp87Order2 q     (q is a *Wieferich* prime base 2)
                  ∨  jsp87Order (q ^ 2) = q * jsp87Order2 q .
```

(`jsp87_lift_dichotomy`.)  Indeed `jsp87Order2 q ∣ jsp87Order (q ^ 2)` by
monotonicity, and `jsp87Order (q ^ 2) ∣ q * jsp87Order2 q` by the lift, so the
quotient is a divisor of the prime `q`.

The two cases have opposite arithmetic content:

* **non-Wieferich** (`¬ jsp87Wieferich q`): `q ^ 2 ∣ 2 ^ k - 1 ↔ q * jsp87Order2 q ∣ k`.
  So `q` divides `2 ^ k - 1` *to the first power only* whenever `q ∤ k`
  (`jsp87_notdvd_mer_sq_of_genuine`).  The square is not free.
* **Wieferich**: `q ^ 2 ∣ 2 ^ k - 1 ↔ q ∣ 2 ^ k - 1` (`jsp87_dvd_mer_sq_of_weierich`).
  The square arrives **for free**, at exactly the levels where `q` occurs at all.

Combined with round 147's prime-index identification this gives the sharp form
`jsp87_dvd_mer_sq_of_prime_iff`:

```
q ^ 2 ∣ 2 ^ p - 1   ↔   jsp87Order2 q = p  ∧  jsp87Wieferich q      (p prime).
```

**THE PRICE OF A WIEFERICH PRIME OF PRIME ORDER.**  A Wieferich prime `q` whose
order of `2` is prime is exactly a prime whose *square* sits in the tower
(`jsp87_weierich_price`).

## 3. The clearing denominator at the square level

Rounds 37–39 used **pairwise coprimality** of the Lambert factors.  This is
exactly what is needed to lift the support statement to prime powers: `q` divides
*at most one* factor of `lambertDen s`, so

```
jsp87_lambertDen_dvd_pow_iff :  q ^ e ∣ lambertDen s  ↔  ∃ p ∈ s, p prime ∧ jsp87Order (q ^ e) = p
```

and in particular

```
jsp87_lambertDen_dvd_sq_iff_weierich :
    q ^ 2 ∣ lambertDen s  ↔  ∃ p ∈ s, p prime ∧ jsp87Order2 q = p ∧ jsp87Wieferich q .
```

**CONSEQUENCE.**  `3, 5, 7, 11, 73` are *not* Wieferich: at every prime `q` the
*visible* primes of the tower enter **to the first power only**, because their
square level `q ^ 2` carries an order which is not prime
(`jsp87_lambertDen_notdvd_q_of_prime_order`).  The order at the square level is
`q` times the order at `q` (`jsp87_genuine_of_prime_order`), and `q * p` is
never prime.

## Main results

* `jsp87Order`, `jsp87_dvd_mer_iff_order_dvd'`, `jsp87Order_mono` — the order of
  `2` modulo a general modulus, and its monotonicity in the modulus;
* `jsp87_lift_pow`, `jsp87_dvd_pow_mer_lift_iter`, `jsp87_levelLadder` —
  **the lift and the level ladder**;
* `jsp87Wieferich`, `jsp87_lift_dichotomy`, `jsp87_dvd_mer_sq_of_genuine`,
  `jsp87_dvd_mer_sq_of_weierich`, `jsp87_dvd_mer_sq_of_prime_iff` —
  **the Wieferich dichotomy** and the price of each branch;
* `jsp87_lambertDen_dvd_pow_iff`, `jsp87_lambertDen_dvd_sq_iff_weierich`,
  `jsp87_lambertDen_notdvd_sq_of_genuine`, `jsp87_lambertDen_notdvd_q_of_prime_order` —
  the clearing denominator at every prime-power level;
* `jsp87_dvd_mer_sq_three_iff`, …, `jsp87_denominator_nine_dichotomy` — the
  *unrestricted* tower at the square level, against the prime-restricted one.
-/

namespace JSP87

set_option maxHeartbeats 800000

/-! ## 0. Small private helpers -/

/-- The multiplicative order of `2` modulo an arbitrary modulus `m ≥ 2`.

For `m = q ^ e` this is the order at the *prime-power level* `q ^ e`. -/
noncomputable def jsp87Order (m : ℕ) : ℕ := orderOf (2 : ZMod m)

/-- `2` and `1` are different in `ℤ / m ℤ` as soon as `2 ≤ m`. -/
private theorem jsp87_two_ne_one' (m : ℕ) (hm : 2 ≤ m) : (2 : ZMod m) ≠ 1 := by
  intro h
  have hn : ((2 : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    rw [show ((2 : ℕ) : ZMod m) = (2 : ZMod m) from rfl, Nat.cast_one, h]
  have hcc : ((2 - 1 : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by norm_num
  have hz : ((2 - 1 : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_sub (by norm_num), hn, sub_self]
  have hd := (ZMod.natCast_eq_zero_iff (a := 1) (b := m)).mp (hcc ▸ hz)
  have hle : m ≤ 1 := Nat.le_of_dvd (by norm_num) hd
  omega

/-- The order of `2` modulo `m` is never `1` when `2 ≤ m`. -/
private theorem jsp87Order_ne_one' (m : ℕ) (hm : 2 ≤ m) : jsp87Order m ≠ 1 := by
  intro hh
  have heq : (2 : ZMod m) = 1 := by
    rw [← orderOf_eq_one_iff]
    exact hh
  exact (jsp87_two_ne_one' m hm heq).elim

/-- If `x ^ 2 = 0` in a commutative semiring then `(1 + x) ^ n = 1 + n * x`.

This is the *whole* of the lifting argument: a nilpotent perturbation of `1` is
picked up by the exponent linearly. -/
private theorem jsp87_one_add_sq_pow {R : Type*} [CommSemiring R] (x : R) (hx : x * x = 0)
    (n : ℕ) : (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hcast : ((m + 1 : ℕ) : R) = (m : R) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, mul_assoc, hx, mul_zero,
      add_zero, hcast]
    ring

/-- Powers of a single base: `q ^ m ∣ q ^ n` as soon as `m ≤ n`. -/
private theorem jsp87_pow_dvd_pow {q m n : ℕ} (h : m ≤ n) : q ^ m ∣ q ^ n := by
  obtain ⟨c, hc⟩ : ∃ c, n = m + c := ⟨n - m, by omega⟩
  rw [hc]
  have key : (q ^ m * q ^ c : ℕ) = q ^ (m + c) := (Nat.pow_add q m c).symm
  rw [← key]
  exact ⟨q ^ c, rfl⟩

/-- `1 ≤ e` forces `ℓ ∣ ℓ ^ e`. -/
private theorem jsp87_self_dvd_pow {ℓ e : ℕ} (he : 1 ≤ e) : ℓ ∣ ℓ ^ e := by
  have h := jsp87_pow_dvd_pow (q := ℓ) (m := 1) (n := e) he
  rw [Nat.pow_one] at h
  exact h

/-- `2 ≤ q` and `1 ≤ e` force `2 ≤ q ^ e`. -/
private theorem jsp87_pow_two_le (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) : 2 ≤ q ^ e := by
  obtain ⟨c, rfl⟩ : ∃ c, e = 1 + c := ⟨e - 1, by omega⟩
  rw [Nat.pow_add q 1 c, Nat.pow_one]
  have h1 : q * 1 ≤ q * q ^ c :=
    Nat.mul_le_mul_left q (Nat.succ_le_of_lt (Nat.pow_pos (a := q) (n := c) (by omega)))
  omega

/-- A prime not dividing `x` is coprime to `x`. -/
private theorem jsp87_coprime_of_not_dvd {ℓ x : ℕ} (hℓ : ℓ.Prime) (h : ¬ (ℓ ∣ x)) :
    Nat.Coprime ℓ x := by
  refine (Nat.coprime_iff_gcd_eq_one).mpr ?_
  by_cases hc : Nat.gcd ℓ x = 1
  · exact hc
  · push Not at hc
    obtain ⟨d, hd, hdℓ⟩ := (Nat.ne_one_iff_exists_prime_dvd (n := Nat.gcd ℓ x)).mp hc
    have h1 : d ∣ x := Nat.dvd_trans hdℓ (Nat.gcd_dvd_right ℓ x)
    have h2 : d ∣ ℓ := Nat.dvd_trans hdℓ (Nat.gcd_dvd_left ℓ x)
    have h3 := hd.two_le
    rcases (Nat.dvd_prime hℓ).mp h2 with hd1 | hd2
    · omega
    · rw [hd2] at h1
      exact (h h1).elim

/-- A prime dividing a product of Lambert factors divides one of them. -/
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
      have h2 : ℓ ∣ ∏ p ∈ s, f p := hcop.dvd_of_dvd_mul_left hdvd
      obtain ⟨p, hp, h3⟩ := ih h2
      exact ⟨p, by rw [Finset.mem_insert]; exact Or.inr hp, h3⟩

/-- If no prime divisor of `ℓ` divides any factor, then `ℓ` is coprime to the
whole product. -/
private theorem jsp87_coprime_prod_of_notdvd {ℓ : ℕ} (hℓ : ℓ.Prime) {s : Finset ℕ}
    {f : ℕ → ℕ} (h : ∀ q ∈ s, ¬ (ℓ ∣ f q)) : Nat.Coprime ℓ (∏ q ∈ s, f q) := by
  classical
  refine (Nat.coprime_iff_gcd_eq_one).mpr ?_
  by_cases hc : Nat.gcd ℓ (∏ q ∈ s, f q) = 1
  · exact hc
  · push Not at hc
    obtain ⟨d, hd, hdℓ⟩ :=
      (Nat.ne_one_iff_exists_prime_dvd (n := Nat.gcd ℓ (∏ q ∈ s, f q))).mp hc
    have h1 : d ∣ ∏ q ∈ s, f q := Nat.dvd_trans hdℓ (Nat.gcd_dvd_right _ _)
    have h2 : d ∣ ℓ := Nat.dvd_trans hdℓ (Nat.gcd_dvd_left _ _)
    have h3 := hd.two_le
    obtain ⟨q, hq, hdq⟩ := jsp87_dvd_prod_of_dvd hd h1
    rcases (Nat.dvd_prime hℓ).mp h2 with hd1 | hd2
    · omega
    · rw [hd2] at hdq
      exact (h q hq hdq).elim

/-- **Two Lambert factors at distinct prime levels share no prime divisor.** -/
private theorem jsp87_level_unique {ℓ p q : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hq : q.Prime)
    (h1 : ℓ ∣ 2 ^ p - 1) (h2 : ℓ ∣ 2 ^ q - 1) : p = q := by
  by_contra hne
  have hcop := coprime_lambert_den_of_distinct_prime hp hq hne
  have hgd : ℓ ∣ Nat.gcd (2 ^ p - 1) (2 ^ q - 1) := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at hgd
  have hle : ℓ ≤ 1 := Nat.le_of_dvd (by norm_num) hgd
  have h2le := hℓ.two_le
  omega

/-! ## 1. The order of `2` modulo a general modulus, and its monotonicity -/

/-- `jsp87Order2 ℓ` is the order modulo the prime `ℓ`. -/
theorem jsp87Order2_eq_order (ℓ : ℕ) : jsp87Order ℓ = jsp87Order2 ℓ := rfl

/-- **THE GENERAL IDENTIFICATION**: `m ∣ 2 ^ k - 1` iff `jsp87Order m ∣ k`, for
*any* modulus `m ≥ 2` — not only for primes. -/
theorem jsp87_dvd_mer_iff_order_dvd' (m k : ℕ) :
    m ∣ 2 ^ k - 1 ↔ jsp87Order m ∣ k := by
  rw [jsp87_mer_iff_pow_one]
  exact (orderOf_dvd_iff_pow_eq_one (x := (2 : ZMod m)) (n := k)).symm

/-- **MONOTONICITY OF THE ORDER.**  If `d ∣ e` and `2 ≤ d`, then the order of `2`
modulo `d` divides the order of `2` modulo `e`. -/
theorem jsp87Order_mono {d e : ℕ} (h : d ∣ e) :
    jsp87Order d ∣ jsp87Order e := by
  have h1 : e ∣ 2 ^ jsp87Order e - 1 :=
    (jsp87_dvd_mer_iff_order_dvd' e (jsp87Order e)).mpr dvd_rfl
  have h2 : d ∣ 2 ^ jsp87Order e - 1 := Nat.dvd_trans h h1
  exact (jsp87_dvd_mer_iff_order_dvd' d (jsp87Order e)).mp h2

/-! ## 2. THE LIFT -/

/-- **THE LIFT.**  If `q ^ e ∣ 2 ^ k - 1` with `e ≥ 1`, then
`q ^ (e+1) ∣ 2 ^ (q * k) - 1`: one level of divisibility is bought with one
factor `q` in the exponent.

The proof is nilpotence: `2 ^ k - 1` is a multiple of `q ^ e`, so as an element
of `ℤ / q ^ (e+1) ℤ` it is `q ^ e · u`, whose square is `0` because
`2 e ≥ e + 1`; raising `1 + q ^ e u` to the `q`-th power gives
`1 + q · q ^ e u = 1`. -/
theorem jsp87_lift_pow (q k e : ℕ) (he : 1 ≤ e) (hd : q ^ e ∣ 2 ^ k - 1) :
    q ^ (e + 1) ∣ 2 ^ (q * k) - 1 := by
  obtain ⟨u, hu⟩ := hd
  have hpos : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.pow_pos (a := 2) (n := k) (by omega))
  have hk1 : (2 ^ k : ℕ) = 1 + (q ^ e * u : ℕ) := by omega
  have hqq : ((q ^ (2 * e) : ℕ) : ZMod (q ^ (e + 1))) = 0 :=
    (ZMod.natCast_eq_zero_iff (q ^ (2 * e)) (q ^ (e + 1))).mpr (jsp87_pow_dvd_pow (by omega))
  have hzero : ((q ^ (e + 1) : ℕ) : ZMod (q ^ (e + 1))) = 0 :=
    (ZMod.natCast_eq_zero_iff (q ^ (e + 1)) (q ^ (e + 1))).mpr dvd_rfl
  have hxk : ((2 ^ k - 1 : ℕ) : ZMod (q ^ (e + 1))) *
      ((2 ^ k - 1 : ℕ) : ZMod (q ^ (e + 1))) = 0 := by
    have key : ((2 ^ k - 1 : ℕ) : ZMod (q ^ (e + 1))) *
          ((2 ^ k - 1 : ℕ) : ZMod (q ^ (e + 1)))
        = (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1)))) *
          (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1)))) := by rw [hu]
    rw [key]
    calc (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1)))) * (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1))))
        = (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1)))) ^ 2 := by rw [pow_two]
      _ = ((q ^ (2 * e) : ℕ) : ZMod (q ^ (e + 1))) *
          ((u : ℕ) : ZMod (q ^ (e + 1))) * ((u : ℕ) : ZMod (q ^ (e + 1))) := by
            push_cast
            ring_nf
      _ = 0 := by rw [hqq]; ring
  have hq : (2 : ZMod (q ^ (e + 1))) ^ (q * k) = 1 := by
    have hpow : (2 : ZMod (q ^ (e + 1))) ^ k = ((2 ^ k : ℕ) : ZMod (q ^ (e + 1))) := by
      rw [Nat.cast_pow]; rfl
    have hu' : ((2 ^ k - 1 : ℕ) : ZMod (q ^ (e + 1)))
        = (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1)))) := by rw [hu]
    have hmain : ((2 ^ k : ℕ) : ZMod (q ^ (e + 1)))
        = 1 + (((2 ^ k - 1 : ℕ) : ZMod (q ^ (e + 1)))) := by
      have hab : ((2 ^ k : ℕ) : ZMod (q ^ (e + 1)))
          = 1 + (((q ^ e * u : ℕ) : ZMod (q ^ (e + 1)))) := by
        have h3 := congrArg (fun z : ℕ => (z : ZMod (q ^ (e + 1)))) hk1
        rw [Nat.cast_add, Nat.cast_one] at h3
        exact h3
      rw [hab, hu']
    have hid : ((q ^ (e + 1) : ℕ) : ZMod (q ^ (e + 1)))
        = (q : ZMod (q ^ (e + 1))) * ((q ^ e : ℕ) : ZMod (q ^ (e + 1))) := by
      rw [Nat.cast_pow, Nat.cast_pow, pow_succ]
      ring
    rw [Nat.mul_comm q k, pow_mul, hpow, hmain, jsp87_one_add_sq_pow _ hxk, hu',
      Nat.cast_mul, ← mul_assoc, ← hid, hzero]
    ring
  exact (jsp87_mer_iff_pow_one (q ^ (e + 1)) (q * k)).mpr hq

/-! ## 3. THE LEVEL LADDER -/

/-- **THE LEVEL LADDER, LEFT HALF.**  The order of `2` modulo `q ^ (c+1)` is a
multiple of the order modulo `q`. -/
theorem jsp87Order_pow_dvd_order (q c : ℕ) (_hq : 2 ≤ q) :
    jsp87Order2 q ∣ jsp87Order (q ^ (c + 1)) := by
  have h : q ∣ q ^ (c + 1) := by
    rw [show (q ^ (c + 1) : ℕ) = q * q ^ c from
      by rw [Nat.pow_add q c 1, Nat.pow_one, mul_comm]]
    exact dvd_mul_right q _
  exact jsp87Order_mono h

/-- **ITERATED LIFT.**  For every odd prime `q` and every `c ≥ 0`,
`q ^ (c+1) ∣ 2 ^ (q ^ c * jsp87Order2 q) - 1`. -/
theorem jsp87_dvd_pow_mer_lift_iter (q c : ℕ) (hq : q.Prime) (_hodd : q ≠ 2) :
    q ^ (c + 1) ∣ 2 ^ (q ^ c * jsp87Order2 q) - 1 := by
  induction c with
  | zero =>
    have hq0 : 2 ≤ q := hq.two_le
    rw [Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.pow_one]
    exact (jsp87_dvd_mer_iff_order_dvd' q (jsp87Order2 q)).mpr dvd_rfl
  | succ m ih =>
    have hm : 1 ≤ m + 1 := by omega
    have hstep := jsp87_lift_pow q (q ^ m * jsp87Order2 q) (m + 1) hm ih
    have hpw : q ^ (Nat.succ m + 1) = q ^ (m + 1 + 1) := by rfl
    rw [hpw] at hstep
    have hq : q ^ Nat.succ m = q ^ m * q := pow_succ q m
    rw [hq]
    have h3 : q * (q ^ m * jsp87Order2 q) = q ^ m * q * jsp87Order2 q := by ring
    rw [h3] at hstep
    exact hstep

/-- **THE LEVEL LADDER.**  For an odd prime `q` and every `c ≥ 0` the order of
`2` modulo `q ^ (c+1)` is squeezed between two explicit integers:

```
jsp87Order2 q  ∣  jsp87Order (q ^ (c+1))  ∣  q ^ c * jsp87Order2 q .
```

The left half is monotonicity; the right half is the iterated lift. -/
theorem jsp87_levelLadder (q c : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    jsp87Order2 q ∣ jsp87Order (q ^ (c + 1)) ∧
      jsp87Order (q ^ (c + 1)) ∣ q ^ c * jsp87Order2 q := by
  refine ⟨jsp87Order_pow_dvd_order q c hq.two_le, ?_⟩
  exact (jsp87_dvd_mer_iff_order_dvd' (q ^ (c + 1)) (q ^ c * jsp87Order2 q)).mp
    (jsp87_dvd_pow_mer_lift_iter q c hq hodd)

/-- The order at a prime-power level is never `1`. -/
theorem jsp87Order_pow_ne_one (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) :
    jsp87Order (q ^ e) ≠ 1 := jsp87Order_ne_one' (q ^ e) (jsp87_pow_two_le q e hq he)

/-- The left half of the level ladder, in the `e` convention. -/
theorem jsp87Order2_dvd_order_pow (q e : ℕ) (hq : 2 ≤ q) (he : 1 ≤ e) :
    jsp87Order2 q ∣ jsp87Order (q ^ e) := by
  have hsub : e - 1 + 1 = e := by omega
  rw [← hsub]
  exact jsp87Order_pow_dvd_order q (e - 1) hq

/-- At a prime-power level the order is at least `2`. -/
theorem jsp87Order_pow_two_le (q e : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (he : 1 ≤ e) :
    2 ≤ jsp87Order (q ^ e) := by
  have h2 := jsp87Order2_two_le q hq hodd
  have hsub : e - 1 + 1 = e := by omega
  have hd := jsp87_dvd_pow_mer_lift_iter q (e - 1) hq hodd
  rw [hsub] at hd
  have hk : (2 : ZMod (q ^ e)) ^ (q ^ (e - 1) * jsp87Order2 q) = 1 :=
    (jsp87_mer_iff_pow_one (q ^ e) (q ^ (e - 1) * jsp87Order2 q)).mp hd
  obtain ⟨c, hc⟩ := jsp87Order2_dvd_order_pow q e hq.two_le he
  by_cases hz : jsp87Order (q ^ e) = 0
  · have hz0 : ∀ n : ℕ, 0 < n → (2 : ZMod (q ^ e)) ^ n ≠ 1 :=
      (orderOf_eq_zero_iff' (x := (2 : ZMod (q ^ e)))).mp hz
    exact (hz0 _ (Nat.mul_pos
      (Nat.pow_pos (a := q) (n := e - 1) (by have := hq.two_le; omega)) (by omega)) hk).elim
  · have hc0 : 0 < c := by
      by_contra hn
      have hcz : c = 0 := by omega
      rw [hcz, Nat.mul_zero] at hc
      exact hz hc
    have hj : jsp87Order2 q ≤ jsp87Order (q ^ e) := by
      have hm : jsp87Order2 q * 1 ≤ jsp87Order2 q * c :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hc0)
      rw [hc]
      omega
    omega

/-! ## 4. THE WIEFERICH DICHOTOMY -/

/-- **THE WIEFERICH DICHOTOMY.**  For an odd prime `q` there is no third
possibility: the order of `2` modulo `q ^ 2` either *does not grow* (`q` is a
Wieferich prime base 2) or it grows by exactly the factor `q`. -/
theorem jsp87_lift_dichotomy (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    jsp87Order (q ^ 2) = jsp87Order2 q ∨ jsp87Order (q ^ 2) = q * jsp87Order2 q := by
  have hk : 2 ≤ jsp87Order2 q := jsp87Order2_two_le q hq hodd
  have hk0 : 0 < jsp87Order2 q := by omega
  obtain ⟨c, hc⟩ := jsp87Order_pow_dvd_order q 1 hq.two_le
  have hq1 : q ^ 1 ∣ 2 ^ jsp87Order2 q - 1 := by
    rw [Nat.pow_one]
    exact (jsp87_dvd_mer_iff_order_dvd' q (jsp87Order2 q)).mpr dvd_rfl
  obtain ⟨d, hd⟩ :=
    (jsp87_dvd_mer_iff_order_dvd' (q ^ 2) (q * jsp87Order2 q)).mp
      (jsp87_lift_pow q (jsp87Order2 q) 1 (by norm_num) hq1)
  have hcd : c * d = q := Nat.mul_right_cancel hk0 (by
    calc c * d * jsp87Order2 q = jsp87Order2 q * c * d := by ring
      _ = (jsp87Order (q ^ 2)) * d := by rw [hc]
      _ = q * jsp87Order2 q := hd.symm)
  have hcd' : c ∣ q := ⟨d, hcd.symm⟩
  rcases (Nat.dvd_prime hq).mp hcd' with rfl | rfl
  · left; simpa using hc
  · right; simpa [Nat.mul_comm] using hc

/-- A prime `q` is **Wieferich** (base 2) when the order of `2` does not grow
when the modulus is lifted from `q` to `q ^ 2`. -/
def jsp87Wieferich (q : ℕ) : Prop := jsp87Order (q ^ 2) = jsp87Order2 q

theorem jsp87_wieferich_iff (q : ℕ) :
    jsp87Wieferich q ↔ jsp87Order (q ^ 2) = jsp87Order2 q := Iff.rfl

/-- **The two branches are complementary**: a prime is either Wieferich or its
order at `q ^ 2` is `q` times the order at `q`. -/
theorem jsp87_genuine_iff (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    ¬ jsp87Wieferich q ↔ jsp87Order (q ^ 2) = q * jsp87Order2 q := by
  rw [jsp87_wieferich_iff]
  constructor
  · intro h
    rcases jsp87_lift_dichotomy q hq hodd with h1 | h1
    · exact absurd h1 h
    · exact h1
  · intro h
    have hk0 : 0 < jsp87Order2 q := by have := jsp87Order2_two_le q hq hodd; omega
    have hone : (1 : ℕ) * jsp87Order2 q = jsp87Order2 q := Nat.one_mul _
    rcases jsp87_lift_dichotomy q hq hodd with h1 | h1
    · rw [h1] at h
      have hq1 : q = 1 := Nat.mul_right_cancel hk0 (by rw [hone]; exact h.symm)
      have := hq.two_le
      omega
    · have hne : q * jsp87Order2 q ≠ jsp87Order2 q := by
        intro hh
        have hq1 : q = 1 := Nat.mul_right_cancel hk0 (by rw [hone]; exact hh)
        have := hq.two_le
        omega
      intro heq
      exact hne (h1.symm.trans heq)

/-- `q ^ 2 ∣ 2 ^ k - 1` iff the order of `2` modulo `q ^ 2` divides `k`. -/
theorem jsp87_dvd_sq_iff_order_sq (q k : ℕ) (_hq : 2 ≤ q) :
    q ^ 2 ∣ 2 ^ k - 1 ↔ jsp87Order (q ^ 2) ∣ k :=
  jsp87_dvd_mer_iff_order_dvd' (q ^ 2) k

/-- **NON-WIEFERICH: THE SQUARE IS EXPENSIVE.**  At a prime `q` that is not
Wieferich, `q ^ 2` divides `2 ^ k - 1` exactly at the exponents that are
*multiples of* `q` times the order of `2` modulo `q`. -/
theorem jsp87_dvd_mer_sq_of_genuine (q k : ℕ) (hq : q.Prime) (hodd : q ≠ 2)
    (hg : ¬ jsp87Wieferich q) : q ^ 2 ∣ 2 ^ k - 1 ↔ q * jsp87Order2 q ∣ k := by
  rw [jsp87_genuine_iff q hq hodd] at hg
  rw [jsp87_dvd_sq_iff_order_sq q k hq.two_le, hg]

/-- **WIEFERICH: THE SQUARE IS FREE.**  At a Wieferich prime `q`, `q ^ 2` divides
`2 ^ k - 1` exactly when `q` does. -/
theorem jsp87_dvd_mer_sq_of_weierich (q k : ℕ) (hq : q.Prime) (_hodd : q ≠ 2)
    (hw : jsp87Wieferich q) : q ^ 2 ∣ 2 ^ k - 1 ↔ q ∣ 2 ^ k - 1 := by
  have hw' : jsp87Order (q ^ 2) = jsp87Order2 q := (jsp87_wieferich_iff q).mp hw
  rw [jsp87_dvd_sq_iff_order_sq q k hq.two_le, hw']
  exact (jsp87_dvd_mer_iff_order_dvd q k).symm

/-- **A PRIME THAT IS NOT WIEFERICH OCCURS ONLY TO THE FIRST POWER.**  If `q`
is not Wieferich, `q` divides `2 ^ k - 1` and `q` does not divide the exponent
`k`, then `q ^ 2` does not divide `2 ^ k - 1`. -/
theorem jsp87_notdvd_mer_sq_of_genuine (q k : ℕ) (hq : q.Prime) (hodd : q ≠ 2)
    (hg : ¬ jsp87Wieferich q) (_h1 : q ∣ 2 ^ k - 1) (h2 : ¬ (q ∣ k)) :
    ¬ (q ^ 2 ∣ 2 ^ k - 1) := by
  intro h
  have h3 : q * jsp87Order2 q ∣ k := (jsp87_dvd_mer_sq_of_genuine q k hq hodd hg).mp h
  have h4 : q ∣ q * jsp87Order2 q := dvd_mul_right q _
  exact (h2 (Nat.dvd_trans h4 h3)).elim

/-- **THE SQUARE AT A PRIME LEVEL.**  For an odd prime `q` and a prime `p`,

```
q ^ 2 ∣ 2 ^ p - 1   ↔   jsp87Order2 q = p  ∧  jsp87Wieferich q .
```

A prime `q` sits in the prime-restricted Lambert tower **with multiplicity two**
only if it is Wieferich *and* its order of `2` is that prime. -/
theorem jsp87_dvd_mer_sq_of_prime_iff (q p : ℕ) (hq : q.Prime) (_hodd : q ≠ 2)
    (hp : p.Prime) :
    q ^ 2 ∣ 2 ^ p - 1 ↔ (jsp87Order2 q = p ∧ jsp87Wieferich q) := by
  rw [jsp87_dvd_sq_iff_order_sq q p hq.two_le]
  constructor
  · intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h2
    · exact absurd h1 (jsp87Order_pow_ne_one q 2 hq.two_le (by omega))
    · have hc0 := jsp87Order_pow_dvd_order q 1 hq.two_le
      have hc' : jsp87Order2 q ∣ p := by
        rw [← h2]
        exact hc0
      rcases (Nat.dvd_prime hp).mp hc' with hc1 | hc2
      · exact absurd hc1 (jsp87Order_ne_one' q hq.two_le)
      · refine ⟨hc2, ?_⟩
        show jsp87Order (q ^ 2) = jsp87Order2 q
        exact h2.trans hc2.symm
  · rintro ⟨ho, hw⟩
    rw [jsp87_wieferich_iff] at hw
    show jsp87Order (q ^ 2) ∣ p
    rw [hw, ho]

/-- **THE PRICE OF A WIEFERICH PRIME OF PRIME ORDER.** -/
theorem jsp87_weierich_price (q p : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (hp : p.Prime)
    (hw : jsp87Wieferich q) (ho : jsp87Order2 q = p) : q ^ 2 ∣ 2 ^ p - 1 :=
  (jsp87_dvd_mer_sq_of_prime_iff q p hq hodd hp).mpr ⟨ho, hw⟩

/-! ## 5. The clearing denominator at every prime-power level -/

/-- The prime `ℓ` divides `lambertDen s` iff it divides one of the Lambert
factors. -/
private theorem jsp87_lambertDen_dvd_one_iff (ℓ : ℕ) (hℓ : ℓ.Prime) (s : Finset ℕ) :
    ℓ ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ ℓ ∣ 2 ^ p - 1 := by
  constructor
  · intro h
    obtain ⟨p, hp, hd⟩ := jsp87_dvd_prod_of_dvd hℓ (by rw [lambertDen_eq] at h; exact h)
    split_ifs at hd
    · exact ⟨p, hp, by assumption, hd⟩
    · have hle := hℓ.two_le
      exact absurd hd (by rw [Nat.dvd_one]; omega)
  · rintro ⟨p, hp, hpp, hd⟩
    rw [lambertDen_eq]
    have hdv : (if p.Prime then 2 ^ p - 1 else 1)
        ∣ ∏ q ∈ s, (if q.Prime then 2 ^ q - 1 else 1) :=
      Finset.dvd_prod_of_mem (f := fun q : ℕ => if q.Prime then 2 ^ q - 1 else 1) hp
    split_ifs at hdv
    exact hd.trans hdv

/-- **THE CLEARING DENOMINATOR AT EVERY PRIME-POWER LEVEL (raw form).** -/
private theorem jsp87_lambertDen_dvd_pow_gen (ℓ e : ℕ) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (s : Finset ℕ) :
    ℓ ^ e ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ ℓ ^ e ∣ 2 ^ p - 1 := by
  constructor
  · intro h
    have h1 : ℓ ∣ lambertDen s := Nat.dvd_trans (jsp87_self_dvd_pow he) h
    obtain ⟨p, hp, hpp, hlp⟩ := (jsp87_lambertDen_dvd_one_iff ℓ hℓ s).mp h1
    have hnot : ∀ q ∈ s.erase p, ¬ (ℓ ∣ (if q.Prime then 2 ^ q - 1 else 1)) := by
      intro q hq hd
      have hmem : q ∈ s := Finset.mem_of_mem_erase hq
      have hne : q ≠ p := by
        intro heq
        have hq2 : p ∈ s.erase p := heq ▸ hq
        have hm := Finset.mem_erase.mp hq2
        exact hm.1 rfl
      split_ifs at hd
      · exact absurd (jsp87_level_unique hℓ hpp (by assumption) hlp hd).symm hne
      · have hle := hℓ.two_le
        exact absurd hd (by rw [Nat.dvd_one]; omega)
    have hcop : Nat.Coprime ℓ (∏ q ∈ s.erase p, (if q.Prime then 2 ^ q - 1 else 1)) :=
      jsp87_coprime_prod_of_notdvd hℓ hnot
    have hcop' : Nat.Coprime (ℓ ^ e)
        (∏ q ∈ s.erase p, (if q.Prime then 2 ^ q - 1 else 1)) :=
      (Nat.coprime_pow_left_iff (show 0 < e by omega) ℓ _).mpr hcop
    have key : (if p.Prime then 2 ^ p - 1 else 1) = 2 ^ p - 1 := by
      simp only [hpp, ite_true]
    have hmul : lambertDen s
        = (2 ^ p - 1) * ∏ q ∈ s.erase p, (if q.Prime then 2 ^ q - 1 else 1) := by
      rw [lambertDen_eq]
      have hme := Finset.mul_prod_erase s
        (fun q : ℕ => if q.Prime then 2 ^ q - 1 else 1) hp
      rw [← hme, key]
    have h2 : ℓ ^ e ∣ (2 ^ p - 1)
        * ∏ q ∈ s.erase p, (if q.Prime then 2 ^ q - 1 else 1) := by
      rw [← hmul]; exact h
    exact ⟨p, hp, hpp, (hcop'.dvd_mul_right).mp h2⟩
  · rintro ⟨p, hp, hpp, hd⟩
    rw [lambertDen_eq]
    have hdv : (if p.Prime then 2 ^ p - 1 else 1)
        ∣ ∏ q ∈ s, (if q.Prime then 2 ^ q - 1 else 1) :=
      Finset.dvd_prod_of_mem (f := fun q : ℕ => if q.Prime then 2 ^ q - 1 else 1) hp
    split_ifs at hdv
    exact hd.trans hdv

/-- **THE CLEARING DENOMINATOR AT EVERY PRIME-POWER LEVEL.**  `q ^ e` divides
`lambertDen s` iff some prime level `p ∈ s` satisfies `jsp87Order (q ^ e) = p`:
the entire prime-power structure of the tower is read off from the orders. -/
theorem jsp87_lambertDen_dvd_pow_iff (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (s : Finset ℕ) :
    q ^ e ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ jsp87Order (q ^ e) = p := by
  rw [jsp87_lambertDen_dvd_pow_gen q e hq he s]
  constructor
  · rintro ⟨p, hp, hpp, hd⟩
    have h1 : jsp87Order (q ^ e) ∣ p :=
      (jsp87_dvd_mer_iff_order_dvd' (q ^ e) p).mp hd
    refine ⟨p, hp, hpp, ?_⟩
    rcases (Nat.dvd_prime hpp).mp h1 with h2 | h2
    · exact absurd h2 (jsp87Order_pow_ne_one q e hq.two_le he)
    · exact h2
  · rintro ⟨p, hp, hpp, ho⟩
    refine ⟨p, hp, hpp, ?_⟩
    rw [← ho]
    exact (jsp87_dvd_mer_iff_order_dvd' (q ^ e) (jsp87Order (q ^ e))).mpr
      (Nat.dvd_refl _)

/-- **THE CLEARING DENOMINATOR AT THE SQUARE LEVEL.**  `q ^ 2` divides
`lambertDen s` iff some prime level `p ∈ s` has `jsp87Order2 q = p` **and** `q`
is Wieferich. -/
theorem jsp87_lambertDen_dvd_sq_iff_weierich (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2)
    (s : Finset ℕ) :
    q ^ 2 ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ jsp87Order2 q = p ∧ jsp87Wieferich q := by
  rw [jsp87_lambertDen_dvd_pow_gen q 2 hq (by omega) s]
  constructor
  · rintro ⟨p, hp, hpp, hd⟩
    have hd' := (jsp87_dvd_mer_sq_of_prime_iff q p hq hodd hpp).mp hd
    exact ⟨p, hp, hpp, hd'.1, hd'.2⟩
  · rintro ⟨p, hp, hpp, ho, hw⟩
    exact ⟨p, hp, hpp, (jsp87_dvd_mer_sq_of_prime_iff q p hq hodd hpp).mpr ⟨ho, hw⟩⟩

/-- **A NON-WIEFERICH PRIME NEVER DIVIDES THE CLEARING DENOMINATOR WITH
MULTIPLICITY `2`.** -/
theorem jsp87_lambertDen_notdvd_sq_of_genuine (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2)
    (hg : ¬ jsp87Wieferich q) (s : Finset ℕ) : ¬ (q ^ 2 ∣ lambertDen s) := by
  intro hd
  obtain ⟨p, hp, hpp, ho, hw⟩ :=
    (jsp87_lambertDen_dvd_sq_iff_weierich q hq hodd s).mp hd
  exact hg hw

/-- **INVISIBILITY AT EVERY DEPTH.**  A prime `q` whose order of `2` is composite
divides no Lambert denominator of the prime-restricted series **to any
multiplicity**: `q ^ e ∤ lambertDen s` for every `e ≥ 1` and every `s`. -/
theorem jsp87_lambertDen_notdvd_pow_of_comp_order (q : ℕ) (hq : q.Prime)
    (hc : ¬ (jsp87Order2 q).Prime) (e : ℕ) (he : 1 ≤ e) (s : Finset ℕ) :
    ¬ (q ^ e ∣ lambertDen s) := by
  intro hd
  obtain ⟨p, hp, hpp, ho⟩ := (jsp87_lambertDen_dvd_pow_iff q e hq he s).mp hd
  have hc' := jsp87Order2_dvd_order_pow q e hq.two_le he
  rw [ho] at hc'
  rcases (Nat.dvd_prime hpp).mp hc' with hc1 | hc2
  · exact absurd hc1 (jsp87Order_ne_one' q hq.two_le)
  · exact hc (hc2 ▸ hpp)

/-! ## 6. Computed levels -/

/-- The dichotomy has only one branch when the order `r` of `2` modulo `q`
fails to lift: then the order at `q ^ 2` is exactly `q * r`. -/
private theorem jsp87_lift_choice (q r : ℕ) (hq : q.Prime) (hodd : q ≠ 2)
    (hr : jsp87Order2 q = r) (hnot : ¬ (q ^ 2 ∣ 2 ^ r - 1)) : jsp87Order (q ^ 2) = q * r := by
  rcases jsp87_lift_dichotomy q hq hodd with h1 | h1
  · exfalso
    have h2 : jsp87Order (q ^ 2) = r := by rw [h1]; exact hr
    exact hnot ((jsp87_dvd_sq_iff_order_sq q r hq.two_le).mpr (by rw [h2]))
  · rw [hr] at h1
    exact h1

/-- `ord_9 2 = 6`: the order of `2` modulo `9` is `3 · 2`, so `3` is **not**
Wieferich. -/
theorem jsp87Order_nine : jsp87Order 9 = 6 :=
  jsp87_lift_choice 3 2 (by norm_num) (by norm_num) jsp87Order2_three (by norm_num)

/-- `ord_25 2 = 20`, so `5` is **not** Wieferich. -/
theorem jsp87Order_twenty_five : jsp87Order 25 = 20 :=
  jsp87_lift_choice 5 4 (by norm_num) (by norm_num) jsp87Order2_five (by norm_num)

/-- `ord_49 2 = 21`, so `7` is **not** Wieferich. -/
theorem jsp87Order_forty_nine : jsp87Order 49 = 21 :=
  jsp87_lift_choice 7 3 (by norm_num) (by norm_num) jsp87Order2_seven (by norm_num)

/-- `ord_121 2 = 110`, so `11` is **not** Wieferich. -/
theorem jsp87Order_one_twenty_one : jsp87Order 121 = 110 :=
  jsp87_lift_choice 11 10 (by norm_num) (by norm_num) jsp87Order2_eleven (by norm_num)

/-- `ord_73² 2 = 657`, so `73` is **not** Wieferich. -/
theorem jsp87Order_fifty_three_squared : jsp87Order 5329 = 657 :=
  jsp87_lift_choice 73 9 (by norm_num) (by norm_num) jsp87Order2_seventythree (by norm_num)

/-- The prime `3` is not Wieferich. -/
theorem jsp87Wieferich_three_false : ¬ jsp87Wieferich 3 := by
  rw [jsp87_wieferich_iff]
  have h3 : (3 : ℕ) ^ 2 = 9 := by norm_num
  rw [h3, jsp87Order_nine, jsp87Order2_three]
  norm_num

/-- The prime `5` is not Wieferich. -/
theorem jsp87Wieferich_five_false : ¬ jsp87Wieferich 5 := by
  rw [jsp87_wieferich_iff]
  have h5 : (5 : ℕ) ^ 2 = 25 := by norm_num
  rw [h5, jsp87Order_twenty_five, jsp87Order2_five]
  norm_num

/-- The prime `7` is not Wieferich. -/
theorem jsp87Wieferich_seven_false : ¬ jsp87Wieferich 7 := by
  rw [jsp87_wieferich_iff]
  have h7 : (7 : ℕ) ^ 2 = 49 := by norm_num
  rw [h7, jsp87Order_forty_nine, jsp87Order2_seven]
  norm_num

/-- The prime `11` is not Wieferich. -/
theorem jsp87Wieferich_eleven_false : ¬ jsp87Wieferich 11 := by
  rw [jsp87_wieferich_iff]
  have h11 : (11 : ℕ) ^ 2 = 121 := by norm_num
  rw [h11, jsp87Order_one_twenty_one, jsp87Order2_eleven]
  norm_num

/-- The prime `73` is not Wieferich. -/
theorem jsp87Wieferich_seventythree_false : ¬ jsp87Wieferich 73 := by
  rw [jsp87_wieferich_iff]
  have h73 : (73 : ℕ) ^ 2 = 5329 := by norm_num
  rw [h73, jsp87Order_fifty_three_squared, jsp87Order2_seventythree]
  norm_num

/-- **THE PRIME `3` NEVER DIVIDES THE CLEARING DENOMINATOR TWICE.** -/
theorem jsp87_lambertDen_notdvd_nine (s : Finset ℕ) : ¬ (9 ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_sq_of_genuine 3 (by norm_num) (by norm_num)
    jsp87Wieferich_three_false s

/-- **NEITHER `5 ^ 2`.** -/
theorem jsp87_lambertDen_notdvd_twenty_five (s : Finset ℕ) : ¬ (25 ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_sq_of_genuine 5 (by norm_num) (by norm_num)
    jsp87Wieferich_five_false s

/-- **NEITHER `7 ^ 2`.** -/
theorem jsp87_lambertDen_notdvd_forty_nine (s : Finset ℕ) : ¬ (49 ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_sq_of_genuine 7 (by norm_num) (by norm_num)
    jsp87Wieferich_seven_false s

/-- **NEITHER `11 ^ 2`.** -/
theorem jsp87_lambertDen_notdvd_one_twenty_one (s : Finset ℕ) : ¬ (121 ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_sq_of_genuine 11 (by norm_num) (by norm_num)
    jsp87Wieferich_eleven_false s

/-- **NEITHER `73 ^ 2`.** -/
theorem jsp87_lambertDen_notdvd_5329 (s : Finset ℕ) : ¬ (5329 ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_sq_of_genuine 73 (by norm_num) (by norm_num)
    jsp87Wieferich_seventythree_false s

/-- **`25` is coprime to the whole clearing denominator** (round 147 proved the
prime `5` is invisible; here the square is coprime too). -/
theorem jsp87_lambertDen_coprime_twenty_five (s : Finset ℕ) :
    Nat.Coprime (lambertDen s) 25 := by
  have h : Nat.Coprime (lambertDen s) (5 ^ 2) :=
    (Nat.coprime_pow_right_iff (by norm_num) (lambertDen s) 5).mpr
      (jsp87_lambertDen_coprime_five s)
  rw [show (5 : ℕ) ^ 2 = 25 by norm_num] at h
  exact h

/-- **`121` is coprime to the whole clearing denominator.** -/
theorem jsp87_lambertDen_coprime_one_twenty_one (s : Finset ℕ) :
    Nat.Coprime (lambertDen s) 121 := by
  have h : Nat.Coprime (lambertDen s) (11 ^ 2) :=
    (Nat.coprime_pow_right_iff (by norm_num) (lambertDen s) 11).mpr
      (jsp87_lambertDen_coprime_eleven s)
  rw [show (11 : ℕ) ^ 2 = 121 by norm_num] at h
  exact h

/-- The clearing denominator is coprime to `3025 = 25 · 121`. -/
theorem jsp87_lambertDen_coprime_3025 (s : Finset ℕ) : Nat.Coprime (lambertDen s) 3025 := by
  have h := (jsp87_lambertDen_coprime_twenty_five s).mul_right
    (jsp87_lambertDen_coprime_one_twenty_one s)
  simpa using h

/-- **`5` is invisible at every depth**: `5 ^ e` never divides the clearing
denominator, for any `e ≥ 1`. -/
theorem jsp87_lambertDen_notdvd_pow_five (e : ℕ) (he : 1 ≤ e) (s : Finset ℕ) :
    ¬ (5 ^ e ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_pow_of_comp_order 5 (by norm_num)
    (by rw [jsp87Order2_five]; norm_num) e he s

/-- Likewise for `11`. -/
theorem jsp87_lambertDen_notdvd_pow_eleven (e : ℕ) (he : 1 ≤ e) (s : Finset ℕ) :
    ¬ (11 ^ e ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_pow_of_comp_order 11 (by norm_num)
    (by rw [jsp87Order2_eleven]; norm_num) e he s

/-- Likewise for `73`. -/
theorem jsp87_lambertDen_notdvd_pow_seventythree (e : ℕ) (he : 1 ≤ e) (s : Finset ℕ) :
    ¬ (73 ^ e ∣ lambertDen s) :=
  jsp87_lambertDen_notdvd_pow_of_comp_order 73 (by norm_num)
    (by rw [jsp87Order2_seventythree]; norm_num) e he s

/-! ## 7. The unrestricted tower at the square level, against the restricted one -/

/-- **THE UNRESTRICTED TOWER AT THE SQUARE LEVEL, LEVEL `9`.** -/
theorem jsp87_dvd_mer_sq_three_iff (k : ℕ) : 9 ∣ 2 ^ k - 1 ↔ 6 ∣ k := by
  have h := (jsp87_dvd_mer_sq_of_genuine 3 k (by norm_num) (by norm_num)
    jsp87Wieferich_three_false)
  rw [jsp87Order2_three] at h
  simpa using h

/-- Likewise at `25`. -/
theorem jsp87_dvd_mer_sq_five_iff (k : ℕ) : 25 ∣ 2 ^ k - 1 ↔ 20 ∣ k := by
  have h := (jsp87_dvd_mer_sq_of_genuine 5 k (by norm_num) (by norm_num)
    jsp87Wieferich_five_false)
  rw [jsp87Order2_five] at h
  simpa using h

/-- Likewise at `49`. -/
theorem jsp87_dvd_mer_sq_seven_iff (k : ℕ) : 49 ∣ 2 ^ k - 1 ↔ 21 ∣ k := by
  have h := (jsp87_dvd_mer_sq_of_genuine 7 k (by norm_num) (by norm_num)
    jsp87Wieferich_seven_false)
  rw [jsp87Order2_seven] at h
  simpa using h

/-- Likewise at `121`. -/
theorem jsp87_dvd_mer_sq_eleven_iff (k : ℕ) : 121 ∣ 2 ^ k - 1 ↔ 110 ∣ k := by
  have h := (jsp87_dvd_mer_sq_of_genuine 11 k (by norm_num) (by norm_num)
    jsp87Wieferich_eleven_false)
  rw [jsp87Order2_eleven] at h
  simpa using h

/-- Likewise at `5329 = 73 ^ 2`. -/
theorem jsp87_dvd_mer_sq_seventythree_iff (k : ℕ) :
    5329 ∣ 2 ^ k - 1 ↔ 657 ∣ k := by
  have h := (jsp87_dvd_mer_sq_of_genuine 73 k (by norm_num) (by norm_num)
    jsp87Wieferich_seventythree_false)
  rw [jsp87Order2_seventythree] at h
  simpa using h

/-- **NO PRIME LEVEL EVER SEES `9` TWICE.** -/
theorem jsp87_notdvd_mer_sq_three_of_prime (p : ℕ) (hp : p.Prime) : ¬ (9 ∣ 2 ^ p - 1) := by
  intro h
  obtain ⟨h1, h2⟩ := (jsp87_dvd_mer_sq_of_prime_iff 3 p (by norm_num) (by norm_num) hp).mp h
  exact jsp87Wieferich_three_false h2

/-- Likewise at `25`. -/
theorem jsp87_notdvd_mer_sq_five_of_prime (p : ℕ) (hp : p.Prime) : ¬ (25 ∣ 2 ^ p - 1) := by
  intro h
  obtain ⟨h1, h2⟩ := (jsp87_dvd_mer_sq_of_prime_iff 5 p (by norm_num) (by norm_num) hp).mp h
  exact jsp87Wieferich_five_false h2

/-- Likewise at `49`. -/
theorem jsp87_notdvd_mer_sq_seven_of_prime (p : ℕ) (hp : p.Prime) : ¬ (49 ∣ 2 ^ p - 1) := by
  intro h
  obtain ⟨h1, h2⟩ := (jsp87_dvd_mer_sq_of_prime_iff 7 p (by norm_num) (by norm_num) hp).mp h
  exact jsp87Wieferich_seven_false h2

/-- Likewise at `121`. -/
theorem jsp87_notdvd_mer_sq_eleven_of_prime (p : ℕ) (hp : p.Prime) : ¬ (121 ∣ 2 ^ p - 1) := by
  intro h
  obtain ⟨h1, h2⟩ := (jsp87_dvd_mer_sq_of_prime_iff 11 p (by norm_num) (by norm_num) hp).mp h
  exact jsp87Wieferich_eleven_false h2

/-- Likewise at `5329`. -/
theorem jsp87_notdvd_mer_sq_seventythree_of_prime (p : ℕ) (hp : p.Prime) :
    ¬ (5329 ∣ 2 ^ p - 1) := by
  intro h
  obtain ⟨h1, h2⟩ :=
    (jsp87_dvd_mer_sq_of_prime_iff 73 p (by norm_num) (by norm_num) hp).mp h
  exact jsp87Wieferich_seventythree_false h2

/-- **THE PRICE OF THE PRIME RESTRICTION AT THE SQUARE LEVEL.**  The square `9`
divides `2 ^ k - 1` at every level `k` that is a multiple of `6` — so the
*unrestricted* Lambert denominator picks up `9` over and over — while the
*prime-restricted* clearing denominator never contains `9` at all. -/
theorem jsp87_denominator_nine_dichotomy (k : ℕ) (s : Finset ℕ) :
    (9 ∣ 2 ^ k - 1 ↔ 6 ∣ k) ∧ ¬ (9 ∣ lambertDen s) :=
  ⟨jsp87_dvd_mer_sq_three_iff k, jsp87_lambertDen_notdvd_nine s⟩

/-- The same statement for `25`: the unrestricted tower sees `25` at every
multiple of `20`; the prime-restricted tower never does. -/
theorem jsp87_denominator_twenty_five_dichotomy (k : ℕ) (s : Finset ℕ) :
    (25 ∣ 2 ^ k - 1 ↔ 20 ∣ k) ∧ Nat.Coprime (lambertDen s) 25 :=
  ⟨jsp87_dvd_mer_sq_five_iff k, jsp87_lambertDen_coprime_twenty_five s⟩

/-! ## 8. Summary -/

/-- **THE WHOLE LEVEL STRUCTURE OF THE PRIME-RESTRICTED LAMBbert TOWER.** -/
theorem jsp87_lambert_level_summary (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (e : ℕ)
    (he : 1 ≤ e) (s : Finset ℕ) :
    (q ^ e ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ jsp87Order (q ^ e) = p) ∧
      (q ^ 2 ∣ lambertDen s ↔ ∃ p ∈ s, p.Prime ∧ jsp87Order2 q = p ∧ jsp87Wieferich q) ∧
      (¬ jsp87Wieferich q → ¬ (q ^ 2 ∣ lambertDen s)) :=
  ⟨jsp87_lambertDen_dvd_pow_iff q e hq he s,
    jsp87_lambertDen_dvd_sq_iff_weierich q hq hodd s,
    fun hw hg => (jsp87_lambertDen_notdvd_sq_of_genuine q hq hodd hw s) hg⟩

/-- **THE TWO BRANCHES OF THE WIEFERICH DICHOTOMY, ASSEMBLED.** -/
theorem jsp87_wieferich_summary (q k : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    (jsp87Order (q ^ 2) = jsp87Order2 q ∨ jsp87Order (q ^ 2) = q * jsp87Order2 q) ∧
      (jsp87Wieferich q → (q ^ 2 ∣ 2 ^ k - 1 ↔ q ∣ 2 ^ k - 1)) ∧
      (¬ jsp87Wieferich q → (q ^ 2 ∣ 2 ^ k - 1 ↔ q * jsp87Order2 q ∣ k)) :=
  ⟨jsp87_lift_dichotomy q hq hodd, fun hw => jsp87_dvd_mer_sq_of_weierich q k hq hodd hw,
    fun hg => jsp87_dvd_mer_sq_of_genuine q k hq hodd hg⟩

end JSP87