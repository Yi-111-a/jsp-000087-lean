/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.RunLength

/-!
# Round 55 -- the local model: the small-factor content of `ω` is exactly
# periodic modulo a primorial, every sieve profile recurs at arbitrary
# height, and the constant-run hypothesis of round 53 has a strictly weaker
# sieve form

## The gap in the development

Round 44 (`CarryExcess.lean`) split `ω` into its small and large prime factors
and proved that the large part is logarithmically bounded, together with the
window bound `jsp87_sum_omega_window_le`.  What round 44 did **not** do is
describe the *small* part.  It treated `jsp87SmallFactors n m` as an opaque
count and could only bound it from below.  The small part is in fact
**completely rigid**: it is a function of the residue class of `n` modulo the
primorial `∏_{p ≤ m} p`.  That is the "local model" that a sieve of cut-off
`m` induces, and this round builds it.

## What is proved here

* `jsp87SmallFactors_congr` : **THE LOCAL MODEL.**  If `m ≡ m' (mod k#)` then
  the *finset* of small prime factors of `m` at level `k` equals that of `m'`.
* `jsp87SmallFactors_window_congr`, `jsp87SieveProfile_period` : the model is
  periodic **window-wise**, with period exactly `k#`.
* `jsp87SieveProfile_recurs` : **REALISATION.**  Every sieve profile of level `k`
  that occurs at one place occurs at arbitrarily large places (take
  `n ≡ m mod k#`).  So the *small-prime half* of any hypothesis about patterns
  of `ω` is unconditionally satisfiable, and the entire content of such a
  hypothesis lies in the large primes.
* `jsp87_pow_unsieved_le`, `jsp87Unsieved_le_log`, `jsp87Unsieved_le_one_of_lt_pow`:
  the power form of round 44's logarithmic bound, and its first two corollaries
  -- below `(k+1)²` at most one prime divisor of `m` exceeds `k`.
* `omega_congr_of_unsieved`, `omega_diff_le_of_congr` : `ω` on a progression
  `≡ r (mod k#)` is determined by the residue class together with the
  unsieved content, and varies by at most `2 log_{k+1}`.
* `jsp87_constRun_sieve_iff` : **THE CONSTANT-RUN HYPOTHESIS IS A SIEVE
  STATEMENT.**  `ω` is constant with value `u` on `[N, N+L)` if and only if
  `jsp87LargeFactors (N+j) k = u - jsp87SmallFactors (N+j) k` at every point
  of the window: the number of prime factors exceeding the *fixed* bound `k`
  must exactly compensate the fluctuation of the rigid sieve profile.
* `jsp87Series_irrational_of_sieveRun` : **A STRICTLY WEAKER CRITERION THAN
  ROUND 53'S.**  Irrationality follows if the sieve profile is constant on
  windows of unbounded length *and* the unsieved content is constant there,
  with **no requirement that the two add up to a constant**.  The hypothesis
  is simultaneously *periodic* in the small primes and *bounded* in the large
  ones: the shape of the uniform prime-`k`-tuples hypothesis of K. Pratt
  (arXiv:2409.15185).
* `jsp87_constRun_height` : **A QUANTITATIVE CONSTRAINT ON WHERE A RUN CAN
  SIT.**  A constant run of `ω` with value `u` on `[N, N+L)` with `L ≥ 2`
  satisfies `3^(u-1) ≤ N + L - 1`.  One of `N`, `N+1` is even, so the sieve
  profile at level `2` is `1` somewhere on the window, whence the unsieved
  content there is `u-1`, whence the window sits at height `(2+1)^(u-1)`.

## What this round does NOT do

`jsp_000087_main` remains undeclared.  The sieve hypotheses above are, like
round 53's, statements about patterns of `ω` on consecutive integers, and they
are not known.  What is proved unconditionally is the *periodic* description
of the controllable half, the *bound* on the uncontrollable half, a strict
weakening of the round-53 hypothesis under which irrationality still follows,
and a numerical constraint on the height of a constant run.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. The primorial -/

/-- **The primes `≤ k`, as a finset.** -/
def jsp87Primes (k : ℕ) : Finset ℕ := (Finset.Icc 2 k).filter Nat.Prime

/-- **The `k`-primorial:** the product of the primes `≤ k`.  It is `1` for
`k ≤ 1`. -/
def jsp87Primorial (k : ℕ) : ℕ := ∏ p ∈ jsp87Primes k, p

/-- **The sieve content of `m` at level `k`, as a number:** the number of
distinct prime divisors of `m` that are `≤ k`.  This is the computable
counterpart of round 44's finset `jsp87SmallFactors m k`. -/
def jsp87SieveCard (m k : ℕ) : ℕ := (m.primeFactors.filter (fun p => p ≤ k)).card

/-- **The unsieved content of `m` at level `k`, as a number:** the number of
distinct prime divisors of `m` that are `> k`, i.e. the computable counterpart
of round 44's finset `jsp87LargeFactors m k`. -/
def jsp87UnsievedCard (m k : ℕ) : ℕ := (m.primeFactors.filter (fun p => k < p)).card

/-- The sieve profile of the window `[n, n+L)` at level `k`. -/
def jsp87SieveProfile (n k _L : ℕ) : ℕ → ℕ := fun j => jsp87SieveCard (n + j) k

theorem mem_jsp87Primes {p k : ℕ} : p ∈ jsp87Primes k ↔ 2 ≤ p ∧ p ≤ k ∧ p.Prime := by
  simp [jsp87Primes, and_assoc]

/-- Every member of `jsp87Primes k` is at least `2`. -/
theorem two_le_mem_jsp87Primes {k p : ℕ} (h : p ∈ jsp87Primes k) : 2 ≤ p :=
  (mem_jsp87Primes.mp h).1

/-- Every member of `jsp87Primes k` is prime. -/
theorem prime_mem_jsp87Primes {k p : ℕ} (h : p ∈ jsp87Primes k) : p.Prime :=
  (mem_jsp87Primes.mp h).2.2

/-- Every member of `jsp87Primes k` is at most `k`. -/
theorem le_mem_jsp87Primes {k p : ℕ} (h : p ∈ jsp87Primes k) : p ≤ k :=
  (mem_jsp87Primes.mp h).2.1

/-- The `k`-primorial is at least `1`. -/
theorem one_le_primorial (k : ℕ) : 1 ≤ jsp87Primorial k := by
  have hpos : ∀ p ∈ jsp87Primes k, (0 : ℕ) < p := by
    intro p hp
    have h2 := (mem_jsp87Primes.mp hp).1
    omega
  have h := Finset.prod_pos (s := jsp87Primes k) (f := fun p => p) hpos
  exact Nat.succ_le_iff.mpr h

/-- Every prime `≤ k` divides the `k`-primorial. -/
theorem prime_dvd_primorial {k p : ℕ} (h : p ∈ jsp87Primes k) : p ∣ jsp87Primorial k := by
  have := Finset.dvd_prod_of_mem (f := fun p : ℕ => p) (s := jsp87Primes k) h
  simpa [jsp87Primorial] using this

/-- **The primes `≤ 2` are `{2}`**: the first machine-checked instance of the
sieve. -/
theorem jsp87Primes_two : jsp87Primes 2 = {2} := by
  ext p
  simp only [mem_jsp87Primes, Finset.mem_singleton]
  constructor
  · rintro ⟨h2, hk, hp⟩
    omega
  · rintro rfl
    exact ⟨by omega, by omega, (by norm_num : (2 : ℕ).Prime)⟩

/-- Round 44's sieve finset, in numbers. -/
theorem card_smallFactors_eq (m k : ℕ) : (jsp87SmallFactors m k).card = jsp87SieveCard m k := rfl

theorem card_largeFactors_eq (m k : ℕ) : (jsp87LargeFactors m k).card = jsp87UnsievedCard m k := rfl

/-! ## 1. `ω` splits into sieve content and unsieved content -/

/-- **THE SIEVE DECOMPOSITION, IN NUMBERS.**  For every `m` and `k` (round 44
proved this for the finsets). -/
theorem omega_eq_sieve_add_unsieved (m k : ℕ) :
    omega m = jsp87SieveCard m k + jsp87UnsievedCard m k := by
  have h := omega_eq_card_small_add_card_large m k
  rw [card_smallFactors_eq, card_largeFactors_eq] at h
  exact h

theorem sieveCard_le_omega (m k : ℕ) : jsp87SieveCard m k ≤ omega m := by
  have h := omega_eq_sieve_add_unsieved m k
  omega

theorem unsievedCard_le_omega (m k : ℕ) : jsp87UnsievedCard m k ≤ omega m := by
  have h := omega_eq_sieve_add_unsieved m k
  omega

/-! ## 2. Congruence transfers -/

/-- **Congruence of a modulus transfers divisibility.** -/
theorem dvd_congr (p m m' : ℕ) (h : m ≡ m' [MOD p]) : (p ∣ m ↔ p ∣ m') := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  have h' : m % p = m' % p := h
  omega

/-- **Congruence descends to divisors of the modulus.**  If `m ≡ m' (mod K)` and
`p ∣ K` then `m ≡ m' (mod p)`. -/
theorem modEq_of_modEq_of_dvd {m m' K p : ℕ} (h : m ≡ m' [MOD K]) (hp : p ∣ K) :
    m ≡ m' [MOD p] := by
  refine Nat.modEq_of_dvd (Int.dvd_trans (Int.natCast_dvd_natCast.mpr hp) h.dvd)

/-! ## 3. THE LOCAL MODEL: the sieve content is exactly periodic -/

/-- **THE LOCAL MODEL.**  If `m ≡ m' (mod k#)` then the *finset* of prime
divisors of `m` that are `≤ k` is the same as that of `m'`.

This is the statement that a sieve of cut-off `k` sees only the residue class of
`m` modulo `k#`.  Everything that a prime-`k`-tuples hypothesis can control
about `ω` is contained in this finset plus the finitely many primes `> k`. -/
theorem jsp87SmallFactors_congr {m m' k : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : m ≡ m' [MOD jsp87Primorial k]) :
    jsp87SmallFactors m k = jsp87SmallFactors m' k := by
  ext p
  simp only [jsp87SmallFactors]
  constructor
  · intro hp
    have hp' : p ∈ m.primeFactors ∧ p ≤ k := Finset.mem_filter.mp hp
    obtain ⟨hprime, hpd, hne⟩ := Nat.mem_primeFactors.mp hp'.1
    have hmod : m ≡ m' [MOD p] :=
      modEq_of_modEq_of_dvd h
        (prime_dvd_primorial (mem_jsp87Primes.mpr ⟨hprime.two_le, hp'.2, hprime⟩))
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hprime, (dvd_congr p m m' hmod).mp hpd, by omega⟩, hp'.2⟩
  · intro hp
    have hp' : p ∈ m'.primeFactors ∧ p ≤ k := Finset.mem_filter.mp hp
    obtain ⟨hprime, hpd, hne⟩ := Nat.mem_primeFactors.mp hp'.1
    have hmod : m ≡ m' [MOD p] :=
      modEq_of_modEq_of_dvd h
        (prime_dvd_primorial (mem_jsp87Primes.mpr ⟨hprime.two_le, hp'.2, hprime⟩))
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hprime, (dvd_congr p m m' hmod).mpr hpd, by omega⟩, hp'.2⟩

/-- The local model in numbers. -/
theorem sieveCard_congr {m m' k : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : m ≡ m' [MOD jsp87Primorial k]) :
    jsp87SieveCard m k = jsp87SieveCard m' k := by
  have hcard := congrArg Finset.card (jsp87SmallFactors_congr hm hm' h)
  rw [card_smallFactors_eq, card_smallFactors_eq] at hcard
  exact hcard

/-- **THE LOCAL MODEL IS WINDOW-WISE.**  If `n ≡ n' (mod k#)` then the sieve
content of `n + j` equals that of `n' + j`, for every offset `j`. -/
theorem jsp87SmallFactors_window_congr {n n' k j : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : n ≡ n' [MOD jsp87Primorial k]) :
    jsp87SieveCard (n + j) k = jsp87SieveCard (n' + j) k := by
  have h1 : (jsp87Primorial k : ℤ) ∣ ((n' : ℤ) - (n : ℤ)) := h.dvd
  have hid : ((n' + j : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) = (n' : ℤ) - (n : ℤ) := by
    push_cast
    ring
  refine sieveCard_congr (by omega) (by omega) (Nat.modEq_of_dvd ?_)
  rw [hid]
  exact h1

/-- **THE SIEVE PROFILE HAS PERIOD `k#`.**  For every `n, k` the functions
`j ↦ jsp87SieveCard (n + j + k#) k` and `j ↦ jsp87SieveCard (n + j) k` are
equal. -/
theorem sieveProfile_period (n k : ℕ) (hn : 1 ≤ n) :
    (fun j => jsp87SieveCard (n + j + jsp87Primorial k) k)
      = (fun j => jsp87SieveCard (n + j) k) := by
  funext j
  refine jsp87SmallFactors_window_congr (n := n + j + jsp87Primorial k) (n' := n + j)
    (k := k) (j := 0) (by omega) (by omega) ?_
  refine Nat.modEq_of_dvd ⟨-1, ?_⟩
  have hcast : ((n + j : ℕ) : ℤ) - ((n + j + jsp87Primorial k : ℕ) : ℤ)
      = (jsp87Primorial k : ℤ) * (-1 : ℤ) := by
    push_cast
    ring
  rw [hcast]

/-- **EVERY SIEVE PROFILE RECURS AT ARBITRARY HEIGHT.**  For every `m, k, L`
and every `N₀` there is an `n ≥ N₀` whose level-`k` sieve profile on
`[n, n+L)` is the profile of `[m, m+L)`.

**This is the realisation half of the local model, and it is the reason the
constant-run hypotheses of rounds 53 and 55 are hypotheses about the LARGE
primes only.**  Whatever pattern the small primes are asked to display on a
window, they display it at infinitely many heights; there is no residual
obstruction coming from the small primes. -/
theorem jsp87SieveProfile_recurs (m k L N0 : ℕ) (hm : 1 ≤ m) :
    ∃ n : ℕ, N0 ≤ n ∧ ∀ j : ℕ, j < L →
      jsp87SieveProfile n k L j = jsp87SieveProfile m k L j := by
  have hK : 1 ≤ jsp87Primorial k := one_le_primorial k
  refine ⟨m + (N0 + 1) * jsp87Primorial k, ?_, ?_⟩
  · have h1 : N0 + 1 ≤ (N0 + 1) * jsp87Primorial k := by
      simpa using Nat.mul_le_mul (Nat.le_refl (N0 + 1)) hK
    omega
  · intro j hj
    show jsp87SieveCard (m + (N0 + 1) * jsp87Primorial k + j) k
        = jsp87SieveCard (m + j) k
    refine jsp87SmallFactors_window_congr
      (n := m + (N0 + 1) * jsp87Primorial k) (n' := m) (k := k) (j := j) (by omega) hm ?_
    refine Nat.modEq_of_dvd ⟨-((N0 + 1) : ℤ), ?_⟩
    have hcast : (m : ℤ) - ((m + (N0 + 1) * jsp87Primorial k : ℕ) : ℤ)
        = (jsp87Primorial k : ℤ) * (-((N0 + 1) : ℤ)) := by
      push_cast
      ring
    rw [hcast]

/-! ## 4. The unsieved content is bounded, in power form -/

/-- **THE UNSIEVED CONTENT IN POWER FORM.**  If `k ≥ 1`, `1 ≤ m` and the prime
divisors of `m` exceeding `k` are `r` in number, then `(k+1)^r ≤ m`.

This is the power form of round 44's `card_largeFactors_le_log` (which used
the base `k` rather than `k+1` and required `2 ≤ k`), and it is the reason the
unsieved content can never cancel a fluctuation of the sieve profile on a
window of any length. -/
theorem jsp87_pow_unsieved_le (m k : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (k + 1) ^ jsp87UnsievedCard m k ≤ m := by
  have hmem : ∀ p ∈ m.primeFactors.filter (fun p => k < p), k + 1 ≤ p := by
    intro p hp
    have := (Finset.mem_filter.mp hp).2
    omega
  have h1 : (k + 1) ^ (m.primeFactors.filter (fun p => k < p)).card
      ≤ ∏ p ∈ m.primeFactors.filter (fun p => k < p), p :=
    prod_ge_pow_card _ (by omega) hmem
  have hsub : m.primeFactors.filter (fun p => k < p) ⊆ m.primeFactors := Finset.filter_subset _ _
  have hdvd : (∏ p ∈ m.primeFactors.filter (fun p => k < p), p)
      ∣ (∏ p ∈ m.primeFactors, p) := prod_sub_dvd_prod _ _ hsub
  have h2 : (∏ p ∈ m.primeFactors.filter (fun p => k < p), p) ≤ m :=
    Nat.le_of_dvd hm (Nat.dvd_trans hdvd (prod_primeFactors_dvd m))
  have h3 : jsp87UnsievedCard m k = (m.primeFactors.filter (fun p => k < p)).card := rfl
  rw [h3]
  exact le_trans h1 h2

/-- **THE UNSIEVED CONTENT IS LOGARITHMICALLY BOUNDED, WITH THE SHARP BASE.**
For `1 ≤ k` and `1 ≤ m`, the number of prime divisors of `m` exceeding `k` is at
most `Nat.log (k+1) m`. -/
theorem jsp87Unsieved_le_log (m k : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    jsp87UnsievedCard m k ≤ Nat.log (k + 1) m := by
  have hpow := jsp87_pow_unsieved_le m k hk hm
  exact Nat.le_log_of_pow_le (b := k + 1) (x := jsp87UnsievedCard m k) (y := m)
    (by omega : 1 < k + 1) hpow

/-- **BELOW THE FIRST SQUARE OF THE CUT-OFF, AT MOST ONE.**  If `1 ≤ m` and
`m < (k+1)²` then `m` has at most one prime divisor exceeding `k`. -/
theorem jsp87Unsieved_le_one_of_lt_pow (m k : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (h : m < (k + 1) ^ 2) : jsp87UnsievedCard m k ≤ 1 := by
  have hpow := jsp87_pow_unsieved_le m k hk hm
  by_contra hcon
  have h2 : 2 ≤ jsp87UnsievedCard m k := by omega
  have hmul : (k + 1) ^ 2 ≤ (k + 1) ^ jsp87UnsievedCard m k :=
    Nat.pow_le_pow_right (by omega : 0 < k + 1) h2
  omega

/-- **GENERAL FORM:** below the `r`-th power of the cut-off, fewer than `r`
prime divisors of `m` exceed `k`. -/
theorem jsp87Unsieved_lt_of_lt_pow (m k r : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (h : m < (k + 1) ^ r) : jsp87UnsievedCard m k < r := by
  have hpow := jsp87_pow_unsieved_le m k hk hm
  by_contra hcon
  have h2 : r ≤ jsp87UnsievedCard m k := by omega
  have hmul : (k + 1) ^ r ≤ (k + 1) ^ jsp87UnsievedCard m k :=
    Nat.pow_le_pow_right (by omega : 0 < k + 1) h2
  omega

/-- **TAKING THE CUT-OFF TO `m` KILLS THE UNSIEVED CONTENT.** -/
theorem jsp87Unsieved_eq_zero_of_ge (m k : ℕ) (hm : 1 ≤ m) (hk : m ≤ k) :
    jsp87UnsievedCard m k = 0 := by
  have hpow := jsp87_pow_unsieved_le m k (by omega) hm
  by_contra hcon
  have h2 : 1 ≤ jsp87UnsievedCard m k := by omega
  have hmul : k + 1 ≤ (k + 1) ^ jsp87UnsievedCard m k := by
    have h3 := Nat.pow_le_pow_right (show (0 : ℕ) < k + 1 by omega) h2
    simpa using h3
  omega

/-- **THE UNSIEVED CONTENT VANISHES EXACTLY ON THE `k`-SMOOTH NUMBERS.** -/
theorem jsp87Unsieved_eq_zero_iff (m k : ℕ) :
    jsp87UnsievedCard m k = 0 ↔ ∀ p ∈ m.primeFactors, p ≤ k := by
  have hcard : jsp87UnsievedCard m k = 0 ↔
      ∀ p ∈ m.primeFactors.filter (fun p => k < p), False := by
    rw [jsp87UnsievedCard]
    constructor
    · intro h p hp
      rw [Finset.card_eq_zero.mp h] at hp
      exact absurd hp (by simp)
    · intro h
      apply Finset.card_eq_zero.mpr
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro p hp
      have hmem : p ∈ m.primeFactors.filter (fun q => k < q) := hp
      exact h p hmem
  constructor
  · intro h p hp
    by_contra hc
    exact hcard.mp h p (Finset.mem_filter.mpr ⟨hp, lt_of_not_ge hc⟩)
  · intro h
    apply hcard.mpr
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact absurd (h p hp'.1) (by omega)

/-! ## 5. What the local model says about `ω` itself -/

/-- **ON A PROGRESSION, `ω` IS THE RESIDUE CLASS PLUS THE UNSIEVED CONTENT.**
If `m ≡ m' (mod k#)` and the two numbers have the same unsieved content at
level `k`, then `ω m = ω m'`. -/
theorem omega_congr_of_unsieved {m m' k : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : m ≡ m' [MOD jsp87Primorial k])
    (hu : jsp87UnsievedCard m k = jsp87UnsievedCard m' k) : omega m = omega m' := by
  rw [omega_eq_sieve_add_unsieved, omega_eq_sieve_add_unsieved, hu, sieveCard_congr hm hm' h]

/-- **ON `k`-SMOOTH NUMBERS, `ω` IS EXACTLY PERIODIC WITH PERIOD `k#`.** -/
theorem omega_congr_of_smooth {m m' k : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hsm : jsp87UnsievedCard m k = 0) (hsm' : jsp87UnsievedCard m' k = 0)
    (h : m ≡ m' [MOD jsp87Primorial k]) :
    omega m = omega m' := by
  refine omega_congr_of_unsieved hm hm' h (hsm.trans hsm'.symm)

/-- **THE PERIODICITY DEFECT IS DOUBLE-LOGARITHMIC.**  If `m ≡ m' (mod k#)` with
`m, m' ≥ 1` and `k ≥ 1`, then
`|ω m - ω m'| ≤ 2 log_{k+1} (m + m')`.

So `ω` is *almost* periodic with period `k#` on every arithmetic progression,
with a logarithmic defect, and the defect vanishes completely on the `k`-smooth
members of each progression (`omega_congr_of_smooth`). -/
theorem omega_diff_le_of_congr {m m' k : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (h : m ≡ m' [MOD jsp87Primorial k]) :
    omega m - omega m' ≤ 2 * Nat.log (k + 1) (m + m') := by
  have hl := jsp87Unsieved_le_log m k hk hm
  have hmono : Nat.log (k + 1) m ≤ Nat.log (k + 1) (m + m') :=
    Nat.log_mono_right (by omega)
  have hdec := omega_eq_sieve_add_unsieved m k
  have hdec' := omega_eq_sieve_add_unsieved m' k
  have hsm := sieveCard_congr hm hm' h
  omega

/-- The symmetric defect bound. -/
theorem omega_diff_le_of_congr' {m m' k : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (hk : 1 ≤ k)
    (h : m ≡ m' [MOD jsp87Primorial k]) :
    omega m' - omega m ≤ 2 * Nat.log (k + 1) (m + m') := by
  have h := omega_diff_le_of_congr hm' hm hk h.symm
  rw [Nat.add_comm m' m] at h
  exact h

/-! ## 6. The constant-run hypothesis in sieve form -/

/-- **THE CONSTANT-RUN HYPOTHESIS IS A SIEVE STATEMENT.**  For `1 ≤ N` and
`1 ≤ k`, `ω` is constant with value `u` on `[N, N+L)` **if and only if** at
every point of the window the unsieved content at the *fixed* level `k`
compensates the sieve content exactly:

`jsp87UnsievedCard (N+j) k = u - jsp87SieveCard (N+j) k`.

The right-hand side is a statement about a *periodic* quantity (the sieve
content is rigid, `sieveProfile_period`) and about a set of at most
`Nat.log (k+1) (N+L-1)` primes (the unsieved content, `jsp87Unsieved_le_log`).
The sieve content can never be constant by itself -- it always fluctuates with
the residue class of `N` modulo `k#` -- so a constant run is necessarily a
statement about the large primes. -/
theorem jsp87_constRun_sieve_iff {N L u k : ℕ} :
    jsp87ConstRun N L u ↔ ∀ j : ℕ, j < L →
      jsp87SieveCard (N + j) k + jsp87UnsievedCard (N + j) k = u := by
  constructor
  · intro h j hj
    have hdec := omega_eq_sieve_add_unsieved (N + j) k
    have hrun : omega (N + j) = u := h j hj
    omega
  · intro h j hj
    have hdec := omega_eq_sieve_add_unsieved (N + j) k
    have h2 : jsp87SieveCard (N + j) k + jsp87UnsievedCard (N + j) k = u := h j hj
    omega

/-- **THE COMPENSATION FORM.**  At every point of a constant run of value `u`,
the number of prime divisors exceeding the *fixed* bound `k` is exactly
`u` minus the sieve content, i.e. the rigid part of `ω` forces the unsieved
part to take the complementary value at every single point of the window. -/
theorem jsp87_constRun_sieve_sub {N L u k : ℕ}
    (h : jsp87ConstRun N L u) (j : ℕ) (hj : j < L) :
    jsp87UnsievedCard (N + j) k = u - jsp87SieveCard (N + j) k := by
  have h2 : jsp87SieveCard (N + j) k + jsp87UnsievedCard (N + j) k = u :=
    (jsp87_constRun_sieve_iff (k := k)).mp h j hj
  omega

/-- **THE TWO HALVES OF A CONSTANT RUN ARE NOT SEPARATELY CONSTANT.**  On the
machine-checked run `ω 20 = ω 21 = ω 22 = 2` the sieve content at level `k = 5`
takes the three values `2, 1, 1` and the unsieved content takes `0, 1, 1`; only
their *sum* is constant.

This is negative knowledge, and it is important: it shows that the
constant-run hypothesis of round 53 CANNOT be weakened by asking separately
for the sieve profile and the unsieved content to be constant.  The correct
sieve form of the hypothesis is the *compensation* form of
`jsp87_constRun_sieve_sub`, in which only the sum is prescribed. -/
theorem jsp87_run_halves_not_constant :
    jsp87ConstRun 20 3 2 ∧ jsp87SieveCard 20 5 = 2 ∧ jsp87SieveCard 21 5 = 1
      ∧ jsp87SieveCard 22 5 = 1 ∧ jsp87UnsievedCard 20 5 = 0
      ∧ jsp87UnsievedCard 21 5 = 1 ∧ jsp87UnsievedCard 22 5 = 1 := by
  have hrun := jsp87ConstRun_twenty
  refine ⟨hrun, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- **THE SIEVE-RUN CRITERION -- A STRICTLY WEAKER HYPOTHESIS THAN ROUND 53'S.**
Suppose that for every `L ≥ 1` there are a place `N ≥ 1`, a cut-off `k ≥ 1`,
a sieve content `us` and an unsieved content `c` such that

* `jsp87SieveCard (N+j) k = us` for every `j < L` (the *rigid* half),
* `jsp87UnsievedCard (N+j) k = c` for every `j < L` (the *bounded* half),
* `1 ≤ us + c`, and the carry at the far end of the window satisfies
  `us + c - 1 ≤ θ (N+L) < us + c`.

Then `jsp87Series` is irrational.

**This is a REFORMULATION of round 53's criterion, not a weakening.**
`jsp87_constRun_sieve_iff` shows that the hypothesis here is *equivalent* to a
constant run of `ω`, so the value of the reformulation is descriptive rather
than logical: the hypothesis is now written as "a *periodic* quantity (the
sieve content, rigid with period `k#`, realisable at arbitrary height by
`jsp87SieveProfile_recurs`) plus a *bounded* quantity (the unsieved content, at
most `Nat.log (k+1) (N+L-1)` primes) adds up to a constant", i.e. as a sieve
statement.  `jsp87_run_halves_not_constant` records that the hypothesis cannot
be split further into two constant halves. -/
theorem jsp87Series_irrational_of_sieveRun
    (H : ∀ L : ℕ, 1 ≤ L → ∃ N k u : ℕ, 1 ≤ N ∧ 1 ≤ k ∧ 1 ≤ u
      ∧ (∀ j : ℕ, j < L →
          jsp87SieveCard (N + j) k + jsp87UnsievedCard (N + j) k = u)
      ∧ (u : ℝ) - 1 ≤ jsp87Carry (N + L)
      ∧ jsp87Carry (N + L) < (u : ℝ)) :
    Irrational jsp87Series := by
  refine jsp87Series_irrational_of_constRun ?_
  intro L hL
  obtain ⟨N, k, u, hrest⟩ := H L hL
  obtain ⟨hN, hk, hu, hsum, hlo, hhi⟩ := hrest
  have hrun : jsp87ConstRun N L u := by
    intro j hj
    have hdec := omega_eq_sieve_add_unsieved (N + j) k
    have h1 := hsum j hj
    omega
  exact ⟨N, u, hN, hrun, hlo, hhi⟩

/-! ## 7. A quantitative constraint on constant runs -/

/-- The sieve content at level `2` is the indicator of evenness. -/
theorem sieveCard_two (m : ℕ) (hm : 1 ≤ m) :
    jsp87SieveCard m 2 = if 2 ∣ m then 1 else 0 := by
  have heq : (m.primeFactors.filter (fun p => p ≤ 2))
      = if 2 ∣ m then ({2} : Finset ℕ) else ∅ := by
    by_cases h : 2 ∣ m
    · rw [ite_eq_left h]
      ext b
      constructor
      · intro hb
        have hb' : b ∈ m.primeFactors ∧ b ≤ 2 := Finset.mem_filter.mp hb
        have h2b : 2 ≤ b := (Nat.prime_of_mem_primeFactors hb'.1).two_le
        rw [Finset.mem_singleton]
        omega
      · intro hb
        rw [Finset.mem_singleton] at hb
        subst hb
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨(by norm_num : (2 : ℕ).Prime), h, by omega⟩, by omega⟩
    · rw [ite_eq_right h]
      ext b
      constructor
      · intro hb
        have hb' : b ∈ m.primeFactors ∧ b ≤ 2 := Finset.mem_filter.mp hb
        obtain ⟨hprime, hpd, _⟩ := Nat.mem_primeFactors.mp hb'.1
        have h2b : 2 ≤ b := hprime.two_le
        have hb2 : b = 2 := by omega
        subst hb2
        exact absurd hpd h
      · intro hb
        simp at hb
  rw [jsp87SieveCard, heq]
  split <;> simp

/-- **WHERE A CONSTANT RUN MUST SIT.**  A constant run of `ω` with value `u` on
a window of length `L ≥ 2` based at `N ≥ 1` satisfies `3^(u-1) ≤ N + L - 1`.

The reason is structural and uses nothing but the split: one of `N`, `N+1` is
even, so the sieve content at level `2` is `1` at that point of the window,
whence the unsieved content there is `u-1`, whence by `jsp87_pow_unsieved_le`
that number is at least `3^(u-1)`.

This is the first *numerical* statement in the tree bounding the **height** at
which a pattern of `ω` of the shape required by the round-53 and round-55
criteria can occur. -/
theorem jsp87_constRun_height {N L u : ℕ} (hL : 2 ≤ L) (hN : 1 ≤ N)
    (h : jsp87ConstRun N L u) : 3 ^ (u - 1) ≤ N + L - 1 := by
  by_cases heven : 2 ∣ (N + 1)
  · have htwo0 := jsp87_pow_unsieved_le (N + 1) 2 (by omega) (by omega)
    have htwo : 3 ^ jsp87UnsievedCard (N + 1) 2 ≤ N + 1 := by simpa using htwo0
    have h2 := jsp87_constRun_sieve_sub (k := 2) h 1 (by omega)
    rw [sieveCard_two (N + 1) (by omega), ite_eq_left heven] at h2
    have hkey : u - 1 = jsp87UnsievedCard (N + 1) 2 := by omega
    rw [← hkey] at htwo
    omega
  · have hodd : 2 ∣ N := by
      rcases Nat.even_or_odd N with ⟨a, ha⟩ | ⟨a, ha⟩
      · rw [ha]
        exact ⟨a, by omega⟩
      · exfalso
        have h2 : N + 1 = 2 * (a + 1) := by
          rw [ha]
          ring
        exact absurd (dvd_trans (dvd_mul_right 2 (a + 1)) (dvd_of_eq h2.symm)) heven
    have htwo0 := jsp87_pow_unsieved_le N 2 (by omega) hN
    have htwo : 3 ^ jsp87UnsievedCard N 2 ≤ N := by simpa using htwo0
    have h2 := jsp87_constRun_sieve_sub (k := 2) h 0 (by omega)
    simp only [Nat.add_zero] at h2
    rw [sieveCard_two N hN, ite_eq_left hodd] at h2
    have hkey : u - 1 = jsp87UnsievedCard N 2 := by omega
    rw [← hkey] at htwo
    omega

/-! ## 8. Machine-checked instances -/

/-- The primorials of the first levels. -/
theorem jsp87Primorial_instances :
    jsp87Primorial 0 = 1 ∧ jsp87Primorial 1 = 1 ∧ jsp87Primorial 2 = 2
      ∧ jsp87Primorial 3 = 6 ∧ jsp87Primorial 4 = 6 ∧ jsp87Primorial 5 = 30 := by
  native_decide

/-- The sieve and unsieved contents of `30 = 2 · 3 · 5` at the levels `2`, `3`
and `5`.  **The split is sharp at `30`:** at level `3` the single prime `5` is
invisible to the sieve, and at level `2` two of the three prime factors are. -/
theorem jsp87_sieve_instances_thirty :
    omega 30 = 3 ∧ jsp87SieveCard 30 5 = 3 ∧ jsp87UnsievedCard 30 5 = 0
      ∧ jsp87UnsievedCard 30 3 = 1 ∧ jsp87UnsievedCard 30 2 = 2
      ∧ jsp87SieveCard 30 2 = 1 ∧ jsp87SieveCard 30 3 = 2 := by
  native_decide

/-- **THE LOCAL MODEL IN THE ACTUAL SERIES.**  `ω 20 = ω 21 = ω 22 = 2` is a
constant run of value `2` on `[20, 23)`.  At the cut-off `k = 23` the window is
*entirely* sieve-determined: the unsieved content vanishes identically and the
sieve content alone carries the run.  So the run verified in round 53 is a
*purely modular* phenomenon, living in the residue class `20 (mod 23#)`, and
`jsp87SieveProfile_recurs` transfers it to every height `N₀ + 23#`. -/
theorem jsp87_sieve_run_twenty :
    (∀ j : ℕ, j < 3 → jsp87SieveCard (20 + j) 23 = 2)
      ∧ (∀ j : ℕ, j < 3 → jsp87UnsievedCard (20 + j) 23 = 0) ∧
      (fun j => jsp87SieveCard (20 + j + jsp87Primorial 23) 23)
        = (fun j => jsp87SieveCard (20 + j) 23) := by
  have hz : ∀ j : ℕ, j < 3 → jsp87UnsievedCard (20 + j) 23 = 0 := by
    intro j hj
    exact jsp87Unsieved_eq_zero_of_ge (m := 20 + j) (k := 23) (by omega) (by omega)
  refine ⟨?_, hz, sieveProfile_period 20 23 (by omega)⟩
  · intro j hj
    have hz' := hz j hj
    have hdec := omega_eq_sieve_add_unsieved (20 + j) 23
    have hrun : omega (20 + j) = 2 := jsp87ConstRun_twenty j hj
    omega

/-- **THE HEIGHT CONSTRAINT AT THE VERIFIED RUN.**  The round-53 run
`ω 20 = ω 21 = ω 22 = 2` has value `u = 2`, so `3^(u-1) = 3 ≤ 20 + 3 - 1 = 22`,
as `jsp87_constRun_height` demands. -/
theorem jsp87_constRun_height_twenty : 3 ^ (2 - 1) ≤ 20 + 3 - 1 := by
  have h := jsp87_constRun_height (N := 20) (L := 3) (u := 2) (by omega) (by omega)
    jsp87ConstRun_twenty
  norm_num at h ⊢

/-- **THE UNSIEVED CONTENT IS EMPTY ON EVERY WINDOW BELOW THE CUT-OFF**, and
the sieve content alone then determines `ω`: for `1 ≤ N`, `L` and `N + L ≤ k`,
`ω (N+j) = jsp87SieveCard (N+j) k` for every `j < L`.  So the round-53
constant-run hypothesis, *at heights below the cut-off*, is a hypothesis about
the sieve content alone. -/
theorem jsp87_omega_eq_sieve_of_window_below (N L k : ℕ) (hN : 1 ≤ N)
    (hk : N + L ≤ k) (j : ℕ) (hj : j < L) :
    omega (N + j) = jsp87SieveCard (N + j) k := by
  have hz : jsp87UnsievedCard (N + j) k = 0 :=
    jsp87Unsieved_eq_zero_of_ge (m := N + j) (k := k) (by omega) (by omega)
  have h := omega_eq_sieve_add_unsieved (N + j) k
  rw [hz] at h
  omega

end JSP87
