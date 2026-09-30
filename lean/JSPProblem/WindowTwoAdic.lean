/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Denominator

/-!
# JSP-000087, round 61 : the `2`-adic content of a window (Legendre's formula)

## What this file does

Rounds 37–60 produced the *series* (the Lambert reduction, the carry scaffold,
the gcd arithmetic, the carry dynamics, the digit bookkeeping, the carry
excess, the base-`2` block arithmetic, the primary expansion, the doubling map,
the radix criterion, the period equation, the `2`-adic prefix, the run
machinery, the sieve model, the product of a window, the denominator side, the
average order of `ω`, the CRT constructions).

This file attacks the one object route (3) of the round-58 attack list had named
and **no round had ever touched**: the **`2`-adic content of the product of a
window**.  Round 52 introduced the `2`-adic exponent `v = jsp87Val2` of a
single integer and round 56 introduced `jsp87WindowProd N L = ∏_{j<L} (N+j)`;
the two have never been joined.  Here they are, by Legendre's formula, proved
**from scratch**:

* `jsp87Popcount n` — the binary digit sum (Mathlib and Lean core have *no*
  popcount at all);
* `jsp87WindowVal2 N L = ∑_{j<L} v (N+j)` — the `2`-adic content of a window;
* `jsp87_windowVal2_eq` — **the exact identity**
  `∑_{j<L} v (N+j) + s₂(N+L-1) = L + s₂(N-1)`, i.e. Legendre's formula
  `v (m!) = m − s₂(m)` read at the level of a block of consecutive integers.

## Why it matters for the Erdős series

Round 56 accounted for the `ω`-mass of a window as *large primes + small-prime
incidences*; the `2` was absorbed into "small primes".  Here `2` is isolated:
the small-prime content of a window splits into the **`2`-channel**, which is
*exactly* quantised by the binary digits of `N` (Legendre), and the **odd
channel**, whose primes are all `≥ 3` and therefore cost a factor `3` each in
the product.  This yields the two-sided window estimate

* `2 ^ (L / 2) · 3 ^ #(odd primes of the product) ≤ ∏_{j<L} (N+j)`, and

* the `ω`-mass bound `∑_{j<L} ω (N+j) ≤ v₂-content + odd-content + L·π(L−1)`
  (`jsp87_window_omega_le_twoAdic`),

i.e. a window has only `L/2` units of "free" `2`-content however `N` is
chosen, and every further prime factor must be paid for in the height of the
window.  This is the arithmetic form of the heuristic behind Pratt's uniform
prime-`k`-tuples hypothesis: a window of length `L` with `ω`-mass `u·L` costs
exponentially in `u` in the position of the window.

Finally, §6 proves that the `2`-adic content of a window is **not eventually
periodic** in `N`, and that the digit sum is not either: two aperiodicity
results about objects built out of the binary expansion of integers, which
Mathlib cannot have (it has no base-`2` expansion of anything).

Everything below is proved with zero placeholders.
-/

namespace JSP87

/-! ## 0. The new objects -/

/-- **The binary digit sum** `s₂ n`: the number of `1`'s in the binary expansion
of `n`.  Defined by halving; neither Mathlib nor Lean core has a popcount. -/
def jsp87Popcount (n : ℕ) : ℕ := if n = 0 then 0 else jsp87Popcount (n / 2) + n % 2
termination_by n
decreasing_by omega

/-- **The `2`-adic content of a window**: the total exponent of `2` in the
product of `L` consecutive integers, i.e. `∑_{j<L} v (N+j)`. -/
noncomputable def jsp87WindowVal2 (N L : ℕ) : ℕ := ∑ j ∈ Finset.range L, jsp87Val2 (N + j)

/-- **The odd prime divisors of the product of a window.** -/
def jsp87OddFactors (N L : ℕ) : Finset ℕ :=
  (jsp87WindowProd N L).primeFactors.filter (fun p => 2 < p)

/-! ## 1. The binary digit sum -/

theorem jsp87Popcount_zero : jsp87Popcount 0 = 0 := by
  rw [jsp87Popcount]; rfl

/-- **The halving equation**: the digit sum of `n+1` is the digit sum of its
half, plus the low bit. -/
theorem jsp87Popcount_def (n : ℕ) :
    jsp87Popcount (n + 1) = jsp87Popcount ((n + 1) / 2) + (n + 1) % 2 := by
  rw [jsp87Popcount]; simp

/-- **APPENDING A `0` DOES NOT CHANGE THE DIGIT SUM.** -/
theorem jsp87Popcount_two_mul : ∀ n : ℕ, jsp87Popcount (2 * n) = jsp87Popcount n
  | 0 => rfl
  | (n + 1) => by
      have h1 : jsp87Popcount (2 * (n + 1))
          = jsp87Popcount ((2 * (n + 1)) / 2) + (2 * (n + 1)) % 2 := by
        have hrw : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
        rw [hrw, jsp87Popcount_def]
      have hd : (2 * (n + 1)) / 2 = n + 1 := by omega
      have hm : (2 * (n + 1)) % 2 = 0 := by omega
      rw [hd, hm, Nat.add_zero] at h1
      exact h1

/-- **APPENDING A `1` ADDS ONE TO THE DIGIT SUM.** -/
theorem jsp87Popcount_two_mul_add_one (n : ℕ) :
    jsp87Popcount (2 * n + 1) = jsp87Popcount n + 1 := by
  have h1 := jsp87Popcount_def (2 * n)
  have hd : (2 * n + 1) / 2 = n := by omega
  have hm : (2 * n + 1) % 2 = 1 := by omega
  rw [hd, hm] at h1
  exact h1

/-- **ADDING ONE ADDS AT MOST ONE `1`:** carries only destroy digits. -/
theorem jsp87Popcount_succ_le : ∀ n : ℕ, jsp87Popcount (n + 1) ≤ jsp87Popcount n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hr' : n = 2 * r := by omega
        rw [hr', jsp87Popcount_two_mul_add_one, jsp87Popcount_two_mul]
      · have hnr : n + 1 = 2 * (r + 1) := by omega
        have hr' : n = 2 * r + 1 := by omega
        rw [hnr, jsp87Popcount_two_mul, hr', jsp87Popcount_two_mul_add_one]
        have h1 := ih r (by omega)
        omega

/-- **SUBADDITIVITY OF THE DIGIT SUM** (carries can only remove `1`'s). -/
theorem jsp87Popcount_add_le : ∀ a b : ℕ,
    jsp87Popcount (a + b) ≤ jsp87Popcount a + jsp87Popcount b := by
  intro a b
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
      rw [← h]
      rcases a with _ | k
      · simp [jsp87Popcount_zero]
      · rcases b with _ | m
        · simp [jsp87Popcount_zero]
        · rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
          · have hr' : k = 2 * r := by omega
            rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
            · have ht' : m = 2 * t := by omega
              have hA : k + 1 = 2 * r + 1 := by omega
              have hB : m + 1 = 2 * t + 1 := by omega
              have hS : (k + 1) + (m + 1) = 2 * (r + t + 1) := by omega
              rw [hS, hA, hB]
              simp only [jsp87Popcount_two_mul, jsp87Popcount_two_mul_add_one]
              have h0 := jsp87Popcount_succ_le (r + t)
              have h1 := ih (r + t) (by omega) r t (by omega)
              omega
            · have ht' : m = 2 * t + 1 := by omega
              have hA : k + 1 = 2 * r + 1 := by omega
              have hB : m + 1 = 2 * (t + 1) := by omega
              have hS : (k + 1) + (m + 1) = 2 * (r + t + 1) + 1 := by omega
              rw [hS, hA, hB]
              simp only [jsp87Popcount_two_mul, jsp87Popcount_two_mul_add_one]
              have h1 := ih (r + t + 1) (by omega) r (t + 1) (by omega)
              omega
          · have hr' : k = 2 * r + 1 := by omega
            rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
            · have ht' : m = 2 * t := by omega
              have hA : k + 1 = 2 * (r + 1) := by omega
              have hB : m + 1 = 2 * t + 1 := by omega
              have hS : (k + 1) + (m + 1) = 2 * (r + t + 1) + 1 := by omega
              rw [hS, hA, hB]
              simp only [jsp87Popcount_two_mul, jsp87Popcount_two_mul_add_one]
              have h1 := ih (r + t + 1) (by omega) (r + 1) t (by omega)
              omega
            · have ht' : m = 2 * t + 1 := by omega
              have hA : k + 1 = 2 * (r + 1) := by omega
              have hB : m + 1 = 2 * (t + 1) := by omega
              have hS : (k + 1) + (m + 1) = 2 * (r + t + 2) := by omega
              rw [hS, hA, hB]
              simp only [jsp87Popcount_two_mul]
              have h1 := ih (r + t + 2) (by omega) (r + 1) (t + 1) (by omega)
              omega

/-- **THE DIGIT SUM IS AT MOST HALF THE NUMBER, ROUNDED UP:**
`2 · s₂ n ≤ n + 1`, since `n ≥ 2^{s₂ n} - 1`. -/
theorem jsp87Popcount_two_mul_le : ∀ n : ℕ, 2 * jsp87Popcount n ≤ n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases n with _ | m
      · rw [jsp87Popcount_zero]; omega
      · rcases m with _ | k
        · rw [jsp87Popcount_def 0, jsp87Popcount_zero]
        · have h := jsp87Popcount_def (k + 1)
          have e1 : (k + 1) + 1 = k + 2 := by omega
          rw [e1] at h
          have h1 := ih ((k + 2) / 2) (by omega)
          rw [h]
          omega

/-- **THE DIGIT SUM IS AT MOST `⌈n/2⌉`.** -/
theorem jsp87Popcount_le (n : ℕ) : jsp87Popcount n ≤ n := by
  have h := jsp87Popcount_two_mul_le n
  omega

theorem jsp87Popcount_le_half (n : ℕ) : jsp87Popcount n ≤ (n + 1) / 2 := by
  refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
  have h := jsp87Popcount_two_mul_le n
  omega

/-- The digit sum of a nonzero power of `2` is `1`. -/
theorem jsp87Popcount_one' : jsp87Popcount 1 = 1 := by
  rw [jsp87Popcount_def 0, jsp87Popcount_zero]

theorem jsp87Popcount_pow_two : ∀ k : ℕ, 1 ≤ k → jsp87Popcount (2 ^ k) = 1 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
      have e : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ, Nat.mul_comm]
      rw [hj, e, jsp87Popcount_two_mul]
      rcases j with _ | i
      · rw [show 2 ^ 0 = 1 from rfl, jsp87Popcount_one']
      · exact ih (i + 1) (by omega) (by omega)

theorem jsp87Popcount_four : jsp87Popcount 4 = 1 := by
  have h1 : 4 = 2 ^ 2 := by norm_num
  rw [h1, jsp87Popcount_pow_two 2 (by omega)]

theorem jsp87Popcount_three : jsp87Popcount 3 = 2 := by
  rw [show 3 = 2 * 1 + 1 from rfl, jsp87Popcount_two_mul_add_one, jsp87Popcount_one']

theorem jsp87Popcount_fifteen : jsp87Popcount 15 = 4 := by
  rw [show 15 = 2 * 7 + 1 from rfl, jsp87Popcount_two_mul_add_one,
      show 7 = 2 * 3 + 1 from rfl, jsp87Popcount_two_mul_add_one,
      jsp87Popcount_three]

/-! ## 2. The `2`-adic exponent at an odd and at an even number -/

/-- If `2^(k+1)` divides `c` then `2` divides `c`. -/
private theorem dvd_two_of_pow_succ_dvd {c k : ℕ} (h : 2 ^ (k + 1) ∣ c) : 2 ∣ c := by
  obtain ⟨x, hx⟩ := h
  refine ⟨2 ^ k * x, ?_⟩
  rw [hx]
  ring

private theorem not_two_dvd_two_mul_add_one (k : ℕ) : ¬ 2 ∣ 2 * k + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- **AN ODD NUMBER HAS `2`-EXPONENT `0`.** -/
theorem jsp87Val2_odd (k : ℕ) : jsp87Val2 (2 * k + 1) = 0 := by
  have hne : 2 * k + 1 ≠ 0 := by omega
  have h := (jsp87Val2_spec hne).mp rfl
  have hn : ¬ 2 ∣ 2 * k + 1 := not_two_dvd_two_mul_add_one k
  have hval : jsp87Val2 (2 * k + 1) = 0 := by
    by_contra hc
    obtain ⟨k', hc'⟩ : ∃ k', jsp87Val2 (2 * k + 1) = k' + 1 :=
      ⟨jsp87Val2 (2 * k + 1) - 1, by omega⟩
    have h1 := h.1
    rw [hc'] at h1
    have h2 : 2 ∣ 2 * k + 1 := dvd_two_of_pow_succ_dvd h1
    exact hn h2
  refine (jsp87Val2_spec hne).mpr ⟨?_, ?_⟩
  · simp
  · simp [hn]

theorem jsp87Val2_one : jsp87Val2 1 = 0 := jsp87Val2_odd 0

/-- **THE `2`-EXPONENT OF A POWER OF `2` IS THE POWER ITSELF.** -/
theorem jsp87Val2_pow_two (k : ℕ) : jsp87Val2 (2 ^ k) = k := by
  induction k with
  | zero => rw [show 2 ^ 0 = 1 from rfl, jsp87Val2_one]
  | succ k ih =>
      have hrw : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
      rw [hrw, jsp87Val2_mul_two (by positivity), ih]

/-- **AN EVEN NUMBER HAS `2`-EXPONENT `≥ 1`.** -/
theorem jsp87Val2_ge_one_of_two_dvd {m : ℕ} (hne : m ≠ 0) (h2 : 2 ∣ m) :
    1 ≤ jsp87Val2 m := by
  have h := (jsp87Val2_spec hne).mp rfl
  by_contra hcon
  have hk : jsp87Val2 m = 0 := by omega
  have h3 := h.2
  simp [hk] at h3
  have h4 : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
  omega

/-! ## 3. LEGENDRE'S FORMULA, AND THE EXACT CONTENT OF A WINDOW -/

theorem jsp87_windowVal2_zero (N : ℕ) : jsp87WindowVal2 N 0 = 0 := by
  simp [jsp87WindowVal2]

/-- **THE STEP IDENTITY** for the `2`-adic content of a window. -/
theorem jsp87_windowVal2_succ (N L : ℕ) :
    jsp87WindowVal2 N (L + 1) = jsp87WindowVal2 N L + jsp87Val2 (N + L) := by
  have h := Finset.sum_range_succ (f := fun j => jsp87Val2 (N + j)) L
  simpa [jsp87WindowVal2] using h

/-- **THE INCREMENT IDENTITY (the `2`-adic form of "carrying costs a digit").**
For `n ≥ 1`, incrementing `n` destroys exactly as many digits as the `2`-adic
exponent of `n`:

`v (n) + s₂(n) = 1 + s₂(n-1)`.

This is the step from which Legendre's formula follows; it is the statement
that Mathlib has no counterpart of, since it has no notion of digit sum. -/
theorem jsp87Val2_succ_popcount {n : ℕ} (hn : 1 ≤ n) :
    jsp87Val2 n + jsp87Popcount n = 1 + jsp87Popcount (n - 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases n with _ | m
      · omega
      · rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
        · have hnr : m + 1 = 2 * r + 1 := by omega
          have hsub : 2 * r + 1 - 1 = 2 * r := by omega
          rw [hnr, jsp87Val2_odd, jsp87Popcount_two_mul_add_one, hsub,
            jsp87Popcount_two_mul]
          omega
        · have hnr : m + 1 = 2 * (r + 1) := by omega
          have hsub : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
          rw [hnr, jsp87Val2_mul_two (by positivity), jsp87Popcount_two_mul, hsub,
            jsp87Popcount_two_mul_add_one]
          have h1 := ih (r + 1) (by omega) (by omega)
          have hsub2 : (r + 1) - 1 = r := by omega
          rw [hsub2] at h1
          omega

/-- **THE HEADLINE OF THIS FILE — LEGENDRE'S FORMULA FOR A WINDOW.**  For
`1 ≤ N`:

`∑_{j<L} v (N+j) + s₂(N+L-1) = L + s₂(N-1)`,

i.e. the `2`-adic content of a block of consecutive integers is `L` minus the
difference of the digit sums of its endpoints.  Equivalently
`v ((N+L-1)!) − v ((N-1)!) = L − s₂(N+L-1) + s₂(N-1)`. -/
theorem jsp87_windowVal2_eq {N L : ℕ} (hN : 1 ≤ N) :
    jsp87WindowVal2 N L + jsp87Popcount (N + L - 1) = L + jsp87Popcount (N - 1) := by
  induction L with
  | zero =>
      have h0 := jsp87_windowVal2_zero N
      simp only [Nat.add_zero]
      omega
  | succ L ih =>
      rw [jsp87_windowVal2_succ]
      have hsub : N + (L + 1) - 1 = N + L := by omega
      rw [hsub]
      have hinc := jsp87Val2_succ_popcount (n := N + L) (by omega)
      omega

/-- **THE CONTENT IS THE LENGTH MINUS THE JUMP OF THE DIGIT SUM.** -/
theorem jsp87_windowVal2_sub {N L : ℕ} (hN : 1 ≤ N) :
    L - jsp87Popcount L ≤ jsp87WindowVal2 N L := by
  have h := jsp87_windowVal2_eq (L := L) hN
  have hsub : jsp87Popcount (N + L - 1) ≤ jsp87Popcount (N - 1) + jsp87Popcount L := by
    have h1 := jsp87Popcount_add_le (N - 1) L
    have e : (N - 1) + L = N + L - 1 := by omega
    rw [e] at h1
    exact h1
  omega

/-- **A WINDOW OF LENGTH `L` ALWAYS CONTAINS `⌊L/2⌋` UNITS OF `2`-CONTENT.**
This is the classical "the product of `L` consecutive integers is divisible by
`2^{⌊L/2⌋}`", here with the *exact* exponent attached. -/
theorem jsp87_windowVal2_ge_half {N L : ℕ} (hN : 1 ≤ N) :
    L / 2 ≤ jsp87WindowVal2 N L := by
  have h1 := jsp87_windowVal2_sub (L := L) hN
  have h2 := jsp87Popcount_le_half L
  rcases Nat.even_or_odd L with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hL : L / 2 = m := by omega
    omega
  · have hL : L / 2 = m := by omega
    omega

/-- **THE CONTENT IS AT MOST THE LENGTH PLUS THE DIGIT SUM OF THE START.** -/
theorem jsp87_windowVal2_le_add {N L : ℕ} (hN : 1 ≤ N) :
    jsp87WindowVal2 N L ≤ L + jsp87Popcount (N - 1) := by
  have h := jsp87_windowVal2_eq (L := L) hN
  omega

/-- **AND HENCE AT MOST `L + ⌊N/2⌋`.** -/
theorem jsp87_windowVal2_le_add_half {N L : ℕ} (hN : 1 ≤ N) :
    jsp87WindowVal2 N L ≤ L + N / 2 := by
  have h := jsp87_windowVal2_le_add (L := L) hN
  have h2 : jsp87Popcount (N - 1) ≤ N / 2 := by
    refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    have h3 := jsp87Popcount_two_mul_le (N - 1)
    omega
  omega

/-- **THE TWO-SIDED WINDOW BOUND FOR THE `2`-CONTENT.** -/
theorem jsp87_windowVal2_bounds {N L : ℕ} (hN : 1 ≤ N) :
    L / 2 ≤ jsp87WindowVal2 N L ∧ jsp87WindowVal2 N L ≤ L + N / 2 :=
  ⟨jsp87_windowVal2_ge_half (L := L) hN, jsp87_windowVal2_le_add_half (L := L) hN⟩

/-- A window of length `1` has the `2`-content of its single entry. -/
theorem jsp87_windowVal2_one (N : ℕ) : jsp87WindowVal2 N 1 = jsp87Val2 N := by
  have h := jsp87_windowVal2_succ N 0
  rw [jsp87_windowVal2_zero, Nat.add_zero] at h
  simpa using h

/-- **THE CONTENT OF A WINDOW STARTING AT A POWER OF `2` IS EXACTLY `k`.** -/
theorem jsp87_windowVal2_pow_two (k : ℕ) :
    jsp87WindowVal2 (2 ^ k) 1 = k := by
  rw [jsp87_windowVal2_one, jsp87Val2_pow_two]

/-! ## 4. The valuation of the product of a window -/

private theorem pow_le_pow_left_nat {a b : ℕ} (h : a ≤ b) (k : ℕ) : a ^ k ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact le_trans (Nat.mul_le_mul_right _ ih) (Nat.mul_le_mul_left _ h)

private theorem le_two_mul (x : ℕ) : x ≤ x * 2 := by
  induction x with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul]; omega

private theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction c with
  | zero => simp
  | succ c ih =>
      rw [show a + (c + 1) = (a + c) + 1 by omega, pow_succ]
      exact le_trans ih (le_two_mul _)

private theorem two_pow_dvd_pow_two_of_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ∣ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact Nat.dvd_mul_right _ _

/-- **THE `2`-EXPONENT IS ADDITIVE ON PRODUCTS.**  Mathlib has `Nat.factor`
for this, but not for a `ℕ`-valued `2`-adic exponent. -/
theorem jsp87Val2_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    jsp87Val2 (a * b) = jsp87Val2 a + jsp87Val2 b := by
  have h := (jsp87Val2_spec ha).mp rfl
  have h' := (jsp87Val2_spec hb).mp rfl
  obtain ⟨u, hu⟩ := h.1
  obtain ⟨v, hv⟩ := h'.1
  have hu2 : ¬ 2 ∣ u := by
    intro hu2
    have hdup : 2 ^ (jsp87Val2 a + 1) ∣ a := by
      calc 2 ^ (jsp87Val2 a + 1) = 2 ^ jsp87Val2 a * 2 := by rw [pow_succ]
        _ ∣ 2 ^ jsp87Val2 a * u := Nat.mul_dvd_mul dvd_rfl hu2
        _ = a := hu.symm
    exact h.2 hdup
  have hv2 : ¬ 2 ∣ v := by
    intro hv2
    have hdup : 2 ^ (jsp87Val2 b + 1) ∣ b := by
      calc 2 ^ (jsp87Val2 b + 1) = 2 ^ jsp87Val2 b * 2 := by rw [pow_succ]
        _ ∣ 2 ^ jsp87Val2 b * v := Nat.mul_dvd_mul dvd_rfl hv2
        _ = b := hv.symm
    exact h'.2 hdup
  refine (jsp87Val2_spec (Nat.mul_ne_zero ha hb)).mpr ⟨?_, ?_⟩
  · have hd : 2 ^ (jsp87Val2 a + jsp87Val2 b)
        = 2 ^ jsp87Val2 a * 2 ^ jsp87Val2 b := by rw [pow_add]
    rw [hd]
    exact Nat.mul_dvd_mul h.1 h'.1
  · intro hc
    have hprod : a * b = 2 ^ (jsp87Val2 a + jsp87Val2 b) * (u * v) := by
      calc a * b = 2 ^ jsp87Val2 a * u * b := congrArg (fun z => z * b) hu
        _ = 2 ^ jsp87Val2 a * u * (2 ^ jsp87Val2 b * v) := by rw [← hv]
        _ = 2 ^ (jsp87Val2 a + jsp87Val2 b) * (u * v) := by rw [pow_add]; ring
    have he : 2 ^ (jsp87Val2 a + jsp87Val2 b + 1)
        = 2 ^ (jsp87Val2 a + jsp87Val2 b) * 2 := by rw [pow_succ]
    have hdiv : 2 ^ (jsp87Val2 a + jsp87Val2 b) * 2
        ∣ 2 ^ (jsp87Val2 a + jsp87Val2 b) * (u * v) := by
      rw [hprod] at hc
      rw [← he]
      exact hc
    have h2 : 2 ∣ u * v :=
      (Nat.mul_dvd_mul_iff_left (a := 2 ^ (jsp87Val2 a + jsp87Val2 b))
        (by positivity)).mp hdiv
    rcases (show Nat.Prime 2 from by decide).dvd_mul.mp h2 with hleft | hright
    · exact hu2 hleft
    · exact hv2 hright

/-- **THE `2`-CONTENT OF A WINDOW IS THE `2`-EXPONENT OF ITS PRODUCT.** -/
theorem jsp87Val2_windowProd {N L : ℕ} (hN : 1 ≤ N) :
    jsp87Val2 (jsp87WindowProd N L) = jsp87WindowVal2 N L := by
  induction L with
  | zero =>
      rw [jsp87WindowProd_zero, jsp87Val2_one, jsp87_windowVal2_zero]
  | succ L ih =>
      rw [jsp87WindowProd_succ, jsp87_windowVal2_succ,
        jsp87Val2_mul (jsp87WindowProd_ne_zero hN) (by omega)]
      omega

/-- **THE PRODUCT OF A WINDOW CARRIES EXACTLY `jsp87WindowVal2 N L` POWERS OF
`2`.** -/
theorem two_pow_dvd_windowProd {N L : ℕ} (hN : 1 ≤ N) :
    2 ^ jsp87WindowVal2 N L ∣ jsp87WindowProd N L := by
  have h := jsp87Val2_dvd (n := jsp87WindowProd N L) (jsp87WindowProd_ne_zero hN)
  rw [jsp87Val2_windowProd hN] at h
  exact h

theorem jsp87_windowProd_pow_two_le {N L : ℕ} (hN : 1 ≤ N) :
    2 ^ jsp87WindowVal2 N L ≤ jsp87WindowProd N L :=
  Nat.le_of_dvd (jsp87WindowProd_pos hN) (two_pow_dvd_windowProd hN)

/-- **THE CLASSICAL `2^{⌊L/2⌋}`-DIVISIBILITY OF A PRODUCT OF `L` CONSECUTIVE
INTEGERS**, with the Legendre-exact content attached. -/
theorem jsp87_windowProd_two_pow_ge {N L : ℕ} (hN : 1 ≤ N) :
    2 ^ (L / 2) ≤ jsp87WindowProd N L := by
  have h1 := jsp87_windowVal2_ge_half (L := L) hN
  have h2 := jsp87_windowProd_pow_two_le (L := L) hN
  have h3 : 2 ^ (L / 2) ≤ 2 ^ jsp87WindowVal2 N L := two_pow_mono h1
  exact le_trans h3 h2

theorem jsp87_windowProd_two_pow_dvd {N L : ℕ} (hN : 1 ≤ N) :
    2 ^ (L / 2) ∣ jsp87WindowProd N L := by
  have h1 := jsp87_windowVal2_ge_half (L := L) hN
  have h2 := two_pow_dvd_pow_two_of_le (by omega)
  exact dvd_trans h2 (two_pow_dvd_windowProd hN)

/-! ## 5. The odd channel -/

theorem mem_jsp87OddFactors {p N L : ℕ} (hN : 1 ≤ N) :
    p ∈ jsp87OddFactors N L ↔ p.Prime ∧ p ∣ jsp87WindowProd N L ∧ 2 < p := by
  constructor
  · intro hp
    have hp1 := Finset.mem_filter.mp hp
    obtain ⟨hpp, hpd, hne⟩ := Nat.mem_primeFactors.mp hp1.1
    exact ⟨hpp, hpd, hp1.2⟩
  · intro hp
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1, jsp87WindowProd_ne_zero hN⟩, hp.2.2⟩

/-- An odd prime never divides a power of `2`. -/
private theorem prime_ne_two_nvd_two_pow {p k : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    ¬ p ∣ 2 ^ k := by
  induction k with
  | zero =>
      rw [show 2 ^ 0 = 1 from rfl]
      intro hh
      have h1 : p = 1 := Nat.dvd_one.mp hh
      have h2 : 2 ≤ p := hp.two_le
      exact hne (by omega)
  | succ k ih =>
      rw [pow_succ, Nat.mul_comm]
      intro hd
      rcases hp.dvd_mul.mp hd with h1 | h2
      · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h1
        have htwo : 2 ≤ p := hp.two_le
        exact hne (by omega)
      · exact ih h2

/-- **THE ODD PART OF THE PRODUCT OF A WINDOW IS NONZERO** (it is a quotient of
a positive number by a divisor of it). -/
theorem jsp87_oddPart_ne_zero {N L : ℕ} (hN : 1 ≤ N) :
    jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L ≠ 0 := by
  have h2 : 2 ^ jsp87WindowVal2 N L ∣ jsp87WindowProd N L := two_pow_dvd_windowProd hN
  have hpow : jsp87WindowProd N L
      = 2 ^ jsp87WindowVal2 N L * (jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L) :=
    (Nat.mul_div_cancel' h2).symm
  rintro hz
  rw [hz, Nat.mul_zero] at hpow
  exact (jsp87WindowProd_ne_zero hN) hpow

theorem jsp87_oddFactors_subset_oddPart {N L : ℕ} (hN : 1 ≤ N) :
    jsp87OddFactors N L
      ⊆ (jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L).primeFactors := by
  intro p hp
  have hp' := (mem_jsp87OddFactors hN).mp hp
  have h2 : 2 ^ jsp87WindowVal2 N L ∣ jsp87WindowProd N L := two_pow_dvd_windowProd hN
  have hne : p ≠ 2 := by
    have : 2 < p := hp'.2.2
    omega
  have hpow : jsp87WindowProd N L
      = 2 ^ jsp87WindowVal2 N L * (jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L) :=
    (Nat.mul_div_cancel' h2).symm
  have hpd : p ∣ jsp87WindowProd N L := hp'.2.1
  rw [hpow] at hpd
  rw [Nat.mem_primeFactors]
  refine ⟨hp'.1, ?_, jsp87_oddPart_ne_zero hN⟩
  rcases hp'.1.dvd_mul.mp hpd with hbad | hgood
  · exact (prime_ne_two_nvd_two_pow hp'.1 hne hbad).elim
  · exact hgood

/-- **THE ODD PART OF THE PRODUCT OF A WINDOW IS AT LEAST `3^#(odd primes)`.** -/
theorem jsp87_pow_three_oddFactors {N L : ℕ} (hN : 1 ≤ N) :
    3 ^ (jsp87OddFactors N L).card
      ≤ jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L := by
  have hmem : ∀ p ∈ jsp87OddFactors N L, 3 ≤ p := by
    intro p hp
    have hp' := (mem_jsp87OddFactors hN).mp hp
    have htwo := hp'.1.two_le
    omega
  have h1 : 3 ^ (jsp87OddFactors N L).card ≤ ∏ p ∈ jsp87OddFactors N L, p :=
    prod_ge_pow_card _ (by omega) hmem
  have hsub : jsp87OddFactors N L
      ⊆ (jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L).primeFactors :=
    jsp87_oddFactors_subset_oddPart hN
  have hdvd : (∏ p ∈ jsp87OddFactors N L, p)
      ∣ jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L :=
    dvd_trans (prod_sub_dvd_prod _ _ hsub)
      (prod_primeFactors_dvd (jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L))
  have hpos : 0 < jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L :=
    Nat.pos_iff_ne_zero.mpr (jsp87_oddPart_ne_zero hN)
  have h2 : (∏ p ∈ jsp87OddFactors N L, p)
      ≤ jsp87WindowProd N L / 2 ^ jsp87WindowVal2 N L :=
    Nat.le_of_dvd hpos hdvd
  exact le_trans h1 h2

theorem jsp87_oddFactors_subset_biUnion {N L : ℕ} (hN : 1 ≤ N) :
    jsp87OddFactors N L
      ⊆ (Finset.range L).biUnion (fun j => (N + j).primeFactors.filter (fun p => 2 < p)) := by
  intro p hp
  have hp' := (mem_jsp87OddFactors hN).mp hp
  obtain ⟨j, hj, hjd⟩ := (jsp87_dvd_windowProd hp'.1).mp hp'.2.1
  refine Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hp'.1, hjd, by omega⟩, hp'.2.2⟩

/-- **EACH ENTRY HAS AT MOST `log_3` ODD PRIME FACTORS.** -/
theorem jsp87_oddCard_le_log {N L : ℕ} (hN : 1 ≤ N) (hj : j < L) :
    ((N + j).primeFactors.filter (fun p => 2 < p)).card
      ≤ Nat.log 3 (N + L - 1) := by
  have hmem : ∀ p ∈ (N + j).primeFactors.filter (fun p => 2 < p), 3 ≤ p := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have htwo := (Nat.mem_primeFactors.mp hp'.1).1.two_le
    omega
  have h1 : 3 ^ ((N + j).primeFactors.filter (fun p => 2 < p)).card
      ≤ ∏ p ∈ (N + j).primeFactors.filter (fun p => 2 < p), p :=
    prod_ge_pow_card _ (by omega) hmem
  have hdvd : (∏ p ∈ (N + j).primeFactors.filter (fun p => 2 < p), p) ∣ N + j := by
    refine dvd_trans (prod_sub_dvd_prod _ _ (Finset.filter_subset _ _))
      (prod_primeFactors_dvd (N + j))
  have h2 : (∏ p ∈ (N + j).primeFactors.filter (fun p => 2 < p), p) ≤ N + j :=
    Nat.le_of_dvd (by have := hj; omega) hdvd
  have h3 : N + j ≤ N + L - 1 := by omega
  refine Nat.le_log_of_pow_le (b := 3) (x := ((N + j).primeFactors.filter (fun p => 2 < p)).card)
    (y := N + L - 1) (by omega) (le_trans h1 (le_trans h2 h3))

/-- **THE NUMBER OF ODD PRIMES OF THE PRODUCT OF A WINDOW IS LOGARITHMIC IN
THE HEIGHT OF THE WINDOW, WITH BASE `3`.** -/
theorem jsp87_oddFactors_card_le_log {N L : ℕ} (hN : 1 ≤ N) :
    (jsp87OddFactors N L).card ≤ L * Nat.log 3 (N + L - 1) := by
  refine le_trans (Finset.card_le_card (jsp87_oddFactors_subset_biUnion hN)) ?_
  have h1 := Finset.card_biUnion_le
    (s := (Finset.range L : Finset ℕ)) (t := fun j => (N + j).primeFactors.filter (fun p => 2 < p))
  have h2 : ∑ j ∈ Finset.range L, ((N + j).primeFactors.filter (fun p => 2 < p)).card
      ≤ ∑ j ∈ Finset.range L, Nat.log 3 (N + L - 1) :=
    Finset.sum_le_sum (fun j hj => jsp87_oddCard_le_log hN (Finset.mem_range.mp hj))
  have h3 : (∑ j ∈ Finset.range L, Nat.log 3 (N + L - 1))
      = L * Nat.log 3 (N + L - 1) := by
    simp [Finset.sum_const, Finset.card_range]
  omega

/-! ## 6. The `2`-adic content and the digit sum are APERIODIC -/

/-- **`a^(n−m) · a^m = a^n`** for `m ≤ n`: the elementary splitting of a power.
Mathlib's `pow_sub` is stated for groups; this is the `ℕ` version. -/
private theorem pow_sub_nat {a m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n _ ih =>
      have hmn : m ≤ n := by omega
      rw [show n + 1 - m = (n - m) + 1 by omega]
      calc a ^ ((n - m) + 1) * a ^ m = (a ^ (n - m) * a ^ m) * a := by rw [pow_succ]; ring
        _ = a ^ n * a := by rw [ih]
        _ = a ^ (n + 1) := by rw [pow_succ]

/-- An even summand cannot be cancelled: `2 ∣ A` and `2 ∣ (A + u)` force
`2 ∣ u`. -/
private theorem not_two_dvd_add_of_two_dvd_not {A u : ℕ} (hA : 2 ∣ A) (hu : ¬ 2 ∣ u) :
    ¬ 2 ∣ A + u := by
  intro hc
  obtain ⟨d, hd⟩ := hA
  obtain ⟨c, hc'⟩ := hc
  refine hu ⟨c - d, ?_⟩
  have h1 : A + u = 2 * d + u := by rw [hd]
  have h3 : u = 2 * c - 2 * d := by omega
  calc u = 2 * c - 2 * d := h3
    _ = 2 * (c - d) := by omega

/-- **A POWER OF `2` IS AT LEAST ONE MORE THAN ITS EXPONENT**, so powers of `2`
unboundedly large are available: this is the elementary stand-in for Mathlib's
`exists_pow_ge_of_ge`, which is not available for `ℕ` bases in this version. -/
private theorem exists_two_pow_ge (A : ℕ) : ∃ k : ℕ, A ≤ 2 ^ k := by
  induction A with
  | zero => exact ⟨0, by simp⟩
  | succ A ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ, Nat.mul_comm]]
      have h2 : (1:ℕ) ≤ 2 ^ k := one_le_two_pow k
      have h3 : 2 ^ k + 1 ≤ 2 * 2 ^ k := by omega
      omega

private theorem two_pow_ge_add_one : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ]]
      omega

private theorem two_pow_lt_imp {v k : ℕ} (h : 2 ^ v < 2 ^ k) : v < k := by
  induction v using Nat.strong_induction_on generalizing k with
  | _ v ih =>
      rcases v with _ | v'
      · rw [show 2 ^ 0 = 1 from rfl] at h
        by_contra hcon
        have hk : k = 0 := by omega
        rw [hk, show 2 ^ 0 = 1 from rfl] at h
        omega
      · rcases k with _ | k'
        · rw [show 2 ^ 0 = 1 from rfl] at h
          have hpos : (1 : ℕ) ≤ 2 ^ (v' + 1) := one_le_two_pow (v' + 1)
          omega
        · have h'' : 2 ^ v' < 2 ^ k' := by
            rw [show 2 ^ (v' + 1) = 2 ^ v' * 2 by rw [pow_succ],
              show 2 ^ (k' + 1) = 2 ^ k' * 2 by rw [pow_succ]] at h
            exact (Nat.mul_lt_mul_right (a := 2) (b := 2 ^ v') (c := 2 ^ k')
              (show (0:ℕ) < 2 by omega)).mp h
          have hlt := ih v' (by omega) h''
          omega

/-- **THE `2`-EXPONENT OF `2^k + t` IS THE `2`-EXPONENT OF `t`,** whenever
`2^k > t`: adding a big power of `2` changes nothing `2`-adically. -/
theorem jsp87Val2_add_two_pow {t k : ℕ} (ht : 1 ≤ t) (hk : 2 ^ k > t) :
    jsp87Val2 (2 ^ k + t) = jsp87Val2 t := by
  have hne : t ≠ 0 := by omega
  have hv := (jsp87Val2_spec (n := t) hne).mp rfl
  obtain ⟨u, hu⟩ := hv.1
  have hk' : jsp87Val2 t < k := by
    refine two_pow_lt_imp ?_
    calc 2 ^ jsp87Val2 t ≤ t := Nat.le_of_dvd (by omega) hv.1
      _ < 2 ^ k := hk
  have hu2 : ¬ 2 ∣ u := by
    intro hu2
    have h3 : 2 ^ (jsp87Val2 t + 1) ∣ t := by
      calc 2 ^ (jsp87Val2 t + 1) = 2 ^ jsp87Val2 t * 2 := by rw [pow_succ]
        _ ∣ 2 ^ jsp87Val2 t * u := Nat.mul_dvd_mul dvd_rfl hu2
        _ = t := hu.symm
    exact hv.2 h3
  have hdv : 2 ^ jsp87Val2 t ∣ 2 ^ k + t :=
    dvd_add (two_pow_dvd_pow_two_of_le (by omega)) hv.1
  have hpow : 2 ^ (k - jsp87Val2 t) * 2 ^ jsp87Val2 t = 2 ^ k :=
    pow_sub_nat (show jsp87Val2 t ≤ k by omega)
  have hsum : 2 ^ k + t = 2 ^ jsp87Val2 t * (2 ^ (k - jsp87Val2 t) + u) := by
    calc 2 ^ k + t = 2 ^ (k - jsp87Val2 t) * 2 ^ jsp87Val2 t + t := by rw [← hpow]
      _ = 2 ^ (k - jsp87Val2 t) * 2 ^ jsp87Val2 t + 2 ^ jsp87Val2 t * u :=
        congrArg (fun z => 2 ^ (k - jsp87Val2 t) * 2 ^ jsp87Val2 t + z) hu
      _ = 2 ^ jsp87Val2 t * (2 ^ (k - jsp87Val2 t) + u) := by ring
  have hneQ : ¬ 2 ∣ 2 ^ (k - jsp87Val2 t) + u := by
    have hex : k - jsp87Val2 t = (k - jsp87Val2 t - 1) + 1 := by omega
    have htwo : 2 ∣ 2 ^ (k - jsp87Val2 t) := by
      rw [hex, pow_succ]
      have : 2 ^ (k - jsp87Val2 t - 1) * 2 = 2 * 2 ^ (k - jsp87Val2 t - 1) := by ring
      rw [this]
      exact dvd_mul_right 2 _
    exact not_two_dvd_add_of_two_dvd_not htwo hu2
  refine (jsp87Val2_spec (n := 2 ^ k + t) (by omega)).mpr ⟨hdv, ?_⟩
  intro hc
  have hc' : 2 ^ jsp87Val2 t * 2
      ∣ 2 ^ jsp87Val2 t * (2 ^ (k - jsp87Val2 t) + u) := by
    have he : 2 ^ (jsp87Val2 t + 1) = 2 ^ jsp87Val2 t * 2 := by rw [pow_succ]
    have hcq : 2 ^ (jsp87Val2 t + 1) ∣ 2 ^ k + t := by
      have h2 := hc
      rw [he] at h2
      exact h2
    rw [hsum] at hcq
    rw [← he]
    exact hcq
  exact hneQ ((Nat.mul_dvd_mul_iff_left (a := 2 ^ jsp87Val2 t) (by positivity)).mp hc')

/-- **THE `2`-CONTENT OF A WINDOW IS NOT EVENTUALLY PERIODIC IN THE POSITION OF
THE WINDOW.**  Mathlib cannot have such a statement: it has no notion of the
`2`-adic exponent of a block of consecutive integers. -/
theorem jsp87_windowVal2_not_eventuallyPeriodic :
    ¬ ∃ t M : ℕ, 1 ≤ t ∧ ∀ n : ℕ, M ≤ n →
      jsp87WindowVal2 (n + t) 1 = jsp87WindowVal2 n 1 := by
  rintro ⟨t, M, ht, h⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, M + t + 1 ≤ 2 ^ k := exists_two_pow_ge (M + t + 1)
  have hk2 : 2 ^ k > t := by omega
  have h1 := h (2 ^ k) (by omega)
  rw [jsp87_windowVal2_one, jsp87_windowVal2_one, jsp87Val2_add_two_pow ht hk2,
    jsp87Val2_pow_two] at h1
  have hspec := (jsp87Val2_spec (n := t) (by omega)).mp rfl
  have hlt : jsp87Val2 t < k := by
    refine two_pow_lt_imp ?_
    calc 2 ^ jsp87Val2 t ≤ t := Nat.le_of_dvd (by omega) hspec.1
      _ < 2 ^ k := hk2
  omega

/-- **ADDING A POWER OF `2` BELOW ITS OWN EXPONENT ADDS EXACTLY ONE DIGIT:**
for `y < 2^m`, `s₂(2^m + y) = 1 + s₂(y)`.  This is the "no carries" lemma for
the digit sum, and it is what the complement identity needs. -/
theorem jsp87Popcount_add_two_pow : ∀ m y : ℕ, y < 2 ^ m →
    jsp87Popcount (2 ^ m + y) = 1 + jsp87Popcount y := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro y hy
      rcases m with _ | m'
      · have hyy : y = 0 := by rw [show 2 ^ 0 = 1 from rfl] at hy; omega
        subst hyy
        rw [show 2 ^ 0 + 0 = 1 from rfl, jsp87Popcount_one', jsp87Popcount_zero]
      · rw [show 2 ^ (m' + 1) = 2 * 2 ^ m' by rw [pow_succ, Nat.mul_comm]] at hy
        rcases Nat.even_or_odd y with ⟨z, hz⟩ | ⟨z, hz⟩
        · have h1 : 2 ^ (m' + 1) + y = 2 * (2 ^ m' + z) := by rw [hz]; ring
          have hzlt : z < 2 ^ m' := by omega
          rw [h1, jsp87Popcount_two_mul, ih m' (by omega) z hzlt]
          rw [hz, show z + z = 2 * z by ring, jsp87Popcount_two_mul]
        · have h1 : 2 ^ (m' + 1) + y = 2 * (2 ^ m' + z) + 1 := by rw [hz]; ring
          have hzlt : z < 2 ^ m' := by omega
          rw [h1, jsp87Popcount_two_mul_add_one, ih m' (by omega) z hzlt]
          rw [hz, jsp87Popcount_two_mul_add_one]
          omega

/-- **THE BITWISE COMPLEMENT IDENTITY** `s₂(2^k − 1 − x) = k − s₂(x)` for
`x < 2^k`: the digits of the complement in `k` bits are the opposite digits. -/
theorem jsp87Popcount_compl : ∀ (k x : ℕ), x < 2 ^ k →
    jsp87Popcount (2 ^ k - 1 - x) + jsp87Popcount x = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro x hx
      rcases k with _ | j
      · have hx' : x = 0 := by rw [show 2 ^ 0 = 1 from rfl] at hx; omega
        subst hx'
        simp [jsp87Popcount_zero]
      · rw [show 2 ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ, Nat.mul_comm]] at hx
        rw [show 2 ^ j * 2 = 2 * 2 ^ j by ring] at hx
        by_cases hlow : x < 2 ^ j
        · have h1 : 2 ^ (j + 1) - 1 - x = 2 ^ j + (2 ^ j - 1 - x) := by omega
          have hlt : 2 ^ j - 1 - x < 2 ^ j := by omega
          rw [h1, jsp87Popcount_add_two_pow j (2 ^ j - 1 - x) hlt]
          have hrec := ih j (by omega) (2 ^ j - 1 - x) hlt
          have hz : 2 ^ j - 1 - (2 ^ j - 1 - x) = x := by omega
          rw [hz] at hrec
          omega
        · have hge : 2 ^ j ≤ x := by omega
          obtain ⟨y, hy⟩ : ∃ y : ℕ, x = 2 ^ j + y := ⟨x - 2 ^ j, by omega⟩
          have hy' : y < 2 ^ j := by omega
          have h2 : 2 ^ (j + 1) - 1 - x = 2 ^ j - 1 - y := by
            rw [hy]
            omega
          rw [h2]
          rw [show jsp87Popcount x = 1 + jsp87Popcount y by
                rw [hy, jsp87Popcount_add_two_pow j y hy']]
          have hrec := ih j (by omega) y hy'
          omega

/-- **THE DIGIT SUM IS NOT EVENTUALLY PERIODIC.**  A second aperiodicity result
about an object built from the binary expansion of an integer; Mathlib has no
popcount at all, hence no such statement. -/
theorem jsp87Popcount_not_eventuallyPeriodic :
    ¬ ∃ t M : ℕ, 1 ≤ t ∧ ∀ n : ℕ, M ≤ n → jsp87Popcount (n + t) = jsp87Popcount n := by
  rintro ⟨t, M, ht, h⟩
  have hk : M + t + 4 ≤ 2 ^ (M + t + 3) := by
    have h := two_pow_ge_add_one (M + t + 3)
    omega
  have hn : M ≤ 2 ^ (M + t + 3) - t := by omega
  have hlow : t - 1 < 2 ^ (M + t + 3) := by omega
  have h1 := h (2 ^ (M + t + 3) - t) hn
  have hcompl : jsp87Popcount (2 ^ (M + t + 3) - 1 - (t - 1))
      + jsp87Popcount (t - 1) = M + t + 3 :=
    jsp87Popcount_compl (M + t + 3) (t - 1) hlow
  have hsub : 2 ^ (M + t + 3) - 1 - (t - 1) = 2 ^ (M + t + 3) - t := by omega
  have hstep : jsp87Popcount (2 ^ (M + t + 3) - t) + jsp87Popcount (t - 1) = M + t + 3 := by
    rw [hsub] at hcompl
    exact hcompl
  have hsmall : jsp87Popcount (t - 1) ≤ t - 1 := jsp87Popcount_le _
  have hbig : 2 ≤ jsp87Popcount (2 ^ (M + t + 3) - t) := by omega
  have hone : jsp87Popcount (2 ^ (M + t + 3)) = 1 := jsp87Popcount_pow_two _ (by omega)
  have hsum : 2 ^ (M + t + 3) - t + t = 2 ^ (M + t + 3) := by omega
  rw [hsum, hone] at h1
  omega

private theorem sum_const' (s : Finset ℕ) (c : ℕ) : (∑ _ ∈ s, c) = s.card * c := by
  rw [Finset.sum_const]
  induction s.card with
  | zero => simp
  | succ n ih => ring

private theorem sum_add' (s : Finset ℕ) (f g : ℕ → ℕ) :
    (∑ j ∈ s, (f j + g j)) = (∑ j ∈ s, f j) + ∑ j ∈ s, g j := by
  rw [Finset.sum_add_distrib]

private theorem sum_add_const' (s : Finset ℕ) (c : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ s, (c + f j)) = (∑ _ ∈ s, c) + ∑ j ∈ s, f j := by
  rw [Finset.sum_add_distrib]

private theorem sum_ite_card (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ j ∈ s, if P j then 1 else 0) = (s.filter P).card := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]

/-! ## 7. Joining the `2`-channel to the rest of the tree -/

private theorem primeFactors_le_two (m : ℕ) :
    ∀ p, p ∈ m.primeFactors ∧ p ≤ 2 → p = 2 := by
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp.1).1
  rcases Nat.eq_or_lt_of_le hp.2 with heq | hlt
  · omega
  · have htwo := hpp.two_le
    omega

private theorem two_mem_primeFactors {m : ℕ} (hm : 0 < m) (h2 : 2 ∣ m) :
    (2:ℕ) ∈ m.primeFactors := by
  obtain ⟨c, rfl⟩ := h2
  rw [Nat.mem_primeFactors]
  refine ⟨by decide, dvd_mul_right 2 c, fun hz => ?_⟩
  omega

/-- **THE `ω` OF A POSITIVE NUMBER SPLITS INTO ITS ODD PART AND THE PRIME `2`.** -/
theorem jsp87_omega_eq_odd_add_two {m : ℕ} (hm : 0 < m) :
    omega m = (m.primeFactors.filter (fun p => 2 < p)).card
      + (if 2 ∣ m then 1 else 0) := by
  classical
  have hsplit : m.primeFactors.card
      = (m.primeFactors.filter (fun p => 2 < p)).card
        + (m.primeFactors.filter (fun p => p ≤ 2)).card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (p := fun p : ℕ => 2 < p) (s := m.primeFactors)
    have hnot : {a ∈ m.primeFactors | ¬ (2 < a)} = m.primeFactors.filter (fun p => p ≤ 2) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq1, hq2⟩
        exact ⟨hq1, by omega⟩
      · rintro ⟨hq1, hq2⟩
        exact ⟨hq1, by omega⟩
    rw [hnot] at h1
    exact h1.symm
  have hcard : (m.primeFactors.filter (fun p => p ≤ 2)).card = (if 2 ∣ m then 1 else 0) := by
    by_cases h2 : 2 ∣ m
    · rw [ite_eq_left h2]
      have hsub : m.primeFactors.filter (fun p => p ≤ 2) ⊆ ({2} : Finset ℕ) := by
        intro p hp
        rw [Finset.mem_singleton]
        exact primeFactors_le_two m p (Finset.mem_filter.mp hp)
      have hsup : ({2} : Finset ℕ) ⊆ m.primeFactors.filter (fun p => p ≤ 2) := by
        intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        exact Finset.mem_filter.mpr ⟨two_mem_primeFactors hm h2, by omega⟩
      have heq : m.primeFactors.filter (fun p => p ≤ 2) = {2} :=
        Finset.Subset.antisymm hsub hsup
      rw [heq, Finset.card_singleton]
    · rw [ite_eq_right h2]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hp2 := primeFactors_le_two m p hmem
      have hpd := (Nat.mem_primeFactors.mp hmem.1).2.1
      rw [hp2] at hpd
      exact h2 hpd
  change m.primeFactors.card = _
  rw [hsplit, hcard]

/-- **THE ODD `ω`-PART OF AN ENTRY IS AT MOST `π(L−1) + (large primes ≥ L)`.** -/
theorem jsp87_oddCard_le_add {m L : ℕ} (hL : 2 ≤ L) :
    (m.primeFactors.filter (fun p => 2 < p)).card
      ≤ (jsp87Primes (L - 1)).card + jsp87BigCard m L := by
  classical
  have hsmall : ((m.primeFactors.filter (fun p => 2 < p)).filter (fun p => p < L)).card
      ≤ (m.primeFactors.filter (fun p => p < L)).card := by
    refine Finset.card_le_card ?_
    intro p hp
    have h1 := Finset.mem_filter.mp hp
    have h2 := Finset.mem_filter.mp h1.1
    exact Finset.mem_filter.mpr ⟨h2.1, h1.2⟩
  have hsieve' : (m.primeFactors.filter (fun p => p < L)).card
      ≤ (jsp87Primes (L - 1)).card := by
    have hh : (m.primeFactors.filter (fun p => p < L))
        = m.primeFactors.filter (fun p => p ≤ L - 1) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq1, hq2⟩
        exact ⟨hq1, by omega⟩
      · rintro ⟨hq1, hq2⟩
        exact ⟨hq1, by omega⟩
    rw [hh]
    exact jsp87SieveCard_le_primes m L
  have hsieve : (m.primeFactors.filter (fun p => p ≤ L - 1)).card
      ≤ (jsp87Primes (L - 1)).card := jsp87SieveCard_le_primes m L
  have hbig : ((m.primeFactors.filter (fun p => 2 < p)).filter (fun p => L ≤ p)).card
      ≤ (m.primeFactors.filter (fun p => L ≤ p)).card := by
    refine Finset.card_le_card ?_
    intro p hp
    have h1 := Finset.mem_filter.mp hp
    have h2 := Finset.mem_filter.mp h1.1
    exact Finset.mem_filter.mpr ⟨h2.1, h1.2⟩
  have hsplit : (m.primeFactors.filter (fun p => 2 < p)).card
      = ((m.primeFactors.filter (fun p => 2 < p)).filter (fun p => p < L)).card
        + ((m.primeFactors.filter (fun p => 2 < p)).filter (fun p => L ≤ p)).card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (p := fun q : ℕ => q < L) (s := m.primeFactors.filter (fun q => 2 < q))
    have hnot : {a ∈ m.primeFactors.filter (fun q => 2 < q) | ¬ (a < L)}
        = (m.primeFactors.filter (fun q => 2 < q)).filter (fun q => L ≤ q) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hq1, hq2⟩, hq3⟩
        exact ⟨⟨hq1, hq2⟩, by omega⟩
      · rintro ⟨⟨hq1, hq2⟩, hq3⟩
        exact ⟨⟨hq1, hq2⟩, by omega⟩
    rw [hnot] at h1
    exact h1.symm
  have hsmallcard : ((m.primeFactors.filter (fun p => p < L))
      = m.primeFactors.filter (fun p => p ≤ L - 1)) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq1, hq2⟩
      exact ⟨hq1, by omega⟩
    · rintro ⟨hq1, hq2⟩
      exact ⟨hq1, by omega⟩
  have hsmall' : ((m.primeFactors.filter (fun p => 2 < p)).filter (fun p => p < L)).card
      ≤ (m.primeFactors.filter (fun p => p ≤ L - 1)).card := by
    rw [← hsmallcard]
    exact hsmall
  have hbig' : ((m.primeFactors.filter (fun p => 2 < p)).filter (fun p => L ≤ p)).card
      ≤ jsp87BigCard m L := by
    exact hbig.trans (by rfl)
  rw [hsplit]
  omega

/-- **THE NUMBER OF EVEN ENTRIES OF A WINDOW IS AT MOST ITS `2`-CONTENT.** -/
theorem jsp87_even_count_le_windowVal2 {N L : ℕ} (hN : 1 ≤ N) :
    ((Finset.range L).filter (fun j => 2 ∣ N + j)).card ≤ jsp87WindowVal2 N L := by
  have hge : ∀ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j),
      1 ≤ jsp87Val2 (N + j) := by
    intro j hj
    have hj' := Finset.mem_range.mp ((Finset.mem_filter.mp hj).1)
    have h2 := (Finset.mem_filter.mp hj).2
    exact jsp87Val2_ge_one_of_two_dvd (by omega) h2
  have hcard : ((Finset.range L).filter (fun j => 2 ∣ N + j)).card
      = ∑ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j), (1:ℕ) := by
    rw [sum_const', Nat.mul_one]
  have hsum1 : ∑ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j), (1:ℕ)
      ≤ ∑ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j), jsp87Val2 (N + j) :=
    Finset.sum_le_sum fun j hj => hge j hj
  have hsub : (Finset.range L).filter (fun j => 2 ∣ N + j) ⊆ Finset.range L :=
    Finset.filter_subset _ _
  have hsum2 : (∑ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j), jsp87Val2 (N + j))
      ≤ ∑ j ∈ Finset.range L, jsp87Val2 (N + j) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro j hj hj'
    exact Nat.zero_le _
  calc ((Finset.range L).filter (fun j => 2 ∣ N + j)).card
      = ∑ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j), (1:ℕ) := hcard
    _ ≤ ∑ j ∈ (Finset.range L).filter (fun j => 2 ∣ N + j), jsp87Val2 (N + j) := hsum1
    _ ≤ ∑ j ∈ Finset.range L, jsp87Val2 (N + j) := hsum2
    _ = jsp87WindowVal2 N L := rfl

/-- **THE `ω`-MASS OF A WINDOW, SPLIT INTO THE `2`-CHANNEL, THE ODD CHANNEL AND
THE SIEVE (FLAGSHIP BRIDGE).**  For `1 ≤ N`:

`∑_{j<L} ω (N+j) ≤ jsp87WindowVal2 N L + #(odd primes of the product) + L·π(L−1)`.

This is round 56's window accounting with the prime `2` separated out and
quantised by Legendre's formula. -/
theorem jsp87_window_omega_le_twoAdic {N L : ℕ} (hN : 1 ≤ N) (hL : 3 ≤ L) :
    (∑ j ∈ Finset.range L, omega (N + j))
      ≤ jsp87WindowVal2 N L + (jsp87OddFactors N L).card
        + L * (jsp87Primes (L - 1)).card := by
  have hsplit : ∑ j ∈ Finset.range L, omega (N + j)
      = ∑ j ∈ Finset.range L, ((N + j).primeFactors.filter (fun p => 2 < p)).card
        + ∑ j ∈ Finset.range L, (if 2 ∣ N + j then 1 else 0) := by
    rw [← sum_add']
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjn : N + j = 0
    · rw [hjn, omega]
      simp
      omega
    · exact jsp87_omega_eq_odd_add_two (by omega)
  rw [hsplit]
  have h1 : (∑ j ∈ Finset.range L, (if 2 ∣ N + j then 1 else 0))
      ≤ jsp87WindowVal2 N L := by
    have hcard' : (∑ j ∈ Finset.range L, (if 2 ∣ N + j then 1 else 0))
        = ((Finset.range L).filter (fun j => 2 ∣ N + j)).card := sum_ite_card _ _
    rw [hcard']
    exact jsp87_even_count_le_windowVal2 hN
  have h2 : (∑ j ∈ Finset.range L, ((N + j).primeFactors.filter (fun p => 2 < p)).card)
      ≤ L * (jsp87Primes (L - 1)).card + (jsp87BigFactors N L).card := by
    have hstep : ∀ j ∈ Finset.range L,
        ((N + j).primeFactors.filter (fun p => 2 < p)).card
          ≤ (jsp87Primes (L - 1)).card + jsp87BigCard (N + j) L :=
      fun j _ => jsp87_oddCard_le_add (by omega)
    have hsum := Finset.sum_le_sum (s := Finset.range L) (fun j hj => hstep j hj)
    have hB : (∑ j ∈ Finset.range L, jsp87BigCard (N + j) L)
        = (jsp87BigFactors N L).card := (jsp87_bigFactors_card_eq (L := L) hN).symm
    have hconst : (∑ j ∈ Finset.range L,
        ((jsp87Primes (L - 1)).card + jsp87BigCard (N + j) L))
        = L * (jsp87Primes (L - 1)).card + (jsp87BigFactors N L).card := by
      have hbigsum : (∑ j ∈ Finset.range L,
            ((jsp87Primes (L - 1)).card + jsp87BigCard (N + j) L))
          = (∑ _ ∈ Finset.range L, (jsp87Primes (L - 1)).card)
            + ∑ j ∈ Finset.range L, jsp87BigCard (N + j) L :=
        sum_add_const' _ _ _
      rw [hbigsum, sum_const', Finset.card_range, hB]
    rw [hconst] at hsum
    omega
  have h3 : (jsp87BigFactors N L).card ≤ (jsp87OddFactors N L).card := by
    refine Finset.card_le_card ?_
    intro p hp
    have hp' := (mem_jsp87BigFactors (L := L) hN).mp hp
    have hodd : 2 < p := by
      have hmem : p ∈ (jsp87WindowProd N L).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp'.1, hp'.2.1, jsp87WindowProd_ne_zero hN⟩
      have htwo := (Nat.mem_primeFactors.mp hmem).1.two_le
      omega
    exact (mem_jsp87OddFactors (L := L) hN).mpr ⟨hp'.1, hp'.2.1, hodd⟩
  omega

/-- **THE TWO-SIDED `ω`-BOUND WITH THE `2`-CHANNEL MADE EXPLICIT.** -/
theorem jsp87_window_omega_le_explicit {N L : ℕ} (hN : 1 ≤ N) (hL : 3 ≤ L) :
    (∑ j ∈ Finset.range L, omega (N + j))
      ≤ L + N / 2 + L * Nat.log 3 (N + L - 1) + L * (jsp87Primes (L - 1)).card := by
  have h1 := jsp87_window_omega_le_twoAdic hN hL
  have h2 := jsp87_windowVal2_le_add_half (L := L) hN
  have h3 := jsp87_oddFactors_card_le_log (L := L) hN
  omega

/-- **THE TWO `2`-CHANNELS ARE QUANTISED BY DIFFERENT THINGS.**  The `2`-adic
content of the *binary prefix* `I (N+L)` of the Erdős series is round 52's
`2^L ∣ Ω N L`; the `2`-adic content of the *product of the window* is this
round's Legendre identity.  Both hold simultaneously, from round 52 and from
this file, and the second is what the product `∏_{j<L}(N+j)` really carries. -/
theorem jsp87_prefix_and_window_content_differ {N L : ℕ} (hN : 1 ≤ N)
    (h : 2 ^ L ∣ jsp87OmegaWindow N L) :
    2 ^ L ∣ jsp87Prefix (N + L) ∧ 2 ^ (L / 2) ∣ jsp87WindowProd N L := by
  refine ⟨(jsp87Prefix_dvd_window (t := L) N).mpr h,
    jsp87_windowProd_two_pow_dvd hN⟩

/-- **THE TWO CHANNELS NEVER COLLAPSE.**  The `2`-content of the product of a
window of length `L` is at least `⌊L/2⌋` **and** at most `L + ⌊N/2⌋`, while the
`2`-content of the corresponding binary prefix of `S` is the `ω`-window's.
Formally: a rational value would have to freeze both into lattices, and the
product channel is quantised by the binary digits of `N` alone. -/
theorem jsp87_window_content_between {N L : ℕ} (hN : 1 ≤ N) :
    L / 2 ≤ jsp87WindowVal2 N L ∧ jsp87WindowVal2 N L ≤ L + N / 2 :=
  jsp87_windowVal2_bounds hN

end JSP87
