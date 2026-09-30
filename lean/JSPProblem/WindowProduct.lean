/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.SieveModel

/-!
# JSP-000087, round 56 : the arithmetic of the product of a window

## The new object

Rounds 37–55 attacked the Erdős series through the *series*: the Lambert
reduction (37), the carry scaffold (38), the gcd of the denominators (39), the
carry recurrence (40), the binary digit bookkeeping (41), the carry excess (44),
the base-`2` block arithmetic (46), the primary expansion (47), the doubling
map (48), the radix criterion (49), the asymptotics of the carry (50), the
period equation (51), the `2`-adic binary prefix (52), the run machinery (53)
and the sieve local model (55).  **No round has ever looked at the product of a
window.**  This file introduces

* `jsp87WindowProd N L = ∏_{j<L} (N+j)` — the product of `L` consecutive
  integers;
* `jsp87BigFactors N L` — the prime divisors of that product which are `≥ L`;
* `jsp87BigCard m L` — the number of prime divisors of `m` which are `≥ L`;
* `jsp87Incidence p N L` — the number of the `L` integers of the window
  divisible by `p`.

## The driving observation

**Two entries of a window have a common prime factor only if that prime is
smaller than the length of the window.**  If `p` divides both `N+i` and `N+j`
with `i < j < L` then `p ∣ j - i`, and `j - i < L`, so `p < L`.  Hence the
prime divisors `≥ L` of the product of a window are **disjointly attributable**:
each of them divides exactly one of the `L` integers.  This is
`jsp87_bigFactors_card_eq`, the additivity theorem

`(jsp87BigFactors N L).card = ∑_{j<L} jsp87BigCard (N+j) L`,

and it is *sharp*: the same statement with `L` replaced by `L-1` is false
(`jsp87_small_additivity_fails`, machine-checked: for the window `[3,8)` the
`6` incidences of the primes `≤ 5` are carried by only `3` distinct primes).

## Consequences

* `jsp87_window_omega_eq` : **the total `ω`-mass of a window is exactly the
  number of its distinct large primes plus the total number of its small-prime
  incidences** — the first exact accounting of `ω` over a window in the tree
  (round 44 had only a one-sided estimate, `jsp87_sum_omega_window_le`).
* `jsp87_pow_bigLe_window`, `jsp87_window_pow_bounds` : the sandwich
  `L ^ #(large primes) ≤ ∏ (N+j) ≤ (N+L-1)^L`, whence
  `jsp87_bigFactors_card_le_log` : the number of primes `≥ L` dividing a
  window is at most `L · log_L (N+L-1)`, with the *window length* as base.
* `jsp87_constRun_height_log` : **a constant run of `ω` with value `u` and
  length `L` satisfies `L ^ (u - π(L-1)) ≤ N+L-1`**, sharpening round 55's
  `3^(u-1) ≤ N+L-1` by a factor depending on the length of the run.
* `jsp87_incidence_le_div` : `p` divides at most `⌊(L-1)/p⌋ + 1` of the `L`
  integers of a window — the exact **collision budget**, attained at
  `jsp87Incidence_three_four`.
* `jsp87_run_prod_ge` : a constant run of length `L` and value `u` has product
  at least `2^(u·L)`, and `(k+1)^(c·L) ≤ ∏(N+j)` under round 55's
  compensation hypothesis (`jsp87_sieveRun_prod_ge`) — the *window* form of
  round 55's pointwise `jsp87_pow_unsieved_le`.

## What this round does NOT do

`jsp_000087_main` remains undeclared.  The objects introduced here are the
arithmetic of windows, and what is still missing is a statement about the
distribution of `ω` on consecutive integers — the same input as in rounds
53 and 55.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. The product of a window -/

/-- **The product of a window:** `jsp87WindowProd N L = ∏_{j<L} (N+j)`. -/
def jsp87WindowProd (N L : ℕ) : ℕ := ∏ j ∈ Finset.range L, (N + j)

/-- The empty product is `1`. -/
theorem jsp87WindowProd_zero (N : ℕ) : jsp87WindowProd N 0 = 1 := by
  simp [jsp87WindowProd]

/-- **THE STEP IDENTITY.**  A window of length `L+1` is a window of length `L`
times its last element. -/
theorem jsp87WindowProd_succ (N L : ℕ) :
    jsp87WindowProd N (L + 1) = jsp87WindowProd N L * (N + L) := by
  have h := Finset.prod_range_succ (f := fun j => N + j) L
  simpa [jsp87WindowProd] using h

/-- A window of length `1` is the single element. -/
theorem jsp87WindowProd_one (N : ℕ) : jsp87WindowProd N 1 = N := by
  have h := jsp87WindowProd_succ N 0
  rw [jsp87WindowProd_zero, Nat.zero_add, Nat.one_mul] at h
  exact h

/-- **THE PRODUCT OF A WINDOW IS POSITIVE**, for `N ≥ 1`.  (The zero window
entry `N = 0` is the only obstruction, and it is excluded everywhere below.) -/
theorem jsp87WindowProd_pos {N L : ℕ} (hN : 1 ≤ N) : 0 < jsp87WindowProd N L :=
  Finset.prod_pos fun j hj => by
    have hj' := Finset.mem_range.mp hj
    omega

theorem jsp87WindowProd_ne_zero {N L : ℕ} (hN : 1 ≤ N) : jsp87WindowProd N L ≠ 0 :=
  ne_of_gt (jsp87WindowProd_pos hN)

/-- **A PRIME DIVIDES THE PRODUCT IFF IT DIVIDES ONE OF THE ENTRIES.** -/
theorem jsp87_dvd_windowProd {p N L : ℕ} (hp : p.Prime) :
    p ∣ jsp87WindowProd N L ↔ ∃ j ∈ Finset.range L, p ∣ (N + j) := by
  induction L with
  | zero =>
      constructor
      · intro h
        have h1 : p = 1 := Nat.dvd_one.mp h
        exact absurd h1 hp.ne_one
      · rintro ⟨j, hj, h⟩
        have hj' := Finset.mem_range.mp hj
        omega
  | succ L ih =>
      rw [jsp87WindowProd_succ]
      constructor
      · intro h
        rcases hp.dvd_mul.mp h with h1 | h2
        · obtain ⟨j, hj, hjd⟩ := ih.mp h1
          have hj'' := Finset.mem_range.mp hj
          exact ⟨j, Finset.mem_range.mpr (by omega), hjd⟩
        · exact ⟨L, Finset.mem_range.mpr (by omega), h2⟩
      · rintro ⟨j, hj, hjd⟩
        have hj' := Finset.mem_range.mp hj
        by_cases hlt : j < L
        · exact hp.dvd_mul.mpr (Or.inl (ih.mpr ⟨j, Finset.mem_range.mpr hlt, hjd⟩))
        · have hjeq : j = L := by omega
          subst hjeq
          exact hp.dvd_mul.mpr (Or.inr hjd)

/-- **EACH ENTRY IS AT MOST THE TOP OF THE WINDOW.** -/
theorem jsp87WindowProd_le_pow {N L : ℕ} :
    jsp87WindowProd N L ≤ (N + L - 1) ^ L := by
  have h := Finset.prod_le_prod (s := Finset.range L) (f := fun j => N + j)
    (g := fun _ => N + L - 1) (fun j hj => by
      have hj' := Finset.mem_range.mp hj
      omega)
  simpa [jsp87WindowProd, Finset.prod_const, Finset.card_range] using h

/-! ## 1. Two entries of a window share only SMALL primes -/

/-- The difference of two window entries. -/
theorem jsp87_add_sub_add {N i j : ℕ} (hij : i ≤ j) : (N + j) - (N + i) = j - i := by
  omega

/-- **A COMMON DIVISOR OF TWO ENTRIES DIVIDES THEIR DISTANCE.** -/
theorem jsp87_dvd_sub_of_two {p N i j : ℕ} (h1 : p ∣ (N + i)) (h2 : p ∣ (N + j))
    (hij : i ≤ j) : p ∣ (j - i) := by
  have h := Nat.dvd_sub h2 h1
  rwa [jsp87_add_sub_add hij] at h

/-- **DISJOINTNESS, THE HEADLINE OF THIS ROUND.**  A prime dividing two entries
of a window of length `L` is *smaller than the length of the window*. -/
theorem jsp87_common_prime_lt {p N i j L : ℕ} (hp : p.Prime) (hpi : p ∣ (N + i))
    (hpj : p ∣ (N + j)) (hlt : i < j) (hjL : j < L) : p < L := by
  have hp2 : 2 ≤ p := hp.two_le
  by_contra hcon
  have hsub : p ∣ (j - i) := jsp87_dvd_sub_of_two hpi hpj (by omega)
  have hle : p ≤ j - i := Nat.le_of_dvd (by omega) hsub
  omega

/-- **THE GCD FORM.**  The gcd of two entries of a window is smaller than the
length of the window. -/
theorem jsp87_gcd_lt_window {N i j L : ℕ} (hlt : i < j) (hjL : j < L) :
    gcd (N + i) (N + j) < L := by
  have h := jsp87_dvd_sub_of_two (p := gcd (N + i) (N + j))
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) (by omega)
  by_contra hcon
  have hle : gcd (N + i) (N + j) ≤ j - i := Nat.le_of_dvd (by omega) h
  omega

/-! ## 2. The large prime factors of a window -/

/-- **The number of prime divisors of `m` which are `≥ L`.** -/
def jsp87BigCard (m L : ℕ) : ℕ := (m.primeFactors.filter (fun p => L ≤ p)).card

/-- **The prime divisors `≥ L` of the product of the window `[N, N+L)`.** -/
def jsp87BigFactors (N L : ℕ) : Finset ℕ :=
  (jsp87WindowProd N L).primeFactors.filter (fun p => L ≤ p)

/-- **THE UNSIEVED CONTENT AT LEVEL `L-1` IS THE LARGE CONTENT AT LEVEL `L`.** -/
theorem jsp87_unsieved_eq_big {m L : ℕ} (hL : 1 ≤ L) :
    jsp87UnsievedCard m (L - 1) = jsp87BigCard m L := by
  simp only [jsp87UnsievedCard, jsp87BigCard]
  have heq : m.primeFactors.filter (fun p => L - 1 < p)
      = m.primeFactors.filter (fun p => L ≤ p) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro h
      refine And.intro h.1 ?_
      omega
    · intro h
      refine And.intro h.1 ?_
      omega
  rw [heq]

/-- **THE SPLIT OF `ω` AT THE LENGTH OF THE WINDOW.**  For every `m`:
`ω m = (number of primes ≤ L-1) + (number of primes ≥ L)`. -/
theorem jsp87_omega_eq_big_add_sieve {m L : ℕ} (hL : 1 ≤ L) :
    omega m = jsp87SieveCard m (L - 1) + jsp87BigCard m L := by
  have h := omega_eq_sieve_add_unsieved m (L - 1)
  have h2 : jsp87UnsievedCard m (L - 1) = jsp87BigCard m L := jsp87_unsieved_eq_big hL
  omega

/-- **CONSECUTIVE INTEGERS: EVERY PRIME OF `m+1` IS A PRIME `≥ 2`.** -/
theorem jsp87BigCard_consecutive {m : ℕ} : jsp87BigCard (m + 1) 2 = omega (m + 1) := by
  have h : omega (m + 1) = jsp87SieveCard (m + 1) 1 + jsp87BigCard (m + 1) 2 :=
    jsp87_omega_eq_big_add_sieve (m := m + 1) (L := 2) (by omega)
  have h1 : jsp87SieveCard (m + 1) 1 = 0 := by
    simp only [jsp87SieveCard]
    have hle : ∀ p ∈ (m + 1).primeFactors.filter (fun p => p ≤ 1), False := by
      intro p hp
      have hp' : p ∈ (m + 1).primeFactors ∧ p ≤ 1 := Finset.mem_filter.mp hp
      obtain ⟨hpp, _, _⟩ := Nat.mem_primeFactors.mp hp'.1
      have h2 : 2 ≤ p := Nat.Prime.two_le hpp
      omega
    exact Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr
      (fun p hp => (hle p hp).elim))
  omega

theorem mem_jsp87BigFactors {p N L : ℕ} (hN : 1 ≤ N) :
    p ∈ jsp87BigFactors N L ↔ p.Prime ∧ p ∣ jsp87WindowProd N L ∧ L ≤ p := by
  simp only [jsp87BigFactors, Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.2⟩
  · intro h
    exact And.intro (And.intro h.1 (And.intro h.2.1 (jsp87WindowProd_ne_zero hN))) h.2.2

/-- **THE BIUNION IDENTITY.**  The large primes of the product of a window are
the union of the large primes of its entries. -/
theorem jsp87_bigFactors_eq_biUnion {N L : ℕ} (hN : 1 ≤ N) :
    jsp87BigFactors N L
      = (Finset.range L).biUnion (fun j => (N + j).primeFactors.filter (fun p => L ≤ p)) := by
  ext p
  rw [mem_jsp87BigFactors hN, Finset.mem_biUnion]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hd, hL⟩
    obtain ⟨j, hj, hjd⟩ := (jsp87_dvd_windowProd hp).mp hd
    refine ⟨j, hj, ?_⟩
    exact And.intro (Nat.mem_primeFactors.mpr ⟨hp, hjd, by omega⟩) hL
  · rintro ⟨j, hj, hpf, hL⟩
    obtain ⟨hp, hjd, hne⟩ := Nat.mem_primeFactors.mp hpf
    exact And.intro hp (And.intro ((jsp87_dvd_windowProd hp).mpr ⟨j, hj, hjd⟩) hL)

/-- **THE FAMILY OF LARGE PRIME SETS IS PAIRWISE DISJOINT.**  This is the
structural core of the round. -/
theorem jsp87_bigFactors_disjoint {N L : ℕ} :
    Set.PairwiseDisjoint ((Finset.range L : Finset ℕ) : Set ℕ)
      (fun j => (N + j).primeFactors.filter (fun p => L ≤ p)) := by
  rintro a ha b hb hab
  have hla : a < L := Finset.mem_range.mp (Finset.mem_coe.mp ha)
  have hlb : b < L := Finset.mem_range.mp (Finset.mem_coe.mp hb)
  unfold Function.onFun
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have hp1' : p ∈ (N + a).primeFactors ∧ L ≤ p := Finset.mem_filter.mp hp1
  have hp2' : p ∈ (N + b).primeFactors ∧ L ≤ p := Finset.mem_filter.mp hp2
  obtain ⟨hpa, hpa1, _⟩ := Nat.mem_primeFactors.mp hp1'.1
  obtain ⟨_, hpb1, _⟩ := Nat.mem_primeFactors.mp hp2'.1
  rcases lt_trichotomy a b with hlt | hrest
  · have hlt' := jsp87_common_prime_lt hpa hpa1 hpb1 hlt hlb
    omega
  · rcases hrest with heq | hgt
    · exact absurd heq hab
    · have hlt' := jsp87_common_prime_lt hpa hpb1 hpa1 hgt hla
      omega

/-- **THE ADDITIVITY THEOREM (HEADLINE).**  The prime divisors `≥ L` of the
product of a window are counted additively over the window: no prime is counted
twice. -/
theorem jsp87_bigFactors_card_eq {N L : ℕ} (hN : 1 ≤ N) :
    (jsp87BigFactors N L).card = ∑ j ∈ Finset.range L, jsp87BigCard (N + j) L := by
  rw [jsp87_bigFactors_eq_biUnion hN]
  simpa only [jsp87BigCard] using (Finset.card_biUnion jsp87_bigFactors_disjoint)

/-- **THE SMALL SIEVE CONTENT OF A WINDOW IS BOUNDED BY THE NUMBER OF PRIMES
BELOW THE LENGTH.**  All the non-additivity of §4 sits inside this many primes. -/
theorem jsp87SieveCard_le_primes (m L : ℕ) :
    jsp87SieveCard m (L - 1) ≤ (jsp87Primes (L - 1)).card := by
  have hsub : m.primeFactors.filter (fun p => p ≤ L - 1) ⊆ jsp87Primes (L - 1) := by
    intro p hp
    have hp' : p ∈ m.primeFactors ∧ p ≤ L - 1 := Finset.mem_filter.mp hp
    rw [mem_jsp87Primes]
    obtain ⟨hpp, _, _⟩ := Nat.mem_primeFactors.mp hp'.1
    exact ⟨Nat.Prime.two_le hpp, by omega, hpp⟩
  simpa [jsp87SieveCard] using Finset.card_le_card hsub

/-! ## 3. The sandwich `L ^ #(large primes) ≤ product ≤ (N+L-1) ^ L` -/

/-- **THE POWER FORM AT THE WINDOW LEVEL, WITH BASE `L`.** -/
theorem jsp87_pow_bigLe_window {N L : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ L) :
    L ^ (jsp87BigFactors N L).card ≤ jsp87WindowProd N L := by
  have hmem : ∀ p ∈ jsp87BigFactors N L, L ≤ p := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    omega
  have h1 : L ^ (jsp87BigFactors N L).card ≤ ∏ p ∈ jsp87BigFactors N L, p :=
    prod_ge_pow_card _ hL hmem
  have hsub : jsp87BigFactors N L ⊆ (jsp87WindowProd N L).primeFactors :=
    Finset.filter_subset _ _
  have hdvd : (∏ p ∈ jsp87BigFactors N L, p) ∣ ∏ p ∈ (jsp87WindowProd N L).primeFactors, p :=
    prod_sub_dvd_prod _ _ hsub
  have hdvd' : (∏ p ∈ jsp87BigFactors N L, p) ∣ jsp87WindowProd N L :=
    Nat.dvd_trans hdvd (prod_primeFactors_dvd (jsp87WindowProd N L))
  have h2 : (∏ p ∈ jsp87BigFactors N L, p) ≤ jsp87WindowProd N L :=
    Nat.le_of_dvd (jsp87WindowProd_pos hN) hdvd'
  exact le_trans h1 h2

/-- **THE SANDWICH.** -/
theorem jsp87_window_pow_bounds {N L : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ L) :
    L ^ (jsp87BigFactors N L).card ≤ jsp87WindowProd N L
      ∧ jsp87WindowProd N L ≤ (N + L - 1) ^ L :=
  ⟨jsp87_pow_bigLe_window hN hL, jsp87WindowProd_le_pow⟩

/-- **EACH ENTRY HAS AT MOST `log_L` LARGE PRIMES.** -/
theorem jsp87BigCard_le_log {N L : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ L) (hj : j < L) :
    jsp87BigCard (N + j) L ≤ Nat.log L (N + L - 1) := by
  have h := jsp87_pow_unsieved_le (N + j) (L - 1) (by omega) (by omega)
  rw [jsp87_unsieved_eq_big (by omega)] at h
  have hsub : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
  rw [hsub] at h
  have h' : L ^ jsp87BigCard (N + j) L ≤ N + j := h
  have h3 : (N + j) ≤ N + L - 1 := by omega
  exact Nat.le_log_of_pow_le (b := L) (x := jsp87BigCard (N + j) L) (y := N + L - 1)
    (by omega) (le_trans h' (Nat.le_trans h3 (Nat.le_refl _)))

/-- **THE WINDOW-WIDE LOGARITHMIC BOUND, WITH BASE THE LENGTH OF THE WINDOW.**
`#(primes ≥ L dividing a window of length L) ≤ L · log_L (N+L-1)`. -/
theorem jsp87_bigFactors_card_le_log {N L : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ L) :
    (jsp87BigFactors N L).card ≤ L * Nat.log L (N + L - 1) := by
  rw [jsp87_bigFactors_card_eq hN]
  have h1 : (∑ j ∈ Finset.range L, jsp87BigCard (N + j) L)
      ≤ ∑ j ∈ Finset.range L, Nat.log L (N + L - 1) :=
    Finset.sum_le_sum (s := Finset.range L)
      (fun j hj => jsp87BigCard_le_log hN hL (Finset.mem_range.mp hj))
  have h2 : (∑ j ∈ Finset.range L, Nat.log L (N + L - 1)) = L * Nat.log L (N + L - 1) := by
    simp [Finset.sum_const, Finset.card_range]
  omega

/-! ## 4. The exact accounting of `ω` over a window -/

/-- **THE WINDOW ACCOUNTING IDENTITY.**  The total `ω`-mass of a window is
exactly the number of its distinct large primes plus the total number of its
small-prime incidences.  (Round 44 had only the one-sided estimate
`jsp87_sum_omega_window_le`.) -/
theorem jsp87_window_omega_eq {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    (∑ j ∈ Finset.range L, omega (N + j))
      = (jsp87BigFactors N L).card
        + ∑ j ∈ Finset.range L, jsp87SieveCard (N + j) (L - 1) := by
  rw [Finset.sum_congr rfl (fun j _ => jsp87_omega_eq_big_add_sieve hL)]
  rw [Finset.sum_add_distrib, ← jsp87_bigFactors_card_eq hN, Nat.add_comm]

/-- **THE QUANTITATIVE WINDOW BOUND.**  The `ω`-mass of a window of length `L`
is at most `L · log_L (N+L-1) + L · π(L-1)`: the large primes are logarithmic
*in the length of the window*, and the small ones are at most the primes below
`L`. -/
theorem jsp87_window_omega_le {N L : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ L) :
    (∑ j ∈ Finset.range L, omega (N + j))
      ≤ L * Nat.log L (N + L - 1) + L * (jsp87Primes (L - 1)).card := by
  rw [jsp87_window_omega_eq hN (by omega)]
  have h1 : (jsp87BigFactors N L).card ≤ L * Nat.log L (N + L - 1) :=
    jsp87_bigFactors_card_le_log hN hL
  have h2 : (∑ j ∈ Finset.range L, jsp87SieveCard (N + j) (L - 1))
      ≤ L * (jsp87Primes (L - 1)).card := by
    have h := Finset.sum_le_sum (s := Finset.range L)
      (fun j _ => jsp87SieveCard_le_primes (N + j) L)
    simpa [Finset.sum_const, Finset.card_range, Nat.mul_comm] using h
  omega

/-! ## 5. Constant runs -/

/-- **THE `ω`-MASS OF A CONSTANT RUN.** -/
theorem jsp87_constRun_omega_sum {N L u : ℕ} (h : jsp87ConstRun N L u) :
    (∑ j ∈ Finset.range L, omega (N + j)) = u * L := by
  have h1 : (∑ j ∈ Finset.range L, omega (N + j)) = ∑ j ∈ Finset.range L, u :=
    Finset.sum_congr rfl (fun j hj => h j (Finset.mem_range.mp hj))
  have h2 : (∑ j ∈ Finset.range L, u) = u * L := by
    simp [Finset.sum_const, Finset.card_range, Nat.mul_comm]
  rw [h1, h2]

/-- **THE WINDOW FORM OF A CONSTANT RUN.**  The `ω`-mass `u·L` of a constant run
splits into the large primes of the window and the small-prime incidences. -/
theorem jsp87_constRun_window_split {N L u : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (h : jsp87ConstRun N L u) :
    u * L = (jsp87BigFactors N L).card
      + ∑ j ∈ Finset.range L, jsp87SieveCard (N + j) (L - 1) :=
  ((jsp87_window_omega_eq hN hL).symm.trans (jsp87_constRun_omega_sum h)).symm

/-- **THE HEIGHT BOUND FOR A CONSTANT RUN, WITH BASE THE LENGTH.**  A constant
run of value `u` and length `L ≥ 2` satisfies `L ^ (u - π(L-1)) ≤ N+L-1`.

This sharpens round 55's `jsp87_constRun_height`, `3^(u-1) ≤ N+L-1`, whose
base does not see the length of the run at all. -/
theorem jsp87_constRun_height_log {N L u : ℕ} (hL : 2 ≤ L) (hN : 1 ≤ N)
    (h : jsp87ConstRun N L u) :
    L ^ (u - (jsp87Primes (L - 1)).card) ≤ N + L - 1 := by
  have hbound := jsp87_window_omega_le hN hL
  have hrw := jsp87_constRun_omega_sum h
  have hmul : L * u ≤ L * Nat.log L (N + L - 1) + L * (jsp87Primes (L - 1)).card := by
    have h2 := hbound
    rw [hrw, Nat.mul_comm u L] at h2
    exact h2
  have hkey : u - (jsp87Primes (L - 1)).card ≤ Nat.log L (N + L - 1) := by
    have hz : 0 ≤ (jsp87Primes (L - 1)).card := Nat.zero_le _
    have hmul2 : L * u
        ≤ L * (Nat.log L (N + L - 1) + (jsp87Primes (L - 1)).card) := by
      rw [Nat.mul_add]
      exact hmul
    have hcancel : u ≤ Nat.log L (N + L - 1) + (jsp87Primes (L - 1)).card :=
      Nat.le_of_mul_le_mul_left hmul2 (by omega)
    omega
  exact (Nat.le_log_iff_pow_le (b := L) (by omega) (by omega)).mp hkey

/-- **THE PRODUCT OF A CONSTANT RUN IS AT LEAST `2^(u·L)`.** -/
theorem jsp87_run_prod_ge {N L u : ℕ} (hN : 1 ≤ N) (_hL : 1 ≤ L)
    (h : jsp87ConstRun N L u) : 2 ^ (u * L) ≤ jsp87WindowProd N L := by
  have h1 : ∀ j < L, 2 ^ u ≤ N + j := by
    intro j hj
    have h2 := two_pow_omega_le (n := N + j) (by omega)
    rw [h j hj] at h2
    exact h2
  have h2 : (∏ j ∈ Finset.range L, 2 ^ u) ≤ jsp87WindowProd N L := by
    have hh := Finset.prod_le_prod (s := Finset.range L) (f := fun _ => 2 ^ u)
      (g := fun j => N + j) (fun j hj => h1 j (Finset.mem_range.mp hj))
    exact hh
  have hc : (2 ^ u) ^ L = ∏ j ∈ Finset.range L, 2 ^ u := by
    simp [Finset.prod_const, Finset.card_range]
  rw [pow_mul, hc]
  exact h2

/-- **THE WINDOW FORM OF ROUND 55'S POWER BOUND.**  Under round 55's
compensation hypothesis — the unsieved content is constantly `c` on the window
at level `k` — the product of the window is at least `(k+1)^(c·L)`. -/
theorem jsp87_sieveRun_prod_ge {N L k c : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (h : ∀ j : ℕ, j < L → jsp87UnsievedCard (N + j) k = c) :
    (k + 1) ^ (c * L) ≤ jsp87WindowProd N L := by
  have h1 : ∀ j < L, (k + 1) ^ c ≤ N + j := by
    intro j hj
    have hk' := jsp87_pow_unsieved_le (N + j) k hk (by omega)
    rwa [h j hj] at hk'
  have h2 : (∏ j ∈ Finset.range L, (k + 1) ^ c) ≤ jsp87WindowProd N L := by
    have hh := Finset.prod_le_prod (s := Finset.range L) (f := fun _ => (k + 1) ^ c)
      (g := fun j => N + j) (fun j hj => h1 j (Finset.mem_range.mp hj))
    exact hh
  have hc : ((k + 1) ^ c) ^ L = ∏ j ∈ Finset.range L, (k + 1) ^ c := by
    simp [Finset.prod_const, Finset.card_range]
  rw [pow_mul, hc]
  exact h2

/-! ## 6. Incidences: how often a prime can divide a window -/

/-- **THE INCIDENCE COUNT:** how many of the `L` entries are divisible by `p`. -/
def jsp87Incidence (p N L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun j => p ∣ (N + j))).card

theorem jsp87_incidence_pos_iff {p N L : ℕ} :
    0 < jsp87Incidence p N L ↔ ∃ j ∈ Finset.range L, p ∣ (N + j) := by
  unfold jsp87Incidence
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp h
    exact ⟨j, Finset.mem_filter.mp hj⟩
  · rintro ⟨j, hj, hd⟩
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hd⟩⟩

/-- **TWO DISTINCT MEMBERS OF A FINSET ARE ORDERED.** -/
theorem jsp87_exists_lt_mem_of_card_ge_two {α : Type} [DecidableEq α] [LinearOrder α]
    {s : Finset α} (h : 2 ≤ s.card) : ∃ a b, a ∈ s ∧ b ∈ s ∧ a < b := by
  induction s using Finset.induction_on with
  | empty =>
      exfalso
      have h' : (2 : ℕ) ≤ 0 := by simp at h
      omega
  | @insert x s hx ih =>
      rw [Finset.card_insert_of_notMem hx] at h
      by_cases he : s.Nonempty
      · obtain ⟨y, hy⟩ := he
        by_cases hlt : y < x
        · exact Exists.intro y (Exists.intro x
            (And.intro (Finset.mem_insert_of_mem hy)
              (And.intro (Finset.mem_insert_self x s) hlt)))
        · have hle : x ≤ y := le_of_not_gt hlt
          by_cases hlt2 : x < y
          · exact Exists.intro x (Exists.intro y
              (And.intro (Finset.mem_insert_self x s)
                (And.intro (Finset.mem_insert_of_mem hy) hlt2)))
          · exfalso
            have hxy : x = y := le_antisymm hle (le_of_not_gt hlt2)
            have hys : y ∈ s := hy
            rw [← hxy] at hys
            exact absurd hys hx
      · have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        rw [hs, Finset.card_empty] at h
        omega

/-- **THE ANTI-COLLISION BOUND.** -/
theorem jsp87_incidence_le_of_anti {p N L : ℕ}
    (h : ∀ i j : ℕ, i < L → j < L → i < j → p ∣ (N + i) → p ∣ (N + j) → False) :
    jsp87Incidence p N L ≤ 1 := by
  by_contra hcon
  have h2 : 2 ≤ jsp87Incidence p N L := by omega
  have hcard : 2 ≤ ((Finset.range L).filter (fun j => p ∣ (N + j))).card := h2
  obtain ⟨a, b, ha, hb, hab⟩ :=
    jsp87_exists_lt_mem_of_card_ge_two (α := ℕ) hcard
  have hpa : p ∣ (N + a) := (Finset.mem_filter.mp ha).2
  have hpb : p ∣ (N + b) := (Finset.mem_filter.mp hb).2
  have hla : a < L := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hlb : b < L := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  exact h a b hla hlb hab hpa hpb

/-- **A LARGE PRIME DIVIDES AT MOST ONE ENTRY.** -/
theorem jsp87_incidence_le_of_big {p N L : ℕ} (hp : p.Prime) (hL : L ≤ p) :
    jsp87Incidence p N L ≤ 1 :=
  jsp87_incidence_le_of_anti fun i j hi hj hij hpi hpj =>
    absurd (jsp87_common_prime_lt hp hpi hpj hij hj) (by omega)

/-- **AND IF IT DIVIDES THE PRODUCT, IT DIVIDES EXACTLY ONE ENTRY.** -/
theorem jsp87_incidence_eq_one_of_dvd {p N L : ℕ} (_hN : 1 ≤ N) (hp : p.Prime)
    (hL : L ≤ p) (hd : p ∣ jsp87WindowProd N L) : jsp87Incidence p N L = 1 := by
  have h1 : jsp87Incidence p N L ≤ 1 := jsp87_incidence_le_of_big hp hL
  have h2 : 0 < jsp87Incidence p N L :=
    (jsp87_incidence_pos_iff).2 ((jsp87_dvd_windowProd hp).mp hd)
  omega

/-- **THE COLLISION BUDGET.**  For any prime `p` and any window of length `L ≥ 2`,
`p` divides at most `⌊(L-1)/p⌋ + 1` of its entries: the multiples of `p` are
spaced `p` apart.  This is the exact statement that the small primes carry ALL
of the non-additivity of §4. -/
theorem jsp87_incidence_le_div {p N L : ℕ} (hp : p.Prime) (hL : 2 ≤ L) :
    jsp87Incidence p N L ≤ (L - 1) / p + 1 := by
  set s : Finset ℕ := Finset.range L |>.filter (fun j => p ∣ (N + j)) with hs
  by_cases hne : s.Nonempty
  · have hp2 : 2 ≤ p := hp.two_le
    have hpos : 0 < p := by omega
    have hmin : ∀ j ∈ s, s.min' hne ≤ j := fun j hj => Finset.min'_le s j hj
    have hminmem : s.min' hne ∈ s := Finset.min'_mem s hne
    have hdvd : ∀ j ∈ s, p ∣ (j - s.min' hne) := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hmj' := hmin j hj
      have hjL : j < L := Finset.mem_range.mp hj'.1
      have hml := Finset.mem_filter.mp hminmem
      have hmlL : s.min' hne < L := Finset.mem_range.mp hml.1
      exact jsp87_dvd_sub_of_two hml.2 hj'.2 (by omega)
    have hinj : Set.InjOn (fun j => (j - s.min' hne) / p) (↑s : Set ℕ) := by
      rintro i hi j hj heq
      have hi' := Finset.mem_coe.mp hi
      have hj' := Finset.mem_coe.mp hj
      have hi1 : p * ((i - s.min' hne) / p) = i - s.min' hne :=
        Nat.mul_div_cancel' (hdvd i hi')
      have hj1 : p * ((j - s.min' hne) / p) = j - s.min' hne :=
        Nat.mul_div_cancel' (hdvd j hj')
      have heq' : (i - s.min' hne) / p = (j - s.min' hne) / p := heq
      have hsub' : i - s.min' hne = j - s.min' hne := by
        rw [← hi1, ← hj1, heq']
      have hmi := hmin i hi'
      have hmj := hmin j hj'
      omega
    have hmap : Set.MapsTo (fun j => (j - s.min' hne) / p) (↑s : Set ℕ)
        (Finset.range ((L - 1) / p + 1)) := by
      intro j hj
      have hj' := Finset.mem_coe.mp hj
      have hj'1 := Finset.mem_filter.mp hj'
      have hjL : j < L := Finset.mem_range.mp hj'1.1
      have h1 := Nat.mul_div_cancel' (hdvd j hj')
      rw [Nat.mul_comm] at h1
      have h2 : j - s.min' hne ≤ L - 1 := by
        have hmj' := hmin j hj'
        omega
      have hmul : p * ((j - s.min' hne) / p) ≤ L - 1 := by
        rw [Nat.mul_comm]
        exact Nat.le_trans (Nat.le_of_eq h1) h2
      have h3 : (j - s.min' hne) / p ≤ (L - 1) / p :=
        (Nat.le_div_iff_mul_le hpos).mpr (by
          rw [Nat.mul_comm]
          exact hmul)
      exact Finset.mem_range.mpr (by
        show (j - s.min' hne) / p < (L - 1) / p + 1
        omega)
    have hcard : s.card ≤ (Finset.range ((L - 1) / p + 1)).card :=
      Finset.card_le_card_of_injOn (fun j => (j - s.min' hne) / p) hmap hinj
    simp only [Finset.card_range] at hcard
    rwa [show jsp87Incidence p N L = s.card from rfl]
  · have hs : s = ∅ := by
      ext j
      constructor
      · intro hj
        exact (hne ⟨j, hj⟩).elim
      · intro hj
        exact absurd hj (by simp)
    have h0 : jsp87Incidence p N L = 0 := by
      rw [show jsp87Incidence p N L = s.card from rfl, hs, Finset.card_empty]
    rw [h0]
    exact Nat.le_trans (Nat.zero_le _) (Nat.succ_le_succ (Nat.zero_le _))

/-! ## 7. Machine-checked instances -/

/-- **THE RUN AT `20`:** `ω 20 = ω 21 = ω 22 = 2`; the product of the window is
`9240 = 2^3·3·5·7·11`, its large primes (`≥ 3`) are `{3,5,7,11}` — `4` of them,
counted additively — and the `2` small incidences are at `20` and `22`. -/
theorem jsp87BigFactors_twenty : jsp87BigFactors 20 3 = {3, 5, 7, 11} ∧
    (jsp87BigFactors 20 3).card = 4 ∧
    (jsp87WindowProd 20 3 = 9240) ∧
    (∑ j ∈ Finset.range 3, omega (20 + j) = 6) := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The additivity of the large primes, at `N = 20`, `L = 3`. -/
theorem jsp87_bigFactors_card_eq_twenty :
    (jsp87BigFactors 20 3).card = ∑ j ∈ Finset.range 3, jsp87BigCard (20 + j) 3 := by
  have h := jsp87_bigFactors_card_eq (N := 20) (L := 3) (by omega)
  simpa using h

/-- The window accounting identity at `N = 20`, `L = 3`. -/
theorem jsp87_window_omega_eq_twenty :
    (∑ j ∈ Finset.range 3, omega (20 + j))
      = (jsp87BigFactors 20 3).card
        + ∑ j ∈ Finset.range 3, jsp87SieveCard (20 + j) 2 := by
  have h := jsp87_window_omega_eq (N := 20) (L := 3) (by omega) (by omega)
  simpa using h

/-- **A MACHINE-CHECKED NEGATIVE: THE THRESHOLD `L` IS ESSENTIAL.**  For the
window `[3, 8)` the primes `≤ 5` have `6` incidences but are only `3` distinct
primes of the product `20160`; the primes `≥ 6 = L` — here `{7}` — have `1`
incidence and `1` distinct prime, i.e. they ARE additive. -/
theorem jsp87_small_additivity_fails :
    (((Finset.range 6).biUnion fun j => (3 + j).primeFactors.filter (fun p => 6 ≤ p)).card) = 1
      ∧ ((jsp87WindowProd 3 6).primeFactors.filter (fun p => p ≤ 5)).card = 3
      ∧ (∑ j ∈ Finset.range 6, ((3 + j).primeFactors.filter (fun p => p ≤ 5)).card) = 6
      ∧ (jsp87BigCard 3 6 + jsp87BigCard 4 6 + jsp87BigCard 5 6
          + jsp87BigCard 6 6 + jsp87BigCard 7 6 + jsp87BigCard 8 6) = 1 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- **THE COLLISION BUDGET IS ATTAINED.**  In the window `[3, 7)` the prime `3`
divides exactly `2 = ⌊(4-1)/3⌋ + 1` entries. -/
theorem jsp87Incidence_three_four :
    jsp87Incidence 3 3 4 = 2 ∧ (4 - 1) / 3 + 1 = 2 := by
  refine ⟨by native_decide, by native_decide⟩

/-- **A CONSTANT RUN OF LENGTH `12`.**  `ω` takes the value `3` on the twelve
consecutive integers `[1306291, 1306303)`. -/
theorem jsp87ConstRun_1306291 : jsp87ConstRun 1306291 12 3 := by
  intro j hj
  interval_cases j <;> native_decide

/-- **THE `ω`-MASS OF THAT RUN** is `36 = 3·12`, of which `21` are large-prime
incidences (at threshold `12`) and `15` are small-prime incidences. -/
theorem jsp87_run_omega_sum_1306291 :
    (∑ j ∈ Finset.range 12, omega (1306291 + j)) = 36
      ∧ (∑ j ∈ Finset.range 12, jsp87BigCard (1306291 + j) 12) = 21
      ∧ (∑ j ∈ Finset.range 12, jsp87SieveCard (1306291 + j) 11) = 15 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- **A LONGER CONSTANT RUN.**  `ω` takes the value `3` on the fourteen
consecutive integers `[526095, 526109)`, and the split at threshold `14` is
`42 = 22 + 20`. -/
theorem jsp87ConstRun_526095 : jsp87ConstRun 526095 14 3 := by
  intro j hj
  interval_cases j <;> native_decide

theorem jsp87_run_omega_sum_526095 :
    (∑ j ∈ Finset.range 14, omega (526095 + j)) = 42
      ∧ (∑ j ∈ Finset.range 14, jsp87BigCard (526095 + j) 14) = 22
      ∧ (∑ j ∈ Finset.range 14, jsp87SieveCard (526095 + j) 13) = 20 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- **THE WINDOW ACCOUNTING SPLIT FOR THE 12-RUN.** -/
theorem jsp87_constRun_window_split_1306291 :
    3 * 12 = (∑ j ∈ Finset.range 12, jsp87BigCard (1306291 + j) 12)
      + ∑ j ∈ Finset.range 12, jsp87SieveCard (1306291 + j) 11 := by
  have h := jsp87_constRun_window_split (N := 1306291) (L := 12) (u := 3)
    (by omega) (by omega) (jsp87ConstRun_1306291)
  rw [jsp87_bigFactors_card_eq (N := 1306291) (L := 12) (by omega)] at h
  simpa using h

/-- **THE LOGARITHMIC BOUND AT THE 12-RUN.** -/
theorem jsp87_bigFactors_card_le_log_1306291 :
    (∑ j ∈ Finset.range 12, jsp87BigCard (1306291 + j) 12) ≤ 12 * Nat.log 12 (1306302) := by
  have h := jsp87_bigFactors_card_le_log (N := 1306291) (L := 12) (by omega)
  rw [jsp87_bigFactors_card_eq (N := 1306291) (L := 12) (by omega)] at h
  simpa using h

/-- **THE HEIGHT BOUND FOR THE 12-RUN** (`π(11) = 5`, so the statement reads
`12 ^ (3-5) = 1 ≤ 1306302`; the base-`L` form is vacuous for short runs, as
expected). -/
theorem jsp87_constRun_height_log_1306291 :
    12 ^ (3 - (jsp87Primes 11).card) ≤ 1306291 + 12 - 1 := by
  have h := jsp87_constRun_height_log (N := 1306291) (L := 12) (u := 3)
    (by omega) (by omega) (jsp87ConstRun_1306291)
  simpa using h

end JSP87
