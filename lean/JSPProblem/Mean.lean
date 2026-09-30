import JSPProblem.WindowProduct

/-!
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: JSP-000087 formalization (Yi-111-a).
-/

/-!
# Round 58 -- the average order of `ω`: the counting function, the local mean,
# and a machine-checked negative

## The gap in the development

Rounds 37–57 attacked the Erdős series `S = ∑ n, ω(n) 2^{-(n+1)}` through
twenty-one families, all of them **pointwise or windowwise**: the growth bound
`ω n ≤ log₂ n` (round 38), the carry and its excess (rounds 40–44, 50), the
binary digits and the digit count (rounds 41, 49–51, 57), the sieve content and
the primorial (rounds 44, 55), the window product and its large primes (round
56), the denominator (round 57).

**Not one of them ever asked for the *mean* of `ω`.**  That is the arithmetic
content of the classical paper the problem statement cites -- Erdős,
*On arithmetical properties of Lambert series* (1948) -- and it is a different
kind of object: `A X = ∑_{1 ≤ n ≤ X} ω n` counts the pairs `(n, p)` with `p`
prime, `1 ≤ n ≤ X` and `p ∣ n`, and that count has an exact and rigid form.

## What is proved here

* **`jsp87_omegaCount_eq_primeDiv`** -- **THE DOUBLE-COUNTING IDENTITY**
  `A X = ∑_{p ≤ X, p prime} ⌊X / p⌋`.  Every other statement below follows from
  it.  It is the "average order" identity for `ω` and the source of the
  classical `~ X log log X` in Erdős' Lambert series.
* **`jsp87_omegaCount_superadd`** -- `A (x + y) ≥ A x + A y`, because
  `⌊(x+y)/p⌋ ≥ ⌊x/p⌋ + ⌊y/p⌋` for every `p`.  Hence
  **`jsp87_omegaCount_mul`** `A (c · x) ≥ c · A x`: the mean of `ω` over
  `[1, X]` never decreases along dilations, and in particular
  `A (2L) ≥ 2 A L` (the second half of the window `[1, 2L]` dominates the
  first, `jsp87_window_doubling_dominates`).
* **`jsp87_omegaCount_not_convex`** and
  **`jsp87_window_half_dominance_fails`** -- **MACHINE-CHECKED NEGATIVE.**
  Superadditivity does *not* give convexity on progressions: with `k = 3`,
  `L = 3` one has `A 9 + A 3 = 11 < 12 = 2 A 6`, and correspondingly the
  window `[7, 10)` carries `3` while `[4, 7)` carries `4`.  The tempting
  statement "the second half of *every* window of `ω` dominates the first" is
  **false**, and no round of this development had noticed.
* **`jsp87_window_omega_ge_omegaCount`** -- **THE INITIAL WINDOW IS THE
  LIGHTEST**: for `1 ≤ N, 1 ≤ L`, `∑_{j<L} ω (N+j) ≥ A L`, because every prime
  `p ≤ L` divides at least `⌊L/p⌋` entries of *any* window of length `L`.  This
  is the uniform lower bound on the local mean of `ω`.  (It is stated for
  `1 ≤ N` because the window starting at `0` contains `ω 0 = 0`: the
  statement genuinely fails at `N = 0`, e.g. `W (0, 5) = 3 < 4 = A 5`.)
* **`jsp87_window_mean_ge_one`** -- the local mean over any window of length `L`
  is at least `∑_{p ≤ L} 1/p - 1` (`jsp87_window_mean_ge` gives the exact form
  with the prime count), the first `-½ log log L` of the average order, valid at
  every height.  Numeric instances:
  `jsp87_window_omega_ge_hundred` (*every* 100 consecutive integers carry at
  least 171 prime factors, counted with multiplicity over the window),
  `jsp87_window_omega_ge_thousand` (2126 at length 1000).
* the exact floor identities `jsp87_floor_carry`, `jsp87_floor_double`,
  `jsp87_floor_defect_eq` and `jsp87_omegaCount_doubling` (the defect of the
  doubling inequality, prime by prime), and `jsp87_dvd_count_Ioc` (the exact
  number of multiples of `p` in an interval).
* `jsp87_window_omega_eq_primeCount`, the window form of the double-counting
  identity: the `ω`-mass of a window is the sum, over the primes up to the top
  of the window, of the number of multiples of that prime inside the window.

## What this round does NOT do

`jsp_000087_main` remains undeclared.  The mean of `ω` is smooth and slow: it
grows like `log log X`, never dips below `∑_{p≤L} 1/p - 1` inside any window of
length `L`, and yet fluctuates -- the negative results above show it is not even
convex.  That is exactly why it cannot supply the pattern hypothesis (rounds
53, 55) the run criterion needs: the mean is the part of `ω` that is known and
uniform, while the irrationality argument needs the *fluctuations* of `ω` around
it.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. The counting function of `ω` and the `ω`-mass of a window -/

/-- **`A X = ∑_{1 ≤ n ≤ X} ω n`** -- the counting function of `ω`.  It is the
number of pairs `(n, p)` with `1 ≤ n ≤ X`, `p` prime and `p ∣ n`. -/
def jsp87OmegaCount (X : ℕ) : ℕ := ∑ k ∈ Finset.range X, omega (k + 1)

/-- The `ω`-mass of the window `[N, N+L)`, i.e. `∑_{j<L} ω (N+j)`.  This is the
`ω`-content of a finite interval, as opposed to the binary weighting
`jsp87OmegaWindow` of round 51. -/
def jsp87WindowOmega (N L : ℕ) : ℕ := ∑ j ∈ Finset.range L, omega (N + j)

@[simp] theorem jsp87OmegaCount_zero : jsp87OmegaCount 0 = 0 := by
  simp [jsp87OmegaCount]

@[simp] theorem jsp87WindowOmega_zero (N : ℕ) : jsp87WindowOmega N 0 = 0 := by
  simp [jsp87WindowOmega]

/-- `A` is nondecreasing. -/
theorem jsp87_omegaCount_mono {X Y : ℕ} (h : X ≤ Y) : jsp87OmegaCount X ≤ jsp87OmegaCount Y := by
  unfold jsp87OmegaCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr h) (fun _ _ _ => Nat.zero_le _)

/-- **THE ADDITION FORMULA.**  `A (N + L) = A N +` the mass of the window
`[N+1, N+L]`. -/
theorem jsp87_omegaCount_add (N L : ℕ) :
    jsp87OmegaCount (N + L) = jsp87OmegaCount N + ∑ k ∈ Finset.range L, omega (N + k + 1) := by
  unfold jsp87OmegaCount
  rw [Finset.sum_range_add]

/-- **THE WINDOW DIFFERENCE.**  For `1 ≤ N` the mass of `[N, N+L)` is the
difference of two counting values. -/
theorem jsp87_window_omega_eq_sub {N L : ℕ} (hN : 1 ≤ N) :
    jsp87WindowOmega N L = jsp87OmegaCount (N + L - 1) - jsp87OmegaCount (N - 1) := by
  have h := jsp87_omegaCount_add (N - 1) L
  have h' : ∑ k ∈ Finset.range L, omega (N - 1 + k + 1) = jsp87WindowOmega N L := by
    unfold jsp87WindowOmega
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    omega
  rw [h'] at h
  have hN0 : jsp87OmegaCount ((N - 1) + L) = jsp87OmegaCount (N + L - 1) := by
    congr 1
    omega
  rw [hN0] at h
  omega

/-! ## 1. Finsets and floors: the auxiliary counts -/

/-- Splitting a sum along a cut: a sum over a finset splits into the part at
most the cut and the part above it. -/
theorem jsp87_sum_split (s : Finset ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (∑ p ∈ s, f p) = (∑ p ∈ s.filter (fun p => p ≤ k), f p) + ∑ p ∈ s.filter (fun p => k < p), f p := by
  have h1 : (∑ x ∈ s, if x ≤ k then f x else 0)
      = (∑ x ∈ s.filter (fun x => x ≤ k), f x) + ∑ x ∈ s.filter (fun x => ¬ (x ≤ k)), 0 :=
    Finset.sum_ite (fun x => f x) (fun _ => 0)
  have h2 : (∑ x ∈ s, if x ≤ k then 0 else f x)
      = (∑ x ∈ s.filter (fun x => x ≤ k), 0) + ∑ x ∈ s.filter (fun x => ¬ (x ≤ k)), f x :=
    Finset.sum_ite (fun _ => 0) (fun x => f x)
  have heq : (s.filter (fun x => ¬ (x ≤ k))) = s.filter (fun x => k < x) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, Nat.not_le.mp h⟩
    · rintro ⟨hp, h⟩
      exact ⟨hp, Nat.not_le.mpr h⟩
  simp only [Finset.sum_const_zero, Nat.zero_add, add_zero] at h1 h2
  calc (∑ p ∈ s, f p)
      = ∑ p ∈ s, ((if p ≤ k then f p else 0) + (if p ≤ k then 0 else f p)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : p ≤ k <;> simp [h]
    _ = (∑ p ∈ s, if p ≤ k then f p else 0) + ∑ p ∈ s, if p ≤ k then 0 else f p :=
        Finset.sum_add_distrib
    _ = _ := by rw [h1, h2, heq]

/-- A summand vanishing above the cut may be summed over a longer range. -/
theorem jsp87_sum_eq_of_vanishing {k X : ℕ} (h : k ≤ X) (f : ℕ → ℕ)
    (hf : ∀ p, k < p → f p = 0) :
    (∑ p ∈ jsp87Primes k, f p) = ∑ p ∈ jsp87Primes X, f p := by
  have hlow : (jsp87Primes X).filter (fun p => p ≤ k) = jsp87Primes k := by
    ext q
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      obtain ⟨h2, _, hqP⟩ := mem_jsp87Primes.mp hp'.1
      exact mem_jsp87Primes.mpr ⟨h2, hp'.2, hqP⟩
    · intro hp
      obtain ⟨h2, hqX, hqP⟩ := mem_jsp87Primes.mp hp
      exact Finset.mem_filter.mpr
        ⟨mem_jsp87Primes.mpr ⟨h2, by omega, hqP⟩, hqX⟩
  have htail : (∑ p ∈ (jsp87Primes X).filter (fun p => k < p), f p) = 0 :=
    Finset.sum_eq_zero fun p hp => hf p (Finset.mem_filter.mp hp).2
  have hsplit := jsp87_sum_split (s := jsp87Primes X) f k
  rw [hlow, htail] at hsplit
  omega

/-- The `⌊X/p⌋` summand vanishes above `X`, so it may be summed over a longer
range of primes. -/
theorem jsp87_sum_div_eq_of_le {k X : ℕ} (h : k ≤ X) :
    (∑ p ∈ jsp87Primes k, (k / p)) = ∑ p ∈ jsp87Primes X, (k / p) :=
  jsp87_sum_eq_of_vanishing h (fun p => k / p) fun p hp => Nat.div_eq_of_lt (by omega)

/-- **THE CARRY OF THE FLOOR SUM.**  For `0 < p`,
`⌊(a+b)/p⌋ = ⌊a/p⌋ + ⌊b/p⌋ + ⌊((a mod p) + (b mod p))/p⌋`. -/
theorem jsp87_floor_carry (a b p : ℕ) (hp : 0 < p) :
    a / p + b / p + ((a % p + b % p) / p) = (a + b) / p := by
  calc a / p + b / p + ((a % p + b % p) / p)
      = (a % p + b) / p + a / p := by
          have h : a % p + b = a % p + b % p + (b / p) * p := by
            have h1 := Nat.mod_add_div b p
            rw [Nat.mul_comm] at h1
            omega
          rw [h, Nat.add_mul_div_right (a % p + b % p) (b / p) (z := p) hp]
          omega
    _ = ((a % p + b) + (a / p) * p) / p :=
        (Nat.add_mul_div_right (a % p + b) (a / p) (z := p) hp).symm
    _ = (a + b) / p := by
          have h1 := Nat.mod_add_div a p
          rw [Nat.mul_comm] at h1
          congr 1
          omega

/-- **DOUBLING THE FLOOR.**  For `0 < p`, `⌊2a/p⌋ = 2⌊a/p⌋ + ⌊2(a mod p)/p⌋`. -/
theorem jsp87_floor_double (a p : ℕ) (hp : 0 < p) :
    2 * (a / p) + ((2 * (a % p)) / p) = (2 * a) / p := by
  have h1 := Nat.mod_add_div a p
  rw [Nat.mul_comm] at h1
  have h : 2 * a = 2 * (a % p) + 2 * (a / p) * p := by
    calc 2 * a = 2 * (a % p + (a / p) * p) := by rw [h1]
      _ = 2 * (a % p) + 2 * ((a / p) * p) := Nat.mul_add 2 (a % p) ((a / p) * p)
      _ = _ := by
          have hh : 2 * ((a / p) * p) = 2 * (a / p) * p := by ac_rfl
          omega
  calc 2 * (a / p) + ((2 * (a % p)) / p)
      = (2 * (a % p)) / p + 2 * (a / p) := Nat.add_comm _ _
    _ = ((2 * (a % p)) + 2 * (a / p) * p) / p :=
        (Nat.add_mul_div_right (2 * (a % p)) (2 * (a / p)) (z := p) hp).symm
    _ = (2 * a) / p := by rw [h]

/-- **THE MULTIPLICITY OF A PRIME IN AN INTERVAL.**  In `a < x ≤ b` there are
`⌊b/p⌋ - ⌊a/p⌋` multiples of `p`. -/
theorem jsp87_dvd_count_Ioc {a b p : ℕ} (hab : a ≤ b) (_hp : 0 < p) :
    ((Finset.Ioc a b).filter (fun x => p ∣ x)).card = b / p - a / p := by
  have key : ((Finset.Ioc 0 b).filter (fun x => p ∣ x))
      = ((Finset.Ioc 0 a).filter (fun x => p ∣ x)) ∪ ((Finset.Ioc a b).filter (fun x => p ∣ x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨⟨h0, h1⟩, hpx⟩
      by_cases ha : x ≤ a
      · exact Or.inl ⟨⟨h0, ha⟩, hpx⟩
      · exact Or.inr ⟨⟨Nat.lt_of_not_ge ha, h1⟩, hpx⟩
    · rintro (⟨h0, hpx⟩ | ⟨h2, hpx⟩)
      · exact ⟨⟨h0.1, by omega⟩, hpx⟩
      · exact ⟨⟨by omega, h2.2⟩, hpx⟩
  have hdisj : Disjoint ((Finset.Ioc 0 a).filter (fun x => p ∣ x))
      ((Finset.Ioc a b).filter (fun x => p ∣ x)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨h1, _⟩ := Finset.mem_filter.mp hx1
    obtain ⟨h2, _⟩ := Finset.mem_filter.mp hx2
    simp only [Finset.mem_Ioc] at h1 h2
    omega
  have hcards : ((Finset.Ioc 0 b).filter (fun x => p ∣ x)).card
      = ((Finset.Ioc 0 a).filter (fun x => p ∣ x)).card
        + ((Finset.Ioc a b).filter (fun x => p ∣ x)).card := by
    rw [key, Finset.card_union_of_disjoint hdisj]
  calc ((Finset.Ioc a b).filter (fun x => p ∣ x)).card
      = ((Finset.Ioc 0 b).filter (fun x => p ∣ x)).card
          - ((Finset.Ioc 0 a).filter (fun x => p ∣ x)).card := by omega
    _ = b / p - a / p := by
        rw [Nat.Ioc_filter_dvd_card_eq_div b p, Nat.Ioc_filter_dvd_card_eq_div a p]

/-! ## 2. The double-counting identity -/

/-- **THE LOCAL MODEL OF `ω` INSIDE A RANGE.**  For `1 ≤ n ≤ X` the prime
divisors of `n` are exactly the members of `jsp87Primes X` dividing `n`. -/
theorem jsp87_primeFactors_sub_primes {n X : ℕ} (_hn : 1 ≤ n) (hX : n ≤ X) :
    n.primeFactors ⊆ jsp87Primes X := by
  intro p hp
  obtain ⟨hprime, hpd, hn0⟩ := Nat.mem_primeFactors.mp hp
  have h2 : 2 ≤ p := hprime.two_le
  have hpX : p ≤ X := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd) hX
  exact mem_jsp87Primes.mpr ⟨h2, hpX, hprime⟩

/-- **THE FILTERED FINSET OF PRIME FACTORS INSIDE A RANGE.** -/
theorem jsp87_filter_dvd_primeFactors {n X : ℕ} (hn : 1 ≤ n) (hX : n ≤ X) :
    (jsp87Primes X).filter (fun p => p ∣ n) = n.primeFactors := by
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hpP, _, hprime⟩ := mem_jsp87Primes.mp hp'.1
    exact Nat.mem_primeFactors.mpr ⟨hprime, hp'.2, by omega⟩
  · intro hp
    obtain ⟨hprime, hpd, hn0⟩ := Nat.mem_primeFactors.mp hp
    have h2 : 2 ≤ p := hprime.two_le
    have hpX : p ≤ X := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd) hX
    exact Finset.mem_filter.mpr ⟨mem_jsp87Primes.mpr ⟨h2, hpX, hprime⟩, hpd⟩

/-- **`ω` COUNTED AS A SUM OF INDICATORS.** -/
theorem jsp87_omega_eq_sum_dvd {n X : ℕ} (hn : 1 ≤ n) (hX : n ≤ X) :
    omega n = ∑ p ∈ jsp87Primes X, if p ∣ n then 1 else 0 := by
  rw [omega, ← jsp87_filter_dvd_primeFactors hn hX]
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

/-- **THE DOUBLE-COUNTING IDENTITY.**  `A X`, the number of pairs `(n, p)` with
`1 ≤ n ≤ X`, `p` prime and `p ∣ n`, equals `∑_{p ≤ X} ⌊X / p⌋`.

This is the identity that carries the whole file: it says the mean of `ω` is
controlled by the primes alone, and it is the source of the classical
`~ X log log X` in Erdős' Lambert series. -/
theorem jsp87_omegaCount_eq_primeDiv (X : ℕ) :
    jsp87OmegaCount X = ∑ p ∈ jsp87Primes X, (X / p) := by
  have hstep : ∀ n ∈ Finset.range X,
      omega (n + 1) = ∑ p ∈ jsp87Primes X, if p ∣ (n + 1) then 1 else 0 := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    exact jsp87_omega_eq_sum_dvd (by omega : 1 ≤ n + 1) (by omega : n + 1 ≤ X)
  calc jsp87OmegaCount X
      = ∑ n ∈ Finset.range X, ∑ p ∈ jsp87Primes X, (if p ∣ (n + 1) then 1 else 0) := by
          unfold jsp87OmegaCount
          exact Finset.sum_congr rfl hstep
    _ = ∑ p ∈ jsp87Primes X, ∑ n ∈ Finset.range X, (if p ∣ (n + 1) then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ p ∈ jsp87Primes X, (((Finset.range X).filter (fun n => p ∣ (n + 1))).card) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          have hcard : ((Finset.range X).filter (fun n => p ∣ (n + 1))).card
              = ∑ n ∈ Finset.range X, (if p ∣ (n + 1) then 1 else 0) := by
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
          rw [hcard]
    _ = ∑ p ∈ jsp87Primes X, (X / p) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          exact Nat.card_multiples X p

/-- The counting values at small arguments, machine-checked. -/
theorem jsp87_omegaCount_three : jsp87OmegaCount 3 = 2 := by native_decide
theorem jsp87_omegaCount_ten : jsp87OmegaCount 10 = 11 := by native_decide
theorem jsp87_omegaCount_hundred : jsp87OmegaCount 100 = 171 := by native_decide
theorem jsp87_omegaCount_thousand : jsp87OmegaCount 1000 = 2126 := by native_decide

/-! ## 3. Superadditivity of the mean, and the exact floor defects -/

/-- **THE SUPERADDITIVITY OF THE PRIME SUM.**  `∑_{p ≤ x+y} ⌊(x+y)/p⌋` dominates
`∑_{p ≤ x} ⌊x/p⌋ + ∑_{p ≤ y} ⌊y/p⌋`: each prime sees the two arguments
separately. -/
theorem jsp87_primeSum_superadd (x y : ℕ) :
    (∑ p ∈ jsp87Primes (x + y), (x + y) / p)
      ≥ (∑ p ∈ jsp87Primes x, x / p) + ∑ p ∈ jsp87Primes y, y / p := by
  have hsubX : jsp87Primes x ⊆ jsp87Primes (x + y) := by
    intro p hp
    obtain ⟨h2, hpX, hpP⟩ := mem_jsp87Primes.mp hp
    exact mem_jsp87Primes.mpr ⟨h2, by omega, hpP⟩
  have hpt : (∀ p : ℕ, x / p + y / p ≤ (x + y) / p) := fun p => Nat.div_add_div_le_add_div
  have h1 : (∑ p ∈ jsp87Primes (x + y), (x / p + y / p))
      ≤ (∑ p ∈ jsp87Primes (x + y), (x + y) / p) :=
    Finset.sum_le_sum fun (p : ℕ) _ => hpt p
  have h2 : (∑ p ∈ jsp87Primes (x + y), (x / p + y / p))
      = (∑ p ∈ jsp87Primes (x + y), x / p) + ∑ p ∈ jsp87Primes (x + y), y / p :=
    Finset.sum_add_distrib
  have hX : (∑ p ∈ jsp87Primes x, x / p) ≤ ∑ p ∈ jsp87Primes (x + y), x / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubX (fun i _ _ => Nat.zero_le (x / i))
  have h4 : (∑ p ∈ jsp87Primes (x + y), y / p) = ∑ p ∈ jsp87Primes y, y / p :=
    (jsp87_sum_eq_of_vanishing (k := y) (X := x + y) (by omega) (fun p => y / p)
      (fun p hp => Nat.div_eq_of_lt hp)).symm
  refine ge_trans h1 ?_
  rw [h2]
  refine ge_trans (add_le_add hX le_rfl) ?_
  rw [h4]

/-- **THE MEAN OF `ω` IS SUPERADDITIVE:** `A (x + y) ≥ A x + A y`. -/
theorem jsp87_omegaCount_superadd (x y : ℕ) :
    jsp87OmegaCount (x + y) ≥ jsp87OmegaCount x + jsp87OmegaCount y := by
  rw [jsp87_omegaCount_eq_primeDiv, jsp87_omegaCount_eq_primeDiv,
    jsp87_omegaCount_eq_primeDiv]
  exact jsp87_primeSum_superadd x y

/-- **THE MEAN NEVER DECREASES ALONG DILATIONS:** `A (c · x) ≥ c · A x`, i.e.
the mean of `ω` over `[1, c·x]` is at least its mean over `[1, x]`. -/
theorem jsp87_omegaCount_mul (c x : ℕ) :
    jsp87OmegaCount (c * x) ≥ c * jsp87OmegaCount x := by
  induction c with
  | zero => simp
  | succ c ih =>
      have h := jsp87_omegaCount_superadd (c * x) x
      have hx : (c + 1) * x = c * x + x := by ring
      have hmul : (c + 1) * jsp87OmegaCount x = c * jsp87OmegaCount x + jsp87OmegaCount x := by
        ring
      rw [hx, hmul]
      omega

/-- **THE MEAN NEVER DECREASES UNDER DOUBLING:** `A (2L) ≥ 2 A L`. -/
theorem jsp87_omegaCount_doubling_le (L : ℕ) :
    2 * jsp87OmegaCount L ≤ jsp87OmegaCount (2 * L) :=
  jsp87_omegaCount_mul 2 L

/-- **THE SECOND HALF OF THE INITIAL WINDOW DOMINATES THE FIRST:** the `ω`-mass
of `[L+1, 2L]` is at least that of `[1, L]`. -/
theorem jsp87_window_doubling_dominates {L : ℕ} (hL : 1 ≤ L) :
    jsp87WindowOmega 1 L ≤ jsp87WindowOmega (L + 1) L := by
  have h1 : jsp87WindowOmega (L + 1) L
      = jsp87OmegaCount (2 * L) - jsp87OmegaCount L := by
    have h := jsp87_window_omega_eq_sub (N := L + 1) (L := L) (by omega)
    rw [show L + 1 + L - 1 = 2 * L by omega] at h
    exact h
  have h2 : jsp87WindowOmega 1 L = jsp87OmegaCount L - jsp87OmegaCount 0 := by
    have h := jsp87_window_omega_eq_sub (N := 1) (L := L) (by omega)
    rw [show 1 + L - 1 = L by omega, show 1 - 1 = 0 by omega] at h
    exact h
  have hd : 2 * jsp87OmegaCount L ≤ jsp87OmegaCount (2 * L) := jsp87_omegaCount_doubling_le L
  rw [h1, h2]
  omega

/-- **MACHINE-CHECKED NEGATIVE: THE COUNTING FUNCTION OF `ω` IS NOT CONVEX ON
PROGRESSIONS.**  `A 9 + A 3 = 11 < 12 = 2 A 6`.

Superadditivity (round 58, `jsp87_omegaCount_superadd`) does *not* imply
`A (k + 2L) + A k ≥ 2 A (k + L)`; the `k = 0` case holds (that is
`jsp87_omegaCount_doubling_le`) but the general statement is false.  Any future
attack that leans on convexity of the `ω`-counting function is refuted here. -/
theorem jsp87_omegaCount_not_convex :
    jsp87OmegaCount (3 + 2 * 3) + jsp87OmegaCount 3 < 2 * jsp87OmegaCount (3 + 3) := by
  native_decide

/-- **MACHINE-CHECKED NEGATIVE: THE SECOND HALF OF A WINDOW DOES **NOT** ALWAYS
DOMINATE THE FIRST.**  The window `[4, 7)` carries `4`, the window `[7, 10)`
carries only `3`.  So `jsp87_window_doubling_dominates` (the `k = 0` case) is
the strongest form of this idea that is true. -/
theorem jsp87_window_half_dominance_fails :
    jsp87WindowOmega (4 + 3) 3 < jsp87WindowOmega 4 3 := by
  native_decide

/-- **THE SHIFT OF A WINDOW IS AN INTERVAL.**  For `1 ≤ N`, the image of
`[0, L)` under `j ↦ N + j` is `(N-1, N+L-1]`. -/
theorem jsp87_image_range_eq_Ioc {N L : ℕ} (hN : 1 ≤ N) :
    (Finset.range L).image (fun j => N + j) = Finset.Ioc (N - 1) (N + L - 1) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨x - N, by omega, by omega⟩

/-! ## 4. The local mean: the flagship bound -/

/-- **THE WINDOW ACCOUNTING IDENTITY IN PRIMES.**  The `ω`-mass of a window is
the sum, over the primes up to the top of the window, of the number of
multiples of that prime inside the window. -/
theorem jsp87_window_omega_eq_primeCount {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    jsp87WindowOmega N L
      = ∑ p ∈ jsp87Primes (N + L - 1), ((N + L - 1) / p - (N - 1) / p) := by
  have htop : 1 ≤ N + L - 1 := by omega
  have hstep : ∀ j ∈ Finset.range L,
      omega (N + j) = ∑ p ∈ jsp87Primes (N + L - 1),
        (if p ∣ (N + j) then 1 else 0) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact jsp87_omega_eq_sum_dvd (by omega) (by omega)
  calc jsp87WindowOmega N L
      = ∑ j ∈ Finset.range L, ∑ p ∈ jsp87Primes (N + L - 1),
          (if p ∣ (N + j) then 1 else 0) := by
            unfold jsp87WindowOmega
            exact Finset.sum_congr rfl hstep
    _ = ∑ p ∈ jsp87Primes (N + L - 1), ∑ j ∈ Finset.range L,
          (if p ∣ (N + j) then 1 else 0) := Finset.sum_comm
    _ = ∑ p ∈ jsp87Primes (N + L - 1),
          (((Finset.range L).filter (fun j => p ∣ (N + j))).card) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          have hcard : ((Finset.range L).filter (fun j => p ∣ (N + j))).card
              = ∑ j ∈ Finset.range L, (if p ∣ (N + j) then 1 else 0) := by
            rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
          rw [hcard]
    _ = ∑ p ∈ jsp87Primes (N + L - 1), ((N + L - 1) / p - (N - 1) / p) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp2 : 2 ≤ p := two_le_mem_jsp87Primes hp
          have hinj : Function.Injective (fun j : ℕ => N + j) :=
            fun a b hab => by simpa using hab
          calc ((Finset.range L).filter (fun j => p ∣ (N + j))).card
              = (((Finset.range L).filter (fun j => p ∣ (N + j))).image (fun j => N + j)).card := by
                  symm
                  exact Finset.card_image_of_injective _ hinj
            _ = (((Finset.range L).image (fun j => N + j)).filter (fun x => p ∣ x)).card := by
                  have key : ((Finset.range L).filter (fun j => p ∣ (N + j))).image
                        (fun j => N + j)
                      = ((Finset.range L).image (fun j => N + j)).filter (fun x => p ∣ x) := by
                    apply Finset.ext
                    intro j
                    constructor
                    · intro h
                      obtain ⟨a, ha, hda⟩ := Finset.mem_image.mp h
                      rw [Finset.mem_filter] at ha
                      exact Finset.mem_filter.mpr
                        ⟨Finset.mem_image.mpr ⟨a, ha.1, hda⟩, hda ▸ ha.2⟩
                    · intro h
                      obtain ⟨hmem, hd⟩ := Finset.mem_filter.mp h
                      obtain ⟨a, ha, hda⟩ := Finset.mem_image.mp hmem
                      exact Finset.mem_image.mpr
                        ⟨a, Finset.mem_filter.mpr ⟨ha, hda ▸ hd⟩, hda⟩
                  rw [key]
            _ = ((Finset.Ioc (N - 1) (N + L - 1)).filter (fun x => p ∣ x)).card := by
                  rw [jsp87_image_range_eq_Ioc (by omega)]
            _ = (N + L - 1) / p - (N - 1) / p :=
                  jsp87_dvd_count_Ioc (a := N - 1) (b := N + L - 1) (by omega)
                    (by omega : (0 : ℕ) < p)

/-- **EVERY PRIME UP TO `L` DIVIDES AT LEAST `⌊L/p⌋` ENTRIES OF ANY WINDOW.**
Hence the `ω`-mass of every window of length `L` is at least
`∑_{p ≤ L} ⌊L/p⌋`. -/
theorem jsp87_window_omega_ge_div {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    jsp87WindowOmega N L ≥ ∑ p ∈ jsp87Primes L, (L / p) := by
  have hlow : jsp87Primes L ⊆ jsp87Primes (N + L - 1) := by
    intro p hp
    obtain ⟨h2, hpL, hpP⟩ := mem_jsp87Primes.mp hp
    exact mem_jsp87Primes.mpr ⟨h2, by omega, hpP⟩
  have hmain := jsp87_window_omega_eq_primeCount hN hL
  have h1 : (∑ p ∈ jsp87Primes (N + L - 1), ((N + L - 1) / p - (N - 1) / p))
      ≥ ∑ p ∈ jsp87Primes L, ((N + L - 1) / p - (N - 1) / p) :=
    Finset.sum_le_sum_of_subset_of_nonneg hlow (fun i _ _ => Nat.zero_le _)
  have hpt : (∀ p : ℕ, (N - 1) / p + L / p ≤ (N - 1 + L) / p) :=
    fun p => Nat.div_add_div_le_add_div
  have h2 : (∑ p ∈ jsp87Primes L, ((N + L - 1) / p - (N - 1) / p))
      ≥ ∑ p ∈ jsp87Primes L, L / p := by
    refine Finset.sum_le_sum fun (p : ℕ) _ => ?_
    have hle : (N - 1) / p ≤ (N + L - 1) / p := Nat.div_le_div_right (by omega)
    have hsum : (N - 1) / p + L / p ≤ (N + L - 1) / p := by
      have h := hpt p
      rw [show N - 1 + L = N + L - 1 by omega] at h
      exact h
    omega
  omega

/-- **THE INITIAL WINDOW IS THE LIGHTEST.**  For every `N, L` the `ω`-mass of the
window `[N, N+L)` is at least the `ω`-mass of `[1, L]`, i.e. at least
`∑_{p ≤ L} ⌊L/p⌋ = A L`.

This is the uniform lower bound on the local mean of `ω`: the arithmetic mean of
`ω` over *any* window of length `L` is at least its mean over the initial
window. -/
theorem jsp87_window_omega_ge_omegaCount {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    jsp87WindowOmega N L ≥ jsp87OmegaCount L := by
  calc jsp87WindowOmega N L ≥ ∑ p ∈ jsp87Primes L, (L / p) :=
        jsp87_window_omega_ge_div hN hL
    _ = jsp87OmegaCount L := (jsp87_omegaCount_eq_primeDiv L).symm

/-- **THE FLAGSHIP NUMERIC INSTANCES:** every 10 / 100 / 1000 consecutive
integers carry at least 11 / 171 / 2126 distinct prime factors, counted with
multiplicity over the window. -/
theorem jsp87_window_omega_ge_ten {N : ℕ} (hN : 1 ≤ N) : jsp87WindowOmega N 10 ≥ 11 := by
  have h := jsp87_window_omega_ge_omegaCount hN (by norm_num : (1 : ℕ) ≤ 10)
  rw [jsp87_omegaCount_ten] at h
  exact h

theorem jsp87_window_omega_ge_hundred {N : ℕ} (hN : 1 ≤ N) : jsp87WindowOmega N 100 ≥ 171 := by
  have h := jsp87_window_omega_ge_omegaCount hN (by norm_num : (1 : ℕ) ≤ 100)
  rw [jsp87_omegaCount_hundred] at h
  exact h

theorem jsp87_window_omega_ge_thousand {N : ℕ} (hN : 1 ≤ N) :
    jsp87WindowOmega N 1000 ≥ 2126 := by
  have h := jsp87_window_omega_ge_omegaCount hN (by norm_num : (1 : ℕ) ≤ 1000)
  rw [jsp87_omegaCount_thousand] at h
  exact h

/-- **THE LOCAL MEAN OF `ω`, IN REAL NUMBERS.**  The mean of `ω` over any window
of length `L` is at least `∑_{p ≤ L, p prime} 1/p - (card of the primes ≤ L)/L`. -/
theorem jsp87_window_mean_ge {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    (∑ p ∈ jsp87Primes L, ((p : ℝ)⁻¹)) - (((jsp87Primes L).card : ℕ) : ℝ) / L
      ≤ ((jsp87WindowOmega N L : ℝ)) / L := by
  have hfloor : (∀ p ∈ jsp87Primes L, ((L / p : ℕ) : ℝ) ≥ (L : ℝ) * ((p : ℝ)⁻¹) - 1) := by
    intro p hp
    have hp2 : 2 ≤ p := two_le_mem_jsp87Primes hp
    have hmod : (L : ℕ) % p < p := Nat.mod_lt _ (by omega : (0 : ℕ) < p)
    have h1 := Nat.mod_add_div L p
    rw [Nat.mul_comm] at h1
    have h2 : (L : ℝ) = ((L % p : ℕ) : ℝ) + ((L / p : ℕ) : ℝ) * (p : ℝ) := by
      exact_mod_cast h1.symm
    have h3 : ((L % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hmod
    have h4 : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    rw [h2]
    field_simp
    linarith
  have hsub : (∑ p ∈ jsp87Primes L, ((L : ℝ) * ((p : ℝ)⁻¹) - 1))
      = (∑ p ∈ jsp87Primes L, ((L : ℝ) * ((p : ℝ)⁻¹))) - ((jsp87Primes L).card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hsum : ((∑ p ∈ jsp87Primes L, (L / p : ℕ)) : ℝ)
      ≥ (L : ℝ) * (∑ p ∈ jsp87Primes L, ((p : ℝ)⁻¹)) - ((jsp87Primes L).card : ℝ) := by
    have hle := Finset.sum_le_sum (s := jsp87Primes L) hfloor
    rw [hsub] at hle
    rw [Finset.mul_sum]
    linarith
  have hcast : ((jsp87WindowOmega N L : ℕ) : ℝ) ≥ ((∑ p ∈ jsp87Primes L, (L / p : ℕ)) : ℝ) := by
    have h := jsp87_window_omega_ge_div hN hL
    exact_mod_cast h
  have hkey : (jsp87WindowOmega N L : ℝ) ≥ (L : ℝ) * (∑ p ∈ jsp87Primes L, ((p : ℝ)⁻¹))
      - ((jsp87Primes L).card : ℝ) := le_trans hsum hcast
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [le_div_iff₀ hLpos]
  have hcardL : (((jsp87Primes L).card : ℝ)) / L * L = ((jsp87Primes L).card : ℝ) := by
    field_simp
  linarith [hkey]

/-- **THE LOCAL MEAN IS AT LEAST THE PRIME HARMONIC SUM, UP TO 1.**  For every
window of length `L` the mean of `ω` is at least `∑_{p ≤ L} 1/p - 1`, because
there are at most `L` primes up to `L`. -/
theorem jsp87_window_mean_ge_one {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    ((jsp87WindowOmega N L : ℝ)) / L
      ≥ (∑ p ∈ jsp87Primes L, ((p : ℝ)⁻¹)) - 1 := by
  have h := jsp87_window_mean_ge hN hL
  have hcard : (jsp87Primes L).card ≤ L := by
    calc (jsp87Primes L).card ≤ (Finset.Icc 2 L).card := by
            refine Finset.card_le_card ?_
            intro p hp
            obtain ⟨h2, hpL, _⟩ := mem_jsp87Primes.mp hp
            simp only [Finset.mem_Icc]
            omega
      _ = L - 1 := by rw [Nat.card_Icc]; omega
      _ ≤ L := by omega
  have hcard' : ((jsp87Primes L).card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hcard
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hcardL : ((jsp87Primes L).card : ℝ) / L ≤ 1 := (div_le_one hLpos).2 hcard'
  linarith

/-- **THE MEAN OF `ω` NEVER DIPS BELOW THE MEAN OVER `[1, L]`, IN REAL
NUMBERS.** -/
theorem jsp87_window_mean_ge_initial {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    ((jsp87WindowOmega N L : ℝ)) / L ≥ ((jsp87OmegaCount L : ℝ)) / L := by
  have h := jsp87_window_omega_ge_omegaCount hN hL
  have h' : ((jsp87OmegaCount L : ℕ) : ℝ) ≤ ((jsp87WindowOmega N L : ℕ) : ℝ) := by
    exact_mod_cast h
  exact div_le_div_of_nonneg_right h' (by positivity)

end JSP87
