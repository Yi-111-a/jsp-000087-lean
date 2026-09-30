/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.PowerPair

/-!
# `JSP-000087` (round 69) — carry runs: the window in which the digit string reads `ω`

`ω n` is the number of distinct prime factors of `n`, the digit-source of the Erdős
series `S = ∑' n, ω n · 2 ^ -(n+1)`; `θ N = 2^N · ∑' k, ω (N+k) · 2 ^ -(N+k+1)` is
the *carry* at the cut point `N` and `c N = ⌊θ N⌋` the *carry excess* (round 41).

Rounds 37–68 built the whole scaffold of Erdős' method on the series, and round 67
finally produced **witnesses** for the two-point aperiodicity of `ω`: on a geometric
ray `q^k` (`k ≥ K`) one has `ω (q^k) = 1 < ω (q^k + t)`.  The recorded blocker
(round 67) is precisely that these witnesses do **not** transfer to the binary digit
string, because

`d N = ω N + c (N+1) − 2 c N` (`jsp87_digit_bookkeeping`).

This round identifies the *windows in which the cancellation cannot happen*.

**The carry run.**  Say that the carry is `u`-constant on `[N, N+L]` when
`c N = c (N+1) = ⋯ = c (N+L) = u`.  Then the bookkeeping identity collapses:

* `jsp87_carryRun_iff` (**the normal form**) — the carry is `u`-constant on
  `[N, N+L]` **iff** `ω (N+j) = d (N+j) + u` for every `j < L`.  In other words:
  **inside a carry run the digit string literally reads `ω` minus a constant.**
* `jsp87_carryRun_omega_mem` — consequently `ω (N+j) ∈ {u, u+1}` there.
* `jsp87_carryRun_pow` (**the flagship**) — a carry run that meets a prime power
  `q^k` has `u = 1` *exactly* (unconditionally: `c N ≥ 1` for `N ≥ 2`, round 44, and
  `ω (q^k) = 1` forces `u ≤ 1`), and the digit at `q^k` is `0`.
* `jsp87_carryRun_pow_digit` — at distance `t` from such a prime power the digit is
  `1`, so the digit string **changes** across the prime power.

Since a rational value of `S` has an eventually periodic digit string
(round 41), and `ω (q^k + t) ≥ 2` on the round-67 rays, this closes the last
gap in the Erdős–Pratt mechanism:

* `jsp87_digitPeriod_excludes_pow` — rationality forbids a prime power in the core
  of a carry run longer than the period;
* `jsp87Series_irrational_of_powCarryRun` — the conditional theorem: **carrying
  runs through prime powers of unbounded length make the series irrational.**

**Why this does not close the gate.**  The hypothesis
`jsp87PowCarryRun t M` — for every `t` and every `M` a carry run of length `> t`
whose core contains a prime power — is a *prime-`k`-tuples type* statement about
patterns of `ω` on consecutive integers (exactly the hypothesis of Pratt,
arXiv:2409.15185, and the same nature as round 53's `constRun`), and it is not
known.  What is new and proved here is the **mechanism**: the normal form of a carry
run, the fact that such a run is pinned to value `1` and forces the digit pattern
`0 … 1` across a prime power, and the exact arithmetic obstruction that a rational
value of `S` imposes on carry runs.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The exact integer carry recurrence -/

/-- **THE CARRY RECURRENCE, IN THE `ℤ`-ARITHMETIC OF THE CARRY EXCESS.**
For `1 ≤ N`,

`c (N+1) = 2 c N + d N − ω N`

with `c N = ⌊θ N⌋` the carry excess, `d N` the `N`-th binary digit of `S` and `ω N`
the `ω`-digit.  This is round 41's `jsp87_digit_bookkeeping` read backwards: the
carry excess is a *transducer state*, driven by the pair `(ω N, d N)`. -/
theorem jsp87_carryExcess_succ {N : ℕ} (hN : 1 ≤ N) :
    jsp87CarryExcess (N + 1) = 2 * jsp87CarryExcess N + jsp87Digit N - (omega N : ℤ) := by
  have h := jsp87_digit_bookkeeping hN
  omega

/-! ## 2. Carry runs -/

/-- **A CARRY RUN.**  `jsp87CarryRun N L u` says that the carry excess takes the
*constant* value `u` at every cut point from `N` to `N + L`:

`c N = c (N+1) = ⋯ = c (N+L) = u`. -/
def jsp87CarryRun (N L u : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ L → jsp87CarryExcess (N + j) = (u : ℤ)

/-- **A `ω`-DIGIT WINDOW.**  `jsp87OmegaDigitWindow N L u` says that on `[N, N+L)`
the `ω`-value is the binary digit plus the constant `u`:

`ω (N+j) = d (N+j) + u` for every `j < L`. -/
def jsp87OmegaDigitWindow (N L u : ℕ) : Prop :=
  ∀ j : ℕ, j < L → (omega (N + j) : ℤ) = jsp87Digit (N + j) + (u : ℤ)

/-- **THE NORMAL FORM OF A CARRY RUN.**  For `1 ≤ N`:

`jsp87CarryRun N L u ↔ c N = u ∧ jsp87OmegaDigitWindow N L u`.

*Proof.*  Induction on `L`, using `jsp87_carryExcess_succ`: if `c (N+j) = u` and
`c (N+j+1) = u` then `2u + d (N+j) − ω (N+j) = u`, i.e.
`ω (N+j) = d (N+j) + u`; conversely that relation propagates the constancy. -/
theorem jsp87_carryRun_iff {N L u : ℕ} (hN : 1 ≤ N) :
    jsp87CarryRun N L u ↔ jsp87CarryExcess N = (u : ℤ) ∧ jsp87OmegaDigitWindow N L u := by
  induction L with
  | zero =>
    constructor
    · intro h
      refine ⟨h 0 (by omega), ?_⟩
      simp [jsp87OmegaDigitWindow]
    · rintro ⟨h0, -⟩
      exact fun j hj => by
        have hj0 : j = 0 := by omega
        rw [hj0, Nat.add_zero]
        exact h0
  | succ L ih =>
    constructor
    · intro hrun
      have hhead : jsp87CarryExcess N = (u : ℤ) := by
        have h := hrun 0 (by omega)
        simpa [Nat.add_zero] using h
      have hrunL : jsp87CarryRun N L u := fun j hj => hrun j (by omega)
      obtain ⟨hN0, hW⟩ := ih.mp hrunL
      have hlast : jsp87CarryExcess (N + L) = (u : ℤ) := by
        have h := hrun L (by omega)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      refine ⟨hN0, ?_⟩
      intro j hj
      by_cases hje : j = L
      · rw [hje]
        have hrec := jsp87_carryExcess_succ (N := N + L) (by omega)
        have hlast' : jsp87CarryExcess (N + L + 1) = (u : ℤ) := hrun (L + 1) (by omega)
        rw [hlast', hlast] at hrec
        omega
      · have hjL : j < L := by omega
        exact hW j hjL
    · rintro ⟨hN0, hW⟩
      have hrunL : jsp87CarryRun N L u := ih.mpr
        ⟨hN0, fun i hi => hW i (by omega)⟩
      intro j hj
      rcases Nat.eq_zero_or_pos j with hz | hz
      · simpa [hz] using hN0
      · have hci : jsp87CarryExcess (N + (j - 1)) = (u : ℤ) := hrunL (j - 1) (by omega)
        have hrec := jsp87_carryExcess_succ (N := N + (j - 1)) (by omega)
        rw [show N + (j - 1) + 1 = N + j by omega, hci] at hrec
        have hd := hW (j - 1) (by omega)
        omega

/-- **EVERY TAIL OF A CARRY RUN IS A CARRY RUN.**  If the carry is `u`-constant on
`[N, N+L]` with `L ≥ 1`, it is `u`-constant on `[N+1, N+L]`, i.e. it is a run of
length `L-1` based at `N+1`.  (The left endpoint is the only delicate one, so runs
are closed under truncation *on the right*.) -/
theorem jsp87_carryRun_succ {N L u : ℕ} (hL : 1 ≤ L) (hrun : jsp87CarryRun N L u) :
    jsp87CarryRun (N + 1) (L - 1) u := by
  intro j hj
  have h' := hrun (j + 1) (by omega)
  have hidx : N + (j + 1) = N + 1 + j := by omega
  rw [hidx] at h'
  exact h'

/-- **A CARRY RUN HAS A UNIQUE VALUE.**  Two runs of the same length based at the
same place cannot have different values. -/
theorem jsp87_carryRun_unique {N L u v : ℕ} (hrun : jsp87CarryRun N L u)
    (hrun' : jsp87CarryRun N L v) : u = v := by
  have h := hrun 0 (by omega)
  have h' := hrun' 0 (by omega)
  simp only [Nat.add_zero] at h h'
  omega

/-! ## 3. What a carry run says about `ω` and about the digits -/

/-- **INSIDE A CARRY RUN, `ω` TAKES ONLY THE TWO VALUES `u` AND `u+1`.**  This is
the first content of the normal form: a carry run is a window on which `ω` is
almost constant. -/
theorem jsp87_carryRun_omega_mem {N L u : ℕ} (hN : 1 ≤ N) (hrun : jsp87CarryRun N L u) :
    ∀ j, j < L → omega (N + j) = u ∨ omega (N + j) = u + 1 := by
  intro j hj
  obtain ⟨-, hW⟩ := (jsp87_carryRun_iff hN).mp hrun
  have hd := hW j hj
  have hmem := jsp87Digit_mem (N + j)
  rcases hmem with h0 | h1
  · left
    have hz : (omega (N + j) : ℤ) = (u : ℤ) := by
      rw [hd, h0]; ring
    exact_mod_cast hz
  · right
    have hz : (omega (N + j) : ℤ) = (u + 1 : ℤ) := by
      rw [hd, h1]; ring
    exact_mod_cast hz

/-- **The `ω`-window of a carry run is bounded.**  Every member of the window has at
most `u+1` distinct prime factors. -/
theorem jsp87_carryRun_omega_le {N L u : ℕ} (hN : 1 ≤ N) (hrun : jsp87CarryRun N L u)
    {j : ℕ} (hj : j < L) : omega (N + j) ≤ u + 1 := by
  rcases jsp87_carryRun_omega_mem hN hrun j hj with h | h <;> omega

/-- **INSIDE A CARRY RUN THE DIGIT STRING READS `ω` MINUS THE RUN VALUE.**  For
`1 ≤ N`, `j < L`, `ω (N+j) = u`: the digit is `0`; and if `ω (N+j) = u + 1` the
digit is `1`. -/
theorem jsp87_carryRun_digit {N L u : ℕ} (hN : 1 ≤ N) (hrun : jsp87CarryRun N L u)
    {j : ℕ} (hj : j < L) :
    (omega (N + j) = u ∧ jsp87Digit (N + j) = 0) ∨ (omega (N + j) = u + 1 ∧ jsp87Digit (N + j) = 1) := by
  obtain ⟨-, hW⟩ := (jsp87_carryRun_iff hN).mp hrun
  have hd := hW j hj
  have hmem := jsp87Digit_mem (N + j)
  rcases jsp87_carryRun_omega_mem hN hrun j hj with h | h
  · left
    refine ⟨h, ?_⟩
    have hz : (jsp87Digit (N + j) : ℤ) = 0 := by omega
    exact_mod_cast hz
  · right
    refine ⟨h, ?_⟩
    have hz : (jsp87Digit (N + j) : ℤ) = 1 := by omega
    exact_mod_cast hz

/-- **A run value `u = 0` is a *low* carry run:** the window then lives where the
carry excess has not yet started. -/
theorem jsp87_carryRun_zero_iff {N L : ℕ} (hN : 1 ≤ N) (hrun : jsp87CarryRun N L 0)
    {j : ℕ} (hj : j < L) : jsp87Digit (N + j) = omega (N + j) := by
  rcases jsp87_carryRun_digit hN hrun hj with h | h
  · omega
  · omega

/-! ## 4. Prime powers inside a carry run -/

/-- **A CARRY RUN OF POSITIVE VALUE THROUGH A PRIME POWER HAS VALUE EXACTLY `1`,
AND THE DIGIT AT THE PRIME POWER IS `0`.**  Let `1 ≤ N ≤ q^k < N+L`, `q` prime,
`k ≥ 1`, let the carry be `u`-constant on `[N, N+L]`, and assume `1 ≤ u`.  Then
`u = 1` and `jsp87Digit (q^k) = 0`.

*Proof.*  By the normal form, `ω (q^k) = d (q^k) + u` with `d ≥ 0`, and
`ω (q^k) = 1` because a prime power has one distinct prime factor; hence `u ≤ 1`.
With `u ≥ 1` this gives `u = 1` and `d (q^k) = 0`. -/
theorem jsp87_carryRun_pow {N L u q k : ℕ} (hN : 1 ≤ N) (hu : 1 ≤ u) (hq : q.Prime)
    (hk : 1 ≤ k) (hrun : jsp87CarryRun N L u) (hqw : N ≤ q ^ k) (hqwL : q ^ k < N + L) :
    u = 1 ∧ jsp87Digit (q ^ k) = 0 := by
  obtain ⟨-, hW⟩ := (jsp87_carryRun_iff hN).mp hrun
  have hjq : q ^ k - N < L := by omega
  have hidx : N + (q ^ k - N) = q ^ k := by omega
  have hw := hW (q ^ k - N) hjq
  rw [hidx] at hw
  have hω : omega (q ^ k) = 1 := omega_prime_pow hq hk
  rw [hω] at hw
  have hmem := jsp87Digit_mem (q ^ k)
  have hd0 : (0 : ℤ) ≤ jsp87Digit (q ^ k) := by
    rcases hmem with h0 | h1
    · simp [h0]
    · simp [h1]
  refine ⟨by omega, by omega⟩

/-- **A ZERO-VALUED CARRY RUN HAS NO `ω`-VALUE ABOVE `1`.**  A run of value `u = 0`
is a place where `ω` is *exactly* the digit string.  In particular it can never
contain a point of `ω`-value `2`, so such runs are irrelevant to the mechanism
below (this is why the hypothesis `1 ≤ u` of `jsp87_carryRun_pow` costs nothing). -/
theorem jsp87_carryRun_zero_small {N L : ℕ} (hN : 1 ≤ N) (hrun : jsp87CarryRun N L 0)
    {j : ℕ} (hj : j < L) : omega (N + j) ≤ 1 := by
  rcases jsp87_carryRun_omega_mem hN hrun j hj with h | h <;> omega

/-- **THE DIGIT PATTERN FORCED BY A CARRY RUN ACROSS A PRIME POWER.**  If the carry
is `u`-constant on `[N, N+L]` with `1 ≤ N`, `1 ≤ u`, `N ≤ q^k` and `q^k + t < N+L`
(`t ≥ 1`, `q` prime, `k ≥ 1`), and if `ω (q^k + t) ≥ 2`, then

`u = 1`, `d (q^k) = 0` and `d (q^k + t) = 1`:

**the binary digit string changes across the prime power, and the run value is
exactly `1`.**  This is unconditional — no period hypothesis is used: round 67
supplies `ω (q^k + t) ≥ 2` on a ray.  A `t`-periodic digit string is therefore
impossible, which is `jsp87_digitPeriod_excludes_pow` below. -/
theorem jsp87_carryRun_pow_digit {N L u q k t : ℕ} (hN : 1 ≤ N) (hu : 1 ≤ u)
    (hq : q.Prime) (hk : 1 ≤ k) (ht : 0 < t) (htw : 2 ≤ omega (q ^ k + t))
    (hrun : jsp87CarryRun N L u) (hqw : N ≤ q ^ k) (hLt : q ^ k + t < N + L) :
    u = 1 ∧ jsp87Digit (q ^ k) = 0 ∧ jsp87Digit (q ^ k + t) = 1 := by
  obtain ⟨hu1, hd0⟩ := jsp87_carryRun_pow hN hu hq hk hrun hqw (by omega)
  obtain ⟨-, hW⟩ := (jsp87_carryRun_iff hN).mp hrun
  have hjw : q ^ k + t - N < L := by omega
  have hidx : N + (q ^ k + t - N) = q ^ k + t := by omega
  have hw := hW (q ^ k + t - N) hjw
  rw [hidx] at hw
  have hmem := jsp87Digit_mem (q ^ k + t)
  have hdle : jsp87Digit (q ^ k + t) ≤ 1 := by
    rcases hmem with h0 | h1
    · simp [h0]
    · simp [h1]
  exact ⟨hu1, hd0, by omega⟩

/-- **A CARRY RUN THROUGH A PRIME POWER FORCES THE TWO VALUES OF `ω`.**  In the
situation of `jsp87_carryRun_pow_digit`, `ω (q^k) = 1` and `ω (q^k + t) = 2`: the
run forces the *exact* pair of `ω`-values, one apart. -/
theorem jsp87_carryRun_pow_pair {N L u q k t : ℕ} (hN : 1 ≤ N) (hu : 1 ≤ u)
    (hq : q.Prime) (hk : 1 ≤ k) (ht : 0 < t) (htw : 2 ≤ omega (q ^ k + t))
    (hrun : jsp87CarryRun N L u) (hqw : N ≤ q ^ k) (hLt : q ^ k + t < N + L) :
    omega (q ^ k) = 1 ∧ omega (q ^ k + t) = 2 := by
  obtain ⟨hu1, hd0, hd1⟩ := jsp87_carryRun_pow_digit hN hu hq hk ht htw hrun hqw hLt
  obtain ⟨-, hW⟩ := (jsp87_carryRun_iff hN).mp hrun
  have hjw : q ^ k + t - N < L := by omega
  have hidx : N + (q ^ k + t - N) = q ^ k + t := by omega
  have hw := hW (q ^ k + t - N) hjw
  rw [hidx] at hw
  refine ⟨omega_prime_pow hq hk, ?_⟩
  exact_mod_cast (show (omega (q ^ k + t) : ℤ) = 2 by omega)

private theorem pow_lt_pow_one_gt {q t k : ℕ} (ht : 0 < t) (_hq : 2 ≤ q)
    (hk : 2 * t < q ^ k) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with hz | hz
  · rw [hz, pow_zero] at hk
    omega
  · omega

/-- **THE `2`-RAY FORM OF THE FLAGSHIP, FROM ROUND 67'S EXPLICIT WITNESSES.**  If
`t` is a positive *even* number, `2 t < 2^k`, and the carry is `u`-constant on a
window `[2^k, 2^k + L]` of positive value which still contains `2^k + t`, then the
digit string of `S` reads `0` at `2^k` and `1` at `2^k + t`.  The witness
`ω (2^k) = 1 < ω (2^k + t)` is round 67's `jsp87_powPair_min_two`. -/
theorem jsp87_carryRun_pow_ray_even {t k L u : ℕ} (ht : 0 < t) (h2 : 2 ∣ t)
    (hk : 2 * t < 2 ^ k) (hu : 1 ≤ u) (hrun : jsp87CarryRun (2 ^ k) L u)
    (hLt : 2 ^ k + t < 2 ^ k + L) :
    jsp87Digit (2 ^ k) = 0 ∧ jsp87Digit (2 ^ k + t) = 1 := by
  obtain ⟨hw, hω⟩ := jsp87_powPair_min_two ht h2 hk
  obtain ⟨-, hd0, hd1⟩ :=
    jsp87_carryRun_pow_digit (N := 2 ^ k) (L := L) (u := u) (q := 2) (k := k) (t := t)
      (by omega) hu (by norm_num) (pow_lt_pow_one_gt ht (by norm_num) hk) ht hω hrun (by omega) hLt
  exact ⟨hd0, hd1⟩

/-- **THE PRIME-RAY FORM OF THE FLAGSHIP.**  If `q` is a prime divisor of `t`,
`2 t < q^k`, and the carry is `u`-constant on a positive-valued window containing
both `q^k` and `q^k + t`, then the digits read `0` and `1` there (round 67's
`jsp87_powPair_min_prime`). -/
theorem jsp87_carryRun_pow_ray_prime {t q k L u : ℕ} (ht : 0 < t) (hq : q.Prime)
    (hqd : q ∣ t) (hk : 2 * t < q ^ k) (hu : 1 ≤ u) (hrun : jsp87CarryRun (q ^ k) L u)
    (hLt : q ^ k + t < q ^ k + L) :
    jsp87Digit (q ^ k) = 0 ∧ jsp87Digit (q ^ k + t) = 1 := by
  obtain ⟨hw, hω⟩ := jsp87_powPair_min_prime ht hq hqd hk
  obtain ⟨-, hd0, hd1⟩ :=
    jsp87_carryRun_pow_digit (N := q ^ k) (L := L) (u := u) (q := q) (k := k) (t := t)
      (by omega) hu hq (pow_lt_pow_one_gt ht hq.two_le hk) ht hω hrun (by omega) hLt
  exact ⟨hd0, hd1⟩

/-! ## 5. A rational value of `S` freezes the carry runs -/

/-- **A PERIODIC DIGIT STRING FORBIDS A PRIME POWER IN THE CORE OF A CARRY RUN.**
Let the binary digits of `S` satisfy `d (n+t) = d n` for all `n ≥ M`, with `t ≥ 1`,
`1 ≤ M ≤ N`, and let the carry be `u`-constant on `[N, N+L]` with `N ≤ q^k` and
`q^k + t < N+L` (`q` prime, `k ≥ 1`, `ω (q^k + t) ≥ 2`).  This is impossible.

Indeed, if `u ≥ 1` the run forces `d (q^k) = 0` and `d (q^k + t) = 1`, while the
period forces them equal; if `u = 0` the run forces `ω (q^k + t) ≤ 1`, contradicting
the hypothesis.

This is the **exact arithmetic obstruction** that a rational value of the Erdős
series imposes on its own carry runs. -/
theorem jsp87_digitPeriod_excludes_pow {t M N L u q k : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hMN : M ≤ N) (hq : q.Prime) (hk : 1 ≤ k) (htw : 2 ≤ omega (q ^ k + t))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hrun : jsp87CarryRun N L u) (hqw : N ≤ q ^ k) (hLt : q ^ k + t < N + L) : False := by
  rcases Nat.lt_or_ge u 1 with hu | hu
  · -- a run of value `0` cannot contain a point of `ω`-value `≥ 2`
    obtain ⟨-, hW⟩ := (jsp87_carryRun_iff (by omega)).mp hrun
    have hjw : q ^ k + t - N < L := by omega
    have hidx : N + (q ^ k + t - N) = q ^ k + t := by omega
    have hw := hW (q ^ k + t - N) hjw
    rw [hidx] at hw
    have hmem := jsp87Digit_mem (q ^ k + t)
    rcases hmem with h0 | h1 <;> omega
  · obtain ⟨-, hd0, hd1⟩ := jsp87_carryRun_pow_digit (N := N) (L := L) (u := u) (q := q)
      (k := k) (t := t) (by omega) hu hq hk ht htw hrun hqw hLt
    have hper' : jsp87Digit (q ^ k + t) = jsp87Digit (q ^ k) := hper (q ^ k) (by omega)
    omega

/-- **A CARRY RUN WITH A PRIME-POWER WITNESS AT DISTANCE `t`.**  `jsp87PowCarryRun t M`
says: past every place `M`, there is a window on which the carry excess of `S` is
*constant* and long enough to contain, at distance `t`, a prime power `q^k` whose
translate by `t` has two distinct prime factors.  A `t`-periodic digit string cannot
coexist with such a window (`jsp87_digitPeriod_excludes_pow`). -/
def jsp87PowCarryRun (t M : ℕ) : Prop :=
  ∃ N L u q k : ℕ, M ≤ N ∧ q.Prime ∧ 1 ≤ k ∧ N ≤ q ^ k ∧ q ^ k + t < N + L
    ∧ 2 ≤ omega (q ^ k + t) ∧ jsp87CarryRun N L u

/-- **THE CARRY-RUN CRITERION FOR IRRATIONALITY.**  Suppose that for every shift
`t ≥ 1` and every place `M ≥ 1` there is a constant-carry window past `M` whose
core contains a prime power `q^k` with `q^k + t` still inside the window and
`ω (q^k + t) ≥ 2`.  Then `jsp87Series` is **irrational**.

*Proof.*  A rational value `a/b` makes the digit string eventually periodic with
some period `t` from some `M` (round 41), and the hypothesis at `(t, M)` is
contradicted by `jsp87_digitPeriod_excludes_pow`. -/
theorem jsp87Series_irrational_of_powCarryRun
    (H : ∀ t : ℕ, 1 ≤ t → ∀ M : ℕ, 1 ≤ M → jsp87PowCarryRun t M) : Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hb : 0 < q.den := Rat.den_pos q
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb (by rw [← hq, Rat.cast_def])
  obtain ⟨N, L, u, qq, k, hMN, hqq, hk, hqw, hLt, htw, hrun⟩ := H t ht M hM
  exact jsp87_digitPeriod_excludes_pow ht hM hMN hqq hk htw hper hrun hqw hLt

/-- **THE CONTRAPOSITIVE, WITH AN EXPLICIT PERIOD AND STARTING POINT.**  If
`S = a / b` with `b > 0` and `t ≥ 1`, then there is a place `M` past which **no**
carry run has a prime-power witness at distance `t`.  In particular: for the actual
digit period `t` of a hypothetical rational value, the carry runs are *shorter than
the distance to the next prime power*. -/
theorem jsp87_rational_imp_powCarryRun_absent {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M ∧ ¬ jsp87PowCarryRun t M := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  refine ⟨t, M, ht, hM, fun hcontra => ?_⟩
  obtain ⟨N, L, u, q, k, hMN, hq, hk, hqw, hLt, htw, hrun⟩ := hcontra
  exact jsp87_digitPeriod_excludes_pow ht hM hMN hq hk htw hper hrun hqw hLt

/-- **THE LENGTH OF A CARRY RUN IS BOUNDED BY THE NEXT PRIME-POWER WITNESS.**  Under
a digit period `t` from `M`, if the carry is `u`-constant on `[N, N+L]` with
`M ≤ N < q^k` (so that `q^k` lies beyond the start of the run), then the run must
stop before `q^k + t`: `N + L ≤ q^k + t`.  Here `ω (q^k + t) ≥ 2` is the round-67
ray hypothesis. -/
theorem jsp87_carryRun_le_pow {t M N L u q k : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hMN : M ≤ N) (hq : q.Prime) (hk : 1 ≤ k) (htw : 2 ≤ omega (q ^ k + t))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hrun : jsp87CarryRun N L u) (hNq : N < q ^ k) : N + L ≤ q ^ k + t := by
  by_contra hcon
  exact jsp87_digitPeriod_excludes_pow ht hM hMN hq hk htw hper hrun (by omega) (by omega)

/-- **CARRY RUNS ARE SHORTER THAN THE NEXT WITNESS OF ANY RAY.**  Let the digits be
periodic with period `t` from `M`, let `ω (q^j) = 1 < ω (q^j + t)` for every
`j ≥ k` (`q` prime), and let the carry be `u`-constant on `[N, N+L]` with `M ≤ N`.
Then `N + L ≤ q^j + t` for every `j ≥ k` with `N < q^j`: the run is shorter than the
least prime power above `N` on the ray, plus the period. -/
theorem jsp87_carryRun_le_ray {t M N L u q k : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hMN : M ≤ N) (hq : q.Prime) (hk : 1 ≤ k)
    (hray : ∀ j, k ≤ j → omega (q ^ j) = 1 ∧ 2 ≤ omega (q ^ j + t))
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n)
    (hrun : jsp87CarryRun N L u) {j : ℕ} (hjk : k ≤ j) (hNq : N < q ^ j) :
    N + L ≤ q ^ j + t :=
  jsp87_carryRun_le_pow (k := j) ht hM hMN hq (by omega) (hray j hjk).2 hper hrun hNq

/-- **THE `ω`-MASS OF A CARRY RUN IS AT MOST `L·(u+1)`.**  Every member of a
constant-carry window has at most `u+1` distinct prime factors, so the total `ω`-mass
of the window is at most `L·(u+1)`.

*Negative companion of round 56.*  Round 56 prices a **constant-`ω`** window,
`L^(u − π(L−1)) ≤ N+L−1`, by rewriting the mass as the *equality* `Σ ω = u·L`.  For
a carry run the mass is only bounded **above** by `L·(u+1)`, and combining two upper
bounds (`jsp87_window_omega_le` and the one above) yields nothing: the price route
of round 56 therefore does **not** transfer to carry runs.  Recorded so that later
rounds do not retry it. -/
theorem jsp87_carryRun_omega_sum_le {N L u : ℕ} (hN : 1 ≤ N)
    (hrun : jsp87CarryRun N L u) :
    (∑ j ∈ Finset.range L, omega (N + j)) ≤ L * (u + 1) := by
  have hstep : ∀ j ∈ Finset.range L, omega (N + j) ≤ u + 1 :=
    fun j hj => jsp87_carryRun_omega_le hN hrun (Finset.mem_range.mp hj)
  have h := Finset.sum_le_sum (s := Finset.range L) (fun j _ => hstep j (by omega))
  simpa [Finset.sum_const, Finset.card_range, Nat.mul_comm] using h

/-! ## 6. A machine-checked carry run in the actual series -/

/-- **`ω` on `[4, 16)`. -/
theorem omega_window_4_16 :
    omega 4 = 1 ∧ omega 5 = 1 ∧ omega 6 = 2 ∧ omega 7 = 1 ∧ omega 8 = 1 ∧ omega 9 = 1
      ∧ omega 10 = 2 ∧ omega 11 = 1 ∧ omega 12 = 2 ∧ omega 13 = 1 ∧ omega 14 = 2
      ∧ omega 15 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **THE CARRY AT `4 + n` LIES IN `[1, 2)` FOR `0 ≤ n ≤ 3`.**  The lower bound is
round 44's uniform `θ N ≥ 1 + 1/128` for `N ≥ 2`; the upper bound is
`jsp87Carry_le_window` with a window of length `8`, so the remaining sum is a
rational number that `norm_num` evaluates. -/
theorem jsp87Carry_window_4 : ∀ n : ℕ, n ≤ 3 → 1 ≤ jsp87Carry (4 + n)
    ∧ jsp87Carry (4 + n) < 2 := by
  intro n hn
  have hle : jsp87Carry (4 + n)
      ≤ (∑ k ∈ Finset.range 8, ((omega (4 + n + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((2 : ℝ) ^ 8)⁻¹ * ((4 + n + 8 + 1 : ℕ) : ℝ) := by
    exact jsp87Carry_le_window (N := 4 + n) (L := 8) (by omega)
  have hupp : jsp87Carry (4 + n) < 2 := by
    obtain ⟨h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩ := omega_window_4_16
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at hle <;>
      linarith
  refine ⟨by linarith [jsp87Carry_ge_one_plus_seven (N := 4 + n) (by omega)], hupp⟩

/-- **The carry excess is `1` at each of the cut points `4, 5, 6, 7`. -/
theorem jsp87CarryExcess_4_7 : ∀ n : ℕ, n ≤ 3 → jsp87CarryExcess (4 + n) = 1 := by
  intro n hn
  have h := jsp87Carry_window_4 n hn
  show (⌊jsp87Carry (4 + n)⌋ : ℤ) = 1
  rw [Int.floor_eq_iff]
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- **A CONSTANT-CARRY RUN IN THE ACTUAL SERIES: `c 4 = c 5 = c 6 = c 7 = 1`.**
The carry excess of the Erdős series is *constant* on the four consecutive cut
points `4, 5, 6, 7`.  By the normal form this is a place where the digit string
reads `ω` verbatim minus `1`. -/
theorem jsp87_carryRun_4 : jsp87CarryRun 4 3 1 := by
  intro j hj
  induction j with
  | zero => exact jsp87CarryExcess_4_7 0 (by omega)
  | succ j ih =>
    induction j with
    | zero => exact jsp87CarryExcess_4_7 1 (by omega)
    | succ j ih =>
      induction j with
      | zero => exact jsp87CarryExcess_4_7 2 (by omega)
      | succ j ih =>
        induction j with
        | zero => exact jsp87CarryExcess_4_7 3 (by omega)
        | succ j ih => omega

/-- **THE HEADLINE INSTANCE OF THIS ROUND: THREE PROVED CONSECUTIVE DIGITS OF THE
ERDŐS SERIES, `d 4 = 0`, `d 5 = 0`, `d 6 = 1`.**

They follow from the verified carry run `c 4 = c 5 = c 6 = c 7 = 1` and the values
`ω 4 = ω 5 = 1`, `ω 6 = 2`: inside a carry run of value `1` the digit is `ω − 1`.
So the binary expansion of `∑' n, ω n 2^-(n+1)` reads

`… 0 0 1 …` at positions `4, 5, 6`

— the first place in the development where digits are read off a *carry run* of
the actual series. -/
theorem jsp87_digit_window_4 :
    jsp87Digit 4 = 0 ∧ jsp87Digit 5 = 0 ∧ jsp87Digit 6 = 1 := by
  obtain ⟨-, hW⟩ := (jsp87_carryRun_iff (by omega)).mp jsp87_carryRun_4
  obtain ⟨h4', h5', h6', -, -, -, -, -, -, -, -, -⟩ := omega_window_4_16
  have d0 : jsp87Digit 4 = 0 := by
    have h := hW 0 (by omega)
    rw [show (4 + 0 : ℕ) = 4 from by omega] at h
    omega
  have d1 : jsp87Digit 5 = 0 := by
    have h := hW 1 (by omega)
    rw [show (4 + 1 : ℕ) = 5 from by omega] at h
    omega
  have d2 : jsp87Digit 6 = 1 := by
    have h := hW 2 (by omega)
    rw [show (4 + 2 : ℕ) = 6 from by omega] at h
    omega
  exact ⟨d0, d1, d2⟩

end JSP87
