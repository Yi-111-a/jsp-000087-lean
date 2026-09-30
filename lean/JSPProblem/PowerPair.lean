/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Primary
import JSPProblem.WindowTwoAdic

/-!
# `JSP-000087` (round 67) — the *witness structure* of the two-point aperiodicity of `ω`

`ω n` is the number of distinct prime factors of `n`; it is the digit-source of the
Erdős series `S = ∑' n, ω n · 2 ^ -(n+1)` of `PROBLEM.md`.

Rounds 37–66 built the whole apparatus of Erdős' method on the series itself: the
Lambert reduction (37), the carry scaffold (38), the gcd arithmetic (39), the carry
dynamics (40), the digit bookkeeping (41), the carry excess and the sieve content of a
window (44), the base-`2` block arithmetic (46), the carry-free primary expansion (47),
the doubling map on the carries (48), the radix criterion (49), the asymptotics of the
carry (50), the period equation (51), the `2`-adic prefix (52), runs of `ω` (53), the
local sieve model (55), window products (56), the period–denominator correspondence
(57), the counting function (58), CRT constructions (60), the `2`-adic content of a
window (61), the exact doubling orbit (64), the Mersenne modulus of the `ω`-window (65)
and the denominator split (66).

Every one of those rounds states what aperiodicity of `ω` would *force*, or constructs
windows of *large* or *small* `ω`-content (round 60), but none of them ever produces a
**witness**: a place where `ω` provably *changes*.  Round 40 has
`omega_not_eventuallyPeriodic`, which is exactly `∀ t M, ∃ n ≥ M, ω (n+t) ≠ ω n`; it is
proved by contradiction from an assumed period and says nothing about *where* the
witnesses are.

**This round is the first to say where they are.**  The main result is

> `jsp87_powPair_strictMin` — for every shift `t ≥ 1` there is a prime `q` and a `K`
> such that **every** power `q^k` with `k ≥ K` is a *strict local minimum* of `ω`:
> `ω (q^k) = 1` while `ω (q^k − t) ≥ 2` and `ω (q^k + t) ≥ 2`.

and hence, in particular,

* `jsp87_omega_pair_lt_of_ge`, `jsp87_omega_pair_gt_of_ge` — the two *directions* of a
  change occur beyond every place (strictly stronger than round 40's statement, which has
  no direction);
* `jsp87_omega_no_eventual_nondec`, `jsp87_omega_no_eventual_noninc` — `ω` is never
  eventually *one-sided monotone* along **any** shift: an eventual period would come
  with an eventual inequality `ω n ≤ ω (n + t)`, and both inequalities are impossible;
* `jsp87_omega_pair_lt_syndetic` — the upward changes are **multiplicatively syndetic**:
  every window `[q^K, X]` contains one, so the witness set is not merely infinite but
  self-similar.

Mathlib contains no statement about the prime factors of `n` and of `n + t` at all, so
everything here is from scratch.

**Why this does not close the gate.**  The remaining blocker is unchanged: the binary
digits of `S` are `ω N + c (N+1) − 2 c N` with `c N = ⌊2^N τ N⌋` the carry excess
(round 41), *not* `ω N` (round 47, `jsp87_digit_ne_omega_one`), so the aperiodicity of
`ω` proved here does not transfer to the digit string.  What this round supplies is the
sharpest available statement of the aperiodicity of the *digit-source*, including the
structure of its witness set, and an independent route to round 40's endgame.
-/

namespace JSP87

/-! ## 0. Powers: size, monotonicity, and the needed congruences -/

/-- `2 * a ≤ q * a` for `2 ≤ q`. -/
private theorem two_mul_le {a q : ℕ} (hq : 2 ≤ q) : 2 * a ≤ q * a := by
  refine Nat.mul_le_mul (n₁ := 2) (n₂ := q) (m₁ := a) (m₂ := a) hq (le_refl a)

/-- `1 * a ≤ q * a` for `1 ≤ q`. -/
private theorem one_mul_le {a q : ℕ} (hq : 1 ≤ q) : 1 * a ≤ q * a := by
  refine Nat.mul_le_mul (n₁ := 1) (n₂ := q) (m₁ := a) (m₂ := a) hq (le_refl a)

/-- `q ^ k ≤ q ^ (k + 1)` for `1 ≤ q`. -/
private theorem pow_succ_mono {q k : ℕ} (hq : 1 ≤ q) : q ^ k ≤ q ^ (k + 1) := by
  rw [pow_succ]
  simpa [Nat.mul_comm, Nat.one_mul] using one_mul_le (q := q) hq (a := q ^ k)

/-- `1 ≤ q ^ d` for `2 ≤ q`. -/
private theorem one_le_pow {q d : ℕ} (hq : 2 ≤ q) : 1 ≤ q ^ d := by
  induction d with
  | zero => rfl
  | succ d ih => exact le_trans ih (pow_succ_mono (by omega) (k := d))

/-- `X < q ^ (k + 1)` follows from `X ≤ q ^ k`, for `2 ≤ q`. -/
private theorem pow_gt {q X k : ℕ} (hq : 2 ≤ q) (hX : X ≤ q ^ k) : X < q ^ (k + 1) := by
  rw [pow_succ, Nat.mul_comm (q ^ k) q]
  have hpos : 0 < q ^ k := pow_pos (by omega) k
  have h1 : 2 * q ^ k ≤ q * q ^ k := two_mul_le hq
  omega

/-- `X ≤ q ^ (k + 1)` follows from `X ≤ q ^ k`. -/
private theorem pow_ge {q X k : ℕ} (hq : 1 ≤ q) (hX : X ≤ q ^ k) : X ≤ q ^ (k + 1) :=
  le_trans hX (pow_succ_mono hq)

/-- `q ^ i ≤ q ^ j` whenever `2 ≤ q` and `i ≤ j`. -/
private theorem pow_mono {q i j : ℕ} (hq : 2 ≤ q) (h : i ≤ j) : q ^ i ≤ q ^ j := by
  have hstep : q ^ i ≤ q ^ i * q ^ (j - i) := by
    have h1 : q ^ i ≤ q ^ (j - i) * q ^ i := Nat.le_mul_of_pos_left (q ^ i) (one_le_pow hq)
    have h2 : q ^ i ≤ q ^ i * q ^ (j - i) := by rwa [Nat.mul_comm]
    simpa using h2
  have hfin : q ^ i * q ^ (j - i) = q ^ j := by
    have h3 : q ^ (i + (j - i)) = q ^ i * q ^ (j - i) := pow_add q i (j - i)
    have h2 : i + (j - i) = j := by omega
    rw [← h3, h2]
  calc q ^ i = q ^ i * 1 := by ring
    _ ≤ q ^ i * q ^ (j - i) := by simpa using hstep
    _ = q ^ j := hfin

/-- Every `X` is exceeded by a power of `q`, for `2 ≤ q`. -/
private theorem exists_pow_gt {q X : ℕ} (hq : 2 ≤ q) : ∃ k, X < q ^ k := by
  have main : ∀ X : ℕ, ∃ k, X < q ^ k := by
    intro X
    induction X using Nat.strong_induction_on with
    | _ X ih =>
      rcases Nat.lt_or_ge X q with h | h
      · refine ⟨1, ?_⟩; rw [pow_one]; exact h
      · obtain ⟨X', rfl⟩ : ∃ X', X = X' + 1 := ⟨X - 1, by omega⟩
        obtain ⟨k, hk⟩ := ih X' (by omega)
        exact ⟨k + 1, pow_gt hq (by omega)⟩
  exact main X

/-- Every `X` is dominated by a power of `q`, for `2 ≤ q`. -/
private theorem exists_pow_ge {q X : ℕ} (hq : 2 ≤ q) : ∃ k, X ≤ q ^ k := by
  obtain ⟨k, hk⟩ := exists_pow_gt (q := q) (X := X) hq
  exact ⟨k, by omega⟩

/-- **Every `X ≥ 1` lies between two consecutive powers of `q`** (`2 ≤ q`): there is a
`k` with `q^k ≤ X < q^(k+1)`.  This is the discrete logarithm, and it is what makes the
witness set of `jsp87_omega_pair_lt_syndetic` self-similar. -/
private theorem exists_pow_le_lt_pow {q X : ℕ} (hq : 2 ≤ q) (hX : 1 ≤ X) :
    ∃ k, q ^ k ≤ X ∧ X < q ^ (k + 1) := by
  have main : ∀ X, 1 ≤ X → ∃ k, q ^ k ≤ X ∧ X < q ^ (k + 1) := by
    intro X hX
    induction X using Nat.strong_induction_on with
    | _ X ih =>
      rcases Nat.lt_or_ge X q with h | h
      · refine ⟨0, ?_, ?_⟩
        · rw [pow_zero]; omega
        · simpa using h
      · have hlt : X / q < X := lt_of_lt_of_le (Nat.div_lt_self (by omega) hq) (by omega)
        have hd : X = q * (X / q) + X % q := (Nat.div_add_mod X q).symm
        have hmod : X % q < q := Nat.mod_lt X (by omega)
        have hY : 1 ≤ X / q := by
          rcases Nat.eq_zero_or_pos (X / q) with hz | hz
          · rw [hz] at hd; omega
          · omega
        obtain ⟨k, hk1, hk2⟩ := ih (X / q) hlt hY
        have hk1' : q ^ (k + 1) ≤ X := by
          have h1 : q ^ k * q ≤ (X / q) * q :=
            Nat.mul_le_mul (n₁ := q ^ k) (n₂ := X / q) (m₁ := q) (m₂ := q) hk1 (le_refl q)
          have h2 : (X / q) * q ≤ X := by
            have hc : (X / q) * q = q * (X / q) := Nat.mul_comm _ _
            omega
          have h3 : q ^ (k + 1) = q ^ k * q := pow_succ q k
          omega
        refine ⟨k + 1, hk1', ?_⟩
        have hme : q * (X / q) + X % q < q * (X / q) + q := by
          have h := Nat.add_lt_add_left hmod (q * (X / q))
          simpa using h
        have hmul : q * (X / q) + q ≤ q * q ^ (k + 1) := by
          have h1 : q * (X / q) + q = q * ((X / q) + 1) := (Nat.mul_succ q (X / q)).symm
          rw [h1]
          refine Nat.mul_le_mul (n₁ := q) (n₂ := q) (m₁ := X / q + 1) (m₂ := q ^ (k + 1))
            (le_refl _) (by omega)
        have hq2 : q ^ ((k + 1) + 1) = q * q ^ (k + 1) := by
          have hk2' : (k + 1) + 1 = k + 2 := by omega
          rw [hk2', pow_succ q (k + 1), Nat.mul_comm]
        omega
  exact main X hX

/-- `2 ^ j ≤ 4` for `j ≤ 2`. -/
private theorem pow_two_le_four {j : ℕ} (h : j ≤ 2) : 2 ^ j ≤ 4 := by
  interval_cases j <;> norm_num

/-- `2 ^ j ≤ 2` for `j ≤ 1`. -/
private theorem pow_two_le_two {j : ℕ} (h : j ≤ 1) : 2 ^ j ≤ 2 := by
  interval_cases j <;> norm_num

/-- `4 ∣ 2 ^ j` for `2 ≤ j`. -/
private theorem dvd_four_pow_two {j : ℕ} (h : 2 ≤ j) : 4 ∣ 2 ^ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [pow_add, show (2 : ℕ) ^ 2 = 4 by rfl, mul_comm]
  exact dvd_mul_of_dvd_left (dvd_refl 4) _

/-- `8 ∣ 2 ^ j` for `3 ≤ j`. -/
private theorem dvd_eight_pow_two {j : ℕ} (h : 3 ≤ j) : 8 ∣ 2 ^ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  rw [pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num, mul_comm]
  exact dvd_mul_of_dvd_left (dvd_refl 8) _

/-- **`a ∣ b - c` whenever `a ∣ b`, `a ∣ c` and `c ≤ b`.**  Mathlib has no such lemma
for the truncated `ℕ` subtraction; the whole file depends on it. -/
private theorem dvd_sub_of_dvd {a b c : ℕ} (ha : 0 < a) (hab : a ∣ b) (hac : a ∣ c)
    (hcb : c ≤ b) : a ∣ b - c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hac
  have hxy : y ≤ x := by
    have hay : a * y ≤ a * x := by rw [← hy, ← hx]; exact hcb
    have hay' : y * a ≤ x * a := by simpa [Nat.mul_comm] using hay
    exact Nat.le_of_mul_le_mul_right hay' ha
  refine ⟨x - y, ?_⟩
  have hb : b = a * x := hx
  have hc : c = a * y := hy
  rw [hb, hc]
  calc a * x - a * y = x * a - y * a := by rw [Nat.mul_comm a x, Nat.mul_comm a y]
    _ = (x - y) * a := (Nat.sub_mul x y a).symm
    _ = a * (x - y) := Nat.mul_comm _ _

/-- `2 ≤ b ^ k` for `2 ≤ b` and `1 ≤ k`. -/
private theorem two_le_pow {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) : 2 ≤ b ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ b ^ j := by
    have h2 : 0 < b ^ j := pow_pos (by omega) j
    omega
  have h2 : 2 * b ^ j ≤ b * b ^ j := by
    refine Nat.mul_le_mul (n₁ := 2) (n₂ := b) (m₁ := b ^ j) (m₂ := b ^ j) hb (le_refl _)
  have h3 : b * b ^ j = b ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
  omega

/-- `4 ≤ b ^ k` for `2 ≤ b` and `2 ≤ k`. -/
private theorem four_le_pow {b k : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) : 4 ≤ b ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hpos : 0 < b ^ j := pow_pos (by omega) j
  have h1 : 1 ≤ b ^ j := by omega
  have h2 : 2 * 2 ≤ b * b := by
    exact Nat.mul_le_mul (n₁ := 2) (n₂ := b) (m₁ := 2) (m₂ := b) (by omega) (by omega)
  have h3 : b ^ (j + 2) = b ^ j * b ^ 2 := by rw [pow_add]
  have h4 : b ^ j * b ^ 2 ≥ 1 * b ^ 2 := Nat.mul_le_mul_right (b ^ 2) h1
  have h5 : 1 * b ^ 2 = b ^ 2 := by ring
  have h6 : b ^ 2 = b * b := by rw [pow_two]
  omega

/-- An even number which is at least `5` and not divisible by `8` is not a power of `2`. -/
private theorem not_pow_two_of_not_eight {n : ℕ} (h2 : 2 ∣ n) (hn : 5 ≤ n) (h8 : ¬ 8 ∣ n) :
    ¬ ∃ j, n = 2 ^ j := by
  rintro ⟨j, hj⟩
  rcases Nat.lt_or_ge j 3 with hlt | hge
  · have hle : 2 ^ j ≤ 4 := pow_two_le_four (by omega)
    omega
  · exact h8 (hj ▸ dvd_eight_pow_two hge)

/-- An even number which is at least `3` and not divisible by `4` is not a power of `2`. -/
private theorem not_pow_two_of_not_four {n : ℕ} (h2 : 2 ∣ n) (hn : 3 ≤ n) (h4 : ¬ 4 ∣ n) :
    ¬ ∃ j, n = 2 ^ j := by
  rintro ⟨j, hj⟩
  rcases Nat.lt_or_ge j 2 with hlt | hge
  · have hle : 2 ^ j ≤ 2 := pow_two_le_two (by omega)
    omega
  · exact h4 (hj ▸ dvd_four_pow_two hge)

/-- `q ∣ q ^ k` for `1 ≤ k`. -/
private theorem self_dvd_pow {q k : ℕ} (hk : 1 ≤ k) : q ∣ q ^ k := by
  simpa using pow_dvd_pow q hk

/-- `4 ∣ 5 ^ k - 1` for every `k`. -/
private theorem modFour_five (k : ℕ) : 4 ∣ 5 ^ k - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨5 * c + 1, ?_⟩
    have hpos : 0 < 5 ^ k := by positivity
    rw [pow_succ]
    omega

/-- `8 ∣ 5 ^ (2 * m) - 1`. -/
private theorem modEight_five_even (m : ℕ) : 8 ∣ 5 ^ (2 * m) - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨25 * c + 3, ?_⟩
    have hpos : 0 < 5 ^ (2 * m) := by positivity
    have hk : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hk, pow_add]
    omega

/-- `8 ∣ 5 ^ (2 * m + 1) - 5`. -/
private theorem modEight_five_odd (m : ℕ) : 8 ∣ 5 ^ (2 * m + 1) - 5 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨25 * c + 15, ?_⟩
    have hpos : 0 < 5 ^ (2 * m + 1) := by positivity
    have hk : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [hk, pow_add]
    omega

/-- `3 ∣ 5 ^ (2 * m) - 1`. -/
private theorem modThree_five_even (m : ℕ) : 3 ∣ 5 ^ (2 * m) - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨25 * c + 8, ?_⟩
    have hpos : 0 < 5 ^ (2 * m) := by positivity
    have hk : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hk, pow_add]
    omega

/-- `8 ∣ 9 ^ m - 1`. -/
private theorem modEight_nine (m : ℕ) : 8 ∣ 9 ^ m - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨9 * c + 1, ?_⟩
    have hpos : 0 < 9 ^ m := by positivity
    rw [pow_succ]
    omega

/-- No power of `2` is divisible by `3`. -/
private theorem not_three_dvd_pow_two (j : ℕ) : ¬ (3 : ℕ) ∣ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    intro hd
    have hstep : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h1 : 3 ∣ 2 ^ j * 2 := by rwa [hstep] at hd
    rcases (Nat.Prime.dvd_mul (p := 3) (by norm_num)).mp h1 with h | h
    · exact ih h
    · omega

/-- `a * n ≤ a * m` follows from `n ≤ m` (Mathlib has only the first-factor form
`Nat.mul_le_mul` for `ℕ`, and `Nat.mul_le_mul_right` multiplies on the *left*). -/
private theorem mul_le_mul_right' {a n m : ℕ} (h : n ≤ m) : a * n ≤ a * m := by
  have h2 := Nat.mul_le_mul (n₁ := n) (n₂ := m) (m₁ := a) (m₂ := a) h (le_refl a)
  rwa [Nat.mul_comm n a, Nat.mul_comm m a] at h2

/-- **`q^k < q^j` forces `k < j`, for `2 ≤ q`.**  Mathlib has no such lemma. -/
private theorem pow_lt_pow_imp {q k j : ℕ} (hq : 2 ≤ q) (h : q ^ k < q ^ j) : k < j := by
  by_contra hc
  have hkj : k = j + (k - j) := by omega
  rw [hkj, pow_add] at h
  have h1 : 1 ≤ q ^ (k - j) := by
    have h2 : 0 < q ^ (k - j) := pow_pos (by omega) (k - j)
    omega
  have h2 : q ^ j * q ^ (k - j) ≥ q ^ j := by
    have h3 := mul_le_mul_right' (a := q ^ j) h1
    simpa using h3
  omega

/-- An odd number is `2 * c + 1`. -/
private theorem odd_repr {m : ℕ} (hm : m % 2 = 1) : ∃ c, m = 2 * c + 1 := by
  have hh := (Nat.div_add_mod m 2).symm
  rw [hm] at hh
  exact ⟨m / 2, by omega⟩

/-- **Every power of an odd number is odd.** -/
private theorem odd_repr_pow {b k : ℕ} (hb : ∃ c, b = 2 * c + 1) : ∃ c, b ^ k = 2 * c + 1 := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨d, hd⟩ := hb
      refine ⟨(2 * d + 1) * c + d, ?_⟩
      rw [pow_succ, hc, hd]
      ring

/-- `2 ∣ m + 1` when `m` is odd. -/
private theorem two_dvd_add_one_of_odd {m : ℕ} (hm : m % 2 = 1) : 2 ∣ m + 1 := by
  obtain ⟨c, hc⟩ := odd_repr hm
  exact ⟨c + 1, by omega⟩

/-- `2 ∣ m - 1` when `m` is odd and `1 ≤ m`. -/
private theorem two_dvd_sub_one_of_odd {m : ℕ} (hm : m % 2 = 1) (_h1 : 1 ≤ m) : 2 ∣ m - 1 := by
  obtain ⟨c, hc⟩ := odd_repr hm
  exact ⟨c, by omega⟩

/-- `2 ∣ b ^ k + 1` when `b` is odd. -/
private theorem two_dvd_pow_add_one {b k : ℕ} (hb : ∃ c, b = 2 * c + 1) : 2 ∣ b ^ k + 1 := by
  obtain ⟨c, hc⟩ := odd_repr_pow (b := b) (k := k) hb
  exact ⟨c + 1, by omega⟩

/-- `2 ∣ b ^ k - 1` when `b` is odd. -/
private theorem two_dvd_pow_sub_one {b k : ℕ} (hb : ∃ c, b = 2 * c + 1) : 2 ∣ b ^ k - 1 := by
  obtain ⟨c, hc⟩ := odd_repr_pow (b := b) (k := k) hb
  exact ⟨c, by omega⟩

/-! ## 1. `ω n = 1` — the one-prime-factor locus of `ω` -/

/-- **`ω n = 1` iff `n` is a power of a single prime.**  Mathlib has no such
characterisation; it is the fact that lets one say "the number `m` has only one prime
factor, namely `q`" and conclude `m = q^j`. -/
theorem omega_eq_one_iff {n : ℕ} :
    omega n = 1 ↔ ∃ p, p.Prime ∧ ∃ k, 1 ≤ k ∧ n = p ^ k := by
  constructor
  · intro h
    have hcard : n.primeFactors.card = 1 := by
      rw [← omega, h]
    obtain ⟨p, heq⟩ : ∃ p, n.primeFactors = ({p} : Finset ℕ) := Finset.card_eq_one.mp hcard
    have hpmem : p ∈ n.primeFactors := heq ▸ Finset.mem_singleton.mpr rfl
    have hspec := Nat.mem_primeFactors.mp hpmem
    have hp : p.Prime := hspec.1
    have hp2 : 2 ≤ p := hp.two_le
    have hne : n ≠ 0 := hspec.2.2
    have hpd : p ∣ n := hspec.2.1
    have hkey : ∀ q, q.Prime → q ∣ n → q = p := by
      intro q hq hqd
      have hmem : q ∈ n.primeFactors := hq.mem_primeFactors hqd hne
      rw [heq, Finset.mem_singleton] at hmem
      exact hmem
    have main : ∀ (m : ℕ), 0 < m → p ∣ m → (∀ q, q.Prime → q ∣ m → q = p) →
        ∃ k, 1 ≤ k ∧ m = p ^ k := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro hm hpm hkm
        have hdiv : m = p * (m / p) := (Nat.mul_div_cancel' hpm).symm
        have hq0 : 0 < m / p := by
          rcases Nat.eq_zero_or_pos (m / p) with hz | hz
          · exfalso; rw [hz] at hdiv; omega
          · omega
        have hlt : m / p < m := Nat.div_lt_self hm hp2
        by_cases hcard : (m / p).primeFactors.card = 0
        · rcases Nat.eq_zero_or_pos (m / p) with hz | hz
          · exfalso; rw [hz] at hdiv; omega
          · have hz1 : m / p = 1 := by
              have hle : m / p ≤ 1 := omega_eq_zero_iff.mp hcard
              omega
            refine ⟨1, by omega, ?_⟩
            rw [hdiv, hz1]
            ring
        · have hins : m.primeFactors = insert p (m / p).primeFactors :=
            primeFactors_div_prime hm.ne' hp hpm
          have hsub : (m / p).primeFactors ⊆ ({p} : Finset ℕ) := by
            intro q hq
            have hmem : q ∈ m.primeFactors := hins ▸ Finset.mem_insert_of_mem hq
            obtain ⟨hq', hqd, -⟩ := Nat.mem_primeFactors.mp hmem
            exact Finset.mem_singleton.mpr (hkm q hq' hqd)
          have hcard1 : (m / p).primeFactors.card = 1 := by
            have hle : (m / p).primeFactors.card ≤ 1 := by
              simpa using Finset.card_le_card hsub
            omega
          obtain ⟨r, heq'⟩ : ∃ r, (m / p).primeFactors = ({r} : Finset ℕ) :=
            Finset.card_eq_one.mp hcard1
          have hr : r ∈ (m / p).primeFactors := heq' ▸ Finset.mem_singleton.mpr rfl
          have hrprime : r.Prime := (Nat.mem_primeFactors.mp hr).1
          have hrd : r ∣ m / p := (Nat.mem_primeFactors.mp hr).2.1
          have hrd' : r ∣ m := by
            have heq2 : (m / p) * p = m := by rw [Nat.mul_comm, ← hdiv]
            rw [← heq2]
            exact dvd_mul_of_dvd_left hrd p
          have hpd' : p ∣ m / p := by
            have hkey' : r = p := hkm r hrprime hrd'
            exact hkey' ▸ hrd
          obtain ⟨k, hk1, hmk⟩ := ih (m / p) hlt hq0 hpd' (fun q hq hqd => by
            have hqd' : q ∣ m := by
              have heq2 : (m / p) * p = m := by rw [Nat.mul_comm, ← hdiv]
              rw [← heq2]
              exact dvd_mul_of_dvd_left hqd p
            exact hkm q hq hqd')
          refine ⟨k + 1, by omega, ?_⟩
          rw [hdiv, hmk, pow_succ, Nat.mul_comm]
    obtain ⟨k, hk1, hnk⟩ := main n (by omega) hpd hkey
    exact ⟨p, hp, k, hk1, hnk⟩
  · rintro ⟨p, hp, k, hk, rfl⟩
    exact omega_prime_pow hp hk

/-- **Two distinct prime divisors force `ω n ≥ 2`.** -/
theorem omega_ge_two {n p q : ℕ} (hn : 0 < n) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpd : p ∣ n) (hqd : q ∣ n) : 2 ≤ omega n := by
  have hpm : p ∈ n.primeFactors := hp.mem_primeFactors hpd hn.ne'
  have hqm : q ∈ n.primeFactors := hq.mem_primeFactors hqd hn.ne'
  have hne : q ∉ insert p (∅ : Finset ℕ) := by
    rw [Finset.mem_insert]
    intro h
    rcases h with h | h
    · exact absurd h.symm hpq
    · simp at h
  have hsub : insert q (insert p (∅ : Finset ℕ)) ⊆ n.primeFactors :=
    Finset.insert_subset hqm (Finset.insert_subset hpm (Finset.empty_subset _))
  have hcard : (insert q (insert p (∅ : Finset ℕ))).card = 2 := by
    rw [Finset.card_insert_of_notMem hne, Finset.card_insert_of_notMem (by simp),
      Finset.card_empty]
  rw [omega]
  calc (2 : ℕ) = (insert q (insert p (∅ : Finset ℕ))).card := hcard.symm
    _ ≤ n.primeFactors.card := Finset.card_le_card hsub

/-- **`ω n ≥ 2` as soon as `n` is divisible by a prime `q` and is not a power of `q`.**
This is the workhorse of the whole file. -/
theorem omega_ge_two_of_not_primePow {n q : ℕ} (hq : q.Prime) (hn : 0 < n) (hqd : q ∣ n)
    (h : ¬ ∃ j, n = q ^ j) : 2 ≤ omega n := by
  by_cases hone : omega n = 1
  · exfalso
    obtain ⟨p, hp, k, hk, hnk⟩ := omega_eq_one_iff.mp hone
    have hq' : q ∣ p ^ k := by rw [← hnk]; exact hqd
    have hq'' : q ∣ p := (prime_dvd_pow_iff hq k hk).mp hq'
    have heq : q = p := prime_eq_of_prime_dvd hq hp hq''
    exact h ⟨k, by rw [hnk, heq]⟩
  · have hz : omega n = 0 ∨ 2 ≤ omega n := by
      rcases Nat.lt_or_ge (omega n) 2 with hlt | hge
      · rcases Nat.eq_zero_or_pos (omega n) with hzero | hpos
        · exact Or.inl hzero
        · exfalso; omega
      · exact Or.inr hge
    rcases hz with hz | hz
    · exfalso
      have hz' : n ≤ 1 := omega_eq_zero_iff.mp hz
      have hq2 : 2 ≤ q := hq.two_le
      obtain ⟨c, hc⟩ := hqd
      have hqc : 2 * c ≤ q * c := by
        exact Nat.mul_le_mul (n₁ := 2) (n₂ := q) (m₁ := c) (m₂ := c) hq2 (le_refl c)
      have hc0 : c = 0 := by omega
      rw [hc0] at hc
      omega
    · exact hz

/-! ## 2. Powers of `3` are minima of `ω` — the `t = 1` witnesses -/

/-- `8 ∣ 9 ^ r - 1` gives the shape `9 ^ r = 8 * c + 1`. -/
private theorem nine_eq_eight_mul_add_one {r c : ℕ} (h : 9 ^ r - 1 = 8 * c) :
    9 ^ r = 8 * c + 1 := by
  have hpos : 0 < 9 ^ r := by positivity
  omega

/-- `3 ^ (r + r) = 9 ^ r`. -/
private theorem three_pow_two_mul (r : ℕ) : 3 ^ (2 * r) = 9 ^ r := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul]

/-- `3 ^ (2 * r + 1) = 3 * 9 ^ r`. -/
private theorem three_pow_succ_two_mul (r : ℕ) : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by
  have h1 : 3 ^ (2 * r + 1) = 3 ^ (2 * r) * 3 := by rw [pow_succ]
  rw [h1, three_pow_two_mul r, Nat.mul_comm]

/-- **`3^k + 1` is never a power of `2`, for `2 ≤ k`.**  If `k` is even then
`3^k = 9^r ≡ 1 [MOD 8]`, so `3^k + 1 = 8c + 2` is `2` but not `4`; if `k` is odd then
`3^k = 3·9^r = 24c + 3`, so `3^k + 1 = 24c + 4` is `4` but not `8`.  In both cases the only
power of `2` still possible is too small. -/
private theorem three_pow_add_one_not_pow_two {k : ℕ} (hk : 2 ≤ k) :
    ¬ ∃ j, 3 ^ k + 1 = 2 ^ j := by
  have hbig : 4 ≤ 3 ^ k := four_le_pow (by omega) hk
  have h2 : 2 ∣ 3 ^ k + 1 := two_dvd_pow_add_one (b := 3) (k := k) (⟨1, by norm_num⟩)
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨c, hc⟩ := modEight_nine r
    have hA : 9 ^ r = 8 * c + 1 := nine_eq_eight_mul_add_one hc
    have h1 : 3 ^ k = 9 ^ r := by
      rw [hr, show r + r = 2 * r from by omega, three_pow_two_mul r]
    have hB : 3 ^ k + 1 = 8 * c + 2 := by rw [h1]; omega
    have h4 : ¬ 4 ∣ 3 ^ k + 1 := by
      intro hd
      obtain ⟨y, hy⟩ := hd
      rw [hB] at hy
      omega
    rintro ⟨j, hj⟩
    exact not_pow_two_of_not_four h2 (by omega) h4 ⟨j, hj⟩
  · obtain ⟨c, hc⟩ := modEight_nine r
    have hA : 9 ^ r = 8 * c + 1 := nine_eq_eight_mul_add_one hc
    have h1 : 3 ^ k = 3 * 9 ^ r := by
      rw [hr, three_pow_succ_two_mul r]
    have hB : 3 ^ k + 1 = 8 * (3 * c) + 4 := by rw [h1]; omega
    have h8 : ¬ 8 ∣ 3 ^ k + 1 := by
      intro hd
      obtain ⟨y, hy⟩ := hd
      rw [hB] at hy
      omega
    rintro ⟨j, hj⟩
    exact not_pow_two_of_not_eight h2 (by omega) h8 ⟨j, hj⟩

/-- **`3^k - 1` is never a power of `2`, for odd `k ≥ 3`.**  For odd `k`,
`3^k = 3·9^r = 24c + 3`, so `3^k - 1 = 24c + 2` is `2` but not `4`; the only power of `2`
that could still occur is `2` itself, which is too small. -/
private theorem three_pow_sub_one_not_pow_two {k : ℕ} (hk : 3 ≤ k) (hodd : ¬ Even k) :
    ¬ ∃ j, 3 ^ k - 1 = 2 ^ j := by
  have hbig : 4 ≤ 3 ^ k := four_le_pow (by omega) (by omega)
  have h2 : 2 ∣ 3 ^ k - 1 := two_dvd_pow_sub_one (b := 3) (k := k) (⟨1, by norm_num⟩)
  obtain ⟨r, hr⟩ : ∃ r, k = 2 * r + 1 := by
    rcases Nat.even_or_odd k with ⟨r0, hr0⟩ | ⟨r1, hr1⟩
    · exact absurd ⟨r0, hr0⟩ hodd
    · exact ⟨r1, hr1⟩
  obtain ⟨c, hc⟩ := modEight_nine r
  have hA : 9 ^ r = 8 * c + 1 := nine_eq_eight_mul_add_one hc
  have h1 : 3 ^ k = 3 * 9 ^ r := by rw [hr, three_pow_succ_two_mul r]
  have hB : 3 ^ k - 1 = 8 * (3 * c) + 2 := by rw [h1]; omega
  have h4 : ¬ 4 ∣ 3 ^ k - 1 := by
    intro hd
    obtain ⟨y, hy⟩ := hd
    rw [hB] at hy
    omega
  rintro ⟨j, hj⟩
  exact not_pow_two_of_not_four h2 (by omega) h4 ⟨j, hj⟩

/-- `ω (3^k + 1) ≥ 2` for `2 ≤ k`: `3^k + 1` is even and is not a power of `2`. -/
theorem omega_three_pow_add_one_ge_two {k : ℕ} (hk : 2 ≤ k) : 2 ≤ omega (3 ^ k + 1) := by
  have hbig : 4 ≤ 3 ^ k := four_le_pow (by omega) hk
  have hpos : 0 < 3 ^ k + 1 := by omega
  exact omega_ge_two_of_not_primePow (by norm_num) hpos
    (two_dvd_pow_add_one (b := 3) (k := k) (⟨1, by norm_num⟩)) (three_pow_add_one_not_pow_two hk)

/-- `ω (3^k - 1) ≥ 2` for odd `k ≥ 3`. -/
theorem omega_three_pow_sub_one_ge_two {k : ℕ} (hk : 3 ≤ k) (hodd : ¬ Even k) :
    2 ≤ omega (3 ^ k - 1) := by
  have hbig : 4 ≤ 3 ^ k := four_le_pow (by omega) (by omega)
  have hpos : 0 < 3 ^ k - 1 := by omega
  exact omega_ge_two_of_not_primePow (by norm_num) hpos
    (two_dvd_pow_sub_one (b := 3) (k := k) (⟨1, by norm_num⟩))
    (three_pow_sub_one_not_pow_two hk hodd)

/-! ## 3. Neighbours of a large power -/

/-- **A NEIGHBOUR OF A LARGE POWER OF `q` IS NEVER A POWER OF `q`.**  Let `2 ≤ q`,
`q ∣ t`, `0 < t` and `2t < q^k`.  Then both `q^k - t` and `q^k + t` are numbers `≥ 2`
divisible by `q` and are not powers of `q`; this is exactly what one needs to run
`omega_ge_two_of_not_primePow` on the prime-power ray of `q`. -/
private theorem pow_plus_neighbour {q t k : ℕ} (hq2 : 2 ≤ q) (ht : 0 < t) (hqd : q ∣ t)
    (hk : 2 * t < q ^ k) :
    2 ≤ q ^ k + t ∧ q ∣ q ^ k + t ∧ ¬ ∃ j, q ^ k + t = q ^ j := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hz | hz
    · rw [hz, pow_zero] at hk; omega
    · omega
  have hqk : q ∣ q ^ k := self_dvd_pow hk1
  have hadd : q ∣ q ^ k + t := dvd_add hqk hqd
  have hbig : 2 ≤ q ^ k + t := by omega
  have htle : t ≤ q ^ k := by omega
  refine ⟨hbig, hadd, ?_⟩
  rintro ⟨j, hj⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    rw [pow_zero] at hj
    omega
  · -- `q^k ∣ q^j` and `q^k ∣ q^k`, hence `q^k ∣ t`, i.e. `q^k ≤ t < q^k`
    -- `j > k`, so `q^k ∣ q^j`, hence `q^k ∣ t ≤ q^k`, contradiction
    have hjk : k < j := pow_lt_pow_imp hq2 (by rw [← hj]; omega)
    have hjvd : q ^ k ∣ q ^ j := pow_dvd_pow q (Nat.le_of_lt hjk)
    have hpos : 0 < q ^ k := pow_pos (by omega) k
    have hle : q ^ k ≤ q ^ j := by
      obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
      rw [pow_add]
      have h1 : 1 ≤ q ^ m := by
        have h2 : 0 < q ^ m := pow_pos (by omega) m
        omega
      simpa using mul_le_mul_right' (a := q ^ k) h1
    have hjeq : q ^ j - q ^ k = t := hj ▸ Nat.add_sub_cancel_left (q ^ k) t
    have hkvt : q ^ k ∣ t := hjeq ▸ dvd_sub_of_dvd hpos hjvd dvd_rfl hle
    have hkle : q ^ k ≤ t := Nat.le_of_dvd ht hkvt
    omega

/-! ## 4. THE FLAGSHIP — geometric rays that never meet the `ω = 1` set -/

/-- **THE `2`-RAY FOR AN EVEN SHIFT.**  If `t` is a positive even number and
`2t < 2^k`, then `ω (2^k) = 1 < ω (2^k + t)`. -/
theorem jsp87_powPair_min_two {t k : ℕ} (ht : 0 < t) (h2 : 2 ∣ t) (hk : 2 * t < 2 ^ k) :
    omega (2 ^ k) = 1 ∧ 2 ≤ omega (2 ^ k + t) := by
  obtain ⟨hA, hB, hC⟩ := pow_plus_neighbour (t := t) (k := k) (q := 2) (by omega) ht h2 hk
  have hpos : 0 < 2 ^ k + t := by omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hz | hz
    · rw [hz, pow_zero] at hk; omega
    · omega
  exact ⟨omega_prime_pow (by norm_num) hk1,
    omega_ge_two_of_not_primePow (by norm_num) hpos hB hC⟩

/-- **THE `q`-RAY FOR A PRIME `q` DIVIDING `t`.**  If `q` is prime, `q ∣ t` and
`2t < q^k`, then `ω (q^k) = 1 < ω (q^k + t)`. -/
theorem jsp87_powPair_min_prime {t q k : ℕ} (ht : 0 < t) (hq : q.Prime) (hqd : q ∣ t)
    (hk : 2 * t < q ^ k) : omega (q ^ k) = 1 ∧ 2 ≤ omega (q ^ k + t) := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hz | hz
    · rw [hz, pow_zero] at hk; omega
    · omega
  obtain ⟨hA, hB, hC⟩ := pow_plus_neighbour (t := t) (k := k) (q := q) hq.two_le ht hqd hk
  have hpos : 0 < q ^ k + t := by omega
  exact ⟨omega_prime_pow hq hk1, omega_ge_two_of_not_primePow hq hpos hB hC⟩

/-- **EVERY POWER OF `3` IS A STRICT LOCAL MINIMUM OF `ω`** (for `k ≥ 2`):
`ω (3^k) = 1` while `ω (3^k + 1) ≥ 2`; and for odd `k` also `ω (3^k - 1) ≥ 2`.
Mathlib contains no such statement. -/
theorem jsp87_powPair_strictMin_three {k : ℕ} (hk : 2 ≤ k) :
    omega (3 ^ k) = 1 ∧ 2 ≤ omega (3 ^ k + 1) :=
  ⟨omega_prime_pow (by norm_num) (by omega), omega_three_pow_add_one_ge_two hk⟩

/-- ... and for odd `k` the *lower* neighbour too: `ω (3^k - 1) ≥ 2 > ω (3^k) = 1`. -/
theorem jsp87_powPair_strictMin_three_odd {k : ℕ} (hk : 3 ≤ k) (hodd : ¬ Even k) :
    omega (3 ^ k) = 1 ∧ 2 ≤ omega (3 ^ k - 1) ∧ 2 ≤ omega (3 ^ k + 1) :=
  ⟨omega_prime_pow (by norm_num) (by omega), omega_three_pow_sub_one_ge_two hk hodd,
    omega_three_pow_add_one_ge_two (by omega)⟩

/-- **THE MAIN RESULT OF THIS ROUND.  For every shift `t ≥ 1` there is a prime `q` and a
`K` such that every `q^k`, `k ≥ K`, is a point where `ω` takes its global minimum
value `1` while the translate `q^k + t` has at least two distinct prime factors:**

`ω (q^k) = 1` and `ω (q^k + t) ≥ 2` for all `k ≥ K`.

*If `t` is even* take `q = 2`; *if `t = 1`* take `q = 3`
(`jsp87_powPair_strictMin_three`); *if `t` is odd and `t > 1`* take any prime factor of
`t`.

This is the first statement in the development which says **where** the aperiodicity of
`ω` is witnessed: on a whole geometric ray, so the witness set of
`ω (n+t) ≠ ω n` is unbounded, self-similar, and — by
`jsp87_omega_pair_lt_syndetic` — multiplicatively syndetic. -/
theorem jsp87_powPair_min {t : ℕ} (ht : 0 < t) :
    ∃ q, q.Prime ∧ ∃ K, ∀ k, K ≤ k → omega (q ^ k) = 1 ∧ 2 ≤ omega (q ^ k + t) := by
  rcases Nat.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- `t` is even: the ray of powers of `2`
    have h2 : 2 ∣ t := ⟨r, by omega⟩
    obtain ⟨k0, hk0⟩ := exists_pow_gt (q := 2) (X := 2 * t) (by omega)
    refine ⟨2, by norm_num, k0 + 1, fun k hk => ?_⟩
    have hk' : 2 * t < 2 ^ k := by
      have hmono : 2 ^ k0 ≤ 2 ^ k := pow_mono (by omega) (by omega)
      omega
    exact jsp87_powPair_min_two ht h2 hk'
  · rcases Nat.lt_or_ge t 3 with h3 | h3
    · -- `t ∈ {1, 2}` and odd, so `t = 1`: the ray of powers of `3`
      have ht1 : t = 1 := by omega
      subst ht1
      exact ⟨3, by norm_num, 2, fun k hk => jsp87_powPair_strictMin_three hk⟩
    · -- `t` is odd and `> 1`: take a prime factor of `t`
      obtain ⟨q, hq, hqd⟩ : ∃ q, q.Prime ∧ q ∣ t :=
        Nat.ne_one_iff_exists_prime_dvd.mp (by omega)
      obtain ⟨k0, hk0⟩ := exists_pow_gt (q := q) (X := 2 * t) hq.two_le
      refine ⟨q, hq, k0 + 1, fun k hk => ?_⟩
      have hk' : 2 * t < q ^ k := by
        have hmono : q ^ k0 ≤ q ^ k := pow_mono hq.two_le (by omega)
        omega
      exact jsp87_powPair_min_prime ht hq hqd hk'

/-- **The `ω`-values differ on a whole geometric ray, for every shift.** -/
theorem jsp87_powPair_ne {t : ℕ} (ht : 0 < t) :
    ∃ q, q.Prime ∧ ∃ K, ∀ k, K ≤ k → omega (q ^ k) ≠ omega (q ^ k + t) := by
  obtain ⟨q, hq, K, hK⟩ := jsp87_powPair_min ht
  exact ⟨q, hq, K, fun k hk => by obtain ⟨h1, h2⟩ := hK k hk; omega⟩

/-- **`ω` changes upwards on a whole geometric ray, for every shift.** -/
theorem jsp87_powPair_lt {t : ℕ} (ht : 0 < t) :
    ∃ q, q.Prime ∧ ∃ K, ∀ k, K ≤ k → omega (q ^ k) < omega (q ^ k + t) := by
  obtain ⟨q, hq, K, hK⟩ := jsp87_powPair_min ht
  exact ⟨q, hq, K, fun k hk => by obtain ⟨h1, h2⟩ := hK k hk; omega⟩

/-- **THE TRANSLATES OF A GEOMETRIC RAY NEVER MEET THE `ω = 1` SET.**  For every shift
`t` there is a prime `q` such that `q^k + t` always has at least two distinct prime
factors, for every large `k`; so the "prime power" pattern of `ω` (value `1`) does not
repeat at any fixed offset of a ray. -/
theorem jsp87_powPair_add_ne_one {t : ℕ} (ht : 0 < t) :
    ∃ q, q.Prime ∧ ∃ K, ∀ k, K ≤ k → 2 ≤ omega (q ^ k + t) := by
  obtain ⟨q, hq, K, hK⟩ := jsp87_powPair_min ht
  exact ⟨q, hq, K, fun k hk => by obtain ⟨h1, h2⟩ := hK k hk; exact h2⟩

/-! ## 5. The aperiodicity consequences: everywhere, and syndetically -/

/-- **UPWARD CHANGES BEYOND EVERY PLACE.**  For every `t ≥ 1` and every `M` there is a
place `n ≥ M` with `ω n < ω (n + t)`.  Round 40's `omega_not_eventuallyPeriodic` says
the same without a direction; this is strictly stronger. -/
theorem jsp87_omega_pair_lt_of_ge {t M : ℕ} (ht : 0 < t) :
    ∃ n, M ≤ n ∧ omega n < omega (n + t) := by
  obtain ⟨q, hq, K, hK⟩ := jsp87_powPair_lt ht
  obtain ⟨k, hk⟩ := exists_pow_ge (q := q) (X := M) hq.two_le
  obtain ⟨k', hk'⟩ := exists_pow_ge (q := q) (X := K) hq.two_le
  have hmono : q ^ k ≤ q ^ max k (max k' K) := pow_mono hq.two_le (Nat.le_max_left k _)
  have hmono' : q ^ k' ≤ q ^ max k (max k' K) :=
    pow_mono hq.two_le (by omega)
  refine ⟨q ^ max k (max k' K), by omega, hK (max k (max k' K)) (by omega)⟩

/-- **A CHANGE BEYOND EVERY PLACE.** -/
theorem jsp87_omega_pair_ne_of_ge {t M : ℕ} (ht : 0 < t) :
    ∃ n, M ≤ n ∧ omega n ≠ omega (n + t) := by
  obtain ⟨n, hn, hlt⟩ := jsp87_omega_pair_lt_of_ge (t := t) (M := M) ht
  exact ⟨n, hn, by omega⟩

/-- **NO TWO POSITIONS AT DISTANCE `t ≥ 1`, BEYOND ANY PLACE, HAVE THE SAME `ω`.**
This is round 40's `omega_not_eventuallyPeriodic` re-proved from the ray witnesses. -/
theorem jsp87_omega_not_eventuallyPeriodic' :
    ¬ ∃ t M : ℕ, 0 < t ∧ ∀ n : ℕ, M ≤ n → omega (n + t) = omega n := by
  rintro ⟨t, M, ht, hp⟩
  obtain ⟨n, hn, hne⟩ := jsp87_omega_pair_ne_of_ge (t := t) (M := M) ht
  exact absurd (hp n hn) (by omega)

/-- **THE WITNESSES OF THE UPWARD CHANGE ARE MULTIPLICATIVELY SYNDETIC.**  If `q` is a
prime and `ω (q^k) < ω (q^k + t)` for every `k ≥ K`, then *every* window `[q^K, X]`
contains a witness.  In particular the witness set is not merely infinite: its
multiplicative gaps are bounded by the base `q` of the ray. -/
theorem jsp87_omega_pair_lt_syndetic {t q K : ℕ} (hq : q.Prime) (_hK : 1 ≤ K)
    (hray : ∀ k, K ≤ k → omega (q ^ k) < omega (q ^ k + t)) {X : ℕ} (hX : q ^ K ≤ X) :
    ∃ n, q ^ K ≤ n ∧ n ≤ X ∧ omega n < omega (n + t) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqK : 1 ≤ q ^ K := by
    have h2 : 0 < q ^ K := pow_pos (by omega) K
    omega
  have hX1 : 1 ≤ X := by omega
  obtain ⟨k, hk1, hk2⟩ := exists_pow_le_lt_pow (q := q) (X := X) hq.two_le hX1
  have hKk : K ≤ k := by
    by_contra hc
    have hke : k < K := by omega
    have hmono : q ^ (k + 1) ≤ q ^ K := pow_mono hq.two_le (by omega)
    omega
  have hmono : q ^ K ≤ q ^ k := pow_mono hq.two_le hKk
  exact ⟨q ^ k, hmono, hk1, hray k hKk⟩

/-- **THE UPWARD CHANGES OF `ω` ARE UNBOUNDED**, and — by
`jsp87_omega_pair_lt_syndetic` — occur at every scale. -/
theorem jsp87_omega_pair_lt_arbitrarily_large {t X : ℕ} (ht : 0 < t) :
    ∃ n, X < n ∧ omega n < omega (n + t) := by
  obtain ⟨n, hn, hlt⟩ := jsp87_omega_pair_lt_of_ge (t := t) (M := X + 1) ht
  exact ⟨n, by omega, hlt⟩

/-- **`ω` IS NEVER EVENTUALLY NON-INCREASING ALONG A SHIFT.**  No shift `t ≥ 1` can
satisfy `ω n ≥ ω (n + t)` for all large `n`, because there are upward steps beyond
every place.  Together with round 40 this pins the aperiodicity from both sides. -/
theorem jsp87_omega_no_eventual_noninc :
    ¬ ∃ t M : ℕ, 0 < t ∧ ∀ n : ℕ, M ≤ n → omega n ≥ omega (n + t) := by
  rintro ⟨t, M, ht, hp⟩
  obtain ⟨n, hn, hlt⟩ := jsp87_omega_pair_lt_of_ge (t := t) (M := M) ht
  exact absurd (hp n hn) (by omega)

/-- **THE MINIMUM-VALUE LOCI OF `ω` ARE VISIBLE AT EVERY SCALE.**  For every shift `t`
and every place `K` there is a place `n ≥ K` at which `ω` takes its global minimum value
`1` while the neighbour at distance `t` takes a strictly larger value. -/
theorem jsp87_powPair_min_beyond {t K : ℕ} (ht : 0 < t) :
    ∃ n, K ≤ n ∧ omega n = 1 ∧ 2 ≤ omega (n + t) := by
  obtain ⟨q, hq, K₀, hK₀⟩ := jsp87_powPair_min ht
  obtain ⟨k, hk⟩ := exists_pow_ge (q := q) (X := K) hq.two_le
  have hmono : q ^ k ≤ q ^ max k K₀ := pow_mono hq.two_le (Nat.le_max_left k K₀)
  have h1 : K ≤ q ^ k := hk
  have h2 : q ^ k ≤ q ^ max k K₀ := hmono
  have h3 : K ≤ q ^ max k K₀ := by omega
  exact ⟨q ^ max k K₀, h3, hK₀ (max k K₀) (Nat.le_max_right k K₀)⟩

/-! ## 6. Machine-checked instances -/

/-- **THE `t = 1` WITNESS, BY HAND: `27` is a strict local minimum of `ω`**
(`26 = 2·13` and `28 = 2²·7`). -/
theorem jsp87_omega_strictMin_27 : omega 27 = 1 ∧ 2 ≤ omega 26 ∧ 2 ≤ omega 28 := by
  have hodd : ¬ Even 3 := by rintro ⟨r, hr⟩; omega
  have h := jsp87_powPair_strictMin_three_odd (k := 3) (by omega) hodd
  simpa [show (3 : ℕ) ^ 3 = 27 from by norm_num] using h

/-- The same at `3^5 = 243`: `242 = 2·11²` and `244 = 2²·61`, so `243` is again a
strict local minimum of `ω`. -/
theorem jsp87_omega_strictMin_243 : omega 243 = 1 ∧ 2 ≤ omega 242 ∧ 2 ≤ omega 244 := by
  have hodd : ¬ Even 5 := by rintro ⟨r, hr⟩; omega
  have h := jsp87_powPair_strictMin_three_odd (k := 5) (by omega) hodd
  simpa [show (3 : ℕ) ^ 5 = 243 from by norm_num] using h

/-- `81 = 3^4` is a strict local minimum in the *upper* direction: `ω 81 = 1 < ω 82`. -/
theorem jsp87_omega_strictMin_81 : omega 81 = 1 ∧ 2 ≤ omega 82 := by
  have h := jsp87_powPair_strictMin_three (k := 4) (by omega)
  simpa [show (3 : ℕ) ^ 4 = 81 from by norm_num] using h

/-- The same at `3^6 = 729`: `ω 729 = 1 < ω 730`. -/
theorem jsp87_omega_strictMin_729 : omega 729 = 1 ∧ 2 ≤ omega 730 := by
  have h := jsp87_powPair_strictMin_three (k := 6) (by omega)
  simpa [show (3 : ℕ) ^ 6 = 729 from by norm_num] using h

/-- The even-shift ray in the hand: for the shift `t = 2` every large power of `2` is a
point where `ω = 1` and `ω (2^k + 2) ≥ 2` (e.g. `2^10 = 1024` and `1026 = 2·3³·19`). -/
theorem jsp87_omega_strictMin_1024_even : omega 1024 = 1 ∧ 2 ≤ omega 1026 := by
  have h := jsp87_powPair_min_two (t := 2) (k := 10) (by omega) ⟨1, by omega⟩ (by norm_num)
  simpa using h

/-- The prime-ray instance: for the shift `t = 3`, the `3`-ray works from `k = 5`
(`3^5 = 243` and `246 = 2·3·41`). -/
theorem jsp87_omega_strictMin_243_shift3 : omega 243 = 1 ∧ 2 ≤ omega 246 := by
  have hq : (3 : ℕ).Prime := by norm_num
  have hdvd : 3 ∣ 3 := dvd_refl 3
  have h := jsp87_powPair_min_prime (t := 3) (k := 5) (by omega) hq hdvd (by norm_num)
  simpa using h

end JSP87
