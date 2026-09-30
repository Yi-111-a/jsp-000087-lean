/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.PeriodEquation

/-!
# Round 52 -- the modular and `2`-adic arithmetic of the binary prefix

## The gap in the development

Rounds 37-51 attacked the carried Erdős series `S = ∑' n, ω(n) 2^(-(n+1))`
through fifteen different families.  Every one of them lives either in `ℝ`
(carries, tails, asymptotics) or on the *binary digit string* `d N =
⌊2^(N+1) S⌋ - 2 ⌊2^N S⌋`.  **No round ever looked at the integer
`I N = ⌊2^N S⌋ - ⌊θ N⌋` itself** -- the numerator of the `N`-th partial sum,
the integer whose binary expansion *is* the prefix of `S`, and the `2`-adic
integer whose digits are the `ω`-values.

That object is the one place in the tree where the analytic and the arithmetic
sides of the problem meet in the most literal way:

* **recursively**, `I (N+1) = 2 I N + ω N` -- the *same* recursion as the carry
  (`θ (N+1) = 2 θ N - ω N`), with the sign of `ω N` flipped;
* **`2`-adically**, `I N` is the integer whose low bits record the `ω`-values
  with carries, and the `2`-adic valuation of `I N` is *exactly* the amount of
  carrying in the partial sum;
* **modularly**, `I N mod m` is the prefix of `S` seen in the residue ring
  `ℤ/mℤ`, and this round proves the first aperiodicity statement about it.

The driving observation is the **`2`-step `I (N+t) = 2^t I N + Ω N t`**, which
identifies the `2`-adic content of the prefix with the `ω`-window `Ω N t` of
round 51 -- the object a uniform prime-`k`-tuples hypothesis is supposed to
control.  Round 51 related `Ω` to the carry excess and the digit block;
**this round relates it to divisibility**, and gets, unconditionally:

* `jsp87_prefix_mod_not_eventuallyPeriodic`: **THE PREFIX IS APERIODIC MODULO
  EVERY `m ≥ 2`** -- `N ↦ I N mod m` is never eventually periodic.  This is a
  *new* aperiodicity statement about a *new* object (the numerator, not the
  digit string, not the carry excess, not the doubling orbit), and it is
  proved from round 49's aperiodicity of `ω` modulo every `m ≥ 2` together with
  the recursion `I (N+1) = 2 I N + ω N`;
* `jsp87_prefix_dvd_window`: `2^t ∣ I (N+t) ↔ 2^t ∣ Ω N t` -- **THE 2-ADIC
  WINDOW EQUIVALENCE**;
* `jsp87_window_mod_not_eventuallyPeriodic`: the `ω`-window itself is aperiodic
  modulo every `m ≥ 2`;
* `jsp87_adic_carry_congr`: under eventual periodicity of the digit string with
  period `t`, `2^t ∣ I (N+t) ↔ 2^t ∣ (c (N+t) - B N t)` -- **the 2-adic content
  of the binary prefix is read off the carry excess**;
* `jsp87Val2`: the `2`-adic exponent of the numerator, with its exact
  specification, and the sawtooth recursion `v (I (N+1)) = v (I N + ω N / 2) + 1`.

## What this round does NOT do

`jsp_000087_main` remains undeclared.  Aperiodicity of `I N mod m` is *not*
enough: rationality of `S` does not freeze `I N mod m` (the digit identity
`d N = ω N + c (N+1) - 2 c N` mixes the two families, and the round-49 result
`jsp87_noCarry_fails_any_radix` already showed that the carry cannot be removed
in any radix).  Nothing unconditional is known about the distribution of the
`ω`-window modulo `2^t - 1`; that is the arithmetic content of the uniform
prime-`k`-tuples hypothesis in Pratt's result (arXiv:2409.15185), an assumption
of the *published* result and not of the catalog statement.
-/

namespace JSP87

set_option maxHeartbeats 800000

/-! ## 0. The binary prefix, as a natural number -/

/-- **The binary prefix of the Erdős series, as a natural number:**
`I N = ∑_{n<N} ω n · 2^(N-1-n) = ⌊2^N S⌋ - ⌊θ N⌋`.

This is round 41's `jsp87IntPart` (an `ℤ`) read as a `ℕ`; it is nonneg for every
`N` (`jsp87IntPart_nonneg`).  It is the numerator of the `N`-th partial sum, and
its binary expansion is the first `N` digits of `S`. -/
noncomputable def jsp87Prefix (N : ℕ) : ℕ := (jsp87IntPart N).toNat

/-- The prefix vanishes at `N = 0`. -/
theorem jsp87Prefix_zero : jsp87Prefix 0 = 0 := by simp [jsp87Prefix, jsp87IntPart]

/-- **THE PREFIX RECURSION: `I (N+1) = 2 I N + ω N`.**  Round 41's
`jsp87IntPart_succ`, read in `ℕ`.  This is the carry recursion
`θ (N+1) = 2 θ N - ω N` with the sign of `ω N` flipped. -/
theorem jsp87Prefix_succ (N : ℕ) : jsp87Prefix (N + 1) = 2 * jsp87Prefix N + omega N := by
  have h := jsp87IntPart_succ N
  simp only [jsp87Prefix] at ⊢
  rw [← Int.toNat_of_nonneg (jsp87IntPart_nonneg (N + 1)),
    ← Int.toNat_of_nonneg (jsp87IntPart_nonneg N)] at h
  exact_mod_cast h

/-- The prefix, read in `ℝ`, is round 41's integer part. -/
theorem jsp87Prefix_cast (N : ℕ) : (jsp87Prefix N : ℝ) = (jsp87IntPart N : ℝ) := by
  have h : ((jsp87IntPart N).toNat : ℤ) = jsp87IntPart N :=
    Int.toNat_of_nonneg (jsp87IntPart_nonneg N)
  exact_mod_cast h

/-- **THE `t`-STEP PREFIX RECURSION: `I (N+t) = 2^t I N + Ω N t`.**  The
homogeneous form of `jsp87Prefix_succ`; its inhomogeneous term is exactly round
51's `ω`-window. -/
theorem jsp87Prefix_iter (N t : ℕ) :
    jsp87Prefix (N + t) = 2 ^ t * jsp87Prefix N + jsp87OmegaWindow N t := by
  induction t with
  | zero => simp [pow_zero, jsp87OmegaWindow_zero]
  | succ t ih =>
      have hstep := jsp87Prefix_succ (N + t)
      have hw := jsp87OmegaWindow_succ N t
      have hsplit : N + (t + 1) = (N + t) + 1 := by omega
      rw [hsplit, hstep, ih, hw]
      rw [pow_succ]
      ring

/-- **THE 2-ADIC WINDOW EQUIVALENCE: `2^t ∣ I (N+t) ↔ 2^t ∣ Ω N t`.**
The `2`-adic content of the binary prefix of `S` is *exactly* the `2`-adic
content of the `ω`-window ending at `N+t`.  This is the first divisibility
statement in the tree that connects the binary prefix to the inhomogeneous term
of the carry recursion. -/
theorem jsp87Prefix_dvd_window (N t : ℕ) :
    2 ^ t ∣ jsp87Prefix (N + t) ↔ 2 ^ t ∣ jsp87OmegaWindow N t := by
  rw [jsp87Prefix_iter]
  exact (by simpa [Nat.add_comm] using
    Nat.dvd_add_left (Nat.dvd_mul_right (2 ^ t) (jsp87Prefix N)))

/-! ## 1. The `2`-adic exponent of a natural number -/

private theorem one_le_two_pow_nat' (m : ℕ) : 1 ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

private theorem two_le_two_pow_of_pos {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ u =>
      have hh : 1 < 2 ^ Nat.succ u := Nat.one_lt_two_pow (Nat.succ_ne_zero u)
      omega

private theorem two_pow_ge_succ (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

private theorem two_pow_dvd_two_pow (a b : ℕ) : 2 ^ a ∣ 2 ^ (a + b) := by
  rw [pow_add]; rw [Nat.mul_comm]; exact Nat.dvd_mul_left _ _

private theorem two_pow_dvd_two_pow_of_le {a b : ℕ} (hab : a ≤ b) : 2 ^ a ∣ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact two_pow_dvd_two_pow a c

/-- **The `2`-adic exponent of `n`**, i.e. the largest `k` with `2^k ∣ n`
(`0` for `n = 0`, whose valuation is not defined).  Mathlib has no such
function for `ℕ` that is stated in this form. -/
noncomputable def jsp87Val2 (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else Nat.findGreatest (fun k => 2 ^ k ∣ n) (n + 1)

theorem jsp87Val2_zero : jsp87Val2 0 = 0 := by simp [jsp87Val2]

/-- **THE SPECIFICATION OF THE 2-ADIC EXPONENT:** for `n ≠ 0`,
`v (n) = k ↔ 2^k ∣ n ∧ ¬ 2^(k+1) ∣ n`. -/
theorem jsp87Val2_spec {n k : ℕ} (hne : n ≠ 0) :
    jsp87Val2 n = k ↔ 2 ^ k ∣ n ∧ ¬ 2 ^ (k + 1) ∣ n := by
  have hd : jsp87Val2 n = Nat.findGreatest (fun j => 2 ^ j ∣ n) (n + 1) := by
    simp only [jsp87Val2, dite_eq_right hne]
  constructor
  · intro hEq
    have hfg : Nat.findGreatest (fun j => 2 ^ j ∣ n) (n + 1) = k := by
      rw [← hd]; exact hEq
    obtain ⟨hkle, hpk, hjk⟩ := Nat.findGreatest_eq_iff.mp hfg
    have hdiv : 2 ^ k ∣ n := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · exact hpk hk0
    have hkn : k ≤ n := by
      by_cases hk0 : k = 0
      · omega
      · have hle : 2 ^ k ≤ n :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (hpk hk0)
        have hh := two_pow_ge_succ k
        omega
    exact ⟨hdiv, fun hcontra => hjk (n := k + 1) (by omega) (by omega) hcontra⟩
  · intro h
    have hdvd : 2 ^ k ∣ n := h.1
    have hnot : ¬ 2 ^ (k + 1) ∣ n := h.2
    have hfg : Nat.findGreatest (fun j => 2 ^ j ∣ n) (n + 1) = k := by
      rw [Nat.findGreatest_eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · have hn : 0 < n := Nat.pos_of_ne_zero hne
        have hle : 2 ^ k ≤ n := Nat.le_of_dvd hn hdvd
        have hks : k ≤ 2 ^ k := by
          have hh := two_pow_ge_succ k
          omega
        omega
      · by_cases hk0 : k = 0
        · intro hk; exact absurd hk0 hk
        · intro _; exact hdvd
      · intro j hj hjle hjP
        have hdvd2 : 2 ^ (k + 1) ∣ 2 ^ j := two_pow_dvd_two_pow_of_le (by omega)
        exact hnot (hdvd2.trans hjP)
    exact hd.trans hfg

theorem jsp87Val2_dvd {n : ℕ} (hne : n ≠ 0) : 2 ^ jsp87Val2 n ∣ n := by
  have hh := (jsp87Val2_spec hne).mp rfl
  exact hh.1

theorem jsp87Val2_not_succ {n : ℕ} (hne : n ≠ 0) : ¬ 2 ^ (jsp87Val2 n + 1) ∣ n := by
  have hh := (jsp87Val2_spec hne).mp rfl
  exact hh.2

/-- **The `2`-adic exponent of a doubled number.** -/
theorem jsp87Val2_mul_two {X : ℕ} (hX : X ≠ 0) :
    jsp87Val2 (2 * X) = jsp87Val2 X + 1 := by
  have hk := (jsp87Val2_spec hX).mp rfl
  refine (jsp87Val2_spec (by omega)).mpr ⟨?_, ?_⟩
  · have h2 : 2 * 2 ^ jsp87Val2 X ∣ 2 * X :=
      (Nat.mul_dvd_mul_iff_left (a := 2) (by omega)).mpr hk.1
    have hh : 2 ^ (jsp87Val2 X + 1) ∣ 2 * X := by
      simpa [pow_succ, Nat.mul_comm] using h2
    exact hh
  · intro hcontra
    have e : 2 ^ (jsp87Val2 X + 1 + 1) = 2 * 2 ^ (jsp87Val2 X + 1) := by
      rw [pow_succ]; ring
    have h3 : 2 * 2 ^ (jsp87Val2 X + 1) ∣ 2 * X := by
      rw [← e]; exact hcontra
    have h2 : 2 ^ (jsp87Val2 X + 1) ∣ X :=
      (Nat.mul_dvd_mul_iff_left (a := 2) (by omega)).mp h3
    exact hk.2 h2

/-! ## 2. Parity, and the `2`-adic chain -/

/-- **THE PARITY OF THE PREFIX: `I (N+1)` is even exactly when `ω N` is.**
The low bit of the binary prefix is the low bit of `ω N`. -/
theorem jsp87Prefix_parity (N : ℕ) : jsp87Prefix (N + 1) % 2 = omega N % 2 := by
  have h := jsp87Prefix_succ N
  rw [h]
  omega

theorem jsp87Prefix_dvd_two_iff (N : ℕ) : 2 ∣ jsp87Prefix (N + 1) ↔ 2 ∣ omega N := by
  have h := jsp87Prefix_succ N
  have hc : 2 ∣ 2 * jsp87Prefix N := dvd_mul_right 2 (jsp87Prefix N)
  have key : ∀ b : ℕ, 2 ∣ b + 2 * jsp87Prefix N ↔ 2 ∣ b := fun b => Nat.dvd_add_left hc
  rw [h]
  constructor
  · intro hd
    have hd' : 2 ∣ omega N + 2 * jsp87Prefix N := by simpa [Nat.add_comm] using hd
    exact (key _).mp hd'
  · intro hd
    have hd' : 2 ∣ omega N + 2 * jsp87Prefix N := (key _).mpr hd
    simpa [Nat.add_comm] using hd'

/-- **THE 2-ADIC CHAIN.**  For `k ≥ 1` and even `ω N`,
`2^(k+1) ∣ I (N+1) ↔ 2^k ∣ I N + ω N / 2`: the divisibility of the prefix by
`2^k` is a statement about the prefix at `N` *plus half of* `ω N`. -/
theorem jsp87Prefix_dvd_pow_succ (k N : ℕ) (hk : 1 ≤ k) (he : 2 ∣ omega N) :
    2 ^ (k + 1) ∣ jsp87Prefix (N + 1) ↔ 2 ^ k ∣ jsp87Prefix N + omega N / 2 := by
  have hk' : 2 ≤ 2 ^ k := two_le_two_pow_of_pos hk
  obtain ⟨u, hu⟩ := exists_eq_mul_of_dvd (p := 2) (by omega) he
  have hu' : omega N = 2 * u := hu
  have hd : omega N / 2 = u := by rw [hu]; omega
  have hsucc : jsp87Prefix (N + 1) = 2 * (jsp87Prefix N + u) := by
    rw [jsp87Prefix_succ N, hu']
    omega
  have key : 2 ^ (k + 1) ∣ 2 * (jsp87Prefix N + u) ↔ 2 ^ k ∣ jsp87Prefix N + u := by
    have h1 : 2 * 2 ^ k ∣ 2 * (jsp87Prefix N + u) ↔ 2 ^ k ∣ jsp87Prefix N + u :=
      Nat.mul_dvd_mul_iff_left (a := 2) (by omega)
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h2]
    exact h1
  rw [hsucc]
  exact key.trans (by rw [hd])

/-- **The prefix at `N+1` has no `2`-adic content when `ω N` is odd.** -/
theorem jsp87Val2_prefix_succ_odd (N : ℕ) (h : ¬ 2 ∣ omega N) :
    jsp87Val2 (jsp87Prefix (N + 1)) = 0 := by
  have hnot : ¬ 2 ∣ jsp87Prefix (N + 1) := by
    intro hh
    exact h ((jsp87Prefix_dvd_two_iff N).mp hh)
  have hne : jsp87Prefix (N + 1) ≠ 0 := by
    intro hh
    have h1 : 2 ∣ jsp87Prefix (N + 1) := by rw [hh]; exact Nat.dvd_zero 2
    exact hnot h1
  refine (jsp87Val2_spec hne).mpr ⟨?_, ?_⟩
  · rw [Nat.pow_zero]; simp
  · simpa using hnot

/-- **THE 2-ADIC SAWTOOTH.**  If `ω N` is even and the prefix is nonzero, then
doubling the prefix *and* adding half of `ω N` raises the `2`-adic exponent by
exactly one. -/
theorem jsp87Val2_prefix_succ_even (N : ℕ) (he : 2 ∣ omega N)
    (hN : jsp87Prefix N ≠ 0) :
    jsp87Val2 (jsp87Prefix (N + 1)) = jsp87Val2 (jsp87Prefix N + omega N / 2) + 1 := by
  obtain ⟨u, hu⟩ := exists_eq_mul_of_dvd (p := 2) (by omega) he
  have hu' : omega N = 2 * u := hu
  have hd : omega N / 2 = u := by rw [hu]; omega
  have hsucc : jsp87Prefix (N + 1) = 2 * (jsp87Prefix N + u) := by
    rw [jsp87Prefix_succ N, hu']
    omega
  rw [hsucc, hd]
  exact jsp87Val2_mul_two (by omega)

/-! ## 3. APERIODICITY OF THE PREFIX -- THE HEADLINE OF THE ROUND -/

/-- **AN EVENTUAL PERIOD OF THE PREFIX MODULO `m` FORCES THE SAME FOR `ω`.**
The key transfer lemma: `I (n+t) ≡ I n [MOD m]` for all `n ≥ M`, together
with the recursion `I (N+1) = 2 I N + ω N`, gives
`ω (n+t) ≡ ω n [MOD m]` for all `n ≥ M`. -/
theorem jsp87Prefix_periodic_imp_omega_periodic {m t M : ℕ}
    (hp : ∀ n, M ≤ n → jsp87Prefix (n + t) ≡ jsp87Prefix n [MOD m])
    (n : ℕ) (hn : M ≤ n) : omega (n + t) ≡ omega n [MOD m] := by
  have h1 : jsp87Prefix (n + t) ≡ jsp87Prefix n [MOD m] := hp n hn
  have hn1 : M ≤ n + 1 := by omega
  have h2 : jsp87Prefix ((n + 1) + t) ≡ jsp87Prefix (n + 1) [MOD m] := hp (n + 1) hn1
  have h2' : jsp87Prefix ((n + 1) + t) = 2 * jsp87Prefix (n + t) + omega (n + t) := by
    have hh := jsp87Prefix_succ (n + t)
    have he : (n + 1) + t = (n + t) + 1 := by omega
    rw [he, hh]
  have h3 : jsp87Prefix (n + 1) = 2 * jsp87Prefix n + omega n := jsp87Prefix_succ n
  have h4 : 2 * jsp87Prefix (n + t) ≡ 2 * jsp87Prefix n [MOD m] := h1.mul_left 2
  have h5 : 2 * jsp87Prefix (n + t) + omega (n + t) ≡ 2 * jsp87Prefix n + omega n [MOD m] := by
    rw [h2', h3] at h2
    exact h2
  exact Nat.ModEq.add_left_cancel h4 h5

/-- **THE APERIODICITY OF THE BINARY PREFIX, MODULO EVERY `m ≥ 2`.**

The sequence `N ↦ I N mod m` -- the first `N` binary digits of `S`, read as an
element of `ℤ/mℤ` -- is **never eventually periodic**, for any `m ≥ 2`.

This is a new aperiodicity statement about a new object.  Rounds 41, 46, 48, 49
and 50 gave aperiodicity criteria for the digit string `d N`, the digit block,
the doubling orbit `fract (θ N)` and the digit *count* `D N`; the numerator
`I N` itself had never been considered.  The proof is the transfer lemma
`jsp87Prefix_periodic_imp_omega_periodic` followed by round 49's
`omega_mod_not_eventuallyPeriodic`. -/
theorem jsp87_prefix_mod_not_eventuallyPeriodic {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ t M : ℕ, 0 < t ∧ ∀ n : ℕ, M ≤ n → jsp87Prefix (n + t) ≡ jsp87Prefix n [MOD m] := by
  rintro ⟨t, M, ht, hp⟩
  have hop : ∀ n : ℕ, M ≤ n → omega (n + t) ≡ omega n [MOD m] :=
    fun n hn => jsp87Prefix_periodic_imp_omega_periodic hp n hn
  have h1 := omega_mod_not_eventuallyPeriodic (m := m) hm
  refine h1 ⟨t, M, ht, ?_⟩
  intro n hn
  exact hop n hn

/-- **The `2`-power instance: the binary prefix is aperiodic modulo `2^k` for
every `k ≥ 1`. -/
theorem jsp87_prefix_mod_pow_two_not_eventuallyPeriodic {k : ℕ} (hk : 1 ≤ k) :
    ¬ ∃ t M : ℕ, 0 < t ∧
      ∀ n : ℕ, M ≤ n → jsp87Prefix (n + t) ≡ jsp87Prefix n [MOD 2 ^ k] :=
  jsp87_prefix_mod_not_eventuallyPeriodic (two_le_two_pow_of_pos hk)

/-- **THE PREFIX ESCAPES EVERY 2-ADIC WINDOW: the divisibility form of the
headline.**  For every `m ≥ 2`, `t > 0` and `M`, some cut point `n ≥ M` fails
`m ∣ I (n+t) - I n`. -/
theorem jsp87_prefix_dvd_not_eventually {m t M : ℕ} (hm : 2 ≤ m) (ht : 0 < t) :
    ∃ n : ℕ, M ≤ n ∧ ¬ (m ∣ jsp87Prefix (n + t) - jsp87Prefix n) := by
  by_contra hcon
  push Not at hcon
  have hmod : ∀ n : ℕ, M ≤ n → jsp87Prefix (n + t) ≡ jsp87Prefix n [MOD m] := by
    intro n hn
    have hd := hcon n hn
    have hle : jsp87Prefix n ≤ jsp87Prefix (n + t) := by
      rw [jsp87Prefix_iter]
      have h2 : jsp87Prefix n ≤ 2 ^ t * jsp87Prefix n := by
        rcases Nat.eq_zero_or_pos (jsp87Prefix n) with hz | hp
        · omega
        · have h1 : 1 ≤ 2 ^ t := one_le_two_pow_nat' t
          simpa using Nat.mul_le_mul_right (jsp87Prefix n) h1
      omega
    exact Nat.ModEq.symm ((Nat.modEq_iff_dvd' hle).mpr hd)
  have hcontra := jsp87_prefix_mod_not_eventuallyPeriodic (m := m) hm
  exact hcontra (⟨t, M, ht, hmod⟩)

/-- **THE PREFIX IS NEVER EVENTUALLY DIVISIBLE BY `2^k`.**  For every `k ≥ 1`
and every `M` there is a cut point `n ≥ M` at which `2^k ∤ I n`: the binary
prefix escapes every fixed power of `2` infinitely often.  A consequence of the
headline, applied with period `1`. -/
theorem jsp87_prefix_dvd_pow_two_not_eventually {k M : ℕ} (hk : 1 ≤ k) :
    ∃ n : ℕ, M ≤ n ∧ ¬ (2 ^ k ∣ jsp87Prefix n) := by
  by_contra hcon
  push Not at hcon
  have hmain := jsp87_prefix_mod_not_eventuallyPeriodic (m := 2 ^ k) (two_le_two_pow_of_pos hk)
  refine hmain ⟨1, M, Nat.zero_lt_succ 0, ?_⟩
  intro n hn
  have hd : 2 ^ k ∣ jsp87Prefix n := hcon n hn
  have hd' : 2 ^ k ∣ jsp87Prefix (n + 1) := hcon (n + 1) (by omega)
  exact hd'.modEq_zero_nat.trans (hd.modEq_zero_nat).symm

/-- **THE 2-ADIC CHAIN, ONE STEP.**  If `2^(k+1) ∣ I (N+1)` with `k ≥ 1` and
`ω N` even, then `2^k ∣ I N + ω N / 2`.  The consequence form of
`jsp87Prefix_dvd_pow_succ`. -/
theorem jsp87Prefix_dvd_pow_succ' (k N : ℕ) (hk : 1 ≤ k) (he : 2 ∣ omega N)
    (hdiv : 2 ^ (k + 1) ∣ jsp87Prefix (N + 1)) :
    2 ^ k ∣ jsp87Prefix N + omega N / 2 :=
  (jsp87Prefix_dvd_pow_succ k N hk he).mp hdiv

/-! ## 4. The window transfers, and the carry excess reads the 2-adic content -/

private theorem int_dvd_sub_iff_left {a b c : ℤ} (h : a ∣ b) : a ∣ c - b ↔ a ∣ c := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := h
    refine ⟨k + l, ?_⟩
    have e1 : c = (c - b) + b := by ring
    rw [e1, hk, hl]
    ring
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := h
    refine ⟨k - l, ?_⟩
    rw [hk, hl]
    ring

private theorem int_dvd_add_iff_left' {a b c : ℤ} (h : a ∣ b) : a ∣ c + b ↔ a ∣ c := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := h
    refine ⟨k - l, ?_⟩
    have e1 : c = (c + b) - b := by ring
    rw [e1, hk, hl]
    ring
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := h
    refine ⟨k + l, ?_⟩
    rw [hk, hl]
    ring

/-- **AN EVENTUAL PERIOD OF THE PREFIX MODULO `m` FORCES THE SAME FOR THE
`ω`-WINDOW OF LENGTH `t`.**  The converse transfer: modular aperiodicity of the
prefix (`jsp87_prefix_mod_not_eventuallyPeriodic`) transfers to modular
aperiodicity of round 51's `ω`-window. -/
theorem jsp87_window_periodic_of_prefix_periodic {m t M : ℕ}
    (hp : ∀ n, M ≤ n → jsp87Prefix (n + t) ≡ jsp87Prefix n [MOD m]) :
    ∀ n, M ≤ n → jsp87OmegaWindow (n + t) t ≡ jsp87OmegaWindow n t [MOD m] := by
  intro n hn
  have hR := (hp n hn).dvd
  have hQ := (hp (n + t) (by omega)).dvd
  have hq : (jsp87Prefix (n + t) : ℤ) = 2 ^ t * (jsp87Prefix n : ℤ)
      + (jsp87OmegaWindow n t : ℤ) := by exact_mod_cast (jsp87Prefix_iter n t)
  have hr : (jsp87Prefix ((n + t) + t) : ℤ) = 2 ^ t * (jsp87Prefix (n + t) : ℤ)
      + (jsp87OmegaWindow (n + t) t : ℤ) := by
    exact_mod_cast (jsp87Prefix_iter (n + t) t)
  have hid : (jsp87OmegaWindow n t : ℤ) - (jsp87OmegaWindow (n + t) t : ℤ)
      = ((jsp87Prefix n : ℤ) - (jsp87Prefix (n + t) : ℤ)) * (-(2 : ℤ) ^ t)
        - ((jsp87Prefix ((n + t) + t) : ℤ) - (jsp87Prefix (n + t) : ℤ)) := by
    linear_combination (-1 : ℤ) * hq + (1 : ℤ) * hr
  have hdvd1 : (m : ℤ) ∣
      ((jsp87Prefix n : ℤ) - (jsp87Prefix (n + t) : ℤ)) * (2 : ℤ) ^ t :=
    Int.dvd_mul_of_dvd_left hR
  obtain ⟨k1, hk1⟩ := hdvd1
  obtain ⟨k2, hk2⟩ := hQ
  have hdvd : (m : ℤ) ∣ (jsp87OmegaWindow n t : ℤ)
      - (jsp87OmegaWindow (n + t) t : ℤ) := by
    refine ⟨k2 - k1, ?_⟩
    rw [hid]
    linear_combination (1 : ℤ) * hk2 + (-1 : ℤ) * hk1
  exact Nat.modEq_of_dvd hdvd

/-- **THE 2-ADIC WINDOW EQUIVALENCE, IN `ℤ`.**  `(2 : ℤ)^t` divides the prefix
`I (N+t)` exactly when it divides the `ω`-window `Ω N t`. -/
theorem jsp87_adic_window_iff (N t : ℕ) :
    (2 : ℤ) ^ t ∣ (jsp87Prefix (N + t) : ℤ) ↔
      (2 : ℤ) ^ t ∣ (jsp87OmegaWindow N t : ℤ) := by
  constructor
  · intro h
    have h1 : 2 ^ t ∣ jsp87Prefix (N + t) :=
      (Int.natCast_dvd_natCast (m := 2 ^ t) (n := jsp87Prefix (N + t))).mp h
    have h2 : 2 ^ t ∣ jsp87OmegaWindow N t := (jsp87Prefix_dvd_window N t).mp h1
    exact (Int.natCast_dvd_natCast (m := 2 ^ t) (n := jsp87OmegaWindow N t)).mpr h2
  · intro h
    have h1 : 2 ^ t ∣ jsp87OmegaWindow N t :=
      (Int.natCast_dvd_natCast (m := 2 ^ t) (n := jsp87OmegaWindow N t)).mp h
    have h2 : 2 ^ t ∣ jsp87Prefix (N + t) := (jsp87Prefix_dvd_window N t).mpr h1
    exact (Int.natCast_dvd_natCast (m := 2 ^ t) (n := jsp87Prefix (N + t))).mpr h2

/-- **THE 2-ADIC CONTENT OF THE BINARY PREFIX IS READ OFF THE CARRY EXCESS.**
Under eventual periodicity of the digit string with period `t` from `M`,
`2^t ∣ I (N+t) ↔ 2^t ∣ (c (N+t) - B N t)`: the residue of the prefix modulo
`2^t` is exactly the residue of the carry excess minus the period block.

This is the first statement in the tree that reads the `2`-adic content of the
binary prefix off the carry excess; it uses round 51's window-block equation
`c (N+t) + Ω N t = 2^t c N + B N t` together with this round's
`jsp87Prefix_dvd_window`. -/
theorem jsp87_adic_carry_congr {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    (2 : ℤ) ^ t ∣ (jsp87Prefix (N + t) : ℤ) ↔
      (2 : ℤ) ^ t ∣ (jsp87CarryExcess (N + t) - jsp87DigitBlock N t) := by
  have hZ := jsp87_window_block_equation ht hM hN hper
  have h1 : (jsp87OmegaWindow N t : ℤ)
      = (jsp87DigitBlock N t - jsp87CarryExcess (N + t))
        + 2 ^ t * jsp87CarryExcess N := by linarith
  have hc1 : ((2 : ℤ) ^ t) * (jsp87CarryExcess N : ℤ)
      = 2 ^ t * jsp87CarryExcess N := by ring
  have hmul : (2 : ℤ) ^ t ∣ 2 ^ t * jsp87CarryExcess N := by
    have h := dvd_mul_right ((2 : ℤ) ^ t) (jsp87CarryExcess N : ℤ)
    rwa [hc1] at h
  rw [jsp87_adic_window_iff]
  have hb : (2 : ℤ) ^ t ∣ (jsp87OmegaWindow N t : ℤ) ↔
      (2 : ℤ) ^ t ∣ (jsp87CarryExcess (N + t) - jsp87DigitBlock N t) := by
    rw [h1]
    constructor
    · intro h
      have h2 : (2 : ℤ) ^ t ∣
          (jsp87DigitBlock N t - jsp87CarryExcess (N + t)) :=
        (int_dvd_add_iff_left' hmul).mp h
      rw [show (jsp87DigitBlock N t - jsp87CarryExcess (N + t) : ℤ)
        = -((jsp87CarryExcess (N + t) - jsp87DigitBlock N t : ℤ)) from by ring] at h2
      exact dvd_neg.mp h2
    · intro h
      have h3 : (2 : ℤ) ^ t
          ∣ -((jsp87DigitBlock N t - jsp87CarryExcess (N + t) : ℤ)) := by
        have hh := h
        rw [show (jsp87CarryExcess (N + t) - jsp87DigitBlock N t : ℤ)
          = -((jsp87DigitBlock N t - jsp87CarryExcess (N + t) : ℤ)) from by ring] at hh
        exact hh
      exact (int_dvd_add_iff_left' hmul).mpr (dvd_neg.mp h3)
  exact hb
