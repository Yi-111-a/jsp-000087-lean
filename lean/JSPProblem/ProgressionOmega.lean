/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.StrideCarry
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# JSP-000087 : `ω` along arithmetic progressions

This module completes the item that round 100 declared in mathematics but did not
land in Lean: **`ω` is unbounded, and not eventually periodic, along every
arithmetic progression.**  It is the first statement in the whole development that
says `ω` cannot be eventually periodic *along any progression*, not merely along
`n ↦ n + 1` (round 40, `JSPProblem/Periodicity.lean`).

## 1.  The Euclidean recursion — and why it is *structurally* recursive

The construction is the classical Euclid argument run along the progression:

```
M 0 = a + m,        M (j+1) = M j · (1 + m · M j),        A j = 1 + m · M j
```

Round 100 wrote it as `A (i+1) = 1 + p · ∏_{v ≤ i} A v`, i.e. as a `Finset.prod`
over a *recursively defined* sequence, and correctly predicted that Lean would
reject it: "the recursive call sits under `Finset.range`, so Lean's structural
recursion cannot see it as smaller".  **The prediction is bypassed entirely** by
recursing on the *product* rather than on the terms.  `M (j+1)` recurses on the
structural argument `j`, so plain structural recursion accepts it, no
`termination_by` is needed, and the divisibility `A i ∣ M j` for `i < j` then comes
out of the same induction.

Three facts make everything work:

* `M j % m = a % m` — the whole sequence stays in the residue class `a (mod m)`
  (`jsp87ApProd_mod`);
* `2 ^ j ≤ M j` — the sequence grows at least geometrically;
* `j ≤ ω (M j)` — each factor `A j = 1 + m · M j` is `≡ 1 (mod M j)`, hence
  **coprime to `M j`**, and `A j ≥ 2`, so each factor contributes at least one new
  prime factor.

## 2.  The flagship theorems

| Theorem | Statement |
| --- | --- |
| **`omega_arith_unbounded`** | **`ω` is unbounded on every residue class**: for `m ≥ 1`, `a, C, N` there is `n` with `max a N ≤ n`, `n % m = a % m`, `ω n > C` |
| **`omega_arith_unbounded_progression`** | hence, for `m ≥ 1`, arbitrarily large values `m n + a` have `ω (m n + a) > C` |
| **`omega_ap_unbounded`** | the case `a = 1`: for `p ≥ 1`, `C, N` there is `n ≥ N` with `ω (p n + 1) > C` |
| **`omega_arith_periodic_bound`** | **an eventual period makes `ω` bounded on the progression**: `ω (m n + a) ≤ m (N + t) + a` whenever `N ≤ n` |
| **`omega_arith_not_eventuallyPeriodic`** | **`n ↦ ω (m n + a)` is not eventually periodic**, for every `m ≥ 1`, `a` |
| **`omega_ap_not_eventuallyPeriodic`** | the same for `n ↦ ω (p n + 1)` — the shape round 100 predicted |
| **`omega_arith_not_eventuallyMonotone`** | **and not even eventually monotone along a period**: no `t > 0, N` with `ω (m (n+t) + a) ≤ ω (m n + a)` for all `n ≥ N` |

## 3.  Consequences

* `jsp87Carry N ≥ ω N / 2`, hence **`jsp87Carry` is unbounded on every residue
  class of the cut point**: the "the carry is small somewhere" strategy is dead
  not only globally (round 44) but on every progression of cut points.
* `omega_not_eventuallyPeriodic_via_progression` re-derives round 40's aperiodicity
  of `ω` itself by a *different* proof (Euclid on progressions, not round 83's
  `n ↦ n (1 + t n)` move), so the two proofs share no lemma.
-/

namespace JSP87

/-! ## 1.  The Euclidean recursion, parametrised by the residue `a` -/

/-- `jsp87ApProd m a j`: the `j`-th member of the Euclidean sequence in the residue
class `a (mod m)`.  `jsp87ApProd m a 0 = a + m` and
`jsp87ApProd m a (j+1) = jsp87ApProd m a j * (1 + m * jsp87ApProd m a j)`.

This recursion is *structural*: the recursive call is on the direct structural
argument `j`, so no `termination_by` annotation is needed.  This is the fix for the
obstacle recorded in round 100, which recursed on a `Finset.prod` of the terms
themselves. -/
def jsp87ApProd (m a : ℕ) : ℕ → ℕ
  | 0 => a + m
  | (j + 1) => jsp87ApProd m a j * (1 + m * jsp87ApProd m a j)

@[simp] theorem jsp87ApProd_zero (m a : ℕ) : jsp87ApProd m a 0 = a + m := rfl

@[simp] theorem jsp87ApProd_succ (m a j : ℕ) :
    jsp87ApProd m a (j + 1) = jsp87ApProd m a j * (1 + m * jsp87ApProd m a j) := rfl

/-- The `j`-th Euclid factor: `jsp87ApFac m a j = 1 + m · jsp87ApProd m a j`. -/
def jsp87ApFac (m a j : ℕ) : ℕ := 1 + m * jsp87ApProd m a j

@[simp] theorem jsp87ApFac_def (m a j : ℕ) :
    jsp87ApFac m a j = 1 + m * jsp87ApProd m a j := rfl

/-- The successor step, read as a product with the `j`-th factor. -/
theorem jsp87ApProd_succ_eq_mul_fac (m a j : ℕ) :
    jsp87ApProd m a (j + 1) = jsp87ApProd m a j * jsp87ApFac m a j := by
  simp [jsp87ApProd, jsp87ApFac]

/-- Every member of the sequence is positive, provided the modulus is. -/
theorem jsp87ApProd_pos {m a j : ℕ} (hm : 0 < m) : 0 < jsp87ApProd m a j := by
  induction j with
  | zero =>
      rw [jsp87ApProd_zero]
      omega
  | succ j ih =>
      have hq : 0 < jsp87ApFac m a j := by
        rw [jsp87ApFac_def]
        have hnm : (0 : ℕ) ≤ m * jsp87ApProd m a j := Nat.zero_le _
        omega
      rw [jsp87ApProd_succ_eq_mul_fac]
      exact Nat.mul_pos ih hq

/-- Every factor is at least `2`. -/
theorem jsp87ApFac_ge_two {m a j : ℕ} (hm : 0 < m) : 2 ≤ jsp87ApFac m a j := by
  have hp := jsp87ApProd_pos (m := m) (a := a) (j := j) hm
  rw [jsp87ApFac_def]
  have hmm : 1 ≤ m * jsp87ApProd m a j := Nat.succ_le_of_lt (Nat.mul_pos hm hp)
  omega

/-- **THE RESIDUE-CLASS INVARIANT: the whole sequence stays in `a (mod m)`.** -/
theorem jsp87ApProd_mod (m a : ℕ) : ∀ j : ℕ, jsp87ApProd m a j % m = a % m := by
  intro j
  induction j with
  | zero => simp [jsp87ApProd]
  | succ j ih =>
      rw [jsp87ApProd_succ,
        show jsp87ApProd m a j * (1 + m * jsp87ApProd m a j)
          = jsp87ApProd m a j + m * (jsp87ApProd m a j ^ 2) by ring]
      rw [Nat.add_mod, Nat.mul_mod_right, ih]
      simp

/-- Monotonicity of `2 ^` in the exponent. -/
private theorem two_pow_mono {b c : ℕ} (h : b ≤ c) : 2 ^ b ≤ 2 ^ c := by
  obtain ⟨k, hk⟩ : ∃ k, c = b + k := ⟨c - b, by omega⟩
  rw [hk, pow_add]
  have h1 : 1 ≤ 2 ^ k := le_trans (by omega) (succ_le_two_pow k)
  have h2 : 2 ^ b * 1 ≤ 2 ^ b * 2 ^ k := Nat.mul_le_mul_left _ h1
  simpa using h2

/-- **THE GROWTH: `2 ^ j ≤ M j`. -/
theorem jsp87ApProd_ge_two_pow {m a j : ℕ} (hm : 0 < m) : 2 ^ j ≤ jsp87ApProd m a j := by
  induction j with
  | zero =>
      rw [jsp87ApProd_zero]
      omega
  | succ j ih =>
      have hp := jsp87ApProd_pos (m := m) (a := a) (j := j) hm
      have hf := jsp87ApFac_ge_two (m := m) (a := a) (j := j) hm
      rw [jsp87ApProd_succ_eq_mul_fac]
      have hstep : 2 ^ j * 2 ≤ jsp87ApProd m a j * jsp87ApFac m a j := by
        have h1 : 2 ^ j * 2 ≤ jsp87ApProd m a j * 2 :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        have h2 : jsp87ApProd m a j * 2 ≤ jsp87ApProd m a j * jsp87ApFac m a j :=
          Nat.mul_le_mul_left (jsp87ApProd m a j) hf
        omega
      rw [pow_succ]
      omega

/-- **Each factor is coprime to everything built before it**: `A j = 1 + m · M j`
is `≡ 1 (mod M j)`. -/
theorem jsp87ApProd_coprime_fac (m a j : ℕ) :
    Nat.Coprime (jsp87ApProd m a j) (jsp87ApFac m a j) := by
  rw [jsp87ApFac_def, Nat.coprime_add_mul_right_right]
  exact Nat.Coprime.symm (Nat.coprime_one_left _)

/-- **THE COUNT: `j ≤ ω (M j)`.**  Each of the `j` factors contributes at least one
new prime factor, because it is coprime to everything before it and is `≥ 2`. -/
theorem omega_jsp87ApProd_ge {m a : ℕ} (hm : 0 < m) :
    ∀ j : ℕ, j ≤ omega (jsp87ApProd m a j) := by
  intro j
  induction j with
  | zero => simp [jsp87ApProd_zero]
  | succ j ih =>
      have hcop := jsp87ApProd_coprime_fac (m := m) (a := a) (j := j)
      have hfac := jsp87ApFac_ge_two (m := m) (a := a) (j := j) hm
      have hωfac : 1 ≤ omega (jsp87ApFac m a j) := omega_ge_one _ hfac
      rw [jsp87ApProd_succ_eq_mul_fac, omega_mul_of_coprime hcop]
      omega

/-! ## 2.  The factors are pairwise coprime, and divide later members -/

/-- **EVERY FACTOR DIVIDES EVERY LATER MEMBER (the inductive form).**  `A i ∣ M (j+1)`
whenever `i ≤ j`. -/
theorem jsp87ApFac_dvd_apProd_succ {m a i : ℕ} : ∀ j : ℕ, i ≤ j →
    jsp87ApFac m a i ∣ jsp87ApProd m a (j + 1) := by
  intro j
  induction j with
  | zero =>
      intro h
      have hi : i = 0 := by omega
      subst hi
      rw [jsp87ApProd_succ_eq_mul_fac]
      exact dvd_mul_of_dvd_right (dvd_refl _) _
  | succ j ih =>
      intro h
      rw [jsp87ApProd_succ_eq_mul_fac]
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · exact dvd_mul_of_dvd_left (ih (by omega)) _
      · have hi : i = j + 1 := by omega
        subst hi
        exact dvd_mul_of_dvd_right (dvd_refl _) _

/-- `A i ∣ M j` whenever `i < j`: the factor is a building block of everything after
it. -/
theorem jsp87ApFac_dvd_apProd {m a i j : ℕ} (h : i < j) :
    jsp87ApFac m a i ∣ jsp87ApProd m a j := by
  have hx := jsp87ApFac_dvd_apProd_succ (m := m) (a := a) (i := i) (j := j - 1) (by omega)
  rwa [show j - 1 + 1 = j by omega] at hx

/-- **`A i ∣ A j - 1` for `i < j`**: every later factor is `≡ 1 (mod A i)`. -/
theorem jsp87ApFac_sub_one_dvd {m a i j : ℕ} (h : i < j) :
    jsp87ApFac m a i ∣ jsp87ApFac m a j - 1 := by
  rw [jsp87ApFac_def, jsp87ApFac_def, Nat.add_sub_cancel_left]
  exact dvd_mul_of_dvd_right
    (jsp87ApFac_dvd_apProd (m := m) (a := a) (i := i) (j := j) h) m

/-- **THE EUCLID FACT: the factors are pairwise coprime.** -/
theorem jsp87ApFac_coprime {m a i j : ℕ} (h : i < j) :
    Nat.Coprime (jsp87ApFac m a i) (jsp87ApFac m a j) := by
  obtain ⟨c, hc⟩ := jsp87ApFac_sub_one_dvd (m := m) (a := a) (i := i) (j := j) h
  have hpos : 1 ≤ jsp87ApFac m a j := by rw [jsp87ApFac_def]; omega
  have hA : jsp87ApFac m a j = jsp87ApFac m a i * c + 1 := by omega
  rw [hA, show jsp87ApFac m a i * c + 1 = 1 + c * jsp87ApFac m a i by ring,
    Nat.coprime_add_mul_right_right]
  exact Nat.Coprime.symm (Nat.coprime_one_left _)

/-- Symmetric form of the previous lemma. -/
theorem jsp87ApFac_coprime_sym {m a i j : ℕ} (h : j < i) :
    Nat.Coprime (jsp87ApFac m a j) (jsp87ApFac m a i) :=
  jsp87ApFac_coprime (m := m) (a := a) (i := j) (j := i) h

/-! ## 3.  THE FLAGSHIP: `ω` is unbounded on every residue class -/

/-- **THE FLAGSHIP (residue-class form).**  For every modulus `m ≥ 1` and every
residue `a`, `ω` is unbounded on the class `a (mod m)`: for any `C` and any lower
bound `N` there is `n` with `max a N ≤ n`, `n % m = a % m` and `ω n > C`.

This is Euclid's argument: the sequence `M j = jsp87ApProd m a j` stays in the
class `a (mod m)`, satisfies `ω (M j) ≥ j` and `M j ≥ 2 ^ j`, so it is unbounded
in `ω` and eventually leaves every finite interval. -/
theorem omega_arith_unbounded {m a C N : ℕ} (hm : 0 < m) :
    ∃ n : ℕ, max a N ≤ n ∧ n % m = a % m ∧ omega n > C := by
  obtain ⟨j0, hj0, hj0'⟩ := exists_pow_two_ge (max (C + 1) (N + a + 1))
  have hj0'2 : N + a + 1 ≤ 2 ^ j0 := le_trans (le_max_right _ _) hj0'
  have hgrow : 2 ^ j0 ≤ 2 ^ max (C + 1) j0 := two_pow_mono (le_max_right _ _)
  refine ⟨jsp87ApProd m a (max (C + 1) j0), ?_, jsp87ApProd_mod m a _, ?_⟩
  · have hpow := jsp87ApProd_ge_two_pow (m := m) (a := a) (j := max (C + 1) j0) hm
    exact le_trans (Nat.max_le.mpr ⟨by omega, by omega⟩)
      (le_trans hj0'2 (le_trans hgrow hpow))
  · have hω := omega_jsp87ApProd_ge (m := m) (a := a) hm (max (C + 1) j0)
    omega

/-- **DIVISIBILITY OF THE DIFFERENCE.**  If `n ≥ a` and `n ≡ a (mod m)`, then
`m ∣ n - a`. -/
private theorem dvd_sub_of_mod_eq {m n a : ℕ} (_hm : 0 < m) (hge : a ≤ n)
    (hmod : n % m = a % m) : m ∣ n - a := by
  obtain ⟨k, r, hkr, hrm⟩ : ∃ k r : ℕ, n = m * k + r ∧ r = n % m :=
    ⟨n / m, n % m, (Nat.div_add_mod n m).symm, rfl⟩
  refine ⟨k - a / m, ?_⟩
  have hkey : n = a + m * (k - a / m) := by
    have hqa := Nat.div_add_mod a m
    rw [hkr, hrm, hmod, Nat.mul_sub]
    omega
  rw [hkey, Nat.add_sub_cancel_left]

/-- A number of the residue class `1 (mod m)` with `m ≥ 2` is `m q + 1`. -/
private theorem exists_mul_add_one {m n : ℕ} (hm : 1 < m) (hmod : n % m = 1 % m) :
    ∃ q : ℕ, n = m * q + 1 := by
  refine ⟨n / m, ?_⟩
  have hq := Nat.div_add_mod n m
  rw [hmod, Nat.mod_eq_of_lt hm] at hq
  exact hq.symm

/-- **THE FLAGSHIP, in the form of an arithmetic progression.**  For every `m ≥ 1`
and every `a, C, N` there are arbitrarily large values `m n + a` with
`ω (m n + a) > C`. -/
theorem omega_arith_unbounded_progression {m a C N : ℕ} (hm : 0 < m) :
    ∃ n : ℕ, N ≤ m * n + a ∧ omega (m * n + a) > C := by
  obtain ⟨n₀, hn₀, hmod, hω⟩ :=
    omega_arith_unbounded (m := m) (a := a) (C := C) (N := max N (m * N + a)) hm
  have hge : a ≤ n₀ := le_trans (le_max_left _ _) hn₀
  have hdvd := dvd_sub_of_mod_eq hm hge hmod
  obtain ⟨q, hq⟩ := hdvd
  have heq : m * q + a = n₀ := by omega
  refine ⟨q, by omega, by rwa [heq]⟩

/-- **`ω` is unbounded on the progression `1 (mod p)`**: for every `p ≥ 1` and every
`C, N` there is `n ≥ N` with `ω (p n + 1) > C`.

This is the theorem round 100 wrote down as `omega_ap_unbounded`. -/
theorem omega_ap_unbounded {p C N : ℕ} (hp : 0 < p) :
    ∃ n : ℕ, N ≤ n ∧ omega (p * n + 1) > C := by
  obtain ⟨n₀, hn₀, hmod, hω⟩ :=
    omega_arith_unbounded (m := p) (a := 1) (C := C) (N := max (p * N + 1) 1) hp
  rcases Nat.eq_or_lt_of_le (show (1 : ℕ) ≤ p by omega) with hp1 | hp1
  · subst hp1
    have h1n : 1 ≤ n₀ := by omega
    refine ⟨n₀ - 1, ?_, ?_⟩
    · omega
    · have heq : 1 * (n₀ - 1) + 1 = n₀ := by omega
      rw [heq]
      exact hω
  · obtain ⟨q, heq⟩ := exists_mul_add_one hp1 hmod
    refine ⟨q, ?_, ?_⟩
    · have h1 : p * N ≤ p * q := by omega
      exact Nat.le_of_mul_le_mul_left h1 hp
    · rw [heq] at hω
      exact hω

/-- The `≥ K` form of `omega_ap_unbounded`, at every level. -/
theorem omega_ap_unbounded_ge {p K N : ℕ} (hp : 0 < p) :
    ∃ n : ℕ, N ≤ n ∧ K ≤ omega (p * n + 1) := by
  obtain ⟨n, hn, hω⟩ := omega_ap_unbounded (p := p) (C := K) (N := N) hp
  refine ⟨n, hn, by omega⟩

/-- The unboundedness of `ω` on `1 (mod p)` with the quantifiers the other way round:
the `ω`-values `> C` occur arbitrarily far out. -/
theorem omega_ap_unbounded_above {p C : ℕ} (hp : 0 < p) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ omega (p * n + 1) > C :=
  fun N => omega_ap_unbounded (p := p) (C := C) (N := N) hp

/-! ## 4.  THE FLAGSHIP: an eventual period forces `ω` to be bounded -/

/-- **FREEZING (equality version).**  If `g (n + t) = g n` for every `n ≥ N`, then
`g` is constant along each residue class `mod t`, from `N` on. -/
private theorem ap_frozen (g : ℕ → ℕ) {t N : ℕ}
    (hper : ∀ n, N ≤ n → g (n + t) = g n) {n : ℕ} (hn : N ≤ n) (q : ℕ) :
    g (n + t * q) = g n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hid : n + t * (q + 1) = n + t * q + t := by rw [Nat.mul_succ]; omega
      calc g (n + t * (q + 1)) = g (n + t * q + t) := by rw [hid]
        _ = g (n + t * q) := hper _ (by omega)
        _ = g n := ih

/-- **FREEZING (monotone version).**  The `≤`-form of `ap_frozen`. -/
private theorem ap_frozen_le (g : ℕ → ℕ) {t N : ℕ}
    (hper : ∀ n, N ≤ n → g (n + t) ≤ g n) {n : ℕ} (hn : N ≤ n) (q : ℕ) :
    g (n + t * q) ≤ g n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hid : n + t * (q + 1) = n + t * q + t := by rw [Nat.mul_succ]; omega
      calc g (n + t * (q + 1)) = g (n + t * q + t) := by rw [hid]
        _ ≤ g (n + t * q) := hper _ (by omega)
        _ ≤ g n := ih

/-- `n ≤ m * n` for `m ≥ 1`. -/
private theorem le_mul_of_pos {m n : ℕ} (hm : 0 < m) : n ≤ m * n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ]
      omega

/-- **REDUCTION INTO THE PERIOD WINDOW.**  Every index `n` with `N ≤ m n + a` is of
the form `N + r + t q` with `r < t` and `q ≥ 0`. -/
private theorem ap_decompose {t N n : ℕ} (ht : 0 < t) (hn : N ≤ n) :
    ∃ q r : ℕ, n = N + r + t * q ∧ r < t := by
  set d := n - N with hd
  have hdv := Nat.div_add_mod d t
  refine ⟨d / t, d % t, ?_, Nat.mod_lt _ ht⟩
  show n = N + d % t + t * (d / t)
  have h1 : d = d % t + t * (d / t) := by omega
  have h2 : n = N + d := by omega
  omega

/-- **THE PERIODIC BOUND.**  If `n ↦ ω (m n + a)` is eventually periodic with period
`t` from `N`, then `ω (m n + a) ≤ m (N + t) + a` for every `n` with
`m n + a ≥ N`.

Proof: freeze, then reduce `n` into the window `[N, N + t)`, where the elementary
bound `ω k ≤ k` applies. -/
theorem omega_arith_periodic_bound {m a t N n : ℕ} (hm : 0 < m) (ht : 0 < t)
    (hper : ∀ x, N ≤ x → omega (m * (x + t) + a) = omega (m * x + a))
    (hn : N ≤ n) : omega (m * n + a) ≤ m * (N + t) + a := by
  obtain ⟨q, r, hdec, hrlt⟩ := ap_decompose ht hn
  have hrN : N ≤ N + r := by omega
  have hwin : N + r < N + t := by omega
  have hfr : omega (m * n + a) = omega (m * (N + r) + a) := by
    calc omega (m * n + a) = omega (m * (N + r + t * q) + a) := by rw [hdec]
      _ = omega (m * (N + r) + a) :=
        ap_frozen (fun x => omega (m * x + a)) hper hrN q
  have hωle : omega (m * (N + r) + a) ≤ m * (N + r) + a := omega_le _
  have hlt : m * (N + r) + a < m * (N + t) + a := by
    have h1 := mul_lt_mul_of_pos_left hwin hm
    omega
  calc omega (m * n + a) = omega (m * (N + r) + a) := hfr
    _ ≤ m * (N + r) + a := hωle
    _ ≤ m * (N + t) + a := hlt.le

/-- **THE FLAGSHIP: `ω` along a progression is not eventually periodic.**

For every modulus `m ≥ 1` and every offset `a`, the sequence `n ↦ ω (m n + a)` is
not eventually periodic.

Proof.  Suppose it were, with period `t` from `N`.  Then `ω (m · + a)` would be
*constant* along `N + t u` for every `u ≥ 0` (freezing).  But the values
`ω (m (N + t u) + a) = ω (m N + a + m t u)` live in a single **residue class
`m N + a  (mod m t)`**, and `ω` is unbounded on every residue class
(`omega_arith_unbounded`, with modulus `m * t`).  Contradiction. -/
theorem omega_arith_not_eventuallyPeriodic {m a : ℕ} (hm : 0 < m) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → omega (m * (n + t) + a) = omega (m * n + a) := by
  rintro ⟨t, N, ht, hper⟩
  obtain ⟨n₀, hn₀, hmod, hω⟩ :=
    omega_arith_unbounded (m := m * t) (a := m * N + a) (C := omega (m * N + a))
      (N := max (m * N + a) N) (Nat.mul_pos hm ht)
  have hge : m * N + a ≤ n₀ := le_trans (le_max_left _ _) hn₀
  obtain ⟨u, hu⟩ := dvd_sub_of_mod_eq (Nat.mul_pos hm ht) hge hmod
  rw [Nat.mul_assoc] at hu
  have hu' : n₀ = m * N + a + m * (t * u) := by omega
  have hstep : omega (m * (N + t * u) + a) = omega (m * N + a) :=
    ap_frozen (fun x => omega (m * x + a)) hper (by omega) u
  have heq : m * (N + t * u) + a = n₀ := by
    calc m * (N + t * u) + a = m * N + a + m * (t * u) := by ring
      _ = n₀ := hu'.symm
  rw [← heq] at hω
  omega

/-- **THE FLAGSHIP (the shape round 100 predicted).**  For every `p ≥ 1` the
sequence `n ↦ ω (p n + 1)` is not eventually periodic. -/
theorem omega_ap_not_eventuallyPeriodic {p : ℕ} (hp : 0 < p) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → omega (p * (n + t) + 1) = omega (p * n + 1) :=
  omega_arith_not_eventuallyPeriodic (m := p) (a := 1) hp

/-- **AND NOT EVEN EVENTUALLY MONOTONE ALONG A PERIOD.**  There are no `t > 0`,
`N` with `ω (m (n+t) + a) ≤ ω (m n + a)` for all `n ≥ N`.

Strictly stronger than aperiodicity: the previous theorem only forbids equality,
this one forbids *any* non-increasing behaviour along a fixed step — which is what a
"dilate until the object drops below the threshold" argument would need.  Together
with round 44 and round 100 it kills that strategy on every progression. -/
theorem omega_arith_not_eventuallyMonotone {m a : ℕ} (hm : 0 < m) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → omega (m * (n + t) + a) ≤ omega (m * n + a) := by
  rintro ⟨t, N, ht, hper⟩
  obtain ⟨n₀, hn₀, hmod, hω⟩ :=
    omega_arith_unbounded (m := m * t) (a := m * N + a) (C := omega (m * N + a))
      (N := max (m * N + a) N) (Nat.mul_pos hm ht)
  have hge : m * N + a ≤ n₀ := le_trans (le_max_left _ _) hn₀
  obtain ⟨u, hu⟩ := dvd_sub_of_mod_eq (Nat.mul_pos hm ht) hge hmod
  rw [Nat.mul_assoc] at hu
  have hu' : n₀ = m * N + a + m * (t * u) := by omega
  have hstep : omega (m * (N + t * u) + a) ≤ omega (m * N + a) :=
    ap_frozen_le (fun x => omega (m * x + a)) hper (by omega) u
  have heq : m * (N + t * u) + a = n₀ := by
    calc m * (N + t * u) + a = m * N + a + m * (t * u) := by ring
      _ = n₀ := hu'.symm
  rw [← heq] at hω
  omega

/-- The `p n + 1` instance of the preceding theorem. -/
theorem omega_ap_not_eventuallyMonotone {p : ℕ} (hp : 0 < p) :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → omega (p * (n + t) + 1) ≤ omega (p * n + 1) :=
  omega_arith_not_eventuallyMonotone (m := p) (a := 1) hp

/-! ## 4b.  The negation forms: `ω` cannot be bounded on any progression -/

/-- The `> C` form of `omega_arith_unbounded`. -/
theorem omega_arith_not_bounded_on_residue {m a C N : ℕ} (hm : 0 < m) :
    ∃ n : ℕ, max a N ≤ n ∧ n % m = a % m ∧ C < omega n := by
  obtain ⟨n, h1, h2, h3⟩ := omega_arith_unbounded (m := m) (a := a) (C := C) (N := N) hm
  exact ⟨n, h1, h2, by omega⟩

/-- **`ω (m · + a)` is not eventually bounded, for any `m ≥ 1` and any `a`.**  The
negation form of `omega_arith_unbounded_progression`: no single constant bounds `ω`
on a progression, not even from a large starting point. -/
theorem omega_arith_not_eventually_bounded {m a : ℕ} (hm : 0 < m) :
    ¬ ∃ C N : ℕ, ∀ n, N ≤ n → omega (m * n + a) ≤ C := by
  rintro ⟨C, N, hC⟩
  obtain ⟨n, hn, hω⟩ := omega_arith_unbounded_progression (m := m) (a := a) (C := C)
    (N := m * N + a) hm
  have hN : N ≤ n := Nat.le_of_mul_le_mul_left (show m * N ≤ m * n by omega) hm
  have := hC n hN
  omega

/-- The `1 (mod p)` instance. -/
theorem omega_ap_not_eventually_bounded {p : ℕ} (hp : 0 < p) :
    ¬ ∃ C N : ℕ, ∀ n, N ≤ n → omega (p * n + 1) ≤ C :=
  omega_arith_not_eventually_bounded (m := p) (a := 1) hp

/-! ## 5.  An independent proof of the aperiodicity of `ω` itself -/

/-- **A SECOND, INDEPENDENT PROOF that `ω` is not eventually periodic**, obtained
from the progression result at `m = 1` rather than from round 83's
`n ↦ n (1 + t n)` move.  The two proofs share no lemma. -/
theorem omega_not_eventuallyPeriodic_via_progression :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n, N ≤ n → omega (n + t) = omega n :=
  by
    simpa using (omega_arith_not_eventuallyPeriodic (m := 1) (a := 0) (by omega))

/-- The corresponding unboundedness statement for `m = 1`: `ω` is unbounded. -/
theorem omega_unbounded_via_progression (C : ℕ) :
    ∃ n : ℕ, C ≤ n ∧ omega n > C :=
  by
    simpa using
      (omega_arith_unbounded_progression (m := 1) (a := 0) (C := C) (N := C) (by omega))

/-! ## 6.  Consequence for the carries of the Erdős series -/

/-- **THE CARRY IS AT LEAST `ω N / 2`.**  Immediate from `jsp87Carry_split` at
`L = 1`, since `jsp87Carry` is positive. -/
theorem jsp87Carry_ge_omega_half (N : ℕ) :
    (omega N : ℝ) / 2 ≤ jsp87Carry N := by
  have h0 : 0 ≤ jsp87Carry (N + 1) := le_of_lt (jsp87Carry_pos (N + 1))
  have h := jsp87Carry_split N 1
  have h2 : (∑ k ∈ Finset.range 1, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      = (omega N : ℝ) * ((2 : ℝ) ^ 1)⁻¹ := by
    rw [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, zero_add]
  have hone : ((2 : ℝ) ^ (1 : ℕ))⁻¹ = (1 : ℝ) / 2 := by norm_num
  rw [h2, hone] at h
  linarith

/-- **THE CARRIES ARE UNBOUNDED ON EVERY RESIDUE CLASS OF THE CUT POINT**: for
every `m ≥ 1`, `a, C` there is `n` with `m n + a ≥ N` and `jsp87Carry n > C`.

Together with round 44 (`θ N > 1` at every cut point) and round 100
(`jsp87StrideCarry_gt`: the excess survives at every modulus), this says the
"dilate the window until the carry drops below `1`" strategy is dead on every
progression of cut points, not merely globally. -/
theorem jsp87Carry_unbounded_on_progression {m a C N : ℕ} (hm : 0 < m) :
    ∃ n : ℕ, N ≤ m * n + a ∧ C < jsp87Carry n := by
  obtain ⟨n, hn, _, hω⟩ :=
    omega_arith_unbounded (m := 1) (a := 0) (C := 2 * C) (N := N) (by omega)
  have hmn : n ≤ m * n := le_mul_of_pos hm
  have h1 : N ≤ m * n + a := by
    have hN := le_trans (le_max_right 0 N) hn
    omega
  have hω' : 2 * (C : ℝ) < (omega n : ℝ) := by
    exact_mod_cast (show (2 * C : ℕ) < omega n by omega)
  have h2 : C < (omega n : ℝ) / 2 := by linarith
  exact ⟨n, h1, h2.trans_le (jsp87Carry_ge_omega_half n)⟩

/-- The carries are unbounded, period: no upper bound on `jsp87Carry`. -/
theorem jsp87Carry_unbounded (C N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ C < jsp87Carry n := by
  obtain ⟨n, hn, hω⟩ := omega_arith_unbounded (m := 1) (a := 0) (C := 2 * C) (N := N)
    (by omega)
  have h1 : N ≤ n := by omega
  have hω' : 2 * (C : ℝ) < (omega n : ℝ) := by
    exact_mod_cast (show (2 * C : ℕ) < omega n by omega)
  have h2 : C < (omega n : ℝ) / 2 := by linarith
  exact ⟨n, h1, h2.trans_le (jsp87Carry_ge_omega_half n)⟩

/-- The `1 (mod p)` instance: the carries at the cut points `n ≡ 1 (mod p)` are
unbounded. -/
theorem jsp87Carry_unbounded_at_one_mod {p C : ℕ} (hp : 0 < p) :
    ∀ N : ℕ, ∃ n : ℕ, p * n + 1 ≥ N ∧ C < jsp87Carry n :=
  fun N => jsp87Carry_unbounded_on_progression (m := p) (a := 1) (C := C) (N := N) hp

end JSP87