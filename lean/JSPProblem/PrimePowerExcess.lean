/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Squarefree
import JSPProblem.LambertIdentity
import Mathlib.Tactic

/-!
# JSP-000087 : `Ω` (prime factors counted with multiplicity), the square
# prime-power divisors of `n`, and the excess series

## Why this file exists

Round 102 listed as untouched the object family that the 110-round development had
never built: **the multiplicity function**

```
Ω n = the number of prime factors of n, counted WITH multiplicity
```

the natural companion of `ω n = (n.primeFactors).card`.  (The name `jsp87Omega`
was already taken in `AltSum.lean` for an `ℤ`-valued alias of `ω`, so the new
function is `jsp87OmegaNat`.)  Mathlib supplies the whole arithmetic of `Ω` through
`n.primeFactorsList`, the list of prime factors of `n` *with repetition*, and this
round turns that into a family of objects and a series:

* **`jsp87OmegaNat` arithmetic** — `jsp87OmegaNat (p ^ k) = k` (hence **unbounded**),
  additivity on products, `jsp87OmegaNat n = jsp87OmegaNat (n / p) + 1` for a prime
  `p ∣ n` (no coprimality hypothesis, and none is possible), and the growth bound
  `2 ^ Ω n ≤ n` that makes the series converge;
* **prime powers** — `jsp87PrimePow` (exponent `≥ 1`) and `jsp87SqPow` (exponent
  `≥ 2`) with the classification `jsp87SqPow_iff : d is a square prime power ↔
  d is a prime power that is not prime`, the bounded-search characterisations used
  to make them `Decidable`, and `jsp87_not_primePow_one`;
* **THE SQUARE-PRIME-POWER DIVISOR SET** `jsp87SqPowDivs` (the divisors of `n` that
  are `p ^ a` with `a ≥ 2`), with `jsp87SqPowDivs_eq_filter`, `jsp87SqPowDivs_subset`,
  and the classification **`jsp87SqPowDivs_empty_iff : jsp87SqPowDivs n = ∅ ↔
  Squarefree n`**.  So the *repeated prime factors* of `n` are visible as a
  divisor set, exactly as round 110 made the *distinct* ones visible;
* **`jsp87Omega_eq_omega_iff_sqf`**: `Ω n = ω n ↔ Squarefree n`, the point where the
  multiplicity family meets round 110's squarefree family;
* **the multiplicity series and the excess series** — `jsp87OmegaNatSeries =
  ∑' n, Ω n 2^{-(n+1)}` and `jsp87ExcessSeries = ∑' n, (Ω n − ω n) 2^{-(n+1)}`, with
  `jsp87Series ≤ jsp87OmegaNatSeries`, the **excess decomposition**
  `jsp87OmegaNatSeries = jsp87Series + jsp87ExcessSeries`, and
  `jsp87ExcessSeries_pos` (the place `n = 4` already contributes `1/32`);
* **`jsp87Omega_not_eventuallyPeriodic`** — `Ω` is aperiodic, in one line, because it
  is unbounded (`Ω (2^k) = k`), in sharp contrast with round 101, where the
  aperiodicity of `ω` (which is *bounded* along powers of `2`) required the whole
  progression machinery.

## What it does *not* give

The Erdős series itself is untouched: `jsp87Series` still carries the
aperiodic-digit blocker (`jsp87_digit_not_eventuallyPeriodic`).  The concrete next
step this round opens is the **divisor-COUNT identity** the round was aiming at,
`# {prime-power divisors of n} = Ω n` (the analogue of round 110's
`jsp87SqfDivs_card`), and then its Lambert regrouping

```
∑' n, (Ω n − ω n) 2^-(n+1)  =  ∑' d prime power with exponent ≥ 2, 1 / (2^(d+1) − 2)
```

which would bound the excess in `[1/30, 1/15]`.  The counting argument was
implemented this round but not debugged to completion; the obstacle is recorded in
`policy.json`.
-/

namespace JSP87

open Finset

private lemma pow_le_pow_of_le {a b : ℕ} (h : a ≤ b) (k : ℕ) : a ^ k ≤ b ^ k := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul (ih (by omega)) h

/-- **`2 ≤ 2 ^ (c + 1)`**, the exponent bound used when searching for a prime power. -/
private lemma jsp87_two_pow_succ_le : ∀ c : ℕ, 2 ≤ 2 ^ (c + 1) := by
  intro c
  induction c with
  | zero => simp [pow_succ]
  | succ c ih =>
      rw [pow_succ]
      calc 2 = 1 * 2 := by ring
        _ ≤ (2 ^ (c + 1)) * 2 := Nat.mul_le_mul (by omega) (Nat.le_refl 2)

/-! ## 0. `Ω`, the number of prime factors counted with multiplicity -/

/-- **`Ω n`** counts the prime factors of `n` *with multiplicity* (Erdős' `Ω`),
the companion of `omega n = (n.primeFactors).card`.  Mathlib's
`n.primeFactorsList` is the list of prime factors of `n` with repetition, and
`n.primeFactors = n.primeFactorsList.toFinset`, so `Ω n` is its length. -/
def jsp87OmegaNat (n : ℕ) : ℕ := n.primeFactorsList.length

@[simp] theorem jsp87Omega_zero : jsp87OmegaNat 0 = 0 := by simp [jsp87OmegaNat]

@[simp] theorem jsp87Omega_one : jsp87OmegaNat 1 = 0 := by simp [jsp87OmegaNat]

/-- **`Ω (p ^ k) = k`**: a prime power has exactly `k` prime factors counted with
multiplicity.  (Mathlib: `Nat.Prime.primeFactorsList_pow`.) -/
theorem jsp87Omega_pow {p k : ℕ} (hp : p.Prime) : jsp87OmegaNat (p ^ k) = k := by
  simp [jsp87OmegaNat, hp.primeFactorsList_pow]

/-- **`Ω (2 ^ k) = k`** — the concrete unboundedness witness. -/
theorem jsp87Omega_two_pow (k : ℕ) : jsp87OmegaNat (2 ^ k) = k := jsp87Omega_pow (by norm_num)

/-- **`Ω` is unbounded.**  This is the whole reason `Ω` is aperiodic (§2). -/
theorem jsp87Omega_unbounded {C : ℕ} : ∃ n, C < jsp87OmegaNat n :=
  ⟨2 ^ (C + 1), by rw [jsp87Omega_two_pow]; omega⟩

/-- **`ω n ≤ Ω n`**: a distinct prime factor is counted at least once. -/
theorem omega_le_jsp87Omega (n : ℕ) : omega n ≤ jsp87OmegaNat n := by
  rw [omega, ← Nat.toFinset_factors, jsp87OmegaNat]
  exact List.toFinset_card_le (l := (n.primeFactorsList : List ℕ))

/-- **`Ω` is additive on products**, coprimality not needed: the factors of
`m * n` are those of `m` followed by those of `n`. -/
theorem jsp87Omega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    jsp87OmegaNat (m * n) = jsp87OmegaNat m + jsp87OmegaNat n := by
  rw [jsp87OmegaNat, jsp87OmegaNat, jsp87OmegaNat, ← List.length_append]
  exact (Nat.perm_primeFactorsList_mul hm hn).length_eq

/-- **Dividing out a prime factor removes exactly one prime factor with
multiplicity**: `Ω n = Ω (n / p) + 1`.  No coprimality hypothesis, and none is
possible: for `n = p ^ 2` one has `p ∣ n / p`. -/
theorem jsp87Omega_div_prime {n p : ℕ} (hp : p.Prime) (hpd : p ∣ n) (hn : n ≠ 0) :
    jsp87OmegaNat n = jsp87OmegaNat (n / p) + 1 := by
  have hpp : Nat.primeFactorsList p = [p] := Nat.primeFactorsList_prime hp
  have hnp : n / p ≠ 0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpd) hp.pos)
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpd
  have h1 : List.Perm (p * (n / p)).primeFactorsList
      (p.primeFactorsList ++ (n / p).primeFactorsList) :=
    Nat.perm_primeFactorsList_mul hp.ne_zero hnp
  have h2 : p.primeFactorsList ++ (n / p).primeFactorsList
      = [p] ++ (n / p).primeFactorsList := congrArg (fun l => l ++ (n / p).primeFactorsList) hpp
  have hperm : List.Perm n.primeFactorsList ([p] ++ (n / p).primeFactorsList) :=
    (List.Perm.of_eq (congrArg (fun m => Nat.primeFactorsList m) hmul.symm)).trans
      (h1.trans (List.Perm.of_eq h2))
  simp only [jsp87OmegaNat]
  rw [hperm.length_eq, List.length_append]
  simp only [List.length_cons, List.length_nil]
  omega

private theorem list_prod_ge_two_pow_length {l : List ℕ} (h : ∀ x ∈ l, 2 ≤ x) :
    2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : 2 ≤ a := h a (by simp)
      have hl : ∀ x ∈ l, 2 ≤ x := fun x hx => h x (by simp [hx])
      rw [List.length_cons, List.prod_cons, pow_succ]
      calc 2 ^ l.length * 2 = 2 * 2 ^ l.length := by ring
        _ ≤ 2 * l.prod := mul_le_mul_of_nonneg_left (ih hl) (by norm_num)
        _ ≤ a * l.prod := mul_le_mul_of_nonneg_right ha (Nat.zero_le _)

/-- **`2 ^ Ω n ≤ n`** for `n ≥ 1` — the multiplicity version of round 37's
`2 ^ ω n ≤ n`, and the reason the `Ω`-series converges. -/
theorem two_pow_jsp87Omega_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ jsp87OmegaNat n ≤ n := by
  rw [jsp87OmegaNat]
  have hnn : n ≠ 0 := by omega
  refine (list_prod_ge_two_pow_length fun x hx =>
    (Nat.prime_of_mem_primeFactorsList hx).two_le).trans ?_
  exact Nat.le_of_eq (Nat.prod_primeFactorsList hnn)

/-- **`Ω n ≤ n - 1`** for `n ≥ 2`. -/
theorem jsp87Omega_lt {n : ℕ} (hn : 2 ≤ n) : jsp87OmegaNat n ≤ n - 1 := by
  have h2 : jsp87OmegaNat n + 1 ≤ 2 ^ jsp87OmegaNat n := succ_le_two_pow (jsp87OmegaNat n)
  have h3 := two_pow_jsp87Omega_le (n := n) (by omega)
  have hkey : jsp87OmegaNat n + 1 ≤ n := le_trans h2 h3
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  omega

theorem jsp87Omega_le_self (n : ℕ) : jsp87OmegaNat n ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [jsp87OmegaNat]
  · have h1 := jsp87Omega_lt h
    omega

/-! ## 1. Prime powers, and the prime-power divisor count -/

/-- `d` is a **prime power**: `p ^ a` for a prime `p` and `a ≥ 1`. -/
def jsp87PrimePow (d : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ ∃ a : ℕ, 1 ≤ a ∧ d = p ^ a

/-- `d` is a **square prime power**: `p ^ a` for a prime `p` and `a ≥ 2`. -/
def jsp87SqPow (d : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ ∃ a : ℕ, 2 ≤ a ∧ d = p ^ a

/-- `d` is a **nontrivial power of `p`** (`p ≥ 2`, `a ≥ 1`) — the fixed-base
version used for the divisor counts. -/
def jsp87PPow (p d : ℕ) : Prop := 2 ≤ p ∧ ∃ a : ℕ, 1 ≤ a ∧ d = p ^ a

/-- A prime power that is not prime is a square prime power. -/
theorem jsp87SqPow_of_primePow_of_not_prime {d : ℕ} (h : jsp87PrimePow d) (hn : ¬ d.Prime) :
    jsp87SqPow d := by
  obtain ⟨p, hp, a, ha, hda⟩ := h
  rw [hda] at hn
  refine ⟨p, hp, a, ?_, hda⟩
  by_contra hlt
  have ha1 : a = 1 := by omega
  rw [ha1, pow_one] at hn
  exact hn hp

/-- Every prime power is a square prime power or a prime. -/
theorem jsp87SqPow_or_prime {d : ℕ} (h : jsp87PrimePow d) : jsp87SqPow d ∨ d.Prime := by
  by_cases hp : d.Prime
  · exact Or.inr hp
  · exact Or.inl (jsp87SqPow_of_primePow_of_not_prime h hp)

/-- A square prime power is a prime power and is not prime. -/
theorem jsp87SqPow_iff_primePow_and_not_prime {d : ℕ} (h : jsp87SqPow d) :
    jsp87PrimePow d ∧ ¬ d.Prime := by
  obtain ⟨p, hp, a, ha, hda⟩ := h
  refine ⟨⟨p, hp, a, by omega, hda⟩, ?_⟩
  intro hdp
  have hstep : p ∣ p ^ a :=
    (show p ∣ p ^ 1 by simp).trans (Nat.pow_dvd_pow p (by omega : 1 ≤ a))
  have hdiv : p ∣ d := hda ▸ hstep
  have h1 : p = d := prime_eq_of_prime_dvd hp hdp hdiv
  have h2 : a = 1 := Nat.pow_right_injective hp.two_le
    ((h1.trans hda).symm.trans (pow_one p).symm)
  omega

/-- **`d` is a square prime power exactly when it is a prime power that is not
prime.** -/
theorem jsp87SqPow_iff {d : ℕ} :
    jsp87SqPow d ↔ jsp87PrimePow d ∧ ¬ d.Prime :=
  ⟨jsp87SqPow_iff_primePow_and_not_prime,
   fun h => jsp87SqPow_of_primePow_of_not_prime h.1 h.2⟩

/-- `1` is not a prime power. -/
theorem jsp87_not_primePow_one : ¬ jsp87PrimePow 1 := by
  rintro ⟨p, hp, a, ha, hda⟩
  have hpa : p ∣ p ^ a := (show p ∣ p ^ 1 by simp).trans (Nat.pow_dvd_pow p ha)
  have h1 : p ∣ 1 := by rw [hda]; exact hpa
  have hp1 : p = 1 := Nat.dvd_one.mp h1
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- **`2 ≤ p` and `d = p ^ a` force `a < d + 1`** — the bound that makes the
exponent searchable. -/
private theorem jsp87_exp_lt_succ {p a d : ℕ} (hp2 : 2 ≤ p) (hda : d = p ^ a) : a < d + 1 := by
  have h1 : 2 ^ a ≤ p ^ a := pow_le_pow_of_le hp2 a
  have h2 : a + 1 ≤ 2 ^ a := succ_le_two_pow a
  have h3 : a + 1 ≤ d := by rw [hda]; exact le_trans h2 h1
  exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ a) h3)

private theorem jsp87_pp_pow_lt {p a d : ℕ} (hp2 : 2 ≤ p) (ha : 1 ≤ a) (hda : d = p ^ a) :
    p ≤ d := by
  have h3 : 2 ≤ p ^ a := by
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (c + 1) := jsp87_two_pow_succ_le c
      _ ≤ p ^ (c + 1) := pow_le_pow_of_le hp2 (c + 1)
  rw [hda]
  exact Nat.le_of_dvd (lt_of_lt_of_le (by norm_num) h3)
    ((show p ∣ p ^ 1 by simp).trans (Nat.pow_dvd_pow p ha))

/-- Bounded search for the base and the exponent of a prime power. -/
theorem jsp87PrimePow_mem_search {d : ℕ} (h : jsp87PrimePow d) :
    ∃ p ∈ Finset.range (d + 1), p.Prime ∧ ∃ a ∈ Finset.range (d + 1), 1 ≤ a ∧ d = p ^ a := by
  obtain ⟨p, hp, a, ha, hda⟩ := h
  exact ⟨p, Finset.mem_range.mpr (Nat.lt_succ_of_le (jsp87_pp_pow_lt hp.two_le ha hda)), hp, a,
    Finset.mem_range.mpr (jsp87_exp_lt_succ hp.two_le hda), ha, hda⟩

theorem jsp87PrimePow_iff_search (d : ℕ) :
    jsp87PrimePow d ↔
      ∃ p ∈ Finset.range (d + 1), p.Prime ∧ ∃ a ∈ Finset.range (d + 1), 1 ≤ a ∧ d = p ^ a := by
  constructor
  · exact jsp87PrimePow_mem_search
  · rintro ⟨p, _, hp, a, _, ha, hda⟩
    exact ⟨p, hp, a, ha, hda⟩

theorem jsp87SqPow_iff_search (d : ℕ) :
    jsp87SqPow d ↔
      ∃ p ∈ Finset.range (d + 1), p.Prime ∧ ∃ a ∈ Finset.range (d + 1), 2 ≤ a ∧ d = p ^ a := by
  constructor
  · rintro ⟨p, hp, a, ha, hda⟩
    exact ⟨p, Finset.mem_range.mpr (Nat.lt_succ_of_le
        (jsp87_pp_pow_lt hp.two_le (by omega) hda)), hp, a,
      Finset.mem_range.mpr (jsp87_exp_lt_succ hp.two_le hda), ha, hda⟩
  · rintro ⟨p, _, hp, a, _, ha, hda⟩
    exact ⟨p, hp, a, ha, hda⟩

theorem jsp87PPow_iff_search (p d : ℕ) :
    jsp87PPow p d ↔ 2 ≤ p ∧ ∃ a ∈ Finset.range (d + 1), 1 ≤ a ∧ d = p ^ a := by
  constructor
  · rintro ⟨hp2, a, ha, hda⟩
    exact ⟨hp2, a, Finset.mem_range.mpr (jsp87_exp_lt_succ hp2 hda), ha, hda⟩
  · rintro ⟨hp2, a, har, ha, hda⟩
    exact ⟨hp2, a, ha, hda⟩

noncomputable instance jsp87PrimePowDecidable (d : ℕ) : Decidable (jsp87PrimePow d) :=
  Classical.propDecidable _

noncomputable instance jsp87SqPowDecidable (d : ℕ) : Decidable (jsp87SqPow d) :=
  Classical.propDecidable _

noncomputable instance jsp87PPowDecidable (p d : ℕ) : Decidable (jsp87PPow p d) :=
  Classical.propDecidable _

/-- The **prime-power divisors** of `n`. -/
noncomputable def jsp87PPDivs (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => jsp87PrimePow d)

/-- The **square prime-power divisors** of `n` (exponent at least `2`). -/
noncomputable def jsp87SqPowDivs (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => jsp87SqPow d)

/-- The divisors of `n` that are nontrivial powers of the prime `p`. -/
noncomputable def jsp87PPowDivs (p n : ℕ) : Finset ℕ := n.divisors.filter (fun d => jsp87PPow p d)

/-- The exponents `a` (including `a = 0`) for which `p ^ a ∣ m`. -/
noncomputable def jsp87PowDivs (p m : ℕ) : Finset ℕ := m.divisors.filter (fun a => p ^ a ∣ m)

/-- **THE SQUARE-PRIME-POWER DIVISORS OF `n` ARE EXACTLY ITS NON-PRIME PRIME-POWER
DIVISORS.** -/
theorem jsp87SqPowDivs_eq_filter {n : ℕ} :
    jsp87SqPowDivs n = (jsp87PPDivs n).filter (fun d => ¬ d.Prime) := by
  ext d
  simp only [jsp87SqPowDivs, jsp87PPDivs, Finset.mem_filter]
  rw [jsp87SqPow_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩

/-- Every square prime power of `n` is a prime-power divisor of `n`. -/
theorem jsp87SqPowDivs_subset {n : ℕ} : jsp87SqPowDivs n ⊆ jsp87PPDivs n := by
  rw [jsp87SqPowDivs_eq_filter]
  intro d hd
  exact (Finset.mem_filter.mp hd).1

/-- **`n` is squarefree exactly when it has no square prime-power divisor.** -/
theorem jsp87SqPowDivs_empty_iff {n : ℕ} (hn : 0 < n) :
    jsp87SqPowDivs n = ∅ ↔ Squarefree n := by
  rw [jsp87SqPowDivs, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hq2
    have hmem : q * q ∈ n.divisors := Nat.mem_divisors.mpr ⟨hq2, hn.ne'⟩
    exact h hmem ⟨q, hq, 2, le_rfl, by ring⟩
  · intro h
    intro x hx
    rintro ⟨p, hp, a, ha, hda⟩
    have hdv : x ∣ n ∧ n ≠ 0 := Nat.mem_divisors.mp hx
    rw [hda] at hdv
    have hpa : p ^ a = p * p ^ (a - 1) := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      rw [pow_succ]
      have hsub : c + 1 - 1 = c := by omega
      rw [hsub]
      ring
    have hkey : p * p ∣ n := by
      refine (show p * p ∣ p ^ a from ?_).trans hdv.1
      rw [hpa]
      exact Nat.mul_dvd_mul_left p ((show p ∣ p ^ 1 by simp).trans
        (Nat.pow_dvd_pow p (by omega : (1 : ℕ) ≤ a - 1)))
    exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) hkey

/-- **A NON-SQUAREFREE `n` HAS A SQUARE PRIME-POWER DIVISOR.** -/
theorem jsp87SqPowDivs_ne_empty {n : ℕ} (hn : 0 < n) {h : ¬ Squarefree n} :
    jsp87SqPowDivs n ≠ ∅ := by
  intro hc
  rw [jsp87SqPowDivs_empty_iff hn] at hc
  exact h hc

/-- **`Ω n = ω n` exactly when `n` is squarefree.**  This is where the multiplicity
family and round 110's squarefree family meet: `Ω − ω` vanishes precisely when `n`
has no repeated prime factor. -/
theorem jsp87Omega_eq_omega_iff_sqf {n : ℕ} (hn : 0 < n) :
    jsp87OmegaNat n = omega n ↔ Squarefree n := by
  rw [jsp87OmegaNat, omega, ← Nat.toFinset_factors]
  constructor
  · intro h
    have h1 : ((n.primeFactorsList : Multiset ℕ)).toFinset.card
        = ((n.primeFactorsList : Multiset ℕ)).card := h.symm
    exact (Nat.squarefree_iff_nodup_primeFactorsList hn.ne').mpr
      ((Multiset.toFinset_card_eq_card_iff_nodup).mp h1)
  · intro h
    exact (List.toFinset_card_of_nodup
      ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne').mp h)).symm

/-! ## 1b. The multiplicity series and the *excess* `Ω − ω` -/

/-- The summand of the multiplicity series, the analogue of `jsp87Term`. -/
noncomputable def jsp87OmegaNatTerm (n : ℕ) : ℝ :=
  ((jsp87OmegaNat n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- **`∑' n, Ω n 2^-(n+1)`: the generating series of the multiplicity function.** -/
noncomputable def jsp87OmegaNatSeries : ℝ := ∑' n : ℕ, jsp87OmegaNatTerm n

/-- The summand of the *excess* series `Ω n − ω n`, i.e. of the repeated
prime factors of `n`. -/
noncomputable def jsp87ExcessTerm (n : ℕ) : ℝ :=
  ((jsp87OmegaNat n - omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹

/-- **THE EXCESS SERIES**: `∑' n, (Ω n − ω n) 2^-(n+1)`, the weight carried by the
repeated prime factors of `n`. -/
noncomputable def jsp87ExcessSeries : ℝ := ∑' n : ℕ, jsp87ExcessTerm n

theorem summable_jsp87ExcessTerm :
    Summable (fun n : ℕ => jsp87ExcessTerm n) := by
  unfold jsp87ExcessTerm
  have hle : ∀ n : ℕ, ((jsp87OmegaNat n - omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      ≤ ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    have h1 : (jsp87OmegaNat n - omega n : ℕ) ≤ n := by
      have h2 := jsp87Omega_le_self n
      have h3 := omega_le_jsp87Omega n
      omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (by positivity)
  exact Summable.of_nonneg_of_le (fun n => by positivity) hle summable_nat_mul_two_pow_neg

theorem summable_jsp87OmegaNatTerm :
    Summable (fun n : ℕ => jsp87OmegaNatTerm n) := by
  unfold jsp87OmegaNatTerm
  have hle : ∀ n : ℕ, ((jsp87OmegaNat n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹
      ≤ ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (jsp87Omega_le_self n)) (by positivity)
  exact Summable.of_nonneg_of_le (fun n => by positivity) hle summable_nat_mul_two_pow_neg

/-- **THE MULTIPLICITY SERIES DOMINATES THE ERDŐS SERIES**: `S ≤ ∑' n, Ω n 2^-(n+1)`,
because `ω n ≤ Ω n`. -/
theorem jsp87Series_le_jsp87OmegaNatSeries : jsp87Series ≤ jsp87OmegaNatSeries := by
  have hle : ∀ n : ℕ, jsp87Term n ≤ jsp87OmegaNatTerm n := by
    intro n
    unfold jsp87Term jsp87OmegaNatTerm
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast (omega_le_jsp87Omega n)) (by positivity)
  unfold jsp87OmegaNatSeries
  exact Summable.tsum_le_tsum hle summable_omega_mul_inv_two_pow summable_jsp87OmegaNatTerm

/-- **THE EXCESS DECOMPOSITION: `∑' n, Ω n 2^-(n+1) = S + ∑' n, (Ω n − ω n) 2^-(n+1)`.**

The multiplicity series splits into the Erdős series plus the weight of the
repeated prime factors — the series analogue of `jsp87SqPowDivs`, which says the
excess `Ω n − ω n` counts the square prime-power divisors of `n`. -/
theorem jsp87OmegaNatSeries_eq_add_excess :
    jsp87OmegaNatSeries = jsp87Series + jsp87ExcessSeries := by
  have hsplit : ∀ n : ℕ, jsp87OmegaNatTerm n = jsp87Term n + jsp87ExcessTerm n := by
    intro n
    have h1 : (jsp87OmegaNat n : ℕ) = omega n + (jsp87OmegaNat n - omega n) :=
      (Nat.add_sub_of_le (omega_le_jsp87Omega n)).symm
    have h2 : ((jsp87OmegaNat n : ℕ) : ℝ)
        = ((omega n : ℕ) : ℝ) + ((jsp87OmegaNat n - omega n : ℕ) : ℝ) := by
      exact_mod_cast h1
    unfold jsp87Term jsp87OmegaNatTerm jsp87ExcessTerm
    simp only [two_pow_neg_eq, pow_succ]
    rw [h2]
    ring
  unfold jsp87OmegaNatSeries jsp87ExcessSeries
  rw [tsum_congr fun n => hsplit n]
  exact Summable.tsum_add summable_omega_mul_inv_two_pow summable_jsp87ExcessTerm

theorem jsp87ExcessSeries_nonneg : 0 ≤ jsp87ExcessSeries := by
  unfold jsp87ExcessSeries
  exact tsum_nonneg fun n => by unfold jsp87ExcessTerm; positivity

/-- **`Ω 4 = 2` and `ω 4 = 1`, machine-checked.** -/
theorem jsp87OmegaNat_four : jsp87OmegaNat 4 = 2 := by
  simp [jsp87OmegaNat, show Nat.primeFactorsList 4 = [2, 2] by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, (by norm_num : Nat.Prime (2 : ℕ)).primeFactorsList_pow,
      List.replicate_succ, List.replicate_one]]

theorem omega_four : omega 4 = 1 := by
  have h : Nat.primeFactorsList 4 = [2, 2] := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, (by norm_num : Nat.Prime (2 : ℕ)).primeFactorsList_pow,
      List.replicate_succ, List.replicate_one]
  rw [omega, ← Nat.toFinset_factors, h]
  native_decide

/-- **THE EXCESS IS STRICTLY POSITIVE**: the place `n = 4` (`Ω 4 = 2`, `ω 4 = 1`)
already contributes `2^-(4+1) = 1/32`, and every summand is nonnegative. -/
theorem jsp87ExcessSeries_pos : 0 < jsp87ExcessSeries := by
  have hnonneg : ∀ i, i ∉ Finset.range 5 → 0 ≤ jsp87ExcessTerm i := by
    intro i _
    unfold jsp87ExcessTerm
    positivity
  have hone : jsp87ExcessTerm 4 = 1 / 32 := by
    unfold jsp87ExcessTerm
    rw [jsp87OmegaNat_four, omega_four]
    norm_num
  have hlow : (1 / 32 : ℝ) ≤ jsp87ExcessSeries := by
    refine le_trans (show (1/32:ℝ) ≤ ∑ i ∈ Finset.range 5, jsp87ExcessTerm i from ?_) ?_
    · have hz0 : jsp87ExcessTerm 0 = 0 := by simp [jsp87ExcessTerm]
      have hz1 : jsp87ExcessTerm 1 = 0 := by simp [jsp87ExcessTerm]
      have hz2 : jsp87ExcessTerm 2 = 0 := by
        have h1 : jsp87OmegaNat 2 = 1 := jsp87Omega_two_pow 1
        have h2 : omega 2 = 1 := by native_decide
        unfold jsp87ExcessTerm
        rw [h1, h2]
        norm_num
      have hz3 : jsp87ExcessTerm 3 = 0 := by
        have h3 : jsp87OmegaNat 3 = 1 := by native_decide
        have h3' : omega 3 = 1 := by native_decide
        unfold jsp87ExcessTerm
        rw [h3, h3']
        norm_num
      rw [show (∑ i ∈ Finset.range 5, jsp87ExcessTerm i)
          = jsp87ExcessTerm 0 + jsp87ExcessTerm 1 + jsp87ExcessTerm 2 + jsp87ExcessTerm 3
            + jsp87ExcessTerm 4 from by norm_num [Finset.sum_range_succ],
        hz0, hz1, hz2, hz3, hone]
      norm_num
    · exact Summable.sum_le_tsum (Finset.range 5) hnonneg summable_jsp87ExcessTerm
  linarith

/-! ## 2. `Ω` is aperiodic -/

/-- **An eventual period for `Ω` forces a linear bound.**  If `Ω (n + t) = Ω n` for
all `n ≥ N`, then every value of `Ω` is one of the finitely many values at
`n < N + t`. -/
theorem jsp87Omega_le_of_eventuallyPeriodic {t N : ℕ} (ht : 0 < t)
    (hper : ∀ n : ℕ, N ≤ n → jsp87OmegaNat (n + t) = jsp87OmegaNat n) (n : ℕ) :
    jsp87OmegaNat n ≤ N + t := by
  by_cases hlow : n < N
  · have h1 := jsp87Omega_le_self n
    omega
  set r := N + (n - N) % t with hr
  set m := (n - N) / t with hm
  have hrN : N ≤ r := by simp only [r]; omega
  have hrlt : r < N + t := by
    have hmod : (n - N) % t < t := Nat.mod_lt _ ht
    simp only [r]
    omega
  have hn_eq : n = r + m * t := by
    have hkey : m * t + (n - N) % t = n - N := by
      have h1 := Nat.div_add_mod (n - N) t
      rw [← hm] at h1
      rwa [Nat.mul_comm] at h1
    simp only [r]
    omega
  have hstep : ∀ j : ℕ, jsp87OmegaNat (r + j * t) = jsp87OmegaNat r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h1 : r + (j + 1) * t = (r + j * t) + t := by ring
        rw [h1, hper _ (by omega), ih]
  rw [hn_eq, hstep m]
  have h1 := jsp87Omega_le_self r
  omega

/-- **`Ω` is NOT eventually periodic.**  A one-line consequence of unboundedness:
an eventual period makes a nonnegative `ℕ`-valued function bounded (§above), and
`Ω (2^k) = k` is unbounded.  Compare round 101, where the aperiodicity of `ω`
(which is *bounded* along powers of `2`) needed the whole progression
machinery. -/
theorem jsp87Omega_not_eventuallyPeriodic :
    ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → jsp87OmegaNat (n + t) = jsp87OmegaNat n := by
  rintro ⟨t, N, ht, hper⟩
  have hk := jsp87Omega_le_of_eventuallyPeriodic ht hper (2 ^ (N + t + 1))
  rw [jsp87Omega_two_pow] at hk
  omega

end JSP87