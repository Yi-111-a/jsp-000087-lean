/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-!
# JSP-000087 : the number of distinct prime factors

This file sets up the arithmetic core for JSP-000087, the question of Erdős whether

`∑ n ≥ 1, ω(n) / 2 ^ n`

is irrational, where `ω n` denotes the number of *distinct* prime factors of `n`
(Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 1948;
settled conditionally by K. Pratt, *The irrationality of a prime factor series under
a prime tuples conjecture*, arXiv:2409.15185).

The main object is `omega n = (n.primeFactors).card`. We prove the structural facts
that the analytic argument needs:

* `omega` is monotone under divisibility, and `n.primeFactors` is obtained from
  `(n / p).primeFactors` by inserting one element;
* `omega` is additive on coprime products and submultiplicative in general;
* **the product of the distinct prime factors divides `n`**, hence `2 ^ omega n ≤ n`
  and therefore `omega n ≤ log₂ n` — the growth bound that makes the series
  `∑ ω(n) / 2 ^ n` converge;
* `omega n ≤ n - 1`, the elementary bound used to control tails.
-/

namespace JSP87

/-- `omega n` is the number of distinct prime factors of `n` (Erdős' `ω`-function). -/
def omega (n : ℕ) : ℕ := (n.primeFactors).card

/-- Right cancellation for `Nat` divisibility. -/
theorem div_mul_cancel' {p n : ℕ} (hd : p ∣ n) : n / p * p = n := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' hd]

@[simp] theorem omega_zero : omega 0 = 0 := by simp [omega]

@[simp] theorem omega_one : omega 1 = 0 := by simp [omega]

/-- `ω n = 0` exactly for `n ≤ 1`. -/
theorem omega_eq_zero_iff {n : ℕ} : omega n = 0 ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    have hn1 : n ≠ 1 := by omega
    have hn0 : 0 < n := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hn1
    have hm : p ∈ n.primeFactors := Nat.Prime.mem_primeFactors hp hpd (by omega)
    have hcard : 0 < (n.primeFactors).card := Finset.card_pos.mpr ⟨p, hm⟩
    have h' : (n.primeFactors).card = 0 := by simpa [omega] using h
    omega
  · intro h
    rcases Nat.lt_or_ge n 1 with h' | h'
    · have hn : n = 0 := by omega
      simp [hn]
    · have hn : n = 1 := by omega
      simp [hn]

/-- A prime dividing `n` is counted by `omega`. -/
theorem omega_pos_of_prime_dvd {p n : ℕ} (hp : p.Prime) (hd : p ∣ n) (hn : 0 < n) :
    0 < omega n := by
  have hm : p ∈ n.primeFactors := Nat.Prime.mem_primeFactors hp hd (by omega)
  rw [omega]
  exact Finset.card_pos.mpr ⟨p, hm⟩

/-- Two primes, one dividing the other, are equal. -/
theorem prime_eq_of_prime_dvd {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hqd : q ∣ p) :
    q = p := (Nat.dvd_prime_two_le hp hq.two_le).mp hqd

/-- **Dividing out a prime factor inserts exactly one element** (it may already be
present, in which case the insertion is vacuous). -/
theorem primeFactors_div_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hd : p ∣ n) :
    n.primeFactors = insert p (n / p).primeFactors := by
  have hnp : n / p ≠ 0 := by
    rintro hz
    have h0 : p * 0 = n := by rw [← Nat.mul_div_cancel' hd, hz, Nat.mul_zero]
    exact hn (by simp at h0; omega)
  ext q
  simp only [Finset.mem_insert, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hqd, _⟩
    by_cases hqp : q = p
    · exact Or.inl hqp
    · refine Or.inr ⟨hq, ?_, hnp⟩
      have hqn : q ∣ n / p * p := by rw [div_mul_cancel' hd]; exact hqd
      rcases hq.dvd_mul.mp hqn with h1 | h2
      · exact h1
      · exact absurd h2 (hqp ∘ prime_eq_of_prime_dvd hq hp)
  · intro hx
    rcases hx with hqp | ⟨hq', hqd, _⟩
    · rw [hqp]
      exact ⟨hp, hd, hn⟩
    · refine ⟨hq', ?_, hn⟩
      exact Nat.dvd_trans (dvd_mul_of_dvd_left hqd p)
        (by rw [div_mul_cancel' hd])

/-- `omega` is monotone under divisibility, for `n ≠ 0`. -/
theorem omega_mono {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) : omega m ≤ omega n := by
  have hsub : m.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hmn hn
  simpa [omega] using Finset.card_le_card hsub

/-- `omega` decreases by one when a prime factor that occurs to the first
multiplicity is divided out. -/
theorem omega_div_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hd : p ∣ n)
    (hnd : p ∉ (n / p).primeFactors) : omega (n / p) = omega n - 1 := by
  have hins : n.primeFactors = insert p (n / p).primeFactors :=
    primeFactors_div_prime (by omega) hp hd
  have hcard : (n / p).primeFactors.card + 1 = n.primeFactors.card := by
    rw [hins, Finset.card_insert_of_notMem hnd]
  have hmem : p ∈ n.primeFactors := hp.mem_primeFactors hd (by omega)
  have hpos : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr ⟨p, hmem⟩
  simp only [omega]
  omega

/-- `k + 1 ≤ 2 ^ k` for every natural `k`. -/
theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have h2 : 2 * (k + 1) ≤ 2 * 2 ^ k := mul_le_mul_of_nonneg_left ih (Nat.zero_le 2)
      omega

/-- A prime dividing `p ^ k` (for `k ≥ 1`) divides `p`. -/
theorem prime_dvd_pow_iff {q p : ℕ} (hq : q.Prime) :
    ∀ k : ℕ, 1 ≤ k → (q ∣ p ^ k ↔ q ∣ p) := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (by omega : ¬ (1 ≤ 0))
  | succ k ih =>
      intro hk
      by_cases h1 : k = 0
      · subst h1
        simpa using (Iff.rfl : (q ∣ p) ↔ q ∣ p)
      · rw [pow_succ, hq.dvd_mul]
        have ih' : q ∣ p ^ k ↔ q ∣ p := ih (by omega)
        constructor
        · rintro (h | h)
          · exact ih'.mp h
          · exact h
        · intro h
          exact Or.inr h

/-- `ω` of a positive prime power is one. -/
theorem omega_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : omega (p ^ k) = 1 := by
  have hdvd : p ∣ p ^ k := (show p ∣ p ^ 1 by simp).trans (Nat.pow_dvd_pow p hk)
  have hsub : (p ^ k).primeFactors ⊆ {p} := by
    intro q hq
    obtain ⟨hq', hqd, _⟩ := Nat.mem_primeFactors.mp hq
    exact Finset.mem_singleton.mpr
      (prime_eq_of_prime_dvd hq' hp ((prime_dvd_pow_iff hq' k hk).mp hqd))
  have hsup : {p} ⊆ (p ^ k).primeFactors := by
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    exact hp.mem_primeFactors hdvd (by
      intro hz
      rw [Nat.pow_eq_zero] at hz
      have hpos : 0 < p := lt_trans Nat.zero_lt_one (lt_of_le_of_lt (Nat.le_refl 1) hp.two_le)
      exact absurd hz.1 (Nat.ne_of_gt hpos))
  have heq : (p ^ k).primeFactors = {p} := Finset.Subset.antisymm hsub hsup
  rw [omega, heq]
  simp

/-- `ω` is additive on coprime products. -/
theorem omega_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  by_cases hm : m = 0
  · have hn1 : n = 1 := by
      have := Nat.coprime_iff_gcd_eq_one.mp h
      simp [hm] at this
      omega
    subst hn1
    simp
  by_cases hn : n = 0
  · have hm1 : m = 1 := by
      have := Nat.coprime_iff_gcd_eq_one.mp h
      simp [hn] at this
      omega
    subst hm1
    simp
  have hsub : (m * n).primeFactors ⊆ m.primeFactors ∪ n.primeFactors := by
    intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    rcases hqp.dvd_mul.mp hqd with h1 | h2
    · exact Finset.mem_union_left _ ((Nat.mem_primeFactors_of_ne_zero hm).2 ⟨hqp, h1⟩)
    · exact Finset.mem_union_right _ ((Nat.mem_primeFactors_of_ne_zero hn).2 ⟨hqp, h2⟩)
  have hmn : m.primeFactors ∪ n.primeFactors ⊆ (m * n).primeFactors := by
    intro q hq
    by_cases hq1 : q ∈ m.primeFactors
    · obtain ⟨hq', hqd', _⟩ := Nat.mem_primeFactors.mp hq1
      exact Nat.Prime.mem_primeFactors hq' (dvd_mul_of_dvd_left hqd' n) (mul_ne_zero hm hn)
    · have hq2 : q ∈ n.primeFactors := by simpa [Finset.mem_union, hq1] using hq
      obtain ⟨hq', hqd', _⟩ := Nat.mem_primeFactors.mp hq2
      exact Nat.Prime.mem_primeFactors hq' (by simpa [Nat.mul_comm] using dvd_mul_of_dvd_left hqd' m)
        (mul_ne_zero hm hn)
  have hdisj : Disjoint m.primeFactors n.primeFactors := by
    refine Finset.disjoint_left.2 ?_
    intro q hq1 hq2
    obtain ⟨hq, hqd1, _⟩ := Nat.mem_primeFactors.mp hq1
    obtain ⟨_, hqd2, _⟩ := Nat.mem_primeFactors.mp hq2
    have hgc : Nat.gcd m n = 1 := Nat.coprime_iff_gcd_eq_one.mp h
    have hq1 : q ∣ 1 := Nat.dvd_trans (Nat.dvd_gcd hqd1 hqd2) (by rw [hgc])
    exact hq.ne_one (by simpa using hq1)
  have hcard : (m.primeFactors ∪ n.primeFactors).card = m.primeFactors.card + n.primeFactors.card :=
    Finset.card_union_of_disjoint hdisj
  have hset : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
    Finset.Subset.antisymm hsub hmn
  calc omega (m * n) = (m * n).primeFactors.card := rfl
    _ = (m.primeFactors ∪ n.primeFactors).card := by rw [hset]
    _ = m.primeFactors.card + n.primeFactors.card := Finset.card_union_of_disjoint hdisj
    _ = omega m + omega n := rfl

/-- A finite set of integers `≥ 2` has product at least `2 ^ card`. -/
theorem prod_ge_two_pow_card (s : Finset ℕ) (h : ∀ p ∈ s, 2 ≤ p) :
    2 ^ s.card ≤ (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
      have h' : ∀ p ∈ s, 2 ≤ p := fun p hp => h p (Finset.mem_insert_of_mem hp)
      have hx : 2 * 2 ^ s.card ≤ 2 * (∏ p ∈ s, p) :=
        mul_le_mul_of_nonneg_left (ih h') (by omega : (0:ℕ) ≤ 2)
      have hy : 2 * (∏ p ∈ s, p) ≤ a * (∏ p ∈ s, p) :=
        mul_le_mul_of_nonneg_right (h a (Finset.mem_insert_self a s)) (Nat.zero_le _)
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using le_trans hx hy

/-- **The product of the distinct prime factors of `n` divides `n`.** -/
theorem prod_primeFactors_dvd (n : ℕ) : (∏ p ∈ n.primeFactors, p) ∣ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [hn]
      · by_cases h1 : n = 1
        · simp [h1]
        · obtain ⟨p, hp, hpd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp h1
          have hlt : n / p < n := Nat.div_lt_self (by omega) (by have := hp.two_le; omega)
          have hins : n.primeFactors = insert p (n / p).primeFactors :=
            primeFactors_div_prime hn hp hpd
          have hrec : (∏ p ∈ (n / p).primeFactors, p) ∣ n / p := ih (n / p) hlt
          rw [hins]
          by_cases hmem : p ∈ (n / p).primeFactors
          · rw [Finset.insert_eq_self.mpr hmem]
            have hstep : n / p ∣ n := ⟨p, (div_mul_cancel' hpd).symm⟩
            exact Nat.dvd_trans hrec hstep
          · rw [Finset.prod_insert hmem]
            obtain ⟨c, hc⟩ := hrec
            refine ⟨c, ?_⟩
            calc n = p * (n / p) := (Nat.mul_div_cancel' hpd).symm
              _ = p * ((∏ q ∈ (n / p).primeFactors, q) * c) := by nth_rewrite 1 [hc]; rfl
              _ = (p * (∏ q ∈ (n / p).primeFactors, q)) * c := by rw [Nat.mul_assoc]

/-- **The growth bound `2 ^ omega n ≤ n`** for `n > 0`. -/
theorem two_pow_omega_le {n : ℕ} (hn : 0 < n) : 2 ^ omega n ≤ n := by
  have h1 : 2 ^ n.primeFactors.card ≤ (∏ p ∈ n.primeFactors, p) :=
    prod_ge_two_pow_card _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : (∏ p ∈ n.primeFactors, p) ∣ n := prod_primeFactors_dvd n
  calc 2 ^ omega n = 2 ^ n.primeFactors.card := rfl
    _ ≤ (∏ p ∈ n.primeFactors, p) := h1
    _ ≤ n := Nat.le_of_dvd hn h2

/-- **The logarithmic bound `omega n ≤ log₂ n`.** -/
theorem omega_le_log2 {n : ℕ} (hn : 0 < n) : omega n ≤ Nat.log 2 n := by
  exact Nat.le_log_of_pow_le (b := 2) (x := omega n) (y := n) Nat.one_lt_two
    (two_pow_omega_le hn)

/-- `omega n ≤ n - 1` for `n ≥ 1`. -/
theorem omega_lt {n : ℕ} (hn : 1 ≤ n) : omega n ≤ n - 1 := by
  have hkey : omega n + 1 ≤ 2 ^ omega n := succ_le_two_pow (omega n)
  have h2 := two_pow_omega_le (n := n) (by omega)
  omega

/-- `omega` is submultiplicative. -/
theorem omega_mul_le {m n : ℕ} : omega (m * n) ≤ omega m + omega n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  have hsub : (m * n).primeFactors ⊆ m.primeFactors ∪ n.primeFactors := by
    intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    rcases hqp.dvd_mul.mp hqd with h1 | h2
    · exact Finset.mem_union_left _ ((Nat.mem_primeFactors_of_ne_zero hm).2 ⟨hqp, h1⟩)
    · exact Finset.mem_union_right _ ((Nat.mem_primeFactors_of_ne_zero hn).2 ⟨hqp, h2⟩)
  have hcard : (m * n).primeFactors.card ≤ (m.primeFactors ∪ n.primeFactors).card :=
    Finset.card_le_card hsub
  exact le_trans hcard (by simpa [omega] using Finset.card_union_le _ _)

end JSP87
