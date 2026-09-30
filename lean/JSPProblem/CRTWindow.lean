/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import Mathlib.Data.Nat.ChineseRemainder
import JSPProblem.Mean

/-!
# JSP-000087 : CRT constructions — the high local minima of `ω`

## Why this file exists

Every one of the twenty-odd previous rounds of this development worked with
**necessary** conditions: what a rational value of

`S = ∑ n ≥ 1, ω(n) / 2 ^ (n+1)`

*would* force (rounds 37–39 Lambert side, 38 and 40 carry side, 41 the digit
bookkeeping, 46 the digit blocks, 47 the primary criterion, 48 the doubling map
on the carries, 49 arbitrary radix, 50–52 asymptotics and the `2`-adic prefix,
55–56 runs and window products, 57 the denominator side, 58 the mean).

The one thing none of them ever did is **construct** anything.  This file
brings the *Chinese remainder theorem* into the development, and with it the
first **existential** results about `ω` and about the carries of the Erdős
series:

* every window length `L` admits a window of `L` **consecutive** integers,
  each of which has at least `k` **distinct** prime factors, for every `k`,
  and arbitrarily far out (`jsp87_window_min_omega_ge`, the flagship);
* consequently the **local minimum** of `ω` over windows is unbounded
  (`jsp87_minWindow_unbounded`), while at every prime every window has local
  minimum exactly `1` (`jsp87_window_min_one_of_prime`): the local minima of
  `ω` oscillate between `1` and arbitrarily large values;
* an eventual period of `ω` would bound those local minima
  (`jsp87_omega_periodic_imp_window_le`), which is a *quantitative*
  aperiodicity obstruction, strictly stronger than round 40's
  `omega_not_eventuallyPeriodic`;
* on such a constructed window the **carries of the series are uniformly
  large**: `θ (N + j) > k/2` for every point of the window
  (`jsp87Carry_gt_half_of_window`), i.e. the carry excess
  `⌊θ N⌋ = jsp87CarryExcess N` stays `≥ ⌊k/2⌋` along an arbitrarily long
  block (`jsp87CarryExcess_window_high`).

## Why the construction stops where it stops — recorded, not hidden

The classical Erdős–Pratt hypothesis is a statement about *exact* patterns of
`ω` on consecutive integers (round 55: `jsp87Series_irrational_of_constRun`).
CRT gives `ω (N + j) ≥ k`, i.e. a **lower bound** on every entry, and can never
give equality, because forcing `ω (N + j) = k` means avoiding *all* other primes
— a prime-`k`-tuples question.  What is proved here is therefore
*complementary* to round 55: the carry is *large* on long blocks, whereas round
55 needs a run on which the carry is *small* (`jsp87CarryExcess_ge_one` of round
44 already shows the carries are `> 1` at every cut point, so the "small carry"
route is closed unconditionally).  Both halves of the CRT construction are
therefore recorded as **negative knowledge for the headline** — see
`jsp_000087_main` in `JSPProblem/Main.lean`, which is still deliberately
withheld.
-/

namespace JSP87

open scoped Function

set_option maxHeartbeats 1000000

/-! ## 0. `k` fresh primes above any bound -/

/-- **There are `k` distinct primes above any bound `P`.**  The list returned is
built by pulling one prime at a time strictly above all the previous ones, so it
is automatically `Nodup`. -/
private lemma jsp87_primes_above : ∀ (k P : ℕ),
    ∃ l : List ℕ, l.length = k ∧ l.Nodup ∧ (∀ p ∈ l, p.Prime) ∧ (∀ p ∈ l, P < p) := by
  intro k
  induction k with
  | zero => intro P; exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    intro P
    obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (P + 1)
    obtain ⟨l, hl, hnd, hpr, hgt⟩ := ih q
    have hqnot : q ∉ l := by
      intro hqin
      have := hgt q hqin
      omega
    refine ⟨q :: l, by simp [hl], List.Nodup.cons hqnot hnd, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hq2
      · exact hpr p hp
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · omega
      · exact lt_trans (show P < q by omega) (hgt p hp)

/-! ## 1. `ω` of a product of distinct primes -/

/-- **`ω` of the product of a finset of distinct primes is the size of the
finset.**  Coprimality is automatic: an inserted prime is not a member of the
finset. -/
private lemma jsp87_prod_primes_omega {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    omega (∏ p ∈ t, (p : ℕ)) = t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [omega]
  | @insert a t ha ih =>
    have hcop : Nat.Coprime (∏ p ∈ t, (p : ℕ)) a := by
      rw [Nat.coprime_prod_left_iff]
      intro b hb
      have hbm : b ∈ insert a t := Finset.mem_insert_of_mem hb
      refine (Nat.Prime.coprime_iff_not_dvd (ht b hbm)).2 ?_
      intro hd
      have hba := prime_eq_of_prime_dvd (ht b hbm) (ht a (Finset.mem_insert_self a t)) hd
      exact ha (hba.symm ▸ hb)
    have hωa : omega (a : ℕ) = 1 := by
      rw [← pow_one (a : ℕ)]
      exact omega_prime_pow (ht a (Finset.mem_insert_self a t)) (by simp)
    rw [Finset.prod_insert ha, omega_mul_of_coprime hcop.symm,
      ih (fun b hb => ht b (Finset.mem_insert_of_mem hb)), hωa,
      Finset.card_insert_of_notMem ha]
    omega

/-- A product of positive integers is positive. -/
private lemma jsp87_prod_primes_pos (t : Finset ℕ) (h : ∀ p ∈ t, 0 < p) :
    0 < ∏ p ∈ t, (p : ℕ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hpos : 0 < a := h a (Finset.mem_insert_self a t)
    rw [Finset.prod_insert ha]
    exact mul_pos hpos (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-! ## 2. Pairwise coprime moduli, each with many prime factors -/

/-- **THE ARITHMETIC CORE OF THE CONSTRUCTION.**  For every `k` and `L` there are
`L` pairwise coprime positive integers, each of which has at least `k`
distinct prime factors.

The moduli are built inductively: at each step a finset of `k` primes strictly
above the product of all previous moduli is taken, and its product is the new
modulus.  A fresh prime `p` above the product `B` of the previous moduli is
larger than each of them, hence divides none of them. -/
private lemma jsp87_coprime_moduli (k L : ℕ) :
    ∃ m : Fin L → ℕ, (∀ j, 0 < m j) ∧ (∀ j, k ≤ omega (m j))
      ∧ (∀ i j : Fin L, i ≠ j → Nat.Coprime (m i) (m j)) := by
  induction L with
  | zero =>
    refine ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun i j => i.elim0⟩
  | succ L ih =>
    obtain ⟨m, hm0, hmω, hmcop⟩ := ih
    classical
    set B : ℕ := ∏ j, m j with hB
    have hBpos : 0 < B := Finset.prod_pos fun j _ => hm0 j
    obtain ⟨l, hl, hnd, hpr, hgt⟩ := jsp87_primes_above k (B + 1)
    set t : Finset ℕ := l.toFinset with ht
    have htcard : t.card = k := by rw [ht, List.toFinset_card_of_nodup hnd, hl]
    have htprime : ∀ p ∈ t, p.Prime := fun p hp => hpr p (List.mem_toFinset.mp hp)
    have htgt : ∀ p ∈ t, B < p := by
      intro p hp
      have h := hgt p (List.mem_toFinset.mp hp)
      omega
    have hBpos' : ∀ j : Fin L, m j ≤ B := by
      intro j
      have hd : m j ∣ B := Finset.dvd_prod_of_mem (s := (Finset.univ : Finset (Fin L)))
        (f := fun _ : Fin L => m _) (a := j) (Finset.mem_univ j)
      exact Nat.le_of_dvd hBpos hd
    have hcop : ∀ (j : Fin L) (p : ℕ) (hp : p ∈ t), Nat.Coprime p (m j) := by
      intro j p hp
      refine (Nat.Prime.coprime_iff_not_dvd (htprime p hp)).2 ?_
      intro hd
      have hle : p ≤ m j := Nat.le_of_dvd (hm0 j) hd
      have hle2 := hBpos' j
      have hgt' := htgt p hp
      omega
    have hrest : ∀ j : Fin L, Nat.Coprime (m j) (∏ p ∈ t, (p : ℕ)) := by
      intro j
      rw [Nat.coprime_prod_right_iff]
      exact fun p hp => (hcop j p hp).symm
    have hrestpos : 0 < ∏ p ∈ t, (p : ℕ) :=
      jsp87_prod_primes_pos t fun p hp => (htprime p hp).pos
    refine ⟨fun j : Fin (L + 1) => if hj : j.val < L then m ⟨j.val, hj⟩ else ∏ p ∈ t, (p : ℕ),
      ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j.val < L
      · simp only [dite_eq_left hj]
        exact hm0 ⟨j.val, hj⟩
      · simp only [dite_eq_right hj]
        exact hrestpos
    · intro j
      by_cases hj : j.val < L
      · simp only [dite_eq_left hj]
        exact hmω ⟨j.val, hj⟩
      · simp only [dite_eq_right hj]
        rw [jsp87_prod_primes_omega htprime]
        omega
    · intro i j hne
      by_cases hi : i.val < L
      · by_cases hj : j.val < L
        · have hne' : (⟨i.val, hi⟩ : Fin L) ≠ ⟨j.val, hj⟩ := by
            intro heq
            have hval : i.val = j.val := congrArg (fun x : Fin L => x.val) heq
            exact hne (Fin.ext hval)
          simp only [dite_eq_left hi, dite_eq_left hj]
          exact hmcop ⟨i.val, hi⟩ ⟨j.val, hj⟩ hne'
        · simp only [dite_eq_left hi, dite_eq_right hj]
          exact hrest ⟨i.val, hi⟩
      · by_cases hj : j.val < L
        · simp only [dite_eq_right hi, dite_eq_left hj]
          exact (hrest ⟨j.val, hj⟩).symm
        · simp only [dite_eq_right hi, dite_eq_right hj]
          exact absurd (Fin.ext (by omega)) hne

/-! ## 3. THE FLAGSHIP: windows whose every entry has many prime factors -/

/-- **THE CONSTRUCTION, WITH AN ARBITRARY LOWER BOUND ON THE POSITION.**

For every `k`, `L` with `1 ≤ L` and every `M` there is a place `N ≥ M` such that
**all** of `N, N+1, …, N+L-1` have at least `k` **distinct** prime factors.

This is the CRT construction: the `L` pairwise coprime moduli of
`jsp87_coprime_moduli` are combined by `Nat.chineseRemainderOfFinset` into a
place `N` with `m j ∣ N + j` for every `j < L`; adding a large multiple of the
product of the moduli pushes `N` past any prescribed `M`. -/
theorem jsp87_window_min_omega_ge_of_ge (k L M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ ∀ j : ℕ, j < L → k ≤ omega (N + j) := by
  classical
  obtain ⟨m, hm0, hmω, hmcop⟩ := jsp87_coprime_moduli k L
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin L)), m i ≠ 0 := fun i _ => (hm0 i).ne'
  have hpp : Set.Pairwise (Finset.univ : Finset (Fin L)) (Nat.Coprime on m) := by
    show ∀ i ∈ (Finset.univ : Finset (Fin L)), ∀ j ∈ (Finset.univ : Finset (Fin L)),
      i ≠ j → Nat.Coprime (m i) (m j)
    intro i _ j _ hne
    exact hmcop i j hne
  set P : ℕ := ∏ i, m i with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hm0 i
  obtain ⟨N0, hN⟩ := Nat.chineseRemainderOfFinset
    (fun i : Fin L => m i * (i.val + 1) - i.val) m (Finset.univ : Finset (Fin L)) hs hpp
  set Q : ℕ := P * (M + 1) with hQ
  have hQ2 : M + 1 ≤ Q := by
    have h2 : 1 ≤ P := by omega
    unfold Q
    exact le_trans (by simp) (Nat.mul_le_mul h2 (le_refl _))
  refine ⟨N0 + Q, by omega, fun j hj => ?_⟩
  set i : Fin L := ⟨j, hj⟩ with hi
  have hival : i.val = j := rfl
  have hdivP : m i ∣ P := Finset.dvd_prod_of_mem (s := (Finset.univ : Finset (Fin L)))
    (f := fun _ : Fin L => m _) (a := i) (Finset.mem_univ i)
  have hdiv : m i ∣ Q := hdivP.mul_right (M + 1)
  have hpos : i.val ≤ m i * (i.val + 1) := by
    have hmi : 1 ≤ m i := by
      have h := hm0 i
      omega
    have h2 : 1 * (i.val + 1) ≤ m i * (i.val + 1) := Nat.mul_le_mul hmi (le_refl _)
    simpa using (show i.val ≤ 1 * (i.val + 1) by simp).trans h2
  set a : ℕ := m i * (i.val + 1) - i.val with ha
  have hZ1 : (m i : ℤ) ∣ (N0 : ℤ) - (a : ℤ) :=
    (Nat.modEq_iff_dvd).mp (Nat.ModEq.symm (hN i (Finset.mem_univ i)))
  have hZ2 : (m i : ℤ) ∣ (Q : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
  have hZ3 : (m i : ℤ) ∣ ((a + i.val : ℕ) : ℤ) := by
    rw [ha, Nat.sub_add_cancel hpos]
    exact Int.natCast_dvd_natCast.mpr ((Nat.dvd_refl (m i)).mul_right (i.val + 1))
  have hEq : ((N0 + Q + j : ℕ) : ℤ) = (N0 : ℤ) - (a : ℤ) + (Q : ℤ) + ((a + i.val : ℕ) : ℤ) := by
    have e1 : ((N0 + Q + j : ℕ) : ℤ) = (N0 : ℤ) + (Q : ℤ) + (j : ℤ) := by
      rw [Nat.cast_add, Nat.cast_add]
    have e2 : ((a + i.val : ℕ) : ℤ) = (a : ℤ) + (i.val : ℤ) := Nat.cast_add ..
    have e3 : (j : ℤ) = (i.val : ℤ) := by rw [← hival]
    rw [e1, e2, e3]
    ring
  have hZ4 : (m i : ℤ) ∣ ((N0 + Q + j : ℕ) : ℤ) := by
    rw [hEq]
    exact hZ1.add hZ2 |>.add hZ3
  have hdvd : m i ∣ N0 + Q + j := Int.natCast_dvd_natCast.mp hZ4
  have hne : N0 + Q + j ≠ 0 := by omega
  exact le_trans (hmω i) (omega_mono hdvd hne)

/-- **THE FLAGSHIP.**  For every `k` and every window length `L ≥ 1` there is a
place `N ≥ 1` at which **every one** of the `L` consecutive integers
`N, …, N+L-1` has at least `k` distinct prime factors. -/
theorem jsp87_window_min_omega_ge (k L : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, j < L → k ≤ omega (N + j) :=
  jsp87_window_min_omega_ge_of_ge k L 1

/-- **A THREE-PRIME WINDOW OF LENGTH `5`.**  There are five consecutive integers,
all of which have at least three distinct prime factors. -/
theorem jsp87_window_min_omega_ge_five_three :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, j < 5 → 3 ≤ omega (N + j) :=
  jsp87_window_min_omega_ge 3 5

/-- **THE WINDOW-SUM FORM.**  The mass of a window
`jsp87WindowOmega N L = ∑ j < L, ω (N + j)` is unbounded above, even when the
window is required to lie beyond any prescribed place.  This is the exact
complement of round 58's uniform lower bound `jsp87OmegaCount L ≤ jsp87WindowOmega N L`. -/
theorem jsp87_windowOmega_ge (k L : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ k * L ≤ jsp87WindowOmega N L := by
  obtain ⟨N, hN, hmin⟩ := jsp87_window_min_omega_ge k L
  refine ⟨N, hN, ?_⟩
  have hsum : k * L ≤ ∑ j ∈ Finset.range L, omega (N + j) := by
    calc k * L = ∑ _i ∈ Finset.range L, k := by simp [Nat.mul_comm]
      _ ≤ ∑ j ∈ Finset.range L, omega (N + j) := by
        refine Finset.sum_le_sum (s := (Finset.range L))
          (f := fun _ : ℕ => k) (g := fun j : ℕ => omega (N + j)) fun j hj => ?_
        rw [Finset.mem_range] at hj
        exact hmin j hj
  have h4 : k * L ≤ jsp87WindowOmega N L := by
    show k * L ≤ ∑ j ∈ Finset.range L, omega (N + j)
    exact hsum
  exact h4

/-- **THE LOCAL MEAN OF `ω` IS UNBOUNDED, WITHIN WINDOWS OF FIXED LENGTH.**
Round 58 proved that it never drops below `∑ p ≤ L, L/p`; this proves that it can
be made arbitrarily large, for every length `L` and beyond every place. -/
theorem jsp87_windowOmega_unbounded (L : ℕ) :
    ∀ K M : ℕ, ∃ N : ℕ, M ≤ N ∧ K * L ≤ jsp87WindowOmega N L := by
  intro K M
  obtain ⟨N, hN, hmin⟩ := jsp87_window_min_omega_ge_of_ge (K + 1) L (max M 2)
  refine ⟨N, by omega, ?_⟩
  have hsum : (K + 1) * L ≤ ∑ j ∈ Finset.range L, omega (N + j) := by
    calc (K + 1) * L = ∑ _i ∈ Finset.range L, (K + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ j ∈ Finset.range L, omega (N + j) := by
        refine Finset.sum_le_sum (s := (Finset.range L))
          (f := fun _ : ℕ => K + 1) (g := fun j : ℕ => omega (N + j)) fun j hj => ?_
        rw [Finset.mem_range] at hj
        exact hmin j hj
  have h2 : (K + 1) * L = K * L + L := by ring
  rw [h2] at hsum
  have h3 : L ≤ ∑ j ∈ Finset.range L, omega (N + j) := by
    calc L = ∑ j ∈ Finset.range L, (1 : ℕ) := by simp
      _ ≤ ∑ j ∈ Finset.range L, omega (N + j) := by
        refine Finset.sum_le_sum (s := (Finset.range L))
          (f := fun _ : ℕ => (1 : ℕ)) (g := fun j : ℕ => omega (N + j)) fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hj2 : 2 ≤ N + j := by omega
        exact omega_ge_one_of_ge_two hj2
  have h4 : K * L + L ≤ jsp87WindowOmega N L := by
    show K * L + L ≤ ∑ j ∈ Finset.range L, omega (N + j)
    exact hsum
  have h3' : L ≤ jsp87WindowOmega N L := by
    show L ≤ ∑ j ∈ Finset.range L, omega (N + j)
    exact h3
  omega

/-! ## 4. The low side: the local minimum `1`, at every prime -/

/-- `ω p = 1` for a prime `p`. -/
theorem jsp87_omega_one_of_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  have h := omega_prime_pow (p := p) (k := 1) hp (by simp)
  simpa using h

/-- **EVERY ENTRY OF A WINDOW STARTING AT A PRIME HAS AT LEAST ONE PRIME
FACTOR.**  So no window beginning at a prime can be a "high minimum" window. -/
theorem jsp87_window_ge_one_of_prime {p L : ℕ} (hp : p.Prime) :
    ∀ j : ℕ, j < L → 1 ≤ omega (p + j) := by
  intro j hj
  have hj2 : 2 ≤ p + j := by
    have : 2 ≤ p := by
      by_contra hc
      have := hp.two_le
      omega
    omega
  exact omega_ge_one_of_ge_two hj2

/-- **AT EVERY PRIME, EVERY WINDOW HAS LOCAL MINIMUM EXACTLY `1`.**  The local
minimum of `ω` over a window is therefore attained at the value `1` at every
prime — the counterpart of `jsp87_window_min_omega_ge`, which makes the local
minimum arbitrarily large. -/
theorem jsp87_window_min_one_of_prime {p L : ℕ} (hp : p.Prime) (hL : 1 ≤ L) :
    ∃ j : ℕ, j < L ∧ omega (p + j) = 1 := by
  refine ⟨0, hL, jsp87_omega_one_of_prime hp⟩

/-- **MACHINE-CHECKED INSTANCE: THE LOCAL MINIMUM OF `ω` IS `1` ON `[3, 6)` AND
`2` AT `6`.**  So no window starting at `3` of length `≥ 4` is a
two-primes-everywhere window, in contrast with `jsp87_window_min_omega_ge`. -/
theorem jsp87_window_min_run3 : omega 3 = 1 ∧ omega 4 = 1 ∧ omega 5 = 1 ∧ omega 6 = 2 := by
  native_decide

/-! ## 5. The oscillation of the local minima, and what periodicity would force -/

/-- **THE LOCAL MINIMA OF `ω` ARE UNBOUNDED.**  For every `K` and every place `M`
there is a window beyond `M` on which **every** entry is `> K`.  In particular
there is no uniform constant bounding the minima of `ω` over windows. -/
theorem jsp87_minWindow_unbounded (K M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ ∃ L : ℕ, 1 ≤ L ∧ ∀ j : ℕ, j < L → K < omega (N + j) := by
  obtain ⟨N, hN, hmin⟩ := jsp87_window_min_omega_ge_of_ge (K + 1) (K + 2) M
  refine ⟨N, hN, K + 2, by omega, fun j hj => ?_⟩
  have := hmin j hj
  omega

/-- **AN EVENTUAL PERIOD OF `ω` BOUNDS THE TAIL.**  If `ω (n + t) = ω n` for all
`n ≥ M` with `t > 0`, then `ω` is bounded on `[M, ∞)` by the largest of the `t`
values `ω M, …, ω (M+t-1)`.  The proof is a strong induction on `n` that strips
off one period at a time. -/
theorem jsp87_omega_periodic_imp_bounded {M t : ℕ} (ht : 0 < t)
    (hper : ∀ n : ℕ, M ≤ n → omega (n + t) = omega n) :
    ∃ K : ℕ, ∀ n : ℕ, M ≤ n → omega n ≤ K := by
  refine ⟨(Finset.range t).sup (fun i => omega (M + i)), fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h0 : n < M + t
    · have hi : n - M < t := by omega
      have hmem : n - M ∈ Finset.range t := Finset.mem_range.2 hi
      have hle : omega (M + (n - M)) ≤ (Finset.range t).sup (fun i => omega (M + i)) :=
        Finset.le_sup (f := fun i => omega (M + i)) hmem
      have heq : n = M + (n - M) := (Nat.add_sub_of_le hn).symm
      rw [heq]
      exact hle
    · have hn' : M ≤ n - t := by omega
      have htn : t ≤ n := by omega
      have h1 : omega (n - t + t) = omega (n - t) := hper (n - t) hn'
      rw [Nat.sub_add_cancel htn] at h1
      have h2 := ih (n - t) (by omega) hn'
      omega

/-- **AN EVENTUAL PERIOD OF `ω` BOUNDS THE LOCAL MINIMA OF `ω`.**  This is a
quantitative version of round 40's `omega_not_eventuallyPeriodic`: the two
statements together say that *no* finite period can describe `ω`, because the
construction of §3 makes the local minima arbitrarily large. -/
theorem jsp87_omega_periodic_imp_window_le {M t : ℕ} (ht : 0 < t)
    (hper : ∀ n : ℕ, M ≤ n → omega (n + t) = omega n) :
    ∃ K : ℕ, ∀ N : ℕ, M ≤ N → ∀ L : ℕ, 1 ≤ L → ∃ j : ℕ, j < L ∧ omega (N + j) ≤ K := by
  obtain ⟨K, hK⟩ := jsp87_omega_periodic_imp_bounded ht hper
  refine ⟨K, fun N hN L hL => ⟨0, hL, hK N hN⟩⟩

/-- **THE TWO-SIDED PICTURE OF THE LOCAL MINIMA OF `ω`.**  No constant can bound
them from above (this file, `jsp87_minWindow_unbounded`), and the value `1` is
attained at every prime (`jsp87_window_min_one_of_prime`).  In particular
`ω` has local minima of every size, and yet the value `1` occurs at every prime —
the sharpest statement about the local minima that the CRT method yields. -/
theorem jsp87_minWindow_dichotomy (K : ℕ) :
    (∃ N : ℕ, 1 ≤ N ∧ ∃ L : ℕ, 1 ≤ L ∧ ∀ j : ℕ, j < L → K < omega (N + j))
      ∧ (∃ p : ℕ, p.Prime ∧ ∃ L : ℕ, 1 ≤ L ∧ ∃ j : ℕ, j < L ∧ omega (p + j) = 1) := by
  have h1 := jsp87_minWindow_unbounded K 1
  have h2 := jsp87_window_min_one_of_prime (p := 3) (L := 1) (by native_decide) (by omega)
  exact ⟨h1, ⟨3, by native_decide, 1, by omega, h2⟩⟩

/-! ## 6. What the construction forces on the carries of the Erdős series -/

/-- **ON A WINDOW WHERE `ω ≥ k` EVERYWHERE, EVERY CARRY IS ABOVE `k/2`.**

The recurrence `θ (N+1) = 2 θ N − ω N` (round 40) together with the positivity
of every carry (`jsp87Carry_pos`) gives `2 θ (N+j) > ω (N+j) ≥ k`, i.e.
`θ (N+j) > k/2`, for every point of the window.  This is the *local* form of
"the carries are large": round 44 proved `θ N > 1` at every single cut point,
this proves the *whole window* is high. -/
theorem jsp87Carry_gt_half_of_window {k L N : ℕ}
    (h : ∀ i : ℕ, i < L → k ≤ omega (N + i)) {j : ℕ} (hj : j < L) :
    (k : ℝ) / 2 < jsp87Carry (N + j) := by
  have hrec := jsp87Carry_succ (N + j)
  have hpos := jsp87Carry_pos (N + j + 1)
  have hk : k ≤ omega (N + j) := h j hj
  have hω : (k : ℝ) ≤ (omega (N + j) : ℝ) := by
    exact_mod_cast hk
  linarith

/-- **The carry at the start of the window.** -/
theorem jsp87Carry_ge_half_of_window {k L N : ℕ} (hL : 1 ≤ L)
    (h : ∀ i : ℕ, i < L → k ≤ omega (N + i)) : (k : ℝ) / 2 ≤ jsp87Carry N := by
  have := jsp87Carry_gt_half_of_window h (j := 0) hL
  simpa using le_of_lt this

/-- **THE CARRY EXCESS IS `≥ ⌊k/2⌋` THROUGHOUT A HIGH WINDOW.**  The carry
excess `jsp87CarryExcess N = ⌊θ N⌋` (round 41) is bounded below by `⌊k/2⌋` at
every point of a window on which `ω ≥ k`. -/
theorem jsp87CarryExcess_ge_of_window {k L N : ℕ}
    (h : ∀ i : ℕ, i < L → k ≤ omega (N + i)) {j : ℕ} (hj : j < L) :
    ((k / 2 : ℕ) : ℤ) ≤ jsp87CarryExcess (N + j) := by
  have hhalf := jsp87Carry_gt_half_of_window h hj
  have hk2 : ((k / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) := by
    have hk := Nat.div_mul_le_self k 2
    exact_mod_cast hk
  have hdiv : ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) / 2 := by
    nlinarith [hk2]
  have hmono : ⌊((k / 2 : ℕ) : ℝ)⌋ ≤ ⌊jsp87Carry (N + j)⌋ :=
    Int.floor_mono (hdiv.trans hhalf.le)
  rw [Int.floor_natCast] at hmono
  exact hmono

/-- **THE CARRY EXCESS CAN BE MADE UNIFORMLY LARGE ON AN ARBITRARILY LONG
BLOCK.**  Combining §3 with the previous lemma: for every `k` and every `L`
there is a place `N ≥ 1` at which the carry excess of the Erdős series does not
drop below `⌊k/2⌋` at any of the `L` successive cut points `N, …, N+L-1`.

Read together with round 41 (`rationality ⟹ the carry excess is not eventually
periodic`) and round 44 (`⌊θ N⌋ ≥ 1` always, `⌊θ N⌋ < ∞`, `ω N < 2⌊θ N⌋ + 2`),
this locates exactly where the CRT method sits: it produces **high** carries on
long blocks, while rationality is contradicted by **small** or **aperiodic**
carries.  Both of those are obstructed (rounds 44, 55), so the construction is
recorded as negative knowledge for the headline rather than as a solution. -/
theorem jsp87CarryExcess_window_high (k L : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, j < L → ((k / 2 : ℕ) : ℤ) ≤ jsp87CarryExcess (N + j) := by
  obtain ⟨N, hN, hmin⟩ := jsp87_window_min_omega_ge k L
  refine ⟨N, hN, fun j hj => jsp87CarryExcess_ge_of_window hmin hj⟩

/-- **THE CARRIES ARE `> 1` ON A WHOLE CONSTRUCTED BLOCK.**  The instance `k = 3`:
there are arbitrarily long blocks of consecutive integers, each with at least
three prime factors, along which every carry of the Erdős series is `> 3/2`. -/
theorem jsp87CarryExcess_window_high_three (L : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, j < L → (1 : ℤ) ≤ jsp87CarryExcess (N + j) :=
  jsp87CarryExcess_window_high 3 L

/-! ## 7. Instances -/

/-- **A TWO-PRIME WINDOW OF LENGTH `4`, AT AN ARBITRARY PLACE.** -/
theorem jsp87_window_min_omega_ge_four_two :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, j < 4 → 2 ≤ omega (N + j) :=
  jsp87_window_min_omega_ge 2 4

/-- **THE WINDOW-SUM INSTANCE: FOUR CONSECUTIVE INTEGERS WITH AT LEAST EIGHT
PRIME FACTORS AMONG THEM.** -/
theorem jsp87_windowOmega_ge_four_two : ∃ N : ℕ, 1 ≤ N ∧ 8 ≤ jsp87WindowOmega N 4 :=
  jsp87_windowOmega_ge 2 4

/-- **THE CARRY-EXCESS INSTANCE FOR `L = 10`.** -/
theorem jsp87CarryExcess_window_high_ten :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j : ℕ, j < 10 → (1 : ℤ) ≤ jsp87CarryExcess (N + j) := by
  exact jsp87CarryExcess_window_high 3 10

/-! ## 8. The two-sided bracket, and the sharpness of the construction -/

/-- **THE LOCAL MEAN OF `ω` OVER A WINDOW OF LENGTH `L` IS BRACKETED ON BOTH
SIDES.**  Round 58 proved the *uniform lower* bound
`jsp87OmegaCount L ≤ jsp87WindowOmega N L` (valid for every position `N`); this
file proves the matching *existential upper* bound: for every `K` there is,
beyond every place, a window of length `L` whose mass is at least `K · L`.  So
the local mean of `ω` is never small, and can be arbitrarily large. -/
theorem jsp87_windowOmega_bracket (N L : ℕ) (hN : 1 ≤ N) (hL : 1 ≤ L) :
    jsp87OmegaCount L ≤ jsp87WindowOmega N L ∧
      ∀ K M : ℕ, ∃ N' : ℕ, M ≤ N' ∧ jsp87OmegaCount L ≤ jsp87WindowOmega N' L
        ∧ K * L ≤ jsp87WindowOmega N' L := by
  refine ⟨jsp87_window_omega_ge_omegaCount hN hL, fun K M => ?_⟩
  obtain ⟨N', hN', hK⟩ := jsp87_windowOmega_unbounded L K (max M 2)
  have hN'1 : 1 ≤ N' := by omega
  exact ⟨N', by omega, jsp87_window_omega_ge_omegaCount hN'1 hL, hK⟩

/-- **AN EVEN INTEGER `≥ 3` WITH EXACTLY ONE PRIME FACTOR IS A MULTIPLE OF `4`.**
So the only even numbers with `ω = 1` that are not divisible by `4` is `2`
itself.  This is the first obstruction to turning the CRT lower bound `ω ≥ k`
into the *constant* runs of round 55. -/
theorem jsp87_omega_one_even_four_dvd {n : ℕ} (h2 : 2 ∣ n) (hn : 3 ≤ n) (hω : omega n = 1) :
    4 ∣ n := by
  have hcard : (n.primeFactors).card = 1 := hω
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have htwo : 2 ∈ n.primeFactors :=
    (by norm_num : Nat.Prime 2).mem_primeFactors h2 (by omega)
  have hmem : 2 ∈ ({a} : Finset ℕ) := by rw [← ha]; exact htwo
  have ha2 : a = 2 := (Finset.mem_singleton.mp hmem).symm
  have hsingle : n.primeFactors = ({2} : Finset ℕ) := by rw [ha, ha2]
  set m : ℕ := n / 2 with hm
  have hmn : m ∣ n := by
    have h := (Nat.dvd_refl m).mul_right 2
    rw [hm, Nat.div_mul_cancel h2] at h
    exact h
  have hsub : m.primeFactors ⊆ n.primeFactors := by
    exact Nat.primeFactors_mono hmn (by omega)
  have hmpf : m.primeFactors ⊆ ({2} : Finset ℕ) := by
    rw [← hsingle]
    exact hsub
  by_cases h4 : 4 ∣ n
  · exact h4
  · exfalso
    have hm2 : ¬ 2 ∣ m := by
      intro h2m
      obtain ⟨t, ht⟩ := h2m
      have hnm : n = 2 * m := by
        symm
        rw [hm, Nat.mul_comm, Nat.div_mul_cancel h2]
      have hnt : n = 4 * t := by rw [hnm, ht]; ring
      have h4t : 4 ∣ n := by rw [hnt]; exact (Nat.dvd_refl 4).mul_right t
      exact absurd h4t h4
    have hnm : n = 2 * m := by
      symm
      rw [hm, Nat.mul_comm, Nat.div_mul_cancel h2]
    by_cases hmle : m ≤ 1
    · have hm2' : 2 ≤ m := by omega
      omega
    · exfalso
      have hm2' : 2 ≤ m := by omega
      have hcard1 : 0 < (m.primeFactors).card := omega_ge_one_of_ge_two hm2'
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hcard1
      have hq2 : q = 2 := Finset.mem_singleton.mp (hmpf hq)
      have hq3 := Nat.mem_primeFactors_of_ne_zero (n := m) (by omega) |>.mp hq
      exact hm2 (hq2 ▸ hq3.2)

/-- **THERE IS NO RUN OF `ω = 1` OF LENGTH `4` PAST `2`.**  A window of four
consecutive integers `≥ 3` contains two even numbers differing by `2`; if both
had `ω = 1` they would both be multiples of `4` (previous lemma), which is
impossible.  Together with `jsp87_window_min_omega_ge` this is the precise reason
the CRT construction cannot be upgraded to round 55's *constant* runs: a
construction can force prime factors into a window, but it cannot keep all the
*other* primes out. -/
theorem jsp87_constRun_one_four_fails {N : ℕ} (hN : 3 ≤ N) : ¬ jsp87ConstRun N 4 1 := by
  intro h
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  by_cases hN2 : 2 ∣ N
  · exfalso
    have h4a : 4 ∣ N := jsp87_omega_one_even_four_dvd hN2 hN h0
    have hone2 : 2 ∣ N + 2 := dvd_add hN2 (Nat.dvd_refl 2)
    have h4b : 4 ∣ N + 2 := jsp87_omega_one_even_four_dvd hone2 (by omega) h2
    omega
  · exfalso
    have hone : 2 ∣ N + 1 := by omega
    have h4a : 4 ∣ N + 1 := jsp87_omega_one_even_four_dvd hone (by omega) h1
    have hone2 : 2 ∣ (N + 1) + 2 := dvd_add hone (Nat.dvd_refl 2)
    have h4b : 4 ∣ (N + 1) + 2 := jsp87_omega_one_even_four_dvd hone2 (by omega) h3
    omega

end JSP87
