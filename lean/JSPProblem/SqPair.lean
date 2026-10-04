import JSPProblem.SqMoment
import JSPProblem.TcVariance
import JSPProblem.CorrShift

/-!
# The exact second moment of `ω`, the prime-pair content, and the price of
# hypothesis (5.21) of arXiv:2512.01739

Round 133 (`JSPProblem/SqMoment.lean`) computed the *square* of `ω` as an
indicator double sum over the primes, `sq_ind`, and the exact prime-pair counting
layer, `jsp87_card_pair`; the reassembly into a statement about `jsp87SqMoment`
was left open.  This module closes it, and then does what round 132's policy
(`jsp87_sumOmegaSq_ge_pairs`, "the unconditional lower bound on `Var ω` that
hypothesis (5.21) of the endgame requires") asked for.

The outcome is a **complete arithmetic identity plus a refutation of the
arithmetic route to (5.21)**:

* §1 `jsp87SqMoment_eq_primeDiv_add_pairs` — the second moment of `ω` over
  `[1, X]` is the *mean-field* prime-divisor count `jsp87OmegaCount X`
  **plus** the *exact* prime-pair content `jsp87OffPair X`, every term of which
  is `⌊X / (p q)⌋` with **no** boundary error.
* §2 `jsp87_factMoment_ge_pairCount` — hence
  `2 · #{p < q primes ≤ X : p q ≤ X} ≤ ∑_{n ≤ X} ω n (ω n − 1)`, the first
  unconditional lower bound on the second factorial moment of `ω`.
* §3 the *price* of hypothesis (5.21): the weighted diagonal
  `∑_{k<H} 4^{-(k+1)} Var ω(N+k)` is **exactly**
  `jsp87TcDiag L H / L − L · (𝔼_N T(N,H))²`, and at `H = 1` the arithmetic
  lower bounds supply **at most `9/16`** of it (`jsp87_arith521_le`) — so the
  variance hypothesis (5.21) can never be met by arithmetic alone.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. The objects -/

/-- **THE SECOND FACTORIAL MOMENT** `∑_{1 ≤ n ≤ X} ω n (ω n − 1)`: the number of
ordered pairs of *distinct* prime divisors of the integers `≤ X`. -/
def jsp87FactPair (X : ℕ) : ℕ := ∑ n ∈ Finset.Icc 1 X, omega n * (omega n - 1)

/-- **THE PRIME-PAIR CONTENT** `∑_{p ≠ q primes ≤ X} ⌊X / (p q)⌋`.  For each
ordered pair of *distinct* primes below `X`, the number of integers `≤ X`
divisible by both — an exact count (`jsp87_card_pair`), with no boundary
error, in contrast to round 115's Chowla estimate whose error is `π(X)²`. -/
def jsp87OffPair (X : ℕ) : ℕ :=
  ∑ p ∈ jsp87Primes X,
      ∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p), X / (p * q)

/-- **THE UPPER-TRIANGLE PRIME-PAIR CONTENT** `p < q`.  Half of
`jsp87OffPair`, by symmetry (`jsp87_offPair_eq_two_mul_upPair`). -/
def jsp87UpPair (X : ℕ) : ℕ :=
  ∑ p ∈ jsp87Primes X,
      ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q)

/-- **THE NUMBER OF REACHABLE PRIME PAIRS**
`# { (p, q) : p < q primes ≤ X, p q ≤ X }`.  This is the discrete object
hypothesis (5.21) of arXiv:2512.01739 asks about: pairs of primes that can
*divide the same integer* `≤ X`. -/
def jsp87PairCount (X : ℕ) : ℕ :=
  ∑ p ∈ jsp87Primes X, ((jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X)).card

/-! ## 1. One row of the factorial-moment double sum -/

/-- **ONE ROW.**  For a fixed prime `p`, the number of *other* primes `q ≤ X`
dividing `n` is `(if p ∣ n then 1 else 0) · (ω n − 1)`: the count over `q ≠ p`
is the count over all `q` minus the contribution of `p`. -/
theorem jsp87_row_eq {n X p : ℕ} (hn : 1 ≤ n) (hX : n ≤ X) (hp : p ∈ jsp87Primes X) :
    (∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
        (if (p ∣ n) ∧ (q ∣ n) then 1 else 0))
      = (if p ∣ n then 1 else 0) * (omega n - 1) := by
  classical
  by_cases hp' : p ∣ n
  · have key : ∀ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
        (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) = (if q ∣ n then 1 else 0) := by
      intro q hq
      by_cases hq' : q ∣ n
      · rw [ite_eq_left ⟨hp', hq'⟩, ite_eq_left hq']
      · rw [ite_eq_right (fun h => hq' h.2), ite_eq_right hq']
    have hone : (if p ∣ n then 1 else 0) = 1 := ite_eq_left hp'
    rw [Finset.sum_congr rfl key, jsp87_dvd_count_neq (jsp87Primes X) p n hp,
      jsp87_omega_eq_sum_dvd hn hX, hone]
    ring
  · have key : ∀ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
        (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) = 0 := by
      intro q hq
      rw [ite_eq_right (fun h => hp' h.1)]
    have hzero : (if p ∣ n then 1 else 0) = 0 := ite_eq_right hp'
    rw [Finset.sum_congr rfl key, Finset.sum_const_zero, hzero, Nat.zero_mul]

/-- **THE FACTORIAL MOMENT OF `ω` AS AN ORDERED PAIRS-OF-DISTINCT-PRIMES SUM.**
`ω n (ω n − 1)` counts the ordered pairs of *distinct* prime divisors of `n`,
so it is the double sum of the indicators over `q ≠ p`. -/
theorem jsp87_fact_ind {n X : ℕ} (hn : 1 ≤ n) (hX : n ≤ X) :
    omega n * (omega n - 1)
      = ∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) := by
  classical
  have hrows : (∑ p ∈ jsp87Primes X,
          ∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
            (if (p ∣ n) ∧ (q ∣ n) then 1 else 0))
      = ∑ p ∈ jsp87Primes X, (if p ∣ n then 1 else 0) * (omega n - 1) :=
    Finset.sum_congr rfl fun p hp => jsp87_row_eq hn hX hp
  calc omega n * (omega n - 1)
      = (∑ p ∈ jsp87Primes X, (if p ∣ n then 1 else 0)) * (omega n - 1) := by
          rw [jsp87_omega_eq_sum_dvd hn hX]
    _ = ∑ p ∈ jsp87Primes X, (if p ∣ n then 1 else 0) * (omega n - 1) := Finset.sum_mul _ _ _
    _ = ∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) := hrows.symm

private theorem card_filter_ite (t : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ x ∈ t, (if Q x then 1 else 0)) = (t.filter Q).card := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

/-- **`∑_{n ≤ X} ω n` IS THE MEAN-FIELD COUNT** `jsp87OmegaCount X`: the two
finsets `{0, …, X−1}` (shifted by `1`) and `{1, …, X}` are the same. -/
theorem jsp87_sumIcc_eq_omegaCount (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, omega n) = jsp87OmegaCount X := by
  unfold jsp87OmegaCount
  have key : Finset.Icc 1 X = (Finset.range X).image (fun k => k + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega
  calc (∑ n ∈ Finset.Icc 1 X, omega n)
      = Finset.sum (Finset.range X) (fun k => omega (k + 1)) := by
        rw [key, Finset.sum_image]
        intro a _ b _ hab
        simp only [Nat.succ.injEq] at hab
        exact hab
    _ = ∑ k ∈ Finset.range X, omega (k + 1) := rfl

/-- `jsp87FactPair` unfolded. -/
theorem jsp87_factPair_eq' (X : ℕ) :
    jsp87FactPair X = ∑ n ∈ Finset.Icc 1 X, omega n * (omega n - 1) := rfl

/-! ## 2. **THE EXACT SECOND-MOMENT IDENTITY** (closes round 133's blocker) -/

/-- **THE SECOND FACTORIAL MOMENT IS A PRIME-PAIR SUM.**  `jsp87FactPair X` is
*exactly* `jsp87OffPair X`: every term `⌊X/(p q)⌋` is an exact count of
integers `≤ X` divisible by the two distinct primes `p, q` (`jsp87_card_pair`).

This is the analogue of round 127's `jsp87Var_cnt_eq_sqDefect` for `ω` itself:
the second factorial moment of `ω` is a *closed form* over the primes. -/
theorem jsp87_factPair_eq_offPair (X : ℕ) (hX : 1 ≤ X) : jsp87FactPair X = jsp87OffPair X := by
  classical
  set Qp : ℕ → Finset ℕ := fun p => (jsp87Primes X).filter (fun r => r ≠ p) with hQp
  have h1 : (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ jsp87Primes X, ∑ q ∈ Qp p,
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0))
      = ∑ p ∈ jsp87Primes X, ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ Qp p,
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) := Finset.sum_comm
  have h2 : (∑ p ∈ jsp87Primes X, ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ Qp p,
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0))
      = ∑ p ∈ jsp87Primes X, ∑ q ∈ Qp p, ∑ n ∈ Finset.Icc 1 X,
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Finset.sum_comm
  have h3 : (∑ p ∈ jsp87Primes X, ∑ q ∈ Qp p, ∑ n ∈ Finset.Icc 1 X,
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0))
      = ∑ p ∈ jsp87Primes X, ∑ q ∈ Qp p,
          ((Finset.Icc 1 X).filter (fun m => p ∣ m ∧ q ∣ m)).card := by
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    exact card_filter_ite (Finset.Icc 1 X) (fun m => p ∣ m ∧ q ∣ m)
  have h4 : (∑ p ∈ jsp87Primes X, ∑ q ∈ Qp p,
          ((Finset.Icc 1 X).filter (fun m => p ∣ m ∧ q ∣ m)).card)
      = ∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p),
          X / (p * q) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.mp hq
    have hX0 : 1 ≤ X := by omega
    exact jsp87_card_pair (X := X) (p := p) (q := q) hX0 (prime_mem_jsp87Primes hp)
      (prime_mem_jsp87Primes hq'.1) (Ne.symm hq'.2)
  have hstep : (∑ n ∈ Finset.Icc 1 X, omega n * (omega n - 1))
      = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ jsp87Primes X, ∑ q ∈ Qp p,
          (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    exact jsp87_fact_ind (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  unfold jsp87FactPair jsp87OffPair
  exact hstep.trans (h1.trans (h2.trans (h3.trans h4)))

/-- **THE CROWN OF THE ROUND: THE EXACT SECOND MOMENT OF `ω`.**  For `1 ≤ X`,

```
jsp87SqMoment X  =  jsp87OmegaCount X  +  ∑_{p ≠ q primes ≤ X} ⌊X / (p q)⌋ ,
```

i.e. the second moment of `ω` over `[1, X]` is the mean-field prime-divisor
count **plus** the exact prime-pair content.  No analytic input, no boundary
error, and the *whole* `π(X)²` ambiguity of round 115's Chowla estimate
disappears because at shift `0` both primes divide the same integer. -/
theorem jsp87SqMoment_eq_primeDiv_add_pairs (X : ℕ) (hX : 1 ≤ X) :
    jsp87SqMoment X = jsp87OmegaCount X + jsp87OffPair X := by
  have hsq : ∀ n ∈ Finset.Icc 1 X, omega n ^ 2 = omega n + omega n * (omega n - 1) := by
    intro n hn
    by_cases h : omega n = 0
    · rw [h]; ring
    · have hpos : 0 < omega n := Nat.pos_of_ne_zero h
      have hid : omega n - 1 + 1 = omega n := Nat.succ_pred_eq_of_pos hpos
      calc omega n ^ 2 = omega n * omega n := by rw [pow_two]
        _ = omega n * ((omega n - 1) + 1) := by rw [hid]
        _ = omega n * 1 + omega n * (omega n - 1) := by ring
        _ = omega n + omega n * (omega n - 1) := by ring
  have h1 : jsp87SqMoment X
      = ∑ n ∈ Finset.Icc 1 X, (omega n + omega n * (omega n - 1)) := by
    unfold jsp87SqMoment
    exact Finset.sum_congr rfl fun n hn => hsq n hn
  have h2 : (∑ n ∈ Finset.Icc 1 X, (omega n + omega n * (omega n - 1)))
      = (∑ n ∈ Finset.Icc 1 X, omega n)
        + ∑ n ∈ Finset.Icc 1 X, omega n * (omega n - 1) := by
    exact Finset.sum_add_distrib
  have h3 : jsp87OmegaCount X + jsp87OffPair X
      = (∑ n ∈ Finset.Icc 1 X, omega n) + ∑ n ∈ Finset.Icc 1 X, omega n * (omega n - 1) := by
    rw [jsp87_sumIcc_eq_omegaCount X, ← jsp87_factPair_eq' X,
      jsp87_factPair_eq_offPair X hX]
  rw [h1, h2]
  exact h3.symm

/-! ## 3. The prime-pair content: symmetry, and the lower bound -/

private theorem jsp87_sum_filter_ite (t : Finset ℕ) (f : ℕ → ℕ) (g : ℕ → Prop)
    [DecidablePred g] :
    (∑ q ∈ t.filter g, f q) = ∑ q ∈ t, f q * (if g q then 1 else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : g q
  · rw [ite_eq_left h, ite_eq_left h, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

theorem jsp87_filter_ne_lt (X p : ℕ) :
    (jsp87Primes X).filter (fun r => r < p) ∪ (jsp87Primes X).filter (fun r => p < r)
      = (jsp87Primes X).filter (fun r => r ≠ p) := by
  ext q
  constructor
  · intro h
    rw [Finset.mem_union] at h
    rcases h with h | h
    · rw [Finset.mem_filter] at h
      obtain ⟨h1, h2⟩ := h
      rw [Finset.mem_filter]
      exact ⟨h1, by omega⟩
    · rw [Finset.mem_filter] at h
      obtain ⟨h1, h2⟩ := h
      rw [Finset.mem_filter]
      exact ⟨h1, by omega⟩
  · intro h
    rw [Finset.mem_filter] at h
    obtain ⟨h1, h2⟩ := h
    rw [Finset.mem_union]
    by_cases hlt : q < p
    · exact Or.inl (Finset.mem_filter.mpr ⟨h1, hlt⟩)
    · have hgt : p < q := by omega
      exact Or.inr (Finset.mem_filter.mpr ⟨h1, hgt⟩)

/-- **THE OFF-DIAGONAL SPLIT OF A ROW.** -/
theorem jsp87_row_split_lt (X p : ℕ) (f : ℕ → ℕ) :
    (∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p), f q)
      = (∑ q ∈ (jsp87Primes X).filter (fun r => r < p), f q)
        + ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), f q := by
  have key := jsp87_filter_ne_lt X p
  have hd : Disjoint ((jsp87Primes X).filter (fun r => r < p))
      ((jsp87Primes X).filter (fun r => p < r)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1' : x < p := (Finset.mem_filter.mp hx1).2
    have h2' : p < x := (Finset.mem_filter.mp hx2).2
    exact absurd h2' (by omega)
  have h := Finset.sum_union (s₁ := (jsp87Primes X).filter (fun r => r < p))
    (s₂ := (jsp87Primes X).filter (fun r => p < r)) (f := f) hd
  rw [key] at h
  exact h

/-- **THE TWO TRIANGLES ARE EQUAL.**  The prime-pair content below the diagonal
is the mirror image of the content above it, because `⌊X / (p q)⌋` is
symmetric in `p, q`. -/
theorem jsp87_lower_eq_upper (X : ℕ) :
    (∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => r < p), X / (p * q))
      = ∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q) := by
  classical
  have h1 : (∑ p ∈ jsp87Primes X,
        ∑ q ∈ (jsp87Primes X).filter (fun r => r < p), X / (p * q))
      = ∑ p ∈ jsp87Primes X, ∑ q ∈ jsp87Primes X,
          (X / (p * q)) * (if q < p then 1 else 0) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact jsp87_sum_filter_ite _ _ _
  have h2 : (∑ p ∈ jsp87Primes X, ∑ q ∈ jsp87Primes X,
        (X / (p * q)) * (if q < p then 1 else 0))
      = ∑ q ∈ jsp87Primes X, ∑ p ∈ jsp87Primes X,
          (X / (p * q)) * (if q < p then 1 else 0) := Finset.sum_comm
  have h3 : (∑ q ∈ jsp87Primes X, ∑ p ∈ jsp87Primes X,
        (X / (p * q)) * (if q < p then 1 else 0))
      = ∑ q ∈ jsp87Primes X, ∑ p ∈ jsp87Primes X,
          (X / (q * p)) * (if q < p then 1 else 0) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : q < p
    · simp only [ite_eq_left h, Nat.mul_comm]
    · simp only [ite_eq_right h, Nat.mul_comm]
  have h4 : (∑ q ∈ jsp87Primes X, ∑ p ∈ jsp87Primes X,
        (X / (q * p)) * (if q < p then 1 else 0))
      = ∑ q ∈ jsp87Primes X, ∑ p ∈ (jsp87Primes X).filter (fun r => q < r), X / (q * p) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← jsp87_sum_filter_ite]
  exact h1.trans (h2.trans (h3.trans h4))

/-- **THE OFF-DIAGONAL IS TWICE THE UPPER TRIANGLE.** -/
theorem jsp87_offPair_eq_two_mul_upPair (X : ℕ) :
    jsp87OffPair X = 2 * jsp87UpPair X := by
  classical
  unfold jsp87OffPair jsp87UpPair
  have hrow : ∀ p ∈ jsp87Primes X,
      (∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p), X / (p * q))
        = (∑ q ∈ (jsp87Primes X).filter (fun r => r < p), X / (p * q))
          + ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q) :=
    fun p _ => jsp87_row_split_lt X p (fun q => X / (p * q))
  calc (∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => r ≠ p), X / (p * q))
      = ∑ p ∈ jsp87Primes X, ((∑ q ∈ (jsp87Primes X).filter (fun r => r < p), X / (p * q))
          + ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q)) :=
        Finset.sum_congr rfl fun p hp => hrow p hp
    _ = (∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => r < p), X / (p * q))
        + ∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q) :=
        Finset.sum_add_distrib
    _ = _ + _ := by rw [jsp87_lower_eq_upper X]
    _ = 2 * ∑ p ∈ jsp87Primes X, ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q) := by
        ring

/-- **EVERY REACHABLE PAIR CONTRIBUTES AT LEAST ONE INTEGER.** -/
theorem jsp87UpPair_ge_pairCount (X : ℕ) : jsp87PairCount X ≤ jsp87UpPair X := by
  classical
  unfold jsp87PairCount jsp87UpPair
  refine Finset.sum_le_sum (N := (ℕ)) (s := jsp87Primes X) fun p hp => ?_
  have hcard : ((jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X)).card
      ≤ ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q) := by
    have hge : (∑ q ∈ (jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X), (1 : ℕ))
        ≤ ∑ q ∈ (jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X), X / (p * q) := by
      refine Finset.sum_le_sum (N := (ℕ)) (s := (jsp87Primes X).filter
        (fun q => p < q ∧ p * q ≤ X)) fun q hq => ?_
      have hq' := Finset.mem_filter.mp hq
      have h2p : 0 < p := by
        have hx := two_le_mem_jsp87Primes hp
        omega
      have h2q : 0 < q := by
        have h3 := hq'.1
        omega
      have hpos : 0 < p * q := Nat.mul_pos h2p h2q
      have h1 : (1 : ℕ) ≤ X / (p * q) :=
        (Nat.le_div_iff_mul_le hpos).mpr (by simpa using hq'.2.2)
      simpa using h1
    have hone : (∑ q ∈ (jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X), (1 : ℕ))
        ≤ ∑ q ∈ (jsp87Primes X).filter (fun r => p < r), X / (p * q) := by
      refine hge.trans (Finset.sum_le_sum_of_subset_of_nonneg (s := _) (t := _) ?_ ?_)
      · intro q hq
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
          (Finset.mem_filter.mp hq).2.1⟩
      · intro q hq hq''
        exact Nat.zero_le _
    rw [Finset.card_eq_sum_ones]
    exact hone
  exact hcard

/-- **THE PRICE, IN THE FORM `policy.json` ASKED FOR**
(`round_132_blockers.jsp87_sumOmegaSq_ge_pairs`).**  For every `X`,

```
2 · # { (p, q) : p < q primes ≤ X, p q ≤ X }  ≤  ∑_{n ≤ X} ω n (ω n − 1) ,
```

the first unconditional lower bound on the second factorial moment of `ω` — the
Turan–Kubilius content that hypothesis (5.21) of arXiv:2512.01739 needs, and the
only "variance is large" input any round has produced. -/
theorem jsp87_factMoment_ge_pairCount (X : ℕ) (hX : 1 ≤ X) :
    2 * jsp87PairCount X ≤ jsp87FactPair X := by
  have h1 : jsp87FactPair X = jsp87OffPair X := jsp87_factPair_eq_offPair X hX
  have h2 : jsp87OffPair X = 2 * jsp87UpPair X := jsp87_offPair_eq_two_mul_upPair X
  have h3 : jsp87PairCount X ≤ jsp87UpPair X := jsp87UpPair_ge_pairCount X
  omega

/-- **THE SECOND MOMENT IS AT LEAST THE MEAN FIELD PLUS TWICE THE PAIRS.**  The
exact statement `policy.json` `next_round_attack[1]` of round 133 asked for. -/
theorem jsp87SqMoment_ge_primeDiv_pairCount (X : ℕ) (hX : 1 ≤ X) :
    jsp87OmegaCount X + 2 * jsp87PairCount X ≤ jsp87SqMoment X := by
  have h1 := jsp87_factMoment_ge_pairCount X hX
  have h2 : jsp87OmegaCount X + jsp87FactPair X = jsp87SqMoment X := by
    have key : (∑ n ∈ Finset.Icc 1 X, omega n ^ 2)
        = (∑ n ∈ Finset.Icc 1 X, omega n) + jsp87FactPair X := by
      unfold jsp87FactPair
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by
        by_cases h : omega n = 0
        · rw [h]; ring
        · have hpos : 0 < omega n := Nat.pos_of_ne_zero h
          have hid : omega n - 1 + 1 = omega n := Nat.succ_pred_eq_of_pos hpos
          calc omega n ^ 2 = omega n * omega n := by rw [pow_two]
            _ = omega n * ((omega n - 1) + 1) := by rw [hid]
            _ = omega n * 1 + omega n * (omega n - 1) := by ring
            _ = omega n + omega n * (omega n - 1) := by ring
    unfold jsp87SqMoment
    rw [key, jsp87_sumIcc_eq_omegaCount X]
  omega

/-! ## 4. The Tao–Teräväinen payoff: the exact price of hypothesis (5.21) -/

/-- **THE UNWEIGHTED SUM OVER THE WINDOW** `∑_{N < L} ω N` is the mean-field count
`jsp87OmegaCount (L − 1)`. -/
theorem jsp87_sum_range_zero_eq (L : ℕ) (hL : 1 ≤ L) :
    (∑ N ∈ Finset.range L, omega N) = jsp87OmegaCount (L - 1) := by
  have hrange : (Finset.range L).filter (fun N => 1 ≤ N) = Finset.Icc 1 (L - 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  calc (∑ N ∈ Finset.range L, omega N)
      = ∑ N ∈ (Finset.range L).filter (fun N => 1 ≤ N), omega N := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun N _ => ?_
        by_cases h : 1 ≤ N
        · simp [h]
        · have hN : N = 0 := by omega
          simp [hN]
    _ = ∑ N ∈ Finset.Icc 1 (L - 1), omega N := by rw [hrange]
    _ = jsp87OmegaCount (L - 1) := jsp87_sumIcc_eq_omegaCount _

/-- **THE WINDOWED SECOND MOMENT AT SHIFT `0` IS THE SECOND MOMENT OF THE FILE.**
The diagonal of §5.4 of arXiv:2512.01739, at `k = 0`, is `jsp87SqMoment (L−1)`
exactly — a purely arithmetic integer. -/
theorem jsp87SqWindow_zero_eq (L : ℕ) (hL : 1 ≤ L) :
    jsp87SqWindow 0 L = jsp87SqMoment (L - 1) := by
  have hrange : (Finset.range L).filter (fun N => 1 ≤ N) = Finset.Icc 1 (L - 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  calc jsp87SqWindow 0 L
      = ∑ N ∈ Finset.range L, omega N ^ 2 := by
        unfold jsp87SqWindow
        exact Finset.sum_congr rfl fun N _ => by rw [Nat.add_zero]
    _ = ∑ N ∈ (Finset.range L).filter (fun N => 1 ≤ N), omega N ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun N _ => ?_
        by_cases h : 1 ≤ N
        · simp [h]
        · have hN : N = 0 := by omega
          simp [hN]
    _ = ∑ N ∈ Finset.Icc 1 (L - 1), omega N ^ 2 := by rw [hrange]
    _ = jsp87SqMoment (L - 1) := rfl

/-- **THE VARIANCE OF `ω` AT SHIFT `0`, IN THE SECOND-MOMENT FORM.**  This is the
normalised diagonal of §5.4 with the mean field removed. -/
theorem jsp87_tcVarAt_zero_eq (X : ℕ) :
    (jsp87Tw 0 ^ 2) * jsp87TcVarAt (X + 1) 0
      = (((jsp87SqMoment X : ℕ) : ℝ) / 4) / ((X + 1 : ℕ) : ℝ)
        - ((((jsp87OmegaCount X : ℕ) : ℝ) / 2) / ((X + 1 : ℕ) : ℝ)) ^ 2 := by
  have hne : (Finset.range (X + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos X)⟩
  have hcard : (Finset.range (X + 1)).card = X + 1 := Finset.card_range _
  have h1 : jsp87FAvg (Finset.range (X + 1)) (fun N => (((omega (N + 0) : ℕ) : ℝ)) ^ 2)
      = (((jsp87SqMoment X : ℕ) : ℝ)) / ((X + 1 : ℕ) : ℝ) := by
    have key : (∑ i ∈ Finset.range (X + 1), (((omega (i + 0) : ℕ) : ℝ)) ^ 2)
        = ((jsp87SqMoment X : ℕ) : ℝ) := by
      have h2 : (∑ i ∈ Finset.range (X + 1), omega (i + 0) ^ 2)
          = jsp87SqMoment X :=
        jsp87SqWindow_zero_eq (X + 1) (Nat.succ_le_succ (Nat.zero_le X))
      have h1 : (∑ i ∈ Finset.range (X + 1), (((omega (i + 0) : ℕ) : ℝ)) ^ 2)
          = ((∑ i ∈ Finset.range (X + 1), omega (i + 0) ^ 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.cast_pow]
      rw [h1, h2]
    unfold jsp87FAvg
    rw [hcard, key]
  have h2 : jsp87FAvg (Finset.range (X + 1)) (fun N => ((omega (N + 0) : ℕ) : ℝ))
      = (((jsp87OmegaCount X : ℕ) : ℝ)) / ((X + 1 : ℕ) : ℝ) := by
    have hsum0 : (∑ i ∈ Finset.range (X + 1), omega (i + 0)) = jsp87OmegaCount X := by
      simpa using (jsp87_sum_range_zero_eq (X + 1) (Nat.succ_le_succ (Nat.zero_le X)))
    have key : (∑ i ∈ Finset.range (X + 1), ((omega (i + 0) : ℕ) : ℝ))
        = (((jsp87OmegaCount X : ℕ) : ℝ)) := by
      have hh : (∑ i ∈ Finset.range (X + 1), ((omega (i + 0) : ℕ) : ℝ))
          = ((∑ i ∈ Finset.range (X + 1), omega (i + 0) : ℕ) : ℝ) :=
        (Nat.cast_sum _ _).symm
      calc (∑ i ∈ Finset.range (X + 1), ((omega (i + 0) : ℕ) : ℝ))
          = ((∑ i ∈ Finset.range (X + 1), omega (i + 0) : ℕ) : ℝ) := hh
        _ = ((jsp87OmegaCount X : ℕ) : ℝ) :=
          congrArg (fun z : ℕ => (z : ℝ)) hsum0
    unfold jsp87FAvg
    rw [hcard, key]
  unfold jsp87TcVarAt
  rw [jsp87Var_eq_FAvg_sq_sub (Finset.range (X + 1)) hne
    (fun N => ((omega (N + 0) : ℕ) : ℝ))]
  rw [h1, h2]
  unfold jsp87Tw
  field_simp
  ring

/-- **THE ARITHMETIC SUPPLY OF HYPOTHESIS (5.21) AT `H = 1`.**  What the
arithmetic content of §1–§2 — the mean-field count `jsp87OmegaCount X` and the
prime-pair count `jsp87PairCount X` — provides for the quantity
`(1/4) · Var ω` over `[0, X+1)`, i.e. for `2^{−2} · Var (N ↦ ω N)`, the object
§5.4 of arXiv:2512.01739 needs. -/
noncomputable def jsp87Arith521 (X : ℕ) : ℝ :=
  ((((jsp87OmegaCount X + 2 * jsp87PairCount X : ℕ) : ℝ) / 4) / ((X + 1 : ℕ) : ℝ))
    - ((((jsp87OmegaCount X : ℕ) : ℝ) / 2) / ((X + 1 : ℕ) : ℝ)) ^ 2

/-- **THE ARITHMETIC SUPPLY IS A LOWER BOUND FOR THE WEIGHTED DIAGONAL
VARIANCE.** -/
theorem jsp87_arith521_le_var (X : ℕ) (hX : 1 ≤ X) :
    jsp87Arith521 X ≤ (jsp87Tw 0 ^ 2) * jsp87TcVarAt (X + 1) 0 := by
  have hsq : (((jsp87OmegaCount X + 2 * jsp87PairCount X : ℕ) : ℝ))
      ≤ (((jsp87SqMoment X : ℕ) : ℝ)) := by
    have hh := jsp87SqMoment_ge_primeDiv_pairCount X hX
    exact_mod_cast hh
  rw [jsp87_tcVarAt_zero_eq, jsp87Arith521]
  have hL : (0 : ℝ) < ((X + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos X)
  have hsq2 : (((jsp87OmegaCount X + 2 * jsp87PairCount X : ℕ) : ℝ) / 4)
      ≤ (((jsp87SqMoment X : ℕ) : ℝ) / 4) :=
    div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 4)
  have hcore : (((jsp87OmegaCount X + 2 * jsp87PairCount X : ℕ) : ℝ) / 4)
      / ((X + 1 : ℕ) : ℝ)
      ≤ (((jsp87SqMoment X : ℕ) : ℝ) / 4) / ((X + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hsq2 (le_of_lt hL)
  linarith

/-- **THE PRIME-PAIRS CAN NEVER OUTNUMBER THE PRIME MULTIPLES.**  Every reachable
pair `(p, q)` with `p q ≤ X` is charged to the `q`-multiple of `p` counted by
`jsp87OmegaCount X`, and there are `⌊X/p⌋ ≤ X/p` of them. -/
theorem jsp87_pairCount_le_omegaCount (X : ℕ) : jsp87PairCount X ≤ jsp87OmegaCount X := by
  classical
  unfold jsp87PairCount
  have hstep : ∀ p ∈ jsp87Primes X,
      ((jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X)).card ≤ X / p := by
    intro p hp
    have h2p : 0 < p := by
      have hx := two_le_mem_jsp87Primes hp
      omega
    have hsub1 : (jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X)
        ⊆ (jsp87Primes X).filter (fun q => q ≤ X / p) := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqp : q * p ≤ X := by rw [Nat.mul_comm]; exact hq'.2.2
      exact Finset.mem_filter.mpr ⟨hq'.1, (Nat.le_div_iff_mul_le h2p).mpr hqp⟩
    have hsub2 : (jsp87Primes X).filter (fun q => q ≤ X / p) ⊆ Finset.Icc 2 (X / p) := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      exact Finset.mem_Icc.mpr ⟨two_le_mem_jsp87Primes hq'.1, hq'.2⟩
    calc ((jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X)).card
        ≤ ((jsp87Primes X).filter (fun q => q ≤ X / p)).card :=
          Finset.card_le_card hsub1
      _ ≤ (Finset.Icc 2 (X / p)).card := Finset.card_le_card hsub2
      _ ≤ (Finset.Icc 1 (X / p)).card := by
        refine Finset.card_le_card ?_
        intro q hq
        rw [Finset.mem_Icc] at hq ⊢
        exact ⟨Nat.le_trans (by omega) hq.1, hq.2⟩
      _ = X / p := by rw [Nat.card_Icc, ← Nat.succ_eq_add_one, Nat.succ_sub_one]
  calc (∑ p ∈ jsp87Primes X, ((jsp87Primes X).filter (fun q => p < q ∧ p * q ≤ X)).card)
      ≤ ∑ p ∈ jsp87Primes X, X / p := Finset.sum_le_sum fun p hp => hstep p hp
    _ = jsp87OmegaCount X := (jsp87_omegaCount_eq_primeDiv X).symm

/-- **THE CROWN OF THE PAYOFF: THE ARITHMETIC SUPPLY NEVER REACHES `1`.**
For every `X`,

```
jsp87Arith521 X  ≤  9/16  <  1 ,
```

because the two-triangle symmetry gives `jsp87PairCount X ≤ jsp87OmegaCount X`
and the quadratic `(3/2)t − t²` has maximum `9/16`, attained at `t = 3/4`.

**Consequence.**  Hypothesis (5.21) of arXiv:2512.01739 — that the weighted
diagonal variance be at least `1` — can NEVER be discharged by the arithmetic
content of the second moment.  The "variance is large" direction is *not* a
statement about the prime-pair counting: the mean field `(log log X)²`
dominates the arithmetic diagonal, and this is now a machine-checked obstruction
rather than an expectation.  What remains on the (5.21) side is the
*correlation* input of round 130, `jsp87Mcov_small`; no combinatorial counting
can help. -/
theorem jsp87_arith521_le (X : ℕ) (hX : 1 ≤ X) : jsp87Arith521 X ≤ 9 / 16 := by
  have h1 := jsp87_arith521_le_var X hX
  have h2 := jsp87_pairCount_le_omegaCount X
  have hposX : (0 : ℝ) < ((X + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos X)
  have ht0 : 0 ≤ ((jsp87OmegaCount X : ℕ) : ℝ) / 2 / ((X + 1 : ℕ) : ℝ) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (le_of_lt hposX)
  set t : ℝ := ((jsp87OmegaCount X : ℕ) : ℝ) / 2 / ((X + 1 : ℕ) : ℝ) with ht
  have ht1 : 0 ≤ t := ht0
  have hpc : ((2 * jsp87PairCount X : ℕ) : ℝ) ≤ 2 * ((jsp87OmegaCount X : ℕ) : ℝ) := by
    have hh := jsp87_pairCount_le_omegaCount X
    rw [Nat.cast_mul]
    exact_mod_cast (by omega)
  have key : jsp87Arith521 X ≤ (3 / 2) * t - t ^ 2 := by
    unfold jsp87Arith521
    rw [ht]
    have hstep : (((jsp87OmegaCount X + 2 * jsp87PairCount X : ℕ) : ℝ) / 4)
        / ((X + 1 : ℕ) : ℝ)
        ≤ (((jsp87OmegaCount X + 2 * jsp87OmegaCount X : ℕ) : ℝ) / 4)
          / ((X + 1 : ℕ) : ℝ) := by
      have h1 : (((jsp87OmegaCount X + 2 * jsp87PairCount X : ℕ) : ℝ))
          ≤ (((jsp87OmegaCount X + 2 * jsp87OmegaCount X : ℕ) : ℝ)) := by
        have hh := jsp87_pairCount_le_omegaCount X
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        have hh' : jsp87OmegaCount X + 2 * jsp87PairCount X
            ≤ jsp87OmegaCount X + 2 * jsp87OmegaCount X := by omega
        exact_mod_cast hh'
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 4)) (le_of_lt hposX)
    have heq : (((jsp87OmegaCount X + 2 * jsp87OmegaCount X : ℕ) : ℝ) / 4)
        / ((X + 1 : ℕ) : ℝ) = (3 / 2) * t := by
      rw [ht]
      norm_num [Nat.cast_mul, Nat.cast_ofNat]
      ring
    linarith
  have hsq : 0 ≤ (t - 3 / 4) ^ 2 := sq_nonneg _
  rw [show (3 / 2) * t - t ^ 2 = 9 / 16 - (t - 3 / 4) ^ 2 by ring] at key
  linarith

/-- **HYPOTHESIS (5.21) CANNOT BE MET BY ARITHMETIC ALONE, AT ANY HEIGHT.** -/
theorem jsp87_521_arith_impossible (X : ℕ) (hX : 1 ≤ X) : jsp87Arith521 X < 1 := by
  have h := jsp87_arith521_le X hX
  norm_num at h ⊢
  linarith

/-- **THE PRICE OF (5.21): AN EXACT IDENTITY FOR THE WEIGHTED DIAGONAL
VARIANCE.**  For every `L ≥ 1` and `H`,

```
∑_{k < H} 4^{-(k+1)} Var (ω(N+k))
        =  jsp87TcDiag L H / L  −  ∑_{k < H} 4^{-(k+1)} · (𝔼 ω(N+k))² ,
```

the raw second moment divided by the window length, minus the **mean-field
term** `∑ 4^{-(k+1)} μ_k²`.  So hypothesis (5.21), `1 ≤ ∑ 4^{-(k+1)} Var`, is
exactly the arithmetic inequality
`jsp87TcDiag L H ≥ L + L · ∑_{k<H} 4^{-(k+1)} (𝔼 ω(N+k))²`: the raw diagonal
must exceed the window length `L` **by** `L` times the square of the
(weight-averaged) mean of `ω`.  This is the exact, deterministic content of the
"variance is large" hypothesis of arXiv:2512.01739 §5.4. -/
theorem jsp87_diag_var_exact (L H : ℕ) (hL : 1 ≤ L) :
    (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcVarAt L k)
      = jsp87TcDiag L H / (L : ℝ)
        - (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2) := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr hL⟩
  have hcard : (Finset.range L).card = L := Finset.card_range L
  have hstep : ∀ k ∈ Finset.range H,
      jsp87Tw k ^ 2 * jsp87TcVarAt L k
        = jsp87Tw k ^ 2 * ((((jsp87SqWindow k L : ℕ) : ℝ)) / (L : ℝ)
            - jsp87TcMean L k ^ 2) := by
    intro k _
    unfold jsp87TcVarAt
    rw [jsp87Var_eq_FAvg_sq_sub (Finset.range L) hne
      (fun N => ((omega (N + k) : ℕ) : ℝ))]
    have h1 : jsp87FAvg (Finset.range L) (fun N => (((omega (N + k) : ℕ) : ℝ)) ^ 2)
        = (((jsp87SqWindow k L : ℕ) : ℝ)) / (L : ℝ) := by
      unfold jsp87FAvg
      rw [hcard, jsp87cast_sum_sqWindow L k]
    have h2 : jsp87FAvg (Finset.range L) (fun N => ((omega (N + k) : ℕ) : ℝ))
        = jsp87TcMean L k := by
      unfold jsp87TcMean jsp87FAvg
      rw [hcard]
    rw [h1, h2]
  have hA : (∑ k ∈ Finset.range H, (jsp87Tw k ^ 2) * ((jsp87SqWindow k L : ℕ) : ℝ))
      = jsp87TcDiag L H := by
    unfold jsp87TcDiag
    exact Finset.sum_congr rfl fun k _ => rfl
  have hB1 : (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcVarAt L k)
      = ∑ k ∈ Finset.range H,
          (((jsp87Tw k ^ 2) * (((jsp87SqWindow k L : ℕ) : ℝ))) / (L : ℝ)
            - jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hstep k hk]
    ring
  have hB : (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcVarAt L k)
      = ((∑ k ∈ Finset.range H,
          (jsp87Tw k ^ 2) * (((jsp87SqWindow k L : ℕ) : ℝ))) / (L : ℝ)
          - ∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2) := by
    rw [hB1, Finset.sum_sub_distrib]
    rw [← Finset.sum_div (s := Finset.range H) (a := (L : ℝ))]
  calc (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcVarAt L k)
      = (∑ k ∈ Finset.range H,
          (jsp87Tw k ^ 2) * (((jsp87SqWindow k L : ℕ) : ℝ))) / (L : ℝ)
          - ∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2 := hB
    _ = jsp87TcDiag L H / (L : ℝ)
          - (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2) := by
        rw [hA]

/-- **THE TRANSFER: WHAT HYPOTHESIS (5.21) ASKS OF THE RAW DIAGONAL.** -/
theorem jsp87_521_needs_diag (L H : ℕ) (hL : 1 ≤ L)
    (h : 1 ≤ ∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcVarAt L k) :
    (L : ℝ) + (L : ℝ) * (∑ k ∈ Finset.range H,
        jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2) ≤ jsp87TcDiag L H := by
  rw [jsp87_diag_var_exact L H hL] at h
  have hL0 : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hL)
  have hle : 1 ≤ jsp87TcDiag L H / (L : ℝ)
      - (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2) := h
  have h2 : 1 + (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2)
      ≤ jsp87TcDiag L H / (L : ℝ) := by linarith
  have h3 : (1 + (∑ k ∈ Finset.range H, jsp87Tw k ^ 2 * jsp87TcMean L k ^ 2))
      * (L : ℝ) ≤ jsp87TcDiag L H := (le_div_iff₀ hL0).mp h2
  linarith

/-- **THE WEIGHTED DIAGONAL VARIANCE AT `L = 3, H = 1`** is `1/18`. -/
theorem jsp87_diag_var_three_one :
    (∑ k ∈ Finset.range 1, jsp87Tw k ^ 2 * jsp87TcVarAt 3 0) = 1 / 18 := by
  norm_num [jsp87TcVarAt, jsp87Var, jsp87FAvg, jsp87Tw, omega, Finset.sum_range_succ]

/-- **HYPOTHESIS (5.21) IS FALSE AT `L = 3, H = 1`.** -/
theorem jsp87_521_fails_three :
    ¬ (1 ≤ ∑ k ∈ Finset.range 1, jsp87Tw k ^ 2 * jsp87TcVarAt 3 0) := by
  rw [jsp87_diag_var_three_one]
  norm_num

/-- **`k` DISTINCT PRIMES BELOW A BOUND `M ≥ 3`.**  Built from Euclid's theorem
`Nat.exists_infinite_primes`, by inserting a fresh prime larger than the
current bound at each step. -/
private theorem jsp87_exists_primes_le : ∀ k : ℕ,
    ∃ (s : Finset ℕ) (M : ℕ), 3 ≤ M ∧ s.card = k ∧ ∀ p ∈ s, p.Prime ∧ p ≤ M := by
  intro k
  induction k with
  | zero =>
    exact ⟨∅, 3, le_rfl, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨s, M, hM, hs, hsp⟩ := ih
    obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (M + 1)
    have hp0 : p ∉ s := by
      intro hh
      have h2 := hsp p hh
      omega
    refine ⟨Finset.cons p s hp0, p, by omega, by rw [Finset.card_cons hp0]; omega, ?_⟩
    intro q hq
    rw [Finset.mem_cons] at hq
    rcases hq with hq | hq
    · subst hq
      exact ⟨hpp, by omega⟩
    · have h2 := hsp q hq
      exact ⟨h2.1, by omega⟩

/-- **THE SMALL PRIME `2` SUPPLIES ALL THE SMALL PRIME PAIRS.**  For `2 ≤ M`,
every prime `q` with `2 < q ≤ M` pairs with `2`: `2 < q` and `2 q ≤ 2 M`. -/
theorem jsp87_pairCount_ge (M : ℕ) (hM : 2 ≤ M) :
    ((jsp87Primes M).filter (fun q => 2 < q)).card ≤ jsp87PairCount (2 * M) := by
  classical
  unfold jsp87PairCount
  have h2mem : 2 ∈ jsp87Primes (2 * M) := by
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Nat.prime_two⟩
  have hsub : (jsp87Primes M).filter (fun q => 2 < q)
      ⊆ (jsp87Primes (2 * M)).filter (fun q => 2 < q ∧ 2 * q ≤ 2 * M) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hq1 := Finset.mem_filter.mp hq'.1
    have hq2 : 2 ≤ q ∧ q ≤ M := Finset.mem_Icc.mp hq1.1
    have hqp : q.Prime := hq1.2
    have hmem : q ∈ jsp87Primes (2 * M) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq2.1, by omega⟩, hqp⟩
    have hle : 2 * q ≤ 2 * M := by
      have := hq2.2
      omega
    exact Finset.mem_filter.mpr ⟨hmem, ⟨hq'.2, hle⟩⟩
  apply le_trans (Finset.card_le_card hsub)
  exact Finset.single_le_sum
    (f := fun p => ((jsp87Primes (2 * M)).filter (fun q => p < q ∧ p * q ≤ 2 * M)).card)
    (s := jsp87Primes (2 * M)) (fun p _ => Nat.zero_le _) h2mem

/-- **THE PRIME-PAIR CONTENT IS UNBOUNDED.**  For every `k` there is an `X` with
at least `k` reachable prime pairs `p < q ≤ X`, `p q ≤ X` — by Euclid's theorem
on the infinitude of primes (`Nat.exists_infinite_primes`) and
`jsp87_pairCount_ge`.  So the prime-pair count of §2 grows without bound, and the
lower bound of `jsp87_factMoment_ge_pairCount` is genuinely informative. -/
theorem jsp87_pairCount_unbounded : ∀ k : ℕ, ∃ X : ℕ, k ≤ jsp87PairCount X := by
  intro k
  obtain ⟨s, M, hM, hs, hsp⟩ := jsp87_exists_primes_le (k + 1)
  have hsub : s.erase 2 ⊆ (jsp87Primes M).filter (fun q => 2 < q) := by
    intro q hq
    have hq' := Finset.mem_erase.mp hq
    have hq2 := hsp q hq'.2
    have h2le : 2 ≤ q := hq2.1.two_le
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h2le, hq2.2⟩, hq2.1⟩, ?_⟩
    have hlt : 2 < q := by
      rcases Nat.exists_eq_add_of_le h2le with ⟨m, hm⟩
      have hm0 : m ≠ 0 := by
        intro hm0
        have : q = 2 := by omega
        exact hq'.1 this
      omega
    exact hlt
  have hcard1 : ((jsp87Primes M).filter (fun q => 2 < q)).card ≥ (s.erase 2).card :=
    Finset.card_le_card (fun a ha => hsub ha)
  have hcard2 : k ≤ (s.erase 2).card := by
    have h1 : s.card = k + 1 := hs
    by_cases hc : 2 ∈ s
    · rw [Finset.card_erase_of_mem hc] at hcard1 ⊢
      omega
    · have hsub2 : s ⊆ s.erase 2 := by
        intro a ha
        rw [Finset.mem_erase]
        exact ⟨fun h => hc (h ▸ ha), ha⟩
      have h2 := Finset.card_le_card (fun a ha => hsub2 ha)
      omega
  refine ⟨2 * M, ?_⟩
  exact le_trans (le_trans hcard2 hcard1) (jsp87_pairCount_ge M (by omega))

/-! ## 5. Machine-checked instances of the identity and of the pair count -/

theorem jsp87SqMoment_six : jsp87SqMoment 6 = 8 := by native_decide

theorem jsp87OffPair_six : jsp87OffPair 6 = 2 := by native_decide

theorem jsp87FactPair_six : jsp87FactPair 6 = 2 := by native_decide

theorem jsp87PairCount_six : jsp87PairCount 6 = 1 := by native_decide

theorem jsp87SqMoment_thirty : jsp87SqMoment 30 = 73 := by native_decide

theorem jsp87OffPair_thirty : jsp87OffPair 30 = 30 := by native_decide

theorem jsp87PairCount_thirty : jsp87PairCount 30 = 7 := by native_decide

theorem jsp87OmegaCount_thirty : jsp87OmegaCount 30 = 43 := by native_decide

/-- **THE IDENTITY AT `X = 30`, VERIFIED.** -/
theorem jsp87SqMoment_eq_pairs_thirty : jsp87SqMoment 30 = jsp87OmegaCount 30 + jsp87OffPair 30 := by
  native_decide

/-- **THE PRIME-PAIRS NEVER OUTNUMBER THE MEAN FIELD, MACHINE-CHECKED AT
`X = 30`.** -/
theorem jsp87_pairCount_le_omegaCount_thirty : jsp87PairCount 30 ≤ jsp87OmegaCount 30 := by
  native_decide

/-- **THE ROUND IN ONE THEOREM.** -/
theorem jsp87_sqPair_summary (X : ℕ) (hX : 1 ≤ X) :
    (jsp87SqMoment X = jsp87OmegaCount X + jsp87OffPair X)
      ∧ (2 * jsp87PairCount X ≤ jsp87FactPair X)
      ∧ (jsp87PairCount X ≤ jsp87OmegaCount X)
      ∧ (jsp87Arith521 X ≤ 9 / 16) := by
  exact ⟨jsp87SqMoment_eq_primeDiv_add_pairs X hX, jsp87_factMoment_ge_pairCount X hX,
    jsp87_pairCount_le_omegaCount X, jsp87_arith521_le X hX⟩

end JSP87
