import JSPProblem.Mean
import JSPProblem.Chowla
import JSPProblem.CorrShift
import JSPProblem.CrtSieve
namespace JSP87

private theorem card_ite_aux (t : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (t.filter Q).card = ∑ x ∈ t, (if Q x then 1 else 0) := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

private theorem ind_congr {t : Finset ℕ} (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ x ∈ t, (P x ↔ Q x)) :
    (∑ x ∈ t, (if P x then 1 else 0)) = ∑ x ∈ t, (if Q x then 1 else 0) := by
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases hp : P x
  · rw [if_pos hp, if_pos ((h x hx).mp hp)]
  · rw [if_neg hp, if_neg (fun hx' => hp ((h x hx).mpr hx'))]

theorem mem_primFactors_iff {n X p : ℕ} (hn : 1 ≤ n) (hX : n ≤ X)
    (hp : p ∈ jsp87Primes X) : (p ∈ n.primeFactors ↔ p ∣ n) := by
  rw [← jsp87_filter_dvd_primeFactors hn hX]
  simp only [Finset.mem_filter]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨hp, h⟩

theorem sq_ind {n X : ℕ} (hn : 1 ≤ n) (hX : n ≤ X) :
    omega n ^ 2 = ∑ p ∈ jsp87Primes X, ∑ q ∈ jsp87Primes X,
      (if (p ∣ n) ∧ (q ∣ n) then 1 else 0) := by
  have hS : (jsp87Primes X).filter (fun r => r ∣ n) = n.primeFactors :=
    jsp87_filter_dvd_primeFactors hn hX
  have hsub : n.primeFactors ⊆ jsp87Primes X := by
    rw [← hS]; exact Finset.filter_subset _ _
  have hkey : (jsp87Primes X).filter (fun x => x ∈ n.primeFactors) = n.primeFactors := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨hsub hx, hx⟩
  have hc2 : omega n = ∑ x ∈ jsp87Primes X, (if x ∈ n.primeFactors then 1 else 0) := by
    rw [omega]
    exact ((card_ite_aux (jsp87Primes X) (fun x => x ∈ n.primeFactors)).symm.trans
      (by rw [hkey])).symm
  have hmem (r : ℕ) (hr : r ∈ jsp87Primes X) : (r ∈ n.primeFactors ↔ r ∣ n) :=
    mem_primFactors_iff hn hX hr
  calc omega n ^ 2 = omega n * omega n := by ring
    _ = (∑ x ∈ jsp87Primes X, (if x ∈ n.primeFactors then 1 else 0))
        * (∑ x ∈ jsp87Primes X, (if x ∈ n.primeFactors then 1 else 0)) :=
          congrArg₂ (fun a b => a * b) hc2 hc2
    _ = (∑ x ∈ jsp87Primes X, (if x ∣ n then 1 else 0))
        * (∑ x ∈ jsp87Primes X, (if x ∣ n then 1 else 0)) := by
          rw [ind_congr (P := fun x => x ∈ n.primeFactors) (Q := fun x => x ∣ n)
            (fun x hx => hmem x hx)]
    _ = ∑ x ∈ jsp87Primes X, (if x ∣ n then 1 else 0)
        * (∑ y ∈ jsp87Primes X, (if y ∣ n then 1 else 0)) := by
          exact Finset.sum_mul _ _ _
    _ = ∑ x ∈ jsp87Primes X, ∑ y ∈ jsp87Primes X,
        (if x ∣ n then 1 else 0) * (if y ∣ n then 1 else 0) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.mul_sum]
    _ = ∑ x ∈ jsp87Primes X, ∑ y ∈ jsp87Primes X,
        (if x ∣ n ∧ y ∣ n then 1 else 0) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          refine Finset.sum_congr rfl fun y hy => ?_
          by_cases hy' : y ∣ n
          · have key : (if x ∣ n then 1 else 0) * (if y ∣ n then 1 else 0)
              = (if x ∣ n ∧ y ∣ n then 1 else 0) := by
              rw [if_pos hy']
              by_cases hx' : x ∣ n
              · rw [if_pos hx', if_pos (And.intro hx' hy')]
              · rw [ite_eq_right hx', ite_eq_right (fun h => hx' h.1)]
            rw [key]
          · have key : (if x ∣ n then 1 else 0) * (if y ∣ n then 1 else 0) = 0 := by
              rw [ite_eq_right hy', Nat.mul_zero]
            have key2 : (0 : ℕ) = (if x ∣ n ∧ y ∣ n then 1 else 0) := by
              rw [ite_eq_right (fun h => hy' h.2)]
            rw [key]
            exact key2

/-! ## 2. Counting the double sum prime pair by prime pair -/

/-- The equivalence `p ∣ n ∧ q ∣ n ↔ p * q ∣ n` for DISTINCT primes. -/
theorem jsp87_pair_dvd_iff {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p ∣ n ∧ q ∣ n) ↔ (p * q ∣ n) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := And.right h
    have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
    have hpn : p ∣ n := And.left h
    have hpb : p ∣ b := hc.dvd_mul_left.mp (show p ∣ q * b from by rw [← hb]; exact hpn)
    obtain ⟨c, hc'⟩ := hpb
    refine ⟨c, ?_⟩
    have h1 : q * b = q * (p * c) := by rw [← hc']
    rw [hb, h1]; ring
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨⟨q * c, by rw [hc]; ring⟩, ⟨p * c, by rw [hc]; ring⟩⟩

/-- The number of `n ∈ [1, X]` with `p ∣ n` and `q ∣ n`, for DISTINCT primes
`p, q`: it is `⌊X/(p q)⌋`, the exact count of multiples of `p q`. -/
theorem jsp87_card_pair {X p q : ℕ} (_hX : 1 ≤ X) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    ((Finset.Icc 1 X).filter (fun n => p ∣ n ∧ q ∣ n)).card = X / (p * q) := by
  have key : (Finset.Icc 1 X).filter (fun n => p ∣ n ∧ q ∣ n)
      = (Finset.Icc 1 X).filter (fun n => p * q ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨And.left h, (jsp87_pair_dvd_iff hp hq hne).mp ⟨And.left (And.right h),
        And.right (And.right h)⟩⟩
    · intro h
      exact ⟨And.left h, (jsp87_pair_dvd_iff hp hq hne).mpr (And.right h)⟩
  rw [key]
  have h' := Nat.card_multiples' X (p * q)
  have key : (Finset.Icc 1 X).filter (fun n => p * q ∣ n)
      = (Finset.range X.succ).filter (fun n => n ≠ 0 ∧ p * q ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [key, h']

/-- The number of `n ∈ [1, X]` divisible by `d`: `⌊X/d⌋`. -/
theorem jsp87_card_Icc_dvd (X d : ℕ) (_hX : 1 ≤ X) :
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card = X / d := by
  have h' := Nat.card_multiples' X d
  have key : (Finset.Icc 1 X).filter (fun n => d ∣ n)
      = (Finset.range X.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [key, h']









/-! ## 4. THE MAIN THEOREM -/

/-- **SPLITTING A SUM OVER A FINESET AT A SINGLE POINT.**  For any `f` and any
`p`, `∑_{q ∈ t} f q` is the sum of `f` over `{q ∈ t | q = p}` plus the sum over
`{q ∈ t | q ≠ p}`.  This is the finset form of the `C(m,2)` identity and is what
separates the diagonal `p = q` of the second-moment double sum from the
off-diagonal. -/
theorem jsp87_sum_split_at (t : Finset ℕ) (p : ℕ) (f : ℕ → ℕ) :
    (∑ q ∈ t, f q) = (∑ q ∈ t.filter (fun q => q = p), f q)
        + ∑ q ∈ t.filter (fun q => q ≠ p), f q := by
  have key : (t.filter (fun q => q = p)) ∪ (t.filter (fun q => q ≠ p)) = t := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    by_cases h : q = p <;> simp [h]
  have hd : Disjoint (t.filter (fun q => q = p)) (t.filter (fun q => q ≠ p)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
  have hsu : (∑ q ∈ t.filter (fun q => q = p), f q)
      + ∑ q ∈ t.filter (fun q => q ≠ p), f q = ∑ q ∈ t, f q := by
    have h := Finset.sum_union (s₁ := t.filter (fun q => q = p))
      (s₂ := t.filter (fun q => q ≠ p)) (f := f) hd
    rw [key] at h
    exact h.symm
  exact hsu.symm
/-! ## 4. THE MAIN THEOREM: the second moment is first moment plus twice the
      pair content -/


/-- **COUNTING THE DIVISORS, MINUS ONE.**  For a finset `t` containing `p`, the
number of `q ∈ t`, `q ≠ p`, with `q ∣ n` is the total number of divisors in `t`
minus the contribution of `p` itself.  This is the finset form of removing one
element from a count. -/
theorem jsp87_dvd_count_neq (t : Finset ℕ) (p n : ℕ) (hp : p ∈ t) :
    ((t.filter (fun q => q ≠ p)).sum (fun q => if q ∣ n then 1 else 0))
      = (t.sum (fun q => if q ∣ n then 1 else 0)) - (if p ∣ n then 1 else 0) := by
  have hsplit := jsp87_sum_split_at t p (fun q => if q ∣ n then 1 else 0)
  have hsub : (t.filter (fun q => q = p)) = {p} := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hz).2
    · intro hz
      rw [Finset.mem_filter]
      exact ⟨by rw [Finset.mem_singleton.mp hz]; exact hp, Finset.mem_singleton.mp hz⟩
  have hd : ((t.filter (fun q => q = p)).sum (fun q => if q ∣ n then 1 else 0))
      = (if p ∣ n then 1 else 0) := by
    rw [hsub, Finset.sum_singleton]
  rw [hsplit, hd]
  by_cases h : p ∣ n
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    omega


end JSP87
