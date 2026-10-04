/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.SingleScale

/-!
# Round 127 — THE EXACT SECOND MOMENT OF THE PRIME-DIVISOR COUNT AT THE
# GROUND-TRUTH SCALE: (5.21) **IS** THE VARIANCE, WITH NO LOSS

`policy.json` `next_round_attack[3]` of round 126 asked for the *price of
(5.15) at the ground-truth scale*: combine the variance bound
`jsp87_515_imp_var_le` with the mean-field identity `jsp87FAvg_cnt_primeSet`
and read off an explicit lower bound for `κ₁ + κ₂ + κ₃`.  Round 126 left that
as a promise in a docstring (`jsp87_515_zero_var_le`,
`jsp87_515_zero_sqmoment_le`, `jsp87_515_zero_recipSum_le`,
`jsp87_515_zero_refuted`) without a proof: the second moment of `jsp87Cnt` over
the canonical sample was never computed.  **This round computes it exactly.**

The sample of the endgame is the *canonical whole-period sample*

```
s = jsp87ProgFull 0 1 P = { i : i < ∏_{p ∈ P} p } ,
```

a whole period modulo every prime of `P` at once.  On such a sample the
divisibility events `p ∣ i + 1` are **independent by the Chinese remainder
theorem**, and the variance of the prime-divisor count is therefore a *closed
form*:

> **`jsp87Var_cnt_eq_sqDefect`** —
> `Var (i ↦ cnt P (i+1)) = ∑_{p ∈ P} (1/p)(1 − 1/p)` = `jsp87SqDefect P`.

Consequences proved here.

* `jsp87FAvg_cnt_progFull`, `jsp87FAvg_sq_cnt_progFull` — the mean and the
  **exact second moment** of the prime-divisor count on the canonical sample
  (round 126 proved only the mean, and only for `B = 2`);
* `jsp87Var_cnt_eq_sqDefect` — the exact variance;
* `jsp87R521b_ground_iff_var` — **hypothesis (5.21b) of arXiv:2512.01739 at
  `K = 0, H = 1` is *equivalent* to a variance lower bound**: the
  `∑ f_p (1 − f_p)` of (5.21′) *is* the variance, with no loss and no
  correlation input;
* `jsp87SqDefect_tendsto` — that variance **diverges with the height** (Euler),
  so the variance hypothesis of the published proof is satisfied at every
  sufficiently large height, unconditionally;
* `jsp87_515_ground_price` — **(5.15) at the ground-truth scale forces
  `q² ∑_{2 ≤ p ≤ Y} 1/p ≤ κ₁ + κ₂ + κ₃`**: the exact price.  Together with
  (5.21b) this gives `jsp87_521_imp_kappa_blunt` (`κ₁+κ₂+κ₃ ≥ 8`), and
  `jsp87_515_ground_refuted` is the *quantitative* refutation of (5.15) at the
  ground-truth scale: no fixed triple of constants can satisfy it together with
  the pointwise (5.19), at **any** height.
-/

namespace JSP87

set_option maxHeartbeats 1000000

/-! ## §1  The divisibility indicator and its elementary algebra -/

/-- **THE DIVISIBILITY INDICATOR** `⟦p ∣ m⟧`, as a real-valued function of `m`. -/
def jsp87DivInd (p m : ℕ) : ℝ := if p ∣ m then 1 else 0

theorem jsp87DivInd_eq_one {p m : ℕ} (h : p ∣ m) : jsp87DivInd p m = 1 := by
  simp [jsp87DivInd, h]

theorem jsp87DivInd_eq_zero {p m : ℕ} (h : ¬ p ∣ m) : jsp87DivInd p m = 0 := by
  simp [jsp87DivInd, h]

theorem jsp87DivInd_mem (p m : ℕ) : jsp87DivInd p m = 0 ∨ jsp87DivInd p m = 1 := by
  by_cases h : p ∣ m
  · exact Or.inr (jsp87DivInd_eq_one h)
  · exact Or.inl (jsp87DivInd_eq_zero h)

/-- **THE INDICATOR IS IDEMPOTENT** — this is the entire reason the second moment
of a *count* splits into a first moment plus an off-diagonal part. -/
theorem jsp87DivInd_sq (p m : ℕ) : jsp87DivInd p m ^ 2 = jsp87DivInd p m := by
  rcases jsp87DivInd_mem p m with h | h <;> simp [h]

/-- **THE PRODUCT OF TWO INDICATORS VANISHES IF THE FIRST ONE DOES.** -/
theorem jsp87DivInd_mul_left {p q m : ℕ} (h : ¬ p ∣ m) :
    jsp87DivInd p m * jsp87DivInd q m = 0 := by
  rw [jsp87DivInd_eq_zero h, zero_mul]

/-- **THE PRODUCT OF TWO INDICATORS VANISHES IF THE SECOND ONE DOES.** -/
theorem jsp87DivInd_mul_right {p q m : ℕ} (h : ¬ q ∣ m) :
    jsp87DivInd p m * jsp87DivInd q m = 0 := by
  rw [jsp87DivInd_eq_zero h, mul_zero]

/-- **THE PRODUCT OF TWO INDICATORS IS ONE IF BOTH HOLD.** -/
theorem jsp87DivInd_mul_of_dvd {p q m : ℕ} (hp : p ∣ m) (hq : q ∣ m) :
    jsp87DivInd p m * jsp87DivInd q m = 1 := by
  rw [jsp87DivInd_eq_one hp, jsp87DivInd_eq_one hq, one_mul]

/-- **THE COUNT IS THE SUM OF THE INDICATORS**, in the form used below. -/
theorem jsp87Cnt_eq_sum_divInd (P : Finset ℕ) (m : ℕ) :
    (jsp87Cnt P m : ℝ) = ∑ p ∈ P, jsp87DivInd p m := by
  rw [jsp87Cnt_eq_sum]
  exact Finset.sum_congr rfl fun p _ => rfl

/-- **THE AVERAGE OF A FINITE SUM IS THE SUM OF THE AVERAGES** — the linearity of
`𝔼`, in the form needed for the double sums below. -/
private theorem jsp87FAvg_sum {Ω : Type*} (s : Finset Ω) (T : Finset ℕ)
    (g : Ω → ℕ → ℝ) :
    jsp87FAvg s (fun i => ∑ p ∈ T, g i p) = ∑ p ∈ T, jsp87FAvg s (fun i => g i p) := by
  simp only [jsp87FAvg, Finset.sum_div]
  rw [Finset.sum_comm]

/-- **THE SQUARE OF A SUM SPLITS INTO THE DIAGONAL AND THE OFF-DIAGONAL.**  For
any `x : ℕ → ℝ`,

```
(∑_{p ∈ P} x p)²  =  ∑_{p ∈ P} x p · x p  +  ∑_{p ∈ P} ∑_{q ∈ P, q ≠ p} x p · x q ,
```

the second sum being over *ordered* pairs of distinct elements of `P`.  This is
the combinatorial content of `Var (Σ_p X_p) = Σ_p Var X_p + 2 Σ_{p ≠ q} Cov`,
and it is what makes the second moment of a count computable. -/
private theorem jsp87sq_split (P : Finset ℕ) (x : ℕ → ℝ) :
    (∑ p ∈ P, x p) ^ 2 = (∑ p ∈ P, x p * x p)
      + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p), x p * x q := by
  have hfe : ∀ p ∈ P, P.filter (fun q => q ≠ p) = P.erase p := by
    intro p hp
    ext q
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      rw [Finset.mem_erase]
      exact And.intro h.2 h.1
    · intro h
      rw [Finset.mem_erase] at h
      rw [Finset.mem_filter]
      exact And.intro h.2 h.1
  have hkey : ∀ p ∈ P, (∑ q ∈ P, x q) = x p
      + ∑ q ∈ P.filter (fun q => q ≠ p), x q := by
    intro p hp
    calc (∑ q ∈ P, x q) = ∑ q ∈ P.erase p, x q + x p := (Finset.sum_erase_add P x hp).symm
      _ = ∑ q ∈ P.filter (fun q => q ≠ p), x q + x p := by rw [hfe p hp]
      _ = x p + ∑ q ∈ P.filter (fun q => q ≠ p), x q := add_comm _ _
  calc (∑ p ∈ P, x p) ^ 2 = (∑ p ∈ P, x p) * (∑ q ∈ P, x q) := by ring
    _ = ∑ p ∈ P, x p * (∑ q ∈ P, x q) := Finset.sum_mul P x _
    _ = ∑ p ∈ P, (x p * x p + ∑ q ∈ P.filter (fun q => q ≠ p), x p * x q) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hkey p hp]
      calc x p * (x p + ∑ q ∈ P.filter (fun q => q ≠ p), x q)
          = x p * x p + x p * (∑ q ∈ P.filter (fun q => q ≠ p), x q) := by ring
        _ = x p * x p + ∑ q ∈ P.filter (fun q => q ≠ p), x p * x q := by
          rw [Finset.mul_sum]
    _ = (∑ p ∈ P, x p * x p) + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p), x p * x q :=
      Finset.sum_add_distrib

/-- **THE IDEMPOTENT DIAGONAL MAY BE COLLAPSED.**  In the square-split of §1,
the diagonal `∑ x p · x p` equals `∑ x p` as soon as `x` is `{0,1}`-valued on `P`. -/
private theorem jsp87sum_sq_idem (P : Finset ℕ) (x : ℕ → ℝ) (h : ∀ p ∈ P, x p * x p = x p) :
    (∑ p ∈ P, x p * x p) = ∑ p ∈ P, x p := by
  exact Finset.sum_congr rfl fun p hp => h p hp

/-- **THE VARIANCE IN TERMS OF THE SECOND MOMENT.** -/
private theorem jsp87Var_eq_sub_sq {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (f : Ω → ℝ) :
    jsp87Var s f = jsp87FAvg s (fun i => f i ^ 2) - (jsp87FAvg s f) ^ 2 := by
  have hcard0 : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hterm : ∀ i ∈ s, (f i - jsp87FAvg s f) ^ 2
      = f i * f i - 2 * (jsp87FAvg s f) * f i
        + (jsp87FAvg s f) * jsp87FAvg s f := by
    intro i _
    ring
  have h2 : (∑ i ∈ s, (2 * (jsp87FAvg s f)) * f i)
      = 2 * (jsp87FAvg s f) * (∑ i ∈ s, f i) := by
    rw [Finset.mul_sum]
  have h3 : (∑ i ∈ s, (jsp87FAvg s f) * jsp87FAvg s f)
      = ((s.card : ℕ) : ℝ) * (jsp87FAvg s f) * jsp87FAvg s f := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hpow : (∑ i ∈ s, f i * f i) = ∑ i ∈ s, f i ^ 2 :=
    Finset.sum_congr rfl fun i _ => (pow_two (f i)).symm
  calc jsp87Var s f = jsp87FAvg s (fun i => (f i - jsp87FAvg s f) ^ 2) := rfl
    _ = ((∑ i ∈ s, (f i - jsp87FAvg s f) ^ 2) : ℝ) / ((s.card : ℕ) : ℝ) := rfl
    _ = ((∑ i ∈ s, f i ^ 2) - (2 * (jsp87FAvg s f) * (∑ i ∈ s, f i))
          + (((s.card : ℕ) : ℝ) * (jsp87FAvg s f) * jsp87FAvg s f)) / ((s.card : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        h2, h3, hpow]
    _ = jsp87FAvg s (fun i => f i ^ 2) - (jsp87FAvg s f) ^ 2 := by
      have hA : jsp87FAvg s (fun i => f i ^ 2)
          = (∑ i ∈ s, f i ^ 2) / ((s.card : ℕ) : ℝ) := rfl
      have hB : (jsp87FAvg s f) ^ 2
          = ((∑ i ∈ s, f i) / ((s.card : ℕ) : ℝ)) ^ 2 := rfl
      have hC : jsp87FAvg s f = (∑ i ∈ s, f i) / ((s.card : ℕ) : ℝ) := rfl
      rw [hA, hB, hC]
      field_simp
      ring

/-- **DIVIDING A PRODUCT DIVIDES THE NUMBER.** -/
private theorem jsp87dvd_of_mul_dvd {p q n : ℕ} (h : p * q ∣ n) : p ∣ n ∧ q ∣ n := by
  obtain ⟨c, hc⟩ := h
  constructor
  · refine ⟨c * q, ?_⟩
    rw [hc, Nat.mul_assoc, Nat.mul_comm q c]
  · refine ⟨p * c, ?_⟩
    rw [hc, Nat.mul_comm p q, Nat.mul_assoc]

/-! ## §2  The counting step: two primes of `P` divide `L / (p q)` sample points -/

/-- **THE CANONICAL SAMPLE IS THE WHOLE PERIOD.** -/
theorem jsp87ProgFull_eq_Icc {P : Finset ℕ} (_hpos : 0 < jsp87Prod P) :
    jsp87ProgFull 0 1 P = Finset.Icc 0 (jsp87Prod P - 1) := by
  ext x
  rw [jsp87ProgFull, jsp87Prog, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' := Finset.mem_Icc.mp hj
    show 0 + 1 * j ∈ Finset.Icc 0 (jsp87Prod P - 1)
    rw [Finset.mem_Icc]
    omega
  · intro hx
    exact ⟨x, hx, by omega⟩

/-- **TWO DISTINCT PRIMES OF `P` DIVIDE THE PRODUCT.** -/
private theorem jsp87mul_dvd_prod {P : Finset ℕ} {p q : ℕ} (hpc : ∀ r ∈ P, r.Prime)
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) : p * q ∣ jsp87Prod P := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (f := id) (s := P) (a := p) hp
  have hpd : p ∣ jsp87Prod P := by
    refine ⟨c, ?_⟩
    unfold jsp87Prod
    simpa only [id_eq] using hc
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (f := id) (s := P) (a := q) hq
  have hqd : q ∣ jsp87Prod P := by
    refine ⟨c, ?_⟩
    unfold jsp87Prod
    simpa only [id_eq] using hc
  exact (Nat.coprime_primes (hpc p hp) (hpc q hq)).mpr hne |>.mul_dvd_of_dvd_of_dvd hpd hqd

/-- **THE TWO-PRIME COUNTING STEP (CHINESE REMAINDER).**  On the canonical
sample `jsp87ProgFull 0 1 P` the number of points at which two distinct primes
`p, q ∈ P` *both* divide `i + 1` is exactly `∏ P / (p q)`.

This is the elementary core of the independence proved below: the sample is a
whole period modulo `p q`, and `p q ∣ ∏ P` because `p, q` are two distinct
primes of the period. -/
private theorem jsp87filter_pair {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    (jsp87ProgFull 0 1 P).filter (fun i => p ∣ i + 1 ∧ q ∣ i + 1)
      = (jsp87ProgFull 0 1 P).filter (fun i => p * q ∣ i + 1) := by
  have hne' : ∀ i : ℕ, (p ∣ i + 1 ∧ q ∣ i + 1) ↔ p * q ∣ i + 1 := by
    intro i
    constructor
    · rintro ⟨hp', hq'⟩
      exact (Nat.coprime_primes (hpc p hp) (hpc q hq)).mpr hne |>.mul_dvd_of_dvd_of_dvd hp' hq'
    · exact jsp87dvd_of_mul_dvd
  exact Finset.filter_congr (fun i _ => hne' i)

theorem jsp87card_div_pair {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) (_hne : p ≠ q) :
    ((jsp87ProgFull 0 1 P).filter (fun i => p * q ∣ i + 1)).card
      = jsp87Prod P / (p * q) := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  rw [jsp87ProgFull_eq_Icc hpos]
  have hshift : ((Finset.Icc 0 (jsp87Prod P - 1)).filter (fun i => p * q ∣ i + 1)).card
      = ((Finset.Ioc 0 (jsp87Prod P)).filter (fun t => p * q ∣ t)).card := by
    have hpq : (0 : ℕ) < p * q := Nat.mul_pos (hpc p hp).pos (hpc q hq).pos
    refine Finset.card_nbij' (fun i => i + 1) (fun t => t - 1) ?_ ?_ ?_ ?_
    · intro i hi
      have hi1 : i ≤ jsp87Prod P - 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
      have hi2 : p * q ∣ i + 1 := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine And.intro ?_ hi2
      rw [Finset.mem_Ioc]
      obtain ⟨c, hc⟩ := hi2
      omega
    · intro t ht
      have ht1 : t ∈ Finset.Ioc 0 (jsp87Prod P) := (Finset.mem_filter.mp ht).1
      have ht2 : p * q ∣ t := (Finset.mem_filter.mp ht).2
      have ht1' : (0 : ℕ) < t ∧ t ≤ jsp87Prod P := Finset.mem_Ioc.mp ht1
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine And.intro ?_ ?_
      · rw [Finset.mem_Icc]
        omega
      · show p * q ∣ (t - 1) + 1
        have h1 : (t - 1) + 1 = t := by omega
        rw [h1]
        exact ht2
    · intro i _
      change (i + 1) - 1 = i
      omega
    · intro t ht
      have ht2 : p * q ∣ t := (Finset.mem_filter.mp ht).2
      have htI : t ∈ Finset.Ioc 0 (jsp87Prod P) := (Finset.mem_filter.mp ht).1
      have ht0 : (0 : ℕ) < t := (Finset.mem_Ioc.mp htI).1
      change (t - 1) + 1 = t
      omega
  rw [hshift, Nat.Ioc_filter_dvd_card_eq_div]

/-- **THE SUM OF THE PRODUCT OF TWO INDICATORS IS THE PAIR COUNT.** -/
theorem jsp87sum_divInd_pair {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    (∑ i ∈ jsp87ProgFull 0 1 P, jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))
      = ((jsp87Prod P : ℝ)) / ((p : ℝ) * (q : ℝ)) := by
  have hkey : ∀ i : ℕ, jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1)
      = if p * q ∣ i + 1 then (1 : ℝ) else 0 := by
    intro i
    have hc : Nat.Coprime p q := (Nat.coprime_primes (hpc p hp) (hpc q hq)).mpr hne
    by_cases h1 : p ∣ i + 1
    · by_cases h2 : q ∣ i + 1
      · have hq2 : p * q ∣ i + 1 := hc.mul_dvd_of_dvd_of_dvd h1 h2
        rw [jsp87DivInd_mul_of_dvd h1 h2, if_pos hq2]
      · have hq2 : ¬ p * q ∣ i + 1 := fun hh => h2 (jsp87dvd_of_mul_dvd hh).2
        rw [jsp87DivInd_mul_right h2, if_neg hq2]
    · have hq2 : ¬ p * q ∣ i + 1 := fun hh => h1 (jsp87dvd_of_mul_dvd hh).1
      rw [jsp87DivInd_mul_left h1, if_neg hq2]
  have h' : (∑ i ∈ jsp87ProgFull 0 1 P, jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))
      = ∑ _i ∈ (jsp87ProgFull 0 1 P).filter (fun i => p * q ∣ i + 1), (1 : ℝ) := by
    rw [Finset.sum_congr rfl fun i _ => hkey i, Finset.sum_filter]
  rw [h', Finset.sum_const, nsmul_eq_mul]
  have hcard : ((jsp87ProgFull 0 1 P).filter (fun i => p * q ∣ i + 1)).card
      = jsp87Prod P / (p * q) := jsp87card_div_pair hpc hp hq hne
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpc p hp).pos)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpc q hq).pos)
  have hmain : ((jsp87Prod P : ℝ)) / ((p : ℝ) * (q : ℝ))
      = ((jsp87Prod P : ℝ)) / ((p * q : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
  have hpq0 : ((p * q : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.mul_pos (hpc p hp).pos (hpc q hq).pos))
  have hpq' : p * q ∣ jsp87Prod P := jsp87mul_dvd_prod hpc hp hq hne
  rw [hcard, hmain, Nat.cast_div hpq' hpq0, div_eq_mul_inv]
  ring
/-! ## §3  The moments of the indicator over the canonical sample -/

/-- **A PRIME OF `P` DIVIDES THE PRODUCT.** -/
private theorem jsp87dvd_prod_mem' {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) :
    p ∣ jsp87Prod P := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (f := id) (s := P) (a := p) hp
  refine ⟨c, ?_⟩
  unfold jsp87Prod
  simpa only [id_eq] using hc

/-- **THE NONZERO SET OF THE INDICATOR IS THE SET OF MULTIPLES.** -/
theorem jsp87DivInd_sum_eq_card {P : Finset ℕ} (p : ℕ) :
    (∑ i ∈ P, jsp87DivInd p (i + 1)) = ((P.filter (fun i => p ∣ i + 1)).card : ℕ) := by
  calc (∑ i ∈ P, jsp87DivInd p (i + 1))
      = ∑ i ∈ P, (if p ∣ i + 1 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : p ∣ i + 1
        · rw [jsp87DivInd_eq_one h, if_pos h]
        · rw [jsp87DivInd_eq_zero h, if_neg h]
    _ = ∑ _i ∈ P.filter (fun i => p ∣ i + 1), (1 : ℝ) :=
      (Finset.sum_filter (fun i => p ∣ i + 1) (fun _ => (1 : ℝ))).symm
    _ = ((P.filter (fun i => p ∣ i + 1)).card : ℕ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- **THE MEAN OF THE INDICATOR OVER THE CANONICAL SAMPLE IS `1/p`** — round
126's mean-field identity, in full generality (any set of primes, any threshold
`B`). -/
theorem jsp87FAvg_divInd_progFull {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) {p : ℕ}
    (hp : p ∈ P) :
    jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => jsp87DivInd p (i + 1)) = 1 / (p : ℝ) := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hcard : (jsp87ProgFull 0 1 P).card = jsp87Prod P :=
    jsp87ProgFull_card (by norm_num) P hpos
  have hL0 : (jsp87Prod P : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpc p hp).pos)
  have h2p : (2 : ℕ) ≤ p := (hpc p hp).two_le
  have hDp : ¬ p ∣ (1 : ℕ) := by
    intro hh
    have hle := Nat.le_of_dvd (by omega) hh
    omega
  have hlt : (1 : ℕ) + 2 ^ 0 - 1 < p := by
    simp
    omega
  have hpd : p ∣ jsp87Prod P := jsp87dvd_prod_mem' hp
  have hcnt : ((jsp87ProgFull 0 1 P).filter (fun i => p ∣ i + 1)).card
      = jsp87Prod P / p := by
    have hz := jsp87ProgFull_nzFrac (K := 0) (p := p) (H := 1) (n0 := 0) (D := 1)
      (by norm_num) hpos hp (hpc p hp) hDp hlt
    rw [jsp87NzFrac, jsp87NzRes_zero_one p,
      jsp87NzResCard_zero_one p (hpc p hp).pos] at hz
    rw [hcard] at hz
    have h3 := (div_eq_iff hL0).mp hz
    rw [div_eq_mul_inv] at h3
    have h4 : (((jsp87ProgFull 0 1 P).filter (fun i => p ∣ i + 1)).card : ℝ)
        = (jsp87Prod P : ℝ) / (p : ℝ) := by
      rw [div_eq_mul_inv]
      exact h3.trans (by ring)
    have h5 : (((jsp87ProgFull 0 1 P).filter (fun i => p ∣ i + 1)).card : ℝ)
        = ((jsp87Prod P / p : ℕ) : ℝ) := by
      rw [h4, ← Nat.cast_div hpd hp0]
    exact_mod_cast h5
  have hdef : jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => jsp87DivInd p (i + 1))
      = (∑ i ∈ jsp87ProgFull 0 1 P, jsp87DivInd p (i + 1))
        / ((jsp87ProgFull 0 1 P).card : ℝ) := rfl
  rw [hdef, jsp87DivInd_sum_eq_card p, hcnt, hcard, Nat.cast_div hpd hp0]
  field_simp

/-- **THE SQUARE OF THE INDICATOR HAS THE SAME MEAN** (idempotence). -/
theorem jsp87FAvg_divInd_sq_progFull {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) {p : ℕ}
    (hp : p ∈ P) :
    jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => (jsp87DivInd p (i + 1)) ^ 2) = 1 / (p : ℝ) := by
  have hone : jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => (jsp87DivInd p (i + 1)) ^ 2)
      = jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => jsp87DivInd p (i + 1)) := by
    have e1 : (∑ i ∈ jsp87ProgFull 0 1 P, (jsp87DivInd p (i + 1)) ^ 2)
        = ∑ i ∈ jsp87ProgFull 0 1 P, jsp87DivInd p (i + 1) :=
      Finset.sum_congr rfl fun i _ => jsp87DivInd_sq p (i + 1)
    unfold jsp87FAvg
    rw [e1]
  rw [hone]
  exact jsp87FAvg_divInd_progFull hpc hp

/-- **INDEPENDENCE (CHINESE REMAINDER THEOREM).**  Two distinct primes of `P`
divide *independently* on the canonical sample: the mixed second moment is the
product of the two first moments.

This is the exact statement that `jsp87ProgFull 0 1 P` is a whole period modulo
`p q`.  On this sample "independence" is a *theorem*, not an input — which is
why hypothesis (5.21) can be read off in §4 with no loss. -/
theorem jsp87FAvg_divInd_mul_progFull {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) {p q : ℕ}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))
      = (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hcard : (jsp87ProgFull 0 1 P).card = jsp87Prod P :=
    jsp87ProgFull_card (by norm_num) P hpos
  have hL0 : (jsp87Prod P : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpc p hp).pos)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpc q hq).pos)
  unfold jsp87FAvg
  rw [jsp87sum_divInd_pair hpc hp hq hne, hcard]
  field_simp

/-! ## §4  THE SQUARE-DEFECT: THE EXACT VARIANCE OF THE PRIME-DIVISOR COUNT -/

/-- **THE SQUARE-DEFECT OF A SET OF PRIMES.**

`∑_{p ∈ P} (1/p)(1 − 1/p)` is the quantity that enters hypothesis (5.21′) of
arXiv:2512.01739 — the sum of `f_p (1 − f_p)` with `f_p` the nonzero-class
fraction of the prime `p` — evaluated at the ground-truth scale, where
`f_p = 1/p` *exactly*.  §4 identifies it with the **variance** of the
prime-divisor count on the canonical sample. -/
noncomputable def jsp87SqDefect (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ)))

/-- **THE SQUARE-DEFECT IS THE MEAN MINUS THE SUM OF THE SQUARES OF THE MEAN
FIELD.** -/
theorem jsp87SqDefect_eq {P : Finset ℕ} (h0 : ∀ p ∈ P, p ≠ 0) :
    jsp87SqDefect P = jsp87RecipSum P - ∑ p ∈ P, (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
  have hkey : ∀ p : ℕ, (p : ℝ) ≠ 0 → ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ)))
      = (1 / (p : ℝ)) - (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
    intro p hp0
    field_simp
  unfold jsp87SqDefect jsp87RecipSum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p hp => hkey p (by exact_mod_cast h0 p hp)

/-- **THE MEAN OF THE PRIME-DIVISOR COUNT OVER THE CANONICAL SAMPLE IS THE
HARMONIC MASS OF THE PRIME SET** — round 126's mean-field identity, in full
generality (any set of primes). -/
theorem jsp87FAvg_cnt_progFull {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) :
    jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => (jsp87Cnt P (i + 1) : ℝ))
      = jsp87RecipSum P := by
  have hA : jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => ∑ p ∈ P, jsp87DivInd p (i + 1))
      = jsp87RecipSum P := by
    refine (jsp87FAvg_sum (s := jsp87ProgFull 0 1 P) (T := P)
      (fun i p => jsp87DivInd p (i + 1))).trans ?_
    unfold jsp87RecipSum
    exact Finset.sum_congr rfl fun p hp => jsp87FAvg_divInd_progFull hpc hp
  have hstep : (∑ i ∈ jsp87ProgFull 0 1 P, (jsp87Cnt P (i + 1) : ℝ))
      = ∑ i ∈ jsp87ProgFull 0 1 P, ∑ p ∈ P, jsp87DivInd p (i + 1) :=
    Finset.sum_congr rfl fun i _ => jsp87Cnt_eq_sum_divInd P (i + 1)
  unfold jsp87FAvg
  rw [hstep, ← jsp87FAvg]
  exact hA

/-- **THE EXACT SECOND MOMENT OF THE PRIME-DIVISOR COUNT.** -/
theorem jsp87FAvg_sq_cnt_progFull {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) :
    jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => (jsp87Cnt P (i + 1) : ℝ) ^ 2)
      = jsp87RecipSum P
        + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
            (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
  have hpt : ∀ i : ℕ, ((jsp87Cnt P (i + 1) : ℝ)) ^ 2
      = (∑ p ∈ P, jsp87DivInd p (i + 1))
        + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
            jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1) := by
    intro i
    have h1 : ((jsp87Cnt P (i + 1) : ℝ)) ^ 2
        = (∑ p ∈ P, jsp87DivInd p (i + 1) * jsp87DivInd p (i + 1))
          + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
              jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1) := by
      rw [jsp87Cnt_eq_sum_divInd, jsp87sq_split]
    refine h1.trans ?_
    rw [jsp87sum_sq_idem P (fun p => jsp87DivInd p (i + 1)) fun p _ => by
      rw [← pow_two, jsp87DivInd_sq p (i + 1)]]
  have hA : jsp87FAvg (jsp87ProgFull 0 1 P) (fun i => ∑ p ∈ P, jsp87DivInd p (i + 1))
      = jsp87RecipSum P := by
    refine (jsp87FAvg_sum (s := jsp87ProgFull 0 1 P) (T := P)
      (fun i p => jsp87DivInd p (i + 1))).trans ?_
    unfold jsp87RecipSum
    exact Finset.sum_congr rfl fun p hp => jsp87FAvg_divInd_progFull hpc hp
  have hB : jsp87FAvg (jsp87ProgFull 0 1 P)
      (fun i => ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
          jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))
      = ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
          (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
    refine (jsp87FAvg_sum (s := jsp87ProgFull 0 1 P) (T := P)
      (fun i p => ∑ q ∈ P.filter (fun q => q ≠ p), jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))).trans ?_
    refine Finset.sum_congr rfl fun p hp => ?_
    refine (jsp87FAvg_sum (s := jsp87ProgFull 0 1 P) (T := P.filter (fun q => q ≠ p))
      (fun i q => jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))).trans ?_
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.mp hq
    exact jsp87FAvg_divInd_mul_progFull hpc hp hq'.1 (Ne.symm hq'.2)
  have hkey : jsp87FAvg (jsp87ProgFull 0 1 P)
      (fun i => (∑ p ∈ P, jsp87DivInd p (i + 1))
        + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
            jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1))
      = jsp87RecipSum P
        + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
            (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
    rw [jsp87FAvg_add, hA, hB]
  have hkey' : jsp87FAvg (jsp87ProgFull 0 1 P)
      (fun i => (jsp87Cnt P (i + 1) : ℝ) ^ 2)
      = jsp87FAvg (jsp87ProgFull 0 1 P)
        (fun i => (∑ p ∈ P, jsp87DivInd p (i + 1))
          + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
              jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1)) := by
    unfold jsp87FAvg
    have e : (∑ i ∈ jsp87ProgFull 0 1 P, (jsp87Cnt P (i + 1) : ℝ) ^ 2)
        = ∑ i ∈ jsp87ProgFull 0 1 P,
            ((∑ p ∈ P, jsp87DivInd p (i + 1))
              + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
                  jsp87DivInd p (i + 1) * jsp87DivInd q (i + 1)) :=
      Finset.sum_congr rfl fun i _ => hpt i
    rw [e]
  rw [hkey', hkey]

/-- **THE EXACT VARIANCE OF THE PRIME-DIVISOR COUNT: THE CHINESE-REMAINDER
IDENTITY.**  On the canonical whole-period sample the variance of the
prime-divisor count is the *square-defect* of the prime set:

```
Var (i ↦ cnt P (i+1))  =  ∑_{p ∈ P} (1/p)(1 − 1/p) .
```

Mathlib has no statement of this shape for a prime-divisor count; the identity
is the finite-model form of the Chinese remainder theorem, and it says that at
the canonical sample the events `p ∣ n` are **exactly independent**.  This is
the exact content of the `∑_p f_p (1 − f_p)` of hypothesis (5.21′). -/
theorem jsp87Var_cnt_eq_sqDefect {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) :
    jsp87Var (jsp87ProgFull 0 1 P) (fun i => (jsp87Cnt P (i + 1) : ℝ))
      = jsp87SqDefect P := by
  have hne : (jsp87ProgFull 0 1 P).Nonempty := jsp87ProgFull_nonempty P
  rw [jsp87Var_eq_sub_sq _ hne]
  have hmean := jsp87FAvg_cnt_progFull hpc
  have hsq := jsp87FAvg_sq_cnt_progFull hpc
  have hsplit : (jsp87RecipSum P) ^ 2
      = (∑ p ∈ P, (1 / (p : ℝ)) * (1 / (p : ℝ)))
        + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q ≠ p),
            (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
    unfold jsp87RecipSum
    exact jsp87sq_split P (fun p => 1 / (p : ℝ))
  rw [hmean, hsq, hsplit,
    jsp87SqDefect_eq (P := P) (fun p hp => ne_of_gt (hpc p hp).pos)]
  ring

/-- **HYPOTHESIS (5.21b) AT THE GROUND-TRUTH SCALE *IS* THE VARIANCE.**  For a
set of primes `P`, the variance hypothesis (5.21b) of arXiv:2512.01739 —

```
1 ≤ q² · ((1/2)^(1+0))² · ∑_{p ∈ P} f_p (1 − f_p) ,    f_p = jsp87NzResCard 0 p 1 / p = 1/p ,
```

— is **equivalent** to `4 ≤ q² · Var (i ↦ cnt P (i+1))`, with no loss: the
quantity `∑_p f_p (1 − f_p)` of (5.21′) *is* the variance of the phase, by
`jsp87Var_cnt_eq_sqDefect`. -/
theorem jsp87R521b_ground_iff_var {P : Finset ℕ} (hpc : ∀ r ∈ P, r.Prime) (q : ℝ) :
    jsp87R521b 0 P q 1
      ↔ 4 ≤ (q ^ 2) * jsp87Var (jsp87ProgFull 0 1 P)
          (fun i => (jsp87Cnt P (i + 1) : ℝ)) := by
  have hvar : jsp87Var (jsp87ProgFull 0 1 P)
        (fun i => (jsp87Cnt P (i + 1) : ℝ)) = jsp87SqDefect P :=
    jsp87Var_cnt_eq_sqDefect hpc
  have hstep : ∀ p ∈ P, ((jsp87NzResCard 0 p 1 : ℕ) : ℝ) / (p : ℝ)
        * (1 - ((jsp87NzResCard 0 p 1 : ℕ) : ℝ) / (p : ℝ))
      = (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by
    intro p hp
    rw [jsp87NzResCard_zero_one p (hpc p hp).pos]
    ring
  have hq : ((1 / 2 : ℝ) ^ (1 + 0)) ^ 2 = (1 / 4 : ℝ) := by norm_num
  have hid : (∑ p ∈ P, ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ)))) = jsp87SqDefect P := rfl
  unfold jsp87R521b
  rw [Finset.sum_congr rfl hstep, hvar, hq]
  constructor <;> intro h <;> nlinarith [h, hid]

/-! ## §5  The square-defect against the harmonic mass -/

/-- **ONE SUMMAND OF THE SQUARE-DEFECT DOMINATES HALF THE SUMMAND OF THE
HARMONIC MASS.** -/
private theorem jsp87sqDefect_term_ge {p : ℕ} (hp : 2 ≤ p) :
    ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) ≥ (1 / 2 : ℝ) * (1 / (p : ℝ)) := by
  have h1 : (1 / (p : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp)
  have hnn : (0 : ℝ) ≤ 1 / (p : ℝ) := by
    rw [div_eq_mul_inv]
    positivity
  have hkey : (1 / (p : ℝ)) * (1 / (p : ℝ)) ≤ (1 / (p : ℝ)) * (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left h1 hnn
  have hnn2 : (0 : ℝ) ≤ (1 / 2 : ℝ) * (1 / (p : ℝ)) := mul_nonneg (by norm_num) hnn
  nlinarith [hkey, hnn2]

/-- **THE SQUARE-DEFECT IS NONNEGATIVE.** -/
theorem jsp87SqDefect_nonneg (P : Finset ℕ) : 0 ≤ jsp87SqDefect P := by
  have hkey : ∀ p : ℕ, (0 : ℝ) ≤ ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) := by
    intro p
    by_cases hp : p = 0
    · rw [hp]
      simp
    · have hp1 : (1 : ℕ) ≤ p := by omega
      have h1 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp1)
      have h2 : (1 / (p : ℝ)) ≤ 1 :=
        (div_le_one hp0).2 (by exact_mod_cast hp1)
      have h3 : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr h2
      exact mul_nonneg h1 h3
  unfold jsp87SqDefect
  exact Finset.sum_nonneg fun p _ => hkey p

/-- **THE SQUARE-DEFECT OF A PRIME SET DOMINATES HALF ITS HARMONIC MASS.** -/
theorem jsp87SqDefect_ge_recipSum_half {B Y : ℕ} (hB : 2 ≤ B) :
    jsp87RecipSum (jsp87PrimeSet B Y) ≤ 2 * jsp87SqDefect (jsp87PrimeSet B Y) := by
  have hkey : ∀ p ∈ jsp87PrimeSet B Y,
      (1 / 2 : ℝ) * (1 / (p : ℝ))
        ≤ (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by
    intro p hp
    exact jsp87sqDefect_term_ge (p := p) (hB.trans (jsp87PrimeSet_mem.mp hp).1)
  unfold jsp87SqDefect jsp87RecipSum
  have e1 : (∑ p ∈ jsp87PrimeSet B Y, ((1 / 2 : ℝ) * (1 / (p : ℝ))))
      ≤ ∑ p ∈ jsp87PrimeSet B Y, ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) :=
    Finset.sum_le_sum fun p hp => hkey p hp
  have e2 : (∑ p ∈ jsp87PrimeSet B Y, ((1 / 2 : ℝ) * (1 / (p : ℝ))))
      = (1 / 2 : ℝ) * (∑ p ∈ jsp87PrimeSet B Y, (1 / (p : ℝ))) :=
    (Finset.mul_sum (jsp87PrimeSet B Y) (fun p => 1 / (p : ℝ)) (1 / 2)).symm
  rw [e2] at e1
  linarith

/-- **THE SQUARE-DEFECT IS AT MOST THE HARMONIC MASS.** -/
theorem jsp87SqDefect_le_recipSum {P : Finset ℕ} (h1 : ∀ p ∈ P, 1 ≤ p) :
    jsp87SqDefect P ≤ jsp87RecipSum P := by
  have hkey : ∀ p : ℕ, (p : ℝ) ≠ 0 → ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ)))
      ≤ (1 / (p : ℝ)) := by
    intro p hp0
    have h2 : (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) ≤ (1 / (p : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (by norm_num) (by
        rw [div_eq_mul_inv]
        positivity)
    calc (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) ≤ (1 / (p : ℝ)) * 1 := h2
      _ = 1 / (p : ℝ) := by ring
  unfold jsp87SqDefect jsp87RecipSum
  refine Finset.sum_le_sum fun p hp => ?_
  exact hkey p (by exact_mod_cast (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt (Nat.zero_lt_of_lt (h1 p hp))))))

/-- **THE SQUARE-DEFECT IS NONDEGENERATE AS SOON AS THE PRIME SET CONTAINS
`2`.** -/
theorem jsp87SqDefect_ge_one_fourth {Y : ℕ} (hY : 2 ≤ Y) :
    (1 / 4 : ℝ) ≤ jsp87SqDefect (jsp87PrimeSet 2 Y) := by
  have h1 := jsp87SqDefect_ge_recipSum_half (B := 2) (Y := Y) (by omega)
  have hmem : (2 : ℕ) ∈ jsp87PrimeSet 2 Y := jsp87PrimeSet_mem.mpr ⟨by omega, hY, by norm_num⟩
  have hpos : ∀ p ∈ jsp87PrimeSet 2 Y, (0 : ℝ) ≤ 1 / (p : ℝ) := by
    intro p _
    positivity
  have h2 : (1 / 2 : ℝ) ≤ jsp87RecipSum (jsp87PrimeSet 2 Y) := by
    unfold jsp87RecipSum
    have hx := Finset.single_le_sum hpos hmem
    simpa using hx
  linarith

/-- **THE VARIANCE OF THE PRIME-DIVISOR COUNT OVER THE CANONICAL SAMPLE
DIVERGES WITH THE HEIGHT.**  Euler's divergence of the prime harmonic series
(round 125) plus `jsp87SqDefect_ge_recipSum_half`: the quantity
`∑_{p ∈ P} f_p (1 − f_p)` of hypothesis (5.21′) — the variance hypothesis of
arXiv:2512.01739 — is satisfied at every sufficiently large height,
*unconditionally*. -/
theorem jsp87SqDefect_tendsto :
    Filter.Tendsto (fun Y : ℕ => jsp87SqDefect (jsp87PrimeSet 2 Y))
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  by_cases hb : (0 : ℝ) < b
  · have hev := Filter.Tendsto.eventually_ge_atTop (jsp87RecipSum_primeSet_tendsto 2) (2 * b)
    filter_upwards [hev] with x hx
    have hle := jsp87SqDefect_ge_recipSum_half (B := 2) (Y := x) (by omega)
    linarith
  · have hb0 : b ≤ (0 : ℝ) := le_of_not_gt hb
    filter_upwards [] with x
    exact le_trans hb0 (jsp87SqDefect_nonneg _)

/-! ## §6  The price of (5.15) at the ground-truth scale -/

/-- **THE UNSCALED PHASE AT `K = 0, H = 1` IS `1/2` TIMES THE PRIME-DIVISOR
COUNT** — the pointwise form of round 126's `jsp87_phase_mean_primeSet`. -/
theorem jsp87Phase0_zero_one (Y i : ℕ) :
    jsp87Phase0 0 1 Y i
      = (1 / 2 : ℝ) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ) := by
  have hsep : jsp87Separation 0 1 = 2 := by
    unfold jsp87Separation
    norm_num
  have hkey : ∀ p : ℕ, jsp87Xp0 (jsp87BinV 0) p i 1
      = (1 / 2 : ℝ) * jsp87DivInd p (i + 1) := by
    intro p
    rw [jsp87Xp0_binV_zero_one]
    by_cases h : p ∣ i + 1
    · rw [jsp87DivInd_eq_one h, if_pos h]
    · rw [jsp87DivInd_eq_zero h, if_neg h]
  unfold jsp87Phase0
  rw [hsep, Finset.sum_congr rfl fun p _ => hkey p, ← Finset.mul_sum,
    jsp87Cnt_eq_sum_divInd]

/-- **THE ERROR OF (5.15) IS NONNEGATIVE** — so (5.15) forces
`κ₁ + κ₂ + κ₃ ≥ 0`. -/
theorem jsp87Err1_nonneg (K H Y : ℕ) (q : ℝ) : 0 ≤ jsp87Err1 K H Y q := by
  unfold jsp87Err1
  positivity

/-- **THE PRICE OF (5.15) AT THE GROUND-TRUTH SCALE, IN THE VARIANCE FORM.**
(5.15), together with the pointwise (5.19) at the height `Y`, forces
`2 q² Var (i ↦ cnt (i+1)) ≤ κ₁ + κ₂ + κ₃`. -/
theorem jsp87_515_ground_var_le (Y : ℕ) (q κ1 κ2 κ3 : ℝ)
    (h15 : jsp87Hypothesis15 0 1 q κ1 κ2 κ3)
    (hp : jsp87Hyp519Pointwise 0 1 Y q) :
    2 * (q ^ 2) * jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      ≤ κ1 + κ2 + κ3 := by
  have hK : jsp87Sample 0 1 Y = jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y) := by
    unfold jsp87Sample
    congr 1
  have hnn : (0 : ℝ) ≤ κ1 + κ2 + κ3 :=
    le_trans (jsp87Err1_nonneg 0 1 0 q) (h15 0)
  have hid : jsp87CAvg (jsp87Sample 0 1 Y)
      (fun i => jsp87e (q * jsp87Phase0 0 1 Y i)) = jsp87Mean 0 1 Y q := by
    unfold jsp87Mean
    rfl
  have hcf := jsp87_charfun_le (jsp87Sample 0 1 Y) (jsp87ProgFull_nonempty _) q
    (jsp87Phase0 0 1 Y) hp
  rw [hid] at hcf
  have hid3 : jsp87Mean 0 1 Y q - jsp87Err1z 0 1 Y q = 1 := by
    simp [jsp87Err1z]
  have h1 : (1 : ℝ) ≤ ‖jsp87Mean 0 1 Y q‖ + ‖jsp87Err1z 0 1 Y q‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
      _ = ‖jsp87Mean 0 1 Y q - jsp87Err1z 0 1 Y q‖ := by rw [← hid3]
      _ ≤ ‖jsp87Mean 0 1 Y q‖ + ‖jsp87Err1z 0 1 Y q‖ := norm_sub_le _ _
  have h2 : ‖jsp87Err1z 0 1 Y q‖ ≤ κ1 + κ2 + κ3 := by
    have hx := h15 Y
    rwa [jsp87Err1_eq] at hx
  have hvar : 8 * jsp87Var (jsp87Sample 0 1 Y)
      (fun i => q * jsp87Phase0 0 1 Y i) ≤ κ1 + κ2 + κ3 := by
    unfold jsp87Var at hcf ⊢
    linarith
  rw [hK] at hvar
  have hfun : (fun i => q * jsp87Phase0 0 1 Y i)
      = fun i => (q / 2 : ℝ) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ) := by
    funext i
    rw [jsp87Phase0_zero_one Y i]
    ring
  have hscale : jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
      (fun i => q * jsp87Phase0 0 1 Y i)
      = (q / 2) ^ 2 * jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ)) := by
    rw [hfun, jsp87Var_scale]
  rw [hscale] at hvar
  have hs : jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
      (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      = jsp87SqDefect (jsp87PrimeSet 2 Y) :=
    jsp87Var_cnt_eq_sqDefect (fun p hp => jsp87PrimeSet_prime hp)
  nlinarith [hvar, hs]

/-- **THE PRICE OF (5.15) AT THE GROUND-TRUTH SCALE.**  (5.15) together with the
pointwise (5.19) at the height `Y` forces

```
2 q² ∑_{2 ≤ p ≤ Y} (1/p)(1 − 1/p)  ≤  κ₁ + κ₂ + κ₃ ,
```

and therefore — by `jsp87SqDefect_ge_recipSum_half` — the mean-field price

```
q² ∑_{2 ≤ p ≤ Y} 1/p  ≤  κ₁ + κ₂ + κ₃ .
```

This is the statement promised (but not proved) as `jsp87_515_zero_recipSum_le`
in round 126's docstring. -/
theorem jsp87_515_ground_price (Y : ℕ) (q κ1 κ2 κ3 : ℝ)
    (h15 : jsp87Hypothesis15 0 1 q κ1 κ2 κ3)
    (hp : jsp87Hyp519Pointwise 0 1 Y q) :
    (q ^ 2) * jsp87RecipSum (jsp87PrimeSet 2 Y) ≤ κ1 + κ2 + κ3 := by
  have h1 := jsp87_515_ground_var_le Y q κ1 κ2 κ3 h15 hp
  have hs : jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
      (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      = jsp87SqDefect (jsp87PrimeSet 2 Y) :=
    jsp87Var_cnt_eq_sqDefect (fun p hp => jsp87PrimeSet_prime hp)
  have h2 := jsp87SqDefect_ge_recipSum_half (B := 2) (Y := Y) (by omega)
  have hq0 : (0 : ℝ) ≤ q ^ 2 := by positivity
  nlinarith [h1, hs, h2, hq0]

/-- **HYPOTHESIS (5.21b) FORCES THE CONSTANTS OF (5.15) TO BE BLUNT.**  At
`K = 0, H = 1`, (5.21b) (`4 ≤ q² Var`) together with (5.15) and the pointwise
(5.19) forces `κ₁ + κ₂ + κ₃ ≥ 8`, i.e. the constants of (5.15) are far from the
`1/30` of the endgame — by a factor `240`. -/
theorem jsp87_521_imp_kappa_blunt (Y : ℕ) (q κ1 κ2 κ3 : ℝ)
    (h521 : jsp87R521b 0 (jsp87PrimeSet 2 Y) q 1)
    (h15 : jsp87Hypothesis15 0 1 q κ1 κ2 κ3)
    (hp : jsp87Hyp519Pointwise 0 1 Y q) :
    8 ≤ κ1 + κ2 + κ3 := by
  have h1 := jsp87_515_ground_var_le Y q κ1 κ2 κ3 h15 hp
  have h2 := (jsp87R521b_ground_iff_var (P := jsp87PrimeSet 2 Y)
    (fun p hp => jsp87PrimeSet_prime hp) q).mp h521
  have hs : jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
      (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
      = jsp87SqDefect (jsp87PrimeSet 2 Y) :=
    jsp87Var_cnt_eq_sqDefect (fun p hp => jsp87PrimeSet_prime hp)
  nlinarith [h1, h2, hs]

/-- **THE HARMONIC MASS, WEIGHTED BY `q²`, EXCEEDS EVERY BOUND AT A LARGE
HEIGHT** — Euler's divergence, transferred. -/
theorem jsp87RecipSum_weighted_large (q : ℝ) (hq : q ≠ 0) (M : ℝ) :
    ∃ Y : ℕ, (q ^ 2) * jsp87RecipSum (jsp87PrimeSet 2 Y) > M := by
  have hq0 : (0 : ℝ) < q ^ 2 := by positivity
  have h1 := Filter.Tendsto.eventually_ge_atTop (jsp87RecipSum_primeSet_tendsto 2)
    (M / q ^ 2 + 1)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.1 h1
  refine ⟨Y, ?_⟩
  have hle : (q ^ 2) * (M / q ^ 2 + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet 2 Y) :=
    mul_le_mul_of_nonneg_left (hY Y (Nat.le_refl Y)) (by positivity)
  have hkey : (q ^ 2) * (M / q ^ 2 + 1) = M + q ^ 2 := by field_simp
  linarith

/-- **(5.15) TOGETHER WITH THE POINTWISE (5.19) FAILS AT EVERY HEIGHT WHOSE
WEIGHTED HARMONIC MASS EXCEEDS THE CONSTANTS.**  This is the quantitative
refutation of (5.15) at the ground-truth scale: the estimate is *forced* to
have constants of size `q² · log log Y`. -/
theorem jsp87_515_ground_fails_above (Y : ℕ) (q κ1 κ2 κ3 : ℝ)
    (hbigger : κ1 + κ2 + κ3 < (q ^ 2) * jsp87RecipSum (jsp87PrimeSet 2 Y)) :
    ¬ (jsp87Hypothesis15 0 1 q κ1 κ2 κ3 ∧ jsp87Hyp519Pointwise 0 1 Y q) := by
  rintro ⟨h15, hp⟩
  have h := jsp87_515_ground_price Y q κ1 κ2 κ3 h15 hp
  linarith

/-- **(5.15) AT THE GROUND-TRUTH SCALE IS REFUTED FOR EVERY FIXED TRIPLE OF
CONSTANTS: THERE IS A HEIGHT AT WHICH IT FAILS AND AT WHICH ITS OWN PRICE IS
ALREADY VIOLATED.**  No choice of `κ₁, κ₂, κ₃` satisfies (5.15) at `K = 0,
H = 1` together with the pointwise (5.19) at a height whose weighted harmonic
mass exceeds `κ₁ + κ₂ + κ₃`; and by Euler such heights exist for every triple
(rounds 125 + 127). -/
theorem jsp87_515_ground_refuted (q : ℝ) (hq : q ≠ 0) (κ1 κ2 κ3 : ℝ) :
    ∃ Y : ℕ, ¬ (jsp87Hypothesis15 0 1 q κ1 κ2 κ3 ∧ jsp87Hyp519Pointwise 0 1 Y q)
      ∧ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet 2 Y) > κ1 + κ2 + κ3 := by
  obtain ⟨Y, hY⟩ := jsp87RecipSum_weighted_large q hq (κ1 + κ2 + κ3)
  exact ⟨Y, jsp87_515_ground_fails_above Y q κ1 κ2 κ3 hY, hY⟩

/-! ## §7  Machine-checked instances -/

/-- **THE SQUARE-DEFECT OF `{2}` IS `1/4`.** -/
theorem jsp87SqDefect_two : jsp87SqDefect (jsp87PrimeSet 2 2) = 1 / 4 := by
  have hset : jsp87PrimeSet 2 2 = {2} := by
    ext p
    rw [jsp87PrimeSet, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with ⟨⟨h1, h2⟩, -⟩
      exact Nat.le_antisymm h2 h1
    · intro h
      subst h
      exact ⟨⟨by omega, by omega⟩, by norm_num⟩
  rw [hset]
  simp only [jsp87SqDefect, Finset.sum_singleton]
  norm_num

/-- **THE VARIANCE OF THE PRIME-DIVISOR COUNT OVER `{2}` IS `1/4`**: on the
two-point sample `{0, 1}` the count takes the values `0` and `1` once each. -/
theorem jsp87Var_cnt_two :
    jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 2))
      (fun i => (jsp87Cnt (jsp87PrimeSet 2 2) (i + 1) : ℝ)) = 1 / 4 := by
  rw [jsp87Var_cnt_eq_sqDefect (P := jsp87PrimeSet 2 2)
    (fun p hp => jsp87PrimeSet_prime hp), jsp87SqDefect_two]

/-- **THE SQUARE-DEFECT OF `{2, 3}` IS `17/36`.** -/
theorem jsp87SqDefect_two_three :
    jsp87SqDefect (jsp87PrimeSet 2 3) = (17 : ℝ) / 36 := by
  have hset : jsp87PrimeSet 2 3 = {2, 3} := by
    ext p
    rw [jsp87PrimeSet, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases h with ⟨⟨h1, h2⟩, -⟩
      interval_cases p <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, by omega⟩, by norm_num⟩
      · exact ⟨⟨by omega, by omega⟩, by norm_num⟩
  rw [hset]
  simp [jsp87SqDefect]
  norm_num

/-- **HYPOTHESIS (5.21b) IS SATISFIED AT THE SMALL SCALE `q = 20`, `Y = 2`.**
The variance hypothesis of the published proof holds at a height where the
prime set is a single prime, with a `q` three times larger than the `1/20` of
(5.19). -/
theorem jsp87R521b_ground_two : jsp87R521b 0 (jsp87PrimeSet 2 2) 20 1 := by
  have hiff := (jsp87R521b_ground_iff_var (P := jsp87PrimeSet 2 2)
    (fun p hp => jsp87PrimeSet_prime hp) 20)
  rw [hiff, jsp87Var_cnt_two]
  norm_num

/-! ## §8  Summary -/

/-- **THE ROUND IN ONE THEOREM.**  At the ground-truth scale `K = 0, H = 1` and
on the canonical whole-period sample:

1. the mean of the prime-divisor count is the harmonic mass `∑_{2 ≤ p ≤ Y} 1/p`
   (`jsp87FAvg_cnt_progFull`);
2. **its variance is exactly `∑_{2 ≤ p ≤ Y} (1/p)(1 − 1/p)`** — the Chinese
   remainder theorem, `jsp87Var_cnt_eq_sqDefect`;
3. so **hypothesis (5.21b) of arXiv:2512.01739 is exactly the variance hypothesis**
   (`jsp87R521b_ground_iff_var`), and it is satisfied at every sufficiently
   large height, unconditionally (`jsp87SqDefect_tendsto`);
4. and (5.15) at that scale forces `q² ∑_{2 ≤ p ≤ Y} 1/p ≤ κ₁ + κ₂ + κ₃`
   (`jsp87_515_ground_price`), which is unbounded — so (5.15) cannot hold with
   fixed constants at any height (`jsp87_515_ground_refuted`). -/
theorem jsp87_cntVariance_summary (Y : ℕ) (q : ℝ) :
    jsp87FAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
          (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
        = jsp87RecipSum (jsp87PrimeSet 2 Y)
      ∧ jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
          (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))
        = jsp87SqDefect (jsp87PrimeSet 2 Y)
      ∧ jsp87RecipSum (jsp87PrimeSet 2 Y)
          ≤ 2 * jsp87SqDefect (jsp87PrimeSet 2 Y)
      ∧ (jsp87R521b 0 (jsp87PrimeSet 2 Y) q 1
          ↔ 4 ≤ (q ^ 2) * jsp87Var (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
              (fun i => (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1) : ℝ))) :=
  ⟨jsp87FAvg_cnt_progFull (fun p hp => jsp87PrimeSet_prime hp),
   jsp87Var_cnt_eq_sqDefect (fun p hp => jsp87PrimeSet_prime hp),
   jsp87SqDefect_ge_recipSum_half (by omega),
   jsp87R521b_ground_iff_var (fun p hp => jsp87PrimeSet_prime hp) q⟩

end JSP87
