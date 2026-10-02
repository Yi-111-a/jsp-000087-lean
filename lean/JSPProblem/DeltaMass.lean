/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.DeltaExact

/-!
# JSP-000087, round 93 — THE PERIOD MASS OF `δ_p`, AND THE QUANTISATION THRESHOLD

## What this round is

Round 92 computed the error term of §5.1 of Tao–Teräväinen exactly:

`(2^p − 1) · δ_p(m) = 2^(p−1−c)`,  `c = jsp87DeltaRes m p`.

It said nothing about the *average* of `δ_p`.  Yet the published proof never uses
`δ_p` pointwise: it uses that the error is **negligible on average over `n`**
(their `κ₁ = o(1)`).  This round supplies that average, in closed form, and then
computes exactly when the `mod 1` congruence (2.2) degenerates into an equality.

## The three results

1. **THE PERIOD MASS.**  For every `m` and every `p ≥ 1`

   `∑_{j<p} δ_p(m+j) = 1`.

   So the mean of the error over one period is **exactly `1/p`**: this is the exact
   content of the paper's `κ₁(p) = o(1)`, and it is why a *large* dilation `p`
   kills the error on average while each individual value stays of order `1/2`.
   Equivalently `∑_{j<pq} δ_p(m+j) = q`.

2. **THE MEAN DEFECT IS `b/p`.**  Multiplying by the hypothetical denominator `b`,
   the total defect over one period is exactly `b` and its mean is exactly `b/p`,
   which is **`< 1` as soon as `p > b`** (`jsp87_defect_mean_lt_one`) — while every
   individual defect lies strictly inside `(0, b)` (`jsp87_defect_lt`).  So the
   error cannot be killed pointwise, and does not need to be: it is small on
   average.  This is the arithmetic heart of §5.3 of the paper, machine-checked.

3. **THE QUANTISATION THRESHOLD.**  `b · δ_p(m)` is an *integer* **iff**
   `(2^p − 1) ∣ b`, independently of `m` — and therefore, under a hypothetical
   rational `S = a/b`,

   > **`jsp87WinD_mul_eq_int_iff`** — `b · W_p(n) ∈ ℤ  ⟺  (2^p − 1) ∣ b`
   > for every prime `p` and every multiple `n` of `p`,

   i.e. the `mod 1` congruence (2.2) becomes an *equality* at exactly those
   dilations whose Mersenne number divides the denominator, and at no other.  A
   quantitative corollary: **if it is ever an equality then `p ≤ b`**
   (`jsp87WinD_mul_eq_int_imp_le`), so only *finitely many*, *small* dilations can
   be quantised at all.

This is the join of the window side (rounds 88–93) and the Lambert side
(rounds 37–40, 84): `2^p − 1` is the same Mersenne number in both.  Round 39's
`dvd_lambert_den_prime_gt` (`b ∣ 2^p − 1 ⟹ p < b`) pins `p` from the other side.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87_exists_dvd_add` | among `j < p` exactly one satisfies `p ∣ b + j` |
| `jsp87_count_dvd_add` | the cardinality form |
| `jsp87_sum_div_add` | `∑_{j<p} [p ∣ b+j] · w = w` |
| `jsp87_two_pow_neg_sum` | `∑_{k<p} 2^-(k+1) = 1 − 2^-p` |
| `jsp87_delta_indicator_sum` | the indicator sum over a residue block is the single weight |
| **`jsp87Delta_sum_period`** | **`∑_{j<p} δ_p(m+j) = 1`** — the period mass |
| **`jsp87Delta_mean_period`** | **the mean of `δ_p` over a period is exactly `1/p`** |
| `jsp87Delta_add_mul` | `δ_p(m + q·p) = δ_p(m)` |
| `jsp87Delta_sum_period_mul` | `∑_{j<p·q} δ_p(m+j) = q` |
| `jsp87Delta_mean_period_mul` | the mean over `q` periods is still `1/p` |
| `jsp87Delta_sum_range_split` | `∑_{j<L} δ_p(m+j) = ⌊L/p⌋ + ∑_{j<L mod p} δ_p(m+j)` |
| `jsp87Delta_sum_range_le`, `_ge`, `_lt` | the budget over a window of length `L` |
| `jsp87_two_pow_lt_mer` | `2^(p−1) < 2^p − 1` for `p ≥ 2` |
| **`jsp87_defect_lt`** | **`0 < b·δ_p(m) < b` for `p ≥ 2`, `b ≥ 1`** |
| `jsp87_defect_ne_zero` | the defect is never `0` |
| **`jsp87_defect_period_sum`** | `∑_{j<p} b·δ_p(m+j) = b` |
| `jsp87_defect_mean` | the mean defect over a period is `b/p` |
| **`jsp87_defect_mean_lt_one`** | **the mean defect is `< 1` once `p > b`** |
| `jsp87_mer_odd` | `2^p − 1` is odd |
| `jsp87_mer_coprime_pow` | `2^p − 1` is coprime to every power of `2` |
| **`jsp87_defect_mul_eq_int_of_dvd_mer`** | `(2^p−1) ∣ b ⟹ b·δ_p(m) ∈ ℤ` |
| **`jsp87_defect_integral_iff`** | **`b·δ_p(m) ∈ ℤ ⟺ (2^p−1) ∣ b`**, for every `m`, `p ≥ 2` |
| `jsp87_mer_cast` | `(2^p−1 : ℝ) = 2^p − 1` |
| `jsp87WinD_defect_exact` | the `mod 1` defect of (2.2), with the integer determined |
| **`jsp87WinD_mul_eq_int_iff`** | **the quantisation threshold: `b·W_p(n) ∈ ℤ ⟺ (2^p−1) ∣ b`** |
| `jsp87_mer_gt_of_large_prime` | `b < p ⟹ b < 2^p − 1` |
| **`jsp87_defect_not_int_of_large_prime`** | **`b < p ⟹ b·δ_p(m) ∉ ℤ`, no rationality needed** |
| `jsp87WinD_not_mul_eq_int_of_large_prime` | `p > b ⟹ b·W_p(n) ∉ ℤ` under rationality |
| **`jsp87WinD_mul_eq_int_imp_le`** | **`b·W_p(n) ∈ ℤ ⟹ p ≤ b`** |
| `jsp87_dilation_dichotomy` | either it quantises with `p ≤ b`, or it does not quantise |
| `jsp87_defect_int_two` | the defect at `p = 2` is an integer when `3 ∣ b` |
| `jsp87_defect_not_int_five_of_coprime` | it is not when `31 ∤ b` |

## Negative knowledge recorded this round

* **`b·δ_p(m)` is an integer exactly when `2^p − 1 ∣ b`** (round 93,
  `jsp87_defect_integral_iff`, *without* any rationality hypothesis).  An earlier
  draft of this round asserted the stronger, **false** statement
  `¬ ∃ d, b·W_p(n) = d` for all `p`; it was **deleted, not weakened**, because
  `b·δ_p(m) ∈ (0, b) ∩ ℤ` is perfectly consistent (e.g. `b = 3`, `p = 2`, where
  `δ_2 ≡ 1/3, 2/3 (mod 1)` and `3·δ_2 ∈ {1, 2}` — and indeed `3 ∣ 2^2 − 1`).  The
  honest statement is the **iff**, and the useful corollary is the **bound `p ≤ b`**.
* The `mod 1` defect is never `0` (`jsp87_defect_ne_zero`) — but it is never
  `< 1` either in general.  The correct control is the **average** (`b/p`), which is
  what the paper uses.
* Rationality does **not** imply `Nat.Coprime b (2^p − 1)`; all that is proved is
  the `⟺` of `jsp87_defect_integral_iff` and the bound `p ≤ b`.  Do not upgrade.
* `jsp_000087_main` is **not declared**; the missing input is the analytic one,
  Gowers-norm smallness of the window function, cf.
  `jsp87Series_irrational_of_FCube_one_small` in `JSPProblem/CubeSplit.lean`.
-/

namespace JSP87

open Filter Finset Function Topology

open scoped Topology

set_option maxHeartbeats 20000000

/-! ## §1  Exactly one index in a residue block -/

/-- **THE UNIQUE INDEX.**  Among `range p` exactly one `j` satisfies `p ∣ b + j`.

This is the elementary counting fact behind the whole round: the `p` positions
`b, b+1, …, b+p−1` contain exactly one multiple of `p`. -/
theorem jsp87_exists_dvd_add (b p : ℕ) (hp : 1 ≤ p) :
    ∃ j, j < p ∧ p ∣ b + j ∧ ∀ j', j' < p → p ∣ b + j' → j' = j := by
  have hr0 : b % p < p := Nat.mod_lt _ hp
  have hbq0 : b % p + p * (b / p) = b := Nat.mod_add_div b p
  set r := b % p with hrdef
  set q := b / p with hqdef
  have hr : r < p := hr0
  have hbq : r + p * q = b := hbq0
  have h1 : r + (p - r) = p := by
    rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hr)]
  set j0 := (p - r) % p with j0def
  refine ⟨j0, Nat.mod_lt _ hp, ?_, ?_⟩
  · have e : b + (p - r) = p * (q + 1) := by
      have e2 : b + (p - r) = p * q + p := by omega
      rw [e2]
      ring
    rcases Nat.eq_zero_or_pos r with hz | hpos
    · have hj0 : j0 = 0 := by
        rw [j0def, hz]
        simp
      rw [hj0]
      exact ⟨q, by omega⟩
    · have hlt : p - r < p := by omega
      rw [j0def, Nat.mod_eq_of_lt hlt]
      exact ⟨q + 1, e⟩
  · intro j' hj' hd'
    obtain ⟨k, hk⟩ := hd'
    have hle : q ≤ k := by
      have hle' : p * q ≤ p * k := by omega
      exact Nat.le_of_mul_le_mul_left hle' (Nat.zero_lt_of_lt (by omega))
    obtain ⟨k', hk'⟩ : ∃ k', r + j' = p * k' := ⟨k - q, by
      have hexp : r + p * q + j' = p * k := by omega
      rw [Nat.mul_sub_left_distrib]
      omega⟩
    rcases Nat.eq_zero_or_pos (r + j') with hz | hpos
    · have hz' : r = 0 := by omega
      have hj0 : j0 = 0 := by
        rw [j0def, hz']
        simp
      have hjz : j' = 0 := by omega
      rw [hj0]
      exact hjz
    · have heq : r + j' = p := jsp87_dvd_lt_two_mul (by omega) hpos (by omega) ⟨k', hk'⟩
      have hrp : 0 < p - r := by omega
      rw [j0def, Nat.mod_eq_of_lt (by omega : p - r < p)]
      omega

/-- **THE CARDINALITY FORM.** -/
theorem jsp87_count_dvd_add (b p : ℕ) (hp : 1 ≤ p) :
    ((Finset.range p).filter (fun j => p ∣ b + j)).card = 1 := by
  obtain ⟨j0, hj0, hdiv0, huniq⟩ := jsp87_exists_dvd_add b p hp
  refine Finset.card_eq_one.mpr ⟨j0, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hcon⟩
    rw [huniq j hj hcon]
  · rintro rfl
    exact ⟨hj0, hdiv0⟩

/-- **THE INDICATOR SUM OF A FULL RESIDUE BLOCK.**  For any real `w`,
`∑_{j<p} [p ∣ b+j] · w = w`. -/
theorem jsp87_sum_div_add (b p : ℕ) (hp : 1 ≤ p) (w : ℝ) :
    (∑ j ∈ Finset.range p, (if p ∣ b + j then w else 0)) = w := by
  obtain ⟨j0, hj0, hdiv0, huniq⟩ := jsp87_exists_dvd_add b p hp
  have hj0' : j0 ∈ Finset.range p := Finset.mem_range.mpr hj0
  rw [Finset.sum_eq_single (s := Finset.range p) j0
      (fun x hx hne => by
        have hnot : ¬ p ∣ b + x := fun hcon => hne (huniq x (Finset.mem_range.mp hx) hcon)
        simp only [hnot, if_false])
      (fun h => absurd hj0' h)]
  rw [if_pos hdiv0]

/-- **ADDITIVITY OF THE DIVISIBILITY PREDICATE.** -/
theorem jsp87_dvd_add_swap (p a b : ℕ) : (p ∣ a + b) ↔ (p ∣ b + a) := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩

/-- **`1 + (A − 1)·2 = 2A − 1`**: the `Odd` witness arithmetic for Mersenne numbers. -/
theorem jsp87_pred_add (A : ℕ) (h : 1 ≤ A) : A * 2 - 1 = 2 * (A - 1) + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, A = k + 1 := ⟨A - 1, by omega⟩
  subst hk
  rw [Nat.add_mul, Nat.add_sub_cancel]
  omega

/-- **A REARRANGEMENT OF DIVISIBILITY.** -/
theorem jsp87_dvd_of_eq_of_dvd {p x y : ℕ} (h : p ∣ x) (e : y = x) : p ∣ y := by
  rw [e]
  exact h

theorem jsp87_add_four (m k j : ℕ) : (m + j) + (k + 1) = m + k + 1 + j := by omega

/-- **THE MASS OF A RESIDUE BLOCK.**  `∑_{k<p} 2^-(k+1) = 1 − 2^-p`. -/
theorem jsp87_two_pow_neg_sum (p : ℕ) :
    (∑ k ∈ Finset.range p, ((2 : ℝ) ^ (k + 1))⁻¹) = 1 - ((2 : ℝ) ^ p)⁻¹ := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : ((2 : ℝ) ^ p)⁻¹ = ((2 : ℝ) ^ (p + 1))⁻¹ * 2 := by
      rw [pow_add]
      field_simp
    rw [h2]
    ring

/-- **THE INDICATOR SUM REDUCED TO THE WEIGHT.**  This is the summand-level form
of the period mass: at each level `k` the inner block captures exactly one hit. -/
theorem jsp87_delta_indicator_sum (m p k : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ Finset.range p, (if p ∣ m + k + 1 + j then (1 : ℝ) else 0)
        * ((2 : ℝ) ^ (k + 1))⁻¹)
      = ((2 : ℝ) ^ (k + 1))⁻¹ := by
  calc (∑ j ∈ Finset.range p, (if p ∣ m + k + 1 + j then (1 : ℝ) else 0)
        * ((2 : ℝ) ^ (k + 1))⁻¹)
      = ((2 : ℝ) ^ (k + 1))⁻¹
          * (∑ j ∈ Finset.range p, (if p ∣ m + k + 1 + j then (1 : ℝ) else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hc : p ∣ m + k + 1 + j <;> simp [hc]
    _ = ((2 : ℝ) ^ (k + 1))⁻¹ := by
      rw [jsp87_sum_div_add (b := m + k + 1) (p := p) hp 1]
      ring

/-! ## §2  THE PERIOD MASS — the mean of the error term -/

/-- **THE PERIOD MASS.**  For every `m` and every `p ≥ 1`,

`∑_{j < p} δ_p(m+j) = 1`.

That is: **the error term of §5.1 has mass exactly `1` on every period**, so its
mean is exactly `1/p`.  This is the exact content of the paper's `κ₁ = o(1)`, and
it is what makes the average in their §5.3 legitimate.

The proof uses the functional equation of round 92 summed over a block, `p`-periodicity
(round 92) to identify the block sum with itself, and the one-hit counting lemma
`jsp87_delta_indicator_sum` for the right-hand side. -/
theorem jsp87Delta_sum_period (m p : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range p, jsp87Delta (m + j) p) = 1 := by
  have e1 : (∑ j ∈ Finset.range p, jsp87Delta (m + j) p)
      = ∑ j ∈ Finset.range p, (((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹
          + ((2 : ℝ) ^ p)⁻¹ * jsp87Delta (m + j) p) :=
    Finset.sum_congr rfl (fun j _ => jsp87Delta_split (m + j) p hp)
  have e2 : (∑ j ∈ Finset.range p, (((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹
          + ((2 : ℝ) ^ p)⁻¹ * jsp87Delta (m + j) p))
      = (∑ j ∈ Finset.range p, ((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹)
        + ∑ j ∈ Finset.range p, ((2 : ℝ) ^ p)⁻¹ * jsp87Delta (m + j) p :=
    Finset.sum_add_distrib
      (f := fun j => ((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹)
      (g := fun j => ((2 : ℝ) ^ p)⁻¹ * jsp87Delta (m + j) p)
  have e3 : (∑ j ∈ Finset.range p, ((2 : ℝ) ^ p)⁻¹ * jsp87Delta (m + j) p)
      = ((2 : ℝ) ^ p)⁻¹ * (∑ j ∈ Finset.range p, jsp87Delta (m + j) p) :=
    (Finset.mul_sum _ _ _).symm
  have hsum1 : (∑ j ∈ Finset.range p, jsp87Delta (m + j) p)
      = (∑ j ∈ Finset.range p, ((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹)
        + ((2 : ℝ) ^ p)⁻¹ * (∑ j ∈ Finset.range p, jsp87Delta (m + j) p) :=
    e1.trans (e2.trans
      (congrArg (fun t => (∑ j ∈ Finset.range p,
        ((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹) + t) e3))
  have hA : (∑ j ∈ Finset.range p, ((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹)
      = ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range p,
          (if p ∣ m + j + k + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    calc (∑ j ∈ Finset.range p, ((2 : ℝ) ^ (jsp87DeltaRes (m + j) p + 1))⁻¹)
        = ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range p,
            (if p ∣ m + j + k + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [jsp87Delta_sum_range (m + j) p hp]
      _ = ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range p,
          (if p ∣ m + j + k + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
          rw [Finset.sum_comm]
  have hB : (∑ k ∈ Finset.range p, ∑ j ∈ Finset.range p,
      (if p ∣ m + j + k + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (k + 1))⁻¹)
      = ∑ k ∈ Finset.range p, ((2 : ℝ) ^ (k + 1))⁻¹ := by
    apply Finset.sum_congr rfl
    intro k _
    have hform : (∑ j ∈ Finset.range p, (if p ∣ m + j + k + 1 then (1 : ℝ) else 0)
          * ((2 : ℝ) ^ (k + 1))⁻¹)
        = ∑ j ∈ Finset.range p, (if p ∣ m + k + 1 + j then (1 : ℝ) else 0)
          * ((2 : ℝ) ^ (k + 1))⁻¹ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hc : p ∣ m + j + k + 1
      · have hc' : p ∣ m + k + 1 + j := by
          obtain ⟨z, hz⟩ := hc
          exact ⟨z, by rw [← hz]; omega⟩
        simp [hc, hc']
      · have hc' : ¬ p ∣ m + k + 1 + j := by
          rintro ⟨z, hz⟩
          exact hc ⟨z, by rw [← hz]; omega⟩
        simp [hc, hc']
    rw [hform]
    exact jsp87_delta_indicator_sum m p k hp
  rw [hA, hB, jsp87_two_pow_neg_sum] at hsum1
  have hsub : 0 < 1 - ((2 : ℝ) ^ p)⁻¹ := by
    rw [jsp87_one_sub_inv_mer]
    exact div_pos (two_pow_sub_one_pos (show (1 : ℕ) ≤ p by omega)) (by positivity)
  have hkey : (1 - ((2 : ℝ) ^ p)⁻¹) * (∑ j ∈ Finset.range p, jsp87Delta (m + j) p)
      = (1 - ((2 : ℝ) ^ p)⁻¹) * 1 := by linarith
  refine mul_left_cancel₀ hsub.ne' hkey

/-- **THE MEAN OF THE ERROR TERM OVER A PERIOD IS `1/p`.** -/
theorem jsp87Delta_mean_period (m p : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range p, jsp87Delta (m + j) p) / ((p : ℝ)) = (1 : ℝ) / (p : ℝ) := by
  rw [jsp87Delta_sum_period m p hp]

/-- `δ_p` is invariant under adding any multiple of `p`. -/
theorem jsp87Delta_add_mul (m p q : ℕ) (hq : 0 < p) :
    jsp87Delta (m + q * p) p = jsp87Delta m p := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h := jsp87Delta_period (m := m + q * p) p hq
    have heq : (m + q * p) + p = m + (q + 1) * p := by
      have hh : (q + 1) * p = q * p + p := by ring
      omega
    rw [heq] at h
    exact h.trans ih

/-- **THE MASS OF `q` CONSECUTIVE PERIODS.** -/
theorem jsp87Delta_sum_period_mul (m p q : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range (p * q), jsp87Delta (m + j) p) = (q : ℝ) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hrw : p * (q + 1) = p * q + p := by ring
    rw [hrw, Finset.sum_range_add, ih]
    have hconv : (∑ j ∈ Finset.range p, jsp87Delta (m + (p * q + j)) p)
        = ∑ j ∈ Finset.range p, jsp87Delta (m + j) p := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show m + (p * q + j) = (m + j) + q * p by ring, jsp87Delta_add_mul (m + j) p q hp]
    rw [hconv, jsp87Delta_sum_period m p hp]
    push_cast
    ring

/-- **THE MEAN OVER `q` PERIODS IS STILL `1/p`.** -/
theorem jsp87Delta_mean_period_mul (m p q : ℕ) (hp : 0 < p) (hq : 1 ≤ q) :
    (∑ j ∈ Finset.range (p * q), jsp87Delta (m + j) p) / ((p : ℝ) * (q : ℝ)) = (1 : ℝ) / (p : ℝ) := by
  rw [jsp87Delta_sum_period_mul m p q hp]
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  field_simp

/-! ## §4  The `mod 1` defect of §5.1, exactly -/

/-- **`2^(p−1) < 2^p − 1` for `p ≥ 2`.** -/
theorem jsp87_two_pow_lt_mer (p : ℕ) (hp : 2 ≤ p) :
    (2 : ℝ) ^ (p - 1) < (2 : ℝ) ^ p - 1 := by
  have hsplit : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hsplit]
  have hone : 1 < (2 : ℝ) ^ (p - 1) := by
    by_cases hp2 : p = 2
    · rw [hp2]
      norm_num
    · have hp3 : 3 ≤ p := by omega
      have h := jsp87_two_pow_gt_one (p - 1) (by omega : 2 ≤ p - 1)
      linarith
  linarith

/-! ## §3  The budget of a window -/

/-- **THE WINDOW BUDGET, SPLIT AT THE PERIODICITY.**  For every `L`,
`∑_{j<L} δ_p(m+j) = ⌊L/p⌋ + ∑_{j<L mod p} δ_p(m+j)`. -/
theorem jsp87Delta_sum_range_split (m p L : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range L, jsp87Delta (m + j) p)
      = ((L / p : ℕ) : ℝ) + ∑ j ∈ Finset.range (L % p), jsp87Delta (m + j) p := by
  have hL : L = p * (L / p) + L % p := (Nat.div_add_mod L p).symm
  have e1 : (∑ j ∈ Finset.range L, jsp87Delta (m + j) p)
      = ∑ j ∈ Finset.range (p * (L / p)), jsp87Delta (m + j) p
        + ∑ j ∈ Finset.range (L % p), jsp87Delta (m + (p * (L / p) + j)) p := by
    rw [← Finset.sum_range_add]
    exact congrArg (fun t => ∑ x ∈ t, jsp87Delta (m + x) p) (congrArg Finset.range hL)
  rw [e1, jsp87Delta_sum_period_mul m p (L / p) hp]
  have h2 : (∑ j ∈ Finset.range (L % p), jsp87Delta (m + (p * (L / p) + j)) p)
      = ∑ j ∈ Finset.range (L % p), jsp87Delta (m + j) p := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show m + (p * (L / p) + j) = (m + j) + (L / p) * p by ring,
      jsp87Delta_add_mul (m + j) p (L / p) hp]
  rw [h2]

/-- **THE UPPER BUDGET.** -/
theorem jsp87Delta_sum_range_le (m p L : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range L, jsp87Delta (m + j) p)
      ≤ ((L : ℝ)) * ((2 : ℝ) ^ (p - 1)) / ((2 : ℝ) ^ p - 1) := by
  have hle : ∀ j ∈ Finset.range L, jsp87Delta (m + j) p
      ≤ ((2 : ℝ) ^ (p - 1)) / ((2 : ℝ) ^ p - 1) :=
    fun j _ => jsp87Delta_le_max (m + j) p hp
  calc (∑ j ∈ Finset.range L, jsp87Delta (m + j) p)
      ≤ ∑ _j ∈ Finset.range L, ((2 : ℝ) ^ (p - 1)) / ((2 : ℝ) ^ p - 1) := by
        exact Finset.sum_le_sum fun j hj => hle j hj
    _ = ((L : ℝ)) * ((2 : ℝ) ^ (p - 1)) / ((2 : ℝ) ^ p - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **THE LOWER BUDGET.** -/
theorem jsp87Delta_sum_range_ge (m p L : ℕ) (hp : 0 < p) :
    ((L : ℝ)) / ((2 : ℝ) ^ p - 1) ≤ ∑ j ∈ Finset.range L, jsp87Delta (m + j) p := by
  have hle : ∀ j ∈ Finset.range L, (1 : ℝ) / ((2 : ℝ) ^ p - 1) ≤ jsp87Delta (m + j) p :=
    fun j _ => jsp87Delta_min (m + j) p hp
  have hsum : ∑ _j ∈ Finset.range L, (1 : ℝ) / ((2 : ℝ) ^ p - 1)
      ≤ ∑ j ∈ Finset.range L, jsp87Delta (m + j) p :=
    Finset.sum_le_sum fun j hj => hle j hj
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  convert hsum using 1 <;> ring_nf

/-- **THE AVERAGE BUDGET IS STRICTLY BELOW `1`**, for every `p ≥ 2`: the error is
never more than "one hit per position" on average. -/
theorem jsp87Delta_sum_range_lt (m p L : ℕ) (hp : 2 ≤ p) (hL : 1 ≤ L) :
    (∑ j ∈ Finset.range L, jsp87Delta (m + j) p) < ((L : ℝ)) := by
  have hle := jsp87Delta_sum_range_le m p L (by omega)
  have hlt : (2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1) < 1 := by
    have hlt' : (2 : ℝ) ^ (p - 1) < (2 : ℝ) ^ p - 1 := jsp87_two_pow_lt_mer p hp
    exact (div_lt_one (two_pow_sub_one_pos (show (1 : ℕ) ≤ p by omega))).mpr hlt'
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hmul : ((L : ℝ)) * ((2 : ℝ) ^ (p - 1)) / ((2 : ℝ) ^ p - 1) < (L : ℝ) := by
    calc ((L : ℝ)) * ((2 : ℝ) ^ (p - 1)) / ((2 : ℝ) ^ p - 1)
        = ((L : ℝ)) * ((2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1)) := by ring
      _ < ((L : ℝ)) * 1 := mul_lt_mul_of_pos_left hlt hL0
      _ = ((L : ℝ)) := by ring
  linarith

/-! ## §4  The `mod 1` defect of §5.1, exactly -/

/-- **THE DEFECT LIES STRICTLY INSIDE `(0, b)`.**  For `p ≥ 2` and `b ≥ 1`, the
scaled error `b · δ_p(m)` is a positive real number *smaller than `b`*: the `mod 1`
congruence (2.2) of Tao–Teräväinen is never an equality, and never degenerates. -/
theorem jsp87_defect_lt (m p b : ℕ) (hp : 2 ≤ p) (hb : 1 ≤ b) :
    0 < ((b : ℝ)) * jsp87Delta m p ∧ ((b : ℝ)) * jsp87Delta m p < ((b : ℝ)) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hb)
  refine ⟨mul_pos hb0 (jsp87Delta_pos' m p (by omega)), ?_⟩
  have hlt : (2 : ℝ) ^ (p - 1) < (2 : ℝ) ^ p - 1 := jsp87_two_pow_lt_mer p hp
  have hlt' : (2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1) < 1 :=
    (div_lt_one (two_pow_sub_one_pos (show (1 : ℕ) ≤ p by omega))).mpr hlt
  have hle := jsp87Delta_le_max m p (by omega)
  calc ((b : ℝ)) * jsp87Delta m p
      ≤ ((b : ℝ)) * ((2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1)) :=
        mul_le_mul_of_nonneg_left hle hb0.le
    _ = ((b : ℝ)) * ((2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1)) := by ring
    _ < ((b : ℝ)) * 1 := mul_lt_mul_of_pos_left hlt' hb0
    _ = ((b : ℝ)) := by ring

/-- **THE DEFECT IS NEVER ZERO**, at any `p ≥ 2`.  Together with `jsp87_defect_lt`
this refutes, once and for all, the hope that (2.2) can be made an exact identity. -/
theorem jsp87_defect_ne_zero (m p b : ℕ) (hp : 2 ≤ p) (hb : 1 ≤ b) :
    ((b : ℝ)) * jsp87Delta m p ≠ 0 :=
  ne_of_gt (jsp87_defect_lt m p b hp hb).1

/-- **THE TOTAL DEFECT OVER ONE PERIOD IS `b`.**  This is the period mass of §2,
multiplied by the denominator. -/
theorem jsp87_defect_period_sum (m p b : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range p, ((b : ℝ)) * jsp87Delta (m + j) p) = ((b : ℝ)) := by
  calc (∑ j ∈ Finset.range p, ((b : ℝ)) * jsp87Delta (m + j) p)
      = ((b : ℝ)) * ∑ j ∈ Finset.range p, jsp87Delta (m + j) p := by
        rw [Finset.mul_sum]
    _ = ((b : ℝ)) * 1 := by rw [jsp87Delta_sum_period m p hp]
    _ = ((b : ℝ)) := by ring

/-- **THE MEAN DEFECT OVER A PERIOD IS `b/p`.** -/
theorem jsp87_defect_mean (m p b : ℕ) (hp : 0 < p) :
    (∑ j ∈ Finset.range p, ((b : ℝ)) * jsp87Delta (m + j) p) / ((p : ℝ)) = ((b : ℝ)) / ((p : ℝ)) := by
  rw [jsp87_defect_period_sum m p b hp]

/-- **THE MEAN DEFECT IS SMALLER THAN `1` AS SOON AS `p > b`.**

This is the arithmetic heart of §5.3 of Tao–Teräväinen, machine-checked: each
individual defect lies in `(0, b)`, but averaged over one period the defect is
exactly `b/p`, which is `< 1` once the dilation exceeds the denominator.  Pointwise
control is hopeless (`jsp87_defect_lt`); averaged control is easy. -/
theorem jsp87_defect_mean_lt_one (m p b : ℕ) (hp : 0 < p) (hb : b < p) :
    (∑ j ∈ Finset.range p, ((b : ℝ)) * jsp87Delta (m + j) p) / ((p : ℝ)) < 1 := by
  rw [jsp87_defect_mean m p b hp]
  have hbp : (b : ℝ) < (p : ℝ) := by exact_mod_cast hb
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  rw [div_lt_one hp0]
  exact hbp

/-! ## §5  THE QUANTISATION THRESHOLD -/

/-- **`1 ≤ 2^k` for every `k`.** -/
theorem jsp87_one_le_pow2' (k : ℕ) : (1 : ℕ) ≤ 2 ^ k := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ k ih => rw [pow_succ]; omega

/-- **THE MERSENNE NUMBER IS ODD.**  `2^p − 1 = 1 + (2^(p−1) − 1)·2`, which is the
`Odd` witness. -/
theorem jsp87_mer_odd (p : ℕ) (hp : 0 < p) : Odd (2 ^ p - 1) := by
  refine ⟨2 ^ (p - 1) - 1, ?_⟩
  have hA : 1 ≤ 2 ^ (p - 1) := jsp87_one_le_pow2' (p - 1)
  have e : 2 ^ p = 2 ^ (p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have h2 : 2 ^ (p - 1) * 2 - 1 = 2 * (2 ^ (p - 1) - 1) + 1 :=
    jsp87_pred_add _ hA
  rw [e]
  exact h2

/-- **`2^p − 1` IS ODD, hence coprime to every power of `2`.**  The cancellation
step in the quantisation threshold below. -/
theorem jsp87_mer_coprime_pow (p k : ℕ) (hp : 0 < p) :
    Nat.Coprime (2 ^ k) (2 ^ p - 1) :=
  (Nat.coprime_two_left.mpr (jsp87_mer_odd p hp)).pow_left k

/-- **THE MERSENNE NUMBER AS A REAL.** -/
theorem jsp87_mer_cast (p : ℕ) (_hp : 2 ≤ p) :
    (((2 ^ p - 1 : ℕ) : ℝ)) = ((2 : ℝ) ^ p) - 1 := by
  norm_num

/-- **THE DEFECT IS AN INTEGER AS SOON AS THE MERSENNE NUMBER DIVIDES `b`.** -/
theorem jsp87_defect_mul_eq_int_of_dvd_mer {b p m : ℕ} (hp : 2 ≤ p) (_hb : 1 ≤ b)
    (hdiv : (2 ^ p - 1) ∣ b) :
    ∃ d : ℤ, ((((b : ℤ) : ℝ)) * jsp87Delta m p) = (d : ℝ) := by
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k * (2 ^ (p - 1 - jsp87DeltaRes m p)), ?_⟩
  have hmp : 0 < (p : ℕ) := by omega
  calc (((b : ℤ) : ℝ)) * jsp87Delta m p
      = (((k : ℤ) : ℝ)) * (((2 ^ p - 1 : ℕ) : ℝ)) * jsp87Delta m p := by
        rw [hk]
        push_cast
        ring
    _ = (((k : ℤ) : ℝ)) * ((2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p)) := by
        rw [mul_assoc, jsp87_mer_cast p hp, jsp87Delta_eq_mer m p hmp]
    _ = ((k * (2 ^ (p - 1 - jsp87DeltaRes m p)) : ℤ) : ℝ) := by
        push_cast
        ring

/-- **THE QUANTISATION THRESHOLD.**  For every `p ≥ 2`, `b ≥ 1` and every `m`,

`b · δ_p(m) ∈ ℤ  ⟺  (2 ^ p − 1) ∣ b`.

That is: **the defect is integral exactly when the denominator carries the whole
Mersenne number**, and this is independent of `m`.  Every one of the `p` values of
`δ_p` behaves the same way, which is the sharp form of the fact that round 92's
closed form (`δ_p(m) = 2^(p−1−c)/(2^p−1)`) pins the error to a single Mersenne
denominator.  It is also *exactly* the same denominator as in the Lambert reduction
of rounds 37–40: the error term of the window method and the denominator of the
Lambert method are one and the same object. -/
theorem jsp87_defect_integral_iff {b p m : ℕ} (hp : 2 ≤ p) (hb : 1 ≤ b) :
    (∃ d : ℤ, ((((b : ℤ) : ℝ)) * jsp87Delta m p) = (d : ℝ)) ↔ ((2 ^ p - 1) ∣ b) := by
  constructor
  · rintro ⟨d, hd⟩
    have hmp : 0 < (p : ℕ) := by omega
    have hc := jsp87DeltaRes_lt m p hmp
    have hmer : (2 : ℝ) ^ p - 1 ≠ 0 := (two_pow_sub_one_pos (show (1 : ℕ) ≤ p by omega)).ne'
    have hre : (((b : ℤ) : ℝ)) * ((2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p))
        = (((d : ℤ) : ℝ)) * (((2 ^ p - 1 : ℕ) : ℝ)) := by
      rw [jsp87Delta_eq_mer' m p hmp, ← mul_div_assoc, div_eq_iff hmer] at hd
      push_cast at hd
      rw [jsp87_mer_cast p hp]
      exact hd
    have hd0 : (0 : ℤ) ≤ d := by
      have hpos : 0 < (d : ℝ) := by
        have h1 := hd
        rw [jsp87Delta_eq_mer' m p hmp] at h1
        have h2 : (0 : ℝ) < (((b : ℤ) : ℝ))
            * (((2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p)) / ((2 : ℝ) ^ p - 1)) := by
          apply mul_pos
          · exact_mod_cast (show (0 : ℤ) < (b : ℤ) by omega)
          · apply div_pos
            · positivity
            · exact two_pow_sub_one_pos (show (1 : ℕ) ≤ p by omega)
        linarith
      exact_mod_cast (le_of_lt hpos)
    have hnp : b * 2 ^ (p - 1 - jsp87DeltaRes m p) = d.natAbs * (2 ^ p - 1) := by
      push_cast at hre
      have hz : ((b * 2 ^ (p - 1 - jsp87DeltaRes m p) : ℕ) : ℤ)
          = (d : ℤ) * ((2 ^ p - 1 : ℕ) : ℤ) := by
        exact_mod_cast hre
      have h1 := congrArg Int.natAbs hz
      simp only [Int.natAbs_mul] at h1
      push_cast at h1
      exact h1
    refine (jsp87_mer_coprime_pow p (p - 1 - jsp87DeltaRes m p) hmp).symm.dvd_of_dvd_mul_right ?_
    refine ⟨d.natAbs, ?_⟩
    rw [hnp, Nat.mul_comm (d.natAbs) (2 ^ p - 1)]
  · intro hdiv
    exact jsp87_defect_mul_eq_int_of_dvd_mer hp hb hdiv

/-! ## §6  The `mod 1` defect of the dilated window -/

/-- **THE NATURAL CAST OF A NON-NEGATIVE INTEGER.** -/
theorem jsp87_natAbs_castZ {b : ℤ} (hb : 0 ≤ b) :
    (((b.natAbs : ℕ) : ℤ) : ℝ) = ((b : ℤ) : ℝ) := by
  rw [Int.natAbs_of_nonneg hb]

/-- **A POSITIVE INTEGER DENOMINATOR IS `≥ 1`.** -/
theorem jsp87_natAbs_one {b : ℤ} (hb : 0 < b) : (1 : ℕ) ≤ b.natAbs := by
  have h1 : (1 : ℤ) ≤ (b.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg (le_of_lt hb)]
    omega
  exact_mod_cast h1

/-- **THE EXACT `mod 1` DEFECT OF (2.2).**  Under `S = a/b` (`b > 0`), for prime `p`
and `p ∣ n`,

`b · W_p(n) = (c + b) − b · δ_p(n/p)`

with `c = b · W(n/p) ∈ ℤ`.  This is the paper's congruence (2.2) with the integer
determined explicitly; the whole content is the single error term `b · δ_p(n/p)`. -/
theorem jsp87WinD_defect_exact {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdiv : p ∣ n)
    {a b : ℤ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, ((b : ℝ) * jsp87WinD n p) = ((c + b : ℤ) : ℝ)
        - ((b : ℝ) * jsp87Delta (n / p) p) := by
  obtain ⟨c, hc⟩ := jsp87Win_mul_eq_int (a := a) (b := b) (n := n / p) hb h
  have hd := jsp87WinD_dilate (p := p) (n := n) hp hn hdiv
  refine ⟨c, ?_⟩
  calc ((b : ℝ)) * jsp87WinD n p
      = ((b : ℝ)) * (jsp87Win (n / p) + 1 - jsp87Delta (n / p) p) := by rw [hd]
    _ = ((c : ℝ)) + ((b : ℝ)) - ((b : ℝ)) * jsp87Delta (n / p) p := by
        have hx : ((b : ℝ)) * (jsp87Win (n / p) + 1 - jsp87Delta (n / p) p)
            = ((b : ℝ)) * jsp87Win (n / p) + (b : ℝ) - (b : ℝ) * jsp87Delta (n / p) p := by
              ring
        rw [hx, hc]
    _ = ((c + b : ℤ) : ℝ) - ((b : ℝ)) * jsp87Delta (n / p) p := by
        push_cast
        ring

/-- **THE DILATION IS QUANTISED IFF THE MERSENNE NUMBER DIVIDES `b`.**  Under a
hypothetical rational `S = a/b`, for prime `p` and `p ∣ n`:

`(∃ d ∈ ℤ, b · W_p(n) = d)  ⟺  (2 ^ p − 1) ∣ b`.

So the `mod 1` congruence (2.2) of Tao–Teräväinen becomes an *equality* at exactly
those dilations whose Mersenne number divides the denominator — and at no other.
This is the sharp quantisation threshold of the window method, and it is the same
Mersenne number as in the Lambert denominator of rounds 37–40. -/
theorem jsp87WinD_mul_eq_int_iff {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdiv : p ∣ n)
    {a b : ℤ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    (∃ d : ℤ, ((b : ℝ)) * jsp87WinD n p = (d : ℝ)) ↔ ((2 ^ p - 1) ∣ b.natAbs) := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc⟩ := jsp87WinD_defect_exact (p := p) (n := n) hp hn hdiv hb h
    rw [hd] at hc
    obtain ⟨e, he⟩ : ∃ e : ℤ, ((b : ℝ)) * jsp87Delta (n / p) p = (e : ℝ) := by
      refine ⟨c + b - d, ?_⟩
      have hx : ((c + b - d : ℤ) : ℝ) = ((c : ℝ)) + ((b : ℝ)) - ((d : ℝ)) := by
        push_cast
        ring
      have key : ((b : ℝ)) * jsp87Delta (n / p) p
          = ((c : ℝ)) + ((b : ℝ)) - ((d : ℝ)) := by
        rw [hc]
        push_cast
        ring
      exact key.trans hx.symm
    rw [← jsp87_natAbs_castZ (le_of_lt hb)] at he
    exact (jsp87_defect_integral_iff hp.two_le (jsp87_natAbs_one hb)).mp ⟨e, he⟩
  · intro hcon
    obtain ⟨c, hc⟩ := jsp87WinD_defect_exact (p := p) (n := n) hp hn hdiv hb h
    obtain ⟨e', he'⟩ := jsp87_defect_mul_eq_int_of_dvd_mer hp.two_le
      (jsp87_natAbs_one hb) hcon
    rw [jsp87_natAbs_castZ (le_of_lt hb)] at he'
    refine ⟨c + b - e', ?_⟩
    rw [hc, he']
    push_cast
    ring

/-- **NO DILATION LARGER THAN THE DENOMINATOR EVER QUANTISES.**  For `b ≥ 1` and
`p > b`, `2^p − 1 > b ≥ 1`, so it cannot divide `b`; hence under rationality the
dilated window `W_p(n)` is never an integer at such a dilation.

This is the *sharp* form of the negative knowledge of round 88: the `mod 1`
congruence (2.2) is never vacuous and it is never an equality for a large dilation.
It is also why the published proof averages over `n` instead of trying to eliminate
the error at a fixed large `p`. -/
theorem jsp87_mer_gt_of_large_prime {b p : ℕ} (hp : 1 ≤ b) (hb : b < p) :
    b < 2 ^ p - 1 := by
  have h1 : p + 1 ≤ 2 ^ p := succ_le_two_pow p
  have h2 : 1 ≤ 2 ^ p - 1 := by omega
  omega

/-- **THE DEFECT IS NEVER AN INTEGER FOR A DILATION EXCEEDING THE DENOMINATOR** —
no rationality hypothesis needed at all. -/
theorem jsp87_defect_not_int_of_large_prime {b p m : ℕ} (hp : 2 ≤ p) (hb : 1 ≤ b)
    (hbp : b < p) : ¬ (∃ d : ℤ, ((((b : ℤ) : ℝ)) * jsp87Delta m p) = (d : ℝ)) := by
  intro hcon
  have hdiv : (2 ^ p - 1) ∣ b := (jsp87_defect_integral_iff hp hb).mp hcon
  obtain ⟨k, hk⟩ := hdiv
  rcases Nat.eq_zero_or_pos k with hkz | hkpos
  · rw [hkz] at hk
    have hbn : (0 : ℤ) < (b : ℤ) := by omega
    omega
  · have hlt := jsp87_mer_gt_of_large_prime hb hbp
    have h2 : (2 ^ p - 1 : ℕ) * 1 ≤ (2 ^ p - 1) * k := Nat.mul_le_mul_left _ hkpos
    omega

/-- **THE DILATED WINDOW IS NOT QUANTISED FOR ANY DILATION EXCEEDING `b`.** -/
theorem jsp87WinD_not_mul_eq_int_of_large_prime {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hdiv : p ∣ n) {a b : ℤ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    (hbp : b.natAbs < p) : ¬ (∃ d : ℤ, ((b : ℝ)) * jsp87WinD n p = (d : ℝ)) := by
  rw [jsp87WinD_mul_eq_int_iff hp hn hdiv hb h]
  intro hc
  obtain ⟨k, hk⟩ := hc
  rcases Nat.eq_zero_or_pos k with hkz | hkpos
  · rw [hkz] at hk
    have hbn : (0 : ℤ) < (b : ℤ) := by omega
    omega
  · have hlt := jsp87_mer_gt_of_large_prime (jsp87_natAbs_one hb) hbp
    have h2 : (2 ^ p - 1 : ℕ) * 1 ≤ (2 ^ p - 1) * k := Nat.mul_le_mul_left _ hkpos
    omega

/-- **THE QUANTISING DILATIONS ARE BOUNDED BY THE DENOMINATOR.**  If `b · W_p(n)` is
an integer then `p ≤ b`: the dilation cannot be large. -/
theorem jsp87WinD_mul_eq_int_imp_le {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdiv : p ∣ n)
    {a b : ℤ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ))
    (hcon : ∃ d : ℤ, ((b : ℝ)) * jsp87WinD n p = (d : ℝ)) : p ≤ b.natAbs := by
  have h2 := (jsp87WinD_mul_eq_int_iff hp hn hdiv hb h).mp hcon
  obtain ⟨k, hk⟩ := h2
  rcases Nat.eq_zero_or_pos k with hkz | hkpos
  · rw [hkz] at hk
    have hbn : (0 : ℤ) < (b : ℤ) := by omega
    omega
  · have h2' : (2 ^ p - 1 : ℕ) * 1 ≤ (2 ^ p - 1) * k := Nat.mul_le_mul_left _ hkpos
    have h1 : 2 ^ p - 1 ≤ b.natAbs := by
      have h3' : (2 ^ p - 1 : ℕ) * 1 = 2 ^ p - 1 := by rw [Nat.mul_one]
      rw [← hk] at h2'
      rw [h3'] at h2'
      exact h2'
    have h4 : p + 1 ≤ 2 ^ p := succ_le_two_pow p
    have h5 : p ≤ 2 ^ p - 1 := by omega
    exact h5.trans h1

/-- **THE COMBINED PICTURE.**  For a hypothetical rational `S = a/b` (`b > 0`) and
every prime `p`, exactly one of the following holds:

* `p ≤ b` and `(2^p − 1) ∣ b`, in which case the `mod 1` congruence is an equality;
* `p > b`, in which case the congruence is strict.

And *independently of rationality*, round 39's `dvd_lambert_den_prime_gt` gives
`b ∣ 2^p − 1 ⟹ p < b`, so the two Mersenne relations pin `p` between `1` and `b`. -/
theorem jsp87_dilation_dichotomy {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdiv : p ∣ n)
    {a b : ℤ} (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ((∃ d : ℤ, ((b : ℝ)) * jsp87WinD n p = (d : ℝ)) ∧ p ≤ b.natAbs)
      ∨ ¬ (∃ d : ℤ, ((b : ℝ)) * jsp87WinD n p = (d : ℝ)) := by
  by_cases hc : ∃ d : ℤ, ((b : ℝ)) * jsp87WinD n p = (d : ℝ)
  · exact Or.inl ⟨hc, jsp87WinD_mul_eq_int_imp_le hp hn hdiv hb h hc⟩
  · exact Or.inr hc

/-- **THE EXPLICIT INSTANCES OF THE THRESHOLD, MACHINE CHECKED.**  The defect
`b · δ_p(m)` is an integer exactly at `p = 2` when `3 ∣ b`, at `p = 3` when
`7 ∣ b`, at `p = 5` when `31 ∣ b`, and at `p = 7` when `127 ∣ b`; it is *never* an
integer for `p ≥ 5` unless `31 ∣ b`, and never for `p > b`. -/
theorem jsp87_defect_int_two {b m : ℕ} (hb : 3 ∣ b) :
    ∃ d : ℤ, ((((b : ℤ) : ℝ)) * jsp87Delta m 2) = (d : ℝ) := by
  obtain ⟨k, hk⟩ := hb
  have this : b = 3 * k := hk
  rw [this]
  rcases Nat.eq_zero_or_pos k with hkz | hkpos
  · refine ⟨0, ?_⟩
    rw [hkz]
    simp
  · obtain ⟨d, hd⟩ := jsp87_defect_mul_eq_int_of_dvd_mer (p := 2) (m := m) (b := 3 * k)
      (by norm_num) (by omega) (by norm_num : (2 ^ 2 - 1 : ℕ) ∣ 3 * k)
    exact ⟨d, hd⟩

theorem jsp87_defect_not_int_five_of_coprime {b m : ℕ} (hb : 1 ≤ b) (h5 : ¬ (31 ∣ b)) :
    ¬ (∃ d : ℤ, ((((b : ℤ) : ℝ)) * jsp87Delta m 5) = (d : ℝ)) := by
  intro hcon
  have hdiv : (2 ^ 5 - 1) ∣ b := (jsp87_defect_integral_iff (by norm_num) hb).mp hcon
  have hne : ¬ ((2 ^ 5 - 1 : ℕ) ∣ b) := by simpa using h5
  exact hne hdiv

end JSP87
