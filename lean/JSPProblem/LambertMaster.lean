/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-113-a).
-/
import JSPProblem.TTRoute
import Mathlib.Tactic

/-!
# JSP-000087 : the master Lambert identity (Erdős #257), and the `+1` series as an
# alternating sum of dilations

## Why this file exists

Rounds 37–112 built the Erdős series `S = ∑' n, ω(n) 2^{-(n+1)}` from forty
directions.  Two of its most classical algebraic re-arrangements had **never**
been written down in Lean, because both of them live *outside* the prime case.

1. **The general Lambert identity (Erdős #257).**  `JSPProblem/LambertIdentity.lean`
   proves `jsp87_lambert` — the *prime* case `S = ∑' p prime, 1 / (2 ^ (p+1) - 2)`.
   The general form, which is what Tao and Teräväinen (arXiv:2512.01739) quote as
   "a special case of [Erdős #257]", replaces `prime` by an **arbitrary**
   predicate `P` and `ω` by the counting function

   ```
   f_P (m)  =  #{ d : d ∣ m,  P d } ,
   ```

   and then reads

   ```
   ∑' m, f_P (m) 2^{-(m+1)}  =  ∑' d, if P d ∧ 1 ≤ d then 1 / (2 ^ (d+1) - 2) else 0.
   ```

   Instances: `P = prime` recovers `jsp87_lambert`; `P = everything` is the
   **Erdős–Borwein identity** `∑_{d ≥ 1} 1/(2^d − 1) = ∑_{m ≥ 1} τ(m) 2^{-m}`; and
   `P = prime ∧ d | m` for a fixed `m` reads off the Lambert weight of the prime
   divisors of a single integer.  The counting function `jsp87DivCard` is a new
   object in the tree, proved monotone in `P`.

2. **The alternating-dilation expansion (§5.2 of arXiv:2512.01739).**  Round 112
   introduced the objects `jsp87PlusLambert = ∑' n, ω(n)/(2^n + 1)` and the
   dilations `jsp87ScaleLambert k = ∑' n, ω(n) 2^{-kn}` but proved nothing about
   their relation.  It is a **purely finite geometric identity**: for
   `x = 2^{-n} ∈ (0,1]`,

   ```
   ω(n)/(2^n + 1)  =  ω(n) ∑_{k<J} (-1)^k x^{k+1}  +  ω(n) · x · (-x)^J / (1 + x) ,
   ```

   and the remainder is dominated by `ω(n) x^J`.  Summing over `n` gives the exact
   expansion with an explicit error term, the dilations satisfy
   `jsp87ScaleLambert (J+1) ≤ jsp87ScaleLambert J / 2`, and the remainder carries
   the **sign of `(-1)^J`**, so the alternating series brackets `jsp87PlusLambert`
   from both sides.
-/

namespace JSP87

open Classical
open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. The counting function `f_P (m) = #{ d : d ∣ m,  P d }` -/

/-- **The divisor-counting function attached to a predicate `P`.**
`jsp87DivCard P m` counts the divisors `d` of `m` that satisfy `P d`.  For
`P = fun d => d.Prime` this is `ω m`; for `P = fun _ => True` it is the
divisor-counting function `τ m`. -/
noncomputable def jsp87DivCard (P : ℕ → Prop) (m : ℕ) : ℕ := (m.divisors.filter P).card

/-- **Monotonicity of the counting function in `P`.** -/
theorem jsp87DivCard_mono {P Q : ℕ → Prop} (hPQ : ∀ d, P d → Q d) (m : ℕ) :
    jsp87DivCard P m ≤ jsp87DivCard Q m := by
  rw [jsp87DivCard, jsp87DivCard]
  refine Finset.card_le_card ?_
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, hPQ _ hd.2⟩

/-- The counting function never exceeds `m` itself. -/
theorem jsp87DivCard_le_self (P : ℕ → Prop) (m : ℕ) : jsp87DivCard P m ≤ m := by
  rw [jsp87DivCard]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (Nat.card_divisors_le_self m)

/-- **A divisor counting function is strictly positive whenever `1` is counted.** -/
theorem jsp87DivCard_pos_of_one (P : ℕ → Prop) {m : ℕ} (hm : 1 ≤ m) (hP : P 1) :
    0 < jsp87DivCard P m := by
  rw [jsp87DivCard]
  refine Finset.card_pos.mpr ⟨1, ?_⟩
  refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨m, by ring⟩, by omega⟩, hP⟩

/-- **The prime case of the counting function is `ω`.** -/
theorem jsp87DivCard_primes (m : ℕ) : jsp87DivCard (fun d => d.Prime) m = omega m := by
  rw [jsp87DivCard, show omega m = (m.primeFactors).card from rfl]
  refine Nat.le_antisymm (Finset.card_le_card ?_) (Finset.card_le_card ?_)
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    rw [Nat.mem_primeFactors]
    exact ⟨hd.2, hd.1.1, hd.1.2⟩
  · intro d hd
    rw [Nat.mem_primeFactors] at hd
    simp only [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hd.2.1, hd.2.2⟩, hd.1⟩

/-- **The unrestricted counting function is the divisor-counting function.**
`jsp87DivCard (fun _ => True) n = #n.divisors = τ n` for every `n`. -/
theorem jsp87DivCard_true (n : ℕ) :
    jsp87DivCard (fun _ => True) n = n.divisors.card := by
  rw [jsp87DivCard]
  refine Nat.le_antisymm (Finset.card_le_card ?_) (Finset.card_le_card ?_)
  · intro d hd
    simp only [Finset.mem_filter] at hd
    exact hd.1
  · intro d hd
    simp only [Finset.mem_filter]
    exact ⟨hd, trivial⟩

/-- **The `P`-divisors of `m` inside `[1, m]` are exactly the `P`-divisors.**  Used to
pass from the `Icc`-form of the counting function to the `Nat.divisors`-form. -/
theorem jsp87DivCard_Icc (P : ℕ → Prop) {m : ℕ} (hm : 1 ≤ m) :
    ((Finset.Icc 1 m).filter (fun d => P d ∧ d ∣ m)) = m.divisors.filter P := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd1, hd2⟩, hP, hd⟩
    exact ⟨⟨hd, by omega⟩, hP⟩
  · rintro ⟨⟨hd, hne⟩, hP⟩
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    exact ⟨⟨by omega, Nat.le_of_dvd (by omega) hd⟩, hP, hd⟩

/-! ## 2. The master double sum -/

/-- **The summand of the master double sum**: the weight of the column `d` at row
`n`, when `d` is a `P`-element dividing `n`. -/
noncomputable def jsp87LamG (P : ℕ → Prop) (c : ℕ × ℕ) : ℝ :=
  if P c.2 ∧ 1 ≤ c.1 ∧ c.2 ∣ c.1 then ((2 : ℝ) ^ (c.1 + 1))⁻¹ else 0

theorem jsp87LamG_nonneg (P : ℕ → Prop) (c : ℕ × ℕ) : 0 ≤ jsp87LamG P c := by
  unfold jsp87LamG
  split_ifs <;> positivity

/-- **Summing a column of the master double sum gives the counting function.** -/
theorem tsum_jsp87LamG_snd (P : ℕ → Prop) (n : ℕ) :
    (∑' d : ℕ, jsp87LamG P (n, d))
      = ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
  classical
  have hfun : (fun d : ℕ => jsp87LamG P (n, d))
      = fun d => (if 1 ≤ n ∧ P d ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
    funext d
    by_cases h1 : 1 ≤ n <;> simp [jsp87LamG, h1]
  rw [hfun, jsp87DivCard]
  have hzero : ∀ d ∉ Finset.range (n + 1),
      (if 1 ≤ n ∧ P d ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) = 0 := by
    intro d hd
    simp only [Finset.mem_range] at hd
    split_ifs with hc
    · obtain ⟨_, _, hdvd⟩ := hc
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    · rfl
  rw [tsum_eq_sum hzero]
  by_cases hn0 : n = 0
  · subst n
    have hzero' : (fun d : ℕ =>
        (if 1 ≤ 0 ∧ P d ∧ d ∣ 0 then ((2 : ℝ) ^ (0 + 1))⁻¹ else 0)) = fun _ => (0 : ℝ) := by
      funext d
      split_ifs with h
      · omega
      · rfl
    have hcard : (0 : ℕ).divisors.filter P = ∅ := by
      ext d
      simp
    rw [hzero', Finset.sum_const_zero, hcard, Finset.card_empty]
    norm_num
  · have hnpos : 1 ≤ n := by omega
    have hdrop : (∑ d ∈ Finset.range (n + 1), (if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℕ) else 0))
        = ∑ d ∈ Finset.range (n + 1), (if P d ∧ d ∣ n then (1 : ℕ) else 0) := by
      refine Finset.sum_congr (M := ℕ)
        (f := fun d => (if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℕ) else 0))
        (g := fun d => (if P d ∧ d ∣ n then (1 : ℕ) else 0)) rfl fun d hd => ?_
      by_cases hc : P d ∧ d ∣ n
      · rw [if_pos ⟨hnpos, hc.1, hc.2⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
    have hnat : (∑ d ∈ Finset.range (n + 1), (if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℕ) else 0))
        = jsp87DivCard P n := by
      have hboole : (∑ d ∈ Finset.range (n + 1), (if P d ∧ d ∣ n then (1 : ℕ) else 0))
          = (((Finset.range (n + 1)).filter (fun d => P d ∧ d ∣ n)).card : ℕ) :=
        Finset.sum_boole _ _
      have hfin : ((Finset.range (n + 1)).filter (fun d => P d ∧ d ∣ n))
          = n.divisors.filter P := by
        refine Finset.Subset.antisymm ?_ ?_
        · intro d hd
          simp only [Finset.mem_filter, Finset.mem_range] at hd
          exact Finset.mem_filter.mpr
            ⟨Nat.mem_divisors.mpr ⟨hd.2.2, by omega⟩, hd.2.1⟩
        · intro d hd
          simp only [Finset.mem_filter, Nat.mem_divisors] at hd
          obtain ⟨hdv, hne⟩ := hd.1
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hnpos hdv), hd.2, hdv⟩
      rw [hdrop, hboole, hfin, jsp87DivCard]
    have hsplit : (∑ d ∈ Finset.range (n + 1),
          (if 1 ≤ n ∧ P d ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) : ℝ)
        = (∑ d ∈ Finset.range (n + 1), (if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℝ) else 0))
            * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      calc (∑ d ∈ Finset.range (n + 1),
          (if 1 ≤ n ∧ P d ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) : ℝ)
          = ∑ d ∈ Finset.range (n + 1),
              ((if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℝ) else 0)
                * ((2 : ℝ) ^ (n + 1))⁻¹) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            by_cases hc : 1 ≤ n ∧ P d ∧ d ∣ n <;> simp [hc]
        _ = (∑ d ∈ Finset.range (n + 1), (if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℝ) else 0))
            * ((2 : ℝ) ^ (n + 1))⁻¹ :=
          (Finset.sum_mul (s := Finset.range (n + 1))
            (f := fun d => (if 1 ≤ n ∧ P d ∧ d ∣ n then (1 : ℝ) else 0))
            (a := ((2 : ℝ) ^ (n + 1))⁻¹)).symm
    rw [hsplit]
    congr 1
    exact_mod_cast hnat

/-- The double sum over `P`-divisors is summable. -/
theorem summable_jsp87LamG (P : ℕ → Prop) : Summable (jsp87LamG P) := by
  classical
  refine (summable_prod_of_nonneg (jsp87LamG_nonneg P)).2 ⟨?_, ?_⟩
  · intro n
    have hs : (fun d : ℕ => jsp87LamG P (n, d)).HasFiniteSupport := by
      refine Set.Finite.subset
        (Finset.finite_toSet (s := (Finset.range (n + 1) : Finset ℕ))) ?_
      intro d hd
      simp only [Function.mem_support] at hd
      by_cases hn0 : n = 0
      · simp [jsp87LamG, hn0] at hd
      · have hguard : P d ∧ 1 ≤ n ∧ d ∣ n := by
          by_contra hcon
          simp [jsp87LamG, hcon] at hd
        have hle : d ≤ n := Nat.le_of_dvd (by omega) hguard.2.2
        exact Finset.mem_coe.2 (Finset.mem_range.mpr (by omega))
    exact summable_of_hasFiniteSupport hs
  · have h1 : (fun n : ℕ => ∑' d : ℕ, jsp87LamG P (n, d))
      = fun n => ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
      funext (tsum_jsp87LamG_snd P)
    rw [h1]
    refine Summable.of_nonneg_of_le
      (g := fun n : ℕ => ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      (f := fun n : ℕ => ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) ?_ ?_ ?_
    · intro n
      exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
    · intro n
      have hcard : (jsp87DivCard P n : ℕ) ≤ n := jsp87DivCard_le_self P n
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    · exact summable_nat_mul_two_pow_neg

/-- **Reindexing the multiples of `d`, for `1 ≤ d`** — the general form of
`LambertSeries.sum_multiples_reindex`, which is stated for primes only. -/
theorem sum_multiples_reindex' (p N : ℕ) (hp : 1 ≤ p) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, (if 1 ≤ n ∧ p ∣ n then w n else 0) : ℝ)
      = ∑ k ∈ Finset.range N, (if 1 ≤ k ∧ p * k < N then w (p * k) else 0) := by
  have hp0 : 0 < p := by omega
  set A : Finset ℕ := Finset.range N with hA
  set S : Finset ℕ := A.filter (fun n => 1 ≤ n ∧ p ∣ n) with hS
  set T : Finset ℕ := A.filter (fun k => 1 ≤ k ∧ p * k < N) with hT
  have hleft : (∑ n ∈ A, (if 1 ≤ n ∧ p ∣ n then w n else 0) : ℝ) = ∑ n ∈ S, w n := by
    rw [hS, Finset.sum_filter]
  have hright : (∑ k ∈ A, (if 1 ≤ k ∧ p * k < N then w (p * k) else 0) : ℝ)
      = ∑ k ∈ T, w (p * k) := by
    rw [hT, Finset.sum_filter]
  have hmem : ∀ k ∈ T, p * k ∈ S := by
    intro k hk
    rw [hT, Finset.mem_filter, hA, Finset.mem_range] at hk
    obtain ⟨hkN, hk1, hk2⟩ := hk
    have hk0 : 0 < k := by omega
    have h1pk : 1 ≤ p * k := by
      have hpos : 0 < p * k := Nat.mul_pos hp0 hk0
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hk2, ⟨h1pk, dvd_mul_of_dvd_left (dvd_refl p) k⟩⟩
  have hinj : ∀ a ∈ T, ∀ b ∈ T, p * a = p * b → a = b := by
    intro a _ b _ heq
    exact Nat.mul_left_cancel hp0 heq
  have hsurj : ∀ b : ℕ, b ∈ S →
      Exists fun a : ℕ => Exists fun (_ha : a ∈ T) => p * a = b := by
    intro m hm
    rw [hS, Finset.mem_filter, hA, Finset.mem_range] at hm
    obtain ⟨hmN, hm1, ⟨k, hk⟩⟩ := hm
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hz | hk'
      · rw [hz, Nat.mul_zero] at hk
        omega
      · exact hk'
    have hkk : k ≤ p * k := Nat.le_mul_of_pos_left k hp0
    have hpklt : p * k < N := by rw [← hk]; exact hmN
    have hklt : k < N := by omega
    have hk1 : 1 ≤ k := by omega
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, ⟨hk1, hpklt⟩⟩, hk.symm⟩
  have hbij : (∑ k ∈ T, w (p * k) : ℝ) = ∑ n ∈ S, w n :=
    Finset.sum_bij (fun k (_ : k ∈ T) => p * k) hmem hinj hsurj (fun _ _ => rfl)
  rw [hleft, hright]
  exact hbij.symm

/-- **The geometric column of the master double sum, for `1 ≤ d`:** the positive
multiples of `d` carry exactly the weight `1 / (2 ^ (d+1) - 2)`. -/
theorem hasSum_jsp87Col (d : ℕ) (hd : 1 ≤ d) :
    HasSum (fun n : ℕ => (if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0))
      ((2 : ℝ) ^ (d + 1) - 2)⁻¹ := by
  have hd0 : 0 < d := by omega
  have hnonneg : ∀ n : ℕ,
      (if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) ≥ 0 := by
    intro n
    split_ifs <;> positivity
  have hle : ∀ n : ℕ,
      (if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)
        ≤ ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    by_cases h1 : 1 ≤ n
    · by_cases h2 : d ∣ n
      · rw [if_pos ⟨h1, h2⟩]
        have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        have hkey : 1 * ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (n : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hcast
            (show (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹ by positivity)
        rwa [one_mul] at hkey
      · rw [if_neg (fun h => h2 h.2)]
        positivity
    · rw [if_neg (fun h => h1 h.1)]
      positivity
  have hsum : Summable (fun n : ℕ =>
      (if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)) :=
    Summable.of_nonneg_of_le hnonneg hle summable_nat_mul_two_pow_neg
  have hterm : ∀ n : ℕ,
      ‖(if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)‖
        ≤ ((n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
    exact hle n
  have hnorm : Summable fun n : ℕ =>
      ‖(if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm summable_nat_mul_two_pow_neg
  have htend1 : Filter.Tendsto (fun M : ℕ => Finset.range (d * M)) Filter.atTop
      Filter.atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone
      (f := fun M : ℕ => Finset.range (d * M)) ?_ ?_
    · intro M N hMN
      have hMN' : d * M ≤ d * N := Nat.mul_le_mul_left d hMN
      intro x hx
      simp only [Finset.mem_range] at *
      omega
    · intro x
      have hx : x + 1 ≤ d * (x + 1) := Nat.le_mul_of_pos_left (x + 1) hd0
      exact ⟨x + 1, Finset.mem_range.mpr (by omega)⟩
  have hseq : ∀ M : ℕ,
      (∑ i ∈ Finset.range (d * M),
          (if 1 ≤ i ∧ d ∣ i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0) : ℝ)
        = ∑ k ∈ Finset.range M, (if 1 ≤ k then ((2 : ℝ) ^ (d * k + 1))⁻¹ else 0) := by
    intro M
    have hre := sum_multiples_reindex' d (d * M) hd (fun m => ((2 : ℝ) ^ (m + 1))⁻¹)
    have hle' : M ≤ d * M := Nat.le_mul_of_pos_left M hd0
    have hM : Finset.range M ⊆ Finset.range (d * M) := by
      intro k hk
      simp only [Finset.mem_range] at *
      omega
    have hzero : ∀ k ∈ Finset.range (d * M), k ∉ Finset.range M →
        (if 1 ≤ k ∧ d * k < d * M then ((2 : ℝ) ^ (d * k + 1))⁻¹ else 0) = 0 := by
      intro k hk1 hk2
      simp only [Finset.mem_range] at hk1 hk2
      have hkn : M ≤ k := by omega
      have hnot : ¬(d * k < d * M) := by
        simp only [Nat.mul_lt_mul_left hd0]
        omega
      rw [if_neg (fun h => hnot h.2)]
    rw [hre]
    rw [← Finset.sum_subset
      (f := fun k => (if 1 ≤ k ∧ d * k < d * M then ((2 : ℝ) ^ (d * k + 1))⁻¹ else 0))
      hM hzero]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    simp only [Nat.mul_lt_mul_left hd0, hk, and_true]
  have htend2 : Filter.Tendsto
      (fun M : ℕ => ∑ i ∈ Finset.range (d * M),
        (if 1 ≤ i ∧ d ∣ i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0))
      Filter.atTop (nhds ((2 : ℝ) ^ (d + 1) - 2)⁻¹) := by
    refine (hasSum_lambert_geometric d hd).tendsto_sum_nat.congr
      (f₂ := fun M : ℕ => ∑ i ∈ Finset.range (d * M),
        (if 1 ≤ i ∧ d ∣ i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0)) ?_
    exact fun M => (hseq M).symm
  exact hasSum_of_subseq_of_summable hnorm htend1 htend2

/-- **A single column of the master double sum**, for every predicate `P` and every
`d`: the multiples of `d` carry exactly the Lambert weight `1 / (2 ^ (d+1) - 2)`
whenever `d` is a `P`-element, and nothing at all otherwise. -/
theorem hasSum_jsp87LamG_fst (P : ℕ → Prop) (d : ℕ) :
    HasSum (fun n : ℕ => jsp87LamG P (n, d))
      (if P d ∧ 1 ≤ d then ((2 : ℝ) ^ (d + 1) - 2)⁻¹ else 0) := by
  classical
  by_cases hd : 1 ≤ d
  · by_cases hPd : P d
    · have hfun : (fun n : ℕ => jsp87LamG P (n, d))
          = fun n => (if 1 ≤ n ∧ d ∣ n then ((2 : ℝ) ^ (n + 1))⁻¹ else 0) := by
        funext n
        by_cases h1n : 1 ≤ n <;> by_cases hdvn : d ∣ n <;>
          simp [jsp87LamG, hPd, h1n, hdvn]
      rw [hfun, if_pos ⟨hPd, hd⟩]
      exact hasSum_jsp87Col d hd
    · have hzero : (fun n : ℕ => jsp87LamG P (n, d)) = fun _ => (0 : ℝ) := by
        funext n
        simp [jsp87LamG, hPd]
      rw [hzero, if_neg (by simp [hPd])]
      simpa using (Summable.zero : Summable (fun _ : ℕ => (0 : ℝ))).hasSum
  · by_cases hd0 : d = 0
    · subst hd0
      have hzero : (fun n : ℕ => jsp87LamG P (n, 0)) = fun _ => (0 : ℝ) := by
        funext n
        simp only [jsp87LamG, Nat.zero_dvd]
        rw [if_neg (fun h => (by omega : ¬(1 ≤ n)) h.2.1)]
      rw [hzero, if_neg (by simp [hd])]
      simpa using (Summable.zero : Summable (fun _ : ℕ => (0 : ℝ))).hasSum
    · have hzero : (fun n : ℕ => jsp87LamG P (n, d)) = fun _ => (0 : ℝ) := by
        funext n
        have hdz : d = 0 := by omega
        have hne : ∀ h : d ∣ n, 1 ≤ d := fun _ => False.elim (absurd hdz hd0)
        simp only [jsp87LamG]
        rw [if_neg (fun h => hd (hne h.2.2))]
      rw [hzero, if_neg (by simp [hd])]
      simpa using (Summable.zero : Summable (fun _ : ℕ => (0 : ℝ))).hasSum

/-! ## 3. THE MASTER LAMBERT IDENTITY (Erdős #257) -/

/-- **THE MASTER LAMBERT IDENTITY.**  For every predicate `P` on `ℕ`,

```
∑' m, #{ d : d ∣ m,  P d } · 2^{-(m+1)}
  =  ∑' d, if P d ∧ 1 ≤ d then 1 / (2 ^ (d+1) - 2) else 0 .
```

For `P = fun d => d.Prime` the left-hand side is the Erdős series and the
right-hand side is `jsp87_lambert` of `LambertIdentity.lean`.  This is the general
form that Tao–Teräväinen cite as "a special case of [Erdős #257]"; the tree had
proved only the prime case. -/
theorem jsp87_lambert_master (P : ℕ → Prop) :
    (∑' n : ℕ, ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑' d : ℕ, (if P d ∧ 1 ≤ d then ((2 : ℝ) ^ (d + 1) - 2)⁻¹ else 0) := by
  classical
  have hswap : (∑' c : ℕ × ℕ, jsp87LamG P c)
      = ∑' d : ℕ, ∑' n : ℕ, jsp87LamG P (n, d) := by
    rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) (jsp87LamG P)]
    simpa [Function.swap] using (summable_jsp87LamG P).prod_symm.tsum_prod
  have h1 : (∑' c : ℕ × ℕ, jsp87LamG P c)
      = ∑' n : ℕ, ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    rw [(summable_jsp87LamG P).tsum_prod]
    exact tsum_congr fun n => tsum_jsp87LamG_snd P n
  rw [← h1, hswap]
  exact tsum_congr fun d => (hasSum_jsp87LamG_fst P d).tsum_eq

/-- **The summability input of the classical Lambert form**: the series
`∑' d, if P d then 1 / (2 ^ d - 1) else 0` converges as soon as every `P`-element is
`≥ 2`, because `1/(2^d - 1) ≤ 2 / 2^d`. -/
theorem summable_lambert_generic (P : ℕ → Prop) (hP : ∀ d, P d → 2 ≤ d) :
    Summable (fun d : ℕ => (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0)) := by
  refine Summable.of_nonneg_of_le
    (g := fun d : ℕ => (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0))
    (f := fun d : ℕ => 2 * ((2 : ℝ) ^ d)⁻¹) ?_ ?_ ?_
  · intro d
    by_cases hPd : P d
    · rw [if_pos hPd]
      have h2 : 2 ≤ d := hP d hPd
      exact inv_nonneg.mpr (by linarith [two_pow_gt_one h2])
    · rw [if_neg hPd]
  · intro d
    by_cases hPd : P d
    · rw [if_pos hPd]
      have h2 : 2 ≤ d := hP d hPd
      have hgt : (1 : ℝ) < (2 : ℝ) ^ d := two_pow_gt_one h2
      have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (d - 1) := by
        rw [← pow_one (2 : ℝ)]
        exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
      have htwo' : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ (d - 1) := by
        calc (2 : ℝ) ^ d = (2 : ℝ) ^ ((d - 1) + 1) := by congr 1 <;> omega
          _ = 2 ^ (d - 1) * 2 := pow_succ _ _
          _ = 2 * 2 ^ (d - 1) := by ring
      have harith : (2 : ℝ) ^ (d - 1) ≤ (2 : ℝ) ^ d - 1 := by
        rw [htwo']
        linarith
      have hle : ((2 : ℝ) ^ d - 1)⁻¹ ≤ 2 * ((2 : ℝ) ^ d)⁻¹ := by
        have hA : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by linarith
        have hB0 : ((2 : ℝ) ^ d - 1)⁻¹ ≤ ((2 : ℝ) ^ (d - 1))⁻¹ :=
          (inv_le_inv₀ hA hpos).2 harith
        have hB : ((2 : ℝ) ^ (d - 1))⁻¹ = 2 * ((2 : ℝ) ^ d)⁻¹ := by
          have hd2 : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by rw [htwo']; ring
          rw [hd2]
          field_simp
        rw [hB] at hB0
        exact hB0
      exact hle
    · rw [if_neg hPd]
      positivity
  · rw [show (fun d : ℕ => 2 * ((2 : ℝ) ^ d)⁻¹) = fun d => 2 * ((2 : ℝ)⁻¹ ^ d) by
        funext d; rw [inv_pow]]
    exact Summable.mul_left 2
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1))

/-- **The master identity in the classical (unshifted) denominators**, for every `P`
whose elements are `≥ 2`: `1/(2^{d+1} - 2) = (1/2) · 1/(2^d - 1)`. -/
theorem jsp87_lambert_classic_master (P : ℕ → Prop) (hP : ∀ d, P d → 2 ≤ d) :
    2 * (∑' n : ℕ, ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = ∑' d : ℕ, (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0) := by
  classical
  have hkey : ∀ d : ℕ, (if P d ∧ 1 ≤ d then ((2 : ℝ) ^ (d + 1) - 2)⁻¹ else 0)
      = (2 : ℝ)⁻¹ * (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0) := by
    intro d
    by_cases hPd : P d
    · by_cases hd1 : 1 ≤ d
      · have h2 : 2 ≤ d := hP d hPd
        rw [if_pos ⟨hPd, hd1⟩, if_pos hPd]
        have hA : (2 : ℝ) ^ (d + 1) - 2 = 2 * ((2 : ℝ) ^ d - 1) := by
          rw [pow_succ]
          ring
        rw [hA]
        field_simp
      · have h2 : 2 ≤ d := hP d hPd
        exact False.elim (hd1 (by omega))
    · rw [if_neg (fun h => hPd h.1), if_neg hPd]
      ring
  have hs2 : Summable (fun d : ℕ => (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0)) :=
    summable_lambert_generic P hP
  calc 2 * (∑' n : ℕ, ((jsp87DivCard P n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = 2 * ∑' d : ℕ, (if P d ∧ 1 ≤ d then ((2 : ℝ) ^ (d + 1) - 2)⁻¹ else 0) := by
        rw [jsp87_lambert_master P]
    _ = 2 * ∑' d : ℕ, (2 : ℝ)⁻¹ * (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0) := by
        apply congrArg (fun x : ℝ => 2 * x)
        exact tsum_congr (fun d => hkey d)
    _ = 2 * ((2 : ℝ)⁻¹ * ∑' d : ℕ, (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0)) :=
        congrArg (fun x : ℝ => 2 * x) (Summable.tsum_mul_left (2 : ℝ)⁻¹ hs2)
    _ = ∑' d : ℕ, (if P d then ((2 : ℝ) ^ d - 1)⁻¹ else 0) := by
        have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [hhalf]
        ring

/-! ## 4. THE `+1` SERIES AS AN ALTERNATING SUM OF DILATIONS (arXiv:2512.01739 §5.2) -/

/-- `x = 2^{-n}`, the dilation variable at the place `n`. -/
noncomputable def jsp87X (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

theorem jsp87X_pos (n : ℕ) : 0 < jsp87X n := by
  unfold jsp87X
  positivity

theorem jsp87X_le_one (n : ℕ) : jsp87X n ≤ 1 := by
  unfold jsp87X
  exact (inv_le_one₀ (by positivity)).2 (by
    cases n with
    | zero => norm_num
    | succ k =>
      have h := Nat.one_lt_two_pow (by omega : k + 1 ≠ 0)
      exact_mod_cast (le_of_lt h))

theorem jsp87X_pow (n k : ℕ) : (jsp87X n) ^ k = ((2 : ℝ) ^ (n * k))⁻¹ := by
  rw [jsp87X, inv_pow, ← pow_mul, Nat.mul_comm]

/-- **The truncated alternating geometric series.**  For `x ≠ -1`,

```
x / (1 + x)  =  ∑_{k<J} (-1)^k x^{k+1}  +  x (-x)^J / (1 + x) ,
```

the exact finite identity on which the whole of §5.2 of arXiv:2512.01739 rests. -/
theorem sum_alt_geom (J : ℕ) (x : ℝ) (hx : (1 : ℝ) + x ≠ 0) :
    x / (1 + x) = (∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * x ^ (k + 1))
      + x * (-x) ^ J / (1 + x) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

/-- **THE PER-PLACE EXPANSION.**  For every `n` and `J`,

```
ω(n)/(2^n + 1)  =  ω(n) ∑_{k<J} (-1)^k 2^{-(k+1)n}  +  ω(n) 2^{-n} (-2^{-n})^J / (1 + 2^{-n}) .
```

Purely finite; no analysis is involved. -/
theorem jsp87_plusTerm_geom (n J : ℕ) :
    ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n + 1)⁻¹
      = ((omega n : ℕ) : ℝ) * (∑ k ∈ Finset.range J, ((-1) ^ k : ℝ) * (jsp87X n) ^ (k + 1))
        + ((omega n : ℕ) : ℝ) * jsp87X n * (-(jsp87X n)) ^ J / (1 + jsp87X n) := by
  have hx : (1 : ℝ) + jsp87X n ≠ 0 := by
    have := jsp87X_pos n
    unfold jsp87X at *
    positivity
  have hone : ((2 : ℝ) ^ n + 1)⁻¹ = jsp87X n / (1 + jsp87X n) := by
    have hA : ((2 : ℝ) ^ n + 1 : ℝ) ≠ 0 := by
      have : (0 : ℝ) < 2 ^ n + 1 := by positivity
      exact ne_of_gt this
    have hB : (1 + jsp87X n : ℝ) ≠ 0 := hx
    rw [eq_div_iff hB]
    unfold jsp87X
    field_simp
  rw [hone, sum_alt_geom J (jsp87X n) hx]
  ring

/-- **THE REMAINDER OF THE TRUNCATED EXPANSION**, the object whose size has to be
controlled in §5.3 of arXiv:2512.01739. -/
noncomputable def jsp87PlusRem (J : ℕ) : ℝ :=
  ∑' n : ℕ, ((omega n : ℕ) : ℝ) * jsp87X n * (-(jsp87X n)) ^ J / (1 + jsp87X n)

end JSP87
