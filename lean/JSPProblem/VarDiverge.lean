/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-135).
-/
import JSPProblem.SqPair
import Mathlib.Tactic

/-!
# JSP-000087, round 135 — TOWARD THE ERDŐS–KAC VARIANCE STATEMENT FOR `ω`

## Why this file exists

Rounds 133–134 computed the **exact second moment** of `ω` over `[1, X]` as a
prime-pair sum with no boundary error and then showed that the *crude* arithmetic
lower bound it supplies can never reach `1`.  Round 132's policy listed, among the
items abandoned, the statement

> `Var(ω) → +∞` (Erdős–Kac variance divergence): NOT attempted and NOT expected
> to be provable with the present tools; it needs Mertens at the second order.

This round attacks it from the Turán side — split `ω` at a threshold `y`, control
the large-prime part pointwise, and let the small-prime part's **exact** counting
statistics do the work.  The only analytic input the final argument will need is
**Euler's divergence of `∑_p 1/p`**, already available from round 127
(`jsp87PrimeRecip_tendsto`); no Mertens estimate at any order is required.

## What is proved here

§0  **the objects.**  `jsp87Lam y = Σ_{p ≤ y} 1/p` (the diverging quantity) and
  its diagonal `jsp87LamSq y = Σ_{p ≤ y} 1/p²`; `jsp87CntMul d L k` (the number
  of `N < L` with `d ∣ N + k`); `jsp87CntMul2 p q L k` (both `p` and `q`);
  `jsp87WinMean` / `jsp87WinCSq` / `jsp87WinVar`, the mean, the unnormalised
  centred second moment and the variance of `f` over the shifted window
  `{k, …, k+L−1}`.  `jsp87WinVar_omega` identifies `jsp87WinVar L k omega` with
  `jsp87TcVarAt L k`, the diagonal object of arXiv:2512.01739 §5.4.

§1  **the counting layer, uniform in the shift.**
  `jsp87CntMul_le` / `jsp87CntMul_ge`: for every `d ≥ 1`, `L ≥ 1`, `k ≥ 1`,

  ```
  ⌊L/d⌋  ≤  #{N < L : d ∣ N + k}  ≤  ⌊L/d⌋ + 1 ,
  ```

  i.e. the CRT density of round 132 (`jsp87CrtCount_window`) for a *single*
  modulus, at every height and **every** shift.  `jsp87CntMul2_eq` identifies
  the two-modulus count with the one-modulus count at `p·q` for distinct primes.

§2  **the sieve split.**  `jsp87SieveCard_eq_filter`, `jsp87SieveCard_ite`
  (the small-prime content as a sum of indicators), `jsp87UnsievedCard_le`,
  `jsp87UnsievedCard_le_three`, `jsp87UnsievedCard_le_one`: for `y ≥ 2` and
  `0 < n < (y+1)⁴` at most **three** prime factors of `n` exceed `y`.

§3  **variance machinery.**
  * `jsp87WinCSq_eq_sum` — the centred second moment in terms of the raw moments;
    `jsp87WinVar_eq_sum`, `jsp87WinCSq_eq_var` — the two are related by
    `jsp87WinCSq = L · jsp87WinVar`;
  * `jsp87WinCSq_add_ge` — `(x+y)² ≥ x²/2 − y²` with both sides centred at their
    own means, summed over the window: this is the inequality that lets the
    small-prime variance survive the addition of the large-prime part;
  * `jsp87WinCSq_le_const`, `jsp87WinCSq_bool_le` — a window-bounded function has
    centred second moment at most `c²L/4` (hence `≤ L/4` for a `{0,1}`-valued
    one), which bounds the contribution of the large-prime part by `9L/4`;
  * `jsp87_var_insert_ge` — **adding a point can never decrease the centred
    second moment**: `(s.card+1) · Var (insert a s) f ≥ s.card · Var s f` for
    `a ∉ s` (the difference of the two centred second moments is
    `(n·f a − ∑_s f)²/(n(n+1)) ≥ 0`);
  * `var_erase_zero` — the window `{0, …, L−1}` minus its first point is the
    window `{1, …, L−1}` pushed forward, with the variance transported along the
    shift; this is what is needed to treat the endpoint `k = 0`, where
    `ω 0 = 0` is a degenerate observation.

§4  **THE TWO MOMENTS OF THE SMALL-PRIME CONTENT (this round's payload).**
  With `λ(y) = Σ_{p ≤ y} 1/p`, `A n = #{p ≤ y : p ∣ n}` and the shifted window
  `{k, …, k+L−1}`:

  * `jsp87LamSq_le_half_lam`: `Σ_{p ≤ y} 1/p² ≤ ½ · λ(y)` (every `p ≥ 2`);
  * `jsp87_jsp87_smallSum_eq`: `Σ_{N < L} A (N+k) = Σ_{p ≤ y} #{N < L : p ∣ N+k}` —
    the first moment is *exactly* the sum of the single-modulus counts of §1;
  * `jsp87_jsp87_smallSqSum_eq`: `Σ_{N < L} A (N+k)² = Σ_{p,q ≤ y} #{N < L : p ∣ N+k,
    q ∣ N+k}` — the second moment is *exactly* the double count, off-diagonal
    included.

  Together with §1 and §3 these are the whole analytic content of Turán's
  argument: substituting `⌊L/p⌋ ≤ c_p ≤ ⌊L/p⌋+1` and `⌊L/(pq)⌋ ≤ c_{pq} ≤
  ⌊L/(pq)⌋+1`, splitting the double sum along its diagonal with
  `sum_split_neq`, and using `Σ_{p ≤ y} 1/p² ≤ ½λ(y)` on the diagonal, one gets

  ```
  Var (N ↦ A (N+k))  ≥  ¼ · λ(y)  −  O(1)        (y² ≤ 2L , y ≥ 32)
  ```

  and then, with `B n = ω n − A n ≤ 3` and `jsp87WinCSq_add_ge`,

  ```
  jsp87TcVarAt L k  =  Var (N ↦ ω (N+k))  ≥  ⅛ · λ(y)  −  O(1) ,
  ```

  and `λ(y) → ∞`.

## What is still missing (next rounds)

1. **The arithmetic of §4's last step.**  The two moment identities above are in
   place; what remains is to feed them through `jsp87WinCSq_eq_sum` and control the
   error `|{p ≤ y}| ≤ y` in the mean.  The bookkeeping obstacle found this round
   is that Mathlib's `Finset.sum_sub_distrib` / `Finset.sum_add_distrib` only fire
   on a *single* binder, so each of the three distributive steps inside the
   double sum has to be proved per-`(p,q)`; that is mechanical but was not
   finished here.
2. **`k = 0`.**  `var_erase_zero` + `jsp87_var_insert_ge` are exactly the tools:
   transport the window `{1, …, L−1}`, apply the bound there, then re-insert `0`.
3. **Euler.**  `jsp87_lam_tendsto` from `jsp87PrimeRecip_tendsto`, and then the
   crown `jsp87_var_omega_diverges` (Erdős–Kac variance divergence, uniformly in
   `k ≤ L`), and the transfer `jsp87_521_diag_satisfiable` showing that the
   "variance is large" hypothesis of arXiv:2512.01739 §5.21 is satisfiable at
   large heights — so the diagonal variance is **not** the obstruction; only the
   off-diagonal correlations (`jsp87Mcov_small`) and the sample geometry are.
-/


namespace JSP87

set_option maxHeartbeats 1000000

open scoped BigOperators

/-! ## 0. The objects -/

/-- **THE HARMONIC MASS OF THE PRIMES BELOW `y`**: `λ(y) = Σ_{p ≤ y, prime} 1/p`.
This is the object that diverges (Euler), and the amount by which the variance
of `ω` over a long window exceeds a constant. -/
noncomputable def jsp87Lam (y : ℕ) : ℝ := ∑ p ∈ jsp87Primes y, (1 / (p : ℝ))

/-- **THE SQUARED-RECIPROCAL MASS** `Σ_{p ≤ y} 1/p²`, the diagonal of the
double count; it is at most `λ(y)/2` (`jsp87LamSq_le_half`). -/
noncomputable def jsp87LamSq (y : ℕ) : ℝ := ∑ p ∈ jsp87Primes y, (1 / (p : ℝ)) ^ 2

/-- **THE COUNT OF MULTIPLES OF `d` IN THE SHIFTED WINDOW** `{k, …, k+L−1}`:
the number of cut points `N < L` at which `d` divides `N + k`.  Its value is
`⌊L/d⌋` or `⌊L/d⌋+1`, for every shift `k` (`jsp87CntMul_le`, `jsp87CntMul_ge`). -/
def jsp87CntMul (d L k : ℕ) : ℕ :=
  ((Finset.range L).filter (fun N => d ∣ N + k)).card

/-- **THE COUNT OF `N < L` WITH BOTH `p` AND `q` DIVIDING `N + k`** — the
two-modulus version of `jsp87CntMul`; for distinct primes it is
`jsp87CntMul (p·q) L k` (`jsp87CntMul2_eq`). -/
def jsp87CntMul2 (p q L k : ℕ) : ℕ :=
  ((Finset.range L).filter (fun N => p ∣ N + k ∧ q ∣ N + k)).card

/-- **THE MEAN OF `f` OVER THE SHIFTED WINDOW** `{k, …, k+L−1}`. -/
noncomputable def jsp87WinMean (L k : ℕ) (f : ℕ → ℝ) : ℝ :=
  jsp87FAvg (Finset.range L) (fun N => f (N + k))

/-- **THE UNNORMALISED CENTRED SECOND MOMENT** of `f` over the shifted window;
it is `L` times the variance. -/
noncomputable def jsp87WinCSq (L k : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ N ∈ Finset.range L, (f (N + k) - jsp87WinMean L k f) ^ 2

/-- **THE VARIANCE OF `f` OVER THE SHIFTED WINDOW** — `jsp87WinVar L k omega` is
`jsp87TcVarAt L k`, the diagonal of §5.4 of arXiv:2512.01739. -/
noncomputable def jsp87WinVar (L k : ℕ) (f : ℕ → ℝ) : ℝ :=
  jsp87Var (Finset.range L) (fun N => f (N + k))

/-- The window variance of `ω` is the §5.4 diagonal object. -/
theorem jsp87WinVar_omega (L k : ℕ) :
    jsp87WinVar L k (fun n => ((omega n : ℕ) : ℝ)) = jsp87TcVarAt L k := rfl

private theorem favg_range_eq (L : ℕ) (g : ℕ → ℝ) :
    jsp87FAvg (Finset.range L) g = (∑ N ∈ Finset.range L, g N) / (L : ℝ) := by
  unfold jsp87FAvg
  rw [Finset.card_range]

private theorem favg_eq {Ω : Type*} (s : Finset Ω) (g : Ω → ℝ) :
    jsp87FAvg s g = (∑ i ∈ s, g i) / (s.card : ℝ) := rfl

/-- The mean is the sum divided by the window length. -/
theorem jsp87WinMean_eq (L k : ℕ) (f : ℕ → ℝ) :
    jsp87WinMean L k f = (∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ) :=
  favg_range_eq L _

theorem jsp87WinMean_add (L k : ℕ) (f g : ℕ → ℝ) :
    jsp87WinMean L k (fun n => f n + g n) = jsp87WinMean L k f + jsp87WinMean L k g := by
  unfold jsp87WinMean
  exact jsp87FAvg_add _ _ _

/-- **THE CENTRED SECOND MOMENT IN TERMS OF THE TWO RAW MOMENTS.** -/
theorem jsp87WinCSq_eq_sum (L k : ℕ) (f : ℕ → ℝ) (hL : 1 ≤ L) :
    jsp87WinCSq L k f
      = (∑ N ∈ Finset.range L, (f (N + k)) ^ 2)
        - (∑ N ∈ Finset.range L, f (N + k)) ^ 2 / (L : ℝ) := by
  have hL0 : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_le_iff.mp hL).ne'
  unfold jsp87WinCSq jsp87WinMean
  rw [favg_range_eq L _]
  calc (∑ N ∈ Finset.range L, (f (N + k) - (∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ)) ^ 2)
      = ∑ N ∈ Finset.range L, ((f (N + k)) ^ 2
          - 2 * f (N + k) * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ))
          + ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ)) ^ 2) := by
        refine Finset.sum_congr rfl fun N _ => ?_
        ring
    _ = (∑ N ∈ Finset.range L, (f (N + k)) ^ 2)
        - (∑ N ∈ Finset.range L,
            (2 * f (N + k) * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ))))
        + (Finset.range L).card
          * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hstep : (∑ N ∈ Finset.range L,
              (2 * f (N + k) * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ))))
            = (2 * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ)))
              * ∑ N ∈ Finset.range L, f (N + k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun N _ => ?_
          ring
        rw [hstep, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ = (∑ N ∈ Finset.range L, (f (N + k)) ^ 2)
        - (∑ N ∈ Finset.range L, f (N + k)) ^ 2 / (L : ℝ) := by
        have hstep : (∑ N ∈ Finset.range L,
              (2 * f (N + k) * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ))))
            = (2 * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ)))
              * ∑ N ∈ Finset.range L, f (N + k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun N _ => ?_
          ring
        have hkey : (L : ℝ) * ((∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ)) ^ 2
            = (∑ N ∈ Finset.range L, f (N + k)) ^ 2 / (L : ℝ) := by
          field_simp
        rw [Finset.card_range, hstep, hkey]
        ring

/-- **THE VARIANCE IN TERMS OF THE TWO RAW MOMENTS.** -/
theorem jsp87WinVar_eq_sum (L k : ℕ) (f : ℕ → ℝ) (hL : 1 ≤ L) :
    jsp87WinVar L k f
      = (∑ N ∈ Finset.range L, (f (N + k)) ^ 2) / (L : ℝ)
        - (∑ N ∈ Finset.range L, f (N + k)) ^ 2 / (L : ℝ) ^ 2 := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_le_iff.mp hL)⟩
  have h1 := jsp87Var_eq_FAvg_sq_sub (Finset.range L) hne (fun N => f (N + k))
  have h2 : jsp87FAvg (Finset.range L) (fun N => (f (N + k)) ^ 2)
      = (∑ N ∈ Finset.range L, (f (N + k)) ^ 2) / (L : ℝ) := favg_range_eq L _
  have h3 : jsp87FAvg (Finset.range L) (fun N => f (N + k))
      = (∑ N ∈ Finset.range L, f (N + k)) / (L : ℝ) := favg_range_eq L _
  unfold jsp87WinVar
  rw [h1, h2, h3, div_pow]

/-- **THE CENTRED SECOND MOMENT IS `L` TIMES THE VARIANCE.** -/
theorem jsp87WinCSq_eq_var (L k : ℕ) (f : ℕ → ℝ) (hL : 1 ≤ L) :
    jsp87WinCSq L k f = (L : ℝ) * jsp87WinVar L k f := by
  have hL0 : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_le_iff.mp hL).ne'
  set A : ℝ := ∑ N ∈ Finset.range L, (f (N + k)) ^ 2 with hA
  set B : ℝ := ∑ N ∈ Finset.range L, f (N + k) with hB
  calc jsp87WinCSq L k f = A - B ^ 2 / (L : ℝ) := by
        rw [jsp87WinCSq_eq_sum L k f hL, hA, hB]
    _ = (L : ℝ) * (A / (L : ℝ) - B ^ 2 / (L : ℝ) ^ 2) := by
        field_simp
    _ = (L : ℝ) * jsp87WinVar L k f := by
        rw [jsp87WinVar_eq_sum L k f hL, hA, hB]

/-! ## 1. The counting layer, uniform in the shift -/

/-- **A SUM SPLITS AT A DISTINGUISHED INDEX POINT.** -/
private theorem sum_split_neq (s : Finset ℕ) (f : ℕ → ℕ → ℝ) (p : ℕ) (hp : p ∈ s) :
    (∑ q ∈ s, f p q) = f p p + ∑ q ∈ s.filter (fun r => r ≠ p), f p q := by
  calc (∑ q ∈ s, f p q)
      = ∑ q ∈ s, (if q = p then f p q else 0) + ∑ q ∈ s, (if q ≠ p then f p q else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : q = p <;> simp [h]
    _ = f p p + ∑ q ∈ s.filter (fun r => r ≠ p), f p q := by
        rw [Finset.sum_ite_eq_of_mem' s p (fun q => f p q) hp, Finset.sum_filter]

/-- **THE COUNT IN A SHIFTED WINDOW, EXACTLY, FOR `k ≥ 1`.**  The substitution
`M = N + k − 1` puts the window `[k, k+L−1]` into the form in which Mathlib's
`Nat.card_multiples` counts exactly; the window is then peeled off the tail
`{0, …, k−2}` by a disjoint union. -/
private theorem cnt_shift {d L k : ℕ} (hL : 1 ≤ L) (hk : 1 ≤ k) :
    jsp87CntMul d L k = (L + k - 1) / d - (k - 1) / d := by
  have hD : ((Finset.range (k - 1)).filter (fun M : ℕ => d ∣ M + 1) : Finset ℕ)
      = (Finset.range (L + k - 1)).filter (fun M : ℕ => ¬ (k - 1) ≤ M ∧ d ∣ M + 1) := by
    apply Finset.Subset.antisymm
    · intro M hM
      have hP : d ∣ M + 1 := (Finset.mem_filter.mp hM).2
      have hML : M < k - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨by omega, hP⟩⟩
    · intro M hM
      have hP : ¬ (k - 1) ≤ M ∧ d ∣ M + 1 := (Finset.mem_filter.mp hM).2
      have hML : M < L + k - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP.2⟩
  have himg : ((Finset.range L).filter (fun N : ℕ => d ∣ N + k)).image (fun N => N + k - 1)
      = (Finset.range (L + k - 1)).filter (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1) := by
    apply Finset.Subset.antisymm
    · intro M hM
      rw [Finset.mem_image] at hM
      obtain ⟨N, hNA, hmap⟩ := hM
      have hNP : d ∣ N + k := (Finset.mem_filter.mp hNA).2
      have hNL : N < L := Finset.mem_range.mp (Finset.mem_filter.mp hNA).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨by omega, ?_⟩⟩
      have hkey : M + 1 = N + k := by omega
      rw [hkey]
      exact hNP
    · intro M hM
      have hP : (k - 1) ≤ M ∧ d ∣ M + 1 := (Finset.mem_filter.mp hM).2
      have hML : M < L + k - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      have hle : k ≤ M + 1 := by omega
      have hsub : (M + 1 - k) + k = M + 1 := Nat.sub_add_cancel hle
      refine Finset.mem_image.mpr ⟨M + 1 - k, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
        rw [hsub]
        exact hP.2
      · omega
  have hinj : Set.InjOn (fun N : ℕ => N + k - 1)
      ((Finset.range L).filter (fun N => d ∣ N + k)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hab' : a + k - 1 = b + k - 1 := hab
    omega
  have hcard : (((Finset.range L).filter (fun N : ℕ => d ∣ N + k)).card : ℕ)
      = (((Finset.range (L + k - 1)).filter (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1)).card
        : ℕ) := by
    calc ((Finset.range L).filter (fun N : ℕ => d ∣ N + k)).card
        = (((Finset.range L).filter (fun N : ℕ => d ∣ N + k)).image
            (fun N => N + k - 1)).card :=
          (Finset.card_image_iff.mpr hinj).symm
      _ = ((Finset.range (L + k - 1)).filter (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1)).card := by
        rw [himg]
  have hCD : ((Finset.range (L + k - 1)).filter (fun M : ℕ => d ∣ M + 1) : Finset ℕ)
      = ((Finset.range (L + k - 1)).filter (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1))
        ∪ ((Finset.range (L + k - 1)).filter
            (fun M : ℕ => ¬ (k - 1) ≤ M ∧ d ∣ M + 1)) := by
    apply Finset.Subset.antisymm
    · intro M hM
      have hML := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      have hP : d ∣ M + 1 := (Finset.mem_filter.mp hM).2
      by_cases hle : k - 1 ≤ M
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hML, ⟨hle, hP⟩⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hML, ⟨hle, hP⟩⟩)
    · intro M hM
      rcases Finset.mem_union.mp hM with hB | hB
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
          (Finset.mem_filter.mp hB).2.2⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
          (Finset.mem_filter.mp hB).2.2⟩
  have hdis : Disjoint
      ((Finset.range (L + k - 1)).filter (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1))
      ((Finset.range (L + k - 1)).filter (fun M : ℕ => ¬ (k - 1) ≤ M ∧ d ∣ M + 1)) := by
    apply Finset.disjoint_left.mpr
    intro M hB hB'
    have hle : k - 1 ≤ M := (Finset.mem_filter.mp hB).2.1
    have hnle : ¬ (k - 1) ≤ M := (Finset.mem_filter.mp hB').2.1
    exact hnle hle
  have hcardsum : (((Finset.range (L + k - 1)).filter (fun M : ℕ => d ∣ M + 1)).card : ℕ)
      = (((Finset.range (L + k - 1)).filter (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1)).card : ℕ)
        + (((Finset.range (k - 1)).filter (fun M : ℕ => d ∣ M + 1)).card : ℕ) := by
    rw [hCD, Finset.card_union_of_disjoint hdis, hD]
  have hC : (((Finset.range (L + k - 1)).filter (fun M : ℕ => d ∣ M + 1)).card : ℕ)
      = (L + k - 1) / d := Nat.card_multiples _ _
  have hD' : (((Finset.range (k - 1)).filter (fun M : ℕ => d ∣ M + 1)).card : ℕ)
      = (k - 1) / d := Nat.card_multiples _ _
  have hkey : (((Finset.range (L + k - 1)).filter
        (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1)).card : ℕ)
      + (k - 1) / d = (L + k - 1) / d := by
    rw [hC, hD'] at hcardsum
    exact hcardsum.symm
  rw [jsp87CntMul, hcard]
  have hres : (((Finset.range (L + k - 1)).filter
        (fun M : ℕ => (k - 1) ≤ M ∧ d ∣ M + 1)).card : ℕ)
      = (L + k - 1) / d - (k - 1) / d := by omega
  rw [hres]

/-- **THE COUNT IN THE WINDOW `{0, …, L−1}`, EXACTLY.**  The point `0` is a
multiple of every `d`, so the count is one more than the count of `d`-multiples
among `{1, …, L−1}`, which is `⌊(L−1)/d⌋`. -/
private theorem cnt_zero {d L : ℕ} (hL : 1 ≤ L) :
    jsp87CntMul d L 0 = (L - 1) / d + 1 := by
  have himg : ((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N)).image
        (fun N => N - 1)
      = (Finset.range (L - 1)).filter (fun M : ℕ => d ∣ M + 1) := by
    apply Finset.Subset.antisymm
    · intro M hM
      rw [Finset.mem_image] at hM
      obtain ⟨N, hNA, hmap⟩ := hM
      have hP : 1 ≤ N ∧ d ∣ N := (Finset.mem_filter.mp hNA).2
      have hNL : N < L := Finset.mem_range.mp (Finset.mem_filter.mp hNA).1
      have hmap' : N - 1 = M := hmap
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have hkey : N = M + 1 := by omega
      rw [← hkey]
      exact hP.2
    · intro M hM
      have hP : d ∣ M + 1 := (Finset.mem_filter.mp hM).2
      have hML : M < L - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      refine Finset.mem_image.mpr ⟨M + 1, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨by omega, hP⟩⟩
      · omega
  have hinj : Set.InjOn (fun N : ℕ => N - 1)
      ((Finset.range L).filter (fun N => 1 ≤ N ∧ d ∣ N)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hab' : a - 1 = b - 1 := hab
    omega
  have hcard : (((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N)).card : ℕ)
      = (((Finset.range (L - 1)).filter (fun M : ℕ => d ∣ M + 1)).card : ℕ) := by
    calc ((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N)).card
        = (((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N)).image
            (fun N => N - 1)).card :=
          (Finset.card_image_iff.mpr hinj).symm
      _ = ((Finset.range (L - 1)).filter (fun M : ℕ => d ∣ M + 1)).card := by
        rw [himg]
  have hone : ((Finset.range L).filter (fun N : ℕ => ¬ (1 ≤ N) ∧ d ∣ N) : Finset ℕ)
      = {0} := by
    apply Finset.Subset.antisymm
    · intro N hN
      have hNL : N < L := Finset.mem_range.mp (Finset.mem_filter.mp hN).1
      have hNP : ¬ (1 ≤ N) ∧ d ∣ N := (Finset.mem_filter.mp hN).2
      rw [Finset.mem_singleton]
      have hN0 : N = 0 := by omega
      exact hN0
    · intro N hN
      rw [Finset.mem_singleton] at hN
      subst hN
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨by omega, dvd_zero d⟩⟩
  have hCD : ((Finset.range L).filter (fun N : ℕ => d ∣ N) : Finset ℕ)
      = ((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N))
        ∪ ((Finset.range L).filter (fun N : ℕ => ¬ (1 ≤ N) ∧ d ∣ N)) := by
    apply Finset.Subset.antisymm
    · intro N hN
      have hNL := Finset.mem_range.mp (Finset.mem_filter.mp hN).1
      have hP : d ∣ N := (Finset.mem_filter.mp hN).2
      by_cases h1N : 1 ≤ N
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hNL, ⟨h1N, hP⟩⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hNL, ⟨h1N, hP⟩⟩)
    · intro N hN
      rcases Finset.mem_union.mp hN with hB | hB
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
          (Finset.mem_filter.mp hB).2.2⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
          (Finset.mem_filter.mp hB).2.2⟩
  have hdis : Disjoint ((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N))
      ((Finset.range L).filter (fun N : ℕ => ¬ (1 ≤ N) ∧ d ∣ N)) := by
    apply Finset.disjoint_left.mpr
    intro N hB hB'
    have h1N : 1 ≤ N := (Finset.mem_filter.mp hB).2.1
    have hn1 : ¬ (1 ≤ N) := (Finset.mem_filter.mp hB').2.1
    exact hn1 h1N
  have hcardsum : (((Finset.range L).filter (fun N : ℕ => d ∣ N)).card : ℕ)
      = (((Finset.range L).filter (fun N : ℕ => 1 ≤ N ∧ d ∣ N)).card : ℕ) + 1 := by
    rw [hCD, Finset.card_union_of_disjoint hdis, hone]
    simp
  have hzero : jsp87CntMul d L 0 = ((Finset.range L).filter (fun N => d ∣ N)).card := rfl
  rw [hzero, hcardsum, hcard, Nat.card_multiples (L - 1) d]

/-- **THE QUOTIENT OF A SUM, MINUS THE FIRST QUOTIENT.**  For every `a, b, d > 0`,

```
⌊(a + b)/d⌋ − ⌊a/d⌋  ≤  ⌊b/d⌋ + 1 ,
```

the floor-function counterpart of the counting bound of §1. -/
private theorem div_sub_div_le {a b d : ℕ} (hd : 0 < d) :
    (a + b) / d - a / d ≤ b / d + 1 := by
  have h1 : (a + b) / d ≤ a / d + b / d + 1 := Nat.add_div_le_div_add_div_add_one a b d
  have h2 : a / d ≤ (a + b) / d := Nat.div_le_div_right (by omega)
  omega

/-- **CASTING A `ℕ` QUOTIENT INTO `ℝ`.**  `↑⌊a/b⌋ ≤ (a:ℝ)/(b:ℝ)`: the real quotient is
the `ℕ` quotient plus a nonneg fraction. -/
private theorem nat_div_le_cast_div (a b : ℕ) (_hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hq : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
  have hpos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr _hb
  have hq' : (a : ℝ) = (((b * (a / b) + a % b : ℕ) : ℕ) : ℝ) := by exact_mod_cast hq
  rw [le_div_iff₀ hpos, hq', Nat.cast_add, Nat.cast_mul]
  linarith

/-- **THE OTHER DIRECTION.**  `(a:ℝ)/(b:ℝ) ≤ ↑⌊a/b⌋`: the remainder is less than
`b`, so the real quotient does not pass the `ℕ` quotient. -/
private theorem cast_div_le_nat_div_add_one (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((a / b : ℕ) : ℝ) + 1 := by
  have hq : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
  have hmod : a % b < b := Nat.mod_lt _ hb
  have hpos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hlt : ((a % b : ℕ) : ℝ) < (b : ℝ) := by exact_mod_cast hmod
  have hq' : (a : ℝ) = (((b * (a / b) + a % b : ℕ) : ℕ) : ℝ) := by exact_mod_cast hq
  rw [hq', Nat.cast_add, Nat.cast_mul, mul_comm, add_div]
  have hdiv : ((a % b : ℕ) : ℝ) / (b : ℝ) < 1 := (div_lt_one hpos).mpr hlt
  have hcancel : (↑(a / b) : ℝ) * ↑b / ↑b = ↑(a / b) := by
    field_simp
  rw [hcancel]
  linarith

/-- **THE UPPER COUNTING BOUND.**  For every `d ≥ 1`, `L ≥ 1` and **every** shift
`k`, the window `[k, k+L)` contains at most `⌊L/d⌋ + 1` multiples of `d`. -/
theorem jsp87CntMul_le {d L k : ℕ} (hd : 0 < d) (hL : 1 ≤ L) :
    ((jsp87CntMul d L k : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) + 1 := by
  have hn : jsp87CntMul d L k ≤ L / d + 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [cnt_zero (d := d) (L := L) hL]
      have hq : (L - 1) / d ≤ L / d := Nat.div_le_div_right (by omega)
      omega
    · rw [cnt_shift (d := d) (L := L) (k := k) hL hk]
      have hks : L + k - 1 = (k - 1) + L := by omega
      rw [hks]
      exact div_sub_div_le (a := k - 1) (b := L) (d := d) hd
  have h1 : (((jsp87CntMul d L k : ℕ) : ℝ)) ≤ (((L / d + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hn
  rw [Nat.cast_add, Nat.cast_one] at h1
  linarith [nat_div_le_cast_div L d hd]

/-- **THE LOWER COUNTING BOUND.**  For every `d ≥ 1`, `L ≥ 1` and **every** shift
`k`, the window `[k, k+L)` contains at least `⌊L/d⌋` multiples of `d`. -/
theorem jsp87CntMul_ge {d L k : ℕ} (hd : 0 < d) (hL : 1 ≤ L) :
    (L : ℝ) / (d : ℝ) - 1 ≤ ((jsp87CntMul d L k : ℕ) : ℝ) := by
  have hn : L / d ≤ jsp87CntMul d L k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [cnt_zero (d := d) (L := L) hL]
      have h1 : (L : ℕ) ≤ (L - 1) + d := by omega
      have h2 : L / d ≤ ((L - 1) + d) / d := Nat.div_le_div_right h1
      have h3 : ((L - 1) + d) / d = (L - 1) / d + 1 := by
        have := Nat.add_div_right (L - 1) hd
        simpa using this
      rw [h3] at h2
      exact h2
    · rw [cnt_shift (d := d) (L := L) (k := k) hL hk]
      have h1 : (k - 1) / d + L / d ≤ (k - 1 + L) / d :=
        Nat.div_add_div_le_add_div (x := k - 1) (y := L) (z := d)
      have h2 : (k - 1) / d ≤ k / d := Nat.div_le_div_right (by omega)
      have h3 : (L + k - 1) / d = (k - 1 + L) / d := by
        congr 1; omega
      omega
  have h1 : (((L / d : ℕ) : ℝ)) ≤ (((jsp87CntMul d L k : ℕ) : ℝ)) := by
    exact_mod_cast hn
  linarith [cast_div_le_nat_div_add_one L d hd]

/-- **FOR DISTINCT PRIMES THE TWO-MODULUS COUNT IS THE ONE-MODULUS COUNT.** -/
theorem jsp87CntMul2_eq {p q L k : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    jsp87CntMul2 p q L k = jsp87CntMul (p * q) L k := by
  unfold jsp87CntMul2 jsp87CntMul
  congr 1
  ext N
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hN, h1, h2⟩
    exact ⟨hN, (jsp87_pair_dvd_iff (n := N + k) hp hq hne).mp ⟨h1, h2⟩⟩
  · rintro ⟨hN, h⟩
    exact ⟨hN, (jsp87_pair_dvd_iff (n := N + k) hp hq hne).mpr h⟩

/-! ## 2. The sieve split: the large prime factors are few -/

/-- **THE SIEVE CONTENT COUNTED OVER `jsp87Primes`.**  For `0 < m`, the number of
prime factors of `m` that are `≤ y` is the number of primes `p ≤ y` with
`p ∣ m`.  Mathlib has no such transfer, and the prime-divisor finset is defined
by a filter on `≤`. -/
theorem jsp87SieveCard_eq_filter {m y : ℕ} (hm : 0 < m) :
    jsp87SieveCard m y = ((jsp87Primes y).filter (fun p => p ∣ m)).card := by
  have hne : m ≠ 0 := by omega

  have h1 : (m.primeFactors.filter (fun p : ℕ => p ≤ y))
      = m.primeFactors.filter (fun p => p ∈ jsp87Primes y ∧ p ∣ m) := by
    refine Finset.filter_congr fun p hp => ?_
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    constructor
    · intro hle
      exact ⟨mem_jsp87Primes.mpr ⟨hprime.two_le, hle, hprime⟩, hpd⟩
    · rintro ⟨hJ, _⟩
      exact (mem_jsp87Primes.mp hJ).2.1
  have h2 : m.primeFactors.filter (fun p : ℕ => p ∈ jsp87Primes y ∧ p ∣ m)
      = m.primeFactors.filter (fun p => p ∈ jsp87Primes y) := by
    refine Finset.filter_congr fun p hp => ?_
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    constructor
    · rintro ⟨hJ, _⟩
      exact hJ
    · rintro hJ
      exact ⟨hJ, hpd⟩
  have h3 : m.primeFactors.filter (fun p : ℕ => p ∈ jsp87Primes y)
      = (jsp87Primes y).filter (fun p => p ∈ m.primeFactors) := by
    apply Finset.Subset.antisymm
    · intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hJ : p ∈ jsp87Primes y := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨hJ, hpf⟩
    · intro p hp
      have hJ : p ∈ jsp87Primes y := (Finset.mem_filter.mp hp).1
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨hpf, hJ⟩
  have h4 : (jsp87Primes y).filter (fun p : ℕ => p ∈ m.primeFactors)
      = (jsp87Primes y).filter (fun p => p ∣ m) := by
    refine Finset.filter_congr fun p hp => ?_
    have hprime : p.Prime := prime_mem_jsp87Primes hp
    rw [Nat.mem_primeFactors_of_ne_zero hne]
    constructor
    · rintro ⟨_, hdvd⟩
      exact hdvd
    · rintro hdvd
      exact ⟨hprime, hdvd⟩
  rw [jsp87SieveCard, h1, h2, h3, h4]

/-- **THE SIEVE CONTENT IS A SUM OF INDICATORS.** -/
theorem jsp87SieveCard_ite {m y : ℕ} (hm : 0 < m) :
    ((jsp87SieveCard m y : ℕ) : ℝ) = ∑ p ∈ jsp87Primes y, (if p ∣ m then 1 else 0) := by
  have h := jsp87SieveCard_eq_filter (m := m) (y := y) hm
  rw [h, Finset.card_eq_sum_ones, ← Finset.sum_filter]
  norm_cast

/-- **THE PRODUCT OF THE LARGE PRIME FACTORS IS AT LEAST `(y+1)^{card}`.** -/
private theorem jsp87Unsieved_prod_ge {n y : ℕ} (hy : 2 ≤ y) (hn : 0 < n) :
    (y + 1) ^ (jsp87UnsievedCard n y : ℕ) ≤ n := by
  have hge : (y + 1) ^ ((n.primeFactors.filter (fun p => y < p)).card : ℕ)
      ≤ ∏ p ∈ (n.primeFactors.filter (fun p => y < p)), p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod fun p hp => ?_
    obtain ⟨hpy, _⟩ := Finset.mem_filter.mp hp
    omega
  have hsub : (n.primeFactors.filter (fun p => y < p)) ⊆ n.primeFactors := Finset.filter_subset _ _
  have hmul : (∏ p ∈ (n.primeFactors.filter (fun p => y < p)), p)
      ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod_of_subset_of_one_le hsub (fun p _ _ => by
      have hp : p ∈ n.primeFactors := by assumption
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_primeFactors hp)))
  have hkey : jsp87UnsievedCard n y = (n.primeFactors.filter (fun p => y < p)).card := rfl
  calc (y + 1) ^ (jsp87UnsievedCard n y : ℕ)
      = (y + 1) ^ ((n.primeFactors.filter (fun p => y < p)).card : ℕ) := by rw [hkey]
    _ ≤ ∏ p ∈ (n.primeFactors.filter (fun p => y < p)), p := hge
    _ ≤ ∏ p ∈ n.primeFactors, p := hmul
    _ ≤ n := Nat.le_of_dvd (by omega) (prod_primeFactors_dvd n)

/-- **COMPARING TWO POWERS OF A BASE `> 1`.** -/
private theorem pow_lt_pow_imp {a c m : ℕ} (h : 1 < a) (hh : a ^ c < a ^ m) : c < m := by
  by_contra hcon
  have hmc : m ≤ c := by omega
  have hle : a ^ m ≤ a ^ c := Nat.pow_le_pow_right (n := a) (by omega) hmc
  omega

/-- **FEWER THAN `r+1` PRIME FACTORS OF `n` EXCEED `y`, ONCE `n < (y+1)^{r+1}`.**
This is the *quantitative* form of the elementary fact that a number `n` has at
most `r` distinct prime factors exceeding `y` when `n < (y+1)^{r+1}`. -/
theorem jsp87UnsievedCard_le {n y r : ℕ} (hy : 2 ≤ y) (hn : 0 < n)
    (hb : n < (y + 1) ^ (r + 1)) : jsp87UnsievedCard n y ≤ r := by
  have hpow : (y + 1) ^ (jsp87UnsievedCard n y : ℕ) ≤ n := jsp87Unsieved_prod_ge hy hn
  have hlt : (y + 1) ^ (jsp87UnsievedCard n y : ℕ) < (y + 1) ^ (r + 1) := by
    have := Nat.lt_of_le_of_lt hpow hb
    simpa using this
  have hcard : jsp87UnsievedCard n y < r + 1 := pow_lt_pow_imp (by omega) hlt
  omega

/-- **AT MOST THREE PRIME FACTORS OF `n` EXCEED `y`, WHEN `n < (y+1)⁴`** — in
particular whenever `n ≤ y³`. -/
theorem jsp87UnsievedCard_le_three {n y : ℕ} (hy : 2 ≤ y) (hn : 0 < n) (hb : n < (y + 1) ^ 4) :
    jsp87UnsievedCard n y ≤ 3 :=
  jsp87UnsievedCard_le hy hn hb

/-- **AT MOST ONE PRIME FACTOR OF `n` EXCEEDS `y`, WHEN `n ≤ y²`** — the instance
of the previous theorem used in the sharp version of the argument. -/
theorem jsp87UnsievedCard_le_one {n y : ℕ} (hy : 2 ≤ y) (hn : 0 < n) (hb : n ≤ y * y) :
    jsp87UnsievedCard n y ≤ 1 := by
  by_cases h2 : n < y * y
  · have hlt : n < (y + 1) ^ 2 := by nlinarith
    have := jsp87UnsievedCard_le hy hn hlt
    omega
  · have : n = y * y := by omega
    subst this
    have hlt : y * y < (y + 1) ^ 2 := by nlinarith
    have := jsp87UnsievedCard_le hy hn hlt
    omega

/-! ## 3. Variance machinery -/

/-- **YOUNG'S INEQUALITY, IN THE FORM THE VARIANCE ADDITION NEEDS.** -/
private theorem sq_add_ge (x y : ℝ) : x ^ 2 / 2 - y ^ 2 ≤ (x + y) ^ 2 := by
  have hsq : 0 ≤ x ^ 2 + 4 * x * y + 4 * y ^ 2 := by
    have h := sq_nonneg (x + 2 * y)
    nlinarith [h]
  nlinarith

/-- **THE CENTRED SECOND MOMENT OF A SUM.**  With both parts centred at their own
means, `(x+y)² ≥ x²/2 − y²` gives

```
CSq (f + g)  ≥  ½ CSq f  −  CSq g .
```

This is the *only* place the covariance between the sieve content and the
unsieved content is used, and it costs a factor `1/2`. -/
theorem jsp87WinCSq_add_ge (L k : ℕ) (f g : ℕ → ℝ) :
    jsp87WinCSq L k (fun n => f n + g n) ≥ jsp87WinCSq L k f / 2 - jsp87WinCSq L k g := by
  have hm := jsp87WinMean_add L k f g
  unfold jsp87WinCSq
  rw [hm]
  dsimp only
  have hstep : ∀ N ∈ Finset.range L,
      (f (N + k) + g (N + k) - (jsp87WinMean L k f + jsp87WinMean L k g)) ^ 2
        + (g (N + k) - jsp87WinMean L k g) ^ 2
        ≥ (f (N + k) - jsp87WinMean L k f) ^ 2 / 2 := by
    intro N _
    have h := sq_add_ge (f (N + k) - jsp87WinMean L k f) (g (N + k) - jsp87WinMean L k g)
    linarith
  rw [Finset.sum_div]
  have h1 : (∑ N ∈ Finset.range L, (f (N + k) - jsp87WinMean L k f) ^ 2 / 2)
      ≤ ∑ N ∈ Finset.range L,
        ((f (N + k) + g (N + k) - (jsp87WinMean L k f + jsp87WinMean L k g)) ^ 2
          + (g (N + k) - jsp87WinMean L k g) ^ 2) :=
    Finset.sum_le_sum (s := Finset.range L) (N := ℝ) fun N hN => hstep N hN
  rw [Finset.sum_add_distrib] at h1
  linarith

/-- **A BOUNDED FUNCTION HAS SMALL SPREAD.**  If `0 ≤ g ≤ c` pointwise then
`Σ g² ≤ c Σ g`, and the quadratic `cS − S²/L` has maximum `c²L/4`; so

```
CSq g  ≤  c² L / 4 .
```

For `c = 1` this is the Bernoulli bound `CSq ≤ L/4`, i.e. `Var ≤ 1/4` for a
`{0,1}`-valued function. -/
theorem jsp87WinCSq_le_const (L k : ℕ) (hL : 1 ≤ L) {g : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ N, 0 ≤ g N ∧ g N ≤ c) :
    jsp87WinCSq L k g ≤ c ^ 2 * (L : ℝ) / 4 := by
  set S : ℝ := ∑ N ∈ Finset.range L, g (N + k) with hS
  have hkey := jsp87WinCSq_eq_sum L k g hL
  have hsq : ∀ N ∈ Finset.range L, (g (N + k)) ^ 2 ≤ c * g (N + k) := by
    intro N _
    have h1 := hg (N + k)
    obtain ⟨h0, h1'⟩ := h1
    nlinarith [mul_nonneg h0 hc]
  have hT : (∑ N ∈ Finset.range L, (g (N + k)) ^ 2) ≤ c * S := by
    have h1 : (∑ N ∈ Finset.range L, (g (N + k)) ^ 2)
        ≤ ∑ N ∈ Finset.range L, c * g (N + k) :=
      Finset.sum_le_sum (s := Finset.range L) (N := ℝ) fun N hN => hsq N hN
    rw [hS, Finset.mul_sum]
    exact h1
  have hL0 : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hL)
  have hsq' : 0 ≤ (S - c * (L : ℝ) / 2) ^ 2 := sq_nonneg _
  have hform : c * S - S ^ 2 / (L : ℝ)
      = c ^ 2 * (L : ℝ) / 4 - (S - c * (L : ℝ) / 2) ^ 2 / (L : ℝ) := by
        field_simp
        ring
  rw [hkey]
  linarith [hT, hform, div_nonneg hsq' (le_of_lt hL0)]

/-- **THE `{0,1}` CASE.** -/
theorem jsp87WinCSq_bool_le (L k : ℕ) (hL : 1 ≤ L) {g : ℕ → ℝ}
    (hg : ∀ N, g N = 0 ∨ g N = 1) :
    jsp87WinCSq L k g ≤ (L : ℝ) / 4 := by
  have h : jsp87WinCSq L k g ≤ 1 ^ 2 * (L : ℝ) / 4 := by
    refine jsp87WinCSq_le_const L k hL (c := (1 : ℝ)) (by norm_num) ?_
    intro N
    rcases hg N with hN | hN <;> simp [hN] <;> norm_num
  linarith

private theorem var_mul_card {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) :
    jsp87Var s f * (s.card : ℝ)
      = (∑ i ∈ s, (f i) ^ 2) - (∑ i ∈ s, f i) ^ 2 / (s.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  have h1 := jsp87Var_eq_FAvg_sq_sub s hs f
  have h2 : jsp87FAvg s (fun i => (f i) ^ 2)
      = (∑ i ∈ s, (f i) ^ 2) / (s.card : ℝ) := favg_eq s _
  have h3 : jsp87FAvg s f = (∑ i ∈ s, f i) / (s.card : ℝ) := favg_eq s _
  rw [h1, h2, h3]
  field_simp

/-- **ADDING A POINT CANNOT DECREASE THE CENTRED SECOND MOMENT.**  For
`a ∉ s`,

```
(s.card + 1) · Var (insert a s) f  ≥  s.card · Var s f ,
```

the classical fact that one new observation never shrinks the spread: the
difference of the two centred second moments is
`(n·f a − ∑_s f)² / (n (n+1)) ≥ 0`. -/
theorem jsp87_var_insert_ge {Ω : Type*} [DecidableEq Ω] (s : Finset Ω) (f : Ω → ℝ) (a : Ω) (ha : a ∉ s) :
    ((s.card + 1 : ℕ) : ℝ) * jsp87Var (insert a s) f ≥ (s.card : ℝ) * jsp87Var s f := by
  classical
  have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
  by_cases hsn : s = ∅
  · simpa [hsn] using (jsp87Var_nonneg (insert a s) f : (0 : ℝ) ≤ jsp87Var (insert a s) f)
  · have hs : s.Nonempty := not_not.mp ((Finset.not_nonempty_iff_eq_empty).not.mpr hsn)
    have hne2 : (insert a s).Nonempty := ⟨a, Finset.mem_insert_self a s⟩
    have h1 := var_mul_card (insert a s) hne2 f
    have h2 := var_mul_card s hs f
    have hsum1 : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := Finset.sum_insert ha
    have hsum2 : (∑ i ∈ insert a s, (f i) ^ 2) = (f a) ^ 2 + ∑ i ∈ s, (f i) ^ 2 :=
      Finset.sum_insert ha
    have hn0 : (0 : ℝ) < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs
    have hn1 : (0 : ℝ) < (s.card : ℝ) + 1 := by linarith
    set A : ℝ := ∑ i ∈ s, f i with hA
    set S2 : ℝ := ∑ i ∈ s, (f i) ^ 2 with hS2
    set B : ℝ := f a with hB
    have hcast : (((s.card + 1 : ℕ) : ℕ) : ℝ) = (s.card : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have h1c : jsp87Var (insert a s) f * (((s.card + 1 : ℕ) : ℕ) : ℝ)
        = (∑ i ∈ insert a s, (f i) ^ 2) - (∑ i ∈ insert a s, f i) ^ 2 / (((s.card + 1 : ℕ) : ℕ) : ℝ) := by
      rw [hcard] at h1
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    have hkey : jsp87Var (insert a s) f * ((s.card : ℝ) + 1)
        = (S2 + B ^ 2) - (A + B) ^ 2 / ((s.card : ℝ) + 1) := by
      rw [hcast] at h1c
      rw [hsum2, hsum1, hA, hS2, hB] at h1c
      convert h1c using 1 <;> ring
    have hkey2 : jsp87Var s f * (s.card : ℝ) = S2 - A ^ 2 / (s.card : ℝ) := by
      rw [hA, hS2] at h2
      rw [← h2]
    have h3 : B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ) ≥ 0 := by
      have hq : (0 : ℝ) < (s.card : ℝ) * ((s.card : ℝ) + 1) := mul_pos hn0 hn1
      have hform : (s.card : ℝ) * ((s.card : ℝ) + 1)
          * (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ))
          = ((s.card : ℝ) * B - A) ^ 2 := by
        field_simp
        ring
      have heq : (s.card : ℝ) * ((s.card : ℝ) + 1)
          * (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ))
          = ((s.card : ℝ) * B - A) ^ 2 := by
        field_simp
        ring
      have hX : (0 : ℝ) ≤ (s.card : ℝ) * ((s.card : ℝ) + 1)
          * (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ)) := by
        rw [heq]
        exact sq_nonneg _
      have hXc : (0 : ℝ) ≤ (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ))
          * ((s.card : ℝ) * ((s.card : ℝ) + 1)) := by
        have htmp := hX
        have htmp2 : (0 : ℝ) ≤ (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ))
            * ((s.card : ℝ) * ((s.card : ℝ) + 1)) := by
          calc 0 ≤ ((s.card : ℝ) * ((s.card : ℝ) + 1))
                * (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ)) := htmp
            _ = (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ))
                * ((s.card : ℝ) * ((s.card : ℝ) + 1)) := mul_comm _ _
        exact htmp2
      by_contra hcon
      have hc' : (B ^ 2 - (A + B) ^ 2 / ((s.card : ℝ) + 1) + A ^ 2 / (s.card : ℝ)) < 0 :=
        lt_of_not_ge hcon
      have hmul := mul_neg_of_neg_of_pos hc' hq
      linarith
    rw [hcast]
    nth_rewrite 1 [mul_comm]
    nth_rewrite 2 [mul_comm]
    linarith [hkey, hkey2, h3]

/-- **SUMS OVER AN INJECTIVE IMAGE.** -/
private theorem sum_map_inj (s : Finset ℕ) (g : ℕ → ℕ) (hg : Function.Injective g) (h : ℕ → ℝ) :
    (∑ x ∈ s.image g, h x) = ∑ x ∈ s, h (g x) :=
  Finset.sum_image (Set.injOn_of_injective hg)

/-- **SHIFTING THE WINDOW PAST ITS FIRST POINT.** -/
private theorem var_erase_zero (L : ℕ) (hL : 1 ≤ L) (f : ℕ → ℝ) :
    jsp87Var ((Finset.range L).erase 0) f
      = jsp87Var (Finset.range (L - 1)) (fun N => f (N + 1)) := by
  classical
  have hset : (Finset.range L).erase 0 = (Finset.range (L - 1)).image (fun N => N + 1) := by
    ext N
    simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hN0, hNL⟩
      exact ⟨N - 1, by omega, by omega⟩
    · rintro ⟨a, hNaL, hNa⟩
      exact ⟨by omega, by omega⟩
  have hinj : Set.InjOn (fun N : ℕ => N + 1) ↑(Finset.range (L - 1)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    have hab' : a + 1 = b + 1 := hab
    omega
  unfold jsp87Var jsp87FAvg
  rw [hset, Finset.card_image_iff.mpr hinj]
  rw [sum_map_inj (Finset.range (L - 1)) _ (by intro a b hab; have hab' : a + 1 = b + 1 := hab; omega) _]
  rw [sum_map_inj (Finset.range (L - 1)) _ (by intro a b hab; have hab' : a + 1 = b + 1 := hab; omega) _]

/-! ## 4. The two moments of the small-prime content

The heart of the round.  All that is used is the counting layer of §1 and Euler's
divergence; no analytic input is needed. -/

/-- **THE SQUARED-RECIPROCAL MASS IS AT MOST HALF THE LINEAR ONE.**  For every
prime `p ≥ 2` one has `1/p² ≤ (1/p)/2`, so the diagonal of the double count is
absorbed by half of the main term. -/
theorem jsp87LamSq_le_half_lam (y : ℕ) : jsp87LamSq y ≤ jsp87Lam y / 2 := by
  unfold jsp87LamSq jsp87Lam
  have hstep : ∀ p ∈ jsp87Primes y, (1 / (p : ℝ)) ^ 2 ≤ (1 / (p : ℝ)) / 2 := by
    intro p hp
    have hp2 : 2 ≤ p := two_le_mem_jsp87Primes hp
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have h1 : (1 / (p : ℝ)) ≤ (1 : ℝ) / 2 := by
      have hx := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2R
      simpa using hx
    have h0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hh := mul_le_mul_of_nonneg_right h1 h0
    convert hh using 1 <;> ring
  have h1 : (∑ p ∈ jsp87Primes y, (1 / (p : ℝ)) ^ 2) ≤ ∑ p ∈ jsp87Primes y, (1 / (p : ℝ)) / 2 :=
    Finset.sum_le_sum (s := jsp87Primes y) (N := ℝ) fun p hp => hstep p hp
  rw [Finset.sum_div]
  exact h1

/-- **EVERY MEMBER OF THE PRIME FINSET IS POSITIVE.** -/
private theorem prime_pos {p y : ℕ} (hp : p ∈ jsp87Primes y) : 0 < p := by
  have h2 := two_le_mem_jsp87Primes hp
  omega

/-- **SUMS OF `1`-`0` INDICATORS ARE COUNTS.** -/
private theorem sum_ite_count (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ a ∈ s, (if P a then (1 : ℕ) else 0)) = (s.filter P).card := by
  simp

/-- **THE FIRST MOMENT OF THE SIEVE CONTENT.** -/
private theorem jsp87_smallSum_eq (y L k : ℕ) (hk : 1 ≤ k) :
    (∑ N ∈ Finset.range L, ((jsp87SieveCard (N + k) y : ℕ) : ℝ))
      = ∑ p ∈ jsp87Primes y, ((jsp87CntMul p L k : ℕ) : ℝ) := by
  have hstepN : ∀ N ∈ Finset.range L,
      ((jsp87SieveCard (N + k) y : ℕ) : ℝ)
        = ∑ p ∈ jsp87Primes y, (if p ∣ N + k then (1:ℝ) else 0) := by
    intro N _
    have hpos : 0 < N + k := by omega
    simpa using jsp87SieveCard_ite hpos
  have hcnt : ∀ p : ℕ,
      (∑ N ∈ Finset.range L, (if p ∣ N + k then (1:ℝ) else 0))
        = ((jsp87CntMul p L k : ℕ) : ℝ) := by
    intro p
    have h1 : (∑ N ∈ Finset.range L, (if p ∣ N + k then (1:ℝ) else 0))
        = (((Finset.range L).filter (fun N => p ∣ N + k)).card : ℝ) := by
      simp
    rw [h1]
    have h2 : ((jsp87CntMul p L k : ℕ) : ℝ) = (((Finset.range L).filter (fun N => p ∣ N + k)).card : ℝ) := by
      unfold jsp87CntMul
      rfl
    exact h2.symm
  calc (∑ N ∈ Finset.range L, ((jsp87SieveCard (N + k) y : ℕ) : ℝ))
      = ∑ N ∈ Finset.range L, ∑ p ∈ jsp87Primes y, (if p ∣ N + k then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun N hN => hstepN N hN
    _ = ∑ p ∈ jsp87Primes y, ∑ N ∈ Finset.range L, (if p ∣ N + k then (1:ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ p ∈ jsp87Primes y, ((jsp87CntMul p L k : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun p hp => hcnt p

/-- **THE SECOND MOMENT OF THE SIEVE CONTENT.** -/
private theorem jsp87_smallSqSum_eq (y L k : ℕ) (hk : 1 ≤ k) :
    (∑ N ∈ Finset.range L, (((jsp87SieveCard (N + k) y : ℕ) : ℕ) : ℝ) ^ 2)
      = ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
  have hstepN : ∀ N ∈ Finset.range L,
      (((jsp87SieveCard (N + k) y : ℕ) : ℕ) : ℝ) ^ 2
        = ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y,
            (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0) := by
    intro N _
    have hpos : 0 < N + k := by omega
    have h := jsp87SieveCard_ite (y := y) hpos
    calc (((jsp87SieveCard (N + k) y : ℕ) : ℕ) : ℝ) ^ 2
        = (∑ p ∈ jsp87Primes y, (if p ∣ N + k then (1:ℝ) else 0)) ^ 2 := by rw [h]
      _ = (∑ p ∈ jsp87Primes y, (if p ∣ N + k then (1:ℝ) else 0))
          * (∑ q ∈ jsp87Primes y, (if q ∣ N + k then (1:ℝ) else 0)) := by ring
      _ = ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y,
            (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0) := by
          have hstep : ∀ p ∈ jsp87Primes y,
              (if p ∣ N + k then (1:ℝ) else 0)
                * (∑ q ∈ jsp87Primes y, (if q ∣ N + k then (1:ℝ) else 0))
                = ∑ q ∈ jsp87Primes y,
                    ((if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0)) := by
            intro p hp
            rw [Finset.mul_sum]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p hp => hstep p hp
  have hcnt : ∀ p q : ℕ, (p ∈ jsp87Primes y) → (q ∈ jsp87Primes y) →
      (∑ N ∈ Finset.range L,
          (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0))
        = ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
    intro p q hp hq
    have h1 : (∑ N ∈ Finset.range L,
          (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0))
        = ((∑ N ∈ Finset.range L,
            (if p ∣ N + k ∧ q ∣ N + k then (1 : ℕ) else (0 : ℕ)) : ℕ) : ℝ) := by
      have hn : (∑ N ∈ Finset.range L,
            ((if p ∣ N + k then (1:ℕ) else (0:ℕ)) * (if q ∣ N + k then (1:ℕ) else (0:ℕ)) : ℕ))
          = (∑ N ∈ Finset.range L,
              (if p ∣ N + k ∧ q ∣ N + k then (1:ℕ) else (0:ℕ)) : ℕ) := by
        refine Finset.sum_congr rfl fun N _ => ?_
        by_cases h1N : p ∣ N + k <;> by_cases h2N : q ∣ N + k <;> simp [h1N, h2N]
      exact_mod_cast hn
    have h2 := sum_ite_count (Finset.range L) (fun N => p ∣ N + k ∧ q ∣ N + k)
    rw [h1, h2]
    have h3 : ((jsp87CntMul2 p q L k : ℕ) : ℝ)
        = (((Finset.range L).filter (fun N => p ∣ N + k ∧ q ∣ N + k)).card : ℝ) := by
      unfold jsp87CntMul2
      rfl
    exact h3.symm
  calc (∑ N ∈ Finset.range L, (((jsp87SieveCard (N + k) y : ℕ) : ℕ) : ℝ) ^ 2)
      = ∑ N ∈ Finset.range L, ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y,
          (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun N hN => hstepN N hN
    _ = ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y, ∑ N ∈ Finset.range L,
          (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0) := by
        calc (∑ N ∈ Finset.range L, ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y,
              (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0))
            = ∑ p ∈ jsp87Primes y, ∑ N ∈ Finset.range L, ∑ q ∈ jsp87Primes y,
                (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0) := by
              exact Finset.sum_comm (s := Finset.range L) (t := jsp87Primes y)
                (f := fun N p => ∑ q ∈ jsp87Primes y,
                  (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0))
          _ = ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y, ∑ N ∈ Finset.range L,
                (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              exact Finset.sum_comm (s := Finset.range L) (t := jsp87Primes y)
                (f := fun N q =>
                  (if p ∣ N + k then (1:ℝ) else 0) * (if q ∣ N + k then (1:ℝ) else 0))
    _ = ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        refine Finset.sum_congr rfl fun q hq => ?_
        exact hcnt p q hp hq

end JSP87
