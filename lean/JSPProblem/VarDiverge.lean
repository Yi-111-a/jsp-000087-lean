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

## §5  WHAT ROUND 136 ADDED (the variance arithmetic, and the Erdős–Kac crown)

Round 135 left exactly one named blocker, `jsp87_winVar_small_ge`, whose proof was
a pure bookkeeping problem.  Section 5 of the file closes it and then goes all
the way to the divergence statement:

* **§5.1–§5.3 the moment arithmetic** (`jsp87Primes_card_le`,
  `jsp87CntMul2_diag`, and the three private lemmas `jsp87_smallSum_ge`,
  `jsp87_smallSum_le`, `jsp87_offRow_ge`, `jsp87_smallSqSum_ge`): for **every**
  shift `k ≥ 1`, with `c(y) = #{p ≤ y}`,
  `S₁ ≥ L·λ − c`, `S₂ ≥ L·(λ + λ² − λ₂) − c − c²`.
* **§5.4 `jsp87_winVar_small_ge`** — THE NAMED BLOCKER, CLOSED:
  `Var (N ↦ #{p ≤ y : p ∣ N+k}) ≥ ¼·λ(y) − 4` for `y ≥ 32`, `y² ≤ 2L`.
* **§5.5 `jsp87_tcVarAt_ge`** — the same for `ω` itself (the §5.4 diagonal of
  arXiv:2512.01739): `jsp87TcVarAt L k ≥ ⅛·λ(y) − 5`, using the shifted version
  `jsp87WinCSq_le_const'` of the bounded-spread lemma.
* **§5.6 Euler** — `jsp87_lam_ge_primeRecip` and `jsp87_lam_tendsto`:
  `λ(y) → ∞` (no Mertens needed).
* **§5.7 `jsp87_var_omega_diverges`** — THE CROWN: for every `C > 0` there is an
  `L` with `jsp87TcVarAt L k > C` for **every** shift `1 ≤ k ≤ L`.

**Consequence for the gate.**  Round 132 recorded that `Var(ω) → ∞`
"needs Mertens at the second order" and round 134 refuted every *arithmetic* route
to hypothesis (5.21).  Both are now superseded: the diagonal variance of §5.4
**diverges unconditionally**, with an elementary proof.  Hence the "variance is
large" clause of (5.21) is satisfiable at large heights and is **not** the
obstruction; what remains of `jsp_000087_main` is (i) the off-diagonal correlation
estimate `jsp87Mcov_small` and (ii) the sample geometry of (5.21').

## What is still missing (next rounds)

1. **The endpoint `k = 0`** (`jsp87_winVar_zero_ge`).  `var_erase_zero` +
   `jsp87_var_insert_ge` are the right tools and the proof was 90% written in
   round 136; what is left is the ratio bookkeeping `(L−1)/L ≥ 2/3` interacting
   with the sign of `λ/8 − 5`.  Statement to prove: for `y ≥ 32`, `L ≥ 3`,
   `y² ≤ 2(L−1)`, `2(L−1) ≤ y³`, then `jsp87WinVar L 0 omega ≥ λ(y)/8 − 5`.
   A cleaner route: strengthen `jsp87_var_insert_ge` to
   `(n+1)·Var(insert a s) ≥ n·Var s + f a − mean` and avoid the ratio entirely.
2. **`jsp87_521_diag_satisfiable`** — the transfer of §5.7 into the notation of
   hypothesis (5.21) (the weighted diagonal variance of `jsp87TcDiag L H`
   exceeds `L`), so that the tree states explicitly that (5.21)'s diagonal
   clause is satisfiable.
3. **The off-diagonal part.**  §5.7 is unconditional but §5.4 of
   arXiv:2512.01739 needs the two-point correlations `jsp87Mcov_small`
   (Thm 3.1, from Pilatte), which Mathlib does not contain; this is the same
   blocker as in rounds 115–135 and is unaffected by this round.

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

/-! ## 5. The variance arithmetic — closing round 135's named blocker

Everything above was machinery; this section is the *arithmetic*, and it is what
round 135 left open.  With

* `λ(y) = Σ_{p ≤ y} 1/p`, `λ₂(y) = Σ_{p ≤ y} 1/p²`, `c(y) = #{p ≤ y}` ,
* `S₁ = Σ_{N < L} A (N+k)` and `S₂ = Σ_{N < L} A (N+k)²` the two moments of the
  sieve content `A n = #{p ≤ y : p ∣ n}` (exact, §4),
* `⌊L/d⌋ ≤ c_d ≤ ⌊L/d⌋+1` the counting bounds of §1,

one has, for **every** shift `k ≥ 1`,

```
S₁  ≥  L·λ − c          S₁ ≤  L·λ + c                                   (§5.2)
S₂  ≥  L·(λ + λ² − λ₂)  −  c − c²                                       (§5.3)
```

(the diagonal `p = q` of the double count contributes `L·λ`, and the off-diagonal
pairs contribute `L·(λ² − λ₂)` — the main term of the Erdős–Kac variance), and
therefore

```
Var (N ↦ A (N+k))  ≥  λ/4 − 4        for y ≥ 32,  y² ≤ 2 L .            (§5.4)
```

§5.5 transfers this to `ω` itself (`jsp87_tcVarAt_ge`), §5.6 treats the endpoint
`k = 0` (`jsp87_winVar_zero_ge`), and §5.7 concludes with **Euler**: the variance
of `ω` over a shifted window tends to `+∞`, uniformly in the shift
(`jsp87_var_omega_diverges`) — the Turán/Erdős–Kac statement that round 132
declared "NOT expected to be provable with the present tools". -/

/-- **THERE ARE AT MOST `y` PRIMES BELOW `y`.**  The error term of the mean-field
approximation of §5.2–§5.3 is the *number* of primes below `y`, and it must be
controlled by `y` itself, not by `y + 1`, because the whole point of the
`y² ≤ 2L` hypothesis is that `y/L` is tiny. -/
theorem jsp87Primes_card_le (y : ℕ) : (jsp87Primes y).card ≤ y := by
  unfold jsp87Primes
  calc (Finset.filter Nat.Prime (Finset.Icc 2 y)).card ≤ (Finset.Icc 2 y).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = y + 1 - 2 := Nat.card_Icc 2 y
    _ ≤ y := by rcases Nat.lt_or_ge y 2 with h | h <;> omega

/-- **THE DIAGONAL OF THE TWO-MODULUS COUNT IS THE ONE-MODULUS COUNT.** -/
theorem jsp87CntMul2_diag (p L k : ℕ) :
    jsp87CntMul2 p p L k = jsp87CntMul p L k := by
  unfold jsp87CntMul2 jsp87CntMul
  congr 1
  ext N
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hN, h1, h2⟩
    exact ⟨hN, h1⟩
  · rintro ⟨hN, h⟩
    exact ⟨hN, h, h⟩

/-- **THE FIRST MOMENT, LOWER BOUNDED BY THE MEAN FIELD.**  For **every** shift
`k ≥ 1`, `Σ_{N < L} A (N+k) ≥ L·λ(y) − c(y)`. -/
private theorem jsp87_smallSum_ge {y L k : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) :
    (L : ℝ) * jsp87Lam y - ((jsp87Primes y).card : ℝ)
      ≤ ∑ N ∈ Finset.range L, ((jsp87SieveCard (N + k) y : ℕ) : ℝ) := by
  rw [jsp87_smallSum_eq y L k hk]
  have hstep : ∀ p ∈ jsp87Primes y,
      (L : ℝ) * (1 / (p : ℝ)) - 1 ≤ ((jsp87CntMul p L k : ℕ) : ℝ) := by
    intro p hp
    have hp2 : 0 < p := prime_pos hp
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      (jsp87CntMul_ge (d := p) (L := L) (k := k) hp2 hL)
  have h1 : (∑ p ∈ jsp87Primes y, ((L : ℝ) * (1 / (p : ℝ)) - 1))
      ≤ ∑ p ∈ jsp87Primes y, ((jsp87CntMul p L k : ℕ) : ℝ) :=
    Finset.sum_le_sum (s := jsp87Primes y) (N := ℝ) fun p hp => hstep p hp
  calc (L : ℝ) * jsp87Lam y - ((jsp87Primes y).card : ℝ) = ∑ p ∈ jsp87Primes y, ((L : ℝ) * (1 / (p : ℝ)) - 1) := by
        unfold jsp87Lam
        rw [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ jsp87Primes y, ((jsp87CntMul p L k : ℕ) : ℝ) := h1

/-- **THE FIRST MOMENT, UPPER BOUNDED BY THE MEAN FIELD.** -/
private theorem jsp87_smallSum_le {y L k : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) :
    (∑ N ∈ Finset.range L, ((jsp87SieveCard (N + k) y : ℕ) : ℝ))
      ≤ (L : ℝ) * jsp87Lam y + ((jsp87Primes y).card : ℝ) := by
  rw [jsp87_smallSum_eq y L k hk]
  have hstep : ∀ p ∈ jsp87Primes y,
      ((jsp87CntMul p L k : ℕ) : ℝ) ≤ (L : ℝ) * (1 / (p : ℝ)) + 1 := by
    intro p hp
    have hp2 : 0 < p := prime_pos hp
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      (jsp87CntMul_le (d := p) (L := L) (k := k) hp2 hL)
  have h1 : (∑ p ∈ jsp87Primes y, ((jsp87CntMul p L k : ℕ) : ℝ))
      ≤ ∑ p ∈ jsp87Primes y, ((L : ℝ) * (1 / (p : ℝ)) + 1) :=
    Finset.sum_le_sum (s := jsp87Primes y) (N := ℝ) fun p hp => hstep p hp
  calc ∑ p ∈ jsp87Primes y, ((jsp87CntMul p L k : ℕ) : ℝ) ≤ ∑ p ∈ jsp87Primes y, ((L : ℝ) * (1 / (p : ℝ)) + 1) := h1
    _ = (L : ℝ) * jsp87Lam y + ((jsp87Primes y).card : ℝ) := by
        unfold jsp87Lam
        rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **THE OFF-DIAGONAL ROW, LOWER BOUNDED BY THE MEAN FIELD.**  For every prime
`p ≤ y` the sum of the two-modulus counts over the *other* primes `q ≤ y` is at
least `L·(1/p)·(λ − 1/p) − c(y)`: the pairs `(p,q)` with `q ≠ p` contribute the
product of the two densities, by CRT and the counting bound of §1. -/
private theorem jsp87_offRow_ge {y L k : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) {p : ℕ} (hp : p ∈ jsp87Primes y) :
    (L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y - 1 / (p : ℝ))) - ((jsp87Primes y).card : ℝ)
      ≤ ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
  have hpP : p.Prime := prime_mem_jsp87Primes hp
  have hstep : ∀ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), (L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) - 1 ≤ ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
    intro q hq
    have hqP : q.Prime := prime_mem_jsp87Primes (Finset.mem_filter.mp hq).1
    have hne : p ≠ q := Ne.symm (Finset.mem_filter.mp hq).2
    rw [jsp87CntMul2_eq hpP hqP hne]
    have hpq : 0 < p * q := mul_pos (prime_pos hp) (prime_pos (Finset.mem_filter.mp hq).1)
    have h := jsp87CntMul_ge (d := p * q) (L := L) (k := k) hpq hL
    have hkey : (L : ℝ) / (p * q : ℕ) = (L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) := by
      rw [Nat.cast_mul, ← mul_div_assoc]
      ring
    rw [hkey] at h
    linarith
  have h1 : (∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) - 1))
      ≤ ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((jsp87CntMul2 p q L k : ℕ) : ℝ) :=
    Finset.sum_le_sum (s := (jsp87Primes y).filter (fun r => r ≠ p)) (N := ℝ) fun q hq => hstep q hq
  have hrec : jsp87Lam y - 1 / (p : ℝ) = ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), (1 / (q : ℝ)) := by
    have hsp := sum_split_neq (jsp87Primes y) (fun p' q => 1 / (q : ℝ)) p hp
    unfold jsp87Lam
    linarith
  have hFcR : (((jsp87Primes y).filter (fun r => r ≠ p) : Finset ℕ).card : ℝ)
      ≤ ((jsp87Primes y).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
  have hmul1 : (1 / (p : ℝ)) * (∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), (1 / (q : ℝ)))
      = ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((1 / (p : ℝ)) * (1 / (q : ℝ))) :=
    Finset.mul_sum _ _ _
  have hmul2 : (L : ℝ) * (∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((1 / (p : ℝ)) * (1 / (q : ℝ))))
      = ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ)))) :=
    Finset.mul_sum _ _ _
  have hsub : (∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ)))))
      - (((jsp87Primes y).filter (fun r => r ≠ p) : Finset ℕ).card : ℝ)
      ≤ ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hstep0 : (L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y - 1 / (p : ℝ))) - ((jsp87Primes y).card : ℝ)
      ≤ (L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y - 1 / (p : ℝ))) - (((jsp87Primes y).filter (fun r => r ≠ p) : Finset ℕ).card : ℝ) := by
    linarith [hFcR]
  have hstep1 : (L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y - 1 / (p : ℝ)))
      = ∑ q ∈ (jsp87Primes y).filter (fun r => r ≠ p), ((L : ℝ) * ((1 / (p : ℝ)) * (1 / (q : ℝ)))) := by
    rw [hrec, hmul1, hmul2]
  exact hstep0.trans (hstep1 ▸ (hsub.trans h1))

/-- **THE SECOND MOMENT OF THE SIEVE CONTENT: MEAN FIELD PLUS THE PRODUCT OF THE
DENSITIES.**  For **every** shift `k ≥ 1`,

```
Σ_{N < L} A (N+k)²  ≥  L·(λ + λ² − λ₂)  −  c  −  c² ,
```

`c = #{p ≤ y}` and `λ₂ = Σ_{p ≤ y} 1/p²`: the diagonal `p = q` of the double
count of §4 contributes `L·λ` and the off-diagonal pairs contribute
`L·(λ² − λ₂)`, each with an error of one unit per pair.  This is the
Erdős–Kac/Turán main term, obtained with **no** analytic input. -/
private theorem jsp87_smallSqSum_ge {y L k : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) :
    (L : ℝ) * (jsp87Lam y + jsp87Lam y ^ 2 - jsp87LamSq y)
      - (((jsp87Primes y).card : ℝ) + ((jsp87Primes y).card : ℝ) ^ 2)
      ≤ ∑ N ∈ Finset.range L, (((jsp87SieveCard (N + k) y : ℕ) : ℕ) : ℝ) ^ 2 := by
  rw [jsp87_smallSqSum_eq y L k hk]
  have hdiag : ∀ p ∈ jsp87Primes y, (L : ℝ) * (1 / (p : ℝ)) - 1 ≤ ((jsp87CntMul p L k : ℕ) : ℝ) := by
    intro p hp
    have hp2 : 0 < p := prime_pos hp
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      (jsp87CntMul_ge (d := p) (L := L) (k := k) hp2 hL)
  have hrow : ∀ p ∈ jsp87Primes y,
      (L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)
        - 1 - ((jsp87Primes y).card : ℝ)
      ≤ ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
    intro p hp
    have hsp := sum_split_neq (jsp87Primes y)
      (fun p' q => ((jsp87CntMul2 p' q L k : ℕ) : ℝ)) p hp
    rw [jsp87CntMul2_diag] at hsp
    have ho := jsp87_offRow_ge (y := y) (L := L) (k := k) hk hL hp
    have hd := hdiag p hp
    have hs : (L : ℝ) * (1 / (p : ℝ)) - 1
          + ((L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y - 1 / (p : ℝ)))
            - ((jsp87Primes y).card : ℝ))
        ≤ ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) := by
      nlinarith [hsp, hd, ho]
    calc (L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)
          - 1 - ((jsp87Primes y).card : ℝ)
        = (L : ℝ) * (1 / (p : ℝ)) - 1
          + ((L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y - 1 / (p : ℝ)))
            - ((jsp87Primes y).card : ℝ)) := by ring
      _ ≤ ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) := hs
  have h1 : (∑ p ∈ jsp87Primes y,
        ((L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)
          - 1 - ((jsp87Primes y).card : ℝ)))
      ≤ ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) :=
    Finset.sum_le_sum (s := jsp87Primes y) (N := ℝ) fun p hp => hrow p hp
  have hA : (∑ p ∈ jsp87Primes y, ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2))
      = (jsp87Lam y + 1) * jsp87Lam y - jsp87LamSq y := by
    have hm : (∑ p ∈ jsp87Primes y, ((1 / (p : ℝ)) * (jsp87Lam y + 1)))
        = (jsp87Lam y + 1) * jsp87Lam y := by
      have h2 : (∑ p ∈ jsp87Primes y, ((1 / (p : ℝ)) * (jsp87Lam y + 1)))
          = ∑ p ∈ jsp87Primes y, ((jsp87Lam y + 1) * (1 / (p : ℝ))) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      rw [h2]
      exact (Finset.mul_sum (s := jsp87Primes y) (f := fun p => 1 / (p : ℝ))
        (a := jsp87Lam y + 1)).symm
    rw [Finset.sum_sub_distrib, hm]
    rfl
  have hC1 : (∑ p ∈ jsp87Primes y, ((L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)))
      = (L : ℝ) * ((jsp87Lam y + 1) * jsp87Lam y - jsp87LamSq y) := by
    have hm := (Finset.mul_sum (s := jsp87Primes y)
      (f := fun p => ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)) (a := (L : ℝ))).symm
    rw [hm, hA]
  have hC2 : (∑ p ∈ jsp87Primes y, (1 : ℝ)) = ((jsp87Primes y).card : ℝ) :=
    Finset.sum_const (s := jsp87Primes y) (b := (1 : ℝ)) |>.trans (by rw [nsmul_eq_mul, mul_one])
  have hC3 : (∑ p ∈ jsp87Primes y, ((jsp87Primes y).card : ℝ))
      = ((jsp87Primes y).card : ℝ) * ((jsp87Primes y).card : ℝ) :=
    Finset.sum_const (s := jsp87Primes y) (b := ((jsp87Primes y).card : ℝ)) |>.trans (by rw [nsmul_eq_mul])
  have hD : (∑ p ∈ jsp87Primes y, (((L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)) - 1 - ((jsp87Primes y).card : ℝ)))
      = (L : ℝ) * ((jsp87Lam y + 1) * jsp87Lam y - jsp87LamSq y) - ((jsp87Primes y).card : ℝ) - (((jsp87Primes y).card : ℝ) * ((jsp87Primes y).card : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hC1, hC2, hC3]
  calc (L : ℝ) * (jsp87Lam y + jsp87Lam y ^ 2 - jsp87LamSq y) - (((jsp87Primes y).card : ℝ) + ((jsp87Primes y).card : ℝ) ^ 2)
      = (L : ℝ) * ((jsp87Lam y + 1) * jsp87Lam y - jsp87LamSq y) - ((jsp87Primes y).card : ℝ) - (((jsp87Primes y).card : ℝ) * ((jsp87Primes y).card : ℝ)) := by ring
    _ = ∑ p ∈ jsp87Primes y, (((L : ℝ) * ((1 / (p : ℝ)) * (jsp87Lam y + 1) - (1 / (p : ℝ)) ^ 2)) - 1 - ((jsp87Primes y).card : ℝ)) := hD.symm
    _ ≤ ∑ p ∈ jsp87Primes y, ∑ q ∈ jsp87Primes y, ((jsp87CntMul2 p q L k : ℕ) : ℝ) := h1



/-- **THE CROWN OF §5: THE VARIANCE OF THE SMALL-PRIME CONTENT DIVERGES
(Turán).**  For every `y ≥ 32`, every window length `L` with `y² ≤ 2L` and
**every** shift `k` with `1 ≤ k`,

```
Var (N ↦ #{p ≤ y : p ∣ N+k})  ≥  ¼ · λ(y)  −  4 ,
```

so the variance of the sieve split grows without bound with `y`, uniformly in
the shift.  This is round 135's named blocker `jsp87_winVar_small_ge`, CLOSED:
it needs no analytic input at all — only the counting layer of §1, the exact
moments of §4 and the trivial bound `#{p ≤ y} ≤ y`. -/
theorem jsp87_winVar_small_ge {y L k : ℕ} (hy : 32 ≤ y) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hyL : y * y ≤ 2 * L) :
    jsp87WinVar L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ)) ≥ jsp87Lam y / 4 - 4 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show (0 : ℕ) < L by omega)
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show (0 : ℕ) < y by omega)
  have hyne : (y : ℝ) ≠ 0 := ne_of_gt hypos
  have hvar := jsp87WinVar_eq_sum L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ)) hL
  have hS1x := jsp87_smallSum_le (y := y) (L := L) (k := k) hk hL
  have hS2x := jsp87_smallSqSum_ge (y := y) (L := L) (k := k) hk hL
  set lam : ℝ := jsp87Lam y with hlam
  set c : ℝ := ((jsp87Primes y).card : ℝ) with hc
  set S1 : ℝ := ∑ N ∈ Finset.range L, ((jsp87SieveCard (N + k) y : ℕ) : ℝ) with hS1
  set S2 : ℝ := ∑ N ∈ Finset.range L, (((jsp87SieveCard (N + k) y : ℕ) : ℕ) : ℝ) ^ 2 with hS2
  have hpiR : c ≤ (y : ℝ) := by
    rw [hc]
    exact_mod_cast (jsp87Primes_card_le y)
  have hlamnn : 0 ≤ lam := by
    rw [hlam]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hS1nn : 0 ≤ S1 := by
    rw [hS1]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hS1' : S1 ≤ (L : ℝ) * lam + c := by
    rw [hS1, hlam, hc]
    exact hS1x
  have hS2' : (L : ℝ) * (lam + lam ^ 2 - jsp87LamSq y) - (c + c ^ 2) ≤ S2 := by
    rw [hS2, hlam, hc]
    exact hS2x
  have hcLnn : 0 ≤ c / (L : ℝ) :=
    div_nonneg (by rw [hc]; exact_mod_cast (Nat.zero_le _)) (le_of_lt hLpos)
  -- the window estimate: at most `1/16` prime per unit of length
  have hcL : c / (L : ℝ) ≤ 1 / 16 := by
    have h1 : c / (L : ℝ) ≤ (y : ℝ) / (L : ℝ) :=
      div_le_div_of_nonneg_right hpiR (le_of_lt hLpos)
    have h2 : (y : ℝ) / (L : ℝ) ≤ 2 / (y : ℝ) := by
      have hcast : (y * y : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hyL
      have hkey : (y : ℝ) ≤ (2 / (y : ℝ)) * (L : ℝ) := by
        have h1 := (le_div_iff₀ hypos).2 (show (y : ℝ) * (y : ℝ) ≤ 2 * (L : ℝ) by linarith [hcast])
        have hexp : 2 * (L : ℝ) / (y : ℝ) = (2 / (y : ℝ)) * (L : ℝ) := by ring
        rw [← hexp]
        exact h1
      exact (div_le_iff₀ hLpos).2 hkey
    have h3 : (2 : ℝ) / (y : ℝ) ≤ 1 / 16 := by
      have hkey : (2 : ℝ) ≤ (y : ℝ) / 16 := by
        rw [le_div_iff₀ (by norm_num)]
        norm_num
        exact_mod_cast hy
      have heq : (y : ℝ) / 16 / (y : ℝ) = 1 / 16 := by field_simp
      rw [← heq]
      exact (div_le_div_iff_of_pos_right hypos).2 hkey
    linarith
  have hc2L : c ^ 2 / (L : ℝ) ≤ 2 := by
    calc c ^ 2 / (L : ℝ) ≤ (y : ℝ) ^ 2 / (L : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith [hpiR]) (le_of_lt hLpos)
      _ ≤ 2 := by
        apply (div_le_iff₀ hLpos).2
        have hcast : (y * y : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hyL
        linarith
  have hcLsq : (c / (L : ℝ)) ^ 2 ≤ 1 := by
    calc (c / (L : ℝ)) ^ 2 ≤ (1 / 16) ^ 2 := by nlinarith [hcLnn]
      _ ≤ 1 := by norm_num
  -- the second moment, with the diagonal absorbed
  have hA : lam + lam ^ 2 - jsp87LamSq y - c / (L : ℝ) - c ^ 2 / (L : ℝ)
      ≤ S2 / (L : ℝ) := by
    have hXe : ((L : ℝ) * (lam + lam ^ 2 - jsp87LamSq y) - (c + c ^ 2)) / (L : ℝ)
        = lam + lam ^ 2 - jsp87LamSq y - c / (L : ℝ) - c ^ 2 / (L : ℝ) := by
      field_simp
      ring
    have h2 := div_le_div_of_nonneg_right hS2' (le_of_lt hLpos)
    rw [hXe] at h2
    exact h2
  -- the first moment squared
  have hC : (S1 / (L : ℝ)) ^ 2 ≤ lam ^ 2 + 2 * lam * (c / (L : ℝ)) + (c / (L : ℝ)) ^ 2 := by
    have h1 : S1 / (L : ℝ) ≤ ((L : ℝ) * lam + c) / (L : ℝ) := by
      rw [div_le_iff₀ hLpos]
      have hq : ((L : ℝ) * lam + c) / (L : ℝ) * (L : ℝ) = (L : ℝ) * lam + c := by
        field_simp
      rw [hq]
      exact hS1'
    have hS1Lnn : 0 ≤ S1 / (L : ℝ) := div_nonneg hS1nn (le_of_lt hLpos)
    have hsq := mul_self_le_mul_self hS1Lnn h1
    have hsq' : (S1 / (L : ℝ)) ^ 2 ≤ (((L : ℝ) * lam + c) / (L : ℝ)) ^ 2 := by
      simpa only [pow_two] using hsq
    have hid' : ((L : ℝ) * lam + c) / (L : ℝ) = lam + c / (L : ℝ) := by
      field_simp
    rw [hid'] at hsq'
    have hexp : (lam + c / (L : ℝ)) ^ 2
        = lam ^ 2 + 2 * lam * (c / (L : ℝ)) + (c / (L : ℝ)) ^ 2 := by ring
    rw [hexp] at hsq'
    exact hsq'
  rw [hvar, hS2, hS1, ← div_pow]
  nlinarith [jsp87LamSq_le_half_lam y]


/-- **A BOUNDED FUNCTION HAS SMALL SPREAD — THE SHIFTED VERSION.**  Identical to
`jsp87WinCSq_le_const`, but the hypothesis is only needed on the window, which
is what one has when the bound is a *height* bound (`ω`'s unsieved content is
`≤ 3` only for `n < (y+1)⁴`). -/
private theorem jsp87WinCSq_le_const' (L k : ℕ) (hL : 1 ≤ L) {g : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ N ∈ Finset.range L, 0 ≤ g (N + k) ∧ g (N + k) ≤ c) :
    jsp87WinCSq L k g ≤ c ^ 2 * (L : ℝ) / 4 := by
  set S : ℝ := ∑ N ∈ Finset.range L, g (N + k) with hS
  have hkey := jsp87WinCSq_eq_sum L k g hL
  have hsq : ∀ N ∈ Finset.range L, (g (N + k)) ^ 2 ≤ c * g (N + k) := by
    intro N hN
    have h1 := hg N hN
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

/-- **§5.5 — THE VARIANCE OF `ω` ITSELF OVER A SHIFTED WINDOW.**  For every
`y ≥ 32`, every `L ≥ 1`, every `1 ≤ k ≤ L` with `y² ≤ 2L` and `2L ≤ y³`,

```
Var (N ↦ ω (N+k))  ≥  ⅛ · λ(y)  −  5 ,
```

i.e. the diagonal variance object `jsp87TcVarAt L k` of arXiv:2512.01739 §5.4
diverges.  The large-prime part of `ω` is at most `3` on the window, so it costs
at most `9L/4` of centred second moment (and a factor `1/2` for the
`(x+y)² ≥ x²/2 − y²` split of `jsp87WinCSq_add_ge`). -/
theorem jsp87_tcVarAt_ge {y L k : ℕ} (hy : 32 ≤ y) (hL : 1 ≤ L) (hk : 1 ≤ k) (hkL : k ≤ L)
    (hyL : y * y ≤ 2 * L) (hy3 : 2 * L ≤ y ^ 3) :
    jsp87TcVarAt L k ≥ jsp87Lam y / 8 - 5 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show (0 : ℕ) < L by omega)
  have hstep : ∀ N ∈ Finset.range L,
      ((omega (N + k) : ℕ) : ℝ) = ((jsp87SieveCard (N + k) y : ℕ) : ℝ)
        + ((jsp87UnsievedCard (N + k) y : ℕ) : ℝ) := by
    intro N hN
    rw [omega_eq_sieve_add_unsieved (N + k) y, Nat.cast_add]
  have hsum1 : (∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ))
      = ∑ N ∈ Finset.range L, (((jsp87SieveCard (N + k) y : ℕ) : ℝ)
        + ((jsp87UnsievedCard (N + k) y : ℕ) : ℝ)) :=
    Finset.sum_congr rfl fun N hN => hstep N hN
  have hsum2 : (∑ N ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) ^ 2)
      = ∑ N ∈ Finset.range L, ((((jsp87SieveCard (N + k) y : ℕ) : ℝ)
        + ((jsp87UnsievedCard (N + k) y : ℕ) : ℝ)) ^ 2) := by
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [hstep N hN]
  have hCS : jsp87WinCSq L k (fun n => ((omega n : ℕ) : ℝ))
      = jsp87WinCSq L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ)
        + ((jsp87UnsievedCard n y : ℕ) : ℝ)) := by
    have hmean : jsp87WinMean L k (fun n => ((omega n : ℕ) : ℝ))
        = jsp87WinMean L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ)
          + ((jsp87UnsievedCard n y : ℕ) : ℝ)) := by
      have hm1 := jsp87WinMean_eq L k (fun n => ((omega n : ℕ) : ℝ))
      have hm2 := jsp87WinMean_eq L k
        (fun n => ((jsp87SieveCard n y : ℕ) : ℝ) + ((jsp87UnsievedCard n y : ℕ) : ℝ))
      rw [hm1, hm2, hsum1]
    unfold jsp87WinCSq
    rw [hmean]
    dsimp only
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [hstep N hN]
  have hCS1 := jsp87WinCSq_add_ge L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ))
    (fun n => ((jsp87UnsievedCard n y : ℕ) : ℝ))
  have hCS2 := jsp87_winVar_small_ge (y := y) (L := L) (k := k) hy hk hL hyL
  have hCS2' : jsp87WinCSq L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ))
      ≥ (L : ℝ) * (jsp87Lam y / 4 - 4) := by
    have hcv := jsp87WinCSq_eq_var L k (fun n => ((jsp87SieveCard n y : ℕ) : ℝ)) hL
    rw [hcv]
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := le_of_lt hLpos
    nlinarith [mul_le_mul_of_nonneg_left hCS2 hLnn]
  have hCS3 : jsp87WinCSq L k (fun n => ((jsp87UnsievedCard n y : ℕ) : ℝ))
      ≤ 3 ^ 2 * (L : ℝ) / 4 := by
    refine jsp87WinCSq_le_const' L k hL (c := (3 : ℝ)) (by norm_num) ?_
    intro N hN
    have hNL : N < L := Finset.mem_range.mp hN
    have hNk : 0 < N + k := by omega
    have h4 : N + k < (y + 1) ^ 4 := by
      have h5 : N + k + 1 ≤ y ^ 3 := by omega
      have h6 : y ^ 3 ≤ (y + 1) ^ 4 := by
        nlinarith [Nat.zero_le (y ^ 3), Nat.zero_le (y + 1)]
      omega
    have hle := jsp87UnsievedCard_le_three (by omega) hNk h4
    exact ⟨Nat.cast_nonneg _, (by exact_mod_cast hle)⟩
  have hCS4 : jsp87WinCSq L k (fun n => ((omega n : ℕ) : ℝ))
      ≥ (L : ℝ) * (jsp87Lam y / 8 - 5) := by
    rw [← hCS] at hCS1
    nlinarith [hCS1, hCS2', hCS3]
  have hcv2 := jsp87WinCSq_eq_var L k (fun n => ((omega n : ℕ) : ℝ)) hL
  have hcv3 : jsp87WinVar L k (fun n => ((omega n : ℕ) : ℝ))
      = jsp87WinCSq L k (fun n => ((omega n : ℕ) : ℝ)) / (L : ℝ) := by
    rw [hcv2]
    field_simp
  have hX : jsp87Lam y / 8 - 5 ≤ jsp87WinCSq L k (fun n => ((omega n : ℕ) : ℝ)) / (L : ℝ) := by
    rw [le_div_iff₀ hLpos]
    nlinarith [hCS4]
  rw [← jsp87WinVar_omega L k, hcv3]
  exact hX

/-- **§5.6 — THE PRIME RECIPROCAL MASS DOMINATES THE PRIME PARTIAL SUM.**  For
`y ≥ 2` every prime below `y` is counted by `jsp87Lam y`. -/
theorem jsp87_lam_ge_primeRecip (y : ℕ) (hy : 2 ≤ y) :
    (∑ i ∈ Finset.range y, jsp87PrimeRecipTerm i) ≤ jsp87Lam y := by
  have h1 : (∑ i ∈ Finset.range y, jsp87PrimeRecipTerm i)
      = ∑ i ∈ (Finset.range y).filter Nat.Prime, (1 / (i : ℝ)) := by
    simp only [jsp87PrimeRecipTerm]
    rw [Finset.sum_filter]
  have hsub : ((Finset.range y).filter Nat.Prime : Finset ℕ) ⊆ jsp87Primes y := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hlt : p < y := Finset.mem_range.mp hmem.1
    rw [mem_jsp87Primes]
    exact ⟨Nat.Prime.two_le hmem.2, by omega, hmem.2⟩
  rw [h1]
  unfold jsp87Lam
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- **THE HARMONIC MASS OF THE PRIMES DIVERGES (Euler, round 127, as a limit).** -/
theorem jsp87_lam_tendsto : Filter.Tendsto jsp87Lam Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro b
  obtain ⟨a, ha⟩ := Filter.tendsto_atTop_atTop.1 jsp87PrimeRecip_tendsto b
  refine ⟨max a 2, fun y hy => ?_⟩
  have h2 : 2 ≤ y := by omega
  exact le_trans (ha y (by omega)) (jsp87_lam_ge_primeRecip y h2)

/-- **§5.7 — THE CROWN: THE VARIANCE OF `ω` OVER A SHIFTED WINDOW IS UNBOUNDED,
UNIFORMLY IN THE SHIFT (the Turán–Erdős–Kac statement).**  For every `C > 0`
there is a window length `L` with `jsp87TcVarAt L k > C` for **every** shift
`1 ≤ k ≤ L`.  With the definition of `jsp87TcVarAt` this says the *diagonal*
variance of §5.4 of arXiv:2512.01739 can be made arbitrarily large: **the
"variance is large" clause of hypothesis (5.21) is satisfiable at large
heights**, so it is NOT the obstruction.  What is left of `jsp_000087_main` is
the off-diagonal correlation estimate `jsp87Mcov_small` and the sample
geometry. -/
theorem jsp87_var_omega_diverges {C : ℝ} (hC : 0 < C) {K : ℕ} :
    ∃ L, K ≤ L ∧ ∀ k, 1 ≤ k → k ≤ L → jsp87TcVarAt L k > C := by
  have hkey : ∀ b : ℝ, ∃ a : ℕ, ∀ y, a ≤ y → b ≤ jsp87Lam y := by
    intro b
    obtain ⟨a, ha⟩ := Filter.tendsto_atTop_atTop.1 jsp87_lam_tendsto b
    exact ⟨a, fun y hy => ha y hy⟩
  obtain ⟨a, ha⟩ := hkey (8 * (C + 5) + 1)
  set y : ℕ := max a (max 32 (2 * (K + 1))) with hy
  have hy1 : 32 ≤ y := by
    rw [hy]
    exact le_trans (le_max_left 32 (2 * (K + 1))) (le_max_right a (max 32 (2 * (K + 1))))
  have hy2 : 8 * (C + 5) + 1 ≤ jsp87Lam y := by
    rw [hy]
    exact ha _ (le_max_left a (max 32 (2 * (K + 1))))
  have hy' : 2 * (K + 1) ≤ y := by
    rw [hy]
    exact le_trans (le_max_right 32 (2 * (K + 1))) (le_max_right a (max 32 (2 * (K + 1))))
  have hy3 : 2 * (K + 1) ≤ y ^ 3 := by
    have h2 : (2 : ℕ) ≤ y := by omega
    have h3 : K + 1 ≤ y * y := by nlinarith [h2, hy']
    have h4 : y ^ 3 ≥ 2 * (y * y) := by nlinarith [sq_nonneg y]
    omega
  set L : ℕ := max K (y * y) with hL
  have hKL : K ≤ L := by
    rw [hL]
    exact le_max_left _ _
  have hyL : y * y ≤ 2 * L := by
    rw [hL]
    have h1 : y * y ≤ max K (y * y) := le_max_right _ _
    omega
  have hy3L : 2 * L ≤ y ^ 3 := by
    rcases Nat.le_total K (y * y) with h | h
    · rw [hL, max_eq_right h]
      have h2 : (2 : ℕ) ≤ y := by omega
      have h3 : 2 * (y * y) ≤ y ^ 3 := by
        have h4 : 2 * (y * y) ≤ y * (y * y) := by nlinarith [sq_nonneg y]
        have h5 : y * (y * y) = y ^ 3 := by rw [pow_succ, pow_two]; ring
        rw [← h5]
        exact h4
      omega
    · rw [hL, max_eq_left h]
      have h2 : 2 * (K + 1) ≤ y ^ 3 := hy3
      omega
  refine ⟨L, hKL, ?_⟩
  intro k hk hkL
  have h1 : 1 ≤ L := by
    have h2 : 0 < L := by
      by_contra h0
      have hL0 : L = 0 := by omega
      rw [hL0] at hyL
      have hz : y * y = 0 := by omega
      rcases Nat.mul_eq_zero.mp hz with h | h <;> omega
    omega
  have h2 := jsp87_tcVarAt_ge (y := y) (L := L) (k := k) hy1 h1 hk hkL hyL hy3L
  have h3 : C < jsp87Lam y / 8 - 5 := by linarith
  linarith


end JSP87
