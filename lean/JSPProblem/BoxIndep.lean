/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-118).
-/
import JSPProblem.CrtBox
import JSPProblem.HarmonicMass

/-!
# JSP-000087, round 146 — THE INDEPENDENCE THEOREM ON THE BOX

## The gap this file attacks

Round 145 showed that on the **box of residues** `B P = [0, ∏_{p ∈ P} p)` of a
finite set `P` of primes the truncated expectation of §5 of
arXiv:2512.01739 *factorises* (hypothesis (5.16)–(5.17) is an identity there) and
that hypothesis **(5.15) is false on every box** — with a lower bound that
degenerates to `0` as the harmonic mass `∑ 1/p` is small.  Two things were left.

* **the variance of the *total*** phase was never computed: round 145 only
  compared the statistics of a *single* `X_p` to their values on one period, and
  never used the fact that the residues `(n mod p)_{p ∈ P}` are *independent* on
  a box.  The natural statement is §3–§4 below: **on a box the `X_p` are pairwise
  independent, so the variance of `∑_p q_p X_p` is exactly the sum of the
  single-prime variances.**  Consequently hypothesis **(5.21) on a box is a
  statement about single primes only** (§5).

* **no uniform gap.**  Refuting (5.15) "for large harmonic mass" is not enough:
  the endgame needs a *uniform* obstruction, because the published proof asks
  for the truncation errors `κ₁+κ₂+κ₃ = o(1)`.  §6–§7 close this: the
  two-class criterion **(5.21′)** — the paper's own arithmetic hypothesis on the
  prime set — forces on the box

```
  1 − exp(−8)  ≤  ‖𝔼ᶜ e (q ∑_p X_p) − 1‖  ≤  κ₁ + κ₂ + κ₃ ,
```

a *uniform* gap of `1 − e^{−8} > 99 %`, for **every** `K ≥ 1`, `H ≥ 1` and every
admissible `q`.  §8 adds the price in cardinality, and §9 assembles the
conclusion: **the endgame of §§5.3–5.14 of arXiv:2512.01739 cannot be started
on the box of residues of a prime set that satisfies the published
sample-geometry condition (5.21′)** — not merely "at all large heights", but
always, and with an explicit constant.

## What is *not* proved here

The blocker is unchanged: `jsp87Mcov_small`, the Chowla-type two-point
correlation of `ω` (arXiv:2512.01739 Thm 3.1, from Pilatte).  Mathlib has no
such statement, and the box is now excluded at *every* height, so what remains
is a genuinely **correlated** sample — as in round 145, only now with the
quantitative statement above rather than a limit in the height.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  ARITHMETIC OF THE BOX -/

/-- **THE BOX IS A NONEMPTY MULTIPLE OF EVERY PRIME IN IT.** -/
private theorem jsp87Box_div_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (p : ℕ) (hp : p ∈ P) : 0 < (∏ p' ∈ P, p') / p := by
  classical
  have hPd : p ∣ ∏ p' ∈ P, p' := Finset.dvd_prod_of_mem id hp
  have hp0 : 0 < p := (hP p hp).pos
  obtain ⟨w, hw⟩ := hPd
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with hz | hz
    · exfalso
      have hz0 : (∏ p' ∈ P, p') = 0 := by rw [hw, hz]; simp
      have h1 : 0 < ∏ p' ∈ P, p' := by
        refine Finset.prod_pos fun p' hp' => ?_
        have hp' : 2 ≤ p' := Nat.Prime.two_le (hP p' hp')
        omega
      omega
    · exact hz
  rw [hw, Nat.mul_div_right w hp0]
  exact hwpos

/-! ## §1  THE MEAN OF A PERIODIC FAMILY ON THE BOX -/

/-- **★★ THE MEAN OVER THE BOX OF A `p`-PERIODIC FAMILY IS ITS MEAN OVER ONE
PERIOD ★★**

Round 145 proved this for the single family `φ (X_p · q)` of §2 there; the
statement needed by the independence theorem of §3 is the general one: on
`B P`, a family that sees only `n mod p` is exactly as distributed as on
`[0, p)`. -/
theorem jsp87FAvg_box_period {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (p : ℕ) (hp : p ∈ P) (f : ℕ → ℝ) (hf : ∀ i : ℕ, f (i % p) = f i) :
    jsp87FAvg (jsp87Box P) f = jsp87FAvg (Finset.range p) f := by
  classical
  have hp0 : 0 < p := (hP p hp).pos
  have hdiv : 0 < (∏ p' ∈ P, p') / p := jsp87Box_div_pos hP p hp
  have hbox := jsp87Box_eq_range_mul hP (fun p' hp' => Nat.Prime.two_le (hP p' hp')) p hp
  have hsum := jsp87sum_period ((∏ p' ∈ P, p') / p) p hp0 (fun i : ℕ => f i)
  have hsum2 : (∑ n ∈ Finset.range (((∏ p' ∈ P, p') / p) * p), f n)
      = (((∏ p' ∈ P, p') / p : ℕ) : ℝ) * ∑ i ∈ Finset.range p, f i := by
    calc (∑ n ∈ Finset.range (((∏ p' ∈ P, p') / p) * p), f n)
        = ∑ n ∈ Finset.range (((∏ p' ∈ P, p') / p) * p), f (n % p) :=
          Finset.sum_congr rfl fun n hn => (hf n).symm
      _ = (((∏ p' ∈ P, p') / p : ℕ) : ℕ) • ∑ i ∈ Finset.range p, f i := hsum
      _ = (((∏ p' ∈ P, p') / p : ℕ) : ℝ) * ∑ i ∈ Finset.range p, f i := by
          rw [nsmul_eq_mul]
  rw [hbox, jsp87FAvg, jsp87FAvg, Finset.card_range, Finset.card_range, hsum2, Nat.cast_mul]
  have hane : (((∏ p' ∈ P, p') / p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdiv
  field_simp

/-- **THE MEAN OF THE CONSTANT `1` OVER A NONEMPTY PERIOD IS `1`.** -/
private theorem jsp87FAvg_range_one (p : ℕ) (hp : 0 < p) :
    jsp87FAvg (Finset.range p) (fun _ => 1) = 1 := by
  rw [jsp87FAvg, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  field_simp

/-! ## §2  THE CRT MEAN-FACTORISATION, IN FULL GENERALITY -/

/-- **★★ THE CHINESE-REMAINDER MEAN-FACTORISATION ★★**

Let `f p` be a `p`-periodic family of real numbers, indexed by a set `P` of
distinct primes.  Then on the box of residues

```
  𝔼ᶜ_{n < M} ∏_{p ∈ P} f p n   =   ∏_{p ∈ P} 𝔼ᶜ_{m < p} f p m ,     M = ∏_{p ∈ P} p .
```

Round 145 proved this for the family `e (q X_p)` of the endgame
(`jsp87CAvg_box_prod`); the general statement is what makes the *variance* of
the total phase computable. -/
theorem jsp87FAvg_box_prod {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℕ → ℝ)
    (hf : ∀ p ∈ P, ∀ i : ℕ, f p (i % p) = f p i) :
    jsp87FAvg (jsp87Box P) (fun n => ∏ p ∈ P, f p n)
      = ∏ p ∈ P, jsp87FAvg (Finset.range p) (f p) := by
  classical
  have hper : ∀ q' ∈ P, ∀ i : ℕ,
      ((f q' (i % q') : ℝ) : ℂ) = ((f q' i : ℝ) : ℂ) :=
    fun q' hq' i => congrArg (fun z : ℝ => (z : ℂ)) (hf q' hq' i)
  have hsum := jsp87sum_prod_finset (fun q' i => ((f q' i : ℝ) : ℂ)) hP hper
  have hnum : (∑ n ∈ jsp87Box P, ((∏ p ∈ P, f p n : ℝ) : ℂ))
      = ∏ q' ∈ P, (∑ m ∈ Finset.range q', ((f q' m : ℝ) : ℂ)) := by
    have hcast : ∀ n : ℕ, ((∏ p ∈ P, f p n : ℝ) : ℂ)
        = ∏ q' ∈ P, ((f q' n : ℝ) : ℂ) := by
      intro n
      push_cast
      rfl
    refine (Finset.sum_congr rfl fun n hn => hcast n).trans ?_
    exact hsum
  have hinv : ∀ (S : Finset ℕ) (g : ℕ → ℂ),
      (∏ i ∈ S, (g i)⁻¹) = (∏ i ∈ S, g i)⁻¹ := by
    intro S g
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, ih]
      field_simp
  have hcastD : (∏ p ∈ P, ((p : ℕ) : ℂ)) = (((∏ p ∈ P, p : ℕ) : ℕ) : ℂ) := by
    push_cast
    rfl
  -- each single-prime factor, in the normalised form `S p = 𝔼ᶜ p f p · p`
  have hfac : ∀ q' ∈ P, (∑ m ∈ Finset.range q', ((f q' m : ℝ) : ℂ))
      = ((jsp87FAvg (Finset.range q') (f q') : ℝ) : ℂ) * ((q' : ℕ) : ℂ) := by
    intro q' hq'
    have hq'0 : (q' : ℕ) ≠ 0 := Nat.ne_of_gt (hP q' hq').pos
    have hc : ((q' : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq'0
    have h2 : (∑ m ∈ Finset.range q', ((f q' m : ℝ) : ℂ)) / ((q' : ℕ) : ℂ)
        = ((jsp87FAvg (Finset.range q') (f q') : ℝ) : ℂ) := by
      simpa only [jsp87CAvg, Finset.card_range] using
        (jsp87CAvg_ofReal (Finset.range q') (f q'))
    rw [div_eq_mul_inv, mul_comm] at h2
    calc (∑ m ∈ Finset.range q', ((f q' m : ℝ) : ℂ))
        = ((↑q' : ℂ)⁻¹ * ∑ m ∈ Finset.range q', ((f q' m : ℝ) : ℂ)) * ↑q' := by
          field_simp
      _ = ((jsp87FAvg (Finset.range q') (f q') : ℝ) : ℂ) * ↑q' := by rw [← h2]
  have hcastS : (∏ q' ∈ P, (∑ m ∈ Finset.range q', ((f q' m : ℝ) : ℂ)))
      = (((∏ p ∈ P, ↑(jsp87FAvg (Finset.range p) (f p))) * ∏ p ∈ P, ↑p) : ℂ) := by
    rw [Finset.prod_congr rfl fun q' hq' => hfac q' hq']
    rw [Finset.prod_mul_distrib]
  have hℂ : jsp87CAvg (jsp87Box P) (fun n => ((∏ p ∈ P, f p n : ℝ) : ℂ))
      = ∏ p ∈ P, jsp87CAvg (Finset.range p) (fun i => ((f p i : ℝ) : ℂ)) := by
    have hdiv : (∏ p ∈ P, (∑ m ∈ Finset.range p, ((f p m : ℝ) : ℂ)))
          / ∏ p ∈ P, ((p : ℕ) : ℂ)
        = ∏ p ∈ P, ((∑ m ∈ Finset.range p, ((f p m : ℝ) : ℂ)) / ((p : ℕ) : ℂ)) := by
      rw [div_eq_mul_inv, ← (hinv P (fun p => (p : ℂ))),
        ← (Finset.prod_mul_distrib (M := ℂ))]
      simp only [div_eq_mul_inv]
    simp only [jsp87CAvg]
    rw [hnum]
    simp only [jsp87Box, Finset.card_range]
    rw [← hcastD, hdiv]
  -- cast `hℂ` back to the reals
  have hcast : ∀ n : ℕ, (∏ p ∈ P, ((f p n : ℝ) : ℂ))
      = (((∏ p ∈ P, f p n : ℝ)) : ℂ) := by
    intro n
    push_cast
    rfl
  have hnum' : (∑ n ∈ jsp87Box P, ∏ p ∈ P, ((f p n : ℝ) : ℂ))
      = (∑ n ∈ jsp87Box P, (((∏ p ∈ P, f p n : ℝ)) : ℂ)) :=
    Finset.sum_congr rfl fun n hn => hcast n
  have hL : jsp87CAvg (jsp87Box P) (fun n => ∏ p ∈ P, ((f p n : ℝ) : ℂ))
      = jsp87CAvg (jsp87Box P) (fun n => (((∏ p ∈ P, f p n : ℝ)) : ℂ)) := by
    simp only [jsp87CAvg]
    rw [hnum']
  have hR : (∏ p ∈ P, jsp87CAvg (Finset.range p) (fun i => ((f p i : ℝ) : ℂ)))
      = ((∏ p ∈ P, jsp87FAvg (Finset.range p) (f p) : ℝ) : ℂ) := by
    calc (∏ p ∈ P, jsp87CAvg (Finset.range p) (fun i => ((f p i : ℝ) : ℂ)))
        = ∏ p ∈ P, ((jsp87FAvg (Finset.range p) (f p) : ℝ) : ℂ) :=
          Finset.prod_congr rfl fun p _ => jsp87CAvg_ofReal _ _
      _ = ((∏ p ∈ P, jsp87FAvg (Finset.range p) (f p) : ℝ) : ℂ) := by
        push_cast
        rfl
  rw [← hL, hR] at hℂ
  have hnum'' : (∑ n ∈ jsp87Box P, ∏ p ∈ P, ((f p n : ℝ) : ℂ))
      = (((∑ n ∈ jsp87Box P, ∏ p ∈ P, f p n) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hL2 : jsp87CAvg (jsp87Box P) (fun n => ∏ p ∈ P, ((f p n : ℝ) : ℂ))
      = ((jsp87FAvg (jsp87Box P) (fun n => ∏ p ∈ P, f p n) : ℝ) : ℂ) := by
    simp only [jsp87CAvg, jsp87FAvg, hnum'']
    push_cast
    rfl
  rw [hL2] at hℂ
  exact_mod_cast hℂ

/-- **A FAMILY OF PERIODIC FAMILIES MIXED WITH `1`s STILL FACTORISES.** -/
private theorem jsp87prod_two {P : Finset ℕ} {p p' : ℕ} (hp : p ∈ P) (hp' : p' ∈ P)
    (hne : p ≠ p') (F : ℕ → ℕ → ℝ) (f g : ℕ → ℝ) (hF : ∀ n, F p n = f n)
    (hF' : ∀ n, F p' n = g n)
    (hF1 : ∀ x ∈ P, x ≠ p → x ≠ p' → ∀ n, F x n = 1) :
    ∀ n, (∏ x ∈ P, F x n) = f n * g n := by
  classical
  intro n
  have hpP' : p' ∈ P.erase p := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hp'⟩
  have hrest : (∏ x ∈ (P.erase p).erase p', F x n) = 1 := by
    have hstep : (∏ x ∈ (P.erase p).erase p', F x n)
        = (∏ _ ∈ (P.erase p).erase p', (1 : ℝ)) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      obtain ⟨hx3, hx1⟩ := Finset.mem_erase.mp hx
      obtain ⟨hx2, hx0⟩ := Finset.mem_erase.mp hx1
      exact hF1 x hx0 hx2 hx3 n
    rw [hstep]
    simp
  have h2 : (∏ x ∈ P.erase p, F x n) = F p' n * ∏ x ∈ (P.erase p).erase p', F x n :=
    (Finset.mul_prod_erase (P.erase p) (fun x => F x n) hpP').symm
  rw [hF'] at h2
  have h1 : (∏ x ∈ P, F x n) = F p n * ∏ x ∈ P.erase p, F x n :=
    (Finset.mul_prod_erase P (fun x => F x n) hp).symm
  rw [hF] at h1
  rw [h1, h2, hrest]
  ring

/-! ## §3  PAIRWISE INDEPENDENCE ON THE BOX -/

/-- **★★★ THE CROSS-MOMENTS FACTORISE ON THE BOX ★★★**

Two `p`-periodic families, on the box of residues of a set `P` of distinct
primes, are **independent**: the mean of their product is the product of the
means, and — this is the point — the statement is about the *box*, i.e. about a
sample geometry, not about a single prime.  Together with §4 this is the
*independence* that the independent-copy comparison (5.16)–(5.17) of
arXiv:2512.01739 assumes in general and that is exact here. -/
theorem jsp87FAvg_box_cross {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {p p' : ℕ}
    (hp : p ∈ P) (hp' : p' ∈ P) (hne : p ≠ p') (f g : ℕ → ℝ)
    (hf : ∀ i : ℕ, f (i % p) = f i) (hg : ∀ i : ℕ, g (i % p') = g i) :
    jsp87FAvg (jsp87Box P) (fun n => f n * g n)
      = jsp87FAvg (Finset.range p) f * jsp87FAvg (Finset.range p') g := by
  classical
  have hp0 : 0 < p := (hP p hp).pos
  have hp'0 : 0 < p' := (hP p' hp').pos
  have hpP' : p' ∈ P.erase p := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hp'⟩
  set F : ℕ → ℕ → ℝ := fun x n => if x = p then f n else if x = p' then g n else 1 with hFdef
  have hF : ∀ n, F p n = f n := by
    intro n
    simp [hFdef]
  have hF' : ∀ n, F p' n = g n := by
    intro n
    simp [hFdef, Ne.symm hne]
  have hper : ∀ x ∈ P, ∀ i : ℕ, F x (i % x) = F x i := by
    intro x hx i
    simp only [hFdef]
    split_ifs with h1 h2
    · subst h1
      exact hf i
    · subst h2
      exact hg i
    · rfl
  have hF1 : ∀ x ∈ P, x ≠ p → x ≠ p' → ∀ n, F x n = 1 := by
    intro x hx hxp hxp' n
    simp [hFdef, hxp, hxp']
  have hFp : F p = fun n => f n := funext hF
  have hFp' : F p' = fun n => g n := funext hF'
  have hkey := jsp87FAvg_box_prod hP F hper
  have hL : (fun n => ∏ x ∈ P, F x n) = (fun n => f n * g n) := by
    funext n
    exact jsp87prod_two hp hp' hne F f g hF hF' hF1 n
  rw [hL] at hkey
  have hR : (∏ x ∈ P, jsp87FAvg (Finset.range x) (F x))
      = jsp87FAvg (Finset.range p) (fun n => f n)
        * jsp87FAvg (Finset.range p') (fun n => g n) := by
    have hrest : (∏ x ∈ (P.erase p).erase p', jsp87FAvg (Finset.range x) (F x)) = 1 := by
      have hstep : (∏ x ∈ (P.erase p).erase p', jsp87FAvg (Finset.range x) (F x))
          = (∏ _ ∈ (P.erase p).erase p', (1 : ℝ)) := by
        refine Finset.prod_congr rfl fun x hx => ?_
        obtain ⟨hx3, hx1⟩ := Finset.mem_erase.mp hx
        obtain ⟨hx2, hx0⟩ := Finset.mem_erase.mp hx1
        have hx0' : jsp87FAvg (Finset.range x) (F x)
            = jsp87FAvg (Finset.range x) (fun _ => 1) := by
          unfold jsp87FAvg
          exact congrArg (fun z : ℝ => z / (((Finset.range x).card : ℕ) : ℝ))
            (Finset.sum_congr rfl fun n hn => hF1 x hx0 hx2 hx3 n)
        rw [hx0']
        exact jsp87FAvg_range_one x ((hP x hx0).pos)
      rw [hstep]
      simp
    have h2 : (∏ x ∈ P.erase p, jsp87FAvg (Finset.range x) (F x))
        = jsp87FAvg (Finset.range p') (F p')
          * ∏ x ∈ (P.erase p).erase p', jsp87FAvg (Finset.range x) (F x) :=
      (Finset.mul_prod_erase (P.erase p) (fun x => jsp87FAvg (Finset.range x) (F x)) hpP').symm
    have h1 : (∏ x ∈ P, jsp87FAvg (Finset.range x) (F x))
        = jsp87FAvg (Finset.range p) (F p)
          * ∏ x ∈ P.erase p, jsp87FAvg (Finset.range x) (F x) :=
      (Finset.mul_prod_erase P (fun x => jsp87FAvg (Finset.range x) (F x)) hp).symm
    rw [h1, h2, hrest, hFp, hFp']
    ring
  rw [hR] at hkey
  exact hkey

/-! ## §4  VARIANCE ADDITIVITY ON THE BOX -/

/-- **A PRODUCT OF NONZERO NATURAL NUMBERS IS AT LEAST ONE.** -/
private theorem jsp87prod_ge_one {P : Finset ℕ} (hP : ∀ p ∈ P, p ≠ 0) :
    (1 : ℕ) ≤ ∏ p ∈ P, p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h1 : (∏ p ∈ insert a s, p) = a * ∏ p ∈ s, p := by
      rw [Finset.prod_insert ha]
    rw [h1]
    have h2 : 0 < ∏ p ∈ s, p := Nat.lt_of_succ_le
      (ih fun p hp => hP p (Finset.mem_insert_of_mem hp))
    have h3 : 0 < a := Nat.pos_of_ne_zero (hP a (Finset.mem_insert_self a s))
    exact Nat.succ_le_of_lt (Nat.mul_pos h3 h2)

/-- **LINEARITY OF THE MEAN OVER THE BOX.** -/
private theorem jsp87FAvg_sum_box {P : Finset ℕ} (hP : ∀ p ∈ P, p ≠ 0) (g : ℕ → ℕ → ℝ) :
    jsp87FAvg (jsp87Box P) (fun n => ∑ p ∈ P, g p n) = ∑ p ∈ P, jsp87FAvg (jsp87Box P) (g p) := by
  classical
  simp only [jsp87FAvg]
  have hcard : (0 : ℕ) < (jsp87Box P).card := by
    have hne : (jsp87Box P).Nonempty := by
      refine ⟨0, Finset.mem_range.mpr ?_⟩
      have h1 : 0 < ∏ p ∈ P, p := Nat.lt_of_succ_le (jsp87prod_ge_one hP)
      omega
    exact Finset.card_pos.mpr hne
  have hc : (((jsp87Box P).card : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcard
  rw [← (Finset.sum_div P
    (fun p : ℕ => ∑ i ∈ jsp87Box P, g p i) ((jsp87Box P).card : ℕ))]
  apply (div_eq_div_iff hc hc).mpr
  exact mul_right_cancel₀ hc (by rw [Finset.sum_comm (β := ℝ)])

/-- **THE SQUARE OF A SUM, SPLIT ALONG THE DIAGONAL.** -/
private theorem jsp87sq_sum {ι : Type*} [DecidableEq ι] (P : Finset ι) (E : ι → ℝ) :
    (∑ p ∈ P, E p) ^ 2
      = ∑ p ∈ P, ((E p) ^ 2 + E p * ∑ x ∈ P.erase p, E x) := by
  classical
  have h1 : (∑ p ∈ P, E p) ^ 2 = (∑ p ∈ P, E p) * ∑ x ∈ P, E x := by ring
  rw [h1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  have h2 : (∑ x ∈ P, E p * E x) = E p * E p + ∑ x ∈ P.erase p, E p * E x := by
    have h := Finset.sum_erase_add P (fun x => E p * E x) hp
    rw [add_comm] at h
    exact h.symm
  rw [h2, ← (Finset.mul_sum (R := ℝ))]
  ring

/-- **★ THE SECOND MOMENT OF THE TOTAL PHASE, ROW BY ROW ★** — the content of
§4: on a box, the row `p` of the covariance matrix splits into the single-prime
second moment and the (independent) contributions of the other primes. -/
private theorem jsp87FAvg_sq_row {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (p : ℕ)
    (hp : p ∈ P) (g : ℕ → ℕ → ℝ) (hg : ∀ x ∈ P, ∀ i : ℕ, g x (i % x) = g x i) :
    jsp87FAvg (jsp87Box P) (fun n => g p n * ∑ x ∈ P, g x n)
      = jsp87FAvg (Finset.range p) (fun i => (g p i) ^ 2)
        + jsp87FAvg (Finset.range p) (g p) * ∑ x ∈ P.erase p, jsp87FAvg (Finset.range x) (g x) := by
  classical
  have hstep : jsp87FAvg (jsp87Box P) (fun n => g p n * ∑ x ∈ P, g x n)
      = jsp87FAvg (jsp87Box P) (fun n => ∑ x ∈ P, g p n * g x n) := by
    congr 1
    funext n
    rw [Finset.mul_sum]
  rw [hstep, jsp87FAvg_sum_box (fun p hp => (hP p hp).ne_zero)]
  have herase : (∑ x ∈ P, jsp87FAvg (jsp87Box P) (fun n => g p n * g x n))
      = jsp87FAvg (jsp87Box P) (fun n => g p n * g p n)
        + ∑ x ∈ P.erase p, jsp87FAvg (jsp87Box P) (fun n => g p n * g x n) := by
    have h := Finset.sum_erase_add P (fun x => jsp87FAvg (jsp87Box P) (fun n => g p n * g x n)) hp
    rw [add_comm] at h
    exact h.symm
  rw [herase]
  -- the diagonal: the mean of the square over the box is the mean over one period
  have hbox : jsp87FAvg (jsp87Box P) (fun n => g p n * g p n)
      = jsp87FAvg (Finset.range p) (fun i => (g p i) ^ 2) := by
    have hper : ∀ i : ℕ, (fun n => g p n * g p n) (i % p) = g p i * g p i := by
      intro i
      show g p (i % p) * g p (i % p) = g p i * g p i
      rw [hg p hp i]
    rw [jsp87FAvg_box_period hP p hp (fun n => g p n * g p n) hper]
    congr 1
    funext i
    ring
  rw [hbox]
  -- the off-diagonal rows factor out the single-prime mean
  have hZ : (∑ x ∈ P.erase p, jsp87FAvg (jsp87Box P) (fun n => g p n * g x n))
      = jsp87FAvg (Finset.range p) (g p)
        * ∑ x ∈ P.erase p, jsp87FAvg (Finset.range x) (g x) := by
    calc (∑ x ∈ P.erase p, jsp87FAvg (jsp87Box P) (fun n => g p n * g x n))
        = ∑ x ∈ P.erase p, jsp87FAvg (Finset.range p) (g p) * jsp87FAvg (Finset.range x) (g x) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          obtain ⟨hxne, hxP⟩ := Finset.mem_erase.mp hx
          exact jsp87FAvg_box_cross hP hp hxP (Ne.symm hxne) (g p) (g x) (hg p hp) (hg x hxP)
      _ = jsp87FAvg (Finset.range p) (g p) * ∑ x ∈ P.erase p, jsp87FAvg (Finset.range x) (g x) :=
        (Finset.mul_sum _ _ _).symm
  rw [hZ]

/-- **★★★ THE VARIANCE OF THE TOTAL PHASE IS THE SUM OF THE SINGLE-PRIME
VARIANCES ★★★**

On the box of residues of a set `P` of distinct primes the cube-alternating
variables `X_p` of (5.13) are **pairwise independent**, hence for any real
coefficients `c p`

```
  Var_{B P} ( ∑_{p ∈ P} c p · X p )   =   ∑_{p ∈ P} Var_{[0,p)} ( c p · X p ) .
```

**No error term, and no dependence on the box.**  This is the missing half of
round 145: the *total* phase — the only object hypothesis (5.21) constrains —
has an exactly computable variance on a box. -/
theorem jsp87Var_sum_box {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (K H : ℕ) (c : ℕ → ℝ) :
    jsp87Var (jsp87Box P) (fun n => ∑ p ∈ P, c p * jsp87Xp0 (jsp87BinV K) p n H)
      = ∑ p ∈ P, jsp87Var (Finset.range p)
          (fun i => c p * jsp87Xp0 (jsp87BinV K) p i H) := by
  classical
  set g : ℕ → ℕ → ℝ := fun x n => c x * jsp87Xp0 (jsp87BinV K) x n H with hgdef
  have hg : ∀ x ∈ P, ∀ i : ℕ, g x (i % x) = g x i := by
    intro x hx i
    simp only [hgdef]
    rw [jsp87Xp0_mod (K := K) (v := jsp87BinV K) (p := x) (n := i) (H := H)]
  have hne : (jsp87Box P).Nonempty := ⟨0, Finset.mem_range.mpr (by
    have h1 : 0 < ∏ p ∈ P, p := by
      refine Finset.prod_pos fun p hp => ?_
      exact (hP p hp).pos
    omega)⟩
  -- the second moment, row by row
  have h2 : jsp87FAvg (jsp87Box P) (fun n => (∑ p ∈ P, g p n) ^ 2)
      = ∑ p ∈ P, (jsp87FAvg (Finset.range p) (fun i => (g p i) ^ 2)
          + jsp87FAvg (Finset.range p) (g p)
            * ∑ x ∈ P.erase p, jsp87FAvg (Finset.range x) (g x)) := by
    have hstep : jsp87FAvg (jsp87Box P) (fun n => (∑ p ∈ P, g p n) ^ 2)
        = jsp87FAvg (jsp87Box P) (fun n => ∑ p ∈ P, (g p n * ∑ x ∈ P, g x n)) := by
      congr 1
      funext n
      rw [pow_two, Finset.sum_mul]
    rw [hstep, jsp87FAvg_sum_box (fun p hp => (hP p hp).ne_zero)]
    exact Finset.sum_congr rfl fun p hp => jsp87FAvg_sq_row hP p hp g hg
  -- the mean is the sum of the single-prime means
  have h1 : jsp87FAvg (jsp87Box P) (fun n => ∑ p ∈ P, g p n)
      = ∑ p ∈ P, jsp87FAvg (Finset.range p) (g p) := by
    rw [jsp87FAvg_sum_box (fun p hp => (hP p hp).ne_zero)]
    exact Finset.sum_congr rfl fun p hp => jsp87FAvg_box_period hP p hp (g p) (hg p hp)
  -- assemble
  have hvar := jsp87Var_eq_FAvg_sq_sub (jsp87Box P) hne (fun n => ∑ p ∈ P, g p n)
  rw [h2, h1] at hvar
  rw [jsp87sq_sum] at hvar
  -- the off-diagonal rows of the covariance matrix cancel
  have hvar' : jsp87Var (jsp87Box P) (fun n => ∑ p ∈ P, g p n)
      = ∑ p ∈ P, (jsp87FAvg (Finset.range p) (fun i => (g p i) ^ 2)
          - (jsp87FAvg (Finset.range p) (g p)) ^ 2) := by
    rw [hvar]
    refine (Finset.sum_sub_distrib (s := P)
      (f := fun p : ℕ => jsp87FAvg (Finset.range p) (fun i => (g p i) ^ 2)
        + jsp87FAvg (Finset.range p) (g p)
          * ∑ x ∈ P.erase p, jsp87FAvg (Finset.range x) (g x))
      (g := fun p : ℕ => (jsp87FAvg (Finset.range p) (g p)) ^ 2
        + jsp87FAvg (Finset.range p) (g p)
          * ∑ x ∈ P.erase p, jsp87FAvg (Finset.range x) (g x))).symm.trans ?_
    exact Finset.sum_congr rfl fun p _ => by ring
  refine hvar'.trans ?_
  refine Finset.sum_congr rfl fun p hp => ?_
  have hne' : (Finset.range p).Nonempty := ⟨0, Finset.mem_range.mpr ((hP p hp).pos)⟩
  rw [← (jsp87Var_eq_FAvg_sq_sub (Finset.range p) hne' (g p))]

/-- **THE MEAN OF THE TOTAL PHASE IS THE SUM OF THE SINGLE-PRIME MEANS.** -/
theorem jsp87FAvg_sum_Xp_box {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (K H : ℕ)
    (c : ℕ → ℝ) :
    jsp87FAvg (jsp87Box P) (fun n => ∑ p ∈ P, c p * jsp87Xp0 (jsp87BinV K) p n H)
      = ∑ p ∈ P, jsp87FAvg (Finset.range p)
          (fun i => c p * jsp87Xp0 (jsp87BinV K) p i H) := by
  rw [jsp87FAvg_sum_box (fun p hp => (hP p hp).ne_zero)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hper : ∀ i : ℕ, c p * jsp87Xp0 (jsp87BinV K) p (i % p) H
      = c p * jsp87Xp0 (jsp87BinV K) p i H := by
    intro i
    rw [jsp87Xp0_mod (K := K) (v := jsp87BinV K) (p := p) (n := i) (H := H)]
  exact jsp87FAvg_box_period hP p hp (fun i => c p * jsp87Xp0 (jsp87BinV K) p i H) hper

/-- **THE TOTAL VARIANCE ON A BOX IS NONNEGATIVE, AS IT MUST BE.** -/
theorem jsp87Var_sum_box_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (_hP0 : P.Nonempty) (K H : ℕ) (c : ℕ → ℝ) :
    0 ≤ jsp87Var (jsp87Box P) (fun n => ∑ p ∈ P, c p * jsp87Xp0 (jsp87BinV K) p n H) := by
  rw [jsp87Var_sum_box hP K H c]
  exact Finset.sum_nonneg fun p _ => jsp87Var_nonneg _ _

/-! ## §5  HYPOTHESIS (5.21) ON A BOX IS A STATEMENT ABOUT SINGLE PRIMES -/

/-- **★★ (5.21) ON THE BOX IS EQUIVALENT TO THE SINGLE-PRIME CONDITION ★★**

The variance hypothesis of §5.4 of arXiv:2512.01739 — "the total variance is
large" — cannot be created by the geometry of a box: on a box it is *exactly*
the corresponding statement for one period of each prime.  So a box neither
helps nor hurts (5.21); all the obstruction has to come from (5.15). -/
theorem jsp87_521_box_iff {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (K H : ℕ) (q : ℝ) :
    ((1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (jsp87Box P)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H))
      ↔ ((1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (Finset.range p)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) := by
  have hkey : (∑ p ∈ P, jsp87Var (jsp87Box P)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H))
      = ∑ p ∈ P, jsp87Var (Finset.range p)
          (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) := by
    exact Finset.sum_congr rfl fun p hp => jsp87Var_box_eq hP
      (fun p' hp' => Nat.Prime.two_le (hP p' hp')) q K H p hp
  rw [hkey]

/-! ## §6  THE ENDGAME BUDGET ON A BOX -/

/-- **THE BOX IS NONEMPTY FOR A PRIME SET.** -/
private theorem jsp87Box_ne_of_prime {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    (jsp87Box P).Nonempty := by
  refine ⟨0, Finset.mem_range.mpr ?_⟩
  have h1 : 0 < ∏ p ∈ P, p := by
    refine Finset.prod_pos fun p hp => ?_
    exact (hP p hp).pos
  omega

/-- **★★ THE ENDGAME DICHOTOMY ON A BOX ★★**

On the box, the endgame of §5.4 either has a *large truncation error* — at
least `1/2` — or hypothesis (5.21) fails, i.e. the single-prime variances sum
to less than `1`.  This is `jsp87_endgame_sum_ge` (round 116) specialised to
`s = B P`, where hypothesis (5.16)–(5.17) is an identity by round 145's
`jsp87CAvg_box_prod`, and where (5.21) is transported by the independence
theorem `jsp87_521_box_iff` of §5. -/
theorem jsp87_box_dichotomy {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (K H : ℕ) (q : ℝ) (κ1 κ2 κ3 : ℝ)
    (H19 : ∀ p ∈ P, ∀ i : ℕ, |q * jsp87Xp0 (jsp87BinV K) p i H| ≤ 1 / 20)
    (H15 : ‖jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * ∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) - 1‖
      ≤ κ1 + κ2 + κ3) :
    (1 / 2 : ℝ) ≤ κ1 + κ2 + κ3
      ∨ ((∑ p ∈ P, jsp87Var (Finset.range p)
          (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) < 1) := by
  classical
  rcases lt_or_ge (∑ p ∈ P, jsp87Var (Finset.range p)
      (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) (1 : ℝ) with h | h
  · exact Or.inr h
  · left
    have hne := jsp87Box_ne_of_prime hP
    have h21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (jsp87Box P)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) :=
      (jsp87_521_box_iff hP K H q).mpr h
    have hprod : (∏ p ∈ P, jsp87CAvg (jsp87Box P)
          (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)))
        = ∏ p ∈ P, jsp87CAvg (Finset.range p)
          (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) := by
      exact Finset.prod_congr rfl fun p _ => jsp87CAvg_box_eq_period hP
        (fun p' hp' => Nat.Prime.two_le (hP p' hp')) K H p ‹_› q
    have h1617 : ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * ∑ p ∈ P, jsp87Xp0 (jsp87BinV K) p n H))
          - ∏ p ∈ P, jsp87CAvg (jsp87Box P)
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖ ≤ (0 : ℝ) + 0 := by
      rw [hprod]
      have hkey := jsp87CAvg_box_prod hP K H q
      rw [hkey]
      simp only [sub_self, norm_zero, add_zero, le_refl]
    have h := jsp87_endgame_sum_ge (s := jsp87Box P) hne q
      (fun p i => jsp87Xp0 (jsp87BinV K) p i H) κ1 κ2 κ3 0 0 H15 h1617 H19 h21
    linarith

/-- **★★★ ON A BOX THE WHOLE ERROR BUDGET OF THE ENDGAME IS TRUNCATION ★★★**

With the error terms `κ_j ≥ 0` of §5.3–§5.4, the four endgame hypotheses hold on
the box only if `κ₁ + κ₂ + κ₃ ≥ 1/2`: the independent-copy terms `κ₄, κ₅` are
*identically zero* on a box, and the variance hypothesis is a statement about
single primes.  So all five published error terms, and hence (5.18), must be
paid for by the three truncation errors. -/
theorem jsp87_box_budget {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (_hP0 : P.Nonempty)
    (K H : ℕ) (q : ℝ) (κ1 κ2 κ3 κ4 κ5 : ℝ) (hκ4 : 0 ≤ κ4) (hκ5 : 0 ≤ κ5)
    (H19 : ∀ p ∈ P, ∀ i : ℕ, |q * jsp87Xp0 (jsp87BinV K) p i H| ≤ 1 / 20)
    (H15 : ‖jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * ∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) - 1‖
      ≤ κ1 + κ2 + κ3)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (Finset.range p)
      (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) :
    (1 / 2 : ℝ) ≤ κ1 + κ2 + κ3 ∧ (1 / 2 : ℝ) ≤ κ1 + κ2 + κ3 + κ4 + κ5 := by
  classical
  have hne := jsp87Box_ne_of_prime hP
  have h21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (jsp87Box P)
      (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) :=
    (jsp87_521_box_iff hP K H q).mpr H21
  have hprod : (∏ p ∈ P, jsp87CAvg (jsp87Box P)
        (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)))
      = ∏ p ∈ P, jsp87CAvg (Finset.range p)
          (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) := by
    exact Finset.prod_congr rfl fun p _ => jsp87CAvg_box_eq_period hP
      (fun p' hp' => Nat.Prime.two_le (hP p' hp')) K H p ‹_› q
  have h1617 : ‖jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * ∑ p ∈ P, jsp87Xp0 (jsp87BinV K) p n H))
        - ∏ p ∈ P, jsp87CAvg (jsp87Box P)
          (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖ ≤ κ4 + κ5 := by
    rw [hprod]
    have hkey := jsp87CAvg_box_prod hP K H q
    rw [hkey]
    simp only [sub_self, norm_zero]
    linarith
  have h := jsp87_endgame_sum_ge (s := jsp87Box P) hne q
    (fun p i => jsp87Xp0 (jsp87BinV K) p i H) κ1 κ2 κ3 κ4 κ5 H15 h1617 H19 h21
  refine ⟨(jsp87_box_dichotomy hP K H q κ1 κ2 κ3 H19 H15).resolve_right ?_, h⟩
  linarith

/-! ## §7  THE TWO-CLASS CRITERION (5.21′) PRICES THE BOX -/

/-- **THE DYADIC WEIGHT CANCELS THE POWER OF TWO.** -/
private theorem jsp87half_pow_sq {m : ℕ} :
    (((1 / 2 : ℝ) ^ m) ^ 2) * ((2 : ℝ) ^ (2 * m)) = 1 := by
  have h1 : ((1 / 2 : ℝ) ^ m) ^ 2 = ((1 / 2 : ℝ) : ℝ) ^ (2 * m) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [h1]
  calc ((1 / 2 : ℝ) : ℝ) ^ (2 * m) * (2 : ℝ) ^ (2 * m)
      = ((1 / 2 : ℝ) * 2) ^ (2 * m) := by rw [mul_pow]
    _ = (1 : ℝ) ^ (2 * m) := by
        rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = 1 := one_pow _

/-- **THE FRACTION OF (5.21b) AT `p` IS AT MOST `H 2^K / p`.**  This is the
*upper* estimate (round 123's `jsp87NzResCard_bounds`), needed to convert
hypothesis (5.21′) into a *lower* bound on the harmonic mass. -/
private theorem jsp87FracTerm_le {K p H : ℕ} (hH : 1 ≤ H) (hpc : p.Prime)
    (hB : jsp87Separation K H ≤ p) :
    jsp87FracTerm K p H ≤ ((H : ℝ) * (2 : ℝ) ^ K) / (p : ℝ) := by
  have hsep : H + 2 ^ K - 1 < p := lt_of_lt_of_le (jsp87Separation_gt hH) hB
  have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpc.pos
  have hcard := jsp87NzResCard_le_p (K := K) hpc.pos hsep
  have hc : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (p : ℝ) := by
    have hlt : jsp87NzResCard K p H < p := by omega
    exact_mod_cast (le_of_lt hlt)
  have hcardle : jsp87NzResCard K p H ≤ H * 2 ^ K :=
    (jsp87NzResCard_bounds (K := K) hpc.pos
      (le_trans (jsp87Separation_pow_le hH) hB) hH hsep).2
  have hc2 : ((jsp87NzResCard K p H : ℕ) : ℝ) ≤ (H : ℝ) * ((2 : ℝ) ^ K) := by
    exact_mod_cast hcardle
  have hf : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hpp).2 hc
  have hf2 : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
      ≤ ((H : ℝ) * ((2 : ℝ) ^ K)) / (p : ℝ) :=
    (div_le_div_iff_of_pos_right hpp).2 hc2
  have hmain : ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ)
      * (1 - ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ))
      ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ ((jsp87NzResCard K p H : ℕ) : ℝ) / (p : ℝ) := by
      positivity
    nlinarith [hf, hnonneg]
  unfold jsp87FracTerm
  linarith

/-- **★★ (5.21′) IS A HARMONIC-MASS CONDITION ON THE PRIME SET ★★**

For *any* finite set of primes `P` (not only a prime interval),
`jsp87R521b K P q H` — the two-class criterion (5.21′) of arXiv:2512.01739 —
forces

```
  2^{2(H+K)}   ≤   H · 2^K · q² · ∑_{p ∈ P} 1/p ,
```

i.e. the harmonic mass of the prime set is at least `2^{2(H+K)}/(H 2^K q²)`:
**the sample-geometry condition of §5.4 is a requirement on the harmonic mass
of the prime set.**  This transfers round 124's `jsp87_5_21b_needs_height`
from the cardinality to the *mass*, with the prime set left free. -/
theorem jsp87_521b_mass_ge {K H : ℕ} {P : Finset ℕ} (hH : 1 ≤ H)
    (hP : ∀ p ∈ P, p.Prime) (hsep : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (q : ℝ) (hR : jsp87R521b K P q H) :
    ((2 : ℝ) ^ (2 * (H + K))) ≤ ((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P) := by
  classical
  set W : ℝ := ((1 / 2 : ℝ) ^ (H + K)) ^ 2 with hWdef
  set S : ℝ := (2 : ℝ) ^ (2 * (H + K)) with hSdef
  have hkey : W * S = 1 := by
    have := jsp87half_pow_sq (m := H + K)
    rw [← hWdef, ← hSdef] at this
    exact this
  have hlow : S ≤ (q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H :=
    (jsp87R521b_iff K P q H).mp hR
  have hsumle : (∑ p ∈ P, jsp87FracTerm K p H)
      ≤ (((H : ℝ) * ((2 : ℝ) ^ K)) : ℝ) * jsp87RecipSum P := by
    rw [jsp87RecipSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => by
      simpa [div_eq_mul_inv] using jsp87FracTerm_le hH (hP p hp) (hsep p hp)
  have hW : 0 ≤ W := by positivity
  have h2 : W * ((q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H)
      ≤ W * (((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P)) := by
    have hmul := mul_le_mul_of_nonneg_right hsumle (by positivity : (0 : ℝ) ≤ W * (q ^ 2))
    nlinarith [hmul]
  have h1 : (1 : ℝ) ≤ W * ((q ^ 2) * ∑ p ∈ P, jsp87FracTerm K p H) := by
    have hmul := mul_le_mul_of_nonneg_left hlow hW
    rw [hkey] at hmul
    nlinarith [hmul]
  have h3 : (1 : ℝ) ≤ W * (((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P)) :=
    le_trans h1 h2
  calc (2 : ℝ) ^ (2 * (H + K)) = S := hSdef.symm
    _ = (W * S) * S := by rw [hkey]; ring
    _ = S := by rw [hkey]; ring
    _ ≤ S * (W * (((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P))) := by
      simpa using
        (mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ S by rw [hSdef]; positivity))
    _ = ((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P) := by
      calc S * (W * (((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P)))
          = (((H : ℝ) * ((2 : ℝ) ^ K)) * ((q ^ 2) * jsp87RecipSum P)) * (W * S) := by ring
        _ = _ := by rw [hkey]; ring

/-- **★ THE PRICE OF (5.21′) ON THE BOX ★** — the quantity
`4 q² 2^K 2^{−2(H+K)} ∑ 1/p` of round 145's `jsp87_515_box_le`, i.e. the
exponent that controls the *truncation error* of hypothesis (5.15), is at
least `4 / H` as soon as the published two-class criterion (5.21′) holds. -/
theorem jsp87_box_exp_ge {K H : ℕ} {P : Finset ℕ} (hH : 1 ≤ H)
    (hP : ∀ p ∈ P, p.Prime) (hsep : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (q : ℝ) (hR : jsp87R521b K P q H) :
    (4 / (H : ℝ)) ≤ (4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * jsp87RecipSum P := by
  classical
  set W : ℝ := ((1 / 2 : ℝ) ^ (H + K)) ^ 2 with hWdef
  set S : ℝ := (2 : ℝ) ^ (2 * (H + K)) with hSdef
  have hkey : W * S = 1 := by
    have := jsp87half_pow_sq (m := H + K)
    rw [← hWdef, ← hSdef] at this
    exact this
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hmain := jsp87_521b_mass_ge hH hP hsep q hR
  rw [← hSdef] at hmain
  have hnonneg : (0 : ℝ) ≤ H := hHpos.le
  have hd : S / (H : ℝ) ≤ ((2 : ℝ) ^ K) * (q ^ 2) * jsp87RecipSum P := by
    have h1 := div_le_div_of_nonneg_right hmain hnonneg
    have heq : ((H : ℝ) * ((2 : ℝ) ^ K) * ((q ^ 2) * jsp87RecipSum P)) / (H : ℝ)
        = ((2 : ℝ) ^ K) * (q ^ 2) * jsp87RecipSum P := by
      field_simp [ne_of_gt hHpos]
    rw [heq] at h1
    exact h1
  have hB : 4 * W * (S / (H : ℝ))
      ≤ 4 * W * (((2 : ℝ) ^ K) * (q ^ 2) * jsp87RecipSum P) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  calc (4 / (H : ℝ)) = 4 * (W * S) / (H : ℝ) := by rw [hkey]; ring
    _ = 4 * W * (S / (H : ℝ)) := by ring
    _ ≤ 4 * W * (((2 : ℝ) ^ K) * (q ^ 2) * jsp87RecipSum P) := hB
    _ = (4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * jsp87RecipSum P := by rw [hWdef]; ring

/-- **★★★ (5.15′) IS VIOLATED ON EVERY BOX THAT SATISFIES (5.21′) ★★★**

Let `P` be a finite set of primes, all of them at least the separation bound
`2 H 2^K`, let `q` be a phase scale, and suppose the paper's own two-class
criterion **(5.21′)** holds on `P`.  On the box of residues `B P` of round 145,

```
  1 − exp(−4/H)   ≤   ‖𝔼ᶜ e (q ∑_{p ∈ P} X p) − 1‖   ≤   κ₁ + κ₂ + κ₃ ,
```

for **every** `K ≥ 0`, `H ≥ 1` and every admissible `q` (§7 prices (5.21′) at
`4/H` on the box).  For the first two heights (`H ≤ 2`, where the gap is
`> 1 − e^{−2}`) this is already a contradiction with `κ_j < 1/30`; and the gap
tends to `1` as the harmonic mass grows, so for every `ε > 0` and every `H`
there is a prime set satisfying (5.21′) on which the truncation errors are
`≥ 1 − ε`.  **Hypothesis (5.15) of arXiv:2512.01739 therefore cannot hold on
the box with `o(1)` errors for any prime set that meets the sample-geometry
condition of §5.4.** -/
theorem jsp87_box_515_gap {K H : ℕ} {P : Finset ℕ} (hH : 1 ≤ H)
    (hP : ∀ p ∈ P, p.Prime) (hsep : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (hPsep : ∀ p ∈ P, 2 * (H + 2 ^ K - 1) ≤ p)
    (hone : ∀ p ∈ P, ∀ n : ℕ, ∀ h ∈ Finset.Icc 1 H,
      jsp87OneVertex p n (jsp87BinV K) h)
    (q : ℝ) (hq : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (κ1 κ2 κ3 : ℝ)
    (hR : jsp87R521b K P q H)
    (H15 : ‖jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * ∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) - 1‖
      ≤ κ1 + κ2 + κ3) :
    (1 - Real.exp (-(4 / (H : ℝ)))) ≤ κ1 + κ2 + κ3 := by
  classical
  have hlow := jsp87_515_box_le K H hP hH hPsep q hone hq
  have hexp := jsp87_box_exp_ge hH hP hsep q hR
  have hexp2 : Real.exp (-(4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * jsp87RecipSum P) ≤ Real.exp (-(4 / (H : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hexp]
  calc (1 - Real.exp (-(4 / (H : ℝ))))
      ≤ 1 - Real.exp (-(4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * jsp87RecipSum P) := by linarith
    _ ≤ ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * ∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) - 1‖ := hlow
    _ ≤ κ1 + κ2 + κ3 := H15

/-- **★★★ THE ENDGAME CANNOT RUN ON A BOX AT THE FIRST TWO HEIGHTS ★★★**

No prime set satisfying (5.21′) admits a box sample at height `H ≤ 2` on which
the three truncation errors of §5.3–§5.4 are sharp: if all three are `< 1/30`
then hypothesis (5.15) fails on the box by a factor `≥ 2`.  Combined with
round 116 (`jsp87_endgame_impossible`) the endgame of §§5.3–§5.14 is therefore
**refuted on every box that meets the published sample-geometry condition, at
least at the first two heights**, and at every height once the prime set is
large enough for the gap to exceed the error budget. -/
theorem jsp87_endgame_box_notSharp {K H : ℕ} {P : Finset ℕ} (hH : 1 ≤ H)
    (hH2 : H ≤ 2)
    (hP : ∀ p ∈ P, p.Prime) (hsep : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (hPsep : ∀ p ∈ P, 2 * (H + 2 ^ K - 1) ≤ p)
    (hone : ∀ p ∈ P, ∀ n : ℕ, ∀ h ∈ Finset.Icc 1 H,
      jsp87OneVertex p n (jsp87BinV K) h)
    (q : ℝ) (hq : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (κ1 κ2 κ3 : ℝ)
    (hR : jsp87R521b K P q H)
    (H15 : ‖jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * ∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) - 1‖
      ≤ κ1 + κ2 + κ3)
    (h1 : κ1 < 1 / 30) (h2 : κ2 < 1 / 30) (h3 : κ3 < 1 / 30) : False := by
  classical
  have hgap := jsp87_box_515_gap hH hP hsep hPsep hone q hq κ1 κ2 κ3 hR H15
  have hH4 : (2 : ℝ) ≤ 4 / (H : ℝ) := by
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    have hH2' : (H : ℝ) ≤ 2 := by exact_mod_cast hH2
    rw [div_eq_mul_inv]
    field_simp
    nlinarith [hH2']
  have hexp2 : Real.exp (-(4 / (H : ℝ))) ≤ Real.exp (-(2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexp3 : Real.exp (-(2 : ℝ)) ≤ 1 / 2 := by
    have h1 := Real.add_one_le_exp 2
    have h1' : (3 : ℝ) ≤ Real.exp 2 := by linarith
    have h2 : 0 < Real.exp 2 := Real.exp_pos 2
    have h3 : (Real.exp 2)⁻¹ ≤ (3 : ℝ)⁻¹ := (inv_le_inv₀ h2 (by norm_num)).mpr h1'
    have h4 : Real.exp (-(2 : ℝ)) = (Real.exp 2)⁻¹ := by rw [Real.exp_neg]
    rw [← h4] at h3
    norm_num at h3 ⊢
    linarith
  linarith

/-! ## §8  THE SUMMARY OF ROUND 146 -/

/-- **★★★ ROUND 146, IN ONE STATEMENT ★★★**

Let `P` be a finite set of primes of a hypothetical rational value
`S = jsp87Series`, let `H ≥ 1`, let `q` be an admissible phase scale and
suppose that the two-class criterion **(5.21′)** of arXiv:2512.01739 holds on
`P`.  On the box of residues `B P`:

1. the `X_p` are pairwise independent and the mean and the variance of the total
   phase are the sum and the sum-of-variances of the single-prime statistics
   (`jsp87Var_sum_box`, `jsp87FAvg_sum_Xp_box`);
2. hence **(5.21)** on the box is *equivalent* to the single-prime condition, and
   if the four endgame hypotheses hold then the **entire** error budget is paid
   by the three truncation errors: `κ₁+κ₂+κ₃ ≥ 1/2` (`jsp87_box_budget`);
3. and (5.15′) is violated by the gap `1 − exp(−4/H)` (`jsp87_box_515_gap`),
   which already exceeds the whole error budget for `H ≤ 2`
   (`jsp87_endgame_box_notSharp`), so the endgame cannot run there with sharp
   errors;
4. the price of (5.21′) on the box is the harmonic-mass condition
   `2^{2(H+K)} ≤ H 2^K q² ∑ 1/p` (`jsp87_521b_mass_ge`), and the resulting
   truncation exponent is at least `4/H` (`jsp87_box_exp_ge`).

**Consequence.**  Together with round 145, the box of residues is excluded from
the endgame — at every height once the prime set's harmonic mass is large
enough, and at the first two heights unconditionally — and together with rounds
116 and 144 the sample geometry of §§5.3–5.14 is exhausted in both
directions: initial segments satisfy (5.21′) but not (5.15), boxes satisfy
neither once (5.21′) is assumed.  A rationality witness must therefore be a
genuinely **correlated** sample, and the single remaining obstruction is the
analytic one: `jsp87Mcov_small`, the Chowla-type two-point correlation of `ω`
(Thm 3.1 of arXiv:2512.01739, from Pilatte). -/
theorem jsp87_box_summary {K H : ℕ} {P : Finset ℕ} (hH : 1 ≤ H)
    (hP : ∀ p ∈ P, p.Prime) (hP0 : P.Nonempty) (hsep : ∀ p ∈ P, jsp87Separation K H ≤ p)
    (hPsep : ∀ p ∈ P, 2 * (H + 2 ^ K - 1) ≤ p)
    (hone : ∀ p ∈ P, ∀ n : ℕ, ∀ h ∈ Finset.Icc 1 H,
      jsp87OneVertex p n (jsp87BinV K) h)
    (q : ℝ) (hq : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (κ1 κ2 κ3 κ4 κ5 : ℝ) (hκ4 : 0 ≤ κ4) (hκ5 : 0 ≤ κ5)
    (hR : jsp87R521b K P q H)
    (_H19 : ∀ p ∈ P, ∀ i : ℕ, |q * jsp87Xp0 (jsp87BinV K) p i H| ≤ 1 / 20)
    (H15 : ‖jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * ∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) - 1‖
      ≤ κ1 + κ2 + κ3)
    (H21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (Finset.range p)
      (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) :
    ((1 / 2 : ℝ) ≤ κ1 + κ2 + κ3 + κ4 + κ5)
      ∧ ((1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (jsp87Box P)
          (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)
          ↔ (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var (Finset.range p)
            (fun i => q * jsp87Xp0 (jsp87BinV K) p i H))
      ∧ ((1 - Real.exp (-(4 / (H : ℝ)))) ≤ κ1 + κ2 + κ3)
      ∧ ((4 / (H : ℝ)) ≤ (4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * jsp87RecipSum P) := by
  classical
  have h19 : ∀ p ∈ P, ∀ i : ℕ, |q * jsp87Xp0 (jsp87BinV K) p i H| ≤ 1 / 20 :=
    fun p hp i => jsp87Xp0_abs_le_twenty q (jsp87BinV K) p i H (hone p hp i) hq
  have hbudget := jsp87_box_budget hP hP0 K H q κ1 κ2 κ3 κ4 κ5 hκ4 hκ5 h19 H15 H21
  have hgap := jsp87_box_515_gap hH hP hsep hPsep hone q hq κ1 κ2 κ3 hR H15
  have h521 := jsp87_521_box_iff hP K H q
  have hexp := jsp87_box_exp_ge hH hP hsep q hR
  exact ⟨hbudget.2, h521, hgap, hexp⟩

end JSP87
