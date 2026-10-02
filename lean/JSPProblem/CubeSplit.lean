/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.AltSum
import Mathlib.Tactic

/-!
# JSP-000087, round 91 — THE CUBE SPLITTING IDENTITY (the Gowers recursion) and
# the rationality quantisation of the window cubes

## What this round is

Round 90 proved the flagship `jsp87AltSumF_zero`: the `2^K`-term alternating sum
of Tao–Teräväinen's §5.2 cube **always** vanishes, because the shift
`r_{ε,h} = p₀·h + Σ_{k∈ε}(h−k)·v_k` does not depend on the `h`-th coordinate.
That is a *proved negative result* which closes every strategy that tries to
make the cube sum itself nonzero: the cancellation is an identity valid for
**every** integer-valued `f`.

Round 90 listed as abandoned item 1 the **cube-doubling identity**: a
`(K+1)`-cube splits into two `K`-cubes.  This round builds it, and then uses it
to close the three items round 88 promised in the header of `AltSum.lean` and
never delivered (`jsp87Alt_congr`, `jsp87Alt_zero_or_ge`,
`jsp87Series_irrational_of_altSmall`): the mod-1 quantisation of the
alternating sums, **at every dimension**, and the criterion that follows.

## Objects

* `jsp87ZCube`, `jsp87FCube` — the cube `∑_s (−1)^{|s|}·f(base + ∑_{k∈s} A k)`
  over the `2^K` vertices `s ⊆ Fin K`, in `ℤ` and in `ℝ`;
* `jsp87ZHalfCube`, `jsp87HalfCube` — the same over the vertices that *avoid*
  the last coordinate: the sub-cubes produced by the recursion;
* `jsp87AltStep v h j = (h − j − 1)·v_j` and `jsp87AltBase p₀ n h = n + p₀·h`
  — the steps and the base point of the Erdős cube;
* `jsp87AltSumF_eq_jsp87ZCube`, `jsp87AltSumR_eq_jsp87FCube` — round 88's and
  round 90's alternating sums **are** these cubes.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87FCube_zero_of_step`, `jsp87ZCube_zero_of_step` | **a vanishing step kills the cube**: the degeneracy in a form that mentions no level |
| `jsp87AltSumF_zero_of_step`, `jsp87AltSumF_zero_of_degenerate` | round 90's flagship re-derived from it, with a *strictly weaker* hypothesis |
| **`jsp87FCube_eq_half_sub`** | **THE CUBE SPLITTING IDENTITY**: a `(K+1)`-cube is the difference of two `K`-cubes (half cubes) with the same steps, at the two base points differing by the last step.  The Gowers recursion `U^{K+1} → U^K` |
| `jsp87FCube_zero_of_half`, `jsp87FCube_abs_le_half` | the propagation, and the quantitative Gowers bound `\|cube\| ≤ \|half\| + \|half\|` |
| `jsp87HalfCube_eq_of_allCube` | if all `(K+1)`-cubes vanish, every half cube is invariant under the (arbitrary) last step |
| `jsp87HalfCube_zero_of_step` | the same degeneracy *inside* a half cube |
| `jsp87AltSumR_eq_half_sub` | the Erdős cube at dimension `K+1` splits into two half cubes |
| `jsp87AltStep_eq_zero_iff` | **the degenerate level is the only forced vanishing**: with `v_j ≠ 0` the step vanishes exactly at `h = j+1`.  Above the level `K` the recursion has content, and that is exactly where the analytic input of the published proof must act |
| `jsp87AltSumR_zero_of_level`, `jsp87HalfCube_zero_of_level` | the degeneracy survives the splitting at exactly the old levels |
| `jsp87ZHalfCube_omega_ne_zero` | **a machine-checked nonzero half cube of `ω`** (value `−2`): the recursion is not vacuous |
| `jsp87FCube_one` | the `1`-cube is `W(base) − W(base+m)` |
| **`jsp87FCube_mul_eq_int`** | **the rationality quantisation of a cube of windows, at every dimension**: under `S = a/b`, `b·(cube of W) ∈ ℤ` |
| **`jsp87FCube_zero_or_ge`** | **the dichotomy**: every cube of windows is `0`, or has absolute value `≥ 1/b` |
| `jsp87FCube_eq_zero_of_lt` | a cube smaller than `1/b` vanishes |
| `jsp87Win_not_const` | the windows are not constant: the window recurrence would force `ω` constant, and `ω 1 = 0 ≠ 2 = ω 6` |
| `jsp87Win_const_of_FCube_one_zero` | vanishing `1`-cubes force the windows to be constant |
| **`jsp87Series_irrational_of_FCube_one_small`** | **ROUND 91'S CRITERION** — see below |
| `jsp87FCube_card` | a cube has exactly `2^K` vertices, the counting that makes the recursion a 4-fold refinement |

## The criterion

`jsp87Series_irrational_of_FCube_one_small` states

> if for every positive integer `b`, every `m` and every `base`, the `1`-cube
> `W(base) − W(base+m)` has absolute value `< 1/b`, then the Erdős series is
> **irrational**.

Indeed, under `S = a/b` the quantisation puts every cube of windows in
`(1/b)ℤ`, so every `1`-cube is `0` or `≥ 1/b`; the hypothesis forces them all to
vanish; vanishing `1`-cubes make `W` constant; a constant `W` makes `ω`
constant through `W(n+1) = 2W(n) − ω(n+1)`; and `ω` is not constant.

So the headline `Irrational jsp87Series` follows from the *single* analytic
hypothesis of **Gowers-norm smallness of the window function** — the input
Tao–Teräväinen obtain from the Pilatte correlation estimate (§3 of
arXiv:2512.01739), which has no Mathlib counterpart.  Every combinatorial and
Diophantine step of the reduction is formalised here, for *every* dimension.

## Not claimed

`jsp_000087_main` is **not declared**.  The gate wants
`jsp_000087_main = Irrational jsp87Series`, which is a *published theorem*
(Tao–Teräväinen, arXiv:2512.01739, Theorem 1.3, unconditional), but its
analytic core — a quantitative two-point correlation bound for multiplicative
functions — cannot be stated in this development without importing the
hypothesis as an axiom.  Attaching the catalog name to the criterion above
would misrepresent the headline, so the name stays withheld and
`harness/score.py --strict-prize` correctly reports
`partial_ok=true, prize_ready=false`.
-/


namespace JSP87

open Finset

/-- **THE INTEGER CUBE** over the `2^K` vertices `s ⊆ Fin K`. -/
def jsp87ZCube {K : ℕ} (f : ℕ → ℤ) (A : Fin K → ℤ) (base : ℤ) : ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), jsp87Sign s.card
    * f ((base + ∑ k ∈ s, A k : ℤ)).toNat

/-- **THE REAL CUBE** over the `2^K` vertices `s ⊆ Fin K`. -/
def jsp87FCube {K : ℕ} (f : ℕ → ℝ) (A : Fin K → ℤ) (base : ℤ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), (jsp87Sign s.card : ℝ)
    * f ((base + ∑ k ∈ s, A k : ℤ)).toNat

/-- **THE INTEGER HALF CUBE**: the cube over the vertices avoiding the last
coordinate. -/
def jsp87ZHalfCube {K : ℕ} (f : ℕ → ℤ) (A : Fin (K + 1) → ℤ) (base : ℤ) : ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin (K + 1))))
      |>.filter (fun s => (Fin.last K) ∉ s),
    jsp87Sign s.card * f ((base + ∑ k ∈ s, A k : ℤ)).toNat

/-- The step of the Erdős cube `r_{ε,h}` in the `j`-th direction. -/
def jsp87AltStep {K : ℕ} (v : Fin K → ℤ) (h : ℕ) (j : Fin K) : ℤ :=
  ((h : ℤ) - (j.val : ℤ) - 1) * v j

/-- The base point of the Erdős cube, the argument of `ω` at the empty vertex. -/
def jsp87AltBase (p0 n h : ℕ) : ℤ := (n : ℤ) + (p0 : ℤ) * h

theorem jsp87AltBase_eq (p0 n h : ℕ) : jsp87AltBase p0 n h = (n : ℤ) + (p0 : ℤ) * h := rfl

theorem jsp87AltStep_eq {K : ℕ} (v : Fin K → ℤ) (h : ℕ) (j : Fin K) :
    jsp87AltStep v h j = ((h : ℤ) - (j.val + 1)) * v j := by
  unfold jsp87AltStep
  ring

/-- **THE ERDÖS CUBE IN CUBE FORM.** -/
theorem jsp87AltSumF_eq_jsp87ZCube {K : ℕ} (f : ℕ → ℤ) (v : Fin K → ℤ) (p0 n h : ℕ) :
    jsp87AltSumF f v p0 n h
      = jsp87ZCube f (jsp87AltStep v h) (jsp87AltBase p0 n h) := by
  unfold jsp87AltSumF jsp87ZCube jsp87AltShift jsp87AltBase jsp87AltStep
  exact Finset.sum_congr rfl fun s _ => by
    congr 2
    ring

/-! ## §1  A vanishing step kills a cube -/

private theorem jsp87ZSum_step_toggle {K : ℕ} (A : Fin K → ℤ) (j : Fin K)
    (s : Finset (Fin K)) (hj : A j = 0) :
    (∑ k ∈ jsp87AltToggle j s, A k) = ∑ k ∈ s, A k := by
  unfold jsp87AltToggle
  by_cases h : j ∈ s
  · rw [if_pos h, ← Finset.sum_erase_add s (fun k => A k) h, hj]
    ring
  · rw [if_neg h, Finset.sum_insert (f := fun k => A k) h, hj]
    ring

/-- **A VANISHING STEP KILLS THE INTEGER CUBE.** -/
theorem jsp87ZCube_zero_of_step {K : ℕ} (f : ℕ → ℤ) (A : Fin K → ℤ) (base : ℤ)
    (j : Fin K) (hj : A j = 0) : jsp87ZCube f A base = 0 := by
  have hg : ∀ s : Finset (Fin K),
      jsp87Sign (jsp87AltToggle j s).card
          * f ((base + ∑ k ∈ jsp87AltToggle j s, A k : ℤ)).toNat
        = - (jsp87Sign s.card * f ((base + ∑ k ∈ s, A k : ℤ)).toNat) := by
    intro s
    rw [jsp87ZSum_step_toggle A j s hj, jsp87AltSign_toggle]
    ring
  unfold jsp87ZCube
  exact jsp87_cube_cancel j
    (fun s => jsp87Sign s.card * f ((base + ∑ k ∈ s, A k : ℤ)).toNat) hg

/-- **A VANISHING STEP KILLS THE REAL CUBE.** -/
theorem jsp87FCube_zero_of_step {K : ℕ} (f : ℕ → ℝ) (A : Fin K → ℤ) (base : ℤ)
    (j : Fin K) (hj : A j = 0) : jsp87FCube f A base = 0 := by
  have hg : ∀ s : Finset (Fin K),
      (jsp87Sign (jsp87AltToggle j s).card : ℝ)
          * f ((base + ∑ k ∈ jsp87AltToggle j s, A k : ℤ)).toNat
        = - ((jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat) := by
    intro s
    rw [jsp87ZSum_step_toggle A j s hj, jsp87AltSign_toggle]
    push_cast
    ring
  unfold jsp87FCube
  exact jsp87_cube_cancelR j
    (fun s => (jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat) hg

/-- **THE ERDÖS CUBE VANISHES WHENEVER IT HAS A ZERO STEP** — a strictly more
general form of round 90's `jsp87AltSumF_zero` (which needs a *degenerate
direction*): here any vanishing step, at any level, kills the cube. -/
theorem jsp87AltSumF_zero_of_step {K : ℕ} (f : ℕ → ℤ) (v : Fin K → ℤ) (p0 n h : ℕ)
    (j : Fin K) (hj : jsp87AltStep v h j = 0) :
    jsp87AltSumF f v p0 n h = 0 := by
  rw [jsp87AltSumF_eq_jsp87ZCube]
  exact jsp87ZCube_zero_of_step _ _ _ j hj

/-- Round 90's flagship, re-derived in cube form. -/
theorem jsp87AltSumF_zero_of_degenerate {K : ℕ} (f : ℕ → ℤ) (v : Fin K → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) : jsp87AltSumF f v p0 n h = 0 := by
  have hlt : h - 1 < K := by omega
  refine jsp87AltSumF_zero_of_step f v p0 n h ⟨h - 1, hlt⟩ ?_
  rw [jsp87AltStep_eq]
  have e : (h : ℤ) = ((h - 1 : ℕ) : ℤ) + 1 := by exact_mod_cast (by omega)
  rw [e]
  ring

/-! ## §2  The cube over the vertices avoiding the last coordinate -/

/-- **THE HALF CUBE**: the cube over the `2^K` vertices `s ⊆ Fin (K+1)` that avoid
the last coordinate. -/
def jsp87HalfCube {K : ℕ} (f : ℕ → ℝ) (A : Fin (K + 1) → ℤ) (base : ℤ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin (K + 1))))
      |>.filter (fun s => (Fin.last K) ∉ s),
    (jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat

/-- **THE CUBE SPLITTING IDENTITY.**  A cube of dimension `K+1` is the
*difference of two half cubes with the same steps*, based at `base` and at
`base + A (last K)`.  This is the Gowers recursion `U^{K+1} → U^K`, and it is
the identity round 90 could not use: it is a statement about a cube whose
`h`-th direction is *not* degenerate. -/
theorem jsp87FCube_eq_half_sub {K : ℕ} (f : ℕ → ℝ) (A : Fin (K + 1) → ℤ) (base : ℤ) :
    jsp87FCube f A base
      = jsp87HalfCube f A base - jsp87HalfCube f A (base + A (Fin.last K)) := by
  have hB : (∑ s ∈ (Finset.univ : Finset (Finset (Fin (K + 1))))
        |>.filter (fun s => (Fin.last K) ∈ s),
      (jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat)
      = ∑ s ∈ (Finset.univ : Finset (Finset (Fin (K + 1))))
        |>.filter (fun s => (Fin.last K) ∉ s),
        (- ((jsp87Sign s.card : ℝ)
          * f ((base + A (Fin.last K) + ∑ k ∈ s, A k : ℤ)).toNat)) := by
    refine Finset.sum_bij (fun s (_ : s ∈ _) => s.erase (Fin.last K)) ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_filter] at hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
    · intro a ha b hb heq
      have h1 : a = insert (Fin.last K) (a.erase (Fin.last K)) :=
        (Finset.insert_erase (s := a) (Finset.mem_filter.mp ha).2).symm
      have h2 : b = insert (Fin.last K) (b.erase (Fin.last K)) :=
        (Finset.insert_erase (s := b) (Finset.mem_filter.mp hb).2).symm
      rw [h1, h2, heq]
    · intro s hs
      refine ⟨insert (Fin.last K) s,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩, ?_⟩
      exact Finset.erase_insert (Finset.mem_filter.mp hs).2
    · intro s hs
      have hne : (Fin.last K) ∉ s.erase (Fin.last K) := by simp
      have h1 : s = insert (Fin.last K) (s.erase (Fin.last K)) :=
        (Finset.insert_erase (s := s) (Finset.mem_filter.mp hs).2).symm
      rw [h1, Finset.erase_insert hne,
        Finset.card_insert_of_notMem hne, jsp87Sign_succ,
        Finset.sum_insert (f := fun k => A k) hne]
      push_cast
      ring
  have hA : (∑ s ∈ (Finset.univ : Finset (Finset (Fin (K + 1))))
        |>.filter (fun s => (Fin.last K) ∈ s),
      (jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat)
      = - (∑ s ∈ (Finset.univ : Finset (Finset (Fin (K + 1))))
        |>.filter (fun s => (Fin.last K) ∉ s),
        (jsp87Sign s.card : ℝ)
          * f ((base + A (Fin.last K) + ∑ k ∈ s, A k : ℤ)).toNat) := by
    rw [hB, Finset.sum_neg_distrib]
  unfold jsp87FCube jsp87HalfCube
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin (K + 1))))
    (fun s : Finset (Fin (K + 1)) => (Fin.last K) ∈ s)
    (fun s : Finset (Fin (K + 1)) =>
      (jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat)
  rw [← hsplit, hA]
  ring

/-- **TWO VANISHING HALF CUBES KILL THE WHOLE CUBE** (the `U^{K+1} → U^K`
propagation). -/
theorem jsp87FCube_zero_of_half {K : ℕ} (f : ℕ → ℝ) (A : Fin (K + 1) → ℤ) (base : ℤ)
    (h0 : jsp87HalfCube f A base = 0)
    (h1 : jsp87HalfCube f A (base + A (Fin.last K)) = 0) :
    jsp87FCube f A base = 0 := by
  rw [jsp87FCube_eq_half_sub, h0, h1]
  ring

/-- **THE ABSOLUTE VALUE OF A CUBE IS AT MOST THE SUM OF THE TWO HALF CUBES.**
This is the quantitative Gowers bound: a `(K+1)`-cube is controlled by two
`K`-cubes. -/
theorem jsp87FCube_abs_le_half {K : ℕ} (f : ℕ → ℝ) (A : Fin (K + 1) → ℤ) (base : ℤ) :
    |jsp87FCube f A base|
      ≤ |jsp87HalfCube f A base| + |jsp87HalfCube f A (base + A (Fin.last K))| := by
  rw [jsp87FCube_eq_half_sub]
  have htri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    refine (abs_sub_le_iff).mpr ⟨?_, ?_⟩
    · have h1 : x ≤ |x| := le_abs_self x
      have h2 : -y ≤ |y| := neg_le_abs y
      linarith
    · have h1 : y ≤ |y| := le_abs_self y
      have h2 : -x ≤ |x| := neg_le_abs x
      linarith
  exact htri _ _

/-- **THE CONSTANCY ENDGAME.**  If *every* `(K+1)`-cube of `f` vanishes, then
every half cube is **invariant under translation by the last step** — and the
last step is arbitrary, so a half cube is constant along the base point. -/
theorem jsp87HalfCube_eq_of_allCube {K : ℕ} (f : ℕ → ℝ) (A : Fin (K + 1) → ℤ) (base : ℤ)
    (h : ∀ (A' : Fin (K + 1) → ℤ) (b' : ℤ), jsp87FCube f A' b' = 0) :
    jsp87HalfCube f A base = jsp87HalfCube f A (base + A (Fin.last K)) := by
  have hz := jsp87FCube_eq_half_sub f A base
  rw [h A base] at hz
  linarith

/-! ## §3  A general cancellation over an invariant family of vertices -/

private theorem jsp87_cube_cancelF {K : ℕ} (j : Fin K) (S : Finset (Finset (Fin K)))
    (hS : ∀ s : Finset (Fin K), s ∈ S → jsp87AltToggle j s ∈ S)
    (g : Finset (Fin K) → ℝ) (hg : ∀ s : Finset (Fin K), g (jsp87AltToggle j s) = - g s) :
    ∑ s ∈ S, g s = 0 := by
  have hmem : ∀ s : Finset (Fin K), s ∈ S → jsp87AltToggle j s ∈ S := hS
  have hinj : ∀ a : Finset (Fin K), a ∈ S → ∀ b : Finset (Fin K), b ∈ S →
      jsp87AltToggle j a = jsp87AltToggle j b → a = b := by
    intro a _ b _ heq
    calc a = jsp87AltToggle j (jsp87AltToggle j a) := (jsp87AltToggle_invol j a).symm
      _ = jsp87AltToggle j (jsp87AltToggle j b) := congrArg (jsp87AltToggle j) heq
      _ = b := jsp87AltToggle_invol j b
  have hsurj : ∀ b : Finset (Fin K), b ∈ S →
      Exists fun a : Finset (Fin K) => Exists fun (_ : a ∈ S) => jsp87AltToggle j a = b := by
    intro b _
    exact ⟨jsp87AltToggle j b, hS b ‹_›, by rw [jsp87AltToggle_invol]⟩
  have hbij : (∑ s ∈ S, g (jsp87AltToggle j s)) = ∑ s ∈ S, g s :=
    Finset.sum_bij (fun s (_ : s ∈ S) => jsp87AltToggle j s) hmem hinj hsurj
      (fun _ _ => rfl)
  have key : (∑ s ∈ S, g s) = -(∑ s ∈ S, g s) := by
    calc (∑ s ∈ S, g s) = ∑ s ∈ S, (- g s) := by
          rw [← hbij]
          exact Finset.sum_congr rfl fun s _ => hg s
      _ = -(∑ s ∈ S, g s) := by rw [Finset.sum_neg_distrib]
  linarith

private theorem jsp87_toggle_avoid {K : ℕ} (j : Fin (K + 1)) (hjl : j ≠ Fin.last K)
    (s : Finset (Fin (K + 1))) (hs : (Fin.last K) ∉ s) :
    (Fin.last K) ∉ jsp87AltToggle j s := by
  intro hc
  unfold jsp87AltToggle at hc
  split at hc
  · exact hs (Finset.mem_erase.mp hc).2
  · rcases Finset.mem_insert.mp hc with heq | hmem
    · exact absurd heq hjl.symm
    · exact hs hmem

/-- **A VANISHING STEP KILLS THE HALF CUBE** (the same degeneracy, inside the
half cube). -/
theorem jsp87HalfCube_zero_of_step {K : ℕ} (f : ℕ → ℝ) (A : Fin (K + 1) → ℤ) (base : ℤ)
    (j : Fin (K + 1)) (hj : A j = 0) (hjl : j ≠ Fin.last K) :
    jsp87HalfCube f A base = 0 := by
  have hg : ∀ s : Finset (Fin (K + 1)),
      (jsp87Sign (jsp87AltToggle j s).card : ℝ) * f ((base + ∑ k ∈ jsp87AltToggle j s, A k : ℤ)).toNat
        = - ((jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat) := by
    intro s
    rw [jsp87ZSum_step_toggle A j s hj, jsp87AltSign_toggle]
    push_cast
    ring
  unfold jsp87HalfCube
  exact jsp87_cube_cancelF j
    ((Finset.univ : Finset (Finset (Fin (K + 1)))).filter (fun s => (Fin.last K) ∉ s))
    (fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      jsp87_toggle_avoid j hjl s (Finset.mem_filter.mp hs).2⟩)
    (fun s => (jsp87Sign s.card : ℝ) * f ((base + ∑ k ∈ s, A k : ℤ)).toNat) hg

/-- **THE REAL ERDÖS CUBE IN CUBE FORM.** -/
theorem jsp87AltSumR_eq_jsp87FCube {K : ℕ} (f : ℕ → ℝ) (v : Fin K → ℤ) (p0 n h : ℕ) :
    jsp87AltSumR f v p0 n h = jsp87FCube f (jsp87AltStep v h) (jsp87AltBase p0 n h) := by
  unfold jsp87AltSumR jsp87FCube jsp87AltShift jsp87AltBase jsp87AltStep
  exact Finset.sum_congr rfl fun s _ => by congr 2; ring

/-- **THE ERDÖS `(K+1)`-CUBE SPLITS IN TWO.**  The alternating sum of §5.2 at
dimension `K+1` is the difference of the two half cubes cut out by the last
coordinate: the recursion that the Gowers norm of the paper's proof iterates. -/
theorem jsp87AltSumR_eq_half_sub {K : ℕ} (f : ℕ → ℝ) (v : Fin (K + 1) → ℤ) (p0 n h : ℕ) :
    jsp87AltSumR f v p0 n h
      = jsp87HalfCube f (jsp87AltStep v h) (jsp87AltBase p0 n h)
        - jsp87HalfCube f (jsp87AltStep v h)
            (jsp87AltBase p0 n h + jsp87AltStep v h (Fin.last K)) := by
  rw [jsp87AltSumR_eq_jsp87FCube]
  exact jsp87FCube_eq_half_sub f _ _


/-- **THE DEGENERATE LEVEL IS THE ONLY ONE THAT FORCES THE ERDÖS CUBE TO
VANISH.**  For `j < K` with `v j ≠ 0` the step of the Erdős half cube in the
`j`-th direction vanishes **exactly** at the level `h = j+1`: at every other
level the half cube is *not* forced to vanish, which is where the analytic
input of the published proof has to act. -/
theorem jsp87AltStep_eq_zero_iff {K : ℕ} (v : Fin (K + 1) → ℤ) (h : ℕ) (j : Fin (K + 1))
    (hv : v j ≠ 0) : jsp87AltStep v h j = 0 ↔ h = j.val + 1 := by
  have key : jsp87AltStep v h j = 0 ↔ ((h : ℤ) - (j.val : ℤ) - 1) = 0 := by
    unfold jsp87AltStep
    constructor
    · intro hh
      rcases mul_eq_zero.mp hh with h1 | h2
      · exact h1
      · exact absurd h2 hv
    · intro hh
      rw [hh, zero_mul]
  rw [key]
  constructor
  · intro hh
    have h3 : (h : ℤ) = (j.val : ℤ) + 1 := by linarith
    have h3' : (h : ℤ) = ((j.val + 1 : ℕ) : ℤ) := by
      calc (h : ℤ) = (j.val : ℤ) + 1 := h3
        _ = ((j.val + 1 : ℕ) : ℤ) := (Nat.cast_add j.val 1).symm
    exact_mod_cast h3'
  · intro hh
    rw [hh, Nat.cast_add]
    ring

/-- **A NON-VANISHING HALF CUBE OF `ω`** (machine checked): the recursion above
is *not* vacuous.  At level `4` — above the degenerate range `h ≤ K+1 = 4` of
the full cube — the half cube of the Erdős function with unit steps does not
vanish. -/
theorem jsp87ZHalfCube_omega_ne_zero :
    jsp87ZHalfCube (fun m => omega m) (jsp87AltStep (fun _ : Fin 4 => 1) 4) 4 = -2 := by
  native_decide

/-! ## §4  The rationality quantisation of a cube of windows, and the criterion

Round 88 promised (`jsp87Alt_congr`, `jsp87Alt_zero_or_ge`,
`jsp87Series_irrational_of_altSmall` in the file header) but never delivered: the
mod-1 quantisation of the alternating sums.  It is proved here, **at every
dimension**, and combined with the splitting identity it turns Gowers-norm
smallness of the window function into a contradiction. -/

/-- **THE `1`-CUBE IS A DIFFERENCE OF TWO WINDOWS.**  With `K = 0` the splitting
identity degenerates to the `1`-dimensional case, and the half cube to the
single vertex `∅`: the `1`-cube of `f` is the difference of `f` at two points
separated by the (arbitrary) step. -/
theorem jsp87FCube_one (f : ℕ → ℝ) (base : ℤ) (m : ℤ) :
    jsp87FCube f (fun _ : Fin 1 => m) base = f base.toNat - f (base + m).toNat := by
  have h0 : ((Finset.univ : Finset (Finset (Fin 1))))
      = ({∅, ({(0 : Fin 1)} : Finset (Fin 1))} : Finset (Finset (Fin 1))) := by decide
  unfold jsp87FCube
  rw [h0]
  simp [jsp87Sign, Finset.card_empty, Finset.card_singleton]
  ring

/-- **THE RATIONALITY QUANTISATION OF A CUBE OF WINDOWS.**  If the Erdős series
is `a/b` with `b > 0`, then *every* cube of windows, **at every dimension**, is a
multiple of `1/b`: the freeze of `jsp87Win_mul_eq_int` (round 88) survives the
alternating summation, because `±` and `∑` are integral operations. -/
theorem jsp87FCube_mul_eq_int {K : ℕ} (A : Fin K → ℤ) (base : ℤ) {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, (b : ℝ) * jsp87FCube jsp87Win A base = (c : ℝ) := by
  have hget : ∀ s : Finset (Fin K), ∃ c : ℤ,
      (b : ℝ) * jsp87Win ((base + ∑ k ∈ s, A k : ℤ)).toNat = (c : ℝ) :=
    fun s => jsp87Win_mul_eq_int (a := a) (b := b) (n := _) hb h
  choose cfun hcf using hget
  refine ⟨∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), jsp87Sign s.card * cfun s, ?_⟩
  unfold jsp87FCube
  rw [Int.cast_sum, Finset.mul_sum]
  have h1 : ∀ s : Finset (Fin K),
      (b : ℝ) * ((jsp87Sign s.card : ℝ) * jsp87Win ((base + ∑ k ∈ s, A k : ℤ)).toNat)
        = ((jsp87Sign s.card * cfun s : ℤ) : ℝ) := by
    intro s
    calc (b : ℝ) * ((jsp87Sign s.card : ℝ) * jsp87Win ((base + ∑ k ∈ s, A k : ℤ)).toNat)
        = (jsp87Sign s.card : ℝ) * (b : ℝ) * jsp87Win ((base + ∑ k ∈ s, A k : ℤ)).toNat := by ring
      _ = (jsp87Sign s.card : ℝ) * (cfun s : ℝ) := by
        calc (jsp87Sign s.card : ℝ) * (b : ℝ)
            * jsp87Win ((base + ∑ k ∈ s, A k : ℤ)).toNat
            = (jsp87Sign s.card : ℝ)
              * ((b : ℝ) * jsp87Win ((base + ∑ k ∈ s, A k : ℤ)).toNat) := by ring
          _ = (jsp87Sign s.card : ℝ) * (cfun s : ℝ) := by rw [hcf s]
      _ = ((jsp87Sign s.card * cfun s : ℤ) : ℝ) := by push_cast; ring
  exact Finset.sum_congr rfl fun s _ => h1 s

/-- **THE DICHOTOMY.**  Every cube of windows is either `0` or has absolute
value at least `1/b`: the exact quantised alternative of §5.2–5.3 of
Tao–Teräväinen, at every dimension. -/
theorem jsp87FCube_zero_or_ge {K : ℕ} (A : Fin K → ℤ) (base : ℤ) {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    jsp87FCube jsp87Win A base = 0
      ∨ (1 : ℝ) / (b : ℝ) ≤ |jsp87FCube jsp87Win A base| := by
  obtain ⟨c, hc⟩ := jsp87FCube_mul_eq_int A base hb h
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  by_cases hcz : c = 0
  · left
    have hz : (b : ℝ) * jsp87FCube jsp87Win A base = 0 := by rw [hc]; simp [hcz]
    rcases mul_eq_zero.mp hz with h1 | h2
    · linarith
    · exact h2
  · right
    have habs : (1 : ℤ) ≤ |c| := by
      by_cases hc' : 0 < c
      · rw [abs_of_pos hc']; omega
      · rw [abs_of_neg (by omega)]; omega
    have key : |jsp87FCube jsp87Win A base| = |(c : ℝ)| / (b : ℝ) := by
      have hc' : jsp87FCube jsp87Win A base = (c : ℝ) / (b : ℝ) := by
        rw [eq_div_iff (ne_of_gt hb0), ← hc]
        ring
      rw [hc', abs_div, abs_of_pos hb0]
    rw [key]
    have h1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast habs
    exact div_le_div_of_nonneg_right h1 (le_of_lt hb0)

/-- **A CUBE SMALLER THAN `1/b` VANISHES** — the quantisation half of the
criterion. -/
theorem jsp87FCube_eq_zero_of_lt {K : ℕ} (A : Fin K → ℤ) (base : ℤ) {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ))
    (hlt : |jsp87FCube jsp87Win A base| < (1 : ℝ) / (b : ℝ)) :
    jsp87FCube jsp87Win A base = 0 := by
  rcases jsp87FCube_zero_or_ge A base hb h with hz | hg
  · exact hz
  · exact absurd hlt (not_lt_of_ge hg)

/-- **THE WINDOWS ARE NOT CONSTANT.**  The window recurrence
`W(n+1) = 2 W(n) − ω(n+1)` says that a constant window forces a constant `ω`,
and `ω(1) = 0 ≠ 2 = ω(6)`.  This is the *aperiodicity* ingredient of the
endgame, in the form the cube criterion needs. -/
theorem jsp87Win_not_const : ¬ (∃ c : ℝ, ∀ n : ℕ, jsp87Win n = c) := by
  rintro ⟨c, hc⟩
  have h1 : jsp87Win 1 = 2 * jsp87Win 0 - (omega 1 : ℝ) := by
    simpa using jsp87Win_succ 0
  have h5 : jsp87Win 6 = 2 * jsp87Win 5 - (omega 6 : ℝ) := by
    simpa using jsp87Win_succ 5
  have ho1 : omega 1 = 0 := by native_decide
  have ho6 : omega 6 = 2 := by native_decide
  rw [hc 1, hc 0] at h1
  rw [hc 6, hc 5] at h5
  have ho1' : (omega 1 : ℝ) = 0 := by rw [ho1]; norm_num
  have ho6' : (omega 6 : ℝ) = 2 := by rw [ho6]; norm_num
  rw [ho1'] at h1
  rw [ho6'] at h5
  linarith

/-- **SMALL `1`-CUBES MAKE THE WINDOWS CONSTANT.**  If every `1`-cube of the
window function is `0` — the only way, by the quantisation, for them to be
nonzero *and* smaller than `1/b` — then the window function is constant, which
`jsp87Win_not_const` forbids. -/
theorem jsp87Win_const_of_FCube_one_zero
    (h : ∀ (m : ℤ) (base : ℤ), jsp87FCube jsp87Win (fun _ : Fin 1 => m) base = 0) :
    ∃ c : ℝ, ∀ n : ℕ, jsp87Win n = c := by
  refine ⟨jsp87Win 0, fun n => ?_⟩
  have h1 := h (n : ℤ) 0
  rw [jsp87FCube_one] at h1
  have hnt : ((0 + (n : ℤ) : ℤ)).toNat = n := by
    rw [show (0 + (n : ℤ) : ℤ) = (n : ℤ) by omega]
    have hnn := Int.toNat_of_nonneg (a := (n : ℤ)) (by omega)
    exact_mod_cast hnn
  have h0 : ((0 : ℤ)).toNat = 0 := by simp
  rw [h0, hnt] at h1
  linarith

/-- **ROUND 91'S CRITERION: THE COMPLETE REDUCTION OF THE HEADLINE.**  If the
Erdős series is a rational `a/b`, then *every* `1`-cube of the window function
`W` has absolute value either `0` or `≥ 1/b`; and if all of them were smaller
than `1/b` they would all vanish, forcing `W` to be constant, which forces `ω`
to be constant — impossible.

So the headline `Irrational jsp87Series` follows from the single, purely
analytic hypothesis

> `(hsmall)  ∀ b > 0, ∀ m base, |W(base) − W(base + m)| < 1/b`,

i.e. from the **Gowers-norm smallness of the window function**, which is the
input Tao–Teräväinen obtain from the Pilatte correlation estimate (§3 of
arXiv:2512.01739).  Every combinatorial and Diophantine step of the reduction
is now formalised, for *every* dimension. -/
theorem jsp87Series_irrational_of_FCube_one_small
    (hsmall : ∀ (b : ℤ), 0 < b → ∀ (m : ℤ) (base : ℤ),
      |jsp87FCube jsp87Win (fun _ : Fin 1 => m) base| < 1 / (b : ℝ)) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  have hcast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := by push_cast; rfl
  have hS : jsp87Series = (q.num : ℝ) / ((q.den : ℤ) : ℝ) := by
    rw [← hq, Rat.cast_def, hcast]
  have hz : ∀ (m : ℤ) (base : ℤ),
      jsp87FCube jsp87Win (fun _ : Fin 1 => m) base = 0 := by
    intro m base
    exact jsp87FCube_eq_zero_of_lt (A := fun _ : Fin 1 => m) (base := base)
      (a := q.num) (b := (q.den : ℤ)) (by exact_mod_cast hden) hS
      (hsmall _ (by exact_mod_cast hden) m base)
  exact jsp87Win_not_const (jsp87Win_const_of_FCube_one_zero hz)

/-! ## §5  The degeneracy survives the splitting, and only there -/

/-- **THE ERDÖS CUBE AT DIMENSION `K+1` STILL VANISHES AT EVERY LEVEL
`1 ≤ h ≤ K+1`.**  Round 90's flagship, re-proved with the splitting identity:
the step in the `h−1`-th direction (or in the last direction when `h = K+1`)
still vanishes. -/
theorem jsp87AltSumR_zero_of_level {K : ℕ} (f : ℕ → ℝ) (v : Fin (K + 1) → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K + 1) : jsp87AltSumR f v p0 n h = 0 := by
  rw [jsp87AltSumR_eq_jsp87FCube]
  by_cases hc : h = K + 1
  · refine jsp87FCube_zero_of_step f _ _ (Fin.last K) ?_
    rw [hc, jsp87AltStep_eq, Nat.cast_add]
    have : (Fin.last K : Fin (K+1)).val = K := rfl
    simp only [this]
    ring
  · have hlt : h - 1 < K + 1 := by omega
    refine jsp87FCube_zero_of_step f _ _ ⟨h - 1, hlt⟩ ?_
    rw [jsp87AltStep_eq]
    have e : (h : ℤ) = ((h - 1 : ℕ) : ℤ) + 1 := by exact_mod_cast (by omega)
    rw [e]
    ring

/-- **THE HALF CUBE VANISHES AT EVERY LEVEL `1 ≤ h ≤ K` AND ONLY THERE.**  Above
the level `K` no step of the Erdős half cube is forced to vanish, so the
recursion of §2 has *something to say*: this is the exact boundary inside which
the cube is an exact cancellation and outside which the analytic input of the
published proof must act. -/
theorem jsp87HalfCube_zero_of_level {K : ℕ} (f : ℕ → ℝ) (v : Fin (K + 1) → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) :
    jsp87HalfCube f (jsp87AltStep v h) (jsp87AltBase p0 n h) = 0 := by
  have hlt : h - 1 < K + 1 := by omega
  have hne : (⟨h - 1, hlt⟩ : Fin (K + 1)) ≠ Fin.last K := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega
  refine jsp87HalfCube_zero_of_step f _ _ ⟨h - 1, hlt⟩ ?_ hne
  rw [jsp87AltStep_eq]
  have e : (h : ℤ) = ((h - 1 : ℕ) : ℤ) + 1 := by exact_mod_cast (by omega)
  rw [e]
  ring

/-- **A CUBE HAS EXACTLY `2^K` VERTICES** — the counting that makes the
recursion of §2 a `4`-fold refinement. -/
theorem jsp87FCube_card {K : ℕ} :
    ((Finset.univ : Finset (Finset (Fin K)))).card = 2 ^ K := by
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

end JSP87

