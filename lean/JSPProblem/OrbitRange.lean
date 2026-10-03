/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.OrbitArith
import JSPProblem.RunLength
import JSPProblem.ProgressionOmega
import Mathlib.Tactic

/-!
# JSP-000087 : the *range* of the doubling orbit of the carries

Rounds 41, 46, 48, 57 and 64 worked with the *binary digits* of the Erdős series
and with the *period* of the doubling orbit `N ↦ Int.fract (θ N)`: round 64
computed the minimal eventual period of the orbit to be `ord_{jsp87OddPart b}(2)`
and the start point to be `v_2(b)`, and it reduced the headline to
`jsp87Series_irrational_iff_fracCarry_notPeriodic`.

**Nothing in the tree has ever looked at the orbit itself as a set of points.**
All the previous statements are about *collisions* (`fract θ i = fract θ j`) or
about *periods*, i.e. about the *arithmetic* of the orbit; none of them about its
*image*.  This module is that attack family, and it is the "limit-set"
formulation of the same obstruction.

## 1.  The four objects

```
jsp87Dbl x          = Int.fract (2 * x)          -- the doubling map on [0,1)
jsp87OrbitRange                              -- {Int.fract (θ N) : N}
jsp87OrbitWindow N = image of [0,N] under N ↦ Int.fract (θ N)
jsp87OrbitCount N  = #(jsp87OrbitWindow N)     -- how many points so far
```

## 2.  What is proved

* **Determinism** (`jsp87_dbl_apply`, `jsp87_orbit_iter`): the successor of an
  orbit point is the *doubling map* applied to it, and `k` iterates of the
  doubling map are the orbit point at `N + k`.  Hence the orbit is a genuine
  dynamical system, so a *finite* orbit is automatically *eventually periodic*.
* **Periodicity ⟹ finite range** (`jsp87_orbitRange_eq_of_periodic`,
  `jsp87_orbitRange_finite_of_periodic`): under an eventual period `t` from `M`
  the whole range is the image of the **first `M + t` points**, so the range is a
  `Finset ℝ` of cardinality `≤ M + t`.  The quantitative core is
  `jsp87_orbit_period_reduce`: `fract θ N = fract θ (M + (N - M) % t)`.
* **Finite range ⟹ periodicity** (`jsp87_orbit_periodic_of_finiteRange`): the
  converse, from pigeonhole + determinism.  Mathlib has no theorem of this shape
  for the base-`2` expansion of any real number.
* **THE CRITERION** (`jsp87Series_irrational_iff_orbitRange_infinite`):

  > `Irrational jsp87Series` **iff** the set `{Int.fract (θ N) : N}` is not
  > contained in any `Finset ℝ`.

  i.e. *the Erdős series is irrational exactly when the doubling orbit of the
  carries has an infinite image* — a statement about a **set**, with no period,
  no modulus and no denominator in it at all.
* **The counting function** (`jsp87_orbitCount_*`): monotone, positive,
  `≤ N + 1`, `= N + 1` on an injective window, `≤ M + t` under an eventual
  period, `=` constant along the period, and `≤ b` for a rational value
  `S = a/b` (`jsp87_orbitCount_le_denominator`).  Hence
  `jsp87Series_irrational_of_orbitCount_unbounded`: *unboundedly many distinct
  orbit points ⟹ irrationality*.

The rational side therefore carries **two** independent finite bounds — one on
the *period* (round 64: `ord_{b'}(2)`) and now one on the *number of distinct
orbit points* (this round: `≤ b`) — and both are consequences of the finiteness
of a single set.  `-/

namespace JSP87

set_option maxHeartbeats 1000000

open Finset

/-- **The doubling map on the unit interval.** -/
noncomputable def jsp87Dbl (x : ℝ) : ℝ := Int.fract (2 * x)

/-- **The range of the doubling orbit of the carries**, i.e. the set of values
taken by the fractional parts of the carries `θ N = 2^N · τ N`. -/
def jsp87OrbitRange : Set ℝ := {x | ∃ N : ℕ, Int.fract (jsp87Carry N) = x}

/-- The distinct orbit points seen among the first `N + 1` indices. -/
noncomputable def jsp87OrbitWindow (N : ℕ) : Finset ℝ :=
  (Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))

/-- **The number of distinct points of the doubling orbit among the first
`N + 1` indices** — the counting function of `jsp87OrbitRange`. -/
noncomputable def jsp87OrbitCount (N : ℕ) : ℕ := jsp87OrbitWindow N |>.card

/-! ## 1.  The orbit is the iteration of the doubling map -/

theorem jsp87_mem_orbitRange {x : ℝ} :
    x ∈ jsp87OrbitRange ↔ ∃ N : ℕ, Int.fract (jsp87Carry N) = x := Iff.rfl

/-- **THE DETERMINISM OF THE ORBIT.**  The successor of the orbit point at `N`
is the doubling map applied to it: the orbit is a genuine dynamical system. -/
theorem jsp87_dbl_apply (N : ℕ) :
    jsp87Dbl (Int.fract (jsp87Carry N)) = Int.fract (jsp87Carry (N + 1)) := by
  show Int.fract (2 * Int.fract (jsp87Carry N)) = _
  rw [jsp87_fractCarry_succ]

/-- **`k` iterates of the doubling map are the orbit point at `N + k`.** -/
theorem jsp87_orbit_iter (N k : ℕ) :
    jsp87Dbl^[k] (Int.fract (jsp87Carry N)) = Int.fract (jsp87Carry (N + k)) := by
  induction k generalizing N with
  | zero => simp
  | succ k ih =>
      have h1 : jsp87Dbl^[k+1] (Int.fract (jsp87Carry N))
          = jsp87Dbl^[k] (jsp87Dbl (Int.fract (jsp87Carry N))) :=
        Function.iterate_succ_apply jsp87Dbl k _
      rw [h1, jsp87_dbl_apply, ih (N := N + 1)]
      have e : N + 1 + k = N + Nat.succ k := by rw [Nat.succ_eq_add_one]; omega
      rw [e]

/-- **THE RANGE IS CLOSED UNDER THE DOUBLING MAP.** -/
theorem jsp87_orbitRange_closed (x : ℝ) (hx : x ∈ jsp87OrbitRange) :
    jsp87Dbl x ∈ jsp87OrbitRange := by
  rcases (jsp87_mem_orbitRange.mp hx) with ⟨N, rfl⟩
  exact ⟨N + 1, (jsp87_dbl_apply N).symm⟩

/-! ## 2.  Elementary properties of the range -/

theorem jsp87_orbitRange_nonempty : jsp87OrbitRange.Nonempty :=
  ⟨Int.fract (jsp87Carry 0), ⟨0, rfl⟩⟩

/-- **Every orbit point lies in `[0, 1)`.** -/
theorem jsp87_orbitRange_subset_unit (x : ℝ) (hx : x ∈ jsp87OrbitRange) :
    0 ≤ x ∧ x < 1 := by
  rcases (jsp87_mem_orbitRange.mp hx) with ⟨N, rfl⟩
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-! ## 3.  An eventual period makes the range finite -/

/-- **ITERATING THE PERIOD.**  `q` periods take the orbit point at `N` to the
orbit point at `N + q·t`. -/
theorem jsp87_orbit_period_iter {t M : ℕ} (_ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
    (N : ℕ) (hN : M ≤ N) (q : ℕ) :
    Int.fract (jsp87Carry (N + q * t)) = Int.fract (jsp87Carry N) := by
  induction q generalizing N with
  | zero => simp
  | succ q ih =>
      have hstep : Int.fract (jsp87Carry (N + (q + 1) * t))
          = Int.fract (jsp87Carry (N + q * t)) := by
        have hid : N + (q + 1) * t = (N + q * t) + t := by ring
        rw [hid]
        exact hper _ (by omega)
      calc Int.fract (jsp87Carry (N + (q + 1) * t))
          = Int.fract (jsp87Carry (N + q * t)) := hstep
        _ = Int.fract (jsp87Carry N) := ih N hN

/-- **THE WINDOW REDUCTION.**  Under an eventual period `t` from `M`, the orbit
point at `N` is the orbit point at `M + (N - M) % t`: *the whole orbit is
determined by its first `t` points after `M`*. -/
theorem jsp87_orbit_period_reduce {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
    (N : ℕ) (hN : M ≤ N) :
    Int.fract (jsp87Carry N) = Int.fract (jsp87Carry (M + (N - M) % t)) := by
  have hsum : (N - M) % t + ((N - M) / t) * t = N - M := by
    simpa [Nat.mul_comm] using Nat.mod_add_div (N - M) t
  have hid : (M + (N - M) % t) + ((N - M) / t) * t = N := by
    calc (M + (N - M) % t) + ((N - M) / t) * t
        = M + ((N - M) % t + ((N - M) / t) * t) := by omega
      _ = M + (N - M) := by rw [hsum]
      _ = N := Nat.add_sub_of_le hN
  have hbase : M ≤ M + (N - M) % t := by omega
  have hiter := jsp87_orbit_period_iter ht hper (M + (N - M) % t) hbase ((N - M) / t)
  rw [hid] at hiter
  exact hiter

/-- **THE RANGE IS CONTAINED IN THE FIRST `M + t` POINTS.** -/
theorem jsp87_orbitRange_subset_window {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
    {x : ℝ} (hx : x ∈ jsp87OrbitRange) :
    ∃ k < M + t, x = Int.fract (jsp87Carry k) := by
  rcases (jsp87_mem_orbitRange.mp hx) with ⟨N, hxN⟩
  by_cases h : M ≤ N
  · refine ⟨M + (N - M) % t, ?_, ?_⟩
    · have hlt : (N - M) % t < t := Nat.mod_lt _ ht
      omega
    · rw [← hxN, jsp87_orbit_period_reduce ht hper N h]
  · refine ⟨N, by omega, hxN.symm⟩

/-- **AN EVENTUAL PERIOD MAKES THE WHOLE ORBIT THE IMAGE OF A FINITE WINDOW.**
The doubling orbit is *exactly* the image of the first `M + t` points, so its
cardinality is at most `M + t`. -/
theorem jsp87_orbitRange_eq_of_periodic {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N)) :
    jsp87OrbitRange = ↑((Finset.range (M + t)).image (fun k : ℕ => Int.fract (jsp87Carry k))) := by
  ext x
  constructor
  · intro hx
    rcases jsp87_orbitRange_subset_window ht hper hx with ⟨k, hk, hxk⟩
    refine Finset.mem_coe.mpr ?_
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hxk.symm⟩
  · intro hx
    simp only [Finset.mem_coe] at hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact ⟨k, rfl⟩

/-- **AN EVENTUAL PERIOD MAKES THE RANGE A `Finset ℝ`.** -/
theorem jsp87_orbitRange_finite_of_periodic {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N)) :
    ∃ s : Finset ℝ, ∀ N, Int.fract (jsp87Carry N) ∈ s := by
  refine ⟨(Finset.range (M + t)).image (fun k : ℕ => Int.fract (jsp87Carry k)), ?_⟩
  intro N
  refine Finset.mem_coe.mpr ?_
  rcases jsp87_orbitRange_subset_window ht hper ⟨N, rfl⟩ with ⟨k, hk, hkN⟩
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hkN.symm⟩

/-- **The size of the range under an eventual period**: a `Finset ℝ` of
cardinality `≤ M + t`. -/
theorem jsp87_orbitRange_card_le_of_periodic {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N)) :
    ∃ s : Finset ℝ, (∀ N, Int.fract (jsp87Carry N) ∈ s) ∧ s.card ≤ M + t := by
  refine ⟨(Finset.range (M + t)).image (fun k : ℕ => Int.fract (jsp87Carry k)), ?_, ?_⟩
  · intro N
    refine Finset.mem_coe.mpr ?_
    rcases jsp87_orbitRange_subset_window ht hper ⟨N, rfl⟩ with ⟨k, hk, hkN⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, hkN.symm⟩
  · calc ((Finset.range (M + t)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card
      ≤ (Finset.range (M + t)).card := Finset.card_image_le
    _ = M + t := by simp

/-! ## 4.  Conversely, a finite range forces an eventual period -/

/-- **A FINITE RANGE GIVES A COLLISION, AND A COLLISION GIVES A PERIOD.**  This
is the only place where determinism (`jsp87_orbit_iter`) is used: the `q`-th
iterate of two equal points is again equal. -/
private theorem jsp87_orbit_period_of_collision {i j : ℕ} (hcoll :
    Int.fract (jsp87Carry i) = Int.fract (jsp87Carry j)) (hne : i ≠ j) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
      ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N) := by
  have hmd : min i j + (max i j - min i j) = max i j := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]
      omega
    · rw [min_eq_right h.le, max_eq_left h.le]
      omega
  have hmj : Int.fract (jsp87Carry (min i j)) = Int.fract (jsp87Carry (max i j)) := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, hcoll, max_eq_right h.le]
    · rw [min_eq_right h.le, max_eq_left h.le]
      exact hcoll.symm
  set d := max i j - min i j with hd
  have hdpos : 0 < d := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [hd, max_eq_right h.le, min_eq_left h.le]
      omega
    · rw [hd, max_eq_left h.le, min_eq_right h.le]
      omega
  have hper : ∀ N, min i j ≤ N →
      Int.fract (jsp87Carry (N + d)) = Int.fract (jsp87Carry N) := by
    intro N hN
    have hidN : N + d = (min i j + (N - min i j)) + d := by rw [Nat.add_sub_of_le hN]
    have hback : min i j + (N - min i j) = N := Nat.add_sub_of_le hN
    have hid2 : min i j + d + (N - min i j) = (min i j + (N - min i j)) + d := by omega
    calc Int.fract (jsp87Carry (N + d))
        = Int.fract (jsp87Carry ((min i j + (N - min i j)) + d)) := by rw [hidN]
      _ = jsp87Dbl^[N - min i j] (Int.fract (jsp87Carry (min i j + d))) := by
          rw [← hid2]
          exact (jsp87_orbit_iter (min i j + d) (N - min i j)).symm
      _ = jsp87Dbl^[N - min i j] (Int.fract (jsp87Carry (min i j))) := by
          rw [show min i j + d = max i j by rw [← hmd]]
          exact congrArg _ hmj.symm
      _ = Int.fract (jsp87Carry (min i j + (N - min i j))) :=
          jsp87_orbit_iter (min i j) (N - min i j)
      _ = Int.fract (jsp87Carry N) := by rw [hback]
  refine ⟨d, min i j + 1, hdpos, by omega, ?_⟩
  intro N hN
  exact hper N (by omega)

/-- **A FINITE RANGE FORCES AN EVENTUAL PERIOD.**  The converse of §3, and the
only place where pigeonhole is used.  Mathlib has no theorem of this shape for
the base-`2` expansion of any real number. -/
theorem jsp87_orbit_periodic_of_finiteRange {s : Finset ℝ}
    (hs : ∀ N, Int.fract (jsp87Carry N) ∈ s) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
      ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N) := by
  classical
  obtain ⟨i, hi, j, hj, hne, hij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (s.card + 2)) (t := s)
      (f := fun k => Int.fract (jsp87Carry (s.card + 2 + k))) (by simp) (fun _ _ => hs _)
  exact jsp87_orbit_period_of_collision (i := s.card + 2 + i) (j := s.card + 2 + j) hij
    (by omega)

/-! ## 5.  THE CRITERION: the range of the doubling orbit -/

/-- **THE RANGE CRITERION FOR THE HEADLINE.**

> `jsp87Series` is irrational **iff** the set of points
> `{Int.fract (θ N) : N ∈ ℕ}` of the doubling orbit of the carries is not
> contained in any `Finset ℝ` — i.e. **iff the orbit of the carries is an
> infinite set**.

This is the "limit-set" form of round 64's period criterion, and it mentions
neither a period, nor a modulus, nor a denominator: only the finiteness of one
set.  The two halves are §3 (a period gives a finite range) and §4 (a finite
range gives a period). -/
theorem jsp87Series_irrational_iff_orbitRange_infinite :
    Irrational jsp87Series ↔ ¬ ∃ s : Finset ℝ, ∀ N, Int.fract (jsp87Carry N) ∈ s := by
  constructor
  · intro hirr
    show ¬ ∃ s : Finset ℝ, ∀ N, Int.fract (jsp87Carry N) ∈ s
    have hirr' : Irrational jsp87Series := hirr
    intro hfin
    obtain ⟨s, hs⟩ := hfin
    obtain ⟨t, M, ht, hM, hper⟩ := jsp87_orbit_periodic_of_finiteRange hs
    exact jsp87Series_irrational_iff_fracCarry_notPeriodic.mp hirr' ⟨t, M, ht, hM, hper⟩
  · intro hnfin
    show Irrational jsp87Series
    refine jsp87Series_irrational_iff_fracCarry_notPeriodic.mpr ?_
    rintro ⟨t, M, ht, hM, hper⟩
    obtain ⟨s, hs⟩ := jsp87_orbitRange_finite_of_periodic ht hper
    exact hnfin ⟨s, hs⟩

/-- **A sufficient condition stated with injectivity.** -/
theorem jsp87Series_irrational_of_orbit_injective
    (h : Function.Injective (fun N : ℕ => Int.fract (jsp87Carry N))) :
    Irrational jsp87Series := by
  refine jsp87Series_irrational_iff_fracCarry_notPeriodic.mpr ?_
  rintro ⟨t, M, ht, hM, hper⟩
  have hne : M + t = M := h (hper M (Nat.le_refl M))
  omega

/-- **A rational value of the series forces a finite set of orbit points.** -/
theorem jsp87Series_rational_imp_orbitRange_finite {a : ℤ} {b : ℕ} (_hb : 0 < b)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ s : Finset ℝ, ∀ N, Int.fract (jsp87Carry N) ∈ s := by
  have hirr : ¬ Irrational jsp87Series := by
    intro h
    refine h ⟨↑(a : ℚ) / b, ?_⟩
    rw [show ((↑(a : ℚ) / b : ℚ) : ℝ) = (↑a / ↑b : ℝ) by push_cast; ring, hS]
  have hex : ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
      ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N) := by
    by_contra hcon
    exact hirr (jsp87Series_irrational_iff_fracCarry_notPeriodic.mpr hcon)
  obtain ⟨t, M, ht, hM, hper⟩ := hex
  exact jsp87_orbitRange_finite_of_periodic ht hper

/-! ## 6.  The counting function of the range -/

theorem jsp87_orbitCount_mono {M N : ℕ} (h : M ≤ N) :
    jsp87OrbitCount M ≤ jsp87OrbitCount N := by
  classical
  unfold jsp87OrbitCount jsp87OrbitWindow
  refine Finset.card_le_card ?_
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by
    have hk' := Finset.mem_range.mp hk
    omega), rfl⟩

theorem jsp87_orbitCount_pos (N : ℕ) : 0 < jsp87OrbitCount N := by
  classical
  unfold jsp87OrbitCount jsp87OrbitWindow
  exact Finset.card_pos.mpr
    ⟨Int.fract (jsp87Carry N),
      Finset.mem_image.mpr ⟨N, Finset.mem_range.mpr (Nat.lt_succ_self N), rfl⟩⟩

theorem jsp87_orbitCount_le (N : ℕ) : jsp87OrbitCount N ≤ N + 1 := by
  classical
  unfold jsp87OrbitCount jsp87OrbitWindow
  calc ((Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card
      ≤ (Finset.range (N + 1)).card := Finset.card_image_le
    _ = N + 1 := by simp

/-- **An injective window is filled completely.** -/
theorem jsp87_orbitCount_eq_of_injOn {N : ℕ}
    (h : Set.InjOn (fun k : ℕ => Int.fract (jsp87Carry k)) (Finset.range (N + 1))) :
    jsp87OrbitCount N = N + 1 := by
  classical
  unfold jsp87OrbitCount jsp87OrbitWindow
  rw [Finset.card_image_of_injOn h]
  simp

/-- **AN EVENTUAL PERIOD BOUNDS THE NUMBER OF DISTINCT ORBIT POINTS.** -/
theorem jsp87_orbitCount_le_of_periodic {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
    (N : ℕ) : jsp87OrbitCount N ≤ M + t := by
  classical
  unfold jsp87OrbitCount jsp87OrbitWindow
  calc ((Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card
      ≤ ((Finset.range (M + t)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card := by
        refine Finset.card_le_card ?_
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        rcases jsp87_orbitRange_subset_window ht hper ⟨k, rfl⟩ with ⟨k', hk', hk'k⟩
        exact Finset.mem_image.mpr ⟨k', Finset.mem_range.mpr hk', hk'k.symm⟩
    _ ≤ (Finset.range (M + t)).card := Finset.card_image_le
    _ = M + t := by simp

/-- **THE COUNTING FUNCTION IS CONSTANT ALONG THE PERIOD.** -/
theorem jsp87_orbitCount_eq_of_periodic {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
    {N : ℕ} (hN : M + t ≤ N + 1) : jsp87OrbitCount (N + t) = jsp87OrbitCount N := by
  classical
  unfold jsp87OrbitCount jsp87OrbitWindow
  have hsub : (Finset.range (N + t + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))
      ⊆ (Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases jsp87_orbitRange_subset_window ht hper ⟨k, rfl⟩ with ⟨k', hk', hk'k⟩
    exact Finset.mem_image.mpr ⟨k', Finset.mem_range.mpr (by
      have hk' := Finset.mem_range.mp hk
      omega), hk'k.symm⟩
  have h1 : ((Finset.range (N + t + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card
      ≤ ((Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card :=
        Finset.card_le_card hsub
  have hsub' : (Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))
      ⊆ (Finset.range (N + t + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by
      have hk' := Finset.mem_range.mp hk
      omega), rfl⟩
  have h1' : ((Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card
      ≤ ((Finset.range (N + t + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card :=
        Finset.card_le_card hsub'
  have h2' : ((Finset.range (N + t + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card
      ≤ ((Finset.range (N + 1)).image (fun k : ℕ => Int.fract (jsp87Carry k))).card :=
        Finset.card_le_card hsub
  omega

/-- **THE ORBIT LIES ON THE LATTICE `1/b ℤ`, AT EVERY INDEX.**  Round 41 proved
this for `1 ≤ N`; the case `N = 0` uses the identity `θ 0 = S`. -/
theorem jsp87_orbitCarry_grid {a : ℤ} {b : ℕ} (hb : 0 < b)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) (N : ℕ) :
    ∃ c : ℕ, c < b ∧ Int.fract (jsp87Carry N) = (c : ℝ) / (b : ℝ) := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hN0 : N = 0 := by omega
    subst hN0
    have hmul : (b : ℝ) * (((a : ℤ) : ℝ) / (b : ℝ)) = ((a : ℤ) : ℝ) := by
      have hnb : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
      calc (b : ℝ) * (((a : ℤ) : ℝ) / (b : ℝ))
          = (((a : ℤ) : ℝ) / (b : ℝ)) * (b : ℝ) := by
              rw [mul_comm (b : ℝ) (((a : ℤ) : ℝ) / (b : ℝ))]
        _ = ((a : ℤ) : ℝ) := div_mul_cancel₀ _ hnb
    have hm : (b : ℝ) * jsp87Series = ((a : ℤ) : ℝ) := by rw [hS]; exact hmul
    obtain ⟨c, hc0, hc1, hcF⟩ := Int.fract_eq_div_of_mul_natCast hb (x := jsp87Series) hm
    have hcast : (Int.toNat c : ℝ) = (c : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hc0)
    have hlt : (Int.toNat c : ℤ) < (b : ℤ) := by rw [Int.toNat_of_nonneg hc0]; omega
    refine ⟨Int.toNat c, ?_, ?_⟩
    · exact_mod_cast hlt
    · rw [jsp87Carry_zero, hcF, hcast]
  · obtain ⟨c, hc, hc_eq⟩ := jsp87_fractCarry_eq_div hb hS (N := N) (by omega)
    exact ⟨c, hc, hc_eq⟩

/-- **THE RATIONAL BOUND ON THE NUMBER OF ORBIT POINTS.**  If
`jsp87Series = a/b` then every orbit point is a `b`-th of a unit
(`jsp87_orbitCarry_grid`), so there are at most `b` distinct ones. -/
theorem jsp87_orbitCount_le_denominator {a : ℤ} {b : ℕ} (hb : 0 < b)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) (N : ℕ) : jsp87OrbitCount N ≤ b := by
  classical
  have hgrid : jsp87OrbitWindow N
      ⊆ (Finset.range b).image (fun c : ℕ => (c : ℝ) / (b : ℝ)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    obtain ⟨c, hc, hc_eq⟩ := jsp87_orbitCarry_grid hb hS k
    exact Finset.mem_image.mpr ⟨c, Finset.mem_range.mpr hc, hc_eq.symm⟩
  calc jsp87OrbitCount N = (jsp87OrbitWindow N).card := rfl
    _ ≤ ((Finset.range b).image (fun c : ℕ => (c : ℝ) / (b : ℝ))).card :=
        Finset.card_le_card hgrid
    _ = b := by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro c hc' d hd' hcd
        have hnb : (b : ℝ) ≠ 0 := by positivity
        have h1 : (c : ℝ) * (b : ℝ) = (d : ℝ) * (b : ℝ) :=
          (div_eq_div_iff hnb hnb).mp hcd
        exact_mod_cast mul_right_cancel₀ hnb h1

/-- **ONE STEP OF THE WINDOW: one new point per index.** -/
theorem jsp87_orbitWindow_succ (N : ℕ) :
    jsp87OrbitWindow (N + 1)
      = insert (Int.fract (jsp87Carry (N + 1))) (jsp87OrbitWindow N) := by
  classical
  unfold jsp87OrbitWindow
  rw [show Finset.range (N + 2) = insert (N + 1) (Finset.range (N + 1)) from by
        ext k
        simp only [Finset.mem_insert, Finset.mem_range]
        omega, Finset.image_insert]

/-- **A GENUINELY NEW ORBIT POINT INCREASES THE COUNTING FUNCTION.** -/
theorem jsp87_orbitCount_succ_of_new {N : ℕ}
    (h : Int.fract (jsp87Carry (N + 1)) ∉ jsp87OrbitWindow N) :
    jsp87OrbitCount (N + 1) = jsp87OrbitCount N + 1 := by
  classical
  unfold jsp87OrbitCount
  rw [jsp87_orbitWindow_succ, Finset.card_insert_of_notMem h]

/-- **One index at a time, the counting function grows by at most one.** -/
theorem jsp87_orbitCount_succ_le (N : ℕ) :
    jsp87OrbitCount (N + 1) ≤ jsp87OrbitCount N + 1 := by
  classical
  unfold jsp87OrbitCount
  rw [jsp87_orbitWindow_succ]
  exact Finset.card_insert_le _ _

/-- **AFTER AN EVENTUAL PERIOD STARTS, THE WHOLE ORBIT IS A FINITE WINDOW.**  The
orbit range is then *literally* the `t`-point window at `M + t`. -/
theorem jsp87_orbitRange_eq_window_of_periodic {t M : ℕ} (ht : 0 < t)
    (hper : ∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N))
    {N : ℕ} (hN : M + t ≤ N + 1) :
    (jsp87OrbitWindow N : Set ℝ) = jsp87OrbitRange := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact ⟨k, rfl⟩
  · intro hx
    rcases jsp87_orbitRange_subset_window ht hper hx with ⟨k, hk, hxk⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hxk.symm⟩

/-! ## 7.  Unboundedly many orbit points force irrationality -/

/-- **THE COUNTING CRITERION.**  If the doubling orbit of the carries takes
unboundedly many distinct values then `jsp87Series` is irrational: a finite image
would give a period (round 64), and a period gives a *uniform bound* `M + t` on
the counting function (contradiction). -/
theorem jsp87Series_irrational_of_orbitCount_unbounded
    (h : ∀ K, ∃ N, K < jsp87OrbitCount N) : Irrational jsp87Series := by
  refine jsp87Series_irrational_iff_fracCarry_notPeriodic.mpr ?_
  rintro ⟨t, M, ht, hM, hper⟩
  obtain ⟨K, hK⟩ := h (M + t)
  exact absurd hK (not_lt_of_ge (jsp87_orbitCount_le_of_periodic ht hper K))

/-- **The contrapositive, in the form the previous rounds use:** a rational value
of the series forces the counting function of the orbit to be *bounded*. -/
theorem jsp87Series_rational_imp_orbitCount_bounded {a : ℤ} {b : ℕ} (hb : 0 < b)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ K, ∀ N, jsp87OrbitCount N ≤ K :=
  ⟨b, fun N => jsp87_orbitCount_le_denominator hb hS N⟩

end JSP87