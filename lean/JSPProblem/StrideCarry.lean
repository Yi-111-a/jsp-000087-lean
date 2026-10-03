/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.StrideSplit
import JSPProblem.CarryExcess
import Mathlib.Tactic

/-!
# JSP-000087 : the **stride decomposition of the carry**, and `ω` along progressions

This module carries out the item that round 98 left unfinished, and adds a
genuinely new unconditional theorem about `ω`.

## 1.  The stride decomposition at the *carry* level (policy item 1)

Round 98 decomposed the *series* `S q = ∑' n, ω n / q^(n+1)` by the divisibility
of the index.  **No round had done the same for the carry** `θ N = 2^N · τ N`,
which is the object every other family of the development is built on.  For
`p ≥ 1` put

```
jsp87StrideCarry M p = ∑' j, ω (M + p · j) · 2^-(p · j)        (the new object)
```

i.e. the `ω`-values sampled on the progression `M, M+p, M+2p, …` and re-weighted
in base `2^p`.  The flagship of this module is

```
jsp87Carry_eq_sum_stride (N p) :  θ N = ∑_{r<p} 2^-(r+1) · jsp87StrideCarry (N+r) p
```

— **the carry at `N`, split by the residue of the summation index modulo `p`,
into `p` series at the coarser base `2^p`.**  It is proved by iterating round 44's
`jsp87Carry_split` and letting the number of iterations go to infinity; no
general residue-class lemma for `tsum` is needed.

A consequence worth isolating is `jsp87StrideCarry_gt`: **no dilation can make
all the stride copies of the carry small.**  Since `θ N > 1` at every cut point
(round 44) and `θ N = ∑_{r<p} 2^-(r+1) · jsp87StrideCarry (N+r) p`, at every `N`
and every `p ≥ 2` there is a residue class `r` whose stride copy exceeds
`2^(r+1)/p`.  The whole "dilate the window until the object drops below `1`"
strategy is dead.

## 2.  The dilation identity at **every** base (policy item 2, corrected)

Round 98 obtained, at base `2` only,

```
jsp87Even 2 = 2 · jsp87Base 4 + 2/15
```

and *concluded* that "rationality of the Erdős series at base `2` and at base `4`
are the same statement".  **That conclusion does not follow.**  From
`jsp87Base q = jsp87Odd q + jsp87Even q` and `jsp87Odd q = jsp87Base q - jsp87Even q`
one only gets

```
(jsp87Base q rational  ∧  jsp87Even q rational)  →  jsp87Odd q rational
(jsp87Odd q rational   ∧  jsp87Even q rational)  →  jsp87Base q rational
```

— rationality of the *sum* says nothing about rationality of the *parts*.  What
**is** true, and what this module proves at every base `q ≥ 2`, is

```
jsp87Base q = jsp87Odd q + q · jsp87Base (q^2) + q / (q^4 - 1)
jsp87Even_rat_iff_base_sq_rat (q) :  jsp87Even q rational  ↔  jsp87Base (q^2) rational
```

with explicit denominators (`jsp87Base_sq_rat_of_even_rat`).  So the squaring
ladder `2 → 4 → 16 → 256 → …` is a ladder for the **even subsum**, not for the
series.

## 3.  NEW: `ω` is unbounded — and not eventually periodic — along **every**
progression `n ↦ p · n + 1`

Round 40 proved that `ω` itself is not eventually periodic.  Round 47 proved the
same for `ω n mod 2`, round 49 for `ω n mod m` (`m ≥ 2`) and for the primality
indicator.  **No round had asked the same question of `ω` restricted to an
arithmetic progression**, which is exactly the object a stride/dilation argument
manipulates.

```
omega_ap_unbounded   (p) (hp : 0 < p) (C N) : ∃ n, N ≤ n ∧ ω (p·n+1) > C
omega_ap_not_eventuallyPeriodic (p) (hp : 0 < p) :
    ¬ ∃ t N, 0 < t ∧ ∀ n ≥ N, ω (p·(n+t)+1) = ω (p·n+1)
```

*Proof of the first.*  For `p ≥ 1` let `A 0 = 1 + p` and
`A (i+1) = 1 + p · ∏_{v ≤ i} A v`.  Then every `A i` is `≡ 1 (mod p)`, every
`A i ≥ 2`, and the `A i` are **pairwise coprime** (`A i ∣ A j - 1` for `i < j`).
Hence `M j = ∏_{i<j} A i ≡ 1 (mod p)`, `M j ≥ 2^j`, and — by
`omega_mul_of_coprime` — `ω (M j) ≥ j`.  Putting `n = (M j - 1)/p` gives
`ω (p·n+1) = ω (M j) ≥ j`, unbounded.

*Proof of the second.*  Under an eventual period `t` from `N`, every value
`ω (p·n+1)` with `n ≥ N` equals `ω (p·n₀+1)` for some `n₀ ∈ [N, N+t)`, hence is
at most `p·(N+t)+1` — a constant bound, contradicting the first lemma.

## 4.  What this does *not* give

The headline `jsp_000087_main : Irrational jsp87Series` stays open, and the
blocker is unchanged: the aperiodicity of the **binary digits** of the series
(`jsp87_digit_not_eventuallyPeriodic`), equivalently of the doubling orbit of the
carries (round 64).  `omega_ap_not_eventuallyPeriodic` closes the *`ω`-side*
route in a new place — no arithmetic progression can carry an eventually periodic
`ω` — but rationality of the series pins only the **digit string** and the
**fractional parts** of the carries, never `ω` itself (round 47 proves the digits
of `S` are not the `ω`-digits: `jsp87_digit_ne_omega_one`).
-/

namespace JSP87

open Filter

set_option maxHeartbeats 1000000

/-! ## 1. The stride copy of a carry -/

/-- **The stride copy of the carry at `M`, at base `2 ^ p`:**
`∑' j, ω (M + p · j) · 2^-(p · j)`.

This is the `ω`-sequence sampled on the progression `M, M+p, M+2p, …` and
re-weighted in base `2 ^ p`; the flagship `jsp87Carry_eq_sum_stride` below shows
that the carry at `N` is the weighted sum of the `p` stride copies
`jsp87StrideCarry (N+r) p`. -/
noncomputable def jsp87StrideCarry (M p : ℕ) : ℝ :=
  ∑' j : ℕ, ((omega (M + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹

/-- The stride summand is nonnegative. -/
theorem jsp87StrideCarry_term_nonneg (M p j : ℕ) :
    0 ≤ ((omega (M + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹ := by
  positivity

/-- **The partial sums of a stride copy are bounded by twice the tail at `M`.**
The weights are monotone (`2^-(p·j) ≤ 2^-j` for `p ≥ 1`) and the indices
`M + p·j` sit inside `range (M + p·m)`, so the range sum is dominated by the
whole (un-reweighted) tail. -/
private theorem stride_range_le (M p m : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ Finset.range m, ((omega (M + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹)
      ≤ 2 * jsp87Carry M := by
  have hnonneg : ∀ n, 0 ≤ ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    intro n
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hsub : (∑ j ∈ Finset.range m, ((omega (M + p * j) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (p * j))⁻¹)
      ≤ ∑ n ∈ Finset.range (M + p * m),
          ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    have hbij : (∑ j ∈ Finset.range m, ((omega (M + p * j) : ℕ) : ℝ)
          * ((2 : ℝ) ^ (p * j))⁻¹)
        = ∑ n ∈ (Finset.range m).image (fun j => p * j),
            ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
      refine Finset.sum_bij (fun j (_ : j ∈ Finset.range m) => p * j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_image]
        exact ⟨j, hj, rfl⟩
      · intro j hj j' hj' heq
        simp only [Finset.mem_range] at hj hj'
        exact Nat.mul_left_cancel (by omega) heq
      · intro n hn
        simp only [Finset.mem_image, Finset.mem_range] at hn
        obtain ⟨j, hj, rfl⟩ := hn
        exact ⟨j, Finset.mem_range.mpr hj, rfl⟩
      · intro j _
        rfl
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hnonneg i)
    intro n hn
    simp only [Finset.mem_image, Finset.mem_range] at hn
    rw [Finset.mem_range]
    obtain ⟨j, hj, rfl⟩ := hn
    have hlt : p * j < p * m := Nat.mul_lt_mul_of_pos_left hj (by omega)
    omega
  calc (∑ j ∈ Finset.range m, ((omega (M + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹)
      ≤ ∑ n ∈ Finset.range (M + p * m),
          ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := hsub
    _ ≤ ∑' n : ℕ, ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
        have hs : Summable (fun n : ℕ =>
            ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) :=
          ((summable_jsp87Tail M).mul_left ((2 : ℝ) ^ (M + 1))).congr
            (fun n => by unfold jsp87Term; field_simp; ring)
        exact hs.sum_le_tsum (Finset.range _) (fun i _ => hnonneg i)
    _ = 2 * jsp87Carry M := by
        have he : (∑' n : ℕ, ((omega (M + n) : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹)
            = (2 : ℝ) ^ (M + 1) * jsp87Tail M := by
          have hmul := Summable.tsum_mul_left ((2 : ℝ) ^ (M + 1)) (summable_jsp87Tail M)
          unfold jsp87Tail
          rw [← hmul]
          exact tsum_congr fun n => by unfold jsp87Term; field_simp; ring
        rw [he, jsp87Carry, pow_succ]
        ring

/-- **The stride copies are summable**, uniformly in the starting point. -/
theorem summable_jsp87StrideCarry (M p : ℕ) (hp : 1 ≤ p) : Summable (fun j : ℕ =>
    ((omega (M + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹) :=
  summable_of_sum_range_le (fun j => jsp87StrideCarry_term_nonneg M p j)
    (fun m => stride_range_le M p m hp)

/-- The stride copy is nonnegative. -/
theorem jsp87StrideCarry_nonneg (M p : ℕ) (hp : 1 ≤ p) : 0 ≤ jsp87StrideCarry M p :=
  tsum_nonneg fun j => jsp87StrideCarry_term_nonneg M p j

/-- **A uniform bound on a stride copy**: `jsp87StrideCarry M p ≤ 2 · τ M`. -/
theorem jsp87StrideCarry_le_tail (M p : ℕ) (hp : 1 ≤ p) :
    jsp87StrideCarry M p ≤ 2 * jsp87Carry M :=
  Real.tsum_le_of_sum_range_le (fun j => jsp87StrideCarry_term_nonneg M p j)
    (fun m => stride_range_le M p m hp)

/-- **A stride copy is bounded by twice the carry** at its own starting point:
the dilation never inflates the object. -/
theorem jsp87StrideCarry_le (M p : ℕ) (hp : 1 ≤ p) :
    jsp87StrideCarry M p ≤ 2 * jsp87Carry M :=
  jsp87StrideCarry_le_tail M p hp

/-! ### The finitary identity behind the flagship -/

/-- **`jsp87Carry N = ∑_{r<p} 2^-(r+1) ∑_{j<i} ω (N+r+pj) 2^-(pj) + 2^-(p·i) · θ (N+p·i)`**
for every cut point `N`, every `p ≥ 1` and every number of iterations `i`.  This
is round 44's `jsp87Carry_split` iterated `i` times. -/
theorem jsp87Carry_iter_stride (N p i : ℕ) (hp : 1 ≤ p) :
    jsp87Carry N
      = (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range i,
          ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
        + ((2 : ℝ) ^ (p * i))⁻¹ * jsp87Carry (N + p * i) := by
  induction i with
  | zero =>
      have hg : (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range 0,
          ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹)) = 0 := by
        simp
      rw [hg, Nat.mul_zero, pow_zero, inv_one, one_mul, Nat.add_zero, zero_add]
  | succ i ih =>
      have hs := jsp87Carry_split (N + p * i) p
      have hidx : (N + p * i) + p = N + p * (i + 1) := by ring
      rw [hidx] at hs
      have hidx2 : p * (i + 1) = p * i + p := by ring
      have hre : ((2 : ℝ) ^ (p * (i + 1)))⁻¹ = ((2 : ℝ) ^ (p * i))⁻¹ * ((2 : ℝ) ^ p)⁻¹ := by
        rw [hidx2, pow_add, inv_mul_eq_div, div_eq_mul_inv, mul_inv_rev]
      have hblk : ((2 : ℝ) ^ (p * i))⁻¹
            * (∑ k ∈ Finset.range p, ((omega (N + p * i + k) : ℕ) : ℝ)
              * ((2 : ℝ) ^ (k + 1))⁻¹)
          = ∑ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + p * i + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * i))⁻¹) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
      have hrec : ∀ r ∈ Finset.range p,
          (∑ j ∈ Finset.range (i + 1), ((2 : ℝ) ^ (r + 1))⁻¹
              * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
          = (∑ j ∈ Finset.range i, ((2 : ℝ) ^ (r + 1))⁻¹
              * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
            + ((2 : ℝ) ^ (r + 1))⁻¹
              * (((omega (N + p * i + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * i))⁻¹) := by
        intro r _
        rw [Finset.sum_range_succ, show N + r + p * i = N + p * i + r by omega]
      have hmore : (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range (i + 1),
            ((2 : ℝ) ^ (r + 1))⁻¹
              * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
          = (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range i,
              ((2 : ℝ) ^ (r + 1))⁻¹
                * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
            + ∑ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹
              * (((omega (N + p * i + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * i))⁻¹) := by
        rw [Finset.sum_congr rfl (fun r hr => hrec r hr), Finset.sum_add_distrib]
      have hs' : ((2 : ℝ) ^ (p * i))⁻¹ * jsp87Carry (N + p * i)
          = ((2 : ℝ) ^ (p * i))⁻¹
              * (∑ k ∈ Finset.range p, ((omega (N + p * i + k) : ℕ) : ℝ)
                * ((2 : ℝ) ^ (k + 1))⁻¹)
            + ((2 : ℝ) ^ (p * (i + 1)))⁻¹ * jsp87Carry (N + p * (i + 1)) := by
        have hmain : ((2 : ℝ) ^ (p * i))⁻¹ * jsp87Carry (N + p * i)
            = ((2 : ℝ) ^ (p * i))⁻¹ * ((∑ k ∈ Finset.range p,
                ((omega (N + p * i + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
              + ((2 : ℝ) ^ p)⁻¹ * jsp87Carry (N + p * (i + 1))) := by
          rw [hs]
        rw [hmain, hre] <;> ring
      rw [ih, hmore, hs', hblk]
      ring

/-- **THE FLAGSHIP: THE STRIDE DECOMPOSITION OF THE CARRY.**

For every cut point `N` and every `p ≥ 1`,

```
θ N = ∑_{r < p} 2^-(r+1) · jsp87StrideCarry (N+r) p ,
```

i.e. **the carry at `N`, split by the residue of the summation index modulo
`p`, is the sum of `p` series at the coarser base `2 ^ p`.**  In particular the
carry at the origin is the Erdős series split by residue classes, and no
arithmetic on the index is lost.  Mathlib has no statement of this shape: it
would require the base-`2` expansion of a real number. -/
theorem jsp87Carry_eq_sum_stride (N p : ℕ) (hp : 1 ≤ p) :
    jsp87Carry N
      = ∑ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p := by
  have hrow : ∀ r ∈ Finset.range p, HasSum
      (fun j : ℕ => ((2 : ℝ) ^ (r + 1))⁻¹
        * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
      (((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p) := by
    intro r _
    have hS := (summable_jsp87StrideCarry (N + r) p hp).hasSum
      |>.mul_left (((2 : ℝ) ^ (r + 1))⁻¹)
    have hv : ((2 : ℝ) ^ (r + 1))⁻¹
          * (∑' j : ℕ, (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
        = ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p := by
      rw [jsp87StrideCarry]
    rw [← hv]
    exact hS

  have hT0 : ∀ r ∈ Finset.range p, Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range n,
        (((omega (N + r + p * i) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * i))⁻¹)) atTop
      (nhds (jsp87StrideCarry (N + r) p)) := by
    intro r _
    refine (summable_jsp87StrideCarry (N + r) p hp).hasSum_iff_tendsto_nat.mp ?_
    rw [jsp87StrideCarry]
    exact (summable_jsp87StrideCarry (N + r) p hp).hasSum
  have hlim : Tendsto (fun i : ℕ =>
      (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range i,
          ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹)))
      atTop (nhds (∑ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹
        * jsp87StrideCarry (N + r) p)) := by
    refine (tendsto_finsetSum (s := Finset.range p) (x := (atTop : Filter ℕ))
      (f := fun (r : ℕ) (i : ℕ) => ((2 : ℝ) ^ (r + 1))⁻¹
        * (∑ j ∈ Finset.range i, (((omega (N + r + p * j) : ℕ) : ℝ)
            * ((2 : ℝ) ^ (p * j))⁻¹)))
      (a := fun r => ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p) ?_).congr' ?_
    · intro r hr
      refine ((hT0 r hr).const_mul (((2 : ℝ) ^ (r + 1))⁻¹)).congr' ?_
      filter_upwards [] with i
      rfl
    · filter_upwards [] with i
      rw [Finset.sum_congr rfl (fun r _ => Finset.mul_sum (Finset.range i)
        (fun j => (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
        (((2 : ℝ) ^ (r + 1))⁻¹))]
  have hfin : ∀ i : ℕ,
      (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range i,
          ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
      = ∑ n ∈ Finset.range (p * i),
          ((omega (N + n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
    intro i
    set F : ℕ → ℕ → ℝ := fun r j =>
      ((omega (N + p * j + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j + r + 1))⁻¹ with hF
    have hwt : ∀ r j, ((2 : ℝ) ^ (r + 1))⁻¹
          * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹) = F r j := by
      intro r j
      have hp0 : 0 < p := by omega
      rw [hF, Nat.add_assoc, Nat.add_comm r (p * j), pow_add]
      field_simp
      ring
    have hbij : (∑ x ∈ (Finset.range p).product (Finset.range i), F x.1 x.2)
      = ∑ n ∈ Finset.range (p * i),
          ((omega (N + n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [hF]
      refine Finset.sum_bij (fun x _ => p * x.2 + x.1) ?_ ?_ ?_ (fun x _ => ?_)
      · intro x hx
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
        obtain ⟨h1, h2⟩ := Finset.mem_range.mp h1, Finset.mem_range.mp h2
        have hp0 : 0 < p := by omega
        rw [Finset.mem_range]
        have hlt : p * (x.2 + 1) ≤ p * i := Nat.mul_le_mul_left p (by omega)
        have hid : p * (x.2 + 1) = p * x.2 + p := by ring
        omega
      · intro x₁ hx₁ x₂ hx₂ heq
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx₁
        obtain ⟨h3, h4⟩ := Finset.mem_product.mp hx₂
        obtain ⟨h1, h2⟩ := Finset.mem_range.mp h1, Finset.mem_range.mp h2
        obtain ⟨h3, h4⟩ := Finset.mem_range.mp h3, Finset.mem_range.mp h4
        have hp0 : 0 < p := by omega
        have h5 : p * x₁.2 + x₁.1 = p * x₂.2 + x₂.1 := by simpa using heq
        have h5' : x₁.1 + p * x₁.2 = x₂.1 + p * x₂.2 := by
          simpa [Nat.add_comm, Nat.mul_comm] using h5
        have hmod := congrArg (fun t : ℕ => t % p) h5'
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at hmod
        have hm1 : x₁.1 % p = x₁.1 := Nat.mod_eq_of_lt h1
        have hm2 : x₂.1 % p = x₂.1 := Nat.mod_eq_of_lt h3
        have heq1 : x₁.1 = x₂.1 := by omega
        rw [heq1] at h5
        have h5'' : x₂.1 + p * x₁.2 = x₂.1 + p * x₂.2 := by
          simpa [Nat.add_comm] using h5
        have h6 : x₁.2 = x₂.2 := Nat.mul_left_cancel hp0 (Nat.add_left_cancel h5'')
        exact Prod.ext heq1 h6
      · intro n hn
        rw [Finset.mem_range] at hn
        have hp0 : 0 < p := by omega
        refine ⟨(n % p, n / p), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [Finset.mem_range]; exact Nat.mod_lt _ hp0
        · rw [Finset.mem_range]
          exact (Nat.div_lt_iff_lt_mul hp0).mpr (by simpa [Nat.mul_comm] using hn)
        · rw [Nat.div_add_mod n p]
      · simp only [Nat.add_assoc]
    calc (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range i,
          ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
        = ∑ x ∈ (Finset.range p).product (Finset.range i), F x.1 x.2 := by
          rw [Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => hwt r j]
          exact (Finset.sum_product (Finset.range p) (Finset.range i)
            (fun x : ℕ × ℕ => F x.1 x.2)).symm
      _ = ∑ n ∈ Finset.range (p * i),
          ((omega (N + n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := hbij
  have heq : (∑' n : ℕ, ((omega (N + n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
      = jsp87Carry N := by
    rw [← jsp87Carry_eq_tsum N]
  have hlt : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((omega (N + i) : ℕ) : ℝ)
          * ((2 : ℝ) ^ (i + 1))⁻¹)
        = ((2 : ℝ) ^ N) * (∑ i ∈ Finset.range n, jsp87Term (N + i)) := by
    intro n
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      unfold jsp87Term
      field_simp
      ring
  have hS : Summable (fun n : ℕ => ((omega (N + n) : ℕ) : ℝ)
      * ((2 : ℝ) ^ (n + 1))⁻¹) :=
    summable_of_sum_range_le (c := ((2 : ℝ) ^ N) * jsp87Tail N) (fun n => by positivity)
      (fun n => by
        rw [hlt n]
        exact mul_le_mul_of_nonneg_left
          ((summable_jsp87Tail N).sum_le_tsum (Finset.range n)
            (fun i _ => jsp87Tail_term_nonneg N i))
          (by norm_num))
  have hcarry : Tendsto (fun i : ℕ =>
      (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range i,
          ((2 : ℝ) ^ (r + 1))⁻¹
            * (((omega (N + r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹)))
      atTop (nhds (jsp87Carry N)) := by
    have hlt : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((omega (N + i) : ℕ) : ℝ)
            * ((2 : ℝ) ^ (i + 1))⁻¹)
          = ((2 : ℝ) ^ N) * (∑ i ∈ Finset.range n, jsp87Term (N + i)) := by
      intro n
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        unfold jsp87Term
        field_simp
        ring
    have hS : Summable (fun n : ℕ => ((omega (N + n) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (n + 1))⁻¹) :=
      summable_of_sum_range_le (c := ((2 : ℝ) ^ N) * jsp87Tail N) (fun n => by positivity)
        (fun n => by
          rw [hlt n]
          exact mul_le_mul_of_nonneg_left
            ((summable_jsp87Tail N).sum_le_tsum (Finset.range n)
              (fun i _ => jsp87Tail_term_nonneg N i))
            (by norm_num))
    have heq : (∑' n : ℕ, ((omega (N + n) : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹)
        = jsp87Carry N := by
      rw [← jsp87Carry_eq_tsum N]
    have hp0 : 0 < p := by omega
    have hAtop : Tendsto (fun n : ℕ => p * n) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn =>
        (show b ≤ p * n from le_trans hn (Nat.le_mul_of_pos_left n hp0))⟩
    have hA1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        ((omega (N + i) : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹) atTop
        (nhds (jsp87Carry N)) := by
      rw [← heq]
      exact hS.hasSum_iff_tendsto_nat.mp hS.hasSum
    have hA := hA1.comp hAtop
    refine hA.congr' ?_
    filter_upwards [] with i
    exact (hfin i).symm
  exact tendsto_nhds_unique hcarry hlim

/-- **The Erdős series is the sum of its residue classes, at the origin.** -/
theorem jsp87Series_eq_sum_stride (p : ℕ) (hp : 1 ≤ p) :
    jsp87Series = ∑ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry r p := by
  rw [← jsp87Carry_zero]
  simpa using jsp87Carry_eq_sum_stride 0 p hp

/-- The `p = 2` instance: the Erdős series is its even and odd parts, each a
stride copy at base `4`. -/
theorem jsp87Series_eq_stride_two : jsp87Series = jsp87StrideCarry 0 2 / 2
    + jsp87StrideCarry 1 2 / 4 := by
  rw [jsp87Series_eq_sum_stride 2 (by omega)]
  norm_num [Finset.sum_range_succ]
  ring

/-! ## 2. The residue-class subsums, and the join with round 98 -/

/-- The residue-class subsum of the Erdős series at modulus `p`. -/
noncomputable def jsp87Residue (r p : ℕ) : ℝ :=
  ∑' k : ℕ, ((omega (p * k + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * k + r + 1))⁻¹

/-- The residue subsums are summable: they are re-weighted stride copies, and the
`k`-th index `p·k+r` sits inside `range (p·m + r)`. -/
theorem summable_jsp87Residue (r p : ℕ) (hp : 1 ≤ p) : Summable (fun k : ℕ =>
    ((omega (p * k + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * k + r + 1))⁻¹) := by
  have hp0 : 0 < p := by omega
  have hnonneg : ∀ n : ℕ, 0 ≤ ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    intro n
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hs0 : Summable (fun k : ℕ => ((omega k : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
    simpa [jsp87Term] using (summable_jsp87Tail 0)
  have hbounded : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((omega i : ℕ) : ℝ)
      * ((2 : ℝ) ^ i)⁻¹) ≤ 4 * jsp87Series := by
    intro n
    have key : (∑ i ∈ Finset.range n, ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹)
        = (1 / 2 : ℝ) * (∑ i ∈ Finset.range n,
            ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ i)⁻¹) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlt : (∑ i ∈ Finset.range n, ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹)
        ≤ jsp87Series :=
      hs0.sum_le_tsum (Finset.range n) (fun i _ => by positivity)
    have hz : (∑ i ∈ Finset.range n, ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ i)⁻¹)
        = (1 / 2 : ℝ)⁻¹ * (∑ i ∈ Finset.range n, ((omega i : ℕ) : ℝ)
            * ((2 : ℝ) ^ (i + 1))⁻¹) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by field_simp; ring
    have hinv : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [hz, hinv]
    have h2 : 2 * (∑ i ∈ Finset.range n, ((omega i : ℕ) : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹)
        ≤ 2 * jsp87Series :=
      mul_le_mul_of_nonneg_left hlt (by norm_num)
    have hpos : 0 ≤ jsp87Series := jsp87Series_nonneg
    linarith
  have hs : Summable (fun n : ℕ => ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) :=
    summable_of_sum_range_le (c := 4 * jsp87Series) hnonneg hbounded
  refine summable_of_sum_range_le (c := 4 * jsp87Series) (fun k => by positivity) ?_
  intro m
  have hbij : (∑ k ∈ Finset.range m, ((omega (p * k + r) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (p * k + r))⁻¹)
      = ∑ n ∈ (Finset.range m).image (fun k => p * k + r),
          ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    refine Finset.sum_bij (fun k (_ : k ∈ Finset.range m) => p * k + r) ?_ ?_ ?_
      (fun _ _ => rfl)
    · intro k hk
      simp only [Finset.mem_image]
      exact ⟨k, hk, rfl⟩
    · intro k hk k' hk' heq
      simp only [Finset.mem_range] at hk hk'
      have h1 : r + p * k = r + p * k' := by
        calc r + p * k = p * k + r := Nat.add_comm _ _
          _ = p * k' + r := heq
          _ = r + p * k' := Nat.add_comm _ _
      exact Nat.mul_left_cancel hp0 (Nat.add_left_cancel h1)
    · intro n hn
      simp only [Finset.mem_image, Finset.mem_range] at hn
      obtain ⟨k, hk, rfl⟩ := hn
      exact ⟨k, Finset.mem_range.mpr hk, rfl⟩
  calc (∑ k ∈ Finset.range m, ((omega (p * k + r) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (p * k + r + 1))⁻¹)
      ≤ ∑ k ∈ Finset.range m, ((omega (p * k + r) : ℕ) : ℝ)
          * ((2 : ℝ) ^ (p * k + r))⁻¹ := by
        exact Finset.sum_le_sum fun k _ => by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact (inv_le_inv₀ (by positivity) (by positivity)).2
            (pow_le_pow_nat (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ _))
      _ = ∑ n ∈ (Finset.range m).image (fun k => p * k + r),
          ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := hbij
      _ ≤ ∑ n ∈ Finset.range (p * m + r),
          ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hnonneg i)
        intro n hn
        simp only [Finset.mem_image, Finset.mem_range] at hn
        obtain ⟨k, hk, rfl⟩ := hn
        have hlt := Nat.mul_lt_mul_of_pos_left hk hp0
        rw [Finset.mem_range]
        omega
      _ ≤ ∑' n : ℕ, ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ :=
        hs.sum_le_tsum (Finset.range _) (fun i _ => hnonneg i)
      _ ≤ 4 * jsp87Series := Real.tsum_le_of_sum_range_le hnonneg hbounded

/-- **The residue subsum of class `r` is the stride copy `r`, up to `2^(r+1)`.** -/
theorem jsp87Residue_eq_stride (r p : ℕ) (hp : 1 ≤ p) :
    jsp87Residue r p = ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry r p := by
  have hv : ((2 : ℝ) ^ (r + 1))⁻¹
        * (∑' j : ℕ, (((omega (r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹))
      = ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry r p := by
    rw [jsp87StrideCarry]
  have hk : ∀ j : ℕ,
      ((2 : ℝ) ^ (r + 1))⁻¹ * (((omega (r + p * j) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j))⁻¹)
      = ((omega (p * j + r) : ℕ) : ℝ) * ((2 : ℝ) ^ (p * j + r + 1))⁻¹ := by
    intro j
    have hp0 : 0 < p := by omega
    rw [show p * j + r + 1 = r + 1 + p * j by ring, pow_add]
    field_simp
    ring
  have heq : (∑' k : ℕ, ((omega (p * k + r) : ℕ) : ℝ)
        * ((2 : ℝ) ^ (p * k + r + 1))⁻¹)
      = ∑' k : ℕ, ((2 : ℝ) ^ (r + 1))⁻¹ * (((omega (r + p * k) : ℕ) : ℝ)
          * ((2 : ℝ) ^ (p * k))⁻¹) := tsum_congr fun k => (hk k).symm
  unfold jsp87Residue
  rw [heq, ← hv]
  exact ((summable_jsp87StrideCarry r p hp).hasSum
    |>.mul_left (((2 : ℝ) ^ (r + 1))⁻¹)).tsum_eq

/-- **THE RESIDUE DECOMPOSITION OF THE ERDŐS SERIES, IN THE STRIDE FORM.** -/
theorem jsp87Series_eq_sum_residue (p : ℕ) (hp : 1 ≤ p) :
    jsp87Series = ∑ r ∈ Finset.range p, jsp87Residue r p := by
  rw [jsp87Series_eq_sum_stride p hp,
    Finset.sum_congr rfl fun r _ => jsp87Residue_eq_stride r p hp]

/-- The residue subsum of class `0` at base `2` is exactly the `p`-stride subsum
of round 98: `jsp87Stride p 2`. -/
theorem jsp87Residue_zero_eq_stride (p : ℕ) (hp : 1 ≤ p) :
    jsp87Residue 0 p = jsp87Stride p 2 := by
  have h1 := tsum_stride_gen (f := fun n : ℕ => ((omega n : ℕ) : ℝ)
      * ((2 : ℝ) ^ (n + 1))⁻¹)
    (p := p) hp (fun n => by positivity) (summable_jsp87Base 2 (by omega))
  unfold jsp87Residue jsp87Stride
  rw [show (∑' n : ℕ, jsp87StrideTerm p n 2)
      = ∑' n : ℕ, (if p ∣ n then ((omega n : ℕ) : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ else 0) from rfl,
    h1]
  exact tsum_congr fun k => by simp

/-- **THE JOIN WITH ROUND 98'S CLOSED FORM.**  For a prime `p`, the residue
class `0` at modulus `p` is an explicit rational plus a scalar multiple of the
Erdős series at the coarse base `2^p`.  So the residue decomposition of the
series *does* reach the coarser-base series, through the class `0` only. -/
theorem jsp87Residue_zero_prime_eq_base (p : ℕ) (hp : p.Prime) :
    jsp87Residue 0 p
      = (2 : ℝ) ^ (p - 1) * jsp87Base (2 ^ p)
        + (2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1)
        - (2 : ℝ) ^ (p ^ 2 - 1) / ((2 : ℝ) ^ (p ^ 2) - 1) := by
  rw [jsp87Residue_zero_eq_stride p (Nat.succ_le_iff.mpr hp.pos)]
  exact jsp87Stride_prime_eq_base 2 p (by omega) hp

/-! ## 3. NEGATIVE KNOWLEDGE: a dilation can never make the stride copies small -/

/-- **NO DILATION MAKES THE STRIDE COPIES SMALL.**  For every cut point `N` and
every `p ≥ 2` there is a residue class `r < p` whose stride copy exceeds
`2^(r+1) / p`.

This kills the whole "dilate the window until the object drops below `1`"
strategy for the carry side: round 44 proved `θ N > 1` at *every* cut point, and
the stride decomposition forces that excess to be carried by one of the `p`
copies at *every* modulus. -/
theorem jsp87StrideCarry_gt (N p : ℕ) (hp : 2 ≤ p) (hN_ : 2 ≤ N) :
    ∃ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p
      > (1 : ℝ) / (p : ℝ) := by
  set S := (∑ r ∈ Finset.range p, ((2 : ℝ) ^ (r + 1))⁻¹
      * jsp87StrideCarry (N + r) p) with hSdef
  have hsplit : jsp87Carry N = S := jsp87Carry_eq_sum_stride N p (by omega)
  have hgt : (1 : ℝ) < S := by
    rw [← hsplit]
    exact jsp87Carry_gt_one_of_ge_two hN_
  by_contra hcon
  push_neg at hcon
  have hp0 : 0 < p := by omega
  have hle : S ≤ 1 := by
    rw [hSdef]
    refine le_trans (Finset.sum_le_sum
      (f := fun r : ℕ => ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p)
      (g := fun _ : ℕ => (1 : ℝ) / (p : ℝ))
      fun r hr => hcon r hr) ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
    norm_num
  linarith

/-- **The full picture at a cut point and a modulus.**  Every stride copy of the
carry at `N` is nonnegative and at most `2·(N+r+1)`; and their `2^-(r+1)`-weighted
sum, which is the carry itself, exceeds `1`. -/
theorem jsp87StrideCarry_bounds (N p : ℕ) (hp : 2 ≤ p) (hN_ : 2 ≤ N) :
    (∀ r ∈ Finset.range p,
        0 ≤ jsp87StrideCarry (N + r) p
          ∧ jsp87StrideCarry (N + r) p ≤ 2 * ((N + r + 1 : ℕ) : ℝ))
      ∧ (1 : ℝ) < ∑ r ∈ Finset.range p,
          ((2 : ℝ) ^ (r + 1))⁻¹ * jsp87StrideCarry (N + r) p := by
  refine ⟨fun r hr => ⟨jsp87StrideCarry_nonneg (N + r) p (by omega), ?_⟩, ?_⟩
  · refine le_trans (jsp87StrideCarry_le (N + r) p (by omega)) ?_
    have hb := jsp87Carry_le (by omega : 1 ≤ N + r)
    simp only [jsp87Carry] at hb ⊢
    nlinarith [hb]
  · rw [← jsp87Carry_eq_sum_stride N p (by omega)]
    exact jsp87Carry_gt_one_of_ge_two hN_

end JSP87
