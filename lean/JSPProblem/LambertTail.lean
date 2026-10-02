/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.LambertIdentity
import JSPProblem.Diophantine
import JSPProblem.DeltaMass

/-!
# JSP-000087 : the `ω`-tail at an arbitrary cut point IS a prime-Lambert series

## Why this file exists

`JSPProblem/LambertIdentity.lean` reduced the Erdős series to the *prime-restricted
Lambert series* at the **single** cut point `N = 0`:

`∑' n, ω(n) / 2^(n+1) = ∑' p, 1 / (2^p - 1)`.

Every later round worked with the `ω`-side of that identity (the carries, the
digits, the blocks, the cubes) or with the Lambert side only at `N = 0`.  **No
round had ever asked what the Lambert side looks like at an arbitrary cut
point** — which is exactly what an Erdős-style argument needs, because such an
argument *moves* the cut point and compares two of them.

This file closes that gap.

## THE MAIN RESULT

At the cut point `N` the part of the series lying to the right of `N` is the
rescaled tail `2^N · τ N = ∑' k ≥ 0, ω(N + k) · 2^-(k+1)`, and this file proves
the **exact closed form**

> **`2^N · τ N = ∑' p prime, 2^(e N p) / (2^p - 1)`,**
> `e N p = if p ∣ N then p - 1 else N mod p - 1`

(`jsp87Tail_eq_remSum`).  In words: **the `ω`-tail at the cut point `N` is the
prime-restricted Lambert series in which each Lambert term `1/(2^p - 1)` is
raised to the power `2^(N mod p)`** — the weight records the position of the
first multiple of `p` at or after the cut point.  This is the join of the two
sides of `JSPProblem/LambertIdentity.lean` at an *arbitrary* cut point.

## The single-prime value (`jsp87PrimeTail_eq`)

The heart of the file is the closed form of the contribution of one prime:

`∑' k, [p ∣ N + k] · 2^-(k+1) = 2^(e N p) / (2^p - 1)`.

The proof avoids any summation over an arithmetic progression (rounds 92–93
showed that reindexing a `tsum` along an AP is the obstacle that cost those
rounds their budget).  Instead it uses only

* the **first-order recurrence** `jsp87PrimeTail_succ`, which comes from
  `Summable.sum_add_tsum_nat_add` exactly as `jsp87Tail_succ` does;
* the **`p`-periodicity in the shift** `jsp87PrimeTail_add`, which is
  `tsum_congr` (`p ∣ N + a + p + j ↔ p ∣ N + a + j`);
* the **iteration** `jsp87PrimeTail_iter`, an elementary induction on the
  number of steps.

With those three, evaluating at `a = 0`, `L = p` closes a linear equation on
`T N` whose right-hand side is a *finite* sum over `j < p`, and the tree already
has the uniqueness lemma for exactly that finite sum
(`jsp87_dvd_add_index`, proved here from `jsp87_exists_dvd_add` of
`JSPProblem/DeltaMass.lean`).

## What else is proved

| Theorem | Statement |
| --- | --- |
| `jsp87PrimeTail_add` | the single-prime tail is `p`-periodic in the cut point |
| `jsp87PrimeTail_iter`, `jsp87PrimeTail_split` | the tail splits after one full period |
| `tsum_lamRemF_snd`, `tsum_lamRemF_fst` | the row and the column of the double sum over `(k, p)` |
| `jsp87RemExp_of_lt` | **above the cut point the residue exponent is the constant `N - 1`** |
| `jsp87RemSum_eq_tsumBig` | the large-prime half is `2^(N-1)` times a plain Lambert tail |
| `jsp87RemSumSml_zero` | the cut point `0` has no small-prime part |
| `jsp87RemTerm_pos`, `jsp87RemTerm_lt_one` | **every prime term lies strictly in `(0, 1)`** |
| `jsp87Series_rational_imp_remSum_int` | **the rationality transfer, on the Lambert side**: for a rational `a/b`, `b · jsp87RemSum N ∈ ℤ` for every `1 ≤ N` |

## Why this is not a reformulation of rounds 88–93

Rounds 88–93 built the window objects of Tao–Teräväinen (`W`, `W_p`, `δ_p`, the
Gowers cubes).  Round 90 itself recorded the negative result that those cubes
vanish for *every* function, so the cancellation they provide can never by
itself contradict rationality; and the `hsmall` hypothesis of
`jsp87Series_irrational_of_FCube_one_small` is **false** (it forces `W` to be
constant, while `jsp87Carry_succ` gives `W (n+1) = 2 W n - ω (n+1)` with `ω`
unbounded).  This file leaves that family alone and works on the **Lambert side
of the original reduction**, at arbitrary cut points, where every statement
below is unconditional and non-vacuous.
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 0. a geometric majorant -/

/-- `∑' n, 2^-(n+1)` is summable. -/
theorem summable_two_pow_neg_add_one : Summable (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹) := by
  have hxi : ‖((2 : ℝ)⁻¹ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by norm_num)
  have h : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) :=
    (hasSum_geometric_of_norm_lt_one (ξ := (2 : ℝ)⁻¹) hxi).summable
  have h' := h.mul_left (2 : ℝ)⁻¹
  refine Summable.congr h' fun n => ?_
  rw [two_pow_neg_eq, pow_succ]
  ring

/-- **A multiple of `p`, enlarged by `p`, is again a multiple of `p`.** -/
theorem jsp87_dvd_add_p {p x : ℕ} (h : p ∣ x) : p ∣ (x + p) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  subst hk
  ring

/-- **A multiple of `p`, diminished by `p`, is again a multiple of `p`.**  This
is what makes the tail of the prime `p` `p`-periodic in the cut point. -/
theorem jsp87_dvd_sub_p {p x : ℕ} (h : p ∣ (x + p)) : p ∣ x := by
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  have hmod : (x + p) % p = x % p := by
    rw [Nat.add_mod]
    simp
  omega

/-- `2^(-L) * 2^(-1) = 2^(-(L+1))`. -/
theorem jsp87_two_pow_inv_mul (L : ℕ) :
    ((2 : ℝ) ^ L)⁻¹ * (2 : ℝ)⁻¹ = ((2 : ℝ) ^ (L + 1))⁻¹ := by
  have h1 : (2 : ℝ) ^ L * (2 : ℝ) = (2 : ℝ) ^ (L + 1) := by
    rw [pow_add (a := (2 : ℝ)) L 1, pow_one]
  rw [← mul_inv]
  exact congrArg (fun z : ℝ => z⁻¹) h1

/-! ## 1. the residue exponent of a prime -/

/-- **The residue exponent** `e N p` of the prime `p` at the cut point `N`:
`p - 1` if `p` divides the cut point (the first multiple of `p` is `N` itself),
and `N mod p - 1` otherwise (the first multiple of `p` at or after `N` is
`N + (p - N mod p)`, so the exponent is `N mod p - 1`). -/
noncomputable def jsp87RemExp (N p : ℕ) : ℕ := if p ∣ N then p - 1 else N % p - 1

/-- The residue exponent never exceeds `p - 1`. -/
theorem jsp87RemExp_le (N p : ℕ) (hp : 1 ≤ p) : jsp87RemExp N p ≤ p - 1 := by
  by_cases hd : p ∣ N
  · rw [jsp87RemExp, if_pos hd]
  · rw [jsp87RemExp, if_neg hd]
    have hlt : N % p < p := Nat.mod_lt _ (by omega)
    omega

/-- The residue exponent is strictly below `p`. -/
theorem jsp87RemExp_lt (N p : ℕ) (hp : 1 ≤ p) : jsp87RemExp N p < p := by
  have := jsp87RemExp_le N p hp
  omega

/-- Above the cut point, the residue exponent is the **constant** `N - 1`. -/
theorem jsp87RemExp_of_lt (N p : ℕ) (hN : 1 ≤ N) (hp : N < p) :
    jsp87RemExp N p = N - 1 := by
  have hnd : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd hN h
    omega
  rw [jsp87RemExp, if_neg hnd, Nat.mod_eq_of_lt hp]

/-- **A positive multiple of `p` strictly below `2p` is `p` itself.** -/
theorem jsp87_mul_lt_two {p m x : ℕ} (_hp : 0 < p) (hm : x = p * m) (h0 : 0 < x) (h2 : x < 2 * p) :
    x = p := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm, hm0] at h0
    omega
  · by_cases hm1 : m = 1
    · rw [hm, hm1]
      simp
    · have hm2 : 2 ≤ m := by omega
      have hle : p * 2 ≤ p * m := Nat.mul_le_mul_left p hm2
      rw [← hm] at hle
      omega

/-- **THE INDEX OF THE FIRST MULTIPLE OF `p` AT OR AFTER `b`.**  If `b % p` is
positive, the unique index `j < p` with `p ∣ b + j` is `p - b % p`.  This is the
combinatorial content of the residue exponent `jsp87RemExp`. -/
theorem jsp87_dvd_add_index {b p : ℕ} (hbpos : 0 < b % p) {j : ℕ} (hlt : j < p)
    (hd : p ∣ b + j) : j = p - b % p := by
  have hmod2 : (b + j) % p = (b % p + j) % p := by rw [Nat.add_mod, Nat.mod_eq_of_lt hlt]
  have hzmod : (b % p + j) % p = 0 := by rw [← hmod2, Nat.dvd_iff_mod_eq_zero.mp hd]
  have hcong : p ∣ b % p + j := Nat.dvd_of_mod_eq_zero hzmod
  obtain ⟨m, hm⟩ := hcong
  have hblt : b % p < p := Nat.mod_lt b (by omega)
  have hpos : 0 < b % p + j := by omega
  have hlt2 : b % p + j < 2 * p := by
    have := Nat.add_lt_add hblt hlt
    omega
  have heq : b % p + j = p := jsp87_mul_lt_two (by omega) hm hpos hlt2
  omega

/-! ## 2. the tail of one prime -/

/-- **The Lambert tail of a single prime `p` at the cut point `N`**: the sum of
`2^-(k+1)` over those `k` for which `p` divides `N + k`. -/
noncomputable def jsp87PrimeTail (N p : ℕ) : ℝ :=
  ∑' k : ℕ, (if p ∣ N + k then ((2 : ℝ) ^ (k + 1))⁻¹ else 0)

/-- Every summand is nonnegative. -/
theorem jsp87PrimeTail_term_nonneg (N p k : ℕ) :
    0 ≤ (if p ∣ N + k then ((2 : ℝ) ^ (k + 1))⁻¹ else 0) := by
  split_ifs <;> positivity

/-- The single-prime tail is a convergent series. -/
theorem summable_jsp87PrimeTail (N p : ℕ) :
    Summable (fun k : ℕ => (if p ∣ N + k then ((2 : ℝ) ^ (k + 1))⁻¹ else 0)) :=
  Summable.of_nonneg_of_le (jsp87PrimeTail_term_nonneg N p)
    (fun k => by by_cases h : p ∣ N + k <;> simp [h]) summable_two_pow_neg_add_one

/-- **The first-order recurrence of the single-prime tail**: the tail at `N + a`
is the term at the cut point, plus the tail at `N + a + 1` discounted by `1/2`. -/
theorem jsp87PrimeTail_succ (N p a : ℕ) :
    jsp87PrimeTail (N + a) p
      = (if p ∣ N + a then (2 : ℝ)⁻¹ else 0) + (2 : ℝ)⁻¹ * jsp87PrimeTail (N + a + 1) p := by
  have hs := summable_jsp87PrimeTail (N + a) p
  have h := hs.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h
  have hstep : (∑' i : ℕ, (if p ∣ N + a + (i + 1) then ((2 : ℝ) ^ (i + 2))⁻¹ else 0))
      = (2 : ℝ)⁻¹ * jsp87PrimeTail (N + a + 1) p := by
    have hm : (2 : ℝ)⁻¹ * jsp87PrimeTail (N + a + 1) p
        = ∑' i : ℕ, (2 : ℝ)⁻¹ * (if p ∣ N + a + 1 + i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0) := by
      unfold jsp87PrimeTail
      exact (Summable.tsum_mul_left _ (summable_jsp87PrimeTail (N + a + 1) p)).symm
    rw [hm]
    have hcomm : ∀ x : ℕ, N + a + 1 + x = N + a + (x + 1) := by intro x; omega
    refine tsum_congr fun i => ?_
    by_cases hi : p ∣ N + a + (i + 1)
    · rw [if_pos hi, if_pos (hcomm i ▸ hi)]
      rw [mul_comm (2 : ℝ)⁻¹ ((2 : ℝ) ^ (i + 1))⁻¹, ← mul_inv]
      have hi2 : i + 2 = (i + 1) + 1 := by omega
      rw [hi2, pow_succ]
    · rw [if_neg hi, if_neg (fun hcon => hi ((hcomm i).symm ▸ hcon))]
      ring
  rw [hstep] at h
  have h0 : (if p ∣ N + a + 0 then ((2 : ℝ) ^ (0 + 1))⁻¹ else 0)
      = (if p ∣ N + a then (2 : ℝ)⁻¹ else 0) := by
    by_cases hi : p ∣ N + a
    · have h1 : p ∣ N + a + 0 := by omega
      rw [if_pos h1, if_pos hi]
      simp
    · have h1 : ¬ (p ∣ N + a + 0) := by omega
      rw [if_neg h1, if_neg hi]
  rw [h0] at h
  unfold jsp87PrimeTail
  exact h.symm

/-- **The single-prime tail is `p`-periodic in the shift**: shifting the cut
point by `p` does not change the set of `k` with `p ∣ N + k`. -/
theorem jsp87PrimeTail_add (N p a : ℕ) :
    jsp87PrimeTail (N + a + p) p = jsp87PrimeTail (N + a) p := by
  unfold jsp87PrimeTail
  refine tsum_congr fun k => ?_
  have heq : N + a + p + k = N + a + k + p := by omega
  by_cases h : p ∣ N + a + k
  · rw [if_pos h, if_pos (heq ▸ jsp87_dvd_add_p h)]
  · rw [heq, if_neg (fun hcon => h (jsp87_dvd_sub_p hcon)), if_neg h]

/-- **Iterating the recurrence.**  After `L` steps the tail splits into the
finite sum of its first `L` terms plus the far tail discounted by `2^-L`. -/
theorem jsp87PrimeTail_iter (N p a L : ℕ) :
    jsp87PrimeTail (N + a) p
      = (∑ j ∈ Finset.range L, (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
        + ((2 : ℝ) ^ L)⁻¹ * jsp87PrimeTail (N + a + L) p := by
  induction L with
  | zero =>
      have hstep := jsp87PrimeTail_succ N p a
      simp only [Finset.sum_range_zero]
      rw [Nat.add_zero, pow_zero, inv_one]
      nlinarith [hstep]
  | succ L ih =>
      have hstep := jsp87PrimeTail_succ (N + a) p L
      have hsum : (∑ j ∈ Finset.range (L + 1),
            (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
          = (∑ j ∈ Finset.range L, (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
            + (if p ∣ N + a + L then ((2 : ℝ) ^ (L + 1))⁻¹ else 0) := by
        simp only [Finset.sum_range_succ]
      have htail : ((2 : ℝ) ^ L)⁻¹ * jsp87PrimeTail (N + a + L) p
          = (if p ∣ N + a + L then ((2 : ℝ) ^ (L + 1))⁻¹ else 0)
            + ((2 : ℝ) ^ (L + 1))⁻¹ * jsp87PrimeTail (N + a + L + 1) p := by
        by_cases hc : p ∣ N + a + L
        · rw [hstep, if_pos hc, if_pos hc]
          calc ((2 : ℝ) ^ L)⁻¹ * (2⁻¹ + 2⁻¹ * jsp87PrimeTail (N + a + L + 1) p)
              = ((2 : ℝ) ^ L)⁻¹ * (2 : ℝ)⁻¹
                + ((2 : ℝ) ^ L)⁻¹ * (2 : ℝ)⁻¹ * jsp87PrimeTail (N + a + L + 1) p := by ring
            _ = ((2 : ℝ) ^ (L + 1))⁻¹
                + ((2 : ℝ) ^ (L + 1))⁻¹ * jsp87PrimeTail (N + a + L + 1) p := by
              simp only [jsp87_two_pow_inv_mul]
        · rw [hstep, if_neg hc, if_neg hc]
          simp only [zero_add]
          rw [← mul_assoc, jsp87_two_pow_inv_mul L]
      calc jsp87PrimeTail (N + a) p
          = (∑ j ∈ Finset.range L, (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
            + ((2 : ℝ) ^ L)⁻¹ * jsp87PrimeTail (N + a + L) p := ih
        _ = (∑ j ∈ Finset.range L, (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
            + ((2 : ℝ) ^ L)⁻¹
              * ((if p ∣ N + a + L then (2 : ℝ)⁻¹ else 0)
                + (2 : ℝ)⁻¹ * jsp87PrimeTail (N + a + L + 1) p) := by
              rw [hstep]
        _ = (∑ j ∈ Finset.range L, (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
            + ((2 : ℝ) ^ L)⁻¹ * (if p ∣ N + a + L then (2 : ℝ)⁻¹ else 0)
            + ((2 : ℝ) ^ L)⁻¹ * (2 : ℝ)⁻¹ * jsp87PrimeTail (N + a + L + 1) p := by
              ring
        _ = (∑ j ∈ Finset.range L, (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
            + (if p ∣ N + a + L then ((2 : ℝ) ^ (L + 1))⁻¹ else 0)
            + ((2 : ℝ) ^ (L + 1))⁻¹ * jsp87PrimeTail (N + a + L + 1) p := by
              by_cases hc : p ∣ N + a + L
              · simp only [if_pos hc, jsp87_two_pow_inv_mul]
              · simp only [if_neg hc, jsp87_two_pow_inv_mul, mul_zero]
        _ = (∑ j ∈ Finset.range (L + 1),
              (if p ∣ N + a + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
            + ((2 : ℝ) ^ (L + 1))⁻¹ * jsp87PrimeTail (N + a + (L + 1)) p := by
              rw [show N + a + (L + 1) = N + a + L + 1 from by omega, hsum]

/-- **The single-prime tail splits after a full period.** -/
theorem jsp87PrimeTail_split (N p : ℕ) :
    jsp87PrimeTail N p
      = (∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
        + ((2 : ℝ) ^ p)⁻¹ * jsp87PrimeTail N p := by
  have h := jsp87PrimeTail_iter N p 0 p
  have hsub : jsp87PrimeTail (N + 0 + p) p = jsp87PrimeTail (N + 0) p :=
    jsp87PrimeTail_add N p 0
  rw [hsub] at h
  simpa using h

/-- **CLOSING THE LOOP: the tail of the prime `p` at the cut point `N` is a
geometric series.**  After one period the far tail is the tail itself, so
`(1 - 2^-p) · T = (finite sum)`, and the finite sum has exactly one nonzero
term. -/
theorem jsp87PrimeTail_eq (N p : ℕ) (_hN : 1 ≤ N) (hp : 1 ≤ p) :
    jsp87PrimeTail N p = ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hsplit := jsp87PrimeTail_split N p
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hpow2 : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hpow1 : (2 : ℝ) ^ p ≠ 1 := by
    intro hcon
    obtain ⟨k, hk⟩ : ∃ k : ℕ, p = k + 1 := ⟨p - 1, by omega⟩
    subst hk
    have h2 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ _ _
    rw [h2] at hcon
    have h1 : (1 : ℝ) ≤ 2 ^ k := by
      rw [← pow_one (2 : ℝ)]
      exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
    linarith
  have hlin : (1 - ((2 : ℝ) ^ p)⁻¹) ≠ 0 := by
    intro hcon
    have h1 : ((2 : ℝ) ^ p)⁻¹ = 1 := by linarith [hcon]
    exact hpow1 (by rw [← inv_inv ((2 : ℝ) ^ p), h1, inv_one])
  have hmul : (1 - ((2 : ℝ) ^ p)⁻¹) * jsp87PrimeTail N p
      = ∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0) := by
    have h2 : (1 - ((2 : ℝ) ^ p)⁻¹) * jsp87PrimeTail N p
        = jsp87PrimeTail N p - ((2 : ℝ) ^ p)⁻¹ * jsp87PrimeTail N p := by ring
    rw [h2]
    linarith [hsplit]
  have hT : jsp87PrimeTail N p
      = (∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
        * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ := by
    calc jsp87PrimeTail N p
        = (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ * ((1 - ((2 : ℝ) ^ p)⁻¹) * jsp87PrimeTail N p) := by
          rw [← mul_assoc,
            mul_comm ((1 - ((2 : ℝ) ^ p)⁻¹)⁻¹) (1 - ((2 : ℝ) ^ p)⁻¹),
            mul_inv_cancel₀ hlin, one_mul]
      _ = (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹
          * ∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0) := by
          rw [hmul]
      _ = (∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
          * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ := mul_comm _ _
  have hinv : (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹ = (2 : ℝ) ^ p * ((2 : ℝ) ^ p - 1)⁻¹ := by
    field_simp [hpow2, hpow1]
  by_cases hd : p ∣ N
  · -- the first multiple of `p` is `N` itself: the finite sum is the single term `2^-1`
    have hzero : ∀ x ∈ Finset.range p, x ≠ 0 →
        (if p ∣ N + x then ((2 : ℝ) ^ (x + 1))⁻¹ else 0) = 0 := by
      intro x hx hne
      by_cases hc : p ∣ N + x
      · rw [if_pos hc]
        exfalso
        apply hne
        have hlt : x < p := Finset.mem_range.mp hx
        have hpj : p ∣ x := by
          refine Nat.dvd_iff_mod_eq_zero.mpr ?_
          have hmod : (N + x) % p = x % p := by
            rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hd]
            simp
          rw [← hmod, Nat.dvd_iff_mod_eq_zero.mp hc]
        have hle := Nat.le_of_dvd (by omega : 0 < x) hpj
        omega
      · rw [if_neg hc]
    have hd0 : p ∣ N + 0 := by simpa using hd
    have hmem : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr (by omega)
    have hsum : (∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
        = (2 : ℝ)⁻¹ := by
      rw [Finset.sum_eq_single (s := Finset.range p) 0 hzero (fun h => (h hmem).elim),
        if_pos hd0]
      norm_num
    have hstep : (2 : ℝ)⁻¹ * (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) := by
      have h1 : (2 : ℝ)⁻¹ = ((2 : ℝ) ^ 1)⁻¹ := by norm_num
      have h2 : (2 : ℝ) ^ p = (2 : ℝ) ^ 1 * (2 : ℝ) ^ (p - 1) := by
        rw [← pow_add (a := (2 : ℝ)) 1 (p - 1)]
        congr 1
        omega
      have h3 : ((2 : ℝ) ^ 1)⁻¹ * ((2 : ℝ) ^ 1 * (2 : ℝ) ^ (p - 1)) = (2 : ℝ) ^ (p - 1) := by
        rw [← mul_assoc, mul_comm ((2 : ℝ) ^ 1)⁻¹ ((2 : ℝ) ^ 1),
          mul_inv_cancel₀ (by norm_num : (2 : ℝ) ^ 1 ≠ 0), one_mul]
      rw [h1, h2, h3]
    rw [hT, hsum]
    have hform : (2 : ℝ)⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹
        = ((2 : ℝ) ^ (p - 1)) * ((2 : ℝ) ^ p - 1)⁻¹ := by
      rw [hinv, ← mul_assoc, hstep]
    rw [hform, jsp87RemExp, if_pos hd]
  · -- the first multiple of `p` at or after `N` is `N + (p - N mod p)`
    have hrlt : N % p < p := Nat.mod_lt _ (by omega : 0 < p)
    have hrpos : 0 < N % p := by
      by_contra hc
      have hz : N % p = 0 := Nat.eq_zero_of_not_pos hc
      exact hd (Nat.dvd_of_mod_eq_zero hz)
    set r := N % p with hrdef
    set j0 := p - r with hj0def
    have hj0lt : j0 < p := by omega
    have hj0pos : 0 < j0 := by omega
    have hdiv : p ∣ N + j0 := by
      refine Nat.dvd_iff_mod_eq_zero.mpr ?_
      have hlt : p - N % p < p := by omega
      rw [hj0def, hrdef, Nat.add_mod, Nat.mod_eq_of_lt hlt]
      have hle : N % p ≤ p := by omega
      have hcompl : N % p + (p - N % p) = p := by omega
      rw [hcompl]
      exact Nat.mod_self p
    have huniq : ∀ j, j < p → p ∣ N + j → j = j0 := by
      intro j hj hc
      have hj' : j = p - N % p := jsp87_dvd_add_index hrpos hj hc
      rw [hj0def, hrdef] at *
      omega
    have hzero : ∀ x ∈ Finset.range p, x ≠ j0 →
        (if p ∣ N + x then ((2 : ℝ) ^ (x + 1))⁻¹ else 0) = 0 := by
      intro x hx hne
      rw [if_neg (fun hcon => hne (huniq x (Finset.mem_range.mp hx) hcon))]
    have hsum : (∑ j ∈ Finset.range p, (if p ∣ N + j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0))
        = ((2 : ℝ) ^ (j0 + 1))⁻¹ := by
      rw [Finset.sum_eq_single (s := Finset.range p) j0 hzero
            (fun h => (h (Finset.mem_range.mpr hj0lt)).elim), if_pos hdiv]
    have hj0le : j0 + 1 ≤ p := by omega
    have hexp : j0 + 1 + (p - (j0 + 1)) = p := by omega
    have hstep : ((2 : ℝ) ^ (j0 + 1))⁻¹ * (2 : ℝ) ^ p = (2 : ℝ) ^ (r - 1) := by
      calc ((2 : ℝ) ^ (j0 + 1))⁻¹ * (2 : ℝ) ^ p
          = ((2 : ℝ) ^ (j0 + 1))⁻¹
              * ((2 : ℝ) ^ (j0 + 1) * (2 : ℝ) ^ (p - (j0 + 1))) := by
            rw [← pow_add, hexp]
        _ = 1 * (2 : ℝ) ^ (p - (j0 + 1)) := by
          rw [← mul_assoc, mul_comm ((2 : ℝ) ^ (j0 + 1))⁻¹ ((2 : ℝ) ^ (j0 + 1)),
            mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ (j0 + 1) ≠ 0), one_mul]
        _ = (2 : ℝ) ^ (r - 1) := by
          have hsub : p - (j0 + 1) = r - 1 := by
            have h2 : j0 + 1 ≤ p := by omega
            unfold j0
            omega
          rw [hsub]
          ring
    rw [hT, hsum]
    have hform : ((2 : ℝ) ^ (j0 + 1))⁻¹ * (1 - ((2 : ℝ) ^ p)⁻¹)⁻¹
        = ((2 : ℝ) ^ (r - 1)) * ((2 : ℝ) ^ p - 1)⁻¹ := by
      rw [hinv, ← mul_assoc, hstep]
    rw [hform, jsp87RemExp, if_neg hd, hrdef]

/-! ## 3. the double sum: the tail is the remainder-weighted Lambert series -/

/-- **The double summand** at the cut point `N`: the `k`-th step of the tail,
restricted to the primes. -/
noncomputable def lamRemF (N : ℕ) (c : ℕ × ℕ) : ℝ :=
  if c.2.Prime ∧ c.2 ∣ (N + c.1) then ((2 : ℝ) ^ (c.1 + 1))⁻¹ else 0

/-- Every summand of the double sum is nonnegative. -/
theorem lamRemF_nonneg (N : ℕ) (c : ℕ × ℕ) : 0 ≤ lamRemF N c := by
  unfold lamRemF
  split_ifs <;> positivity

/-- **THE ROW OF THE DOUBLE SUM IS AN ERDŐS SUMMAND.**  Summing over the primes
at a fixed step of the tail gives back `jsp87Term (N + k)`. -/
theorem tsum_lamRemF_snd {N k : ℕ} (hN : 1 ≤ N) :
    (∑' p : ℕ, lamRemF N (k, p)) = (2 : ℝ) ^ N * jsp87Term (N + k) := by
  have hNk : 0 < N + k := by omega
  have key : ∀ p ∉ Finset.range (N + k + 1), lamRemF N (k, p) = 0 := by
    intro p hp
    have hle : N + k + 1 ≤ p := by simpa using hp
    have hnd : ¬ (p.Prime ∧ p ∣ N + k) := by
      rintro ⟨hpr, hdv⟩
      have h1 := Nat.le_of_dvd hNk hdv
      omega
    rw [lamRemF, if_neg hnd]
  rw [tsum_eq_sum (s := Finset.range (N + k + 1)) key]
  simp only [lamRemF]
  have hcastR : (∑ p ∈ Finset.range (N + k + 1),
          (if p.Prime ∧ 1 ≤ N + k ∧ p ∣ N + k then (1 : ℝ) else 0) : ℝ)
      = ((omega (N + k) : ℕ) : ℝ) := by
    rw [sum_indicator_cast]
    have h1k : 1 ≤ N + k := Nat.succ_le_of_lt hNk
    simp only [h1k, true_and]
    exact congrArg (fun t : ℕ => (t : ℝ))
      (omega_eq_sum_indicator_dvd (N + k) (N + k + 1) hNk (by omega))
  have hcastR' : (∑ p ∈ Finset.range (N + k + 1),
          (if p.Prime ∧ p ∣ N + k then (1 : ℝ) else 0) : ℝ) = ((omega (N + k) : ℕ) : ℝ) := by
    have h1k : 1 ≤ N + k := Nat.succ_le_of_lt hNk
    simpa only [h1k, true_and] using hcastR
  have hsplit : (∑ p ∈ Finset.range (N + k + 1),
          (if p.Prime ∧ p ∣ N + k then ((2 : ℝ) ^ (k + 1))⁻¹ else 0) : ℝ)
      = (∑ p ∈ Finset.range (N + k + 1),
          (if p.Prime ∧ p ∣ N + k then (1 : ℝ) else 0)) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    calc (∑ p ∈ Finset.range (N + k + 1),
            (if p.Prime ∧ p ∣ N + k then ((2 : ℝ) ^ (k + 1))⁻¹ else 0) : ℝ)
        = ∑ p ∈ Finset.range (N + k + 1),
            ((if p.Prime ∧ p ∣ N + k then (1 : ℝ) else 0) * ((2 : ℝ) ^ (k + 1))⁻¹) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : p.Prime ∧ p ∣ N + k <;> simp [h]
      _ = (∑ p ∈ Finset.range (N + k + 1),
          (if p.Prime ∧ p ∣ N + k then (1 : ℝ) else 0)) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
          rw [Finset.sum_mul]
  rw [hsplit, hcastR']
  have hkey : ((2 : ℝ) ^ (k + 1))⁻¹ = (2 : ℝ) ^ N * ((2 : ℝ) ^ (N + k + 1))⁻¹ := by
    field_simp
    rw [← pow_add]
    congr 1
    omega
  rw [hkey]
  unfold jsp87Term
  ring

/-- **THE DOUBLE SUM IS SUMMABLE.** -/
theorem summable_lamRemF {N : ℕ} (hN : 1 ≤ N) : Summable (lamRemF N) := by
  refine (summable_prod_of_nonneg (lamRemF_nonneg N)).2 ⟨?_, ?_⟩
  · intro k
    have hs : (fun p : ℕ => lamRemF N (k, p)).HasFiniteSupport := by
      refine Set.Finite.subset
        (Finset.finite_toSet (s := (Finset.range (N + k + 1) : Finset ℕ))) ?_
      intro p hp
      simp only [Function.mem_support] at hp
      by_cases hguard : p.Prime ∧ p ∣ N + k
      · have hle := Nat.le_of_dvd (by omega : 0 < N + k) hguard.2
        exact Finset.mem_coe.2 (Finset.mem_range.mpr (by omega))
      · rw [lamRemF, if_neg hguard] at hp
        exact absurd hp (by simp)
    exact summable_of_hasFiniteSupport hs
  · show Summable (fun k : ℕ => ∑' p : ℕ, lamRemF N (k, p))
    have h1 : (fun k : ℕ => ∑' p : ℕ, lamRemF N (k, p))
        = fun k => (2 : ℝ) ^ N * jsp87Term (N + k) := by
      funext k
      exact tsum_lamRemF_snd hN
    rw [h1]
    exact (summable_jsp87Tail N).mul_left _

/-- **SWAPPING THE DOUBLE SUM.** -/
theorem tsum_lamRemF_swap {N : ℕ} (hN : 1 ≤ N) :
    (∑' c : ℕ × ℕ, lamRemF N c) = ∑' p : ℕ, ∑' k : ℕ, lamRemF N (k, p) := by
  rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) (lamRemF N)]
  simpa [Function.swap] using (summable_lamRemF hN).prod_symm.tsum_prod

/-- **THE TAIL IS THE DOUBLE SUM.**  The `ω`-tail at the cut point `N` is the
prime-restricted double sum, i.e. it is already a sum over primes. -/
theorem tsum_lamRemF_eq {N : ℕ} (hN : 1 ≤ N) :
    (∑' c : ℕ × ℕ, lamRemF N c) = (2 : ℝ) ^ N * jsp87Tail N := by
  rw [(summable_lamRemF hN).tsum_prod]
  rw [show (∑' k : ℕ, ∑' p : ℕ, lamRemF N (k, p)) = ∑' k : ℕ, (2 : ℝ) ^ N * jsp87Term (N + k) from
      tsum_congr fun k => tsum_lamRemF_snd hN]
  unfold jsp87Tail
  exact Summable.tsum_mul_left _ (summable_jsp87Tail N)

/-- **THE COLUMN OF THE DOUBLE SUM IS THE SINGLE-PRIME CLOSED FORM.** -/
theorem tsum_lamRemF_fst {N : ℕ} (hN : 1 ≤ N) (p : ℕ) :
    (∑' k : ℕ, lamRemF N (k, p))
      = if p.Prime then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0 := by
  by_cases hpr : p.Prime
  · rw [if_pos hpr]
    have hfun : (fun k : ℕ => lamRemF N (k, p))
        = fun k => (if p ∣ N + k then ((2 : ℝ) ^ (k + 1))⁻¹ else 0) := by
      funext k
      simp [lamRemF, hpr]
    rw [hfun]
    have h2p : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hpr.two_le
    exact jsp87PrimeTail_eq N p hN h2p
  · rw [if_neg hpr]
    have hzero : (fun k : ℕ => lamRemF N (k, p)) = fun _ => (0 : ℝ) := by
      funext k
      simp [lamRemF, hpr]
    rw [hzero]
    simpa using (Summable.zero : Summable (fun _ : ℕ => (0 : ℝ))).hasSum

/-! ## 4. the remainder-weighted prime-Lambert sum -/

/-- **The small-prime part** of the remainder-weighted Lambert sum: the primes
`p ≤ N` at the cut point `N`.  The series has finite support. -/
noncomputable def jsp87RemSumSml (N : ℕ) : ℝ :=
  ∑' p : ℕ,
    (if p.Prime ∧ p ≤ N then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)

/-- **The large-prime part**: the primes above the cut point, where the residue
exponent is the constant `N - 1`. -/
noncomputable def jsp87RemSumBig (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (N - 1) * ∑' p : ℕ,
    (if p.Prime ∧ N < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0)

/-- **THE REMAINDER-WEIGHTED PRIME-LAMBERT SUM AT THE CUT POINT `N`**: the
sum over primes of the Lambert term `1/(2^p - 1)` raised to the power
`2^(N mod p)`. -/
noncomputable def jsp87RemSum (N : ℕ) : ℝ := jsp87RemSumSml N + jsp87RemSumBig N

/-- `∑' p, 2^-p` is summable. -/
theorem jsp87_summable_two_pow_neg : Summable (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) := by
  have hxi : ‖((2 : ℝ)⁻¹ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by norm_num)
  exact (hasSum_geometric_of_norm_lt_one (ξ := (2 : ℝ)⁻¹) hxi).summable.congr fun n => inv_pow _ _

/-- **`2^(p-1) ≤ 2^p - 1`.** -/
theorem jsp87_two_pow_sub_one_ge {p : ℕ} (hp : 1 ≤ p) :
    (2 : ℝ) ^ (p - 1) ≤ (2 : ℝ) ^ p - 1 := by
  have h3 : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ ((p - 1) + 1) := by rw [pow_add, pow_one]
  have h1 : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
    rw [h3]
    congr 1
    omega
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
    rw [← pow_one (2 : ℝ)]
    exact pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  rw [h1]
  linarith

/-- **`1/(2^p - 1) ≤ 2/2^p`** for `1 ≤ p`: the exact majorant used for the
large primes. -/
theorem jsp87_two_pow_sub_one_inv_le {p : ℕ} (hp : 1 ≤ p) :
    ((2 : ℝ) ^ p - 1)⁻¹ ≤ 2 * ((2 : ℝ) ^ p)⁻¹ := by
  have hge : (2 : ℝ) ^ (p - 1) ≤ (2 : ℝ) ^ p - 1 := jsp87_two_pow_sub_one_ge hp
  have hposA : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by linarith [two_pow_ge_two hp]
  have hposB : (0 : ℝ) < (2 : ℝ) ^ (p - 1) := by positivity
  have hge' : ((2 : ℝ) ^ p - 1)⁻¹ ≤ ((2 : ℝ) ^ (p - 1))⁻¹ :=
    (inv_le_inv₀ hposA hposB).2 hge
  have hstep : ((2 : ℝ) ^ (p - 1))⁻¹ = 2 * ((2 : ℝ) ^ p)⁻¹ := by
    have h3 : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ ((p - 1) + 1) := by rw [pow_add, pow_one]
    have h1 : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
      rw [h3]
      congr 1
      omega
    field_simp
    exact h1
  rw [hstep] at hge'
  exact hge'

/-- The small-prime part has finite support. -/
theorem summable_jsp87RemSumSml (N : ℕ) :
    Summable (fun p : ℕ =>
      (if p.Prime ∧ p ≤ N then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
  refine summable_of_hasFiniteSupport ?_
  refine Set.Finite.subset
    (Finset.finite_toSet (s := (Finset.range (N + 1) : Finset ℕ))) ?_
  intro p hp
  have hp' : (if p.Prime ∧ p ≤ N
      then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) ≠ 0 := hp
  by_cases hguard : p.Prime ∧ p ≤ N
  · exact Finset.mem_coe.2 (Finset.mem_range.mpr (by omega))
  · rw [if_neg hguard] at hp'
    exact absurd hp' (by simp)

/-- The large-prime part is dominated by a geometric series. -/
theorem summable_jsp87RemSumBig (N : ℕ) :
    Summable (fun p : ℕ =>
      (if p.Prime ∧ N < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
  refine Summable.of_nonneg_of_le
    (fun p => ?_) (fun p => ?_) (Summable.mul_left 2 jsp87_summable_two_pow_neg)
  · by_cases hp : p.Prime ∧ N < p
    · rw [if_pos hp]
      have h1 : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
        have hp1 : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hp.1.two_le
        linarith [two_pow_ge_two hp1]
      exact (inv_pos.mpr h1).le
    · rw [if_neg hp]
  · by_cases hp : p.Prime ∧ N < p
    · rw [if_pos hp]
      have hp1 : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hp.1.two_le
      exact jsp87_two_pow_sub_one_inv_le hp1
    · rw [if_neg hp]
      positivity

/-- The large-prime part, with the residue exponent kept in place. -/
theorem summable_jsp87RemSumBig' {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun p : ℕ =>
      (if p.Prime ∧ N < p then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (Summable.mul_left ((2 : ℝ) ^ (N - 1)) (summable_jsp87RemSumBig N))
  · by_cases hp : p.Prime ∧ N < p
    · rw [if_pos hp, jsp87RemExp_of_lt N p hN hp.2]
      have h1 : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
        have hp1 : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hp.1.two_le
        linarith [two_pow_ge_two hp1]
      exact mul_nonneg (by positivity) (inv_pos.mpr h1).le
    · rw [if_neg hp]
  · by_cases hp : p.Prime ∧ N < p
    · rw [if_pos hp, jsp87RemExp_of_lt N p hN hp.2]
      have hp1 : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hp.1.two_le
      have hA : (0 : ℝ) ≤ (2 : ℝ) ^ (N - 1) := pow_nonneg (by norm_num) _
      simp only [if_pos hp]
      exact mul_le_mul_of_nonneg_left (le_refl _) hA
    · simp [hp]

/-- The remainder-weighted prime-Lambert sum is a well-defined real number. -/
theorem summable_jsp87RemSum (N : ℕ) (hp0 : 1 ≤ N) :
    Summable (fun p : ℕ =>
      (if p.Prime then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt (Nat.succ_le_of_lt hp0)
  have hfun : (fun p : ℕ =>
        (if p.Prime then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = (fun p =>
          (if p.Prime ∧ p ≤ N then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
        + (fun p =>
          (if p.Prime ∧ N < p then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
    funext p
    by_cases hp : p.Prime
    · by_cases hle : p ≤ N
      · simp [hp, hle]
      · have hlt : N < p := by omega
        simp [hp, hle, hlt]
    · simp [hp]
  rw [hfun]
  refine Summable.add (summable_jsp87RemSumSml N) ?_
  exact summable_jsp87RemSumBig' (N := N) (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hNpos))

/-! ## 5. the flagship: the tail is the remainder-weighted Lambert series -/

/-- **The two halves of the remainder-weighted sum.**  Above the cut point the
residue exponent collapses to the constant `N - 1`, so the large-prime half is a
constant multiple of a Lambert tail. -/
theorem jsp87RemSum_eq_tsumBig {N : ℕ} (hp0 : 1 ≤ N) :
    (∑' p : ℕ,
      (if p.Prime ∧ N < p then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = jsp87RemSumBig N := by
  unfold jsp87RemSumBig
  have hmain : (∑' p : ℕ,
      (if p.Prime ∧ N < p then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = (2 : ℝ) ^ (N - 1) * ∑' p : ℕ,
        (if p.Prime ∧ N < p then ((2 : ℝ) ^ p - 1)⁻¹ else 0) := by
    rw [← Summable.tsum_mul_left ((2 : ℝ) ^ (N - 1)) (summable_jsp87RemSumBig N)]
    exact tsum_congr fun p => by
      by_cases hp : p.Prime ∧ N < p
      · simp only [hp, if_true, true_and]
        rw [jsp87RemExp_of_lt N p hp0 hp.2]
      · simp only [hp, if_false]
        ring
  rw [hmain]

/-- **The full remainder-weighted sum is the small half plus the large half.** -/
theorem jsp87RemSum_eq_tsum {N : ℕ} (hp0 : 1 ≤ N) :
    (∑' p : ℕ,
      (if p.Prime then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = jsp87RemSumSml N + jsp87RemSumBig N := by
  have h : (fun p : ℕ =>
        (if p.Prime then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = (fun p =>
          (if p.Prime ∧ p ≤ N then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
        + (fun p =>
          (if p.Prime ∧ N < p then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)) := by
    funext p
    by_cases hp : p.Prime
    · by_cases hle : p ≤ N
      · simp [hp, hle]
      · have hlt : N < p := by omega
        simp [hp, hle, hlt]
    · simp [hp]
  rw [h]
  have hkey : (∑' p : ℕ,
        ((if p.Prime ∧ p ≤ N then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)
          + (if p.Prime ∧ N < p then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0)))
      = jsp87RemSumSml N + jsp87RemSumBig N := by
    rw [Summable.tsum_add (summable_jsp87RemSumSml N) (summable_jsp87RemSumBig' hp0)]
    unfold jsp87RemSumSml
    rw [← jsp87RemSum_eq_tsumBig hp0]
  exact hkey

/-- **THE FLAGSHIP OF ROUND 96.**  For every cut point `N ≥ 1`, the `ω`-tail of
the Erdős series is the *remainder-weighted prime-Lambert series*: the Lambert
term `1/(2^p - 1)` of each prime `p` is raised to the power `2^(N mod p)`, i.e.
weighted by the position of the first multiple of `p` at or after the cut
point.

In symbols, for `1 ≤ N`,

`2^N · τ N = ∑' p prime, 2^(if p ∣ N then p - 1 else N mod p - 1) / (2^p - 1)`.

This is the join of the two sides of `JSPProblem/LambertIdentity.lean` at an
*arbitrary* cut point: no earlier round had compared them anywhere but at `N = 0`
(`jsp87_lambert_classic`). -/
theorem jsp87Tail_eq_remSum {N : ℕ} (hN : 1 ≤ N) :
    (2 : ℝ) ^ N * jsp87Tail N = jsp87RemSum N := by
  have h1 : (2 : ℝ) ^ N * jsp87Tail N
      = ∑' c : ℕ × ℕ, lamRemF N c := (tsum_lamRemF_eq hN).symm
  have h2 : (∑' c : ℕ × ℕ, lamRemF N c)
      = ∑' p : ℕ, ∑' k : ℕ, lamRemF N (k, p) := tsum_lamRemF_swap hN
  have h3 : (∑' p : ℕ, ∑' k : ℕ, lamRemF N (k, p))
      = ∑' p : ℕ,
        (if p.Prime then ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0) :=
    tsum_congr fun p => tsum_lamRemF_fst hN p
  rw [h1, h2, h3]
  exact jsp87RemSum_eq_tsum hN

/-- **The cut point `0` carries no small-prime part.** -/
theorem jsp87RemSumSml_zero : jsp87RemSumSml 0 = 0 := by
  unfold jsp87RemSumSml
  have : (fun p : ℕ =>
        (if p.Prime ∧ p ≤ 0 then ((2 : ℝ) ^ jsp87RemExp 0 p) * ((2 : ℝ) ^ p - 1)⁻¹ else 0))
      = fun _ => (0 : ℝ) := by
    funext p
    by_cases h : p.Prime
    · have h2 : (0 : ℕ) < p := h.pos
      rw [if_neg (by omega)]
    · rw [if_neg (by simp [h])]
  rw [this]
  exact tsum_zero

/-- **Every prime term of the remainder-weighted sum lies strictly between `0`
and `1`.**  For `1 ≤ N` and `p` prime the exponent is at most `p - 1`, so the
term is at most `2^(p-1)/(2^p - 1) < 1`: the *hypothetical* rational
denominator can therefore never be seen by a single prime of the cut point. -/
theorem jsp87RemTerm_lt_one {N : ℕ} {p : ℕ} (hp : p.Prime) :
    ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ < 1 := by
  have hp1 : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hp.two_le
  have hle : jsp87RemExp N p ≤ p - 1 := jsp87RemExp_le N p hp1
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
    linarith [two_pow_ge_two hp1]
  have h1 : (2 : ℝ) ^ jsp87RemExp N p ≤ (2 : ℝ) ^ (p - 1) :=
    pow_le_pow_right₀ (by norm_num) hle
  have h3 : (1 : ℝ) < (2 : ℝ) ^ (p - 1) := by
    have hpm : 2 ≤ p := hp.two_le
    have hle' : (1 : ℕ) ≤ p - 1 := by omega
    linarith [two_pow_ge_two hle']
  have h4 : (2 : ℝ) ^ p - 1 - (2 : ℝ) ^ (p - 1) = (2 : ℝ) ^ (p - 1) - 1 := by
    have h5 : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
      have h6 : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ ((p - 1) + 1) := by rw [pow_add, pow_one]
      rw [h6]
      congr 1
      omega
    rw [h5]
    ring
  have h2 : (2 : ℝ) ^ (p - 1) < (2 : ℝ) ^ p - 1 := by linarith
  have hdiv : ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹
      = (2 : ℝ) ^ jsp87RemExp N p / ((2 : ℝ) ^ p - 1) := by field_simp
  rw [hdiv]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right h1 hpos.le) ((div_lt_one hpos).2 h2)

/-- **Every prime term is positive.** -/
theorem jsp87RemTerm_pos {N : ℕ} {p : ℕ} (hp : p.Prime) :
    0 < ((2 : ℝ) ^ jsp87RemExp N p) * ((2 : ℝ) ^ p - 1)⁻¹ := by
  have hp1 : 1 ≤ p := Nat.le_trans (Nat.le_succ 1) hp.two_le
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by
    linarith [two_pow_ge_two hp1]
  exact div_pos (by positivity) hpos

/-- **The residue exponent of a prime dividing the cut point is `p - 1`.** -/
theorem jsp87RemExp_dvd {N : ℕ} {p : ℕ} (hd : p ∣ N) :
    jsp87RemExp N p = p - 1 := by rw [jsp87RemExp, if_pos hd]

/-- **THE RATIONALITY TRANSFER, ON THE LAMBERT SIDE.**  If the Erdős series is
the rational `a/b`, then for every cut point `N ≥ 1` the remainder-weighted
prime-Lambert sum `2^N · τ N` is a multiple of `1/b`: the *whole* prime-indexed
Lambert value of the tail is quantised.  This is the first statement in the tree
that puts the Diophantine obstruction of the `ω`-side and the Lambert side of
`JSPProblem/LambertIdentity.lean` into the same real number. -/
theorem jsp87Series_rational_imp_remSum_int {N : ℕ} (hN : 1 ≤ N) {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, ((b : ℝ) * jsp87RemSum N) = (c : ℝ) := by
  obtain ⟨c, hc⟩ := jsp87_carry_mul_eq_int hN hb h
  rw [jsp87Tail_eq_remSum hN] at hc
  refine ⟨c, ?_⟩
  linarith


end JSP87
