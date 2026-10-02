/-
# JSP-000087, round 88 — THE TAO–TERÄVÄINEN ALTERNATING-SUM REDUCTION (§5)
# JSP-000087, round 90 — the GOWERS CUBE of §5.2 is now PROVED to cancel
#   (`jsp87AltSumF_zero`, `jsp87AltSum_zero`, `jsp87AltWinD_zero`); see the
#   section `THE GOWERS-CUBE CANCELLATION` below.

## Status of the headline — this supersedes rounds 37–87

The catalog question `Is ∑_{n≥1} ω(n)/2^n irrational?` is **no longer
conditional**.  Tao and Teräväinen, *Quantitative correlations and some problems
on prime factors of consecutive integers*, arXiv:2512.01739 (v1 Dec 2025, v2 Apr
2026), prove **Theorem 1.3 (Erdős #69)**: the series is **irrational,
unconditionally**.  (§1.3 of that paper states that Pratt, arXiv:2409.15185,
had previously obtained it conditionally on a prime-tuples conjecture.)

The blocker recorded by fifty rounds of this harness ("open, or at best
conditional on a uniform prime-k-tuples hypothesis") is therefore **stale, and is
retracted here**.  The published proof nevertheless rests on a quantitative
two-point correlation estimate for multiplicative functions with a logarithmic
saving, derived from Pilatte's work (§3 of the paper): no Mathlib counterpart
exists, so the gate cannot be closed here.

What *is* formalisable — and what no round of this tree had ever written down —
is the **whole reduction of §5**: the exact arithmetic by which rationality of the
series forces an alternating sum of `2^K` dilated windows to be an integer.

## Objects

* `jsp87Win n = ∑' h ≥ 1, ω(n+h)·2^{-h}` — the paper's window sum (after (1.7));
* `jsp87WinD n p = ∑' h ≥ 1, ω(n+p·h)·2^{-h}` — the *dilated* window;
* `jsp87Delta m p = ∑' h ≥ 1, [p | m+h]·2^{-h}` — the paper's error `δ_p`;
* `r_{ε,h} = p₀·h + Σ_{k=1}^{K}(h−k)·ε_k·v_k` — the Gowers-cube shift;
* `jsp87Alt v p₀ n = ∑' h ≥ 1, Σ_ε (−1)^{|ε|}·ω(n + r_{ε,h})·2^{-h}` — the
  alternating window of §5.2–5.3.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87Win_succ` | `W(n+1) = 2 W(n) − ω(n+1)`: the window carry recurrence |
| `jsp87Win_mul_eq_int`, `jsp87Win_ge_inv` | rationality freezes every window into `(1/b)ℤ` |
| `omega_mul_prime` | `ω(p·n) = ω(n) + 1 − 1_{p\|n}`: the dilating identity of §5.1 |
| `jsp87WinD_dilate` | **the exact window-dilation identity** `W_p(n) = W(n/p) + 1 − δ_p(n/p)` |
| `jsp87Delta_pos` | **the error never vanishes**: `δ_p(m) > 0` always (negative knowledge) |
| `jsp87WinD_congr` | **the mod-1 congruence** `\|b·W_p(n) − m\| ≤ b·δ_p(n/p)`, paper (2.2) |
| `jsp87AltSum_zero` | **the cube cancellation** `Σ_ε (−1)^{\|ε\|}ω(n+r_{ε,h}) = 0` for `1 ≤ h ≤ K` |
| `jsp87Alt_eq_shift` | the same at the level of the series (the paper's (2.5)) |
| `jsp87Alt_eq_finset` | **the alternating window is the alternating sum of the dilated windows** |
| `jsp87Alt_congr` | **the alternating-sum mod-1 theorem** |
| `jsp87Alt_zero_or_ge` | **the dichotomy**: the alternating window is `0` or `≥ 1/b` |
| `jsp87Series_irrational_of_altSmall` | **the criterion** |

## Not claimed

`jsp_000087_main` is **not declared**.  The reduction above is exact on its own
side; the missing input is the Tao–Teräväinen variance bound (§5.4–5.14), built
on the Pilatte correlation estimate.  Attaching the catalog name to a weaker
statement would misrepresent the headline.
-/

import JSPProblem.CutPeriod
import JSPProblem.BaseFamily

namespace JSP87

open Filter Finset Function Topology

open scoped Topology

set_option maxHeartbeats 40000000

/-! ## §0  Elementary bounds -/

private theorem omega_le_all (m : ℕ) : omega m ≤ m := by
  rcases Nat.lt_or_ge m 1 with h | h
  · rw [omega_eq_zero_iff.mpr (by omega : m ≤ 1)]
    omega
  · exact le_trans (omega_lt h) (Nat.sub_le _ _)

private theorem omega_le_real (m : ℕ) : (omega m : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast omega_le_all m

private theorem natCast_add_le (a b c : ℕ) (h : a ≤ b + c) : (a : ℝ) ≤ ((b + c : ℕ) : ℝ) := by
  rw [Nat.cast_add]
  exact_mod_cast h

private theorem natCast_mul_add_le (a b c d : ℕ) (h : a ≤ b * c + d) :
    (a : ℝ) ≤ (b : ℝ) * (c : ℝ) + (d : ℝ) := by
  rw [← Nat.cast_mul, ← Nat.cast_add]
  exact_mod_cast h

/-! ## §1  The window sums of §5.1 -/

/-- **The window sum** `W(n) = ∑' h ≥ 1, ω(n+h)·2^{-h}`. -/
noncomputable def jsp87Win (n : ℕ) : ℝ :=
  ∑' h : ℕ, (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹

theorem summable_jsp87Win (n : ℕ) :
    Summable (fun h : ℕ => (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
  have hnonneg : ∀ h : ℕ, 0 ≤ (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹ := by
    intro h
    positivity
  have hle : ∀ h : ℕ, (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
      ≤ ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
        + (1 : ℝ) * (((h : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
    intro h
    have h1 : (omega (n + h + 1) : ℝ) ≤ ((n + 1 + h : ℕ) : ℝ) :=
      natCast_add_le (omega (n + h + 1)) (n + 1) h
        ((omega_le_all (n + h + 1)).trans (by omega))
    rw [Nat.cast_add (m := n + 1) (n := h)] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ((2 : ℝ) ^ (h + 1))⁻¹)
    rw [add_mul] at h2
    linarith
  exact Summable.of_nonneg_of_le
    (f := fun h : ℕ => ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
      + (1 : ℝ) * (((h : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹))
    (g := fun h : ℕ => (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹)
    hnonneg hle ((summable_const_mul_two_pow_neg ((n + 1 : ℕ) : ℝ)).add
      (summable_natmul_self_two_pow_neg.mul_left (1 : ℝ)))

theorem jsp87Win_nonneg (n : ℕ) : 0 ≤ jsp87Win n :=
  tsum_nonneg fun _ => by positivity

/-- **THE WINDOW CARRY RECURRENCE.**  `W(n+1) = 2 W(n) − ω(n+1)`: the window
sequence obeys the doubling recurrence of the Erdős carry, one normalisation
higher than round 40's `jsp87Carry_succ`. -/
theorem jsp87Win_succ (n : ℕ) : jsp87Win (n + 1) = 2 * jsp87Win n - (omega (n + 1) : ℝ) := by
  have hs0 : Summable (fun h : ℕ => (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) :=
    summable_jsp87Win n
  have hs1 : Summable (fun h : ℕ => (omega (n + 1 + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) :=
    summable_jsp87Win (n + 1)
  have hC : (∑' h : ℕ, (omega (n + 1 + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1 + 1))⁻¹)
      = (1 / 2 : ℝ) * (∑' h : ℕ, (omega (n + 1 + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
    rw [← Summable.tsum_mul_left (1 / 2 : ℝ) hs1]
    exact tsum_congr fun h => by rw [pow_succ]; ring
  have h3 : (∑' h : ℕ, (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹)
      = (omega (n + 1) : ℝ) * (1 / 2 : ℝ)
        + (1 / 2 : ℝ) * (∑' h : ℕ, (omega (n + 1 + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
    have h1 := hs0.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h1
    rw [← h1, ← hC]
    have e0 : (omega (n + 0 + 1) : ℝ) * ((2 : ℝ) ^ (0 + 1))⁻¹
        = (omega (n + 1) : ℝ) * (1 / 2 : ℝ) := by norm_num
    have e1 : (∑' i : ℕ, (omega (n + (i + 1) + 1) : ℝ) * ((2 : ℝ) ^ (i + 1 + 1))⁻¹)
        = ∑' h : ℕ, (omega (n + 1 + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1 + 1))⁻¹ := by
      refine tsum_congr fun i => ?_
      have e2 : n + (i + 1) + 1 = n + 1 + i + 1 := by omega
      rw [e2]
    rw [e0, e1]
  have h4 : jsp87Win (n + 1) = ∑' h : ℕ, (omega (n + 1 + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹ := rfl
  have h5 : jsp87Win n = ∑' h : ℕ, (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹ := rfl
  rw [h4, h5, h3]
  linarith

/-- `W(n) > 0` for every `n`. -/
theorem jsp87Win_pos (n : ℕ) : 0 < jsp87Win n := by
  have h1 : jsp87Win (n + 1) = 2 * jsp87Win n - (omega (n + 1) : ℝ) := jsp87Win_succ n
  have h2 : jsp87Win (n + 2) = 2 * jsp87Win (n + 1) - (omega (n + 2) : ℝ) := by
    have := jsp87Win_succ (n + 1)
    rwa [show n + 1 + 1 = n + 2 by omega] at this
  have hnn : (0 : ℝ) ≤ jsp87Win (n + 2) := jsp87Win_nonneg (n + 2)
  have hge : (1 : ℝ) ≤ (omega (n + 2) : ℝ) := by
    have : 1 ≤ omega (n + 2) := omega_ge_one_of_ge_two (by omega)
    exact_mod_cast this
  have h4 : (1 : ℝ) / 2 ≤ jsp87Win (n + 1) := by
    nlinarith
  nlinarith

/-- `W(n) ≤ n + 2`, from `∑' h (n+1+h)·2^{-(h+1)} = n + 2`. -/
theorem jsp87Win_le (n : ℕ) : jsp87Win n ≤ (n + 2 : ℝ) := by
  have hs := summable_jsp87Win n
  have hle : ∀ h : ℕ, (omega (n + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
      ≤ ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
        + (1 : ℝ) * (((h : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
    intro h
    have h1 : (omega (n + h + 1) : ℝ) ≤ ((n + 1 + h : ℕ) : ℝ) :=
      natCast_add_le (omega (n + h + 1)) (n + 1) h
        ((omega_le_all (n + h + 1)).trans (by omega))
    rw [Nat.cast_add (m := n + 1) (n := h)] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ((2 : ℝ) ^ (h + 1))⁻¹)
    rw [add_mul] at h2
    linarith
  have hts := Summable.tsum_le_tsum hle hs
    ((summable_const_mul_two_pow_neg ((n + 1 : ℕ) : ℝ)).add
      (summable_natmul_self_two_pow_neg.mul_left (1 : ℝ)))
  rw [tsum_weighted] at hts
  unfold jsp87Win
  push_cast at hts ⊢
  linarith

/-- **THE WINDOW IS THE CARRIED SERIES AT THE NEXT CUT POINT.**
`W(n) + ω(n) = 2^{n+1} · τ(n+1)`: the window and the carry tail of round 38 differ
only by the term sitting at the cut point.  (This is the correct normalisation of
the identity; `jsp87Win n = 2^{n+1} · jsp87Tail n` is **false**, the `ω n` term
does not vanish.) -/
theorem jsp87Win_add_omega_scaled_tail (n : ℕ) :
    jsp87Win n + (omega n : ℝ) = (2 : ℝ) ^ (n + 1) * jsp87Tail n := by
  have hsT : Summable (fun k : ℕ => (omega (n + k) : ℝ) * ((2 : ℝ) ^ (n + k + 1))⁻¹) :=
    summable_jsp87Tail n
  have h1 := hsT.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h1
  have hWtail : (∑' j : ℕ, (omega (n + j + 1) : ℝ) * ((2 : ℝ) ^ (n + j + 2))⁻¹)
      = ((2 : ℝ) ^ (n + 1))⁻¹ * jsp87Win n := by
    have hsW := summable_jsp87Win n
    have hM := Summable.tsum_mul_left ((2 : ℝ) ^ (n + 1))⁻¹ hsW
    have hP : (∑' j : ℕ, (omega (n + j + 1) : ℝ) * ((2 : ℝ) ^ (n + j + 2))⁻¹)
        = ∑' j : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹
          * ((omega (n + j + 1) : ℝ) * ((2 : ℝ) ^ (j + 1))⁻¹) :=
      tsum_congr fun j => by push_cast; ring
    rw [hP, hM, jsp87Win]
  have htail : jsp87Tail n
      = (omega n : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ + ((2 : ℝ) ^ (n + 1))⁻¹ * jsp87Win n := by
    unfold jsp87Tail
    have e1 : (∑' k : ℕ, jsp87Term (n + k))
        = ∑' i : ℕ, (omega (n + i) : ℝ) * ((2 : ℝ) ^ (n + i + 1))⁻¹ := rfl
    have e2 : (∑' i : ℕ, (omega (n + (i + 1)) : ℝ) * ((2 : ℝ) ^ (n + (i + 1) + 1))⁻¹)
        = ∑' j : ℕ, (omega (n + j + 1) : ℝ) * ((2 : ℝ) ^ (n + j + 2))⁻¹ := by
      refine tsum_congr fun i => ?_
      have e3 : n + (i + 1) = n + i + 1 := by omega
      have e5 : n + i + 1 + 1 = n + i + 2 := by omega
      rw [e3, e5]
    have e3 : (omega (n + 0) : ℝ) * ((2 : ℝ) ^ (n + 0 + 1))⁻¹
        = (omega n : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      have e6 : n + 0 + 1 = n + 1 := by omega
      rw [e6, Nat.add_zero]
    rw [e1, ← h1, e2, e3, hWtail]
  rw [htail]
  field_simp
  ring

/-- **THE WINDOW IS THE RESCALED CARRY AT THE NEXT CUT POINT.**
`W(n) = 2^{n+1} · τ(n+1) = jsp87Carry (n+1)`: the window is *exactly* the carry of
round 40 one cut point further out.  This is the join of round 40's carry with
the §5.1 window. -/
theorem jsp87Win_eq_carry (n : ℕ) :
    jsp87Win n = (2 : ℝ) ^ (n + 1) * jsp87Tail (n + 1) := by
  have h1 := jsp87Carry_succ n
  simp only [jsp87Carry] at h1
  have h2 := jsp87Win_add_omega_scaled_tail n
  have hx : (2 : ℝ) * (((2 : ℝ) ^ n) * jsp87Tail n)
      = ((2 : ℝ) ^ (n + 1)) * jsp87Tail n := by
    rw [pow_succ]
    ring
  rw [hx] at h1
  push_cast at h2 ⊢
  linarith

/-- **THE RATIONALITY FREEZE OF THE WINDOW** (the paper's (1.1)). -/
theorem jsp87Win_mul_eq_int {n : ℕ} {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ c : ℤ, ((b : ℝ) * jsp87Win n) = (c : ℝ) := by
  obtain ⟨c, hc⟩ := jsp87_carry_mul_eq_int (a := a) (b := b) (N := n + 1) (by omega) hb h
  have hc' := jsp87Win_eq_carry n
  rw [← hc'] at hc
  refine ⟨c, ?_⟩
  rw [show (b : ℝ) * jsp87Win n = jsp87Win n * (b : ℝ) by ring, hc]

/-- **Every window of a rational series is `≥ 1/b`** (the lower half of the
paper's two-sided contradiction). -/
theorem jsp87Win_ge_inv {n : ℕ} {a b : ℤ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ((1 : ℝ) / (b : ℝ)) ≤ jsp87Win n := by
  obtain ⟨c, hc⟩ := jsp87Win_mul_eq_int (a := a) (b := b) (n := n) hb h
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb1 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcpos : 0 < c := by
    have h1 : (0 : ℝ) < (c : ℝ) := by
      rw [← hc]
      have hb1 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hW := jsp87Win_pos n
      positivity
    exact_mod_cast h1
  have hone : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega)
  calc (1 : ℝ) / (b : ℝ) ≤ (c : ℝ) / (b : ℝ) := div_le_div_of_nonneg_right hone (le_of_lt hb1)
    _ = jsp87Win n := by rw [← hc]; field_simp

/-! ## §2  The dilating identity `ω(pn) = ω(n) + 1 − 1_{p | n}` (paper §5.1) -/

/-- **THE DILATING IDENTITY.**  For prime `p`,
`ω(p·n) = ω(n) + 1 − 1_{p | n}`: the additivity of `ω` across a dilation by a
prime, the first step of §5.1. -/
theorem omega_mul_prime {p n : ℕ} (hp : p.Prime) :
    omega (p * n) = if p ∣ n then omega n else omega n + 1 := by
  by_cases hn : n = 0
  · have hzero : omega 0 = 0 := by simp [omega]
    rw [hn, if_pos (dvd_zero p), Nat.mul_zero, hzero]
  by_cases hdiv : p ∣ n
  · rw [if_pos hdiv, show p * n = n * p by ring]
    exact omega_mul_eq_omega_of_dvd (m := n) (n := p) hdiv hn
  · rw [if_neg hdiv]
    have hcop : Nat.Coprime p n := hp.coprime_iff_not_dvd.mpr hdiv
    rw [omega_mul_of_coprime hcop,
      show omega p = 1 by simpa using (omega_prime_pow hp (by norm_num : (1 : ℕ) ≤ 1))]
    ring

/-! ## §3  The dilated window and the error term `δ` -/

/-- **THE DILATED WINDOW** `W_p(n) = ∑' h ≥ 1, ω(n + p·h)·2^{-h}`. -/
noncomputable def jsp87WinD (n p : ℕ) : ℝ :=
  ∑' h : ℕ, (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹

/-- **THE ERROR TERM** `δ_p(m) = ∑' h ≥ 1, [p | m+h]·2^{-h}`; the paper's
`δ_p(n) = ∑' h, [p² | n+ph]·2^{-h}` when `p ∣ n`. -/
noncomputable def jsp87Delta (m p : ℕ) : ℝ :=
  ∑' h : ℕ, (if p ∣ m + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹

theorem summable_jsp87WinD (n p : ℕ) :
    Summable (fun h : ℕ => (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
  have hle : ∀ h : ℕ, (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
      ≤ ((n + p : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
        + ((p : ℕ) : ℝ) * (((h : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
    intro h
    have h1 : (omega (n + p * (h + 1)) : ℝ)
        ≤ ((n + p : ℕ) : ℝ) + ((p : ℕ) : ℝ) * (h : ℝ) := by
      have hx : (omega (n + p * (h + 1)) : ℝ) ≤ ((n + p * (h + 1) : ℕ) : ℝ) := omega_le_real _
      have hy : (n + p * (h + 1) : ℕ) ≤ n + p + p * h := by nlinarith
      have hz : ((n + p * (h + 1) : ℕ) : ℝ) ≤ ((n + p + p * h : ℕ) : ℝ) := by
        exact_mod_cast hy
      rw [Nat.cast_add (m := n + p) (n := p * h), Nat.cast_mul (m := p) (n := h)] at hz
      exact hx.trans hz
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ((2 : ℝ) ^ (h + 1))⁻¹)
    rw [add_mul, mul_assoc] at h2
    linarith
  exact Summable.of_nonneg_of_le
    (f := fun h : ℕ => ((n + p : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
      + ((p : ℕ) : ℝ) * (((h : ℕ) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹))
    (g := fun h : ℕ => (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹)
    (fun h => by positivity) hle ((summable_const_mul_two_pow_neg ((n + p : ℕ) : ℝ)).add
      (summable_natmul_self_two_pow_neg.mul_left ((p : ℕ) : ℝ)))

theorem summable_jsp87Delta (m p : ℕ) :
    Summable (fun h : ℕ => (if p ∣ m + h + 1 then (1 : ℝ) else 0)
      * ((2 : ℝ) ^ (h + 1))⁻¹) := by
  have hle : ∀ h : ℕ, (if p ∣ m + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹
      ≤ ((2 : ℝ) ^ (h + 1))⁻¹ := by
    intro h
    by_cases hp : p ∣ m + h + 1 <;> simp [hp]
  exact Summable.of_nonneg_of_le (f := fun h : ℕ => ((2 : ℝ) ^ (h + 1))⁻¹)
    (g := fun h : ℕ => (if p ∣ m + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹)
    (fun h => by positivity) hle (summable_two_pow_neg)

theorem jsp87Delta_nonneg (m p : ℕ) : 0 ≤ jsp87Delta m p :=
  tsum_nonneg fun _ => by positivity

theorem jsp87Delta_le_one (m p : ℕ) : jsp87Delta m p ≤ 1 := by
  have hle : ∀ h : ℕ, (if p ∣ m + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹
      ≤ ((2 : ℝ) ^ (h + 1))⁻¹ := by
    intro h
    by_cases hp : p ∣ m + h + 1 <;> simp [hp]
  have hts := Summable.tsum_le_tsum hle (summable_jsp87Delta m p) (summable_two_pow_neg)
  unfold jsp87Delta
  rw [tsum_two_pow_neg] at hts
  exact hts

/-- **THE ERROR NEVER VANISHES.**  For prime `p` and every `m ≥ 1` the
progression `m+1, m+2, …` meets a multiple of `p`, so `δ_p(m) > 0`.

Negative knowledge about §5.1 of Tao–Teräväinen, and exactly what a reader of
that paper needs: the congruence (2.2) can **never** be promoted to an exact
identity, because `p | m + h` has a solution `h ≥ 1` for *every* `m`.  The error
is negligible only *on average over `n`* (the paper's `κ₁ = o(1)`), never
pointwise. -/
theorem jsp87Delta_pos {m p : ℕ} (hp : p.Prime) (hm : 1 ≤ m) : 0 < jsp87Delta m p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : (m + 1) % p < p := Nat.mod_lt _ (by omega)
  have hrem : (m + 1) % p + p * ((m + 1) / p) = m + 1 := Nat.mod_add_div _ _
  set h0 : ℕ := p - (m + 1) % p with h0def
  have h0pos : 1 ≤ h0 := by omega
  have hdiv0 : p ∣ m + h0 + 1 := by
    refine ⟨((m + 1) / p) + 1, ?_⟩
    have hab : (m + 1) % p + (p - (m + 1) % p) = p := by rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
    have e : (m + 1) + (p - (m + 1) % p) = p * (((m + 1) / p) + 1) := by
      have h1 : m + 1 = (m + 1) % p + p * ((m + 1) / p) := hrem.symm
      nth_rewrite 1 [h1]
      rw [show (m + 1) % p + p * ((m + 1) / p) + (p - (m + 1) % p)
          = ((m + 1) % p + (p - (m + 1) % p)) + p * ((m + 1) / p) by ring, hab]
      ring
    calc m + h0 + 1 = m + (p - (m + 1) % p) + 1 := by rw [h0def]
      _ = (m + 1) + (p - (m + 1) % p) := by omega
      _ = p * (((m + 1) / p) + 1) := e
  have heq : ((if p ∣ m + h0 + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h0 + 1))⁻¹)
      ≤ ∑' h : ℕ, (if p ∣ m + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹ :=
    tsum_ge_term (summable_jsp87Delta m p) (fun _ => by positivity) h0
  have h1 : (0 : ℝ)
      < ((if p ∣ m + h0 + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h0 + 1))⁻¹) := by
    rw [if_pos hdiv0]
    positivity
  unfold jsp87Delta
  linarith

/-- **THE EXACT WINDOW-DILATION IDENTITY** (the paper's (2.2), before the passage
to `mod 1`).  If `p` is prime and `p ∣ n` then

`∑' h ≥ 1, ω(n+p h)·2^{-h} = ∑' h ≥ 1, ω(n/p+h)·2^{-h} + 1 − ∑' h ≥ 1, [p | n/p+h]·2^{-h}`.

The three terms are the dilated window, the ordinary window at `n/p`, the
constant `∑' h 2^{-h} = 1`, and the error `δ_p(n/p)`. -/
theorem jsp87WinD_dilate {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdiv : p ∣ n) :
    jsp87WinD n p = jsp87Win (n / p) + 1 - jsp87Delta (n / p) p := by
  have hsD := summable_jsp87WinD n p
  have hsW := summable_jsp87Win (n / p)
  have hsDel := summable_jsp87Delta (n / p) p
  have hpoint : ∀ h : ℕ,
      (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
        = (omega ((n / p) + (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
          + ((2 : ℝ) ^ (h + 1))⁻¹
          - (if p ∣ (n / p) + (h + 1) then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹ := by
    intro h
    have hmul : n + p * (h + 1) = (n / p) * p + p * (h + 1) := by
      have h1 : (n / p) * p = n := div_mul_cancel' hdiv
      omega
    have hmul2 : (n / p) * p + p * (h + 1) = p * ((n / p) + (h + 1)) := by ring
    rw [hmul, hmul2]
    have hω : omega (p * ((n / p) + (h + 1))) = omega ((n / p) + (h + 1)) + 1
        - (if p ∣ (n / p) + (h + 1) then (1 : ℝ) else 0) := by
      by_cases hb : p ∣ (n / p) + (h + 1)
      · rw [if_pos hb, omega_mul_prime hp, if_pos hb]
        push_cast
        ring
      · rw [if_neg hb, omega_mul_prime hp, if_neg hb]
        push_cast
        ring
    push_cast
    have eidx : (n / p) + (h + 1) = 1 + n / p + h := by omega
    rw [hω, eidx]
    ring

  have hpoint' : ∀ h : ℕ,
      (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
        = (omega (n / p + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
          + ((2 : ℝ) ^ (h + 1))⁻¹
          - (if p ∣ n / p + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹ := by
    intro h
    have hx := hpoint h
    rw [show (n / p) + (h + 1) = n / p + h + 1 by omega] at hx
    exact hx
  have hsum : (∑' h : ℕ, (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹)
      = (∑' h : ℕ, (omega (n / p + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹)
        + (∑' h : ℕ, ((2 : ℝ) ^ (h + 1))⁻¹)
        - (∑' h : ℕ, (if p ∣ n / p + h + 1 then (1 : ℝ) else 0)
          * ((2 : ℝ) ^ (h + 1))⁻¹) := by
    have hsplit : (fun h : ℕ => (omega (n + p * (h + 1)) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹)
        = (fun h : ℕ => (omega (n / p + h + 1) : ℝ) * ((2 : ℝ) ^ (h + 1))⁻¹
          + ((2 : ℝ) ^ (h + 1))⁻¹
          - (if p ∣ n / p + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
      funext h
      exact hpoint' h
    rw [tsum_congr (fun h => congrFun hsplit h),
      ← Summable.tsum_add hsW (summable_two_pow_neg),
      ← Summable.tsum_sub (Summable.add hsW (summable_two_pow_neg)) hsDel]
  unfold jsp87WinD jsp87Win jsp87Delta
  rw [hsum, tsum_two_pow_neg]

/-- **THE MOD-1 CONGRUENCE OF §5.1** (the paper's equation (2.2)). -/
theorem jsp87WinD_congr {p n : ℕ} {a b : ℤ} (hp : p.Prime) (hn : 1 ≤ n) (hdiv : p ∣ n)
    (hb : 0 < b) (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ m : ℤ, |(b : ℝ) * jsp87WinD n p - (m : ℝ)| ≤ (b : ℝ) * jsp87Delta (n / p) p := by
  obtain ⟨c, hc⟩ := jsp87Win_mul_eq_int (a := a) (b := b) (n := n / p) hb h
  have hdil := jsp87WinD_dilate (p := p) (n := n) hp hn hdiv
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h2 : 0 ≤ (b : ℝ) * jsp87Delta (n / p) p := by
    have := jsp87Delta_nonneg (n / p) p
    positivity
  refine ⟨c + b, ?_⟩
  rw [hdil]
  have hsplit : (b : ℝ) * (jsp87Win (n / p) + 1 - jsp87Delta (n / p) p)
      = ((c : ℝ) + (b : ℝ)) - (b : ℝ) * jsp87Delta (n / p) p := by
    have h1 : (b : ℝ) * (jsp87Win (n / p) + 1 - jsp87Delta (n / p) p)
        = (b : ℝ) * jsp87Win (n / p) + (b : ℝ) - (b : ℝ) * jsp87Delta (n / p) p := by ring
    rw [h1, hc]
  rw [hsplit, show ((c : ℤ) + b : ℤ) = c + b from rfl, Int.cast_add]
  have e1 : (((c : ℝ) + (b : ℝ)) - (b : ℝ) * jsp87Delta (n / p) p)
      - ((c : ℝ) + (b : ℝ)) = -(b : ℝ) * jsp87Delta (n / p) p := by ring
  rw [e1]
  have habs : |-(b : ℝ) * jsp87Delta (n / p) p| = (b : ℝ) * jsp87Delta (n / p) p := by
    rw [abs_mul, abs_neg, abs_of_pos hb0, abs_of_nonneg (jsp87Delta_nonneg _ _)]
  rw [habs]

/-! ## §4  The Gowers cube of §5.2 -/

/-- The sign `(-1)^{|s|}`. -/
def jsp87Sign (e : ℕ) : ℤ := if e % 2 = 0 then 1 else -1

@[simp] theorem jsp87Sign_zero : jsp87Sign 0 = 1 := by simp [jsp87Sign]

theorem jsp87Sign_succ (e : ℕ) : jsp87Sign (e + 1) = - jsp87Sign e := by
  rcases Nat.mod_two_eq_zero_or_one e with h | h
  · have he : e = 2 * (e / 2) := by omega
    have h1 : (e + 1) % 2 = 1 := by rw [he]; omega
    have h1n : ¬ (e + 1) % 2 = 0 := by omega
    unfold jsp87Sign
    rw [if_neg h1n, if_pos h]
  · have hne : e % 2 ≠ 0 := by omega
    have he : e = 2 * (e / 2) + 1 := by omega
    have h2 : (e + 1) % 2 = 0 := by rw [he]; omega
    unfold jsp87Sign
    rw [if_neg hne, if_pos h2]
    ring

theorem jsp87Sign_ne_zero (e : ℕ) : jsp87Sign e ≠ 0 := by
  unfold jsp87Sign
  split <;> norm_num

theorem jsp87Sign_mul_self (e : ℕ) : jsp87Sign e * jsp87Sign e = 1 := by
  unfold jsp87Sign
  split <;> norm_num

/-- **THE CUBE SHIFT** `r_{ε,h} = p₀·h + Σ_{k∈ε} (h−k)·v_k`, in `ℤ`.  For `h ≥ 1`
this is the paper's `p_ε·h − Σ_{k=1}^K k ε_k v_k`. -/
def jsp87AltShift {K : ℕ} (v : Fin K → ℤ) (p0 h : ℕ) (s : Finset (Fin K)) : ℤ :=
  (p0 : ℤ) * h + ∑ k ∈ s, ((h : ℤ) - (k.val + 1)) * v k

/-- One summand of the alternating sum. -/
def jsp87AltSub {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ) (s : Finset (Fin K)) : ℤ :=
  jsp87Sign s.card * omega ((n : ℤ) + jsp87AltShift v p0 h s).toNat

/-- **THE ALTERNATING SUM** over all `2^K` vertices of the cube. -/
def jsp87AltSum {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ) : ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), jsp87AltSub v p0 n h s

/-- Toggling the `j`-th coordinate of the cube. -/
def jsp87AltToggle {K : ℕ} (j : Fin K) (s : Finset (Fin K)) : Finset (Fin K) :=
  if j ∈ s then s.erase j else insert j s

/-! ## §5  THE GOWERS-CUBE CANCELLATION (the combinatorics of Tao–Teräväinen §5.2)

The shift `r_{ε,h} = p₀·h + Σ_{k∈ε}(h−k)·v_k` does **not** depend on the
`h`-th coordinate `ε_h`: its coefficient is `(h − h) = 0`.  Hence pairing every
vertex `ε` of the cube with the vertex obtained by flipping `ε_h` leaves the
argument of `ω` unchanged and reverses the sign, and the `2^K`-term alternating
sum **vanishes identically**.  This is the combinatorial heart of the reduction,
and this section proves it, together with the exact description of *which*
edges of the cube are degenerate. -/

/-- `ω` read as an integer-valued function, for the cube sums below (the
name `omega` is taken by the tactic in this file). -/
def jsp87Omega : ℕ → ℤ := fun m => omega m

/-- `jsp87AltToggle` is its own inverse. -/
theorem jsp87AltToggle_invol {K : ℕ} (j : Fin K) (s : Finset (Fin K)) :
    jsp87AltToggle j (jsp87AltToggle j s) = s := by
  unfold jsp87AltToggle
  by_cases hj : j ∈ s
  · rw [if_pos hj,
      if_neg (show j ∉ s.erase j by
        intro hmem; rw [Finset.mem_erase] at hmem; exact hmem.1 rfl)]
    exact Finset.insert_erase hj
  · rw [if_neg hj, if_pos (Finset.mem_insert_self j s)]
    exact Finset.erase_insert hj

/-- Toggling is a bijection of the vertex set onto itself. -/
theorem jsp87AltToggle_mem_univ {K : ℕ} (j : Fin K) (s : Finset (Fin K)) :
    jsp87AltToggle j s ∈ (Finset.univ : Finset (Finset (Fin K))) :=
  Finset.mem_univ _

/-- **THE SIGN REVERSAL.**  Flipping one coordinate of a vertex reverses its
sign `(-1)^{|s|}`. -/
theorem jsp87AltSign_toggle {K : ℕ} (j : Fin K) (s : Finset (Fin K)) :
    jsp87Sign (jsp87AltToggle j s).card = - jsp87Sign s.card := by
  by_cases hj : j ∈ s
  · rw [jsp87AltToggle, if_pos hj]
    have h2 : (s.erase j).card + 1 = s.card := by
      have hc := Finset.card_erase_of_mem hj
      have h1 : 1 ≤ s.card := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have h3 : -(jsp87Sign (s.erase j).card) = jsp87Sign s.card := by
      rw [← h2]
      exact (jsp87Sign_succ _).symm
    have hne := jsp87Sign_ne_zero (s.erase j).card
    linarith
  · rw [jsp87AltToggle, if_neg hj, Finset.card_insert_of_notMem hj]
    exact jsp87Sign_succ s.card

/-- **THE BLIND SPOT.**  The coefficient of `v_j` in the shift `r_{ε,h}` is
`(h − (j+1))`, which vanishes for `j = h − 1`; so the shift is *independent of the
`h`-th coordinate*, exactly as §5.2 requires. -/
theorem jsp87AltShift_toggle {K : ℕ} (v : Fin K → ℤ) (p0 h : ℕ) (j : Fin K)
    (s : Finset (Fin K)) (hj : j.val + 1 = h) :
    jsp87AltShift v p0 h (jsp87AltToggle j s) = jsp87AltShift v p0 h s := by
  have hz : ((h : ℤ) - (j.val + 1 : ℤ)) * v j = 0 := by
    have h3 : (h : ℤ) = (j.val + 1 : ℤ) := by omega
    rw [h3]
    ring
  by_cases hmem : j ∈ s
  · rw [jsp87AltToggle, if_pos hmem]
    have hs := Finset.sum_erase_add s (fun k : Fin K => ((h : ℤ) - (k.val + 1)) * v k)
      hmem
    rw [hz, add_zero] at hs
    unfold jsp87AltShift
    rw [hs]
  · rw [jsp87AltToggle, if_neg hmem]
    unfold jsp87AltShift
    rw [Finset.sum_insert hmem, hz, zero_add]

/-- **THE EDGE LENGTH.**  The `j`-th edge of the cube, out of the vertex `s`,
has length `(h − (j+1))·v_j`. -/
theorem jsp87AltShift_edge {K : ℕ} (v : Fin K → ℤ) (p0 h : ℕ) (j : Fin K)
    (s : Finset (Fin K)) (hj : j ∉ s) :
    jsp87AltShift v p0 h (insert j s) = jsp87AltShift v p0 h s
      + ((h : ℤ) - (j.val + 1)) * v j := by
  unfold jsp87AltShift
  rw [Finset.sum_insert hj]
  ring

/-- **AN EDGE IS BLANK IFF ITS STEP VANISHES OR IT IS THE DEGENERATE
DIRECTION.**  This is the precise statement of §5.2: the `h`-th direction of the
cube is blank for *every* choice of the steps, while every other direction is
blank exactly when its step is zero — and a non-vanishing step is where the
analytic input of the published proof has to act. -/
theorem jsp87AltShift_edge_zero_iff {K : ℕ} (v : Fin K → ℤ) (p0 h : ℕ) (j : Fin K)
    (s : Finset (Fin K)) (hj : j ∉ s) :
    jsp87AltShift v p0 h (insert j s) = jsp87AltShift v p0 h s
      ↔ (v j = 0 ∨ h = j.val + 1) := by
  constructor
  · intro he
    by_cases hc : h = j.val + 1
    · exact Or.inr hc
    · left
      by_contra! hv
      -- the edge is zero, so its length `((h : ℤ) - (j.val + 1)) * v j` vanishes
      rw [jsp87AltShift_edge v p0 h j s hj] at he
      have hL : ((h : ℤ) - (j.val + 1)) * v j = 0 := by linarith
      rcases mul_eq_zero.mp hL with hco | hco
      · have hjval : h = j.val + 1 := by omega
        exact hc hjval
      · exact absurd hco hv
  · intro hz
    rcases hz with hv | hc
    · rw [jsp87AltShift_edge v p0 h j s hj, hv]
      ring
    · have htog : jsp87AltToggle j s = insert j s := by
        rw [jsp87AltToggle, if_neg hj]
      rw [← htog]
      exact jsp87AltShift_toggle v p0 h j s hc.symm

/-- The alternating sum over all `2^K` vertices of a cube, for an arbitrary
integer-valued `f`: the general form of the object `(-1)^{|ε|}·f(n + r_ε)` of
§5.2. -/
def jsp87AltSumF {K : ℕ} (f : ℕ → ℤ) (v : Fin K → ℤ) (p0 n h : ℕ) : ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
    jsp87Sign s.card * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat

/-- The general alternating sum is the `ω`-alternating sum. -/
theorem jsp87AltSum_eq_jsp87AltSumF {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ) :
    jsp87AltSumF jsp87Omega v p0 n h = jsp87AltSum v p0 n h := rfl

/-- **AN EVEN VERTEX CONTRIBUTES `+f`.** -/
theorem jsp87AltSumF_eq_of_even (f : ℕ → ℤ) {K : ℕ} (v : Fin K → ℤ)
    (p0 n h : ℕ) (s : Finset (Fin K)) (he : s.card % 2 = 0) :
    jsp87Sign s.card * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat
      = f ((n : ℤ) + jsp87AltShift v p0 h s).toNat := by
  unfold jsp87Sign
  rw [if_pos he]
  ring

/-- **AN ODD VERTEX CONTRIBUTES `−f`.** -/
theorem jsp87AltSumF_eq_neg_of_odd (f : ℕ → ℤ) {K : ℕ} (v : Fin K → ℤ)
    (p0 n h : ℕ) (s : Finset (Fin K)) (ho : s.card % 2 ≠ 0) :
    jsp87Sign s.card * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat
      = - f ((n : ℤ) + jsp87AltShift v p0 h s).toNat := by
  unfold jsp87Sign
  rw [if_neg ho]
  ring

/-- The even-cardinality vertices of the cube. -/
def jsp87AltEven {K : ℕ} : Finset (Finset (Fin K)) :=
  (Finset.univ : Finset (Finset (Fin K))).filter (fun s => s.card % 2 = 0)

/-- The odd-cardinality vertices of the cube. -/
def jsp87AltOdd {K : ℕ} : Finset (Finset (Fin K)) :=
  (Finset.univ : Finset (Finset (Fin K))).filter (fun s => s.card % 2 = 1)

/-- **THE EVEN AND ODD FACES PARTITION THE CUBE.** -/
theorem jsp87AltEven_union_odd {K : ℕ} :
    jsp87AltEven ∪ jsp87AltOdd = (Finset.univ : Finset (Finset (Fin K))) := by
  ext s
  simp only [Finset.mem_union, jsp87AltEven, jsp87AltOdd, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rcases Nat.mod_two_eq_zero_or_one s.card with h | h <;> simp [h]

/-- A difference of two sums is a sum of differences. -/
private theorem sum_sub_eq (s : Finset ι) (f g : ι → ℤ) :
    (∑ x ∈ s, f x) - ∑ x ∈ s, g x = ∑ x ∈ s, (f x - g x) :=
  (Finset.sum_sub_distrib f g).symm

/-- **THE FACE SPLIT.**  The alternating sum is the difference of the two face
sums: the total `f`-mass on the even vertices minus the total `f`-mass on the
odd vertices. -/
theorem jsp87AltSumF_eq_add {K : ℕ} (f : ℕ → ℤ) (v : Fin K → ℤ) (p0 n h : ℕ) :
    jsp87AltSumF f v p0 n h
      = (∑ s ∈ jsp87AltEven, f ((n : ℤ) + jsp87AltShift v p0 h s).toNat)
        - (∑ s ∈ jsp87AltOdd, f ((n : ℤ) + jsp87AltShift v p0 h s).toNat) := by
  have hB : (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
        (if s.card % 2 = 0 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0))
      = ∑ s ∈ jsp87AltEven, f ((n : ℤ) + jsp87AltShift v p0 h s).toNat :=
    (Finset.sum_filter _ _).symm
  have hC : (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
        (if s.card % 2 = 1 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0))
      = ∑ s ∈ jsp87AltOdd, f ((n : ℤ) + jsp87AltShift v p0 h s).toNat :=
    (Finset.sum_filter _ _).symm
  have hkey : jsp87AltSumF f v p0 n h
      = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
        ((if s.card % 2 = 0 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0)
          - (if s.card % 2 = 1 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0)) := by
    unfold jsp87AltSumF
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold jsp87Sign
    rcases Nat.mod_two_eq_zero_or_one s.card with he | ho
    · rw [if_pos he, if_neg (by omega : ¬ (s.card % 2 = 1)), if_pos he]
      ring
    · rw [if_neg (by omega : ¬ (s.card % 2 = 0)), if_pos ho,
        if_neg (by omega : ¬ (s.card % 2 = 0))]
      ring
  rw [hkey, ← sum_sub_eq, hB, hC]

/-- **THE CUBE MEASURE IS INVARIANT.**  The uniform measure on the vertices is
carried to itself by a coordinate toggle. -/
theorem jsp87_cube_invariance {ι : Type*} [AddCommGroup ι] {K : ℕ} (j : Fin K)
    (g : Finset (Fin K) → ι) :
    ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s
      = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g (jsp87AltToggle j s) := by
  set U : Finset (Finset (Fin K)) := Finset.univ
  have hmem : ∀ s : Finset (Fin K), s ∈ U → jsp87AltToggle j s ∈ U :=
    fun s _ => Finset.mem_univ _
  have hinj : ∀ a : Finset (Fin K), a ∈ U → ∀ b : Finset (Fin K), b ∈ U →
      jsp87AltToggle j a = jsp87AltToggle j b → a = b := by
    intro a _ b _ heq
    calc a = jsp87AltToggle j (jsp87AltToggle j a) := (jsp87AltToggle_invol j a).symm
      _ = jsp87AltToggle j (jsp87AltToggle j b) := congrArg (jsp87AltToggle j) heq
      _ = b := jsp87AltToggle_invol j b
  have hsurj : ∀ b : Finset (Fin K), b ∈ U →
      Exists fun a : Finset (Fin K) => Exists fun (_ : a ∈ U) =>
        jsp87AltToggle j a = b := by
    intro b _
    exact ⟨jsp87AltToggle j b, Finset.mem_univ _, by rw [jsp87AltToggle_invol]⟩
  exact (Finset.sum_bij (fun s (_ : s ∈ U) => jsp87AltToggle j s) hmem hinj hsurj
    (fun _ _ => rfl)).symm

/-- **THE INVOLUTION–SUM.**  Any `ℤ`-valued function on the vertex set that is
*odd* under one coordinate toggle sums to zero. -/
theorem jsp87_cube_cancel {K : ℕ} (j : Fin K) (g : Finset (Fin K) → ℤ)
    (hg : ∀ s : Finset (Fin K), g (jsp87AltToggle j s) = - g s) :
    ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s = 0 := by
  set U : Finset (Finset (Fin K)) := Finset.univ
  have hmem : ∀ s : Finset (Fin K), s ∈ U → jsp87AltToggle j s ∈ U :=
    fun s _ => Finset.mem_univ _
  have hinj : ∀ a : Finset (Fin K), a ∈ U → ∀ b : Finset (Fin K), b ∈ U →
      jsp87AltToggle j a = jsp87AltToggle j b → a = b := by
    intro a _ b _ heq
    calc a = jsp87AltToggle j (jsp87AltToggle j a) := (jsp87AltToggle_invol j a).symm
      _ = jsp87AltToggle j (jsp87AltToggle j b) := congrArg (jsp87AltToggle j) heq
      _ = b := jsp87AltToggle_invol j b
  have hsurj : ∀ b : Finset (Fin K), b ∈ U →
      Exists fun a : Finset (Fin K) => Exists fun (_ : a ∈ U) =>
        jsp87AltToggle j a = b := by
    intro b _
    exact ⟨jsp87AltToggle j b, Finset.mem_univ _, by rw [jsp87AltToggle_invol]⟩
  have hbij : (∑ s ∈ U, g (jsp87AltToggle j s)) = ∑ s ∈ U, g s :=
    Finset.sum_bij (fun s (_ : s ∈ U) => jsp87AltToggle j s) hmem hinj hsurj
      (fun _ _ => rfl)
  have key : (∑ s ∈ U, g s) = -(∑ s ∈ U, g s) := by
    calc (∑ s ∈ U, g s) = ∑ s ∈ U, (- g s) := by
          rw [← hbij]
          exact Finset.sum_congr rfl fun s _ => hg s
      _ = -(∑ s ∈ U, g s) := by
          rw [Finset.sum_neg_distrib]
  linarith

/-- **THE FLAGSHIP: THE GOWERS-CUBE CANCELLATION.**  For every integer-valued
function `f`, every cube of every dimension `K`, every base `p₀`, every cut
point `n` and every level `1 ≤ h ≤ K`, the `2^K`-term alternating sum of §5.2
**vanishes**: the cube degenerates in its `h`-th direction, so the sign flip is
always an exact cancellation. -/
theorem jsp87AltSumF_zero (f : ℕ → ℤ) {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) :
    jsp87AltSumF f v p0 n h = 0 := by
  have hlt : h - 1 < K := by omega
  set j : Fin K := ⟨h - 1, hlt⟩
  have hjval : j.val + 1 = h := by
    show h - 1 + 1 = h
    omega
  have hg : ∀ s : Finset (Fin K),
      jsp87Sign (jsp87AltToggle j s).card
        * f ((n : ℤ) + jsp87AltShift v p0 h (jsp87AltToggle j s)).toNat
        = - (jsp87Sign s.card * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat) := by
    intro s
    rw [jsp87AltSign_toggle, jsp87AltShift_toggle v p0 h j s hjval]
    ring
  exact jsp87_cube_cancel j (fun s => jsp87Sign s.card
    * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat) hg

/-- **THE FLAGSHIP FOR `ω`**: the Erdős function's cube sum vanishes. -/
theorem jsp87AltSum_zero {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) :
    jsp87AltSum v p0 n h = 0 := by
  rw [← jsp87AltSum_eq_jsp87AltSumF]
  exact jsp87AltSumF_zero jsp87Omega v p0 n h h1 h2

/-- **THE WHOLE CUBE, ALL LEVELS AT ONCE.**  A single choice of `n` and `p₀`
cancels at *every* level of the cube, simultaneously: this is the uniformity in
the level that the published reduction iterates over. -/
theorem jsp87AltSum_zero_all {K : ℕ} (v : Fin K → ℤ) (p0 n : ℕ) :
    ∀ h ∈ Finset.Icc 1 K, jsp87AltSum v p0 n h = 0 := by
  intro h hmem
  rw [Finset.mem_Icc] at hmem
  exact jsp87AltSum_zero v p0 n h hmem.1 hmem.2

/-- **THE MASS BALANCE OF THE CUBE.**  At a level `1 ≤ h ≤ K` the total `ω`-mass
on the even faces of the cube equals the total `ω`-mass on the odd faces: the
cancellation of §5.2, read as a statement about the two halves of the cube. -/
theorem jsp87AltSum_omega {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) :
    (∑ s ∈ jsp87AltEven, omega ((n : ℤ) + jsp87AltShift v p0 h s).toNat)
      = ∑ s ∈ jsp87AltOdd, omega ((n : ℤ) + jsp87AltShift v p0 h s).toNat := by
  have hz : jsp87AltSumF jsp87Omega v p0 n h = 0 :=
    jsp87AltSumF_zero jsp87Omega v p0 n h h1 h2
  have key := jsp87AltSumF_eq_add jsp87Omega v p0 n h
  rw [key] at hz
  unfold jsp87Omega at hz
  linarith

/-- **THE CUBE SUM IS AT MOST THE TOTAL MASS.**  Every summand is `±f` of a
vertex, so the absolute value of the cube sum is bounded by the total `f`-mass
of the `2^K` vertices. -/
theorem jsp87AltSumF_le_mass (f : ℕ → ℤ) {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ) :
    |jsp87AltSumF f v p0 n h|
      ≤ ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
        |f ((n : ℤ) + jsp87AltShift v p0 h s).toNat| := by
  have hkey : jsp87AltSumF f v p0 n h
      = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
        ((if s.card % 2 = 0 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0)
          - (if s.card % 2 = 1 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0)) := by
    unfold jsp87AltSumF
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold jsp87Sign
    rcases Nat.mod_two_eq_zero_or_one s.card with he | ho
    · rw [if_pos he, if_neg (by omega : ¬ (s.card % 2 = 1)), if_pos he]
      ring
    · rw [if_neg (by omega : ¬ (s.card % 2 = 0)), if_pos ho,
        if_neg (by omega : ¬ (s.card % 2 = 0))]
      ring
  rw [hkey]
  refine le_trans (Finset.abs_sum_le_sum_abs
    (fun s : Finset (Fin K) =>
      (if s.card % 2 = 0 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0)
        - (if s.card % 2 = 1 then f ((n : ℤ) + jsp87AltShift v p0 h s).toNat else 0))
    (Finset.univ : Finset (Finset (Fin K)))) ?_
  refine Finset.sum_le_sum fun s _ => ?_
  rcases Nat.mod_two_eq_zero_or_one s.card with he | ho
  · rw [if_pos he, if_neg (by omega : ¬ (s.card % 2 = 1))]
    simp
  · rw [if_neg (by omega : ¬ (s.card % 2 = 0)), if_pos ho]
    simp

/-! ### The same combinatorics on the window objects

The cancellation above is a fact about the *cube*, not about `ω`: it holds for
every real-valued function of the cut point.  Applied to the paper's **dilated
window** `W_p` of §5.1–5.2 it says that the alternating sum of the `2^K`
dilated windows of §5.3 vanishes exactly, so that any lower bound on a
*non-degenerate* cube sum of windows would be a contradiction — which is where
the analytic input of the published proof enters. -/

/-- The real-valued cube sum. -/
def jsp87AltSumR {K : ℕ} (f : ℕ → ℝ) (v : Fin K → ℤ) (p0 n h : ℕ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))),
    (jsp87Sign s.card : ℝ) * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat

/-- The involution–sum in `ℝ`. -/
theorem jsp87_cube_cancelR {K : ℕ} (j : Fin K) (g : Finset (Fin K) → ℝ)
    (hg : ∀ s : Finset (Fin K), g (jsp87AltToggle j s) = - g s) :
    ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s = 0 := by
  have hinv := jsp87_cube_invariance (j := j) (g := g)
  have step : (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s)
      = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), (- g s) := by
    rw [hinv]
    exact Finset.sum_congr rfl fun s _ => hg s
  have hneg : (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), (- g s))
      = - ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s := by
    rw [Finset.sum_neg_distrib]
  have key : (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s)
      = - (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s) := by
    calc (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s)
        = ∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), (- g s) := step
      _ = - (∑ s ∈ (Finset.univ : Finset (Finset (Fin K))), g s) := hneg
  linarith

/-- **THE REAL GOWERS-CUBE CANCELLATION.** -/
theorem jsp87AltSumR_zero (f : ℕ → ℝ) {K : ℕ} (v : Fin K → ℤ) (p0 n h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) :
    jsp87AltSumR f v p0 n h = 0 := by
  have hlt : h - 1 < K := by omega
  set j : Fin K := ⟨h - 1, hlt⟩
  have hjval : j.val + 1 = h := by
    show h - 1 + 1 = h
    omega
  have hg : ∀ s : Finset (Fin K),
      (jsp87Sign (jsp87AltToggle j s).card : ℝ)
        * f ((n : ℤ) + jsp87AltShift v p0 h (jsp87AltToggle j s)).toNat
        = - ((jsp87Sign s.card : ℝ)
          * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat) := by
    intro s
    rw [jsp87AltSign_toggle, jsp87AltShift_toggle v p0 h j s hjval]
    push_cast
    ring
  exact jsp87_cube_cancelR j (fun s => (jsp87Sign s.card : ℝ)
    * f ((n : ℤ) + jsp87AltShift v p0 h s).toNat) hg

/-- **THE DILATED-WINDOW CUBE SUM VANISHES.**  The `2^K` alternating sum of the
paper's dilated windows `W_p` over the cube of §5.2–5.3 is exactly `0`. -/
theorem jsp87AltWinD_zero {K : ℕ} (v : Fin K → ℤ) (p0 n p h : ℕ)
    (h1 : 1 ≤ h) (h2 : h ≤ K) :
    jsp87AltSumR (fun m => jsp87WinD m p) v p0 n h = 0 :=
  jsp87AltSumR_zero (fun m => jsp87WinD m p) v p0 n h h1 h2

end JSP87
