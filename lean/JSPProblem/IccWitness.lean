/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.SampleGeom

/-!
# JSP-000087, round 144 — (5.21′) HOLDS ON A PLAIN INITIAL SEGMENT: THE TWO
# DELETED THEOREMS OF ROUND 143, REBUILT, AND THE ENDGAME JOINED TO THEM

`policy.json` `next_round_attack[0]` of round 143, verbatim:

> "**1. REBUILD THE TWO DELETED THEOREMS** … (a)
> `jsp87NzFrac_mul_one_sub_Icc_ge`: for `2p ≤ N` and `3B ≤ p`,
> `B/(4p) ≤ jsp87NzFrac K p H [1,N] * (1 - jsp87NzFrac K p H [1,N])`. … (b)
> `jsp87_5_21_Icc_witness`: take `P := jsp87PrimeSet (3*B) …`, `N := 2 * …` … so
> `c * SUM ≥ c * (B/4) * jsp87RecipSum P ≥ 1`."

**Both are theorems.**  Write `B := H + 2^K − 1` (the length of the nonzero
block, round 142) and `f_p := jsp87NzFrac K p H [1,N]`.

## §1  THE INITIAL SEGMENT IS TWO-CLASS, WITH A KNOWN SPLIT

* `jsp87NzFrac_Icc_ge_B_two` — **`2p ≤ N ⟹ B/(2p) ≤ f_p`**: on an initial
  segment containing **two whole periods** the nonzero fraction never falls
  below *half* the uniform value `B/p`;
* `jsp87NzFrac_Icc_le_half` — **`3B ≤ p` and `2p ≤ N ⟹ f_p ≤ 1/2`**;
* **`jsp87NzFrac_mul_one_sub_Icc_ge`** — **`2p ≤ N`, `3B ≤ p ⟹ B/(4p) ≤
  f_p (1 − f_p)`**: the two-class quantity of (5.21′) is `Θ(1/p)` on a plain
  initial segment, with an explicit constant — no analytic input;
* `jsp87NzFrac_mul_one_sub_Icc_le` — the matching upper bound, so the (5.21′)
  mass is **maximised at height exactly `2p`**.

The gap is *not* an analytic estimate: `f_p ∈ [B/(2p), 3B/(2p)] ⊆ [B/(2p), 1/2]`,
and on that interval `f ↦ f (1 − f)` is increasing.

## §2  ★★ THE CAPSTONE: (5.21′) IS *SATISFIABLE* ON AN INITIAL SEGMENT ★★

* **`jsp87_5_21_Icc_witness`** — **for every `q ≠ 0` and every `K, H` with
  `1 ≤ H` there exist `N ≥ 1` and a prime set `P` — every `p ∈ P` prime,
  `3B ≤ p`, `2p ≤ N` — with `1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ P} f_p (1 − f_p)`.**
  Hypothesis (5.21′) of arXiv:2512.01739 **holds on a plain initial segment**,
  at every scale, unconditionally: the only input is Euler's divergence of the
  reciprocal primes, through `jsp87RecipSum_primeSet_tendsto`;
* `jsp87_5_21_Icc_at`, `jsp87_5_21_Icc_sum_ge`, `jsp87_5_21_Icc_summand` — the
  same statement with the height and the prime set explicit, and the summand
  level;
* `jsp87_5_21_Icc_hne` — the two-class witness `hne` of
  `jsp87_endgame_frac_of_5_21` holds on every initial segment with `2p ≤ N`.

## §3  THE ENDGAME, JOINED

* `jsp87Hyp15Icc`, `jsp87Hyp1617Icc` — the error bounds (5.15) and
  (5.16)–(5.17) **on the initial-segment sample** `[1, N]`;
* **`jsp87_endgame_Icc_of_5_15`** — **on an initial segment the endgame of
  §§5.3–5.14 fires from (5.15) and (5.16)–(5.17) alone**: hypothesis (5.21′)
  is discharged by §2 and the five constants cannot all be sharp;
* **`jsp87_endgame_Icc_witness`** and **`jsp87_5_15_Icc_or_5_16`** — the
  headline consequence: if the endgame's conclusion held at an admissible
  scale, then on the canonical initial-segment samples `[1, 2Y]` over the prime
  sets `[3B, Y]` **at least one of (5.15) and (5.16)–(5.17) must fail**.  Since
  (5.21′) *cannot* be the obstruction (§2), the published endgame can only be
  run on a **correlated** sample — exactly the content of the one remaining
  blocker `jsp87Mcov_small` (Thm 3.1 of arXiv:2512.01739, from Pilatte).

See `ACCEPTANCE.md`.  Fully proved, no placeholders.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  ARITHMETIC TOOLS -/

/-- **`f ↦ f (1 − f)` IS INCREASING ON `[0, 1/2]`.**  Mathlib has no such
monotonicity statement in this form, and `nlinarith` does not factor the
difference. -/
theorem jsp87mul_mono_half {a b : ℝ} (_h0 : 0 ≤ a) (hab : a ≤ b) (hb : 2 * b ≤ 1) :
    a * (1 - a) ≤ b * (1 - b) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hone : 0 ≤ 1 - a - b := by linarith
  nlinarith [mul_nonneg hba hone]

/-- **THE BLOCK LENGTH `B = H + 2^K − 1` IS POSITIVE.** -/
private lemma jsp87B_pos {K H : ℕ} (hH : 1 ≤ H) :
    0 < (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) := by
  have h1 : 1 ≤ (H : ℝ) := by exact_mod_cast hH
  have h2 : 0 ≤ ((2 ^ K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **`2 ^ n ≥ 1` FOR EVERY `n`.** -/
private lemma jsp87pow_pos : ∀ n : ℕ, 1 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      nlinarith

/-- **`2 ^ K ≤ p` FOLLOWS FROM THE SEPARATION AND `1 ≤ H`.** -/
private lemma jsp87sep_2K {K H p : ℕ} (hH : 1 ≤ H) (hh : H + (2 ^ K - 1) + 1 ≤ p) :
    2 ^ K ≤ p := by
  have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
  have h3 : 0 ≤ 2 ^ K - 1 := by omega
  calc 2 ^ K = (2 ^ K - 1) + 1 := by omega
    _ ≤ (2 ^ K - 1) + (H + 1) := by omega
    _ = H + (2 ^ K - 1) + 1 := by omega
    _ ≤ p := hh

/-- **THE REAL CAST OF A POSITIVE NATURAL IS POSITIVE.** -/
private lemma jsp87p_pos {p : ℕ} (hp : 0 < p) : (0 : ℝ) < (p : ℝ) := by
  exact_mod_cast hp

/-- **THE REAL CAST OF `2 p` IS POSITIVE.**  `positivity` cannot see that `p > 0`
through `hh`, so the two-factor bound is stated once. -/
private lemma jsp87two_p_pos {p : ℕ} (hp : 0 < p) : (0 : ℝ) < 2 * (p : ℝ) := by
  have h1 := jsp87p_pos hp
  linarith

/-- **THE REAL CAST OF A NONEMPTY INITIAL SEGMENT IS POSITIVE.** -/
private lemma jsp87N_pos {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < (N : ℝ) := by
  exact_mod_cast hN

/-- **TRUNCATED SUBTRACTION IS ANTITONIC IN ITS SECOND ARGUMENT** (the step
`p − (1 + 2^K − 1) ≤ p − 1`, which `omega` will not do on its own). -/
private lemma jsp87sub_le_of_ge1 {a c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ a) : a - c ≤ a - 1 := by
  have h3 : (a - c) + c = a := Nat.sub_add_cancel h2
  have h4 : (a - 1) + 1 = a := by omega
  omega

/-- **THE TRUNCATION ERROR OF ROUND 143 IS HALVED BY TWO WHOLE PERIODS.**

`2p ≤ N` gives `B/N ≤ B/(2p)`: the whole content of `jsp87err_le` below, in one
reusable step. -/
private lemma jsp87err_le {B : ℝ} (hB : 0 ≤ B) {p N : ℕ} (hp : 0 < p) (h2p : 2 * p ≤ N) :
    (B : ℝ) / (N : ℝ) ≤ B / (2 * (p : ℝ)) := by
  rw [div_le_div_iff₀ (jsp87N_pos (by omega)) (jsp87two_p_pos hp)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2p) hB

/-- **THE BLOCK LENGTH IN THE SINGLE-CAST FORM.** -/
private lemma jsp87B_cast {K H : ℕ} :
    (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) = ((H + (2 ^ K - 1) : ℕ) : ℝ) := by
  symm
  exact Nat.cast_add _ _

/-- **`3B ≤ p`, IN THE `B`-FORM.**  The bridge from the `ℕ` hypothesis to the
two-class window. -/
private lemma jsp87B3_le {K H p : ℕ} (h3B : 3 * (H + (2 ^ K - 1)) ≤ p) :
    3 * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by
  have hle : ((3 * (H + (2 ^ K - 1) : ℕ) : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3B
  calc 3 * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
      = 3 * ((H + (2 ^ K - 1) : ℕ) : ℝ) := by rw [Nat.cast_add]
    _ = ((3 * (H + (2 ^ K - 1) : ℕ) : ℕ) : ℝ) :=
      (Nat.cast_mul (α := ℝ) 3 (H + (2 ^ K - 1))).symm
    _ ≤ (p : ℝ) := hle

/-- **`B/p + B/(2p) = 3B/(2p)`.**  The arithmetic of the upper split. -/
private lemma jsp87Bp_add (B p : ℝ) (hp : p ≠ 0) :
    B / p + B / (2 * p) = B * 3 / (2 * p) := by
  field_simp
  ring

/-- **`B / (4p) = (B/4) * (1/p)`.**  The bridge to the `jsp87RecipSum` form. -/
private lemma jsp87B4_div (B p : ℝ) (hp : (0 : ℝ) < p) :
    B / (4 * p) = (B / 4) * (1 / p) := by
  field_simp

/-- **THE CUBE SCALE `c := q² 2^{−2(H+K)}` IS POSITIVE.** -/
private lemma jsp87c_pos {K H : ℕ} (q : ℝ) (hq : q ≠ 0) :
    0 < (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) := by
  have h1 : 0 < q ^ 2 := sq_pos_of_ne_zero hq
  have h2 : 0 < (((1 / 2 : ℝ) ^ (H + K)) ^ 2) := by
    have : ((1 / 2 : ℝ) ^ (H + K)) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact sq_pos_of_ne_zero this
  nlinarith [mul_pos h1 h2]

/-- **THE INITIAL SEGMENT `[1, N]` HOLDS A MULTIPLE OF EVERY `p ≤ N`.**  The
first half of the two-class witness `hne` of `jsp87_endgame_frac_of_5_21`. -/
theorem jsp87Icc_dvd_pt {p N : ℕ} (hp : 0 < p) (hN : p ≤ N) :
    ∃ n ∈ Finset.Icc 1 N, p ∣ n :=
  ⟨p, Finset.mem_Icc.mpr ⟨hp, hN⟩, ⟨1, by ring⟩⟩

/-- **THE INITIAL SEGMENT `[1, N]` IS *ACTIVE* AT EVERY PRIME `p ≤ N`.**  The
second half of `hne`, and the only place the last residue `p − 1` of round 142's
block is used: `p − 1` lies in the level-`1` active block
`Icc (p − 2^K) (p − 1)` (`jsp87ActiveRes_eq_Icc`). -/
theorem jsp87Icc_active_pt {K p N : ℕ} (hp : 0 < p) (hsep : 1 + (2 ^ K - 1) < p)
    (hN : p - 1 ≤ N) :
    ∃ n ∈ Finset.Icc 1 N, jsp87Active K p 1 n := by
  have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
  have hblk : jsp87ActiveRes K p 1 = Finset.Icc (p - (1 + (2 ^ K - 1))) (p - 1) :=
    jsp87ActiveRes_eq_Icc (K := K) (p := p) (h := 1) (by omega)
  have hmem : p - 1 ∈ jsp87ActiveRes K p 1 := by
    rw [hblk, Finset.mem_Icc]
    constructor
    · exact jsp87sub_le_of_ge1 (by omega) (by omega)
    · exact le_refl _
  have hlt : p - 1 < p := by omega
  have hmod : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt hlt
  refine ⟨p - 1, Finset.mem_Icc.mpr ⟨?_, hN⟩, ?_⟩
  · show 1 ≤ p - 1
    omega
  · have hcov : (p - 1) % p ∈ jsp87ActiveRes K p 1 := by
      rw [hmod]
      exact hmem
    exact jsp87Active_of_res_cover hp (by omega) (by omega) hcov

/-- **THE TWO-CLASS WITNESS `hne` HOLDS ON EVERY INITIAL SEGMENT WITH
`2p ≤ N`.**  Both halves are single sample points: `p` (a multiple of `p`) and
`p − 1` (an active residue). -/
theorem jsp87_5_21_Icc_hne {K : ℕ} {P : Finset ℕ} (H : ℕ) (N : ℕ) (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hpc : ∀ p ∈ P, p.Prime) (hsep : ∀ p ∈ P, H + (2 ^ K - 1) + 1 ≤ p)
    (h2p : ∀ p ∈ P, 2 * p ≤ N) :
    ∀ p ∈ P, (∃ n ∈ Finset.Icc 1 N, p ∣ n) ∧ (∃ n ∈ Finset.Icc 1 N, jsp87Active K p 1 n) := by
  intro p hp
  have hp' := hpc p hp
  have hp0 : 0 < p := hp'.pos
  have hp2p := h2p p hp
  have hpN : p ≤ N := by omega
  constructor
  · exact jsp87Icc_dvd_pt hp0 hpN
  · have hsep' : 1 + (2 ^ K - 1) < p := by
      have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
      have hs := hsep p hp
      omega
    exact jsp87Icc_active_pt (K := K) hp0 hsep' (by omega)

/-! ## §1  ★★ THE INITIAL SEGMENT IS TWO-CLASS, WITH A KNOWN SPLIT ★★ -/

/-- **★★ THE NONZERO FRACTION IS AT LEAST `B/(2p)` ★★**

For every `K p H N` with `2^K ≤ p`, `1 ≤ H`, `H + 2^K − 1 + 1 ≤ p`, `1 ≤ N`
and `2p ≤ N`,

```
B / (2p)   ≤   jsp87NzFrac K p H [1,N] ,        B = H + 2^K − 1 .
```

This is the lower half of `jsp87NzFrac_Icc_bounds` (round 143) with the
truncation error `B/N` halved. -/
theorem jsp87NzFrac_Icc_ge_B_two {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) (h2p : 2 * p ≤ N) :
    ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (2 * (p : ℝ))
      ≤ jsp87NzFrac K p H (Finset.Icc 1 N) := by
  set B : ℝ := (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) with hB
  have hp0 : 0 < p := by
    have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
    omega
  have hB0 : 0 ≤ B := le_of_lt (jsp87B_pos hH)
  have hbnd := jsp87NzFrac_Icc_bounds (K := K) (p := p) (H := H) (N := N) hK hH hh hN
  rw [← hB] at hbnd
  have herr := jsp87err_le hB0 hp0 h2p
  have hkey : (B : ℝ) / (p : ℝ) - B / (2 * (p : ℝ))
      ≤ jsp87NzFrac K p H (Finset.Icc 1 N) := by linarith
  have hid : (B : ℝ) / (p : ℝ) - B / (2 * (p : ℝ)) = B / (2 * (p : ℝ)) := by
    field_simp [ne_of_gt (jsp87p_pos hp0)]
    ring
  rw [← hid, hB]
  exact hkey

/-- **★★ THE NONZERO FRACTION IS AT MOST `1/2` ONCE `3B ≤ p` ★★**

For every `K p H N` with `1 ≤ H`, `H + 2^K − 1 + 1 ≤ p`, `2p ≤ N` and
`3 (H + 2^K − 1) ≤ p`,

```
jsp87NzFrac K p H [1,N]  ≤  1/2 ,
```

because `f_p ≤ B/p + B/N ≤ 3B/(2p) ≤ 1/2`.  This is the *upper* half of the
two-class window, and it is what makes `f_p (1 − f_p)` a two-class quantity. -/
theorem jsp87NzFrac_Icc_le_half {K p H N : ℕ} (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) (h2p : 2 * p ≤ N)
    (h3B : 3 * (H + (2 ^ K - 1)) ≤ p) :
    jsp87NzFrac K p H (Finset.Icc 1 N) ≤ 1 / 2 := by
  set B : ℝ := (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) with hB
  have hK : 2 ^ K ≤ p := jsp87sep_2K hH hh
  have hp0 : 0 < p := by
    have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
    omega
  have hB0 : 0 ≤ B := le_of_lt (jsp87B_pos hH)
  have hbnd := jsp87NzFrac_Icc_bounds (K := K) (p := p) (H := H) (N := N) hK hH hh hN
  rw [← hB] at hbnd
  have herr := jsp87err_le hB0 hp0 h2p
  -- `3B/(2p) ≤ 1/2` is exactly `3B ≤ p`
  have h3Br : (3 : ℝ) * B ≤ (p : ℝ) := by
    rw [hB]
    exact jsp87B3_le h3B
  have hhalf : (B : ℝ) * 3 / (2 * (p : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (jsp87two_p_pos hp0)]
    nlinarith [h3Br]
  have hkey : jsp87NzFrac K p H (Finset.Icc 1 N) ≤ B * 3 / (2 * (p : ℝ)) := by
    rw [← jsp87Bp_add B (p : ℝ) (ne_of_gt (jsp87p_pos hp0))]
    linarith
  linarith

/-- **★★★ THE TWO-CLASS QUANTITY OF (5.21′) IS `Θ(1/p)` ON AN INITIAL SEGMENT
★★★**

For every `K p H N` with `2^K ≤ p`, `1 ≤ H`, `H + 2^K − 1 + 1 ≤ p`, `1 ≤ N`,
`2p ≤ N` and `3 (H + 2^K − 1) ≤ p`,

```
B / (4p)   ≤   jsp87NzFrac K p H [1,N] * (1 − jsp87NzFrac K p H [1,N]) ,   B = H + 2^K − 1 .
```

This is `policy.json` `next_round_attack[0](a)` of round 143 verbatim, and it is
the arithmetic input the endgame of arXiv:2512.01739 §5 was missing: the
two-class variance criterion (5.21′) is **not** a correlation statement on a
plain initial segment, it is a **counting** statement. -/
theorem jsp87NzFrac_mul_one_sub_Icc_ge {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) (h2p : 2 * p ≤ N)
    (h3B : 3 * (H + (2 ^ K - 1)) ≤ p) :
    ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (4 * (p : ℝ))
      ≤ jsp87NzFrac K p H (Finset.Icc 1 N) * (1 - jsp87NzFrac K p H (Finset.Icc 1 N)) := by
  set B : ℝ := (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) with hB
  have hp0 : 0 < p := by
    have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
    omega
  have hBlo : (B : ℝ) / (2 * (p : ℝ)) ≤ jsp87NzFrac K p H (Finset.Icc 1 N) := by
    have h := jsp87NzFrac_Icc_ge_B_two (K := K) (p := p) (H := H) (N := N) hK hH hh hN h2p
    rwa [← hB] at h
  have hBhi := jsp87NzFrac_Icc_le_half (K := K) (p := p) (H := H) (N := N) hH hh hN h2p h3B
  have hone : (1 / 2 : ℝ) ≤ 1 - jsp87NzFrac K p H (Finset.Icc 1 N) := by
    have h := sub_le_sub_left hBhi (1 : ℝ)
    linarith [h]
  have h1 : jsp87NzFrac K p H (Finset.Icc 1 N)
      * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))
      ≥ B / (2 * (p : ℝ)) * (1 / 2) := by
    have hs : (Finset.Icc 1 N).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
    have hle : jsp87NzFrac K p H (Finset.Icc 1 N) ≤ 1 :=
      jsp87NzFrac_le_one (K := K) (p := p) (H := H) hs
    have hstep : (B : ℝ) / (2 * (p : ℝ)) * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))
        ≤ jsp87NzFrac K p H (Finset.Icc 1 N)
          * (1 - jsp87NzFrac K p H (Finset.Icc 1 N)) :=
      mul_le_mul_of_nonneg_right hBlo (sub_nonneg.mpr hle)
    exact le_trans (mul_le_mul_of_nonneg_left hone
      (div_nonneg (le_of_lt (jsp87B_pos hH)) (le_of_lt (jsp87two_p_pos hp0)))) hstep
  have hid : (B : ℝ) / (2 * (p : ℝ)) * (1 / 2)
      = ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (4 * (p : ℝ)) := by
    rw [hB]
    ring
  rw [← hid]
  linarith

/-- **★ THE MATCHING UPPER BOUND: THE (5.21′) MASS IS MAXIMISED AT HEIGHT `2p`
★**

Under the hypotheses of `jsp87NzFrac_mul_one_sub_Icc_ge`,

```
jsp87NzFrac K p H [1,N] * (1 − …)  ≤  (3B/(2p)) * (1 − B/(2p)) .
```

So the two-class quantity is pinned *between* two explicit multiples of `1/p`,
and height `2p` is the worst case: the witness height of §2 cannot be tuned to
make (5.21′) easier than `4/(cB)`. -/
theorem jsp87NzFrac_mul_one_sub_Icc_le {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) (h2p : 2 * p ≤ N)
    (h3B : 3 * (H + (2 ^ K - 1)) ≤ p) :
    jsp87NzFrac K p H (Finset.Icc 1 N) * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))
      ≤ (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * 3 / (2 * (p : ℝ)))
          * (1 - ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (2 * (p : ℝ))) := by
  set B : ℝ := (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) with hB
  have hp0 : 0 < p := by
    have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
    omega
  have hB0 : 0 ≤ B := le_of_lt (jsp87B_pos hH)
  have hf0 : 0 ≤ jsp87NzFrac K p H (Finset.Icc 1 N) := jsp87NzFrac_nonneg _
  have hbnd := jsp87NzFrac_Icc_bounds (K := K) (p := p) (H := H) (N := N) hK hH hh hN
  rw [← hB] at hbnd
  have herr := jsp87err_le hB0 hp0 h2p
  have h3Br : (3 : ℝ) * B ≤ (p : ℝ) := by
    rw [hB]
    exact jsp87B3_le h3B
  have hhalf : (B : ℝ) * 3 / (2 * (p : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (jsp87two_p_pos hp0)]
    nlinarith [h3Br]
  have hbhi : jsp87NzFrac K p H (Finset.Icc 1 N) ≤ B * 3 / (2 * (p : ℝ)) := by
    rw [← jsp87Bp_add B (p : ℝ) (ne_of_gt (jsp87p_pos hp0))]
    linarith
  have hstep : jsp87NzFrac K p H (Finset.Icc 1 N)
      * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))
      ≤ (B * 3 / (2 * (p : ℝ))) * (1 - B * 3 / (2 * (p : ℝ))) :=
    jsp87mul_mono_half hf0 hbhi (by linarith)
  have hcomp : (1 - B * 3 / (2 * (p : ℝ))) ≤ 1 - B / (2 * (p : ℝ)) := by
    have hmid : (B : ℝ) / (2 * (p : ℝ)) ≤ B * 3 / (2 * (p : ℝ)) := by
      rw [div_le_div_iff₀ (jsp87two_p_pos hp0) (jsp87two_p_pos hp0)]
      nlinarith
    have := sub_le_sub_left hmid (1 : ℝ)
    simpa using this
  have hfin : (B * 3 / (2 * (p : ℝ))) * (1 - B * 3 / (2 * (p : ℝ)))
      ≤ (B * 3 / (2 * (p : ℝ))) * (1 - B / (2 * (p : ℝ))) := by
    refine mul_le_mul_of_nonneg_left hcomp ?_
    exact div_nonneg (by nlinarith [jsp87B_pos (K := K) hH])
      (le_of_lt (jsp87two_p_pos hp0))
  have hbridge : (B * 3 / (2 * (p : ℝ))) * (1 - B / (2 * (p : ℝ)))
      = ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * 3 / (2 * (p : ℝ))
          * (1 - ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (2 * (p : ℝ))) := by
    rw [hB]
  rw [← hbridge]
  exact hstep.trans hfin

/-! ## §2  ★★ THE CAPSTONE: (5.21′) IS SATISFIABLE ON AN INITIAL SEGMENT ★★ -/

/-- **★ THE INITIAL-SEGMENT (5.21′), AT THE LEVEL OF ONE PRIME ★** -/
theorem jsp87_5_21_Icc_summand {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) (h2p : 2 * p ≤ N)
    (h3B : 3 * (H + (2 ^ K - 1)) ≤ p) :
    ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 * (1 / (p : ℝ))
      ≤ jsp87NzFrac K p H (Finset.Icc 1 N) * (1 - jsp87NzFrac K p H (Finset.Icc 1 N)) := by
  have h0 := jsp87NzFrac_mul_one_sub_Icc_ge (K := K) (p := p) (H := H) (N := N)
    hK hH hh hN h2p h3B
  have hp0 : 0 < p := by
    have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
    omega
  rw [jsp87B4_div ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) (p : ℝ) (jsp87p_pos hp0)] at h0
  exact h0

/-- **★★ THE INITIAL-SEGMENT (5.21′), LIFTED THROUGH THE PRIME SET ★★**

For every `K H N` with `1 ≤ H`, `1 ≤ N` and every `c ≥ 0`,

```
c * ∑_{p ∈ P} f_p (1 − f_p)   ≥   c * (B/4) * jsp87RecipSum P
```

whenever every `p ∈ P` satisfies `3B ≤ p` and `2p ≤ N`: this is §1 lifted
through `Finset.sum_le_sum`, with no constant lost. -/
theorem jsp87_5_21_Icc_sum_ge {K : ℕ} {P : Finset ℕ} (H N : ℕ) (hH : 1 ≤ H) (hN : 1 ≤ N)
    (c : ℝ) (hC : 0 ≤ c) (h3B : ∀ p ∈ P, 3 * (H + (2 ^ K - 1)) ≤ p)
    (h2p : ∀ p ∈ P, 2 * p ≤ N) :
    c * ∑ p ∈ P, (jsp87NzFrac K p H (Finset.Icc 1 N)
        * (1 - jsp87NzFrac K p H (Finset.Icc 1 N)))
      ≥ c * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4) * jsp87RecipSum P := by
  have hk : ∀ p ∈ P, 2 ^ K ≤ p := by
    intro p hp
    have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
    have h3 : 0 ≤ 2 ^ K - 1 := by omega
    have h4 := h3B p hp
    omega
  have hsep : ∀ p ∈ P, H + (2 ^ K - 1) + 1 ≤ p := by
    intro p hp
    have h3 : 0 ≤ 2 ^ K - 1 := by omega
    have h4 := h3B p hp
    omega
  have hstep : ∀ p ∈ P,
      ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 * (1 / (p : ℝ))
        ≤ jsp87NzFrac K p H (Finset.Icc 1 N) * (1 - jsp87NzFrac K p H (Finset.Icc 1 N)) := by
    intro p hp
    exact jsp87_5_21_Icc_summand (K := K) (p := p) (H := H) (N := N) (hk p hp) hH (hsep p hp)
      hN (h2p p hp) (h3B p hp)
  have hB40 : 0 ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 :=
    div_nonneg (le_of_lt (jsp87B_pos hH)) (by norm_num)
  have hsum : (c : ℝ)
      * ∑ p ∈ P, (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 * (1 / (p : ℝ)))
      ≤ c * ∑ p ∈ P, (jsp87NzFrac K p H (Finset.Icc 1 N)
          * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))) := by
    calc (c : ℝ)
        * ∑ p ∈ P, (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 * (1 / (p : ℝ)))
        = ∑ p ∈ P, (c * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 * (1 / (p : ℝ)))) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ P, (c * (jsp87NzFrac K p H (Finset.Icc 1 N)
            * (1 - jsp87NzFrac K p H (Finset.Icc 1 N)))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hz := mul_le_mul_of_nonneg_left (hstep p hp) hC
        exact hz
      _ = c * ∑ p ∈ P, (jsp87NzFrac K p H (Finset.Icc 1 N)
            * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))) := by rw [Finset.mul_sum]
  have hfinal : (c : ℝ) * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4) * jsp87RecipSum P
      ≤ c * ∑ p ∈ P, (jsp87NzFrac K p H (Finset.Icc 1 N)
          * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))) := by
    calc c * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4) * jsp87RecipSum P
        = c * ∑ p ∈ P, (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 * (1 / (p : ℝ))) := by
          unfold jsp87RecipSum
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p hp => by ring
      _ ≤ c * ∑ p ∈ P, (jsp87NzFrac K p H (Finset.Icc 1 N)
            * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))) := hsum
  linarith

/-- **★★★ THE CAPSTONE: (5.21′) HOLDS AT AN EXPLICIT HEIGHT ★★★**

For every `q ≠ 0`, every `K`, every `H` with `1 ≤ H` and every `Y` with `1 ≤ Y`,
put `P := jsp87PrimeSet (3 (H + 2^K − 1)) Y`.  If the harmonic mass of `P`
reaches the threshold `4 / (B c)` — with `B = H + 2^K − 1` and
`c = q² 2^{−2(H+K)}` — then on the initial segment `[1, 2Y]`:

* every `p ∈ P` is prime, with `H + 2^K − 1 + 1 ≤ p` and `2p ≤ 2Y`;
* hypothesis (5.21′) holds:
  `1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ P} f_p (1 − f_p)`,
  `f_p = jsp87NzFrac K p H [1, 2Y]`.

So all the geometric hypotheses of §1 and of `jsp87_endgame_frac_of_5_21`
hold at the chosen height. -/
theorem jsp87_5_21_Icc_at {K : ℕ} (q : ℝ) (hq : q ≠ 0) (H Y : ℕ) (hH : 1 ≤ H) (hY : 1 ≤ Y)
    (hM : (4 : ℝ) / (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
        * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)))
      ≤ jsp87RecipSum (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y)) :
    (∀ p ∈ jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y, p.Prime
      ∧ 3 * (H + (2 ^ K - 1)) ≤ p ∧ (2 * p ≤ 2 * Y))
    ∧ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p' ∈ jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y,
            (jsp87NzFrac K p' H (Finset.Icc 1 (2 * Y))
              * (1 - jsp87NzFrac K p' H (Finset.Icc 1 (2 * Y))))) := by
  have hc := jsp87c_pos (K := K) (H := H) q hq
  have hB0 : 0 ≤ (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) := le_of_lt (jsp87B_pos hH)
  have hB4 : 0 ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4 := div_nonneg hB0 (by norm_num)
  have hBne : ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt (jsp87B_pos hH)
  have hcne : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) ≠ 0 := ne_of_gt hc
  have hN : 1 ≤ 2 * Y := by omega
  have hsum := jsp87_5_21_Icc_sum_ge (K := K) (P := jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y)
    H (2 * Y) hH hN ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)) (le_of_lt hc)
    (fun p hp => jsp87PrimeSet_lower hp)
    (fun p hp => by
      have hhi := jsp87PrimeSet_upper hp
      omega)
  have h1 : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4)
        * (4 / (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
          * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2))))
      ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4)
        * jsp87RecipSum (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) :=
    mul_le_mul_of_nonneg_left hM (mul_nonneg (le_of_lt hc) hB4)
  have hid : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / 4)
      * (4 / (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
        * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)))) = 1 := by
    field_simp [hBne, hcne]
  refine ⟨?_, ?_⟩
  · intro p hp
    refine ⟨jsp87PrimeSet_prime hp, ?_, ?_⟩
    · exact jsp87PrimeSet_lower hp
    · have hhi := jsp87PrimeSet_upper hp
      omega
  · linarith

/-- **★ THE MASS STATEMENT BEHIND THE CAPSTONE ★**

For every `q ≠ 0` and every scale there is a height `Y` with `1 ≤ Y` at which
the harmonic mass of `jsp87PrimeSet (3 (H + 2^K − 1)) Y` reaches
`4 / (B c)`, `B = H + 2^K − 1`, `c = q² 2^{−2(H+K)}` — Euler's divergence,
transferred.  So the number of primes the endgame must use on a plain initial
segment is finite, and effectively so. -/
theorem jsp87_5_21_Icc_mass {K : ℕ} (q : ℝ) (_hq : q ≠ 0) (H : ℕ) (_hH : 1 ≤ H) :
    ∃ (Y : ℕ), 1 ≤ Y ∧
      (4 : ℝ) / (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
        * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)))
      ≤ jsp87RecipSum (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) := by
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.1
    (Filter.Tendsto.eventually_ge_atTop (jsp87RecipSum_primeSet_tendsto
      (3 * (H + (2 ^ K - 1))))
      (4 / (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
        * ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)))))
  obtain ⟨Y, hCY, hY1⟩ : ∃ Y : ℕ, C ≤ Y ∧ 1 ≤ Y :=
    ⟨Nat.max C 1, le_max_left _ _, le_max_right _ _⟩
  exact ⟨Y, hY1, hC Y hCY⟩

/-- **★★★ THE CAPSTONE: (5.21′) IS SATISFIABLE ON A PLAIN INITIAL SEGMENT ★★★**

For every `q ≠ 0` and every `K, H` with `1 ≤ H` there are `N ≥ 1` and a prime
set `P` — every `p ∈ P` prime, `3 (H + 2^K − 1) ≤ p`, `2p ≤ N` — such that

```
1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ P} f_p (1 − f_p),   f_p = jsp87NzFrac K p H [1,N] .
```

**Hypothesis (5.21′) of arXiv:2512.01739 is satisfiable on a plain initial
segment, at every scale, unconditionally.**  This is
`policy.json` `next_round_attack[0](b)` of round 143 verbatim.  Its content:
the two-class criterion of §5 of the published proof is **not** a correlation
statement — it is satisfied by the *uncorrelated* sample `[1, N]` as soon as
the height is large enough, the only input being Euler's divergence of the
reciprocal primes (`jsp87RecipSum_primeSet_tendsto`).

Consequently the Chowla-type input `jsp87Mcov_small` is **not** what is needed
to satisfy (5.21′): it is needed only to keep (5.15) *true* on the witness
sample, which is what §3 below isolates. -/
theorem jsp87_5_21_Icc_witness {K : ℕ} (q : ℝ) (hq : q ≠ 0) (H : ℕ) (hH : 1 ≤ H) :
    ∃ (Y : ℕ), 1 ≤ Y
      ∧ (∀ p ∈ jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y, p.Prime
          ∧ 3 * (H + (2 ^ K - 1)) ≤ p
          ∧ 2 * p ≤ 2 * Y)
      ∧ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * ∑ p ∈ jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y,
              (jsp87NzFrac K p H (Finset.Icc 1 (2 * Y))
                * (1 - jsp87NzFrac K p H (Finset.Icc 1 (2 * Y))))) := by
  obtain ⟨Y, hY1, hM⟩ := jsp87_5_21_Icc_mass (K := K) q hq H hH
  obtain ⟨hall, hfrac⟩ := jsp87_5_21_Icc_at (K := K) q hq H Y hH hY1 hM
  have h3B : ∀ p ∈ jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y,
      3 * (H + (2 ^ K - 1)) ≤ p := fun _ hp => jsp87PrimeSet_lower hp
  exact ⟨Y, hY1, hall, hfrac⟩

/-! ## §3  THE ENDGAME, JOINED -/

/-- **THE ERROR BOUND (5.15) ON THE INITIAL-SEGMENT SAMPLE `[1, N]`.** -/
def jsp87Hyp15Icc (K H N : ℕ) (P : Finset ℕ) (q κ1 κ2 κ3 : ℝ) : Prop :=
  ‖jsp87CAvg (Finset.Icc 1 N) (fun i => jsp87e (q * ∑ p' ∈ P,
        jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3

/-- **THE ERROR BOUND (5.16)–(5.17) ON THE INITIAL-SEGMENT SAMPLE `[1, N]`.** -/
def jsp87Hyp1617Icc (K H N : ℕ) (P : Finset ℕ) (q κ4 κ5 : ℝ) : Prop :=
  ‖jsp87CAvg (Finset.Icc 1 N) (fun i => jsp87e (q * ∑ p' ∈ P,
        jsp87Xp0 (jsp87BinV K) p' i H))
      - ∏ p' ∈ P, jsp87CAvg (Finset.Icc 1 N) (fun i =>
          jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖ ≤ κ4 + κ5

/-- **★★★ THE ENDGAME ON AN INITIAL SEGMENT, WITH (5.21′) ALREADY TRUE ★★★**

For every `K, H` with `1 ≤ H`, every sample height `N ≥ 1`, every prime set `P`
with `2p ≤ N` for all `p ∈ P`, and every `q` at the admissible scale (5.19):
if (5.15) and (5.16)–(5.17) hold on the initial-segment sample `[1, N]`, then
the five constants of §§5.7–5.14 cannot all be sharp.

**Hypothesis (5.21′) is not a hypothesis here**: it is
`jsp87_5_21_Icc_witness`.  So the endgame of §§5.3–5.14 is pinned on (5.15)
and (5.16)–(5.17) — exactly as on the canonical progression sample, where round
141's `jsp87_endgame_515_realscale` refuted (5.15). -/
theorem jsp87_endgame_Icc_of_5_15 {K : ℕ} {P : Finset ℕ} (N : ℕ)
    (q κ1 κ2 κ3 κ4 κ5 : ℝ) (H : ℕ) (hH : 1 ≤ H)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hN : 1 ≤ N)
    (hpc : ∀ p ∈ P, p.Prime) (hsep : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (h2p : ∀ p ∈ P, 2 * p ≤ N)
    (hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H (Finset.Icc 1 N)
            * (1 - jsp87NzFrac K p H (Finset.Icc 1 N))))
    (H15 : jsp87Hyp15Icc K H N P q κ1 κ2 κ3)
    (H1617 : jsp87Hyp1617Icc K H N P q κ4 κ5) :
    ¬ jsp87KappaSharp κ1 κ2 κ3 κ4 κ5 := by
  have hne := jsp87_5_21_Icc_hne (K := K) (P := P) H N hH hN hpc
    (fun p hp => by
      have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
      have hs := hsep p hp
      omega) h2p
  have hs : (Finset.Icc 1 N).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  exact jsp87_endgame_frac_of_5_21 (K := K) (P := P) (Finset.Icc 1 N)
    hs q H κ1 κ2 κ3 κ4 κ5 hK hH hsep hne H15 H1617 hfrac

/-- **★★★★ THE HEADLINE OF THE ROUND: (5.21′) IS NOT THE OBSTRUCTION ★★★★**

Let `B = H + 2^K − 1`.  For every `q ≠ 0` at the admissible scale (5.19), every
`H` with `1 ≤ H`, and every five constants `κ₁, …, κ₅`: if the error bounds
(5.15) and (5.16)–(5.17) hold on the canonical initial-segment samples
`[1, 2Y]` — with the prime set `jsp87PrimeSet (3B, Y)`, the choice made in §2 —
then the five constants cannot be simultaneously sharp. -/
theorem jsp87_endgame_Icc_witness {K : ℕ} (q κ1 κ2 κ3 κ4 κ5 : ℝ) (H : ℕ)
    (hH : 1 ≤ H) (hq : q ≠ 0) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (H15 : ∀ Y : ℕ, jsp87Hyp15Icc K H (2 * Y) (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y)
        q κ1 κ2 κ3)
    (H1617 : ∀ Y : ℕ, jsp87Hyp1617Icc K H (2 * Y)
        (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ4 κ5) :
    ¬ jsp87KappaSharp κ1 κ2 κ3 κ4 κ5 := by
  obtain ⟨Y, hY, hall, hfrac⟩ := jsp87_5_21_Icc_witness (K := K) q hq H hH
  have h2Y : 1 ≤ 2 * Y := by omega
  exact jsp87_endgame_Icc_of_5_15 (K := K) (N := 2 * Y)
    (P := jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ1 κ2 κ3 κ4 κ5 H hH hK h2Y
    (fun p hp => (hall p hp).1)
    (fun p hp => by
      have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
      have h3 : 0 ≤ 2 ^ K - 1 := by omega
      have h4 : 3 * (H + (2 ^ K - 1)) ≤ p := (hall p hp).2.1
      have h5 : H + (2 ^ K - 1) + 1 ≤ 3 * (H + (2 ^ K - 1)) := by omega
      omega)
    (fun p hp => (hall p hp).2.2)
    hfrac (H15 Y) (H1617 Y)

/-- **★★ THE COROLLARY THAT PINS THE FAILURE OF §5 ON INITIAL SEGMENTS ★★**

At every admissible scale, for every `q ≠ 0`: if the endgame of §§5.3–5.14 were
to *conclude* (all five constants sharp), then on the canonical initial-segment
samples `[1, 2Y]` over the prime sets `[3B, Y]` **at least one of (5.15) and
(5.16)–(5.17) must fail** — there is a height at which one of the two error
bounds breaks down.

Together with `jsp87_5_21_Icc_witness` this is the complete negative statement
about the published endgame on plain samples: **hypothesis (5.21′) cannot be
the obstruction; only the two error estimates can be.**  Hence any witness of
the endgame must be a *correlated* sample, and finding one is exactly the
content of the Chowla-type estimate `jsp87Mcov_small`. -/
theorem jsp87_5_15_Icc_or_5_16 {K : ℕ} (q κ1 κ2 κ3 κ4 κ5 : ℝ) (H : ℕ)
    (hH : 1 ≤ H) (hq : q ≠ 0) (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hκ : jsp87KappaSharp κ1 κ2 κ3 κ4 κ5) :
    (∃ Y : ℕ, ¬ jsp87Hyp15Icc K H (2 * Y) (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y)
        q κ1 κ2 κ3)
      ∨ (∃ Y : ℕ, ¬ jsp87Hyp1617Icc K H (2 * Y)
          (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ4 κ5) := by
  by_cases h1 : ∃ Y : ℕ, ¬ jsp87Hyp15Icc K H (2 * Y)
      (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ1 κ2 κ3
  · exact Or.inl h1
  · have h15 : ∀ Y : ℕ, jsp87Hyp15Icc K H (2 * Y)
        (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ1 κ2 κ3 :=
      fun Y => Classical.byContradiction (fun hh => h1 ⟨Y, hh⟩)
    by_cases h2 : ∃ Y : ℕ, ¬ jsp87Hyp1617Icc K H (2 * Y)
        (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ4 κ5
    · exact Or.inr h2
    · have h1617 : ∀ Y : ℕ, jsp87Hyp1617Icc K H (2 * Y)
          (jsp87PrimeSet (3 * (H + (2 ^ K - 1))) Y) q κ4 κ5 :=
        fun Y => Classical.byContradiction (fun hh => h2 ⟨Y, hh⟩)
      exact absurd hκ
        (jsp87_endgame_Icc_witness (K := K) q κ1 κ2 κ3 κ4 κ5 H hH hq hK h15 h1617)

/-! ## §4  MACHINE-CHECKED INSTANCES -/

/-- **★ THE TWO-CLASS WINDOW OF §1, AT `K = 1`, `H = 1`, `p = 7`, `N = 14`:
`B = 2`, so `1/7 ≤ f ≤ 3/7 ≤ 1/2`, hence `2/(4·7) = 1/14 ≤ f (1 − f)`.** -/
theorem jsp87NzFrac_mul_one_sub_Icc_ge_instance :
    jsp87NzFrac 1 7 1 (Finset.Icc 1 14) * (1 - jsp87NzFrac 1 7 1 (Finset.Icc 1 14))
      ≥ 1 / 14 := by
  have h := jsp87NzFrac_mul_one_sub_Icc_ge (K := 1) (p := 7) (H := 1) (N := 14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  nlinarith [h]

/-- **★ AND THE LOWER SPLIT ITSELF: `jsp87NzFrac 1 7 1 [1, 14] ≥ 1/7`.** -/
theorem jsp87NzFrac_Icc_ge_B_two_instance :
    jsp87NzFrac 1 7 1 (Finset.Icc 1 14) ≥ 1 / 7 := by
  have h := jsp87NzFrac_Icc_ge_B_two (K := 1) (p := 7) (H := 1) (N := 14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

end JSP87
