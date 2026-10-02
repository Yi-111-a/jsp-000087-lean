/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.CubeSplit

/-!
# JSP-000087, round 92 — THE EXACT CLOSED FORM OF THE ERROR TERM `δ_p`

## What this round is

Round 88 introduced the error term of §5.1 of Tao–Teräväinen

`δ_p(m) = ∑' h, [p ∣ m+h+1] · 2^(-(h+1))`

and bounded it only (`0 ≤ δ_p(m) ≤ 1`, and `δ_p(m) > 0` for prime `p`,
`m ≥ 1`).  Round 91 listed its exact evaluation as deferred item 2, on the
assumption that it "needs a tsum-over-an-AP helper".  **That assumption is
false, and this round proves the closed form exactly**, for every `p ≥ 1` and
every `m`:

> **`jsp87Delta_eq_mer`**  `(2 ^ p - 1) · δ_p(m) = 2 ^ (p - 1 - c)`,
> where `c = jsp87DeltaRes m p` is the least `c < p` with `p ∣ m + c + 1`.

So the error term of Tao–Teräväinen is **a power of two divided by the
Mersenne number `2^p − 1`** — a fact that joins the window side of this
development to the Lambert side of rounds 37–40 and 84, where `2^p − 1` is
*the* denominator.

No tsum reindexing is needed.  `Summable.sum_add_tsum_nat_add` splits the
series into its finite prefix of length `p` and its tail, the tail is literally
`2^(-p)` times the summand, and the prefix is a **single** term
(`Finset.sum_eq_single`, plus uniqueness of the residue `jsp87DeltaRes_unique`).
That yields the functional equation

`jsp87Delta_split`  `δ_p(m) = 2^(-(c+1)) + 2^(-p) · δ_p(m)`,

from which the closed form follows by clearing `1 - 2^(-p)`.

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87DeltaRes` (def), `jsp87DeltaRes_lt`, `jsp87DeltaRes_eq` | the residue `c = (p - 1 - m % p) % p`, the least `c < p` with `p ∣ m+c+1`, in closed form |
| `jsp87DeltaRes_spec` | `p ∣ m + c + 1` |
| `jsp87DeltaRes_unique` | for `h < p`: `p ∣ m+h+1 ↔ h = c` — this is what makes the finite prefix a single term |
| `jsp87Delta_term_shift` | the summand is `p`-geometric: `g (h+p) = 2^(-p) · g h` |
| `jsp87Delta_sum_range` | the finite prefix of length `p` is exactly `2^(-(c+1))` |
| **`jsp87Delta_split`** | **the functional equation** `δ_p(m) = 2^(-(c+1)) + 2^(-p) · δ_p(m)` |
| **`jsp87Delta_eq_mer`** | **THE EXACT CLOSED FORM** `(2^p−1) · δ_p(m) = 2^(p−1−c)` |
| **`jsp87Delta_eq_mer'`** | `δ_p(m) = 2^(p−1−c) / (2^p − 1)` |
| `jsp87_pow_le` (with the private `jsp87_one_le_pow2`, `jsp87_two_le_pow2`) | `2^(p−1−c) ≤ 2^(p−1)` for `c < p` |
| `jsp87Delta_pos'` | `δ_p(m) > 0` for every `p ≥ 1` (round 88 had it only for prime `p`, `m ≥ 1`) |
| **`jsp87Delta_min`** | `δ_p(m) ≥ 1/(2^p − 1)` — the **Lambert term** `1/(2^p−1)` is the exact minimum |
| **`jsp87Delta_le_max`** | `δ_p(m) ≤ 2^(p−1)/(2^p − 1)` — the exact maximum |
| `jsp87Delta_lt_one` | `δ_p(m) < 1` for `p ≥ 2` (sharp: `δ_1(m) = 1` exactly) |
| `jsp87Delta_le_two_thirds` | `δ_p(m) ≤ 2/3` for `p ≥ 2`, attained at `p = 2`.  **This replaces the dyadic `≤ 1/2`, which is false** (see below) |
| **`jsp87Delta_period`**, `jsp87Delta_congr`, `jsp87Delta_mod` | `δ_p` is **exactly** `p`-periodic in `m`; `δ_p(m) = δ_p (m % p)` |
| **`jsp87Delta_geo_form`** | **the policy target, exactly:** for `1 ≤ m < p`, `δ_p(m) = 2^(-(p−m)) / (1 − 2^(-p))` |

Together `jsp87Delta_min` and `jsp87Delta_le_max` pin `δ_p(m)` down to an
explicit set of `p` dyadic rationals with denominator `2^p − 1`.

## Negative knowledge recorded this round

* **`δ_p(m) ≤ 1/2` is FALSE.**  For `p = 2`, `m = 1` one has `δ_2(1) = 2/3`.  A
  draft of this round asserted `jsp87Delta_le_half`; the statement was **deleted,
  not weakened**, and replaced by `jsp87Delta_le_two_thirds`.  Do not retry the
  dyadic half bound.
* **`δ_p(m) < 1` needs `p ≥ 2`.**  `δ_1(m) = 1` exactly (`c = 0`, `2^1 − 1 = 1`).
* **`1 − 2^(-p)` is not `2^p − 1`.**  The true identity is
  `1 − 2^(-p) = (2^p − 1) · 2^(-p)`, and nonvanishing of `1 − 2^(-p)` comes from
  `mul_ne_zero (ne_of_gt (two_pow_sub_one_pos _)) (by positivity)`.
* The announced *tsum-over-an-AP* obstacle **does not exist**; see above.

## Not proved here (deliberate)

* The **equality** characterisations of the sharp bounds,
  `δ_p(m) = 1/(2^p−1) ↔ p ∣ m` and `δ_p(m) = 2^(p−1)/(2^p−1) ↔ p ∣ m+1`.
  They need `2^k = 1 ↔ k = 0` at base 2 (Mathlib has no `pow_injective` /
  `pow_eq_one_iff_of_gt_one` under these imports) together with the
  residue/divisibility equivalence `m % p = p − 1 ↔ p ∣ m + 1`.
* The **period mass** `∑_{j<p} δ_p(m+j) = 1`, i.e. the mean of the error over a
  period is exactly `1/p` — the exact content of the paper's `κ₁ = o(1)`
  average estimate.  It needs a hand-written `Finset.sum_bij` for the residue
  map on `range p`.
* `jsp_000087_main` is **not declared**; the missing input is the analytic one,
  Gowers-norm smallness of the window function (hsmall) from the Pilatte-type
  two-point correlation estimate, cf. `jsp87Series_irrational_of_FCube_one_small`
  in `JSPProblem/CubeSplit.lean`.
-/

namespace JSP87

open Filter Finset Function Topology

open scoped Topology

set_option maxHeartbeats 20000000

/-! ## §1  The residue that indexes the error term -/

/-- **THE ONLY SMALL MULTIPLE.**  If `0 < x < 2p` and `p ∣ x` with `0 < p`, then
`x = p`: `p` is the least positive multiple of itself, and `2p` is out of range.
This one-line fact is what collapses the finite part of the error sum. -/
theorem jsp87_dvd_lt_two_mul {p x : ℕ} (_hp : 0 < p) (hx0 : 0 < x) (hx : x < 2 * p)
    (hd : p ∣ x) : x = p := by
  obtain ⟨k, hk⟩ := hd
  rw [hk] at hx hx0
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hz | hpos
    · rw [hz, Nat.mul_zero] at hx0; exact absurd hx0 (by simp)
    · exact hpos
  have hk2 : k < 2 := by
    rw [Nat.mul_comm 2 p] at hx
    exact Nat.lt_of_mul_lt_mul_left hx
  have hk3 : k = 1 := by omega
  rw [hk3, Nat.mul_one] at hk
  exact hk

/-- **The Euclidean split of `m + h`.** -/
theorem jsp87_add_div_mod (m p h : ℕ) :
    m + h = p * (m / p) + (m % p + h) := by
  have hdv := Nat.div_add_mod m p
  calc m + h = (m % p + p * (m / p)) + h := by omega
    _ = p * (m / p) + (m % p + h) := by omega

/-- **The residue of the error term**: the least `c < p` with `p ∣ m + c + 1`.
Equivalently `c = p - 1 - (m mod p)`. -/
def jsp87DeltaRes (m p : ℕ) : ℕ := (p - 1 - m % p) % p

theorem jsp87DeltaRes_lt (m p : ℕ) (hp : 0 < p) : jsp87DeltaRes m p < p := by
  unfold jsp87DeltaRes
  exact Nat.mod_lt _ (by omega)

theorem jsp87DeltaRes_eq (m p : ℕ) (hp : 0 < p) :
    jsp87DeltaRes m p = p - 1 - m % p := by
  unfold jsp87DeltaRes
  rw [Nat.mod_eq_of_lt (by omega)]

/-- **THE RESIDUE DIVIDES**: `p ∣ m + c + 1`. -/
theorem jsp87DeltaRes_spec (m p : ℕ) (hp : 0 < p) : p ∣ m + jsp87DeltaRes m p + 1 := by
  have hres : jsp87DeltaRes m p = p - 1 - m % p := jsp87DeltaRes_eq m p hp
  have hr : m % p < p := Nat.mod_lt _ (by omega)
  have hsr : m % p + jsp87DeltaRes m p + 1 = p := by rw [hres]; omega
  refine ⟨m / p + 1, ?_⟩
  rw [show m + jsp87DeltaRes m p + 1 = m + (jsp87DeltaRes m p + 1) by omega,
    jsp87_add_div_mod m p (jsp87DeltaRes m p + 1)]
  nlinarith

/-- **UNIQUENESS OF THE RESIDUE.**  For `h < p`, `p ∣ m + h + 1` holds exactly at
`h = c`.  This is what makes the finite part of the error sum a single term. -/
theorem jsp87DeltaRes_unique (m p h : ℕ) (hp : 0 < p) (hh : h < p) :
    (p ∣ m + h + 1) ↔ h = jsp87DeltaRes m p := by
  have hr : m % p < p := Nat.mod_lt _ (by omega)
  have hres : jsp87DeltaRes m p = p - 1 - m % p := jsp87DeltaRes_eq m p hp
  have hkey : p ∣ m % p + h + 1 ↔ m % p + h + 1 = p := by
    constructor
    · rintro ⟨k, hk⟩
      exact jsp87_dvd_lt_two_mul hp (by omega) (by omega) ⟨k, hk⟩
    · intro hk
      exact ⟨1, by omega⟩
  constructor
  · intro hd
    rw [show m + h + 1 = m + (h + 1) by omega, jsp87_add_div_mod m p (h + 1)] at hd
    have hd' : p ∣ m % p + (h + 1) := by
      obtain ⟨k, hk⟩ := hd
      refine ⟨k - m / p, ?_⟩
      have hle : m / p ≤ k := by
        have hle' : p * (m / p) ≤ p * k := by omega
        exact Nat.le_of_mul_le_mul_left hle' (Nat.zero_lt_of_lt hp)
      have hsub : p * k - p * (m / p) = p * (k - m / p) :=
        (Nat.mul_sub_left_distrib p k (m / p)).symm
      have hkey2 : m % p + (h + 1) = p * k - p * (m / p) := by
        have := Nat.eq_sub_of_add_eq hk
        omega
      rw [hkey2, hsub]
    have hk' : m % p + h + 1 = p := hkey.mp hd'
    omega
  · intro hk
    rw [hk]
    exact jsp87DeltaRes_spec m p hp

/-- **ADDING A MULTIPLE OF `p` DOES NOT CHANGE DIVISIBILITY.**  This elementary
lemma is what lets us shift the index of the error summand by `p`. -/
theorem jsp87_dvd_add_mul_self (p x n : ℕ) (hp : 0 < p) :
    (p ∣ x) ↔ (p ∣ x + n * p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, Nat.succ_mul, ← Nat.add_assoc]
      constructor
      · rintro ⟨k, hk⟩
        have heq : x + n * p = p * k := hk
        have hne : x + n * p + p = p * (k + 1) := by
          rw [heq]; ring_nf
        exact ⟨k + 1, hne⟩
      · rintro ⟨k, hk⟩
        rcases Nat.eq_zero_or_pos k with hz | hpos
        · rw [hz, Nat.mul_zero] at hk
          exfalso; omega
        · have hle : p * 1 ≤ p * k := Nat.mul_le_mul_left p hpos
          have hsub := Nat.eq_sub_of_add_eq hk
          refine ⟨k - 1, ?_⟩
          rw [hsub, Nat.mul_sub_left_distrib, Nat.mul_one]

/-! ## §2  The exact closed form of the error term -/

/-- **THE `p`-GEOMETRIC SHIFT OF THE ERROR SUMMAND.**  The summand of `δ_p` at
index `h + p` is `2^{-p}` times the summand at index `h`: the indicator
`[p ∣ m+h+1]` is `p`-periodic, and the weight picks up a factor `2^{-p}`. -/
theorem jsp87Delta_term_shift (m p h : ℕ) (hp : 0 < p) :
    (if p ∣ m + (h + p) + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + p + 1))⁻¹
      = ((2 : ℝ) ^ p)⁻¹
        * ((if p ∣ m + h + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (h + 1))⁻¹) := by
  have hdv : (p ∣ m + (h + p) + 1) ↔ (p ∣ m + h + 1) := by
    have e1 : m + (h + p) + 1 = (m + h + 1) + p := by omega
    have e2 : m + h + 1 + p = (m + h + 1) + 1 * p := by omega
    rw [e1, e2, jsp87_dvd_add_mul_self (p := p) (x := m + h + 1) 1 hp]
  have hpw : ((2 : ℝ) ^ (h + p + 1))⁻¹ = ((2 : ℝ) ^ p)⁻¹ * ((2 : ℝ) ^ (h + 1))⁻¹ := by
    have e2 : (h + p + 1 : ℕ) = p + (h + 1) := by omega
    rw [e2, pow_add]
    field_simp
  rw [hpw]
  by_cases hc : p ∣ m + h + 1 <;> simp [hc, hdv]

/-- **THE FINITE PART IS A SINGLE TERM.**  Among `h < p`, exactly one index
satisfies `p ∣ m + h + 1`, namely the residue `c`. -/
theorem jsp87Delta_sum_range (m p : ℕ) (hp : 0 < p) :
    (∑ h ∈ Finset.range p, (if p ∣ m + h + 1 then (1 : ℝ) else 0)
        * ((2 : ℝ) ^ (h + 1))⁻¹) = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹ := by
  have hc : jsp87DeltaRes m p ∈ Finset.range p := Finset.mem_range.mpr (jsp87DeltaRes_lt m p hp)
  have hne : ∀ b ∈ Finset.range p, b ≠ jsp87DeltaRes m p →
      ¬ (p ∣ m + b + 1) := by
    intro b hb hbn hcon
    exact hbn ((jsp87DeltaRes_unique m p b hp (Finset.mem_range.mp hb)).mp hcon)
  rw [Finset.sum_eq_single (s := Finset.range p) (jsp87DeltaRes m p)
      (fun b hb hbn => by
        have hfalse := hne b hb hbn
        simp only [hfalse, if_false, zero_mul])
      (fun ha => absurd hc ha)]
  have hspec := jsp87DeltaRes_spec m p hp
  rw [if_pos hspec, one_mul]

/-! ## §3  `δ_p` is `p`-periodic in `m` -/

/-- **THE ERROR TERM IS `p`-PERIODIC IN `m`.**  `δ_p(m)` depends only on `m mod p`,
so `δ_p(m + p) = δ_p(m)`.  This is a statement about the *paper's* error, and it
is new: it says the error term of §5.1 is a function of `m mod p` only. -/
theorem jsp87Delta_period (m p : ℕ) (hp : 0 < p) : jsp87Delta (m + p) p = jsp87Delta m p := by
  unfold jsp87Delta
  refine tsum_congr fun h => ?_
  have hiff := jsp87_dvd_add_mul_self (p := p) (x := m + h + 1) 1 hp
  have heq : (m + p + h + 1 : ℕ) = (m + h + 1) + 1 * p := by omega
  rw [heq]
  by_cases hc : p ∣ m + h + 1
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg]
    exact fun hcon => hc (hiff.mpr hcon)

/-- **`δ_p` depends only on `m mod p`**: for `m ≡ m' (mod p)`, `δ_p(m) = δ_p(m')`. -/
theorem jsp87Delta_congr {m m' p : ℕ} (_hp : 0 < p) (h : m ≡ m' [MOD p]) :
    jsp87Delta m p = jsp87Delta m' p := by
  unfold jsp87Delta
  refine tsum_congr fun k => ?_
  have hiff : (p ∣ m + k + 1) ↔ (p ∣ m' + k + 1) := by
    have hmod : (m + k + 1) % p = (m' + k + 1) % p := by
      have hm := h.add_right (k + 1)
      rwa [Nat.ModEq] at hm
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hmod]
  by_cases hc : p ∣ m + k + 1
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg]
    exact fun hcon => hc (hiff.mpr hcon)

/-- **`δ_p(m)` equals `δ_p(m mod p)`.** -/
theorem jsp87Delta_mod (m p : ℕ) (hp : 0 < p) : jsp87Delta m p = jsp87Delta (m % p) p := by
  refine jsp87Delta_congr hp ?_
  have hr : m % p < p := Nat.mod_lt _ (by omega)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hr]

/-! ## §4  THE EXACT CLOSED FORM OF THE ERROR TERM -/

/-- **THE FUNCTIONAL EQUATION OF `δ_p`.**  Splitting the series into its first `p`
terms and its tail, and using the `p`-geometric shift of the summand, gives

`δ_p(m) = 2^{-(c+1)} + 2^{-p} · δ_p(m)`,

where `c = jsp87DeltaRes m p`.  This is the whole content of the closed form. -/
theorem jsp87Delta_split (m p : ℕ) (hp : 0 < p) :
    jsp87Delta m p = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹
      + ((2 : ℝ) ^ p)⁻¹ * jsp87Delta m p := by
  have hs := summable_jsp87Delta m p
  have hsplit := hs.sum_add_tsum_nat_add p
  have htail : (∑' k : ℕ, (if p ∣ m + (k + p) + 1 then (1 : ℝ) else 0)
        * ((2 : ℝ) ^ (k + p + 1))⁻¹)
      = ((2 : ℝ) ^ p)⁻¹ * jsp87Delta m p := by
    unfold jsp87Delta
    rw [← Summable.tsum_mul_left ((2 : ℝ) ^ p)⁻¹ hs]
    exact tsum_congr fun k => jsp87Delta_term_shift m p k hp
  rw [jsp87Delta_sum_range m p hp] at hsplit
  rw [htail] at hsplit
  have hL : (∑' k : ℕ, (if p ∣ m + k + 1 then (1 : ℝ) else 0) * ((2 : ℝ) ^ (k + 1))⁻¹)
      = jsp87Delta m p := rfl
  rw [hL] at hsplit
  linarith

/-- **THE MERSENNE SPLIT.**  For `E < p`,

`(2 ^ (E + 1))⁻¹ · 2 ^ p = 2 ^ (p − 1 − E)`,

i.e. `2^(p−1−E) · 2^(E+1) = 2^p`.  This is the arithmetic step that converts the
functional equation `δ = 2^-(c+1) + 2^-p δ` into the closed form. -/
theorem jsp87_pow_mer_split {E p : ℕ} (hE : E < p) :
    ((2 : ℝ) ^ (E + 1))⁻¹ * (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1 - E) := by
  have key : (p - 1 - E) + (E + 1) = p := by omega
  have hkey : (2 : ℝ) ^ (p - 1 - E) * (2 : ℝ) ^ (E + 1) = (2 : ℝ) ^ p := by
    rw [← pow_add, key]
  calc ((2 : ℝ) ^ (E + 1))⁻¹ * (2 : ℝ) ^ p
      = ((2 : ℝ) ^ (E + 1))⁻¹ * ((2 : ℝ) ^ (p - 1 - E) * (2 : ℝ) ^ (E + 1)) := by
        rw [← hkey]
    _ = (2 : ℝ) ^ (p - 1 - E) * (((2 : ℝ) ^ (E + 1))⁻¹ * (2 : ℝ) ^ (E + 1)) := by ring
    _ = (2 : ℝ) ^ (p - 1 - E) := by
        have hz := inv_mul_cancel₀ (a := (2 : ℝ) ^ (E + 1)) (by positivity)
        rw [hz, mul_one]

/-- **`1 − 2^{-p}` is the normalised Mersenne number.** -/
theorem jsp87_one_sub_inv_mer (p : ℕ) :
    1 - ((2 : ℝ) ^ p)⁻¹ = ((2 : ℝ) ^ p - 1) / (2 : ℝ) ^ p := by
  field_simp

/-- **`2^p > 1` for `p ≥ 1`**, so every normalisation by `2^p − 1` is legal. -/
theorem jsp87_two_pow_gt_one (p : ℕ) (hp : 2 ≤ p) : 1 < (2 : ℝ) ^ p :=
  two_pow_gt_one hp

/-- **`2^p − 1 ≠ 0` for `p ≥ 1`.** -/
theorem jsp87_mer_ne_zero (p : ℕ) (hp : 1 ≤ p) : (2 : ℝ) ^ p - 1 ≠ 0 :=
  ne_of_gt (two_pow_sub_one_pos hp)

/-- **THE EXACT CLOSED FORM.**  For every `m` and every `p ≥ 1`,

`(2 ^ p − 1) · δ_p(m) = 2 ^ (p − 1 − c)`,

where `c = jsp87DeltaRes m p ∈ [0, p)`.

Equivalently: **the paper's error term is a power of two divided by the Mersenne
number `2^p − 1`.**  This is the single most useful new fact of round 92: it
computes the error term of §5.1 of Tao–Teräväinen exactly, and it *joins the
window side of this development to the Lambert side* (rounds 37–40), where
`2^p − 1` is the prime-indexed denominator. -/
theorem jsp87Delta_eq_mer (m p : ℕ) (hp : 0 < p) :
    ((2 : ℝ) ^ p - 1) * jsp87Delta m p
      = (2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p) := by
  have hc := jsp87DeltaRes_lt m p hp
  have hs := jsp87Delta_split m p hp
  have h1 : 1 ≤ p := by omega
  have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos h1
  have hz1 : (2 : ℝ) ^ p * ((2 : ℝ) ^ p)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have h1d : ((2 : ℝ) ^ p - 1) * ((2 : ℝ) ^ p)⁻¹ = 1 - ((2 : ℝ) ^ p)⁻¹ := by
    rw [sub_mul, hz1, one_mul]
  have hne : 1 - ((2 : ℝ) ^ p)⁻¹ ≠ 0 := by
    rw [← h1d]; exact mul_ne_zero (ne_of_gt hmer) (by positivity)
  have hA : jsp87Delta m p * (1 - ((2 : ℝ) ^ p)⁻¹)
      = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹ := by linarith
  have hexp : (p - 1 - jsp87DeltaRes m p) + (jsp87DeltaRes m p + 1) = p := by omega
  have hkey : (2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p)
      * ((2 : ℝ) ^ (jsp87DeltaRes m p + 1)) = (2 : ℝ) ^ p := by rw [← pow_add, hexp]
  have hmul : ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹ * (2 : ℝ) ^ p
      = (2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p) := by
    calc ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹ * (2 : ℝ) ^ p
        = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹
            * ((2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p)
              * (2 : ℝ) ^ (jsp87DeltaRes m p + 1)) := by rw [← hkey]
      _ = (2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p)
            * (((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹
              * (2 : ℝ) ^ (jsp87DeltaRes m p + 1)) := by ring
      _ = (2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p) := by
        rw [inv_mul_cancel₀ (a := (2 : ℝ) ^ (jsp87DeltaRes m p + 1)) (by positivity),
          mul_one]
  have hdiv : jsp87Delta m p
      = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹ * (2 : ℝ) ^ p
        / ((2 : ℝ) ^ p - 1) := by
    calc jsp87Delta m p = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹
        / (1 - ((2 : ℝ) ^ p)⁻¹) := (eq_div_iff hne).mpr hA
      _ = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹
          / (((2 : ℝ) ^ p - 1) * ((2 : ℝ) ^ p)⁻¹) := by rw [← h1d]
      _ = ((2 : ℝ) ^ (jsp87DeltaRes m p + 1))⁻¹ * (2 : ℝ) ^ p
          / ((2 : ℝ) ^ p - 1) := by field_simp
  rw [hdiv]
  field_simp [ne_of_gt hmer]
  rw [← pow_add]
  congr 1
  omega

/-- `1 ≤ 2^c`, the trivial but useful `ℝ`-power fact. -/
private theorem jsp87_one_le_pow2 (c : ℕ) : (1 : ℝ) ≤ 2 ^ c := by
  induction c with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; nlinarith

/-- `2 ≤ 2^c` for `c ≥ 1`. -/
private theorem jsp87_two_le_pow2 {c : ℕ} (h1 : 1 ≤ c) : (2 : ℝ) ≤ 2 ^ c := by
  have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (m := 1) h1
  simpa using h

/-- **THE POW MONOTONICITY WE NEED.**  With `c < p`, `2^(p−1−c) ≤ 2^(p−1)`. -/
theorem jsp87_pow_le (p c : ℕ) (hp : 0 < p) (hc : c < p) :
    (2 : ℝ) ^ (p - 1 - c) ≤ (2 : ℝ) ^ (p - 1) := by
  have h1 : (2 : ℝ) ^ (p - 1 - c) * (2 : ℝ) ^ c = (2 : ℝ) ^ (p - 1) := by
    have hexp' : (p - 1 - c) + c = p - 1 := by omega
    rw [← pow_add, hexp']
  calc (2 : ℝ) ^ (p - 1 - c) = (2 : ℝ) ^ (p - 1 - c) * 1 := by ring
    _ ≤ (2 : ℝ) ^ (p - 1 - c) * (2 : ℝ) ^ c :=
      mul_le_mul_of_nonneg_left (jsp87_one_le_pow2 c) (by positivity)
    _ = (2 : ℝ) ^ (p - 1) := h1

/-- **THE CLOSED FORM, DIVIDED.**  `δ_p(m) = 2^(p−1−c) / (2^p − 1)`, where
`c = jsp87DeltaRes m p`. -/
theorem jsp87Delta_eq_mer' (m p : ℕ) (hp : 0 < p) :
    jsp87Delta m p = (2 : ℝ) ^ (p - 1 - jsp87DeltaRes m p) / ((2 : ℝ) ^ p - 1) := by
  have hne : ((2 : ℝ) ^ p - 1) ≠ 0 := (two_pow_sub_one_pos (by omega : (1 : ℕ) ≤ p)).ne'
  refine (eq_div_iff hne).mpr ?_
  rw [mul_comm, jsp87Delta_eq_mer m p hp]

/-- **THE ERROR TERM IS POSITIVE**, for every `p ≥ 1` (round 88 proved this only
for prime `p` and `m ≥ 1`). -/
theorem jsp87Delta_pos' (m p : ℕ) (hp : 0 < p) : 0 < jsp87Delta m p := by
  rw [jsp87Delta_eq_mer' m p hp]
  have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos (by omega)
  have hc := jsp87DeltaRes_lt m p hp
  positivity

/-- **THE SHARP UPPER BOUND.**  `δ_p(m) ≤ 2^(p−1) / (2^p − 1)`, with equality
exactly when `p ∣ m + 1`: the error term is a power of two over a Mersenne
number, so it is never "generic". -/
theorem jsp87Delta_le_max (m p : ℕ) (hp : 0 < p) :
    jsp87Delta m p ≤ (2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1) := by
  have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos (by omega)
  have hc := jsp87DeltaRes_lt m p hp
  rw [jsp87Delta_eq_mer' m p hp]
  exact div_le_div_of_nonneg_right (jsp87_pow_le p (jsp87DeltaRes m p) hp hc) hmer.le

/-- **THE SHARP LOWER BOUND.**  `δ_p(m) ≥ 1 / (2^p − 1)`, with equality exactly
when `p ∣ m`.  Together with `jsp87Delta_le_max` this pins `δ_p(m)` down to an
explicit finite set of `p` values. -/
theorem jsp87Delta_min (m p : ℕ) (hp : 0 < p) :
    (1 : ℝ) / ((2 : ℝ) ^ p - 1) ≤ jsp87Delta m p := by
  have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos (by omega)
  have hc := jsp87DeltaRes_lt m p hp
  rw [jsp87Delta_eq_mer' m p hp]
  exact div_le_div_of_nonneg_right (jsp87_one_le_pow2 (p - 1 - jsp87DeltaRes m p))
    hmer.le

/-- **THE ERROR TERM IS `< 1`** for every `p ≥ 2`.  (For `p = 1` the error term
is exactly `1`, so `p ≥ 2` is sharp.) -/
theorem jsp87Delta_lt_one (m p : ℕ) (hp : 2 ≤ p) : jsp87Delta m p < 1 := by
  have hp' : 0 < p := by omega
  have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos (by omega)
  have hc := jsp87DeltaRes_lt m p hp'
  rw [jsp87Delta_eq_mer' m p hp', div_lt_iff₀ hmer]
  have hmono := jsp87_pow_le p (jsp87DeltaRes m p) hp' hc
  have hone := jsp87_two_le_pow2 (by omega : (1 : ℕ) ≤ p - 1)
  have hp_s : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  nlinarith [hmono, hone, hp_s]

/-- **THE UNIFORM `2/3` BOUND.**  For `p ≥ 2` the error term never exceeds
`2/3`, and `2/3` is attained at `p = 2`.  (The dyadic bound `≤ 1/2` is *false*
for `p = 2`, where `δ_2(1) = 2/3`; this is the correct constant.) -/
theorem jsp87Delta_le_two_thirds (m p : ℕ) (hp : 2 ≤ p) :
    jsp87Delta m p ≤ (2 : ℝ) / 3 := by
  have h2 : (2 : ℝ) ^ (p - 1) / ((2 : ℝ) ^ p - 1) ≤ (2 : ℝ) / 3 := by
    have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos (by omega)
    have hone := jsp87_two_le_pow2 (by omega : (1 : ℕ) ≤ p - 1)
    have hp_s : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [div_le_iff₀ hmer, hp_s]
    nlinarith [hone]
  exact le_trans (jsp87Delta_le_max m p (by omega)) h2

/-- **THE POLICY TARGET, EXACTLY.**  For `1 ≤ m < p` the error term of §5.1 of
Tao–Teräväinen is the closed form
`δ_p(m) = 2^(−(p−m)) / (1 − 2^(−p))`, i.e. `(2 ^ (p − m))⁻¹ / (1 − (2 ^ p)⁻¹)`. -/
theorem jsp87Delta_geo_form {m p : ℕ} (h1 : 1 ≤ m) (h2 : m < p) :
    jsp87Delta m p = ((2 : ℝ) ^ (p - m))⁻¹ / (1 - ((2 : ℝ) ^ p)⁻¹) := by
  have hp : 0 < p := by omega
  have hmer : 0 < (2 : ℝ) ^ p - 1 := two_pow_sub_one_pos (by omega)
  have h1d : ((2 : ℝ) ^ p - 1) * ((2 : ℝ) ^ p)⁻¹ = 1 - ((2 : ℝ) ^ p)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ (by positivity), one_mul]
  have hne : 1 - ((2 : ℝ) ^ p)⁻¹ ≠ 0 := by
    rw [← h1d]
    exact mul_ne_zero (ne_of_gt hmer) (by positivity)
  rw [jsp87Delta_eq_mer' m p hp]
  have hres : jsp87DeltaRes m p = p - 1 - m := by
    have hmp : m % p = m := Nat.mod_eq_of_lt h2
    have hlt : p - 1 - m < p := by omega
    unfold jsp87DeltaRes
    rw [hmp, Nat.mod_eq_of_lt hlt]
  rw [hres]
  have hexp : p - 1 - (p - 1 - m) = m := by omega
  rw [hexp]
  field_simp [ne_of_gt hmer]
  rw [← pow_add]
  congr 1
  omega


end JSP87
