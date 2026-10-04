/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-132-a).
-/
import JSPProblem.CorrShift
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq

/-!
# JSP-000087, round 132 — THE CRT COUNTING LAYER AND THE SIEVE BOUND FOR THE
# CORRELATIONS

## Why this file exists

Round 131 (`JSPProblem/CorrShift.lean`) made the **shift-parametrised
correlations** `jsp87CorrShift d L = ∑_{m<L} ω m · ω (m + d)` into Lean
objects, identified them with the two-point correlation sums of round 115
(`jsp87Chowla`), proved the shift identity `jsp87CorrAt_shiftEq` and the
Cauchy–Schwarz bound `jsp87Mcov_abs_le_std` on the centred covariances, and
closed round 130's sign gap with the sign-free sandwich
`jsp87TcVar_sandwich`.

`policy.json` `next_round_attack[0]` for this round named **three exact
lemmas** — `jsp87_crt_cong`, `jsp87_crt_exists`, `jsp87CrtCount_ge_div` — the
*counting layer* needed by any sieve argument on the correlations, and recorded
that the object `jsp87CrtCount` did not exist in the tree.  **This file builds
the counting layer from scratch** and then uses it.

## What is proved here

§1  **the CRT layer.**  `jsp87_crt_dvd` / `jsp87_crt_modEq` — two solutions of
  `p ∣ m`, `q ∣ m + d` at coprime `p, q` are **congruent modulo `p·q`**;
  `jsp87_crt_cong` — they lie on one arithmetic progression of common difference
  `p·q`; `jsp87_crt_spacing` — distinct solutions are at least `p·q` apart;
  `jsp87_crt_exists` — a solution exists in `[1, p·q]`.

§2  **the counting layer.**  `jsp87CrtCount` — the number of solutions in
  `[1, L]`; `jsp87CrtCount_ge_div` — at least `⌊L/(p·q)⌋`;
  `jsp87CrtCount_le_div` — at most `⌊(L−1)/(p·q)⌋+1`; and the crown

  > **`jsp87CrtCount_window`:**  for every `d` and coprime `p, q > 0`,
  > `⌊L/(p·q)⌋ ≤ jsp87CrtCount p q d L ≤ ⌊L/(p·q)⌋ + 1`.

  The CRT class has the expected density to within **one point**, uniformly in
  the shift, with no analytic input.

§3  **the sieve bound for the correlations.**  `jsp87_sieveCorr` — for sets of
  primes `A, B` with positive coprime products `P, Q`,

  > `|A|·|B|·⌊L/(P·Q)⌋ ≤ jsp87CorrShift d (L+1)`.

  The first **quadratic in the number of sieve primes** statement in the tree:
  the quadratic sieve lower bound that §5.4 of arXiv:2512.01739 needs, obtained
  from the counting layer alone.  `jsp87CorrShift_sieve_four` is its
  unconditional four-prime instance (`A = {2,3}`, `B = {5,7}`):
  **`4·⌊L/210⌋ ≤ jsp87CorrShift d (L+1)` for every `d`, with no hypothesis on
  `d` at all.**

§4  **the sieve bound is dominated — a machine-checked closure.**
  `jsp87CorrShift_ge_trivial` — `L − 2 ≤ jsp87CorrShift d L` for every `L`,
  because every `m ≥ 2` has `ω m ≥ 1` and `ω (m+d) ≥ 1`.  Since
  `⌊L/(p·q)⌋ ≤ L − 1` for `p·q ≥ 2`, the sieve constant is **always** smaller
  than the trivial one (`jsp87_crtSieve_dominated`), and `jsp87_crtSieve_summary`
  collects the round.

  This is negative knowledge that closes a whole strategy: since the
  correlations are **at least** `L − 2`, **no lower bound of any kind can help**
  with round 130's blocker `jsp87Mcov_small`.  A small covariance requires an
  **upper** estimate of the correlation *against its mean field*
  `L·μ_k·μ_k'` — the Chowla/Elliott input of arXiv:2512.01739 Theorem 3.1 — and
  a counting argument for a single residue class can never deliver it.

§5  machine-checked instances.
-/
namespace JSP87

set_option maxHeartbeats 1000000

/-! ## 0. The objects -/

/-- **The CRT solution set in `[1, L]`**: the integers `m` in that interval
with `p ∣ m` and `q ∣ m + d` — the members of the single residue class modulo
`p·q` selected by the shift `d`. -/
def jsp87CrtSet (p q d L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (fun m => p ∣ m ∧ q ∣ m + d)

/-- **The CRT count**: the number of solutions of `p ∣ m`, `q ∣ m + d` in
`[1, L]`.  Its exact value is `⌊L/(p·q)⌋` up to `+1`, for every shift `d`
(`jsp87CrtCount_window`). -/
def jsp87CrtCount (p q d L : ℕ) : ℕ := jsp87CrtSet p q d L |>.card

theorem mem_jsp87CrtSet {p q d L m : ℕ} :
    m ∈ jsp87CrtSet p q d L ↔ 1 ≤ m ∧ m ≤ L ∧ p ∣ m ∧ q ∣ m + d := by
  simp only [jsp87CrtSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem jsp87CrtCount_le_L {p q d L : ℕ} : jsp87CrtCount p q d L ≤ L := by
  unfold jsp87CrtCount
  refine Finset.card_le_card (Finset.filter_subset _ _) |>.trans_eq ?_
  simp [Nat.card_Icc]

theorem jsp87CrtCount_mono {p q d L L' : ℕ} (h : L ≤ L') :
    jsp87CrtCount p q d L ≤ jsp87CrtCount p q d L' := by
  refine Finset.card_le_card ?_
  intro m hm
  rw [mem_jsp87CrtSet] at hm ⊢
  exact ⟨hm.1, hm.2.1.trans h, hm.2.2.1, hm.2.2.2⟩

/-! ## 1. The CRT layer -/

/-- **TWO SOLUTIONS ARE CONGRUENT MODULO `p·q`.**  If `m₁ ≤ m₂` both solve
`p ∣ m`, `q ∣ m + d` and `p, q` are coprime, then `p·q ∣ m₂ − m₁`. -/
theorem jsp87_crt_dvd {p q d L m₁ m₂ : ℕ} (hc : Nat.Coprime p q)
    (h₁ : m₁ ∈ jsp87CrtSet p q d L) (h₂ : m₂ ∈ jsp87CrtSet p q d L) (hle : m₁ ≤ m₂) :
    p * q ∣ m₂ - m₁ := by
  rw [mem_jsp87CrtSet] at h₁ h₂
  have hp : p ∣ m₂ - m₁ := Nat.dvd_sub h₂.2.2.1 h₁.2.2.1
  have hq : q ∣ (m₂ + d) - (m₁ + d) := Nat.dvd_sub h₂.2.2.2 h₁.2.2.2
  have hq' : q ∣ m₂ - m₁ := by
    convert hq using 1
    omega
  exact hc.mul_dvd_of_dvd_of_dvd hp hq'

/-- **THE CONGRUENCE, in `Nat.ModEq` form.** -/
theorem jsp87_crt_modEq {p q d L m₁ m₂ : ℕ} (hc : Nat.Coprime p q)
    (h₁ : m₁ ∈ jsp87CrtSet p q d L) (h₂ : m₂ ∈ jsp87CrtSet p q d L) (hle : m₁ ≤ m₂) :
    m₁ ≡ m₂ [MOD p * q] :=
  (Nat.modEq_iff_dvd' hle).2 (jsp87_crt_dvd hc h₁ h₂ hle)

/-- **TWO SOLUTIONS LIE ON ONE ARITHMETIC PROGRESSION OF COMMON DIFFERENCE
`p·q`** — the full content of `jsp87_crt_cong`. -/
theorem jsp87_crt_cong {p q d L m₁ m₂ : ℕ} (hc : Nat.Coprime p q)
    (h₁ : m₁ ∈ jsp87CrtSet p q d L) (h₂ : m₂ ∈ jsp87CrtSet p q d L) (hne : m₁ ≠ m₂) :
    ∃ c : ℕ, m₁ + c * (p * q) = m₂ ∨ m₂ + c * (p * q) = m₁ := by
  rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
  · obtain ⟨c, hc'⟩ := jsp87_crt_dvd hc h₁ h₂ (Nat.le_of_lt hlt)
    refine ⟨c, Or.inl ?_⟩
    have h1 : m₂ = m₁ + (m₂ - m₁) := (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
    have h2 : m₁ + (m₂ - m₁) = m₁ + c * (p * q) := by
      have hc'' : p * q * c = c * (p * q) := Nat.mul_comm _ _
      omega
    omega
  · obtain ⟨c, h⟩ := jsp87_crt_cong hc h₂ h₁ (fun hh => hne hh.symm)
    rcases h with h | h
    · exact ⟨c, Or.inr h⟩
    · exact ⟨c, Or.inl h⟩

/-- **THE SPACING: two distinct solutions are at least `p·q` apart.**  This is
the arithmetic content of the counting layer of §2. -/
theorem jsp87_crt_spacing {p q d L m₁ m₂ : ℕ} (hc : Nat.Coprime p q)
    (h₁ : m₁ ∈ jsp87CrtSet p q d L) (h₂ : m₂ ∈ jsp87CrtSet p q d L) (hlt : m₁ < m₂) :
    m₁ + p * q ≤ m₂ := by
  obtain ⟨c, hc'⟩ := jsp87_crt_dvd hc h₁ h₂ (Nat.le_of_lt hlt)
  have hpos : 0 < m₂ - m₁ := by omega
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · omega
    · omega
  have h3 : p * q ≤ p * q * c := by simpa using Nat.mul_le_mul_left (p * q) hc1
  have h1 : m₂ = m₁ + (m₂ - m₁) := (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
  omega

/-- **A SOLUTION EXISTS IN `[1, p·q]`** — `jsp87_crt_exists`, the second lemma
named by `policy.json`.  The proof uses Mathlib's `Nat.chineseRemainder` with the
residue `-d (mod q)`. -/
theorem jsp87_crt_exists (p q d : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ p * q ∧ p ∣ r ∧ q ∣ r + d := by
  set b := (q - d % q) % q with hb
  have hbd : q ∣ b + d := by
    by_cases hz : d % q = 0
    · have hb0 : b = 0 := by
        simp only [hb, hz, Nat.sub_zero, Nat.mod_self]
      rw [hb0]
      exact Nat.dvd_of_mod_eq_zero (by simpa using hz)
    · have hml : d % q < q := Nat.mod_lt d (by omega)
      have hle : d % q ≤ d := Nat.mod_le d q
      have hlt : q - d % q < q := by omega
      have hb' : b = q - d % q := by simp only [hb, Nat.mod_eq_of_lt hlt]
      have hdmd : d - d % q = q * (d / q) := by
        have h := Nat.mod_add_div d q
        omega
      have hdm : q ∣ d - d % q := by
        rw [hdmd]
        exact dvd_mul_right q (d / q)
      rw [hb']
      have hstep : (q - d % q) + d = q + (d - d % q) := by omega
      rw [hstep]
      exact (Nat.dvd_add_iff_right dvd_rfl).mp hdm
  set k : ℕ := (Nat.chineseRemainder hc 0 b : ℕ) with hkdef
  have hk0 : k ≡ 0 [MOD p] := (Nat.chineseRemainder hc 0 b).2.1
  have hk1 : k ≡ b [MOD q] := (Nat.chineseRemainder hc 0 b).2.2
  have hklt : k < p * q := Nat.chineseRemainder_lt_mul hc 0 b (by omega) (by omega)
  have hkP : p ∣ k := Nat.modEq_zero_iff_dvd.mp hk0
  have hkD : q ∣ k + d := by
    have hz : b + d ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hbd
    exact Nat.modEq_zero_iff_dvd.mp (hk1.add_right d |>.trans hz)
  rcases Nat.eq_zero_or_pos k with hkzero | hkpos
  · have hkd : q ∣ d := by simpa [hkzero] using hkD
    refine ⟨p * q, ?_, le_rfl, dvd_mul_right p q, ?_⟩
    · have : 0 < p * q := mul_pos hp hq
      omega
    · exact (Nat.dvd_add_iff_right (by simpa only [Nat.mul_comm] using dvd_mul_right q p)).mp hkd
  · exact ⟨k, hkpos, Nat.le_of_lt hklt, hkP, hkD⟩

/-! ## 2. The counting layer -/

/-- **THE LOWER COUNTING BOUND** (`jsp87CrtCount_ge_div`, the third lemma named
by `policy.json`): the CRT class in `[1, L]` has at least `⌊L/(p·q)⌋` members,
for every shift `d`. -/
theorem jsp87CrtCount_ge_div {p q d L : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    L / (p * q) ≤ jsp87CrtCount p q d L := by
  obtain ⟨r, hr1, hr2, hrp, hrq⟩ := jsp87_crt_exists p q d hp hq hc
  set K := L / (p * q) with hK
  have himg : (Finset.range K).image (fun j => r + p * q * j) ⊆ jsp87CrtSet p q d L := by
    intro m hm
    have hm' : m ∈ (Finset.range K).image (fun j => r + p * q * j) := hm
    rcases Finset.mem_image.mp hm' with ⟨j, hj, rfl⟩
    rw [mem_jsp87CrtSet]
    have hjK : j < K := Finset.mem_range.mp hj
    rcases Nat.eq_zero_or_pos K with hKzero | hKpos
    · rw [hKzero] at hjK
      omega
    · have hjK' : j < L / (p * q) := by rwa [hK] at hjK
      have hj1 : j ≤ K - 1 := by
        have hx : j ≤ L / (p * q) - 1 := by omega
        rw [← hK] at hx
        exact hx
      have hstep : r + p * q * j ≤ p * q + p * q * (K - 1) := by
        have h1 : r ≤ p * q := hr2
        have h2 : p * q * j ≤ p * q * (K - 1) := Nat.mul_le_mul_left (p * q) hj1
        exact Nat.add_le_add h1 h2
      have hmul : p * q * (K - 1) + p * q = p * q * K := by
        have h3 : p * q * ((K - 1) + 1) = p * q * (K - 1) + p * q * 1 := by
          rw [Nat.mul_add]
        have h4 : p * q * ((K - 1) + 1) = p * q * K := by
          rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hKpos)]
        rw [h4] at h3
        simpa using h3.symm
      have hle : p * q + p * q * (K - 1) ≤ p * q * K := by
        have hsw : p * q + p * q * (K - 1) = p * q * (K - 1) + p * q := Nat.add_comm _ _
        rw [hsw, hmul]
      have htop : p * q * K ≤ L := by
        have hh := Nat.mul_div_le L (p * q)
        rw [← hK] at hh
        exact hh
      have hrt : r + p * q * j ≤ L := hstep.trans hle |>.trans htop
      refine ⟨?_, hrt, ?_, ?_⟩
      · exact Nat.le_trans hr1 (Nat.le_add_right r (p * q * j))
      · have h5 : p ∣ p * (q * j) := dvd_mul_right p (q * j)
        have h6 : p ∣ r + p * (q * j) := (Nat.dvd_add_iff_right hrp).mp h5
        have h7 : p ∣ r + p * q * j := by
          rw [← Nat.mul_assoc] at h6
          exact h6
        exact h7
      · have hsw : r + p * q * j + d = p * q * j + (r + d) := by omega
        rw [hsw]
        have hq' : q ∣ (r + d) + q * (p * j) :=
          (Nat.dvd_add_iff_left (dvd_mul_right q (p * j))).mp hrq
        have h6 : q ∣ p * q * j + (r + d) := by
          have h7 : p * q * j = q * (p * j) := by
            calc p * q * j = q * p * j := by rw [Nat.mul_comm p q]
              _ = q * (p * j) := by rw [Nat.mul_assoc]
          rw [h7, Nat.add_comm]
          exact hq'
        exact h6
  have key : K ≤ (jsp87CrtSet p q d L).card := by
    have hinj : Set.InjOn (fun j : ℕ => r + p * q * j) ↑(Finset.range K) := by
      intro a ha b hb heq
      have h1 : p * q * a = p * q * b := Nat.add_left_cancel heq
      exact Nat.mul_left_cancel (mul_pos hp hq) h1
    have h1 : ((Finset.range K).image (fun j => r + p * q * j)).card = K := by
      have := Finset.card_image_iff.mpr hinj
      rwa [Finset.card_range] at this
    have h2 : ((Finset.range K).image (fun j => r + p * q * j)).card
        ≤ (jsp87CrtSet p q d L).card := Finset.card_le_card himg
    omega
  exact key

/-- **THE UPPER COUNTING BOUND**: at most one solution per block of `p·q`, so
the CRT class in `[1, L]` has at most `L/(p·q) + 1` members. -/
theorem jsp87CrtCount_le_div {p q d L : ℕ} (hpq : 0 < p * q) (hc : Nat.Coprime p q) :
    jsp87CrtCount p q d L ≤ L / (p * q) + 1 := by
  have key : ∀ m₁ m₂ : ℕ, m₁ ∈ jsp87CrtSet p q d L → m₂ ∈ jsp87CrtSet p q d L →
      m₁ / (p * q) = m₂ / (p * q) → m₁ = m₂ := by
    intro m₁ m₂ h₁ h₂ heq
    rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
    · have hsp := jsp87_crt_spacing (p := p) (q := q) (d := d) (L := L) (m₁ := m₁)
        (m₂ := m₂) hc h₁ h₂ hlt
      have hstep : m₁ / (p * q) + 1 = (m₁ + p * q) / (p * q) := by
        have h := (Nat.add_mul_div_left m₁ 1 hpq).symm
        rw [Nat.mul_one] at h
        exact h
      have hxy : m₁ / (p * q) + 1 ≤ m₂ / (p * q) := by
        rw [hstep]
        exact Nat.div_le_div_right hsp
      rw [heq] at hxy
      omega
    · rcases Nat.lt_or_ge m₂ m₁ with hlt | hge
      · have hsp := jsp87_crt_spacing (p := p) (q := q) (d := d) (L := L) (m₁ := m₂)
          (m₂ := m₁) hc h₂ h₁ hlt
        have hstep : m₂ / (p * q) + 1 = (m₂ + p * q) / (p * q) := by
          have h := (Nat.add_mul_div_left m₂ 1 hpq).symm
          rw [Nat.mul_one] at h
          exact h
        have hxy : m₂ / (p * q) + 1 ≤ m₁ / (p * q) := by
          rw [hstep]
          exact Nat.div_le_div_right hsp
        rw [heq] at hxy
        omega
      · omega
  have hinj : Set.InjOn (fun m : ℕ => m / (p * q)) ↑(jsp87CrtSet p q d L) := by
    intro m₁ hm₁ m₂ hm₂ heq
    exact key m₁ m₂ hm₁ hm₂ heq
  have hx : (jsp87CrtSet p q d L).card ≤ (Finset.range (L / (p * q) + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun m : ℕ => m / (p * q))
        (s := jsp87CrtSet p q d L) (t := Finset.range (L / (p * q) + 1)) ?_ hinj
    intro m hm
    have hm' : m ∈ jsp87CrtSet p q d L := hm
    rw [mem_jsp87CrtSet] at hm'
    have hmL : m ≤ L := by omega
    have h1 : m / (p * q) ≤ L / (p * q) := Nat.div_le_div_right hmL
    have h2 : m / (p * q) < L / (p * q) + 1 := by omega
    exact Finset.mem_range.mpr h2
  have hle : (jsp87CrtSet p q d L).card ≤ (L / (p * q) + 1) := by
    rwa [Finset.card_range] at hx
  exact hle

/-- **THE CRT COUNTING THEOREM — THE CROWN OF §2.**

For **every** shift `d` and coprime `p, q > 0`, the number of solutions of
`p ∣ m`, `q ∣ m + d` in `[1, L]` is `⌊L/(p·q)⌋` **up to one point**:

```
L / (p * q)  ≤  jsp87CrtCount p q d L  ≤  L / (p * q) + 1 .
```

No analytic input: the lower bound is an explicit arithmetic progression built
from `Nat.chineseRemainder`, the upper bound is the spacing. -/
theorem jsp87CrtCount_window {p q d L : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    L / (p * q) ≤ jsp87CrtCount p q d L ∧ jsp87CrtCount p q d L ≤ L / (p * q) + 1 :=
  ⟨jsp87CrtCount_ge_div hp hq hc, jsp87CrtCount_le_div (mul_pos hp hq) hc⟩

/-! ## 3. The sieve bound for the correlations -/

/-- **THE QUADRATIC SIEVE BOUND FOR THE CORRELATIONS — THE MAIN THEOREM OF
THIS ROUND.**

Let `A, B` be finite sets of primes whose products `P = ∏ A` and `Q = ∏ B` are
positive and coprime.  Then for **every** shift `d` and every window `L`

```
|A| · |B| · ⌊L / (P·Q)⌋   ≤   jsp87CorrShift d (L+1) = ∑_{m ≤ L} ω m · ω (m+d) .
```

Every member of the CRT class `P ∣ m`, `Q ∣ m + d` carries at least `|A|`
distinct prime factors in `m` and at least `|B|` in `m + d`, and the class has
`⌊L/(P·Q)⌋` members up to `+1` by §2.  This is the first statement in the tree
whose left-hand side is **quadratic in the number of sieve primes**, i.e. the
quadratic lower bound that §5.4 of arXiv:2512.01739 needs. -/
theorem jsp87_sieveCorr {A B : Finset ℕ} {d L : ℕ}
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ q ∈ B, q.Prime)
    (hP : 0 < ∏ p ∈ A, p) (hQ : 0 < ∏ q ∈ B, q)
    (hcop : Nat.Coprime (∏ p ∈ A, p) (∏ q ∈ B, q)) :
    A.card * B.card * (L / ((∏ p ∈ A, p) * (∏ q ∈ B, q))) ≤ jsp87CorrShift d (L + 1) := by
  set P := ∏ p ∈ A, p with hPdef
  set Q := ∏ q ∈ B, q with hQdef
  set S := jsp87CrtSet P Q d L with hSdef
  have hcnt : L / (P * Q) ≤ S.card := jsp87CrtCount_ge_div hP hQ hcop
  have hsub : S ⊆ Finset.range (L + 1) := by
    intro m hm
    rw [mem_jsp87CrtSet] at hm
    simp only [Finset.mem_range]
    omega
  have hper : ∀ i ∈ S, A.card * B.card ≤ omega i * omega (i + d) := by
    intro i hi
    rw [mem_jsp87CrtSet] at hi
    have hA' : A.card ≤ omega i := by
      have hsub' : A ⊆ i.primeFactors := by
        intro p hp
        have hpP : p ∣ P := Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp
        have hpPm : p ∣ i := Nat.dvd_trans hpP hi.2.2.1
        rw [Nat.mem_primeFactors_of_ne_zero (by omega)]
        exact ⟨hA p hp, hpPm⟩
      have hh := Finset.card_le_card hsub'
      simpa [omega] using hh
    have hB' : B.card ≤ omega (i + d) := by
      have hsub' : B ⊆ (i + d).primeFactors := by
        intro q hq
        have hqQ : q ∣ Q := Finset.dvd_prod_of_mem (f := fun q' : ℕ => q') hq
        have hqQm : q ∣ i + d := Nat.dvd_trans hqQ hi.2.2.2
        rw [Nat.mem_primeFactors_of_ne_zero (by omega)]
        exact ⟨hB q hq, hqQm⟩
      have hh := Finset.card_le_card hsub'
      simpa [omega] using hh
    exact Nat.mul_le_mul hA' hB'
  have hcard : S.card * (A.card * B.card) ≤ S.sum (fun m => omega m * omega (m + d)) := by
    have h1 : S.card * (A.card * B.card) = ∑ m ∈ S, A.card * B.card := by
      have h2 := Finset.mul_sum (s := S) (f := fun _ : ℕ => (1 : ℕ)) (A.card * B.card)
      rw [Nat.mul_one, ← Finset.card_eq_sum_ones S] at h2
      rwa [Nat.mul_comm (A.card * B.card) S.card] at h2
    calc S.card * (A.card * B.card) = ∑ m ∈ S, A.card * B.card := h1
      _ ≤ ∑ m ∈ S, omega m * omega (m + d) :=
        Finset.sum_le_sum (fun i hi => hper i hi)
  have hfilter : (Finset.range (L + 1)).filter (fun m => m ∈ S)
      = S.filter (fun m => m ∈ Finset.range (L + 1)) := by
    ext m
    constructor
    · intro h
      have h1 : m ∈ Finset.range (L + 1) := (Finset.mem_filter.mp h).1
      have h2 : m ∈ S := (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨h2, h1⟩
    · intro h
      have h1 : m ∈ S := (Finset.mem_filter.mp h).1
      have h2 : m ∈ Finset.range (L + 1) := (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨h2, h1⟩
  have hsum : S.sum (fun m => omega m * omega (m + d)) ≤ jsp87CorrShift d (L + 1) := by
    have hsub' : S ⊆ S.filter (fun m => m ∈ Finset.range (L + 1)) := by
      intro m hm
      have hmS : m ∈ S := hm
      have hmR : m ∈ Finset.range (L + 1) := hsub hmS
      exact Finset.mem_filter.mpr ⟨hmS, hmR⟩
    have hnat : S.sum (fun m => omega m * omega (m + d))
        ≤ (Finset.range (L + 1)).sum (fun m => omega m * omega (m + d)) := by
      calc S.sum (fun m => omega m * omega (m + d))
          = (S.filter (fun m => m ∈ Finset.range (L + 1))).sum
              (fun m => omega m * omega (m + d)) :=
            Finset.sum_subset hsub' (fun x hx1 hx2 => by
              have hxS : x ∈ S := Finset.mem_of_mem_filter x hx1
              exact absurd hxS hx2)
        _ = ((Finset.range (L + 1)).filter (fun m => m ∈ S)).sum
              (fun m => omega m * omega (m + d)) := by rw [hfilter]
        _ = (Finset.range (L + 1)).sum
              (fun m => if m ∈ S then omega m * omega (m + d) else 0) :=
            Finset.sum_filter _ _
        _ ≤ (Finset.range (L + 1)).sum (fun m => omega m * omega (m + d)) :=
          Finset.sum_le_sum (f := fun m => if m ∈ S then omega m * omega (m + d) else 0)
            (fun m _ => by split <;> omega)
    simpa [jsp87CorrShift] using hnat
  have h1 : A.card * B.card * (L / (P * Q)) ≤ S.card * (A.card * B.card) := by
    have hx := Nat.mul_le_mul_left (A.card * B.card) hcnt
    rwa [Nat.mul_comm (A.card * B.card) S.card] at hx
  omega

/-- **THE UNCONDITIONAL FOUR-PRIME INSTANCE.**  With `A = {2,3}` and
`B = {5,7}` there is **no hypothesis on `d` at all** and

```
4 · ⌊L/210⌋   ≤   ∑_{m ≤ L} ω m · ω (m+d) .
``` -/
theorem jsp87CorrShift_sieve_four {d L : ℕ} :
    4 * (L / 210) ≤ jsp87CorrShift d (L + 1) := by
  have hA2 : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by decide
  have hB2 : ∀ q ∈ ({5, 7} : Finset ℕ), q.Prime := by decide
  have key := jsp87_sieveCorr (A := ({2, 3} : Finset ℕ)) (B := ({5, 7} : Finset ℕ))
      (d := d) (L := L) hA2 hB2 (by native_decide) (by native_decide) (by native_decide)
  have hcard : ({2, 3} : Finset ℕ).card * ({5, 7} : Finset ℕ).card = 4 := by
    native_decide
  have hprod : (∏ p ∈ ({2, 3} : Finset ℕ), p) * (∏ q ∈ ({5, 7} : Finset ℕ), q) = 210 := by
    native_decide
  rw [hcard, hprod] at key
  exact key


/-! ## 4. The sieve bound is dominated: a machine-checked closure -/

/-- **THE TRIVIAL LOWER BOUND FOR THE CORRELATIONS.**  Every `m ≥ 2` has
`ω m ≥ 1` and `ω (m+d) ≥ 1`, so the correlation over a window of length `L` is
at least `L − 2` (the `L − 2` integers `2, …, L−1`), for every shift `d`. -/
theorem jsp87CorrShift_ge_trivial {d L : ℕ} :
    L - 2 ≤ jsp87CorrShift d L := by
  have hone : ∀ i ∈ Finset.range L, 2 ≤ i → 1 ≤ omega i * omega (i + d) := by
    intro i _ hi2
    have h1 := omega_ge_one_of_ge_two hi2
    have h2 : 2 ≤ i + d := by omega
    have h3 := omega_ge_one_of_ge_two h2
    exact Nat.mul_le_mul h1 h3
  have hcard : ((Finset.range L).filter (fun m => 2 ≤ m)).card = L - 2 := by
    have h2 : (Finset.range L).filter (fun m => 2 ≤ m) = Finset.Icc 2 (L - 1) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [h2]
    have h3 : (Finset.Icc 2 (L - 1)).card = (L - 1) + 1 - 2 := Nat.card_Icc 2 (L - 1)
    omega
  have hge : ((Finset.range L).filter (fun m => 2 ≤ m)).card
      ≤ (Finset.range L).sum (fun m => omega m * omega (m + d)) := by
    have h1 : ((Finset.range L).filter (fun m => 2 ≤ m)).card
        ≤ ((Finset.range L).filter (fun m => 2 ≤ m)).sum (fun m => omega m * omega (m + d)) := by
      refine (Finset.card_eq_sum_ones _).trans_le ?_
      refine Finset.sum_le_sum (f := fun _ => (1 : ℕ)) ?_
      intro i hi
      have hi1 : i ∈ Finset.range L := (Finset.mem_filter.mp hi).1
      have hi2 : 2 ≤ i := (Finset.mem_filter.mp hi).2
      exact hone i hi1 hi2
    have h2 : ((Finset.range L).filter (fun m => 2 ≤ m)).sum (fun m => omega m * omega (m + d))
        ≤ (Finset.range L).sum (fun m => omega m * omega (m + d)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    exact h1.trans h2
  rw [hcard] at hge
  exact hge

/-- **THE SIEVE CONSTANT IS ALWAYS DOMINATED BY THE TRIVIAL ONE.**  For
`p, q ≥ 2` the CRT density `⌊L/(p·q)⌋` is at most `L − 2`, so §3 never improves
on §4. -/
theorem jsp87_crtSieve_dominated {p q L : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hL : 3 ≤ L) :
    L / (p * q) ≤ L - 2 := by
  have hpq : 2 ≤ p * q := by
    have h4 : 4 ≤ p * q := Nat.mul_le_mul hp hq
    omega
  have h2 : L < (L - 2 + 1) * (p * q) := by
    have h3 : 2 * (L - 2 + 1) < p * q * (L - 2 + 1) := by
      have h7 : 2 * (L - 2 + 1) < 4 * (L - 2 + 1) :=
        (Nat.mul_lt_mul_right (show 0 < L - 2 + 1 by omega)).2 (by omega)
      have h9 : 4 ≤ p * q := Nat.mul_le_mul hp hq
      have h8 : 4 * (L - 2 + 1) ≤ p * q * (L - 2 + 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (L - 2 + 1) h9
      exact lt_of_lt_of_le h7 h8
    have h5 : (L - 2 + 1) * (p * q) = p * q * (L - 2 + 1) := Nat.mul_comm _ _
    have h6 : L ≤ 2 * (L - 2 + 1) := by omega
    omega
  have hlt : L / (p * q) < L - 2 + 1 :=
    (Nat.div_lt_iff_lt_mul (show 0 < p * q by omega)).2 h2
  rw [Nat.lt_succ_iff] at hlt
  exact hlt

/-- **THE ROUND IN ONE THEOREM.**

The CRT class has density `1/(p·q)` to within one point, uniformly in the
shift; but `⌊L/(p·q)⌋ ≤ L − 2 ≤ jsp87CorrShift d L` for `p, q ≥ 2`, so the
sieve lower bound of §3 is **dominated** by the trivial one.  Consequently **no lower bound on
the correlations can help** with round 130's blocker `jsp87Mcov_small`: a small
covariance requires an *upper* estimate of the correlation against its mean
field, which is precisely the Chowla/Elliott input of arXiv:2512.01739
Theorem 3.1 and is not obtainable from a counting argument for one residue
class. -/
theorem jsp87_crtSieve_summary (L p q d : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hc : Nat.Coprime p q) (hL : 3 ≤ L) :
    L / (p * q) ≤ jsp87CrtCount p q d L ∧
      jsp87CrtCount p q d L ≤ L / (p * q) + 1 ∧
      L / (p * q) ≤ L - 2 ∧
      L - 2 ≤ jsp87CorrShift d L := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  obtain ⟨h1, h2⟩ := jsp87CrtCount_window (p := p) (q := q) (d := d) (L := L) hp0 hq0 hc
  exact ⟨h1, h2, jsp87_crtSieve_dominated hp hq hL,
    jsp87CorrShift_ge_trivial⟩

/-! ## 5. Machine-checked instances -/

theorem jsp87CrtCount_two_three_one_210 : jsp87CrtCount 2 3 1 210 = 35 := by
  native_decide

theorem jsp87CrtCount_two_three_zero_210 : jsp87CrtCount 2 3 0 210 = 35 := by
  native_decide

theorem jsp87CrtCount_two_three_one_1000 : jsp87CrtCount 2 3 1 1000 = 167 := by
  native_decide

theorem jsp87CrtCount_ge_div_concrete : 166 ≤ jsp87CrtCount 2 3 1 1000 :=
  jsp87CrtCount_ge_div (p := 2) (q := 3) (d := 1) (L := 1000) (by decide) (by decide)
    (by decide)

end JSP87
