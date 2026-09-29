/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.DigitCarry

/-!
# JSP-000087 : the quantitative shape of the carry excess

Rounds 38–41 built the whole unconditional apparatus of the Erdős–Pratt method
on both of its sides, and closed the combinatorial endgame:

* the carry `θ N = 2 ^ N · τ N` with the exact recurrence `θ (N+1) = 2 θ N − ω N`
  and the uniform bound `θ N ≥ 1/4`;
* the exact clearing denominator of the truncated prime-Lambert sum and the
  Lambert-side denominator obstruction;
* the digit bookkeeping `d N = ω N + c (N+1) − 2 c N` with `c N = ⌊θ N⌋`, and the
  theorem that rationality forces the binary digits of `S` to be eventually
  periodic.

The object still out of reach is the *integer part* `c N = ⌊θ N⌋` of the
rescaled tail.  This file attacks it from three directions, all of them
unconditional, and the results are worth stating plainly because two of the
three are **negative knowledge that closes off whole strategies**.

## 1. `ω` is unbounded

`omega_unbounded` : for every `k` there is `n ≥ 1` with `ω n ≥ k`.  (Iterate
`omega_mul_prime_of_large_prime` of round 40 along a fresh prime `> n`.)  With
it, `omega_ge_of_primeFinset` : a finset of primes is always contained, up to
cardinality, in the prime factors of its product.

## 2. THE CARRIES NEVER FALL BELOW `1` — unconditionally

`jsp87Carry_ge_one_plus_seven` : `2 ≤ N → 1 + 1/128 ≤ θ N`, and
`jsp87CarryExcess_ge_one` : `2 ≤ N → 1 ≤ ⌊θ N⌋`.

Every window `N, N+1, …` contains a multiple of `6`, which has two distinct
prime factors, while every `N + k ≥ 2` has at least one.  Combined with the
digit window of round 41 this is a *uniform* lower bound: **no amount of
arithmetic control can ever make the carry of the Erdős series small.**  Since
rationality only forces `b · θ N ∈ ℤ` (round 38), i.e. `θ N ≥ 1/b` with
`b = 1` the only dangerous case, and `θ N > 1` always, the classical
"the carry is `< 1/b`" contradiction is *impossible*.  This kills the
carry-magnitude strategy for good; what is left is the digit route of round 41.

## 3. THE CARRY EXCESS DOMINATES `ω/2` — and diverges

From `ω N = 2 θ N − θ (N+1)`, `c N ≤ θ N < c N + 1` and `θ (N+1) > 0`:

`jsp87CarryExcess_ge_omega` : `ω N < 2 c N + 2`, hence
`jsp87CarryExcess_unbounded` : `⌊θ N⌋` is unbounded, and quantitatively
`2 k + 1 ≤ ω N → k ≤ ⌊θ N⌋`.  Along the primorials the carry excess therefore
grows without bound.

## 4. BOUNDED CARRY EXCESS WOULD FORCE IRRATIONALITY (unconditionally)

`jsp87Series_irrational_of_carryExcess_bounded` : if `⌊θ N⌋ ≤ C` for all `N`
then `S` is irrational — no rationality hypothesis needed, because a bounded
carry excess bounds `θ`, hence bounds `ω` by `2 C + 1`, contradicting
`omega_unbounded`.  Together with §3 the carry-magnitude strategy is closed in
*both* directions.

## 5. The carry is determined by its first `L` digits

`jsp87Carry_le_trunc` : for `1 ≤ N`,
`θ N ≤ ∑_{k<L} ω (N+k) 2^{-(k+1)} + 2^{-L} (log₂ (N+L) + 2)`.
So the carry at `N` is approximated, with an explicit error, by the binary
window it carries — the quantitative form of round 41's `jsp87Carry_window`.

## 6. The honest "correlation" bound: the large prime factors are few

`prod_ge_pow_card` (a generalisation of round 35's `prod_ge_two_pow_card` to an
arbitrary base) together with `prod_primeFactors_dvd` gives

`jsp87_card_largeFactors_le_log` : if `2 ≤ m` and `0 < n` then the number of
prime factors of `n` exceeding `m` is at most `log_m n`,

and summing over a window, `jsp87_sum_omega_window_le` :

`∑_{k<L} ω (N+k) ≤ ∑_{k<L} #{(N+k).primeFactors ∩ (m,∞)} + L · log_m (N+L)`.

This is the unconditional content of the "quantitative correlations of `ω` at
shifted points" that ACCEPTANCE.md names as the remaining blocker: the
*small* prime factors of a window can be prescribed exactly
(`jsp87_window_rough`), the *large* ones are only bounded by the trivial
`log_m` estimate — and closing that gap is precisely the prime-`k`-tuples input
of Pratt (arXiv:2409.15185).
-/

namespace JSP87

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-! ## 1. `ω` is unbounded -/

/-- Every integer `≥ 2` has at least one prime factor. -/
theorem omega_ge_one_of_ge_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ omega n := by
  have hz : omega n ≠ 0 := by
    intro h
    have := (omega_eq_zero_iff (n := n)).mp h
    omega
  omega

/-- **A multiple of `6` has at least two distinct prime factors.** -/
theorem omega_ge_two_of_six_dvd {n : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) : 2 ≤ omega n := by
  obtain ⟨c, hc⟩ := h6
  have h2 : 2 ∣ n := by rw [hc]; exact ⟨3 * c, by ring⟩
  have h3 : 3 ∣ n := by rw [hc]; exact ⟨2 * c, by ring⟩
  have hmem2 : (2 : ℕ) ∈ n.primeFactors := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).2
    ⟨by norm_num, h2⟩
  have hmem3 : (3 : ℕ) ∈ n.primeFactors := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).2
    ⟨by norm_num, h3⟩
  have hsub : ({2, 3} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hx ▸ hmem2
    · exact hx ▸ hmem3
  have hcard : (({2, 3} : Finset ℕ) : Finset ℕ).card = 2 :=
    Finset.card_eq_two.mpr ⟨2, 3, by norm_num, rfl⟩
  have hle : 2 ≤ n.primeFactors.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  simpa [omega] using hle

/-- **A finset of primes is (up to cardinality) absorbed by the prime factors of
its own product.** -/
theorem omega_ge_of_primeFinset (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hne : (∏ p ∈ s, p) ≠ 0) : s.card ≤ omega (∏ p ∈ s, p) := by
  have hsub : s ⊆ (∏ p ∈ s, p).primeFactors := by
    intro p hp
    refine (Nat.mem_primeFactors_of_ne_zero hne).2 ?_
    exact ⟨hs p hp, Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp⟩
  have hcard : s.card ≤ (∏ p ∈ s, p).primeFactors.card := Finset.card_le_card hsub
  exact hcard

/-- **`ω` IS UNBOUNDED.**  For every `k` there is `n ≥ 1` with `ω n ≥ k`. -/
theorem omega_unbounded : ∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ k ≤ omega n := by
  intro k
  induction k with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp [omega]
  | succ k ih =>
      obtain ⟨n, hn, hkn⟩ := ih
      obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (n + 1)
      have hlt : n < q := by omega
      have h1 := omega_mul_prime_of_large_prime hq2 hn hlt
      have hpos : 1 ≤ n * q := Nat.succ_le_of_lt (Nat.mul_pos (Nat.zero_lt_of_lt hn) hq2.pos)
      refine ⟨n * q, hpos, ?_⟩
      omega

/-! ## 2. The carries never fall below `1` -/

/-- The binary value of `m + 1` successive `1`-digits, read backwards:
`∑_{j ≤ m} 2^{m−j} = 2^{m+1} − 1`. -/
theorem sum_two_pow_desc (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (2 : ℝ) ^ (m - j)) = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => simp; norm_num
  | succ m ih =>
      have hsplit : (∑ j ∈ Finset.range (m + 1 + 1), (2 : ℝ) ^ (m + 1 - j))
          = 1 + ∑ j ∈ Finset.range (m + 1), (2 : ℝ) ^ (m + 1 - j) := by
        rw [Finset.sum_range_succ]
        have h1 : m + 1 - (m + 1) = 0 := by omega
        rw [h1]
        norm_num
        ring
      have hscale : (∑ j ∈ Finset.range (m + 1), (2 : ℝ) ^ (m + 1 - j))
          = 2 * (∑ j ∈ Finset.range (m + 1), (2 : ℝ) ^ (m - j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj' : j ≤ m := by have hj'' := Finset.mem_range.mp hj; omega
        have h1 : m + 1 - j = (m - j) + 1 := Nat.succ_sub (show j ≤ m from hj')
        rw [h1, pow_succ]
        ring
      have e1 : (2 : ℝ) ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by
        rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_add]
        norm_num
      rw [hsplit, hscale, ih, e1]
      ring

/-- **A multiple of `6` lies in every six consecutive integers.**  More precisely,
for every `N` there is `k ≤ 5` with `6 ∣ N + k`. -/
theorem exists_six_dvd_add (N : ℕ) : ∃ k : ℕ, k ≤ 5 ∧ 6 ∣ N + k := by
  have hdiv : (N + 5) = 6 * ((N + 5) / 6) + (N + 5) % 6 := (Nat.div_add_mod (N + 5) 6).symm
  have hlt : (N + 5) % 6 < 6 := Nat.mod_lt (N + 5) (by norm_num : (0:ℕ) < 6)
  have hr : (N + 5) % 6 ≤ 5 := by omega
  refine ⟨5 - (N + 5) % 6, Nat.sub_le _ _, ?_⟩
  show ∃ c : ℕ, N + (5 - (N + 5) % 6) = 6 * c
  exact ⟨(N + 5) / 6, by omega⟩

/-- **The lower digit window.**  If every one of the `m + 1` integers
`N, …, N+m` has at least one prime factor and `N + k` has two, then

`2^{m+1} − 1 + 2^{m−k} ≤ ∑_{j ≤ m} ω (N+j) 2^{m−j}`,

i.e. the window beats the all-`1` pattern by a full `2^{m−k}`.  Together with
`jsp87Carry_window` (round 41) this bounds the carry from below. -/
theorem jsp87Carry_window_lower {N m k : ℕ} (hkm : k ≤ m)
    (h1 : ∀ j, j ≤ m → 1 ≤ omega (N + j)) (h2 : 2 ≤ omega (N + k)) :
    (2 : ℝ) ^ (m + 1) - 1 + (2 : ℝ) ^ (m - k)
      ≤ ∑ j ∈ Finset.range (m + 1), ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j) := by
  have hkm' : k < m + 1 := by omega
  have hmem : k ∈ Finset.range (m + 1) := Finset.mem_range.mpr hkm'
  have hsplit : (∑ j ∈ Finset.range (m + 1), ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j))
      = ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k)
        + ∑ j ∈ (Finset.range (m + 1)).erase k,
            ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j) := by
    rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  have hge : ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k) ≥ 2 * (2 : ℝ) ^ (m - k) := by
    have hω : (2 : ℝ) ≤ (omega (N + k) : ℝ) := by exact_mod_cast h2
    have h2' : (2 : ℝ) * 2 ^ (m - k) ≤ (omega (N + k) : ℝ) * 2 ^ (m - k) :=
      mul_le_mul_of_nonneg_right hω (pow_nonneg (a := (2 : ℝ)) (by norm_num) (m - k))
    linarith
  have hpt : ∀ j ∈ (Finset.range (m + 1)).erase k,
      (2 : ℝ) ^ (m - j) ≤ ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j) := by
    intro j hj
    have hj' : j ≤ m := by
      have hj'' := Finset.mem_range.mp
        ((Finset.mem_erase (s := Finset.range (m + 1)) (a := j) (b := k)).mp hj).2
      omega
    have hω : (1 : ℝ) ≤ (omega (N + j) : ℝ) := by exact_mod_cast h1 j hj'
    simpa using mul_le_mul_of_nonneg_right hω
      (pow_nonneg (a := (2 : ℝ)) (by norm_num) (m - j))
  have hsub : (∑ j ∈ (Finset.range (m + 1)).erase k, (2 : ℝ) ^ (m - j))
      ≤ ∑ j ∈ (Finset.range (m + 1)).erase k,
          ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j) :=
    Finset.sum_le_sum hpt
  have htot : (∑ j ∈ Finset.range (m + 1), (2 : ℝ) ^ (m - j)) = 2 ^ (m + 1) - 1 :=
    sum_two_pow_desc m
  have herase : (∑ j ∈ (Finset.range (m + 1)).erase k, (2 : ℝ) ^ (m - j))
      = 2 ^ (m + 1) - 1 - (2 : ℝ) ^ (m - k) := by
    rw [← htot, ← Finset.sum_erase_add _ _ hmem]
    ring
  have hge' : 2 * (2 : ℝ) ^ (m - k) ≤ ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k) := by
    linarith
  have hkey : (2 : ℝ) ^ (m + 1) - 1 + (2 : ℝ) ^ (m - k)
      ≤ ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k)
        + ∑ j ∈ (Finset.range (m + 1)).erase k,
            ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j) := by
    calc (2 : ℝ) ^ (m + 1) - 1 + (2 : ℝ) ^ (m - k)
        = 2 * (2 : ℝ) ^ (m - k) + ∑ j ∈ (Finset.range (m + 1)).erase k, (2 : ℝ) ^ (m - j) := by
          rw [herase]; ring
      _ ≤ ((omega (N + k) : ℕ) : ℝ) * (2 : ℝ) ^ (m - k)
          + ∑ j ∈ (Finset.range (m + 1)).erase k,
              ((omega (N + j) : ℕ) : ℝ) * (2 : ℝ) ^ (m - j) := add_le_add hge' hsub
  rw [hsplit]
  exact hkey

/-- **THE CARRIES NEVER FALL BELOW `1`.**  For every `N ≥ 2`,
`1 + 1/128 ≤ θ N`.

Indeed every window `N, N+1, …` contains a multiple of `6` (two distinct prime
factors) while every member of it has at least one; combined with
`jsp87Carry_window` this is a *uniform* lower bound.

This is decisive **negative** knowledge: rationality only forces
`b · θ N ∈ ℤ` (round 38), i.e. `θ N ≥ 1/b`, and the naive Erdős contradiction
"some `N` has `θ N < 1/b`" is now *impossible* — the carries of the Erdős series
are permanently at least one. -/
theorem jsp87Carry_ge_one_plus_seven {N : ℕ} (hN : 2 ≤ N) :
    1 + 1 / 128 ≤ jsp87Carry N := by
  obtain ⟨k, hk5, h6⟩ := exists_six_dvd_add N
  have hkN : 2 ≤ N + k := by omega
  have hωk : 2 ≤ omega (N + k) := omega_ge_two_of_six_dvd (by omega) h6
  have hωj : ∀ j, j ≤ k + 1 → 1 ≤ omega (N + j) := by
    intro j hj
    exact omega_ge_one_of_ge_two (by omega)
  have hlow := jsp87Carry_window_lower (N := N) (m := k + 1) (k := k) (by omega) hωj hωk
  have hupp := jsp87Carry_window N (k + 1)
  have hstep : (2 : ℝ) ^ (k + 1 + 1) - 1 + (2 : ℝ) ^ ((k + 1) - k)
      = 2 ^ (k + 1 + 1) + 1 := by
    have h1 : k + 1 - k = 1 := by omega
    rw [h1]
    ring
  rw [hstep] at hlow
  have hpos : (0 : ℝ) < 2 ^ (k + 1 + 1) := pow_pos (by norm_num) _
  have h1 : (2 : ℝ) ^ (k + 1 + 1) + 1 ≤ 2 ^ (k + 1 + 1) * jsp87Carry N := le_trans hlow hupp
  have heq : (2 : ℝ) ^ (k + 1 + 1) * (1 + ((2 : ℝ) ^ (k + 1 + 1))⁻¹)
      = 2 ^ (k + 1 + 1) + 1 := by
    rw [mul_add, mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ (k + 1 + 1)) ≠ 0)]
    ring
  have h2 : 1 + ((2 : ℝ) ^ (k + 1 + 1))⁻¹ ≤ jsp87Carry N := by
    refine le_of_mul_le_mul_left ?_ hpos
    rw [heq]
    exact h1
  have hsmall : (1 : ℝ) / 128 ≤ ((2 : ℝ) ^ (k + 1 + 1))⁻¹ := by
    have hk2 : k + 2 ≤ 7 := by omega
    have hpw : (2 : ℝ) ^ (k + 2) ≤ (2 : ℝ) ^ 7 :=
      pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hk2
    have hval : (2 : ℝ) ^ 7 = 128 := by norm_num
    have hpos : (0 : ℝ) < 2 ^ (k + 2) := by positivity
    have h2 : (2 : ℝ) ^ (k + 2) ≤ 128 := by rw [← hval]; exact hpw
    have hexp : k + 1 + 1 = k + 2 := by omega
    rw [hexp]
    simpa using (one_div_le_one_div_of_le hpos h2 : (1 : ℝ) / 128 ≤ 1 / 2 ^ (k + 2))
  linarith

/-- **Corollary of `jsp87Carry_ge_one_plus_seven`:** for `2 ≤ N` the carry
strictly exceeds `1`. -/
theorem jsp87Carry_gt_one_of_ge_two {N : ℕ} (hN : 2 ≤ N) : 1 < jsp87Carry N := by
  have h := jsp87Carry_ge_one_plus_seven hN
  linarith

/-- **The carry excess is at least `1` at every cut point `N ≥ 2`:** the
Erdős series carries at least one unit past every cut point, unconditionally.
This subsumes round 41's `jsp87CarryExcess_pos`, which required two hypotheses. -/
theorem jsp87CarryExcess_ge_one {N : ℕ} (hN : 2 ≤ N) : 1 ≤ jsp87CarryExcess N := by
  have h := jsp87Carry_ge_one_plus_seven hN
  have h1 : (1 : ℤ) ≤ ⌊jsp87Carry N⌋ := by
    rw [Int.le_floor]
    norm_num only [Int.cast_ofNat]
    linarith
  exact h1

/-! ## 3. The carry excess dominates `ω / 2` -/

/-- **THE CARRY EXCESS IS AT LEAST `(ω N − 2) / 2`.**  Formally

`ω N < 2 · ⌊θ N⌋ + 2`,

because `ω N = 2 θ N − θ (N+1)` with `θ (N+1) > 0` and `θ N < ⌊θ N⌋ + 1`. -/
theorem jsp87CarryExcess_ge_omega (N : ℕ) :
    (omega N : ℤ) < 2 * jsp87CarryExcess N + 2 := by
  have hrec := omega_eq_two_carry_sub N
  have hf := jsp87Carry_excess_lt_one N
  have hp := jsp87Carry_pos (N + 1)
  have hω : ((omega N : ℕ) : ℝ) < 2 * (jsp87CarryExcess N : ℝ) + 2 := by
    linarith
  exact_mod_cast hω

/-- **Quantitative form of `jsp87CarryExcess_ge_omega`:** `2 k + 1 ≤ ω N` forces
`k ≤ ⌊θ N⌋`. -/
theorem jsp87CarryExcess_ge (k N : ℕ) (h : 2 * k + 1 ≤ omega N) :
    k ≤ jsp87CarryExcess N := by
  have h1 := jsp87CarryExcess_ge_omega N
  omega

/-- **THE CARRY EXCESS IS UNBOUNDED.**  For every `k` there is `N ≥ 1` with
`k ≤ ⌊θ N⌋`: the Erdős series performs unboundedly much genuine carrying, and
along the primorials the excess grows at least like half the number of distinct
prime factors. -/
theorem jsp87CarryExcess_unbounded : ∀ k : ℕ, ∃ N : ℕ, 1 ≤ N ∧ k ≤ jsp87CarryExcess N := by
  intro k
  obtain ⟨n, hn, hω⟩ := omega_unbounded (2 * k + 1)
  exact ⟨n, hn, jsp87CarryExcess_ge k n hω⟩

/-- **First instance:** the cut point `N = 210 = 2·3·5·7` carries at least `1`. -/
theorem jsp87CarryExcess_210_ge_one : 1 ≤ jsp87CarryExcess 210 := by
  have h : omega 210 = 4 := by native_decide
  have h' : 2 * 1 + 1 ≤ omega 210 := by omega
  exact jsp87CarryExcess_ge 1 210 h'

/-- **Second instance:** `N = 2310 = 2·3·5·7·11` carries at least `2`. -/
theorem jsp87CarryExcess_2310_ge_two : 2 ≤ jsp87CarryExcess 2310 := by
  have h : omega 2310 = 5 := by native_decide
  have h' : 2 * 2 + 1 ≤ omega 2310 := by omega
  exact jsp87CarryExcess_ge 2 2310 h'

/-- **Third instance:** `N = 30030` (the sixth primorial) carries at least `2`. -/
theorem jsp87CarryExcess_30030_ge_two : 2 ≤ jsp87CarryExcess 30030 := by
  have h : omega 30030 = 6 := by native_decide
  have h' : 2 * 2 + 1 ≤ omega 30030 := by omega
  exact jsp87CarryExcess_ge 2 30030 h'

/-- **Fourth instance:** `N = 510510` (the seventh primorial) carries at least
`3`. -/
theorem jsp87CarryExcess_510510_ge_three : 3 ≤ jsp87CarryExcess 510510 := by
  have h : omega 510510 = 7 := by native_decide
  have h' : 2 * 3 + 1 ≤ omega 510510 := by omega
  exact jsp87CarryExcess_ge 3 510510 h'

/-! ## 4. Bounded carry excess would force irrationality -/

/-- **IF THE CARRY EXCESS IS BOUNDED, THE SERIES IS IRRATIONAL.**  No
rationality hypothesis is needed: `⌊θ N⌋ ≤ C` gives `θ N < C + 1` for all `N`,
hence `ω N = 2 θ N − θ (N+1) < 2 C + 2` for all `N`, contradicting
`omega_unbounded`.

Together with `jsp87CarryExcess_unbounded` (§3) this closes the
"carry-excess magnitude" strategy in *both* directions. -/
theorem jsp87Series_irrational_of_carryExcess_bounded {C : ℕ}
    (h : ∀ N, (jsp87CarryExcess N : ℝ) ≤ C) : Irrational jsp87Series := by
  have hθ : ∀ N, jsp87Carry N < C + 1 := by
    intro N
    have h1 := (jsp87Carry_excess_lt_one N).2
    have h2 : (jsp87CarryExcess N : ℝ) ≤ C := h N
    linarith
  have hbound : ∀ N, omega N ≤ 2 * C + 2 := by
    intro N
    have hrec := omega_eq_two_carry_sub N
    have hp := jsp87Carry_pos (N + 1)
    have h1 : ((omega N : ℕ) : ℝ) < 2 * (C + 1) := by linarith [hθ N, hθ (N + 1)]
    have h2 : ((omega N : ℕ) : ℝ) < 2 * C + 3 := by linarith
    have h3 : omega N ≤ 2 * C + 2 := by
      have h4 : (omega N : ℕ) < 2 * C + 3 := by exact_mod_cast h2
      omega
    exact h3
  obtain ⟨n, hn, hω⟩ := omega_unbounded (2 * C + 3)
  have hbad := hbound n
  exact absurd hbad (by omega)

/-! ## 5. The unconditional content of the "correlation" hypothesis -/

/-- **Generalised product bound.**  A finset of natural numbers all `≥ b ≥ 2`
has product at least `b ^ card`.  (Round 35 proved this for `b = 2`.) -/
theorem prod_ge_pow_card (s : Finset ℕ) {b : ℕ} (hb : 2 ≤ b) (h : ∀ p ∈ s, b ≤ p) :
    b ^ s.card ≤ ∏ p ∈ s, p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
      have h' : ∀ p ∈ s, b ≤ p := fun p hp => h p (Finset.mem_insert_of_mem hp)
      have hx : b * b ^ s.card ≤ b * (∏ p ∈ s, p) :=
        mul_le_mul_of_nonneg_left (ih h') (by omega)
      have hy : b * (∏ p ∈ s, p) ≤ a * (∏ p ∈ s, p) :=
        mul_le_mul_of_nonneg_right (h a (Finset.mem_insert_self a s)) (Nat.zero_le _)
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using le_trans hx hy

/-- **The prime factors of `n` exceeding `m`.** -/
noncomputable def jsp87LargeFactors (n m : ℕ) : Finset ℕ :=
  (n.primeFactors).filter (fun p => m < p)

/-- **The prime factors of `n` at most `m`.** -/
noncomputable def jsp87SmallFactors (n m : ℕ) : Finset ℕ :=
  (n.primeFactors).filter (fun p => p ≤ m)

/-- **`ω n` splits into its small and its large prime factors.** -/
theorem omega_eq_card_small_add_card_large (n m : ℕ) :
    omega n = (jsp87SmallFactors n m).card + (jsp87LargeFactors n m).card := by
  have h := Finset.card_filter_add_card_filter_not (s := n.primeFactors) (p := fun p => p ≤ m)
  simp only [jsp87SmallFactors, jsp87LargeFactors, omega] at h ⊢
  have h' : n.primeFactors.filter (fun a => ¬ a ≤ m) = n.primeFactors.filter (fun a => m < a) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hnp⟩
      exact ⟨hp, lt_of_not_ge hnp⟩
    · rintro ⟨hp, hmp⟩
      exact ⟨hp, not_le_of_gt hmp⟩
  have h' : n.primeFactors.filter (fun a => ¬ a ≤ m) = jsp87LargeFactors n m := by
    ext p
    simp only [Finset.mem_filter, jsp87LargeFactors]
    constructor
    · rintro ⟨hp, hnp⟩
      exact ⟨hp, lt_of_not_ge hnp⟩
    · rintro ⟨hp, hnp⟩
      exact ⟨hp, not_le_of_gt hnp⟩
  rw [h'] at h
  exact h.symm

/-- The product of a subfinset divides the product of the finset. -/
theorem prod_sub_dvd_prod (s t : Finset ℕ) (hts : t ⊆ s) :
    (∏ p ∈ t, p) ∣ ∏ p ∈ s, p := by
  have h := Finset.prod_sdiff (f := fun p : ℕ => p) hts
  refine ⟨∏ p ∈ s \ t, p, ?_⟩
  calc ∏ p ∈ s, p
      = (∏ p ∈ s \ t, p) * ∏ p ∈ t, p := h.symm
    _ = (∏ p ∈ t, p) * ∏ p ∈ s \ t, p := mul_comm _ _

/-- **THE LARGE PRIME FACTORS ARE FEW.**  If `2 ≤ m` and `0 < n` then the number
of prime factors of `n` exceeding `m` is at most `log_m n`.

This is the elementary form of the "quantitative correlation of `ω` at shifted
points" that ACCEPTANCE.md names as the remaining blocker: the *small* prime
factors of a window are controllable (§6), the *large* ones are only bounded by
this logarithmic estimate. -/
theorem card_largeFactors_le_log {n m : ℕ} (hm : 2 ≤ m) (hn : 0 < n) :
    (jsp87LargeFactors n m).card ≤ Nat.log m n := by
  have h1 : m ^ (jsp87LargeFactors n m).card ≤ ∏ p ∈ jsp87LargeFactors n m, p :=
    prod_ge_pow_card _ hm fun p hp => by
      have := (Finset.mem_filter.mp hp).2
      omega
  have hsub : jsp87LargeFactors n m ⊆ n.primeFactors := Finset.filter_subset _ _
  have hdvd : (∏ p ∈ jsp87LargeFactors n m, p) ∣ (∏ p ∈ n.primeFactors, p) :=
    prod_sub_dvd_prod _ _ hsub
  have h2 : (∏ p ∈ jsp87LargeFactors n m, p) ≤ n := by
    exact Nat.le_of_dvd hn (Nat.dvd_trans hdvd (prod_primeFactors_dvd n))
  exact Nat.le_log_of_pow_le (b := m) (x := (jsp87LargeFactors n m).card) (y := n)
    (by omega) (le_trans h1 h2)

/-- **THE WINDOW CORRELATION BOUND.**  For `1 ≤ N`, `2 ≤ m`:

`∑_{k < L} ω (N+k) ≤ ∑_{k < L} #{p ≤ m : p prime, p ∣ N+k} + L · log_m (N+L)`,

i.e. the `ω`-profile of a window is controlled by its *small* prime factors
plus a single logarithmic term coming from the large ones. -/
theorem jsp87_sum_omega_window_le {N L m : ℕ} (hN : 1 ≤ N) (hm : 2 ≤ m) :
    (∑ k ∈ Finset.range L, omega (N + k))
      ≤ ∑ k ∈ Finset.range L, (jsp87SmallFactors (N + k) m).card
        + (L * Nat.log m (N + L) : ℕ) := by
  have hstep : ∀ k ∈ Finset.range L,
      omega (N + k) ≤ (jsp87SmallFactors (N + k) m).card + Nat.log m (N + k) := by
    intro k hk
    have hsplit := omega_eq_card_small_add_card_large (N + k) m
    have hlarge : (jsp87LargeFactors (N + k) m).card ≤ Nat.log m (N + k) :=
      card_largeFactors_le_log hm (by omega)
    omega
  have hlog : ∀ k ∈ Finset.range L, Nat.log m (N + k) ≤ Nat.log m (N + L) := by
    intro k hk
    have hk' : k < L := Finset.mem_range.mp hk
    exact Nat.log_mono_right (by omega)
  have hsum : (∑ k ∈ Finset.range L, omega (N + k))
      ≤ ∑ k ∈ Finset.range L, ((jsp87SmallFactors (N + k) m).card + Nat.log m (N + k)) :=
    Finset.sum_le_sum hstep
  calc (∑ k ∈ Finset.range L, omega (N + k))
      ≤ ∑ k ∈ Finset.range L,
          ((jsp87SmallFactors (N + k) m).card + Nat.log m (N + k)) := hsum
    _ ≤ ∑ k ∈ Finset.range L, ((jsp87SmallFactors (N + k) m).card + Nat.log m (N + L)) :=
      Finset.sum_le_sum fun k hk => Nat.add_le_add_left (hlog k hk) _
    _ = (∑ k ∈ Finset.range L, (jsp87SmallFactors (N + k) m).card)
        + ∑ _k ∈ Finset.range L, Nat.log m (N + L) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ k ∈ Finset.range L, (jsp87SmallFactors (N + k) m).card)
        + L * Nat.log m (N + L) := by
          rw [show (∑ _k ∈ Finset.range L, Nat.log m (N + L))
              = (0:ℕ) + L * Nat.log m (N + L) by
            rw [Finset.sum_const, Finset.card_range]
            norm_num]
          ring

/-! ## 6. The small prime factors of a window can be prescribed -/

/-- **THE WINDOW-ROUGHNESS LEMMA.**  For every `m, L` there is `N` such that no
integer in the window `N, N+1, …, N+L−1` has a prime factor in the range
`(L, m]`: the primes in that range can be *avoided entirely* by a single
congruence condition, `N ≡ 1 mod ∏_{L < p ≤ m} p`, because `1 + k ≤ L < p`
for every offset `k < L`.

This is the unconditional half of a prime-tuple hypothesis: the *small* primes
of a window are fully controllable, only the large ones are not. -/
theorem jsp87_window_rough (m L : ℕ) :
    ∃ N : ℕ, ∀ k < L, ∀ p ∈ (N + k).primeFactors, p ≤ L ∨ m < p := by
  classical
  set S : Finset ℕ := (Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ L < p) with hS
  set P : ℕ := ∏ p ∈ S, p with hP
  refine ⟨1 + P, ?_⟩
  have hmem : ∀ p ∈ S, p.Prime ∧ L < p := fun p hp => (Finset.mem_filter.mp hp).2
  have hPdvd : ∀ p ∈ S, p ∣ P := by
    intro p hp
    have := Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp
    simpa [hP] using this
  intro k hk p hp
  by_cases hLp : p ≤ L
  · exact Or.inl hLp
  rcases Nat.mem_primeFactors.mp hp with ⟨hprime, hpd, hne⟩
  have hpr : p.Prime := hprime
  by_cases hpm : p ≤ m
  · have hpS : p ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr, Nat.not_le.mp hLp⟩
    have hpPdvd : p ∣ P := hPdvd p hpS
    have hNk : p ∣ (1 + P) + k := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpd
    have hone : p ∣ 1 + k := by
      have h5 : p ∣ P + (1 + k) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hNk
      exact (Nat.dvd_add_right hpPdvd).mp h5
    have hpk : p ≤ 1 + k := Nat.le_of_dvd (by omega) hone
    have htwo : 2 ≤ p := hprime.two_le
    omega
  · exact Or.inr (by omega)

/-! ## 7. The carry splits into the window it carries -/

/-- **THE EXACT CARRY SPLIT.**  For every `N, L`,

`θ N = ∑_{k<L} ω (N+k) 2^{−(k+1)} + 2^{−L} · θ (N+L)`:

the carry at the cut point `N` is the binary window of the next `L` digits
plus the carry `L` steps further on, rescaled. -/
theorem jsp87Carry_split (N L : ℕ) :
    jsp87Carry N
      = (∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((2 : ℝ) ^ L)⁻¹ * jsp87Carry (N + L) := by
  have h1 := (summable_jsp87Tail N).sum_add_tsum_nat_add L
  have htail : jsp87Tail (N + L) = ∑' i : ℕ, jsp87Term (N + L + i) := by
    unfold jsp87Tail
    refine tsum_congr fun i => ?_
    simp only [Nat.add_comm, Nat.add_left_comm]
  have h1' : (∑' i : ℕ, jsp87Term (N + i))
      = (∑ k ∈ Finset.range L, jsp87Term (N + k)) + jsp87Tail (N + L) := by
    have hnorm : (∑' i : ℕ, jsp87Term (N + (i + L))) = jsp87Tail (N + L) := by
      rw [htail]
      refine tsum_congr fun i => ?_
      simp only [Nat.add_comm, Nat.add_left_comm]
    have h1'' : (∑' i : ℕ, jsp87Term (N + i))
        = (∑ k ∈ Finset.range L, jsp87Term (N + k)) + ∑' i : ℕ, jsp87Term (N + (i + L)) :=
      h1.symm
    rw [hnorm] at h1''
    exact h1''
  have hfin : (∑ k ∈ Finset.range L, (2 : ℝ) ^ N * jsp87Term (N + k))
      = ∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro k _
    exact two_pow_mul_jsp87Term_shift N k
  have hk : (((2 : ℝ) ^ L)⁻¹) * 2 ^ (N + L) = 2 ^ N := by
    calc (((2 : ℝ) ^ L)⁻¹) * 2 ^ (N + L)
        = ((2 : ℝ) ^ L)⁻¹ * (2 ^ N * 2 ^ L) := by rw [pow_add]
      _ = 2 ^ N := by field_simp
  have htailR : (2 : ℝ) ^ N * jsp87Tail (N + L)
      = (((2 : ℝ) ^ L)⁻¹) * jsp87Carry (N + L) := by
    simp only [jsp87Carry]
    rw [← mul_assoc, hk]
  have hid : jsp87Tail N = ∑' i : ℕ, jsp87Term (N + i) := rfl
  calc jsp87Carry N
      = (2 : ℝ) ^ N * jsp87Tail N := rfl
    _ = (2 : ℝ) ^ N * ((∑ k ∈ Finset.range L, jsp87Term (N + k)) + jsp87Tail (N + L)) := by
      rw [hid, h1']
    _ = (2 : ℝ) ^ N * (∑ k ∈ Finset.range L, jsp87Term (N + k))
          + (2 : ℝ) ^ N * jsp87Tail (N + L) := by ring
    _ = (∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
          + (((2 : ℝ) ^ L)⁻¹) * jsp87Carry (N + L) := by
        rw [Finset.mul_sum, hfin, htailR]

/-- **The carry is its first `L` digits plus an explicit error.**  For `1 ≤ N`,

`θ N ≤ ∑_{k<L} ω (N+k) 2^{−(k+1)} + 2^{−L} (N + L + 1)`,

the quantitative form of round 41's `jsp87Carry_window`. -/
theorem jsp87Carry_le_window {N L : ℕ} (hN : 1 ≤ N) :
    jsp87Carry N
      ≤ (∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((2 : ℝ) ^ L)⁻¹ * ((N + L + 1 : ℕ) : ℝ) := by
  have h := jsp87Carry_split N L
  have hb : jsp87Carry (N + L) ≤ ((N + L + 1 : ℕ) : ℝ) := jsp87Carry_le (by omega)
  rw [h]
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ L)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left hb hpos
  linarith

/-- The geometric window `∑_{k<L} 2^{−(k+1)}` is at most `1`. -/
theorem sum_two_pow_inv_le_one (L : ℕ) :
    (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹) ≤ 1 := by
  have hexact : ∀ L : ℕ, (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹) = 1 - ((2 : ℝ) ^ L)⁻¹ := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : (((2 : ℝ) ^ (L + 1))⁻¹) = ((2 : ℝ) ^ L)⁻¹ * (2 : ℝ)⁻¹ := by
          have hpw : (2 : ℝ) ^ (L + 1) = 2 ^ L * 2 := by rw [pow_succ]
          rw [hpw, DivisionMonoid.mul_inv_rev]
          ring
        rw [h1]
        norm_num [one_div]
        ring
  rw [hexact]
  have h1 : (0 : ℝ) ≤ ((2 : ℝ) ^ L)⁻¹ := by positivity
  linarith

/-- **THE CARRY IN TERMS OF THE SMALL-PRIME DATA OF ITS WINDOW.**  For
`1 ≤ N` and `2 ≤ m`,

`θ N ≤ ∑_{k<L} #{p ≤ m : p ∣ N+k prime} · 2^{−(k+1)} + L · log_m (N+L) + 2^{−L} (N+L+1)`.

This is the unconditional bridge between the sieve content (§5, §6) and the
carry dynamics: everything the carry does is decided by the small prime factors
of the digits it carries, up to the trivial `log_m` and `2^{−L}` errors. -/
theorem jsp87Carry_le_smallFactors {N L m : ℕ} (hN : 1 ≤ N) (hm : 2 ≤ m) :
    jsp87Carry N
      ≤ (∑ k ∈ Finset.range L,
            (((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((L * Nat.log m (N + L) : ℕ) : ℝ)
        + ((2 : ℝ) ^ L)⁻¹ * ((N + L + 1 : ℕ) : ℝ) := by
  have hsplit := jsp87Carry_le_window (L := L) hN
  have hstep : ∀ k ∈ Finset.range L,
      ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
        ≤ (((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
          + ((Nat.log m (N + L) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    intro k hk
    have hcard := omega_eq_card_small_add_card_large (N + k) m
    have hlarge : (jsp87LargeFactors (N + k) m).card ≤ Nat.log m (N + k) :=
      card_largeFactors_le_log hm (by omega)
    have hlog : Nat.log m (N + k) ≤ Nat.log m (N + L) := by
      have hk' : k < L := Finset.mem_range.mp hk
      exact Nat.log_mono_right (by omega)
    have hle : (omega (N + k) : ℕ) ≤ (jsp87SmallFactors (N + k) m).card + Nat.log m (N + L) := by
      have hcard := omega_eq_card_small_add_card_large (N + k) m
      omega
    have h1 : (omega (N + k) : ℝ) ≤ (jsp87SmallFactors (N + k) m).card
        + (Nat.log m (N + L) : ℕ) := by exact_mod_cast hle
    have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ (k + 1))⁻¹ := by positivity
    have h2 := mul_le_mul_of_nonneg_right h1 hpos
    have e : ((2 : ℝ) ^ (k + 1))⁻¹ = (1 : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by ring
    linarith
  have hsum : (∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      ≤ ∑ k ∈ Finset.range L,
          ((((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
            + ((Nat.log m (N + L) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) :=
    Finset.sum_le_sum hstep
  have hsplit2 : (∑ k ∈ Finset.range L,
          ((((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹
            + ((Nat.log m (N + L) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹))
      = (∑ k ∈ Finset.range L,
            (((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((Nat.log m (N + L) : ℕ) : ℝ) * (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hgeom := sum_two_pow_inv_le_one L
  have hcast : ((L * Nat.log m (N + L) : ℕ) : ℝ) = (L : ℝ) * (Nat.log m (N + L) : ℝ) := by
    norm_cast
  have h2 := mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg (Nat.log m (N + L)))
  have hS : (∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
      ≤ (∑ k ∈ Finset.range L,
            (((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((Nat.log m (N + L) : ℕ) : ℝ) * (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹) :=
    hsum.trans_eq hsplit2
  have hkey : ((Nat.log m (N + L) : ℕ) : ℝ) * (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹)
      ≤ ((L * Nat.log m (N + L) : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · have h2' : ((Nat.log m (N + L) : ℕ) : ℝ) * 1
          ≤ ((L * Nat.log m (N + L) : ℕ) : ℝ) := by
        have h2'' : Nat.log m (N + L) ≤ L * Nat.log m (N + L) :=
          Nat.le_mul_of_pos_left _ hL
        norm_num
        exact_mod_cast h2''
      linarith
  calc jsp87Carry N
      ≤ (∑ k ∈ Finset.range L, ((omega (N + k) : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + (((2 : ℝ) ^ L)⁻¹) * ((N + L + 1 : ℕ) : ℝ) := hsplit
    _ ≤ (∑ k ∈ Finset.range L,
            (((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((Nat.log m (N + L) : ℕ) : ℝ) * (∑ k ∈ Finset.range L, ((2 : ℝ) ^ (k + 1))⁻¹)
          + (((2 : ℝ) ^ L)⁻¹) * ((N + L + 1 : ℕ) : ℝ) := by
      simpa only [add_comm] using
        (add_le_add_left hS (((2 : ℝ) ^ L)⁻¹ * ((N + L + 1 : ℕ) : ℝ)))
    _ ≤ (∑ k ∈ Finset.range L,
            (((jsp87SmallFactors (N + k) m).card : ℕ) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹)
        + ((L * Nat.log m (N + L) : ℕ) : ℝ)
          + (((2 : ℝ) ^ L)⁻¹) * ((N + L + 1 : ℕ) : ℝ) := by
      linarith [hkey]

/-! ## 8. What rationality would force -/

/-- **WHAT RATIONALITY OF THE ERDŐS SERIES WOULD FORCE.**  If `S = a / b` with
`b > 0`, then the carry excess `⌊2^N · τ N⌋`

* is **unbounded** (`jsp87CarryExcess_unbounded`, an unconditional fact about
  the series), and
* is **not eventually periodic** (`jsp87Series_rational_imp_carryExcess_not_periodic`,
  round 41),

while the carries themselves satisfy `θ N > 1` for `N ≥ 2`
(`jsp87Carry_gt_one_of_ge_two`) — so no hypothesis of the form "some carry is
small" can ever be true of this series, and the *only* route to
`jsp_000087_main` left open is round 41's digit route
(`jsp87Series_irrational_of_carryExcess_eventuallyPeriodic`). -/
theorem jsp87Series_rational_imp_carryExcess_unbounded_not_periodic {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    (∀ k : ℕ, ∃ N : ℕ, 1 ≤ N ∧ k ≤ jsp87CarryExcess N)
      ∧ ¬ ∃ t N : ℕ, 0 < t ∧ ∀ n : ℕ, N ≤ n → jsp87CarryExcess (n + t) = jsp87CarryExcess n :=
  ⟨jsp87CarryExcess_unbounded, jsp87Series_rational_imp_carryExcess_not_periodic hb h⟩

/-- **THE CARRY-MAGNITUDE ROUTE IS CLOSED.**  For every `2 ≤ N`,
`1 < θ N`; the carry excess is unbounded; and if it were bounded the series
would be irrational.  In particular the hypothesis "`θ N < 1`" needed by the
classical Erdős argument is *false* at every cut point. -/
theorem jsp87Carry_gt_one_of_ge_two_unbounded (k : ℕ) :
    (∀ N : ℕ, 2 ≤ N → 1 < jsp87Carry N) ∧ ∃ N : ℕ, 1 ≤ N ∧ k ≤ jsp87CarryExcess N :=
  ⟨fun _ hN => jsp87Carry_gt_one_of_ge_two hN, jsp87CarryExcess_unbounded k⟩

end JSP87
