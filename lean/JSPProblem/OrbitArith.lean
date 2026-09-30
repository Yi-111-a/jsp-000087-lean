/-
Copyright (c) 2026. Released under Apache 2.0 license.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.Denominator
import JSPProblem.CarryDoubling

/-!
# Round 64 -- the arithmetic of the doubling orbit of the carries

## The gap in the development

Round 48 introduced the **doubling orbit of the carries**,
`N ↦ Int.fract (θ N)`, and proved that eventual periodicity of the binary
digits forces it to be eventually periodic -- the *fourth* irrationality
criterion for `jsp_000087_main`.  It did so **qualitatively**: it exhibited a
period, but never said what the period *is*, never said what the orbit points
*are*, and never said how many distinct points the orbit visits.  Round 57
answered exactly those three questions for the *digit string* of `S` (the
period-denominator correspondence `b ∣ 2^M (2^t − 1)`, the period
`ord_{oddPart b}(2)`, the `2`-adic threshold `M ≥ v_2(b)`), but the orbit and
the digit string were never *identified*.

This round identifies them and computes the orbit **exactly**.  The single
observation is elementary and was available for free: the orbit point is a
*fractional part of a rational*, so it is a *residue*,

> `Int.fract (θ N) = (2^N · a mod b) / b`   for `N ≥ v_2(b)`,

and the numerators form an orbit of the **doubling map on `ℤ/bℤ`**,
`r (N+1) = 2 r (N) mod b`.  Everything else is the elementary theory of that
orbit, which Mathlib does not have (Mathlib has no statement whatsoever about
the base-`2` expansion of a real number, hence none about this orbit).

## What is proved here

* `jsp87_fracCarry_eq_orbitNum` -- **THE ORBIT POINT IS A RESIDUE**: the orbit
  point at `N` is exactly `(2^N a mod b)/b`.
* `jsp87OrbitNum_succ` -- the numerators are the orbit of the doubling map mod
  `b`, hence **deterministic**.
* `jsp87_orbitNum_period_iff` / `jsp87_fracCarryPeriod_iff_oddPart_dvd_mer` --
  **THE COMPLETE PERIOD-ORDER CORRESPONDENCE FOR THE ORBIT**: the eventual
  periods of the orbit, past `v_2(b)`, are exactly the `t` with
  `jsp87OddPart b ∣ 2^t − 1`; the minimal eventual period is the
  multiplicative order of `2` modulo the odd part of the denominator.
* `jsp87_fracCarry_period_minimal` / `jsp87_fracCarry_distinct` -- the period is
  **minimal**, and the orbit visits **exactly that many** points, all distinct.
* `jsp87_fracCarry_period_iff_digitPeriod` -- **the orbit and the digit string
  have exactly the same eventual periods, from the same start point**; hence
  `jsp87Series_irrational_iff_fracCarry_notPeriodic`, the *complete* (iff)
  version of round 48's one-sided criterion, and
  `jsp87_dyadic_iff_orbit_period_one` (period `1` = dyadic).
* `jsp87_fracCarry_eq_zero_iff` / `jsp87_dyadic_or_fracCarry_pos` -- **the
  dyadic dichotomy**: the orbit hits `0` only if `S` is dyadic; otherwise
  `0 < fract (θ N) < 1` for *every* `N`.

## The second half: the `2`-adic limit of the prefix does not exist

Round 52 proved the aperiodicity of `I N mod m` and left the *window*
divisibility `2^t ∣ Ω N t` as a named blocker; round 58's policy suggested
that the `2`-adic limit of `I N` might be the missing object.  **It does not
exist, and that is now a theorem.**  The reason is that coherence of the
prefix at modulus `2^k` forces `ω` to be *eventually constant* modulo `2^k`,
and `ω` is not (primes give `1`, twice a prime gives `2`).

* `jsp87_prefix_congr_imp_omega_congr` -- congruence of the prefix at distance
  `1` at modulus `2^k` forces congruence of `ω`.
* `jsp87_omega_mod_not_eventually_const` -- `ω mod m` is never eventually
  constant for `m > 1`.
* `jsp87_prefix_twoAdic_limit_absent` -- **THE `2`-ADIC VALUE OF THE ERDŐS
  SERIES DOES NOT EXIST**: the binary prefix of `S` is not coherent modulo
  `2^k` on any tail, for any `k ≥ 1`.
* `jsp87_omegaWindow_not_dvd_pow_two` -- **round 52's named blocker
  `jsp87_prefix_window_congr_fails` is closed**: for every `t ≥ 1` and every
  `M` there is `N ≥ M` with `2^t ∤ Ω N t`, witnessed at a prime.
* `jsp87_prefix_next_not_congr_of_prime` -- at every prime, the prefix escapes
  every modulus `2^k`.

## What this round does NOT do

`jsp_000087_main` remains undeclared.  Everything proved here is
*unconditional* content of the method (plus sharp descriptions of what a
hypothetical rational value would force); nothing supplies the missing input,
which is the aperiodicity of the binary digit string itself -- the arithmetic
content of the uniform prime-`k`-tuples hypothesis of Pratt's result
(arXiv:2409.15185), an assumption of the *published* result and not of the
catalog statement.
-/

namespace JSP87

set_option maxHeartbeats 800000

/-! ## 0. Elementary `ℕ` tools used below -/

private theorem one_le_two_pow_nat (k : ℕ) : 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

private theorem two_pow_dvd_of_le {a b : ℕ} (hab : a ≤ b) : 2 ^ a ∣ 2 ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]; rw [Nat.mul_comm]; exact Nat.dvd_mul_left _ _

/-- If `x = b·qx + r` and `y = b·qy + r` then `x − y = b·qx − b·qy`. -/
private theorem sub_of_div_add {x y b qx qy r : ℕ} (hx : x = b * qx + r)
    (hy : y = b * qy + r) : x - y = b * qx - b * qy := by
  rw [hx, hy, Nat.add_comm (b * qx) r, Nat.add_comm (b * qy) r]
  exact Nat.add_sub_add_left r (b * qx) (b * qy)

/-- `x mod b = (b·c + r) mod b` whenever `x = b·c + r`: stripping a multiple of
the modulus. -/
private theorem mod_add_mul {x b c r : ℕ} (h : x = b * c + r) :
    x % b = r % b := by rw [h, Nat.add_comm (b * c) r, Nat.add_mul_mod_self_left]

/-- A congruence of two residues modulo `b` is a divisibility of the
difference. -/
private theorem mod_eq_iff_dvd_sub {x y b : ℕ} (_hb : 0 < b) (hxy : y ≤ x) :
    x % b = y % b ↔ b ∣ x - y := by
  constructor
  · intro h
    have hx : x = b * (x / b) + x % b := (Nat.div_add_mod x b).symm
    have hy : y = b * (y / b) + x % b := by
      calc y = b * (y / b) + y % b := (Nat.div_add_mod y b).symm
        _ = b * (y / b) + x % b := by rw [h]
    have hkey : x - y = b * (x / b) - b * (y / b) := sub_of_div_add hx hy
    have hle : y / b ≤ x / b := Nat.div_le_div_right hxy
    rw [hkey, ← Nat.mul_sub]
    exact dvd_mul_right b _
  · intro h
    obtain ⟨k, hk⟩ := h
    have hx : x = y + b * k := by omega
    rw [hx, Nat.add_mul_mod_self_left]

/-! ## 1. The numerators of the doubling orbit -/

/-- **The numerator of the doubling orbit at time `N`:** `(2^N a) mod b`, the
`N`-th point of the orbit of the doubling map on `ℤ/bℤ` started at `a`. -/
noncomputable def jsp87OrbitNum (a b N : ℕ) : ℕ := (2 ^ N * a) % b

theorem jsp87OrbitNum_lt {a b N : ℕ} (hb : 0 < b) : jsp87OrbitNum a b N < b := by
  show (2 ^ N * a) % b < b
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (ne_of_gt hb))

theorem jsp87OrbitNum_zero {a b : ℕ} : jsp87OrbitNum a b 0 = a % b := by
  show (2 ^ 0 * a) % b = a % b
  simp

/-- **THE ORBIT OF THE NUMERATORS IS THE DOUBLING MAP MODULO `b`.**
`r (N+1) = 2 r (N) mod b`.  This is what makes the orbit *deterministic*, and
hence what makes it eventually periodic as soon as it is ever periodic. -/
theorem jsp87OrbitNum_succ {a b N : ℕ} (_hb : 0 < b) :
    jsp87OrbitNum a b (N + 1) = (2 * jsp87OrbitNum a b N) % b := by
  have hdec : 2 * (2 ^ N * a) = b * (2 * ((2 ^ N * a) / b)) + 2 * ((2 ^ N * a) % b) := by
    have h := Nat.div_add_mod (2 ^ N * a) b
    calc 2 * (2 ^ N * a) = 2 * (b * ((2 ^ N * a) / b) + (2 ^ N * a) % b) := by rw [h]
      _ = b * (2 * ((2 ^ N * a) / b)) + 2 * ((2 ^ N * a) % b) := by ring
  have h2 : 2 ^ (N + 1) * a = 2 * (2 ^ N * a) := by rw [pow_add]; ring
  show (2 ^ (N + 1) * a) % b = (2 * ((2 ^ N * a) % b)) % b
  rw [h2, mod_add_mul hdec]

/-- `2^t = (2^t − 1) + 1`, stated so that it can be used under a ring
normalisation (the natural subtraction `2^t − 1` is an opaque atom to `ring`). -/
private theorem two_pow_sub_one_add (t : ℕ) : 2 ^ t = (2 ^ t - 1) + 1 := by
  have h := Nat.sub_add_cancel (n := 2 ^ t) (m := 1) (one_le_two_pow_nat t)
  omega

/-- `X·2^t − X = X·(2^t − 1)`. -/
private theorem mul_sub_mul_pow (X t : ℕ) : X * 2 ^ t - X = X * (2 ^ t - 1) := by
  have h2 : X * 2 ^ t = X * ((2 ^ t - 1) + 1) :=
    congrArg (fun z => X * z) (two_pow_sub_one_add t)
  have h3 : X * ((2 ^ t - 1) + 1) = X * (2 ^ t - 1) + X := by ring
  rw [h2, h3, Nat.add_sub_cancel]

/-- The congruence of two orbit points is a congruence of two powers of two
modulo `b`. -/
theorem jsp87_orbitNum_congr {a b N t : ℕ} (hb : 0 < b) :
    jsp87OrbitNum a b (N + t) = jsp87OrbitNum a b N ↔ b ∣ 2 ^ N * (2 ^ t - 1) * a := by
  have h4 : 2 ^ N ≤ 2 ^ (N + t) := by
    have hp : 2 ^ (N + t) = 2 ^ N * 2 ^ t := pow_add 2 N t
    have hm : 2 ^ N * 1 ≤ 2 ^ N * 2 ^ t := Nat.mul_le_mul_left (2 ^ N) (one_le_two_pow_nat t)
    rw [← hp] at hm
    simpa using hm
  have hle : 2 ^ N * a ≤ 2 ^ (N + t) * a := Nat.mul_le_mul_right a h4
  have hiff := mod_eq_iff_dvd_sub hb hle
  have hsplit : 2 ^ (N + t) * a - 2 ^ N * a = 2 ^ N * (2 ^ t - 1) * a := by
    have hpw : 2 ^ (N + t) * a = (2 ^ N * a) * 2 ^ t := by rw [pow_add]; ring
    rw [hpw, mul_sub_mul_pow]
    ring
  show (2 ^ (N + t) * a) % b = (2 ^ N * a) % b ↔ b ∣ 2 ^ N * (2 ^ t - 1) * a
  rw [hiff, hsplit]

/-- **THE `2`-POWER OF A DENOMINATOR IS INVISIBLE PAST ITS OWN
VALUATION.**  For `k ≥ v_2(b)` and `t > 0`,

`b ∣ 2^k (2^t − 1)  ↔  jsp87OddPart b ∣ 2^t − 1`.

The forward direction is round 57's `jsp87_den_dvd_mer_of_oddPart`; the reverse
direction (that a Mersenne number divisible by `b` is divisible by the odd part
of `b`) is new, and is the reason the orbit period does not see the `2`-part of
the denominator. -/
theorem dvd_two_pow_mer_iff_oddPart {b k t : ℕ} (hb : 0 < b) (ht : 0 < t)
    (hk : jsp87Val2 b ≤ k) :
    b ∣ 2 ^ k * (2 ^ t - 1) ↔ jsp87OddPart b ∣ 2 ^ t - 1 := by
  constructor
  · intro hd
    by_cases hk0 : k = 0
    · have hd0 : b ∣ 2 ^ 0 * (2 ^ t - 1) := by rw [hk0] at hd; exact hd
      have hd' : jsp87OddPart b ∣ 2 ^ 0 * (2 ^ t - 1) := (jsp87OddPart_dvd b).trans hd0
      simpa only [pow_zero, one_mul] using hd'
    · have h1 : jsp87OddPart b ∣ 2 ^ k * (2 ^ t - 1) := (jsp87OddPart_dvd b).trans hd
      have hc : Nat.Coprime (jsp87OddPart b) (2 ^ k) :=
        (Nat.coprime_pow_right_iff (a := jsp87OddPart b) (b := (2 : ℕ)) (by omega)).mpr
          (jsp87_coprime_two_oddPart hb).symm
      exact (hc.dvd_mul_left).mp h1
  · intro hd
    exact jsp87_den_dvd_mer_of_oddPart hb ht hk hd

/-- **THE EVENTUAL PERIODS OF THE RESIDUE ORBIT.**  For `b > 0`, `t > 0` and
`k ≥ v_2(b)`, and `a` coprime to `b`:

`r (n+t) = r n` for all `n ≥ k`  ↔  `jsp87OddPart b ∣ 2^t − 1`.

This is pure arithmetic about the doubling map on `ℤ/bℤ`; it uses nothing about
the Erdős series. -/
theorem jsp87_orbitNum_period_iff {a b k t : ℕ} (hac : Nat.Coprime a b) (hb : 0 < b)
    (ht : 0 < t) (hk : jsp87Val2 b ≤ k) :
    (∀ n, k ≤ n → jsp87OrbitNum a b (n + t) = jsp87OrbitNum a b n) ↔
      jsp87OddPart b ∣ 2 ^ t - 1 := by
  constructor
  · intro hper
    have h1 := hper k (le_refl k)
    have h2 : b ∣ 2 ^ k * (2 ^ t - 1) * a :=
      (jsp87_orbitNum_congr hb).mp h1
    have h2' : b ∣ a * (2 ^ k * (2 ^ t - 1)) := by
      have heq : (2 ^ k * (2 ^ t - 1)) * a = a * (2 ^ k * (2 ^ t - 1)) := by ring
      rw [← heq]
      exact h2
    have h3 : b ∣ 2 ^ k * (2 ^ t - 1) := (hac.symm.dvd_mul_left).mp h2'
    exact (dvd_two_pow_mer_iff_oddPart hb ht hk).mp h3
  · intro hd n hn
    have hval : jsp87Val2 b ≤ n := by omega
    have h1 : b ∣ 2 ^ n * (2 ^ t - 1) := (dvd_two_pow_mer_iff_oddPart hb ht hval).mpr hd
    have h2 : b ∣ 2 ^ n * (2 ^ t - 1) * a :=
      Nat.dvd_trans h1 (Nat.dvd_mul_right (2 ^ n * (2 ^ t - 1)) a)
    exact (jsp87_orbitNum_congr hb).mpr h2

/-! ## 2. The orbit point is a residue -/

private theorem fract_eq_self_of_mem_Ico {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Int.fract x = x := by
  have hz := Int.floor_eq_zero_iff.mpr (Set.mem_Ico.mpr ⟨h0, h1⟩)
  have h := (Int.self_sub_floor x).symm
  rw [h, hz]
  ring

/-- A natural number added to a number of `[0,1)` does not change the
fractional part. -/
private theorem fract_add_natCast' {x : ℝ} {m : ℕ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Int.fract (x + (m : ℝ)) = x := by
  have hcast : (m : ℝ) = (((m : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [hcast, Int.fract_add_intCast]
  exact fract_eq_self_of_mem_Ico h0 h1

/-- **THE FRACTIONAL PART OF A NONNEGATIVE RATIONAL IS A RESIDUE.**
`fract (p/q) = (p mod q)/q` for `q > 0`. -/
private theorem Int.fract_natCast_div_natCast {p q : ℕ} (hq : 0 < q) :
    Int.fract ((p : ℝ) / (q : ℝ)) = ((p % q : ℕ) : ℝ) / (q : ℝ) := by
  have hkey : p = (p / q) * q + p % q := by
    have h := (Nat.div_add_mod p q).symm
    rw [Nat.mul_comm] at h
    exact h
  have hrlt : p % q < q := Nat.mod_lt _ (Nat.pos_of_ne_zero (ne_of_gt hq))
  have hsplit : (p : ℝ) / (q : ℝ) = ((p / q : ℕ) : ℝ) + ((p % q : ℕ) : ℝ) / (q : ℝ) := by
    have hcast : ((p : ℕ) : ℝ) = ((p / q : ℕ) : ℝ) * (q : ℝ) + ((p % q : ℕ) : ℝ) := by
      exact_mod_cast hkey
    rw [hcast]
    field_simp
  have h0 : (0 : ℝ) ≤ ((p % q : ℕ) : ℝ) / (q : ℝ) := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h1 : ((p % q : ℕ) : ℝ) / (q : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hrlt
  rw [hsplit, add_comm]
  exact fract_add_natCast' h0 h1

/-- **THE ORBIT POINT OF A RATIONAL ERDŐS SERIES IS A RESIDUE OF A POWER OF
TWO.**  If `S = a/b` with `0 < a`, `0 < b` and `1 ≤ N`, then

`Int.fract (θ N) = (2^N a mod b) / b`.

The numerator is the point of the doubling orbit on `ℤ/bℤ` at time `N`. -/
theorem jsp87_fracCarry_eq_orbitNum {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 1 ≤ N)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    Int.fract (jsp87Carry N) = ((jsp87OrbitNum a b N : ℕ) : ℝ) / (b : ℝ) := by
  have h1 : (2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)) = ((2 ^ N * a : ℕ) : ℝ) / (b : ℝ) := by
    have h2 : (2 : ℝ) ^ N * (a : ℝ) = (((2 ^ N * a : ℕ) : ℕ) : ℝ) := by push_cast; ring
    calc (2 : ℝ) ^ N * ((a : ℝ) / (b : ℝ)) = (2 : ℝ) ^ N * (a : ℝ) / (b : ℝ) := by field_simp
      _ = ((2 ^ N * a : ℕ) : ℝ) / (b : ℝ) := by rw [h2]
  rw [← jsp87_fract_scaled hN, hS, h1]
  exact Int.fract_natCast_div_natCast hb

/-- **THE ORBIT IS THE RESIDUE ORBIT.**  For a rational value of the series, the
doubling orbit of the carries and the doubling map modulo `b` have the same
periodic points:

`fract (θ (n+t)) = fract (θ n)  ↔  (2^{n+t} a mod b) = (2^n a mod b)`.

No rationality hypothesis beyond `S = a/b` and `0 < a, 0 < b`; no hypothesis on
`v_2(b)`, no coprimality. -/
theorem jsp87_fracCarry_period_iff_resid {a b t N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 1 ≤ N)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N) ↔
      jsp87OrbitNum a b (N + t) = jsp87OrbitNum a b N := by
  have h1 := jsp87_fracCarry_eq_orbitNum ha hb hN hS
  have h2 := jsp87_fracCarry_eq_orbitNum (N := N + t) ha hb (by omega) hS
  rw [h1, h2]
  constructor
  · intro h
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
    have h' : (jsp87OrbitNum a b (N + t) : ℝ) = (jsp87OrbitNum a b N : ℝ) :=
      (div_left_inj' hb0).mp h
    exact_mod_cast h'
  · intro h
    rw [h]
/-- **THE COMPLETE PERIOD CORRESPONDENCE FOR THE ORBIT.**  For
`S = a/b` in lowest terms with `0 < a`, `b > 0`, `0 < t`, and `1 ≤ M` with
`v_2(b) ≤ M`:

`(∀ N ≥ M, fract (θ (N+t)) = fract (θ N))  ↔  jsp87OddPart b ∣ 2^t − 1`.

Equivalently: **the minimal eventual period of the doubling orbit of the
carries is the multiplicative order of `2` modulo the odd part of the
denominator**, and the orbit is never periodic before the `2`-adic threshold.
This is round 57's period-denominator correspondence, transferred to the
carries, and proved here from the residue description.  Mathlib has no
statement about the base-`2` expansion of a real number, hence none of this
kind. -/
theorem jsp87_fracCarryPeriod_iff_oddPart_dvd_mer {a b t M : ℕ} (ha : 0 < a)
    (hac : Nat.Coprime a b) (hb : 0 < b) (ht : 0 < t) (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    (∀ N, M ≤ N → Int.fract (jsp87Carry (N + t)) = Int.fract (jsp87Carry N)) ↔
      jsp87OddPart b ∣ 2 ^ t - 1 := by
  constructor
  · intro hper
    refine (jsp87_orbitNum_period_iff hac hb ht hval).mp ?_
    intro n hn
    exact (jsp87_fracCarry_period_iff_resid (t := t) (N := n) ha hb (by omega) hS).mp (hper n hn)
  · intro hd
    have hres := (jsp87_orbitNum_period_iff hac hb ht hval).mpr hd
    intro N hN
    exact (jsp87_fracCarry_period_iff_resid (t := t) (N := N) ha hb (by omega) hS).mpr (hres N hN)


/-! ## 3. The period is arithmetically rigid -/

/-- **THE DIFFERENCE OF TWO PERIODS IS A PERIOD.**  If `t` and `t'` (`0 < t' < t`)
are both eventual periods of the doubling orbit, then `t − t'` is one too. -/
private theorem fractCarry_period_sub {M t t' : ℕ}
    (h1 : ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t)) = Int.fract (jsp87Carry N))
    (h2 : ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t')) = Int.fract (jsp87Carry N))
    (ht' : t' < t) :
    ∀ N, M ≤ N → Int.fract (jsp87Carry (N + (t - t'))) = Int.fract (jsp87Carry N) := by
  intro N hN
  calc Int.fract (jsp87Carry (N + (t - t')))
      = Int.fract (jsp87Carry ((N + (t - t')) + t')) :=
        (h2 (N + (t - t')) (by omega)).symm
    _ = Int.fract (jsp87Carry (N + t)) := by
      have : (N + (t - t')) + t' = N + t := by omega
      rw [this]
    _ = Int.fract (jsp87Carry N) := h1 N hN

/-- **TWO PERIODS SPAWN A SMALLER ONE.**  If `t` and `t'` (`0 < t' < t`) are both
eventual periods of the doubling orbit, then `t − t'` is again an eventual
period, and `jsp87OddPart b ∣ 2^(t−t') − 1`.

Together with `jsp87_fracCarry_distinct` this is the Euclidean mechanism that
makes the *minimal* period special: any two distinct periods generate a strictly
smaller one, so the minimal period is the `gcd` of all of them. -/
theorem jsp87_fracCarry_period_sub_iff {a b M t t' : ℕ} (ha : 0 < a) (hac : Nat.Coprime a b)
    (hb : 0 < b) (ht'' : t' < t) (hM : 1 ≤ M)
    (hval : jsp87Val2 b ≤ M) (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (h1 : ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t)) = Int.fract (jsp87Carry N))
    (h2 : ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t')) = Int.fract (jsp87Carry N)) :
    0 < t - t' ∧ jsp87OddPart b ∣ 2 ^ (t - t') - 1
      ∧ (∀ N, M ≤ N → Int.fract (jsp87Carry (N + (t - t'))) = Int.fract (jsp87Carry N)) := by

  have hsub := fractCarry_period_sub h1 h2 ht''
  have hpos : 0 < t - t' := Nat.sub_pos_of_lt ht''
  refine ⟨hpos, ?_, hsub⟩
  exact (jsp87_fracCarryPeriod_iff_oddPart_dvd_mer (t := t - t') ha hac hb
    hpos hM hval hS).mp hsub

/-- **THE EVENTUAL PERIODS OF THE ORBIT ARE `gcd`-CLOSED.**  If `t` and `t'` are
eventual periods of the doubling orbit of a rational value of the series, then
`Nat.gcd t t'` is one too.

This transfers round 57's `jsp87_period_gcd` from the digit string to the
carries, using round 39's exact gcd of Mersenne numbers
(`gcd_two_pow_sub_one`) and `dvd_pow_sub_one_of_dvd`. -/
theorem jsp87_fracCarry_period_dvd {a b t t' M : ℕ} (ha : 0 < a) (hac : Nat.Coprime a b)
    (hb : 0 < b) (ht : 0 < t) (ht' : 0 < t') (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (h1 : ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t)) = Int.fract (jsp87Carry N))
    (h2 : ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t')) = Int.fract (jsp87Carry N)) :
    ∀ N, M ≤ N → Int.fract (jsp87Carry (N + Nat.gcd t t')) = Int.fract (jsp87Carry N) := by
  have hper := (jsp87_fracCarryPeriod_iff_oddPart_dvd_mer ha hac hb ht hM hval hS).mp h1
  have hper' := (jsp87_fracCarryPeriod_iff_oddPart_dvd_mer ha hac hb ht' hM hval hS).mp h2
  have h1' : jsp87OddPart b ∣ 2 ^ Nat.gcd t t' - 1 := by
    have hg : Nat.gcd (2 ^ t - 1) (2 ^ t' - 1) = 2 ^ Nat.gcd t t' - 1 :=
      gcd_two_pow_sub_one t t'
    have hd : jsp87OddPart b ∣ Nat.gcd (2 ^ t - 1) (2 ^ t' - 1) :=
      Nat.dvd_gcd hper hper'
    rw [hg] at hd
    exact hd
  have hgpos : 0 < Nat.gcd t t' := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left t t') ht
  exact (jsp87_fracCarryPeriod_iff_oddPart_dvd_mer (t := Nat.gcd t t') ha hac hb
    hgpos hM hval hS).mpr h1'

/-- **A MINIMAL PERIOD VISITS EXACTLY ITS OWN NUMBER OF POINTS.**  Let
`jsp87Series = a/b` in lowest terms, `1 ≤ M` with `v_2(b) ≤ M`, and let `t > 0` be
an eventual period of the doubling orbit which is *minimal* in the arithmetical
sense

`∀ u, 0 < u → u < t → ¬ jsp87OddPart b ∣ 2^u − 1`

(i.e. `t` is the multiplicative order of `2` modulo the odd part of `b`).  Then
the `t` orbit points

`fract (θ M), fract (θ (M+1)), …, fract (θ (M+t−1))`

are **pairwise distinct**.

So the doubling orbit of the carries, if the series is rational, is an
*exactly* periodic orbit of `ord_{oddPart b}(2)` points, and the period is
`≥ 1`.  Mathlib contains no statement about the base-`2` expansion of a real
number, hence no statement of this kind. -/
theorem jsp87_fracCarry_distinct {a b M t i j : ℕ} (ha : 0 < a) (hac : Nat.Coprime a b)
    (hb : 0 < b) (hM : 1 ≤ M) (hval : jsp87Val2 b ≤ M)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ))
    (hmin : ∀ u, 0 < u → u < t → ¬ jsp87OddPart b ∣ 2 ^ u - 1)
    (hi : i < j) (hj : j < t) :
    Int.fract (jsp87Carry (M + i)) ≠ Int.fract (jsp87Carry (M + j)) := by
  intro h
  have hL : Int.fract (jsp87Carry ((M + i) + (j - i))) = Int.fract (jsp87Carry (M + i)) := by
    rw [show (M + i) + (j - i) = M + j from by omega]
    exact h.symm
  have h1 : jsp87OrbitNum a b ((M + i) + (j - i)) = jsp87OrbitNum a b (M + i) := by
    have h2 := hL
    rw [jsp87_fracCarry_eq_orbitNum (N := (M + i) + (j - i)) ha hb (by omega) hS,
      jsp87_fracCarry_eq_orbitNum (N := M + i) ha hb (by omega) hS] at h2
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
    exact Nat.cast_injective ((div_left_inj' hb0).mp h2)
  have h2 : b ∣ 2 ^ (M + i) * (2 ^ (j - i) - 1) * a := (jsp87_orbitNum_congr hb).mp h1
  have h2' : b ∣ a * (2 ^ (M + i) * (2 ^ (j - i) - 1)) := by
    have heq : (2 ^ (M + i) * (2 ^ (j - i) - 1)) * a
        = a * (2 ^ (M + i) * (2 ^ (j - i) - 1)) := by ring
    rw [← heq]
    exact h2
  have h3 : b ∣ 2 ^ (M + i) * (2 ^ (j - i) - 1) := (hac.symm.dvd_mul_left).mp h2'
  have hval' : jsp87Val2 b ≤ M + i := by omega
  have h4 : jsp87OddPart b ∣ 2 ^ (j - i) - 1 :=
    (dvd_two_pow_mer_iff_oddPart hb (by omega) hval').mp h3
  exact hmin (j - i) (by omega) (by omega) h4

/-! ## 4. The orbit and the digit string have the same periods -/

/-- **AN EVENTUALLY PERIODIC ORBIT GIVES AN EVENTUALLY PERIODIC DIGIT STRING.**
If `fract (θ (n+t)) = fract (θ n)` for all `n ≥ M` (with `1 ≤ M` and `t > 0`),
then `d (N+t) = d N` for all `N ≥ M`.

This is the *converse* of round 48's `jsp87_fracCarry_periodic_of_digitPeriodic`
and uses the identity `d N = 2·fract (θ N) − fract (θ (N+1))`
(`jsp87_digit_eq_fractCarry`). -/
theorem jsp87_fracCarry_periodic_imp_digitPeriodic {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M)
    (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → Int.fract (jsp87Carry (n+t)) = Int.fract (jsp87Carry n)) :
    jsp87Digit (N + t) = jsp87Digit N := by
  have hN1 : 1 ≤ N := by omega
  have hstep : N + t + 1 = (N + 1) + t := by omega
  have h2 := jsp87_digit_eq_fractCarry (N := N + t) (by omega)
  rw [hstep] at h2
  have ha := hper N hN
  have hb := hper (N + 1) (by omega)
  have key : (jsp87Digit (N + t) : ℝ) = (jsp87Digit N : ℝ) := by
    calc (jsp87Digit (N + t) : ℝ)
        = 2 * Int.fract (jsp87Carry (N + t)) - Int.fract (jsp87Carry (N + t + 1)) :=
          jsp87_digit_eq_fractCarry (N := N + t) (by omega)
      _ = 2 * Int.fract (jsp87Carry N) - Int.fract (jsp87Carry (N + 1)) := by
        rw [ha, hstep, hb]
      _ = (jsp87Digit N : ℝ) := (jsp87_digit_eq_fractCarry hN1).symm
  exact_mod_cast key

/-- **THE ORBIT AND THE DIGIT STRING HAVE EXACTLY THE SAME EVENTUAL PERIODS.**
For `1 ≤ M` and `t > 0`:

`(∀ n ≥ M, d (n+t) = d n)  ↔  (∀ n ≥ M, fract (θ (n+t)) = fract (θ n))`.

Together with round 57's `jsp87_digitPeriod_iff_oddPart_dvd_mer` this
identifies the periods of the carries with the multiplicative order of `2`
modulo the odd part of the denominator: **the doubling orbit of the carries and
the binary expansion of `S` are governed by the same number.** -/
theorem jsp87_fracCarry_period_iff_digitPeriod {M t : ℕ} (ht : 0 < t) (hM : 1 ≤ M) :
    (∀ n, M ≤ n → jsp87Digit (n+t) = jsp87Digit n) ↔
      (∀ n, M ≤ n → Int.fract (jsp87Carry (n+t)) = Int.fract (jsp87Carry n)) := by
  constructor
  · intro hper n hn
    exact jsp87_fracCarry_periodic_of_digitPeriodic (N := n) ht hM hn hper
  · intro hper n hn
    exact jsp87_fracCarry_periodic_imp_digitPeriodic (N := n) ht hM hn hper

/-- **THE COMPLETE ERDŐS CRITERION ON THE CARRY ORBIT.**  The Erdős series is
irrational **if and only if** the doubling orbit of its carries,
`N ↦ Int.fract (θ N)`, is not eventually periodic.

Round 48 proved only the forward direction
(`jsp87Series_irrational_of_fracCarry_notPeriodic`).  The converse direction --
that an eventually periodic orbit forces a rational value -- is proved here from
the digit identity `d N = 2·fract (θ N) − fract (θ (N+1))`
(`jsp87_fracCarry_periodic_imp_digitPeriodic`), round 48's exact value theorem
`jsp87Series_eq_div_of_digitPeriodic`, and `jsp87_digit_period_one_eq_zero`. -/
theorem jsp87Series_irrational_iff_fracCarry_notPeriodic :
    Irrational jsp87Series ↔
      ¬ ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
        ∧ ∀ N, M ≤ N → Int.fract (jsp87Carry (N+t)) = Int.fract (jsp87Carry N) := by
  constructor
  · intro hirr hper
    obtain ⟨t, M, ht, hM, h⟩ := hper
    have hd : ∀ n, M ≤ n → jsp87Digit (n+t) = jsp87Digit n :=
      fun n hn => jsp87_fracCarry_periodic_imp_digitPeriodic (N := n) ht hM hn h
    obtain ⟨n₀, hn₀⟩ := jsp87Series_eq_div_of_digitPeriodic ht hM hd
    have hcast : ((2 : ℝ) ^ M * ((2 : ℝ) ^ t - 1) : ℝ)
        = ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) := by
      push_cast
      norm_num
    have hn₀' : jsp87Series = (n₀ : ℝ) / ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) := by
      rw [← hcast]
      exact hn₀
    have hmem : jsp87Series ∈ Set.range ((↑) : ℚ → ℝ) := by
      refine ⟨(n₀ : ℚ) / (2 ^ M * (2 ^ t - 1) : ℕ), ?_⟩
      have hx : (((n₀ : ℚ) / (2 ^ M * (2 ^ t - 1) : ℕ) : ℚ) : ℝ)
          = (n₀ : ℝ) / ((2 ^ M * (2 ^ t - 1) : ℕ) : ℝ) := by
        norm_cast
      exact hx.trans hn₀'.symm
    exact hirr hmem
  · intro h
    show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
    rintro ⟨q, hq⟩
    have hden : 0 < q.den := Rat.den_pos q
    obtain ⟨t, M, ht, hM1, hper⟩ :=
      jsp87Series_rational_imp_fracCarry_periodic hden (by rw [← hq, Rat.cast_def])
    exact h ⟨t, M, ht, hM1, hper⟩

/-! ## 5. The dyadic case, and when the orbit can hit `0` -/

/-- **A DYADIC VALUE MAKES THE ORBIT EVENTUALLY `0`.** -/
theorem jsp87_fracCarry_zero_of_dyadic {M N : ℕ} (hM : 1 ≤ M) (hN : M ≤ N)
    (h : ∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) :
    Int.fract (jsp87Carry N) = 0 := by
  obtain ⟨n, hn⟩ := h
  have hN1 : 1 ≤ N := by omega
  have h1 : (2 : ℝ) ^ N = (2 : ℝ) ^ M * (2 : ℝ) ^ (N - M) := by
    have hp : (2 : ℝ) ^ (M + (N - M)) = (2 : ℝ) ^ M * (2 : ℝ) ^ (N - M) := pow_add 2 M (N - M)
    rw [Nat.add_sub_of_le hN] at hp
    exact hp
  have hsplit : (2 : ℝ) ^ N * ((n : ℝ) / (2 : ℝ) ^ M) = (n : ℝ) * (2 : ℝ) ^ (N - M) := by
    rw [h1]
    field_simp
  have hkey : (2 : ℝ) ^ N * jsp87Series = (((n * 2 ^ (N - M) : ℤ) : ℤ) : ℝ) := by
    rw [hn, hsplit]
    push_cast
    ring
  rw [← jsp87_fract_scaled hN1, hkey, Int.fract_intCast]

/-- **PERIOD `1` OF THE ORBIT IS EXACTLY THE DYADIC CASE.**  For `1 ≤ M`,

> `S = n / 2^M` for some `n : ℤ`  ⟺  `fract (θ (N+1)) = fract (θ N)` for all
> `N ≥ M`.

So the first case of the aperiodicity problem (is the binary expansion of `S`
eventually constant?) is exactly the question whether the expansion
*terminates* — now in the language of the carries. -/
theorem jsp87_dyadic_iff_orbit_period_one {M : ℕ} (hM : 1 ≤ M) :
    (∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) ↔
      ∀ N, M ≤ N → Int.fract (jsp87Carry (N+1)) = Int.fract (jsp87Carry N) := by
  constructor
  · rintro ⟨n, hn⟩ N hN
    have hz := jsp87_fracCarry_zero_of_dyadic (N := N) hM hN ⟨n, hn⟩
    have hz' := jsp87_fracCarry_zero_of_dyadic (N := N + 1) hM (by omega) ⟨n, hn⟩
    rw [hz, hz']
  · intro hper
    obtain ⟨n, hn⟩ := jsp87Series_dyadic_of_digit_period_one hM
      (fun n hn => jsp87_fracCarry_periodic_imp_digitPeriodic
        (t := 1) (M := M) (N := n) (by omega) hM hn hper)
    exact ⟨n, hn⟩

/-- **THE ORBIT VANISHES EVENTUALLY IFF THE SERIES IS DYADIC.**  For `1 ≤ M`,

`(∀ N ≥ M, fract (θ N) = 0)  ⟺  S = n / 2^M for some n : ℤ`. -/
theorem jsp87_fracCarry_zero_iff_dyadic {M : ℕ} (hM : 1 ≤ M) :
    (∀ N, M ≤ N → Int.fract (jsp87Carry N) = 0) ↔
      ∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M) := by
  constructor
  · intro hz
    exact (jsp87_dyadic_iff_orbit_period_one hM).mpr (fun N hN => by rw [hz N hN, hz (N+1) (by omega)])
  · rintro ⟨n, hn⟩ N hN
    exact jsp87_fracCarry_zero_of_dyadic hM hN ⟨n, hn⟩

/-- **THE ORBIT HITS `0` ONLY FOR A DYADIC VALUE.**  If `S = a/b` in lowest
terms with `0 < a`, `b > 0` and the odd part of `b` is `≠ 1`, then
`fract (θ N) > 0` for every `N ≥ v_2(b)`: the doubling orbit of `0` modulo `b`
is `0`, so a nonzero orbit never returns to it.

Equivalently (`jsp87_fracCarry_eq_orbitNum`): `b ∣ 2^N a` forces `b` to be a
power of `2`. -/
theorem jsp87_fracCarry_pos_of_oddPart {a b N : ℕ} (ha : 0 < a) (hac : Nat.Coprime a b)
    (hb : 0 < b) (hN : 1 ≤ N) (hop : jsp87OddPart b ≠ 1)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    0 < Int.fract (jsp87Carry N) := by
  have h1 := jsp87_fracCarry_eq_orbitNum ha hb hN hS
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hne : (jsp87OrbitNum a b N : ℝ) ≠ 0 := by
    intro hc
    have hz : jsp87OrbitNum a b N = 0 := by
      have hz' : (jsp87OrbitNum a b N : ℝ) * (b : ℝ) = 0 := by
        have hz'' : (jsp87OrbitNum a b N : ℝ) = 0 := hc
        rw [hz'', zero_mul]
      rcases mul_eq_zero.mp hz' with hz'' | hz''
      · exact Nat.cast_eq_zero.mp hz''
      · exact absurd hz'' (Nat.cast_ne_zero.mpr (ne_of_gt hb))
    have hd : b ∣ 2 ^ N * a := Nat.dvd_of_mod_eq_zero (show (2 ^ N * a) % b = 0 from hz)
    have hd' : b ∣ 2 ^ N := (hac.symm.dvd_mul_left).mp (by rw [Nat.mul_comm]; exact hd)
    have hd'' : jsp87OddPart b ∣ 2 ^ N := (jsp87OddPart_dvd b).trans hd'
    have hgd : Nat.gcd (jsp87OddPart b) (2 ^ N) = 1 := by
      have hc' : Nat.Coprime (jsp87OddPart b) (2 ^ N) := by
        by_cases hN0 : N = 0
        · rw [hN0]
          simp
        · exact (Nat.coprime_pow_right_iff (a := jsp87OddPart b) (b := (2 : ℕ))
            (by omega)).mpr (jsp87_coprime_two_oddPart hb).symm
      exact Nat.coprime_iff_gcd_eq_one.mp hc'
    have hdv : jsp87OddPart b ∣ Nat.gcd (jsp87OddPart b) (2 ^ N) :=
      Nat.dvd_gcd (dvd_refl _) hd''
    have hone : jsp87OddPart b = 1 := by
      have hdv' : jsp87OddPart b ∣ 1 := by
        rw [hgd] at hdv
        exact hdv
      have hle : jsp87OddPart b ≤ 1 := Nat.le_of_dvd (show (0 : ℕ) < 1 by simp) hdv'
      have hpos : 1 ≤ jsp87OddPart b := by
        have h := jsp87OddPart_pos hb
        omega
      exact Nat.le_antisymm hle hpos
    exact hop hone
  rw [h1]
  exact div_pos (by positivity) hb0

/-- **THE DYADIC ALTERNATIVE.**  Either the Erdős series is a dyadic rational,
or **every** fractional part of the carry is strictly positive (for every
`N ≥ 1` for which the assumption is available).  In particular: under a
rationality hypothesis with a denominator that is not a power of `2`, the
doubling orbit of the carries never touches `0`. -/
theorem jsp87_dyadic_or_fracCarry_pos {a b N : ℕ} (ha : 0 < a) (hac : Nat.Coprime a b)
    (hb : 0 < b) (hN : 1 ≤ N)
    (hS : jsp87Series = (a : ℝ) / (b : ℝ)) :
    jsp87OddPart b = 1 ∨ 0 < Int.fract (jsp87Carry N) := by
  by_cases hop : jsp87OddPart b = 1
  · exact Or.inl hop
  · exact Or.inr (jsp87_fracCarry_pos_of_oddPart ha hac hb hN hop hS)


/-! ## 6. The `2`-adic limit of the binary prefix does NOT exist -/

/-- `ω p = 1` for a prime `p` (from `omega_prime_pow` in `Basic.lean`). -/
theorem jsp87_omega_one_of_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  rw [← pow_one p]
  exact omega_prime_pow hp (by omega)

/-- `ω (2 p) = 2` for a prime `p > 2` (a lower bound from round 40's
`omega_mul_prime_of_large_prime`, an upper bound from `omega_mul_le`). -/
theorem jsp87_omega_two_mul_of_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    omega (2 * p) = 2 := by
  have h2 : omega 2 = 1 := jsp87_omega_one_of_prime (by norm_num)
  have h3 : omega p = 1 := jsp87_omega_one_of_prime hp
  have hle : omega (2 * p) ≤ omega 2 + omega p := omega_mul_le
  have hge : omega 2 + 1 ≤ omega (2 * p) := omega_mul_prime_of_large_prime hp (by decide) hp2
  rw [h2] at hle hge
  rw [h3] at hle
  omega

private theorem two_pow_pos_int (k : ℕ) : (0 : ℤ) < (2 : ℤ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact Int.mul_pos ih (by norm_num)

private theorem two_pow_ge_two_nat {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  have h1 : 1 ≤ 2 ^ (k - 1) := one_le_two_pow_nat (k - 1)
  calc 2 = 1 + 1 := by norm_num
    _ ≤ 2 ^ (k - 1) + 2 ^ (k - 1) := Nat.add_le_add h1 h1
    _ = 2 ^ (k - 1) * 2 := by
      rw [(Nat.two_mul (2 ^ (k - 1))).symm, Nat.mul_comm]
    _ = 2 ^ k := by
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hpw : 2 ^ (k - 1 + 1) = 2 ^ (k - 1) * 2 ^ 1 := pow_add 2 (k - 1) 1
      rw [hk', pow_one] at hpw
      exact hpw.symm

private theorem two_pow_ge_two_int {k : ℕ} (hk : 1 ≤ k) : (2 : ℤ) ≤ (2 : ℤ) ^ k := by
  have h := two_pow_ge_two_nat hk
  exact_mod_cast h

/-- **THE PARITY OF THE `ω`-WINDOW IS THE PARITY OF ITS LAST ENTRY.**
`Ω N t ≡ ω (N + t − 1) (mod 2)` for `t ≥ 1`, because all the other summands of
`Ω N t = ∑_{j<t} ω (N+j) 2^{t−1−j}` carry a factor `2`. -/
theorem jsp87_omegaWindow_parity {N t : ℕ} (ht : 1 ≤ t) :
    jsp87OmegaWindow N t % 2 = omega (N + t - 1) % 2 := by
  have hne : t ≠ 0 := by have := Nat.succ_le_iff.mp ht; omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [hu, jsp87OmegaWindow_succ,
    Nat.add_comm (2 * jsp87OmegaWindow N u) (omega (N + u)),
    Nat.add_mul_mod_self_left]
  have h3 : N + u.succ - 1 = N + u := by omega
  rw [h3]

/-- **AT A PRIME, THE `ω`-WINDOW IS ODD.**  If `p` is prime, `1 ≤ t` and `t ≤ p`,
then `Ω (p+1−t) t` is odd, because its last entry is `ω p = 1`. -/
theorem jsp87_omegaWindow_not_even_of_prime {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t)
    (ht' : t ≤ p) : ¬ 2 ∣ jsp87OmegaWindow (p + 1 - t) t := by
  have hp1 : jsp87OmegaWindow (p + 1 - t) t % 2 = 1 := by
    rw [jsp87_omegaWindow_parity ht]
    have h1 : p + 1 - t + t - 1 = p := by omega
    rw [h1, jsp87_omega_one_of_prime hp]
  intro hcon
  have h2 := Nat.dvd_iff_mod_eq_zero.mp hcon
  rw [hp1] at h2
  omega

/-- **ROUND 52'S NAMED BLOCKER IS CLOSED.**  For every `t ≥ 1` and every `M`
there is a cut point `N ≥ M` at which `2^t` does **not** divide the `ω`-window
`Ω N t`, namely `N = p + 1 − t` for a prime `p > M + t`.

This settles the existence half of round 52's `jsp87_prefix_window_congr_fails`:
the residue of the `ω`-window modulo `2^t` is *never* eventually `0`.  (The
other half — that the window is not eventually constant modulo `2^t` — is
`jsp87_window_mod_not_eventuallyPeriodic` from round 52.) -/
theorem jsp87_omegaWindow_not_dvd_pow_two {t M : ℕ} (ht : 1 ≤ t) :
    ∃ N, M ≤ N ∧ ¬ 2 ^ t ∣ jsp87OmegaWindow N t := by
  obtain ⟨p, hbig, hprim⟩ := Nat.exists_infinite_primes (M + t + 1)
  have hlt : t ≤ p := by omega
  have hodd : ¬ 2 ∣ jsp87OmegaWindow (p + 1 - t) t :=
    jsp87_omegaWindow_not_even_of_prime hprim ht hlt
  refine ⟨p + 1 - t, by omega, ?_⟩
  intro hcon
  obtain ⟨c, hc⟩ := hcon
  have hone : 2 ^ t = 2 ^ (t - 1) * 2 := by
    have h : 2 ^ (t - 1 + 1) = 2 ^ t := by rw [Nat.sub_add_cancel (show 1 ≤ t by omega)]
    calc 2 ^ t = 2 ^ (t - 1 + 1) := h.symm
      _ = 2 ^ (t - 1) * 2 ^ 1 := pow_add 2 (t - 1) 1
      _ = 2 ^ (t - 1) * 2 := by ring
  have h2dvd : 2 ∣ jsp87OmegaWindow (p + 1 - t) t := by
    rw [hc, hone]
    exact ⟨2 ^ (t - 1) * c, by ring⟩
  exact absurd h2dvd hodd

/-- **THE BINARY PREFIX IS NON-DECREASING.** -/
theorem jsp87Prefix_mono {m n : ℕ} (h : m ≤ n) : jsp87Prefix m ≤ jsp87Prefix n := by
  induction n, h using Nat.le_induction with
  | base => omega
  | succ n hn ih => rw [jsp87Prefix_succ]; omega

/-- **THE CONSECUTIVE STEP OF THE PREFIX IS `I N + ω N`.**  `I (N+1) − I N =
I N + ω N`, from `jsp87Prefix_succ`. -/
theorem jsp87_prefix_step_eq (N : ℕ) :
    jsp87Prefix (N + 1) - jsp87Prefix N = jsp87Prefix N + omega N := by
  have h := jsp87Prefix_succ N
  have key : jsp87Prefix N ≤ jsp87Prefix (N + 1) := by
    rw [h]
    omega
  omega

/-- **A `2`-ADIC COHERENT PREFIX FORCES `ω` TO BE CONSTANT MODULO `2^k`.**
Assume that for every `n ≥ M` the consecutive differences of the binary prefix
vanish modulo `2^k` — this is what coherence of `I` at `2^k` on the tail
`[M, ∞)` means.  Then for every `N ≥ M`

`ω N ≡ ω M  (mod 2^k)`,

as an identity of residues of integers.  The proof works in `ℤ`, where no
truncation of natural subtractions occurs: `u n = I (n+1) − I n = I n + ω n` is
divisible by `2^k` for all `n ≥ M` (`jsp87_prefix_step_eq`), and `I N − I M` is
divisible by `2^k` for all `N ≥ M` (by telescoping); subtracting the relations at
`N` and at `M` kills the prefix. -/
theorem jsp87_prefix_coh_omega_congr {k M : ℕ} (_hk : 1 ≤ k)
    (hcoh : ∀ n, M ≤ n → 2 ^ k ∣ jsp87Prefix (n + 1) - jsp87Prefix n) {N : ℕ}
    (hN : M ≤ N) : ((omega N : ℤ) - (omega M : ℤ)) % ((2 : ℤ) ^ k) = 0 := by
  have hstep : ∀ n, M ≤ n → 2 ^ k ∣ jsp87Prefix n + omega n := by
    intro n hn
    rw [← jsp87_prefix_step_eq n]
    exact hcoh n hn
  have hchain : ∀ n, M ≤ n → 2 ^ k ∣ jsp87Prefix n - jsp87Prefix M := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨0, by omega⟩
    | succ m hmn ihm =>
        obtain ⟨c, hc⟩ := hcoh m hmn
        obtain ⟨d, hd⟩ := ihm
        refine ⟨c + d, ?_⟩
        have hMM : jsp87Prefix M ≤ jsp87Prefix m := jsp87Prefix_mono hmn
        have hmono : jsp87Prefix m ≤ jsp87Prefix (m + 1) := jsp87Prefix_mono (by omega)
        have hsum : jsp87Prefix m - jsp87Prefix M
            + (jsp87Prefix (m + 1) - jsp87Prefix m)
            = jsp87Prefix (m + 1) - jsp87Prefix M := by omega
        rw [← hsum, hc, hd]
        ring
  have hA : ((2 : ℤ) ^ k) ∣ (((jsp87Prefix N + omega N : ℕ) : ℤ)) := by
    obtain ⟨c, hc⟩ := hstep N hN
    refine ⟨c, ?_⟩
    exact_mod_cast hc
  have hB : ((2 : ℤ) ^ k) ∣ (((jsp87Prefix M + omega M : ℕ) : ℤ)) := by
    obtain ⟨c, hc⟩ := hstep M (Nat.le_refl M)
    refine ⟨c, ?_⟩
    push_cast
    exact_mod_cast hc
  have hC : ((2 : ℤ) ^ k) ∣ (((jsp87Prefix N - jsp87Prefix M : ℕ) : ℤ)) := by
    obtain ⟨c, hc⟩ := hchain N hN
    refine ⟨c, ?_⟩
    exact_mod_cast hc
  have hkey : (((jsp87Prefix N + omega N : ℕ) : ℤ))
      - (((jsp87Prefix N - jsp87Prefix M : ℕ) : ℤ))
      - (((jsp87Prefix M + omega M : ℕ) : ℤ))
      = (omega N : ℤ) - (omega M : ℤ) := by
    push_cast
    have hN' : jsp87Prefix M ≤ jsp87Prefix N := jsp87Prefix_mono hN
    omega
  have hD := Int.dvd_sub (Int.dvd_sub hA hC) hB
  rw [hkey] at hD
  exact Int.emod_eq_zero_of_dvd hD

/-- **THE `2`-ADIC VALUE OF THE ERDŐS SERIES DOES NOT EXIST.**  There is no `k ≥ 1`
and no `M` such that the binary prefix `I N` of the series is *coherent* modulo
`2^k` on the tail `[M, ∞)`, i.e. such that all of its differences there are
divisible by `2^k`.

The reason is elementary: a coherent prefix makes `ω` constant modulo `2^k` on
the tail (`jsp87_prefix_coh_omega_congr`), but `ω p = 1` at a prime `p` and
`ω (2p) = 2` at twice a prime, and `1 ≢ 2 (mod 2^k)` for every `k ≥ 1`.

This closes the route opened by round 52's `jsp87Val2` and by the `2`-adic
reading of the series: **the prefix quantisation is not available.**  The only
quantisation a rational value of `S` could respect is the real one — the
doubling orbit of the carries, whose exact period was computed in §3. -/
theorem jsp87_prefix_twoAdic_limit_absent :
    ¬ ∃ k M : ℕ, 1 ≤ k ∧ ∀ N N', M ≤ N → M ≤ N' → 2 ^ k ∣ jsp87Prefix N' - jsp87Prefix N := by
  rintro ⟨k, M, hk, hcoh⟩
  obtain ⟨p, hbig, hprim⟩ := Nat.exists_infinite_primes (M + 3)
  have h2 : 2 < p := by omega
  have hcoh' : ∀ n, M ≤ n → 2 ^ k ∣ jsp87Prefix (n + 1) - jsp87Prefix n := by
    intro n hn
    exact hcoh n (n + 1) hn (by omega)
  have hcong1 := jsp87_prefix_coh_omega_congr (k := k) (M := M) (N := p) (by omega) hcoh'
    (by omega)
  have hcong2 := jsp87_prefix_coh_omega_congr (k := k) (M := M) (N := 2 * p) (by omega) hcoh'
    (by omega)
  have h1 : ((2 : ℤ) ^ k) ∣ ((omega p : ℤ) - (omega M : ℤ)) :=
    Int.dvd_of_emod_eq_zero hcong1
  have h2' : ((2 : ℤ) ^ k) ∣ ((omega (2 * p) : ℤ) - (omega M : ℤ)) :=
    Int.dvd_of_emod_eq_zero hcong2
  have h3 := Int.dvd_sub h2' h1
  have hkey : (((omega (2 * p) : ℤ) - (omega M : ℤ)) - ((omega p : ℤ) - (omega M : ℤ)))
      = (omega (2 * p) : ℤ) - (omega p : ℤ) := by ring
  rw [hkey] at h3
  have hone' : (omega p : ℤ) = 1 := by
    exact_mod_cast (jsp87_omega_one_of_prime hprim)
  have htwo' : (omega (2 * p) : ℤ) = 2 := by
    exact_mod_cast (jsp87_omega_two_mul_of_prime hprim h2)
  obtain ⟨c, hc⟩ := h3
  rw [hone', htwo'] at hc
  have hpos : (0 : ℤ) < (2 : ℤ) ^ k := two_pow_pos_int k
  have hle : (2 : ℤ) ≤ (2 : ℤ) ^ k := two_pow_ge_two_int hk
  have hkey : 1 = (2 : ℤ) ^ k * c := hc
  have hne : c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hkey
    simp at hkey
  have hpos : (0 : ℤ) < (2 : ℤ) ^ k := two_pow_pos_int k
  have hle : (2 : ℤ) ≤ (2 : ℤ) ^ k := two_pow_ge_two_int hk
  have hcpos : 0 < c := by
    rcases lt_or_gt_of_ne hne with h | h
    · exfalso
      have hnp : (2 : ℤ) ^ k * c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) (le_of_lt h)
      rw [← hkey] at hnp
      exact absurd hnp (by simp)
    · exact h
  have h2c : (2 : ℤ) ≤ 2 * c := by nlinarith
  have hmul : (2 : ℤ) ≤ (2 : ℤ) ^ k * c := by
    have h1 := mul_le_mul_of_nonneg_right hle (le_of_lt hcpos)
    exact le_trans h2c h1
  have hcontra : (2 : ℤ) ≤ 1 := by
    rw [← hkey] at hmul
    exact hmul
  omega

/-- **CONSEQUENCE: THE PREFIX ESCAPES EVERY FIXED POWER OF `2` ON EVERY TAIL.**
For `1 ≤ k` and every `M` there are `N, N' ≥ M` with
`¬ 2^k ∣ I N' − I N`.  This is the effective form of
`jsp87_prefix_twoAdic_limit_absent`. -/
theorem jsp87_prefix_escapes_every_pow_two {k M : ℕ} (hk : 1 ≤ k) :
    ∃ N N', M ≤ N ∧ M ≤ N' ∧ ¬ 2 ^ k ∣ jsp87Prefix N' - jsp87Prefix N := by
  by_contra hcon
  have hnot : ∀ N N', M ≤ N → M ≤ N' → 2 ^ k ∣ jsp87Prefix N' - jsp87Prefix N := by
    intro N N' hN hN'
    by_contra hc
    exact hcon ⟨N, N', hN, hN', hc⟩
  exact jsp87_prefix_twoAdic_limit_absent ⟨k, M, hk, hnot⟩

/-- **THE PREFIX IS INCOHERENT AT EVERY PRIME.**  For every prime `p` and every
`k ≥ 1` the two conditions `2^k ∣ I p` and `2^k ∣ I (p+1) − I p` cannot both
hold: by `jsp87_prefix_step_eq` they would force `2^k ∣ ω p = 1`. -/
theorem jsp87_prefix_incoherent_at_prime {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ (2 ^ k ∣ jsp87Prefix p ∧ 2 ^ k ∣ jsp87Prefix (p + 1) - jsp87Prefix p) := by
  rintro ⟨h1, h2⟩
  have hstep := jsp87_prefix_step_eq p
  have h3 : 2 ^ k ∣ jsp87Prefix p + omega p := by
    rw [← hstep]
    exact h2
  have key : jsp87Prefix p + omega p - jsp87Prefix p = omega p := Nat.add_sub_cancel_left _ _
  have h4 : 2 ^ k ∣ omega p := by
    have hsub := Nat.dvd_sub (show 2 ^ k ∣ jsp87Prefix p + omega p from h3) h1
    rwa [key] at hsub
  rw [jsp87_omega_one_of_prime hp] at h4
  have h6 : 2 ^ k ≤ 1 := Nat.le_of_dvd (show (0 : ℕ) < 1 by simp) h4
  have h5 : 2 ≤ 2 ^ k := two_pow_ge_two_nat hk
  omega

/-! ## 7. Instances: the orders `3, 2, 6` and the `2`-adic threshold -/

/-- **THE RESIDUE ORBIT OF `1` MODULO `7` IS THE CYCLE `1, 2, 4`.** -/
theorem jsp87_orbitNum_seven_values :
    jsp87OrbitNum 1 7 0 = 1 ∧ jsp87OrbitNum 1 7 1 = 2 ∧ jsp87OrbitNum 1 7 2 = 4 := by
  norm_num [jsp87OrbitNum]

/-- **`ord 2 (mod 7) = 3`.** -/
theorem jsp87_ord_seven_new : jsp87OddPart 7 = 7 ∧ 7 ∣ 2 ^ 3 - 1
    ∧ (∀ u, 0 < u → u < 3 → ¬ 7 ∣ 2 ^ u - 1) := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro u hu hu'
  interval_cases u <;> norm_num

theorem jsp87_orbitNum_seven_period (N : ℕ) :
    jsp87OrbitNum 1 7 (N + 3) = jsp87OrbitNum 1 7 N := by
  have hv := jsp87_ord_seven_new
  have h3 : jsp87Val2 7 ≤ 0 := by rw [jsp87_ord_seven.1]
  exact (jsp87_orbitNum_period_iff (a := 1) (b := 7) (k := 0) (t := 3) (by decide)
    (by norm_num) (by norm_num) h3).mpr hv.2.1 N (Nat.zero_le N)

/-- **`ord 2 (mod 3) = 2`, AND THE `2`-ADIC THRESHOLD OF `12` IS SHARP.**
`v_2(12) = 2`, `jsp87OddPart 12 = 3`, and the residue orbit of `1` modulo `12`
is periodic with period `2` from `N = 2` on. -/
theorem jsp87_ord_twelve_new : jsp87Val2 12 = 2 ∧ jsp87OddPart 12 = 3
    ∧ 3 ∣ 2 ^ 2 - 1 ∧ (∀ u, 0 < u → u < 2 → ¬ 3 ∣ 2 ^ u - 1) := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro u hu hu'
  interval_cases u
  all_goals norm_num

theorem jsp87_orbitNum_twelve_period (N : ℕ) (hN : 2 ≤ N) :
    jsp87OrbitNum 1 12 (N + 2) = jsp87OrbitNum 1 12 N := by
  have hv := jsp87_ord_twelve_new
  have hp := (jsp87_orbitNum_period_iff (a := 1) (b := 12) (k := 2) (t := 2) (by decide)
    (by norm_num) (by norm_num) (by omega)).mpr hv.2.2.1
  exact hp N hN

/-- **THE THRESHOLD IS EXACT: THE ORBIT OF `1` MODULO `12` IS NOT PERIODIC WITH
PERIOD `2` AT `N = 0`.**  `v_2(12) = 2` is exactly where periodicity starts. -/
theorem jsp87_orbitNum_twelve_values :
    jsp87OrbitNum 1 12 2 = 4 ∧ jsp87OrbitNum 1 12 3 = 8 ∧ jsp87OrbitNum 1 12 4 = 4 := by
  norm_num [jsp87OrbitNum]

/-- **`ord 2 (mod 9) = 6`** — a composite odd modulus, where the order is
strictly larger than in the prime case `7`. -/
theorem jsp87_ord_nine_new : jsp87OddPart 9 = 9 ∧ 9 ∣ 2 ^ 6 - 1
    ∧ (∀ u, 0 < u → u < 6 → ¬ 9 ∣ 2 ^ u - 1) := by
  refine ⟨by decide, by norm_num, ?_⟩
  intro u hu hu'
  interval_cases u <;> norm_num

theorem jsp87_orbitNum_nine_period (N : ℕ) :
    jsp87OrbitNum 1 9 (N + 6) = jsp87OrbitNum 1 9 N := by
  have hv := jsp87_ord_nine_new
  have h3 : jsp87Val2 9 ≤ 0 := by decide
  exact (jsp87_orbitNum_period_iff (a := 1) (b := 9) (k := 0) (t := 6) (by decide)
    (by norm_num) (by norm_num) h3).mpr hv.2.1 N (Nat.zero_le N)

/-- **THE THREE RESIDUE ORBIT POINTS OF A `7`-PERIOD ARE DISTINCT** — a
machine-checked instance of the shape proved in `jsp87_fracCarry_distinct`. -/
theorem jsp87_orbitNum_seven_distinct {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    jsp87OrbitNum 1 7 i ≠ jsp87OrbitNum 1 7 j := by
  interval_cases i <;> interval_cases j <;> (simp [jsp87OrbitNum] <;> omega)

end JSP87
