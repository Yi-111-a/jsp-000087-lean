/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-111-a).
-/
import JSPProblem.CarryAsymptotic
import JSPProblem.CarryDoubling

/-!
# JSP-000087 : the period equation, and the `ω`-window arithmetic

Rounds 37–46 attacked the *carried* Erdős series `S = ∑' n, ω(n) 2^{-(n+1)}`
through ten *periodicity* angles; round 47 the *carry-free* (primary)
expansion; round 48 the *doubling map* on the carries; round 49 the criterion
in *arbitrary radix* (and closed the radix route by
`jsp87_noCarry_fails_any_radix`); round 50 the *asymptotic* behaviour of the
carry and of the binary digit string.

**This round attacks neither the period `t` itself nor the digit string.**  It
attacks the *homogeneous part* of the carry recurrence, i.e. the object that all
the previous rounds wrote down but never manipulated:

> the `t`-step form of round 40's `θ (N+1) = 2 θ N − ω N` has an inhomogeneous
> term which is a **window of `ω`-values read in base `2`**,
> `θ (N+t) = 2^t · θ N − Ω N t`,  `Ω N t = ∑_{j<t} ω (N+j) · 2^{t-1-j}`.

The `ω`-window `Ω N t` had **never been defined in the tree**.  It is the
natural "local content" of the carry at lag `t`, and it is the object that a
prime-`k`-tuples correlation hypothesis is supposed to control (it is a weighted
average of the `ω`-values of `t` consecutive integers).

## Main results

| Theorem | Statement |
| --- | --- |
| `jsp87OmegaWindow`, `jsp87OmegaWindow_succ` | **the new object** `Ω N t = ∑_{j<t} ω (N+j) 2^{t-1-j}`, and its step relation `Ω N (t+1) = 2 Ω N t + ω (N+t)` |
| `jsp87OmegaWindow_ge` | **`2^t − 1 ≤ Ω N t` for `2 ≤ N`**: the window is exponentially large, because every `ω (N+j) ≥ 1` |
| `jsp87Carry_iter` | **THE ITERATED CARRY RECURRENCE `θ (N+t) = 2^t θ N − Ω N t`** — the `t`-step form of round 40, with the `ω`-window as the inhomogeneity |
| `jsp87CarryShift`, `jsp87OmegaDiff` | the lag-`t` carry increment `θ (N+t) − θ N`, and the lag-`t` `ω`-difference |
| `jsp87CarryShift_step` | **THE PERIOD EQUATION, STEP FORM (unconditional): `ω (N+t) − ω N = 2 Δ N − Δ (N+1)`** — the `ω`-family is *contained in* the carry family |
| `jsp87CarryShift_block` | the block form `Δ (N+t) = 2^t Δ N − P N t` with the `ω`-difference window as inhomogeneity |
| `jsp87CarryShift_eq_excess` | **under eventual periodicity of the digits, the lag-`t` carry increment is the lag-`t` *carry-excess* increment** — an exact `ℤ` identity |
| `jsp87_window_periodEquation` | **THE WINDOW EQUATION: `(2^t−1) θ N = (c (N+t) − c N) + Ω N t`** under eventual periodicity |
| **`jsp87_omegaWindow_dvd`** | **THE WINDOW DIVISIBILITY OBSTRUCTION: `2^t − 1 ∣ c (N+t) − c N + Ω N t`** — the first *divisibility* statement in the carry family, and a Mersenne number now divides a quantity built from `ω` |
| `jsp87_omega_diff_periodEquation` | **THE PERIOD EQUATION: the lag-`t` `ω`-difference is the *second difference* of the carry excess** |
| `jsp87Series_rational_imp_omega_diff_periodEquation` | what a rational value of `S` forces, stated on the `ω`-family |
| `jsp87_omega_diff_periodEquation_bound` | under eventual periodicity the lag-`t` `ω`-difference is bounded by `6 · log₂(N+t+1)` |
| `jsp87_dyadic_iff_carryInt` | **THE DYADIC CROSS-IDENTIFICATION: `S = n/2^M` iff *some carry is an integer*** |
| `jsp87_carryInt_iff_digitZero` | hence: the binary digits of `S` are eventually `0` **iff some carry is an integer** |
| `jsp87_carry_int_ge_two` | under the dyadic hypothesis the carry excess is at least `2` at every cut point (unconditionally: at least `1`) |
| `jsp87_dyadic_omega_eq` | **under the dyadic hypothesis `ω N = 2 c N − c (N+1)`**: the whole `ω`-family is a doubling-difference of the carry excess |
| `jsp87_dyadic_omega_bounds` | the quantitative squeeze `2 c N − log₂(N+1) ≤ ω N ≤ 2 c N − 2` |
| `jsp87Series_irrational_of_omegaWindow_never_dvd` | **THE FIFTH IRRATIONALITY CRITERION, in terms of the `ω`-window divisibility test** |

## Why this still does not close JSP-000087

The window divisibility says the hypothetical rational value would have to pass
a *congruence test in the Mersenne number `2^t − 1`* at **every** cut point
`N ≥ M`, with the residue `−Ω N t`.  Nothing unconditional is known about the
distribution of `Ω N t` modulo `2^t − 1`; that is the arithmetic content of the
prime-`k`-tuples hypothesis in Pratt's result, and it is an *assumption of the
published result*, not of the catalog statement.
-/

namespace JSP87

/-! ## 0. The `ω`-window -/

/-- **The `ω`-window at `N`, of length `t`, read in base `2`:**
`Ω N t = ∑_{j < t} ω (N+j) · 2^{t-1-j}`.

This is the inhomogeneous term of the `t`-step carry recurrence
(`jsp87Carry_iter`): a weighted average of the `ω`-values of the `t` integers
`N, N+1, …, N+t−1`, in decreasing powers of `2`.  It is the object a correlation
hypothesis on `ω` at *shifted* integers would have to control. -/
def jsp87OmegaWindow (N t : ℕ) : ℕ := ∑ j ∈ Finset.range t, omega (N + j) * 2 ^ (t - 1 - j)

/-- The empty window vanishes. -/
theorem jsp87OmegaWindow_zero (N : ℕ) : jsp87OmegaWindow N 0 = 0 := by
  simp [jsp87OmegaWindow]

/-- The window of length `1` is the `ω`-value at its base point. -/
theorem jsp87OmegaWindow_one (N : ℕ) : jsp87OmegaWindow N 1 = omega N := by
  have h : jsp87OmegaWindow N 1 = ∑ j ∈ Finset.range 1, omega (N + j) * 2 ^ (1 - 1 - j) := rfl
  rw [Finset.sum_range_succ, Finset.sum_range_zero, add_zero] at h
  norm_num at h
  exact h

/-- The window, read in `ℝ`. -/
theorem jsp87OmegaWindow_cast (N t : ℕ) :
    (jsp87OmegaWindow N t : ℝ)
      = ∑ j ∈ Finset.range t, ((omega (N + j) : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ (t - 1 - j) := by
  simp only [jsp87OmegaWindow, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- **THE WINDOW STEP: `Ω N (t+1) = 2 · Ω N t + ω (N+t)`.**  A new window is the
old one, doubled, with the `ω`-value at the new endpoint appended. -/
theorem jsp87OmegaWindow_succ (N t : ℕ) :
    jsp87OmegaWindow N (t + 1) = 2 * jsp87OmegaWindow N t + omega (N + t) := by
  unfold jsp87OmegaWindow
  have hkey : ∀ j ∈ Finset.range (t + 1),
      omega (N + j) * 2 ^ (t + 1 - 1 - j) = omega (N + j) * 2 ^ (t - j) := by
    intro j _
    have he : t + 1 - 1 - j = t - j := by omega
    rw [he]
  have hstep : ∀ j ∈ Finset.range t,
      omega (N + j) * 2 ^ (t - j) = 2 * (omega (N + j) * 2 ^ (t - 1 - j)) := by
    intro j hj
    have hj' : j < t := Finset.mem_range.mp hj
    have hkey : t - j = (t - 1 - j) + 1 := by omega
    rw [hkey, pow_succ]
    ring
  rw [Finset.sum_congr rfl hkey, Finset.sum_range_succ, Finset.mul_sum,
    Finset.sum_congr rfl hstep, Nat.sub_self, pow_zero, mul_one]

private theorem one_le_two_pow_nat (m : ℕ) : 1 ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

/-- **The all-ones window, in `ℕ`:** `∑_{j<t} 2^{t-1-j} = 2^t − 1`.  This is
`CarryExcess.sum_two_pow_desc` re-proved over `ℕ` (that lemma is stated in `ℝ`,
and here the sums live in `ℕ`). -/
private theorem sum_pow_desc_nat (t : ℕ) (ht : 0 < t) :
    (∑ j ∈ Finset.range t, (2 : ℕ) ^ (t - 1 - j)) = 2 ^ t - 1 := by
  have hmain : ∀ m : ℕ, (∑ j ∈ Finset.range (m + 1), (2 : ℕ) ^ (m - j)) = 2 ^ (m + 1) - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hone : 1 ≤ 2 ^ m := one_le_two_pow_nat m
        have hsplit : (∑ j ∈ Finset.range (m + 1 + 1), (2 : ℕ) ^ (m + 1 - j))
            = 1 + ∑ j ∈ Finset.range (m + 1), (2 : ℕ) ^ (m + 1 - j) := by
          rw [Finset.sum_range_succ]
          have h1 : m + 1 - (m + 1) = 0 := by omega
          rw [h1]
          norm_num
          ring
        have hscale : (∑ j ∈ Finset.range (m + 1), (2 : ℕ) ^ (m + 1 - j))
            = 2 * (∑ j ∈ Finset.range (m + 1), (2 : ℕ) ^ (m - j)) := by
          rw [Finset.mul_sum]
          have hkey : ∀ j ∈ Finset.range (m + 1),
              (2 : ℕ) ^ (m + 1 - j) = 2 * (2 : ℕ) ^ (m - j) := by
            intro j hj
            have hj' : j ≤ m := by have hj'' := Finset.mem_range.mp hj; omega
            have h1 : m + 1 - j = (m - j) + 1 := Nat.succ_sub hj'
            rw [h1, pow_succ]
            ring
          exact Finset.sum_congr rfl hkey
        have e1 : (2 : ℕ) ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by
          rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_add]
          norm_num
        rw [hsplit, hscale, ih, e1]
        omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hkey : ∀ j ∈ Finset.range m.succ,
      (2 : ℕ) ^ (m.succ - 1 - j) = 2 ^ (m - j) := by
    intro j hj
    have hj' : j < m.succ := Finset.mem_range.mp hj
    congr 1
  rw [hm]
  rw [Finset.sum_congr rfl hkey]
  exact hmain m

/-- **THE WINDOW IS EXPONENTIALLY LARGE: `2^t − 1 ≤ Ω N t` for `2 ≤ N`.**

Every integer at or above `2` has at least one prime factor
(`omega_ge_one_of_ge_two`), so the window dominates the all-ones window
`∑_{j<t} 2^{t-1-j} = 2^t − 1`.  Together with `jsp87OmegaWindow_le` this pins
the `ω`-window between a Mersenne number and a linear function of `N`. -/
theorem jsp87OmegaWindow_ge {N t : ℕ} (hN : 2 ≤ N) : 2 ^ t - 1 ≤ jsp87OmegaWindow N t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · omega
  · have key : ∀ j ∈ Finset.range t,
        2 ^ (t - 1 - j) ≤ omega (N + j) * 2 ^ (t - 1 - j) := by
      intro j _
      have h1 : 1 ≤ omega (N + j) := omega_ge_one_of_ge_two (by omega)
      have h2 : (0 : ℕ) ≤ 2 ^ (t - 1 - j) := by positivity
      simpa using mul_le_mul_of_nonneg_right h1 h2
    unfold jsp87OmegaWindow
    calc (∑ j ∈ Finset.range t, omega (N + j) * 2 ^ (t - 1 - j))
        ≥ ∑ j ∈ Finset.range t, 2 ^ (t - 1 - j) := Finset.sum_le_sum key
      _ = 2 ^ t - 1 := sum_pow_desc_nat t ht

/-- The window is at most `(N+t) · (2^t − 1)`, using `ω m ≤ m − 1`. -/
theorem jsp87OmegaWindow_le {N t : ℕ} : jsp87OmegaWindow N t ≤ (N + t) * (2 ^ t - 1) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [jsp87OmegaWindow]
  · have key : ∀ j ∈ Finset.range t,
        omega (N + j) * 2 ^ (t - 1 - j) ≤ ((N + t : ℕ) : ℕ) * 2 ^ (t - 1 - j) := by
      intro j hjmem
      have hjlt : j < t := Finset.mem_range.mp hjmem
      have hj3 : omega (N + j) ≤ N + t := by
        rcases Nat.eq_zero_or_pos (N + j) with h | hpos
        · rw [h]; simp [omega]
        · have hj2 : omega (N + j) ≤ N + j - 1 := omega_lt hpos
          omega
      have h2 : (0 : ℕ) ≤ 2 ^ (t - 1 - j) := by positivity
      simpa using mul_le_mul_of_nonneg_right hj3 h2
    unfold jsp87OmegaWindow
    calc (∑ j ∈ Finset.range t, omega (N + j) * 2 ^ (t - 1 - j))
        ≤ ∑ j ∈ Finset.range t, ((N + t : ℕ) : ℕ) * 2 ^ (t - 1 - j) := Finset.sum_le_sum key
      _ = ((N + t : ℕ) : ℕ) * (2 ^ t - 1) := by
          rw [← Finset.mul_sum, sum_pow_desc_nat t ht]

/-- **The iterated carry recurrence: the window reads off the `ω`-content of the
carry over `t` steps.** -/
theorem jsp87OmegaWindow_succ_cast (N t : ℕ) :
    (jsp87OmegaWindow N (t + 1) : ℝ)
      = 2 * (jsp87OmegaWindow N t : ℝ) + (omega (N + t) : ℝ) := by
  rw [jsp87OmegaWindow_succ]
  norm_cast

/-- **THE ITERATED CARRY RECURRENCE.**  For every `N` and `t`,

`θ (N+t) = 2^t · θ N − Ω N t`.

This is the `t`-step form of round 40's `jsp87Carry_succ`, with the `ω`-window
as the inhomogeneous term; it is the analogue of round 47's
`jsp87BinaryTail_iter` for the *carried* series. -/
theorem jsp87Carry_iter (N t : ℕ) :
    jsp87Carry (N + t) = 2 ^ t * jsp87Carry N - (jsp87OmegaWindow N t : ℝ) := by
  induction t with
  | zero =>
      have hw : jsp87OmegaWindow N 0 = 0 := jsp87OmegaWindow_zero N
      rw [hw]
      simp [jsp87Carry]
  | succ t ih =>
      have h2 := jsp87Carry_succ (N + t)
      have hN : (N + t) + 1 = N + (t + 1) := by omega
      rw [hN] at h2
      have hw := jsp87OmegaWindow_succ_cast N t
      have hsucc : (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := (pow_succ (2 : ℝ) t).trans (by ring)
      rw [h2, hsucc, hw, ih]
      ring

/-- The carry increment along the period is `(2^t−1) θ N − Ω N t`. -/
theorem jsp87Carry_iter_sub (N t : ℕ) :
    jsp87Carry (N + t) - jsp87Carry N
      = ((2 : ℝ) ^ t - 1) * jsp87Carry N - (jsp87OmegaWindow N t : ℝ) := by
  have h := jsp87Carry_iter N t
  linarith

/-! ## 2. The period equation, step form: the `ω`-family lives in the carry family -/

/-- The lag-`t` **increment of the carry**: `Δ N := θ (N+t) − θ N`. -/
noncomputable def jsp87CarryShift (N t : ℕ) : ℝ := jsp87Carry (N + t) - jsp87Carry N

/-- The lag-`t` **difference of `ω`**: `ω (N+t) − ω N`. -/
def jsp87OmegaDiff (N t : ℕ) : ℤ := (omega (N + t) : ℤ) - (omega N : ℤ)

/-- The `ω`-difference, read in `ℝ`. -/
theorem jsp87OmegaDiff_cast (N t : ℕ) :
    ((jsp87OmegaDiff N t : ℤ) : ℝ) = (omega (N + t) : ℝ) - (omega N : ℝ) := by
  simp only [jsp87OmegaDiff, Int.cast_sub, Int.cast_natCast]

/-- **THE PERIOD EQUATION, STEP FORM — and it is UNCONDITIONAL.**

`Δ (N+1) = 2 Δ N − (ω (N+t) − ω N)`, i.e.

`ω (N+t) − ω N = 2 Δ N − Δ (N+1)`.

So the entire `ω`-family, at *every* lag `t`, is recovered from the carry
family: no hypothesis on `ω` is needed, and in particular a rational value of `S`
would not change this.  This is the first statement in the tree that puts the
`ω`-family and the carry family in a two-way equation. -/
theorem jsp87CarryShift_step (N t : ℕ) :
    jsp87CarryShift (N + 1) t
      = 2 * jsp87CarryShift N t - ((jsp87OmegaDiff N t : ℤ) : ℝ) := by
  have h1 := jsp87Carry_succ (N + t)
  have h2 := jsp87Carry_succ N
  have hs : (N + 1) + t = (N + t) + 1 := by omega
  simp only [jsp87CarryShift, hs]
  rw [h1, h2, jsp87OmegaDiff_cast]
  ring

/-- **The unconditional bridge, in `ℝ`:** the lag-`t` `ω`-difference is the second
difference of the lag-`t` carry increments. -/
theorem jsp87_omega_diff_eq_carryShift (N t : ℕ) :
    ((jsp87OmegaDiff N t : ℤ) : ℝ)
      = 2 * jsp87CarryShift N t - jsp87CarryShift (N + 1) t := by
  rw [jsp87CarryShift_step]
  ring

/-- **The `ω`-difference window:** the inhomogeneous term of the block equation
for the carry increments. -/
noncomputable def jsp87OmegaDiffWindow (N t : ℕ) : ℝ :=
  (jsp87OmegaWindow (N + t) t : ℝ) - (jsp87OmegaWindow N t : ℝ)

/-- **THE PERIOD EQUATION, BLOCK FORM.**  Iterating the step form `t` times,
with `jsp87Carry_iter` applied at `N + t` and at `N`:

`Δ (N+t) = 2^t · Δ N − P N t`,  `P N t := Ω (N+t) t − Ω N t`.

So the block-`t` increment of the carry is a **doubling map driven by the
`ω`-difference window**. -/
theorem jsp87CarryShift_block (N t : ℕ) :
    jsp87CarryShift (N + t) t = 2 ^ t * jsp87CarryShift N t - jsp87OmegaDiffWindow N t := by
  have h1 := jsp87Carry_iter (N + t) t
  have h2 := jsp87Carry_iter N t
  have hs : N + 2 * t = (N + t) + t := by omega
  simp only [jsp87CarryShift, jsp87OmegaDiffWindow]
  rw [h1, h2]
  ring

/-! ## 3. Eventual periodicity of the digits freezes the increments -/

private theorem two_pow_sub_one_cast' (k : ℕ) :
    (((2 : ℤ) ^ k - 1 : ℤ) : ℝ) = (2 : ℝ) ^ k - 1 := by
  push_cast
  ring

private theorem two_pow_sub_one_pos' {j : ℕ} (hj : 0 < j) : 0 < (2 : ℝ) ^ j - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have h : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h2 : (1 : ℝ) ≤ 2 ^ m := by exact_mod_cast one_le_two_pow_nat m
  rw [h]
  nlinarith

private theorem digitBlock_le_int (N t : ℕ) :
    (jsp87DigitBlock N t : ℤ) ≤ 2 ^ t - 1 := by
  have h := (jsp87_digitBlock_bounds N t).2
  omega

private theorem digitBlock_le_real (N t : ℕ) :
    (jsp87DigitBlock N t : ℝ) ≤ 2 ^ t - 1 := by
  exact_mod_cast digitBlock_le_int N t

/-- **THE LAG-`t` CARRY INCREMENT IS THE LAG-`t` CARRY-EXCESS INCREMENT.**

If the binary digits of `S` are eventually periodic from `M` with period `t > 0`
(`1 ≤ M`) then for every `N ≥ M`

`θ (N+t) − θ N = c (N+t) − c N`,

i.e. advancing the carry by the period changes it by an **integer**: the
fractional part of the carry is period-`t`-periodic (round 48), so the whole
period-increment of the carry lives in `ℤ`, and that integer is exactly the
increment of the carry excess `c N = ⌊θ N⌋`. -/
theorem jsp87CarryShift_eq_excess {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    jsp87CarryShift N t
      = ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ) := by
  have hfr := jsp87_fracCarry_periodic_of_digitPeriodic ht hM hN hper
  have hs1 : jsp87Carry (N + t) = (⌊jsp87Carry (N + t)⌋ : ℝ) + Int.fract (jsp87Carry (N + t)) := by
    exact (Int.floor_add_fract _).symm
  have hs0 : jsp87Carry N = (⌊jsp87Carry N⌋ : ℝ) + Int.fract (jsp87Carry N) := by
    exact (Int.floor_add_fract _).symm
  have h1 := congrArg (fun z : ℝ => z - jsp87Carry N) hs1
  have h2 := congrArg (fun z : ℝ => jsp87Carry (N + t) - z) hs0
  rw [hfr] at h1
  have hkey : jsp87Carry (N + t) - jsp87Carry N
      = (⌊jsp87Carry (N + t)⌋ - ⌊jsp87Carry N⌋ : ℝ) := by
    linarith
  simp only [jsp87CarryShift, jsp87CarryExcess, Int.cast_sub]
  exact hkey

/-- **The lag-`t` carry increment is an INTEGER** under eventual periodicity of
the digits: the period alone turns the whole carry-increment arithmetic into
`ℤ`-arithmetic. -/
theorem jsp87CarryShift_int {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ∃ k : ℤ, jsp87CarryShift N t = (k : ℝ) := by
  refine ⟨jsp87CarryExcess (N + t) - jsp87CarryExcess N, ?_⟩
  rw [jsp87CarryShift_eq_excess ht hM hN hper]

/-! ## 4. The window equation and the window–block equation -/

/-- **THE WINDOW EQUATION.**  If the digits are eventually periodic from `M` with
period `t > 0`, then for every `N ≥ M`

`(2^t − 1) · θ N = (c (N+t) − c N) + Ω N t`.

Equivalently: the Mersenne number `2^t − 1`, the carry at `N`, the increment of
the carry excess along the period, and the `ω`-window at `N` satisfy one exact
equation.  (Left-hand side: `θ (N+t) − θ N` by `jsp87Carry_iter`; right-hand
side: the same quantity by `jsp87CarryShift_eq_excess`.) -/
theorem jsp87_window_periodEquation {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ((2 : ℝ) ^ t - 1) * jsp87Carry N
      = ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ) + (jsp87OmegaWindow N t : ℝ) := by
  have hiter := jsp87Carry_iter N t
  have hdiff : jsp87Carry (N + t) - jsp87Carry N
      = ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ) :=
    jsp87CarryShift_eq_excess ht hM hN hper
  linarith

/-- **THE QUANTISATION BY THE PERIOD, IN BLOCK FORM.**  Under the hypotheses of
`jsp87_window_periodEquation`,

`(2^t − 1) · θ N = (2^t − 1) · c N + B N t`,

where `B N t = jsp87DigitBlock N t` is the `t`-digit block.  (This is round 48's
`jsp87_fracCarry_eq_block_of_digitPeriodic` multiplied through by `2^t − 1`.) -/
theorem jsp87_carry_block_equation {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ((2 : ℝ) ^ t - 1) * jsp87Carry N
      = ((2 : ℝ) ^ t - 1) * (jsp87CarryExcess N : ℝ) + (jsp87DigitBlock N t : ℝ) := by
  have hfr := jsp87_fracCarry_eq_block_of_digitPeriodic ht hM hN hper
  have hA0 : (0 : ℝ) < (2 : ℝ) ^ t - 1 := two_pow_sub_one_pos' ht
  have hmul : ((2 : ℝ) ^ t - 1) * Int.fract (jsp87Carry N) = (jsp87DigitBlock N t : ℝ) := by
    rw [hfr]
    exact mul_div_cancel₀ _ (ne_of_gt hA0)
  have hsplit : jsp87Carry N = (⌊jsp87Carry N⌋ : ℝ) + Int.fract (jsp87Carry N) :=
    (Int.floor_add_fract _).symm
  have h1 := congrArg (fun z : ℝ => ((2 : ℝ) ^ t - 1) * z) hsplit
  have h1' : ((2 : ℝ) ^ t - 1) * jsp87Carry N
      = ((2 : ℝ) ^ t - 1) * (⌊jsp87Carry N⌋ : ℝ) + (jsp87DigitBlock N t : ℝ) := by
    rw [h1, mul_add, hmul]
  simp only [jsp87CarryExcess] at h1' ⊢
  exact h1'

/-- **THE WINDOW–BLOCK EQUATION — THE HEADLINE OF THIS ROUND.**

If the digits of `S` are eventually periodic from `M` with period `t > 0`, then
for every `N ≥ M`

`c (N+t) + Ω N t = 2^t · c N + B N t`,

i.e. **the `ω`-window at `N`, the carry excess at `N + t`, the carry excess at
`N` and the digit block determine each other exactly.**  Equivalently:

* the carry excess one period ahead is `2^t` times the carry excess now, plus
  the digit block, minus the `ω`-window;
* the `ω`-window is *readable* from the digit string and the carry excess.

This is the first exact `ℤ`-equation in the tree that involves a *window of
`ω`-values*; it joins round 47's digit block, round 48's grid and this round's
`ω`-window.  The proof compares two expressions for `(2^t−1)·θ N`: the window
equation (this round) and the block equation (round 48). -/
theorem jsp87_window_block_equation {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    jsp87CarryExcess (N + t) + (jsp87OmegaWindow N t : ℤ)
      = 2 ^ t * jsp87CarryExcess N + jsp87DigitBlock N t := by
  have hkey := jsp87_window_periodEquation ht hM hN hper
  have hq := jsp87_carry_block_equation ht hM hN hper
  have hcast : ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ)
      = (jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ) := by
    simp only [Int.cast_sub]
  have heq : (jsp87CarryExcess (N + t) : ℝ) + (jsp87OmegaWindow N t : ℝ)
      = 2 ^ t * (jsp87CarryExcess N : ℝ) + (jsp87DigitBlock N t : ℝ) := by
    linarith
  refine (Int.cast_inj).mp (show
      ((jsp87CarryExcess (N + t) + (jsp87OmegaWindow N t : ℤ) : ℤ) : ℝ)
        = ((2 ^ t * jsp87CarryExcess N + jsp87DigitBlock N t : ℤ) : ℝ) from ?_)
  push_cast
  exact heq

/-- **THE WINDOW CONGRUENCE.**  Under the hypotheses of
`jsp87_window_block_equation`,

`(2 : ℤ)^t − 1 ∣ c (N+t) − c N + Ω N t − B N t`,

with quotient exactly `c N`.  So a hypothetical rational value of `S` would have
to pass a *congruence test in the Mersenne number `2^t − 1`* at every cut point,
with residue `B N t − Ω N t`. -/
theorem jsp87_window_block_congr {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    (2 : ℤ) ^ t - 1
      ∣ jsp87CarryExcess (N + t) - jsp87CarryExcess N + (jsp87OmegaWindow N t : ℤ)
        - jsp87DigitBlock N t := by
  have hZ := jsp87_window_block_equation ht hM hN hper
  refine ⟨jsp87CarryExcess N, ?_⟩
  linarith [hZ]

/-- **THE CARRY EXCESS AT MOST QUADRUPLE-POWERS PER PERIOD:**
`c (N+t) ≤ 2^t · c N`, since `Ω N t ≥ 2^t − 1` and `B N t ≤ 2^t − 1`.  So if
the digit string is eventually periodic with period `t` from `M`, the carry
excess grows at most like `2^t` per period. -/
theorem jsp87_carryExcess_window_le {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hN2 : 2 ≤ N) (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    (jsp87CarryExcess (N + t) : ℝ) ≤ 2 ^ t * (jsp87CarryExcess N : ℝ) := by
  have hZ := jsp87_window_block_equation ht hM hN hper
  have hB' : (jsp87DigitBlock N t : ℝ) ≤ 2 ^ t - 1 :=
    digitBlock_le_real N t
  have heq : (jsp87CarryExcess (N + t) : ℝ) + (jsp87OmegaWindow N t : ℝ)
      = 2 ^ t * (jsp87CarryExcess N : ℝ) + (jsp87DigitBlock N t : ℝ) := by
    exact_mod_cast hZ
  have hO : (2 : ℝ) ^ t - 1 ≤ (jsp87OmegaWindow N t : ℝ) := by
    have h := jsp87OmegaWindow_ge (N := N) (t := t) hN2
    have hsub : ((2 ^ t - 1 : ℕ) : ℝ) = (2 ^ t : ℝ) - 1 := by
      have hh : ((2 ^ t - 1 : ℕ) : ℝ) = ((2 ^ t : ℕ) : ℝ) - 1 := by
        calc ((2 ^ t - 1 : ℕ) : ℝ) = ((2 ^ t : ℕ) : ℝ) - ((1 : ℕ) : ℝ) :=
              Nat.cast_sub (one_le_two_pow_nat t)
          _ = ((2 ^ t : ℕ) : ℝ) - 1 := by norm_num
      rwa [Nat.cast_pow] at hh
    have heq : (2 : ℝ) ^ t - 1 = ((2 ^ t - 1 : ℕ) : ℝ) := by
      rw [hsub]
    rw [heq]
    exact Nat.cast_le.mpr h
  linarith

/-- **THE WINDOW IS READABLE FROM THE DIGITS AND THE CARRY EXCESS:**
`Ω N t ≤ 2^t · c N + 2^t − 1`, from the window–block equation, `c (N+t) ≥ 0` and
`B N t ≤ 2^t − 1`.  In particular a *small* carry excess forces a *small*
`ω`-window, i.e. long stretches of `ω`-values equal to `1`. -/
theorem jsp87_omegaWindow_le_carryExcess {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    (jsp87OmegaWindow N t : ℝ) ≤ 2 ^ t * (jsp87CarryExcess N : ℝ) + 2 ^ t - 1 := by
  have hZ := jsp87_window_block_equation ht hM hN hper
  have hB' : (jsp87DigitBlock N t : ℝ) ≤ 2 ^ t - 1 :=
    digitBlock_le_real N t
  have heq : (jsp87CarryExcess (N + t) : ℝ) + (jsp87OmegaWindow N t : ℝ)
      = 2 ^ t * (jsp87CarryExcess N : ℝ) + (jsp87DigitBlock N t : ℝ) := by
    exact_mod_cast hZ
  have hc : (0 : ℝ) ≤ (jsp87CarryExcess (N + t) : ℝ) := by
    have h := jsp87CarryExcess_nonneg (N + t)
    exact_mod_cast h
  linarith

/-- **THE WINDOW PLUS THE EXCESS INCREMENT IS AT LEAST `2^t − 1`** for `2 ≤ N`
(the window equation plus round 44's `jsp87Carry_ge_one_plus_seven`). -/
theorem jsp87_omegaWindow_excess_ge' {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hN2 : 2 ≤ N) (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ) + (jsp87OmegaWindow N t : ℝ)
      ≥ (2 : ℝ) ^ t - 1 := by
  have hkey := jsp87_window_periodEquation ht hM hN hper
  have hθ : 1 ≤ jsp87Carry N := by linarith [jsp87Carry_ge_one_plus_seven hN2]
  have hmul : (2 : ℝ) ^ t * jsp87Carry N ≥ (2 : ℝ) ^ t * 1 :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have hL : ((2 : ℝ) ^ t - 1) * jsp87Carry N = 2 ^ t * jsp87Carry N - jsp87Carry N := by
    ring
  have hX : ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ)
      + (jsp87OmegaWindow N t : ℝ) ≥ (2 : ℝ) ^ t - 1 := by
    rw [← hkey, hL]
    have hnonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ t - 1) * (jsp87Carry N - 1) :=
      mul_nonneg (le_of_lt (two_pow_sub_one_pos' ht)) (by linarith)
    nlinarith [hnonneg]
  exact hX

/-! ## 5. The period equation: the `ω`-difference is a second difference of the
carry excess -/

/-- **THE PERIOD EQUATION.**

If the binary digits of `S` are eventually periodic from `M` with period `t > 0`,
then for every `N ≥ M`

`ω (N+t) − ω N = 2 (c (N+t) − c N) − (c (N+1+t) − c (N+1))`.

That is: **the lag-`t` `ω`-difference is exactly the second difference of the
carry excess.**  The unconditional version of this identity is
`jsp87_omega_diff_eq_carryShift`; the point of this form is that everything on
the right is an *integer* built from the carry excess, so a rational value of `S`
would pin the `ω`-family to the `ℤ`-lattice generated by the carry excess. -/
theorem jsp87_omega_diff_periodEquation {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    (omega (N + t) : ℤ) - (omega N : ℤ)
      = 2 * (jsp87CarryExcess (N + t) - jsp87CarryExcess N)
        - (jsp87CarryExcess (N + 1 + t) - jsp87CarryExcess (N + 1)) := by
  have hstep := jsp87CarryShift_step N t
  have hN1 : M ≤ N + 1 := by omega
  have hE0 := jsp87CarryShift_eq_excess ht hM hN hper
  have hE1 := jsp87CarryShift_eq_excess (N := N + 1) ht hM hN1 hper
  rw [hE0, hE1] at hstep
  have hcastE : ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ)
      = (jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ) := by
    simp only [Int.cast_sub]
  have hcastE' : ((jsp87CarryExcess (N + 1 + t) - jsp87CarryExcess (N + 1) : ℤ) : ℝ)
      = (jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ) := by
    simp only [Int.cast_sub]
  have heq : ((jsp87OmegaDiff N t : ℤ) : ℝ)
      = 2 * ((jsp87CarryExcess (N + t) - jsp87CarryExcess N : ℤ) : ℝ)
        - ((jsp87CarryExcess (N + 1 + t) - jsp87CarryExcess (N + 1) : ℤ) : ℝ) := by
    linarith [hstep]
  refine (Int.cast_inj).mp (show
      (((omega (N + t) : ℤ) - (omega N : ℤ) : ℤ) : ℝ)
        = ((2 * (jsp87CarryExcess (N + t) - jsp87CarryExcess N)
            - (jsp87CarryExcess (N + 1 + t) - jsp87CarryExcess (N + 1)) : ℤ) : ℝ) from ?_)
  push_cast
  linarith [heq, hcastE, hcastE', jsp87OmegaDiff_cast N t]

/-- **WHAT A RATIONAL VALUE OF `S` FORCES, STATED ON THE `ω`-FAMILY.**  If
`S = a / b` with `b > 0` then there are `t > 0`, `M` with `1 ≤ M` such that for
every `N ≥ M` the lag-`t` `ω`-difference is the second difference of the
carry excess. -/
theorem jsp87Series_rational_imp_omega_diff_periodEquation {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
      ∧ ∀ N, M ≤ N →
        (omega (N + t) : ℤ) - (omega N : ℤ)
          = 2 * (jsp87CarryExcess (N + t) - jsp87CarryExcess N)
            - (jsp87CarryExcess (N + 1 + t) - jsp87CarryExcess (N + 1)) := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  exact ⟨t, M, ht, hM, fun N hN => jsp87_omega_diff_periodEquation ht hM hN hper⟩

private theorem abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b

private theorem abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le' a (-b)
  rwa [abs_neg] at h

/-- **THE LOGARITHMIC BOUND ON THE `ω`-DIFFERENCE UNDER EVENTUAL PERIODICITY.**

Under the hypotheses of `jsp87_omega_diff_periodEquation`,

`|ω (N+t) − ω N| ≤ 6 · log₂ (N+t+1)`,

by the logarithmic bound `c N ≤ (log N + 1)/log 2` of round 50 applied to the
four carry excesses in the period equation.  So a rational value of `S` would
force the `ω`-differences at the period to be **logarithmic**. -/
theorem jsp87_omega_diff_periodEquation_bound {M t N : ℕ} (ht : 0 < t) (hM : 1 ≤ M) (hN : M ≤ N)
    (hper : ∀ n, M ≤ n → jsp87Digit (n + t) = jsp87Digit n) :
    |(omega (N + t) : ℝ) - (omega N : ℝ)|
      ≤ 6 * ((Real.log (N + t + 1) + 1) / Real.log 2) := by
  have hper' := jsp87_omega_diff_periodEquation ht hM hN hper
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcarry (u : ℕ) (hu : 1 ≤ u) (hv : u ≤ N + t + 1) :
      ((jsp87CarryExcess u : ℝ)) ≤ (Real.log (N + t + 1) + 1) / Real.log 2 := by
    have h1 := jsp87CarryExcess_le_logb (N := u) hu
    have h2 : Real.log u ≤ Real.log (N + t + 1) := by
      apply Real.log_le_log
      · have hpos : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
        linarith
      · exact_mod_cast hv
    have h3 : Real.log u / Real.log 2 + 1 / Real.log 2
        ≤ Real.log (N + t + 1) / Real.log 2 + 1 / Real.log 2 := by
      have := div_le_div_of_nonneg_right h2 hlog2.le
      linarith
    have h4 : ((jsp87CarryExcess u : ℝ)) ≤ Real.log u / Real.log 2 + 1 / Real.log 2 := by
      have h5 : (Real.log u + 1) / Real.log 2
          = Real.log u / Real.log 2 + 1 / Real.log 2 := by field_simp
      rw [h5] at h1
      exact h1
    have heq : (Real.log (N + t + 1) + 1) / Real.log 2
        = Real.log (N + t + 1) / Real.log 2 + 1 / Real.log 2 := by field_simp
    rw [heq]
    linarith
  have hA : ((jsp87CarryExcess (N + t) : ℝ)) ≤ (Real.log (N + t + 1) + 1) / Real.log 2 :=
    hcarry (N + t) (by omega) (by omega)
  have hB : ((jsp87CarryExcess (N + 1 + t) : ℝ)) ≤ (Real.log (N + t + 1) + 1) / Real.log 2 :=
    hcarry (N + 1 + t) (by omega) (by omega)
  have hC : ((jsp87CarryExcess N : ℝ)) ≤ (Real.log (N + t + 1) + 1) / Real.log 2 :=
    hcarry N (by omega) (by omega)
  have hD : ((jsp87CarryExcess (N + 1) : ℝ)) ≤ (Real.log (N + t + 1) + 1) / Real.log 2 :=
    hcarry (N + 1) (by omega) (by omega)
  have hn0 : (0 : ℝ) ≤ (jsp87CarryExcess (N + t) : ℝ) := by
    exact_mod_cast (jsp87CarryExcess_nonneg (N + t))
  have hn1 : (0 : ℝ) ≤ (jsp87CarryExcess (N + 1 + t) : ℝ) := by
    exact_mod_cast (jsp87CarryExcess_nonneg (N + 1 + t))
  have hn2 : (0 : ℝ) ≤ (jsp87CarryExcess N : ℝ) := by
    exact_mod_cast (jsp87CarryExcess_nonneg N)
  have hn3 : (0 : ℝ) ≤ (jsp87CarryExcess (N + 1) : ℝ) := by
    exact_mod_cast (jsp87CarryExcess_nonneg (N + 1))
  have hperR : (omega (N + t) : ℝ) - (omega N : ℝ)
      = 2 * ((jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ))
        - ((jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ)) := by
    have h2 : ((omega (N + t) - omega N : ℤ) : ℝ)
        = (omega (N + t) : ℝ) - (omega N : ℝ) := by
      rw [Int.cast_sub]
      rfl
    have h3 : ((2 * (jsp87CarryExcess (N + t) - jsp87CarryExcess N)
        - (jsp87CarryExcess (N + 1 + t) - jsp87CarryExcess (N + 1)) : ℤ) : ℝ)
        = 2 * ((jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ))
          - ((jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ)) := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_sub]
      norm_num
    have h4 := congrArg (fun z : ℤ => (z : ℝ)) hper'
    linarith [h2, h3]
  rw [hperR]
  have hring : 2 * ((jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ))
      - ((jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ))
      = 2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ)
        - (jsp87CarryExcess (N + 1 + t) : ℝ) + (jsp87CarryExcess (N + 1) : ℝ) := by ring
  rw [hring]
  calc |2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ)
        - (jsp87CarryExcess (N + 1 + t) : ℝ) + (jsp87CarryExcess (N + 1) : ℝ)|
      ≤ |2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ)|
          + |(jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ)| := by
        have hform : (2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ))
            - (jsp87CarryExcess (N + 1 + t) : ℝ) + (jsp87CarryExcess (N + 1) : ℝ)
            = (2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ))
              + (-((jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ))) := by
          ring
        rw [hform]
        have h1 := abs_add_le' (2 * (jsp87CarryExcess (N + t) : ℝ)
            - 2 * (jsp87CarryExcess N : ℝ))
          (-((jsp87CarryExcess (N + 1 + t) : ℝ) - (jsp87CarryExcess (N + 1) : ℝ)))
        rwa [abs_neg] at h1
      _ ≤ 2 * ((jsp87CarryExcess (N + t) : ℝ) + (jsp87CarryExcess N : ℝ))
          + ((jsp87CarryExcess (N + 1 + t) : ℝ) + (jsp87CarryExcess (N + 1) : ℝ)) := by
        have e3 : |2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ)|
            = 2 * |(jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ)| := by
          rw [show (2 * (jsp87CarryExcess (N + t) : ℝ) - 2 * (jsp87CarryExcess N : ℝ))
              = 2 * ((jsp87CarryExcess (N + t) : ℝ) - (jsp87CarryExcess N : ℝ)) by ring,
            abs_mul, abs_of_nonneg (by norm_num)]
        rw [e3]
        have e1 := abs_sub_le' (jsp87CarryExcess (N + t) : ℝ) (jsp87CarryExcess N : ℝ)
        rw [abs_of_nonneg hn0, abs_of_nonneg hn2] at e1
        have e2 := abs_sub_le' (jsp87CarryExcess (N + 1 + t) : ℝ) (jsp87CarryExcess (N + 1) : ℝ)
        rw [abs_of_nonneg hn1, abs_of_nonneg hn3] at e2
        linarith
      _ ≤ 2 * ((Real.log (N + t + 1) + 1) / Real.log 2 + (Real.log (N + t + 1) + 1) / Real.log 2)
          + ((Real.log (N + t + 1) + 1) / Real.log 2 + (Real.log (N + t + 1) + 1) / Real.log 2) := by
        have hAL : (jsp87CarryExcess (N + t) : ℝ)
            ≤ (Real.log (N + t + 1) + 1) / Real.log 2 := by
          simpa using hA
        have hCL : (jsp87CarryExcess N : ℝ)
            ≤ (Real.log (N + t + 1) + 1) / Real.log 2 := by
          simpa using hC
        have hBL : (jsp87CarryExcess (N + 1 + t) : ℝ)
            ≤ (Real.log (N + t + 1) + 1) / Real.log 2 := by
          simpa using hB
        have hDL : (jsp87CarryExcess (N + 1) : ℝ)
            ≤ (Real.log (N + t + 1) + 1) / Real.log 2 := by
          simpa using hD
        linarith
      _ = 6 * ((Real.log (N + t + 1) + 1) / Real.log 2) := by ring

/-! ## 6. The dyadic sub-case, as a carry-integrality statement -/

/-- **THE DYADIC CROSS-IDENTIFICATION.**  For `1 ≤ M`,

`S = n / 2^M` for some `n : ℤ`  **iff**  *some* carry `θ N` (at some `N ≥ 1`) is an
**integer**.

(⇒) from `jsp87_scaled_decomposition`: `2^M S = I M + θ M` with `I M ∈ ℤ`.
(⇐) likewise, at the cut point `N` where the carry is integral.

So the period-`1` sub-case of JSP-000087 — which round 48 identified with the
question whether the binary expansion of `S` *terminates* — is exactly the
question whether a single carry of the series is an integer. -/
theorem jsp87_dyadic_imp_carry_int {M : ℕ} (hM : 1 ≤ M) (n : ℤ)
    (hn : jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) :
    ∃ k : ℤ, jsp87Carry M = (k : ℝ) := by
  have hneM : ((2 : ℝ) ^ M) ≠ 0 := by positivity
  have hscaled : (2 : ℝ) ^ M * jsp87Series = (n : ℝ) := by
    rw [hn, mul_div_cancel₀ _ hneM]
  have hdecomp := jsp87_scaled_decomposition M hM
  have hkey : (2 : ℝ) ^ M * jsp87Tail M = (n : ℝ) - (jsp87IntPart M : ℝ) := by
    linarith [hscaled, hdecomp]
  refine ⟨n - jsp87IntPart M, ?_⟩
  calc jsp87Carry M = (2 : ℝ) ^ M * jsp87Tail M := rfl
    _ = (n : ℝ) - (jsp87IntPart M : ℝ) := hkey
    _ = ((n - jsp87IntPart M : ℤ) : ℝ) := by
      push_cast
      ring

/-- **AN INTEGRAL CARRY MAKES `S` DYADIC.** -/
theorem jsp87_carry_int_imp_dyadic {N : ℕ} (hN : 1 ≤ N) (k : ℤ)
    (hk : jsp87Carry N = (k : ℝ)) :
    ∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ N) := by
  have hdecomp := jsp87_scaled_decomposition N hN
  have hthis : jsp87Carry N = (2 : ℝ) ^ N * jsp87Tail N := rfl
  have hs : (2 : ℝ) ^ N * jsp87Series = (k : ℝ) + (jsp87IntPart N : ℝ) := by
    rw [hdecomp, ← hthis, hk]
    ring
  have hne : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  have hS : jsp87Series * (2 : ℝ) ^ N = (k : ℝ) + (jsp87IntPart N : ℝ) := by
    rw [mul_comm]
    exact hs
  have hcast : ((k + jsp87IntPart N : ℤ) : ℝ) = (k : ℝ) + (jsp87IntPart N : ℝ) := by
    rw [Int.cast_add]
  refine ⟨k + jsp87IntPart N, ?_⟩
  refine (eq_div_iff hne).2 ?_
  rw [hcast]
  exact hS

/-- **THE DYADIC CROSS-IDENTIFICATION (both directions).** -/
theorem jsp87_dyadic_iff_carryInt (M : ℕ) (hM : 1 ≤ M) :
    (∃ n : ℤ, jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) ↔ ∃ k : ℤ, jsp87Carry M = (k : ℝ) := by
  constructor
  · rintro ⟨n, hn⟩
    exact jsp87_dyadic_imp_carry_int hM n hn
  · rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := jsp87_carry_int_imp_dyadic (N := M) hM k hk
    exact ⟨n, hn⟩

/-- **THE CARRY-INTEGRALITY CHARACTERISATION OF THE DYADIC CASE.**  For `1 ≤ M`,
the binary digits of `S` are eventually `0` from `M` **iff some carry of the
series is an integer**.  (The left-hand side is round 48's
`jsp87Series_dyadic_iff`.) -/
theorem jsp87_carryInt_iff_digitZero (M : ℕ) (hM : 1 ≤ M) :
    (∃ k : ℤ, jsp87Carry M = (k : ℝ)) ↔ ∀ N, M ≤ N → jsp87Digit N = 0 := by
  rw [← jsp87_dyadic_iff_carryInt M hM, jsp87Series_dyadic_iff hM]

/-- **INTEGRALITY PROPAGATES FORWARD.** -/
theorem jsp87_carry_int_succ {N : ℕ} (k : ℤ) (hk : jsp87Carry N = (k : ℝ)) :
    ∃ k' : ℤ, jsp87Carry (N + 1) = (k' : ℝ) := by
  have h := jsp87Carry_succ N
  rw [hk] at h
  refine ⟨2 * k - omega N, ?_⟩
  push_cast
  linarith

/-- **INTEGRALITY PROPAGATES FORWARD, ALONG ANY RANGE.** -/
theorem jsp87_carry_int_of_le {M N : ℕ} (hM : 1 ≤ M) (hN : M ≤ N) (k : ℤ)
    (hk : jsp87Carry M = (k : ℝ)) :
    ∃ k' : ℤ, jsp87Carry N = (k' : ℝ) := by
  induction N generalizing M with
  | zero => omega
  | succ N ih =>
      rcases Nat.eq_or_lt_of_le hN with h | hlt
      · subst h
        exact ⟨k, hk⟩
      · obtain ⟨k', hk'⟩ := ih (M := M) hM (by omega) hk
        exact jsp87_carry_int_succ k' hk'

/-- **AN INTEGRAL CARRY IS ITS OWN CARRY EXCESS:** if `θ N` is an integer then
`⌊θ N⌋ = θ N`. -/
theorem jsp87_carry_int_excess {N : ℕ} (k : ℤ) (hk : jsp87Carry N = (k : ℝ)) :
    jsp87CarryExcess N = k := by
  have hf : ⌊jsp87Carry N⌋ = k := by rw [hk]; exact Int.floor_intCast k
  exact hf

/-- **UNDER THE DYADIC HYPOTHESIS THE CARRY EXCESS IS AT LEAST `2`** at every
cut point `N ≥ 2` (unconditionally it is at least `1`, round 44): an integral
carry is `> 1`. -/
theorem jsp87_carry_int_ge_two {N : ℕ} (hN : 2 ≤ N) (k : ℤ)
    (hk : jsp87Carry N = (k : ℝ)) : 2 ≤ k := by
  have h1 : (1 : ℝ) < k := by
    rw [← hk]
    exact jsp87Carry_gt_one_of_ge_two hN
  have h1' : (1 : ℤ) < k := by exact_mod_cast h1
  omega

/-- **THE DYADIC PERIOD EQUATION: `ω N = 2 c N − c (N+1)`.**

Under the dyadic hypothesis (`S = n / 2^M`, `1 ≤ M`) the carry is integral at
every `N ≥ M`, hence the carry excess *is* the carry, and round 40's recurrence
`θ (N+1) = 2 θ N − ω N` becomes the statement that **the whole `ω`-family is a
doubling-difference of the carry excess**.  This is the period-`1` instance of
`jsp87_omega_diff_periodEquation`, here obtained from the dyadic hypothesis
alone. -/
theorem jsp87_dyadic_omega_eq {M : ℕ} (hM : 1 ≤ M) (n : ℤ)
    (hn : jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) (N : ℕ) (hN : M ≤ N) :
    (omega N : ℤ) = 2 * jsp87CarryExcess N - jsp87CarryExcess (N + 1) := by
  obtain ⟨kM, hkM⟩ := jsp87_dyadic_imp_carry_int hM n hn
  obtain ⟨kN, hkN⟩ := jsp87_carry_int_of_le hM hN kM hkM
  obtain ⟨kN1, hkN1⟩ := jsp87_carry_int_succ kN hkN
  have hrec := jsp87Carry_succ N
  rw [hkN, hkN1] at hrec
  have hfloorN := jsp87_carry_int_excess kN hkN
  have hfloorN1 := jsp87_carry_int_excess kN1 hkN1
  rw [hfloorN, hfloorN1]
  have hR : ((omega N : ℕ) : ℝ) = 2 * (kN : ℝ) - (kN1 : ℝ) := by linarith [hrec]
  exact_mod_cast hR

/-- **THE DYADIC SQUEEZE.**  Under the dyadic hypothesis, for every `N ≥ M ≥ 1`

`(omega N : ℝ) ≤ 2 * (jsp87CarryExcess N : ℝ) − 2`  and
`2 * (jsp87CarryExcess N : ℝ) − (Real.log (N+1) + 1)/Real.log 2 ≤ (omega N : ℝ)`.

That is: under a dyadic value of `S`, the `ω`-value at `N` is squeezed into a
window of width `log₂(N+1) + 2` placed just below `2 c N` — the carry excess
would determine `ω N` up to a logarithmic error. -/
theorem jsp87_dyadic_omega_bounds {M : ℕ} (hM : 1 ≤ M) (n : ℤ)
    (hn : jsp87Series = (n : ℝ) / ((2 : ℝ) ^ M)) (N : ℕ) (hN : M ≤ N) :
    ((omega N : ℝ) ≤ 2 * (jsp87CarryExcess N : ℝ) - 2)
      ∧ (2 * (jsp87CarryExcess N : ℝ) - (Real.log (N + 1 : ℕ) + 1) / Real.log 2
        ≤ (omega N : ℝ)) := by
  obtain ⟨kM, hkM⟩ := jsp87_dyadic_imp_carry_int hM n hn
  obtain ⟨kN, hkN⟩ := jsp87_carry_int_of_le hM hN kM hkM
  obtain ⟨kN1, hkN1⟩ := jsp87_carry_int_succ kN hkN
  have hrec := jsp87Carry_succ N
  rw [hkN, hkN1] at hrec
  have hfloorN := jsp87_carry_int_excess kN hkN
  have hfloorN1 := jsp87_carry_int_excess kN1 hkN1
  have hN1 : 2 ≤ N + 1 := by omega
  have hge : (2 : ℤ) ≤ kN1 := jsp87_carry_int_ge_two hN1 kN1 hkN1
  have hge' : (2 : ℝ) ≤ (jsp87CarryExcess (N + 1) : ℝ) := by
    rw [hfloorN1]
    exact_mod_cast hge
  have hrec' : (omega N : ℤ)
      = 2 * (jsp87CarryExcess N : ℤ) - jsp87CarryExcess (N + 1) :=
    jsp87_dyadic_omega_eq hM n hn N hN
  have hR : ((omega N : ℕ) : ℝ) = 2 * (jsp87CarryExcess N : ℝ) - (jsp87CarryExcess (N + 1) : ℝ) := by
    exact_mod_cast hrec'
  have hle : ((jsp87CarryExcess (N + 1) : ℝ)) ≤ (Real.log (N + 1 : ℕ) + 1) / Real.log 2 := by
    have h1 := jsp87CarryExcess_le_logb (N := N + 1) (by omega)
    rw [hfloorN1] at h1
    rw [hfloorN1]
    exact h1
  constructor
  · linarith
  · linarith

/-! ## 7. The fifth irrationality criterion, on the `ω`-window congruence -/

/-- **RATIONALITY ⇒ SOME CANDIDATE PERIOD PASSES THE WINDOW CONGRUENCE TEST.**

If `S = a / b` with `b > 0` then there are `t > 0`, `M` with `1 ≤ M` such that

`2^t − 1 ∣ c (N+t) − c N + Ω N t − B N t`  for every `N ≥ M`. -/
theorem jsp87Series_rational_imp_omegaWindow_congr {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : jsp87Series = (a : ℝ) / (b : ℝ)) :
    ∃ t M : ℕ, 0 < t ∧ 1 ≤ M
      ∧ ∀ N, M ≤ N → (2 : ℤ) ^ t - 1
        ∣ jsp87CarryExcess (N + t) - jsp87CarryExcess N + (jsp87OmegaWindow N t : ℤ)
          - jsp87DigitBlock N t := by
  obtain ⟨t, M, ht, hM, hper⟩ := jsp87_digit_eventuallyPeriodic hb h
  exact ⟨t, M, ht, hM, fun N hN => jsp87_window_block_congr ht hM hN hper⟩

/-- **THE FIFTH IRRATIONALITY CRITERION.**

If **no** candidate period `t > 0` and start point `M` passes the window
congruence test `2^t − 1 ∣ c (N+t) − c N + Ω N t − B N t` at *every* `N ≥ M`,
then the Erdős series is **irrational**.  This is a criterion on a genuinely new
object — the residue of the `ω`-window modulo the Mersenne number `2^t − 1`.
Together with the four criteria of rounds 41, 46, 47 and 48 the development now
has five independent obstructions to `jsp_000087_main`, phrased on five
different objects. -/
theorem jsp87Series_irrational_of_omegaWindow_never_congr
    (h : ∀ t M : ℕ, 0 < t → 1 ≤ M →
      ¬ (∀ N, M ≤ N → (2 : ℤ) ^ t - 1
        ∣ jsp87CarryExcess (N + t) - jsp87CarryExcess N + (jsp87OmegaWindow N t : ℤ)
          - jsp87DigitBlock N t)) :
    Irrational jsp87Series := by
  show jsp87Series ∉ Set.range ((↑) : ℚ → ℝ)
  rintro ⟨q, hq⟩
  have hden : 0 < q.den := Rat.den_pos q
  obtain ⟨t, M, ht, hM1, hcongr⟩ :=
    jsp87Series_rational_imp_omegaWindow_congr hden (by rw [← hq, Rat.cast_def])
  exact h t M ht hM1 hcongr

end JSP87
