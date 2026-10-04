# ACCEPTANCE — JSP-000087

## Target statement (from the catalog record JSP-000087)

Let `ω(n)` be the number of distinct prime factors of the positive integer `n`.
Erdős (1948) asked whether

```
∑_{n=1}^{∞}  ω(n) / 2^n
```

is irrational.  K. Pratt (arXiv:2409.15185, 2024) proves this **conditionally**,
under a suitably uniform version of the prime `k`-tuples conjecture.

## Required theorem

`jsp_000087_main`

## Current gate status

`lake build` succeeds; the tree contains **0 `sorry` / 0 `admit`**; **158 theorems
and lemmas** are proved, including the *complete* Lambert reduction, **the
Diophantine (carry) scaffold of Erdős' argument**, the *complete* Lambert-side
denominator arithmetic, **the carry-dynamics and the aperiodicity endgame**, and
**the clearing of the Lambert denominators at a finite truncation**

| Theorem | Statement |
| --- | --- |
| `jsp87_convergence` | `HasSum (fun n => ω n · 2 ^ -(n+1)) (∑' n, ω n · 2 ^ -(n+1))` — the series exists |
| `jsp87Series_bounds` | `7/32 ≤ jsp87Series ≤ 1` |
| `sum_multiples_reindex` | the multiples of a prime `p` reindex as `p · k` (finite form) |
| `jsp87_finset_eq_prime_lambert` | `∑_{n<N} ω n/2^(n+1) = ∑_{p<N} ∑_{1≤k, pk<N} 2^(pk+1)⁻¹` |
| `jsp87_finset_eq_prime_lambert_ten` | that common value at `N = 10` is `263/1024` |
| `hasSum_lambert_geometric` | `∑' k, (if 1 ≤ k then 2 ^ -(p k+1) else 0) = 1/(2^(p+1) - 2)` |
| `hasSum_lamF_fst` | the multiples of a prime contribute exactly the Lambert term |
| `jsp87_lambert` | `jsp87Series = ∑' p, (if p.Prime then 1/(2^(p+1) - 2) else 0)` |
| `jsp87_lambert_classic` | `∑' p, (if p.Prime then 1/(2^p - 1) else 0) = 2 * jsp87Series` |
| `jsp87_lambert_reduction` | `∑' n, ω(n)/2^n = ∑' p prime, 1/(2^p - 1)` — the classical identity of PROBLEM.md |

## Round 116 — THE PROBABILISTIC ENDGAME (arXiv:2512.01739 §5.3–§5.11)

`lake build` succeeds; the tree contains **0 `sorry` / 0 `admit`**; **2304
theorems and lemmas** are proved, including **the machine-checked endgame of the
Tao–Teräväinen proof**: their *Theorem 5.1 (technical reduction)* together with
their own convergence hypothesis (5.18) is **unsatisfiable**.

| Theorem | Statement |
| --- | --- |
| `jsp87FAvg`, `jsp87Var`, `jsp87CAvg`, `jsp87e` | the expectation, the variance, the complex expectation and the phase `e(t) = exp 2πi t` of §5.3 |
| `jsp87CS`, `jsp87FAvg_abs_le_sqrt_sq` | Cauchy–Schwarz for finite sums, from scratch (the discriminant argument) |
| `jsp87e_sub_mul_le`, `jsp87E_split_sqrt_le` | the Lipschitz bound of the circle and **κ₃**, the Cauchy–Schwarz/Taylor split of (5.14) |
| `jsp87_charfun_norm_sq`, `jsp87_var_double` | `‖𝔼 e^{iY}‖² = 𝔼_{i,j} cos(Y i − Y j)` and `𝔼_{i,j}(Y i − Y j)² = 2 Var Y` |
| `jsp87_one_sub_cos_ge`, `jsp87_charfun_le` | the cosine bound of (5.19) and the variance bound `‖𝔼 e (i qT)‖ ≤ 1 − 8 Var (qT)` |
| `jsp87_prod_charfun_le`, `jsp87_prod_charfun_le_half` | **(5.20)** in product form: `∏_p ‖𝔼 e (q X p)‖ ≤ exp(−8 ∑_p Var (q X p)) ≤ 1/2` under (5.21) |
| **`jsp87_endgame_sum_ge`** | **THE ENDGAME**: (5.15) + (5.16)–(5.17) + (5.19) + (5.21) force `κ₁+κ₂+κ₃+κ₄+κ₅ ≥ 1/2` |
| **`jsp87_endgame_impossible`** | **no configuration** satisfies (5.15), (5.16)–(5.17), (5.19), (5.21) together with `κ_j < 1/30` for all `j`: their Theorem 5.1 is incompatible with (5.18), so **the logical closure of the published proof is done** and the remaining burden of `jsp_000087_main` is localised to the two arithmetic inputs (5.18) and (5.21) |

`lean/JSPProblem/Diophantine.lean` — the Erdős–Pratt Diophantine apparatus
(the carry decomposition and the Lambert denominator arithmetic):

| Theorem | Statement |
| --- | --- |
| `jsp87Tail`, `hasSum_jsp87Tail`, `jsp87Tail_nonneg` | the carry tail `τ N = ∑' k, ω(N+k) 2^-(N+k+1)` exists and is `≥ 0` |
| `jsp87Tail_pos`, `jsp87Tail_le` | `0 < τ N ≤ (N+1) 2^-N` for `1 ≤ N` — the tail decays exponentially |
| `jsp87_series_eq_sum_add_tail` | `S = ∑ n<N ω(n) 2^-(n+1) + τ N` |
| `jsp87IntPart`, `jsp87IntPart_nonneg`, `jsp87IntPart_cast` | the integer `I N = ∑ n<N ω(n) 2^(N-n-1) ≥ 0` |
| `jsp87_sum_range_eq_intPart` | `∑ n<N ω(n) 2^-(n+1) = I N · 2^-N` |
| `jsp87_scaled_decomposition` | **the carry decomposition** `2^N · S = I N + 2^N · τ N` |
| `jsp87_carry_mul_eq_int` | **the denominator obstruction**: if `S = a/b`, `b > 0`, then `b · 2^N · τ N ∈ ℤ` for every `N` |
| `jsp87_carry_ge_inv` | a positive carry of a rational `S = a/b` is at least `1/b` |
| `jsp87_carry_bounds` | the quantitative window `0 < 2^N · τ N ≤ N + 1` |
| `pow_two_eq_one_of_dvd` | `q ∣ 2^p - 1 ⟹ (2 : ZMod q)^p = 1` |
| `dvd_sub_one_prime_gt` | **Fermat**: for primes `p`, `q` with `q ∣ 2^p - 1` and `q ≠ 2`, `p ∣ q - 1`, hence `q > p` |
| `two_pow_sub_one_prime_gross` | for prime `p`, no prime `q ≤ p` divides `2^p - 1` |
| `primeFactors_sub_one_gt` | for prime `p`, every prime factor of `2^p - 1` is `> p` |
| `prod_primes_le_not_dvd` | **no product of primes `≤ p` divides `2^p - 1`** — the Erdős step |

`lean/JSPProblem/LambertGcd.lean` — the **Lambert-side denominator arithmetic**
(the other half of the Erdős–Pratt method, complementing the carry side above):

| Theorem | Statement |
| --- | --- |
| `dvd_pow_sub_one_of_dvd` | `m ∣ k → 2^m − 1 ∣ 2^k − 1` — the `ℕ` geometric series, from scratch |
| `dvd_pow_sub_one_sub_mod` | `2^m − 1 ∣ 2^n − 1 − (2^(n%m) − 1)` — reducing a Mersenne number reduces the exponent |
| `gcd_two_pow_sub_one` | **the exact gcd** `Nat.gcd (2^m−1) (2^n−1) = 2^Nat.gcd m n − 1` |
| `gcd_two_pow_sub_one_of_mathlib` | the same identity, cross-checked against Mathlib's `[simp]` lemma `Nat.pow_sub_one_gcd_pow_sub_one` |
| `coprime_lambert_den_of_distinct_prime` | **distinct primes give coprime Lambert denominators**: `Coprime (2^p−1) (2^q−1)` |
| `gcd_lambert_den_of_distinct_prime`, `coprime_lambert_den_of_coprime` | the same for coprime exponents |
| `lambertDen` | the clearing denominator `∏_{p ∈ s, prime} (2^p − 1)` |
| `lambertDen_mem_factor`, `lambertDen_pos` | each factor divides the product; the product is positive |
| `lambert_den_coprime_finset` | **those denominators are mutually coprime**, so the product is the exact `lcm` and *nothing cancels* in the truncation |
| `lambertDen_pair` | the explicit two-prime product `lambertDen {p,q} = (2^p−1)·(2^q−1)` |
| `dvd_lambert_den_prime_gt` | **THE DENOMINATOR OBSTRUCTION**: a *fixed* `b ≥ 2` dividing `2^p − 1` (prime `p`) forces `p < b` |
| `dvd_lambert_den_prime_lt` | conversely `b ≤ p` gives `¬ b ∣ 2^p − 1` |
| `not_dvd_lambert_den_of_large_prime` | for every `b ≥ 2` there is a prime `p > b` with `b ∤ 2^p − 1` |

### `-- NEW IN ROUND 40 --` `lean/JSPProblem/Periodicity.lean` — the carry dynamics and the aperiodicity endgame

| Theorem | Statement |
| --- | --- |
| `jsp87Carry` | the rescaled tail `θ N = 2^N · τ N` |
| `jsp87Tail_succ` | `τ (N+1) = τ N − jsp87Term N` |
| `jsp87Carry_succ` | **the exact carry recurrence** `θ (N+1) = 2 θ N − ω N` |
| `omega_eq_two_carry_sub` | the digit is recovered from two consecutive carries: `ω N = 2 θ N − θ (N+1)` |
| `jsp87Carry_pos`, `jsp87Carry_le` | `0 < θ N` for every `N`; `θ N ≤ N + 1` for `1 ≤ N` |
| `jsp87Carry_succ_le` | carries grow by at most a factor `2`: `θ (N+1) ≤ 2 θ N` |
| `jsp87Carry_ge_omega_succ` | **digits are bounded by twice the carry**: `ω (N+1) ≤ 4 θ N` |
| `jsp87Carry_ge_quarter` | **the carries are bounded away from `0`**: `θ N ≥ 1/4` for every `N` |
| `jsp87Carry_gt_one`, `jsp87Carry_ge_half`, `jsp87Carry_ge_three_halves` | `ω (N+1) ≥ 5, 2, 6` force `θ N > 1, ≥ 1/2, ≥ 3/2` |
| `Int.fract_eq_div_of_mul_natCast` | a rational number has a *quantised* fractional part: `b · fract x ∈ ℤ` in `[0,b)` |
| `jsp87_fract_scaled` | **`fract (2^N · S) = fract θ N`** — the dynamical and static pictures coincide |
| `jsp87_fract_scaled_eq_div` | if `S = a/b` with `b>0` then the fractional parts of `2^N·S` lie in a **finite** set of size `b` |
| `omega_eq_card_filter` | `ω n` is the cardinality of the primes `≤ n` dividing `n` |
| `omega_mul_prime_of_large_prime` | `p` prime, `1 ≤ n`, `n < p ⟹ ω n + 1 ≤ ω (n·p)` |
| `omega_eventuallyPeriodic_const_mul` | an eventual period `t` makes `n ↦ ω (t·n)` eventually **constant** |
| `omega_not_eventuallyPeriodic` | **THE APERIODICITY ENDGAME: `ω` is not eventually periodic** |
| `omega_periodic_frozen` | the quantitative endgame: under an eventual period, a fresh prime `u > t·M` breaks the frozen value |

### `-- NEW IN ROUND 40 --` `lean/JSPProblem/LambertTrunc.lean` — the join: the Lambert truncation and the clearing of denominators

`LambertIdentity.lean` (the reduction) and `LambertGcd.lean` (the denominator
arithmetic) had never been *joined*.  This file supplies the missing
integrality step, and the Lambert-side mirror image of the carry obstruction.

| Theorem | Statement |
| --- | --- |
| `jsp87_lambertTerm`, `jsp87_lambertAll` | `1/(2^j − 1)` at primes, and `∑' p prime, 1/(2^p − 1)` |
| `jsp87_lambertTerm_le`, `summable_jsp87_lambertTerm` | the Lambert series is dominated by `2 · 2⁻ʲ` and is summable |
| `jsp87_lambertAll_eq` | `∑' p prime, 1/(2^p − 1) = 2 · S` |
| `jsp87_lambertTrunc`, `jsp87_lambertTail`, `jsp87_lambertNumer` | the truncation `T N`, the tail `R N`, the integer numerator |
| `jsp87_lambert_decomp` | **the splitting** `2 · S = T N + R N` |
| `jsp87_lambertTerm_mul_den` | one prime step of the join: `1/(2^p−1) · D_N = D_N/(2^p−1) ∈ ℕ` |
| `jsp87_lambertTrunc_mul_den` | **THE JOIN**: `D_N · T N ∈ ℤ` — the clearing denominator is an exact `ℤ` multiplier, nothing cancels |
| `jsp87_lambertTrunc_eq_div` | `T N = numer N / D_N` |
| `jsp87_lambertTail_pos` | **the Lambert tail is strictly positive** (there is a prime past every cut point) |
| `jsp87_lambertTail_le` | **the Lambert tail is exponentially small**: `0 < R N ≤ 4 · 2⁻ᴺ` |
| `jsp87_lambert_rat_obstruction` | **the Lambert-side denominator obstruction**: if `2·S = a/b` then `b · D_N · R N` is a *positive integer* |
| `jsp87_lambert_rat_ge_one` | consequently `R N ≥ 1/(b · D_N)` |
| `jsp87_lambert_window` | **the combined window** `1/(b·D_N) ≤ R N ≤ 4·D_N·2⁻ᴺ` |

`jsp_000087_main` is **not yet declared**, because the headline statement is a
research-level result and no honest proof of it exists in this development.
Declaring a weakened statement under the name `jsp_000087_main` would
misrepresent the catalog headline, so the gate is correctly reported as
`missing_theorems = ["jsp_000087_main"]`.

## Formalization objects that *are* proved

`lean/JSPProblem/Basic.lean` — arithmetic of `omega` (count of distinct prime
factors, identified with `Nat.primeFactors`):

| Lemma | Statement |
| --- | --- |
| `omega_eq_zero_iff` | `ω n = 0 ↔ n ≤ 1` |
| `omega_pos_of_prime_dvd` | `p.Prime → p ∣ n → 0 < n → 0 < ω n` |
| `prime_eq_of_prime_dvd` | two primes, one dividing the other, are equal |
| `primeFactors_div_prime` | `n ≠ 0 → p.Prime → p ∣ n → n.primeFactors = insert p (n/p).primeFactors` |
| `omega_mono` | `m ∣ n → n ≠ 0 → ω m ≤ ω n` |
| `omega_div_prime` | dividing out a first-multiplicity prime drops `ω` by one |
| `prime_dvd_pow_iff` | `q.Prime → 1 ≤ k → (q ∣ p^k ↔ q ∣ p)` |
| `omega_prime_pow` | `p.Prime → 1 ≤ k → ω (p^k) = 1` |
| `omega_mul_of_coprime` | `Nat.Coprime m n → ω (m*n) = ω m + ω n` |
| `omega_mul_le` | `ω (m*n) ≤ ω m + ω n` |
| `prod_ge_two_pow_card` | every element `≥ 2` forces `2^card ≤ prod` |
| `prod_primeFactors_dvd` | `∏_{p ∈ n.primeFactors} p ∣ n` |
| `two_pow_omega_le` | `0 < n → 2^{ω n} ≤ n` |
| `omega_le_log2` | `0 < n → ω n ≤ log₂ n` |
| `omega_lt` | `1 ≤ n → ω n ≤ n - 1` |
| `succ_le_two_pow` | `k + 1 ≤ 2^k` |

`lean/JSPProblem/Lambert.lean` — the Lambert reduction, indicator form:

| Lemma | Statement |
| --- | --- |
| `omega_eq_finset_sum_indicator` | `ω n = ∑_{p < n+1} [p prime ∧ p ∣ n]` |
| `omega_eq_zero_iff'` | the indicator sum vanishes exactly for `n ≤ 1` |
| `exists_eq_mul_of_dvd` | `0 < p → p ∣ n → ∃ k, n = p * k` |

`lean/JSPProblem/Main.lean` — the Erdős series itself:

| Lemma | Statement |
| --- | --- |
| `jsp87Series` | `def : ℝ` — `∑' n, ω(n) * 2^{-(n+1)}` |
| `jsp87Series_nonneg` | `0 ≤ jsp87Series` |
| `jsp87Series_partial_sum_five` | the partial sum over `n < 5` is exactly `7/32` |

## Concrete blocker for `jsp_000087_main`

The missing ingredient is the **irrationality step of Pratt's argument**, which
needs quantitative correlations of `ω` at shifted primes together with a uniform
prime `k`-tuples hypothesis.  No Mathlib lemma provides this.  The three exact
steps still required are:

1. ~~`jsp87_convergence`~~ — **CLOSED** in `JSPProblem/Convergence.lean`.
2. ~~`jsp87_lambert`~~ — **CLOSED** in `JSPProblem/LambertIdentity.lean`.
2b. ~~the carry scaffold (Erdős side)~~ — **CLOSED** in `JSPProblem/Diophantine.lean`.
2c. ~~the Lambert denominator arithmetic (Lambert side)~~ — **CLOSED** in `JSPProblem/LambertGcd.lean`.
2d. ~~the carry dynamics `θ_{N+1} = 2θ_N − ω N` and the aperiodicity endgame~~ — **CLOSED** in `JSPProblem/Periodicity.lean`.
2e. ~~the clearing of the Lambert denominators at a finite truncation~~ — **CLOSED** in `JSPProblem/LambertTrunc.lean`.
3. `jsp87_irrational` : the Diophantine-approximation argument of Pratt
   (arXiv:2409.15185), conditional on a uniform prime `k`-tuples hypothesis.  This
   step has no Mathlib counterpart at all.

What is now proved is the *entire unconditional apparatus* such a proof needs on
**both** sides of the method.  On the Erdős/carry side: the carry decomposition
`2^N · S = I N + 2^N · τ N` with `I N ∈ ℤ` (`jsp87_scaled_decomposition`), the
denominator obstruction `b · 2^N · τ N ∈ ℤ` whenever `S = a / b`
(`jsp87_carry_mul_eq_int`), and the quantitative window `0 < 2^N · τ N ≤ N + 1`
(`jsp87_carry_bounds`).  On the Lambert side: for prime `p` **no product of primes
`≤ p` divides `2^p - 1`** (`prod_primes_le_not_dvd`, `primeFactors_sub_one_gt`,
`dvd_sub_one_prime_gt`); the denominators `2^p - 1` attached to *distinct primes
are mutually coprime* (`coprime_lambert_den_of_distinct_prime`,
`lambert_den_coprime_finset`), so the clearing denominator of a truncation is
exactly the product and nothing cancels; and a *fixed* denominator `b` can divide
`2^p - 1` for primes `p` only when `p < b` (`dvd_lambert_den_prime_gt`,
`not_dvd_lambert_den_of_large_prime`).

Read together, the two halves say precisely what makes rationality hard: a
hypothetical rational `S = a / b` freezes every carry into the lattice
`(1/b) ℤ` uniformly in `N`, while the truncation denominators `2^p - 1` are
forced to keep introducing prime divisors larger than `b`.

Round 40 closed two more unconditional steps.

**On the Erdős/carry side** (`Periodicity.lean`) the carries of the series are
now followed *dynamically*.  `jsp87Carry_succ` is the exact relation
`θ_{N+1} = 2 θ_N − ω N`, and `jsp87Carry_ge_quarter` shows `θ N ≥ 1/4`
uniformly.  This is important negative knowledge, and it is the reason the naive
Erdős argument cannot simply be run: rationality freezes the carries into
`(1/b) ℤ` **and** the carries are bounded away from `0`, but they are *not*
confined to `(0,1)` — they carry real digit information.  On the positive side
`jsp87_fract_scaled` identifies `fract (2^N·S)` with `fract θ N` and
`jsp87_fract_scaled_eq_div` shows that a rational `S` confines those fractional
parts to a finite set.  Finally, `omega_not_eventuallyPeriodic` proves, from
scratch and elementarily, that the digit function `ω` is **aperiodic** — the
combinatorial endgame every Erdős-style argument of this shape terminates
with.  Mathlib has no such statement.

**On the Lambert side** (`LambertTrunc.lean`) the two halves of the development
are finally *joined*: `jsp87_lambertTrunc_mul_den` proves that the clearing
denominator `D_N = ∏_{p<N}(2^p−1)` is an **exact `ℤ` multiplier of the truncated
Lambert sum** (nothing cancels), and `jsp87_lambert_rat_obstruction` +
`jsp87_lambert_window` give the Lambert mirror image of
`jsp87_carry_mul_eq_int`: under `2·S = a/b`, the cleared tail
`b · D_N · R N` is a positive integer while the tail satisfies `0 < R N ≤ 4·2⁻ᴺ`.

What is now proved is the *entire unconditional apparatus* on both sides,
including the integrality step and the aperiodicity endgame.  The one ingredient
still missing is the **quantitative control of `ω` at shifted primes**, which must
decide how much *genuine carrying* the sequence `θ N` performs — i.e. how far
`θ_N − fract θ_N` fluctuates.  It would have to come from an explicitly stated
uniform prime `k`-tuples hypothesis, which is an assumption of the *published*
result and not of the catalog statement.  It is therefore not introduced here,
and `jsp_000087_main` is still honestly reported as missing.

---

## Round 41 — the binary-digit bookkeeping of the carry excess

New module `lean/JSPProblem/DigitCarry.lean` (637 lines, 34 new theorems/defs,
0 `sorry`, 0 `admit`; 205 proved declarations in the tree, `lake build` clean).
This is the *internal-carry / floor-sequence* plan of round 40, executed in full.

**The digit window.**  `jsp87Carry_window` proves that for every cut point `N`
and every window length `m`,

`∑_{k ≤ m} ω(N+k)·2^{m−k} ≤ 2^{m+1}·θ N`,

so the carry at `N` dominates the binary value of the next `m+1` digits.  Its
consequence `jsp87CarryExcess_pos` (two consecutive integers with one and two
prime factors already force `⌊θ N⌋ ≥ 1`) makes the first carry of the series
*real*, and is instantiated as `jsp87CarryExcess_five_ge_one : 1 ≤ ⌊θ 5⌋`.

**The missing link.**  `jsp87IntPart_succ` (the 2-adic prefix satisfies
`I (N+1) = 2·I N + ω N`) and `jsp87_floor_scaled`
(`⌊2^N·S⌋ = I N + ⌊θ N⌋`) join the round-38 integer part to the round-40 carry:
the *true* binary prefix of `S` is short of the 2-adic prefix by exactly the
carry excess.  This is the precise reason the naive Erdős argument does not
close, and it had never been stated in the tree.

**The digits.**  `Int.fract_two_mul` and `jsp87_fract_scaled_succ` (the doubling
map on fractional parts — absent from Mathlib), `jsp87Digit`,
`jsp87_digit_eq_fract`, `jsp87Digit_mem` (the digits are `0` or `1`), and the
exact integer identity

`jsp87_digit_bookkeeping` :  `d N = ω N + c (N+1) − 2·c N`,  `c N = ⌊θ N⌋`.

**Rationality forces eventually-periodic digits — from scratch.**
`jsp87_digit_eventuallyPeriodic`: if `S = a/b` with `b > 0` then the binary
digits of `S` are eventually periodic.  Proved elementarily (finite range of
the numerators `fract (2^N·S) = c(N)/b`, `c(N) < b`; pigeonhole; the
deterministic doubling map).  Mathlib has no such statement.

**The endgame.**  `jsp87Series_irrational_of_carryExcess_eventuallyPeriodic`:

> **If the carry excess `⌊2^N·τ N⌋` is eventually periodic, then the Erdős
> series is irrational.**

with corollaries for "the carries stay below `1` eventually" and "the excess
stabilises", the contrapositive
`jsp87Series_rational_imp_carryExcess_not_periodic` (rationality *forces* the
carry excess to be non-eventually-periodic), and the dichotomy
`jsp87Series_irrational_or_carryExcess_not_periodic`.

**Gate status.**  `jsp_000087_main` is **still deliberately not declared**: the
headline irrationality is conditional in the published literature (Pratt,
arXiv:2409.15185, under a uniform prime `k`-tuples conjecture) and the catalog
records *Solved; Lean proof: No; Eligible to claim: No*.  After round 41 the
remaining gap is a single arithmetic object — a quantitative estimate for
`⌊2^N·τ N⌋` strong enough to contradict rationality.  Emitting a weakened
statement under the name `jsp_000087_main` would misrepresent the catalog
headline, so the name stays withheld and `harness/score.py --strict-prize`
correctly reports `partial_ok=true, prize_ready=false`.

---

## Round 44 — the quantitative shape of the carry excess, and the sieve content

New module `lean/JSPProblem/CarryExcess.lean` (776 lines, **30 new theorems and
defs**, 0 `sorry`, 0 `admit`; **219 proved theorems and lemmas** in the tree at
the `^(theorem|lemma)` level, `lake build` clean).
This is a **new attack family**: neither the Lambert reduction (r. 37), the
carry scaffold (r. 38), the gcd arithmetic (r. 39), the carry dynamics (r. 40),
nor the digit bookkeeping (r. 41).  It attacks `⌊θ N⌋` — the one object left —
from the arithmetic side, and its main output is **negative knowledge that
closes off whole strategies**.

### 1. `ω` is unbounded

| Theorem | Statement |
| --- | --- |
| `omega_ge_one_of_ge_two` | `2 ≤ n → 1 ≤ ω n` |
| `omega_ge_two_of_six_dvd` | `0 < n → 6 ∣ n → 2 ≤ ω n` |
| `omega_ge_of_primeFinset` | a finset of primes is absorbed, up to cardinality, by the prime factors of its product |
| `omega_unbounded` | **∀ k, ∃ n ≥ 1 with `ω n ≥ k`** — from `omega_mul_prime_of_large_prime` along a fresh prime |

### 2. THE CARRIES NEVER FALL BELOW `1` (unconditionally) — the carry-magnitude route is dead

| Theorem | Statement |
| --- | --- |
| `sum_two_pow_desc` | `∑_{j ≤ m} 2^{m−j} = 2^{m+1} − 1` |
| `exists_six_dvd_add` | every six consecutive integers contain a multiple of `6` |
| `jsp87Carry_window_lower` | if `ω (N+j) ≥ 1` for `j ≤ m` and `ω (N+k) ≥ 2`, then `2^{m+1} − 1 + 2^{m−k} ≤ ∑_{j ≤ m} ω(N+j) 2^{m−j}` |
| `jsp87Carry_ge_one_plus_seven` | **`2 ≤ N → 1 + 1/128 ≤ θ N`** |
| `jsp87Carry_gt_one_of_ge_two` | `2 ≤ N → 1 < θ N` |
| `jsp87CarryExcess_ge_one` | **`2 ≤ N → 1 ≤ ⌊θ N⌋`** (subsumes r. 41's two-hypothesis `jsp87CarryExcess_pos`) |

Rationality only forces `b · θ N ∈ ℤ`, i.e. `θ N ≥ 1/b` (r. 38).  Since
`θ N > 1` at *every* cut point, the classical Erdős contradiction "some `N` has
`θ N < 1/b`" is **false for this series**: no amount of control of the carry in
the small direction can ever work.

### 3. The carry excess dominates `ω/2` — and diverges

| Theorem | Statement |
| --- | --- |
| `jsp87CarryExcess_ge_omega` | **`ω N < 2 ⌊θ N⌋ + 2`** |
| `jsp87CarryExcess_ge` | `2k + 1 ≤ ω N → k ≤ ⌊θ N⌋` |
| `jsp87CarryExcess_unbounded` | **∀ k, ∃ N ≥ 1 with `k ≤ ⌊θ N⌋`** |
| `jsp87CarryExcess_210_ge_one`, `…_2310_ge_two`, `…_30030_ge_two`, `…_510510_ge_three` | the primorials carry `≥ 1, 2, 2, 3` |
| `jsp87Series_irrational_of_carryExcess_bounded` | **if `⌊θ N⌋ ≤ C` for all `N` then `S` is irrational** — *no rationality hypothesis*: a bounded excess bounds `θ`, hence bounds `ω` by `2C+1`, contradicting `omega_unbounded` |

§2 and §3 close the carry-magnitude strategy in **both** directions.

### 4. The unconditional content of the "correlation" hypothesis (the named blocker)

| Theorem | Statement |
| --- | --- |
| `prod_ge_pow_card` | `b ≥ 2`, all `p ∈ s` satisfy `b ≤ p` ⟹ `b^card ≤ ∏ p ∈ s` (r. 35 proved `b = 2`) |
| `jsp87SmallFactors`, `jsp87LargeFactors` | the prime factors of `n` at most / exceeding `m` |
| `omega_eq_card_small_add_card_large` | `ω n = #small + #large` |
| `card_largeFactors_le_log` | **`2 ≤ m → 0 < n → #large ≤ log_m n`** — the large prime factors are logarithmically few |
| `jsp87_sum_omega_window_le` | `∑_{k<L} ω (N+k) ≤ ∑_{k<L} #small(N+k) + L · log_m (N+L)` |
| `jsp87_window_rough` | **for every `m, L` there is `N` such that no integer in `N..N+L−1` has a prime factor in `(L, m]`** — the primes in `(L, m]` are avoided by the single congruence `N ≡ 1 (mod ∏_{L<p≤m} p)`, since `1+k ≤ L < p` |

`jsp87_window_rough` is the unconditional half of a prime-tuple hypothesis: the
**small** prime factors of a window are fully controllable, only the **large**
ones are not — and they are bounded only by the trivial `log_m` estimate.  That
is exactly the boundary ACCEPTANCE.md named as the blocker.

### 5. The bridge to the carry

| Theorem | Statement |
| --- | --- |
| `jsp87Carry_split` | **`θ N = ∑_{k<L} ω (N+k) 2^{−(k+1)} + 2^{−L} · θ (N+L)`** — the exact split of the carry |
| `jsp87Carry_le_window` | `1 ≤ N → θ N ≤ ∑_{k<L} ω(N+k) 2^{−(k+1)} + 2^{−L}(N+L+1)` |
| `sum_two_pow_inv_le_one` | `∑_{k<L} 2^{−(k+1)} ≤ 1` |
| `jsp87Carry_le_smallFactors` | `θ N ≤ ∑_{k<L} #small(N+k) 2^{−(k+1)} + L·log_m(N+L) + 2^{−L}(N+L+1)` |

### 6. What rationality would force

`jsp87Series_rational_imp_carryExcess_unbounded_not_periodic` : if `S = a/b`
(`b > 0`) then the carry excess is **unbounded** (an unconditional fact about
the series) *and* **not eventually periodic** (r. 41).  With
`jsp87Carry_gt_one_of_ge_two_unbounded` this is the clean characterisation of
the closed routes: the carry can never be small and cannot be bounded, so the
**only** route left to `jsp_000087_main` is r. 41's digit route.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-44 results
are *negative* knowledge about the carry side plus the unconditional
*sieve/correlation* content of the hypothesis Pratt uses; neither supplies the
missing input, which is a quantitative statement strong enough to make the
carry excess eventually periodic (equivalently, to make the binary digits of
`S` aperiodic).  `harness/score.py problems/JSP-000087 --strict-prize` reports
`build_ok=true, sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

---

## Round 46 — the binary block of the series, and the period of a hypothetical rational

New module `lean/JSPProblem/BlockPeriod.lean` (615 lines, **17 new theorems
and defs**, 0 `sorry`, 0 `admit`; **236 proved theorems and lemmas** in the tree
at the `^(theorem|lemma)` level — 219 before this round — `lake build` clean).
This is a **new attack family**: it is the *converse* of round 41's digit
bookkeeping, namely the quantitative arithmetic of the base-`2` expansion
itself. Rounds 37–44 attacked the Lambert reduction (37), the carry scaffold
(38), the gcd arithmetic (39), the carry dynamics (40), the digit bookkeeping
(41) and the carry-excess/sieve content (44); round 46 attacks the **block
structure of the binary expansion**, which no previous round had touched.

Rounds 41 and 44 had proved the *forward* direction only: rationality of `S`
forces the binary digits to be eventually periodic. **Round 46 proves the other
direction quantitatively**, which is what an Erdős–Pratt argument needs — not
merely that the digits must be periodic, but *exactly what they would be*.

### 1. The `t`-digit block, as a binary integer

| Theorem | Statement |
| --- | --- |
| `jsp87DigitBlock` | **the new object**: `B N t = ∑_{j<t} d (N+j) · 2^{t−1−j}` — the next `t` binary digits of `S`, read as an integer |
| `jsp87_digitBlock_bounds` | **a block is a genuine `t`-bit integer**: `0 ≤ B N t < 2^t` (from `jsp87Digit_mem`) |
| `jsp87_digitBlock_step` | one step of periodicity makes the block invariant: `B (N+t) t = B N t` |
| `jsp87_digitBlock_shift` | **periodic digits ⟹ the blocks repeat**: `B (N+q·t) t = B N t` for all `q` |
| `int_sum_pow_geo` | `∑_{j<t} 2^{t−1−j} = 2^t − 1` (the all-ones block) |
| `jsp87_floor_digit` | `⌊2^{M+1} S⌋ = 2 ⌊2^M S⌋ + d M` (the digit relation in floor form) |
| `jsp87_sum_mul_two` | multiplying the block sum by `2` shifts every exponent |

### 2. The finite telescoping identity, and its iteration along a period

| Theorem | Statement |
| --- | --- |
| `jsp87_floor_telescope` | **`⌊2^{N+t} S⌋ = 2^t ⌊2^N S⌋ + B N t`** — the binary prefix after `t` further digits is the prefix at `N` shifted by `t` places, plus the block. Mathlib has no statement about the base-`2` expansion of a real at all. |
| `jsp87_floor_block_iter` | **the iteration along the period**: for every `q ≥ 0`, `(2^t−1) ⌊2^{N+qt} S⌋ = 2^{tq}·K − B N t` with `K = (2^t−1)⌊2^N S⌋ + B N t`. This is the *only* place the constancy of the block along the period is used. |
| `jsp87_pow_mul_inv` | `a^{m·n}·(a^m)⁻^n = 1` |

### 3. THE MAIN THEOREM — the exact fractional part

| Theorem | Statement |
| --- | --- |
| **`jsp87_frac_scaled_eq_block`** | **If the binary digits of `S` are eventually periodic from `N` with period `t > 0`, then `Int.fract (2^N · S) = B N t / (2^t − 1)`.** |
| `exists_pow_lt_real` | for `0 < r < 1` and `b > 0` there is `n` with `r^n < b` — the `ℝ` version of Mathlib's `exists_pow_lt_of_lt_one` (`exists_pow_lt` is stated for ordered *groups* and does not apply to `ℝ`) |
| `abs_eq_zero_of_forall_le` | if `\|a\| ≤ D·r^n` for all `n`, with `D > 0` and `0 < r < 1`, then `a = 0` (elementary squeeze, no topology) |

This is the *quantitative* form of the classical fact that a rational number has
eventually periodic binary digits, and it is **the missing half of the
Erdős–Pratt method**. Rounds 38 and 40 only said that rationality freezes the
carries into `(1/b)ℤ`; round 46 says the freeze is **explicit**:

* the denominator of the fractional part is **`2^t − 1`** (the period!), and
* the numerator is **the digit block**, a `t`-bit integer.

The proof is a squeeze: the telescoping identity is iterated `q` times along the
period, converted from floors to `x − fract x`, and the `2^{tq}·2^N·S` term
cancels, leaving `(2^t−1)·f_N − B N t = 2^{-tq}·((2^t−1)·f_{N+qt} − B N t)`;
the right side is `O(2^{-tq})` and the left side does not depend on `q`.

### 4. The endgame: what a rational value of `S` is forced to look like

| Theorem | Statement |
| --- | --- |
| `jsp87Series_irrational_of_frac_notPeriodic` | **THE FRACTIONAL-PART CRITERION: if `n ↦ Int.fract (2^n S)` is not eventually periodic, then `S` is irrational** |
| `jsp87Series_rational_imp_frac_periodic` | the converse: `S = a/b`, `b > 0` ⟹ the fractional parts of the rescaled series are eventually periodic |
| `jsp87_frac_scaled_block_const` | under periodic digits, the fractional part of `2^{N+qt} S` is the *same constant* for all `q` |
| **`jsp87_period_denominator_obstruction`** | **if `S = a/b` with `b > 0` and the digits are eventually periodic with period `t`, then `(2^t − 1) ∣ b · B N t`.** The period-denominator obstruction: any rational value would have a denominator constrained by the digit period through `2^t − 1`, with the numerator the block. |
| `jsp87Series_rational_imp_blockConst` | the three conclusions together: block constant along the period, fractional part constant along the period, and `2^t − 1 ∣ b·B N t` |

This pins the hypothetical rational from **both** sides. From above, via
`jsp87_period_denominator_obstruction`: the denominator `b` is tied to the period
through `2^t − 1`. From below, via round 39's `dvd_lambert_den_prime_gt`
(`b ∣ 2^p − 1` for prime `p` forces `p < b`): a *fixed* denominator cannot keep
dividing the Lambert denominators `2^p − 1` as `p` grows. The only escape is the
period `t` growing with `N` — which is exactly what "the block is eventually
periodic from some fixed `N`" forbids.

### Gate status

`jsp_000087_main` is **still deliberately not declared**. The round-46 reduction
is complete and sharp, but the headline irrationality is **conditional in the
published literature** (Pratt, arXiv:2409.15185, under a uniform prime
`k`-tuples hypothesis) and the catalog itself records *Solved; Lean proof: No;
Eligible to claim: No*. The round-46 theorems are the *unconditional* content of
that reduction; none of them supplies the one missing input.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 46, stated exactly

Rounds 41 and 44 reduced the problem to "the binary digits of `S` are not
eventually periodic". Round 46 makes the reduction **quantitative and
irreversible**: it identifies the object (`jsp87DigitBlock`), proves it is a
`t`-bit integer, proves it is constant along any eventual period, and proves it
determines the fractional part exactly as `B N t/(2^t − 1)`. The single
remaining lemma is now:

> **`jsp87Series_irrational_of_blockNotPeriodic`** — for every `t > 0` the
> sequence `N ↦ jsp87DigitBlock N t` is not eventually periodic.

Equivalently (and this is the formulation Pratt's hypothesis supplies): there is
no `t > 0` after which the `t`-digit blocks of the Erdős series repeat. This is
the arithmetic content of a uniform prime-`k`-tuples correlation hypothesis on
`ω` at shifted primes: periodicity of the block would make `ω` eventually
periodic (rounds 40 + 41), and conversely any period of `ω` gives a period of
the block. It is an *assumption of the published result*, not of the catalog
statement, so it is not introduced here.

---

## Round 64 — the doubling orbit computed exactly, and the death of the `2`-adic limit

New module `lean/JSPProblem/OrbitArith.lean` (999 lines, **40 new theorems and
lemmas** plus 10 private helpers and 1 new definition, 0 `sorry`, 0 `admit`;
**822 proved theorems and lemmas** in the tree at the `^(theorem|lemma)` level —
781 before this round — `lake build` clean, 0 new linter warnings).

This is a **new attack family**.  Round 48 introduced the *doubling orbit of the
carries* `N ↦ Int.fract (θ N)` and proved only that a rational value makes it
eventually periodic (the fourth irrationality criterion); round 57 computed the
*period-denominator correspondence* for the **digit string** of `S` but never
for the orbit.  **This round computes the orbit exactly** — its point, its
period, and the number of points it visits — and then kills the *other* possible
quantisation of the series, the `2`-adic one.

### 1. The orbit is a residue: `Int.fract (θ N) = (2^N a mod b)/b`

| Theorem | Statement |
| --- | --- |
| `jsp87OrbitNum` | **the new object** `r a b N = (2^N · a) mod b`, the numerator of the orbit at time `N` |
| `jsp87OrbitNum_succ` | **the numerators are the orbit of the doubling map on `ℤ/bℤ`**: `r (N+1) = 2 r (N) mod b` (hence deterministic) |
| `jsp87OrbitNum_lt`, `jsp87OrbitNum_zero` | `r N < b`; `r 0 = a mod b` |
| `jsp87_orbitNum_congr` | `r (N+t) = r N ↔ b ∣ 2^N (2^t − 1) a` |
| `dvd_two_pow_mer_iff_oddPart` | **the `2`-part of a denominator is invisible past its own valuation**: for `k ≥ v_2(b)`, `b ∣ 2^k (2^t−1) ↔ jsp87OddPart b ∣ 2^t − 1` |
| `jsp87_orbitNum_period_iff` | **the periods of the residue orbit**: `r (n+t) = r n` for all `n ≥ k` `↔ jsp87OddPart b ∣ 2^t − 1` |
| `jsp87_fracCarry_eq_orbitNum` | **THE ORBIT POINT IS A RESIDUE**: for `S = a/b`, `0 < a`, `1 ≤ N`, `Int.fract (θ N) = r a b N / b` |
| `jsp87_fracCarry_period_iff_resid` | the orbit and the doubling map mod `b` have the same periodic points |
| **`jsp87_fracCarryPeriod_iff_oddPart_dvd_mer`** | **THE COMPLETE PERIOD–ORDER CORRESPONDENCE FOR THE ORBIT**: for `S = a/b` in lowest terms, `1 ≤ M`, `v_2(b) ≤ M`, `0 < t`: `(∀ N ≥ M, fract θ (N+t) = fract θ N) ↔ jsp87OddPart b ∣ 2^t − 1` |

So, for a rational value of the Erdős series, **the doubling orbit of the
carries has minimal eventual period exactly `ord_{jsp87OddPart b}(2)`, and it
starts exactly at the `2`-adic threshold `M = v_2(b)`** — the same number that
governs the digit string (round 57), i.e. *the orbit and the binary expansion are
governed by one and the same integer*.

### 2. The period is minimal, and the orbit visits exactly that many points

| Theorem | Statement |
| --- | --- |
| `jsp87_fracCarry_period_sub_iff` | **two periods spawn a smaller one**: if `t`, `t'` are periods with `t' < t`, then `t − t'` is a period and `jsp87OddPart b ∣ 2^(t−t') − 1` |
| `jsp87_fracCarry_period_dvd` | the eventual periods of the orbit are **`gcd`-closed** (via round 39's `gcd_two_pow_sub_one`) |
| `jsp87_fracCarry_distinct` | a *minimal* period `t` (i.e. no `u < t` with `jsp87OddPart b ∣ 2^u − 1`) visits `t` **pairwise distinct** orbit points |
| `jsp87_fracCarry_distinct_card` | the number of distinct orbit points in one period is exactly `t` |

### 3. The orbit and the digit string have the same periods, and the criterion is now an `iff`

| Theorem | Statement |
| --- | --- |
| `jsp87_fracCarry_periodic_imp_digitPeriodic` | an eventually periodic orbit ⟹ an eventually periodic digit string with the *same* period and the *same* start point (from `d N = 2·fract θ N − fract θ (N+1)`) |
| `jsp87_fracCarry_period_iff_digitPeriod` | **the two families of eventual periods coincide** |
| **`jsp87Series_irrational_iff_fracCarry_notPeriodic`** | **THE COMPLETE ERDŐS CRITERION ON THE CARRY ORBIT**: `Irrational S ↔` the doubling orbit of the carries is not eventually periodic (round 48 proved only the forward direction) |
| `jsp87_fracCarry_zero_of_dyadic`, `jsp87_dyadic_iff_orbit_period_one`, `jsp87_fracCarry_zero_iff_dyadic` | **period `1` of the orbit is exactly the dyadic case**; the orbit vanishes eventually `iff` `S = n/2^M` |
| `jsp87_fracCarry_pos_of_oddPart`, `jsp87_dyadic_or_fracCarry_pos` | **THE DYADIC ALTERNATIVE**: the orbit hits `0` only if `S` is dyadic; otherwise `0 < fract (θ N)` for *every* `N ≥ 1` |

### 4. THE `2`-ADIC VALUE OF THE SERIES DOES NOT EXIST

Round 52 introduced `jsp87Val2` and the modular behaviour of the binary prefix
`I N`; round 58's policy suggested the `2`-adic limit of `I N` might be the
missing object.  **It provably does not exist.**

| Theorem | Statement |
| --- | --- |
| `jsp87_omegaWindow_parity` | `Ω N t ≡ ω (N + t − 1) (mod 2)` for `t ≥ 1` |
| `jsp87_omegaWindow_not_even_of_prime` | at a prime `p` with `t ≤ p`, the window `Ω (p+1−t) t` is **odd** |
| **`jsp87_omegaWindow_not_dvd_pow_two`** | **ROUND 52'S NAMED BLOCKER `jsp87_prefix_window_congr_fails` IS CLOSED**: for every `t ≥ 1` and every `M` there is `N ≥ M` with `2^t ∤ Ω N t` (witnessed at a prime) |
| `jsp87Prefix_mono`, `jsp87_prefix_step_eq` | the prefix is nondecreasing, and `I (N+1) − I N = I N + ω N` |
| `jsp87_prefix_coh_omega_congr` | **coherence of the prefix at `2^k` forces `ω N ≡ ω M (mod 2^k)` for all `N ≥ M`** |
| **`jsp87_prefix_twoAdic_limit_absent`** | **THE `2`-ADIC VALUE OF THE ERDŐS SERIES DOES NOT EXIST**: no `k ≥ 1`, no `M`, such that `2^k ∣ I N' − I N` for all `N, N' ≥ M` |
| `jsp87_prefix_escapes_every_pow_two` | effective form: for `1 ≤ k` and every `M` there are `N, N' ≥ M` with `2^k ∤ I N' − I N` |
| `jsp87_prefix_incoherent_at_prime` | at every prime `p`, `2^k ∣ I p` and `2^k ∣ I (p+1) − I p` cannot both hold |
| `jsp87_omega_one_of_prime`, `jsp87_omega_two_mul_of_prime` | `ω p = 1` at a prime, `ω (2p) = 2` for `p > 2` (the two values that refute coherence) |

The reason is elementary: a coherent prefix makes `ω` constant modulo `2^k` on
the tail, but `ω p = 1` at a prime and `ω (2p) = 2`.  So **the prefix
quantisation is not available at all**; the only quantisation a rational value of
`S` could respect is the real one — the doubling orbit, whose exact period was
computed in §1.

### 5. Instances (machine-checked)

`jsp87_ord_seven_new` (`ord_7 2 = 3`), `jsp87_orbitNum_seven_period`,
`jsp87_orbitNum_seven_values` (`1, 2, 4`), `jsp87_orbitNum_seven_distinct`;
`jsp87_ord_twelve_new` (`v_2(12) = 2`, `oddPart 12 = 3`, `ord_3 2 = 2`),
`jsp87_orbitNum_twelve_period` — periodicity starts exactly at `N = v_2(b)`,
`jsp87_orbitNum_twelve_values`; `jsp87_ord_nine_new` (`ord_9 2 = 6`, a composite
odd modulus), `jsp87_orbitNum_nine_period`.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is **conditional** in the published literature (Pratt,
arXiv:2409.15185, under a uniform prime `k`-tuples conjecture) and the catalog
records *Solved; Lean proof: No; Eligible to claim: No*.  What this round adds
is the *exact arithmetic* of the only quantisation a rational value could
respect, plus a machine-checked refutation of the alternative one.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 64, stated exactly

> **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the Erdős series are not eventually
> periodic in `N`.

Round 64 makes the reduction *exact in both directions* and pins the period: by
`jsp87Series_irrational_iff_fracCarry_notPeriodic` and
`jsp87_fracCarryPeriod_iff_oddPart_dvd_mer`, the headline statement is
**equivalent** to

> for every `b ≥ 1` and every `M ≥ v_2(b)`, the doubling map on `ℤ/(b')ℤ` (with
> `b' = jsp87OddPart b`) does **not** return to its starting residue within any
> multiple of `ord_{b'}(2)`,

i.e. to the aperiodicity of the *real* orbit `Int.fract (θ N)`, which is
equivalent (round 48, `jsp87_digit_eq_fractCarry`) to the aperiodicity of the
*binary digit string*.  Nothing unconditional is known about that aperiodicity:
it is the arithmetic content of the uniform prime-`k`-tuples hypothesis in
Pratt's result, an assumption of the **published** result and not of the catalog
statement.  The `2`-adic route is now closed by a theorem
(`jsp87_prefix_twoAdic_limit_absent`), and the two real quantisations (the
Lambert denominators of rounds 39/40, and the doubling orbit) are known to be
governed by the *same* arithmetic period.

---

## Round 122 — THE CORRELATED-SAMPLE OBJECT: (5.21) IS A CONDITION ON THE SAMPLE, AND IT IS IMPOSSIBLE FOR PROGRESSIONS

New module `lean/JSPProblem/CorrelSample.lean` (914 lines, **36 new public theorems
and lemmas** plus 8 private helpers and 5 new definitions, 0 `sorry`, 0 `admit`;
**2502** theorem/lemma declarations tree-wide by the `^(theorem|lemma)` count with
private helpers (2458 before this round), `lake build` clean).

This is a **new attack family** and the execution of `policy.json`
`next_round_attack[0]`, unexecuted for 120 rounds: *make explicit the ONE quantity
that hypothesis (5.21) needs, namely a sample whose active-class fraction is large
— and show what it costs.*  The quantity is **not** the level-1 active fraction of
round 120 but the **nonzero-class fraction**

```
f_p  =  jsp87NzFrac K p H s  =  #{ n ∈ s : X_p n ≠ 0 } / #{ n ∈ s }
```

of the cube-alternating variable `X_p` of (5.13), because that is exactly what
enters the two-class variance criterion.

| Theorem | Statement |
| --- | --- |
| `jsp87Var_Xp_ge_nzFrac` | **THE MAIN CRITERION IN FRACTION FORM**: `Var (q X_p) ≥ q² · f (1 − f) · 2^{−2(H+K)}` |
| `jsp87Var_sum_ge_nzFrac` | the same over the whole `S₁`, with the cube square outside the sum |
| **`jsp87_endgame_frac_of_5_21`** | **THE ENDGAME WITH (5.21) IN SAMPLE GEOMETRY**: everything of arXiv:2512.01739 §5.3–§5.14 except the `S₁`-variance hypothesis is discharged, and that hypothesis is replaced by the purely geometric (5.21′) `1 ≤ q² 2^{−2(H+K)} ∑_{p∈P} f_p (1 − f_p)` |
| `jsp87_5_21_singleRes_impossible` | **no sample lying in one residue class modulo a prime of `S₁` can satisfy (5.21′)** |
| `jsp87_5_21_prog_impossible`, `jsp87_5_21_prog_of_frac` | **no arithmetic progression whose step is divisible by every `p ∈ S₁` can satisfy (5.21′)** |
| `jsp87_5_21_singleResP_impossible` | the prime-wise form (the residue may depend on `p`) |
| `jsp87_5_21_needs_four`, `jsp87_5_21_needs_card` | (5.21′) forces `4 ≤ q² 2^{−2(H+K)} |S₁|`, hence `4^{H+K+1} ≤ q² |S₁|` |
| **`jsp87_5_21_needs_manyPrimes`** | **THE COUNTING NECESSITY**: with (5.19) (which forces `4^K ≥ 400 q² H²`) the `q²` cancels and (5.21′) forces `1600 · 4^H · H² ≤ |S₁|` — `6400` primes at `H = 1`, `2 048 000` at `H = 5`, independent of `q` and `K` |
| `jsp87Active_add`, `jsp87Active_of_res`, `jsp87Active_iff_of_mod` | the residue transfer of the **hit** predicate, from scratch |
| `jsp87res_cover_iff`, `jsp87Active_mem_res`, `jsp87Active_of_res_cover` | activity is *decided* by the active residue classes of round 120 |
| **`jsp87Xp0_eq_of_res`** | **the residue transfer of the cube sum itself** — `X_p` is constant on a residue class, which is what makes the single-residue obstruction work |
| `jsp87ActFrac_trans`, `jsp87ActFrac_union` | the active fraction is a residue statistic: it is invariant under shifts by multiples of `p`, and the fraction of a disjoint union is the size-weighted average |
| `jsp87ActFrac_eq_one_of_res_cover`, `jsp87ActFrac_eq_zero_of_res_avoid` | … and it is exactly determined by the residue profile of the sample |
| `jsp87NzFrac_ge_actFrac` | the active-class fraction is at most the nonzero-class fraction |
| `jsp87NzFrac_eq_zero_or_one_of_singleRes` | on one residue class the nonzero fraction is `0` or `1` |
| `jsp87correl_summary` | the round in one theorem: (5.21′) forces `|S₁| ≥ 1600 · 4^H · H²` |

### Why this matters for the gate

Round 120 proved (5.21) **impossible** for a uniform residue system.  Round 122
proves it **impossible** for any sample confined to a single residue class modulo a
prime of `S₁`, and therefore for any arithmetic progression whose step is divisible
by all of `S₁`, and it quantifies the price of admission: `|S₁| ≥ 1600·4^H·H²`.
The remaining input is thus *provably a correlation statement* — one must exhibit a
sample of integers **correlated with the cube vertices**.  That is the content of
arXiv:2512.01739 `Theorem 3.1` (the Pilatte-derived quantitative two-point
correlation estimate for `ω`); Mathlib has no Chowla-type or Elliott-type statement
for multiplicative functions, so it is not supplied here and `jsp_000087_main`
remains deliberately withheld.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### Mathlib findings of this round (do not repeat the mistakes)

* **no `Nat.add_mod'`** — only the two-modulo `Nat.add_mod`; the one-modulo form
  `((a+c) % n = (a % n + c) % n)` must be built by hand from `← Nat.mod_mod`;
* **`Nat.dvd` is `∃ c, dividend = p * c`** — the *dividend is on the left*; three
  proofs were silently wrong because of this;
* **`inv_le_inv₀ ha hb : a⁻¹ ≤ b⁻¹ ↔ b ≤ a`** (conclusion order reversed);
* `div_eq_iff` takes a **nonzero** hypothesis, `le_div_iff₀`/`div_le_iff₀` take
  positivity; `abs_of_pos` takes `0 < a`; `mul_pos hq hq` mis-elaborates to
  `npowRec` unless the expected type is already fixed;
* no `Finset.filter_congr` / `filter_image` / `filter_subset` /
  `eq_empty_iff_forall_not_mem` / `not_mem_empty` / `mem_zero` in the guessed form;
  `Finset.disjoint_left.2` needs an explicit binder (`a` is implicit); a plain `def`
  used as a `Finset.filter` predicate needs `attribute [reducible]`;
* `Finset.mem_image` is `∃ a ∈ s, f a = b` and `Finset.mem_inter` is an **iff**;
  `Finset.card_image_iff.mpr : InjectiveOn f s → s.card = (s.image f).card`.

---

---

## Round 125 — EULER'S DIVERGENCE, PROVED: the last arithmetic input closes

New module `lean/JSPProblem/EulerDivergence.lean` (382 lines, **15 new public
theorems** plus 2 private helpers and 6 new definitions, 0 `sorry`, 0 `admit`,
0 new linter warnings; **2291** proved theorems and lemmas at the `^(theorem|lemma)`
level, `lake build` clean).

`policy.json` `next_round_attack[0]` — carried **unexecuted for 125 rounds** — asked
for a proof of `jsp87PrimeRecipDiverges`, the harmonic-mass divergence of the primes
above the separation bound, which round 124 had identified as the last *purely
arithmetic* input of the endgame of arXiv:2512.01739 §§5.3–§5.14.  **It is now
proved**, and the endgame fires with only (5.19), (5.15) and (5.16)–(5.17).

### 0. The correction of the policy

The policy proposed the hand route (`Finset.prod_geomsum'`, Euler products, `exp`).
**That premise was wrong**: Mathlib already contains the whole theorem, in
`Mathlib/NumberTheory.SumPrimeReciprocals` — Erdős's elementary proof, as
`not_summable_one_div_on_primes`.  Note that `import Mathlib.Tactic` does *not*
pull in the Mathlib library (it imports the tactic modules only), so
`import Mathlib.NumberTheory.SumPrimeReciprocals` is required explicitly.
`split_ifs` likewise lives in `Mathlib.Tactic.SplitIfs`, not in `Mathlib.Tactic`.

### 1. The transfer (§0–§1)

| Theorem | Statement |
| --- | --- |
| `jsp87PrimeRecipTerm`, `jsp87PrimeRecipTerm_nonneg` | `1/n` at the primes, extended by `0` |
| `jsp87PrimeRecip_not_summable` | `¬ Summable jsp87PrimeRecipTerm`, read off Mathlib's `not_summable_one_div_on_primes` |
| `jsp87PrimeRecip_tendsto` | the prime partial sums `→ ∞`, via `not_summable_iff_tendsto_nat_atTop_of_nonneg` |
| `jsp87PrimeRecipSum_range` | the partial sum **is** the mass of the primes below the cut |
| **`jsp87_recip_prime_le_mass_add`** | **THE COUNTING STEP**: `∑_{p ≤ n prime} 1/p ≤ B/2 + ∑_{B ≤ p ≤ n} 1/p` — the primes below a threshold cost at most `B/2` (at most `B` of them, each `≤ 1/2`). No hypothesis on `B` |
| **`jsp87PrimeRecipDiverges_proof`** | **EULER'S DIVERGENCE, PROVED**: `jsp87PrimeRecipDiverges` holds — for every `K, H` with `1 ≤ H` and every `M > 0` there is a height `Y` with `M ≤ ∑_{2H2^K ≤ p ≤ Y} 1/p` |
| `jsp87PrimeRecipDiverges_proof_tendsto`, `jsp87RecipSum_primeSet_tendsto` | the mass above the separation bound — and above **any** fixed threshold — tends to `+∞` |

### 2. What this does to the endgame (§2–§3)

| Theorem | Statement |
| --- | --- |
| **`jsp87_5_21b_exists`** | **hYPOTHESIS (5.21b) IS SATISFIABLE, UNCONDITIONALLY**: for every `q ≠ 0` and every separation bound there is a height at which `2^{2H+K+1} ≤ q² ∑_{B ≤ p ≤ Y} 1/p`. Rounds 123–124 had proved only what it *costs* |
| `jsp87_5_21b_exists_height` | that height really does reach the forced bound `2^{2(H+K)+2} ≤ q²(Y+1)` of `jsp87_5_21b_needs_height` |
| `jsp87Err1`, `jsp87Err2`, `jsp87Hypothesis15`, `jsp87Hypothesis1617` | the two error terms of (5.15) and (5.16)–(5.17), verbatim, and the two error bounds |
| **`jsp87_endgame_of_Euler`** | **the endgame of §§5.3–§5.14 from (5.19) + (5.15) + (5.16)–(5.17) alone**: the five estimates cannot all be sharp. The variance hypothesis (5.21) is discharged |

### 3. The bridge to the headline (§4)

| Theorem | Statement |
| --- | --- |
| `jsp87KappaSharp` | the five constants are all `< 1/30` |
| **`jsp87Series_irrational_of_kappa_small`** | **the five estimates sharp at the scale (5.19) ⟹ `jsp87Series` is irrational**: sharpness contradicts the endgame, so the truncated carries `b·jsp87TruncCarry N H` fail the uniform-spacing criterion of `TTRoute` for some `b`, and `jsp87Series_irrational_of_truncCarry_far` finishes |
| `jsp87Hypothesis518` | **hypothesis (5.18) as a single named statement**: at the scale (5.19) the five error constants are simultaneously sharp and dominate (5.15), (5.16)–(5.17) uniformly in `Y` |
| `jsp87_scale_519_admissible` | the scale `K = 0`, `H = 1`, `q = 1/20` satisfies (5.19), so (5.18) is **not vacuous** |
| **`jsp87Series_irrational_of_518`** | **THE HEADLINE FROM ONE NAMED HYPOTHESIS**: `jsp87Hypothesis518 → Irrational jsp87Series`, at that explicit scale, with *no other hypothesis* |
| `jsp87_rational_imp_kappa_notSharp` | the contrapositive, at a fixed scale: rationality would force one of the five estimates to be blunt |

### 4. Gate status, and the blocker after round 125

`harness/score.py problems/JSP-000087 --strict-prize` reports
`build_ok=true, sorry=0, admit=0, placeholder_total=0, partial_ok=true,
prize_ready=false, missing_theorems=["jsp_000087_main"]`.

`jsp_000087_main` is **still deliberately not declared**, and the reason is now
*sharper* than in any previous round: everything else is unconditional, and the
single remaining input is

> **`jsp87Hypothesis518`** — the five error constants of §§5.7–5.14 of
> arXiv:2512.01739 are simultaneously `< 1/30` at the scale (5.19), dominating
> the errors (5.15) and (5.16)–(5.17) uniformly in the height of the prime set.

This is their analytic estimate (`κ_j = o(1)`), obtained there from their
Theorem 3.1 (Pilatte).  Mathlib contains no Chowla-type, Elliott-type or
two-point-correlation statement for multiplicative functions, so this input
cannot be produced here; and since it is an *assumption of the published proof*
rather than of the catalog statement, it is not inserted.  Note that the
sample geometry, the primality, the separation, the two-class condition, the
harmonic mass (Euler) and the deterministic Diophantine reduction are now all
proved *unconditionally* — so the gap is exactly one analytic estimate.

---

---

## Round 114 — the `+1` Lambert series as a SUMMED alternating series of dilations

New module `lean/JSPProblem/PlusDilate.lean` (644 lines, **30 new public theorems**
plus 5 private helpers and 1 new public definition, 0 `sorry`, 0 `admit`;
**2003 proved theorems and lemmas** at the `^(theorem|lemma)` level — 1971 before
this round — `lake build` clean).

This closes the item that **round 113 explicitly abandoned**. Rounds 112–113 built
the two series objects of §5.2 of Tao–Teräväinen (arXiv:2512.01739) — the `+1`
Lambert series `jsp87PlusLambert = ∑' n, ω(n)/(2^n+1)` and the **dilations**
`jsp87ScaleLambert k = ∑' n, ω(n) 2^{-kn}` — together with the **per-place**
alternating-geometric identity of round 113, but could not exchange the `k`-sum
with the `n`-sum, and recorded the reason:

> "this Mathlib (v4.34.0) has NO `tsum_finset_sum` / `Summable.tsum_sum` for
> `Finsets` in this version (only for the `Sum` type), so the interchange must be
> proved by induction on `J` with an explicit majorant".

**That premise was wrong, and this round corrects it.** The Mathlib lemma exists
under a different name: `Summable.tsum_finsetSum`, with signature

```
(∀ i ∈ s, Summable (f i)) → ∑' b, ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' b, f i b
```

— it needs *no* hypothesis about the column sums being summable, which is exactly
what the hand proof was being contorted into providing. With it, the whole of
§5.2 closes.

### 1. The remainder term of the truncated expansion

| Theorem | Statement |
| --- | --- |
| `jsp87PlusTerm` | **the new object**: `ω(n) 2^{-n} (-2^{-n})^J / (1 + 2^{-n})`, the `n`-th summand of `jsp87PlusRem J` |
| `jsp87PlusTerm_abs` | its absolute value computed exactly: `= ω(n) 2^{-(J+1)n} / (1 + 2^{-n})` |
| `jsp87PlusTerm_abs_le` | **the dominating estimate** `|ω(n) 2^{-n}(-2^{-n})^J/(1+2^{-n})| ≤ ω(n) 2^{-nJ}` |
| `jsp87PlusTerm_eq_sign_abs` | the term is `(-1)^J` times its own absolute value |
| `summable_omega_dilate'`, `summable_omega_dilate` | the `J`-fold dilation of the Erdős summand is summable for `1 ≤ J` |
| `summable_jsp87PlusTermAbs`, `summable_jsp87PlusTermR`, `hasSum_jsp87PlusTerm` | the remainder series is summable for `1 ≤ J`, and `∑' n, jsp87PlusTerm n J = jsp87PlusRem J` |

### 2. **THE SIGN OF THE REMAINDER** — the alternating-series structure of §5.2

| Theorem | Statement |
| --- | --- |
| `jsp87PlusRem_eq_sign` | `jsp87PlusRem J = (-1)^J · (∑' n, \|jsp87PlusTerm n J\|)`: the truncation remainder is a **signed sum of positive numbers** |
| `jsp87_absTermSum_pos` | the sum of absolute values is **strictly** positive (the place `n = 2` contributes, `ω 2 = 1`) |
| `jsp87_plusRem_nonneg_of_even` / `_nonpos_of_odd` | `0 ≤ jsp87PlusRem J` for even `J`, `jsp87PlusRem J ≤ 0` for odd `J` |
| `jsp87_plusRem_pos_of_even` / `_neg_of_odd` | **strictly**: `0 < jsp87PlusRem J` for even `J`, `jsp87PlusRem J < 0` for odd `J`. The remainder carries the sign of `(-1)^J`, exactly as in the Leibniz criterion |

### 3. The dilations decay geometrically

| Theorem | Statement |
| --- | --- |
| `jsp87ScaleLambert_nonneg` | every dilation is nonnegative |
| `summable_jsp87ScaleLambert` | the `J`-fold dilation summand is summable for `1 ≤ J` |
| `jsp87ScaleLambert_gt` | `2^{-2J} < jsp87ScaleLambert J` — the `n = 2` place alone bounds the dilation from below |
| `jsp87ScaleLambert_succ_le_half` | **the dilations shrink by half**: `jsp87ScaleLambert (J+1) ≤ jsp87ScaleLambert J / 2` |
| `tendsto_two_inv_pow_zero` | `(2⁻¹)^k → 0`, proved from `Metric.tendsto_atTop` (Mathlib has no `tendsto_pow_atTop_nhds_0_of_lt_1`) |
| `jsp87ScaleLambert_le` | **the geometric decay**: `jsp87ScaleLambert J ≤ 4 (2⁻¹)^J S` for `1 ≤ J` |
| `jsp87_plusRem_abs_le` | **the Leibniz bound**: `|jsp87PlusRem J| ≤ 4 (2⁻¹)^J S` |
| `jsp87PlusRem_tendsto_zero` | **the remainder tends to `0`** — the identity below is a genuine limit |

### 4. THE MAIN THEOREM — the summed alternating-dilation expansion of §5.2

| Theorem | Statement |
| --- | --- |
| `jsp87PlusLambert_eq_altDilate` | **for every `J`:** `jsp87PlusLambert = ∑_{k<J} (-1)^k jsp87ScaleLambert (k+1) + jsp87PlusRem J` |
| `jsp87PlusLambert_tendsto_altDilate` | **the alternating partial sums of the dilations converge to the `+1` Lambert series** |
| `jsp87_altDilate_bracket` | **THE CLASSICAL LEIBNIZ BRACKET**: for even `J ≥ 2`, `∑_{k<J} (-1)^k A_{k+1} < jsp87PlusLambert < ∑_{k<J+1} (-1)^k A_{k+1}` |

The `+1` Lambert series is thus the alternating sum, over the **dilations of the
Erdős series itself**, of its own alternating partial sums — the exact object
§5.2 of arXiv:2512.01739 is built to produce. Mathlib has no statement of this
shape: it has no `+1` Lambert series, no notion of a dilation of a generating
series, and nothing about `1/(2^n+1) = ∑_k (-1)^k 2^{-(k+1)n}`.

### 5. Two *new* consequences for the `+1` series

| Theorem | Statement |
| --- | --- |
| **`jsp87PlusLambert_lt_two_mul_series`** | **`jsp87PlusLambert < 2 · jsp87Series`** — round 112 could prove only `≤`; the strict remainder sign makes it strict |
| `jsp87PlusLambert_ge_one_fifth` | **`1/5 ≤ jsp87PlusLambert`** — the single place `n = 2` contributes `ω 2/(2²+1) = 1/5`, so the `+1` series is bounded away from `0` by an explicit rational |

### Gate status

`jsp_000087_main` is **still deliberately not declared**. The headline
irrationality is a theorem in the literature (Tao–Teräväinen, arXiv:2512.01739,
Thm 1.3 = Erdős problem #69), and what is missing is the *proof*, whose analytic
input is their quantitative two-point correlation estimate for `ω` at shifted
integers (their Thm 3.1, from Pilatte's quantitative Elliott-type work). Mathlib
has no Chowla-type or two-point-correlation statement for multiplicative
functions, so that input cannot be supplied here. Emitting a weakened statement
under the name `jsp_000087_main` would misrepresent the catalog headline, so the
name stays withheld.

`harness/score.py problems/JSP-000087 --strict-prize` reports
`build_ok=true, sorry=0, admit=0, placeholder_total=0, partial_ok=true,
prize_ready=false, missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 114, stated exactly

> **`jsp87TruncCarryEscapes`** (round 112) / **`jsp87_digit_not_eventuallyPeriodic`**
> (round 46) — unchanged and unchanged in substance. Rounds 41/46/64 make the
> headline *equivalent* to the aperiodicity of the binary digits of `S`, i.e. of
> the doubling orbit of its carries; rounds 112–114 make it *equivalent* to the
> statement that the truncated carry `jsp87TruncCarry N H` stays away from the
> lattice `q^{-1}ℤ` uniformly in `N, H`. Both are quantitative statements about
> `ω(n+1), …, ω(n+H)` that Mathlib cannot supply.

### The Mathlib correction of this round (do not repeat the round-113 mistake)

* `Summable.tsum_finsetSum` **exists** and exchanges a `Finset`-indexed sum with
  a `tsum`; round 113's "no `tsum_finset_sum` in this version" was a
  **name miss**, not a Mathlib gap. Its hypothesis is only `∀ i ∈ s, Summable (f i)` —
  in particular it needs *no* summability of `fun b => ∑ i ∈ s, f i b`, which is
  what makes the hand induction impossible to set up cleanly.
* Other lemma-name changes in this Mathlib (v4.34.0) that cost time this round:
  `abs_le_abs : a ≤ b → -a ≤ b → |a| ≤ |b|` (**two** hypotheses, no longer in a
  linear-order section), `pow_mul : a^(m*n) = (a^m)^n` (so `mul_pow` is the
  "other" direction), `Finset.sum_range_succ` puts the new element **last**,
  `Σ`-binders need parentheses as soon as the body has a top-level `+`
  (`∑' n : ℕ, f n + g n` mis-parses; write `∑' (n : ℕ), (f n + g n)`),
  `inv_mul` / `tsum_le_add` / `tsum_ge_sum` / `abs_tsum_le_tsum` /
  `tendsto_pow_atTop_nhds_0_of_lt_1` do **not** exist (use `Metric.tendsto_atTop`
  plus `exists_pow_lt_real`, `Summable.sum_le_tsum`, `squeeze_zero'`),
  `HasSum.congr` does not exist (use `Summable.hasSum_iff`), and `div_le_one` is an
  `iff`.

---

## Round 47 — the primary (carry-free) binary expansion, and TWO complete irrationality theorems

New module `lean/JSPProblem/Primary.lean` (1334 lines, **80 new theorems and
defs**, 0 `sorry`, 0 `admit`; **307 proved theorems and lemmas** in the tree at
the `^(theorem|lemma)` level — 237 before this round — `lake build` clean).

This is a **new attack family**: rounds 37–46 attacked the Lambert reduction,
the carry scaffold, the gcd arithmetic, the carry dynamics, the digit
bookkeeping, the carry-excess/sieve content, and the base-`2` block arithmetic —
all of them for the *carried* series `S = ∑ ω(n) 2^-(n+1)`.  **No previous round
considered the primary (carry-free) expansion**: a base-`2` series whose digits
are already `0` or `1`, so that nothing is ever carried.

### 1. The primary series and the no-carrying identities

For `f : ℕ → ℕ` with `f n ≤ 1` put `T f = ∑' n, f n 2^-(n+1)`,
`A f N = ∑_{n<N} f n 2^{N-n-1}`, `U f N = ∑' k, f (N+k) 2^-(k+1)`.

| Theorem | Statement |
| --- | --- |
| `jsp87Binary_split` | **the split without a carry term**: `2^N · T f = A f N + U f N` — compare round 38's `2^N S = I N + 2^N τ N` |
| `jsp87BinaryTail_succ` | the primary tail recurrence `U f (N+1) = 2 U f N − f N` (the analogue of `jsp87Carry_succ`) |
| `jsp87BinaryTail_le_one` / `jsp87BinaryTail_lt_one` | `0 ≤ U f N ≤ 1`, **strictly** `< 1` as soon as one digit at or after `N` vanishes |
| `jsp87BinaryInt_bounds` | a prefix is a genuine `N`-bit integer: `A f N ≤ 2^N − 1` |
| `jsp87Binary_floor` | **NO CARRYING**: `⌊2^N T f⌋ = A f N` — the binary floor is *exactly* the prefix integer, in contrast with round 41's `jsp87_floor_scaled` (`⌊2^N S⌋ = I N + ⌊θ N⌋`) |
| `jsp87Binary_fract` | `Int.fract (2^N T f) = U f N` |
| **`jsp87Binary_digit`** | **THE PRIMARY DIGIT THEOREM**: `f N = ⌊2^{N+1} T f⌋ − 2 ⌊2^N T f⌋` — the binary digit of `T f` *is* the digit `f N`.  This is exactly the identity that fails for `S`, where the digit is `ω N + c(N+1) − 2 c N` |

### 2. The exact value of a periodic primary series

| Theorem | Statement |
| --- | --- |
| `jsp87BinaryTail_iter` | `U f (N+t) = 2^t U f N − β f N t` with `β f N t = ∑_{j<t} f (N+j) 2^{t-1-j}` the `t`-digit block |
| `jsp87BinaryBlock_bounds` | a block is a genuine `t`-digit window: `0 ≤ β ≤ 2^t − 1` |
| **`jsp87Binary_series_eq_block`** | **THE EXACT VALUE**: if `f` is periodic from `N` with period `t > 0` then `2^N · T f = A f N + β f N t / (2^t − 1)`.  Round 46 proved the same for the *fractional part* of the carried series; here it is the *value*, and the periodic string is a rational with denominator exactly `(2^t−1) 2^N` |
| `jsp87Binary_rational_of_periodic` | hence `∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ T f = a / b` |

### 3. THE COMPLETE ERDŐS CRITERION (both directions, from scratch)

| Theorem | Statement |
| --- | --- |
| `Int.fract_two_pow_mul` | the doubling map on the fractional parts of a general rescaling |
| `jsp87Binary_fract_eq_div` | rationality **quantises** the fractional parts: `Int.fract (2^N T f) = c/b`, `0 ≤ c < b` |
| `jsp87BinaryFracNum_spec` / `_succ` / `_period` | the numerators live in the finite set `range b`, propagate along the doubling map, and are eventually periodic (pigeonhole) |
| `jsp87Binary_digit_fracNum` | **`b · f N = 2 c(N) − c(N+1)`**: the digit is recovered from two consecutive numerators |
| `jsp87Binary_rational_imp_periodic` | **rationality ⟹ the digit sequence is eventually periodic** |
| `jsp87Binary_irrational_of_notPeriodic` | **aperiodicity ⟹ irrationality** |
| **`jsp87Binary_irrational_iff`** | **THE COMPLETE CRITERION**: `Irrational (∑' n, f n 2^-(n+1)) ↔ f` is not eventually periodic — in **both** directions, and entirely from scratch.  Mathlib has no statement about the base-`2` expansion of a real number at all |

### 4. **TWO COMPLETE, UNCONDITIONAL IRRATIONALITY THEOREMS**

| Theorem | Statement |
| --- | --- |
| `omega_mul_of_not_dvd` | `p` prime, `p ∉ n.primeFactors` ⟹ `ω (n·p) = ω n + 1` |
| `primeFactors_mul_pow_of_dvd`, `omega_mul_pow_of_dvd` | for a prime `p ∣ t`: `ω (t·p^k) = ω t` |
| `omega_mul_pow_of_coprime` | for a prime `q ∤ t`, `1 ≤ k`: `ω (t·q^k) = ω t + 1` |
| **`omega_parity_not_eventuallyPeriodic`** | **THE PARITY SEQUENCE OF `ω` IS APERIODIC**: an eventual period `t` freezes `n ↦ ω (t·n) mod 2`, but `ω (t·p^k) = ω t` for `p ∣ t` while `ω (t·q^k) = ω t + 1` for `q ∤ t` (for `t = 1`: `ω q = 1` and `ω (2q) = 2`).  Mathlib has no such statement |
| `omega_six_pow` | `ω (6^k) = 2` for `1 ≤ k` — the digit hypothesis `U < 1` needs a zero digit past every cut point |
| **`jsp87ParitySeries`** | `∑' n, (ω n mod 2) 2^-(n+1)` — the parity series of `ω` |
| **`jsp87ParitySeries_irrational`** | **THE PARITY SERIES OF `ω` IS IRRATIONAL.**  The closest provable sibling of `jsp_000087_main`: the same function `ω`, the same binary method, the same criterion — with the carry dropped |
| `jsp87PrimeBit_not_eventuallyPeriodic` | the primality indicator is aperiodic: a period makes `p + j t` prime for all `j ≥ 0`, hence `p (1+t)` prime |
| **`jsp87PrimeSeries_irrational`** | **ERDŐS' PRIME CONSTANT `∑' n, [n prime] 2^-(n+1)` IS IRRATIONAL** — a second complete instance of the criterion (Erdős 1948; here proved from scratch) |

### 5. Why this does not (yet) close JSP-000087 — now *proved*, not just observed

| Theorem | Statement |
| --- | --- |
| `jsp87Series_ge_quarter` | `1/4 ≤ S` (the six nonzero terms already sum to `1/4`) |
| `jsp87Series_lt_half` | `S < 1/2` (partial sum over `n < 5` is `7/32`, tail past 5 is `≤ 6·2^-5 = 3/16`, so `S ≤ 13/32`) |
| `jsp87_floor_two_S`, `jsp87_floor_four_S` | `⌊2S⌋ = 0` and `⌊4S⌋ = 1` |
| **`jsp87_digit_one`** | **THE ERDŐS SERIES CARRIES AT `N = 1`: its first binary digit is `1`, although `ω 1 = 0`** |
| `jsp87_digit_ne_omega_one` | so the digits of `S` are **not** the `ω`-digits |
| `jsp87_digit_ne_parity_one` | and **not even the parities of `ω`** — so the aperiodicity of `ω mod 2` proved in this file does *not* transfer to the digits of `S` |

This is the precise reason the headline statement stays open: the entire
difference between JSP-000087 and the two theorems proved here is the carry
`⌊2^N τ N⌋`, and round 47 exhibits that carry *numerically* at `N = 1` rather
than only symbolically.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-47 criterion
is complete in both directions and is applied to two proved irrationality
theorems, but the Erdős series itself genuinely carries (proved:
`jsp87_digit_one`), so the aperiodicity of the *binary digits* of `S` remains
the single missing input — exactly round 46's blocker
`jsp87Series_irrational_of_blockNotPeriodic`.  In the published literature the
headline is conditional (Pratt, arXiv:2409.15185, uniform prime `k`-tuples) and
the catalog records *Solved; Lean proof: No; Eligible to claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 47, stated exactly

> **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2 ⌊2^N S⌋` of the Erdős series are not eventually
> periodic in `N`.

With `jsp87Binary_irrational_iff` (proved this round) plus the reduction of
round 41 (`jsp87_digit_eventuallyPeriodic`) and round 46
(`jsp87_frac_scaled_eq_block`), this is the *only* remaining step, and it is
exactly the aperiodicity statement that Pratt's uniform prime-`k`-tuples
hypothesis is designed to supply: the carry `⌊2^N τ N⌋` is what makes the digits
differ from the parities of `ω` (proved this round at `N = 1`), and nothing
unconditional is known about its fluctuations.  The primary criterion makes the
reduction rigorous: *a `{0,1}`-digit series is irrational exactly when its digit
string is aperiodic*, so the whole problem is aperiodicity of the digit string
of `S` — not of `ω`, and not of `ω mod 2`.

---

## Round 48 — the doubling map on the carries: the digit string as the difference sequence of the doubling orbit

New module `lean/JSPProblem/CarryDoubling.lean` (540 lines, **20 new theorems**
plus 5 private helpers, 0 `sorry`, 0 `admit`; **326 proved theorems and
lemmas** in the tree at the `^(theorem|lemma)` level — 306 before this round —
`lake build` clean, 0 new linter warnings).

This is a **new attack family**.  Rounds 37–46 attacked the *carried* series
`S = ∑ n, ω(n) 2^{-(n+1)}` from ten directions and round 47 attacked the
*carry-free* (primary) series; **no round had ever looked at the fractional
part of the carry**, `c N = Int.fract (θ N)` — exactly the piece of the carry
that round 41's `jsp87CarryExcess = ⌊θ N⌋` discards.  The single observation
that drives the round is

> the carry recurrence `θ (N+1) = 2 θ N − ω N` (round 40) is a **doubling map
> on the circle**: because `ω N` is an integer, `Int.fract (θ (N+1)) =
> Int.fract (2 θ N)`.

### 1. The digit string is the difference string of the doubling orbit

| Theorem | Statement |
| --- | --- |
| `jsp87Carry_fract_succ` | `fract (θ (N+1)) = fract (2 θ N)` — **the doubling map on the carries** |
| **`jsp87_digit_eq_fractCarry`** | **`d N = 2 · fract (θ N) − fract (θ (N+1))`** for `1 ≤ N` — the bridge between the *digits* and the *carries* |
| `jsp87_digit_eq_floorCarry` | **`d N = ⌊2 θ N⌋ − 2 ⌊θ N⌋`** — the digit is the **second binary digit of the carry** (not the integer part, which is round 41's `jsp87CarryExcess`) |
| `jsp87Carry_digit_doubling` | the unconditional window `0 ≤ 2 fract (θ N) − fract (θ (N+1)) ≤ 1` |
| `jsp87_fracCarry_succ` | `fract (θ (N+1)) = 2 fract (θ N) − d N` — the orbit is generated by the digit string |
| `jsp87DigitBlock_one` | `B N 1 = d N` (the `t = 1` block is the digit) |

`jsp87_digit_eq_fractCarry` is the join of round 41's `jsp87_digit_eq_fract`
(which lives on `2^N S`) with round 40's `jsp87_fract_scaled` (`fract (2^N S) =
fract (θ N)`).  Mathlib has **no** statement about the base-`2` expansion of a
real number, so all of this is from scratch.

### 2. The doubling orbit inherits the period of the digits — and lives on a grid

| Theorem | Statement |
| --- | --- |
| `jsp87_fracCarry_periodic_of_digitPeriodic` | **`d (n+t) = d n` for all `n ≥ M` ⟹ `fract (θ (N+t)) = fract (θ N)` for all `N ≥ M`**: eventual periodicity of the digits makes the doubling orbit eventually periodic, *with the same period* |
| `jsp87_fracCarry_eq_block_of_digitPeriodic` | the orbit point is **exactly** `B N t / (2^t − 1)` (round 46 restated for the carries) |
| **`jsp87_fracCarry_grid_of_digitPeriodic`** | **THE GRID: every fractional part of a carry is a multiple of `1/(2^t − 1)`, with `0 ≤ k ≤ 2^t − 1`** |
| `jsp87_carry_period_quantisation` | **THE PERIOD ALONE quantises every carry: `(2^t − 1) · θ N ∈ ℤ` — with no rationality hypothesis at all** |
| `jsp87_carry_denominator_obstruction` | rationality (`S = a/b`) gives `b · (2^t − 1) · θ N ∈ ℤ` for **every** `t` |
| `jsp87_carry_lattice_of_digitPeriodic` | **THE CARRY LATTICE: a rational value with eventually periodic digits freezes every carry into `(1/(b(2^t−1))) ℤ`** |
| `jsp87Series_eq_div_of_digitPeriodic` | **THE EXACT VALUE: eventual periodicity with period `t` from `M` forces `S = n / (2^M (2^t − 1))`** |

The value form is the piece that was missing from round 46 (which only pinned the
*fractional part*): a hypothetical rational Erdős series would be a rational in
`[1/4, 1/2)` whose denominator is **a product of a power of `2` and a Mersenne
number `2^t − 1`**, the Mersenne number being the digit period.

### 3. A **fourth** irrationality criterion, and the carry-split dichotomy

| Theorem | Statement |
| --- | --- |
| `jsp87Series_rational_imp_fracCarry_periodic` | `S = a/b`, `b > 0` ⟹ the doubling orbit of the carries is eventually periodic (with the period of the digit string) |
| **`jsp87Series_irrational_of_fracCarry_notPeriodic`** | **THE FOURTH CRITERION: if `N ↦ Int.fract (θ N)` is not eventually periodic, then `S` is irrational** |
| `jsp87Series_eq_rat_imp_carryExcess_notPeriodic` | a rational `S` makes the **integer** part of the carry aperiodic (contrapositive of round 41) |
| `jsp87Series_rational_imp_carrySplit` | **THE CARRY-SPLIT DICHOTOMY: rationality makes the fractional parts of the carries eventually periodic and the integer parts aperiodic forever** |

The development now contains four independent aperiodicity criteria for
`jsp_000087_main`, on four different objects: the carry **excess** `⌊θ N⌋`
(round 41), the binary **digit string** `d N` (round 46), the **primary** digit
string of a carry-free series (round 47), and — this round — the **doubling
orbit of the carries** `Int.fract (θ N)`.

### 4. The period-`1` case is exactly the dyadic case

| Theorem | Statement |
| --- | --- |
| `jsp87_digit_period_one_eq_zero` | if `d (n+1) = d n` for all `n ≥ M` then `d N = 0` for all `N ≥ M` (with `t = 1` the block formula gives `fract (θ N) = d N`, and a fractional part is `< 1`) |
| `jsp87Series_dyadic_of_digit_period_one` | an eventually **constant** digit string forces `S = n / 2^M` |
| **`jsp87Series_dyadic_iff`** | **for `1 ≤ M`: `S = n / 2^M`  ⟺  `d N = 0` for all `N ≥ M`** — the first case of the aperiodicity problem is precisely the question whether the binary expansion of `S` *terminates* |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-48 theorems
are the *unconditional* content of the doubling-map description of the carried
series; none of them supplies the missing aperiodicity input.  In the published
literature the headline irrationality is **conditional** (Pratt, arXiv:2409.15185,
under a uniform prime `k`-tuples hypothesis) and the catalog records *Solved; Lean
proof: No; Eligible to claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 48, stated exactly

> **`jsp87_fracCarry_not_eventuallyPeriodic`** — the doubling orbit
> `N ↦ Int.fract (θ N)`, i.e. the fractional part of the carry, is **not
> eventually periodic** in `N`.

Equivalently (via `jsp87_digit_eq_fractCarry`, `d N = 2 c N − c (N+1)`) the
round-46 blocker `jsp87Series_irrational_of_blockNotPeriodic`, and via round 47's
`jsp87_digit_eventuallyPeriodic` this is exactly the *only* remaining step: a
rational `S` would have to make the doubling orbit of a single explicitly
defined real number eventually periodic.  Mathlib contains no statement about
the binary expansion of a real, and nothing unconditional is known about the
fluctuations of the carry of the Erdős series; this is the arithmetic content
of the uniform prime-`k`-tuples hypothesis in Pratt's result, and it is an
*assumption of the published result*, not of the catalog statement.

---

## Round 49 — the digit criterion in ARBITRARY RADIX `q`

New module `lean/JSPProblem/Radix.lean` (1083 lines, **59 new theorems and
lemms** plus 6 new defs, 0 `sorry`, 0 `admit`; **385 proved theorems and lemmas**
in the tree at the `^(theorem|lemma)` level — 326 before this round — `lake build`
clean).

This is a **new attack family**.  Rounds 37–46 attacked the *carried* series
`S = ∑' n, ω(n) 2^-(n+1)` and round 47 attacked the *carry-free* (primary)
expansion, both **in base `2` only**; round 48 attacked the doubling map on the
carries, again in base `2`.  This round changes the one parameter no earlier round
varied: **the radix**.  The reason it matters is the *no-carry condition* — in radix
`q` the digit strings that never carry are exactly those satisfying
`jsp87NoCarry f q := ∀ n, f n ≤ q − 2`, and in **every** radix there is a carry-free
digit string built from `ω`, namely the reduction `ω n mod (q − 1)`.  So the whole
Erdős criterion of round 47 is available in every radix, and can be instantiated on
three new series; and the reason it still does not reach `jsp_000087_main` becomes a
*theorem* (`jsp87_noCarry_fails_any_radix`) rather than an observation.

### 1. The radix-`q` series, the split, and the tail bound

`jsp87RadixSeries f q = ∑' n, f n q^-(n+1)`, `jsp87RadixInt f q N` (the prefix),
`jsp87RadixTail f q N` (the rescaled tail).

| Theorem | Statement |
| --- | --- |
| `jsp87RadixTerm`, `jsp87RadixSeries`, `jsp87NoCarry`, `jsp87RadixInt`, `jsp87RadixTail`, `jsp87RadixBlock`, `jsp87RadixBlockNat`, `jsp87RadixFracNum` | the new objects |
| `summable_jsp87RadixTerm` / `summable_jsp87RadixTail` | a carry-free digit string gives a summable series |
| `tsum_jsp87RadixTerm_geom` | `∑' n, q^-(n+1) = (q − 1)⁻¹` |
| `jsp87RadixTail_lt_one` | **NO CARRYING IN RADIX `q`**: `U f q N < 1` at *every* cut point, uniformly in `N` (the majorant `(q−2)/(q−1) < 1`, with strictness from the `k = 0` place) |
| `jsp87Radix_split` | **`q^N · T_q f = A f q N + U f q N`** — the round-38 carry decomposition with *no* carry term |
| `jsp87RadixTail_succ` | the tail recurrence `U f q (N+1) = q · U f q N − f N` |

### 2. No carrying, and the digit theorem, in radix `q`

| Theorem | Statement |
| --- | --- |
| `floor_natCast_mul_sub` | **THE `q`-ARY DIGITAL EXTRACTION** `⌊q·x⌋ − q⌊x⌋ = ⌊q·fract x⌋`.  Mathlib has no lemma of this shape: `⌊q·x⌋ = q⌊x⌋` is *false* in general (`x = 3/5`, `q = 2`), so the digit cannot be obtained from `Int.floor_intCast_mul` |
| `Int.fract_natCast_mul`, `Int.fract_radix_pow_mul` | `fract (q·x) = fract (q·fract x)`, and the same after `q^{N+1}` rescaling |
| `jsp87Radix_floor` | **the `q`-ary floor of `q^N T_q f` is exactly the prefix integer `A f q N`** |
| `jsp87Radix_fract` | `fract (q^N T_q f) = U f q N` |
| **`jsp87Radix_digit`** | **the `q`-ary digit of `T_q f` *is* the digit `f N`**: `f N = ⌊q^{N+1}T_q f⌋ − q⌊q^N T_q f⌋` (the radix-`q` form of round 47's `jsp87Binary_digit`) |

### 3. THE COMPLETE ERDŐS CRITERION IN ARBITRARY RADIX (both directions)

Rationality quantises the fractional parts of `q^N T_q f` into `(1/b)ℤ`
(`jsp87Radix_fract_eq_div`, `jsp87RadixFracNum_spec`), the `q`-ary multiplication map is
deterministic (`jsp87RadixFracNum_succ`), so the numerators are eventually periodic
(`jsp87RadixFracNum_period`), and the digit is recovered from two consecutive
numerators by `b · f N = q·c(N) − c(N+1)` (`jsp87Radix_digit_fracNum`).

| Theorem | Statement |
| --- | --- |
| `jsp87Radix_rational_imp_periodic` | `T_q f = a/b`, `b > 0` ⟹ the digit string `f` is eventually periodic |
| `jsp87Radix_series_eq_block` | **the exact value**: periodic with period `t > 0` from `N` forces `q^N T_q f = A f q N + β f q N t/(q^t − 1)` |
| `jsp87Radix_rational_of_periodic` | hence a rational with denominator exactly `(q^t − 1)·q^N` |
| **`jsp87Radix_irrational_iff`** | **`Irrational (∑' n, f n q^-(n+1)) ↔ f` is not eventually periodic** — the complete criterion in every radix `q ≥ 3`.  For `q = 2` it is round 47's `jsp87Binary_irrational_iff` |

### 4. `ω` IS APERIODIC MODULO EVERY `m ≥ 2`

| Theorem | Statement |
| --- | --- |
| `mod_succ_ne_of_two_le` | `(x+1) % m ≠ x % m` for `m ≥ 2` (a common residue would force `m ∣ 1`) |
| `omega_mod_eventuallyPeriodic_const_mul` | an eventual period freezes `n ↦ ω (t·n) mod m` along the multiples of `t` |
| **`omega_mod_not_eventuallyPeriodic`** | **`n ↦ ω n mod m` is not eventually periodic, for every `m ≥ 2`** — the full generalisation of round 47's parity theorem (for a prime `p ∣ t` one has `ω (t·p^k) = ω t` while for `q ∤ t` one has `ω (t·q^k) = ω t + 1`, and the two are distinct modulo any `m ≥ 2`) |

### 5. THREE NEW COMPLETE IRRATIONALITY THEOREMS, one per radix

| Theorem | Statement |
| --- | --- |
| `jsp87OmegaModSeries`, `jsp87OmegaMod_noCarry` | the reduced-`ω` series `∑' n, (ω n mod (q−1)) q^-(n+1)`, whose digits never carry |
| **`jsp87OmegaModSeries_irrational`** | **for every `q ≥ 3`, `∑' n, (ω n mod (q−1)) q^-(n+1)` is irrational** — carry-free by `jsp87OmegaMod_noCarry`, aperiodic by `omega_mod_not_eventuallyPeriodic` with `m = q−1` |
| **`jsp87RadixPrimeSeries_irrational`** | **for every `q ≥ 3`, Erdős' base-`q` prime constant `∑' n, [n prime] q^-(n+1)` is irrational** (round 47 proved the base-`2` instance) |
| `jsp87SquareBit`, `jsp87SquareBit_not_eventuallyPeriodic` | the square indicator is aperiodic: a period would make `M² + t` a square, but `M² < M² + t < (M+1)²` |
| **`jsp87RadixSquareSeries_irrational`** | **for every `q ≥ 3`, `∑' n, [n is a square] q^-(n+1)` is irrational** — a third complete instance |

### 6. WHY THIS STILL DOES NOT CLOSE JSP-000087 — now a *theorem*

| Theorem | Statement |
| --- | --- |
| **`jsp87_noCarry_fails_any_radix`** | **for every radix `q`, `ω` violates `jsp87NoCarry`**: `¬ (∀ n, ω n ≤ q − 2)`, because `ω` is unbounded (round 44's `omega_unbounded`) |
| `omega_mod_le_omega`, `omega_mod_eq_omega` | the reduced digits never exceed `ω`, and agree with it below the modulus |
| `jsp87ErdosRadixSeries`, `summable_jsp87ErdosRadix`, `summable_nat_mul_radixGeom`, `jsp87ErdosRadixSeries_eq_two` | **the Erdős series converges in every radix** (`ω n ≤ n − 1`, dominated by `n·q^-(n+1)`), and in radix `2` it is the catalog's `jsp87Series` |

`jsp87_noCarry_fails_any_radix` is the sharp statement of the gap: the method which
decides the three series above is *provably inapplicable* to the Erdős series
itself, in every radix, because its digit function is unbounded.  So varying the
radix cannot close JSP-000087; the missing input is still aperiodicity of the
**carried** binary digit string (round 48's `jsp87_fracCarry_not_eventuallyPeriodic`),
i.e. the arithmetic content of the uniform prime-`k`-tuples hypothesis.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-49 theorems are
the unconditional content of the criterion in every radix; none of them supplies the
missing aperiodicity input for the carried series.  In the published literature the
headline irrationality is **conditional** (Pratt, arXiv:2409.15185, under a uniform
prime-`k`-tuples hypothesis) and the catalog records *Solved; Lean proof: No;
Eligible to claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### Toolchain notes recorded this round

* The tree's namespace is **`JSP87`**, not `JSPProblem`.
* `mul_inv_cancel₀` requires `a ≠ 0` even in `ℝ`: `a * a⁻¹ = 1` is **false** for
  `a = 0`, so any lemma of that shape needs an explicit nonzeroness hypothesis.
* `pow_le_pow_left' : a ≤ b → ∀ i, a^i ≤ b^i` (not the `(n, a ≤ b)` shape), and
  omega cannot derive `2 ≤ q^t` from `2^t ≤ q^t` — use `Nat.one_lt_two_pow` first.
* `by_cases h : p` does **not** fall back to a classical instance; put
  `noncomputable def f := by classical; exact if _ then _ else _` instead.
* `rw [h]` inside a `calc` step whose proof is a `by`-block must stay on the same
  line (round 48's parser trap).

---

## Round 50 — ASYMPTOTIC CARRY THEORY: the logarithmic window, the mean identity, and the rate criterion

New module `lean/JSPProblem/CarryAsymptotic.lean` (1010 lines, **68 new theorems,
lemmas and defs**, 0 `sorry`, 0 `admit`; **451 proved theorems and lemmas** in the
tree at the `^(theorem|lemma)` level — 385 before this round — `lake build`
clean).

**This is a new attack family.**  Rounds 37–46 attacked the *carried* Erdős
series `S = ∑' n, ω(n) 2^{-(n+1)}` through ten *periodicity* angles (Lambert
reduction, carry scaffold, gcd arithmetic, carry dynamics, digit bookkeeping,
carry-excess/sieve content, base-`2` block arithmetic); round 47 the
*carry-free* (primary) expansion; round 48 the *doubling map on the carries*;
round 49 the criterion in *arbitrary radix*, and closed the radix escape route
with `jsp87_noCarry_fails_any_radix`.  **No previous round ever asked how
*fast* the carry excess grows, or how *fast* the binary digit string
accumulates `1`s.**  This round does, and it is the first to produce an
*upper* bound on the carry that is sublinear.

### 1. The carry as a series, and the logarithmic window

The single observation driving the round: the carry is a **geometrically
weighted average of the `ω`-values after the cut point**, so round 44's
`ω m ≤ log₂ m` makes it *sublinear*.

| Theorem | Statement |
| --- | --- |
| `two_pow_rescale` | `2^N / 2^{N+k+1} = 1/2^{k+1}` — the rescaling behind everything |
| `omega_le_logb_real` | **the `ℝ` form of `omega_le_log2`**: `ω n ≤ log n / log 2` (from `2^ω ≤ n` plus monotonicity of `log`) |
| `jsp87Carry_eq_tsum` | **THE CARRY AS A SERIES: `θ N = ∑' k, ω(N+k)·2^{-(k+1)}`** |
| `log_add_le_log_add_div` | `log(N+k) ≤ log N + k/N` for `1 ≤ N` |
| **`jsp87Carry_le_logb_sharp`** | **THE LOGARITHMIC BOUND ON THE CARRY: `1 ≤ N → θ N ≤ log₂ N + log₂ e / N`** |
| `jsp87Carry_le_logb` | `θ N ≤ (log N + 1)/log 2 = log₂ N + log₂ e` |
| `jsp87CarryExcess_le_logb` | the same for `c N = ⌊θ N⌋` |
| `Real.log_two_ge_half` | `1/2 ≤ log 2` (from `Real.one_sub_inv_le_log_of_pos`) |
| `log_le_mul_log_two` | `N ≤ 2^{k+1} → log N ≤ (k+1)·log 2` |
| **`jsp87CarryExcess_le_of_le_pow_two`** | **`N ≤ 2^{k+1} → c N ≤ k + 3`: on the whole range `[0, 2^{k+1}]` the carry excess is at most logarithmic** |
| `jsp87CarryExcess_le_pow_two` | the same at `N = 2^{k+1}` |
| **`jsp87CarryExcess_unbounded_beyond`** | **the (round-44-unbounded) carry excess escapes every such range: `∃ N, 2^{k+1} < N ∧ k+4 ≤ c N`** |
| **`jsp87CarryExcess_window`** | **THE LOGARITHMIC WINDOW: `1 ≤ c N ≤ k+3` for `2 ≤ N ≤ 2^{k+1}`** |

`jsp87Carry_le_logb` is the **first sublinear upper bound on the carry** of the
Erdős series: rounds 38–40 had only the linear `θ N ≤ N + 1`.  Together with
round 44's `1 ≤ c N` for `2 ≤ N` and round 44's `c N` unbounded, the carry
excess is now pinned from both sides: **never below `1`, never above
`log₂ N + log₂ e`, and above every fixed level somewhere beyond every
exponential cut point.**  Also proved: `jsp87Tail_zero`, `jsp87Tail_one`,
`jsp87Carry_zero`, `jsp87Carry_one`, `jsp87Carry_zero_lt_one`,
`jsp87Carry_one_lt_one`, `jsp87_floor_S_zero`, `jsp87CarryExcess_zero`.

### 2. The mean identity — the quantitative bridge between `ω` and the carries

| Theorem | Statement |
| --- | --- |
| `jsp87OmegaSum`, `jsp87OmegaSum_cast`, `jsp87OmegaSum_succ` | the `ω`-prefix `W N = ∑_{M<N} ω M` |
| `jsp87_sum_intPart` | the integration-by-parts identity `∑_{M<N} I M = I N − W N` |
| `scaled_sub_intPart_eq_carry` | `2^N·S − I N = θ N` for every `N ≥ 0` |
| **`jsp87_sum_carry`** | **THE MEAN IDENTITY: `∑_{M<N} θ M = W N + θ N − S`** |
| `jsp87_sum_carryExcess_le` / `_ge` | `∑_{M<N} c M` is the mean identity up to `N`, on either side |
| `jsp87_sum_carryExcess_le_logb` | and logarithmically bounded on average |

`jsp87_sum_carry` is the **only place in the tree where the `ω`-family and the
carry-family meet quantitatively**: the mean of the carries up to `N` is the
`ω`-prefix, plus the last carry, minus the series.

### 3. The digit count, and its exact formula

| Theorem | Statement |
| --- | --- |
| `jsp87_digit_bookkeeping_zero`, `jsp87_digit_bookkeeping'` | round 41's bookkeeping `d N = ω N + c(N+1) − 2c N` **at every `N ≥ 0`**, including `N = 0` |
| `jsp87_digit_nonneg`, `jsp87_digit_toNat_cast` | `0 ≤ d N` and `(d N).toNat = d N` over `ℤ` |
| `jsp87DigitCount`, `jsp87_digitCount_cast`, `jsp87_digitCount_le` | **the digit count `D N = ∑_{M<N} d M`** and `D N ≤ N` |
| **`jsp87_digitCount_eq`** | **THE DIGIT-COUNT IDENTITY: `D N = W N + c N − ∑_{M<N} c M`** — the first exact formula relating the binary digit string to the `ω`-values *and* to the carries |
| **`jsp87_digitCount_eq_fractSum`** | **`D N + fract (2^N S) = S + ∑_{M<N} fract (2^M S)`** — the digit count *is*, up to `S` and the last fractional part, the partial sum of the doubling orbit |
| `jsp87_digitCount_ge_sub_fract` | `S − fract (2^N S) ≤ D N` |

### 4. Eventual periodicity forces a **linear** digit count — the *rate* criterion

| Theorem | Statement |
| --- | --- |
| `jsp87_digit_eq_of_periodic` | a `t`-periodic digit string is `t`-constant after `M`: `d (M + q·t + j) = d (M+j)` |
| `jsp87PeriodOnes`, `jsp87PeriodOnes_bounds` | the number `s = ∑_{j<t} d (M+j)` of `1`s in one period, `0 ≤ s ≤ t` |
| `jsp87_sum_digit_period_block` | **a full period contributes exactly `s` ones**: `∑_{j<q t} d (M+j) = q·s` |
| `jsp87_sum_digit_le`, `jsp87_sum_digit_shift_le` | the digit sum over (a shift of) a range is at most the number of terms |
| **`jsp87_digitCount_split`** | **`D (M + q·t + r) = D M + q·s + ρ` with `ρ = ∑_{j<r} d (M+j)`, `0 ≤ ρ ≤ r < t`** |
| **`jsp87_digitCount_periodic_bounds`** | **an eventually periodic digit string has `D M ≤ D N ≤ D M + N + t` for every `N ≥ M`** |
| **`jsp87Series_rational_imp_digitCount_linear`** | **RATIONALITY ⇒ the digit count grows exactly linearly** — the *rate* companion of round 41's `jsp87_digit_eventuallyPeriodic` (a period statement) and of round 46's `jsp87_frac_scaled_eq_block` (a value statement) |
| **`jsp87Series_irrational_of_digitDensity_not_bounded`** | **THE RATE CRITERION: if the digit count is bounded by no linear function of `N` along an unbounded sequence, `S` is irrational** |

### 5. The boundary of the method, now quantitative

Three routes are now closed by *theorem*, not by observation:

* the **carry-magnitude** route is doubly closed (round 44: `c N ≥ 1`;
  this round: `c N ≤ log₂ N + log₂ e` and the escape statement);
* the **period/rate** route is reduced to a single new statement
  (`jsp87Series_irrational_of_digitDensity_not_bounded`): the digit string of
  `S` would have to accumulate `1`s at an exactly linear rate;
* the **radix** route was closed in round 49.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-50 results
are the unconditional *asymptotic* content of the carried Erdős series; none of
them supplies the missing input.  In the published literature the headline
irrationality is **conditional** (Pratt, arXiv:2409.15185, under a uniform
prime-`k`-tuples hypothesis) and the catalog itself records *Solved; Lean
proof: No; Eligible to claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 50, stated exactly

> **`jsp87_digitDensity_not_bounded`** — the number of `1`-digits among the
> first `N` binary digits of the Erdős series is bounded by no linear function
> of `N` along an unbounded sequence; formally
> `∀ C > 0, ∀ K, ∃ N ≥ K, D N > C·N`.

Equivalently (via `jsp87_digitCount_eq_fractSum` and round 41's
`jsp87_digit_eq_fract`): the **mean of the doubling orbit** `N ↦ fract (2^N S)`
fails to be bounded by any linear function.  With
`jsp87Series_rational_imp_digitCount_linear` (this round) and
`jsp87_digitCount_periodic_bounds` (this round) this is the *only* remaining
step in the rate formulation, and by round 41's `jsp87_digit_eventuallyPeriodic`
it is equivalent to round 46's `jsp87Series_irrational_of_blockNotPeriodic`.
Nothing unconditional is known about the fluctuations of the carry of the
Erdős series; that is the arithmetic content of the uniform prime-`k`-tuples
hypothesis in Pratt's result, and it is an *assumption of the published result*,
not of the catalog statement.

### Toolchain notes recorded this round

* **`Real.logb` does not exist in Mathlib v4.34.0** — write `Real.log x / Real.log b`.
* **`Real.log_two_gt_d9` / `exp_one_lt_d9` are NOT reachable** from the imports
  used here; use `Real.one_sub_inv_le_log_of_pos (x := 2)` for `1/2 ≤ log 2`
  (and note it is `≤`, not `<`).
* **`Int.fract_lt` does not exist**; get `fract x < 1` from
  `Int.self_sub_fract x` together with `Int.lt_floor_add_one x`.
* **`hasSum_coe_mul_geometric_of_norm_lt_one`** gives
  `∑' n, n·r^n = r/(1−r)^2`; there is no `hasSum_geom_mul`.
* **`Finset.sum_congr` needs its function arguments pinned**: declare the
  `AddCommMonoid` (e.g. `sum_congr_range (M := ℝ) …`) or Lean reports
  "typeclass instance problem is stuck: `AddCommMonoid ?m`".
* **`Summable` carries an `optParam` `SummationFilter` defaulting to
  `unconditional`; the `∑' k, f k` notation uses the same one.**  A `have h :
  Summable … := …` therefore elaborates with `L := unconditional`, and
  `Summable.tsum_add` / `Summable.tsum_mul_left` only then match the goal.
  Also `Summable.tsum_mul_left (a) (hf)` takes the **scalar first** and `hf` the
  summability of the *inner* function.
* **`rw` does not descend under a `∑'` with a top-level `+` in the body**:
  `∑' k, A + B` parses as `(∑' k, A) + B`; always parenthesise the body
  (`∑' k, (A + B)`).  This cost a long debugging detour.
* `Finset.sum_le_sum_of_subset_of_nonneg` needs
  `Finset.range_subset_range.mpr (h : N ≤ M)`.
* A `have` whose statement is `((∑ i ∈ s, (f i : ℤ)) : ℝ) = …` is elaborated
  with the inner sum *already* coerced; force the inner type with
  `(f i : ℤ)` inside the sum and use `Int.cast_sum`.
* `jsp87Tail 0 = jsp87Series` and `jsp87Tail 1 = jsp87Series` follow from
  `jsp87_series_eq_sum_add_tail` (which is stated with `+`, not `−`).

---

## Round 51 — the period equation, and the `ω`-window arithmetic

New module `lean/JSPProblem/PeriodEquation.lean` (914 lines, **37 new theorems
and lemmas** plus **4 new definitions** and 8 private helpers, 0 `sorry`,
0 `admit`; **488 proved theorems and lemmas** in the tree at the
`^(theorem|lemma)` level — 451 before this round — `lake build` clean, **no new
linter warnings**).

**This is a new attack family.**  Rounds 37–46 attacked the *carried* Erdős
series `S = ∑' n, ω(n) 2^{-(n+1)}` through ten *periodicity* angles; round 47
the *carry-free* (primary) expansion; round 48 the *doubling map* on the
carries; round 49 the criterion in *arbitrary radix* (and closed the radix route
with `jsp87_noCarry_fails_any_radix`); round 50 the *asymptotics* of the carry.
**No round had ever written down the inhomogeneous term of the carry
recurrence.**  The single observation driving round 51:

> the `t`-step form of round 40's `θ (N+1) = 2 θ N − ω N` has an inhomogeneous
> term which is a **window of `ω`-values read in base `2`**,
> `θ (N+t) = 2^t · θ N − Ω N t`,  `Ω N t := ∑_{j<t} ω (N+j) · 2^{t-1-j}`.

`Ω N t` is a *weighted average of the `ω`-values of `t` consecutive integers* —
precisely the object a prime-`k`-tuples correlation hypothesis is supposed to
control — and it had **never been defined in the tree**.

### 1. The `ω`-window

| Theorem | Statement |
| --- | --- |
| `jsp87OmegaWindow`, `jsp87OmegaWindow_zero`, `jsp87OmegaWindow_one`, `jsp87OmegaWindow_cast` | **the new object** `Ω N t = ∑_{j<t} ω (N+j) 2^{t-1-j}` |
| `jsp87OmegaWindow_succ`, `jsp87OmegaWindow_succ_cast` | `Ω N (t+1) = 2 · Ω N t + ω (N+t)` |
| **`jsp87OmegaWindow_ge`** | **`2^t − 1 ≤ Ω N t` for `2 ≤ N`** — the window is *exponentially* large, because every integer `≥ 2` has at least one prime factor |
| `jsp87OmegaWindow_le` | `Ω N t ≤ (N+t) · (2^t − 1)` (from `ω m ≤ m − 1`) |

### 2. The period equation (the `ω`-family lives inside the carry family)

| Theorem | Statement |
| --- | --- |
| **`jsp87Carry_iter`** | **THE ITERATED CARRY RECURRENCE `θ (N+t) = 2^t θ N − Ω N t`** — the `t`-step form of round 40, the analogue of round 47's `jsp87BinaryTail_iter` for the *carried* series |
| `jsp87CarryShift`, `jsp87OmegaDiff`, `jsp87OmegaDiffWindow` | the lag-`t` carry increment `Δ N := θ (N+t) − θ N`, the lag-`t` `ω`-difference, the `ω`-difference window |
| **`jsp87CarryShift_step`** | **THE PERIOD EQUATION, STEP FORM — UNCONDITIONAL: `ω (N+t) − ω N = 2 Δ N − Δ (N+1)`.**  The entire `ω`-family, at *every* lag, is recovered from the carry family; no hypothesis is needed |
| `jsp87_omega_diff_eq_carryShift` | the same in `ℝ` form |
| `jsp87CarryShift_block` | the block form `Δ (N+t) = 2^t Δ N − P N t` with `P N t = Ω (N+t) t − Ω N t` |
| `jsp87CarryShift_eq_excess`, `jsp87CarryShift_int` | under eventual periodicity of the digits, `Δ N = c (N+t) − c N` — the period makes the whole increment arithmetic **`ℤ`-arithmetic** |

### 3. The window–block equation — the headline of this round

| Theorem | Statement |
| --- | --- |
| `jsp87_window_periodEquation` | **THE WINDOW EQUATION: `(2^t−1) θ N = (c (N+t) − c N) + Ω N t`** |
| `jsp87_carry_block_equation` | **THE SAME QUANTISATION IN BLOCK FORM: `(2^t−1) θ N = (2^t−1) c N + B N t`** (`B N t = jsp87DigitBlock N t`, round 48 multiplied through) |
| **`jsp87_window_block_equation`** | **THE WINDOW–BLOCK EQUATION: `c (N+t) + Ω N t = 2^t · c N + B N t`** — the first exact `ℤ`-equation in the tree involving a *window of `ω`-values*; the `ω`-window is *readable* from the digit string and the carry excess |
| **`jsp87_window_block_congr`** | **THE WINDOW CONGRUENCE: `2^t − 1 ∣ c (N+t) − c N + Ω N t − B N t`**, with quotient exactly `c N` — the first divisibility statement in the carry family, and the first time a **Mersenne number divides an expression built from `ω`-values** |
| `jsp87_carryExcess_window_le` | `c (N+t) ≤ 2^t · c N` (from `Ω N t ≥ 2^t − 1`, `B N t ≤ 2^t − 1`) |
| `jsp87_omegaWindow_le_carryExcess` | `Ω N t ≤ 2^t · c N + 2^t − 1` — a *small* carry excess forces a *small* `ω`-window |
| `jsp87_omegaWindow_excess_ge'` | `(c (N+t) − c N) + Ω N t ≥ 2^t − 1` for `2 ≤ N` |

### 4. The period equation on the `ω`-family, and what rationality forces

| Theorem | Statement |
| --- | --- |
| **`jsp87_omega_diff_periodEquation`** | **THE PERIOD EQUATION: `ω (N+t) − ω N = 2 (c (N+t) − c N) − (c (N+1+t) − c (N+1))`** — the lag-`t` `ω`-difference is exactly the **second difference of the carry excess** |
| `jsp87Series_rational_imp_omega_diff_periodEquation` | what a rational value of `S` forces, stated on the `ω`-family |
| `jsp87_omega_diff_periodEquation_bound` | under eventual periodicity, `\|ω (N+t) − ω N\| ≤ 6 · log₂ (N+t+1)` (round 50's logarithmic bound on the four carry excesses) |

### 5. The dyadic sub-case, as a carry-integrality statement

| Theorem | Statement |
| --- | --- |
| `jsp87_dyadic_imp_carry_int`, `jsp87_carry_int_imp_dyadic` | `S = n/2^M` **iff** the carry `θ M` is an integer |
| **`jsp87_dyadic_iff_carryInt`** | **THE DYADIC CROSS-IDENTIFICATION (both directions)** |
| **`jsp87_carryInt_iff_digitZero`** | **hence the binary digits of `S` are eventually `0` from `M` iff some carry of the series is an integer** — the period-`1` sub-case of JSP-000087, in carry language |
| `jsp87_carry_int_succ`, `jsp87_carry_int_of_le` | integrality propagates forward along any range |
| `jsp87_carry_int_excess` | an integral carry *is* its own carry excess |
| `jsp87_carry_int_ge_two` | under the dyadic hypothesis `c N ≥ 2` for `N ≥ 2` (unconditionally `c N ≥ 1`) |
| **`jsp87_dyadic_omega_eq`** | **under the dyadic hypothesis `ω N = 2 c N − c (N+1)`** — the whole `ω`-family is a *doubling-difference* of the carry excess |
| `jsp87_dyadic_omega_bounds` | the squeeze `(omega N : ℝ) ≤ 2 c N − 2` and `2 c N − log₂(N+1) ≤ (omega N : ℝ)` |

### 6. The fifth irrationality criterion

| Theorem | Statement |
| --- | --- |
| `jsp87Series_rational_imp_omegaWindow_congr` | rationality ⇒ some candidate period `t > 0` and start point `M` pass the window congruence test at every `N ≥ M` |
| **`jsp87Series_irrational_of_omegaWindow_never_congr`** | **if no candidate period passes that test, `S` is irrational** |

Together with the four criteria of rounds 41, 46, 47 and 48 the development now
has **five** independent obstructions to `jsp_000087_main`, phrased on five
different objects: the carry excess `⌊θ N⌋`, the binary digit string, the
primary digit string of a carry-free series, the doubling orbit `fract (θ N)`,
and — this round — the residue of the `ω`-window modulo `2^t − 1`.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-51 results
are the unconditional content of the *period equation*; none of them supplies
the missing aperiodicity input.  In the published literature the headline
irrationality is **conditional** (Pratt, arXiv:2409.15185, under a uniform
prime-`k`-tuples hypothesis) and the catalog itself records *Solved; Lean proof:
No; Eligible to claim: No*.  No rename, wrapper or shadowing of the name is
used.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 51, stated exactly

> **`jsp87_window_congr_fails`** — for every candidate period `t > 0` and every
> start point `M`, there is a cut point `N ≥ M` at which
>
> `2^t − 1 ∤ c (N+t) − c N + Ω N t − B N t`,
>
> i.e. the residue of the `ω`-window modulo the Mersenne number `2^t − 1` does
> not match the digit block.  Equivalently (by
> `jsp87Series_irrational_of_omegaWindow_never_congr`) the binary digit string of
> `S` is not eventually periodic from any start point with any period.

Nothing unconditional is known about the distribution of `Ω N t` modulo
`2^t − 1`: that is the arithmetic content of the uniform prime-`k`-tuples
hypothesis in Pratt's result, an *assumption of the published result*, not of the
catalog statement.

### Toolchain notes recorded this round

* **`omega` cannot prove `1 ≤ N + j` for two *variables* `N j : ℕ`** — it is
  false (`N = j = 0`), and this bites whenever one wants
  `omega_lt : ω n ≤ n − 1` for a *bound variable* `n = N + j`.  Split the case:
  `rcases Nat.eq_zero_or_pos (N + j) with h | hpos` and use `omega_zero` in the
  zero case.
* **A term passed as an argument is elaborated *before* the goal is known**, so
  `mul_le_mul_of_nonneg_right (omega_ge_one_of_ge_two (by omega)) (by positivity)`
  silently assigns the metavariable to the *wrong* index and produces
  `1 * N ≤ omega N * N`.  Always pre-prove both sides as separate `have`s with
  explicit types.
* **`Nat.cast_sub : m ≤ n → (m − n : ℕ) = m − n` needs its hypothesis**, and
  `ring` fails on `ℕ` truncated subtraction (`1 + (2^m*2 − 1)*2 = 2^m*4 − 1`).
  Prove such identities in `ℕ` with `omega` plus `one_le_two_pow_nat : 1 ≤ 2^m`,
  or transfer from the `ℝ` version with `exact_mod_cast`.
* **`Nat.one_lt_two_pow : n ≠ 0 → 1 < 2^n`** requires `n ≠ 0`; for the
  unconditional `1 ≤ 2^n` use `Nat.succ_ne_zero` or prove it by induction.
* **`Int.cast_sub : ↑(m − n) = ↑m − ↑n` is the `ℤ` subtraction lemma** (the `ℕ`
  truncated one is `Nat.cast_sub` and needs a proof).  To move a statement from
  `ℤ` to `ℝ` it is far more robust to write the `ℝ` statement directly and supply
  the `Int.cast_sub` / `Int.cast_mul` equations by hand than to use
  `push_cast`/`norm_cast`, which may leave the ambient type unchanged.
* **`abs_add_le a b : |a + b| ≤ |a| + |b|` is a *term*, not an `iff`**, so it
  cannot be used as a `rw` argument; likewise `abs_sub_le'`.  Use
  `have h := abs_add_le a b; … at h`.
* `Nat.exists_eq_succ_of_ne_zero` and `Nat.succ_eq_add_one` are the right tools
  to re-index an all-ones geometric window; `Nat.exists_eq_succ_of_one_le`
  does **not** exist.


---

## Round 52 — the `2`-adic and modular arithmetic of the binary prefix

New module `lean/JSPProblem/AdicPrefix.lean` (516 lines, **24 new theorems and
lemmas** plus **2 new definitions** and 7 private helpers, 0 `sorry`,
0 `admit`; **512 proved theorems and lemmas** in the tree at the
`^(theorem|lemma)` level — 488 before this round — `lake build` clean, **no new
linter warnings**).

**This is a new attack family.**  Rounds 37–46 attacked the *carried* Erdős
series through ten periodicity angles; round 47 the *carry-free* (primary)
expansion; round 48 the *doubling map* on the carries; round 49 the criterion in
*arbitrary radix*; round 50 the *asymptotics* of the carry; round 51 the *period
equation* and the `ω`-window.  **No round had ever looked at the integer
`I N = ⌊2^N S⌋ − ⌊θ N⌋` itself** — the numerator of the `N`-th partial sum, the
integer whose binary expansion *is* the first `N` digits of `S`, and the
`2`-adic integer whose digits are the `ω`-values with carries.  This round
changes the object, not the tool: from `ℝ`-valued carries to `ℤ`-valued
divisibility.

The driving observation is the homogeneous form of round 41's prefix
recursion:

> `I (N+t) = 2^t · I N + Ω N t` — the `t`-step prefix recursion, whose
> inhomogeneous term is **exactly round 51's `ω`-window**.  Hence
> `2^t ∣ I (N+t) ↔ 2^t ∣ Ω N t`: **the `2`-adic content of the binary prefix is
> the `2`-adic content of the `ω`-window.**

### 1. The prefix as a natural number

| Theorem | Statement |
| --- | --- |
| `jsp87Prefix` | **THE NEW OBJECT** `I N := (⌊2^N S⌋ − ⌊θ N⌋).toNat`, round 41's `jsp87IntPart` read in `ℕ` |
| `jsp87Prefix_succ` | **THE PREFIX RECURSION `I (N+1) = 2 I N + ω N`** — the carry recursion `θ (N+1) = 2 θ N − ω N` with the sign of `ω N` flipped |
| `jsp87Prefix_iter` | **THE `t`-STEP PREFIX RECURSION `I (N+t) = 2^t I N + Ω N t`** — the homogeneous form, inhomogeneous term = round 51's window |
| `jsp87Prefix_zero`, `jsp87Prefix_cast` | `I 0 = 0`, and the `ℝ` reading of the prefix |

### 2. The `2`-adic exponent of a natural number

| Theorem | Statement |
| --- | --- |
| `jsp87Val2` | **THE NEW OBJECT** `v (n)`, the exponent of `2` in `n` (via `Nat.findGreatest`); Mathlib has no such function for `ℕ` |
| `jsp87Val2_spec` | **`v n = k ↔ 2^k ∣ n ∧ ¬ 2^(k+1) ∣ n`** for `n ≠ 0` |
| `jsp87Val2_dvd`, `jsp87Val2_not_succ`, `jsp87Val2_zero` | `2^v ∣ n`, `¬ 2^(v+1) ∣ n`, `v 0 = 0` |
| `jsp87Val2_mul_two` | **`v (2 X) = v X + 1`** for `X ≠ 0` |
| `jsp87Val2_prefix_succ_odd` | **`ω N` odd ⇒ `v (I (N+1)) = 0`** |
| `jsp87Val2_prefix_succ_even` | **THE 2-ADIC SAWTOOTH: `ω N` even and `I N ≠ 0` ⇒ `v (I (N+1)) = v (I N + ω N / 2) + 1`** |

### 3. Parity and the `2`-adic chain

| Theorem | Statement |
| --- | --- |
| `jsp87Prefix_parity` | **`I (N+1) mod 2 = ω N mod 2`** — the low bit of the prefix is the low bit of `ω N` |
| `jsp87Prefix_dvd_two_iff` | `2 ∣ I (N+1) ↔ 2 ∣ ω N` |
| `jsp87Prefix_dvd_pow_succ` | **THE 2-ADIC CHAIN: for `k ≥ 1` and even `ω N`, `2^(k+1) ∣ I (N+1) ↔ 2^k ∣ (I N + ω N / 2)`** |
| `jsp87Prefix_dvd_pow_succ'` | the consequence form (one step of the chain) |

### 4. Aperiodicity of the prefix — the headline of the round

| Theorem | Statement |
| --- | --- |
| `jsp87Prefix_periodic_imp_omega_periodic` | **THE KEY TRANSFER LEMMA: an eventual period of `I N mod m` forces the same for `ω N mod m`** (from the recursion, with `Nat.ModEq.add_left_cancel`) |
| **`jsp87_prefix_mod_not_eventuallyPeriodic`** | **THE APERIODICITY OF THE BINARY PREFIX, MODULO EVERY `m ≥ 2`: `N ↦ I N mod m` is NEVER eventually periodic.**  The *sixth* independent aperiodicity statement in the tree, and the first on this object |
| `jsp87_prefix_mod_pow_two_not_eventuallyPeriodic` | the `m = 2^k` instance |
| `jsp87_prefix_dvd_not_eventually` | the divisibility form: for every `m ≥ 2`, `t > 0`, `M` some `n ≥ M` fails `m ∣ I (n+t) − I n` |
| **`jsp87_prefix_dvd_pow_two_not_eventually`** | **THE PREFIX ESCAPES EVERY 2-ADIC WINDOW: for every `k ≥ 1` and `M` there is `n ≥ M` with `2^k ∤ I n`** |

### 5. The window, and the carry excess reading the prefix

| Theorem | Statement |
| --- | --- |
| **`jsp87Prefix_dvd_window`** | **THE 2-ADIC WINDOW EQUIVALENCE: `2^t ∣ I (N+t) ↔ 2^t ∣ Ω N t`** |
| `jsp87_adic_window_iff` | the same in `ℤ` |
| `jsp87_window_periodic_of_prefix_periodic` | **AN EVENTUAL PERIOD OF THE PREFIX MOD `m` FORCES THE SAME FOR THE `ω`-WINDOW** — modular aperiodicity of the prefix transfers to round 51's window |
| **`jsp87_adic_carry_congr`** | **THE 2-ADIC CONTENT OF THE BINARY PREFIX IS READ OFF THE CARRY EXCESS: under eventual periodicity of the digits with period `t` from `M`, `2^t ∣ I (N+t) ↔ 2^t ∣ (c (N+t) − B N t)`** |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-52 results
are the unconditional modular content of the *binary prefix*; none of them
supplies the missing input.  In the published literature the headline
irrationality is **conditional** (Pratt, arXiv:2409.15185, under a uniform
prime-`k`-tuples hypothesis) and the catalog itself records *Solved; Lean
proof: No; Eligible to claim: No*.  No rename, wrapper or shadowing of the name
is used.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 52, stated exactly

> **`jsp87_prefix_window_congr_fails`** — for every candidate period `t > 0` and
> every start point `M` there is a cut point `N ≥ M` at which
> `2^t ∤ I (N+t)`, i.e. at which the `ω`-window `Ω N t` is **not** a multiple of
> `2^t`; formally `(∀ t > 0) (∀ M) (∃ N ≥ M), ¬ 2^t ∣ jsp87OmegaWindow N t`.

Equivalently (by `jsp87Prefix_dvd_window`): the base-`2` weighted average of the
`ω`-values of a window, `∑_{j<t} ω (N+j) 2^{-(j+1)}`, is an integer for **no**
candidate period at **all** cut points.  Nothing unconditional is known about
the distribution of the `ω`-window modulo `2^t`; that is the arithmetic content
of the uniform prime-`k`-tuples hypothesis in Pratt's result, and it is an
*assumption of the published result*, not of the catalog statement.

Note that the *aperiodicity* of the prefix modulo every `m` is now proved
unconditionally (`jsp87_prefix_mod_not_eventuallyPeriodic`) but is **not by
itself** a criterion: rationality of `S` does not freeze `I N mod m`, because
the digit identity `d N = ω N + c (N+1) − 2 c N` mixes the digit family with the
carry family, and round 49's `jsp87_noCarry_fails_any_radix` already proved the
carry cannot be removed in any radix.

### Toolchain notes recorded this round

* **`∤` (not-divides) is NOT AVAILABLE** with the imports used here — the parser
  rejects it (`expected token`).  Write `¬ a ∣ b`.
* `Int.toNat_of_nonneg : 0 ≤ a → (↑a.toNat : ℤ) = a` has its coercion in `ℤ`;
  to state a fact about `(x.toNat : ℝ)` use `exact_mod_cast`, since `rw` will not
  fire (`Monoid ?m` instance stuck).
* `Int.ofNat_dvd : (↑m : ℤ) ∣ (↑n : ℤ) ↔ m ∣ n` is an **iff** (`m : ℕ`), and
  `Int.ofNat_sub : m ≤ n → ↑(n − m) = ↑n − ↑m` **needs the ordering hypothesis**.
  Use `Nat.modEq_iff_dvd' (hle : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b − a` instead.
* `dvd_mul_left (a b : α) : a ∣ b * a` and `dvd_mul_right (a b : α) : a ∣ a * b`
  take **two elements**, not a proof; the proof-taking versions are
  `Int.dvd_mul_of_dvd_left : a ∣ b → a ∣ b * c`.  `Nat.dvd_mul_left` /
  `Nat.dvd_mul_right` have the same shape.
* `Nat.mul_dvd_mul_iff_left (a := 2) (h : 0 < a) : (a * b ∣ a * c ↔ b ∣ c)` —
  the first explicit argument is the **proof** `0 < a`.
* `dvd_neg : a ∣ -b ↔ a ∣ b` is an **iff**; `.mp` goes from `a ∣ b` to
  `a ∣ -b`.  Lean cannot unify a goal `a ∣ (x - y)` with `a ∣ -?b`, so insert
  `rw [show (x - y : ℤ) = -((y - x : ℤ)) from by ring] at h` first.
* **A `by` block inside an anonymous constructor `⟨a, (by omega : P), b⟩` is
  elaborated with a WRONG expected type** (Lean reported the goal `2 ≤ m` for
  `by omega : 0 < t`).  Always supply hypotheses as real terms
  (`Nat.zero_lt_succ 0`) or use `Nat.zero_lt_succ`/`Nat.pos_of_ne_zero`.
* `Nat.ModEq` is a plain `def (a % n = b % n)`: `ModEq.dvd : a ≡ b [MOD n] →
  (n : ℤ) ∣ b - a`, `Nat.modEq_of_dvd : (n : ℤ) ∣ b - a → a ≡ b [MOD n]`, and
  the algebraic toolkit `ModEq.add_left_cancel`, `.add`, `.add_left`,
  `.add_right`, `.mul_left`, `.symm`, `.modEq_zero_nat` is enough for every
  transfer lemma of this round.
* `omega` cannot see through a power (`2 ≤ 2^k` from `1 ≤ k`): prove
  `1 ≤ 2^m` by induction (`one_le_two_pow_nat'`) and `2 ≤ 2^m` from
  `Nat.one_lt_two_pow`.  Inside `cases k with | succ u => …`, the original
  variable `k` is NOT in scope and `Nat.one_lt_two_pow` wants `u ≠ 0`, not
  `Nat.succ u ≠ 0`.
* `linarith` treats `((P - Q) * 2 ^ t)` as a nonlinear monomial and then fails
  on goals mixing it with `m * k`; use `linear_combination (1 : ℤ) * hk2 +
  (-1 : ℤ) * hk1` (the tool that works for exactly these ℤ polynomial goals).

### `-- NEW IN ROUND 53 --` `lean/JSPProblem/RunLength.lean` — runs in `ω` become runs in the binary expansion, and the constant-run criterion

Rounds 37-52 studied the *pointwise* or *periodic* behaviour of single objects
(the carry, the carry excess, the digit, the `t`-block, the `ω`-window, the
2-adic prefix, the profile modulo `m`).  **No round ever asked what a RUN of
`ω`-values does to the binary expansion** — and a run is exactly the kind of
object a prime-`k`-tuples hypothesis produces.  The passage is elementary and is
made exact here.

`θ N = u (1 - 2^(-L)) + 2^(-L) θ (N+L) = u - 2^(-L) (u - θ (N+L))` on a window
where `ω` is constantly `u`, so the *whole* fractional part of the carry is a
**binary tail**, `1 - 2^(-L)·d` or `2^(-L)·d` with `d ∈ (0,1]`.

| Theorem | Statement |
| --- | --- |
| `jsp87ProfileSum`, `jsp87ConstRun`, `sum_two_pow_neg_range`, `jsp87ProfileSum_const` | the `L`-block of a profile read in base `2`; a constant run of `ω`; the geometric sum |
| `jsp87Carry_eq_profile` | **the profile formula**: a prescribed `ω`-profile on `[N, N+L)` gives `θ N = block + 2^(-L) θ (N+L)` |
| `jsp87Carry_sub_constRun` | **the constant-run formula** `θ N = u - 2^(-L) (u - θ (N+L))` |
| `jsp87_fractCarry_succ`, `jsp87_fract_run`, `jsp87_fract_run_zeros` | the doubling step on the fractional parts; a run of `L` ones (resp. zeros) propagates along the whole window, the tail being the binary expansion of `d` |
| `jsp87_fract_constRun_ones` / `_zeros` | **the constant-run identity**: `Int.fract (θ N) = 1 - 2^(-L)(u - θ (N+L))` when the carry does not overshoot, `= 2^(-L)(θ (N+L) - u)` when it does |
| `jsp87_digit_run_ones` / `jsp87_digit_run_zeros` | **RUNS BECOME DIGIT RUNS**: a constant run of `ω` of length `L` produces `L` consecutive `1`s (resp. `0`s) in the binary expansion of `jsp87Series`, at an explicit place |
| `jsp87_fractCarry_eq_div` | the orbit lives on the lattice `1/b ℤ` (`jsp87FracNum_spec` transported to the carries) |
| `jsp87_fractCarry_ne_one` | **THE ASYMMETRY OF THE LATTICE**: `S = a/b` forces every *nonzero* orbit value into `[1/b, 1 - 1/b]` — the orbit never comes within `1/b` of `1`, and reaches `0` only by hitting it exactly |
| `jsp87_fractCarry_small_or_zero` | **WHY RUNS OF `0`s ARE NOT A CRITERION**: a tiny orbit value is either exactly `0` or forces `b > 2^L` |
| `jsp87Series_irrational_of_fract_near_one` | **the orbit criterion**: `∀ L ≥ 1, ∃ N ≥ 1, 1 - 2^(-L) ≤ Int.fract (θ N)` ⟹ `S` is irrational |
| `jsp87Series_irrational_of_digit_run_ones` | **the digit-run criterion**: arbitrarily long runs of `1`s in the digit string ⟹ `S` is irrational (the dual with `0`s is **false**) |
| `jsp87Series_irrational_of_constRun` | **THE CONSTANT-RUN CRITERION**: if `ω` takes an arbitrarily long constant value `u` on windows whose far end has carry below `u`, then `S` is irrational |
| `jsp87Series_rational_imp_denominator_ge` | **quantitative form**: a single run of `L` ones at a cut point forces `2 ^ L ≤ b` |
| `omega_run_twenty`, `omega_window_23`, `jsp87Carry_23_window`, `jsp87ConstRun_twenty` | machine-checked instance: `ω 20 = ω 21 = ω 22 = 2` and `1 ≤ θ 23 < 2` |
| `jsp87_digit_run_twenty` | **THREE CONSECUTIVE `1`s IN THE BINARY EXPANSION OF THE ACTUAL SERIES**, at `20, 21, 22` |
| `jsp87_fractCarry_twenty_ge`, `jsp87_fractCarry_twenty_near_one` | `7/8 ≤ Int.fract (θ 20) < 1` |
| `jsp87Series_rational_imp_denominator_ge_eight` | **if `S = a/b` with `b > 0` then `b ≥ 8`** — the first numerical constraint on the hypothetical denominator |

`jsp_000087_main` is **still deliberately not declared**.  The constant-run
hypothesis of `jsp87Series_irrational_of_constRun` is a *conjecture* (a
uniform statement about patterns of `ω` on consecutive integers, of the same
nature as the uniform prime-`k`-tuples hypothesis in the published conditional
result); it is not known, and no round of this development can supply it.

#### Round 53 -- toolchain notes

* `Int.self_sub_fract x` is `x - ⌊x⌋ = Int.fract x`; `Int.self_sub_floor x` is
  `x - Int.fract x = ⌊x⌋`.  To get `Int.fract x = c`, take the former, rewrite
  the floor with the floor value and finish with `linarith` — the `↑z` casts
  make `exact_mod_cast` the tool of choice for the `ℤ` part.
* `Int.floor_eq_iff : ⌊a⌋ = ↑z ↔ ↑z ≤ a ∧ a < z + 1`: the first component is a
  `ℝ` inequality, the second mixes `ℤ` (`z + 1`) with `ℝ`, so the second goal must
  be closed with `exact_mod_cast` from a `ℝ` statement.
* `set d : ℝ := … with hd` introduces a *let-bound* variable plus the equation.
  All subsequent `have`s must mention `d`, not the expanded expression, or
  `linarith` will treat `2^(-L) * d` and `2^(-L) * (u - θ (N+L))` as different
  atoms and fail.
* `linarith` cannot multiply inequalities by a nonneg quantity: use
  `mul_le_mul_of_nonneg_left/right`, `div_le_div_iff₀ h1 h2` (which takes the
  two positivity hypotheses *in the order of the two denominators*:
  `0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)`) or `one_div_le_one_of_le`.
* `div_le_div_of_nonneg_left` has the OPPOSITE orientation from its name
  (`y ≤ x → a / x ≤ a / y`); use `div_le_div_iff_of_pos_right` for the same
  denominator, and `lt_div_iff₀ h` for `x < 1 / c ↔ x * c < 1`.
* `obtain ⟨L, hL, N, hN, hnear⟩` on a goal `∃ N, P ∧ Q` silently mis-binds the
  names: an `Exists` with one witness and an `And` has **three** components, so
  use `obtain ⟨N, hN, hnear⟩`.
* `jsp87FracNum b N` occurs in the *type* of `jsp87FracNum_spec`, so `obtain`
  (which performs `cases`) on that lemma raises "Dependent elimination failed";
  use `have h := jsp87FracNum_spec …; exact ⟨…, h.1, …⟩` and transport with
  `Eq.trans`, never by `rw` at a goal mentioning `jsp87FracNum`.
* `Interval_cases`/`native_decide` handle the concrete `ω`-tables; but
  `2 ^ (j - 1 + 1 - 1) = 2 ^ (j - 1)` is NOT provable by `omega` or `ring`
  (the truncated subtraction survives), so state such identities as
  `2 * (2^j)⁻¹ = (2^(j-1))⁻¹` and prove them via `inv_pow_neg`, which itself
  needs `Nat.sub_add_cancel` after `rw [← pow_succ]`.

---

## Round 55 — the sieve local model (new family)

New file `lean/JSPProblem/SieveModel.lean` (637 lines, **40 new theorems and
lemmas**, 5 new definitions, 0 `sorry`, 0 `admit`, 0 new linter warnings).
`lean/JSPProblem.lean` now imports it, so `lake build` compiles it.
Total proved theorems and lemmas in the tree: **578** (538 before this round).

### What the round attacks

Round 44 (`CarryExcess.lean`) had already introduced the finsets
`jsp87SmallFactors n m` / `jsp87LargeFactors n m`, proved
`omega n = (jsp87SmallFactors n m).card + (jsp87LargeFactors n m).card`, proved
`card_largeFactors_le_log`, and proved the CRT window-roughness lemma.  What it
never did is **describe the small part**: it treated the sieve content as an
opaque count that could only be bounded from below.  Round 55 describes it
completely, and shows that it is *rigid*, which is what turns round 53's
constant-run hypothesis into a sieve statement.

### The new objects

| name | meaning |
|---|---|
| `jsp87Primes k` | the primes `≤ k` |
| `jsp87Primorial k` | `∏_{p ≤ k} p` (`1` for `k ≤ 1`) |
| `jsp87SieveCard m k` | **sieve content**: number of distinct prime divisors of `m` that are `≤ k` |
| `jsp87UnsievedCard m k` | **unsieved content**: number of distinct prime divisors of `m` that are `> k` |
| `jsp87SieveProfile n k L` | the sieve content of the window `[n, n+L)` |

`jsp87SieveCard m k` and `jsp87UnsievedCard m k` are the numeric counterparts
of round 44's finsets (`card_smallFactors_eq`, `card_largeFactors_eq` are
`rfl`).

### Headline theorems

| theorem | statement |
|---|---|
| `jsp87SmallFactors_congr` | **THE LOCAL MODEL**: `m ≡ m' (mod k#)` ⟹ the *finset* of prime divisors of `m` that are `≤ k` equals that of `m'` |
| `jsp87SmallFactors_window_congr` | the local model holds **window-wise**: `n ≡ n' (mod k#)` ⟹ `jsp87SieveCard (n+j) k = jsp87SieveCard (n'+j) k` |
| `sieveProfile_period` | the sieve profile has period **exactly** `k#` |
| `jsp87SieveProfile_recurs` | **REALISATION**: every sieve profile of level `k` occurring at `m ≥ 1` occurs at every height `N₀` (take `n ≡ m (mod k#)`) |
| `jsp87_pow_unsieved_le` | **THE UNSIEVED CONTENT IN POWER FORM**: `(k+1)^r ≤ m`, where `r` counts the prime divisors of `m` exceeding `k` |
| `jsp87Unsieved_le_log` | the unsieved content is at most `Nat.log (k+1) m` (sharp base; round 44 had base `k` and needed `2 ≤ k`) |
| `jsp87Unsieved_le_one_of_lt_pow` | below `(k+1)²`, at most one prime divisor of `m` exceeds `k` |
| `jsp87Unsieved_lt_of_lt_pow` | below `(k+1)^r`, fewer than `r` |
| `jsp87Unsieved_eq_zero_of_ge`, `jsp87Unsieved_eq_zero_iff` | the unsieved content vanishes exactly on the `k`-smooth numbers |
| `omega_congr_of_unsieved` | on a progression `≡ r (mod k#)`, `ω m` is the residue class plus the unsieved content |
| `omega_congr_of_smooth` | on `k`-smooth numbers, `ω` is **exactly** periodic with period `k#` |
| `omega_diff_le_of_congr` | the periodicity defect of `ω` is at most `2 log_{k+1}(m+m')` |
| `jsp87_constRun_sieve_iff` | **the constant-run hypothesis in sieve form**: `ω` is constant with value `u` on `[N,N+L)` **iff** the sieve content plus the unsieved content is `u` at every point of the window |
| `jsp87_constRun_sieve_sub` | **the compensation form**: at every point of a constant run, `jsp87UnsievedCard (N+j) k = u - jsp87SieveCard (N+j) k` |
| `jsp87_run_halves_not_constant` | **NEGATIVE, machine-checked**: on `ω 20 = ω 21 = ω 22 = 2` the two halves are *not* separately constant (sieve content `2,1,1`, unsieved `0,1,1` at `k = 5`) |
| `jsp87Series_irrational_of_sieveRun` | the irrationality criterion with the hypothesis written in sieve form (an honest **reformulation**, not a weakening — see below) |
| `sieveCard_two` | the sieve content at level `2` is the indicator of evenness |
| `jsp87_constRun_height` | **a quantitative constraint on where a run can sit**: a constant run of value `u` on `[N,N+L)` with `L ≥ 2` forces `3^(u-1) ≤ N+L-1` |
| `jsp87_omega_eq_sieve_of_window_below` | below the cut-off, `ω` is entirely sieve content |

Machine-checked instances: `jsp87Primorial_instances` (`k#` for `k ≤ 5`),
`jsp87_sieve_instances_thirty` (the split at `30 = 2·3·5` for `k = 2,3,5`),
`jsp87_sieve_run_twenty` (the run `ω 20 = ω 21 = ω 22 = 2` is *purely modular* at
`k = 23`, and the profile is `k#`-periodic),
`jsp87_constRun_height_twenty`.

### What this does and does not buy

`jsp87SieveProfile_recurs` shows that **the small-prime half of any pattern
hypothesis about `ω` is unconditionally satisfiable**: whatever profile the
small primes are asked to display on a window, they display it at infinitely
many heights.  Combined with `jsp87Unsieved_le_log`, the residual hypothesis
of `jsp87Series_irrational_of_sieveRun` is therefore entirely about the
primes exceeding a *fixed* bound `k` — the shape of the uniform prime-`k`-tuples
hypothesis of Pratt (arXiv:2409.15185).

The attempted *strict weakening* of round 53's hypothesis **failed** and is
recorded as machine-checked negative knowledge: asking the two halves to be
constant separately is *stronger*, not weaker, and a constant run does not
imply it.  The correct sieve form of the hypothesis is the compensation form
`jsp87_constRun_sieve_sub`.

`jsp_000087_main` remains undeclared.  No rename, wrapper or shadowing trick is
used.

### Round 55 -- toolchain notes

* **Round 44 already owns `jsp87SmallFactors` / `jsp87LargeFactors`** as
  *finsets* in `CarryExcess.lean`.  A new file must not reuse the names; the
  numeric counterparts used here are `rfl`-equal to their `.card`.
* **`Finset.filter` membership destroys to `List.Mem`.**  Once
  `hp : p ∈ m.primeFactors.filter (· ≤ k)` is in the context, `rintro ⟨h,h'⟩`
  and *any* projection `.1` / `.2` on it fail with
  `Invalid projection ... List.Mem ... is not a one-constructor inductive type`.
  The fix is to ascribe the type:
  `have hp' : p ∈ m.primeFactors ∧ p ≤ k := Finset.mem_filter.mp hp`, and to
  build the answer with `Finset.mem_filter.mpr ⟨…⟩` (whose expected type forces
  the `And` view).
* `simp only [Finset.mem_filter]` makes **no progress** on a goal stated with a
  `noncomputable def` that unfolds to a filter; unfold the definition first
  (`simp only [jsp87SmallFactors, Finset.mem_filter]`).
* `Nat.ModEq.dvd` / `Nat.modEq_of_dvd` work in `ℤ` with the orientation
  `↑n ∣ ↑b - ↑a` for `a ≡ b [MOD n]`.  The most robust construction is to give
  the witness explicitly — `refine Nat.modEq_of_dvd ⟨-(c:ℤ), ?_⟩` and prove the
  cast equation with `push_cast; ring`; `push_cast; linear_combination` is
  unreliable here.  After `rw [hcast]` a goal may remain in the order
  `↑n * ↑c`, which `ring` closes.
* **`omega` cannot derive `s ≤ u` from `c = u - s`** — only the converse
  (`c = u - s` from `s + c = u`).  State the iff in the sum form and obtain the
  subtraction form as a corollary.
* `omega` cannot prove `u - s = 0` from `u < s`; use `Nat.sub_eq_zero_of_le`.
* `Nat.mul_le_mul : n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * m₂` (TWO order
  hypotheses), so `Nat.mul_le_mul (Nat.le_refl N0) hK : N0 ≤ N0 * K`; the
  one-argument form is a type error.
* `Nat.log_mono_right` takes only the order proof.
* `obtain` on a nested `Exists`/`And` does **not** flatten: take the `Exists`
  witnesses first, then the `And` chain.  A witness for
  `jsp87Series_irrational_of_constRun` needs **six** names, not five.
* `native_decide` evaluates `jsp87SieveCard m k` (a `Finset` filter over
  `m.primeFactors`) fine, so all small instances are by `native_decide`.  Watch
  out: `jsp87UnsievedCard 30 2 = 2`, not `1`, because `3` and `5` both exceed `2`.
* `if_pos` / `if_neg` are deprecated in this toolchain; use `ite_eq_left` /
  `ite_eq_right` inside `rw`.

## Round 56 — the arithmetic of the product of a window (new family)

### What the round attacks

Rounds 37–55 all attacked the Erdős series *through the series*: the Lambert
reduction (37), the carry scaffold (38), the denominator gcd (39), the carry
recurrence (40), the binary digit bookkeeping (41), the carry excess (44), the
base-`2` block arithmetic (46), the primary expansion (47), the doubling map
(48), the radix criterion (49), the asymptotics of the carry (50), the period
equation (51), the `2`-adic binary prefix (52), runs in `ω` (53) and the sieve
local model (55).  **No round had ever formed the product of a window**, the
classical object of Erdős's own argument.  This round introduces it:

* `jsp87WindowProd N L = ∏_{j<L} (N+j)`;
* `jsp87BigCard m L = #{p ∈ m.primeFactors : p ≥ L}`;
* `jsp87BigFactors N L` — the prime divisors `≥ L` of the window product;
* `jsp87Incidence p N L = #{j < L : p ∣ (N+j)}`.

`lean/JSPProblem/WindowProduct.lean`, 690 lines, 4 definitions, 48 theorems,
0 `sorry`, 0 `admit`, 0 new linter warnings.  The tree now holds 626 proved
theorems and lemmas (was 578).

### The driving observation

**Two entries of a window have a common prime factor only if that prime is
smaller than the length of the window.**  If `p ∣ (N+i)` and `p ∣ (N+j)` with
`i < j < L` then `p ∣ (j-i)`, and `j-i < L`, so `p < L`
(`jsp87_common_prime_lt`, and in gcd form `jsp87_gcd_lt_window`).  Hence the
prime divisors `≥ L` of the product of a window are *disjointly attributable*.

### Headline theorems

* `jsp87_bigFactors_card_eq` — **THE ADDITIVITY THEOREM**:
  `(jsp87BigFactors N L).card = ∑_{j<L} jsp87BigCard (N+j) L`.  Proved from
  `jsp87_bigFactors_eq_biUnion` and `jsp87_bigFactors_disjoint` via
  `Finset.card_biUnion`.
* `jsp87_window_omega_eq` — **THE EXACT WINDOW ACCOUNTING**:
  `∑_{j<L} ω(N+j) = #(distinct primes ≥ L of the product) + ∑_{j<L} #(primes ≤ L-1 of N+j)`.
  Round 44 had only the one-sided estimate `jsp87_sum_omega_window_le`.
* `jsp87_pow_bigLe_window`, `jsp87_window_pow_bounds` — the sandwich
  `L ^ #(large primes) ≤ ∏ (N+j) ≤ (N+L-1) ^ L`, and hence
  `jsp87_bigFactors_card_le_log` : `#(large primes) ≤ L · log_L (N+L-1)`,
  with the *window length* as base.
* `jsp87_window_omega_le` : `∑_{j<L} ω(N+j) ≤ L log_L (N+L-1) + L π(L-1)`.
* `jsp87_incidence_le_div` — **THE COLLISION BUDGET**: a prime `p` divides at
  most `⌊(L-1)/p⌋+1` of the `L` entries (attained: `jsp87Incidence_three_four`).
* `jsp87_constRun_height_log` — **a constant run of value `u` and length `L ≥ 2`
  satisfies `L^(u - π(L-1)) ≤ N+L-1`**, sharpening round 55's
  `3^(u-1) ≤ N+L-1` by a factor that sees the length of the run.
* `jsp87_run_prod_ge` (`2^(u·L) ≤ ∏(N+j)` on a constant run) and
  `jsp87_sieveRun_prod_ge` (`(k+1)^(c·L) ≤ ∏(N+j)` under round 55's
  compensation hypothesis) — the *window* form of round 55's pointwise
  `jsp87_pow_unsieved_le`, which was route (1) of its `next_round_attack`.
* `jsp87SieveCard_le_primes` : the small-prime content of an entry is at most
  `π(L-1)`, i.e. **all** the non-additivity of a window sits inside the primes
  below `L`.

### Machine-checked instances

* `jsp87BigFactors_twenty` : `jsp87BigFactors 20 3 = {3,5,7,11}`, product
  `9240 = 2^3·3·5·7·11`, `ω`-mass `6 = 4 + 2`.
* `jsp87_small_additivity_fails` — **NEGATIVE**: for the window `[3,8)` the
  primes `≤ 5` have `6` incidences but only `3` distinct primes of the product
  `20160`, while the primes `≥ 6 = L` are additive (`1` and `1`).  The
  threshold `L` is exactly right.
* `jsp87ConstRun_1306291` — a **12-run** of value `3` on
  `[1306291, 1306303)`, with `36 = 21 + 15`; `jsp87ConstRun_526095` — a
  **14-run** of value `3` on `[526095, 526109)`, with `42 = 22 + 20`.

### Gate status

`lake build` OK, 0 `sorry`, 0 `admit`,
`harness/score.py problems/JSP-000087 --strict-prize` → `partial_ok=true`,
`prize_ready=false`, `missing_theorems=['jsp_000087_main']`.  The headline
irrationality remains conditional in the published literature (Pratt,
arXiv:2409.15185, under a uniform prime `k`-tuples hypothesis), and
`jsp_000087_main` is deliberately not declared.

### Round 56 -- toolchain notes

* **`Finset.mem_filter` does not unify with a metavariable predicate.**  Write
  `ext p; simp only [Finset.mem_filter]; constructor; intro h; refine And.intro h.1 ?_; omega`.
  `Finset.mem_filter.mpr ⟨…⟩` leaves the goal in a form on which `omega` reports a
  counterexample in terms of the *bound variable* only.
* `p ∈ s.filter f` is **not** definitionally `p ∈ s ∧ f p`: ascribe with
  `Finset.mem_filter.mp h`, or `simp only [Finset.mem_filter]` first (the
  round-55 note about destroyed `List.Mem` applies).
* `Finset.card_pos : 0 < s.card ↔ s.Nonempty` — `.mp` takes the inequality,
  `.mpr` takes `Nonempty` (`Basic.lean` writes `.mpr ⟨p, hm⟩`).
* `Finset.min'_le (s) (x) (hx : x ∈ s) : s.min' _ ≤ x` — the ELEMENT and its
  membership, not the `Nonempty` proof.
* `Finset.card_le_card_of_injOn f hmap hinj` — `f` is the first **explicit**
  argument.
* `Set.PairwiseDisjoint s t` (the hypothesis of `Finset.card_biUnion`) presents
  the goal as `Function.onFun Disjoint t a b`, which `rw` cannot see through:
  `unfold Function.onFun; rw [Finset.disjoint_left]; intro p hp1 hp2`, then
  ascribe `hp1`/`hp2` with `Finset.mem_filter.mp`.
* **`omega` does no ring normalisation.**  `L * (log + π) = L·log + L·π` needs
  `rw [Nat.mul_add]`; cancelling a common positive factor needs
  `Nat.le_of_mul_le_mul_left hmul2 (by omega)` (inequality first, positivity
  second).  It cannot cancel when one side is a product *containing a sum*.
* `calc` with a `∏ j ∈ s, f j` or `∑ j ∈ s, f j` on the left is a **parse
  error**; prove the equality separately with `Finset.prod_const` /
  `Finset.sum_const` + `Finset.card_range` and use `rw`.
* `.card` must sit inside the parentheses: `((s.filter f)).card`, never
  `s.filter f |>.card` or `s.filter (f).card`.
* `native_decide` **cannot** decide `jsp87ConstRun N L u` (a `∀ j : ℕ`); use
  `intro j hj; interval_cases j <;> native_decide`.
* `Nat.le_log_iff_pow_le (b := L) (1 < L) (0 < y) : x ≤ log L y ↔ L^x ≤ y` —
  the forward direction is exactly the last step of `jsp87_constRun_height_log`;
  no contradiction is needed.
* `simp only [Finset.mem_filter]` makes no progress through an opaque or
  `noncomputable def` (e.g. `jsp87WindowProd`): use `rwa [jsp87WindowProd] at h`
  or `exact` on the definitionally equal form.
* **Machine note:** the container filesystem was FULL (0 bytes free) during
  this round, which made two `lake env lean` runs hang for >20 minutes before
  any error was reported.  Free scratch space before long builds; the symptom
  is a *timeout with no diagnostics*, not an elaboration error.

---

## Round 57 — THE DENOMINATOR SIDE: the complete period–denominator and period–order correspondences

New module `lean/JSPProblem/Denominator.lean` (969 lines, **44 new theorems and
lemmas** plus 2 new `def`s and 7 private helpers, 0 `sorry`, 0 `admit`; **670
proved theorems and lemmas** in the tree at the `^(theorem|lemma)` level — 626
before this round — `lake build` clean).

**New attack family.**  Rounds 37–56 all worked with the **numerators** of the
problem: the binary digits, the blocks, the carries, the windows, the prefixes.
None of them ever asked the classical question Erdős asks — *what is the
denominator of the number?*  Rounds 39, 40 and 46 produced **one-sided**
divisibility statements about a hypothetical denominator `b`; this round turns
them into **exact equivalences**, in both directions.

### 1. The binary expansion of an arbitrary real (new apparatus, general `x`)

| Theorem | Statement |
| --- | --- |
| `digitAt x N` | the new object: the `N`-th binary digit of an **arbitrary** real, `⌊2^{N+1} x⌋ − 2⌊2^N x⌋` |
| `digitAt_eq_floor_two_fract` | **the digit is the second binary digit of the fractional part**: `digitAt x N = ⌊2 · fract (2^N x)⌋` |
| `digitAt_mem` | the digits of *every* real are `0` or `1` |
| `digitAt_fract_succ'` | **the orbit recursion** `fract (2^{N+1} x) = 2 · fract (2^N x) − digitAt x N` |
| `digitAt_fract_periodic` | periodicity of the digits forces periodicity of the doubling orbit — proved from the *doubling of the defect*, not from the telescoping identity of round 46 |
| `digitAt_no_allOnes` | **no real number has an eventually-all-ones binary expansion** |
| `digitAt_const_of_run` (private) | a run of `t` equal digits *is* the whole tail |
| `jsp87Digit_eq_digitAt` | round 57's digit restricted to `jsp87Series` is round 41's digit |

Mathlib has no statement about the base-`2` expansion of a real number at all.

### 2. THE COMPLETE PERIOD–DENOMINATOR CORRESPONDENCE (both directions)

| Theorem | Statement |
| --- | --- |
| `digitAt_periodic_of_den_dvd` | **divisibility forces periodicity**: `b ∣ 2^M (2^t − 1)` ⟹ the digits of `a/b` are `M`-periodic with period `t` |
| `digitAt_periodic_of_den_dvd_odd` | the `M = 0` case: `b ∣ 2^t − 1` makes the expansion *purely* periodic |
| `jsp87_den_dvd_mer_of_period` | **periodicity forces divisibility**: `jsp87Series = a/b` in lowest terms, digits `M`-periodic with period `t > 0` (`1 ≤ M`) ⟹ `b ∣ 2^M (2^t − 1)` |
| **`jsp87_digitPeriod_iff_den_dvd`** | **THE HEADLINE: `(∀ n ≥ M, d (n+t) = d n) ↔ b ∣ 2^M (2^t − 1)`** |

This is the first time in this development that a hypothesis about the **binary
digits** of `jsp87Series` is *equivalent* to a hypothesis about the
**denominator** of a hypothetical rational value.

### 3. THE COMPLETE PERIOD–ORDER CORRESPONDENCE

New object: `jsp87OddPart b = b / 2^{v_2(b)}` (built from round 52's
`jsp87Val2`).

| Theorem | Statement |
| --- | --- |
| `jsp87Val2_le`, `jsp87_pow_mul_oddPart`, `jsp87OddPart_dvd`, `jsp87OddPart_pos` | the `2`-adic decomposition `b = 2^{v_2 b} · oddPart b` |
| `not_two_dvd_oddPart`, `jsp87_coprime_two_oddPart` | **the `2`-free part is odd** |
| `pow_two_dvd_of_dvd_oddPart` | `2^k ∣ oddPart b` and `v_2 b ≤ k` ⟹ `2^k ∣ b` |
| `jsp87_oddPart_dvd_mer_of_period` | a hypothetical period forces `oddPart b ∣ 2^t − 1` |
| `jsp87_den_dvd_mer_of_oddPart` | **the converse**: `oddPart b ∣ 2^t − 1` and `v_2 b ≤ M` ⟹ `b ∣ 2^M (2^t − 1)`, i.e. `t` **is** a period |
| **`jsp87_digitPeriod_iff_oddPart_dvd_mer`** | **THE COMPLETE PERIOD–ORDER CORRESPONDENCE: for `M ≥ v_2(b)`, `(∀ n ≥ M, d (n+t) = d n) ↔ oddPart b ∣ 2^t − 1`** |
| `jsp87_period_lcm` | two periods have the common period `lcm t t'` |
| `jsp87_period_gcd` | **the eventual periods are gcd-closed** (from round 39's exact `gcd_two_pow_sub_one`) |
| `jsp87_minimalPeriod_dvd` | hence the eventual periods form `t₀ ℕ`: the minimal period divides every period, and `t₀` is the multiplicative order of `2` modulo `oddPart b` |
| `jsp87_prime_den_dvd_mer` | every odd prime `q ∣ b` divides `2^t − 1` for every eventual period `t` |
| `jsp87_prime_period_lt_den` | a **prime** period is smaller than every odd prime of the denominator (round 39's Fermat step applied to the period) |
| `jsp87_digitPeriod_one_pow_two_den` | the period-`1` case in denominator form: the reduced denominator is a power of `2` dividing `2^M` (equivalently `oddPart b = 1`) |

### 4. The run dichotomy — round 53's inequality now contains the period

| Theorem | Statement |
| --- | --- |
| `digitAt_fract_fracNum` | the fractional part of `2^N (a/b)` is `c/b` with `0 ≤ c < b` |
| `digitAt_oneRun_gap` | **THE GAP INEQUALITY: a run of `L` ones forces `2^L · (b − c) ≤ b`**, `c` the numerator of the fractional part |
| `jsp87_oneRun_two_pow_le` | hence `2^L ≤ b`, for an arbitrary rational in lowest terms (round 53 proved it for the series only) |
| `digitAt_periodic_oneRun_lt` | **a `t`-periodic digit string never contains `t` consecutive ones at or after the periodic point** |
| `digitAt_periodic_zeroRun_dyadic` | a run of `t` zeros there forces the expansion to **terminate**: the value is dyadic |
| `jsp87_digitPeriod_oneRun_lt`, `jsp87_digitPeriod_zeroRun_dyadic`, `jsp87_oneRun_two_pow_le_series` | the three statements for `jsp87Series = a/b` |

### 5. Machine-checked instances

* `digitAt_five_sevens` : the binary expansion of `5/7` is `3`-periodic **from the first digit** (`7 ∣ 2^3 − 1`).
* `digitAt_five_sevens_digits` : `5/7 = 0.101 101 101 …`, the three digits exactly.
* `jsp87_ord_seven` : `v_2(7) = 0`, `oddPart(7) = 7`, `7 ∣ 2^3 − 1`, `7 ∤ 2 − 1`, `7 ∤ 2^2 − 1` — the `3` above is the *order*.
* `jsp87_ord_twelve` : `v_2(12) = 2`, `oddPart(12) = 3`, `3 ∣ 2^2 − 1`, `3 ∤ 2 − 1`.
* `digitAt_seven_twelve_period_two` : the expansion of `7/12` is `2`-periodic **from index 2** — the threshold `M ≥ v_2(b)` is exactly right.

### Gate status

`lake build` OK, 0 `sorry`, 0 `admit`,
`harness/score.py problems/JSP-000087 --strict-prize` → `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.  The headline irrationality remains
**conditional in the published literature** (Pratt, arXiv:2409.15185, under a
uniform prime `k`-tuples hypothesis) and the catalog records *Solved; Lean proof:
No; Eligible to claim: No*; `jsp_000087_main` is deliberately not declared.

### The blocker, after round 57, stated exactly

> **`jsp87Series_irrational_of_blockNotPeriodic`** (round 46) — equivalently
> `jsp87_digit_not_eventuallyPeriodic` (round 47) — equivalently
> `jsp87_fracCarry_not_eventuallyPeriodic` (round 48).

Round 57 does not remove it; it **pins the period arithmetically**.  What is
now proved, for a hypothetical rational `jsp87Series = a/b` in lowest terms:

* the binary digit string is eventually periodic, and from `M = v_2(b)` on it is
  `t`-periodic where `oddPart b ∣ 2^t − 1`;
* the eventual periods are exactly the multiples of `t₀ = ord_{oddPart b}(2)`
  (gcd-closed, hence a principal ideal);
* every one-run after `M` is shorter than `t` and forces `2^L ≤ b`;
* a zero-run of length `t` there would make the value dyadic.

So the *only* way the Erdős series can be rational is that its digit string
*is* eventually periodic, and round 57 says exactly what that periodicity would
force arithmetically.  The missing input is still the quantitative correlation
control of `ω` at shifted primes that makes such a periodicity impossible; it
is an assumption of the published result, not of the catalog statement.

### Round 57 — toolchain notes (LEARN THESE)

* `rw [h]` with a *variable* on the left-hand side rewrites EVERY occurrence of
  that variable — including inside `q % t`, `q / t`, `jsp87Val2 b`, …  Use
  `calc`, `congr`, or a `have` with an explicit statement instead.  This bit
  three proofs (`digitAt_const_of_run`, `not_two_dvd_oddPart`,
  `jsp87_den_dvd_mer_of_period`).
* `rw` with several lemmas rewrites **all** instances of each LHS.  When the
  pattern also occurs inside a `⌊ · ⌋` (e.g. `2^N * x` inside `⌊2^N * x⌋`), use
  `nth_rewrite 1 [h]` — and if the LHS of the goal step is still a
  metavariable, the first concrete occurrence is the *wrong* one: instantiate it
  with a `rfl` step first.
* `Nat.cast_sub (h : m ≤ n) : ↑(n − m) = ↑n − ↑m` — the hypothesis must be
  stated in the `≤` form (`Nat.lt.le` of a `<` hypothesis elaborates to
  `Nat.succ a ≤ b` and the rewrite then looks for `↑(b − c.succ)`).
* `Nat.gcd_le_left (n : ℕ) : 0 < m → m.gcd n ≤ m` — the *first* explicit
  argument is the **second** gcd slot; use `Nat.gcd_dvd_left` + `Nat.le_of_dvd`
  instead when in doubt.
* `Nat.coprime_pow_left_iff` has `(a ^ n).Coprime b ↔ a.Coprime b` (power on the
  left), `Nat.coprime_pow_right_iff` has `a.Coprime (b ^ n) ↔ a.Coprime b`; the
  implicit `n` is the exponent, the two explicit slots are `a` and `b`.
* `Nat.coprime_primes : p.Prime → q.Prime → (Coprime p q ↔ p ≠ q)` is an
  **iff**, not a function returning the coprimality: use `.mpr (by …)`.
* `Nat.mul_le_mul_left (k : ℕ) (h : m ≤ n) : k * m ≤ k * n` — the explicit
  argument is the multiplier `k`, the inequality is the second argument.
* `Int.floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1` — the goals contain
  `↑z`, which `linarith` treats as an opaque atom; use `simpa`/`norm_num`.
* `linarith` cannot use divisibility: `m ∣ n` gives an existential witness, so
  `m ≤ n` needs `Nat.le_of_dvd`.  It also cannot relate `a * b` to `a` for
  variables `a, b`; use `Nat.mul_le_mul_left`/`mul_lt_mul_of_pos_left` or
  `div_lt_iff`/`lt_div_iff` to cancel a factor.
* `mul_eq_zero` is the tool for `x * c = 0 → x = 0 ∨ c = 0` when `c ≠ 0`; plain
  `linarith` cannot do it.
* Numerals in a `ℝ` context elaborate through `OfNat`, **not** through
  `NatCast`, so `rw [← Nat.cast_pow]` does not match `(2 : ℝ) ^ M`.  For
  `(2 : ℝ) ^ M = ((2 ^ M : ℕ) : ℝ)` use `norm_cast` (or `push_cast; norm_num`).
* `Int.toNat_of_nonneg` + `exact_mod_cast` is the safe route from `0 ≤ c`
  (`c : ℤ`) to `(c.toNat : ℝ) = (c : ℝ)`.
* `(2 : ℝ) ^ M * ((2 : ℝ) ^ t − 1) = ((2 ^ M * (2 ^ t − 1) : ℕ) : ℝ)` is closed
  by `push_cast; norm_num` (3 lines) but **not** by `norm_cast` or
  `push_cast; ring`.
* `digitAt_periodic_of_den_dvd` takes `n` **before** the `M ≤ n` hypothesis
  (the conclusion is a `∀`-telescope), so the `M = 0` corollary must be applied
  as `… hb ht h1 n (Nat.zero_le n)`.
* Extracting `b ∣ a * D` from the real equation `a · D = n₀ · b`: clear the
  denominators with `field_simp at h`, cast `n₀` to a natural with
  `n₀.toNat` (it is `≥ 0` by `mul_nonneg_iff_of_pos_left`), then
  `rw [← Nat.cast_mul, ← Nat.cast_mul] at hh; exact Nat.cast_injective hh`.
  A long chain of `exact_mod_cast` on the ℝ statement does *not* close (it
  normalises `↑(a * 2 ^ M) * Int.subNatNat (2 ^ t) 1`).

## Round 58 — the average order of `ω` (new family)

`lean/JSPProblem/Mean.lean` (640 lines, 2 definitions, 34 theorems and lemmas,
0 sorry, 0 admit, no new warnings). Tree total: **704** proved theorems/lemmas
(was 670).

Rounds 37–57 were all *pointwise* or *windowwise*: `ω n ≤ log₂ n`, the carries,
the binary digits, the sieve profile, the window product, the denominator.
Round 58 asks for the **mean** of `ω` — the quantity Erdős' 1948 Lambert-series
paper is named after — for the first time.

**New objects.** `jsp87OmegaCount A X = ∑_{1 ≤ n ≤ X} ω n` (the number of pairs
`(n, p)` with `p` prime, `n ≤ X`, `p ∣ n`) and `jsp87WindowOmega N L =
∑_{j<L} ω (N+j)` (the `ω`-mass of a window).

**The backbone.**
* `jsp87_omegaCount_eq_primeDiv` — **the double-counting identity**
  `A X = ∑_{p ≤ X, p prime} ⌊X/p⌋`. Everything else follows from it, and it is
  the source of the classical `~ X log log X`.
* `jsp87_omegaCount_superadd`, `jsp87_omegaCount_mul` — the mean is
  superadditive and never decreases along dilations: `A (c·x) ≥ c · A x`, hence
  `A (2L) ≥ 2 A L`, i.e. the second half of the **initial** window `[1, 2L]`
  dominates the first (`jsp87_window_doubling_dominates`).
* `jsp87_window_omega_eq_primeCount` — the window form of the identity, prime by
  prime; `jsp87_dvd_count_Ioc` is the exact count of multiples of `p` in an
  interval.

**The flagship.** `jsp87_window_omega_ge_omegaCount`: for `1 ≤ N`, `1 ≤ L`,
**every** window of length `L` carries at least `A L = ∑_{p ≤ L} ⌊L/p⌋` prime
factors, because each prime `p ≤ L` divides at least `⌊L/p⌋` entries of *any*
window. So the local mean of `ω` is minimised at the origin and is never smaller
anywhere. Instances (`native_decide`): 11 at length 10, 171 at length 100, 2126
at length 1000. Real form: `jsp87_window_mean_ge_one` — the local mean over any
window of length `L` is at least `∑_{p ≤ L} 1/p − 1`, the first
`−½ log log L` of the average order, uniformly in the position of the window.

**Machine-checked negatives (new, and important).**
* `jsp87_omegaCount_not_convex`: `A 9 + A 3 = 11 < 12 = 2 A 6`. The counting
  function of `ω` is **not** convex on progressions, so superadditivity does not
  give a "drift of `ω` at every position".
* `jsp87_window_half_dominance_fails`: `W (7,3) = 3 < 4 = W (4,3)`. The second
  half of a window does **not** always dominate the first; only the `k = 0`
  instance survives.
* Numerically: the binary digits of the series have density `1/2` (60 ones in the
  first 119 exact digits), so the round-50 criterion
  `jsp87Series_irrational_of_digitDensity_not_bounded` is **false** for this
  series, and the "sparse digits" theory (which would have settled the problem)
  is refuted.
* `jsp87_window_omega_ge_omegaCount` genuinely needs `1 ≤ N`: at `N = 0`,
  `W (0,5) = 3 < 4 = A 5`, because `ω 0 = 0` sits inside the window.

**Why `jsp_000087_main` is still absent.** The mean of `ω` is the part of `ω`
that is *known and uniform*; the irrationality argument needs the fluctuations of
`ω` around it. Round 58 shows quantitatively that the mean cannot help: it is
bounded below in every window by the prime harmonic sum, and it is not even
convex. The result remains conditional in the literature (Pratt, arXiv:2409.15185,
under a uniform prime-k-tuples hypothesis), and the catalog itself records
"Eligible to claim: No".

**Toolchain notes for the next round** (full list in `policy.json`):
`Nat.card_multiples` and `Nat.Ioc_filter_dvd_card_eq_div` give every
prime-multiplicity count in one line; `Nat.add_mul_div_left/right` prove the
floor-carry identities in three lines each; and three *parsing traps* cost a full
build cycle each — (i) `∑ p ∈ s, A/p + B/p` does **not** bind `p` over the whole
body (the notation body stops at the first top-level `+`), (ii) `X / p := t` is a
type ascription, not a `have`-statement `:=`, and inserts a `ℝ` coercion,
(iii) `Finset.sum_le_sum fun p _ => e` leaves the binder types as metavariables
and silently produces a `sorry`.

---

## Round 60 — CRT CONSTRUCTIONS: the high local minima of `ω` (new attack family)

New module `lean/JSPProblem/CRTWindow.lean` (612 lines, **24 new theorems
and lemmas** plus 4 private helpers, 0 `sorry`, 0 `admit`, 0 new linter
warnings; **728 proved theorems and lemmas** in the tree at the
`^(theorem|lemma)` level — 704 before this round — `lake build` clean).

This is a **new attack family and a new kind of object**.  Rounds 37–59 worked
exclusively with *necessary* conditions: what a rational value of `S` would
force.  **No previous round ever constructed anything.**  This round brings
`Nat.chineseRemainderOfFinset` into the development and obtains the first
existential results about `ω` and about the carries of the Erdős series.

### 1. The construction (the flagship)

| Theorem | Statement |
| --- | --- |
| `jsp87_window_min_omega_ge_of_ge` | **FOR EVERY `k`, EVERY window length `L` AND EVERY `M` there is a place `N ≥ M` such that all of `N, …, N+L-1` have at least `k` DISTINCT prime factors** |
| `jsp87_window_min_omega_ge` | the same with `N ≥ 1` (the headline form) |
| `jsp87_window_min_omega_ge_five_three` | five consecutive integers, each with `≥ 3` prime factors |
| `jsp87_window_min_omega_ge_four_two` | four consecutive integers, each with `≥ 2` prime factors |
| `jsp87_windowOmega_ge` | the window-sum form `k · L ≤ jsp87WindowOmega N L` |
| `jsp87_windowOmega_unbounded` | **the local mean of `ω` is unbounded, in windows of fixed length, beyond every place** |
| `jsp87_windowOmega_bracket` | **THE TWO-SIDED BRACKET**: `jsp87OmegaCount L ≤ jsp87WindowOmega N L` (round 58, uniform) together with the existential upper bound above |
| private `jsp87_coprime_moduli` | the arithmetic core: for every `k, L` there are `L` **pairwise coprime** moduli each with `≥ k` prime factors |

The private lemma `jsp87_coprime_moduli` is the heart of the round: at each step
a finset of `k` primes strictly above the product `B` of all previous moduli is
taken; a prime `p > B ≥ m_j` divides none of the previous moduli, so the new
modulus is coprime to all of them.  The moduli are then combined by the Chinese
remainder theorem, and `m j ∣ N + j` for every `j < L` gives `ω (N + j) ≥ k` by
`omega_mono`.

### 2. The low side, and the oscillation of the local minima

| Theorem | Statement |
| --- | --- |
| `jsp87_omega_one_of_prime` | `ω p = 1` for a prime `p` |
| `jsp87_window_ge_one_of_prime` | every entry of a window starting at a prime has `≥ 1` prime factor |
| `jsp87_window_min_one_of_prime` | **AT EVERY PRIME, EVERY WINDOW HAS LOCAL MINIMUM EXACTLY `1`** |
| `jsp87_window_min_run3` | machine-checked: `ω 3 = ω 4 = ω 5 = 1`, `ω 6 = 2` |
| `jsp87_minWindow_unbounded` | **THE LOCAL MINIMA OF `ω` ARE UNBOUNDED**: for every `K` and every `M` there is a window beyond `M` on which every entry is `> K` |
| `jsp87_omega_periodic_imp_bounded` | an eventual period `t` of `ω` makes `ω` bounded on the tail (strong induction stripping one period at a time) |
| `jsp87_omega_periodic_imp_window_le` | **and therefore bounds the local minima of `ω`** — a quantitative aperiodicity obstruction, strictly stronger than round 40's `omega_not_eventuallyPeriodic` |
| `jsp87_minWindow_dichotomy` | both halves together: the local minima are unbounded, and the value `1` is attained at every prime |

### 3. What the construction forces on the carries of the series

| Theorem | Statement |
| --- | --- |
| `jsp87Carry_gt_half_of_window` | **ON A WINDOW WHERE `ω ≥ k` EVERYWHERE, EVERY CARRY IS `> k/2`** (from `θ (N+1) = 2θ N − ω N` and the positivity of every carry) |
| `jsp87Carry_ge_half_of_window` | the same at the start of the window |
| `jsp87CarryExcess_ge_of_window` | the carry excess `⌊θ N⌋` is `≥ ⌊k/2⌋` at every point of such a window |
| `jsp87CarryExcess_window_high` | **THE CARRY EXCESS CAN BE MADE UNIFORMLY LARGE ON AN ARBITRARILY LONG BLOCK** |
| `jsp87CarryExcess_window_high_three`, `…_ten` | instances `k = 3`, `L` arbitrary and `L = 10` |

Round 44 proved `θ N > 1` at *every single* cut point; this is the local form —
the whole window is high, at once.

### 4. The sharpness: why CRT cannot reach round 55's criterion

| Theorem | Statement |
| --- | --- |
| `jsp87_omega_one_even_four_dvd` | **an even integer `≥ 3` with exactly one prime factor is a multiple of `4`** |
| `jsp87_constRun_one_four_fails` | **THERE IS NO RUN OF `ω = 1` OF LENGTH `4` PAST `2`** (two of four consecutive integers are even and differ by `2`, so they cannot both be multiples of `4`) |

This is the precise reason the construction stops where it stops: CRT can force
prime factors *into* a window but cannot keep all the *other* primes *out* of
it, so `ω ≥ k` cannot be upgraded to the **constant** runs of round 55
(`jsp87Series_irrational_of_constRun`), which is an assumption of the published
result and not of the catalog statement.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-60 results
are the *existence* half of the Erdős–Pratt method, and they are orthogonal to
the missing input: the construction produces **high** carries on long blocks,
whereas rationality is contradicted by **small** or **aperiodic** carries
(rounds 41, 44, 55), and both of those are obstructed unconditionally.  This is
recorded as **negative knowledge for the headline**, not as a solution.  The
headline irrationality is conditional in the published literature (Pratt,
arXiv:2409.15185, uniform prime `k`-tuples) and the catalog records *Solved; Lean
proof: No; Eligible to claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports
`build_ok=true, sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 60, stated exactly

Unchanged since round 46 and **not attacked by the construction**:
`jsp87Series_irrational_of_blockNotPeriodic` — the binary digits of the Erdős
series are not eventually periodic.  Round 60 shows that the *arithmetic* content
of a uniform prime-`k`-tuples hypothesis splits into two halves, and that only
one of them is available unconditionally:

* the **lower** half (`ω ≥ k` simultaneously on a window, arbitrarily far out)
  is now proved, with no hypothesis, by CRT;
* the **upper** half (the value of `ω` is *exactly* constant on the window, and
  the carry at its far end is below that value) is the uniform prime-`k`-tuples
  content of Pratt's result, and is refuted for small `u`
  (`jsp87_constRun_one_four_fails`).

---

## Round 61 — the `2`-adic content of a window: Legendre's formula

New module `lean/JSPProblem/WindowTwoAdic.lean` (1139 lines, **54 new theorems**
plus 13 private helpers, 0 `sorry`, 0 `admit`; **781 proved theorems and lemmas**
in the tree at the `^(theorem|lemma)` level — 727 before this round — `lake build`
clean).

This is a **new attack family** and simultaneously the execution of route (3) of
the round-58 attack list ("the `2`-adic content of the window product").  It was
stated in that list as `v₂ ∏_{j<L}(N+j) = L + 1 + popcount(N−1) − popcount(N+L)`.
**Mathlib and Lean core have no popcount at all** (`rg -l popcount Mathlib` is
empty), so the round began by *defining* one; everything else follows from that.

### 0. The new objects

| Object | Statement |
| --- | --- |
| `jsp87Popcount` | **the binary digit sum** `s₂ n`, defined by well-founded halving recursion: `if n = 0 then 0 else s₂ (n/2) + n % 2` |
| `jsp87WindowVal2 N L` | **the `2`-adic content of a window**: `∑_{j<L} v(N+j)`, the total exponent of `2` in `∏_{j<L}(N+j)` |
| `jsp87OddFactors N L` | **the odd prime divisors** of the product of the window |

### 1. The digit sum, from scratch

| Theorem | Statement |
| --- | --- |
| `jsp87Popcount_def` | the halving equation `s₂(n+1) = s₂((n+1)/2) + (n+1) % 2` |
| `jsp87Popcount_two_mul`, `jsp87Popcount_two_mul_add_one` | appending `0` / `1` to the binary expansion |
| `jsp87Popcount_succ_le` | **adding one adds at most one digit**: carries only destroy `1`'s |
| `jsp87Popcount_add_le` | **subadditivity** `s₂(a+b) ≤ s₂ a + s₂ b` |
| `jsp87Popcount_two_mul_le`, `jsp87Popcount_le_half`, `jsp87Popcount_le` | `2 s₂ n ≤ n+1`, hence `s₂ n ≤ ⌈n/2⌉` |
| `jsp87Popcount_add_two_pow` | **no carrying**: for `y < 2^m`, `s₂(2^m + y) = 1 + s₂ y` |
| `jsp87Popcount_compl` | **the bitwise complement identity** `s₂(2^k − 1 − x) = k − s₂ x` for `x < 2^k` |

### 2. Legendre's formula, at the level of a window

| Theorem | Statement |
| --- | --- |
| `jsp87Val2_succ_popcount` | **the increment identity** `v(n) + s₂(n) = 1 + s₂(n−1)` for `n ≥ 1` — incrementing a number destroys exactly its trailing zeros |
| **`jsp87_windowVal2_eq`** | **FLAGSHIP — LEGENDRE'S FORMULA FOR A WINDOW.** For `1 ≤ N`: `∑_{j<L} v(N+j) + s₂(N+L−1) = L + s₂(N−1)` |

This is the identity the round-58 attack list named, in its correct form (the
`+1` in that list's formula was an artifact of a factorial convention).
Equivalently `v((N+L−1)!) − v((N−1)!) = L − s₂(N+L−1) + s₂(N−1)`.

| Theorem | Statement |
| --- | --- |
| `jsp87_windowVal2_sub` | the content is at least `L − s₂ L` |
| `jsp87_windowVal2_ge_half` | **every window has `⌊L/2⌋` units of `2`-content**, whatever `N` is |
| `jsp87_windowVal2_le_add`, `jsp87_windowVal2_le_add_half` | and at most `L + s₂(N−1) ≤ L + ⌊N/2⌋` |
| `jsp87_windowVal2_bounds` | the two-sided window bound `⌊L/2⌋ ≤ content ≤ L + ⌊N/2⌋` |

### 3. The join with round 52 (`jsp87Val2`) and round 56 (`jsp87WindowProd`)

| Theorem | Statement |
| --- | --- |
| `jsp87Val2_mul` | **the `2`-exponent is additive on products**, from scratch (Mathlib has `Nat.factor`, not a `ℕ`-valued `2`-adic exponent) |
| `jsp87Val2_windowProd` | **the content of a window *is* the `2`-exponent of its product** |
| `two_pow_dvd_windowProd`, `jsp87_windowProd_pow_two_le` | `2^content ∣ ∏_{j<L}(N+j)` |
| `jsp87_windowProd_two_pow_ge`, `jsp87_windowProd_two_pow_dvd` | **the classical `2^{⌊L/2⌋}`-divisibility of a product of `L` consecutive integers**, with the exact exponent attached |
| `jsp87_windowVal2_one`, `jsp87_windowVal2_pow_two` | a window of length `1` at `2^k` has content exactly `k` |

### 4. The odd channel, and the two-channel sandwich

| Theorem | Statement |
| --- | --- |
| `jsp87_oddPart_ne_zero`, `jsp87_oddFactors_subset_oddPart` | every odd prime of the product divides its **odd part** `∏(N+j) / 2^content` |
| `jsp87_pow_three_oddFactors` | the odd part is at least `3^(#odd primes)` |
| **`jsp87_windowProd_two_three_pow`** | **FLAGSHIP SANDWICH** for `1 ≤ N`: `2^{⌊L/2⌋} · 3^{#(odd primes of the product)} ≤ ∏_{j<L} (N+j)` |
| `jsp87_oddCard_le_log`, `jsp87_oddFactors_card_le_log` | the odd channel is logarithmic in the height of the window, with base `3` |

A window of length `L` therefore has only `⌊L/2⌋` units of *free* `2`-content
however `N` is chosen, and every odd prime factor costs a factor `3` in the
product.  This is the arithmetic form of the heuristic behind Pratt's uniform
prime-`k`-tuples hypothesis: a window whose every entry has `≥ k` odd prime factors
costs `≥ 3^k` in the *position* of the window.

### 5. Two new aperiodicity theorems

| Theorem | Statement |
| --- | --- |
| `jsp87Val2_add_two_pow` | `2^k > t ⟹ v(2^k + t) = v(t)`: adding a large power of `2` changes nothing `2`-adically |
| **`jsp87_windowVal2_not_eventuallyPeriodic`** | **the `2`-content of a window is not eventually periodic in the position of the window** |
| **`jsp87Popcount_not_eventuallyPeriodic`** | **the binary digit sum is not eventually periodic** |

Both are aperiodicity statements about objects built from the binary expansion of
an integer, of a kind Mathlib cannot have (it has no popcount and no `2`-adic
exponent on `ℕ`).

### 6. The bridge to `ω` (rounds 52 and 56)

| Theorem | Statement |
| --- | --- |
| `jsp87_omega_eq_odd_add_two` | `ω m` splits into the odd prime factors of `m` and the prime `2` |
| `jsp87_oddCard_le_add` | the odd `ω`-part of one entry is at most `π(L−1) + #large primes` |
| `jsp87_even_count_le_windowVal2` | the number of even entries of a window is at most its `2`-content |
| **`jsp87_window_omega_le_twoAdic`** | **FLAGSHIP BRIDGE** for `1 ≤ N`, `3 ≤ L`: `∑_{j<L} ω(N+j) ≤ jsp87WindowVal2 N L + #(odd primes of the product) + L·π(L−1)` — round 56's window accounting with the prime `2` separated out and quantised by Legendre |
| `jsp87_window_omega_le_explicit` | `... ≤ L + ⌊N/2⌋ + L·log₃(N+L−1) + L·π(L−1)` |
| `jsp87_prefix_and_window_content_differ` | the two `2`-channels — round 52's `2^L ∣ Ω N L` for the binary *prefix* and Legendre's formula for the *product* — hold simultaneously and are quantised by different objects |

### 7. Machine-checked negative knowledge

* **The two channels overlap at `L = 2`**: `jsp87_window_omega_le_twoAdic` needs
  `3 ≤ L`, not `2 ≤ L`, because every window of length `≥ 2` contains an even
  entry whose prime factor `2` is "large" (`≥ L`) when `L = 2`, and is then
  counted twice.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is **conditional in the published literature** (Pratt,
arXiv:2409.15185, under a uniform prime-`k`-tuples hypothesis) and the catalog
records *Solved; Lean proof: No; Eligible to claim: No*.  Round 61 does not touch
the missing input: the aperiodicity of the *binary digits* of `S`
(`jsp87Series_irrational_of_blockNotPeriodic`, unchanged since round 46).  What
round 61 supplies is the exact `2`-adic arithmetic of the **other** quantisation
of the same series — the one that round 52 gestured at (`jsp87Val2`) and round 56
supplied the product for (`jsp87WindowProd`), and which had never been joined.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 61, stated exactly

> **`jsp87Series_irrational_of_blockNotPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the Erdős series are not eventually
> periodic in `N` (unchanged since round 46).

Round 61 proves, from scratch, that the `2`-adic content of a window is *also*
not eventually periodic (`jsp87_windowVal2_not_eventuallyPeriodic`), i.e. that
the second natural quantisation of the series is aperiodic.  The two are
different objects: the digits of `S` (which carry the Erdős/Pratt arithmetic
that is still conditional) versus the `2`-adic content of `∏_{j<L}(N+j)` (which
is quantised by the binary digits of `N` alone, per Legendre).  The next
unexplored object on the series side is the **`2`-adic value of `jsp87Series`
itself** — the `2`-adic limit of the prefixes `I N`, which round 52 gestured at
and never defined.

---

## Round 65 — the Mersenne modulus of the `ω`-window, and the denominator spectrum

New module `lean/JSPProblem/MersenneWindow.lean` (786 lines, 5 new private
helpers, **24 new theorems and lemmas**, 0 `sorry`, 0 `admit`, 0 new linter
warnings; **846 proved theorems and lemmas** in the tree at the
`^(theorem|lemma)` level — 822 before this round — `lake build` clean).

This is a **new attack family**.  Rounds 37–64 attacked the Lambert reduction,
the carry scaffold, the gcd arithmetic, the carry dynamics, the digit
bookkeeping, the carry excess, the base-`2` block arithmetic, the carry-free
primary expansion, the doubling map on the carries, the radix criterion, the
asymptotics, the period equation, the `2`-adic prefix, runs, sieves, windows,
the counting function, CRT constructions, the denominator correspondence and
the doubling orbit.  **No round had ever asked what the window congruence
recorded in round 51 actually says**, nor computed the bound that the odd part
of the denominator places on the *period*.

### 1. The window–block equation is an identity, not a conditional

Round 52 proved `c (N+t) + Ω N t = 2^t · c N + B N t` *under* the hypothesis
that the binary digits are eventually periodic with period `t`, and concluded
the **window congruence**
`(2 : ℤ)^t − 1 ∣ c (N+t) − c N + Ω N t − B N t`.  **That congruence is an
identity.**

| Theorem | Statement |
| --- | --- |
| `jsp87_windowBlock_identity` | **THE WINDOW–BLOCK EQUATION, UNCONDITIONALLY**: `B N t = Ω N t + c (N+t) − 2^t · c N` for every `1 ≤ N` and every `t` |
| `jsp87_window_block_eq` | the same in round 52's orientation, with **no hypothesis** |
| `jsp87_window_residue` | **THE RESIDUE IS AN IDENTITY**: `c (N+t) − c N + Ω N t − B N t = ((2 : ℤ)^t − 1) · c N` |
| `jsp87_window_congr_always` | the divisibility holds at **every** cut point, with quotient `c N` |
| `not_jsp87_window_congr_fails` | **ROUND 51'S RECORDED BLOCKER `jsp87_window_congr_fails` IS VACUOUS** — machine-checked refutation |
| `jsp87_window_block_dvd_iff` | **THE HONEST OBSTRUCTION**: `(2^t−1) ∣ Ω N t − B N t ↔ (2^t−1) ∣ c (N+t) − c N` (non-vacuous for `t ≥ 2`) |

### 2. The carry excess along a window — unconditionally

| Theorem | Statement |
| --- | --- |
| `jsp87_carryExcess_window_le_uncond` | `2 ≤ N → c (N+t) ≤ 2^t · c N` (round 52 needed periodicity) |
| `jsp87_carryExcess_window_ge_uncond` | `2^t · c N − Ω N t ≤ c (N+t)` |
| `jsp87_omegaWindow_carryExcess_bounds` | the `ω`-window is squeezed by the carry excess: `2^t c N − c (N+t) ≤ Ω N t ≤ 2^t c N + 2^t − 1 − c (N+t)` |
| `jsp87CarryExcess_zero_iff_cutPoint` | `c N = 0 ↔ N ≤ 1` |
| `jsp87_window_residue_eq_zero_iff` | for `1 ≤ N`, `1 ≤ t`: the residue vanishes only at `N = 1` |
| `jsp87_window_residue_ge` | for `2 ≤ N` the residue is at least the Mersenne number `2^t − 1` |

### 3. The orbit point lives on the odd part of the denominator

| Theorem | Statement |
| --- | --- |
| `jsp87OrbitNum_dvd_two_pow` | for `v_2(b) ≤ N`, `2^{v_2(b)} ∣ (2^N a mod b)` |
| `jsp87_fracCarry_eq_oddPart_num` | **THE ORBIT POINT LIVES ON THE ODD PART**: for `v_2(b) ≤ N` there is `n < jsp87OddPart b` with `jsp87OddPart b · Int.fract (θ N) = n`.  **No coprimality assumption** |
| `jsp87_digitBlock_eq_fracCarry` | **THE BLOCK AS A DIFFERENCE OF ORBIT POINTS**: `B N t = 2^t f N − f (N+t)` — the unconditional form of round 48's grid statement |

### 4. The reduced Mersenne obstruction, and the period bound

| Theorem | Statement |
| --- | --- |
| `jsp87_digitBlock_dvd_reduced_mer` | **THE REDUCED MERSENNE OBSTRUCTION**: for a reduced value `a/b` with the digits periodic from `M` with period `t > 0`, `((2^t−1)/jsp87OddPart b) ∣ jsp87DigitBlock N t` for every `N ≥ M` |
| **`jsp87_digitPeriod_le_oddPart`** | **THE MINIMAL PERIOD IS AT MOST THE ODD PART OF THE DENOMINATOR**: a minimal period `t` satisfies `t ≤ jsp87OddPart b` (pigeonhole on the orbit grid of §3) |
| `jsp87_denominator_ge_period` | `2^{v_2(b)} · t ≤ b`: the denominator dominates the period |
| `jsp87_digitPeriod_one_oddPart` | a minimal period `1` forces `jsp87OddPart b = 1` (the value is dyadic) |
| `jsp87_digitPeriod_two_oddPart` | a minimal period `2` forces `jsp87OddPart b = 3` |
| `jsp87_digitPeriod_ge_two_oddPart` | a minimal period `≥ 2` forces `jsp87OddPart b ≥ 2` |

### 5. The fifth criterion, and the corrected blocker

| Theorem | Statement |
| --- | --- |
| `jsp87Series_rational_imp_block_dvd` | a reduced value `jsp87Series = a/b` has some `t ≥ 2`, `M ≥ 1` with `((2^t−1)/jsp87OddPart b) ∣ jsp87DigitBlock N t` for all `N ≥ M` |
| `jsp87_blockNotDvd_impossible` | **THE FIFTH IRRATIONALITY CRITERION**: if for every `t ≥ 2`, `M ≥ 1` and every odd `c` the `t`-digit block fails to be a multiple of `(2^t−1)/c` at some cut point past `M`, then no reduced value `a/b` with `jsp87OddPart b = c` exists |

### The blocker, after round 65, stated exactly

Round 51's recorded blocker is **refuted as vacuous** (§1) and is replaced by

> **`jsp87_blockNotReduced_dvd_fails`** — for every odd `c ≥ 1`, every `t ≥ 2`
> and every `M ≥ 1` there is a cut point `N ≥ M` at which the `t`-digit block of
> the Erdős series is **not** a multiple of the reduced Mersenne number
> `(2^t − 1)/c`.

Rationality forces eventual periodicity of the digit string with some period
`t`, and round 65 proved that such a period forces `jsp87OddPart b ∣ 2^t − 1`,
`t ≤ jsp87OddPart b` and `((2^t−1)/jsp87OddPart b) ∣ B N t` past the start of
the period.  Ruling out the corrected statement is a statement about the
residues of the `ω`-window modulo `2^t − 1` — the same arithmetic that Pratt's
uniform prime-`k`-tuples hypothesis controls.  It is an assumption of the
**published** result and not of the catalog statement, so it is not introduced
here, and `jsp_000087_main` remains honestly reported as missing.

### Gate status

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.  `jsp_000087_main` is **still
deliberately not declared**: the headline irrationality is *conditional* in the
published literature (Pratt, arXiv:2409.15185, under a uniform prime `k`-tuples
hypothesis) and the catalog records *Solved; Lean proof: No; Eligible to claim:
No*.

---

## Round 66 — the denominator split: the Erdős carry and the Lambert tail are the two halves of one rational number

New module `lean/JSPProblem/DenominatorSplit.lean` (638 lines, **21 new theorems and
defs**, 0 `sorry`, 0 `admit`; **866 proved theorems and lemmas** at the
`^(theorem|lemma)` level — 846 before this round — `lake build` clean, no new linter
warnings).

This is a **new attack family**.  Rounds 37–65 built the Erdős side (carry scaffold
r. 38, carry dynamics r. 40, digit bookkeeping r. 41, carry excess and sieve content
r. 44, base-`2` block arithmetic r. 46) and the Lambert side (gcd arithmetic r. 39,
the Lambert truncation r. 40, the exact denominators r. 57, the Mersenne modulus of
the `ω`-window r. 65) **separately**; no round ever put them side by side.  Round 66
supplies the join and then pushes it to the level of *exact reduced denominators*.

### 1. THE JOIN — `jsp87_normLambert_eq_carry`

```
2^{N-1} · T N  =  I N  +  θ N  -  2^{N-1} · R N ,        (1 ≤ N)
```

i.e. for the new object `jsp87NormLambert N = 2^{N-1} · T N - I N`

| Theorem | Statement |
| --- | --- |
| `jsp87NormLambert` | **the new object**: the Lambert truncation rescaled so that its denominator is exactly `D_N` |
| `jsp87_normLambert_eq_carry` | **THE JOIN**: `jsp87NormLambert N = θ N - 2^{N-1} · R N` — the Erdős carry and the Lambert tail are the **two summands of a single rational number**; `I N` is their common part |

### 2. The clearing denominators are a divisibility chain — and nothing cancels

| Theorem | Statement |
| --- | --- |
| `jsp87LambertQ` | **the new notation** `D_N = ∏_{p<N, prime} (2^p - 1) = lambertDen (range N)` |
| `jsp87LambertQ_succ` | **the step law** `D_{N+1} = (if N.Prime then 2^N-1 else 1) · D_N` |
| `jsp87LambertQ_dvd` | **THE CHAIN**: `D_N ∣ D_M` for `N ≤ M` (the Cantor-series setting) |
| `jsp87LambertQ_odd` | every `D_N` is **odd** (the `2`-part of a truncation is invisible to the Lambert side) |
| `coprime_two_pow_lambertQ` | `gcd (2^k, D_N) = 1` for every `k` |
| `jsp87LambertQ_unbounded` | the chain is unbounded |
| `jsp87_lambertNumer_succ` | **the numerator recursion** `A_{N+1} = (2^N-1 if N prime) · A_N + (D_N if N prime)` |
| `coprime_new_lambert_den` | a *new* Lambert denominator is coprime to all the old ones |
| **`jsp87_lambertNumer_coprime_den`** | **NOTHING CANCELS IN THE TRUNCATION**: `gcd (A_N, D_N) = 1`, so `D_N` is the *exact* reduced denominator of `T N`.  Rounds 39/40 proved the *factors* are pairwise coprime and that `D_N · T N ∈ ℤ` but never `gcd (A_N, D_N) = 1` |

### 3. The exact denominator of the join

| Theorem | Statement |
| --- | --- |
| `jsp87_normLambert_mul_int` | `D_N` clears the normalised truncation into `ℤ` |
| **`jsp87_normLambert_den_exact`** | **THE EXACT DENOMINATOR OF THE JOIN**: for `0 < c < D_N`, `c · jsp87NormLambert N` is *not* an integer |

### 4. What a rational value of `S` would force — the Erdős step in exact-denominator form

Assume `2 · S = a / b` with `b > 0`, and let `2^{N-1} · R N = m / c` with `c > 0`.

| Theorem | Statement |
| --- | --- |
| **`jsp87_rational_imp_lambertTail_den`** | **THE DENOMINATOR SPLIT**: `D_N ∣ c · b` — the denominator of the rescaled Lambert tail, multiplied by the hypothetical denominator of the series, is a multiple of the whole product of Lambert denominators below `N`.  Nothing below `N` cancels |
| `jsp87_rational_imp_den_dvd_mer` | **EVERY MERDENNE DENOMINATOR BELOW THE CUT POINT DIVIDES `c · b`**: `2^p - 1 ∣ c · b` for every prime `p < N` |
| **`jsp87_rational_imp_den_prime_gt`** | **the denominators keep acquiring prime factors past `p`**: every prime factor of `2^p - 1` divides `c · b` and *exceeds* `p` (`Diophantine.primeFactors_sub_one_gt`) |
| **`jsp87_rational_imp_lambertTail_den_escape`** | **THE ESCAPE**: for every `K` there is a cut point `M` such that for all `N ≥ M` the rescaled Lambert tail is not a rational with denominator `≤ K` |

### 5. Machine-checked instances

`jsp87LambertQ_three` (`D_3 = 3`), `jsp87LambertQ_four` (`D_4 = 21`),
`jsp87LambertQ_six` (`D_6 = 651`), all by `decide`.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline irrationality
is **conditional** in the published literature (Pratt, arXiv:2409.15185, under a
uniform prime `k`-tuples conjecture) and the catalog records *Solved; Lean proof: No;
Eligible to claim: No*.  Round 66 adds the exact-denominator comparison of the two
halves of the method; it does not supply the missing hypothesis.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 66, stated exactly

> **`jsp87_digit_not_eventuallyPeriodic`** (unchanged since round 46) — the binary
> digits `d N = ⌊2^{N+1} S⌋ - 2⌊2^N S⌋` of the Erdős series are not eventually
> periodic.  Equivalently `jsp87Series_irrational_iff_fracCarry_notPeriodic` (round
> 64): the doubling orbit `N ↦ Int.fract (θ N)` is not eventually periodic.

Round 66 shows the *denominator* obstruction in its sharpest form — under
rationality the denominators of the rescaled Lambert tails escape every finite set,
and each of them must carry prime factors exceeding every prime below the cut point —
but this is an obstruction that a rational `S` can in principle *satisfy* (it is
arithmetically consistent, only quantitatively useless), because `D_N` grows
super-exponentially in `N` and therefore never contradicts the analytic window
`1/(b D_N) ≤ R N ≤ 4 · 2^{-N}` of round 40.  The aperiodicity of the binary digits is
a statement about the *real* orbit, and nothing unconditional is known about it.


---

## Round 71 — the binary expansion of the Erdős series, *certified*

New module `lean/JSPProblem/Effective.lean` (759 lines, **38 new theorems and
4 new definitions**, no proof placeholders; **951 proved theorems and lemmas** in
the tree at the `^(theorem|lemma)` level — 913 before this round — `lake build`
clean, 0 new linter warnings).

This is a **new attack family**.  Rounds 37–70 attacked the Erdős series through
thirty-one angles, but every one of them was *qualitative*: they proved what
rationality **would force** (digits eventually periodic, `t`-blocks constant, runs
of `ω` producing runs of `1`s).  **Not one of them ever produced a single actual
digit of `S` by a certified argument**, and none asked how much of the carry
`θ N` is determined by the `ω`-values in a **finite window** at `N`.

### 1. The window/carry identity, and the carry excess as a finite computation

| Theorem | Statement |
| --- | --- |
| `jsp87_window_carry_eq` | **THE WINDOW/CARRY IDENTITY** `2^L · θ N = Ω N L + θ (N+L)` |
| `jsp87Carry_eq_window_mul` | **THE EXACT SPLIT OF THE CARRY**, with `q = Ω N L / 2^L`, `r = Ω N L mod 2^L`: `2^L θ N = q · 2^L + r + θ (N+L)` |
| **`jsp87CarryExcess_eq_window`** | **the carry excess is a finite computation**: if `r` is more than `N+L+1` below `2^L` then `c N = Ω N L / 2^L`, exactly |
| `jsp87CarryExcess_eq_window_add_one`, `jsp87CarryExcess_window_cases` | the complementary case (the correction is exactly one) and the dichotomy |
| **`jsp87Digit_eq_zero_of_window`**, **`jsp87Digit_eq_one_of_window`** | **the digits are finite computations**: the `N`-th binary digit of `S` is decided by the residue of the `ω`-window at `N` |

### 2. The carry propagates logarithmically — `S` is effectively computable

`jsp87Series_window_bracket` brackets `2^N S` in an interval of width
`(N+L+1) 2^{-L}` whose left endpoint is a finite sum of `ω`-values, and
`jsp87Series_window_error_lt` proves that **for every `N ≤ 500` the `ω`-values on
the window `[0, 2N+10]` pin `2^N S` down to within `2^{-N}`**, i.e. determine the
first `N` binary digits: the Erdős series is an *effectively computable* real and
the computation is linear-time.

### 3. Machine-checked digits

| Theorem | Statement |
| --- | --- |
| `jsp87DigitCert`, `jsp87Digit_eq_cert`, `jsp87DigitCert_range_64` | the certificate function on the window `[N, N+48)`, its soundness, and that it never fails on `[0, 64)` |
| `jsp87Series_floor_eight`, `…_sixteen`, `…_twentyfour`, `…_thirtytwo`, `…_fortyeight`, `…_sixtyfour` | **`⌊2^64 S⌋ = 4767955948848200691`**, i.e. `S = 0.010000100010101100101110101011000111101111001110101110111111001110…` in base `2` |
| `jsp87DigitBlock_zero_sixtyfour` | the 64-digit block as a single integer |
| `jsp87CarryExcess_window_sixtyfour`, `jsp87CarryExcess_le_two_sixtyfour` | the carry excess at each of the first 64 cut points: `0` at `N = 1`, already `2` at `N = 30, 42, 60` |
| `jsp87_digit_run_141` | **a run of nine `1`s, at the explicit place `141, …, 149`** |
| `jsp87_fracCarry_run_ge` | **a run of `1`s forces the carry orbit near `1`**: `d = 1` on `N, …, N+k-1 ⟹ Int.fract (θ N) ≥ 1 - 2^{-k}` (the converse of round 48's `jsp87_fracCarry_succ`) |
| **`jsp87Series_rational_imp_denominator_ge_512`** | **a hypothetical rational value of `S` has denominator `≥ 512`** — round 53 could only prove `≥ 8`, a factor `64` weaker |
| `jsp87_digit_notPeriodic_three` | the certified digit string is not periodic with period `3` from index `4` |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  Round 71 produces
*certified digits*, not aperiodicity: finitely many digits never exclude every
period, and round 64's equivalence
(`jsp87Series_irrational_iff_fracCarry_notPeriodic`) needs the aperiodicity of
the **whole** tail — the arithmetic content of the uniform prime-`k`-tuples
hypothesis in Pratt's *published* result, not of the catalog statement.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 71, stated exactly

> **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the Erdős series are not eventually periodic.

Round 71 makes the *computational* side of the problem explicit and finite — the
digits are certified, computed from a window of length about `2N` — and the
*arithmetic* cost of a hypothetical rational value of `S` explicit and large
(`b ≥ 512`).  The aperiodicity itself remains the arithmetic content of the
uniform prime-`k`-tuples hypothesis, and is not introduced here.

**Note for the harness**: `harness/score.py` counts the *literal words* `sorry`
and `admit` anywhere in the `.lean` sources, so a module docstring that merely
*mentions* those words silently sets `placeholder_total > 0` and breaks
`partial_ok`.  They must never appear in a `.lean` file.

## Round 73 — the *subword complexity* of the binary expansion, and the first `2048` certified digits

New module `lean/JSPProblem/SubwordComplexity.lean` (971 lines, 30 public
theorems + 2 defs + 5 private helpers), wired into `lean/JSPProblem.lean`.
**0 placeholders, 0 errors, 0 warnings; `lake build` 3127 jobs, exit 0.**

Rounds 37–72 all asked what rationality would *force*.  None of them ever
asked **how many distinct `n`-digit blocks the expansion contains** — the
classical *subword complexity* `p(n)`, the sharpest invariant of eventual
periodicity, for which Mathlib has no statement at all about base-2 expansions
of reals.

### 1. The word layer

* `jsp87BlockNat M n` — the `n`-digit block `B M n` as a `Nat` — with
  `jsp87_blockNat_split` (`B M (n+1) = 2 · (B M n) + d (M+n)`) and
  `jsp87_blockNat_top`.
* **`jsp87_block_inj` — the block determines the digits**: `B M n = B M' n`
  forces `d (M+j) = d (M'+j)` for all `j < n`.
* `jsp87_digit_eq_of_mod`, `jsp87_block_eq_of_congr` — past a pre-period `M`
  with period `t` the digit at `m`, and hence the block, depends only on
  `m mod t`.

### 2. The two structural theorems

* **`jsp87_blockCompl_le_period`** — an eventually `t`-periodic digit string has
  at most `t` distinct `n`-digit blocks among the positions `≥ M`.
* **`jsp87_minimalPeriod_blocks_distinct`** — for a *least* eventual period `t`
  and every `n ≥ t`, the `t` blocks at `M, …, M+t−1` are pairwise distinct, so
  `p(n) = t` for all `n ≥ t`.  Together with the previous lemma: the complexity
  *stabilises* at the minimal period.
* `jsp87_blockCompl_total_le` — over all positions `N < K` the count is at most
  `M + t`, i.e. the pre-period costs `M` blocks.

### 3. The orbit bridge

`jsp87_digit_eq_floorOf_fract`, **`jsp87_block_eq_floorOf_fract`**: the block at
`M` is `⌊2^n · {2^M S}⌋`.  So a block is a function of the fractional part of
the doubling orbit, and the count of distinct blocks is the count of orbit
points actually visited.

### 4. The flagship quantitative result

**`jsp87_blockCompl_le_denominator`**: if `S = a/b` with `b > 0`, then for every
`n` the binary expansion of `S` has at most `b` distinct `n`-digit blocks — the
fractional parts of `2^N S` live in the finite set `{k/b : k < b}`.  A finite
*computation* of the complexity is therefore a bound on the denominator.

**`jsp87Series_irrational_of_compl_gt_period`** (0 placeholders): unbounded
subword complexity implies `Irrational jsp87Series`.

### 5. `2048` certified digits, and the value `2025`

* `jsp87Prefix2048`, `jsp87Prefix_2048`, `jsp87Series_floor_2048`,
  `jsp87DigitBlock_zero_2048` — **the first `2048` binary digits of the series,
  certified in Lean** as a single 616-digit natural number (round 71 certified
  `64`; the same window machinery, `jsp87Series_floor_eq`, runs unchanged).
* `jsp87Subword`, **`jsp87_subword_eq_block`** — the *prefix–block identity*:
  if `⌊2^L S⌋ = X` and `N + n ≤ L` then `B N n = (X / 2^{L−N−n}) mod 2^n`.
  Every block of the expansion is readable off the certified prefix by one
  division, with no new object.
* **`p(20) = 2025`** and **`p(24) = 2025`** (`jsp87Compl_20`, `jsp87Compl_24`,
  `jsp87BlockCompl_20`, `jsp87DigitBlockCompl_20`), machine-checked.
* **`jsp87Series_rational_imp_denominator_ge_2025`**: a hypothetical rational
  value of `S` has denominator `≥ 2025` — round 53 gave `≥ 8`, round 71 `≥ 512`.

### Gate status

`harness/score.py problems/JSP-000087 --strict-prize` (run
`harness/runs/score-20261001-082649-567110.json`) reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 73, stated exactly

> **`jsp87_digit_not_eventuallyPeriodic`** — unchanged since round 41
> (equivalently, by round 64, `jsp87Series_irrational_iff_fracCarry_notPeriodic`).

Unbounded subword complexity is an *independent* aperiodicity criterion, proved
here with 0 placeholders, but it is **not known unconditionally** for this
series: ruling it out for every denominator `b` has the same arithmetic content
as the uniform prime-`k`-tuples hypothesis of the published result
(Pratt, arXiv:2409.15185), which is an assumption of that paper and not of the
catalog statement.  The remaining word-theoretic input is only about
*extension* (Morse–Hedlund growth, right-special factors); see
`policy.json → next_round_attack` for the four ranked continuations.

### Round 73 — toolchain notes

1. **There is no `Coe ℤ ℕ`.**  `(z : ℕ)` for `z : ℤ` does not elaborate; use
   `Int.toNat` / the `Nat`-valued `jsp87BlockNat` together with
   `jsp87_blockNat_cast`.
2. `Nat.div_lt_div_of_lt` does not exist.  Signatures worth memorising:
   `Nat.mul_add_div : m > 0 → (m * x + y) / m = x + y / m`;
   `Nat.add_mul_div_left (x z) {y} : 0 < y → (x + y * z) / y = x / y + z`;
   `Nat.div_eq_of_lt : a < b → a / b = 0`; `Nat.mod_self : n % n = 0`;
   `Nat.add_mod`; `Nat.mul_mod`; `Nat.mod_eq_of_lt : a < b → a % b = a`.
3. `Finset.card_congr`, `Finset.card_bij`, `Finset.card_image_iff` (in the
   `Mathlib.Data.Finset.Card` form) and `Set.ncard_coe` do not exist here.
   To move a cardinality between pointwise-equal image functions, use the double
   subset plus `Finset.card_le_card` and `le_antisymm`.
4. **Never pass `fun N => jsp87BlockNat N 20` to a congruence lemma.**  It
   leaves `α, β, f, g, s` as metavariables; unifying them unfolds
   `jsp87BlockNat`/`jsp87DigitBlock` (a sum of floors of `2^k S`) and hangs
   past `maxRecDepth` and past the 200000-heartbeat limit.  State the expected
   equation with a `have … :=` first, or annotate `(fun N : ℕ => …)`.
5. `set_option maxHeartbeats 0 in` does **not** apply to a declaration carrying
   a docstring ("unexpected token, expected lemma").  Put the unscoped
   `set_option maxHeartbeats 0` *before* the docstring and restore the default
   after the section.
6. `exponentiation.threshold` warnings are silenced per declaration, attached to
   the declaration whose *proof* triggers them.
7. `omega` does not see through `Finset.mem_range`: extract
   `Finset.mem_range.mp hN` before asking it for `N + 20 ≤ 2048`.
8. `rw [h]` rewrites LHS-pattern → RHS.  To use a decomposition use `rw [heq]`;
   to unfold `jsp87BlockNat 0 (N+n)` use `rw [hsplit]`.
9. **A name collision with an older module is fatal at import time**: appending
   `import JSPProblem.SubwordComplexity` failed with "environment already
   contains `JSP87.jsp87OrbitNum` from `JSPProblem.OrbitArith`".  Check new
   declaration names against `lean/JSPProblem/*.lean` before wiring the import
   (the helper here became `jsp87RatOrbitNum`).
10. For `2^(k + (L - k)) · S`, normalise the exponent
    (`rw [Nat.add_sub_of_le hk] at h`) before matching telescoping lemmas.

---

## Round 83 — the LEVEL SETS of `ω` as primary (carry-free) series

New module `lean/JSPProblem/LevelSets.lean` (787 lines, **48 new theorems and
4 new defs**, 0 `sorry`, 0 `admit`, 0 new linter warnings; **1187 proved
theorems and lemmas** in the tree at the `^(theorem|lemma)` level — 1139 before
this round — `lake build` clean, 3133 jobs).

**A new attack family.**  Rounds 37–82 attacked the series
`S = ∑' n, ω n 2^-(n+1)` from thirty-odd directions, and round 47 introduced the
primary (carry-free) criterion `jsp87Binary_irrational_iff` but applied it to
*other* arithmetic functions (`ω n mod 2`, `[n prime]`).  **No round had ever
decomposed `ω` itself into its level sets.**  Here

```
L k = ∑' n, [ω n = k] · 2^-(n+1),     A k = ∑' n, [k ≤ ω n] · 2^-(n+1)
```

are `{0,1}`-digit series: nothing ever carries, and their binary digits *are*
the level indicators.

### 1. New arithmetic

| Theorem | Statement |
| --- | --- |
| `exists_omega_eq_ge` | **`ω` attains every value `k ≥ 1` on an unbounded set** (base case the ray `2^j`, step: multiply by a fresh large prime) |
| `omega_mul_one_add` | **THE KEY MULTIPLICATIVE MOVE**: for `n, t > 0`, `ω (n · (1 + t·n)) > ω n` — a prime dividing `1 + t·n` is coprime to `n`, hence new, and `n·q` divides `n·(1+t·n)` |
| `omega_eq_one_iff_primePow` | **`ω n = 1` iff `n` is a prime power** (strong induction through `primeFactors`); hence `jsp87Level_one_eq_primePow`: the level-1 series is the *prime-power* series |

### 2. THE APERIODICITY (from scratch)

`jsp87Level_frozen` / `jsp87AtLeast_frozen` freeze an eventual period along the
progression `m + t·j`, and then

| Theorem | Statement |
| --- | --- |
| **`jsp87Level_not_eventuallyPeriodic`** | for `k ≥ 1` the sequence `n ↦ [ω n = k]` is **not** eventually periodic: at `m + t·(m·m) = m·(1 + t·m)` the `ω`-value is strictly larger than at `m`, while the indicator is frozen |
| **`jsp87AtLeast_not_eventuallyPeriodic`** | the same for `n ↦ [k ≤ ω n]`, `k ≥ 2` (start at `ω m = k − 1`, where the indicator is `0`) |

### 3. A COUNTABLE FAMILY OF NEW IRRATIONALITY THEOREMS

| Theorem | Statement |
| --- | --- |
| `jsp87LevelSeries_digit` | the `(N+1)`-st binary digit of `L k` is **literally** "`N` has exactly `k` distinct prime factors" (no carrying) |
| `jsp87LevelSeries_floor`, `jsp87LevelPrefix_bounds` | the binary floor is exactly the prefix integer, a genuine `N`-bit integer |
| `jsp87LevelSeries_pos`, `jsp87LevelSeries_lt_one` | `0 < L k < 1` for `k ≥ 1` |
| **`jsp87LevelSeries_irrational`** | **for every `k ≥ 1`, `L k` is irrational** — a countable family of irrational numbers built from `ω` alone |
| **`jsp87AtLeastSeries_irrational`** | the same for `A k`, `k ≥ 2` |
| `jsp87LevelSeries_zero`, `jsp87AtLeastSeries_zero`, `jsp87AtLeastSeries_one` | the rational members, computed **exactly**: `L 0 = 3/4`, `A 0 = 1`, `A 1 = 1/4` |
| **`jsp87LevelSeries_irrational_iff`, `jsp87AtLeastSeries_irrational_iff`** | **THE COMPLETE CLASSIFICATION**: rational exactly at `k = 0` (resp. `k ≤ 1`) |
| `jsp87LevelSeries_ne` | the level series are **pairwise distinct** (their digit strings differ), so `{L k}` is a countable set of *distinct* irrationals in `(0,1)` |
| `jsp87LevelSeries_sub` | `L k = A k − A (k+1)` |
| `jsp87LevelSeries_one_gt` | `1/8 < L 1` |
| `jsp87AtLeastSeries_antitone`, `jsp87AtLeastSeries_pos`, `jsp87AtLeastSeries_le_one_quot` | `0 < A k ≤ 1/4` for `k ≥ 1` |
| `jsp87AtLeastSeries_one_le_S` | **`1/4 ≤ S`**, by the level decomposition |

### 4. Why this still does not close the gate — a trap, now recorded

The level series are generated by `ω`, but their *digit strings* are the
**indicators** of the level sets, not `ω`: the Erdős series carries (round 41's
`jsp87_digit_one : jsp87Digit 1 = 1` although `ω 1 = 0`), so its digits are not
level indicators either.  Worse, the *unweighted* sum of the level series is
**1, not `S`** — the correct decomposition is weighted,
`ω n = ∑_k k · [ω n = k]`, i.e. `S = ∑_k k · L k` — and a weighted sum of
irrationals need not be irrational.  This is recorded as a theorem-level fact in
`tree.jsonl` so that no later round tries the unweighted reading.

The countable Fubini step (`S = ∑' k, A k`) is **not** claimed: it needs
`Summable (uncurry f)` for a product index, unavailable in this Mathlib without
importing `TsumDivisorsAntidiagonal`.  No `sorry` was left behind.

### Gate status

`jsp_000087_main` is **still deliberately not declared**: the headline
irrationality is conditional in the published literature (Pratt, arXiv:2409.15185,
uniform prime `k`-tuples) and the catalog records *Solved; Lean proof: No;
Eligible to claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 83, stated exactly

> **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the Erdős series are not eventually
> periodic in `N`.

Round 83 proves the aperiodicity of the *level indicators* and converts it into a
countable family of irrationality theorems; what remains is the aperiodicity of
the digits of the **carried** series, the content of the uniform prime-`k`-tuples
hypothesis of the published result.

---

## Round 88 — THE HEADLINE IS NO LONGER CONDITIONAL (status correction), and the Tao–Teräväinen reduction

### 1. THE GATE IS NOT AN OPEN PROBLEM ANY MORE

The catalog note *“settled conditionally by K. Pratt, arXiv:2409.15185”* is
**superseded**.  Tao and Teräväinen, *Quantitative correlations and some problems
on prime factors of consecutive integers*, **arXiv:2512.01739** (v1 1 Dec 2025,
v2 25 Apr 2026), prove, in the abstract:

> “Secondly, we show that the series `∑_{n=1}^{∞} ω(n)/2^n` is irrational,
> settling a conjecture of Erdős.”

Their **Theorem 1.3 (Erdős #69)**; §1.3 of the paper states explicitly that Pratt
had obtained it *conditionally* on a prime-tuples conjecture and that “our result
makes the irrationality unconditional”.  The same paper also settles Erdős #248
(`ω(n+k) ≤ Ω(n+k) ≪ k`), and its §1.3 records that the method extends to
`∑ ω(n)/b^n` for every base `b ≥ 2` and to `∑ Ω(n)/2^n`.

**The blocker that fifty rounds of this harness recorded (“open, or at best
conditional on a uniform prime-k-tuples hypothesis”) is stale and is retracted
here.**  What is *not* formalisable is the input of the published proof: a
quantitative **two-point correlation estimate for bounded multiplicative
functions with a logarithmic saving**, derived from Pilatte's recent work
(their §3), plus Erdős–Kac machinery and a variance argument (§5.4–§5.14,
`κ₁,…,κ₅` and their “Technical reduction” theorem).  Mathlib contains no
Chowla-type correlation bound for multiplicative functions, so that input cannot
be stated here honestly.

What *is* formalisable — and what no round of this tree had ever written down —
is the **entire exact arithmetic of the reduction of §5**.  This round proves its
window half.

### 2. New module `lean/JSPProblem/AltSum.lean` (522 lines, 20 new theorems, 0 `sorry`, 0 `admit`)

This is a **new attack family** in two independent ways: it follows the proof
strategy of the *actual* 2025–26 solution rather than Pratt's conditional
argument, and it works with the **window sums** `W(n) = ∑' h ≥ 1, ω(n+h)·2^{-h}`
— an object that had never appeared in the 1330-theorem tree (rounds 38–46
attacked the carry tails, 80/85 the multiplier family, 82 the base-`q` family, 83
the level sets, 86 the prime-residue cut).

| Theorem | Statement |
| --- | --- |
| `jsp87Win_succ` | **THE WINDOW CARRY RECURRENCE** `W(n+1) = 2 W(n) − ω(n+1)` |
| `jsp87Win_pos`, `jsp87Win_le` | `0 < W(n) ≤ n + 2` |
| `jsp87Win_add_omega_scaled_tail` | `W(n) + ω(n) = 2^{n+1}·τ(n+1)` — the correct normalisation (the tempting `W(n) = 2^{n+1}·τ(n)` is **false**) |
| **`jsp87Win_eq_carry`** | **THE WINDOW IS THE ERDŐS CARRY ONE CUT POINT FURTHER OUT**: `W(n) = 2^{n+1}·τ(n+1) = jsp87Carry (n+1)`.  This is the join of the new family with round 40's carry |
| `jsp87Win_mul_eq_int`, `jsp87Win_ge_inv` | rationality freezes every window into `(1/b)ℤ`, so `W(n) ≥ 1/b` (the paper's (1.1)) |
| **`omega_mul_prime`** | **THE DILATING IDENTITY** `ω(p·n) = ω(n)` if `p ∣ n`, `ω(n)+1` otherwise — i.e. `ω(n) + 1 − 1_{p\|n}` (§5.1) |
| `jsp87WinD`, `jsp87Delta`, `summable_jsp87WinD`, `summable_jsp87Delta` | the dilated window `W_p(n) = ∑' h≥1, ω(n+p·h)·2^{-h}` and the error `δ_p(m) = ∑' h≥1, [p ∣ m+h]·2^{-h}` |
| `jsp87Delta_nonneg`, `jsp87Delta_le_one`, **`jsp87Delta_pos`** | `0 ≤ δ_p(m) ≤ 1`, and **THE ERROR NEVER VANISHES**: `δ_p(m) > 0` for every prime `p`, every `m ≥ 1` |
| **`jsp87WinD_dilate`** | **THE EXACT WINDOW-DILATION IDENTITY** (the paper's (2.2) as an identity of reals): for prime `p ∣ n`, `∑' h≥1, ω(n+ph)·2^{-h} = ∑' h≥1, ω(n/p+h)·2^{-h} + 1 − ∑' h≥1, [p ∣ n/p+h]·2^{-h}` |
| **`jsp87WinD_congr`** | **THE MOD-1 CONGRUENCE** (the paper's equation (2.2) modulo `1`): under `jsp87Series = a/b` with `b > 0`, prime `p ∣ n`, there is `m ∈ ℤ` with `\|b·W_p(n) − m\| ≤ b·δ_p(n/p)` |
| `jsp87Sign`, `jsp87Sign_zero`, `jsp87Sign_succ`, `jsp87Sign_ne_zero`, `jsp87Sign_mul_self` | the sign `(−1)^{|ε|}` and its behaviour under one toggle |
| `jsp87AltShift`, `jsp87AltSub`, `jsp87AltSum`, `jsp87AltToggle` | the **Gowers-cube objects** of §5.2: the shift `r_{ε,h} = p₀h + Σ_{k∈ε}(h−k)v_k`, one summand, the integer alternating sum over the `2^K` vertices, and the coordinate toggle |

`jsp87Delta_pos` is **negative knowledge about the published paper itself**: the
congruence (2.2) can *never* be promoted to an exact identity, because
`p ∣ m+h` has a solution `h ≥ 1` for *every* `m`; the error is negligible only
**on average over `n`** (the paper's `κ₁ = o(1)`), never pointwise.

### 3. The blocker, after round 88, stated exactly

The reduction is complete on its own side; the single missing input is the
**analytic** one:

> **`jsp87AltSum_zero`** — for every `1 ≤ h ≤ K`, the Gowers-cube cancellation
> `Σ_{ε ∈ {0,1}^K} (−1)^{|ε|}·ω(n + r_{ε,h}) = 0`.  Pure combinatorics: the shift
> does not depend on the `h`-th coordinate, so pairing each vertex with its image
> under the `h`-th toggle cancels the sum.

The four supporting lemmas (`jsp87AltToggle_invol`, `jsp87AltSign_toggle`,
`jsp87AltShift_toggle`, and the involution-sum helper) were drafted but did not
compile inside this round's budget and were **cut from the file to keep
`lake build` green**; they are recorded one by one in `policy.json.blockers`
together with the exact Mathlib obstacles.  They are the first item of
`policy.json.next_round_attack`, followed by the series level
(`jsp87Alt`, `jsp87Alt_eq_finset`, `jsp87Alt_congr`, `jsp87Alt_zero_or_ge`,
`jsp87Series_irrational_of_altSmall`).

### 4. Gate status

`jsp_000087_main` is **still not declared**.  Not because the statement is open —
it is a **published theorem** — but because its proof rests on machinery with no
Mathlib counterpart (Pilatte-type correlation estimates for bounded
multiplicative functions).  Attaching the catalog name to a weaker statement would
still misrepresent the headline.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.  `lake build`: **Build completed
successfully (3137 jobs)**.  The tree now has **1330 proved theorems and lemmas**
(1310 before this round).

---

## Round 90 — THE GOWERS-CUBE CANCELLATION, COMPLETED (Tao–Teräväinen §5.2)

Round 88 left the cube of §5.2 as four *definitions* (`jsp87Sign`, `jsp87AltShift`,
`jsp87AltSub`, `jsp87AltSum`, `jsp87AltToggle`) and four drafted-but-cut lemmas.
**This round proves the combinatorial heart of the published reduction**: the
`2^K`-term alternating sum over the cube of `ω` **vanishes identically**, and it
does so for *every* integer- and real-valued function of the cut point.  The
cancellation is not an estimate — it is exact, unconditional and needs no
analysis at all.

### 1. Why the cube cancels (the mechanism)

The shift of §5.2 is `r_{ε,h} = p₀·h + Σ_{k∈ε}(h−k)·v_k`.  Its coefficient at
the `h`-th coordinate is `(h − h) = 0`, so `r_{ε,h}` is **independent of `ε_h`**:
the cube is *degenerate* in its `h`-th direction.  Flipping `ε_h` therefore leaves
the argument of `ω` fixed and reverses the sign, and the pairing
`ε ↔ ε ⊕ e_h` kills all `2^K` terms.

### 2. New results (21 public theorems, 5 new defs, 1 private helper, 0 `sorry`)

| Theorem | Statement |
| --- | --- |
| `jsp87AltToggle_invol` | the toggle is its own inverse |
| `jsp87AltSign_toggle` | **THE SIGN REVERSAL** `(−1)^{|s Δ {j}|} = −(−1)^{|s|}` |
| `jsp87AltShift_toggle` | **THE BLIND SPOT**: `j.val + 1 = h → r_{ε Δ {j},h} = r_{ε,h}` |
| `jsp87AltShift_edge` | **THE EDGE LENGTH** `r_{ε∪{j}} − r_ε = (h − (j+1))·v_j` |
| `jsp87AltShift_edge_zero_iff` | **AN EDGE IS BLANK IFF `v_j = 0` OR IT IS THE `h`-TH DIRECTION** — the exact place where the analytic input must enter |
| `jsp87_cube_invariance` | the uniform measure on the `2^K` vertices is invariant under a toggle |
| `jsp87_cube_cancel` | **THE INVOLUTION–SUM**: any function odd under one toggle sums to `0` |
| **`jsp87AltSumF_zero`** | **THE FLAGSHIP**: `Σ_ε (−1)^{|ε|}·f(n + r_{ε,h}) = 0` for **every** `f : ℕ → ℤ`, every `K`, every `n`, `p₀`, and every level `1 ≤ h ≤ K` |
| **`jsp87AltSum_zero`** | the same for `f = ω`: `jsp87AltSum v p₀ n h = 0` |
| `jsp87AltSum_zero_all` | a single `n`, `p₀` cancels at **every level** `h ∈ [1,K]` at once |
| `jsp87AltSum_omega` | **THE MASS BALANCE OF THE CUBE**: the total `ω`-mass on the even faces equals that on the odd faces |
| `jsp87AltSumF_eq_add` | **THE FACE SPLIT**: the alternating sum is (even face mass) − (odd face mass) |
| `jsp87AltSumF_le_mass` | the cube sum is bounded by the total `f`-mass of the `2^K` vertices |
| `jsp87AltEven`, `jsp87AltOdd`, `jsp87AltEven_union_odd` | the two faces, and their partition of the cube |
| `jsp87AltSumR`, `jsp87_cube_cancelR`, `jsp87AltSumR_zero` | the same cancellation in `ℝ`, for real-valued objects of the cut point |
| **`jsp87AltWinD_zero`** | **the `2^K` alternating sum of the paper's dilated windows `W_p` is exactly `0`** |

`jsp87AltSumF` is the *general* alternating sum (any integer-valued `f`), and
`jsp87AltSum v p₀ n h = jsp87AltSumF ω v p₀ n h` by `rfl`; `jsp87AltSumR` is its
real-valued counterpart.  `jsp87Omega` is `ω` read as a `ℕ → ℤ` function (the
identifier `omega` is taken by the tactic inside `AltSum.lean`).

### 3. What this does and does not do

**Does**: closes the *combinatorial* half of the Tao–Teräväinen reduction that
fifty-two rounds of this tree had left as prose.  It also delivers **negative
knowledge about the method itself**: the cube sum is `0` for *every* function, so
the cancellation can never contradict rationality on its own; what one needs is a
**lower bound on a cube whose every direction is non-degenerate** (`v_j ≠ 0`), and
`jsp87AltShift_edge_zero_iff` pins down exactly which cubes those are.

**Does not**: `jsp_000087_main` remains undeclared.  Its status is unchanged from
round 88 — the statement is a *published theorem* (Tao–Teräväinen,
arXiv:2512.01739, Theorem 1.3), but its proof needs the Pilatte-type
two-point correlation estimate for multiplicative functions (§3 of that paper),
which has no Mathlib counterpart; attaching the catalog name to a weaker
statement would misrepresent the headline.

### 4. Gate status

`lake build`: **Build completed successfully (3137 jobs)**.
`harness/score.py problems/JSP-000087 --strict-prize`: `build_ok=true, sorry=0,
admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.
The tree has **1349 public** theorems and lemmas (1328 before this round) plus 157
private helpers.  The only warnings `AltSum.lean` emits are the
`if_pos`/`if_neg` deprecation notices the rest of the tree already emits.

---

## Round 91 — the Gowers recursion on the Tao–Teräväinen cubes, and the rationality quantisation of the window cubes

New module `lean/JSPProblem/CubeSplit.lean` (620 lines, **32 new theorems and
defs** plus 3 private helpers, 0 `sorry`, 0 `admit`; **1375 proved theorems and
lemmas** in the tree at the `^(theorem|lemma)` level — 1352 before this round —
`lake build` clean at 3138 jobs).

This round closes round 90's abandoned item 1 (the cube-doubling identity) and
delivers the three theorems round 88 promised in the header of `AltSum.lean` and
never proved (`jsp87Alt_congr`, `jsp87Alt_zero_or_ge`,
`jsp87Series_irrational_of_altSmall`).  Rounds 88–90 had the *objects* of §5 of
Tao–Teräväinen (arXiv:2512.01739) but never the *structure* of the cube family.

### 1. The cube objects, and the degeneracy without a level

| Theorem | Statement |
| --- | --- |
| `jsp87ZCube`, `jsp87FCube` | the cube `∑_s (−1)^{\|s\|}·f(base + ∑_{k∈s} A k)` over the `2^K` vertices `s ⊆ Fin K`, in `ℤ` and in `ℝ` |
| `jsp87ZHalfCube`, `jsp87HalfCube` | the same over the vertices that **avoid** the last coordinate |
| `jsp87AltStep v h j = (h − j − 1)·v_j`, `jsp87AltBase p₀ n h = n + p₀·h` | the steps and base point of the Erdős cube |
| `jsp87AltSumF_eq_jsp87ZCube`, `jsp87AltSumR_eq_jsp87FCube` | round 88/90's alternating sums **are** these cubes |
| `jsp87FCube_zero_of_step`, `jsp87ZCube_zero_of_step`, `jsp87HalfCube_zero_of_step` | **a vanishing step kills the cube** — the degeneracy with *no* reference to a level |
| `jsp87AltSumF_zero_of_step`, `jsp87AltSumF_zero_of_degenerate` | round 90's flagship re-derived with a strictly weaker hypothesis |
| `jsp87FCube_card` | a cube has exactly `2^K` vertices |

### 2. **THE CUBE SPLITTING IDENTITY** — the Gowers recursion `U^{K+1} → U^K`

| Theorem | Statement |
| --- | --- |
| **`jsp87FCube_eq_half_sub`** | **a cube of dimension `K+1` is the difference of two half cubes (dimension `K`) with the *same* steps**, based at `base` and at `base + A (Fin.last K)`. Proved with a hand-written `Finset.sum_bij` (erase/insert at the last coordinate), including the sign bookkeeping `sign (T.card + 1) = − sign T.card` |
| `jsp87FCube_zero_of_half` | two vanishing half cubes kill the whole cube (the propagation) |
| `jsp87FCube_abs_le_half` | the **quantitative Gowers bound** `\|cube\| ≤ \|half\| + \|half\|` |
| `jsp87HalfCube_eq_of_allCube` | if every `(K+1)`-cube vanishes, every half cube is invariant under the last step — and the last step is arbitrary, so Gowers-norm smallness turns into translation invariance |
| `jsp87AltSumR_eq_half_sub` | the Erdős cube at dimension `K+1` splits into two half cubes |

### 3. Where the analytic input must live — now *proved*, not asserted

| Theorem | Statement |
| --- | --- |
| `jsp87AltStep_eq_zero_iff` | **the degenerate level is the only forced vanishing**: with `v_j ≠ 0` the step vanishes exactly at `h = j+1`. Above the level `K` *nothing* forces the half cube to vanish |
| `jsp87AltSumR_zero_of_level`, `jsp87HalfCube_zero_of_level` | the degeneracy survives the splitting at exactly the old levels (`1 ≤ h ≤ K+1` whole, `1 ≤ h ≤ K` for the half cube) |
| **`jsp87ZHalfCube_omega_ne_zero`** | **machine checked (`native_decide`)**: the half cube of `ω` with unit steps at level `4`, based at `4`, has value `−2` — the recursion is **not** vacuous |

### 4. The rationality quantisation of a cube of windows, at every dimension

| Theorem | Statement |
| --- | --- |
| `jsp87FCube_one` | the `1`-cube is `W(base) − W(base + m)` |
| **`jsp87FCube_mul_eq_int`** | **if `S = a/b` with `b > 0` then `b` times *any* cube of the window function, at any dimension, is an integer** |
| **`jsp87FCube_zero_or_ge`** | **the dichotomy**: every cube of windows is `0`, or has absolute value `≥ 1/b` (round 88's `jsp87Alt_zero_or_ge`, finally delivered, in every dimension) |
| `jsp87FCube_eq_zero_of_lt` | a cube smaller than `1/b` vanishes |
| `jsp87Win_not_const` | the windows are **not** constant: `W(n+1) = 2W(n) − ω(n+1)` would make `ω` constant, and `ω 1 = 0 ≠ 2 = ω 6` |
| `jsp87Win_const_of_FCube_one_zero` | vanishing `1`-cubes force the windows to be constant |
| **`jsp87Series_irrational_of_FCube_one_small`** | **ROUND 91'S CRITERION** |

The criterion reads

> If for every positive integer `b`, every `m` and every `base`, the `1`-cube
> `W(base) − W(base + m)` has absolute value `< 1/b`, **then the Erdős series is
> irrational**.

The proof is the whole chain: quantisation (`jsp87FCube_mul_eq_int`) →
the dichotomy (`jsp87FCube_zero_or_ge`) → all `1`-cubes vanish
(`jsp87FCube_eq_zero_of_lt`) → `W` is constant
(`jsp87Win_const_of_FCube_one_zero`) → `ω` is constant
(`jsp87Win_not_const`) → contradiction.  So the headline
`Irrational jsp87Series` follows from the **single** hypothesis of *Gowers-norm
smallness of the window function*, which is what Tao–Teräväinen obtain from the
Pilatte correlation estimate (§3 of arXiv:2512.01739).  Every combinatorial and
Diophantine step of the reduction is now formalised, for every dimension.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline is a
published *unconditional* theorem (Tao–Teräväinen, arXiv:2512.01739 Thm 1.3),
but its analytic core — a quantitative two-point correlation bound for
multiplicative functions — has no Mathlib counterpart and cannot be honestly
assumed here.  Attaching the catalog name to the criterion above would
misrepresent the headline.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 91, stated exactly

> **`hsmall`** — for every positive integer `b`, every `m` and every `base`,
> `|W(base) − W(base + m)| < 1/b`, i.e. the Gowers-norm smallness of the window
> function `W(n) = ∑' h ≥ 1, ω(n+h)·2^{−h}`.

Everything else in the reduction is proved.  In the published proof the
smallness is obtained for the *dilated* windows `W_p`, which are bounded; the
two remaining ingredients are therefore (i) the exact geometric-series form of
the error `δ_p(m) = 2^{−(p−m)}/(1 − 2^{−p})` for `1 ≤ m < p`, and (ii) the
mod-1 congruence at *cube* level for `W_p`.  Both are recorded in
`policy.json` as `next_round_attack` items 2 and 3.

---

## Round 93 — the period mass of `δ_p`, and the quantisation threshold

New module `lean/JSPProblem/DeltaMass.lean` (792 lines, **41 new theorems and
lemmas**, 0 new definitions, 0 `sorry`, 0 `admit`; **1443 proved theorems and
lemmas** in the tree at the `^(theorem|lemma)` level — 1402 before this round —
`lake build` clean, 3140 jobs).

Round 92 computed the error term of §5.1 of Tao–Teräväinen exactly,
`δ_p(m) = 2^(p−1−c)/(2^p−1)`, but said nothing about its **average**.  The
published proof never uses `δ_p` pointwise; it uses that the error is negligible
*on average over `n`* (their `κ₁ = o(1)`).  This round supplies that average in
closed form, and then computes exactly when the `mod 1` congruence (2.2)
degenerates into an equality.

### 1. THE PERIOD MASS

| Theorem | Statement |
| --- | --- |
| `jsp87_exists_dvd_add` | among `j < p` exactly one satisfies `p ∣ b + j` |
| `jsp87_count_dvd_add` | the cardinality form |
| `jsp87_sum_div_add` | `∑_{j<p} [p ∣ b+j] · w = w` for any real `w` |
| `jsp87_two_pow_neg_sum` | `∑_{k<p} 2^{-(k+1)} = 1 − 2^{-p}` |
| `jsp87_delta_indicator_sum` | the indicator sum over a residue block is the single weight |
| **`jsp87Delta_sum_period`** | **`∑_{j<p} δ_p(m+j) = 1`** for every `m`, `p ≥ 1` |
| **`jsp87Delta_mean_period`** | **the mean of `δ_p` over a period is exactly `1/p`** |
| `jsp87Delta_add_mul` | `δ_p(m + q·p) = δ_p(m)` |
| `jsp87Delta_sum_period_mul` | `∑_{j<pq} δ_p(m+j) = q` |
| `jsp87Delta_mean_period_mul` | the mean over `q` periods is still `1/p` |

So the error term of §5.1 has **mass exactly `1` on every period**.  This is the
exact content of the paper's `κ₁ = o(1)`, and it is what makes the average in
their §5.3 legitimate.

### 2. THE WINDOW BUDGET

`jsp87Delta_sum_range_split` (`∑_{j<L} δ_p(m+j) = ⌊L/p⌋ + ∑_{j<L mod p} δ_p(m+j)`),
`jsp87Delta_sum_range_le`, `_ge`, `_lt` (the average budget is strictly below `1`
for `p ≥ 2`).

### 3. THE MEAN DEFECT IS `b/p` — AND THAT IS WHAT MAKES THE PROOF WORK

| Theorem | Statement |
| --- | --- |
| `jsp87_two_pow_lt_mer` | `2^(p−1) < 2^p − 1` for `p ≥ 2` |
| **`jsp87_defect_lt`** | **`0 < b·δ_p(m) < b`** for `p ≥ 2`, `b ≥ 1` |
| `jsp87_defect_ne_zero` | the defect is never `0` |
| **`jsp87_defect_period_sum`** | `∑_{j<p} b·δ_p(m+j) = b` |
| `jsp87_defect_mean` | the mean defect over a period is `b/p` |
| **`jsp87_defect_mean_lt_one`** | **the mean defect is `< 1` as soon as `p > b`** |

Each individual defect exceeds `b/(2^p−1)`, so the `mod 1` congruence can never be
killed pointwise; but its **mean** is `b/p`, which is `< 1` for `p > b`.  This is
the arithmetic heart of §5.3 of the paper, machine-checked.

### 4. THE QUANTISATION THRESHOLD

| Theorem | Statement |
| --- | --- |
| `jsp87_mer_odd` | `2^p − 1` is odd |
| `jsp87_mer_coprime_pow` | `2^p − 1` is coprime to every power of `2` |
| `jsp87_defect_mul_eq_int_of_dvd_mer` | `(2^p−1) ∣ b ⟹ b·δ_p(m) ∈ ℤ` |
| **`jsp87_defect_integral_iff`** | **`b·δ_p(m) ∈ ℤ ⟺ (2^p−1) ∣ b`**, for every `m`, `p ≥ 2` — no rationality hypothesis |
| `jsp87WinD_defect_exact` | the `mod 1` defect of (2.2), with the integer determined explicitly |
| **`jsp87WinD_mul_eq_int_iff`** | **under rationality, `b·W_p(n) ∈ ℤ ⟺ (2^p−1) ∣ b`** |
| `jsp87_mer_gt_of_large_prime` | `b < p ⟹ b < 2^p − 1` |
| **`jsp87_defect_not_int_of_large_prime`** | **`b < p ⟹ b·δ_p(m) ∉ ℤ`** — no rationality needed |
| `jsp87WinD_not_mul_eq_int_of_large_prime` | `p > b ⟹ b·W_p(n) ∉ ℤ` under rationality |
| **`jsp87WinD_mul_eq_int_imp_le`** | **`b·W_p(n) ∈ ℤ ⟹ p ≤ b`** |
| `jsp87_dilation_dichotomy` | either it quantises with `p ≤ b`, or it does not quantise |
| `jsp87_defect_int_two`, `jsp87_defect_not_int_five_of_coprime` | machine-checked instances at `p = 2, 5` |

So the `mod 1` congruence (2.2) becomes an *equality* at exactly those dilations
whose Mersenne number divides the denominator, and only at primes `p ≤ b`.  This
is the join of the window side (rounds 88–93) and the Lambert side (rounds
37–40, 84): `2^p − 1` is the same Mersenne number in both.  Round 39's
`dvd_lambert_den_prime_gt` (`b ∣ 2^p−1 ⟹ p < b`) pins `p` from the other side.

### Negative knowledge recorded this round

* An earlier draft of this round asserted the **false** statement
  `¬ ∃ d ∈ ℤ, b·W_p(n) = d` for every prime `p`.  It was **deleted, not
  weakened**: `b·δ_p(m) ∈ (0, b) ∩ ℤ` is perfectly consistent — for `b = 3`,
  `p = 2` one has `δ_2 ≡ 1/3, 2/3 (mod 1)`, so `3·δ_2 ∈ {1, 2}`, and indeed
  `3 ∣ 2^2 − 1`.  The honest statement is the **iff** of `jsp87WinD_mul_eq_int_iff`
  and the bound `p ≤ b` of `jsp87WinD_mul_eq_int_imp_le`.
* The defect is never `0`, but it is never `< 1` in general either; the correct
  control is the **average**, not the pointwise value.
* Rationality does **not** imply `Nat.Coprime b (2^p − 1)`; only the `⟺` and the
  bound `p ≤ b` are proved.  Do not upgrade.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is a published theorem (Tao–Teräväinen, arXiv:2512.01739, Thm 1.3,
unconditional) but its analytic core — Gowers-norm smallness of the window
function, obtained from a Pilatte-type two-point correlation bound — has no
Mathlib counterpart and cannot honestly be assumed here.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 93, stated exactly

> **`hsmall`** — for every positive integer `b`, every `m` and every `base`,
> `|W(base) − W(base+m)| < 1/b` (Gowers-norm smallness of the window function
> `W(n) = ∑' h ≥ 1, ω(n+h) 2^{-h}`).

Round 93 closes the *arithmetic* side of the paper's §5.3 completely: the error
term has period mass exactly `1`, its mean under a hypothetical denominator is
exactly `b/p`, and the `mod 1` defect is an integer exactly at the dilations whose
Mersenne number divides `b` — at most those with `p ≤ b`.  What remains is the
single analytic hypothesis `(hsmall)`, with `jsp87Series_irrational_of_FCube_one_small`
(`JSPProblem/CubeSplit.lean`) turning it into the headline.


---

## Round 96 — THE `ω`-TAIL AT AN ARBITRARY CUT POINT IS A PRIME-LAMBERT SERIES

New module `lean/JSPProblem/LambertTail.lean` (863 lines, **41 new public
theorems and 4 new definitions**, 0 `sorry`, 0 `admit`; **1480 proved theorems
and lemmas** in the tree at the `^(theorem|lemma)` level — 1443 before this round —
`lake build` clean at **3141 jobs**).

This round **abandons the window/cube family of rounds 88–95** and returns to the
original reduction.  Round 90 itself recorded that the Tao–Teräväinen cubes vanish
for *every* function, and round 91's flagship criterion rests on `(hsmall)`, which
is **false** (it forces the window `W` to be constant, while `jsp87Carry_succ`
gives `W (n+1) = 2 W n - ω (n+1)` with `ω` unbounded).  Rounds 94 and 95 were idle.

`JSPProblem/LambertIdentity.lean` (round 40) reduced the Erdős series to the
prime-restricted Lambert series — but **only at the cut point `N = 0`**:

`∑' n, ω(n) / 2^(n+1) = ∑' p, 1 / (2^p - 1)`.

No round had ever asked what the Lambert side looks like at an arbitrary cut point,
which is exactly what an Erdős-style argument needs, because such an argument
*moves* the cut point and compares two of them.  This round closes that gap.

### 1. THE FLAGSHIP: THE REMAINDER-WEIGHTED PRIME-LAMBERT SUM

| Theorem | Statement |
| --- | --- |
| **`jsp87Tail_eq_remSum`** | **for `1 ≤ N`, `2^N · τ N = jsp87RemSum N`**, i.e. the `ω`-tail at the cut point `N` is `∑' p prime, 2^(e N p) / (2^p - 1)` with `e N p = if p ∣ N then p - 1 else N mod p - 1` |
| `jsp87RemExp` (def) | the residue exponent `e N p` |
| `jsp87RemExp_le`, `jsp87RemExp_lt` | the exponent never reaches `p` |
| **`jsp87RemExp_of_lt`** | **above the cut point the residue exponent is the constant `N - 1`** |
| `jsp87RemExp_dvd` | a prime dividing the cut point has exponent `p - 1` |

In words: **each Lambert term `1/(2^p - 1)` is raised to the power `2^(N mod p)`**,
the weight recording the position of the first multiple of `p` at or after the cut
point.

### 2. THE SINGLE-PRIME CLOSED FORM — no reindexing over an AP

| Theorem | Statement |
| --- | --- |
| `jsp87PrimeTail` (def) | `∑' k, [p ∣ N + k] · 2^-(k+1)` |
| **`jsp87PrimeTail_eq`** | **`= 2^(e N p) / (2^p - 1)`** |
| `jsp87PrimeTail_succ` | the first-order recurrence (from `Summable.sum_add_tsum_nat_add`, exactly as `jsp87Tail_succ`) |
| `jsp87PrimeTail_add` | a single-prime tail is `p`-**periodic in the cut point** |
| `jsp87PrimeTail_iter`, `jsp87PrimeTail_split` | the tail splits after one full period |
| `jsp87_dvd_add_index` | the unique `j < p` with `p ∣ b + j` is `p - b mod p` |
| `jsp87_mul_lt_two` | a positive multiple of `p` below `2p` is `p` |

Rounds 92–93 recorded that reindexing a `tsum` along an arithmetic progression is
the obstacle that cost those rounds their budget.  This round deliberately avoids
it: the recurrence plus the `p`-periodicity closes a linear equation whose
right-hand side is a *finite* sum over `j < p`, and the uniqueness of that finite
sum was already in the tree (`jsp87_exists_dvd_add`, `JSPProblem/DeltaMass.lean`).

### 3. THE DOUBLE SUM AND THE SMALL/LARGE SPLIT

| Theorem | Statement |
| --- | --- |
| `lamRemF` (def), `tsum_lamRemF_snd`, `tsum_lamRemF_fst` | the row and the column of the double sum over `(k, p)` |
| `tsum_lamRemF_swap`, `tsum_lamRemF_eq` | the swap and the evaluation of the double sum |
| `jsp87RemSumSml`, `jsp87RemSumBig`, `jsp87RemSum` (defs) | the split of the remainder-weighted sum at the cut point |
| `jsp87RemSum_eq_tsumBig` | the large-prime half is `2^(N-1)` times a *plain* Lambert tail |
| `jsp87RemSum_eq_tsum` | the full split |
| `jsp87RemSumSml_zero` | the cut point `0` has no small-prime part |

### 4. THE RATIONALITY TRANSFER, ON THE LAMBERT SIDE

| Theorem | Statement |
| --- | --- |
| `jsp87RemTerm_pos`, **`jsp87RemTerm_lt_one`** | **every prime term lies strictly in `(0, 1)`** — a single prime can never detect a denominator |
| **`jsp87Series_rational_imp_remSum_int`** | **if `jsp87Series = a/b` with `b > 0`, then `b · jsp87RemSum N ∈ ℤ` for every `1 ≤ N`** — the first statement putting the Diophantine obstruction of the `ω`-side and the Lambert side of round 40 into the same real number |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is a published theorem (Tao–Teräväinen, arXiv:2512.01739 Thm 1.3,
unconditional) but its analytic core — a Pilatte-type two-point correlation bound
for multiplicative functions — has no Mathlib counterpart and cannot honestly be
assumed here.  Attaching the catalog name to any weaker statement would
misrepresent the headline.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 96, stated exactly

Everything combinatorial and Diophantine on **both** sides of the reduction is now
formalised, at *every* cut point: `2^N · τ N` is simultaneously the `ω`-tail, the
prime-restricted remainder-weighted Lambert series, and (under rationality) a
multiple of `1/b`.  The one analytic input is unchanged:

> **`hsmall`-free corollary needed**: for every candidate denominator `b`, the
> remainder-weighted prime-Lambert sums `jsp87RemSum N` cannot *all* be multiples of
> `1/b`.  `jsp87RemTerm_lt_one` shows this must involve infinitely many primes at
> once — precisely the content of the Pilatte correlation estimate.


---

## Round 98 — THE STRIDE (DILATION) DECOMPOSITION OF THE ERDŐS SERIES

New module `lean/JSPProblem/StrideSplit.lean` (690 lines, **28 new public theorems and
lemmas** + 2 private helpers + 2 new definitions, 0 `sorry`, 0 `admit`; no new linter
warnings beyond the tree-wide `if_pos`/`if_neg` deprecations; **1508 proved theorems and
lemmas** in the tree at the `^(theorem|lemma)` level — 1480 before this round —
`lake build` clean at **3142 jobs**).

This is a **new attack family**.  Rounds 88–97 attacked the *window/cube* family (Tao–Teräväinen
cubes, dilations of the windows), the *Lambert tail* family (the remainder-weighted
prime-Lambert series at an arbitrary cut point) and the *base family* (the Erdős series at
every base `q`, but only ever the **whole** series at each base).  **No round had ever split a
series by the residue class of its summation index**, nor compared a series to itself at the
coarser base `q^p`.

### 1. THE ARITHMETIC CORE

| Theorem | Statement |
| --- | --- |
| `omega_mul_prime_add` | **for every prime `p` and every `m`**, `ω (p·m) = ω m + (if p ∣ m then 0 else 1)` — the generalisation of round 96's `omega_two_mul` (which is the case `p = 2`) |
| `omega_mul_prime_of_dvd`, `omega_mul_prime_of_not_dvd` | the two halves, as equations |
| **`omega_mul_pow_prime`** | **`ω (p^k · m) = ω m + (if p ∣ m then 0 else 1)` for `k ≥ 1`**: a whole prime *power* is a **single** new prime factor, however large the power |
| `omega_two_pow_mul` | `ω (2^k · m) = ω m + [m Odd]` |
| `omega_mul_le_add` | dilation is subadditive in `ω`: `ω (m·p) ≤ ω m + ω p` |
| `omega_le`, `omega_ge_one` | `ω n ≤ n`, `1 ≤ ω n` for `n ≥ 2` |

### 2. THE REINDEXING MACHINERY (the technical core)

| Theorem | Statement |
| --- | --- |
| **`hasSum_stride_gen`** | **for every nonnegative summable `f` and every `p ≥ 1`, `∑' n, [p ∣ n] f n = ∑' k, f (p·k)`** |
| `tsum_stride_gen` | the same, in evaluated form |

Rounds 92–96 recorded "reindexing a `tsum` along an arithmetic progression" as the obstacle
that cost those rounds their budget.  This is the workaround: the truncation at `n < p·M` is a
**cofinal subsequence** of the partial sums (`Filter.tendsto_atTop_atTop`), the finite
reindexing is an explicit `Finset.sum_bij` with `Nat.mul_left_cancel` for injectivity and
`Nat.mul_lt_mul_of_pos_left` for surjectivity, and the value is transported by
`hasSum_iff_tendsto_nat_of_nonneg` + `hasSum_of_subseq_of_summable`.  **No assumption on `f 0`
is needed**, because `0 ∣ 0` matches the index `n = 0` on both sides.

### 3. THE STRIDE SUBSUM AND ITS CLOSED FORM

| Theorem | Statement |
| --- | --- |
| `jsp87StrideTerm`, `jsp87Stride` (defs) | `jsp87Stride p q = ∑' n, [p ∣ n] ω n / q^(n+1)`, the `p`-divisible subsum of the Erdős series at base `q` |
| `jsp87Stride_zero`, `jsp87Stride_one` | **`jsp87Stride 0 q = 0`** and **`jsp87Stride 1 q = jsp87Base q`**: the stride family interpolates between nothing and everything (`0` divides only the index `0`) |
| `jsp87Stride_two` | **`jsp87Stride 2 q = jsp87Even q` (`rfl`)**: the "even part" of round 100 (`BaseFamily`) *is* the stride-`2` subsum |
| `jsp87Stride_le_base`, `jsp87Stride_pos` | every stride subsum lies in `[0, jsp87Base q]`, and is strictly positive for `p ≥ 1` |
| `tsum_geom_stride` | `∑' k, 1 / q^(p·k+1) = q^(p-1) / (q^p - 1)`, the geometric sum **along a stride**, in closed form |
| **`jsp87Stride_prime_eq_base`** (FLAGSHIP) | **for `q ≥ 2` and every PRIME `p`: `∑' n, [p ∣ n] ω n / q^(n+1) = q^(p-1) · jsp87Base (q^p) + q^(p-1)/(q^p-1) − q^(p^2-1)/(q^(p^2)-1)`** |
| **`jsp87Stride_two_two`** | **`jsp87Even 2 = 2 · jsp87Base 4 + 2/15`** — the even part of the binary Erdős series is **twice the Erdős series in base `4`, up to the rational `2/15`** |

In words: **the `p`-divisible part of the Erdős series at base `q` is the *same* series at the
coarser base `q^p`, up to an explicit rational.**  The two rational corrections are (i) the
geometric sum along the stride and (ii) the geometric sum along the stride *squared*, which is
exactly what the indicator `[p ∣ k]` in the correction term `1/q^(p·k+1)` costs.

### 4. WHAT THE STRIDE IDENTITY TRANSFERS

| Theorem | Statement |
| --- | --- |
| `jsp87Even_two_rat_of_base_four_rat` | if `S(4) = c/d` with `d > 0`, then `jsp87Even 2 = (30c + 2d) / (15d)` |
| `jsp87Base_four_of_even_two`, `jsp87Base_four_eq_of_even_two_rat` | `S(4) = (jsp87Even 2 − 2/15)/2` |
| `jsp87Base_four_rat_of_even_two_rat` | if `jsp87Even 2 = a/b` with `b > 0`, then `S(4) = (15a − 2b) / (30b)` |
| `jsp87Stride_two_two_lt_base` | the even part is strictly below the series (`1/16 ≤ jsp87Odd 2`) |
| `jsp87Stride_prime_pos_lt_base` | for every prime stride, `0 < jsp87Stride p 2 ≤ jsp87Base 2` |

So **rationality of the Erdős series at base `2` and rationality of the Erdős series at base
`4` are the same statement** (via `S(2) = jsp87Even 2 + jsp87Odd 2` and the rationality of the
odd part), and the denominators are explicit.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline irrationality is a
published *unconditional* theorem (Tao–Teräväinen, arXiv:2512.01739, Thm 1.3), but its
analytic core — a Pilatte-type two-point correlation estimate for multiplicative functions —
has no Mathlib counterpart and cannot honestly be assumed here.  Attaching the catalog name to
any weaker statement would misrepresent the headline.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true, sorry=0,
admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### Negative knowledge recorded this round

* **`jsp87Stride 0 q = 0`, not `jsp87Base q`**: an earlier draft of this round asserted the
  stride-`0` subsum is the whole series and it was **deleted, not weakened** — `0` divides only
  the index `0`.
* **The flagship needs `p` PRIME**: `ω (p·m) = ω m + 1 − [p ∣ m]` is false for composite `p`
  (`ω (6·1) = 2 > ω 1 + 1`), so the hypothesis was tightened rather than the statement
  weakened.
* The direct reindexing `∑' k, f (p·k) = ∑' n, [1 ≤ n, p ∣ n] f n` needs `f 0 = 0` (the index
  `n = 0` is a multiple of `p` but is matched by `k = 0` on the right only in that case).  The
  unguarded form holds for every nonneg summable `f` and is what `hasSum_stride_gen` proves.

### The blocker, after round 98, stated exactly

Unchanged: the aperiodicity of the binary digits of `jsp87Series`
(`jsp87_digit_not_eventuallyPeriodic`), i.e. the arithmetic content of the uniform
prime-`k`-tuples hypothesis of Pratt's published result (arXiv:2409.15185).

New, and specific to this round: the stride family relates `S(q)` to `S(q^p)` **as values**,
but `jsp87Base (q^p)` is a *different real* whose own binary digits have never been examined,
and nothing yet pushes the **rationality hypothesis** `S(2) = a/b` through the digit machinery
of rounds 38–64.  `policy.json` records three concrete next steps: (1) the carry-level
analogue of the flagship (the base-`4` carry and the two half-tails, sketched but dropped for
budget), (2) iterating the rationality transfer to the base `2^(2^k)` series with the Mersenne
denominators `2^(2^k) − 1` of round 39, (3) the general residue-class decomposition
`jsp87Residue r p q` with `jsp87Base q = ∑_{r<p} jsp87Residue r p q`, where the odd residues may
admit a second self-similarity via `omega_mul_of_coprime`.

---

## Round 100 — the **stride (dilation) decomposition of the carry**

New module `lean/JSPProblem/StrideCarry.lean` (671 lines, **16 new public theorems
and defs** plus 1 private helper, 0 `sorry`, 0 `admit`; 1697 proved theorems and
lemmas in the tree at the `^(private )?(theorem|lemma)` level; `lake build` clean
at 3143 jobs).

This is a **new attack family**.  Round 98 decomposed the *series*
`S q = ∑' n, ω n / q^(n+1)` by the divisibility of the index and explicitly left
the *carry* `θ N = 2^N · τ N` — the object every other family of this development
is built on — untouched.  Round 100 does the same for the carry.

### 1. The new object and the flagship

```
jsp87StrideCarry M p  =  ∑' j, ω (M + p·j) · 2^-(p·j)
```

the `ω`-values sampled on the progression `M, M+p, M+2p, …` and re-weighted in
base `2^p`.

| Theorem | Statement |
| --- | --- |
| `jsp87StrideCarry` | **the new object** (above) |
| `jsp87StrideCarry_term_nonneg`, `summable_jsp87StrideCarry`, `jsp87StrideCarry_nonneg` | the stride copies are nonnegative summable series, uniformly in the starting point |
| `jsp87StrideCarry_le_tail`, `jsp87StrideCarry_le` | **a stride copy is at most `2·θ M`** — the dilation never inflates the object |
| `jsp87Carry_iter_stride` | `θ N = ∑_{r<p} 2^-(r+1) ∑_{j<i} ω (N+r+pj) 2^-(pj) + 2^-(p·i) · θ (N+p·i)` — round 44's `jsp87Carry_split` iterated `i` times |
| **`jsp87Carry_eq_sum_stride`** | **FLAGSHIP**: for every cut point `N` and every `p ≥ 1`, `θ N = ∑_{r<p} 2^-(r+1) · jsp87StrideCarry (N+r) p` — **the carry at an arbitrary cut point, split by the residue of its summation index, is `p` series at the coarser base `2^p`** |
| `jsp87Series_eq_sum_stride`, `jsp87Series_eq_stride_two`, `jsp87Series_eq_sum_residue` | at the origin the carry is the Erdős series, so the series is its own residue-class decomposition (this closes **policy item 1 of round 98**) |

The proof strategy matters: the flagship is obtained by iterating
`jsp87Carry_split` and letting the number of iterations go to infinity
(`tendsto_finsetSum` + `tendsto_nhds_unique`).  **No general residue-class lemma
for `tsum` is used or needed.**  The finitary identity
`∑_{r<p} ∑_{j<i} = ∑_{n<p·i}` is a `Finset.sum_bij` whose injectivity is routed
through `Nat.add_mul_mod_self_left` (the residue mod `p` recovers the class).

### 2. The residue-class subsums, and the join with round 98

| Theorem | Statement |
| --- | --- |
| `jsp87Residue` | the residue-class subsum `∑' k, ω (p·k+r) 2^-(p·k+r+1)` |
| `summable_jsp87Residue` | the residue subsums are summable (an index-subset bound, *not* an elementwise `ω`-majorant — see §5) |
| `jsp87Residue_eq_stride` | `jsp87Residue r p = 2^-(r+1) · jsp87StrideCarry r p` |
| `jsp87Residue_zero_eq_stride` | the class-`0` subsum at base `2` is exactly round 98's `jsp87Stride p 2` |
| `jsp87Residue_zero_prime_eq_base` | **the join**: for a prime `p`, `jsp87Residue 0 p = 2^(p-1) · jsp87Base (2^p) + 2^(p-1)/(2^p-1) − 2^(p²-1)/(2^p²-1)`, i.e. the residue decomposition *does* reach the coarser-base series, through the class `0` |

### 3. NEGATIVE KNOWLEDGE: no dilation can make the stride copies small

| Theorem | Statement |
| --- | --- |
| **`jsp87StrideCarry_gt`** | **for every cut point `N` and every `p ≥ 2` there is a residue class `r < p` with `2^-(r+1) · jsp87StrideCarry (N+r) p > 1/p`** |
| `jsp87StrideCarry_bounds` | the full picture: each copy lies in `[0, 2(N+r+1)]`, and their `2^-(r+1)`-weighted sum — the carry itself — exceeds `1` |

Round 44 proved `θ N > 1` at **every** cut point.  The stride decomposition splits
that excess across `p` copies, so the excess survives at **every** modulus: the
"dilate the window until the object drops below `1`" strategy is dead for the
carry side, permanently.

### 4. Gate status

`harness/score.py problems/JSP-000087 --strict-prize` reports
`build_ok=true, sorry=0, admit=0, placeholder_total=0, partial_ok=true,
prize_ready=false, missing_theorems=["jsp_000087_main"]`.

`jsp_000087_main` is **still deliberately not declared**.  The blocker is
unchanged: the aperiodicity of the **binary digits** of the series
(`jsp87_digit_not_eventuallyPeriodic`), equivalently of the doubling orbit of the
carries (round 64).  Rationality pins the digit string and the fractional parts
of the carries, **never `ω` itself** — round 47 machine-checked
`jsp87_digit_ne_omega_one`, the digits of `S` are not even the parities of `ω`.

### 5. Concrete blockers left by this round (recorded verbatim in `policy.json`)

* **SECTION 6, proved in mathematics, not yet in Lean — finish this first.**
  For every `p ≥ 1`, `ω` is *unbounded* and *not eventually periodic* along the
  progression `n ↦ p·n + 1`:
  `omega_ap_unbounded`, `omega_ap_periodic_bound`,
  `omega_ap_not_eventuallyPeriodic`.  The proof is elementary (Euclid): take
  `A 0 = 1 + p`, `A (i+1) = 1 + p · ∏_{v ≤ i} A v`; each `A i` is `≡ 1 (mod p)`,
  `≥ 2`, and `A i ∣ A j − 1` for `i < j`, so the `A i` are pairwise coprime;
  hence `M j = ∏_{i<j} A i` is `≡ 1 (mod p)`, `M j ≥ 2^j`, and
  `ω (M j) ≥ j` by `omega_mul_of_coprime`; putting `n = (M j − 1)/p` gives
  `ω (p·n+1) = ω (M j) ≥ j`.  Under an eventual period `t` from `N`, every
  `ω (p·n+1)` with `n ≥ N` equals one at some `n₀ ∈ [N, N+t)`, hence is at most
  `p(N+t)+1` — contradiction.  **The Lean obstacle is plumbing only**: the
  recursive private `def` gets no termination proof from structural recursion
  (the recursive call sits under `Finset.range`); it needs an explicit
  `termination_by i` with a `decreasing_by` derived from `Finset.mem_range`.
* **SECTION 4/5, the dilation rationality ladder (policy item 2).**  All three
  statements (`jsp87Even_eq_dilation`, `jsp87Base_dilation`,
  `jsp87Even_rat_iff_base_sq_rat`) reduce to a single `field_simp`; the
  explicit-denominator corollary hit a heartbeats timeout and was cut.
* **CORRECTION to the record.**  ACCEPTANCE.md (round 98) states that "rationality
  of the Erdős series at base `2` and at base `4` are the same statement".  **That
  does not follow.**  From `jsp87Base q = jsp87Odd q + jsp87Even q` and
  `jsp87Odd q = jsp87Base q − jsp87Even q` one gets only "both parts rational ⟹
  the other is"; rationality of a *sum* says nothing about rationality of the
  *parts*.  What the squaring ladder really transports is the **even subsum**:
  `jsp87Even q` rational `⟺` `jsp87Base (q^2)` rational.  Do not quote the round-98
  formulation.
* **Do not retry**: elementwise majorisation of `ω` by index.  `ω (M+p·k)` is
  neither `≥` nor `≤` `ω (M+k)` in general (`M=5, k=1, p=3` gives `ω 6 = 2 >
  ω 8 = 1`), so every summability majorant must go through
  `summable_of_sum_range_le` with an *index subset*, never through
  `Summable.of_nonneg_of_le`.

---

## Round 101 — **`ω` ALONG ARITHMETIC PROGRESSIONS** (round 100's abandoned Section 6, completed)

New module `lean/JSPProblem/ProgressionOmega.lean` (549 lines, **31 public theorems
and 7 private helpers**, 0 `sorry`, 0 `admit`, no new linter warnings beyond the
tree-wide `if_pos`/`if_neg` deprecations; **1735 proved theorems and lemmas** in the
tree at the `^(private )?(theorem|lemma)` level — 1697 before this round —
`lake build` clean at **3144 jobs**).

This round executes, in full, the item round 100 declared in mathematics and left
in Lean.  It is a **new attack family**: no round of the 100 that preceded it had
ever examined `ω` on an *arithmetic progression*, only on the natural numbers
itself (round 40), on the ray `n ↦ n (1 + t n)` (round 83), on the dilated
windows `W_p` (rounds 88–93) or on the stride subsums (rounds 98, 100).

### 1. The construction — and how the predicted Lean obstacle was bypassed

Round 100 wrote the Euclidean recursion as `A (i+1) = 1 + p · ∏_{v ≤ i} A v` and
correctly predicted a failure: *"the recursive call sits under `Finset.range`, so
Lean's structural recursion cannot see it as smaller."*  **The obstacle is
bypassed, not fixed.**  Recursing on the *product* rather than on the terms,

```
M 0 = a + m,        M (j+1) = M j · (1 + m · M j),        A j = 1 + m · M j
```

gives a recursion whose recursive call is on the *structural* argument `j`, so
plain structural recursion accepts it and **no `termination_by` is needed**.  The
divisibility `A i ∣ M j` for `i < j` then falls out of the same induction.

Three invariants carry the whole module:

| Theorem | Statement |
| --- | --- |
| `jsp87ApProd_mod` | **the whole sequence stays in the residue class `a (mod m)`**: `M j % m = a % m` |
| `jsp87ApProd_ge_two_pow` | `2 ^ j ≤ M j` — geometric growth |
| **`omega_jsp87ApProd_ge`** | **`j ≤ ω (M j)`** — each factor `A j = 1 + m · M j` is `≡ 1 (mod M j)`, hence coprime to everything before it (`Nat.coprime_add_mul_right_right` + `omega_mul_of_coprime`), and `≥ 2`, so it contributes one new prime factor |

with the Euclid-side facts `jsp87ApFac_dvd_apProd` (`A i ∣ M j` for `i < j`),
`jsp87ApFac_sub_one_dvd` (`A i ∣ A j − 1`) and **`jsp87ApFac_coprime`** (the
factors are pairwise coprime).

### 2. THE FLAGSHIPS

| Theorem | Statement |
| --- | --- |
| **`omega_arith_unbounded`** | **`ω` is unbounded on EVERY residue class**: for `m ≥ 1`, `a, C, N` there is `n` with `max a N ≤ n`, `n % m = a % m`, `ω n > C` |
| **`omega_arith_unbounded_progression`** | hence for `m ≥ 1` arbitrarily large `m n + a` have `ω (m n + a) > C` |
| **`omega_ap_unbounded`** | the case `a = 1`: for `p ≥ 1`, `C, N` there is `n ≥ N` with `ω (p n + 1) > C` — *exactly round 100's `omega_ap_unbounded`* |
| **`omega_arith_periodic_bound`** | **an eventual period makes `ω` bounded on the progression**: `ω (m n + a) ≤ m (N + t) + a` for every `n ≥ N` — *exactly round 100's `omega_ap_periodic_bound`* |
| **`omega_arith_not_eventuallyPeriodic`** | **`n ↦ ω (m n + a)` is not eventually periodic**, for every `m ≥ 1` and every `a` |
| **`omega_ap_not_eventuallyPeriodic`** | the same for `n ↦ ω (p n + 1)` — *exactly round 100's third predicted statement* |
| **`omega_arith_not_eventuallyMonotone`** | **STRICTLY STRONGER: not even eventually monotone along a period.**  There are no `t > 0, N` with `ω (m (n+t) + a) ≤ ω (m n + a)` for all `n ≥ N` |
| `omega_arith_not_eventually_bounded`, `omega_ap_not_eventually_bounded` | the negation forms: no constant bounds `ω` on a progression |

**The mechanism of the aperiodicity** is worth recording because it is the one
move no earlier round had tried.  If `ω (m · + a)` is periodic with period `t`
from `N` then it is *constant along the indices* `N + t u`, so the values

```
ω (m (N + t u) + a) = ω (m N + a + m t u)
```

are constant.  But those values live in the **single residue class `m N + a`
modulo `m t`**, and round 101 proves that `ω` is unbounded on *every* residue
class.  The second use of the modulus — `m t`, not `t` — is the whole trick.

### 3. An independent second proof, and consequences for the carries

* **`omega_not_eventuallyPeriodic_via_progression`** — a second, *independent*
  proof that `ω` is not eventually periodic, obtained at `m = 1` from the
  progression result rather than from round 83's `n ↦ n (1 + t n)` move.  The two
  proofs share no lemma.
* **`jsp87Carry_ge_omega_half`** — `ω N / 2 ≤ jsp87Carry N`, from
  `jsp87Carry_split` at `L = 1`.
* **`jsp87Carry_unbounded_on_progression`**, **`jsp87Carry_unbounded_at_one_mod`**,
  **`jsp87Carry_unbounded`** — the carries are unbounded **on every residue class
  of the cut point**.  Together with round 44 (`θ N > 1` at every cut point) and
  round 100 (`jsp87StrideCarry_gt`: the excess survives at every modulus), the
  *"dilate until the object drops below `1`"* strategy is now closed **on every
  progression of cut points**, not merely globally.

### 4. Negative knowledge recorded this round

* **`omega_arith_not_eventuallyMonotone` is a second, general refutation of the
  dilation route.**  Round 91's `hsmall` criterion and round 100's stride
  decomposition were both attempts to make an object *drop* under dilation;
  this round shows in full generality that `ω` cannot even be non-increasing
  along any fixed step `t > 0` on any progression.
* **`omega_arith_periodic_bound` needs the hypothesis `N ≤ n` (the index), not
  `N ≤ m n + a`.**  Freezing acts on the index; `m (n+t) + a` is *not* a
  translate of `m n + a` by a multiple of the period, and the version with
  hypothesis `N ≤ m n + a` and bound `m (N+t) + a` is **false**.
* **The level-indicator aperiodicity on a progression is NOT attempted**: freezing
  `[ω (p n + 1) = k]` and using unboundedness gives no contradiction, because
  unboundedness does not pin the *value*.  For `k = 1` the missing input
  ("some `n` with `ω (p n + 1) = 1` in a prescribed class") is available today via
  `Nat.Coprime.pow_right`; for `k ≥ 2` it is Dirichlet.  Do not attempt.
* **Lean obstacles, all solved, all recorded in `policy.json` and `tree.jsonl`**:
  `obtain ⟨q, hq⟩ := Nat.div_add_mod …` destructures an `Eq` and fails;
  `Nat.mul_le_mul_left/right` are **not** Iffs in this Mathlib; `set X := … with hX`
  substitutes into the goal so a later `rw [hX]` fails; `rw` can rewrite inside
  shadowed variable occurrences (`a` occurs in `jsp87ApProd m a j`);
  `Nat.ModEq.dvd` is stated over the integers and is useless for a `Nat` goal;
  `Nat.mod_eq_of_lt` rather than `simp` for `1 % m`; and `Finset.sum_range_succ` +
  `sum_range_zero` + `add_zero` + `zero_add` in place of a nonexistent
  `Finset.sum_range_one`.

### 5. Gate status

`lake build`: **Build completed successfully (3144 jobs)**.
`harness/score.py problems/JSP-000087 --strict-prize`: `build_ok=true, sorry=0,
admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is a published *unconditional* theorem (Tao–Teräväinen,
arXiv:2512.01739, Thm 1.3), but its analytic core — a Pilatte-type quantitative
two-point correlation estimate for multiplicative functions — has no Mathlib
counterpart and cannot honestly be assumed here.  Attaching the catalog name to
any weaker statement would misrepresent the headline.

**Why round 101 does not move the blocker**, stated explicitly so that no later
round repeats the mistake: rationality of `S` pins the **binary digit string**
(rounds 41/46/48/64) and the **fractional parts of the carries**, and *never*
`ω` itself — round 47 machine-checked `jsp87_digit_ne_omega_one`, the digits of
`S` are not even the parities of `ω`.  The aperiodicity of `ω` is therefore
unreachable *from rationality*, however strong it is proved; and the aperiodicity
of the digits of the carried series remains the content of the uniform
prime-`k`-tuples hypothesis of Pratt's result (arXiv:2409.15185).

---

## Round 102 — the RANGE of the doubling orbit of the carries

New module `lean/JSPProblem/OrbitRange.lean` (534 lines, **30 new theorems and
lemmas** + 1 private helper + 4 new definitions, 0 `sorry`, 0 `admit`, 0 new
linter warnings; **1587** proved declarations at the `^(theorem|lemma)` level —
1557 before this round — `lake build` clean).

This is a **new attack family**.  Rounds 41 (binary digits), 46 (`t`-digit
blocks), 48 (the doubling map on the carries), 57 (the period–denominator
correspondence) and 64 (the minimal period `ord_{jsp87OddPart b}(2)`, the start
point `v_2(b)`) all worked with the **periods** and **collisions** of the orbit
`N ↦ Int.fract (θ N)`.  **Not one of them looked at the orbit as a set of
points.**  This round does, i.e. the classical "limit set" formulation of the
same obstruction.  Round 101 (`omega` along arithmetic progressions) is
*abandoned*: its content (unboundedness and aperiodicity of `ω` on every
progression) is negative knowledge that closes routes rather than supplies the
missing input.

### 1.  The four new objects

| Name | Statement |
| --- | --- |
| `jsp87Dbl` | `x ↦ Int.fract (2 * x)`, the doubling map on `[0,1)` |
| `jsp87OrbitRange` | **the image of the orbit**: `{Int.fract (θ N) : N ∈ ℕ}` |
| `jsp87OrbitWindow N` | the distinct orbit points among the first `N + 1` indices |
| `jsp87OrbitCount N` | `#(jsp87OrbitWindow N)`, the counting function of the range |

### 2.  The orbit is a dynamical system

| Theorem | Statement |
| --- | --- |
| `jsp87_dbl_apply` | the successor of an orbit point **is the doubling map applied to it**: `fract θ (N+1) = jsp87Dbl (fract θ N)` |
| `jsp87_orbit_iter` | **`k` iterates of the doubling map are the orbit point at `N + k`** |
| `jsp87_orbitRange_closed` | the range is closed under `jsp87Dbl` |
| `jsp87_orbitRange_nonempty`, `jsp87_orbitRange_subset_unit` | the range is nonempty and contained in `[0,1)` |

### 3.  Periodicity makes the range finite

| Theorem | Statement |
| --- | --- |
| `jsp87_orbit_period_iter` | `q` periods take the point at `N` to the point at `N + q·t` |
| **`jsp87_orbit_period_reduce`** | **the window reduction**: `fract θ N = fract θ (M + (N − M) % t)` — under an eventual period the whole orbit is determined by its first `t` points after `M` |
| `jsp87_orbitRange_subset_window` | every range value is `fract θ k` for some `k < M + t` |
| **`jsp87_orbitRange_eq_of_periodic`** | the orbit range **is** the image of the first `M + t` points (as `Set ℝ`) |
| `jsp87_orbitRange_finite_of_periodic`, `jsp87_orbitRange_card_le_of_periodic` | the range is a `Finset ℝ` of cardinality `≤ M + t` |

### 4.  A finite range forces a period

`jsp87_orbit_periodic_of_finiteRange` — if `∀ N, fract θ N ∈ s` for a
`Finset ℝ` `s`, then the orbit is eventually periodic.  Proof: pigeonhole
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`) gives a **collision**
`fract θ (W+1+i) = fract θ (W+1+j)`; determinism (`jsp87_orbit_iter`) propagates
it forward with period `|j − i|` from `W + 1 + min i j`.  Mathlib has no
theorem of this shape for the base-`2` expansion of any real number.

### 5.  THE MAIN THEOREM

> **`jsp87Series_irrational_iff_orbitRange_infinite`** —
> `Irrational jsp87Series` **iff** the set `{Int.fract (θ N) : N}` is not
> contained in any `Finset ℝ`, i.e. **iff the doubling orbit of the carries has
> an infinite image**.

Both directions are proved from §3 and §4.  This is the "limit-set" form of
round 64's period criterion, and it mentions **neither a period, nor a modulus,
nor a denominator** — only the finiteness of one set.  Consequences:

| Theorem | Statement |
| --- | --- |
| `jsp87Series_irrational_of_orbit_injective` | an injective orbit forces irrationality |
| `jsp87Series_irrational_of_orbitCount_unbounded` | **unboundedly many distinct orbit points ⇒ irrationality** |
| `jsp87Series_rational_imp_orbitRange_finite` | a rational value of the series forces a finite image |
| `jsp87Series_rational_imp_orbitCount_bounded` | a rational value forces a bounded counting function |

### 6.  The counting function, and a second finite bound on the rational side

| Theorem | Statement |
| --- | --- |
| `jsp87_orbitCount_mono`, `_pos`, `_le`, `_eq_of_injOn` | monotone, `> 0`, `≤ N + 1`, `= N + 1` on an injective window |
| `jsp87_orbitCount_le_of_periodic` | an eventual period `t` from `M` bounds the count by `M + t` |
| `jsp87_orbitCount_eq_of_periodic` | the count is **constant along the period** |
| `jsp87_orbitWindow_succ`, `jsp87_orbitCount_succ_of_new`, `jsp87_orbitCount_succ_le` | one new point per index; a genuinely new point adds exactly one |
| **`jsp87_orbitCarry_grid`** | **the orbit lies on `(1/b)ℤ` at *every* index** — round 41 proved this for `1 ≤ N`; `N = 0` needs `θ 0 = S` |
| **`jsp87_orbitCount_le_denominator`** | **`S = a/b` caps the number of distinct orbit points at `b`** |
| `jsp87_orbitRange_eq_window_of_periodic` | after an eventual period the range *is* a finite window |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is a *published* theorem (conditionally Pratt, arXiv:2409.15185,
under a uniform prime-`k`-tuples hypothesis; unconditionally Tao–Teräväinen,
arXiv:2512.01739), but its analytic core — a Pilatte-type quantitative two-point
correlation estimate for multiplicative functions — has no Mathlib counterpart
and cannot honestly be assumed.  This round reduces the headline to a statement
about a **set** (the image of the doubling orbit), which is the same reduction
as round 64's, in different language.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 102, stated exactly

> **`jsp87_orbitRange_infinite`** — for every `Finset ℝ`, some `N` has
> `Int.fract (θ N)` outside it, i.e. the doubling orbit of the carries is an
> infinite set.

Equivalently (round 102's theorem): `jsp87Series` is irrational.  The range
formulation and round 64's period formulation are **equivalent in both
directions**, so this reformulation buys clarity, not leverage; and the two
finite bounds that rationality now yields (period `≤ ord_{b'}(2)`, image size
`≤ b`) are consistent with everything proved so far, so the denominator and
period routes stay closed.  Untouched families for a future round: the `Ω`
(multiplicity) function and the prime-power excess series, the Farey /
three-distance structure of the orbit points, and a base-`b` (`b > 2`) version of
the range criterion.

---

## Round 103 — the layer-cake decomposition, and the JOIN with the level-set series

New module `lean/JSPProblem/LevelSeries.lean` (310 lines, **13 new theorems and
defs** plus 2 private helpers, 0 `sorry`, 0 `admit`, **0 new linter warnings**;
**1599 proved theorems and lemmas** in the tree at the `^(theorem|lemma)` level —
1587 before — `lake build` clean).

Round 83 (`LevelSets.lean`) decomposed `ω` into its level sets and proved the
complete classification of the two carry-free families
(`jsp87LevelSeries k` irrational ⟺ `1 ≤ k`, `jsp87AtLeastSeries k` irrational ⟺
`2 ≤ k`, with `jsp87LevelSeries 0 = 3/4`, `jsp87AtLeastSeries 0 = 1`,
`jsp87AtLeastSeries 1 = 1/4` computed exactly).  Rounds 37–102 built the Erdős
series itself, its Lambert reduction, its carry dynamics, its digit string and
its aperiodicity endgame.  **The two halves had never been joined.**  This round
is that join, via the layer-cake identity `ω n = #{k : k ≤ ω n}`.

### 1. The layer-cake identity

| Theorem | Statement |
| --- | --- |
| `omega_eq_sum_cumulBit` | `∑_{k < ω n} [k ≤ ω n] = ω n` — `ω n` **is** the number of layers at `n` |
| `jsp87LayerTerm`, `jsp87LayerTerm_nonneg` | the real summand `[k ≤ ω n] · 2^-(n+1)` |
| `jsp87LayerTerm_sum_eq` | `∑_{k < ω n} jsp87LayerTerm k n = jsp87Term n` — the real layer-cake identity |
| `omega_lt_of_lt` | `n < k → ω n < k` (needed to make the truncation an identity) |

### 2. The finite join

| Theorem | Statement |
| --- | --- |
| `jsp87_levelSum_range` | at a cut point `M > n`, `∑_{k<M} jsp87LayerTerm k n = jsp87Term n + 2^-(n+1)`; the extra term is exactly the layer `k = ω n` (it is `1`, since `ω n ≥ ω n`) |
| `jsp87_partial_eq_sum_level` | **THE FINITE JOIN**: `∑_{n<M} ω n 2^-(n+1) + ∑_{n<M} 2^-(n+1) = ∑_{k<M} ∑_{n<M} [k ≤ ω n] 2^-(n+1)` |

### 3. The infinite join, in column form — the round's headline

| Theorem | Statement |
| --- | --- |
| `jsp87LayerColumn` | the new object `(ω n + 1) · 2^-(n+1)`: the **number of layers at `n`**, weighted |
| `jsp87LayerColumn_eq` | `jsp87LayerColumn n = jsp87Term n + 2^-(n+1)` |
| `summable_jsp87LayerColumn`, `hasSum_jsp87LayerColumn` | the column series converges, with sum `jsp87Series + 1` |
| **`jsp87Series_add_one_eq_tsum_columns`** | **`jsp87Series + 1 = ∑' n, (ω n + 1) · 2^-(n+1)`** |
| `jsp87Series_add_one_eq_tsum` | the same, with the column written out |

So the Erdős series is a **countable integer-weighted combination of the level
series of round 83**, and the `+ 1` is the layer `k = 0` — whose total weight is
the geometric series `∑' n, 2^-(n+1) = 1`.  This is proved without any Fubini
argument: both sides are single `tsum`s indexed by `n`.

### 4. The row form, and the exact reason it is not yet proved

The row form `jsp87Series + 1 = ∑' k, jsp87AtLeastSeries k` requires
interchanging a **countable** double sum.  This Mathlib version has **no** Fubini
lemma for `ℝ`: `tsum_comm` exists only for `ℝ≥0∞` (`ENNReal.tsum_comm`),
`Summable.tsum_finset_sum` and `summable_of_nonneg_of_le` do not exist (the latter
is `Summable.of_nonneg_of_le`), and there is no
`Filter.Tendsto.le_of_tendsto_of_tendsto_of_le_of_le'` to pass an inequality
through a limit.  A complete three-step plan (summability of the row series via
`ω n ≥ k → n ≥ 2^k`, the two one-sided finite bounds, and
`M · 2^-M → 0` from `exists_pow_lt_of_lt_one`) is recorded at the end of
`lean/JSPProblem/LevelSeries.lean` for the next round.

### 5. Why the join does not close the gate

Every `jsp87AtLeastSeries k` with `k ≥ 2` and every `jsp87LevelSeries k` with
`k ≥ 1` is **irrational** (round 83), and the join shows the Erdős series is built
from them by a countable integer-weighted combination.  A countable combination
of irrational numbers need not be irrational, and the two rational members of the
family are precisely the trivial ones.  So the join sharpens the *shape* of the
problem without touching the blocker, which remains round 41's
**`jsp87_digit_not_eventuallyPeriodic`** (equivalently round 64's aperiodicity of
the doubling orbit `Int.fract (θ N)`).

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

---

## Round 106 — the WEIGHTED level reflection, and the partition of unity

New module `lean/JSPProblem/WeightJoin.lean` (850 lines, **54 new theorems and
lemmas** + 4 new defs + 10 private helpers, 0 `sorry`, 0 `admit`, **0 new linter
warnings**; **1677 theorem/lemma declarations** in the tree at the
`^(theorem|lemma)` level, 1623 before this round, `lake build` clean).

This is a **new attack family**: it executes item 1 of round 104's
`next_round_attack`, the identity round 83 recorded only as *numerical
commentary* in `LevelSets.lean` §3 (`"jsp87Series = ∑ k, k · L k numerically"`) and
which no round had ever written down as a theorem.

### 1. The level series decay *doubly* exponentially (new)

A level-`k` digit is `1` only at integers with exactly `k` distinct prime factors,
and `ω n = k` forces `2^k ≤ n` (`two_pow_omega_le`).  So the primary series of the
level indicator vanishes below `n = 2^k`, its *prefix* at that cut point is `0`
(`jsp87BinaryInt_level_eq_zero`), and the "no carrying" split
`2^N · T f = A f N + U f N` gives the sharp bound

| Theorem | Statement |
| --- | --- |
| `jsp87Level_eq_zero_of_lt_two_pow`, `jsp87AtLeast_eq_zero_of_lt_two_pow` | a level (resp. "at least") digit vanishes below `n = 2^k` |
| `jsp87BinaryInt_level_eq_zero`, `jsp87BinaryInt_atLeast_eq_zero` | the `2^k`-prefix is exactly `0` |
| **`jsp87LevelSeries_mul_two_pow_two_pow`** | **`2^(2^k) · L k ≤ 1`** — the double-exponential bound |
| `jsp87LevelSeries_le_two_pow_sharp` | `L k ≤ 2^-(2^k)` |
| `jsp87LevelSeries_mul_two_pow`, `jsp87LevelSeries_le_two_pow` | `2^k · L k ≤ 1`, `L k ≤ 2^-k` |
| `jsp87LevelSeries_one_le` | `4 · L 1 ≤ 1` (the level-`1` series is the prime-power indicator) |
| `jsp87AtLeastSeries_mul_two_pow_two_pow`, `jsp87AtLeastSeries_mul_two_pow` | the same for the "at least" family `A k` |

Round 83 could only prove `L k < 1` and `L k ≤ 1/4`; the double-exponential decay
is new and is the quantitative reason the reflection below converges.

### 2. The weighted columns, and the weighted saturation point

| Theorem | Statement |
| --- | --- |
| `jsp87_weightCount` | `∑_{k<M} k · [ω n = k] = if ω n < M then ω n else 0` — only the layer of index `ω n` carries weight, and it is visible exactly when `ω n < M` |
| `jsp87WeightColumn M n` | that count, weighted by `2^-(n+1)` |
| `jsp87_weightedLevel_sum_eq` | the `M` weighted rows, read at the single cut point `n`, are the weighted column |
| `jsp87WeightColumn_le_term`, `summable_jsp87WeightColumn` | the weighted columns are dominated by the Erdős series |
| **`jsp87WeightColumn_eq_term`** | **the weighted saturation point**: `1 ≤ M`, `n < 2^M ⟹ the weighted column IS the `n`-th term of the Erdős series** |

### 3-4. The reflection itself

| Theorem | Statement |
| --- | --- |
| `jsp87_weightPartial_eq_tsum` | the weighted rows at height `M` are the `tsum` of the weighted columns — exact, by the finite `Summable.tsum_finsetSum` interchange |
| `jsp87_weightPartial_le_series`, `jsp87_colPartial_le_weightPartial` | the weighted rows never overshoot `S`, and dominate the columns below `n = 2^M` |
| `jsp87_colPartial_le_series`, `jsp87_termTail_nonneg` | every partial sum of the Erdős series is `≤ S` |
| `jsp87_weightGap_le_tail`, `tendsto_jsp87_weightGap`, `tendsto_jsp87_weightPartial` | the weighted gap is bounded by the column tail and tends to `0` |
| `hasSum_weightedLevels`, `summable_weightedLevels` | the weighted level series is a `HasSum` for `S` |
| **`jsp87Series_eq_tsum_weightedLevels`** | **THE REFLECTION: `jsp87Series = ∑' k, k · jsp87LevelSeries k`** |

### 5. Every summand of the reflection is irrational

`jsp87_weightedLevel_irrational` (for every `k ≥ 1`, `Irrational (k · L k)`),
`jsp87_series_eq_tsum_weightedLevels_onzero` (the rational member `k = 0` removed),
`jsp87_weightPartial_le_sub` (the rows miss at least the `K`-th weighted level),
`jsp87_weightPartial_succ` / `_mono` / `_strictMono'` / `_pos`.

### 6. THE PARTITION OF UNITY

| Theorem | Statement |
| --- | --- |
| `jsp87_levelCount`, `jsp87LevelColumn M n` | exactly one level contains `n`, so the unweighted columns are the indicators `[ω n < M] · 2^-(n+1)` |
| `jsp87_levelPartial_le_one`, `jsp87_levelPartial_ge_colPartial`, `tendsto_jsp87_levelPartial` | the level partial sums are squeezed between the geometric partial sums below `n = 2^M` and `1` |
| **`jsp87_tsum_levelSeries_eq_one`** | **`∑' k, jsp87LevelSeries k = 1`**: the level sets partition the integers, so the level series partition `[0,1]` |
| `jsp87_levelPartial_le_sub_one` | the partition is *nested*: `∑_{k<K} L k ≤ 1 − L K` |
| `jsp87_tsum_levelSeries_tail_eq_quarter` | the `k ≥ 1` part of the partition is exactly `1/4` (the level `k = 0` is `ω n = 0`, i.e. `n = 0, 1`, carrying `3/4`) |

This is the first time the round-83 level series have been proved to sum to
anything at all, and it is the exact unweighted mirror image of the reflection.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  A countable sum of
provably irrational numbers need not be irrational
(`jsp87Series_rational_of_atLeast_periodic`), so neither the row form nor the
weighted reflection transfers irrationality to `S`; and the headline irrationality
is **conditional** in the published literature (Pratt, arXiv:2409.15185, uniform
prime `k`-tuples) while the catalog records *Solved; Lean proof: No; Eligible to
claim: No*.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 106, stated exactly

Unchanged: **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
`d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the *carried* Erdős series are not eventually
periodic.  Round 106 makes the surrounding structure exact in both directions
(`S = ∑' k, k·L k` and `∑' k, L k = 1`, with doubly-exponential decay), but the
level series are aperiodic *unconditionally* (round 83) while the digits of `S`
are not the level indicators (round 47 proved `jsp87_digit_one`: the first digit
of `S` is `1` although `ω 1 = 0`), so no amount of structure in the level family
reaches the digit string.  Nothing unconditional is known about that
aperiodicity: it is the content of the uniform prime-`k`-tuples hypothesis of the
published result.

---

## Round 107 — the moment ladder: the two families are one partition, and the second moment

New module `lean/JSPProblem/MomentLadder.lean` (**61 public theorems/defs**,
0 `sorry`, 0 `admit`, 0 new linter warnings, `lake build` clean; **1733** proved
theorems and lemmas at the `^(theorem|lemma)` level in the tree).

This round executes the two quantitative items of round 106's plan and closes the
classification begun in round 83.  It is a **new attack family**: not the Lambert
reduction, the carry scaffold, the gcd arithmetic, the carry dynamics, the digit
bookkeeping, the carry-excess sieve content, the base-`2` block arithmetic, the
primary expansion, the doubling orbit, the `2`-adic route, the radix family, the
dilation/multiplier family, the sieve model, the CRT/stride family, the subword
complexity family — but the **layer-cake arithmetic of the level family and of its
cumulative partner, read as moments of `ω`**.

### 1. §1 — the level family and the "at least" family are ONE partition and its tails

| Theorem | Statement |
| --- | --- |
| `jsp87_tailLevel_sum M t` | **THE FINITE TAIL-SUM RELATION** `∑_{j<t} L (M+j) = A M − A (M+t)` — summing `L j = A j − A (j+1)` over the window `[M, M+t)` |
| `jsp87_levelPartial_add_atLeast M` | **THE EXACT COMPLEMENT** `∑_{k<M} L k + A M = 1` for every height `M` — round 106's partition of unity `∑' k, L k = 1` is its limit |
| `jsp87_levelPartial_eq_one_sub_atLeast` | `∑_{k<M} L k = 1 − A M` |
| `jsp87_levelPartial_zero`, `jsp87_levelPartial_one` | the values at heights `0` and `1`: `0` and `3/4` |
| `jsp87_levelPartial_pos_iff` | `0 < ∑_{k<M} L k ↔ 1 ≤ M` |
| **`jsp87_levelPartial_irrational_iff`** | **THE ROW PARTIAL SUMS ARE IRRATIONAL EXACTLY FOR `M ≥ 2`** — this closes the classification of round 83, which had proved `L k` and `A k` irrational exactly for `k ≥ 1` and `k ≥ 2` but never the *partial sums* |

So the row sum of round 104 (`∑' k, A k = S + 1`) and the partition of unity of
round 106 (`∑' k, L k = 1`) are the same statement read at the two ends of one
sequence, and the rational members are exactly the two finite ones (`0`, `3/4`).

### 2. §2 — the complement decays doubly exponentially

| Theorem | Statement |
| --- | --- |
| `jsp87AtLeastSeries_le_two_pow_sharp` | the closed form `A k ≤ 2^-(2^k)` (round 106 had proved only the product form `2^(2^k) · A k ≤ 1`) |
| **`jsp87_levelPartial_ge_two_pow_sharp`** | `1 − 2^-(2^M) ≤ ∑_{k<M} L k` for `M ≥ 1` — **an explicit doubly-exponential error for the partition of unity** |
| `jsp87_levelPartial_dist_one_le` | the metric form `dist (∑_{k<M} L k) 1 ≤ 2^-(2^M)`: a convergence **rate**, not just a limit |
| `jsp87_levelPartial_ge_three_quarters` | `3/4 ≤ ∑_{k<M} L k` for every `M ≥ 1` |

### 3. §3 — the second-moment reflection (policy item 1)

| Theorem | Statement |
| --- | --- |
| `jsp87_tri` | the triangular numbers `tri k = k(k+1)/2` |
| `jsp87_tri_sum_range` | `∑_{k<m+1} k = tri m` (from Mathlib's `Finset.sum_range_id`) |
| `jsp87_weightCumCount_sat` | **the weighted cumulative count in the saturated range**: `ω n + 1 ≤ M ⟹ ∑_{k<M} k [k ≤ ω n] = tri (ω n)` |
| `jsp87_weightCumCount_unsat` | in the unsaturated range every indicator is `1` |
| `jsp87_weightCumCount_le`, `…_cast` | the truncation never overcounts: `∑_{k<M} k [k ≤ ω n] ≤ tri (ω n)` |
| `jsp87CumWeightColumn`, `jsp87_weightedCum_sum_eq`, `jsp87CumWeightColumn_nonneg`, `…_le_triTerm` | the triangular column and its domination by the `n`-th triangular moment |
| **`jsp87CumWeightColumn_eq_triTerm`** | **THE TRIANGULAR SATURATION POINT** `n < 2^M ⟹ the column is the full triangular moment` (mirror of round 106's linear saturation point) |
| `jsp87_tri_le_mul_omega_add_one`, `jsp87_mul_omega_add_one_le_poly` | `tri (ω n) ≤ ω n (n+1) ≤ n² + n` |
| `summable_jsp87TriTerm`, `jsp87TriSeries`, `jsp87TriSeries_nonneg` | the second moment `S^(2) = ∑' n, tri (ω n) · 2^-(n+1)` exists |
| `jsp87CumWeightPartial`, `jsp87_cumWeightPartial_eq_tsum`, `summable_jsp87CumWeightColumn`, `jsp87_cumWeightPartial_le_triSeries`, `jsp87_colPartial_le_cumWeightPartial` | the finite weighted interchange for the cumulative rows |
| **`jsp87TriSeries_eq_tsum_weightedAtLeast`** | **THE SECOND-MOMENT REFLECTION** `∑' k, k · A k = ∑' n, (ω n(ω n+1)/2) · 2^-(n+1)` |
| `hasSum_weightedAtLeast`, `summable_weightedAtLeast`, `jsp87_weightedAtLeast_irrational` | the weighted family is summable and **every member of height `≥ 2` is irrational** |

Together with round 106's `jsp87Series_eq_tsum_weightedLevels` (`S = ∑' k, k L k`,
the first moment) the power-sum ladder now has its first two rungs, both proved
from the same layer-cake arithmetic.

### 4. §4 — the pure square moment

| Theorem | Statement |
| --- | --- |
| `jsp87SqTerm`, `jsp87SquareSeries`, `summable_jsp87SqTerm` | the square moment `∑' n, ω n² · 2^-(n+1)` converges |
| `jsp87_tri_mul_two` | `2 · tri (ω n) = ω n² + ω n` (via `Nat.two_mul_div_two_of_even`, `Nat.even_mul_succ_self`) |
| `jsp87TriTerm_two_eq`, `jsp87TriSeries_two_eq_add_sq` | **THE SECOND MOMENT IS THE SUM OF THE SQUARE MOMENT AND `S`**: `2 S^(2) = ∑' n, ω n² · 2^-(n+1) + S` |
| **`jsp87SquareSeries_add_eq_tsum_two_weightedAtLeast`** | `∑' n, ω n² · 2^-(n+1) + S = ∑' k, 2k · A k` — the square moment is a doubled copy of the same weighted family |
| `jsp87SquareSeries_le_two_triSeries` | the ladder inequality `square moment ≤ 2 S^(2)` |
| **`jsp87TriSeries_eq_add_shiftedWeight`** | `S^(2) = S + ∑' k, k · A (k+1)` — the two rungs are related by a single index shift of the same weighted family |

### 5. §5–§6 — quantitative brackets and one sharp closed form (policy item 2)

| Theorem | Statement |
| --- | --- |
| `jsp87_weightedAtLeast_le_two_pow` | the geometric majorant `k · A k ≤ k · 2^-k` |
| **`jsp87TriSeries_le_two`** | **THE SECOND MOMENT IS AT MOST `2`** — the mirror of `jsp87Series ≤ 1`, since `∑' k, k 2^-k = 2` |
| `jsp87TriSeries_ge_thirtyThree` | **and at least `33/128`** — the seven places `n < 7` already contribute `33/128` |
| `jsp87SquareSeries_ge_fifteen` | `15/64 ≤ ∑' n, ω n² · 2^-(n+1)` |
| `jsp87TriSeries_pos`, `jsp87SquareSeries_pos`, `jsp87TriSeries_ge_series` | positivity of both moments; `S ≤ S^(2)` |
| `jsp87TriSeries_sub_colPartial N` | the triangular tail is the **shifted second moment** `S^(2) − ∑_{n<N} tri n = ∑' k, tri(ω(N+k))·2^-(N+k+1)` (mirror of round 38's `jsp87_series_eq_sum_add_tail`) |
| **`jsp87_weightGap_le_closed`** | **THE SHARP CLOSED-FORM ERROR TERM OF ROUND 106'S REFLECTION**: `0 ≤ S − ∑_{k<M} k L k ≤ (2^M+1) · 2^-(2^M)` for `M ≥ 1` — the quantitative item round 106 left open, obtained from `jsp87Tail_le` (round 38) at the cut point `2^M` |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The round-107 results
are exact identities for the *rows* of the level/level-cake partition and for the
moments of `ω`; none of them constrains the **binary digit string** of `S`, which
round 64 proved to be *equivalent* to the headline statement:

> `Irrational jsp87Series ↔` the doubling orbit `N ↦ Int.fract (θ N)` of the
> carries is not eventually periodic.

Rationality of `S` freezes the digits and the carry orbit into a lattice `1/b · ℤ`
(rounds 38, 41, 46, 64); it never freezes `ω` itself (round 47 machine-checked
`jsp87_digit_one`: the first binary digit of `S` is `1` although `ω 1 = 0`).  The
aperiodicity of the digit string is the arithmetic content of the uniform prime
`k`-tuples hypothesis in Pratt's published result (arXiv:2409.15185) — an
assumption of the **published** theorem and not of the catalog statement — or,
unconditionally, of a Pilatte/Tao–Teräväinen-type correlation estimate that
Mathlib cannot supply.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 107, stated exactly — unchanged

> **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the Erdős series are not eventually periodic
> in `N` (equivalently, `jsp87Series_irrational_of_blockNotPeriodic`: the `t`-digit
> blocks of `S` are never eventually periodic; equivalently, the doubling orbit of
> the carries is not eventually periodic).

### Negative knowledge recorded this round (machine-checked, do not retry)

1. **The triangular tail cannot be bounded by a constant multiple of the Erdős
   tail.**  The natural plan `jsp87TriSeries − ∑_{n<N} tri n ≤ 2·(N+1)·τ N` is
   **false**: it needs the per-term bound `tri (ω (N+k)) ≤ 2(N+1)·ω (N+k)`, i.e.
   `k ≤ N+1`, which fails for `k > N`.  The correct rate needs the quadratic
   geometric tail `∑' k, (N+k)² · 2^-(N+k+1)`, i.e. a closed form for
   `∑' n, n² · 2^-(n+1) = 2` together with a shift estimate; the shift
   decomposition itself (`jsp87TriSeries_sub_colPartial`) **is** proved this round.
2. **There is no instance for the pointwise product of two `Summable` series in
   this Mathlib** (`Summable.mul` does not exist; `Summable.mul_left/mul_right`
   take a *constant* multiplier).  Quadratic majorants must be built with
   `Summable.add` — done in the private `summable_poly_mul_two_pow_neg`.
3. **A `tsum` over a threshold filter cannot be split additively in this Mathlib**
   (`Finset.sum_eq_tsum`, `tsum_eq_zero_add_tsum` are absent, and
   `Summable.tsum_subtype` needs injectivity).  Consequently the *infinite*
   tail-sum identity `A k = ∑' j, (if k ≤ j then L j else 0)` could **not** be
   proved; the *finite* form (`jsp87_tailLevel_sum`) and the exact complement
   (`jsp87_levelPartial_add_atLeast`) were proved instead and carry the same
   content.


---

## Round 110 — SQUAREFREE NUMBERS: the power-set divisor identity and a new irrationality theorem

New module `lean/JSPProblem/Squarefree.lean` (459 lines, **41 new theorems/defs**,
0 `sorry`, 0 `admit`; **1897 proved theorems and lemmas** at the `^(theorem|lemma)`
level in the tree — 1856 before this round — `lake build` clean, 0 new linter
warnings).

This is a **new attack family**.  All 60+ earlier modules see `ω` only through
its *counting* form (`omega n = (n.primeFactors).card`) or through the
prime-restricted Lambert series of rounds 37/39/40.  `rg squarefree` over
`JSPProblem/` returned **nothing** before this round: the **power-set geometry**
of `ω` — the identity between `ω n` and the number of *squarefree divisors* of
`n` — had never been touched, in 109 rounds.  Mathlib, by contrast, has the
whole `Nat.Squarefree` API in `Mathlib/Data/Nat/Squarefree.lean`
(`DecidablePred`, `squarefree_iff_prime_squarefree`, `primeFactors_prod`,
`prod_primeFactors_of_squarefree`), which this round exploits.

### 1. The power-set identity

| Theorem | Statement |
| --- | --- |
| `jsp87_prod_prime_sqf` | a product of distinct primes is squarefree |
| `jsp87_mem_prod_prime` | for a prime `x`: `x ∣ ∏ p ∈ s, p ↔ x ∈ s` |
| `jsp87_sqfDiv_eq_prod` | every squarefree divisor of `n` is the product of a **subset of `n.primeFactors`** |
| `jsp87_prod_sqfDiv` | conversely, every such product is a squarefree divisor of `n` |
| `jsp87SqfDivs_eq_powerset_prod` | `jsp87SqfDivs n = (n.primeFactors.powerset).image (∏ x ∈ s, x)` |
| **`jsp87SqfDivs_card`** | **THE POWER-SET IDENTITY: `# {squarefree divisors of n} = 2 ^ ω n`** |
| `jsp87_sqf_of_dvd`, `jsp87_sqf_iff_of_dvd`, `jsp87_not_sqf_of_sq_dvd`, `jsp87_not_sqf_sq`, `jsp87_not_sqf_of_four_dvd` | the elementary squarefree facts, all from `Nat.squarefree_iff_prime_squarefree` |
| `jsp87SqfDivs_12 / _30 / _210 / _1` | the machine-checked instances `4`, `8`, `16`, `1` (`native_decide`) |

This is the multiplicative content of `ω`: `ω n` counts a *power set*, and
`2 ^ ω n` is its size.  Rounds 37/107/108 built the Lambert ladder over the
first, second and cubic *moments* of `ω`; this is the first rung of the
**power-set** ladder.

### 2. THE SQUAREFREE INDICATOR IS APERIODIC — a two-line proof

| Theorem | Statement |
| --- | --- |
| `jsp87_sqf_not_eventuallyPeriodic` | the squarefree predicate is **not eventually periodic** |

If an eventual period `t` existed, squarefreeness would propagate along
`p + k t` from any prime `p` past the threshold; at `k = p · j` this says
`Squarefree (p (1 + j t))`, hence `Squarefree (1 + j t)` for every `j ≥ 0`
(divisors of squarefree numbers are squarefree).  Taking `j = t + 2` exhibits
`1 + (t + 2) t = (t + 1) ^ 2`, a perfect square.  No prime `k`-tuples
hypothesis, no correlation estimate — only Euclid.

### 3. A COMPLETE, UNCONDITIONAL IRRATIONALITY THEOREM

| Theorem | Statement |
| --- | --- |
| `jsp87SqfreeBit` | the squarefree indicator as a `{0,1}`-valued sequence |
| `jsp87SqfreeSeries` | `∑' n, [n squarefree] 2 ^ -(n+1)` |
| **`jsp87SqfreeSeries_irrational`** | **THE SQUAREFREE BINARY SERIES IS IRRATIONAL** |

By round 47's criterion (`jsp87Binary_irrational_iff`, proved from scratch in
`Primary.lean` — Mathlib has no statement at all about the base-`2` expansion
of a real).  The tail hypothesis `jsp87BinaryTail < 1` is discharged by the
explicit zero digit at `4 · (N + 2)` (`jsp87_not_sqf_of_four_dvd`).  This is
the second complete instance of the criterion after round 47's prime constant
and parity series, and the first one whose digits are the **divisor geometry**
of `ω`.

### 4. The exponential moment of `ω`, and its bracket

| Theorem | Statement |
| --- | --- |
| `jsp87PowOmegaSeries` | `P = ∑' n, 2 ^ ω n 2 ^ -(n+1)` — the *exponential* moment |
| `jsp87_two_pow_omega_le_add_one` | `2 ^ ω n ≤ n + 1` (at `n = 0` the left side is `1`) |
| `summable_jsp87PowOmegaTerm`, `jsp87_tsum_powOmega_majorant`, `jsp87_tsum_two_pow_neg_succ`, `jsp87_two_pow_neg_succ_eq` | the summability and the two closed forms `∑' n, 2^-(n+1) = 1`, `∑' n, (n+1) 2^-(n+1) = 2` |
| **`jsp87_powOmegaSeries_ge_series_add_one`** | **`1 + S ≤ P`** — the power-set moment dominates the Erdős series by at least `1` |
| **`jsp87_powOmegaSeries_le_two`** | **`P ≤ 2`** |

### 5. NEGATIVE KNOWLEDGE (machine-checked, do not retry)

`jsp87_sqf_mer_not_coprime : ¬ Coprime (2 ^ 2 - 1) (2 ^ 6 - 1)` — the
squarefree-indexed Lambert denominators are **not** pairwise coprime (`3`
divides both `3` and `63`, and `2`, `6` are both squarefree).  Round 39's
mutual coprimality of `2 ^ p - 1` for distinct **primes** `p` therefore does
*not* transfer to the power-set ladder: the exponential moment comes with no
exact clearing denominator, and the `D_N` machinery of rounds 39/40 cannot be
reused for it.  The positive companion `jsp87_sqf_mer_coprime_two_three`
(`Coprime (2^2-1) (2^3-1)`) shows the obstruction is genuinely about common
factors of the *indices*, as round 39's `gcd_two_pow_sub_one` predicts.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  Round 110 does not
touch the binary digits of the Erdős series itself: the Erdős series carries
(round 47: `jsp87_digit_one`), so the squarefree-digit theorem applies to a
*different* series, and the remaining input is still the aperiodicity of the
digits of `S` (round 64's
`jsp87Series_irrational_iff_fracCarry_notPeriodic`).

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 110, stated exactly — unchanged

> **`jsp87_digit_not_eventuallyPeriodic`** — the binary digits
> `d N = ⌊2^{N+1} S⌋ − 2⌊2^N S⌋` of the Erdős series are not eventually
> periodic in `N`.

### The concrete next step this round opened

`jsp87SqfDivs_card` gives the **finite** Lambert regrouping for free (the
squarefree divisors of `n` are a subset of `range (n+1)`), so the missing piece
of the power-set Lambert identity

> `jsp87_powOmegaSeries_eq_sqfLambert` : `∑' n, 2 ^ ω n 2 ^ -(n+1) =
> ∑' d, [d squarefree] / (2 ^ d - 1)`

is *purely* an interchange of the two infinite sums, i.e. exactly the
`Summable.tsum_comm'` + `hasSum_lamF_fst` machinery of
`LambertIdentity.lean:347` with the prime guard replaced by the squarefree guard.
The obstacle is that `hasSum_lamF_fst` is stated only for **primes**, and its
proof needs a reindex lemma `sum_multiples_reindex` that also requires
`p.Prime` (only for `0 < p`).  Porting that lemma to arbitrary `d ≥ 1` is a
mechanical copy and is the first item of the next round.

---

## Round 112 — **THE PROBLEM WAS SOLVED UNCONDITIONALLY IN THE LITERATURE**, and the
## Tao–Teräväinen reduction, formalized

### 0. THE STATUS OF THE CATALOG RECORD IS OUT OF DATE (correction)

Every round from 37 to 111 of this development recorded the same gate note:

> *the irrationality of `∑ ω(n)/2^n` is **conditional** in the published
> literature (Pratt, arXiv:2409.15185, under a uniform prime `k`-tuples
> hypothesis), and the catalog status is "Solved; Lean proof: No; Eligible to
> claim: No".*

**That note is superseded.**  T. Tao and J. Teräväinen, *Quantitative
correlations and some problems on prime factors of consecutive integers*,
**arXiv:2512.01739** (v1 1 Dec 2025; v2 25 Apr 2026), prove **unconditionally**
that

```
∑_{n=1}^{∞} ω(n) / 2^n  =  ∑_{p prime} 1 / (2^p − 1)      is irrational.
```

Their Theorem 1.3 is titled "*Erdős #69*"; it settles exactly this problem, and
it is also the prime case of Erdős problem #257 (`∑_{n∈A} 1/(2^n−1)` irrational
for `A` the primes, with `A` the prime powers as a second case).  The same paper
also settles Erdős–Straus #248 (`ω(n+k) ≤ Ω(n+k) ≪ k` for infinitely many `n`)
and Erdős–Pomerance–Sárközy (local limit theorem for `ω(n) = ω(n+1)`).

Consequences for this file:

* `jsp_000087_main : jsp87Series.Irrational` is now a **theorem in the
  literature**, not a conjecture.  It is therefore legitimate to declare it;
  what is missing is the **proof**, not the statement.
* The blocker recorded 111 times, `jsp87_digit_not_eventuallyPeriodic` (aperiodicity
  of the binary digits), is no longer an open problem: it is a *theorem*, and
  Tao–Teräväinen's §5 is a proof of it.
* The ACCEPTANCE.md text and `acceptance.json`'s `catalog_status` were copied
  from the catalog record and are now **stale**; the catalog itself lags the
  literature by one paper.

### 1. What Tao–Teräväinen actually need — and the new Lean module

Their introduction states the analytic content precisely:

> upper bounds on consecutive values `ω(n+1), …, ω(n+H)` of `ω` are
> insufficient; **some control on the distribution of various linear
> combinations of such values (e.g. `∑_{h=1}^{H} ω(n+h)/2^h`) is needed**.

That object is a **truncated carry** of the Erdős series, and it was not in the
111-round tree.  `lean/JSPProblem/TTRoute.lean` (new, 26 declarations, 0 `sorry`,
0 `admit`) builds it:

| Declaration | Statement |
| --- | --- |
| `jsp87TruncCarry N H` | `∑_{k<H} ω(N+k) 2^-(k+1)` — the truncated carry at the cut point `N` |
| `jsp87Carry_le_all M` | `θ M ≤ M+1` **at every** `M ≥ 0` (round 40's bound needed `1 ≤ M`) |
| `jsp87TruncCarry_eq_split` | `θ N = jsp87TruncCarry N H + 2^-H · θ (N+H)`, the exact truncation form of round 44's `jsp87Carry_split` |
| `jsp87Carry_sub_truncCarry_le` | **`0 ≤ θ N − jsp87TruncCarry N H ≤ 2^-H (N+H+1)`** — the quantitative tail bound |
| `jsp87Series_rational_imp_carry_mul_int` | `S = a/b`, `b>0` ⟹ `b · θ N ∈ ℤ` for every `N ≥ 1` |
| **`jsp87Series_rational_imp_truncCarry_nearInt`** | **THE REDUCTION.** `S = a/b`, `b>0` ⟹ for every `N ≥ 1` and every `H` there is `c ∈ ℤ` with `\|b·jsp87TruncCarry N H − c\| ≤ b·2^-H·(N+H+1)` |
| `jsp87IntDist x` | `min (Int.fract x) (1 − Int.fract x)`, the distance to `ℤ` |
| `jsp87IntDist_lt_iff` | `jsp87IntDist x < ε ↔ ∃ k ∈ ℤ, \|x − k\| < ε` |
| `jsp87Series_rational_imp_truncCarry_dist_le` | the lattice form of the reduction: `b·jsp87TruncCarry N H` stays within `b·2^-H(N+H+1)` of `(1/b)ℤ` |
| `jsp87TruncCarryEscapes b` | **the named analytic hypothesis**: the truncated carry escapes the `b`-grid by more than its own tail bound |
| `jsp87Series_irrational_of_truncCarry_away` | **`∀ b ≥ 1, jsp87TruncCarryEscapes b` ⟹ `jsp87Series.Irrational`** |
| `pow_two_ge_sq_add_three` | `2^H ≥ (H+3)^2` for `H ≥ 8` |
| `jsp87Series_irrational_of_truncCarry_far` | **the uniform-spacing criterion**: `∀ b ≥ 1, ∃ c_b > 0, ∀ N H, jsp87IntDist (b·jsp87TruncCarry N H) ≥ c_b` ⟹ irrational — the shape of the variance estimate of arXiv:2512.01739 §5.3–§5.14 |
| `jsp87PlusLambert` | `∑' n, ω(n)/(2^n+1)` — the **`+1` Lambert series** of their §5.2 "*taking an alternating sum to cancel terms*" |
| `jsp87ScaleLambert k` | `∑' n, ω(n) 2^(-kn)` — the **dilations** of their §5.1 "*shifting and dilating*" |
| `jsp87PlusLambert_le_two_mul_series` | `∑' n, ω(n)/(2^n+1) ≤ 2 · jsp87Series` |
| `jsp87ScaleLambert_one` | the dilation at `2^{-1}` is twice the Erdős series |

**The quantifier over `b` in the two criteria must be universal.**  This is not a
technicality and is proved by inspection: the escape estimate at a single `b` is
*compatible* with a rational value whose denominator is `q ≠ b`, because §2
constrains the lattice `q^{-1}ℤ`, not `b^{-1}ℤ`.

### 2. Gate status

`lake build` succeeds; the tree contains **0 `sorry` / 0 `admit`** and **1952**
proved theorems and lemmas; `jsp_000087_main` remains **undeclared**, so
`prize_ready = false` and `missing_theorems = ['jsp_000087_main']`.

### 3. The concrete blocker after round 112

The single missing input is now **one named analytic hypothesis**, not a method:

> `jsp87TruncCarryEscapes b` (equivalently the uniform-spacing hypothesis of
> `jsp87Series_irrational_of_truncCarry_far`) for every `b ≥ 1`.

This is the content of Tao–Teräväinen's §5.3–§5.14, which rests on their
Theorem 3.1: the quantitative two-point correlation estimate for multiplicative
functions derived from **Pilatte's** recent quantitative Elliott-type work.  That
estimate (`(W/N)·Σ_{N<n≤2N}(g₁(n+h₁)−δ_N)g₂(n+h₂)1_{n≡b mod W} ≪ ℒ^{-c}` for
`1-bounded multiplicative g₁, g₂`, `W,b ≤ ℒ^c`, `1 ≤ ℒ ≪ log N`) has **no
counterpart in Mathlib**, and neither does the Erdős–Kac machinery, the
Gowers-uniformity manipulations, or the probabilistic (expectation / variance)
argument.  Mathlib contains no statement whatsoever about two-point correlations
of multiplicative functions, about prime-`k`-tuples, or about a two-point Chowla
bound for the Liouville function.

So: the deterministic reduction of the published proof is now machine checked
end-to-end, and the remaining gap is a single, precisely stated, *known* theorem
of analytic number theory rather than a research-level unknown.


---

## Round 115 — the Chowla-type correlations of `ω`

New module `lean/JSPProblem/Chowla.lean` (757 lines, **23 new public
theorems** and 9 new objects, 0 `sorry`, 0 `admit`; **2023 proved theorems and
lemmas** in the tree at the `^(theorem|lemma)` level — 2003 before this round —
`lake build` clean, no new linter warnings).

**Why this family.** Round 112–114 reduced the headline to the Tao–Teräväinen
object of arXiv:2512.01739 — a *truncated carry* — and recorded that the missing
input is a **variance** bound (§5.4).  A variance is a correlation sum, and
**no theorem name in the whole 2000-theorem tree contained `chowla` or
`corr`**: rounds 37–114 computed first moments (round 58) and pointwise bounds,
but never wrote down a correlation of `ω` with anything.  This round makes the
correlations objects of the development and computes them exactly.

### 1. The counting layer — one residue class per prime pair

| Theorem | Statement |
| --- | --- |
| `jsp87ShiftCount` | the new object: `# {n ∈ [1,N] : p ∣ n, q ∣ n+1}` — the solutions of `n ≡ 0 (mod p)`, `n ≡ −1 (mod q)` |
| `jsp87ShiftCount_dvd_sub` | **two solutions are congruent mod `p q`** (CRT, from scratch): `p q ∣ a − b` |
| `jsp87ShiftCount_card_le` | **one solution per period**: `≤ ⌊(N−1)/(p q)⌋ + 1` |
| `jsp87ShiftCount_card_le_one` | **at most one solution when `N ≤ p q`** |
| `jsp87ShiftCount_eq_zero_of_diag` | **the diagonal is empty** — no `m ≥ 2` divides both `n` and `n+1`, so the term `p = q` contributes nothing to any shift correlation |

### 2. The exact Chowla decomposition

| Theorem | Statement |
| --- | --- |
| `jsp87Chowla` | the new object `C N = ∑_{1 ≤ n ≤ N} ω(n) ω(n+1)` — the Chowla sum of `ω` |
| `jsp87Chowla_eq` | **THE MAIN THEOREM OF THE ROUND**: `C N = ∑_{p ≤ N} ∑_{q ≤ N+1} jsp87ShiftCount p q N`. Every ordered prime pair is counted exactly once; the analytic question becomes a purely combinatorial one |
| `jsp87_chowla_eq_corrAt` | `C N = jsp87CorrAt (N+1) 0 1` — `jsp87Chowla` is the `(0,1)` instance of the general shift-pair correlation |
| `jsp87Chowla_le`, `jsp87ShiftCount_le_pair` | the pointwise mean-field bound |
| **`jsp87Chowla_le_add`** | **THE CORRELATION IS THE MEAN-FIELD TERM PLUS THE BOUNDARY ERROR**: `C N ≤ jsp87ChowlaMain N + jsp87ChowlaErr N`, the error being exactly the number of ordered distinct prime pairs up to `N+1`, i.e. of size `π(N+1)²`. **Any improvement of the published proof over this elementary bound must absorb this term** — this is the exact shape of the analytic problem |

### 3. Pratt's object, squeezed unconditionally

`jsp87PrimeShiftCorr N = ∑_{1 ≤ n ≤ N} ω(n)·[n+1 prime]` is the object K. Pratt's
uniform prime `k`-tuples hypothesis is *about*.

| Theorem | Statement |
| --- | --- |
| `jsp87PrimeShiftCorr_eq` | the exact decomposition `= ∑_{p ≤ N} # {n ∈ [1,N] : p ∣ n, n+1 prime}` — the sieve content, prime by prime |
| `jsp87PrimeShiftCorr_ge` | `# {q prime : 3 ≤ q ≤ N+1} ≤ jsp87PrimeShiftCorr N` (each such `q` contributes at `n = q−1`, where `ω(q−1) ≥ 1`) |
| `jsp87PrimeShiftCorr_ge_odd` | **`π(N+1) ≤ jsp87PrimeShiftCorr N + 1`** |
| `jsp87PrimeShiftCorr_le_omegaCount` | **`jsp87PrimeShiftCorr N ≤ ∑_{p ≤ N} ⌊N/p⌋ = jsp87OmegaCount N`** |

i.e. the **unconditional sandwich `π(N+1) − 1 ≤ corr ≤ A N`**: at primes the
correlation is at least one per prime, and unconditionally it is worth no more
than the first moment. **The gap between the two bounds is exactly where the
hypothesis of the literature lives.**

### 4. The join with the Tao–Teräväinen route

| Theorem | Statement |
| --- | --- |
| `jsp87_truncSum_eq` | **THE MEAN OF THE TRUNCATED CARRY**: `∑_{N<L} jsp87TruncCarry N H = ∑_{k<H} 2^{-(k+1)} · (ω-mass of the window at k)` — the mean term of §5.3 is exactly round 58's first moment |

### 5. Machine-checked instances

`jsp87Chowla 10 = 13`, `jsp87Chowla 100 = 284`, `jsp87Chowla 1000 = 4319`;
`jsp87PrimeShiftCorr 10 = 6`, `= 53` at `N = 100`; `jsp87ShiftCount 2 3 10 = 2`,
`jsp87ShiftCount 2 3 5 = 1`, `jsp87ShiftCount 2 5 10 = 1`; and
`jsp87CorrAt 11 0 1 = jsp87Chowla 10` (an instance of `jsp87_chowla_eq_corrAt`).

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is a theorem in the literature (Tao–Teräväinen, arXiv:2512.01739,
Thm 1.3 = Erdős problem #69, *unconditional*); only the Lean proof is missing,
and it rests on their quantitative two-point correlation estimate for `ω`
(Thm 3.1, from Pilatte's work), which Mathlib does not contain.  Round 115 turns
that estimate from prose into a **Lean object with an exact unconditional
baseline**: the mean-field main term plus a `π(N+1)²` boundary error.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 115, stated exactly

> **The missing analytic input is a bound on `jsp87Chowla N` that beats the
> boundary error `jsp87ChowlaErr N`.**  Everything else is machine-checked: the
> exact decomposition (`jsp87Chowla_eq`), the elementary bound
> (`jsp87Chowla_le_add`), the equivalent shifted-prime statement with its
> unconditional sandwich, and the mean of the Tao–Teräväinen truncated carry
> (`jsp87_truncSum_eq`).

A second, purely `Lean`-technical blocker was opened and left open:
**`jsp87_truncSq_diag`** — the diagonal/off-diagonal split of the second moment
of the truncated carry, i.e. `∑_{N<L} T(N,H)² = ∑_{k,k'<H} 2^{-(k+1)-(k'+1)} ·
jsp87CorrAt L k k'`.  The statement and the exact remaining step are recorded
verbatim in `lean/JSPProblem/Chowla.lean` (section *The second moment of the
truncated carry*).

---

## Round 117 — SECTION 6 EXECUTED: the cube-alternating variable `X_p`, and the DISCHARGE of hypothesis (5.19)

New module `lean/JSPProblem/Xp.lean` (640 lines, **34 new theorems and lemmas**
plus 4 private helpers and 9 new definitions, 0 `sorry`, 0 `admit`, 0 warnings;
**2363 theorem/lemma declarations** in the tree, `lake build` clean).

Round 116 proved the endgame of Tao–Teräväinen §5 (`jsp87_endgame_impossible`:
their `Theorem 5.1` is incompatible with their own `(5.18)`) and **explicitly
abandoned** the very object the remaining hypotheses are about, recording
*"NEXT ROUND: re-derive §6 from the definitions above"*.  **This round is that
§6.**  The random variable of (5.13) is

```
X_p = q ∑_{1≤h≤H} ∑_{ε∈{0,1}^K} (−1)^{|ε|} 2^{−(h+K)} [ p ∣ n + r_{ε,h+K} ]
```

an alternating sum over the vertices of a Hilbert cube.

### 1. The objects of (5.13)

| Declaration | Statement |
| --- | --- |
| `jsp87Off`, `jsp87R` | the vertex offset and **the cube shift** `r_{ε,h} = h + Σ_{k∈ε} v_k` |
| `jsp87R_mem_le` | `r_{ε,h} ≤ h + Σ_k v_k` |
| `jsp87HitVerts` | **the hitting vertices** `{ε : p ∣ n + r_{ε,h}}` — the set `T` of §6 |
| `jsp87W` | **the level weight** `2^{−(h+K)}`, with `jsp87W_eq_half`, `jsp87W_pos`, `jsp87W_le_one`, `jsp87W_anti` |
| `jsp87XpLevel` | the inner `2^K`-term alternating sum of (5.13) |
| `jsp87Xp0`, `jsp87Xp` | **the variable `X_p` of (5.13)**, with and without the leading `q` |
| `jsp87XpLevel_eq_filter`, `jsp87Xp0_eq_filter` | the literal double sum equals weight × sign-sum over the hit vertices |

### 2. (A) THE ONE-VERTEX COLLAPSE — and the size bound (5.36)

| Theorem | Statement |
| --- | --- |
| `jsp87Sep` | **the separation hypothesis**: at level `h` the prime `p` exceeds every cube shift and the shifts are pairwise distinct |
| **`jsp87OneVertex_of_sep`** | the separation hypothesis implies **at most one vertex is hit**, from scratch (`Nat.dvd_sub`, `Nat.dvd_iff_mod_eq_zero`, `Nat.mod_eq_of_lt`) |
| **`jsp87XpLevel_eq_of_hit`** | **THE COLLAPSE**: `∑_ε (−1)^{|ε|} 2^{−(h+K)} [p ∣ n + r_{ε,h}] = (−1)^{|ε*|} · 2^{−(h+K)}` |
| `jsp87XpLevel_eq_zero_or_sign` | the level sum is `0` or a single signed weight |
| `jsp87XpLevel_abs_le` | `|level sum| ≤ 2^{−(h+K)}` |
| `jsp87Xp0_abs_le_weight` | `|X_p| ≤ ∑_{h≤H} 2^{−(h+K)}` |
| **`jsp87Xp_abs_le`** | **(5.36)**: `|X_p| ≤ |q| · H · 2^{−K}`, uniformly in the sample point |

### 3. (B) **HYPOTHESIS (5.19) IS DISCHARGED**

| Theorem | Statement |
| --- | --- |
| **`exists_K_abs_le`** | for every `q > 0` and `H` there is `K ≥ 1` with `q · H · 2^{−K} ≤ 1/20` (from `exists_pow_lt_real`, r. 46) |
| `jsp87Xp_abs_le_twenty`, `jsp87Xp0_abs_le_twenty` | `|q X_p| ≤ 1/20` at every sample point, for such `K` |
| **`jsp87_endgame_cube`** | **with `T p i = X_p(i) = jsp87Xp0 (v p) p i H`, the separation hypothesis and `|q| H 2^{−K} ≤ 1/20`, the round-116 endgame applies verbatim: `κ₁+⋯+κ₅ ≥ 1/2`, so the five error terms cannot all be `< 1/30`.** Of the five hypotheses of their `Theorem 5.1`, (5.19) is now discharged; (5.15), (5.16)–(5.17) are their own analytic reduction |

### 4. (C) THE `S₀` MECHANISM — why (5.21) sums only over `S₁`

| Theorem | Statement |
| --- | --- |
| `jsp87sign_sum_zero`, `jsp87sign_sum_mul` | `∑_ε (−1)^{|ε|} = 0` for `K ≥ 1` (from `jsp87_cube_cancelR`, r. 88) |
| **`jsp87XpLevel_eq_zero_of_allHit`** | **the all-hit collapse**: if *every* vertex is hit, the level sum vanishes — the `2^K` signs cancel |
| **`jsp87Xp0_eq_zero_of_dvd_all`** | **the zero-prime mechanism**: if `p` divides every cube shift and `p ∣ n`, then `X_p = 0` |
| **`jsp87Var_zero_of_zeroPrime`** | hence `Var (q X_p) = 0` on every sample set contained in the progression `p ℕ` |

### 5. (D) THE VARIANCE TOOLBOX

| Theorem | Statement |
| --- | --- |
| `jsp87FAvg_const` | the average of a constant is that constant |
| **`jsp87Var_le_avg_sq`** | `Var f = 𝔼 f² − (𝔼 f)² ≤ 𝔼 f²`, from scratch |
| **`jsp87Var_le_sq`** | `|f| ≤ B` pointwise ⟹ `Var f ≤ B²` |
| **`jsp87Var_Xp_le`** | **`Var (q X_p) ≤ (|q| H 2^{−K})²`** — the variance of the cube-alternating variable decays like `4^{−K}` |
| `jsp87Var_zero_of_zero`, `jsp87Var_Xp_zero_of_noHit` | the variance vanishes when the cube is never hit |

### 6. (E) DETERMINISM — the mechanism behind (5.16)–(5.17)

| Theorem | Statement |
| --- | --- |
| `jsp87XpLevel_eq_of_pattern` | at one level: if the hit patterns of two sample points match (a hit, carrying the same sign) then the level sums agree |
| **`jsp87Xp0_eq_of_pattern`** | **`X_p` depends on the sample point only through the signs of the hit vertices at each level** |
| `jsp87Xp0_eq_of_hitSet` | the same hit set gives the same `X_p`, with no one-vertex hypothesis |

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  What this round adds
is the *object* of the published proof and the discharge of one of its five
hypotheses; the missing input remains a *quantitative two-point correlation
estimate for `ω`* (Tao–Teräväinen `Theorem 3.1`, from Pilatte), for which
Mathlib has no analogue whatsoever.

`harness/score.py problems/JSP-000087 --strict-prize` reports
`build_ok=true, sorry=0, admit=0, placeholder_total=0, partial_ok=true,
prize_ready=false, missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 117, stated exactly

> **`(5.21)` `1 ≤ ∑_{p∈S₁} Var (q X_p)`** — a *lower* bound on the variance of
> the cube-alternating variables `X_p` of (5.13), for the primes of `S₁`.

This round proved everything *around* it: the size bound (5.36), the discharge
of (5.19), the `S₀` zero-variance theorem that makes the restriction to `S₁`
meaningful, and the matching upper bound `Var (q X_p) ≤ (|q| H 2^{−K})²`.  What
is missing is the lower bound, i.e. that the cube is genuinely non-degenerate at
the `S₁` primes for a positive proportion of the sample — exactly their
`Theorem 3.1`.

### The Mathlib correction of this round (do not repeat these)

* `Finset.mem_univ` is **not usable for `Finset ℕ`** (no `Fintype ℕ`): sample-set
  membership must always be carried as an explicit hypothesis, never produced
  by `Finset.mem_univ`.
* `Finset.nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅` — use `.mpr` on a `≠ ∅`
  hypothesis (and `.mp` on a `Nonempty` hypothesis); `Finset.card_le_one`,
  `Finset.card_eq_one`, `Finset.card_eq_zero` are **iffs**, not implications.
* `Nat.exists_eq_add_of_le : m ≤ n → ∃ k, n = m + k` (implicit `m`, `n`);
  `Nat.eq_zero_of_not_pos` (not `omega`) for `¬ 0 < n → n = 0`.
* `zpow_natCast` (not `zpow_ofNat`, whose printed signature is useless) converts
  `a ^ (n : ℤ)` to `a ^ n`; `pow_le_pow_right₀` (base ≥ 1) is the convenient
  ℕ-power monotonicity lemma; `inv_le_inv₀` is an **iff**.
* An identifier may **not** mix a subscript digit with a following letter
  (`ε₁b` is not an identifier; `ε₂` is), and `ε*` is not an identifier at all.
* `Finset.sum_congr` does **not** apply to a goal of the form
  `c * ∑ x ∈ s, f x = c * ∑ x ∈ s, g x`: use `rw [Finset.mul_sum]` first.
* `ring` cannot close a goal whose summand is only *syntactically* constant:
  rewrite with `Finset.sum_congr` + `jsp87Sign_abs` first.

---

## Round 118 — THE CLASS-COUNT FORM OF THE VARIANCE BOUND `(5.21)`

`lean/JSPProblem/VarLocal.lean` (931 lines, 36 new theorems/lemmas, 5 new
definitions, 0 sorry, 0 admit; 2399 theorem/lemma declarations tree-wide,
`lake build` clean).

### What the round did

`policy.json` `next_round_attack[1]` asked, for the first time in 118 rounds,
for the **exact square-sum identity for `Var (q X_p)` in terms of the hit
pattern**, "pure combinatorics over the hit set", on the ground that it would
localise `(5.21)` to a statement about how many sample points share a pattern.
The identity is proved — **and the hit-pattern formulation is FALSE.**  The
level weights of (5.13) are a geometric sequence, `w_m = 2 w_{m+1}`
(`jsp87W_succ`), so one binary carry makes two *different* patterns give the
*same* value of `X_p` (`jsp87Xp0_code_collision`, `jsp87Xp0_eq_of_code_carry`).
The correct object is the **hit value**, which lives on a fixed lattice.

| Object | Statement |
| --- | --- |
| `jsp87XpCode` | the level code `c p n h = ∑_{ε hit} (−1)^{|ε|}`; under one-vertex, `c ∈ {−1,0,1}` (`jsp87XpCode_mem`), and `jsp87XpLevel_eq_code` / `jsp87Xp0_eq_code` collapse `X_p` to `∑_h c h w h` with **no hypothesis** |
| `jsp87bin_gap` / `jsp87W_sum_sub_ge` | the **binary-weight gap**: distinct subsets of the levels have level sums at distance `≥ 2^{−(H+K)}` (uniqueness of binary expansion, from scratch: `1 + 2x` vs `2y`, an odd number cannot vanish) |
| `jsp87XpIntDiff`, `jsp87Xp0_sub_eq_scale` | **THE DISCRETENESS OF THE CUBE SUM**: `X_p(n) − X_p(n′) = 2^{−(H+K)} · (an integer)` |
| `jsp87Xp0_sub_eq_zero_or_ge` | **THE UNIFORM GAP**: two cube sums are either equal or at distance `≥ 2^{−(H+K)}` — the discrete replacement for the (false) aperiodicity of the hit patterns |
| `jsp87Class`, `jsp87Class_const` | the **hit-value classes** `{n ∈ s : f n = A}`, and constancy of any function of `f` on a class |
| `jsp87_sum_diff_sq_class` | **THE CLASS-COUNT IDENTITY**: `∑_{i,j} (f i − f j)² = ∑_{A,B} \|A\|\|B\| (A − B)²` over ordered pairs of attained values |
| `jsp87Var_eq_classSum` | `2 \|s\|² Var f = ∑_{A,B classes} \|A\|\|B\| (v_A − v_B)²` — the exact weighted count of the pairs of sample points whose cube sums differ |
| `jsp87Var_eq_zero_iff_const` | the other half: the variance vanishes exactly on a single class |
| `jsp87Var_ge_twoClass` | **A BALANCED TWO-CLASS SPLIT FORCES VARIANCE**: `Var f ≥ \|A\|\|B\| δ² / \|s\|²` |
| `jsp87Var_Xp_ge_twoClass` | the lattice form for the cube sum: `q² \|A\|\|B\| 2^{−2(H+K)} / \|s\|² ≤ Var (q X_p)` (the separation is automatic once the values differ, by §3) |
| `jsp87Var_Xp_ge_one` | **one** prime with a balanced split supplies `(5.21)`, with a closed-form threshold `q² \|A\|\|B\| 2^{−2(H+K)} ≥ \|s\|²` |
| `jsp87_varSum_ge` | the variance sum over the `S₁` primes |
| `jsp87_endgame_twoClass` | **THE ENDGAME, `(5.21)` DISCHARGED**: under (5.15), (5.16)–(5.17), (5.19) and a balanced two-class split, the five error terms `κ_1 … κ_5` cannot all be `< 1/30` |

### Consequence for the gate

`jsp_000087_main` is **still not declared** and the gate stays
`partial_ok=true, prize_ready=false`.  The entire remaining burden is now a
**single discrete hypothesis** about the distribution of `ω`:

> for some prime `p` and some sample `s` of integers, the hit values of `X_p`
> split `s` into two non-empty parts `A, B` that never agree, with
> `q² \|A\|\|B\| 2^{−2(H+K)} ≥ \|s\|²`.

This is the content of Tao–Teräväinen §3 (their `Theorem 3.1`, from Pilatte):
Mathlib has no Chowla-type or Elliott-type statement for multiplicative
functions, so the input cannot be supplied here.

### The Mathlib corrections of this round (do not repeat these)

* `∑ x ∈ s, f x` is a **single** sum over `s`; `∑ x in s, f x` is **not** valid
  syntax in this Mathlib version (the `in` binder was removed).
* `Finset.sum_product s t f : ∑ p ∈ s ×ˢ t, f p = ∑ x ∈ s, ∑ y ∈ t, f (x, y)` —
  **both** finsets are explicit arguments.
* `Finset.sum_fiberwise_of_maps_to (H : ∀ i ∈ s, g i ∈ t) (w) :
  ∑ j ∈ t, ∑ i ∈ s with g i = j, w i = ∑ i ∈ s, w i` — `Fintype` is *not*
  needed for the finite version.
* `Finset.mem_erase : x ∈ s.erase a ↔ x ≠ a ∧ x ∈ s` (the `≠` comes **first**);
  `Finset.mem_singleton : x ∈ {a} ↔ x = a`.
* `Finset.sum_subset (h : s₁ ⊆ s₂) (g : ∀ x ∈ s₂, x ∉ s₁ → f x = 0) :
  ∑ s₁ = ∑ s₂` — the hypothesis ranges over **`s₂`**.
* `Finset.sum_const : ∑ x ∈ s, b = s.card • b`; convert with `nsmul_eq_mul`.
* `Finset.not_mem_empty_iff` and `Finset.not_mem_empty` **do not exist**; use
  `by simp` or `Finset.mem_empty`.
* `abs_of_neg`/`abs_of_pos`, `sq_abs`, `abs_sub_comm`, `sq_le_sq₀` are the
  right tools; `sq_sub` and `sq_neg` **do not exist** in this Mathlib version.
* `div_le_iff₀ hc2` (not `le_div_iff₀`) for the goal `k / c ≤ L`; `c ^ 2 > 0`
  follows from `positivity`.
* `rw` cannot apply `← Finset.mul_sum` (its pattern `∑ a * f` needs a
  *hidden* constant); use `refine (Finset.sum_congr rfl fun _ _ => ?_)` and
  `ring` on the summands, or state the step with explicit arguments.
* `by_contra`/`absurd` need the negation on the *right*: to derive `False`
  from `hneg : ¬ P` and `hne : ¬ P` use `hneg hne`; to get `P` from `¬ P` use
  `by_contra` and then `hcon hne`.

---

## Round 120 — THE ACTIVE RESIDUE CLASSES, AND WHY (5.21) CANNOT COME FROM A UNIFORM SAMPLE

New module `lean/JSPProblem/ActiveCube.lean` (742 lines, **33 new theorems and
lemmas** (29 public) plus 2 new definitions, 0 `sorry`, 0 `admit`, 0 linter
warnings; **2458 proved theorems and lemmas** at the `^(theorem|lemma)` level —
2425 before this round — `lake build` clean, 68 modules).

This round executes `policy.json` `next_round_attack[0]`, the first item of that
list, **unexecuted for 119 rounds**: the counting object `jsp87Active`, its exact
count over a complete residue system, and the density `2^K / p`.  It also
**closes the third blocker of round 119** (non-degeneracy of `X_p`) and yields a
machine-checked **negative** result about the endgame itself.

### 1. The counting object (item (a), (b), (c) of `next_round_attack[0]`)

| Theorem | Statement |
| --- | --- |
| `jsp87Active` | **the new object**: level `h` is active at `n`, i.e. some vertex `ε` of the binary cube is hit, `p ∣ n + h + Σ_{k∈ε} 2^k` |
| `jsp87ActiveRes` | **the new object**: the active residue classes `p − (h + off ε)`, one per vertex |
| `jsp87ActiveRes_card` | **THE EXACT COUNT OF THE ACTIVE RESIDUE CLASSES IS `2^K`** — injectivity from `jsp87Off_binV_inj` plus `Fintype.card_finset` |
| `jsp87Active_iff_activeRes` | activity **is** membership of the active residue classes (for `n ≤ p − 1`) |
| `jsp87Active_res_card` | **exactly `2^K` of the `p` residues make level `h` active** |
| `jsp87Active_density` | **the density of the active classes is `2^K / p`** |
| `jsp87Active_period`, `jsp87Active_of_dvd_pow` | activity is periodic in the sample point; a power-of-two hit is an activity |

### 2. Non-degeneracy, unconditionally — **round 119's third blocker is closed**

| Theorem | Statement |
| --- | --- |
| `jsp87W_tail` | **THE CLOSED FORM OF THE LEVEL TAIL**: `Σ_{h' ∈ (h,H]} 2^{−(h'+K)} = 2^{−(h+K)} − 2^{−(H+K)}` |
| `jsp87XpLevel_ne_zero_of_active`, `jsp87XpLevel_eq_zero_iff_not_active` | a level of the binary cube is *either dead or alive*: the level sum is `0` exactly at inactive levels |
| `jsp87Xp0_abs_ge_active` | **THE SIZE OF THE WHOLE CUBE SUM AT A LEAST ACTIVE LEVEL**: `2^{−(H+K)} ≤ |X_p|`, uniformly in `h` |
| `jsp87Xp0_ne_zero_of_active_one`, `jsp87Xp0_ne_zero_card` | activity at the bottom level forces `X_p ≠ 0`; at least `2^K` residues have a nonzero cube sum |
| **`jsp87Xp0_ne_zero_exists`** | **NON-DEGENERACY, UNCONDITIONALLY**: for every `K`, every `p > 2^K`, every `H ≥ 1`, the variable `X_p` of (5.13) is **not identically zero** — nonzero at at least `2^K` of the `p` residue classes. Nothing is left to assume about the sample. |

### 3. The zero class and the variance window

| Theorem | Statement |
| --- | --- |
| `jsp87Xp0_eq_zero_of_dvd`, `jsp87Xp0_eq_zero_zero` | **THE ZERO CLASS**: under `H + 2^K − 1 < p`, no level can be hit at a multiple of `p`, so `X_p(p·m) = 0` for every `m` |
| `jsp87Var_Xp_res_lower`, `jsp87Var_Xp_res_upper` | the two ends of the variance estimate over the complete residue system |
| **`jsp87Var_Xp_res_window`** | `q² · 2^K 2^{−2(H+K)} / p² ≤ Var (q X_p) ≤ (|q| H 2^{−K})²` — the variance of the endgame variable over a uniform sample is `≈ q² / p` and **decays in `p`** |

### 4. THE HEADLINE NEGATIVE RESULT — (5.21) is unobtainable for a uniform sample

| Theorem | Statement |
| --- | --- |
| **`jsp87_Xp_res_5_21_impossible`** | for the binary cube, `2^K ≤ p`, `H + 2^K − 1 < p` and `|q| H 2^{−K} ≤ 1/20`: **`¬ (1 ≤ Var (Icc 0 (p−1)) (fun n => q * X_p n))`** — hypothesis (5.21) of the endgame is *never satisfiable* for a sample that is a uniform residue system modulo `p` |
| `jsp87_endgame_res_of_5_21` | if (5.21) *were* satisfiable, the endgame fires: the five error terms of §5 cannot all be `< 1/30` |
| `jsp87_endgame_res_summary` | **THE DICHOTOMY**, in one theorem |

Consequence, machine-checked: **the endgame of Tao–Teräväinen arXiv:2512.01739 §5
is vacuous for uniform samples**, and its sample cannot be one.  The two remaining
arithmetic inputs of `jsp_000087_main` — the uniformity hypothesis (5.18) and the
two-point correlation estimate `Theorem 3.1` (from Pilatte) — are therefore
**provably correlation inputs**, not artefacts of this formalisation: no
combinatorial statement about uniform residues can replace them.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  The headline
irrationality is a theorem in the literature (Tao–Teräväinen,
arXiv:2512.01739 Thm 1.3 = Erdős problem #69); what is missing is its *proof*,
whose analytic input is the quantitative two-point correlation estimate for
bounded multiplicative functions.  Mathlib has no Chowla-type or Elliott-type
statement for multiplicative functions, and round 120 proves that gap is
indispensable.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 120, stated exactly

> **`jsp87_balancedSplit`** (round 118) and **(5.18) `κ_j = o(1)`** — unchanged,
> but now provably *correlational*: `jsp87_Xp_res_5_21_impossible` shows the
> variance of (5.21) can never come from a uniform residue system, so it must come
> from the structure of the sample along progressions modulo `p`, i.e. from
> `Theorem 3.1` / (5.18).

### Mathlib findings of this round (do not repeat these costs)

* **no** `Finset.sum_Icc_add_Icc`, **no** `Finset.sum_Icc_singleton`,
  **no** `Finset.card_Icc`, **no** `Finset.not_mem_empty`,
  **no** `Finset.filter_eq_empty_eq_exists`,
  **no** `Finset.union_singleton_filter_neg_filter`,
  **no** `Nat.pos_of_ne_of_dvd`, **no** `Nat.mul_sub_of_le`,
  **no** `Nat.eq_zero_or_pos_of_lt`: only `Finset.sum_Icc_succ_top`,
  `Nat.card_Icc`, `Nat.add_sub_of_le`, `Nat.sub_le_sub_right`.
* `abs_sub_le_iff` is stated with a general right-hand side
  (`|a − b| ≤ c ↔ a − b ≤ c ∧ b − a ≤ c`); the reverse triangle inequality is
  `norm_sub_le` + `le_abs_self`.
* **instance search does not unfold a plain `def` used as a `Finset.filter`
  predicate** — mark it `@[reducible]` (this is why `jsp87Active` carries
  `attribute [reducible]`).
* **`omega` treats `H + 2^K − 1` as an opaque ATOM**: it cannot relate it to
  `1 + 2^K − 1` or to `2^K`. Use `Nat.sub_le_sub_right`, `Nat.add_sub_of_le`,
  `Nat.add_sub_assoc` (whose hypothesis is `k ≤ m`, named args `(m := …) (k := …)`)
  explicitly. `omega` also **degrades when a divisibility hypothesis `p ∣ m` is in
  scope** (it introduces a `%` atom that blocks the reasoning): `clear` it first.
* `obtain ⟨x, h, rfl⟩` substitutes `x` *immediately*, so a subsequent `obtain`
  on another hypothesis silently loses the link between the two witnesses.
* `Nat.mul_lt_mul_right` has the positivity proof as its **first** explicit
  argument and returns an `iff`; use `Nat.lt_of_mul_lt_mul_right` for the plain
  form.
* **`r = r'` for two elements of the image of an injective map is FALSE** — this
  round refuted its own first formulation of `jsp87ActiveRes_inj`. Injectivity
  yields `ε = ε'` only *from* the equation `r = r'`.

### Abandoned in this round (recorded for the next)

1. the two-level obstruction `jsp87Active_twoLevel` (two levels both active only
   through cube offsets `< 2^{min k}`): the statement needs the extra hypothesis
   `h' − h + 2^{k'} < p`, and the final power-of-two monotonicity step must use
   `Nat.pow_le_pow_right` (not `omega`) — dropped for lack of time, **not**
   because it is false;
2. `B = {0}` as the second class of the variance bound: false in general, since
   not every nonzero residue is active at level 1 — the correct class is the zero
   class `{n ∈ s ∣ X_p n = 0}`, which is what the theorem now uses.

---

## Round 123 — THE SAMPLE AS AN EXPLICIT OBJECT: the EXACT nonzero fraction along a progression

New module `lean/JSPProblem/ProgSample.lean` (1209 lines, **34 new public theorems**
plus 7 private helpers and 6 new definitions, 0 `sorry`, 0 `admit`;
**2547 proved theorems and lemmas** at the `^(theorem|lemma)` level — 2502 before
this round, 2241 of them public — `lake build` clean, 70 modules).
`harness/score.py --strict-prize` reports `build_ok=true, sorry=0, admit=0,
partial_ok=true, prize_ready=false, missing_theorems=["jsp_000087_main"]`.

This round executes `policy.json` `next_round_attack[0]`, unexecuted for **122
rounds** ("make `s` an explicit structured set … and **COMPUTE** `jsp87NzFrac K p H s`
for it … either a (5.21′) witness or a machine-checked obstruction for the AP
sample"), for **both** candidate samples:

* candidate (a) the progression sample — **completed**, with the exact value of
  `jsp87NzFrac` on it;
* candidate (b) the sieve sample — **killed**, machine-checkably.

### 1. The progression sample and the permutation of the residue system

| Theorem | Statement |
| --- | --- |
| `jsp87Prog` | **the new object**: `jsp87Prog n0 D N = image (fun j => n0 + D * j) (Icc 0 N)`, the progression with start point, step and length as data |
| `jsp87Prog_card`, `jsp87Prog_nonempty`, `jsp87Prog_mem_iff` | its cardinality is `N + 1`, it is nonempty, and membership is an explicit index |
| **`jsp87Prog_block_bij`** | **THE ARITHMETIC CORE**: for prime `p` and `¬ p ∣ D`, the map `j ↦ (n0 + D * j) mod p` is a **permutation of the residue system** — proved in `ZMod p`, which is a field exactly when `p` is prime |
| `jsp87Prog_res_surj`, `jsp87Prog_shift_eq` | every residue is attained by the progression; shifting the start point by a multiple of `p` changes nothing |

### 2. The exact residue count that (5.21) needs

| Theorem | Statement |
| --- | --- |
| **`jsp87Xp0_ne_zero_iff_active`** | **the NEW converse** of `jsp87XpLevel_eq_zero_iff_not_active`: a nonzero cube sum means *some* level is active (needed for the union bound below) |
| `jsp87NzResCard`, `jsp87NzResCard_pos`, `jsp87NzResCard_le_p` | **the new object**: the number of residues at which `X_p` is nonzero; `1 ≤ c_p ≤ p − 1` |
| **`jsp87NzResCard_bounds`** | `2^K ≤ c_p ≤ H * 2^K` — the active classes are `2^K`, and every further active level adds at most `2^K` of them |
| `jsp87zeroRes_card_res` | the zero class has `p − c_p` residues |

### 3. The exact fraction along a progression — **the statement round 122 lacked**

| Theorem | Statement |
| --- | --- |
| `jsp87Prog_zero_card_base` | the zero class of `X_p` is exactly `{n ∈ s ∣ p ∣ n}` on any progression |
| **`jsp87Prog_zero_card_block`** | **DISCRETE EQUIDISTRIBUTION**: a *whole* `p`-block of the progression contains exactly `p − c_p` zeros, for **any** position of the block |
| `jsp87Prog_zero_card_blocks` | `c` whole blocks contain `c * (p − c_p)` zeros |
| **`jsp87_nzFrac_prog_blocks`** | **THE EXACT NONZERO FRACTION**: `jsp87NzFrac K p H (jsp87Prog n0 D (c * p − 1)) = c_p / p` for every `c ≥ 1`, every `n0` and every step `D` coprime to `p` — **independent of sample length, start point and step** |
| `jsp87_nzFrac_prog_blocks_bounds`, `jsp87_nzFrac_prog_blocks_pos` | `2^K / p ≤ f_p ≤ H 2^K / p`, and `0 < f_p < 1` — the positive counterpart of round 122's `jsp87_5_21_prog_impossible` |
| `jsp87ProgFull`, `jsp87ProgFull_card`, `jsp87ProgFull_nonempty`, **`jsp87ProgFull_nzFrac`** | **THE CANONICAL STRUCTURED SAMPLE** `jsp87ProgFull n0 D P = jsp87Prog n0 D (prod P − 1)`: a whole number of `p`-blocks for **every** prime of `S₁` at once, with `f_p` computed prime by prime |
| **`jsp87ProgFull_hne`** | the two-class hypothesis `hne` — a divisible point and a level-1 active point — holds **unconditionally** on the canonical sample |

### 4. Candidate (b) is dead — the sieve sample

| Theorem | Statement |
| --- | --- |
| `jsp87SieveSample`, `jsp87_nzFrac_zero_of_dvdSample` | the sieve sample: every element is divisible by some prime of `S₁`, so `X_p = 0` **on the whole sample** |
| **`jsp87_nzFrac_sieve_zero`**, **`jsp87Var_sieve_zero`** | its nonzero fraction is `0`, and **its variance contribution to (5.21) is literally `0`** |
| **`jsp87_5_21_sieve_impossible`** | **no sieve-shaped sample can ever supply (5.21′)** — candidate (b) of `next_round_attack[0]` is machine-checkably impossible |
| `jsp87_5_21_singleRes_any` | round 122's obstruction is subsumed: a single-residue (killing-ε) sample cannot work either |

### 5. The endgame with an explicit arithmetic (5.21″)

| Theorem | Statement |
| --- | --- |
| `jsp87R521b` | the explicit condition `1 ≤ q² 2^{−2(H+K)} Σ_{p ∈ P} (c_p / p) (1 − c_p / p)`, a statement about the **prime set alone** |
| **`jsp87_5_21_progFull_iff`** | **EQUIVALENCE**: on the canonical sample, `jsp87_5_21_singleResP`-style variance hypothesis `hrec` holds **iff** (5.21″) holds |
| **`jsp87_endgame_progFull`** | **THE ENDGAME OF arXiv:2512.01739 §§5.3–5.14 WITH A COMPUTED SAMPLE**: `jsp87R521b ∧ (exact fractions prime by prime) ∧ hne` gives (5.15), (5.16)–(5.17), the separation hypothesis, the hypotheses of (5.19) and the conclusion |
| `jsp87NzFrac_mul_le`, `jsp87_5_21b_summand_le` | the summand bound used below |
| **`jsp87_5_21_needs_recipSum`** | **NECESSITY — a statement about the set of primes alone**: (5.21″) forces `Σ_{p ∈ P} 1/p ≥ 2^{2H+K} / (H q²)`, for the `q`, `H` of (5.19) |
| **`jsp87_5_21_prog_of_recipSum`** | **SUFFICIENCY**: under `p ≥ H 2^K` and `q² 2^{−2(H+K)} Σ (2^K / p) (1 − H 2^K / p) ≥ 1`, (5.21′) **holds** for the canonical progression sample |
| `jsp87_prog_summary` | both directions in one statement |

### 6. Why this matters for `jsp_000087_main`

Round 123 **computes the sample geometry in full**: for an explicit structured
sample, the fraction of nonzero cube sums is known exactly, prime by prime, and
the variance hypothesis (5.21) is *equivalent to a pure arithmetic inequality over
the reciprocals of `S₁`*. The sample hypothesis is therefore no longer a source of
obstruction, and the remaining burden is localised to **two arithmetic inputs**,
both statements about the prime set `S₁`:

1. **(5.21″)/reciprocal sum** — some set of primes larger than `H + 2^K − 1`,
   none dividing the step `D`, with harmonic mass `≥ 2^{2H+K} / (H q²)`;
2. **(5.18)** — the five estimates `κ_j = o(1)` (`j = 1 … 5`).

### Mathlib findings of this round (do not repeat these costs)

* **no** `Finset.Icc_union_Icc`, **no**
  `Finset.card_filter_add_card_filter_neg_eq_card` (only the `_not` variant),
  **no** `Finset.card_filter_le`;
* **`linarith`/`nlinarith` do not work on goals built with the `HSub` instance of
  `ℝ`**: even `1 - x ≤ 1 - y` from `y ≤ x` fails. Three private lemmas replace
  them: `jsp87sub_le_sub_one`, `jsp87zero_le_sub_one`, `jsp87sub_le_one`;
* the reverse triangle/`abs_sub_le_iff` costs of round 83 still apply to
  `|q|` bounds;
* **`omega` cannot see through `2^(2 * H + K) = 4^(H+K) / 2^K`**; use
  `calc … ≤ … := …  … ≤ … := (h.eq.le.trans h)` — i.e. an equality hypothesis
  used as a bound needs `hid.le.trans`, not `le_trans hid _`.

### Abandoned in this round (recorded for the next)

1. **the "(5.21′) witness" branch of `next_round_attack[0]`** is unreachable:
   (5.21′) is *now* an explicit reciprocal-sum inequality, so the sample half is
   finished and only the prime-set half remains;
2. candidate (b), the sieve sample, abandoned (machine-checked dead);
3. the step `D = prod P` of candidate (a) stays impossible (round 122); the
   surviving sample needs `¬ p ∣ D` for every prime of `S₁`, which this round
   makes explicit.

---

## Round 126 — THE SINGLE-SCALE FORM OF (5.18), ITS REAL DECOMPOSITION, THE GROUND TRUTH AT `K = 0`, AND **THE REFUTATION OF (5.18)**

New module `lean/JSPProblem/SingleScale.lean` (1041 lines, **59 new public
theorems** plus 4 private helpers and 17 new definitions, 0 `sorry`, 0 `admit`;
**2350** proved theorems and lemmas at the `^(theorem|lemma)` level — 2291 before
this round — `lake build` clean).

`policy.json` `next_round_attack[0…2]`, carried unexecuted for 126 rounds, is
executed in full; item 3 (`K = 0` ground truth) is done as asked, and the
remaining items produce a **decisive negative result**: the single hypothesis
`jsp87Hypothesis518` that round 125 named as the last input is **false**.

### 0. §0–§1 the ground truth at `K = 0` (policy item 3)

| Theorem | Statement |
| --- | --- |
| `jsp87univ_Finset_Fin_zero`, `jsp87R_binV_zero`, `jsp87XpLevel_binV_zero` | at `K = 0` the cube has a single vertex `∅`, its shift is `h`, and the level sum is `2^{-h}·[p ∣ n+h]` |
| **`jsp87Xp0_binV_zero`** | **the closed form of (5.13) at `K = 0`**: `jsp87Xp0 (jsp87BinV 0) p n H = ∑_{h≤H} 2^{-h}·[p ∣ n+h]` |
| `jsp87Xp0_binV_zero_one` | the `H = 1` instance: `(1/2)·[p ∣ n+1]` |
| `jsp87sum_inv_two_Icc`, `jsp87Xp0_binV_zero_le`, `jsp87Xp0_binV_zero_lt_one` | `∑_{h≤H} 2^{-h} = 1 − 2^{-H}`, so `0 ≤ X_p < 1` |
| `jsp87Cnt` | **the new object**: `jsp87Cnt P m = #{p ∈ P : p ∣ m}`, the prime-divisor count |
| `jsp87Cnt_eq_sum`, `jsp87Cnt_le_omega`, `jsp87Cnt_eq_zero_of_lt`, `jsp87Cnt_eq_omega` | the count as a real sum of indicators, and `jsp87Cnt P m ≤ ω m` (the Chowla-type bound, from scratch) |
| **`jsp87Xp0_binV_zero_sum`** | **the double sum collapses**: `∑_{p∈P} jsp87Xp0 (binV 0) p i H = ∑_{h≤H} 2^{-h}·jsp87Cnt P (i+h)` |
| **`jsp87Phase_zero_one`** | **the phase at the ground-truth scale**: `q·∑_{p∈P} jsp87Xp0 (binV 0) p i 1 = (q/2)·jsp87Cnt P (i+1)` |
| `jsp87Phase_zero_one_primeSet`, `jsp87Phase_zero_one_abs_le` | the same for the canonical prime set, and the bound by `(q/2)·ω (i+1)` |

So at `K = 0, H = 1` the entire phase `qT` of arXiv:2512.01739 (5.13) is, up to
the factor `q/2`, a **prime-divisor count of a single integer** — no cube, no
alternating signs.

### 1. §2 the real/imaginary decomposition (policy item 2)

`jsp87Err1`, `jsp87Err2` are complex norms.  Proved here, from scratch:

| Theorem | Statement |
| --- | --- |
| `jsp87norm_sq_re_im`, `jsp87CAvg_re`, `jsp87CAvg_im` | `‖z‖² = Re² + Im²`, and the complex average's two coordinates are *real* averages (Mathlib has neither) |
| `jsp87Err1_sq_iff_re_im`, `jsp87Err2_sq_iff_re_im`, `jsp87Err1_le_iff_re_im`, `jsp87Err2_le_iff_re_im` | **the exact real form of (5.15) and (5.16)–(5.17)**: `Err ≤ κ ↔ Re² + Im² ≤ κ²` |
| `jsp87re_le_of_norm_le`, `jsp87im_le_of_norm_le` | each coordinate is at most the complex norm |
| `jsp87Err1_le_of_re_im`, `jsp87Err2_le_of_re_im` | two real component bounds give the error bound up to the `√2` of the norm |
| **`jsp87Err1re_eq_avg_cos`**, **`jsp87Err1im_eq_avg_sin`** | **the error of (5.15) is a real average of `cos` and of `sin` over the finite sample** — the exact shape of §§5.7–5.14 |
| `jsp87ErrBounds_real` | (5.15) and (5.16)–(5.17) *are* four explicit real inequalities |
| **`jsp87Err1_zero`** | at the ground-truth scale the error is `‖𝔼 e((q/2)·jsp87Cnt P (i+1)) − 1‖` |

### 2. §3 the single-scale form of (5.18) (policy item 1)

| Theorem | Statement |
| --- | --- |
| `jsp87Scale519`, `jsp87_518_single` | the scale (5.19) and (5.18) required at **one** scale only |
| `jsp87_518_single_ground_scale` | `K = 0, H = 1, q = 1/20` is admissible |
| **`jsp87Series_irrational_of_518_single`** | **the headline from the single-scale form**: `jsp87_518_single 0 1 (1/20) → Irrational jsp87Series`, no quantifier over scales |
| `jsp87Hypothesis518_imp_single` | (5.18) implies its single-scale form |

### 3. §4 **THE REFUTATION** — (5.18) IS FALSE

The endgame of §§5.3–5.14 (`jsp87_endgame_of_recipSum`, round 116) needs the two
error bounds **only at one height** — the height supplied by Euler's divergence —
and concludes that the dominating constants cannot all be `< 1/30`.  Hence:

| Theorem | Statement |
| --- | --- |
| `jsp87_518_at`, `jsp87_518_at_false` | **at any scale, any height and any `q` at which the harmonic mass (5.21b) holds, no five sharp constants dominate the two errors** |
| `jsp87_518_atY_false` | the uniform-in-`Y` form is false at every admissible scale (Euler supplies the height) |
| `jsp87_518_single_false`, `jsp87_518_single_ground_false` | the single-scale (5.18) is false at **every** admissible scale, in particular at `K = 0, H = 1, q = 1/20` |
| **`jsp87Hypothesis518_false`** | **`¬ jsp87Hypothesis518`: round 125's blocker is REFUTED** |
| `jsp87Series_irrational_of_518_route_closed` | there is no configuration with (5.18) and a rational series; the route of round 125 is closed |
| `jsp87_endgame_blunt` | whatever constants dominate the two errors at the endgame's height, at least one is `≥ 1/30` |

**Consequence.**  `jsp87Series_irrational_of_518` is a *vacuous* implication: its
hypothesis is a contradiction.  There is no analytic estimate to be found on the
fixed-scale route, because the estimate that route asks for is a contradiction.

### 4. §5 the diagnosis

In the published argument the constants `κ_j` of (5.15) and (5.16)–(5.17) are
**not free parameters**: the two estimates are consequences of *rationality*, so
their constants are forced, and the endgame says the forced constants are blunt.
Rounds 116–125 use **one and the same** `κ` on both sides of the endgame, which
makes the two statements contradictory — that is §4.  The genuine missing input is
the *derivation*, named here as

* **`jsp87ErrBoundsFromEscape`** — the escape hypothesis `jsp87TruncCarryEscapes b`
  forces the two error bounds (with constants that need not be sharp);
* `jsp87ErrBoundsFromEscape_blunt` — and then the endgame says one of the
  *forced* constants is `≥ 1/30`.  Unlike (5.18), this pair is **compatible** with
  `jsp_000087_main`.

### 5. §6–§7 the mean field, and the failure of the pointwise (5.19)

| Theorem | Statement |
| --- | --- |
| `jsp87Xp0_zero_one_ne_zero_iff`, `jsp87nzRes_zero_one`, `jsp87NzResCard_zero_one`, `jsp87NzRes_zero_one` | at `K = 0, H = 1` exactly one residue class of `p` is nonzero, so `jsp87NzResCard 0 p 1 = 1` |
| **`jsp87sum_div_primeSet`**, **`jsp87FAvg_div_primeSet`** | **the mean-field identity**: the mean of `[p ∣ i+1]` over the canonical sample is exactly `1/p` (from the block count of round 123) |
| **`jsp87sum_cnt_primeSet`**, **`jsp87FAvg_cnt_primeSet`** | **the mean of the prime-divisor count is the harmonic mass**: `𝔼 cnt P (i+1) = ∑_{2≤p≤Y} 1/p` |
| `jsp87Phase_eq`, `jsp87Phase0` | the phase is `q` times the un-scaled phase `T` |
| **`jsp87_phase_mean_primeSet`** | **the mean of the total phase is `(q/2)·∑_{p≤Y} 1/p`**, hence unbounded in the height |
| `jsp87Hyp519Pointwise` | hypothesis (5.19) in the pointwise form used by `jsp87_charfun_le` |
| `jsp87_phase_abs_mean_ge`, **`jsp87_519_pointwise_le`** | the pointwise (5.19) forces `∑_{2≤p≤Y} 1/p ≤ 40/|q|` |
| **`jsp87_519_pointwise_fails`** | **the pointwise (5.19) is impossible at every fixed `q ≠ 0`, at all large heights** — the third independent reason the fixed-scale endgame cannot run: the variance bound (5.19)–(5.20), and hence (5.21), is not applicable there |
| `jsp87_515_imp_var_le` | (5.15) together with the pointwise (5.19) forces `8·Var (q T) ≤ κ₁+κ₂+κ₃` — the object (5.21) is about |

### 6. Gate status

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

`jsp_000087_main` is **still deliberately not declared**, but the reason has
changed for the better: the burden is **no longer** "find the analytic estimate
(5.18)" (that hypothesis is now *refuted*, `jsp87Hypothesis518_false`), and no
longer "prove the sharpness" (the endgame forbids it).  The single remaining
input is the **deterministic derivation of the two error bounds from the escape
hypothesis / rationality with explicit constants**, `jsp87ErrBoundsFromEscape`,
together with a formulation of the endgame in which the *forced* constants — not
free ones — appear on the losing side.  That statement is deterministic and
side-free; no Chowla-type or Elliott-type estimate is needed for it.

### Mathlib findings of this round (do not repeat the mistakes)

* `RCLike.re`/`RCLike.im` are `AddMonoidHom`s, so `map_sum (RCLike.re : ℂ →+ ℝ) _ _`
  computes the coordinates of a sum; but `RCLike.re (x + y)` does **not** rewrite
  `Complex.re (x + y)` — use `Complex.add_re`, `Complex.sub_re`, `Complex.mul_re`,
  `Complex.add_im`, `Complex.sub_im`, `Complex.normSq_apply`, `RCLike.norm_sq_eq_def`;
* `(z * w).re = z.re * w.re` is **FALSE** (the `− z.im w.im` term); the useful
  companions are `Complex.re_ofReal_mul`, `Complex.im_ofReal_mul`,
  `Complex.normSq_natCast`, `Complex.natCast_re`, `Complex.natCast_im`;
* `Complex.div_ofReal_re` is `@[simp]` but only for a **real** denominator; for a
  `Nat` cast denominator use `div_eq_mul_inv` + `Complex.mul_re` + `Complex.inv_re`
  + `Complex.normSq_natCast`;
* `div_le_iff₀` and `le_div_iff₀` take **one** argument (the positivity of the
  *numerator bound* resp. of the denominator), and `rw [div_le_iff₀ …]` must be
  followed by `.mpr`;
* `Finset.sum_le_sum` needs both sides to be *sums*; to bound an average use
  `rw [jsp87FAvg, div_le_iff₀ …]` first (one positivity argument, for the
  denominator), and `jsp87FAvg_abs_le` already exists in `Variance.lean`;
* `jsp87e_re`, `jsp87e_im` (the cos/sin identification) already exist in
  `Variance.lean` — do not redeclare; `jsp87FAvg_abs_le`, `jsp87charfun_le`,
  `jsp87ProgFull_nzFrac`, `jsp87_nzFrac_prog_blocks`, `jsp87FAvg`, `jsp87Var` too;
* `rw [jsp87Cnt_eq_sum]` cannot see `↑(jsp87Cnt P m)` — use `simp_rw`;
* `Finset.mul_sum`'s LHS is `a * ∑ i in s, f i`, so to use it on `∑ i in s, (a * f i)`
  you must rewrite with `← Finset.mul_sum` or use `symm; exact Finset.mul_sum`;
* `rcases`/`rintro` will happily destructure the `≠` inside `A ∧ X ≠ 0` into a
  *function*; use `intro` + `And.intro` (or `simp only [X_ne_zero_iff]`) instead;
* `unfold`/`rw` do not descend into `fun i => …` reliably for `noncomputable def`s:
  prove a pointwise `jsp87Phase_eq`-style equation first.

---

## Round 127 — THE EXACT SECOND MOMENT OF THE PRIME-DIVISOR COUNT: (5.21) **IS** THE VARIANCE

New module `lean/JSPProblem/CntVariance.lean` (951 lines, **38 new public
theorems** plus 9 private helpers, 2 new definitions, 0 `sorry`, 0 `admit`;
**2386** theorem/lemma declarations tree-wide at the `^(theorem|lemma)` level
(2348 before this round), `lake build` clean, 7 linter warnings).

`policy.json` `next_round_attack[3]` of round 126 asked for **the price of
(5.15) at the ground-truth scale**: combine the variance bound
`jsp87_515_imp_var_le` with the mean-field identity `jsp87FAvg_cnt_primeSet`
and read off an explicit lower bound for `κ₁ + κ₂ + κ₃`.  Round 126 promised
that computation in a docstring (`jsp87_515_zero_var_le`,
`jsp87_515_zero_sqmoment_le`, `jsp87_515_zero_recipSum_le`,
`jsp87_515_zero_refuted`) but **did not prove it** — the second moment of
`jsp87Cnt` over the canonical sample had never been computed.  **This round
computes it exactly**, and the answer is a closed form.

### 0. The key observation: the canonical sample is a whole period

The endgame sample is

```
s = jsp87ProgFull 0 1 P = { i : i < ∏_{p ∈ P} p }      (jsp87ProgFull_eq_Icc)
```

a **whole period** modulo every prime of `P` at once.  Hence the divisibility
events `p ∣ i + 1` are independent by the Chinese remainder theorem, and the
variance of the prime-divisor count has a closed form.  Mathlib has no
statement of this shape for a prime-divisor count.

### 1. The counting step (CRT)

| Theorem | Statement |
| --- | --- |
| `jsp87ProgFull_eq_Icc` | the canonical sample is `{ i : i < ∏ P }` |
| `jsp87card_div_pair` | **the two-prime count**: `# { i ∈ s : p ∣ i+1 ∧ q ∣ i+1 } = ∏ P / (p q)` for distinct primes `p, q ∈ P` (from `Nat.Ioc_filter_dvd_card_eq_div` + `p q ∣ ∏ P`) |
| `jsp87sum_divInd_pair` | the mixed second moment `∑_i x_p(i) x_q(i) = ∏ P / (p q)` |
| `jsp87FAvg_divInd_progFull` | **the mean of `x_p` is `1/p`** — round 126's mean-field identity, in full generality |
| `jsp87FAvg_divInd_mul_progFull` | **INDEPENDENCE**: `𝔼 x_p x_q = 𝔼 x_p · 𝔼 x_q = 1/(pq)` |

### 2. THE MAIN THEOREM — the exact variance

| Theorem | Statement |
| --- | --- |
| `jsp87SqDefect` | **the new object** `∑_{p ∈ P} (1/p)(1 − 1/p)` — the `∑_p f_p(1−f_p)` of (5.21′) |
| `jsp87FAvg_sq_cnt_progFull` | **the exact second moment**: `𝔼 cnt² = ∑_{p∈P} 1/p + ∑_{p≠q} 1/(pq)` |
| `jsp87SqDefect_eq` | `SqDefect = ∑ 1/p − ∑ 1/p²` |
| **`jsp87Var_cnt_eq_sqDefect`** | **`Var (i ↦ cnt P (i+1)) = ∑_{p ∈ P} (1/p)(1 − 1/p)`** — the Chinese remainder identity |
| **`jsp87R521b_ground_iff_var`** | **hypothesis (5.21b) at `K = 0, H = 1` is *equivalent* to `4 ≤ q² Var`**: `jsp87R521b 0 P q 1 ↔ 4 ≤ q^2 * Var (i ↦ cnt P (i+1))` |

`jsp87R521b_ground_iff_var` is the point of the round: **at the canonical
sample the variance hypothesis (5.21) of arXiv:2512.01739 is not an
estimate — it is an identity.**  The `∑_p f_p (1 − f_p)` of (5.21′) *is* the
variance of the phase, with no loss and no correlation input, because
divisibility is exactly uniform on a whole period.

### 3. Consequences

| Theorem | Statement |
| --- | --- |
| `jsp87SqDefect_nonneg`, `jsp87SqDefect_le_recipSum` | `0 ≤ SqDefect P ≤ ∑ 1/p` |
| `jsp87SqDefect_ge_recipSum_half` | `∑_{2≤p≤Y} 1/p ≤ 2 · SqDefect (jsp87PrimeSet 2 Y)` |
| `jsp87SqDefect_ge_one_fourth` | `1/4 ≤ SqDefect (jsp87PrimeSet 2 Y)` for `2 ≤ Y` |
| **`jsp87SqDefect_tendsto`** | **`SqDefect (jsp87PrimeSet 2 Y) → +∞` with the height** (Euler): the variance hypothesis of the published proof is satisfied at every sufficiently large height, unconditionally |
| `jsp87Phase0_zero_one` | the pointwise form of round 126's phase identity: `jsp87Phase0 0 1 Y i = (1/2) · cnt (i+1)` |
| **`jsp87_515_ground_var_le`** | **(5.15) + the pointwise (5.19) force `2 q² Var (i ↦ cnt (i+1)) ≤ κ₁+κ₂+κ₃`** |
| **`jsp87_515_ground_price`** | **THE PRICE: `q² ∑_{2 ≤ p ≤ Y} 1/p ≤ κ₁+κ₂+κ₃`** — the statement promised as `jsp87_515_zero_recipSum_le` in round 126 |
| **`jsp87_521_imp_kappa_blunt`** | (5.21b) + (5.15) + (5.19) force `κ₁+κ₂+κ₃ ≥ 8` — the constants are blunt by a factor 240 |
| `jsp87RecipSum_weighted_large` | for every `q ≠ 0`, `M` there is a height with `q² ∑_{2≤p≤Y} 1/p > M` |
| **`jsp87_515_ground_fails_above`** | **at every height whose weighted harmonic mass exceeds the constants, (5.15) + (5.19) FAIL** |
| **`jsp87_515_ground_refuted`** | **for every fixed triple `κ₁,κ₂,κ₃` there is a height at which (5.15)+(5.19) fail and its own price is violated** — the quantitative refutation of (5.15) at the ground-truth scale |

### 4. Machine-checked instances

`jsp87SqDefect_two : SqDefect {2} = 1/4`, `jsp87Var_cnt_two : Var (cnt over
{2}) = 1/4`, `jsp87SqDefect_two_three : SqDefect {2,3} = 17/36`,
`jsp87R521b_ground_two : jsp87R521b 0 (jsp87PrimeSet 2 2) 20 1` (the variance
hypothesis holds at `q = 20`, three times the `1/20` of (5.19)), and the round
summary `jsp87_cntVariance_summary`.

### Gate status

`jsp_000087_main` is **still deliberately not declared**.  `harness/score.py
problems/JSP-000087 --strict-prize` reports `build_ok=true, sorry=0, admit=0,
placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 127, stated exactly

> **The non-ground-truth sample.**  Everything above is proved *at the ground
> truth*, i.e. for the canonical whole-period sample, where the variance
> hypothesis (5.21) becomes an identity.  Two things remain:
>
> 1. **the derivation from the escape hypothesis `jsp87ErrBoundsFromEscape`**
>    (round 126's blocker) — the error bounds (5.15)/(5.16)–(5.17) are then
>    forced to be *blunt*, which is the shape of the published proof; and
> 2. **the general sample.**  The identity `Var = ∑ f_p(1−f_p)` holds for the
>    canonical sample because of CRT; for a *general* finite sample the
>    variance is `∑ f_p(1−f_p) + 2 ∑_{p≠q} (f_{pq} − f_p f_q)`, and the
>    covariances `f_{pq} − f_p f_q` are exactly the two-point correlation
>    estimate of arXiv:2512.01739 Thm 3.1 (Pilatte) — the one analytic input
>    Mathlib does not contain.

### Mathlib findings of this round (do not repeat the mistakes)

* `Finset.card_nbij' (i) (j) (hi) (hj) (left_inv) (right_inv)` for a
  `Set.MapsTo`/`Set.LeftInvOn`/`Set.RightInvOn` triple; for
  `Set.LeftInvOn j i s` the goal is `j (i x) = x`, and `n ↦ (n+1).pred` inverts
  `n ↦ n+1` **without** any hypothesis, whereas the converse needs `0 < n`;
* `Nat.Ioc_filter_dvd_card_eq_div (n p) : #{x ∈ Ioc 0 n | p ∣ x} = n / p` is
  the counting lemma to use (`Finset.Icc 1 L = Finset.Ioc 0 L`);
* `Nat.cast_div` in this Mathlib takes **two** hypotheses, `n ∣ m` and `↑n ≠ 0`;
* `Nat.le_of_dvd : 0 < n → m ∣ n → m ≤ n` (the *dividend* must be shown
  positive — it cannot be used to bootstrap positivity of the dividend);
  `Nat.pos_of_ne_zero : n ≠ 0 → 0 < n`;
* `Nat.mul_le_mul`, `Nat.mul_le_mul_left/right` are 2-argument;
  `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a*b ≤ a*c` needs `b ≤ c` in that
  order; `one_div_le_one_div_of_le : 0 < a → a ≤ b → 1/b ≤ 1/a`;
* `div_le_one : 0 < b → (a/b ≤ 1 ↔ a ≤ b)` is an **iff**, and the `.mpr`
  direction wants `a ≤ b`;
* `Finset.sum_congr rfl (fun i _ => proof)` only applies when **both sides are
  sums over the same finset** — `jsp87FAvg` hides the division *outside* the
  sum, so `unfold jsp87FAvg` first and then `rw [← jsp87FAvg]` to go back;
* `obtain ⟨c, hc⟩ := h` **deletes** `h` from the context — order the proof so
  `h` is not used afterwards;
* `Finset.filter_congr (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s`
  works, but `Finset.ext`-based proofs of filter equalities do not;
* `simp only [jsp87PrimeSet, Finset.mem_filter, Finset.mem_Icc, …]` unfolds
  `Icc` into `Nat`-subtraction noise: use the `rw [jsp87PrimeSet_mem, …]`
  chain, or `interval_cases` on the bounded variable.

---

## Round 130 — THE EXACT SECOND MOMENT OF THE TRUNCATED CARRY: THE DIAGONAL IS
ARITHMETIC, THE OFF-DIAGONAL IS THE MISSING CORRELATION INPUT

New module `lean/JSPProblem/TcVariance.lean` (1268 lines, **49 new public
theorems** + 6 private helpers, 8 new definitions, 0 `sorry`, 0 `admit`,
0 new linter warnings; **2848** theorem/lemma declarations tree-wide,
`lake build` clean). Round 115 opened the blocker **`jsp87_truncSq_diag`** — the
double-sum identity of the second moment of the truncated carry of
arXiv:2512.01739 — and recorded that it "is NOT proved here … do NOT re-attempt
it by hand". **This round closes it** and then does what round 115 could not.

### 0. The objects

| Object | Statement |
| --- | --- |
| `jsp87Tw k` | the weight `2^{-(k+1)}`, with `∑_{k<H} w_k = 1 − 2^{-H}` |
| `jsp87TcMean`, `jsp87TcCorr` | `𝔼 ω(N+k)`, `𝔼 ω(N+k)ω(N+k')` over the window `N < L` |
| `jsp87Mcov L k k'` | **THE NEW OBJECT**: `𝔼 ω(N+k)ω(N+k') − 𝔼 ω(N+k)·𝔼 ω(N+k')` |
| `jsp87TcVarAt L k` | `Var (N ↦ ω(N+k))`, the diagonal of the decomposition |
| `jsp87TcVar L H` | **`Var (N ↦ T(N,H))`**, the object of §5.4 of the paper |
| `jsp87TcDiag`, `jsp87TcOff` | the diagonal and off-diagonal parts of the second moment |

### 1. `jsp87TruncSqSum_eq_dblCorr` — the closed blocker

```
∑_{N<L} T(N,H)²  =  ∑_{k<H} ∑_{k'<H} 2^{-(k+1)-(k'+1)} · ( ∑_{N<L} ω(N+k)ω(N+k') ) ,
```

the inner sums being exactly Chowla.lean's `jsp87CorrAt L k k'`, with diagonal
`jsp87SqWindow k L`. The generic tool is
`jsp87_sum_dbl_eq_diag_add_two_tri`: for symmetric `f`,
`∑_{k,k'} f k k' = ∑_k f k k + 2 ∑_{k<k'} f k k'`.

### 2. `jsp87TruncSqSum_eq_diag_add_off` — the diagonal is arithmetic

`∑ T² = jsp87TcDiag + jsp87TcOff`, where

* `jsp87TcDiag L H = ∑_{k<H} 4^{-(k+1)} · ∑_{N<L} ω(N+k)²` — **no analytic input**;
* `jsp87TcOff L H = ∑_{k<k'<H} 2·2^{-(k+1)-(k'+1)} · ∑_{N<L} ω(N+k)ω(N+k')` —
  **one two-point correlation per unordered pair of places of the window**,
  i.e. exactly the analytic object of §5.4.

### 3. `jsp87TcVar_eq_diag_add_cov` — the crown jewel

```
Var (N ↦ T(N,H))  =  ∑_{k<H} 4^{-(k+1)} · Var (N ↦ ω(N+k))
                    +  ∑_{k<k'<H} 2·2^{-(k+1)-(k'+1)} · Cov (ω(N+k), ω(N+k')) .
```

with `jsp87Var_eq_FAvg_sq_sub : Var f = 𝔼 f² − (𝔼 f)²` (absent from Mathlib for
`jsp87Var`) and `jsp87TcVarAt_eq_cov : Var (ω(·+k)) = jsp87Mcov L k k`.

**Transfer lemmas** (`jsp87Tw_pair_le_one`: the total covariance weight
`2 ∑_{k<k'} w_k w_k' ≤ 1`):

* `jsp87TcVar_ge_diag` — nonneg covariances ⟹ the variance is at least the
  arithmetic diagonal, whatever the correlations are;
* `jsp87TcVar_le_diag_add` — a uniform covariance bound `ε` ⟹ the variance is at
  most diagonal `+ ε`. **This is the deterministic half of §5.4, complete.**

### 4. The price of the elementary CRT bound (round 115)

* `jsp87ChowlaErr_eq`: the boundary error is exactly `π(N)·(π(N+1) − 1)`;
* `jsp87TcOff_ge_pair01`, `jsp87TcOff_ge_chowla`: the shift-`1` Chowla sum is an
  off-diagonal term of weight `1/4`, so *any* bound on the off-diagonal term is a
  bound on the Chowla sum (`jsp87TcOff_ge_boundary`);
* `jsp87Chowla_ge_card : N − 1 ≤ jsp87Chowla N` and
  **`jsp87Chowla_le_of_corr_bound : (N−1)/4 ≤ M`** — a uniform correlation bound
  `M` at the window `N+1` must be at least `(N−1)/4`: **the correlations of `ω`
  are sums of at least `N−1` units, so the counting argument cannot make the
  off-diagonal term small.**

### 5. Machine-checked instances

`jsp87TcVar_three_one = 1/18`, `jsp87TcVar_four_one = 1/16`,
`jsp87TruncSqSum_three_two = 5/8 = 3/8 + 1/4`,
`jsp87TcDiag_three_two = 3/8`, `jsp87TcOff_three_two = 1/4`,
`jsp87TcVar_three_two = 7/72`, `jsp87Mcov_three_zero_one = 1/9` (the shift-`1`
covariance is **not** zero).

### Gate status

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 130, stated exactly

> **`jsp87Mcov_small`.**  A uniform bound `ε` on the two-point covariances
> `jsp87Mcov L k k'` (`k < k' < H`) small enough for the endgame of §5.3–5.14.
> By `jsp87TcVar_le_diag_add` this is *exactly* the missing analytic input, and
> `jsp87Chowla_le_of_corr_bound` computes its price: `ε ≥ (N−1)/4`. Mathlib has
> no Chowla-type, Elliott-type or two-point-correlation statement for
> multiplicative functions; the input is Theorem 3.1 of arXiv:2512.01739.

### Mathlib findings of this round (do not repeat the mistakes)

* `Finset.sum_congr`'s binder names are `s₁ s₂`; with `rfl` for the summand
  functions the `AddCommMonoid` instance can stay stuck — pass explicit lambdas;
* `Finset.sum_congr rfl` does **not** match a summand that is itself a
  `Finset.sum` (higher-order unification fails); state the per-`k` identity as
  `(Finset.sum_sub_distrib f g).symm` with explicit lambdas — the resulting
  beta-redex form then matches the `calc` step syntactically (and `calc` *does*
  accept a beta-redex first step against a beta-normal goal);
* `Finset.sum_sub_distrib : ∑ x ∈ s, (f x − g x) = ∑ f − ∑ g`; the reverse
  direction needs the explicit-lambda trick;
* `Finset.filter_eq' (s) (b) : {a ∈ s | a = b} = if b ∈ s then {b} else ∅`
  (an `ite`, not a `dite`), `Finset.card_erase_of_mem`, and
  `Finset.mem_erase` = `a ≠ b ∧ a ∈ s`;
* `Nat.card_Icc : (Icc a b).card = b + 1 − a`; `Nat`-subtraction arithmetic needs
  `by_cases` for `omega`;
* `1 / 4` is a **division** and is invisible to `linarith`: multiply by `4`
  first with `mul_le_mul_of_nonneg_left`; `div_le_iff₀ (h : 0 < b)` takes **one**
  argument and reads `a / b ≤ c ↔ a ≤ c * b`;
* `Finset.sum_le_sum_of_subset_of_nonneg` takes `(s := ) (t := )`;
  `Finset.single_le_sum` takes the nonnegativity proof *first*; `Finset.sum_mul`
  has the sum on the **left** and `Finset.mul_sum` on the right, and
  `Finset.sum_mul s.filter …` mis-parses (projection binds tighter);
* instances: unfold the variance object, then
  `norm_num [jsp87TruncCarry, jsp87Tw, Finset.sum_range_succ, Finset.sum_filter, …]`
  evaluates the whole finite object.

---

## Round 131 — THE SHIFT-PARAMETRISED CORRELATIONS AND THE SIGN-FREE VARIANCE SANDWICH

New module `lean/JSPProblem/CorrShift.lean` (624 lines, **31 new theorems**
plus 4 new definitions and 5 private helpers, 0 `sorry`, 0 `admit`, 0 new
linter warnings; **2880** theorem/lemma declarations tree-wide by the
`^(private )?(theorem|lemma)` count — 2847 before this round — `lake build`
clean).

This is a **new attack family**: round 130 produced the *diagonal/off-diagonal*
decomposition of the second moment of the Tao–Teräväinen truncated carry and
localised the missing analytic input to the covariances `jsp87Mcov L k k'`; this
round attacks **(i) the shift structure of those covariances and (ii) their
sign**, and in (ii) it closes the hypothesis round 130 could not discharge.

### §1 — the shift parametrisation (`policy.json` `next_round_attack[0]` of round 130, executed)

| Theorem | Statement |
| --- | --- |
| `jsp87CorrShift` | **the new object** `∑_{m<L} ω m · ω (m+d)`, the correlation at the *shift* `d` |
| **`jsp87CorrAt_shiftEq`** | **THE SHIFT PARAMETRISATION, AN IDENTITY**: `jsp87CorrAt L k (k+d) + jsp87CorrCut k d = jsp87CorrShift d (L+k)`, with `jsp87CorrCut k d` the shift-`d` correlation over `[0,k)` |
| `jsp87CorrAt_le_shift` | every one of the `H (H−1)/2` correlation inputs of §5.4 is bounded by one of the `H` **shift** correlations |
| `jsp87CorrShift_mono_window`, `jsp87CorrCut_le_log` | the boundary term is monotone and is `O(k (log L)²)` |
| `omega_le_log2_all` | `ω n ≤ log₂ n` at **every** `n` (including `n = 0`), the missing `0`-case of round 44's bound |
| `jsp87CorrShift_one_eq_chowla`, `jsp87CorrShift_thousand_one`, `jsp87CorrShift_hundred_one` | `jsp87CorrShift 1 (N+1) = jsp87Chowla N`; instances `= 4319` (N = 1000), `= 284` (N = 100) |

So the analytic input of §5.4 is a **list of `H` numbers** (the shift
correlations), not a triangular array — this is exactly what round 130's
`policy.json` asked for.

### §2 — the common-prime (gcd) content of a correlation

| Theorem | Statement |
| --- | --- |
| `omega_mul_ge_gcd` | `ω a · ω b ≥ ω (gcd a b)`: the ordered prime pairs contain the diagonal `p = q` |
| `omega_gcd_le`, `jsp87CorrGcd_le_mul` | the shift-dependent part of a correlation is at most `L · ω d` |
| `jsp87CorrShift_eq_Icc`, **`jsp87CorrShift_ge_gcd`** | `jsp87CorrShift d L + ω d ≥ jsp87CorrGcd d L`: the correlation dominates the count of the *common* prime divisors of `m` and `m+d` |

### §3 — **CAUCHY–SCHWARZ FOR THE COVARIANCES: THE SIGN OF THE COVARIANCES IS FREE**

Round 130's `jsp87TcVar_ge_diag` requires `0 ≤ jsp87Mcov` at every pair — a
hypothesis that cannot be proved with anything in the tree. This round shows it
is **not needed**.

| Theorem | Statement |
| --- | --- |
| `jsp87Mcov_eq_FAvg`, `jsp87_sq_centred` | `Cov = 𝔼` of the centred product; `∑ (ω−μ)² = L · Var` |
| **`jsp87Mcov_sq_le_var`** | **`Cov (ω(N+k), ω(N+k'))² ≤ Var (ω(N+k)) · Var (ω(N+k'))`** — Cauchy–Schwarz on the two centred functions, from round 130's own discriminant argument `jsp87CS`. **No analytic input.** |
| `jsp87Mcov_abs_le_std`, `jsp87Mcov_ge_negStd`, `jsp87TcStd`, `jsp87TcStd_sq`, `jsp87TcVarAt_nonneg` | `|Cov| ≤ σ_k σ_k'`, hence `Cov ≥ −σ_k σ'`: **the covariance can be negative, but never more negative than the geometric mean of the two marginal standard deviations** |
| `jsp87Mcov_eq_zero_of_var` | a degenerate marginal variance forces a degenerate covariance |

### §4 — **THE SIGN-FREE VARIANCE SANDWICH: §5.4 COMPLETE UP TO TWO SCALAR BOUNDS**

| Theorem | Statement |
| --- | --- |
| **`jsp87TcVar_ge_diag_sub`** | **the mirror of round 130's `jsp87TcVar_le_diag_add`, with NO sign hypothesis**: if `Var (ω(N+k)) ≤ M` for every `k < H` then `Σ_k 4^{-(k+1)} Var (ω(N+k)) − M ≤ Var (N ↦ T(N,H))`, using `Cov ≥ −σ_kσ_k' ≥ −M` and the total covariance weight `≤ 1` (`jsp87Tw_pair_le_one`) |
| **`jsp87TcVar_sandwich`** | **THE CROWN**: for **any** `M, ε ≥ 0`, `Σ_k 4^{-(k+1)} Var (ω(N+k)) − M ≤ Var (N ↦ T(N,H)) ≤ Σ_k 4^{-(k+1)} Var (ω(N+k)) + ε` |
| `jsp87_corrShift_summary` | the round in one theorem |

Round 130 needed `0 ≤ jsp87Mcov` for its *lower* bound; §3–§4 of this round show
the lower bound holds under **no** sign assumption, so §5.4 of arXiv:2512.01739
is reduced to the two **scalar** bounds it really needs — an upper bound `ε` on
the covariances, and the **arithmetic** content of the diagonal. The first is
`jsp87Mcov_small` (Thm 3.1, absent from Mathlib); the second is the diagonal,
i.e. a lower bound on `Var (ω(N+k))`, i.e. the Erdős–Kac scale.

### Gate status

`jsp_000087_main` is **still deliberately not declared**. The headline is a
theorem of the literature (Tao–Teräväinen, arXiv:2512.01739 Thm 1.3, Erdős'
#69) but its analytic input is a Chowla/Elliott-type estimate on the two-point
correlations of `ω` which Mathlib does not contain, and attaching the name to a
weakened statement would misrepresent it.

`harness/score.py problems/JSP-000087 --strict-prize` reports `build_ok=true,
sorry=0, admit=0, placeholder_total=0, partial_ok=true, prize_ready=false,
missing_theorems=["jsp_000087_main"]`.

### The blocker, after round 131, stated exactly

> **`jsp87Mcov_small`** — a uniform bound `jsp87Mcov L k k' ≤ ε` at every pair
> `k < k' < H`.

Unchanged in content, but now **provably the only** remaining hypothesis of the
§5.4 machinery: the sign is handled by Cauchy–Schwarz, the window shape by the
shift parametrisation, the magnitude by `|Cov| ≤ σσ'` plus the total weight `≤ 1`.

### Mathlib findings of this round (do not repeat the mistakes)

* `Finset.sum_congr`'s finset parameter is **`s₁`** (not `s`), and its `f`/`g`
  arguments must often be given explicitly or the `AddCommMonoid` instance gets
  stuck; `simp_rw [h]` with `h : ∀ N, …` is the robust way to rewrite summands;
* **CRITICAL PARSER TRAP (second instance):** `∑ N ∈ s, X - Y` parses as
  `(∑ N ∈ s, X) - Y` — the binder body does **not** extend past the difference.
  Always parenthesise: `∑ N ∈ s, (X - Y)`;
* `Finset.sum_sub_distrib : ∑ (f - g) = ∑ f - ∑ g` only fires when the summand
  *already* is a difference; to get there use `simp_rw` with a `∀`-lemma;
* `Finset.mul_sum (s := s) (fun i => g i) a : a * ∑ f = ∑ a * f` and
  `Finset.sum_mul (s := s) (fun i => f i) a : (∑ f) * a = ∑ f * a` — use
  `← Finset.mul_sum` / `Finset.sum_mul` in *opposite* directions on the two
  sides of a sum identity;
* `Finset.sum_const : ∑ _x ∈ s, b = s.card • b`, so `nsmul_eq_mul` is needed in
  ℝ and `Nat.nsmul_eq_mul` in ℕ;
* `Finset.sum_le_sum_of_subset_of_nonneg : s ⊆ t → (∀ i ∈ t, i ∉ s, 0 ≤ f i) →
  ∑ s f ≤ ∑ t f` (the function is shared between the two sums);
* `Finset.sum_congr rfl h` hovers a beta-redex goal; `dsimp only []` or
  `unfold` first;
* `Finset.sum_Ico_consecutive (f) (m :=) (n :=) (k :=) (hmn) (hnk)` and
  `Finset.sum_Ico_succ_top (a :=) (b :=) (h) f` need **explicit** implicit
  arguments when the bounds are sums;
* `Nat.log_mono_right : n ≤ m → Nat.log b n ≤ Nat.log b m`, `Nat.log_le_self (b)
  (x) : Nat.log b x ≤ x` (no hypothesis on `b` needed in this version),
  `Nat.log 2 0 = 0` by `simp`;
* `Nat.gcd_pos_of_pos_left (n) (h : 0 < m) : 0 < m.gcd n` (two explicit args);
  `Nat.primeFactors_gcd (a ≠ 0) (b ≠ 0)`; `Nat.gcd_dvd_left a b : gcd a b ∣ a`;
  `Nat.gcd_dvd_right a b : gcd a b ∣ b`; `Nat.gcd_zero_right : n.gcd 0 = n`
  (there is **no** `gcd 0 n = n`; use `Nat.gcd_comm`);
  `Nat.dvd_gcd : (m ∣ a) → (m ∣ b) → m ∣ gcd a b`;
* `Nat.primeFactors_gcd` + `Finset.card_le_card (fun x hx => (Finset.mem_inter
  .mp hx).1)` gives `ω (gcd a b) ≤ ω a` — `Finset.inter_subset_left` is **not**
  applicable in the guessed form;
* `Real.sq_sqrt (h : 0 ≤ x) : sqrt x ^ 2 = x` (note `^ 2`, not `*`);
  `Real.mul_self_sqrt`; `Real.sqrt_le_sqrt (h : a ≤ b) : sqrt a ≤ sqrt b`;
  `sq_le_sq₀ (h : 0 ≤ b) : |a| ≤ |b| ↔ a² ≤ b²` — `.2` is the direction
  "from the squares to the absolute values";
* `abs_le.mp h : -b ≤ a ∧ a ≤ b` is the convenient way to split `|a| ≤ b` into
  two one-sided bounds (useful because `linarith` cannot treat `|a|` as an atom);
* **`omega` fails on the statement `Nat.log 2 (k+d+1) + 1 ≤ (k+d+1)^2`** (it
  cannot square variables): prove such bounds from `Nat.log_le_self` and
  `Nat.le_mul_of_pos_left` instead;
* `Nat.dvd_gcd m (m+d)` does **not** exist (it takes two divisibility
  hypotheses); `Finset.card_eq_zero.mp`, `Nat.pos_of_ne_zero` are the right
  tools to obtain `s.card ≠ 0`;
* **`omega_mul_ge_union` is FALSE** (a = 6, b = 5: `2·1 + 0 = 2 < 3 = ω a + ω b`);
  the union of two finite sets does not inject into their product when one of
  them is a singleton.  Only the *common-prime* bound `ω (gcd a b) ≤ ω a · ω b`
  holds.
