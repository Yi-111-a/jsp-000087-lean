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
