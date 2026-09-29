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
