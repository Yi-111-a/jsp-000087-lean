# JSP-000087

**Is the generating series `∑ n ≥ 1, ω(n) / 2^n` irrational**, where `ω(n)` is the
number of *distinct* prime factors of `n`?

## Catalog record

- JSP identifier: **JSP-000087**
- Catalog index title: *Is the specified generating series involving the number of
  distinct prime factors of an integer irrational?*
- Mathematical area: Number theory / Irrationality
- Date proposed: no later than 1968 (bibliographic evidence)
- Current status (catalog): **Solved**; Lean proof: **No**; Eligible to claim: **No**
- Catalog source (per `acceptance.json` `catalog_url`):
  `https://github.com/TheJustinSunPrize/awards/blob/main/problems/README.md`,
  detail record `catalog-0001-0100.md#JSP-000087`

## References recorded in the catalog

- `[Er48]` P. Erdős, *On arithmetical properties of Lambert series*,
  J. Indian Math. Soc. (N.S.) **12** (1948), 63–66.
- `[Pr24]` K. Pratt, *The irrationality of a prime factor series under a prime
  tuples conjecture*, arXiv:2409.15185 (2024). Abstract: "Let `ω(n)` denote the
  number of distinct prime factors of `n`. Assuming a suitably uniform version of
  the prime `k`-tuples conjecture, we show that the number `∑_{n=1}^{∞} ω(n)/2^n`
  is irrational. This settles (conditionally) a question of Erdős."
- `[TaTe25]` *Quantitative correlations and some problems on prime factors of
  consecutive integers*, arXiv:2512.01739 (2025).

## Mathematical content

Because `ω(n) = #{p prime : p ∣ n}`, the generating series is the
prime-restricted Lambert series

```
∑_{n≥1} ω(n) x^n  =  ∑_{p prime} ∑_{k≥1} x^{pk}  =  ∑_{p prime} x^p / (1 - x^p),
```

and at `x = 1/2` this equals `∑_{p prime} 1/(2^p - 1)`.  Erdős (1948) proved
irrationality of the corresponding *unrestricted* Lambert series
`∑_{n≥1} 1/(2^n - 1)` and asked whether the prime-restricted variant is also
irrational.  Pratt (2024) answers this **conditionally**, under a uniform prime
`k`-tuples hypothesis.

Convergence is elementary: `2^{ω(n)} ≤ n` (the product of the distinct prime
factors divides `n`), hence `ω(n) ≤ log₂ n`, so `∑ ω(n)/2^n` converges.

## Status of this Lean formalization

See `ACCEPTANCE.md`.  `lean/JSPProblem/` contains a zero-sorry development of
the arithmetic core of `ω` and of the indicator-sum identity that is the first
step of the Lambert reduction.  The irrationality statement itself is a
research-level result and is **not** yet formalized.
