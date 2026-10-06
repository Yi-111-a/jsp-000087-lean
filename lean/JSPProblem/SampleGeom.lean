/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.ResidueBlock
import JSPProblem.SqMoment

/-!
# JSP-000087, round 143 — THE SAMPLE GEOMETRY AT GENERAL `N`: EXACT SUPPORT,
# SMALL SHIFTS, AND THE INITIAL SEGMENT IS *NOT* A CORRELATED SAMPLE

`policy.json` `next_round_attack[0]` of round 142, verbatim:

> "**RESIDUE-BLOCK SECTIONS 3–6** … (a) EXACT SUPPORT ON AN ARBITRARY FINITE
> SAMPLE … `jsp87NzRes_eq_filter`, `jsp87NzRes K p H s = s.filter (fun n =>
> p − (H + 2^K − 1) ≤ n % p)`; (b) THE SMALL-SHIFT REFORMULATION, `X_p n ≠ 0
> <-> exists j in Icc 1 (H + 2^K − 1), p ∣ n + j` …; (c) THE POLICY GUESS IS
> REFUTED …; (d) THE WHOLE-PERIOD SAMPLE IS EXACTLY UNIFORM …"

and `next_round_attack[1]`:

> "**CLOSE THE GAP BETWEEN THE CANONICAL AND THE CORRELATED SAMPLE.** …
> Is (5.15) still refutable for a sample of the form `{n : n ∈ [1, Y]}` (an
> initial segment), i.e. does the support bound survive truncation?"

**All four items are theorems, and they all point the same way: sample geometry
can never refute the endgame.**  Write `B := H + 2^K − 1` (the length of the
nonzero block) and `f_p (s) := jsp87NzFrac K p H s`.

## §1 the support on an ARBITRARY sample is an IDENTITY

* `jsp87NzRes_eq_filter` — `jsp87NzRes K p H s = s.filter (fun n => p − B ≤ n mod p)`,
  item (a), for **every** sample;
* `jsp87ZeroRes_eq_filter` — the complementary identity for the zero class;
* `jsp87NzFrac_eq_block_card` — `f_p` is a count of residues.

## §2 the SMALL-SHIFT reformulation — item (b)

* `jsp87dvd_shift_iff` — **`p ∣ n + j ↔ p − (n mod p) = j`** for `1 ≤ j < p`;
* `jsp87nz_iff_dvd_shift` — **`X_p n H ≠ 0 ↔ ∃ j ∈ Icc 1 B, p ∣ n + j`**, i.e.
  `X_p` is nonzero **iff `p` divides one of the `B` integers immediately above `n`**
  (iff some multiple of `p` lies in `(n, n + B]`);
* `jsp87shift_unique` — the shift is **unique**, so it is a bijection.

## §3 the counting layer over intervals

* `jsp87count_Icc_dvd (a b p)` — `# { n ∈ [a,b] : p ∣ n } = b/p − (a−1)/p`;
* `jsp87card_shift_dvd (p N j)` — the shift `n ↦ n + j` carries
  `# { n ∈ [1,N] : p ∣ n + j }` to `# { m ∈ [1+j, N+j] : p ∣ m }`;
* `jsp87count_shift_dvd` — since `j < p` the latter is exactly `⌊(N+j)/p⌋`.

## §4  ★★ THE MAIN THEOREMS OF THIS MODULE ★★

* `jsp87nzRes_Icc_biUnion`, `jsp87shiftClasses_disjoint` — the nonzero points of an
  initial segment are the **disjoint union**, over `j ∈ Icc 1 B`, of the shift
  classes `p ∣ n + j`;
* **`jsp87card_nzRes_Icc_eq_sum`** —
  **`# { n ∈ [1,N] : X_p n ≠ 0 } = Σ_{j ∈ Icc 1 B} ⌊(N+j)/p⌋`**, exactly, no error
  term and no analytic input;
* **`jsp87card_nzRes_Icc_mul`**, **`jsp87NzFrac_Icc_mul_eq`** — item (d): for `N = k p`
  the count is exactly `k B` and the fraction is exactly `B / p`;
* `jsp87card_nzRes_Icc_le`, `jsp87card_nzRes_Icc_ge` — the count bounds
  `B·(N/p) ≤ count ≤ B·((N+B)/p)`;
* **`jsp87NzFrac_Icc_bounds`** — **`B/p − B/N ≤ f_p ([1,N]) ≤ B/p + B/N`**: the
  residue-block support of round 142 **survives truncation**, quantitatively — the
  answer to `next_round_attack[1]`'s question;
* `jsp87NzFrac_Icc_close` — `|f_p − B/p| ≤ B/N`.

## §5  NEGATIVE KNOWLEDGE: (5.21′) IS GEOMETRY, NOT ANALYSIS

* `jsp87NzFrac_eq_one_of_block` — a sample lying entirely inside the block has
  `f_p = 1`;
* `jsp87NzFrac_eq_zero_of_out` — a sample lying entirely outside has `f_p = 0`,
  **so the policy's guess ("a small sample forces `f_p = 0`") is refuted**: `f_p = 1`
  is equally possible, and either way `f_p (1 − f_p) = 0`;
* **`jsp87_5_21_straddle`** — **hypothesis (5.21′) of arXiv:2512.01739 forces the
  sample to STRADDLE the block boundary for EVERY prime of `S₁`**, since it is a
  positive lower bound on a sum of nonnegative terms.

Together with round 141's `jsp87_endgame_515_realscale` (which refutes (5.15) on
the whole-period sample), this pins the failure of the endgame of §5 of
arXiv:2512.01739 on **estimate (5.15) and on nothing else**: the support shape,
the truncation and the sample size are all irrelevant to (5.21′).  The residual
input is unchanged: the Chowla-type two-point correlation `jsp87Mcov_small`.
See `ACCEPTANCE.md`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  ARITHMETIC TOOLS -/

/-- **THE ℕ→ℝ CAST OF A QUOTIENT IS AT MOST THE REAL QUOTIENT.**  Mathlib's
`Nat.cast_div` needs `p ∣ a`; only the *upper* bound is needed here, and it is
unconditional. -/
private lemma jsp87cast_div_le (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ a / b := by
  have h1 : (b : ℝ) * ((a / b : ℕ) : ℝ) + (a % b : ℕ) = a := by
    exact_mod_cast Nat.div_add_mod a b
  have h3 : (0 : ℝ) ≤ ((a % b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hid : a / b = ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) / b := by
    rw [← h1]
    field_simp
  calc ((a / b : ℕ) : ℝ) = ((a / b : ℕ) : ℝ) + 0 := by ring
    _ ≤ ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) / b := by
      have hn : (0 : ℝ) ≤ ((a % b : ℕ) : ℝ) / b := div_nonneg h3 (by positivity)
      linarith
    _ = a / b := by rw [hid]

/-- **THE CAST OF A DIVISION IS AT LEAST THE REAL DIVISION MINUS ONE.**  The
companion of `jsp87cast_div_le`, from `a % b < b`. -/
private lemma jsp87cast_div_ge_sub_one (a b : ℕ) (hb : 0 < b) :
    a / b - 1 ≤ ((a / b : ℕ) : ℝ) := by
  have h1 : (b : ℝ) * ((a / b : ℕ) : ℝ) + (a % b : ℕ) = a := by
    exact_mod_cast Nat.div_add_mod a b
  have h2 : (a % b : ℕ) < b := Nat.mod_lt a hb
  have h3 : (0 : ℝ) ≤ ((a % b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hid : a / b = ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) / b := by
    rw [← h1]
    field_simp
  have hle : ((a % b : ℕ) : ℝ) / b ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hb)]
    exact_mod_cast (Nat.le_of_lt h2)
  calc a / b - 1 = ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) / b - 1 := by rw [hid]
    _ ≤ ((a / b : ℕ) : ℝ) := by linarith

/-- **`2 ^ n ≥ 1` FOR EVERY `n`.**  Needed because `omega` cannot see through the
exponential. -/
private lemma jsp87pow_pos : ∀ n : ℕ, 1 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      nlinarith

/-- **THE ONLY MULTIPLE OF `p` IN `[1, 2p)` IS `p` ITSELF.**  The step of §2 that
`omega` will not do by itself, because it involves a variable divisor. -/
private lemma jsp87div_eq_p (a p : ℕ) (hp : 0 < p) (ha1 : 1 ≤ a) (ha2 : a < 2 * p)
    (hd : p ∣ a) : a = p := by
  obtain ⟨t, ht⟩ := hd
  have ht1 : 1 ≤ t := by
    by_contra hc
    have hz2 : a = 0 := by rw [ht, Nat.eq_zero_of_not_pos hc]; ring
    omega
  have hlt : p * t < p * 2 := by rw [← ht]; omega
  have ht2 : t < 2 := by
    have hlt' : t * p < 2 * p := by simpa [Nat.mul_comm] using hlt
    exact (Nat.mul_lt_mul_right hp).1 hlt'
  have ht3 : t = 1 := by omega
  rw [ht, ht3]
  ring

/-! ## §1  ★ THE SUPPORT ON AN ARBITRARY FINITE SAMPLE IS AN IDENTITY ★ -/

/-- **★ THE NONZERO CLASS OF THE SAMPLE IS EXACTLY THE RESIDUE FILTER ★**

```
jsp87NzRes K p H s  =  s.filter (fun n => p − (H + 2^K − 1) ≤ n mod p)
```

for **every** finite sample `s`.  This is `policy.json`
`next_round_attack[0](a)` of round 142 verbatim: the support is not bounded, it
is *computed*; `X_p` restricted to any sample is a **function of the residue
modulo `p` alone**, and its nonzero set is a block of residues. -/
theorem jsp87NzRes_eq_filter {K p H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (s : Finset ℕ) :
    jsp87NzRes K p H s = s.filter (fun n => p - (H + (2 ^ K - 1)) ≤ n % p) := by
  ext n
  constructor
  · intro hn
    rw [Finset.mem_filter] at hn
    have hn1 : n ∈ s := hn.1
    have hn2 : jsp87Xp0 (jsp87BinV K) p n H ≠ 0 := hn.2
    rw [Finset.mem_filter]
    exact ⟨hn1, (jsp87nz_iff_res_block hK hh hH n).mp hn2⟩
  · intro hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_filter]
    exact ⟨hn.1, (jsp87nz_iff_res_block hK hh hH n).mpr hn.2⟩

/-- **THE ZERO CLASS IS THE COMPLEMENTARY FILTER.** -/
theorem jsp87ZeroRes_eq_filter {K p H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (s : Finset ℕ) :
    jsp87ZeroRes K p H s = s.filter (fun n => n % p < p - (H + (2 ^ K - 1))) := by
  ext n
  constructor
  · intro hn
    have hn' := (Finset.mem_filter.mp hn)
    rw [Finset.mem_filter]
    by_cases hcon : p - (H + (2 ^ K - 1)) ≤ n % p
    · exact absurd hn'.2 ((jsp87nz_iff_res_block hK hh hH n).mpr hcon)
    · exact ⟨hn'.1, Nat.lt_of_not_ge hcon⟩
  · intro hn
    have hn' := (Finset.mem_filter.mp hn)
    rw [Finset.mem_filter]
    refine ⟨hn'.1, ?_⟩
    by_contra hcon
    exact (Nat.not_le.mpr hn'.2) ((jsp87nz_iff_res_block hK hh hH n).mp hcon)

/-- **THE NONZERO FRACTION IN BLOCK FORM.**  The fraction `f_p` is the fraction of
the sample whose residue lies in the block `[p − B, p − 1]`. -/
theorem jsp87NzFrac_eq_block_card {K p H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (s : Finset ℕ) :
    jsp87NzFrac K p H s = ((s.filter (fun n => p - (H + (2 ^ K - 1)) ≤ n % p)).card : ℕ)
      / ((s.card : ℕ) : ℝ) := by
  rw [jsp87NzFrac, jsp87NzRes_eq_filter hK hH hh s]

/-! ## §2  ★★ THE SMALL-SHIFT REFORMULATION ★★ -/

/-- **★★ `p ∣ n + j` IS THE SAME AS "THE RESIDUE OF `n` IS `p − j`" ★★**

For `0 < p` and `1 ≤ j < p`,

```
p ∣ n + j   ⟺   p − (n mod p) = j .
```

The right-hand side is the **depth** of the residue in the period, so the
nonzero block `p − B ≤ n mod p` is exactly "the depth is at most `B`", i.e.
"some multiple of `p` lies in `(n, n + B]`". -/
theorem jsp87dvd_shift_iff (p n j : ℕ) (hp : 0 < p) (hj1 : 1 ≤ j) (hjp : j < p) :
    p ∣ n + j ↔ p - (n % p) = j := by
  have hmod : n % p < p := Nat.mod_lt n hp
  constructor
  · intro h
    have hz : (n + j) % p = 0 := (Nat.dvd_iff_mod_eq_zero.mp h)
    have hadd : (n + j) % p = (n % p + j) % p := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hjp]
    rw [hadd] at hz
    have hlt2 : n % p + j < 2 * p := by omega
    have hsum : n % p + j = p :=
      jsp87div_eq_p (n % p + j) p hp (by omega) hlt2 (Nat.dvd_iff_mod_eq_zero.mpr hz)
    have hle : n % p ≤ p := Nat.le_of_lt hmod
    omega
  · intro h
    have hsum : n % p + j = p := by omega
    have hrem : n % p + p * (n / p) = n := Nat.mod_add_div n p
    refine ⟨n / p + 1, ?_⟩
    calc n + j = (n % p + p * (n / p)) + j := by rw [hrem]
      _ = p * (n / p) + (n % p + j) := by ring
      _ = p * (n / p + 1) := by rw [hsum]; ring

/-- **★★ THE CUBE SUM IS NONZERO IFF `p` DIVIDES ONE OF THE `B` INTEGERS
IMMEDIATELY ABOVE `n` ★★**

```
X_p (n) ≠ 0   ⟺   ∃ j ∈ Icc 1 B,  p ∣ n + j ,      B = H + 2^K − 1 .
```

`next_round_attack[0](b)` of round 142 verbatim: `X_p` is nonzero **iff `p`
divides one of the `H + 2^K − 1` integers immediately above `n`**, i.e. iff some
multiple of `p` lies in the window `(n, n + B]`. -/
theorem jsp87nz_iff_dvd_shift {K p H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (n : ℕ) :
    jsp87Xp0 (jsp87BinV K) p n H ≠ 0
      ↔ ∃ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), p ∣ n + j := by
  rw [jsp87nz_iff_res_block hK hh hH n]
  constructor
  · intro hmem
    have hp0 : 0 < p := by omega
    have hmod : n % p < p := Nat.mod_lt n hp0
    set j : ℕ := p - (n % p) with hjdef
    have hj1 : 1 ≤ j := by
      rw [hjdef]
      have := Nat.sub_pos_of_lt hmod
      omega
    have hjp : j < p := by rw [hjdef]; omega
    have hjle : j ≤ H + (2 ^ K - 1) := by rw [hjdef]; omega
    refine ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjle⟩, ?_⟩
    exact (jsp87dvd_shift_iff p n j hp0 hj1 hjp).mpr hjdef
  · rintro ⟨j, hj, hd⟩
    rw [Finset.mem_Icc] at hj
    have hp0 : 0 < p := by omega
    have hjp : j < p := by omega
    have hmod : n % p < p := Nat.mod_lt n hp0
    have hjval : p - (n % p) = j := (jsp87dvd_shift_iff p n j hp0 hj.1 hjp).mp hd
    have hsum : (n % p) + j = p := by omega
    omega

/-- **THE SHIFT IS UNIQUE.**  Because the block is shorter than the period, two
different shifts cannot both divide: the reformulation of §2 is a bijection
between the block and the divisors, not an existential. -/
theorem jsp87shift_unique {p n j j' : ℕ} (hp : 0 < p)
    (hj : 1 ≤ j) (hj' : 1 ≤ j') (hjB : j < p) (hjB' : j' < p)
    (hd : p ∣ n + j) (hd' : p ∣ n + j') : j = j' := by
  have h1 : p - (n % p) = j := (jsp87dvd_shift_iff p n j hp hj hjB).mp hd
  have h2 : p - (n % p) = j' := (jsp87dvd_shift_iff p n j' hp hj' hjB').mp hd'
  omega

/-! ## §3  THE COUNTING LAYER OVER INTERVALS -/

/-- **THE NUMBER OF MULTIPLES OF `p` IN `[a, b]` IS `b/p − (a−1)/p`.**  The
elementary counting lemma behind §4; the tree previously had only the
initial-segment case `a = 1` (`jsp87_card_Icc_dvd`). -/
theorem jsp87count_Icc_dvd (a b p : ℕ) (hab : 1 ≤ a) (h : a ≤ b) :
    (((Finset.Icc a b).filter (fun n => p ∣ n)).card : ℕ) = b / p - (a - 1) / p := by
  have hb1 : 1 ≤ b := by omega
  have h1 : ((Finset.Icc 1 b).filter (fun n => p ∣ n)).card = b / p :=
    jsp87_card_Icc_dvd b p hb1
  by_cases ha1 : a = 1
  · have hIc : Finset.Icc a b = Finset.Icc 1 b := by rw [ha1]
    rw [hIc, h1, ha1]
    simp
  · have ha2 : 2 ≤ a := by omega
    have hpos : 1 ≤ a - 1 := Nat.le_sub_of_add_le ha2
    have h3 : ((Finset.Icc 1 (a - 1)).filter (fun n => p ∣ n)).card = (a - 1) / p :=
      jsp87_card_Icc_dvd (a - 1) p hpos
    have hsub : (Finset.Icc 1 (a - 1)) ⊆ (Finset.Icc 1 b) := by
      intro x hx
      rw [Finset.mem_Icc] at hx ⊢
      omega
    have hle : ((Finset.Icc 1 (a - 1)).filter (fun n => p ∣ n)).card
        ≤ ((Finset.Icc 1 b).filter (fun n => p ∣ n)).card := by
      refine Finset.card_le_card ?_
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      have hxm : x ∈ Finset.Icc 1 (a - 1) := hx.1
      exact ⟨hsub hxm, hx.2⟩
    have hdisj : Disjoint ((Finset.Icc a b).filter (fun n => p ∣ n))
        ((Finset.Icc 1 (a - 1)).filter (fun n => p ∣ n)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      rw [Finset.mem_Icc] at hx1 hx2
      omega
    have hfil : ((Finset.Icc a b).filter (fun n => p ∣ n))
        ∪ ((Finset.Icc 1 (a - 1)).filter (fun n => p ∣ n))
        = (Finset.Icc 1 b).filter (fun n => p ∣ n) := by
      rw [← Finset.filter_union]
      ext x
      simp only [Finset.mem_filter]
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
      omega
    have hcard : ((Finset.Icc a b).filter (fun n => p ∣ n)).card
        = ((Finset.Icc 1 b).filter (fun n => p ∣ n)).card
          - ((Finset.Icc 1 (a - 1)).filter (fun n => p ∣ n)).card := by
      have hh := Finset.card_union_of_disjoint hdisj
      rw [hfil] at hh
      omega
    rw [hcard, h1, h3]

/-- **THE SHIFT CARRIES THE COUNT OF MULTIPLES.**  `n ↦ n + j` is a bijection from
`[1,N]` onto `[1+j, N+j]`, and it carries "`p ∣ n + j`" to "`p ∣ m`". -/
theorem jsp87card_shift_dvd (p N j : ℕ) (hj : 1 ≤ j) :
    (((Finset.Icc 1 N).filter (fun n => p ∣ n + j)).card : ℕ)
      = (((Finset.Icc (1 + j) (N + j)).filter (fun m => p ∣ m)).card : ℕ) := by
  classical
  have hinj : Function.Injective (fun n : ℕ => n + j) := by
    intro a b h
    have h' : a + j = b + j := h
    omega
  have key : ((Finset.Icc 1 N).filter (fun n => p ∣ n + j)).image (fun n : ℕ => n + j)
      = (Finset.Icc (1 + j) (N + j)).filter (fun m => p ∣ m) := by
    ext m
    constructor
    · intro hm
      obtain ⟨n, hn1, hn2⟩ := (Finset.mem_image.mp hm)
      rw [Finset.mem_filter] at hn1
      have hn1' := Finset.mem_Icc.mp hn1.1
      have hn2' : n + j = m := hn2
      clear hn2
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · show p ∣ m
        rw [← hn2']
        exact hn1.2
    · intro hm
      rw [Finset.mem_filter] at hm
      have hm' := Finset.mem_Icc.mp hm.1
      rw [Finset.mem_image]
      refine ⟨m - j, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · omega
        · omega
        · convert hm.2 using 1
          omega
      · show m - j + j = m
        omega
  rw [← key]
  exact (Finset.card_image_of_injective _ hinj).symm

/-- **THE COUNT OF MULTIPLES OF `p` AMONG `n + j` FOR `1 ≤ n ≤ N` IS EXACTLY
`⌊(N+j)/p⌋` WHEN `j < p`.** -/
theorem jsp87count_shift_dvd (p N j : ℕ) (hN : 1 ≤ N) (hj : 1 ≤ j) (hjp : j < p) :
    (((Finset.Icc 1 N).filter (fun n => p ∣ n + j)).card : ℕ) = (N + j) / p := by
  have h0 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le j) hjp
  have hle : 1 + j ≤ N + j := Nat.add_le_add_right hN j
  have h := jsp87count_Icc_dvd (1 + j) (N + j) p (by omega) (by omega)
  have hj0 : j / p = 0 := Nat.div_eq_of_lt hjp
  calc ((Finset.Icc 1 N).filter (fun n => p ∣ n + j)).card
      = ((Finset.Icc (1 + j) (N + j)).filter (fun m => p ∣ m)).card :=
        jsp87card_shift_dvd p N j hj
    _ = (N + j) / p - (1 + j - 1) / p := h
    _ = (N + j) / p := by
        have hsub : (1 + j - 1) / p = j / p := by rw [show 1 + j - 1 = j by omega]
        rw [hsub, hj0, Nat.sub_zero]

/-! ## §4  ★★ THE EXACT COUNT OVER AN INITIAL SEGMENT ★★ -/

/-- **★ THE NONZERO POINTS OF AN INITIAL SEGMENT ARE THE `B` DISJOINT SHIFT
CLASSES ★**

`next_round_attack[1]`'s question — *does the support bound survive
truncation?* — has the answer that the support of the initial segment is the
**disjoint union**, over `j ∈ Icc 1 B`, of the classes `p ∣ n + j`. -/
theorem jsp87nzRes_Icc_biUnion {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) :
    (Finset.Icc 1 N).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)
      = (Finset.Icc 1 (H + (2 ^ K - 1))).biUnion
          (fun j => (Finset.Icc 1 N).filter (fun n => p ∣ n + j)) := by
  classical
  ext n
  constructor
  · intro hn
    have hn' := (Finset.mem_filter.mp hn)
    rw [Finset.mem_biUnion]
    obtain ⟨j, hj, hd⟩ := (jsp87nz_iff_dvd_shift hK hH hh n).mp hn'.2
    refine ⟨j, hj, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hn'.1, hd⟩
  · intro hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨j, hj, hd⟩ := hn
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_filter]
    refine ⟨hd.1, ?_⟩
    exact (jsp87nz_iff_dvd_shift hK hH hh n).mpr (Exists.intro j ⟨hj, hd.2⟩)

/-- **THE SHIFT CLASSES ARE PAIRWISE DISJOINT.**  This is `jsp87shift_unique`
packaged as a `PairwiseDisjoint`, for every index set `L` inside the block. -/
theorem jsp87shiftClasses_disjoint {p N K H : ℕ} (hN : 1 ≤ N)
    (hBl : H + (2 ^ K - 1) + 1 ≤ p) (L : Finset ℕ)
    (hL : ∀ j ∈ L, 1 ≤ j ∧ j ≤ H + (2 ^ K - 1)) :
    Set.PairwiseDisjoint L
      (fun j => (Finset.Icc 1 N).filter (fun n => p ∣ n + j)) := by
  intro x hx y hy hne
  have hx' : 1 ≤ x ∧ x ≤ H + (2 ^ K - 1) := hL x hx
  have hy' : 1 ≤ y ∧ y ≤ H + (2 ^ K - 1) := hL y hy
  exact Finset.disjoint_left.2 (fun n hn1 hn2 => by
    rw [Finset.mem_filter] at hn1 hn2
    exact hne (jsp87shift_unique (by omega) hx'.1 hy'.1 (by omega) (by omega) hn1.2 hn2.2))

/-- **★★ THE EXACT COUNT OF NONZERO POINTS IN AN INITIAL SEGMENT ★★**

```
# { n ∈ [1,N] : X_p n ≠ 0 }  =  Σ_{j ∈ Icc 1 B} ⌊ (N + j) / p ⌋ ,   B = H + 2^K − 1 ,
```

an exact closed form, `⌊·⌋` by `⌊·⌋`, with **no error term and no analytic
input**.  This is the sharpening of round 141's counting bounds that
`next_round_attack[0](d)` asks for. -/
theorem jsp87card_nzRes_Icc_eq_sum {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) :
    (((Finset.Icc 1 N).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card : ℕ)
      = ∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p := by
  classical
  rw [jsp87nzRes_Icc_biUnion hK hH hh hN]
  have hdisj := jsp87shiftClasses_disjoint hN (by omega) (Finset.Icc 1 (H + (2 ^ K - 1)))
    (fun j hj => Finset.mem_Icc.mp hj)
  rw [Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  exact jsp87count_shift_dvd p N j hN hj.1 (by omega)

/-- **★★ THE COUNT OVER `k` WHOLE PERIODS IS EXACTLY `k B` ★★** -/
theorem jsp87card_nzRes_Icc_mul {K p H k : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hk : 1 ≤ k) :
    (((Finset.Icc 1 (k * p)).filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)).card : ℕ)
      = k * (H + (2 ^ K - 1)) := by
  have hK1 : 1 ≤ 2 ^ K := jsp87pow_pos K
  have hp1 : 1 ≤ p := by omega
  have hkN : 1 ≤ k * p := Nat.mul_le_mul hk hp1
  rw [jsp87card_nzRes_Icc_eq_sum hK hH hh hkN]
  have hcard : ((Finset.Icc 1 (H + (2 ^ K - 1))).card : ℕ) = H + (2 ^ K - 1) := by
    rw [Nat.card_Icc]
    omega
  have hjp : ∀ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), j < p := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Nat.lt_of_le_of_lt hj.2 (by omega)
  calc (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (k * p + j) / p)
      = ∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), k := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have h1 : k * p + j = j + p * k := by
          calc k * p + j = j + k * p := Nat.add_comm _ _
            _ = j + p * k := by rw [Nat.mul_comm]
        rw [h1, Nat.add_mul_div_left _ _ (Nat.lt_of_succ_le hp1),
          Nat.div_eq_of_lt (hjp j hj)]
        simp
    _ = k * (Finset.Icc 1 (H + (2 ^ K - 1))).card := by
        have hsc := Finset.sum_const (s := Finset.Icc 1 (H + (2 ^ K - 1))) (b := (k : ℕ))
        rw [nsmul_eq_mul] at hsc
        exact hsc.trans
          (Nat.mul_comm (Finset.Icc 1 (H + (2 ^ K - 1))).card (k : ℕ))
    _ = k * (H + (2 ^ K - 1)) := by rw [hcard]

/-- **★★ THE WHOLE-PERIOD INITIAL SEGMENT IS EXACTLY UNIFORM ★★**

```
jsp87NzFrac K p H [1, k p]  =  B / p ,     B = H + 2^K − 1 ,
```

i.e. `next_round_attack[0](d)` verbatim: for the initial-segment sample
`[1, k p]` — any number of whole periods — the nonzero fraction is *exactly*
`(H + 2^K − 1)/p`, with no limit and no error term. -/
theorem jsp87NzFrac_Icc_mul_eq {K p H k : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hk : 1 ≤ k) :
    jsp87NzFrac K p H (Finset.Icc 1 (k * p)) = ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ) := by
  have hN : 1 ≤ k * p := by
    have hp1 : 1 ≤ p := by omega
    have h := Nat.mul_le_mul hk hp1
    simpa only [Nat.one_mul] using h
  unfold jsp87NzFrac
  rw [jsp87card_nzRes_Icc_mul hK hH hh hk]
  have hcard : ((Finset.Icc 1 (k * p)).card : ℕ) = k * p := by
    rw [Nat.card_Icc]
    omega
  rw [hcard]
  have hsub : (((2 ^ K - 1 : ℕ) : ℕ) : ℝ) = ((2 : ℝ) ^ K) - 1 := by
    rw [Nat.cast_sub (jsp87pow_pos K), Nat.cast_pow 2 K]
    norm_num
  push_cast
  rw [hsub]
  have hkp : ((k * p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega)
  field_simp

/-- **THE BLOCK LENGTH IS NONNEGATIVE AS A REAL.**  Written as the *sum of the
casts* `(H : ℝ) + (2^K − 1 : ℝ)`, which is what the coercion of
`↑(H + 2^K − 1)` elaborates to. -/
private lemma jsp87B_nonneg (K H : ℕ) : 0 ≤ (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) := by
  have h1 : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ ((2 ^ K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **THE BLOCK LENGTH IS POSITIVE.** -/
private lemma jsp87B_pos (K H : ℕ) (hH : 1 ≤ H) :
    0 < (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) := by
  have h1 : 1 ≤ (H : ℝ) := by exact_mod_cast hH
  have h2 : 0 ≤ ((2 ^ K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **THE BLOCK LENGTH AS A SINGLE CAST.** -/
private lemma jsp87B_eq (K H : ℕ) :
    (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) = ((H + (2 ^ K - 1) : ℕ) : ℝ) := by
  symm
  exact Nat.cast_add _ _

/-- **`↑(N + B)` IS `↑N + B` IN THE REALS.** -/
private lemma jsp87NB_eq (K H N : ℕ) :
    (((N + (H + (2 ^ K - 1) : ℕ) : ℕ) : ℝ))
      = ((N : ℝ) + ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))) := by
  rw [Nat.cast_add, jsp87B_eq]

/-- **THE SEPARATION HYPOTHESIS IMPLIES `2^K ≤ p`.** -/
private lemma jsp87sep_2K (K H p : ℕ) (hH : 1 ≤ H) (hh : H + (2 ^ K - 1) + 1 ≤ p) :
    2 ^ K ≤ p := by
  have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
  have h3 : 0 ≤ 2 ^ K - 1 := by omega
  have h4 : (2 ^ K - 1) + 1 = 2 ^ K := by omega
  calc 2 ^ K = (2 ^ K - 1) + 1 := h4.symm
    _ ≤ (2 ^ K - 1) + (H + 1) := by omega
    _ = H + (2 ^ K - 1) + 1 := by omega
    _ ≤ p := hh

/-- **THE CARD OF THE BLOCK OF AN INITIAL SEGMENT IS `B`.** -/
private theorem jsp87B_card (K H : ℕ) :
    ((Finset.Icc 1 (H + (2 ^ K - 1))).card : ℕ) = H + (2 ^ K - 1) := by
  rw [Nat.card_Icc]
  omega

/-- **★ THE COUNT IS AT MOST `B · ⌊(N+B)/p⌋` ★** -/
theorem jsp87card_nzRes_Icc_le {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) :
    (jsp87NzRes K p H (Finset.Icc 1 N)).card
      ≤ (H + (2 ^ K - 1)) * ((N + (H + (2 ^ K - 1))) / p) := by
  have heq : (jsp87NzRes K p H (Finset.Icc 1 N)).card
      = ∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p := by
    have hz := jsp87card_nzRes_Icc_eq_sum (K := K) (p := p) (H := H) (N := N)
      hK hH hh hN
    exact hz
  rw [heq]
  have hle : (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p)
      ≤ ∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + (H + (2 ^ K - 1))) / p := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    exact Nat.div_le_div_right (by omega)
  have hsc : (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + (H + (2 ^ K - 1))) / p)
      = (Finset.Icc 1 (H + (2 ^ K - 1))).card
        * ((N + (H + (2 ^ K - 1))) / p) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  calc (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p)
      ≤ ∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + (H + (2 ^ K - 1))) / p := hle
    _ = (Finset.Icc 1 (H + (2 ^ K - 1))).card
        * ((N + (H + (2 ^ K - 1))) / p) := hsc
    _ = (H + (2 ^ K - 1)) * ((N + (H + (2 ^ K - 1))) / p) := by
        rw [jsp87B_card]

/-- **★ THE COUNT IS AT LEAST `B · ⌊N/p⌋` ★** -/
theorem jsp87card_nzRes_Icc_ge {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) :
    (H + (2 ^ K - 1)) * (N / p) ≤ (jsp87NzRes K p H (Finset.Icc 1 N)).card := by
  have heq : (jsp87NzRes K p H (Finset.Icc 1 N)).card
      = ∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p := by
    have hz := jsp87card_nzRes_Icc_eq_sum (K := K) (p := p) (H := H) (N := N)
      hK hH hh hN
    exact hz
  rw [heq]
  have hkey : (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), N / p)
      ≤ ∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    exact Nat.div_le_div_right (by omega)
  have hsc : (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), N / p)
      = (H + (2 ^ K - 1)) * (N / p) := by
    rw [Finset.sum_const, nsmul_eq_mul, jsp87B_card]
    simp
  calc (H + (2 ^ K - 1)) * (N / p)
      = ∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), N / p := hsc.symm
    _ ≤ ∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (N + j) / p := hkey

/-- **★★★ THE INITIAL SEGMENT IS WITHIN `B/N` OF THE UNIFORM VALUE ★★★**

```
B/p − B/N   ≤   jsp87NzFrac K p H [1,N]   ≤   B/p + B/N ,    B = H + 2^K − 1 ,
```

i.e. **the residue-block support of round 142 survives truncation,
quantitatively**: the nonzero fraction of the initial segment is the
whole-period value `B/p` up to an error of at most `B/N`.  This is
`next_round_attack[1]` of round 142 ("does the support bound survive
truncation?") — **it does**. -/
theorem jsp87NzFrac_Icc_bounds {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) :
    ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ) - ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (N : ℝ)
      ≤ jsp87NzFrac K p H (Finset.Icc 1 N)
    ∧ jsp87NzFrac K p H (Finset.Icc 1 N)
        ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ) + ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (N : ℝ) := by
  have hK1 : 1 ≤ 2 ^ K := jsp87pow_pos K
  have hp0 : 0 < p := by omega
  have hp0' : (p : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hcardN : ((Finset.Icc 1 N).card : ℕ) = N := by rw [Nat.card_Icc]; omega
  have hsum : jsp87NzFrac K p H (Finset.Icc 1 N)
      = (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (((N + j) / p : ℕ) : ℝ)) / (N : ℝ) := by
    have hz := jsp87card_nzRes_Icc_eq_sum (K := K) (p := p) (H := H) (N := N)
      hK hH hh hN
    unfold jsp87NzFrac
    rw [hz, hcardN]
    push_cast
    rfl
  constructor
  · -- the lower bound
    have hkey : (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), ((N : ℝ) / (p : ℝ) - 1))
        ≤ ∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (((N + j) / p : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have h1 : (((N / p : ℕ) : ℝ)) ≤ ((N + j) / p : ℕ) := by
        exact_mod_cast (Nat.div_le_div_right (by omega))
      have h2 := jsp87cast_div_ge_sub_one (N + j) p hp0
      have h3' : ((N : ℝ) / (p : ℝ)) ≤ (((N + j : ℕ) : ℝ)) / (p : ℝ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr (by omega))
          (by positivity : (0 : ℝ) ≤ p)
      linarith
    have hsc : (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), ((N : ℝ) / (p : ℝ) - 1))
        = ((Finset.Icc 1 (H + (2 ^ K - 1))).card : ℝ)
          * ((N : ℝ) / (p : ℝ) - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    calc ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ) - ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (N : ℝ)
        = ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * ((N : ℝ) / (p : ℝ) - 1) / (N : ℝ) := by
          field_simp
      _ = ((Finset.Icc 1 (H + (2 ^ K - 1))).card : ℝ)
          * ((N : ℝ) / (p : ℝ) - 1) / (N : ℝ) := by
        rw [jsp87B_card, ← jsp87B_eq]
      _ ≤ (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), ((N : ℝ) / (p : ℝ) - 1)) / (N : ℝ) := by
        rw [hsc]
      _ ≤ (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (((N + j) / p : ℕ) : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right hkey (by positivity)
  · -- the upper bound
    have hkey : (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (((N + j) / p : ℕ) : ℝ))
        ≤ ∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)),
            (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have h0 : N + j ≤ N + (H + (2 ^ K - 1)) := by omega
      have h1 : (N + j) / p ≤ (N + (H + (2 ^ K - 1))) / p :=
        Nat.div_le_div_right h0
      exact_mod_cast h1
    have hsc : (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)),
            (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ))
        = ((Finset.Icc 1 (H + (2 ^ K - 1))).card : ℝ)
          * (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    calc (∑ j ∈ Finset.Icc 1 (H + (2 ^ K - 1)), (((N + j) / p : ℕ) : ℝ)) / (N : ℝ)
        ≤ (∑ _j ∈ Finset.Icc 1 (H + (2 ^ K - 1)),
            (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right hkey (by positivity)
      _ = ((Finset.Icc 1 (H + (2 ^ K - 1))).card : ℝ)
          * (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ) / (N : ℝ) := by rw [hsc]
      _ ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
          * (((N : ℝ) + ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)))) / (p : ℝ) / ((N : ℝ)) := by
        rw [jsp87B_card, ← jsp87B_eq]
        have h1 : (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ)
            ≤ (((N + (H + (2 ^ K - 1)) : ℕ) : ℝ)) / (p : ℝ) :=
          jsp87cast_div_le (N + (H + (2 ^ K - 1))) p hp0
        have h1 : ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ)
            ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
              * (((N : ℝ) + ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)))) / (p : ℝ) := by
          have h1' : (((N + (H + (2 ^ K - 1))) / p : ℕ) : ℝ)
              ≤ (((N + (H + (2 ^ K - 1)) : ℕ) : ℝ)) / (p : ℝ) :=
            jsp87cast_div_le (N + (H + (2 ^ K - 1))) p hp0
          rw [jsp87NB_eq] at h1'
          convert mul_le_mul_of_nonneg_left h1' (jsp87B_nonneg K H) using 1 <;> ring
        exact div_le_div_of_nonneg_right h1
          (by have := hp0; have := hN; positivity : (0 : ℝ) ≤ (N : ℝ))
      _ = ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ)
          + ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
            / ((p : ℝ) * (N : ℝ)) := by
        rw [← div_div]
        field_simp [hp0', hN']
      _ ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ)
          + ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (N : ℝ) := by
        have hB : (H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
          have hB' : (H + (2 ^ K - 1) : ℕ) ≤ p := by omega
          exact_mod_cast hB'
        have h5 : ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * ((H : ℝ)
              + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ) ≤ (H : ℝ)
            + ((2 ^ K - 1 : ℕ) : ℝ) := by
          have h1 : ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) * ((H : ℝ)
                + ((2 ^ K - 1 : ℕ) : ℝ))
              ≤ (p : ℝ) * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hB (jsp87B_nonneg K H)
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < p)]
          nlinarith
        have h6 : ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
              * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / ((p : ℝ) * (N : ℝ))
            ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
              * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ) / ((N : ℝ)) := by
              rw [← div_div]
        have h7 : ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ))
              * ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / ((p : ℝ) * (N : ℝ))
            ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / ((N : ℝ)) :=
          h6.trans (div_le_div_of_nonneg_right h5
            (by have := hp0; have := hN; positivity : (0 : ℝ) ≤ (N : ℝ)))
        exact add_le_add_right h7 (((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ))

/-- **THE INITIAL SEGMENT IS WITHIN `B/N` OF THE UNIFORM VALUE** (the `|·|`-form
of `jsp87NzFrac_Icc_bounds`). -/
theorem jsp87NzFrac_Icc_close {K p H N : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) (hN : 1 ≤ N) :
    |jsp87NzFrac K p H (Finset.Icc 1 N) - ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (p : ℝ)|
      ≤ ((H : ℝ) + ((2 ^ K - 1 : ℕ) : ℝ)) / (N : ℝ) := by
  have hb := jsp87NzFrac_Icc_bounds hK hH hh hN
  rw [abs_le]
  constructor
  · linarith [And.left hb]
  · linarith [And.right hb]

/-! ## §5  NEGATIVE KNOWLEDGE, AND THE ANSWER TO `next_round_attack[1]` -/

/-- **A SAMPLE ENTIRELY INSIDE THE BLOCK HAS NONZERO FRACTION `1`.**  This is
half of item (c) of round 142's policy: a sample may avoid the block
(`f_p = 0`) **or** fill it (`f_p = 1`), so the policy's guess "a small sample
forces `f_p = 0`" is **false**, while `f_p (1 − f_p) = 0` survives. -/
theorem jsp87NzFrac_eq_one_of_block {K p H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) {s : Finset ℕ} (hs : s.Nonempty)
    (hin : ∀ n ∈ s, p - (H + (2 ^ K - 1)) ≤ n % p) :
    jsp87NzFrac K p H s = 1 := by
  have hsub : s ⊆ jsp87NzRes K p H s := by
    intro n hn
    rw [jsp87NzRes_eq_filter hK hH hh s]
    show n ∈ s.filter (fun m => p - (H + (2 ^ K - 1)) ≤ m % p)
    rw [Finset.mem_filter]
    exact ⟨hn, hin n hn⟩
  have hcard : s.card ≤ (jsp87NzRes K p H s).card :=
    Finset.card_le_card hsub
  have hcard2 : (jsp87NzRes K p H s).card ≤ s.card := by
    unfold jsp87NzRes
    exact Finset.card_filter_le _ _
  unfold jsp87NzFrac
  have hne : (0 : ℝ) ≠ ((s.card : ℕ) : ℝ) := by
    intro hz
    have hz' : (s.card : ℕ) = 0 := by exact_mod_cast hz.symm
    exact (Finset.card_ne_zero.mpr hs) hz'
  calc ((jsp87NzRes K p H s).card : ℝ) / ((s.card : ℕ) : ℝ)
      = ((s.card : ℕ) : ℝ) / ((s.card : ℕ) : ℝ) := by
        have hcc : (jsp87NzRes K p H s).card = s.card := le_antisymm hcard2 hcard
        rw [hcc]
    _ = 1 := by field_simp [hne]

/-- **A SAMPLE ENTIRELY OUTSIDE THE BLOCK HAS NONZERO FRACTION `0`.** -/
theorem jsp87NzFrac_eq_zero_of_out {K p H : ℕ} (hK : 2 ^ K ≤ p) (hH : 1 ≤ H)
    (hh : H + (2 ^ K - 1) + 1 ≤ p) {s : Finset ℕ} (hs : s.Nonempty)
    (hout : ∀ n ∈ s, n % p < p - (H + (2 ^ K - 1))) :
    jsp87NzFrac K p H s = 0 := by
  have hzero : jsp87NzRes K p H s = ∅ := by
    ext n
    constructor
    · intro hn
      have hn' := (Finset.mem_filter.mp hn)
      have hcon : p - (H + (2 ^ K - 1)) ≤ n % p :=
        (jsp87nz_iff_res_block hK hh hH n).mp hn'.2
      exact absurd hcon (Nat.not_le.mpr (hout n hn'.1))
    · intro h
      have hfalse : False := by simp at h
      exact hfalse.elim
  unfold jsp87NzFrac
  rw [hzero]
  simp

/-- **★★ (5.21′) FORCES THE SAMPLE TO STRADDLE THE BLOCK BOUNDARY, FOR EVERY
PRIME OF `S₁` ★★**

Hypothesis (5.21′) of arXiv:2512.01739, in the fraction form
`jsp87_endgame_frac_of_5_21`, is

```
1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ S₁} f_p (1 − f_p),     f_p = jsp87NzFrac K p H s ,
```

a positive lower bound on a **sum of nonnegative terms**.  Hence if even ONE
prime of `S₁` sees the whole sample on one side of the block boundary — inside
or outside — that term vanishes and (5.21′) is **impossible**.  So a witness of
(5.21′) must straddle for **every** prime of `S₁`: this is the sharpest
structural statement available about the "correlated sample" of §5 of
arXiv:2512.01739, and it is pure geometry, with no analytic input. -/
theorem jsp87_5_21_straddle {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ) (hH : 1 ≤ H)
    (hsep : ∀ p ∈ P, H + (2 ^ K - 1) + 1 ≤ p)
    (huni : ∀ p ∈ P, (∀ n ∈ s, p - (H + (2 ^ K - 1)) ≤ n % p)
              ∨ (∀ n ∈ s, n % p < p - (H + (2 ^ K - 1)))) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) := by
  intro h
  have h2K : 1 ≤ 2 ^ K := jsp87pow_pos K
  have h3 : 0 ≤ 2 ^ K - 1 := by omega
  have h4 : 2 ^ K - 1 + 1 = 2 ^ K := by omega
  have h5 : 2 ^ K ≤ H + (2 ^ K - 1) + 1 := by omega
  have hzero : ∀ p ∈ P, jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) = 0 := by
    intro p hp
    rcases huni p hp with h | h
    · have h1 : jsp87NzFrac K p H s = 1 :=
        jsp87NzFrac_eq_one_of_block (jsp87sep_2K K H p hH (hsep p hp)) hH (hsep p hp) hs h
      rw [h1]
      ring
    · have h1 : jsp87NzFrac K p H s = 0 :=
        jsp87NzFrac_eq_zero_of_out (jsp87sep_2K K H p hH (hsep p hp)) hH (hsep p hp) hs h
      rw [h1]
      ring
  have hsum0 : (∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) = 0 :=
    Finset.sum_eq_zero fun p hp => hzero p hp
  rw [hsum0] at h
  have hz : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * (0 : ℝ) = 0 := by ring
  rw [hz] at h
  exact absurd h (by norm_num)

/-! ## §6  MACHINE-CHECKED INSTANCES -/

/-- **★ THE MULTIPLES OF `5` AMONG `n + 2`, `1 ≤ n ≤ 20`: EXACTLY `⌊22/5⌋ = 4`.** -/
theorem jsp87count_shift_dvd_instance :
    (((Finset.Icc 1 20).filter (fun n => 5 ∣ n + 2)).card : ℕ) = 4 := by
  rw [jsp87count_shift_dvd 5 20 2 (by omega) (by omega)]
  norm_num

/-- **★ AND WITH `p = 6`, `j = 3`, `N = 210`: EXACTLY `35`.** -/
theorem jsp87count_shift_dvd_instance₂ :
    (((Finset.Icc 1 210).filter (fun n => 6 ∣ n + 3)).card : ℕ) = 35 := by
  rw [jsp87count_shift_dvd 6 210 3 (by omega) (by omega)]
  norm_num

/-- **★ AND THE INTERVAL FORM OF §3: THE MULTIPLES OF `7` IN `[8, 44]` ARE
`⌊44/7⌋ − ⌊7/7⌋ = 5`.** -/
theorem jsp87count_Icc_dvd_instance :
    (((Finset.Icc 8 44).filter (fun n => 7 ∣ n)).card : ℕ) = 5 := by
  rw [jsp87count_Icc_dvd 8 44 7 (by omega) (by omega)]

end JSP87
