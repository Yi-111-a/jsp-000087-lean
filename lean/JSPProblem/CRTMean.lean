/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.SingleScale
import JSPProblem.CharFun
import JSPProblem.SampleMean

/-!
# Round 138 — THE CHINESE-REMAINDER FACTORISATION OF THE ENDGAME'S MEAN, AT EVERY SCALE

Round 128 computed the complex mean of the endgame over the canonical sample at the
*ground-truth scale only* (`K = 0`, `H = 1`) and found it to be an Euler product.
Nothing was done at general `K` and `H` — the scales the endgame of
arXiv:2512.01739 §§5.3–5.14 is actually quantified over — and the cube sums `X_p`
(the alternating cube variables of (5.13)) were never shown to be `p`-periodic in
a usable form.

This module supplies exactly that, and then applies the Chinese remainder theorem.

## §0–§1  the arithmetic, from scratch

* `jsp87_mod_add_mul_inj` (private) — multiplication by a unit is injective on
  `Z / QZ`, proved from `Nat.Coprime.dvd_mul_left` and `Nat.modEq_iff_dvd'`.
* `jsp87_sum_perm` (private) — the residue average is invariant under the affine
  change of variable `b ↦ x + c·b`.
* `jsp87_sum_range_mul` (private) — every `k < m·n` is uniquely `a + m·b`.
* `jsp87_crt_sum_prod` — **THE CHINESE-REMAINDER THEOREM FOR SUMS**: for a Finset
  of primes `P` and functions `f p` that depend only on `n mod p`,

  ```
  (∑_{n < ∏ P} ∏_{p ∈ P} f p ((x + c·n) mod p)) = ∏_{p ∈ P} ( ∑_{a < p} f p a )
  ```

  whenever `c` is prime to every member of `P`.

## §2–§3  the consequence for the endgame

* `jsp87Phase_eq_prod` — the phase of (5.13) is the product of the single-cube
  exponentials `e (q · X_p)`.
* `jsp87Mean_eq_prod` — **THE MEAN IS AN EULER PRODUCT AT EVERY SCALE**:
  `jsp87Mean K H Y q = ∏_{p ≤ Y} ( (1/p) ∑_{a<p} e (q · X_p (a)) )`, for every
  cube dimension `K`, every depth `H`, every height `Y`.  Round 128 had this at
  `K = 0, H = 1` only.
* `jsp87ProdMean_eq_prod` — the product of the single-prime means has the *same*
  closed form.
* `jsp87Mean_eq_prodMean` — **so the complex error of (5.16)–(5.17) vanishes
  identically at EVERY scale**: over a whole number of periods the cube sums
  attached to distinct primes are exactly independent in the mean.  This is the
  machine-checked content of the independence claim of (5.16)–(5.17), and it
  needs no analytic input whatever — not even at `K ≥ 1`, where the cube sums are
  genuinely alternating.
* `jsp87Err2z_any`, `jsp87Err2_any`, `jsp87Hypothesis1617_any` — hence
  hypotheses (5.16)–(5.17) are satisfied with `κ₄ = κ₅ = 0` at every scale,
  generalising round 128's `jsp87Hypothesis1617_ground`.
* `jsp87_endgame_blunt_three` — **the endgame's five constants are only three**:
  at every admissible scale and every height where the harmonic-mass condition
  (5.21b) holds, at least one of `κ₁, κ₂, κ₃` is `≥ 1/30`; the two-class
  constants never appear.

## What this does not do

`jsp87_000087_main` is not declared.  The residual gap is unchanged: (5.15) — the
error `‖E[e^{q Σ X_p}] − 1‖` — is the only remaining obstacle of the endgame, and
`jsp87_endgame_blunt_three` now says so exactly.  Rounds 116 and 130 refuted
(5.15) on every *equidistributed* sample, which includes the canonical one used
here; so the endgame must be re-run on a genuinely non-equidistributed sample,
and that re-formulation is the open item recorded in `policy.json`.  No analytic
input was used or needed anywhere in this file.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  Residue arithmetic -/

/-- **MULTIPLICATION BY A UNIT IS INJECTIVE ON THE RESIDUES.** -/
private theorem jsp87_mod_add_mul_inj (Q c x : ℕ) (hQ : 0 < Q) (hc : Nat.Coprime c Q)
    {b b' : ℕ} (hb : b < Q) (hb' : b' < Q) (h : (x + c * b) % Q = (x + c * b') % Q) :
    b = b' := by
  by_cases hle : b ≤ b'
  · have hord : x + c * b ≤ x + c * b' := by
      have := Nat.mul_le_mul_left c hle
      omega
    have hdv : Q ∣ (x + c * b') - (x + c * b) := (Nat.modEq_iff_dvd' hord).mp h
    have heq : (x + c * b') - (x + c * b) = c * (b' - b) := by
      rw [Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    have hd : Q ∣ c * (b' - b) := by rw [← heq]; exact hdv
    have hd2 : Q ∣ b' - b := (hc.symm.dvd_mul_left (m := c) (n := b' - b)).mp
      (by simpa [Nat.mul_comm c (b' - b)] using hd)
    have hz : b' - b = 0 := Nat.eq_zero_of_dvd_of_lt hd2 (by omega)
    omega
  · have hsym : (x + c * b') % Q = (x + c * b) % Q := h.symm
    exact (jsp87_mod_add_mul_inj Q c x hQ hc hb' hb hsym).symm

/-- **AVERAGING A FUNCTION OVER A SHIFTED RESIDUE SYSTEM.**  The residue average
is invariant under the affine change of variable `b ↦ x + c·b`, valid because `c`
is a unit mod `Q`.  This is the only ingredient of the Chinese remainder theorem
used below. -/
private theorem jsp87_sum_perm (Q c x : ℕ) (hQ : 0 < Q) (hc : Nat.Coprime c Q) (g : ℕ → ℂ) :
    (∑ b ∈ Finset.range Q, g ((x + c * b) % Q)) = ∑ b ∈ Finset.range Q, g (b % Q) := by
  have hmem : ∀ b ∈ Finset.range Q, (x + c * b) % Q ∈ Finset.range Q :=
    fun b _ => Finset.mem_range.mpr (Nat.mod_lt _ hQ)
  have hinj : Set.InjOn (fun b => (x + c * b) % Q) (Finset.range Q : Set ℕ) := by
    intro a ha b hb hcongr
    exact jsp87_mod_add_mul_inj Q c x hQ hc (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)
      hcongr
  have hsub : (Finset.range Q).image (fun a => (x + c * a) % Q) ⊆ Finset.range Q := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hmem a ha
  have hcard : (Finset.range Q).card ≤ ((Finset.range Q).image (fun a => (x + c * a) % Q)).card := by
    rw [Finset.card_image_of_injOn (s := Finset.range Q) hinj]
  have himg : (Finset.range Q).image (fun a => (x + c * a) % Q) = Finset.range Q :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact Finset.sum_bij (s := Finset.range Q) (t := Finset.range Q)
    (f := fun b => g ((x + c * b) % Q)) (g := fun b => g (b % Q))
    (fun b (_hb : b ∈ Finset.range Q) => (x + c * b) % Q) hmem hinj
    (fun b hb => by
      obtain ⟨a, ha, hba⟩ := Finset.mem_image.mp (himg ▸ hb)
      exact ⟨a, ⟨ha, hba⟩⟩) (fun b _ => by simp)

/-- **THE DECOMPOSITION OF A WHOLE RECTANGLE OF INDICES.**  Every `k < m·n` is
uniquely `a + m·b` with `a < m` and `b < n`. -/
private theorem jsp87_sum_range_mul (f : ℕ → ℂ) (m n : ℕ) :
    (∑ k ∈ Finset.range (m * n), f k)
      = ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f (a + m * b) := by
  have hmem : ∀ k ∈ Finset.range (m * n),
      ((k % m, k / m) : ℕ × ℕ) ∈ Finset.range m ×ˢ Finset.range n := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hm0 : m = 0
    · subst hm0
      rw [Nat.zero_mul] at hk
      omega
    · have hm0' : 0 < m := Nat.pos_of_ne_zero hm0
      refine Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm0'), Finset.mem_range.mpr ?_⟩
      rw [Nat.div_lt_iff_lt_mul hm0']
      simpa [Nat.mul_comm] using hk
  have hinj : ∀ a ∈ Finset.range (m * n), ∀ b ∈ Finset.range (m * n),
      (a % m, a / m) = (b % m, b / m) → a = b := by
    intro a _ b _ hcongr
    have h3 : a % m + m * (a / m) = a := Nat.mod_add_div a m
    have h4 : b % m + m * (b / m) = b := Nat.mod_add_div b m
    have h1 : a % m = b % m := congrArg Prod.fst hcongr
    have h2 : a / m = b / m := congrArg Prod.snd hcongr
    calc a = a % m + m * (a / m) := h3.symm
      _ = b % m + m * (b / m) := by rw [h1, h2]
      _ = b := h4
  have hsurj : ∀ p ∈ Finset.range m ×ˢ Finset.range n,
      ∃ k ∈ Finset.range (m * n), (k % m, k / m) = p := by
    intro p hp
    obtain ⟨hmem, hn⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_range] at hmem hn
    by_cases hm0 : 0 < m
    · have hbnd : m * p.2 ≤ m * (n - 1) := Nat.mul_le_mul_left m (by omega)
      have hk1 : m * (n - 1) + m = m * n := by
        have hnn : (n - 1) + 1 = n := by omega
        calc m * (n - 1) + m = m * ((n - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = m * n := by rw [hnn]
      have hpm1 : p.1 ≤ m - 1 := by omega
      have hsum := Nat.add_le_add hpm1 hbnd
      refine ⟨p.1 + m * p.2, Finset.mem_range.mpr (by
        calc p.1 + m * p.2 ≤ (m - 1) + m * (n - 1) := hsum
          _ = m * n - 1 := by omega
          _ < m * n := by omega), ?_⟩
      refine Prod.ext ?_ ?_
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmem]
      · rw [Nat.add_mul_div_left p.1 p.2 hm0, Nat.div_eq_of_lt hmem]
        simp
    · have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst hmz
      exact absurd hmem (Nat.not_lt_zero _)
  have h := Finset.sum_bij (s := Finset.range (m * n))
    (t := Finset.range m ×ˢ Finset.range n) (f := f) (g := fun p => f (p.1 + m * p.2))
    (fun k _ => ((k % m, k / m) : ℕ × ℕ)) hmem hinj
    (fun b hb => by obtain ⟨k, hk, hkb⟩ := hsurj b hb; exact ⟨k, ⟨hk, hkb⟩⟩)
    (fun k _ => by
      have hX : k % m + m * (k / m) = k := Nat.mod_add_div k m
      rw [hX])
  rw [h, Finset.sum_product]

/-! ## §1  THE CHINESE-REMAINDER THEOREM FOR SUMS -/

/-- **THE PRODUCT OF A FINITSET OF POSITIVE NUMBERS IS POSITIVE.** -/
private theorem jsp87Prod_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < jsp87Prod P := by
  rcases P.eq_empty_or_nonempty with h | h
  · rw [h]; simp [jsp87Prod]
  · exact Finset.prod_pos fun i hi => (hP i hi).pos

/-- **THE CHINESE-REMAINDER THEOREM FOR SUMS.**  Let `P` be a Finset of primes and
let `f p` depend only on `n` modulo `p`.  Then over a whole period `jsp87Prod P`
the sum of the product of the `f p` is the product of the one-period sums; the
same holds after the affine change of variable `n ↦ x + c·n`, provided `c` is
prime to every member of `P`.

This is the statement that turns the endgame's mean into an Euler product at
**every** scale, not only at the ground-truth one. -/
theorem jsp87_crt_sum_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℕ → ℂ) (hf : ∀ p ∈ P, ∀ a b, a % p = b % p → f p a = f p b)
    (x c : ℕ) (hc : ∀ p ∈ P, Nat.Coprime c p) :
    (∑ n ∈ Finset.range (jsp87Prod P), ∏ p ∈ P, f p ((x + c * n) % p))
      = ∏ p ∈ P, (∑ a ∈ Finset.range p, f p a) := by
  classical
  induction P using Finset.induction_on generalizing x c with
  | empty =>
      simp [jsp87Prod]
  | @insert p P hpP ih =>
    have hcp : Nat.Coprime c p := hc p (Finset.mem_insert_self p P)
    have hprim : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert.mpr (Or.inr hq))
    have hc' : ∀ q ∈ P, Nat.Coprime (c * p) q := by
      intro q hq
      have h1 : Nat.Coprime c q := hc q (Finset.mem_insert.mpr (Or.inr hq))
      have h2 : Nat.Coprime p q := (Nat.coprime_primes
        (hP p (Finset.mem_insert_self p P)) (hprim q hq)).mpr (by
          intro hcongr
          subst hcongr
          exact hpP hq)
      have h3 : Nat.Coprime (p * c) q := Nat.Coprime.mul_left h2 h1
      rwa [Nat.mul_comm] at h3
    have hprod : jsp87Prod (insert p P) = p * jsp87Prod P := by
      unfold jsp87Prod
      rw [Finset.prod_insert hpP]
    -- the inner double sum, by the induction hypothesis
    have hinner : ∀ a : ℕ,
        (∑ b ∈ Finset.range (jsp87Prod P),
            ∏ q ∈ P, f q ((x + c * a + (c * p) * b) % q))
          = ∏ q ∈ P, (∑ i ∈ Finset.range q, f q i) := by
      intro a
      exact ih hprim (fun q hq a b hab => hf q (Finset.mem_insert.mpr (Or.inr hq)) a b hab)
        (x + c * a) (c * p) hc'
    -- the outer one-period sum of the `p`-factor
    have houter : (∑ a ∈ Finset.range p, f p ((x + c * a) % p))
        = ∑ a ∈ Finset.range p, f p a := by
      rw [jsp87_sum_perm p c x (by
        have := (hP p (Finset.mem_insert_self p P)).two_le
        omega) hcp (f p)]
      exact Finset.sum_congr rfl fun a _ =>
        hf p (Finset.mem_insert_self p P) (a % p) a (Nat.mod_mod a p)
    have hkey : ∀ a b : ℕ, x + c * (a + p * b) = x + c * a + (c * p) * b := by
      intro a b; ring
    have hmod : ∀ a b : ℕ, (x + c * (a + p * b)) % p = (x + c * a) % p := by
      intro a b
      rw [hkey, show x + c * a + (c * p) * b = x + c * a + p * (c * b) by ring,
        Nat.add_mul_mod_self_left]
    have hsplit : ∀ n : ℕ, (∏ q ∈ insert p P, f q ((x + c * n) % q))
          = f p ((x + c * n) % p) * ∏ q ∈ P, f q ((x + c * n) % q) := by
      intro n
      rw [Finset.prod_insert hpP]
    have hL : (∑ n ∈ Finset.range (jsp87Prod (insert p P)),
          (∏ q ∈ insert p P, f q ((x + c * n) % q)))
        = ∑ a ∈ Finset.range p,
            f p ((x + c * a) % p) * (∏ q ∈ P, ∑ i ∈ Finset.range q, f q i) := by
      rw [hprod]
      rw [Finset.sum_congr rfl (fun n _ => hsplit n)]
      rw [jsp87_sum_range_mul
        (fun n => f p ((x + c * n) % p) * ∏ q ∈ P, f q ((x + c * n) % q))
        p (jsp87Prod P)]
      refine Finset.sum_congr rfl ?_
      intro a _
      calc (∑ b ∈ Finset.range (jsp87Prod P),
            f p ((x + c * (a + p * b)) % p) * ∏ q ∈ P, f q ((x + c * (a + p * b)) % q))
          = ∑ b ∈ Finset.range (jsp87Prod P),
              f p ((x + c * a) % p) * ∏ q ∈ P, f q ((x + c * (a + p * b)) % q) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [hmod a b]
          _ = ∑ b ∈ Finset.range (jsp87Prod P),
              f p ((x + c * a) % p) * ∏ q ∈ P, f q ((x + c * a + (c * p) * b) % q) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [hkey a b]
          _ = f p ((x + c * a) % p) * (∏ q ∈ P, ∑ i ∈ Finset.range q, f q i) := by
            rw [(Finset.mul_sum (a := f p ((x + c * a) % p))
              (s := Finset.range (jsp87Prod P))
              (f := fun b => ∏ q ∈ P, f q ((x + c * a + (c * p) * b) % q))).symm]
            rw [hinner a]
    rw [Finset.prod_insert hpP]
    rw [hL]
    rw [(Finset.sum_mul (s := Finset.range p)
      (f := fun a => f p ((x + c * a) % p))
      (a := ∏ q ∈ P, ∑ i ∈ Finset.range q, f q i)).symm]
    rw [houter]

/-! ## §2  THE MEAN OF THE ENDGAME IS AN EULER PRODUCT AT **EVERY** SCALE -/

/-- **`X_p` DEPENDS ONLY ON `n` MODULO `p`.** -/
private theorem jsp87Xp0_mod {K : ℕ} (p n H : ℕ) :
    jsp87Xp0 (jsp87BinV K) p n H = jsp87Xp0 (jsp87BinV K) p (n % p) H := by
  have hiter : ∀ (m k : ℕ),
      jsp87Xp0 (jsp87BinV K) p (m + p * k) H = jsp87Xp0 (jsp87BinV K) p m H := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
        have hk : m + p * Nat.succ k = (m + p * k) + p := by
          rw [Nat.mul_succ]
          ring
        rw [hk]
        rw [jsp87Xp0_period (jsp87BinV K) p (m + p * k) H]
        exact ih
  rw [← Nat.mod_add_div n p, Nat.add_mul_mod_self_left, Nat.mod_mod]
  exact hiter (n % p) (n / p)

/-- **EVERY MEMBER OF A FINSET DIVIDES THE PRODUCT OF THE FINSET.** -/
private theorem jsp87dvd_prod_mem {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) : p ∣ jsp87Prod P := by
  -- each member divides the product
  rw [jsp87Prod]
  exact Finset.dvd_prod_of_mem (f := id) (s := P) (a := p) hp

/-- **AN EXPONENTIAL OF A SUM IS THE PRODUCT OF THE EXPONENTIALS.** -/
private theorem jsp87e_prod (P : Finset ℕ) (t : ℕ → ℝ) :
    (∏ p ∈ P, jsp87e (t p)) = jsp87e (∑ p ∈ P, t p) := by
  induction P using Finset.induction_on with
  | empty => simp [jsp87e]
  | @insert p P hpP ih =>
      rw [Finset.prod_insert hpP, Finset.sum_insert hpP, jsp87e_add, ih]

/-- **THE PRODUCT OF THE PRIMES OF A PRIME INTERVAL IS POSITIVE.** -/
private theorem jsp87Prod_primeSet_pos (B Y : ℕ) :
    0 < jsp87Prod (jsp87PrimeSet B Y) :=
  jsp87Prod_pos (jsp87PrimeSet B Y) (fun _ hp => jsp87PrimeSet_prime hp)

/-- **THE MEAN OVER THE CANONICAL SAMPLE, FOR A `q`-PERIODIC FUNCTION.** -/
private theorem jsp87CAvg_ProgFull' {P : Finset ℕ} {q : ℕ} (hQ : 0 < jsp87Prod P)
    (hq : 0 < q) (hqd : q ∣ jsp87Prod P) (g : ℕ → ℂ) (hg : ∀ i, g i = g (i % q)) :
    jsp87CAvg (jsp87ProgFull 0 1 P) g = (∑ a ∈ Finset.range q, g a) / ((q : ℕ) : ℂ) := by
  have hcard : 0 < (jsp87ProgFull 0 1 P).card := by
    rw [jsp87ProgFull_card (by norm_num) P hQ]
    exact hQ
  rw [jsp87ProgFull_eq_Icc hQ]
  have heq : Finset.Icc 0 (jsp87Prod P - 1) = Finset.range (jsp87Prod P) := by
    ext x
    rw [Finset.mem_Icc, Finset.mem_range]
    constructor <;> omega
  rw [heq]
  exact jsp87CAvg_uniform (Finset.range (jsp87Prod P)) q g hq hg
    (by rw [Finset.card_range]; exact hQ) (jsp87Uniform_range hq hqd)

/-- **THE PHASE OF (5.13) IS A PRODUCT OF THE SINGLE-CUBE EXPONENTIALS.** -/
theorem jsp87Phase_eq_prod (K H Y : ℕ) (q : ℝ) (i : ℕ) :
    jsp87e (q * (∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
        jsp87Xp0 (jsp87BinV K) p' i H))
      = ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H) := by
  rw [Finset.mul_sum]
  exact (jsp87e_prod (jsp87PrimeSet (jsp87Separation K H) Y)
    (fun p' => q * jsp87Xp0 (jsp87BinV K) p' i H)).symm

/-- **THE CAST OF `jsp87Prod`.** -/
private theorem jsp87_prod_cast (P : Finset ℕ) :
    ((jsp87Prod P : ℕ) : ℂ) = ∏ q ∈ P, ((q : ℕ) : ℂ) := by
  induction P using Finset.induction_on with
  | empty => simp [jsp87Prod]
  | @insert p P hpP ih =>
      have hprod : jsp87Prod (insert p P) = p * jsp87Prod P := by
        unfold jsp87Prod
        rw [Finset.prod_insert hpP]
      rw [hprod, Nat.cast_mul, Finset.prod_insert hpP, ih]

/-- **★ THE CLOSED FORM OF THE MEAN, AT EVERY SCALE ★**

For every depth `H`, every cube dimension `K` and every height `Y`, the complex
mean of the phase of arXiv:2512.01739 (5.15) over the canonical sample is the
Euler product

```
∏_{p ≤ Y prime} ( (1/p) ∑_{a < p} e (q · X_p (a)) ) ,
```

the single-prime factors being the one-period means of the cube sums `X_p`.  At
`K = 0, H = 1` this is round 128's `jsp87Mean_ground_eq_prod`; here it holds at
**every** scale, by the Chinese remainder theorem. -/
theorem jsp87Mean_eq_prod (K H Y : ℕ) (q : ℝ) :
    jsp87Mean K H Y q
      = ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          (∑ a ∈ Finset.range p', jsp87e (q * jsp87Xp0 (jsp87BinV K) p' a H))
            / ((p' : ℕ) : ℂ) := by
  classical
  have hQ : 0 < jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y) :=
    jsp87Prod_primeSet_pos _ _
  have hper : ∀ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y, ∀ a b : ℕ,
      a % p' = b % p' →
      jsp87e (q * jsp87Xp0 (jsp87BinV K) p' a H)
        = jsp87e (q * jsp87Xp0 (jsp87BinV K) p' b H) := by
    intro p' hp' a b hab
    rw [jsp87Xp0_mod (K := K) p' a H, jsp87Xp0_mod (K := K) p' b H, hab]
  have hhdvd : ∀ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
      p' ∣ jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y) :=
    fun p' hp' => jsp87dvd_prod_mem (P := jsp87PrimeSet (jsp87Separation K H) Y) hp'
  have hcrt := jsp87_crt_sum_prod (jsp87PrimeSet (jsp87Separation K H) Y)
    (fun r hr => jsp87PrimeSet_prime hr)
    (fun p n => jsp87e (q * jsp87Xp0 (jsp87BinV K) p n H)) hper 0 1 (by simp)
  have hg : ∀ i : ℕ,
      jsp87e (q * (∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p' i H))
        = jsp87e (q * (∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p'
            (i % jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)) H)) := by
    intro i
    have heq : (∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p'
            (i % jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)) H)
        = ∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          jsp87Xp0 (jsp87BinV K) p' i H := by
      refine Finset.sum_congr (M := ℝ) rfl fun p' hp' => ?_
      have hstep : (i % jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)) % p' = i % p' :=
        (Nat.mod_mod_of_dvd i (hhdvd p' hp'))
      rw [jsp87Xp0_mod (K := K) p' (i % jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)) H,
        hstep, jsp87Xp0_mod (K := K) p' i H]
    rw [heq]
  have h1 : jsp87Mean K H Y q
      = (∑ n ∈ Finset.range (jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)),
          ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87e (q * jsp87Xp0 (jsp87BinV K) p' ((0 + 1 * n) % p') H))
          / ((jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y) : ℕ) : ℂ) := by
    unfold jsp87Mean jsp87Sample jsp87Phase
    rw [jsp87CAvg_ProgFull' hQ hQ (Nat.dvd_refl _)
      (fun i => jsp87e (q * (∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
        jsp87Xp0 (jsp87BinV K) p' i H))) hg]
    have hsum : (∑ a ∈ Finset.range (jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)),
          jsp87e (q * (∑ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87Xp0 (jsp87BinV K) p' a H)))
        = ∑ n ∈ Finset.range (jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y)),
          ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87e (q * jsp87Xp0 (jsp87BinV K) p' ((0 + 1 * n) % p') H) := by
      refine Finset.sum_congr (M := ℂ) rfl fun n _ => ?_
      rw [Nat.zero_add, Nat.one_mul]
      have hred : (∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87e (q * jsp87Xp0 (jsp87BinV K) p' (n % p') H))
          = ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
            jsp87e (q * jsp87Xp0 (jsp87BinV K) p' n H) := by
        refine Finset.prod_congr (M := ℂ) rfl fun p' _ => ?_
        rw [jsp87Xp0_mod (K := K) p' n H]
      rw [hred]
      exact jsp87Phase_eq_prod K H Y q n
    rw [hsum]
  rw [h1, hcrt, jsp87_prod_cast]
  simp only [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/-! ## §3  (5.16)–(5.17) IS VACUOUS AT **EVERY** SCALE -/

/-- **THE PRODUCT OF THE SINGLE-PRIME MEANS, IN CLOSED FORM, AT EVERY SCALE.** -/
theorem jsp87ProdMean_eq_prod (K H Y : ℕ) (q : ℝ) :
    jsp87ProdMean K H Y q
      = ∏ p' ∈ jsp87PrimeSet (jsp87Separation K H) Y,
          (∑ a ∈ Finset.range p', jsp87e (q * jsp87Xp0 (jsp87BinV K) p' a H))
            / ((p' : ℕ) : ℂ) := by
  classical
  unfold jsp87ProdMean jsp87Sample
  refine Finset.prod_congr (M := ℂ) rfl fun p' hp' => ?_
  have hQ : 0 < jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y) :=
    jsp87Prod_primeSet_pos _ _
  have hpos : 0 < p' := (jsp87PrimeSet_prime hp').pos
  have hdvd : p' ∣ jsp87Prod (jsp87PrimeSet (jsp87Separation K H) Y) :=
    jsp87dvd_prod_mem (P := jsp87PrimeSet (jsp87Separation K H) Y) hp'
  have hg : ∀ i, jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H)
      = jsp87e (q * jsp87Xp0 (jsp87BinV K) p' (i % p') H) := by
    intro i
    rw [jsp87Xp0_mod (K := K) p' i H]
  rw [jsp87CAvg_ProgFull' hQ hpos hdvd _ hg]

/-- **★ THE MEAN IS THE PRODUCT OF THE SINGLE-PRIME MEANS, AT EVERY SCALE ★**

This is the machine-checked content of the independence claim (5.16)–(5.17) of
arXiv:2512.01739 §§5.7–5.14, for the canonical sample: over a whole number of
periods, the cube sums attached to distinct primes are **exactly** independent in
the mean, at every depth `H` and every cube dimension `K`.  Round 128 established
this only at `K = 0, H = 1`. -/
theorem jsp87Mean_eq_prodMean (K H Y : ℕ) (q : ℝ) :
    jsp87Mean K H Y q = jsp87ProdMean K H Y q :=
  (jsp87Mean_eq_prod K H Y q).trans (jsp87ProdMean_eq_prod K H Y q).symm

/-- **THE COMPLEX ERROR OF (5.16)–(5.17) VANISHES AT EVERY SCALE.** -/
theorem jsp87Err2z_any (K H Y : ℕ) (q : ℝ) : jsp87Err2z K H Y q = 0 := by
  unfold jsp87Err2z
  rw [jsp87Mean_eq_prodMean K H Y q]
  ring

/-- **(5.16)–(5.17) HOLDS AT EVERY SCALE WITH `κ₄ = κ₅ = 0`.**  This *generalises*
round 128's `jsp87Hypothesis1617_ground`, which was the ground-truth scale
`K = 0, H = 1` only: the constants `κ₄, κ₅` of the endgame are free at every
scale. -/
theorem jsp87Hypothesis1617_any (K H : ℕ) (q : ℝ) : jsp87Hypothesis1617 K H q 0 0 := by
  intro Z
  rw [jsp87Err2_eq, jsp87Err2z_any]
  norm_num

/-- **THE ERROR OF (5.16)–(5.17) IS ZERO, AT EVERY SCALE.** -/
theorem jsp87Err2_any (K H Y : ℕ) (q : ℝ) : jsp87Err2 K H Y q = 0 := by
  rw [jsp87Err2_eq, jsp87Err2z_any]
  norm_num

/-- **★ THE ENDGAME'S FIVE CONSTANTS ARE ONLY THREE ★**

At **every** admissible scale `(K, H, q)` and **every** height `Y` at which the
harmonic-mass condition (5.21b) holds, the endgame of
`JSPProblem.HarmonicMass` forces at least one of `κ₁, κ₂, κ₃` to be `≥ 1/30`;
the two-class constants `κ₄, κ₅` never appear, because (5.16)–(5.17) holds with
them equal to `0` (`jsp87Hypothesis1617_any`). -/
theorem jsp87_endgame_blunt_three (K H Y : ℕ) (q κ1 κ2 κ3 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) (hH : 1 ≤ H)
    (hrecip : (2 : ℝ) ^ (2 * H + K + 1)
      ≤ (q ^ 2) * jsp87RecipSum (jsp87PrimeSet (jsp87Separation K H) Y))
    (e1 : jsp87Err1 K H Y q ≤ κ1 + κ2 + κ3) :
    1 / 30 ≤ κ1 ∨ 1 / 30 ≤ κ2 ∨ 1 / 30 ≤ κ3 := by
  have he2 : jsp87Err2 K H Y q ≤ (0 : ℝ) + (0 : ℝ) := by
    rw [jsp87Err2_any K H Y q]
    norm_num
  have hzero : (0 : ℝ) < 1 / 30 := by norm_num
  by_contra hcon
  push Not at hcon
  exact jsp87_endgame_of_recipSum K H Y q κ1 κ2 κ3 (0 : ℝ) (0 : ℝ) hK hH hrecip e1 he2
    ⟨hcon.1, hcon.2.1, hcon.2.2, hzero, hzero⟩

end JSP87
