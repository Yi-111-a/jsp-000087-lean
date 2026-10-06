/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.IccWitness
import JSPProblem.EulerDivergence
import JSPProblem.SharpVar
import JSPProblem.Xp
import JSPProblem.Variance

/-!
# JSP-000087, round 145 — THE CRT-BOX ENDGAME

## The gap this file attacks

Rounds 116–144 machine-checked the endgame of Tao–Teräväinen
(arXiv:2512.01739) §§5.3–5.14 and then attacked the two-class criterion
(5.21′) geometrically: round 142 computed the **exact support** of the
cube-alternating variable `X_p` (a block of `H + 2^K − 1` residues), round
143 computed the **exact count** over an initial segment, round 144 showed
(5.21′) is satisfiable on a plain initial segment.  The conclusion was: *no
sample geometry can refute (5.21′)*, so the remaining burden lies with the
error estimates (5.15) and (5.16)–(5.17).

Nothing in those rounds looked at the sample the published proof can *most
easily* control: the **box of residues**

```
B P = [0, M),      M = ∏ p ∈ P, p,     P a set of distinct primes.
```

On `B P` the residues `(n mod p)_{p ∈ P}` run through `∏_{p ∈ P} [0, p)`
exactly once each (the Chinese remainder theorem), and `X_p` depends on `n`
only through `n mod p`.  Hence the random structure of §5 **collapses to
independent single-prime statistics**: hypothesis **(5.16)–(5.17)** holds
with `κ₄ = κ₅ = 0` (an identity, not an estimate), while hypothesis **(5.15)**
is **refuted at every height**, because the single-prime variances are
`Θ(1/p)` (round 140's `jsp87Var_Xp_res_sharp`) and Euler's divergence makes
`∑_p Var` arbitrarily large.

Both statements are proved here from scratch: the two periodization
primitives of §0 are proved by hand (injectivity of `t ↦ (c + a t) mod m`
for `gcd a m = 1`, then pigeonhole; and the base-`M` division of a range).

## What is *not* proved here

The endgame of §5.4 still cannot be *started*: (5.15) is false on boxes, so
a rationality-driven configuration is never a box.  The blocker is unchanged
(`jsp87Mcov_small`, the Chowla-type two-point correlation of ω of
arXiv:2512.01739 Thm 3.1 / Pilatte), but it is now localised to a strictly
smaller class of samples: **a witness sample must be correlated, and in
particular must not be a box of primes.**
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §0  TWO PERIODIZATION PRIMITIVES, FROM SCRATCH -/

/-- **`k · (b − c) = k · b − k · c` for `c ≤ b`**: Euclid's lemma is usable on
differences.  (`omega` cannot do this: it treats products of two variables as
atoms, so the identity is not Presburger.  The proof goes through `ℤ`.) -/
private theorem jsp87mul_sub {k b c : ℕ} (h : c ≤ b) :
    k * (b - c) = k * b - k * c := by
  apply Nat.cast_injective (R := ℤ)
  have hsub : k * c ≤ k * b := Nat.mul_le_mul_left k h
  rw [Nat.cast_mul, Nat.cast_sub h, Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_mul]
  ring

/-- **`gcd a m = 1` makes `t ↦ (c + a t) mod m` injective on `[0, m)`.**

The classical step of the Chinese remainder theorem.  If
`(c + a t) mod m = (c + a t') mod m` with `t < t' < m`, then `m ∣ a (t' − t)`
— the two decompositions `c + a t = r + m u`, `c + a t' = r + m v` give
`a t' − a t = m v − m u`, hence `m ∣ a t' − a t`, and Euclid's lemma
(`jsp87mul_sub` + `Nat.dvd_sub` + `Nat.Coprime.dvd_of_dvd_mul_left`) yields
`m ∣ t' − t`, impossible for `0 < t' − t < m`. -/
private theorem jsp87mod_mul_ne {m a c t t' : ℕ} (_hm : 2 ≤ m) (ha : 0 < a)
    (hc : Nat.Coprime a m) (_ht : t < m) (_ht' : t' < m) (hlt : t < t') :
    (c + a * t) % m ≠ (c + a * t') % m := by
  intro heq
  obtain ⟨u, hu⟩ : ∃ u : ℕ, c + a * t = (c + a * t) % m + m * u :=
    ⟨(c + a * t) / m, (Nat.mod_add_div (c + a * t) m).symm⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ, c + a * t' = (c + a * t') % m + m * v :=
    ⟨(c + a * t') / m, (Nat.mod_add_div (c + a * t') m).symm⟩
  have heq' : (c + a * t) % m = (c + a * t') % m := heq
  have hlt2 : a * t ≤ a * t' := (Nat.mul_lt_mul_of_pos_left hlt ha).le
  -- `a t' − a t = m v − m u`
  have hkey : a * t' - a * t = m * v - m * u := by
    have hv' : (c + a * t) % m + m * v = c + a * t' := by
      rw [← heq'] at hv; exact hv.symm
    have hB : (c + a * t') + m * u = (c + a * t) + m * v := by
      calc (c + a * t') + m * u = ((c + a * t) % m + m * v) + m * u := by rw [hv']
        _ = ((c + a * t) % m + m * u) + m * v := by omega
        _ = (c + a * t) + m * v := by
            exact congrArg (fun z : ℕ => z + m * v) hu.symm
    have hA : a * t' + m * u = a * t + m * v := by omega
    have hle2 : m * u ≤ a * t + m * v := by omega
    have h4 : a * t' = (a * t + m * v) - m * u := by
      have h5 := Nat.add_sub_of_le hle2
      omega
    have hle3 : m * u ≤ m * v := by omega
    rw [h4, Nat.add_sub_assoc hle3 (a * t), Nat.add_sub_cancel_left]
  obtain ⟨w, hw⟩ := Nat.dvd_sub (Nat.dvd_mul_right m v) (Nat.dvd_mul_right m u)
  obtain ⟨z, hz⟩ : ∃ z : ℕ, a * t' - a * t = m * z := by
    refine ⟨w, ?_⟩
    calc a * t' - a * t = m * v - m * u := hkey
      _ = m * w := hw
  obtain ⟨z', hz'⟩ : ∃ z' : ℕ, a * (t' - t) = m * z' := by
    refine ⟨z, ?_⟩
    have hj := jsp87mul_sub (k := a) (b := t') (c := t) (Nat.le_of_lt hlt)
    calc a * (t' - t) = a * t' - a * t := hj
      _ = m * z := hz
  have hdvd : m ∣ t' - t := hc.symm.dvd_of_dvd_mul_left ⟨z', hz'⟩
  have hz : t' - t = 0 := by
    rcases Nat.eq_zero_or_pos (t' - t) with hzero | hpos
    · exact hzero
    · exfalso
      have hlt'' : t' - t < m := by omega
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : 1 ≤ k := by
        have hkne : k ≠ 0 := by
          intro hkz
          have := hk
          simp [hkz] at this
          omega
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hkne)
      have hkm : t' - t = k * m := by
        calc t' - t = m * k := hk
          _ = k * m := Nat.mul_comm _ _
      have hmul : m ≤ k * m := by simpa using Nat.mul_le_mul_right m hk1
      have hmk : m ≤ t' - t := by
        calc m ≤ k * m := hmul
          _ = t' - t := hkm.symm
      omega
  omega

/-- **THE CHINESE-REMAINDER PERIODIZATION.**

If `gcd a m = 1` then `t ↦ (c + a t) mod m` permutes `[0, m)`, so a sum over a
whole period of `m` consecutive integers sees every residue exactly once.  This
is the independence bookkeeping of §5, proved from `jsp87mod_mul_ne` plus the
pigeonhole principle (`Finset.surj_on_of_inj_on_of_card_le`). -/
private theorem jsp87sum_mod_mul {m a c : ℕ} (hm : 2 ≤ m) (ha : 0 < a)
    (hc : Nat.Coprime a m) {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ t ∈ Finset.range m, f ((c + a * t) % m)) = ∑ i ∈ Finset.range m, f i := by
  classical
  have hsurj : ∀ i : ℕ, i ∈ Finset.range m →
      ∃ t : ℕ, ∃ ht : t ∈ Finset.range m, (c + a * t) % m = i := by
    intro i hi
    obtain ⟨t, ht, hiteq⟩ := Finset.surj_on_of_inj_on_of_card_le
      (s := Finset.range m) (t := Finset.range m)
      (fun t _ => (c + a * t) % m)
      (fun t _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
      (fun x y hx hy heq => by
        simp only [Finset.mem_range] at hx hy
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (jsp87mod_mul_ne hm ha hc hx hy h heq)
        · exact h
        · exact False.elim (jsp87mod_mul_ne (t := y) (t' := x) hm ha hc hy hx h heq.symm))
      (by rw [Finset.card_range]) i hi
    exact ⟨t, ht, hiteq.symm⟩
  exact Finset.sum_bij (fun t _ => (c + a * t) % m)
    (fun t _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
    (fun a₁ ha₁ a₂ ha₂ heq => by
      simp only [Finset.mem_range] at ha₁ ha₂
      rcases lt_trichotomy a₁ a₂ with h | h | h
      · exact False.elim (jsp87mod_mul_ne hm ha hc ha₁ ha₂ h heq)
      · exact h
      · exact False.elim (jsp87mod_mul_ne (t := a₂) (t' := a₁) hm ha hc ha₂ ha₁ h heq.symm))
    (fun i hi => hsurj i hi) (fun t _ => rfl)

/-- **DIVISION OF A RANGE IN BASE `M`.**

`n ↦ (n / M, n mod M)` bijects `[0, a M)` with `[0, a) × [0, M)`, with inverse
`(k, i) ↦ i + M k` (a consequence of `Nat.mod_add_div`).  Every double counting
identity below is an instance. -/
private theorem jsp87sum_range_div {R : Type*} [AddCommMonoid R]
    (a M : ℕ) (g : ℕ → ℕ → R) :
    (∑ n ∈ Finset.range (a * M), g (n / M) (n % M))
      = ∑ k ∈ Finset.range a, ∑ i ∈ Finset.range M, g k i := by
  classical
  by_cases hM : M = 0
  · subst hM
    simp
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hprod : (∑ x ∈ Finset.range a ×ˢ Finset.range M, g x.1 x.2)
      = ∑ k ∈ Finset.range a, ∑ i ∈ Finset.range M, g k i :=
    Finset.sum_product _ _ _
  have hbij : ∀ n ∈ Finset.range (a * M),
      (n / M, n % M) ∈ Finset.range a ×ˢ Finset.range M := by
    intro n hn
    have hn' : n < a * M := Finset.mem_range.mp hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hMpos).2 hn'),
      Finset.mem_range.mpr (Nat.mod_lt _ hMpos)⟩
  have hinjb : ∀ x ∈ Finset.range (a * M), ∀ y ∈ Finset.range (a * M),
      (x / M, x % M) = (y / M, y % M) → x = y := by
    intro x hx y hy hxy
    have hxy' : x / M = y / M ∧ x % M = y % M := by simpa using hxy
    have hq : x / M = y / M := hxy'.1
    have hr : x % M = y % M := hxy'.2
    have h5 : x = x % M + M * (y / M) := by
      rw [← hq]; exact (Nat.mod_add_div x M).symm
    have h6 : y = y % M + M * (y / M) := (Nat.mod_add_div y M).symm
    omega
  have hsurjb : ∀ b ∈ Finset.range a ×ˢ Finset.range M,
      ∃ n : ℕ, ∃ hn : n ∈ Finset.range (a * M), (n / M, n % M) = b := by
    intro b hb
    rcases b with ⟨k, i⟩
    have hb' := Finset.mem_product.mp hb
    have hk : k < a := Finset.mem_range.mp hb'.1
    have hi : i < M := Finset.mem_range.mp hb'.2
    have hbound : i + M * k < a * M := by
      have h1 : M * k + i < M * k + M := by omega
      have h2 : M * k + M = M * (k + 1) := (Nat.mul_succ M k).symm
      have h3 : M * (k + 1) ≤ M * a := Nat.mul_le_mul_left M (by omega)
      have h4 : M * k + i < M * a := by
        calc M * k + i < M * k + M := h1
          _ = M * (k + 1) := h2
          _ ≤ M * a := h3
      simpa [Nat.add_comm, Nat.mul_comm] using h4
    refine ⟨i + M * k, Finset.mem_range.mpr hbound, ?_⟩
    show ((i + M * k) / M, (i + M * k) % M) = (k, i)
    have hdiv : (i + M * k) / M = k := by
      rw [Nat.add_mul_div_left (y := M) (x := i) (z := k) hMpos,
        Nat.div_eq_of_lt hi, Nat.zero_add]
    have hmod : (i + M * k) % M = i := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    rw [hdiv, hmod]
  rw [← hprod]
  exact Finset.sum_bij (s := Finset.range (a * M))
    (t := Finset.range a ×ˢ Finset.range M)
    (fun n _ => (n / M, n % M)) hbij hinjb hsurjb (fun n _ => rfl)

/-- **THE PERIODIZATION IDENTITY.**

For `0 < M` and any `a ≥ 1`, the sum of an `M`-periodic function over a whole
number of periods is exactly `a` times the sum over one period. -/
theorem jsp87sum_period {R : Type*} [AddCommMonoid R]
    (a M : ℕ) (_hM : 0 < M) (f : ℕ → R) :
    (∑ n ∈ Finset.range (a * M), f (n % M))
      = (a : ℕ) • ∑ i ∈ Finset.range M, f i := by
  calc (∑ n ∈ Finset.range (a * M), f (n % M))
      = ∑ k ∈ Finset.range a, ∑ i ∈ Finset.range M, f i :=
        jsp87sum_range_div a M (fun _ i => f i)
    _ = ((Finset.range a).card • (∑ i ∈ Finset.range M, f i)) :=
        (Finset.sum_congr rfl (fun k _ => rfl)).trans (Finset.sum_const _)
    _ = (a : ℕ) • (∑ i ∈ Finset.range M, f i) := by rw [Finset.card_range]

/-- **A PERIOD IS INVISIBLE TO THE MODULUS.**  If `n ∣ t` then the residue of
`s + t` mod `n` is the residue of `s`. -/
private theorem jsp87mod_add_dvd {q' s t : ℕ} (h : q' ∣ t) : (s + t) % q' = s % q' :=
  by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h, Nat.add_zero, Nat.mod_mod]

/-! ## §1  `X_p` IS A FUNCTION OF `n mod p` -/

/-- **DIVISIBILITY IS A FUNCTION OF THE RESIDUE.** -/
private theorem jsp87dvd_add_mod (p c n : ℕ) : p ∣ n % p + c ↔ p ∣ n + c := by
  have hkey : n % p + c + p * (n / p) = n + c := by
    have h := Nat.mod_add_div n p
    omega
  rw [← hkey]
  exact Nat.dvd_add_iff_left (Nat.dvd_mul_right p (n / p))

/-- **THE HITTING VERTICES DEPEND ONLY ON `n mod p`.** -/
theorem jsp87HitVerts_mod {K : ℕ} (p n : ℕ) (v : Fin K → ℕ) (h : ℕ) :
    jsp87HitVerts p n v h = jsp87HitVerts p (n % p) v h := by
  ext ε
  simp only [jsp87HitVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (jsp87dvd_add_mod p (jsp87R v h ε) n).symm

/-- **★★ THE CUBE SUM IS `p`-PERIODIC ★★**

`X_p n = X_p (n mod p)`: the cube-alternating variable of (5.13) is a function
on `ℤ/pℤ`.  This is what makes rounds 142–144's residue statements statements
about *all* integers, and it is what lets the Chinese remainder theorem be
applied to the endgame of §3 below. -/
theorem jsp87Xp0_mod {K : ℕ} (v : Fin K → ℕ) (p n H : ℕ) :
    jsp87Xp0 v p n H = jsp87Xp0 v p (n % p) H := by
  unfold jsp87Xp0
  refine Finset.sum_congr rfl fun h _ => ?_
  unfold jsp87XpLevel
  refine Finset.sum_congr rfl fun ε _ => ?_
  by_cases hd : p ∣ n + jsp87R v h ε
  · have hd' : p ∣ n % p + jsp87R v h ε := (jsp87dvd_add_mod p (jsp87R v h ε) n).2 hd
    simp only [hd, hd', ite_true]
  · have hd' : ¬ (p ∣ n % p + jsp87R v h ε) :=
      fun hh => hd ((jsp87dvd_add_mod p (jsp87R v h ε) n).1 hh)
    simp only [hd, hd', ite_false]


/-- **`X_p` only depends on `n` through `n mod p`.** -/
theorem jsp87Xp0_modEq {K : ℕ} (v : Fin K → ℕ) (p n n' H : ℕ)
    (h : n % p = n' % p) : jsp87Xp0 v p n H = jsp87Xp0 v p n' H := by
  calc jsp87Xp0 v p n H = jsp87Xp0 v p (n % p) H := jsp87Xp0_mod v p n H
    _ = jsp87Xp0 v p (n' % p) H := by rw [h]
    _ = jsp87Xp0 v p n' H := (jsp87Xp0_mod v p n' H).symm

/-- **THE HITTING VERTICES OF (5.13) ON A FULL PERIOD.**  `X_p` restricted to
`[0, p)` is the canonical representative used everywhere below. -/
theorem jsp87Xp0_range_eq (K p H : ℕ) (n : ℕ) (hn : n < p) :
    jsp87Xp0 (jsp87BinV K) p n H = jsp87Xp0 (jsp87BinV K) p (n % p) H := by
  rw [Nat.mod_eq_of_lt hn]

/-- **★★ THE SUM OF A FUNCTION OF `X_p` OVER WHOLE PERIODS OF `p` IS
`a` TIMES THE SUM OVER ONE PERIOD ★★**

For `0 < p` and any `φ : ℝ → ℂ`,

```
∑_{n < a·p} φ (X_p n)  =  a · ∑_{m < p} φ (X_p m) .
```

**Every statistic of the endgame that is a function of a single `X_p` and of
the sample `[0, a p)` is independent of the height `a`.**  This is the fact
that makes the CRT box of §3 collapse onto the single prime `p`, and it is
the *only* place where `X_p`'s periodicity (§1) is used. -/
theorem jsp87sum_Xp_period {K : ℕ} {R : Type*} [AddCommMonoid R] [NatCast R]
    (v : Fin K → ℕ) (p a H : ℕ) (hp : 0 < p) (φ : ℝ → R) :
    (∑ n ∈ Finset.range (a * p), φ (jsp87Xp0 v p n H))
      = (a : ℕ) • ∑ m ∈ Finset.range p, φ (jsp87Xp0 v p m H) := by
  have h1 := jsp87sum_period a p hp (fun i : ℕ => φ (jsp87Xp0 v p i H))
  refine (Finset.sum_congr rfl fun n hn => ?_).trans h1
  have hnp : jsp87Xp0 v p (n % p) H = jsp87Xp0 v p n H :=
    (jsp87Xp0_mod v p n H).symm
  simp only [hnp]


/-! ## §2  EVERY MEAN AND VARIANCE OF A SINGLE `X_p` IS HEIGHT-INDEPENDENT -/

/-- **THE REAL MEAN OF A FUNCTION OF `X_p` OVER A BOX OF PERIODS.** -/
private theorem jsp87FAvg_Xp_period {K : ℕ} (φ : ℝ → ℝ) (p a H : ℕ)
    (hp : 0 < p) (ha : 1 ≤ a) :
    jsp87FAvg (Finset.range (a * p)) (fun i => φ (jsp87Xp0 (jsp87BinV K) p i H))
      = jsp87FAvg (Finset.range p) (fun i => φ (jsp87Xp0 (jsp87BinV K) p i H)) := by
  have hsum := jsp87sum_Xp_period (jsp87BinV K) p a H hp φ
  rw [nsmul_eq_mul] at hsum
  have hane : ((a : ℕ) : ℝ) ≠ 0 := by
    have : (a : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hpne : ((p : ℕ) : ℝ) ≠ 0 := by
    have : (p : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hA : ((∑ n ∈ Finset.range (a * p), φ (jsp87Xp0 (jsp87BinV K) p n H) : ℝ))
      = ((a : ℕ) : ℝ) * ∑ m ∈ Finset.range p, φ (jsp87Xp0 (jsp87BinV K) p m H) := hsum
  rw [jsp87FAvg, jsp87FAvg, Finset.card_range, Finset.card_range, hA, Nat.cast_mul]
  field_simp

/-- **★★ THE COMPLEX MEAN OF THE SINGLE-PRIME PHASE OVER A BOX OF PERIODS ★★**

For `0 < p` and `1 ≤ a`, the truncated mean `𝔼ᶜ e (q X_p)` over the box
`[0, a p)` equals its value over ONE period `[0, p)`: the quantity that
hypotheses (5.19)/(5.21) of arXiv:2512.01739 use for a single prime does not
depend on the height. -/
theorem jsp87CAvg_Xp_period {K : ℕ} (q : ℝ) (p a H : ℕ) (hp : 0 < p) (ha : 1 ≤ a) :
    jsp87CAvg (Finset.range (a * p))
        (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))
      = jsp87CAvg (Finset.range p)
        (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) := by
  have hsum := jsp87sum_Xp_period (jsp87BinV K) p a H hp (fun x : ℝ => jsp87e (q * x))
  rw [nsmul_eq_mul] at hsum
  have hane : ((a : ℕ) : ℂ) ≠ 0 := by
    have : (a : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := by
    have : (p : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hA : ((∑ n ∈ Finset.range (a * p), jsp87e (q * jsp87Xp0 (jsp87BinV K) p n H) : ℂ))
      = ((a : ℕ) : ℂ)
        * ∑ m ∈ Finset.range p, jsp87e (q * jsp87Xp0 (jsp87BinV K) p m H) := hsum
  rw [jsp87CAvg, jsp87CAvg, Finset.card_range, Finset.card_range, hA, Nat.cast_mul]
  field_simp

/-- **THE VARIANCE OF THE SINGLE-PRIME PHASE OVER A BOX OF PERIODS.**  As for
the mean, the variance of `q X_p` over `[0, a p)` is the variance over one
period: **the only statistic of §5 that a single prime contributes is a
function of `p` alone.** -/
theorem jsp87Var_Xp_period {K : ℕ} (q : ℝ) (p a H : ℕ) (hp : 0 < p) (ha : 1 ≤ a) :
    jsp87Var (Finset.range (a * p)) (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)
      = jsp87Var (Finset.range p) (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) := by
  have h2 := jsp87FAvg_Xp_period (K := K) (fun x : ℝ => (q * x) ^ 2) p a H hp ha
  have h3 := jsp87FAvg_Xp_period (K := K) (fun x : ℝ => q * x) p a H hp ha
  have hne1 : (Finset.range (a * p)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by
        have h1 : 0 < a * p := Nat.mul_pos (by omega) hp
        omega)⟩
  have hne2 : (Finset.range p).Nonempty :=
    ⟨0, Finset.mem_range.mpr hp⟩
  rw [jsp87Var_eq_FAvg_sq_sub _ hne1 _, jsp87Var_eq_FAvg_sq_sub _ hne2 _]
  have h4 : (jsp87FAvg (Finset.range (a * p))
      (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) ^ 2
      = (jsp87FAvg (Finset.range p)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H)) ^ 2 :=
    congrArg (fun x : ℝ => x ^ 2) h3
  linarith

/-! ## §3  THE CRT BOX: THE PRODUCT FORM OF §5 IS AN IDENTITY THERE -/

/-- **THE BOX OF RESIDUES OF A FINITE SET OF NATURAL NUMBERS.**  For a set `P`
of distinct primes this is the smallest interval on which the residues
`(n mod p)_{p ∈ P}` run through the whole product of the ranges `[0, p)`. -/
noncomputable def jsp87Box (P : Finset ℕ) : Finset ℕ := Finset.range (∏ p ∈ P, p)

theorem jsp87Box_card (P : Finset ℕ) : (jsp87Box P).card = ∏ p ∈ P, p :=
  Finset.card_range _

theorem jsp87Box_mem {P : Finset ℕ} {n : ℕ} (hn : n ∈ jsp87Box P) : n < ∏ p ∈ P, p :=
  Finset.mem_range.mp hn

/-- **THE BOX IS NONEMPTY AND ITS SIZE IS AT LEAST `1`.** -/
theorem jsp87Box_one_le {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) : (1 : ℕ) ≤ ∏ p ∈ P, p :=
  Finset.one_le_prod (fun i _ => hP i ‹_›)

/-- **★★ THE CHINESE-REMAINDER SUM-FACTORIZATION ★★**

Let `f q i` be a `q`-periodic family (`f q (i mod q) = f q i`) indexed by a set
`S` of distinct primes.  Then

```
∑_{i < ∏_{q ∈ S} q} ∏_{q ∈ S} f q i  =  ∏_{q ∈ S} ( ∑_{m < q} f q m ) .
```

This is the sum form of the Chinese remainder theorem, and it is what makes
hypothesis (5.16)–(5.17) of arXiv:2512.01739 an *identity* on the box: the
expectations of the `X_p` factor exactly, with no error term at all.  The proof
is by induction on `S`; the step applies `jsp87sum_mod_mul` (a unit permutes
the residues) to the newly inserted prime. -/
private theorem jsp87sum_prod_finset_aux (f : ℕ → ℕ → ℂ) :
    ∀ (S : Finset ℕ), (∀ q' ∈ S, q'.Prime) → (∀ q' ∈ S, ∀ i : ℕ, f q' (i % q') = f q' i) →
      (∑ i ∈ Finset.range (∏ q' ∈ S, q'), ∏ q' ∈ S, f q' i)
        = ∏ q' ∈ S, (∑ m ∈ Finset.range q', f q' m) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | @insert q S hq ih =>
    intro hprim hper
    have hprimS : ∀ q' ∈ S, q'.Prime :=
      fun q' hq' => hprim q' (Finset.mem_insert_of_mem hq')
    have hperS : ∀ q' ∈ S, ∀ i : ℕ, f q' (i % q') = f q' i :=
      fun q' hq' i => hper q' (Finset.mem_insert_of_mem hq') i
    by_cases hS0 : S.Nonempty
    · obtain ⟨q0, hq0⟩ := hS0
      have hq0p : q0.Prime := hprimS q0 hq0
      have hcop : Nat.Coprime q (∏ q' ∈ S, q') := by
        refine Nat.Coprime.prod_right fun q' hq' => ?_
        exact (Nat.coprime_primes (hprim q (Finset.mem_insert_self q S))
          (hprimS q' hq')).2 (by
            intro heq
            subst heq
            exact hq hq')
      have hMpos : 0 < ∏ q' ∈ S, q' := by
        refine Finset.prod_pos fun q' hq' => ?_
        have hp : 2 ≤ q' := Nat.Prime.two_le (hprimS q' hq')
        omega
      have hih : (∑ i ∈ Finset.range (∏ q' ∈ S, q'), ∏ q' ∈ S, f q' i)
          = ∏ q' ∈ S, (∑ m ∈ Finset.range q', f q' m) :=
        ih hprimS hperS
      -- the integrand splits: the new prime sees `(s + a k) mod q`, the old
      -- ones see only `s`
      have hsplit : ∀ (s k : ℕ) (P : Finset ℕ) (a : ℕ)
          (hperP : ∀ q' ∈ insert q P, ∀ i : ℕ, f q' (i % q') = f q' i),
          (∀ q' ∈ P, q' ∣ a) → q ∉ P →
          (∏ q' ∈ insert q P, f q' (s + a * k))
            = f q ((s + a * k) % q) * ∏ q' ∈ P, f q' (s % q') := by
        intro s k P a hperP hdiv hqP
        have hqper : f q ((s + a * k) % q) = f q (s + a * k) :=
          hperP q (Finset.mem_insert_self q P) (s + a * k)
        have hP : (∏ q' ∈ P, f q' (s + a * k)) = ∏ q' ∈ P, f q' (s % q') := by
          refine Finset.prod_congr rfl fun q' hq' => ?_
          obtain ⟨w, hw⟩ := hdiv q' hq'
          have hdvd : q' ∣ a * k := by
            refine ⟨w * k, ?_⟩
            rw [hw]
            ring
          have hmod : (s + a * k) % q' = s % q' := jsp87mod_add_dvd hdvd
          calc f q' (s + a * k) = f q' ((s + a * k) % q') :=
              (hperP q' (Finset.mem_insert_of_mem hq') (s + a * k)).symm
            _ = f q' (s % q') := by rw [hmod]
        calc (∏ q' ∈ insert q P, f q' (s + a * k))
            = f q (s + a * k) * ∏ q' ∈ P, f q' (s + a * k) := by
              rw [Finset.prod_insert hqP]
          _ = f q ((s + a * k) % q) * ∏ q' ∈ P, f q' (s + a * k) := by rw [hqper]
          _ = f q ((s + a * k) % q) * ∏ q' ∈ P, f q' (s % q') := by rw [hP]
      -- the sum over the box, split by residue modulo `M' = ∏ S`
      have hsum : (∑ i ∈ Finset.range (q * (∏ q' ∈ S, q')), ∏ q' ∈ insert q S, f q' i)
          = (∑ m ∈ Finset.range q, f q m)
            * (∑ i ∈ Finset.range (∏ q' ∈ S, q'), ∏ q' ∈ S, f q' i) := by
        have hdiv : ∀ q' ∈ S, q' ∣ (∏ q'' ∈ S, q'') :=
          fun q' hq' => Finset.dvd_prod_of_mem id hq'
        have hg : (∑ i ∈ Finset.range (q * (∏ q' ∈ S, q')), ∏ q' ∈ insert q S, f q' i)
            = ∑ n ∈ Finset.range (q * (∏ q' ∈ S, q')), ∏ q' ∈ insert q S,
                f q' ((n % (∏ q' ∈ S, q')) + (∏ q' ∈ S, q') * (n / (∏ q' ∈ S, q'))) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have h1 : n % (∏ q' ∈ S, q') + (∏ q' ∈ S, q') * (n / (∏ q' ∈ S, q')) = n :=
            Nat.mod_add_div n _
          rw [h1]
        have hstep := jsp87sum_range_div q (∏ q' ∈ S, q')
          (fun k r => ∏ q' ∈ insert q S, f q' (r + (∏ q'' ∈ S, q'') * k))
        have hconv : (∑ y ∈ Finset.range (∏ q' ∈ S, q'), ∑ x ∈ Finset.range q,
                ∏ q' ∈ insert q S, f q' (y + (∏ q'' ∈ S, q'') * x))
            = ∑ i ∈ Finset.range (∏ q' ∈ S, q'), ∑ k ∈ Finset.range q,
                ∏ q' ∈ insert q S, f q' (i + (∏ q'' ∈ S, q'') * k) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          refine Finset.sum_congr rfl fun x hx => rfl
        have hinner : ∀ i : ℕ, i ∈ Finset.range (∏ q' ∈ S, q') →
            (∑ k ∈ Finset.range q, ∏ q' ∈ insert q S, f q' (i + (∏ q'' ∈ S, q'') * k))
              = (∑ m ∈ Finset.range q, f q m) * (∏ q' ∈ S, f q' i) := by
          intro i hi
          have hterm : ∀ k : ℕ,
              (∏ q' ∈ insert q S, f q' (i + (∏ q'' ∈ S, q'') * k))
                = f q ((i + (∏ q'' ∈ S, q'') * k) % q) * (∏ q' ∈ S, f q' i) := by
            intro k
            have hsplit' := hsplit i k S (∏ q'' ∈ S, q'') hper hdiv hq
            have hP2 : (∏ q' ∈ S, f q' (i % q')) = ∏ q' ∈ S, f q' i :=
              Finset.prod_congr rfl fun q' hq' => hper q' (Finset.mem_insert_of_mem hq') i
            rw [hsplit', hP2]
          -- `M'` is a unit mod `q`, so the new prime's residues are permuted
          have hstep' : (∑ k ∈ Finset.range q,
                f q ((i + (∏ q'' ∈ S, q'') * k) % q))
              = ∑ k ∈ Finset.range q, f q k :=
            jsp87sum_mod_mul (Nat.Prime.two_le (hprim q (Finset.mem_insert_self q S)))
              (by omega) hcop.symm (fun m => f q m)
          have h1 : (∑ k ∈ Finset.range q,
                ∏ q' ∈ insert q S, f q' (i + (∏ q'' ∈ S, q'') * k))
              = ∑ k ∈ Finset.range q, f q ((i + (∏ q'' ∈ S, q'') * k) % q)
                  * (∏ q' ∈ S, f q' i) :=
            Finset.sum_congr rfl fun k _ => hterm k
          have h2 : (∑ k ∈ Finset.range q, f q ((i + (∏ q'' ∈ S, q'') * k) % q))
                  * (∏ q' ∈ S, f q' i)
              = (∑ k ∈ Finset.range q, f q k) * (∏ q' ∈ S, f q' i) :=
            congrArg (fun z : ℂ => z * (∏ q' ∈ S, f q' i)) hstep'
          have h3 : (∑ k ∈ Finset.range q,
                  f q ((i + (∏ q'' ∈ S, q'') * k) % q) * (∏ q' ∈ S, f q' i))
              = ((∑ k ∈ Finset.range q, f q ((i + (∏ q'' ∈ S, q'') * k) % q)) : ℂ)
                  * (∏ q' ∈ S, f q' i) :=
            (Finset.sum_mul (Finset.range q)
              (fun m => f q ((i + (∏ q'' ∈ S, q'') * m) % q))
              ((∏ q' ∈ S, f q' i) : ℂ)).symm
          have h4 : ((∑ k ∈ Finset.range q, f q k) : ℂ) * (∏ q' ∈ S, f q' i)
              = ∑ k ∈ Finset.range q, f q k * (∏ q' ∈ S, f q' i) :=
            Finset.sum_mul _ _ _
          rw [h1, h3, h2, h4]
        rw [hg, hstep, Finset.sum_comm, hconv]
        refine (Finset.sum_congr rfl fun i hi => hinner i hi).trans ?_
        rw [Finset.mul_sum]
      rw [Finset.prod_insert hq, hsum, Finset.prod_insert hq, hih]
    · -- `S = ∅`: the box is `[0, q)` and the identity is trivial
      have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS0
      subst hS
      simp

theorem jsp87sum_prod_finset {S : Finset ℕ} (f : ℕ → ℕ → ℂ)
    (hprim : ∀ q' ∈ S, q'.Prime)
    (hper : ∀ q' ∈ S, ∀ i : ℕ, f q' (i % q') = f q' i) :
    (∑ i ∈ Finset.range (∏ q' ∈ S, q'), ∏ q' ∈ S, f q' i)
      = ∏ q' ∈ S, (∑ m ∈ Finset.range q', f q' m) :=
  jsp87sum_prod_finset_aux f S hprim hper

/-- **THE PRODUCT OF EXPONENTIALS IS THE EXPONENTIAL OF THE SUM** — the bridge
between the factorised form (which the Chinese remainder theorem produces) and
the total phase of (5.13). -/
private theorem jsp87prod_exp_total {P : Finset ℕ} (c : ℝ) (V : ℕ → ℝ) :
    (∏ p' ∈ P, jsp87e (c * V p')) = jsp87e (c * (∑ p' ∈ P, V p')) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    have hz : jsp87e 0 = 1 := by simp [jsp87e]
    simp [hz]
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp, Finset.sum_insert hp, ih, ← jsp87e_add]
    congr 1
    ring

/-- **★ THE TOTAL PHASE FACTORISES EXACTLY ON THE BOX ★**

For a finite set `P` of primes, the truncated mean of `e (q Σ_p X_p)` over the
box `B P = [0, ∏_{p ∈ P} p)` is **exactly** the product of the single-prime
means over `[0, p)`:

```
𝔼ᶜ_{n < M} e (i q ∑_{p ∈ P} X_p n)  =  ∏_{p ∈ P} 𝔼ᶜ_{m < p} e (i q X_p m) ,
    M = ∏_{p ∈ P} p .
```

**No error term.**  This is the content of hypothesis (5.16)–(5.17) of
arXiv:2512.01739 on the box: the product form of the truncated expectation is
an *identity* there, because the residues `(n mod p)_{p ∈ P}` are independent
on `[0, M)`.  It is proved from §0 (the Chinese remainder theorem, from scratch)
and §1 (the periodicity of `X_p`). -/
theorem jsp87CAvg_box_prod {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (K H : ℕ) (q : ℝ) :
    jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))
      = ∏ p ∈ P, jsp87CAvg (Finset.range p)
          (fun m => jsp87e (q * jsp87Xp0 (jsp87BinV K) p m H)) := by
  classical
  have hper : ∀ p' ∈ P, ∀ i : ℕ,
      jsp87e (q * jsp87Xp0 (jsp87BinV K) p' (i % p') H)
        = jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H) := by
    intro p' hp' i
    rw [(jsp87Xp0_mod (K := K) (v := jsp87BinV K) (p := p') (n := i) (H := H)).symm]
  have hcrt : (∑ i ∈ Finset.range (∏ q' ∈ P, q'),
        ∏ q' ∈ P, jsp87e (q * jsp87Xp0 (jsp87BinV K) q' i H))
      = ∏ q' ∈ P, (∑ m ∈ Finset.range q', jsp87e (q * jsp87Xp0 (jsp87BinV K) q' m H)) :=
    jsp87sum_prod_finset (fun p' i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H)) hP hper
  have hsum : (∑ n ∈ jsp87Box P, jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))
      = ∏ p' ∈ P, (∑ m ∈ Finset.range p',
          jsp87e (q * jsp87Xp0 (jsp87BinV K) p' m H)) := by
    have hre : ∀ n : ℕ, (∏ p' ∈ P, jsp87e (q * jsp87Xp0 (jsp87BinV K) p' n H))
        = jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)) := by
      intro n
      exact jsp87prod_exp_total q (fun p' => jsp87Xp0 (jsp87BinV K) p' n H)
    calc (∑ n ∈ jsp87Box P, jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))
        = ∑ n ∈ jsp87Box P, ∏ p' ∈ P, jsp87e (q * jsp87Xp0 (jsp87BinV K) p' n H) :=
          Finset.sum_congr rfl fun n hn => (hre n).symm
      _ = ∏ p' ∈ P, (∑ m ∈ Finset.range p',
          jsp87e (q * jsp87Xp0 (jsp87BinV K) p' m H)) := by
          have : jsp87Box P = Finset.range (∏ q' ∈ P, q') := rfl
          rw [this, hcrt]
  have hinv : ∀ (S : Finset ℕ) (f : ℕ → ℂ),
      (∏ i ∈ S, (f i)⁻¹) = (∏ i ∈ S, f i)⁻¹ := by
    classical
    intro S f
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, ih]
      field_simp
  have hcast : ((∏ p ∈ P, (p : ℕ) : ℂ)) = ((∏ p ∈ P, p : ℕ) : ℂ) := by push_cast; rfl
  simp only [jsp87CAvg, jsp87Box_card, Finset.card_range]
  rw [hsum]
  rw [div_eq_mul_inv]
  have hkey : ((↑(∏ p ∈ P, (p : ℕ)) : ℂ))⁻¹ = ∏ p ∈ P, ((p : ℕ) : ℂ)⁻¹ := by
    rw [hcast.symm]
    exact (hinv P (fun p => (p : ℂ))).symm
  rw [hkey]
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun p _ => by rw [← div_eq_mul_inv])]

/-- **THE BOX IS A WHOLE NUMBER OF PERIODS OF `p`.** -/
theorem jsp87Box_eq_range_mul {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPne : ∀ p ∈ P, 2 ≤ p) (p : ℕ) (hp : p ∈ P) :
    jsp87Box P = Finset.range (((∏ p' ∈ P, p') / p) * p) := by
  classical
  have hPd : p ∣ ∏ p' ∈ P, p' := Finset.dvd_prod_of_mem id hp
  have hp0 : 0 < p := by have := hPne p hp; omega
  obtain ⟨w, hw⟩ := hPd
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with hz | hz
    · exfalso
      have hz0 : (∏ p' ∈ P, p') = 0 := by rw [hw, hz]; simp
      have h1 : 0 < ∏ p' ∈ P, p' := by
        refine Finset.prod_pos fun p' hp' => ?_
        have hp' : 2 ≤ p' := Nat.Prime.two_le (hP p' hp')
        omega
      omega
    · exact hz
  have hdiv : (∏ p' ∈ P, p') / p = w := by
    rw [hw, Nat.mul_div_right w hp0]
  have hM : ((∏ p' ∈ P, p') / p) * p = ∏ p' ∈ P, p' := by
    rw [hdiv, Nat.mul_comm w p, hw]
  rw [jsp87Box, hM]

/-- **THE MEAN OF THE SINGLE-PRIME PHASE ON THE BOX IS ITS MEAN ON ONE PERIOD.** -/
theorem jsp87CAvg_box_eq_period {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPne : ∀ p ∈ P, 2 ≤ p) (K H : ℕ) (p : ℕ) (hp : p ∈ P) (q : ℝ) :
    jsp87CAvg (jsp87Box P) (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))
      = jsp87CAvg (Finset.range p) (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) := by
  classical
  have hPd : p ∣ ∏ p' ∈ P, p' := Finset.dvd_prod_of_mem id hp
  have hp0 : 0 < p := by have := hPne p hp; omega
  obtain ⟨w, hw⟩ := hPd
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with hz | hz
    · exfalso
      have hz0 : (∏ p' ∈ P, p') = 0 := by rw [hw, hz]; simp
      have h1 : 0 < ∏ p' ∈ P, p' := by
        refine Finset.prod_pos fun p' hp' => ?_
        have hp' : 2 ≤ p' := Nat.Prime.two_le (hP p' hp')
        omega
      omega
    · exact hz
  have hdiv : (∏ p' ∈ P, p') / p = w := by
    rw [hw, Nat.mul_div_right w hp0]
  rw [jsp87Box_eq_range_mul hP hPne p hp]
  exact jsp87CAvg_Xp_period (K := K) q p ((∏ p' ∈ P, p') / p) H hp0
    (by rw [hdiv]; exact Nat.succ_le_of_lt hwpos)

/-- **THE VARIANCE OF A SINGLE `X_p` ON THE BOX IS ITS VARIANCE ON ONE PERIOD.**
Combining §2 with `p ∣ ∏_{p' ∈ P} p'`: the box is a whole number of periods
of `p`, so every statistic of the endgame that a single prime contributes is
independent of the box. -/
theorem jsp87Var_box_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPne : ∀ p ∈ P, 2 ≤ p) (q : ℝ) (K H : ℕ) (p : ℕ) (hp : p ∈ P) :
    jsp87Var (jsp87Box P) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H)
      = jsp87Var (Finset.range p) (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  classical
  have hPd : p ∣ ∏ p' ∈ P, p' := Finset.dvd_prod_of_mem id hp
  have hp0 : 0 < p := by have := hPne p hp; omega
  obtain ⟨w, hw⟩ := hPd
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with hz | hz
    · exfalso
      have hz0 : (∏ p' ∈ P, p') = 0 := by rw [hw, hz]; simp
      have h1 : 0 < ∏ p' ∈ P, p' := by
        refine Finset.prod_pos fun p' hp' => ?_
        have hp' : 2 ≤ p' := Nat.Prime.two_le (hP p' hp')
        omega
      omega
    · exact hz
  have hdiv : (∏ p' ∈ P, p') / p = w := by
    rw [hw, Nat.mul_div_right w hp0]
  rw [jsp87Box_eq_range_mul hP hPne p hp]
  exact jsp87Var_Xp_period (K := K) q p ((∏ p' ∈ P, p') / p) H hp0
    (by rw [hdiv]; exact Nat.succ_le_of_lt hwpos)

/-! ## §4  THE ENDGAME CANNOT RUN ON A BOX: (5.15) IS REFUTED -/

/-- **THE NORM OF A PRODUCT.** -/
private theorem jsp87norm_prod_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∏ i ∈ s, z i‖ ≤ ∏ i ∈ s, ‖z i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    calc ‖z i * ∏ j ∈ s, z j‖ = ‖z i‖ * ‖∏ j ∈ s, z j‖ := Complex.norm_mul _ _
      _ ≤ ‖z i‖ * ∏ j ∈ s, ‖z j‖ := by
          refine mul_le_mul_of_nonneg_left ih (norm_nonneg _)

/-- **★★★ (5.15) IS REFUTED ON EVERY BOX ★★★**

Let `P` be a finite set of primes, all of them at least `2(H + 2^K − 1)`, let
`B = H + 2^K − 1`, and suppose the phase is admissible, `|q| H 2^{-K} ≤ 1/20`.
On the box `B P` of §3,

```
1 − exp( −4 q² 2^K 2^{−2(H+K)} ∑_{p ∈ P} 1/p )  ≤  ‖𝔼ᶜ_{n < M} e (q ∑_{p ∈ P} X_p) − 1‖ ,
    M = ∏_{p ∈ P} p .
```

**Consequence.**  For `P = jsp87PrimeSet (2B) Y` the harmonic mass on the right
diverges with `Y` (Euler, `jsp87RecipSum_primeSet_tendsto`), so the left side
tends to `1`: **the concentration hypothesis (5.15) of arXiv:2512.01739 fails
on every box at all large heights, for every admissible `q ≠ 0`.**

The chain is: §3 makes the mean a *product* of single-prime means; the
single-prime variances are `Θ(1/p)` (round 140's `jsp87Var_Xp_res_sharp`),
and the phase bound (5.19) turns each factor into `exp(−8 Var)`
(`jsp87_prod_charfun_le`).  So the endgame of §§5.3–5.14 **cannot be started on
a box**: a rationality-driven configuration must be a correlated sample, which
is the content of the one remaining blocker `jsp87Mcov_small`. -/
theorem jsp87_515_box_le {P : Finset ℕ} (K H : ℕ) (hP : ∀ p ∈ P, p.Prime) (hH : 1 ≤ H)
    (hPsep : ∀ p ∈ P, 2 * (H + 2 ^ K - 1) ≤ p) (q : ℝ)
    (hone : ∀ p ∈ P, ∀ n : ℕ, ∀ h ∈ Finset.Icc 1 H,
      jsp87OneVertex p n (jsp87BinV K) h)
    (hq : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    1 - Real.exp (-(4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * jsp87RecipSum P)
      ≤ ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))) - 1‖ := by
  classical
  set c : ℝ := (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) with hc
  -- THE MEAN IS A PRODUCT OF SINGLE-PRIME MEANS (§3)
  have hbox : jsp87CAvg (jsp87Box P)
      (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))
      = ∏ p ∈ P, jsp87CAvg (Finset.range p)
          (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H)) :=
    jsp87CAvg_box_prod hP K H q
  -- THE POINTWISE PHASE BOUND (5.19) FOR EVERY SINGLE PRIME
  have hT : ∀ p ∈ P, ∀ i : ℕ,
      |q * jsp87Xp0 (jsp87BinV K) p i H| ≤ 1 / 20 := by
    intro p hp i
    exact jsp87Xp0_abs_le_twenty q (jsp87BinV K) p i H (hone p hp i) hq
  have hne : (jsp87Box P).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    have h1 : 0 < ∏ p ∈ P, p := by
      refine Finset.prod_pos fun p hp => ?_
      have hp' : 2 ≤ p := Nat.Prime.two_le (hP p hp)
      omega
    omega
  -- THE PRODUCT OF THE SINGLE-PRIME NORMS IS AT MOST `exp (−8 Σ Var)`
  have hprod := jsp87_prod_charfun_le (s := jsp87Box P) hne q
    (fun p i => jsp87Xp0 (jsp87BinV K) p i H) hT
  have hnorm : ∀ p ∈ P,
      ‖jsp87CAvg (Finset.range p) (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖
        = ‖jsp87CAvg (jsp87Box P) (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖ := by
    intro p hp
    rw [jsp87CAvg_box_eq_period hP (fun p' hp' => Nat.Prime.two_le (hP p' hp')) K H p hp q]
  -- EACH SINGLE-PRIME VARIANCE IS `c / (2 p)`
  have hvar : ∀ p ∈ P,
      c / (2 * (p : ℕ)) ≤ jsp87Var (Finset.range p)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) := by
    intro p hp
    have h1 := jsp87Var_Xp_res_sharp (K := K) (p := p) (H := H) hH (hPsep p hp) q
    rw [hc]
    exact h1
  have hsum : (∑ p ∈ P, jsp87Var (jsp87Box P)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H))
      = ∑ p ∈ P, jsp87Var (Finset.range p)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact jsp87Var_box_eq hP (fun p' hp' => Nat.Prime.two_le (hP p' hp')) q K H p hp
  have hlow : c / 2 * jsp87RecipSum P
      ≤ ∑ p ∈ P, jsp87Var (jsp87Box P)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) := by
    have hL : (c / 2) * jsp87RecipSum P = ∑ p' ∈ P, (c / 2) * (1 / (p' : ℝ)) := by
      rw [jsp87RecipSum]
      exact Finset.mul_sum _ _ _
    rw [hsum, hL]
    refine Finset.sum_le_sum fun p hp => ?_
    have h1 := hvar p hp
    have hp2 : 2 ≤ p := Nat.Prime.two_le (hP p hp)
    have hp0 : (0 : ℕ) < p := by omega
    have hc1 : (0 : ℝ) < 2 := by norm_num
    have hc2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have h3 : c / 2 * (1 / (p : ℝ)) = c / (2 * (p : ℕ)) := by field_simp
    rw [h3]
    have h6 : c ≤ jsp87Var (Finset.range p)
        (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) * (2 * (p : ℕ)) :=
      (div_le_iff₀ (mul_pos hc1 hc2)).1 h1
    linarith
  -- THE MEAN IS SMALL
  have hexp : ‖jsp87CAvg (jsp87Box P)
      (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
      ≤ Real.exp (-(8 : ℝ) * (c / 2 * jsp87RecipSum P)) := by
    calc ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
        = ‖∏ p ∈ P, jsp87CAvg (Finset.range p)
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖ := by rw [hbox]
      _ ≤ ∏ p ∈ P, ‖jsp87CAvg (Finset.range p)
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖ :=
          jsp87norm_prod_le _ _
      _ = ∏ p ∈ P, ‖jsp87CAvg (jsp87Box P)
            (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p i H))‖ := by
          apply Finset.prod_congr rfl
          intro p hp
          exact hnorm p hp
      _ ≤ Real.exp (-(8 : ℝ) * (∑ p ∈ P, jsp87Var (jsp87Box P)
            (fun i => q * jsp87Xp0 (jsp87BinV K) p i H))) := hprod
      _ ≤ Real.exp (-(8 : ℝ) * (c / 2 * jsp87RecipSum P)) := by
          apply Real.exp_le_exp.mpr
          have hmul := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 8)
          linarith
  -- THE MEAN IS FAR FROM `1`
  have hdist : 1 - Real.exp (-(8 : ℝ) * (c / 2 * jsp87RecipSum P))
      ≤ ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))) - 1‖ := by
    have h1 : ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
        ≤ Real.exp (-(8 : ℝ) * (c / 2 * jsp87RecipSum P)) := hexp
    have htri : ‖(1 : ℂ) - jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
          + ‖jsp87CAvg (jsp87Box P)
            (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
        ≥ ‖(1 : ℂ)‖ := by
      have h5 := norm_add_le ((1 : ℂ) - jsp87CAvg (jsp87Box P)
        (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))))
        (jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))))
      rw [sub_add_cancel] at h5
      linarith
    have h4 : (1 : ℝ) = ‖(1 : ℂ)‖ := (norm_one : ‖(1 : ℂ)‖ = 1).symm
    have h2 : (1 : ℝ) - ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
        ≤ ‖(1 : ℂ) - jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖ := by
      linarith
    have h3 : ‖(1 : ℂ) - jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H)))‖
        = ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))) - 1‖ := by
      rw [norm_sub_rev]
    linarith
  -- ASSEMBLE: `8 · (c / 2) = 4 · c`
  have hfinal : 1 - Real.exp (-(4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K)
        * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * jsp87RecipSum P)
      ≤ ‖jsp87CAvg (jsp87Box P)
          (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))) - 1‖ := by
    have h8 : (8 : ℝ) * (c / 2 * jsp87RecipSum P)
        = 4 * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * jsp87RecipSum P := by
      simp only [hc]
      ring
    calc 1 - Real.exp (-(4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K)
            * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * jsp87RecipSum P)
        = 1 - Real.exp (-(8 : ℝ) * (c / 2 * jsp87RecipSum P)) := by
          have hx : -(4 : ℝ) * (q ^ 2) * ((2 : ℝ) ^ K) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
              * jsp87RecipSum P = -(8 : ℝ) * (c / 2 * jsp87RecipSum P) := by linarith [h8]
          rw [hx]
      _ ≤ ‖jsp87CAvg (jsp87Box P)
            (fun n => jsp87e (q * (∑ p' ∈ P, jsp87Xp0 (jsp87BinV K) p' n H))) - 1‖ :=
        hdist
  exact hfinal

end JSP87
