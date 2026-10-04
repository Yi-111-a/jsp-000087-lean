/-
Copyright (c) 2026. Released under Apache 2.0.
Authors: JSP-000087 formalization (Yi-117).
-/
import JSPProblem.ActiveCube

/-!
# JSP-000087, round 122 — THE CORRELATED-SAMPLE OBJECT, AND THE `S₁`-VARIANCE
IN SAMPLE GEOMETRY

## Why this file exists

Round 120 proved, as **machine-checked negative knowledge**, that hypothesis
(5.21) of arXiv:2512.01739

```
(5.21)   1 ≤ ∑_{p ∈ S₁} Var (q X_p)
```

is **never satisfiable by a uniform residue system**: `jsp87_Xp_res_5_21_impossible`
concludes `¬ (1 ≤ Var (Icc 0 (p-1)) (fun n => q * X_p n))` from (5.19) alone,
because (5.19) puts every value of `q X_p` in `[−1/20, 1/20]`.  The remaining
burden of `jsp_000087_main` was therefore localised to the **structure of the
sample**, and `policy.json` `next_round_attack[0]` asked for exactly one object:

> "Define … the sample-weighted hit count … Make explicit the ONE quantity that
> (5.21) needs, namely a sample whose active-class fraction is `≥ 1/q²` — and
> show that this fraction is at most `2^K / p` for a uniform sample … while it is
> unknown for a correlated one."

**This file builds that object.**  The quantity (5.21) needs is not the *level-1
active* fraction but the **nonzero fraction**

```
jsp87NzFrac K p H s  =  #{ n ∈ s : X_p n ≠ 0 } / #{ n ∈ s }
```

— the fraction of the sample at which the cube sum is *not* the zero function.
This is the quantity that enters the two-class variance criterion of
`VarLocal.lean` §6, and this file proves

* **the criterion in fraction form** — `jsp87Var_Xp_ge_nzFrac`,
  `jsp87Var_sum_ge_nzFrac`, and **THE ENDGAME**
  `jsp87_endgame_frac_of_5_21`, in which hypothesis (5.21) is *replaced* by a
  purely sample-geometric inequality (5.21′);
* **the fraction is a residue statistic** — `jsp87Active_iff_of_mod`,
  `jsp87Active_add`, `jsp87res_cover_iff`, `jsp87ActFrac_trans`,
  `jsp87ActFrac_union`; the sample's residue profile alone determines it;
* **TWO IMPOSSIBILITY THEOREMS** — `jsp87_5_21_singleRes_impossible` and
  `jsp87_5_21_prog_impossible`: **no sample confined to one residue class modulo
  `p`, and in particular no arithmetic progression whose step is divisible by every
  `p ∈ S₁`, can supply (5.21′)**;
* **and the quantitative necessity of MANY PRIMES** —
  `jsp87_5_21_needs_card` and `jsp87_5_21_needs_manyPrimes`: (5.21′) forces
  `4^{H+K+1} ≤ q² |S₁|`, and *combined with (5.19)* it forces

```
1600 · 4^H · H²  ≤  |S₁| ,
```

independently of `q` and of the cube dimension `K`.

## What is *not* proved here

`jsp_000087_main` is **not declared**.  The estimate that a *correlated* sample
really does have a large nonzero fraction is the content of arXiv:2512.01739
`Theorem 3.1` (a quantitative two-point correlation estimate for `ω`, from
Pilatte's work); Mathlib contains no Chowla-type or Elliott-type statement for
multiplicative functions, so it cannot be supplied here.  What this round adds
is that (5.21) is a **geometric** condition on the sample, with the sharp
necessity bounds above.
-/

namespace JSP87

open Finset

set_option maxHeartbeats 1000000

/-! ## §0  Congruence transfer -/

/-- **AN EMPTY FINSET HAS NO MEMBERS.** -/
private theorem jsp87not_mem_of_eq_empty {α : Type*} {s : Finset α} {a : α} (he : s = ∅)
    (h : a ∈ s) : False := by
  rw [he] at h
  simp at h

/-- **SUBTRACTING A MULTIPLE OF `p` FROM A MULTIPLE OF `p` GIVES A MULTIPLE OF
`p`.**  This is the arithmetic behind `p ∣ t` and `p ∣ (t + c) ⟹ p ∣ c`. -/
private theorem jsp87dvd_of_dvd_add {p m k : ℕ} (hm : p ∣ m) (hk : p ∣ m + k) : p ∣ k := by
  have h1 := Nat.dvd_iff_mod_eq_zero.mp hk
  have h2 := Nat.dvd_iff_mod_eq_zero.mp hm
  have h3 : (m + k) % p = (m % p + k % p) % p := Nat.add_mod m k p
  rw [h1, h2] at h3
  have h4 : k % p = 0 := by
    rw [Nat.zero_add, Nat.mod_mod] at h3
    exact h3.symm
  exact Nat.dvd_iff_mod_eq_zero.mpr h4

/-- **DIVISIBILITY BY `p` OF `(a % p) + c` IMPLIES DIVISIBILITY OF `a + c`.** -/
private theorem jsp87dvd_of_mod {p a c : ℕ} (hd : p ∣ (a % p) + c) : p ∣ a + c := by
  obtain ⟨m, hm⟩ := hd
  refine ⟨m + a / p, ?_⟩
  calc a + c = (p * (a / p) + a % p) + c := by rw [Nat.div_add_mod a p]
    _ = p * (a / p) + (a % p + c) := by omega
    _ = p * (a / p) + p * m := by rw [hm]
    _ = p * (m + a / p) := by ring

/-- **ACTIVITY IS INVARIANT UNDER A SHIFT BY A MULTIPLE OF `p`.**  In words: the
hit set of the cube at level `h` is a union of residue classes modulo `p`. -/
theorem jsp87Active_add {K p h n t : ℕ} (ht : p ∣ t) :
    jsp87Active K p h (n + t) ↔ jsp87Active K p h n := by
  obtain ⟨k, hk⟩ := ht
  constructor
  · rintro ⟨ε, c, hmem⟩
    rw [jsp87R_binV] at hmem
    have hmem' : t + (n + jsp87Off (jsp87BinV K) ε + h) = p * c := by
      calc t + (n + jsp87Off (jsp87BinV K) ε + h)
          = n + t + (h + jsp87Off (jsp87BinV K) ε) := by omega
        _ = p * c := hmem
    have hsub : p ∣ n + jsp87Off (jsp87BinV K) ε + h :=
      jsp87dvd_of_dvd_add ⟨k, hk⟩ ⟨c, hmem'⟩
    obtain ⟨c', hc'⟩ := hsub
    refine ⟨ε, c', ?_⟩
    rw [jsp87R_binV]
    omega
  · rintro ⟨ε, c, hmem⟩
    rw [jsp87R_binV] at hmem
    refine ⟨ε, c + k, ?_⟩
    calc (n + t) + (h + jsp87Off (jsp87BinV K) ε)
        = (n + (h + jsp87Off (jsp87BinV K) ε)) + t := by omega
      _ = p * c + t := by rw [hmem]
      _ = p * c + p * k := by rw [hk]
      _ = p * (c + k) := by ring

/-- **ACTIVITY IS A FUNCTION OF THE RESIDUE OF THE SAMPLE POINT ALONE.** -/
theorem jsp87Active_of_res {K p h n : ℕ} :
    jsp87Active K p h n ↔ jsp87Active K p h (n % p) := by
  have ht : p ∣ p * (n / p) := ⟨n / p, by ring⟩
  have hiff := jsp87Active_add (K := K) (p := p) (h := h) (n := n % p) ht
  have heq : (n % p) + p * (n / p) = n := by
    have h1 := Nat.div_add_mod n p
    omega
  have hEq : jsp87Active K p h ((n % p) + p * (n / p)) = jsp87Active K p h n :=
    congrArg (fun m : ℕ => jsp87Active K p h m) heq
  exact (Iff.of_eq hEq.symm).trans hiff

/-- **ACTIVITY DEPENDS ONLY ON THE RESIDUE OF THE SAMPLE POINT.**  This is the
bridge from `jsp87Active` to a *sample* statistic: two sample points congruent
modulo `p` hit the same vertices of the cube. -/
theorem jsp87Active_iff_of_mod {K p h n r : ℕ} (hm : n % p = r % p) :
    jsp87Active K p h n ↔ jsp87Active K p h r := by
  rw [jsp87Active_of_res, hm]
  exact (jsp87Active_of_res (K := K) (p := p) (h := h) (n := r)).symm

/-- **THE CUBE SUM REDUCES TO THE RESIDUE.** -/
private theorem jsp87Xp0_mod_eq {K p H : ℕ} (v : Fin K → ℕ) (n : ℕ) :
    jsp87Xp0 v p n H = jsp87Xp0 v p (n % p) H := by
  have hiter : ∀ c c₀ : ℕ, jsp87Xp0 v p (p * c + c₀) H = jsp87Xp0 v p c₀ H := by
    intro c
    induction c with
    | zero =>
        intro c₀
        simp only [Nat.mul_zero, Nat.zero_add]
    | succ c ih =>
        intro c₀
        have heq : p * (c + 1) + c₀ = (p * c + c₀) + p := by ring
        rw [heq, jsp87Xp0_period, ih]
  have hn : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  have hA : jsp87Xp0 v p n H = jsp87Xp0 v p (p * (n / p) + n % p) H :=
    congrArg (fun m : ℕ => jsp87Xp0 v p m H) hn
  rw [hA]
  exact hiter (n / p) (n % p)

/-- **CONGRUENT SAMPLE POINTS GIVE THE SAME CUBE SUM** — the `jsp87Xp0` analogue
of `jsp87Active_iff_of_mod`, and the reason the *value* of `X_p` is a residue
statistic too. -/
theorem jsp87Xp0_eq_of_res {K p H : ℕ} (v : Fin K → ℕ) {n r : ℕ} (hm : n % p = r % p) :
    jsp87Xp0 v p n H = jsp87Xp0 v p r H := by
  calc jsp87Xp0 v p n H = jsp87Xp0 v p (n % p) H := jsp87Xp0_mod_eq (p := p) (H := H) v n
    _ = jsp87Xp0 v p (r % p) H := by rw [hm]
    _ = jsp87Xp0 v p r H := (jsp87Xp0_mod_eq (p := p) (H := H) v r).symm

/-! ## §1  The correlated-sample objects -/

/-- **THE ACTIVE PART OF THE SAMPLE** at level `h` for the prime `p`. -/
def jsp87ActRes (K p h : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.filter (fun n => jsp87Active K p h n)

attribute [reducible] jsp87ActRes

/-- **THE ACTIVE-CLASS FRACTION**: the fraction of the sample lying in an active
residue class modulo `p`.  This is the quantity `policy.json`
`next_round_attack[0]` asks for; round 120 computed it for the complete residue
system (`2^K / p`, `jsp87Active_density`) and proved there that (5.21) is then
impossible.  Here it is an object for an *arbitrary* sample. -/
noncomputable def jsp87ActFrac (K p h : ℕ) (s : Finset ℕ) : ℝ :=
  ((jsp87ActRes K p h s).card : ℕ) / ((s.card : ℕ) : ℝ)

/-- **THE NONZERO PART OF THE SAMPLE**: the sample points at which the cube sum
`X_p` of (5.13) is nonzero. -/
noncomputable def jsp87NzRes (K p H : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.filter (fun n => jsp87Xp0 (jsp87BinV K) p n H ≠ 0)

/-- **THE ZERO PART OF THE SAMPLE**: the sample points at which the cube sum
`X_p` vanishes. -/
noncomputable def jsp87ZeroRes (K p H : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.filter (fun n => jsp87Xp0 (jsp87BinV K) p n H = 0)

attribute [reducible] jsp87NzRes jsp87ZeroRes

/-- **THE NONZERO-CLASS FRACTION** — the fraction of the sample at which `X_p` is
nonzero.  This, and not the level-1 active fraction, is the quantity that enters
the two-class variance criterion of `VarLocal.lean` §6. -/
noncomputable def jsp87NzFrac (K p H : ℕ) (s : Finset ℕ) : ℝ :=
  ((jsp87NzRes K p H s).card : ℕ) / ((s.card : ℕ) : ℝ)

/-! ## §2  The active fraction is a residue statistic -/

private theorem jsp87ActRes_sub {K p h : ℕ} (s : Finset ℕ) :
    jsp87ActRes K p h s ⊆ s := Finset.filter_subset _ _

theorem jsp87ActFrac_nonneg {K p h : ℕ} (s : Finset ℕ) : 0 ≤ jsp87ActFrac K p h s := by
  unfold jsp87ActFrac
  positivity

theorem jsp87ActFrac_le_one {K p h : ℕ} {s : Finset ℕ} (hs : s.Nonempty) :
    jsp87ActFrac K p h s ≤ 1 := by
  unfold jsp87ActFrac
  have h0 : 0 < ((s.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [div_le_one h0]
  have h1 : (jsp87ActRes K p h s).card ≤ s.card :=
    Finset.card_le_card (jsp87ActRes_sub s)
  exact_mod_cast h1

/-- **ACTIVITY AT THE SAMPLE POINT IS MEMBERSHIP OF THE ACTIVE PART.** -/
theorem jsp87mem_actRes {K p h n : ℕ} {s : Finset ℕ} (hn : n ∈ s) :
    jsp87Active K p h n ↔ n ∈ jsp87ActRes K p h s := by
  simp [jsp87ActRes, hn]

/-- **AN ACTIVE RESIDUE CLASS MAKES EVERY POINT IN IT ACTIVE.** -/
theorem jsp87Active_of_res_cover {K p h n : ℕ} (hp : 0 < p) (h1 : 1 ≤ h)
    (hh : h + 2 ^ K - 1 < p) (hcov : (n % p) ∈ jsp87ActiveRes K p h) :
    jsp87Active K p h n := by
  rw [jsp87ActiveRes, Finset.mem_image] at hcov
  obtain ⟨ε, _, hEq⟩ := hcov
  have hb : h + jsp87Off (jsp87BinV K) ε ≤ p - 1 := by
    have := jsp87Off_binV_lt ε
    omega
  have hmod : p - (h + jsp87Off (jsp87BinV K) ε) = n % p := hEq
  have hpt : (h + jsp87Off (jsp87BinV K) ε) ≤ p := by omega
  have h1' : (n % p) + (h + jsp87Off (jsp87BinV K) ε) = p := by
    rw [← hmod, Nat.sub_add_cancel hpt]
  refine ⟨ε, ?_⟩
  rw [jsp87R_binV]
  exact jsp87dvd_of_mod (a := n) (c := h + jsp87Off (jsp87BinV K) ε) ⟨1, by omega⟩

/-- **AN ACTIVE SAMPLE POINT LIES IN AN ACTIVE RESIDUE CLASS.** -/
theorem jsp87Active_mem_res {K p h n : ℕ} (hp : 0 < p) (h1 : 1 ≤ h)
    (hh : h + 2 ^ K - 1 < p) (hact : jsp87Active K p h n) :
    (n % p) ∈ jsp87ActiveRes K p h := by
  rw [jsp87Active_of_res] at hact
  have hlt : n % p < p := Nat.mod_lt _ hp
  exact (jsp87Active_iff_activeRes h1 hp (by omega) hh).mp hact

/-- **ACTIVITY IS DETECTED BY THE ACTIVE RESIDUE CLASSES.**  This is the bridge
between the *hit* definition (round 117) and the *residue* counting (round 120). -/
theorem jsp87res_cover_iff {K p h n : ℕ} (hp : 0 < p) (h1 : 1 ≤ h)
    (hh : h + 2 ^ K - 1 < p) :
    jsp87Active K p h n ↔ (n % p) ∈ jsp87ActiveRes K p h :=
  ⟨jsp87Active_mem_res hp h1 hh, jsp87Active_of_res_cover hp h1 hh⟩

/-- **THE ACTIVE FRACTION IS `1` WHEN EVERY SAMPLE POINT LIES IN AN ACTIVE
RESIDUE CLASS.**  Together with `jsp87ActFrac_eq_zero_of_res_avoid` this says the
fraction is a function of the residue profile of the sample alone. -/
theorem jsp87ActFrac_eq_one_of_res_cover {K p h : ℕ} (hp : 0 < p) (h1 : 1 ≤ h)
    (hh : h + 2 ^ K - 1 < p) (s : Finset ℕ) (hs : s.Nonempty)
    (hcov : ∀ n ∈ s, (n % p) ∈ jsp87ActiveRes K p h) :
    jsp87ActFrac K p h s = 1 := by
  have hset : jsp87ActRes K p h s = s := by
    ext n
    constructor
    · intro hn
      exact jsp87ActRes_sub s hn
    · intro hn
      rw [jsp87ActRes, Finset.mem_filter]
      exact ⟨hn, jsp87Active_of_res_cover hp h1 hh (hcov n hn)⟩
  unfold jsp87ActFrac
  rw [hset]
  exact div_self (ne_of_gt (by exact_mod_cast Finset.card_pos.mpr hs))

/-- **THE ACTIVE FRACTION IS `0` WHEN NO SAMPLE POINT LIES IN AN ACTIVE RESIDUE
CLASS.** -/
theorem jsp87ActFrac_eq_zero_of_res_avoid {K p h : ℕ} (hp : 0 < p) (h1 : 1 ≤ h)
    (hh : h + 2 ^ K - 1 < p) (s : Finset ℕ)
    (hav : ∀ n ∈ s, (n % p) ∉ jsp87ActiveRes K p h) :
    jsp87ActFrac K p h s = 0 := by
  have hset : jsp87ActRes K p h s = ∅ := by
    ext n
    constructor
    · intro hn
      have hn' := Finset.mem_filter.mp hn
      have hfalse : False :=
        absurd ((jsp87res_cover_iff hp h1 hh).mp hn'.2)
          (hav n (jsp87ActRes_sub s hn))
      exact hfalse.elim
    · intro hn
      have hfalse : False := by simp at hn
      exact hfalse.elim
  unfold jsp87ActFrac
  rw [hset]
  simp

/-- **THE ACTIVE FRACTION ONLY SEES THE RESIDUE CLASSES.**  Shifting the sample by
a multiple of `p` leaves the fraction unchanged. -/
theorem jsp87ActFrac_trans {K p h : ℕ} (s : Finset ℕ) (t : ℕ) (ht : p ∣ t) :
    jsp87ActFrac K p h (s.image (fun n => n + t)) = jsp87ActFrac K p h s := by
  have hset : (s.image (fun n => n + t)).filter (fun n => jsp87Active K p h n)
      = (s.filter (fun n => jsp87Active K p h n)).image (fun n => n + t) := by
    rw [Finset.filter_image]
    apply congrArg (fun g : Finset ℕ => g.image (fun n => n + t))
    refine Finset.filter_congr ?_
    intro n _
    exact jsp87Active_add (K := K) (p := p) (h := h) (n := n) ht
  have hcard : ((s.image (fun n => n + t)).filter
        (fun n => jsp87Active K p h n)).card
      = (s.filter (fun n => jsp87Active K p h n)).card := by
    rw [hset]
    exact Finset.card_image_iff.mpr fun a ha b hb hab => by omega
  have hcardS : (s.image (fun n => n + t)).card = s.card :=
    Finset.card_image_of_injective _ fun a b hab => by omega
  unfold jsp87ActFrac jsp87ActRes
  rw [hcard, hcardS]

/-- **THE ACTIVE FRACTION OF A DISJOINT UNION IS THE SIZE-WEIGHTED AVERAGE.**
Spreading a sample over more residue classes interpolates between the two
fractions. -/
theorem jsp87ActFrac_union {K p h : ℕ} {s t : Finset ℕ} (hs : s.Nonempty) (ht : t.Nonempty)
    (hdis : ∀ a, a ∈ s → a ∈ t → False) :
    (((jsp87ActRes K p h (s ∪ t)).card : ℕ) : ℝ)
      = ((s.card : ℕ) : ℝ) * jsp87ActFrac K p h s
        + ((t.card : ℕ) : ℝ) * jsp87ActFrac K p h t := by
  have hdisR : Disjoint (jsp87ActRes K p h s) (jsp87ActRes K p h t) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    exact hdis a ha'.1 hb'.1
  have hsetU : jsp87ActRes K p h (s ∪ t)
      = jsp87ActRes K p h s ∪ jsp87ActRes K p h t := by
    ext n
    simp only [jsp87ActRes, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨(h | h), hact⟩
      · exact Or.inl ⟨h, hact⟩
      · exact Or.inr ⟨h, hact⟩
    · intro h
      rcases h with h | h
      · exact ⟨Or.inl h.1, h.2⟩
      · exact ⟨Or.inr h.1, h.2⟩
  have hcardU : ((jsp87ActRes K p h (s ∪ t)).card : ℕ)
      = (jsp87ActRes K p h s).card + (jsp87ActRes K p h t).card := by
    rw [hsetU]
    exact Finset.card_union_of_disjoint hdisR
  have hsc : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have htc : ((t.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ht
  have hcasts : ((jsp87ActRes K p h s).card + (jsp87ActRes K p h t).card : ℕ)
      = ((jsp87ActRes K p h s).card : ℕ) + ((jsp87ActRes K p h t).card : ℕ) := by
    omega
  unfold jsp87ActFrac
  rw [hcardU]
  calc (((jsp87ActRes K p h s).card + (jsp87ActRes K p h t).card : ℕ) : ℝ)
      = ((jsp87ActRes K p h s).card : ℕ) * (((s.card : ℕ) : ℝ) / ((s.card : ℕ) : ℝ))
          + (((jsp87ActRes K p h t).card : ℕ) / ((t.card : ℕ) : ℝ))
            * ((t.card : ℕ) : ℝ) := by
        rw [hcasts, Nat.cast_add]
        field_simp [hsc, htc]
    _ = ((s.card : ℕ) : ℝ) * (((jsp87ActRes K p h s).card : ℕ) / ((s.card : ℕ) : ℝ))
        + ((t.card : ℕ) : ℝ) * (((jsp87ActRes K p h t).card : ℕ) / ((t.card : ℕ) : ℝ)) := by
        field_simp [hsc, htc]

/-! ## §3  The two-class criterion in fraction form -/

theorem jsp87NzZero_union {K p H : ℕ} (s : Finset ℕ) :
    jsp87NzRes K p H s ∪ jsp87ZeroRes K p H s = s := by
  ext n
  simp only [Finset.mem_union]
  constructor
  · intro h
    rcases h with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  · intro hn
    by_cases hz : jsp87Xp0 (jsp87BinV K) p n H = 0
    · exact Or.inr (by rw [Finset.mem_filter]; exact ⟨hn, hz⟩)
    · exact Or.inl (by rw [Finset.mem_filter]; exact ⟨hn, hz⟩)

theorem jsp87NzZero_inter {K p H : ℕ} (s : Finset ℕ) :
    jsp87NzRes K p H s ∩ jsp87ZeroRes K p H s = ∅ := by
  ext n
  constructor
  · intro h
    have hh := Finset.mem_inter.mp h
    have h1 := (Finset.mem_filter.mp hh.1).2
    have h2 := (Finset.mem_filter.mp hh.2).2
    exact (h1 h2).elim
  · intro h
    have hfalse : False := by simp at h
    exact hfalse.elim

private theorem jsp87NzZero_disjoint {K p H : ℕ} (s : Finset ℕ) :
    Disjoint (jsp87NzRes K p H s) (jsp87ZeroRes K p H s) := by
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  have h1 := (Finset.mem_filter.mp ha).2
  have h2 := (Finset.mem_filter.mp hb).2
  exact (h1 h2).elim

/-- **THE TWO CLASSES SPLIT THE SAMPLE.** -/
theorem jsp87card_nz_add_zero {K p H : ℕ} (s : Finset ℕ) :
    (jsp87NzRes K p H s).card + (jsp87ZeroRes K p H s).card = s.card := by
  rw [← Finset.card_union_of_disjoint (jsp87NzZero_disjoint (K := K) (p := p) (H := H) s),
    jsp87NzZero_union (K := K) (p := p) (H := H) s]

theorem jsp87NzFrac_nonneg {K p H : ℕ} (s : Finset ℕ) : 0 ≤ jsp87NzFrac K p H s := by
  unfold jsp87NzFrac
  positivity

theorem jsp87NzFrac_le_one {K p H : ℕ} {s : Finset ℕ} (hs : s.Nonempty) :
    jsp87NzFrac K p H s ≤ 1 := by
  unfold jsp87NzFrac
  have h0 : 0 < ((s.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [div_le_one h0]
  have h1 : (jsp87NzRes K p H s).card ≤ s.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact_mod_cast h1

theorem jsp87NzFrac_add_zero {K p H : ℕ} {s : Finset ℕ} (hs : s.Nonempty) :
    jsp87NzFrac K p H s
        + (((jsp87ZeroRes K p H s).card : ℕ) / ((s.card : ℕ) : ℝ)) = 1 := by
  have h0 : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hc := jsp87card_nz_add_zero (K := K) (p := p) (H := H) s
  unfold jsp87NzFrac
  field_simp
  exact_mod_cast hc

/-- **THE ZERO-CLASS FRACTION IS THE COMPLEMENT OF THE NONZERO FRACTION.** -/
theorem jsp87ZeroFrac_eq_one_sub_nz {K p H : ℕ} {s : Finset ℕ} (hs : s.Nonempty) :
    (((jsp87ZeroRes K p H s).card : ℕ) / ((s.card : ℕ) : ℝ))
      = 1 - jsp87NzFrac K p H s := by
  linarith [jsp87NzFrac_add_zero (K := K) (p := p) (H := H) hs]

/-- **THE MAIN TWO-CLASS CRITERION, IN FRACTION FORM.**  Writing `f` for the
fraction of the sample at which `X_p` is nonzero,

```
Var (q X_p)  ≥  q² · f (1 − f) · 2^{−2(H+K)} .
```

This is `jsp87Var_Xp_ge_twoClass` of `VarLocal.lean` §6 with the *size* of the two
classes replaced by their *fractions*; it is the quantitative form of what
`policy.json` `next_round_attack[0]` calls "the ONE quantity that (5.21) needs". -/
theorem jsp87Var_Xp_ge_nzFrac {K : ℕ} (s : Finset ℕ) (hs : s.Nonempty) (q : ℝ) (p H : ℕ)
    (hA : (jsp87NzRes K p H s).Nonempty) (hB : (jsp87ZeroRes K p H s).Nonempty) :
    (q ^ 2) * ((jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))
        * (((1 / 2 : ℝ) ^ (H + K)) ^ 2))
      ≤ jsp87Var s (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  have hne : ∀ x ∈ jsp87NzRes K p H s, ∀ y ∈ jsp87ZeroRes K p H s,
      jsp87Xp0 (jsp87BinV K) p x H ≠ jsp87Xp0 (jsp87BinV K) p y H := by
    intro x hx y hy
    intro hEq
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hx'.2 (by rw [hEq, hy'.2])
  have hV := jsp87Var_Xp_ge_twoClass s hs q (jsp87BinV K) p H (jsp87NzRes K p H s)
    (jsp87ZeroRes K p H s) ((jsp87NzZero_union (K := K) (p := p) (H := H) s).symm)
    (jsp87NzZero_inter (K := K) (p := p) (H := H) s) hA hB hne
  have hsc : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hcast : (((jsp87NzRes K p H s).card * (jsp87ZeroRes K p H s).card : ℕ) : ℝ)
      = (((jsp87NzRes K p H s).card : ℕ) : ℝ)
        * (((jsp87ZeroRes K p H s).card : ℕ) : ℝ) := by exact_mod_cast Nat.cast_mul _ _
  have hcast1 : (((jsp87NzRes K p H s).card : ℕ) : ℝ)
      = jsp87NzFrac K p H s * ((s.card : ℕ) : ℝ) := by
    unfold jsp87NzFrac
    field_simp
  have hcast2 : (((jsp87ZeroRes K p H s).card : ℕ) : ℝ)
      = (1 - jsp87NzFrac K p H s) * ((s.card : ℕ) : ℝ) := by
    have hz := jsp87ZeroFrac_eq_one_sub_nz (K := K) (p := p) (H := H) hs
    calc ((jsp87ZeroRes K p H s).card : ℕ)
        = (((jsp87ZeroRes K p H s).card : ℕ) / ((s.card : ℕ) : ℝ))
            * ((s.card : ℕ) : ℝ) := by field_simp
      _ = (1 - jsp87NzFrac K p H s) * ((s.card : ℕ) : ℝ) := by rw [hz]
  rw [hcast, hcast1, hcast2] at hV
  convert hV using 1 <;> field_simp <;> ring

/-- **THE ACTIVE-CLASS FRACTION IS AT MOST THE NONZERO-CLASS FRACTION.**  The
bridge between the two objects of §1: a sample point at which the cube is hit at
the bottom level is a sample point at which the cube sum is nonzero. -/
theorem jsp87NzFrac_ge_actFrac {K p H : ℕ} (hp : 2 ^ K ≤ p) (hH : 1 ≤ H) (s : Finset ℕ) :
    jsp87ActFrac K p 1 s ≤ jsp87NzFrac K p H s := by
  have hsub : jsp87ActRes K p 1 s ⊆ jsp87NzRes K p H s := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_filter]
    exact ⟨hn.1, jsp87Xp0_ne_zero_of_active_one hp hn.2 hH⟩
  by_cases hs : s.Nonempty
  · have h0 : 0 < ((s.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs
    have hcard : ((jsp87ActRes K p 1 s).card : ℕ) ≤ ((jsp87NzRes K p H s).card : ℕ) :=
      Finset.card_le_card hsub
    unfold jsp87ActFrac jsp87NzFrac
    exact (div_le_div_iff_of_pos_right h0).2 (Nat.cast_le.2 hcard)
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    unfold jsp87ActFrac jsp87NzFrac
    rw [hz]
    simp

/-- **THE VARIANCE SUM OVER `S₁`, IN FRACTION FORM.** -/
theorem jsp87Var_sum_ge_nzFrac {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ) (hH : 1 ≤ H) (hsep : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (hne : ∀ p ∈ P, (∃ n ∈ s, p ∣ n) ∧ (∃ n ∈ s, jsp87Active K p 1 n)) :
    (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, ((jsp87NzFrac K p H s) * (1 - jsp87NzFrac K p H s))
      ≤ ∑ p ∈ P, jsp87Var s (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
  have h1 : ∀ p ∈ P,
      (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))
        ≤ jsp87Var s (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := by
    intro p hp
    have hlt := hsep p hp
    have hp' : 2 ^ K ≤ p := by omega
    have hp0 : 0 < p := by omega
    obtain ⟨⟨n, hn1, hn2⟩, ⟨m, hm1, hm2⟩⟩ := hne p hp
    have hV := jsp87Var_Xp_ge_nzFrac s hs q p H
      ⟨m, by rw [Finset.mem_filter]; exact ⟨hm1, jsp87Xp0_ne_zero_of_active_one hp' hm2 hH⟩⟩
      ⟨n, by rw [Finset.mem_filter]; exact ⟨hn1, jsp87Xp0_eq_zero_of_dvd hp0 hlt hn2⟩⟩
    convert hV using 1 <;> ring
  have h2 := Finset.sum_le_sum h1
  calc (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, ((jsp87NzFrac K p H s) * (1 - jsp87NzFrac K p H s))
      = ∑ p ∈ P, ((q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
          * (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ P, jsp87Var s (fun n => q * jsp87Xp0 (jsp87BinV K) p n H) := h2

/-! ## §4  THE ENDGAME WITH (5.21) IN SAMPLE GEOMETRY -/

/-- **THE ENDGAME, WITH HYPOTHESIS (5.21) REPLACED BY A SAMPLE-GEOMETRIC
CONDITION (5.21′).**

Everything else is exactly as in `jsp87_endgame_cube_pow`: (5.15), (5.16)–(5.17),
(5.19), and the separation hypothesis `H + 2^K − 1 < p` for every prime of `S₁`.
The *only* arithmetic input is

```
(5.21′)   1 ≤ q² 2^{−2(H+K)} ∑_{p ∈ S₁} f_p (1 − f_p) ,
          f_p = jsp87NzFrac K p H s ,
```

i.e. **the sample is sufficiently spread in residue classes, prime by prime**.
This is the exact reformulation of the `S₁`-variance hypothesis demanded by
`policy.json` `next_round_attack[0]`; §5 below shows what it excludes. -/
theorem jsp87_endgame_frac_of_5_21 {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ) (κ1 κ2 κ3 κ4 κ5 : ℝ)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hH : 1 ≤ H) (hsep : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (hne : ∀ p ∈ P, (∃ n ∈ s, p ∣ n) ∧ (∃ n ∈ s, jsp87Active K p 1 n))
    (H15 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p' ∈ P,
          jsp87Xp0 (jsp87BinV K) p' i H)) - 1‖ ≤ κ1 + κ2 + κ3)
    (H1617 : ‖jsp87CAvg s (fun i => jsp87e (q * ∑ p' ∈ P,
          jsp87Xp0 (jsp87BinV K) p' i H))
        - ∏ p' ∈ P, jsp87CAvg s (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV K) p' i H))‖
      ≤ κ4 + κ5)
    (hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :
    ¬ ((κ1 < 1 / 30) ∧ (κ2 < 1 / 30) ∧ (κ3 < 1 / 30) ∧ (κ4 < 1 / 30) ∧ (κ5 < 1 / 30)) := by
  have hH21 : (1 : ℝ) ≤ ∑ p ∈ P, jsp87Var s (fun i => q * jsp87Xp0 (jsp87BinV K) p i H) := by
    have h := jsp87Var_sum_ge_nzFrac (K := K) (P := P) s hs q H hH hsep hne
    linarith
  exact jsp87_endgame_cube_pow (P := P) s hs q K H κ1 κ2 κ3 κ4 κ5 hK hsep H15 H1617 hH21

/-! ## §5  What (5.21′) cannot be -/

/-- **THE MAXIMUM OF THE FRACTION PRODUCT.** -/
theorem jsp87mul_one_sub_le (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    0 ≤ f * (1 - f) ∧ f * (1 - f) ≤ 1 / 4 := by
  constructor <;> nlinarith [sq_nonneg (f - 1 / 2)]

theorem jsp87NzFrac_mul_one_sub {K p H : ℕ} {s : Finset ℕ} (hs : s.Nonempty) :
    0 ≤ jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s)
      ∧ jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) ≤ 1 / 4 :=
  jsp87mul_one_sub_le _ (jsp87NzFrac_nonneg s) (jsp87NzFrac_le_one hs)

/-- **A SAMPLE IN A SINGLE RESIDUE CLASS HAS A DEGENERATE NONZERO FRACTION.**
The cube sum is constant on the sample, hence the nonzero fraction is `0` or `1`. -/
theorem jsp87NzFrac_eq_zero_or_one_of_singleRes {K : ℕ} (p H : ℕ)
    {s : Finset ℕ} (hs : s.Nonempty) (r : ℕ) (hr : ∀ n ∈ s, n % p = r % p) :
    jsp87NzFrac K p H s = 0 ∨ jsp87NzFrac K p H s = 1 := by
  have hconst : ∀ n ∈ s, jsp87Xp0 (jsp87BinV K) p n H = jsp87Xp0 (jsp87BinV K) p r H :=
    fun n hn => jsp87Xp0_eq_of_res (jsp87BinV K) (hr n hn)
  have hcardpos : 0 < ((s.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  by_cases hz : jsp87Xp0 (jsp87BinV K) p r H = 0
  · left
    have hsub : jsp87NzRes K p H s = ∅ := by
      ext n
      constructor
      · intro hn
        have hn' := Finset.mem_filter.mp hn
        exact (hn'.2 (by rw [hconst n hn'.1, hz])).elim
      · intro h
        have hfalse : False := by simp at h
        exact hfalse.elim
    unfold jsp87NzFrac
    rw [hsub]
    simp
  · right
    have hsub : jsp87NzRes K p H s = s := by
      ext n
      constructor
      · intro hn
        exact (Finset.mem_filter.mp hn).1
      · intro hn
        rw [Finset.mem_filter]
        refine ⟨hn, ?_⟩
        rw [hconst n hn]
        exact fun hz' => hz hz'
    unfold jsp87NzFrac
    rw [hsub]
    exact div_self (ne_of_gt hcardpos)

/-- **HYPOTHESIS (5.21′) CANNOT BE SUPPLIED BY A SAMPLE IN ONE RESIDUE CLASS.**
Machine-checked negative knowledge: the `S₁`-variance of (5.21) requires the
sample to *spread* over the residue classes modulo every `p ∈ S₁`. -/
theorem jsp87_5_21_singleRes_impossible {K p H : ℕ} {s : Finset ℕ}
    (hs : s.Nonempty) (r : ℕ) (hr : ∀ n ∈ s, n % p = r % p) (q : ℝ) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) := by
  intro h
  rcases jsp87NzFrac_eq_zero_or_one_of_singleRes p H hs r hr with h0 | h1
  · have hz : jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) = 0 := by rw [h0]; ring
    rw [hz, mul_zero] at h
    exact absurd h (by norm_num)
  · have hz : jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) = 0 := by rw [h1]; ring
    rw [hz, mul_zero] at h
    exact absurd h (by norm_num)

/-- **HYPOTHESIS (5.21′) CANNOT BE SUPPLIED BY AN ARITHMETIC PROGRESSION WHOSE
STEP IS DIVISIBLE BY EVERY PRIME OF `S₁`.**  The sample of §5 of
arXiv:2512.01739 is a structured set of integers, and this theorem says that a
structured set which is *congruent* sample point to sample point modulo the whole
of `S₁` is worthless for the endgame: all `p ∈ S₁` then see a single residue
class, the nonzero fraction is degenerate, and the variance vanishes. -/
theorem jsp87_5_21_prog_impossible {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (n0 D : ℕ) (hsub : s ⊆ s.image (fun j => n0 + D * j))
    (hD : ∀ p ∈ P, p ∣ D) (q : ℝ) (H : ℕ) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) := by
  intro h
  have hres : ∀ p ∈ P, ∀ n ∈ s, n % p = n0 % p := by
    intro p hp n hn
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp (hsub hn)
    have hDj : p ∣ D * j := by
      obtain ⟨k, hk⟩ := hD p hp
      refine ⟨j * k, ?_⟩
      calc D * j = (p * k) * j := by rw [hk]
        _ = p * (j * k) := by ring
    rw [← heq]
    calc (n0 + D * j) % p = ((n0 % p) + (D * j) % p) % p := Nat.add_mod _ _ _
      _ = ((n0 % p) + 0) % p := by rw [Nat.dvd_iff_mod_eq_zero.mp hDj]
      _ = n0 % p := by rw [Nat.add_zero, Nat.mod_mod]
  have hzero : ∀ p ∈ P, jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) = 0 := by
    intro p hp
    rcases jsp87NzFrac_eq_zero_or_one_of_singleRes p H hs n0 (hres p hp) with h0 | h1
    · rw [h0]
      ring
    · rw [h1]
      ring
  have hsum0 : ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s)) = 0 :=
    Finset.sum_eq_zero fun p hp => hzero p hp
  rw [hsum0] at h
  have hz0 : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * (0 : ℝ) = 0 := by ring
  rw [hz0] at h
  exact absurd h (by norm_num)

/-! ## §6  How many primes (5.21′) needs -/

/-- **(5.21′) FORCES FOUR TIMES THE CUBE SQUARE.**  Since `f (1 − f) ≤ 1/4`, the
`S₁`-variance sum is at most `|S₁| / 4`, so (5.21′) forces

```
4 ≤ q² 2^{−2(H+K)} |S₁| .
``` -/
theorem jsp87_5_21_needs_four {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ)
    (hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :
    (4 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * ((P.card : ℕ) : ℝ) := by
  have hsum : ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))
      ≤ ((P.card : ℕ) : ℝ) / 4 := by
    calc _ ≤ ∑ _p ∈ P, (1 / 4 : ℝ) :=
        Finset.sum_le_sum fun p _ => (jsp87NzFrac_mul_one_sub hs).2
      _ = ((P.card : ℕ) : ℝ) / 4 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hc2 : (0 : ℝ) ≤ (((1 / 2 : ℝ) ^ (H + K)) ^ 2) := by positivity
  have hq2 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have h1 := mul_le_mul_of_nonneg_left hsum (mul_nonneg hq2 hc2)
  have h2 : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * (((P.card : ℕ) : ℝ) / 4)
      = (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * ((P.card : ℕ) : ℝ) / 4 := by ring
  rw [h2] at h1
  have h3 : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
      * ((P.card : ℕ) : ℝ) / 4 := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 4)
  convert h4 using 1 <;> ring

/-- **`4^{m+1} · 2^{−2m} = 4`.** -/
private theorem jsp87four_pow (m : ℕ) :
    ((4 : ℝ) ^ (m + 1) * (((1 / 2 : ℝ) ^ m) ^ 2)) = 4 := by
  have hsq : ((1 / 2 : ℝ) ^ m) ^ 2 = ((1 / 4 : ℝ) ^ m) := by
    calc ((1 / 2 : ℝ) ^ m) ^ 2 = (1 / 2 : ℝ) ^ (m * 2) := (pow_mul ..).symm
      _ = (1 / 2 : ℝ) ^ (2 * m) := by rw [Nat.mul_comm m 2]
      _ = ((1 / 2 : ℝ) ^ 2) ^ m := pow_mul ..
      _ = (1 / 4 : ℝ) ^ m := by rw [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
  have h1 : (1 / 4 : ℝ) ^ m = ((4 : ℝ) ^ m)⁻¹ := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
  rw [hsq, h1]
  calc (4 : ℝ) ^ (m + 1) * ((4 : ℝ) ^ m)⁻¹ = 4 * (4 ^ m * (4 ^ m)⁻¹) := by
        rw [pow_succ]
        ring
    _ = 4 := by rw [mul_inv_cancel₀ (by positivity)]; ring

/-- **THE MERSENNE COUNT: (5.21′) FORCES `4^{H+K+1} ≤ q² |S₁|`.** -/
theorem jsp87_5_21_needs_card {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ)
    (hne : ∀ p ∈ P, (∃ n ∈ s, p ∣ n) ∧ (∃ n ∈ s, jsp87Active K p 1 n))
    (hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :
    ((4 : ℝ) ^ (H + K + 1)) ≤ (q ^ 2) * ((P.card : ℕ) : ℝ) := by
  have h4 := jsp87_5_21_needs_four (K := K) (P := P) s hs q H hfrac
  have hc2 : (0 : ℝ) < (((1 / 2 : ℝ) ^ (H + K)) ^ 2) := by positivity
  have hdiv : (4 : ℝ) / (((1 / 2 : ℝ) ^ (H + K)) ^ 2) ≤ (q ^ 2) * ((P.card : ℕ) : ℝ) := by
    apply (div_le_iff₀ hc2).mpr
    convert h4 using 1 <;> ring
  have heq : (4 : ℝ) / (((1 / 2 : ℝ) ^ (H + K)) ^ 2) = 4 ^ (H + K + 1) :=
    (div_eq_iff (ne_of_gt hc2)).mpr (jsp87four_pow (H + K)).symm
  rw [heq] at hdiv
  exact hdiv

/-- **THE DIMENSION LOWER BOUND IMPLIED BY (5.19)**: `|q| H 2^{−K} ≤ 1/20` forces
`4^K ≥ 400 q² H²`. -/
private theorem jsp87four_pow_ge {K H : ℕ} (hq : 0 < q) (hH : 1 ≤ H)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20) :
    (400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2 ≤ (4 : ℝ) ^ K := by
  rw [jsp87W_eq_half, abs_of_pos hq, Nat.zero_add] at hK
  have h1 : (1 / 2 : ℝ) ^ K ≤ (1 : ℝ) / (20 * (q * ((H : ℕ) : ℝ))) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * (q * ((H : ℕ) : ℝ)))).2
    calc (1 / 2 : ℝ) ^ K * (20 * (q * ((H : ℕ) : ℝ)))
        = 20 * (q * ((H : ℕ) : ℝ) * (1 / 2 : ℝ) ^ K) := by ring
      _ ≤ 20 * (1 / 20) := mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ) ≤ 20)
      _ = 1 := by norm_num
  have h2 : ((1 / 2 : ℝ) ^ K) ^ 2 ≤ ((1 : ℝ) / (20 * (q * ((H : ℕ) : ℝ)))) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr h1
  have h3 : ((1 / 4 : ℝ) : ℝ) ^ K ≤ 1 / ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) := by
    have hsq : ((1 / 2 : ℝ) ^ K) ^ 2 = ((1 / 4 : ℝ) : ℝ) ^ K := by
      calc ((1 / 2 : ℝ) ^ K) ^ 2 = (1 / 2 : ℝ) ^ (K * 2) := (pow_mul ..).symm
        _ = (1 / 2 : ℝ) ^ (2 * K) := by rw [Nat.mul_comm K 2]
        _ = ((1 / 2 : ℝ) ^ 2) ^ K := pow_mul ..
        _ = ((1 / 4 : ℝ) : ℝ) ^ K := by
          have h2 : ((1 / 2 : ℝ) ^ 2) = ((1 / 4 : ℝ) : ℝ) := by norm_num
          rw [h2]
    have h2' : ((1 / 4 : ℝ) : ℝ) ^ K ≤ (1 : ℝ) / ((20 * (q * ((H : ℕ) : ℝ))) ^ 2) := by
      calc ((1 / 4 : ℝ) : ℝ) ^ K
          ≤ ((1 : ℝ) / (20 * (q * ((H : ℕ) : ℝ)))) ^ 2 := by rw [← hsq]; exact h2
        _ = (1 : ℝ) / ((20 * (q * ((H : ℕ) : ℝ))) ^ 2) := by rw [div_pow]; norm_num
    convert h2' using 1 <;> ring
  have h4 : (0 : ℝ) < (4 : ℝ) ^ K := by positivity
  have h5 : (0 : ℝ) < ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) := by positivity
  have h6 : ((4 : ℝ) ^ K)⁻¹ ≤ ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [show ((1 / 4 : ℝ) ^ K) = ((4 : ℝ) ^ K)⁻¹ from by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]] at h3
    convert h3 using 1 <;> ring
  exact (inv_le_inv₀ h4 h5).mp h6

/-- **HOW MANY PRIMES (5.21′) NEEDS: `1600 · 4^H · H² ≤ |S₁|`.**

Combining (5.19) — which forces the cube dimension to satisfy `4^K ≥ 400 q² H²` —
with the Mersenne count `4^{H+K+1} ≤ q² |S₁|`, the factor `q²` cancels and the
requirement becomes a statement about `H` alone: the `S₁` of the endgame must
contain at least `1600 · 4^H · H²` primes.  For `H = 1` that is `6400` primes;
for `H = 5`, `2 048 000`.  This is the **quantitative content** of what round 120
had only proved negatively: (5.21) is impossible for a uniform sample, and it is
impossible for any sample supported on fewer than `1600·4^H·H²` primes. -/
theorem jsp87_5_21_needs_manyPrimes {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ) (hq : 0 < q) (hH : 1 ≤ H)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hsep : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (hne : ∀ p ∈ P, (∃ n ∈ s, p ∣ n) ∧ (∃ n ∈ s, jsp87Active K p 1 n))
    (hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :
    ((1600 : ℝ) * ((4 : ℝ) ^ H) * ((H : ℕ) : ℝ) ^ 2) ≤ ((P.card : ℕ) : ℝ) := by
  have hD := jsp87_5_21_needs_card (K := K) (P := P) s hs q H hne hfrac
  have hE : (400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2 ≤ (4 : ℝ) ^ K := jsp87four_pow_ge hq hH hK
  have hD' : (4 : ℝ) ^ (H + 1) * (4 : ℝ) ^ K ≤ (q ^ 2) * ((P.card : ℕ) : ℝ) := by
    have heq : H + K + 1 = (H + 1) + K := by ring
    rw [heq, pow_add] at hD
    exact hD
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ K := by positivity
  have hDpos : (0 : ℝ) < ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) := by positivity
  have hDne : ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) ≠ 0 := ne_of_gt hDpos
  have hA : (4 : ℝ) ^ (H + 1) ≤ ((q ^ 2) * ((P.card : ℕ) : ℝ)) / (4 : ℝ) ^ K := by
    apply (le_div_iff₀ h4pos).mpr
    exact hD'
  have hB : (1 : ℝ) / (4 : ℝ) ^ K ≤ (1 : ℝ) / ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) := by
    have hinv := (inv_le_inv₀ h4pos hDpos).mpr hE
    convert hinv using 1 <;> ring
  have hP : (0 : ℝ) ≤ (q ^ 2) * ((P.card : ℕ) : ℝ) := by positivity
  have hC : ((q ^ 2) * ((P.card : ℕ) : ℝ)) / (4 : ℝ) ^ K
      ≤ ((q ^ 2) * ((P.card : ℕ) : ℝ)) / ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hB hP
    convert hmul using 1 <;> ring
  have hE2 : (4 : ℝ) ^ (H + 1)
      ≤ ((q ^ 2) * ((P.card : ℕ) : ℝ)) / ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) :=
    le_trans hA hC
  have hF : ((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) * (4 : ℝ) ^ (H + 1)
      ≤ (q ^ 2) * ((P.card : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hE2 hDpos.le
    convert hmul using 1 <;> field_simp [hDne]
  have hq2 : (0 : ℝ) < ((q : ℝ) ^ 2) := by positivity
  have hq2ne : (q ^ 2) ≠ 0 := ne_of_gt hq2
  have hH9 : (((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) * (4 : ℝ) ^ (H + 1)) / (q ^ 2)
      ≤ ((P.card : ℕ) : ℝ) := by
    rw [div_le_iff₀ hq2]
    convert hF using 1 <;> ring
  have hL : (1600 : ℝ) * ((4 : ℝ) ^ H) * ((H : ℕ) : ℝ) ^ 2
      = (((400 : ℝ) * q ^ 2 * ((H : ℕ) : ℝ) ^ 2) * (4 : ℝ) ^ (H + 1)) / (q ^ 2) := by
    field_simp [hq2ne]
    rw [pow_succ]
    ring
  rw [hL]
  exact hH9

/-! ## §7  The summary of the round -/

/-- **THE SUMMARY OF ROUND 122.**

Hypothesis (5.21) of the endgame of arXiv:2512.01739 is, provably and from
scratch,

1. **a purely geometric condition on the sample** (5.21′): the nonzero fraction
   `f_p = #{n ∈ s : X_p n ≠ 0} / #{n ∈ s}` of every prime of `S₁` must satisfy
   `q² 2^{−2(H+K)} ∑_p f_p (1 − f_p) ≥ 1` (`jsp87_endgame_frac_of_5_21`);
2. **and that condition is impossible for any sample lying in one residue class
   modulo any `p ∈ S₁`** (`jsp87_5_21_singleRes_impossible`), hence in particular
   **impossible for any arithmetic progression whose step is divisible by the
   whole of `S₁`** (`jsp87_5_21_prog_impossible`);
3. **and it needs at least `1600 · 4^H · H²` primes in `S₁`**
   (`jsp87_5_21_needs_manyPrimes`), a bound independent of `q` and `K`.

Together with round 120's `jsp87_Xp_res_5_21_impossible`, the `S₁`-variance
hypothesis of the published proof is now fully characterised geometrically: it is
impossible for uniform samples and for progressions, and possible only for a
sample *correlated* with the cube vertices.  Establishing such a sample is
arXiv:2512.01739 `Theorem 3.1` (from Pilatte); Mathlib has no Chowla-type or
Elliott-type statement for multiplicative functions, so it is not supplied here. -/
theorem jsp87_correl_summary {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (q : ℝ) (H : ℕ) (hq : 0 < q) (hH : 1 ≤ H)
    (hK : |q| * ((H : ℕ) : ℝ) * jsp87W K 0 ≤ 1 / 20)
    (hsep : ∀ p ∈ P, H + 2 ^ K - 1 < p)
    (hne : ∀ p ∈ P, (∃ n ∈ s, p ∣ n) ∧ (∃ n ∈ s, jsp87Active K p 1 n))
    (hfrac : (1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :
    ((1600 : ℝ) * ((4 : ℝ) ^ H) * ((H : ℕ) : ℝ) ^ 2) ≤ ((P.card : ℕ) : ℝ) :=
  jsp87_5_21_needs_manyPrimes s hs q H hq hH hK hsep hne hfrac

/-- **AND THE PROGRESSION SAMPLE IS DEAD.**  The companion of
`jsp87_correl_summary`: a sample *contained in* an arithmetic progression
`{n₀ + D j}` whose step is divisible by every `p ∈ S₁` can never satisfy (5.21′),
no matter how many primes `S₁` has. -/
theorem jsp87_5_21_prog_of_frac {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (n0 D : ℕ) (hsub : s ⊆ s.image (fun j => n0 + D * j)) (hD : ∀ p ∈ P, p ∣ D)
    (q : ℝ) (H : ℕ) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) :=
  jsp87_5_21_prog_impossible s hs n0 D hsub hD q H

/-- **THE PRIME-WISE FORM OF THE SINGLE-RESIDUE OBSTRUCTION.**  If the sample is
congruent sample point to sample point modulo *every* `p ∈ S₁` (with a residue
that may depend on `p`), then (5.21′) is impossible. -/
theorem jsp87_5_21_singleResP_impossible {K : ℕ} {P : Finset ℕ} (s : Finset ℕ) (hs : s.Nonempty)
    (hres : ∀ p ∈ P, ∃ r : ℕ, ∀ n ∈ s, n % p = r % p) (q : ℝ) (H : ℕ) :
    ¬ ((1 : ℝ) ≤ (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2)
        * ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s))) := by
  intro h
  have hzero : ∀ p ∈ P, jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s) = 0 := by
    intro p hp
    obtain ⟨r, hr⟩ := hres p hp
    rcases jsp87NzFrac_eq_zero_or_one_of_singleRes p H hs r hr with h0 | h1
    · rw [h0]
      ring
    · rw [h1]
      ring
  have hsum0 : ∑ p ∈ P, (jsp87NzFrac K p H s * (1 - jsp87NzFrac K p H s)) = 0 :=
    Finset.sum_eq_zero fun p hp => hzero p hp
  rw [hsum0] at h
  have hz0 : (q ^ 2) * (((1 / 2 : ℝ) ^ (H + K)) ^ 2) * (0 : ℝ) = 0 := by ring
  rw [hz0] at h
  exact absurd h (by norm_num)

end JSP87
