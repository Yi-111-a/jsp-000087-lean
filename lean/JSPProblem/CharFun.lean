/-
Copyright (c) 2026. Released under Apache 2.0.
-/
import JSPProblem.CntVariance

/-!
# Round 128 — THE EXACT CHARACTERISTIC FUNCTION OF THE PRIME-DIVISOR COUNT ON A
# WHOLE PERIOD

`policy.json` `next_round_attack[0]` asked for the exact covariances of the
sample; round 127 closed it for *polynomial* moments (mean, second moment,
variance) and showed that the covariances vanish by CRT on the canonical sample.
This file does the remaining, genuinely harder part of the same question: **the
exponential moment**, i.e. the object that the endgame of arXiv:2512.01739
actually uses.

## §0–§1  the object

```
jsp87CharFun P θ  =  𝔼_{i ∈ jsp87ProgFull 0 1 P} [ e (θ · cnt P (i+1)) ] .
```

This is the complex mean of the phase of the endgame **at the ground-truth
scale** (`K = 0, H = 1`), by `jsp87Phase_zero_one` of round 126 — i.e. it is
`jsp87Mean 0 1 Y q` with `θ = q/2`.

## §2–§3  THE CLOSED FORM

`jsp87CharFun_eq_prod` is the headline of this round:

```
jsp87CharFun P θ  =  ∏_{p ∈ P} ( 1 − 1/p + e θ / p ) ,
```

a **finite product, evaluated**.  Nothing is estimated, nothing is assumed: the
mean of `e^{iθ·cnt}` over a whole period is the product of the single-prime
means, because the divisibility events are independent by CRT (round 127 for
pairs, this file for *all* subsets, via the inclusion–exclusion expansion of
§1 and the counting lemma `jsp87card_div_subset` of §2).

## §4  the modulus

`jsp87CharFun_normSq` computes the modulus exactly,

```
‖jsp87CharFun P θ‖² = ∏_{p ∈ P} ( 1 − (2/p)(1 − 1/p)(1 − cos 2πθ) ) ,
```

and `jsp87CharFun_norm_le` turns it into the exponential estimate
`≤ exp (−2(1 − cos 2πθ) · jsp87SqDefect P)`, where `jsp87SqDefect` is the
**variance of round 127**.  So the whole endgame mean is controlled by the very
quantity round 127 computed in closed form, and Euler's divergence makes it
tend to `0`.

## §5  THE JOIN WITH THE ENDGAME

* `jsp87Err2z_ground_zero` — **hypotheses (5.16)–(5.17) hold with the constants
  exactly `0` at the ground-truth scale**: the mean of the phase is *literally*
  the product of the single-prime means.  Two of the five sharp constants of the
  endgame are free.
* `jsp87Err1_ground_tendsto` — **the error of (5.15) tends to `1`** with the
  height, hence
* `jsp87_515_ground_false`, `jsp87_endgame_ground_blocked` — **hypothesis (5.15)
  is refuted at every large height for every total constant `< 1`**, and
  therefore the endgame of §§5.3–5.14 **cannot be run on the canonical
  whole-period sample at all**: for every choice of the five constants, the
  conjunction of (5.15), (5.16)–(5.17) and the sharpness `κ_j < 1/30` is
  unsatisfiable.  The sample, not the constants, is the obstruction.
-/open scoped BigOperators

set_option maxHeartbeats 1000000

namespace JSP87

/-! ## §1  The subset expansion: a product of indicators, and a product of
`(1 + u)` -/

/-- **A CHARACTER OF THE COUNT IS A PRODUCT OF INDICATORS.** -/
private theorem jsp87pow_cnt (z : ℂ) (P : Finset ℕ) (m : ℕ) :
    z ^ (jsp87Cnt P m) = ∏ p ∈ P, (if p ∣ m then z else 1) := by
  induction P using Finset.induction_on with
  | empty => simp [jsp87Cnt]
  | @insert a P ha ih =>
    by_cases h : a ∣ m
    · have hf : (insert a P).filter (fun q => q ∣ m)
          = insert a (P.filter (fun q => q ∣ m)) := by
        rw [Finset.filter_insert]
        rw [if_pos h]
      have hcard : jsp87Cnt (insert a P) m = jsp87Cnt P m + 1 := by
        unfold jsp87Cnt
        rw [hf]
        exact Finset.card_insert_of_notMem (by
          rw [Finset.mem_filter]
          exact fun ⟨h', _⟩ => ha h')
      rw [hcard, pow_succ', ih]
      rw [Finset.prod_insert (s := P) (a := a) ha, if_pos h]
    · have hf : (insert a P).filter (fun q => q ∣ m)
          = P.filter (fun q => q ∣ m) := by
        rw [Finset.filter_insert]
        rw [if_neg h]
      have hcard : jsp87Cnt (insert a P) m = jsp87Cnt P m := by
        unfold jsp87Cnt
        rw [hf]
      rw [hcard, ih]
      rw [Finset.prod_insert (s := P) (a := a) ha, if_neg h, one_mul]

/-- **`insert a` IS INJECTIVE ON THE POWERSET OF A SET NOT CONTAINING `a`.** -/
private theorem jsp87insert_inj_pow (a : ℕ) (T : Finset ℕ) (ha : a ∉ T) :
    Set.InjOn (fun S : Finset ℕ => insert a S) ↑T.powerset := by
  intro x hx y hy hxy
  have haX : a ∉ x := fun h => ha ((Finset.mem_powerset.mp hx) h)
  have haY : a ∉ y := fun h => ha ((Finset.mem_powerset.mp hy) h)
  have hxy' : insert a x = insert a y := hxy
  calc x = (insert a x).erase a := (Finset.erase_insert haX).symm
    _ = (insert a y).erase a := by rw [hxy']
    _ = y := Finset.erase_insert haY

/-- **THE POWERSET OF AN INSERT IS THE TWO CLASSES OF SUBSETS.** -/
private theorem jsp87powerset_disjoint (T : Finset ℕ) (a : ℕ) (ha : a ∉ T) :
    Disjoint T.powerset (T.powerset.image (insert a)) := by
  rw [Finset.disjoint_left]
  intro S hS1 hS2
  rcases Finset.mem_image.mp hS2 with ⟨U, hU, rfl⟩
  have hS1' := Finset.mem_powerset.mp hS1
  exact ha (hS1' (Finset.mem_insert_self a U))

/-- **A PRODUCT OF `(1 + u)` IS A SUM OVER SUBSETS.** -/
private theorem jsp87prod_sum (T : Finset ℕ) (u : ℕ → ℂ) :
    (∏ p ∈ T, (1 + u p)) = ∑ S ∈ T.powerset, ∏ p ∈ S, u p := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have hkey : ∀ S ∈ T.powerset, ∏ p ∈ insert a S, u p = u a * ∏ p ∈ S, u p :=
      fun S hS => Finset.prod_insert (s := S) (a := a)
        (fun hq => ha ((Finset.mem_powerset.mp hS) hq))
    have himg : (∑ _S ∈ T.powerset.image (insert a), ∏ p ∈ _S, u p)
        = ∑ U ∈ T.powerset, u a * ∏ p ∈ U, u p := by
      have h1 := (Finset.sum_image (s := T.powerset) (g := fun T' => insert a T')
        (f := fun S => ∏ p ∈ S, u p) (jsp87insert_inj_pow a T ha))
      rw [h1]
      exact Finset.sum_congr rfl fun U hU => hkey U hU
    rw [Finset.powerset_insert, Finset.sum_union (jsp87powerset_disjoint T a ha)]
    rw [himg, ← Finset.mul_sum]
    rw [Finset.prod_insert (s := T) (a := a) ha, ih]
    ring

/-- **THE SUBSET SUM OF THE CHARACTER EXPANSION, evaluated.** -/
private theorem jsp87expand_recip (T : Finset ℕ) (z : ℂ) :
    (∑ S ∈ T.powerset, (z - 1) ^ S.card * ∏ p ∈ S, ((1 / (p : ℝ)) : ℂ))
      = ∏ p ∈ T, (1 + (z - 1) * ((1 / (p : ℝ)) : ℂ)) := by
  have hstep : ∀ S : Finset ℕ,
      (z - 1) ^ S.card * ∏ p ∈ S, ((1 / (p : ℝ)) : ℂ)
        = ∏ p ∈ S, ((z - 1) * ((1 / (p : ℝ)) : ℂ)) := by
    intro S
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun S _ => hstep S)]
  exact (jsp87prod_sum T (fun p => (z - 1) * ((1 / (p : ℝ)) : ℂ))).symm

/-- **THE INCLUSION–EXCLUSION EXPANSION OF A CHARACTER.**

For every `T ⊆ ℕ`, every `z : ℂ` and every `m`,

```
∏_{p ∈ T} (if p ∣ m then z else 1)
  =  ∑_{S ⊆ T} (z − 1)^{|S|} · (1 if all primes of S divide m else 0) .
```

This is the identity that turns a mean over a sample into a finite sum over
**subsets** of the prime set, hence into a finite sum of exact counts. -/
private theorem jsp87expand_prod (T : Finset ℕ) (z : ℂ) :
    ∀ m : ℕ,
    (∏ p ∈ T, (if p ∣ m then z else 1))
      = ∑ S ∈ T.powerset, (z - 1) ^ S.card
          * (if ∀ p ∈ S, p ∣ m then (1 : ℂ) else 0) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    intro m
    have hconj : ∀ S : Finset ℕ,
        (∀ p ∈ insert a S, p ∣ m) ↔ a ∣ m ∧ (∀ p ∈ S, p ∣ m) := by
      intro S
      constructor
      · intro h
        exact ⟨h a (Finset.mem_insert_self a S),
          fun p hp => h p (Finset.mem_insert_of_mem hp)⟩
      · rintro ⟨hda, hcon⟩ p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hda
        · exact hcon p hp
    have hkey : ∀ S ∈ T.powerset,
        (z - 1) ^ (insert a S).card
            * (if ∀ p ∈ insert a S, p ∣ m then (1 : ℂ) else 0)
          = ((z - 1) * (if a ∣ m then (1 : ℂ) else 0))
            * ((z - 1) ^ S.card * (if ∀ p ∈ S, p ∣ m then (1 : ℂ) else 0)) := by
      intro S hS
      have haS : a ∉ S := fun hq => ha ((Finset.mem_powerset.mp hS) hq)
      have hfac : (if ∀ p ∈ insert a S, p ∣ m then (1 : ℂ) else 0)
          = (if a ∣ m then (1 : ℂ) else 0)
            * (if ∀ p ∈ S, p ∣ m then (1 : ℂ) else 0) := by
        by_cases ha0 : a ∣ m
        · by_cases hS0 : ∀ p ∈ S, p ∣ m
          · rw [if_pos ((hconj S).mpr ⟨ha0, hS0⟩), if_pos ha0, if_pos hS0]
            ring
          · rw [if_neg (fun h => hS0 ((hconj S).mp h).2), if_pos ha0, if_neg hS0]
            ring
        · rw [if_neg (fun h => ha0 (h a (Finset.mem_insert_self a S))), if_neg ha0]
          ring
      rw [Finset.card_insert_of_notMem haS, pow_succ', hfac]
      ring
    have himg : (∑ _S ∈ T.powerset.image (insert a),
        (z - 1) ^ _S.card * (if ∀ p ∈ _S, p ∣ m then (1 : ℂ) else 0))
        = ∑ U ∈ T.powerset, ((z - 1) * (if a ∣ m then (1 : ℂ) else 0))
          * ((z - 1) ^ U.card * (if ∀ p ∈ U, p ∣ m then (1 : ℂ) else 0)) := by
      have h1 := (Finset.sum_image (s := T.powerset) (g := fun T' => insert a T')
        (f := fun S => (z - 1) ^ S.card
          * (if ∀ p ∈ S, p ∣ m then (1 : ℂ) else 0)) (jsp87insert_inj_pow a T ha))
      rw [h1]
      exact Finset.sum_congr rfl fun U hU => hkey U hU
    rw [Finset.powerset_insert, Finset.sum_union (jsp87powerset_disjoint T a ha)]
    rw [himg, ← Finset.mul_sum]
    rw [Finset.prod_insert (s := T) (a := a) ha, ih]
    by_cases ha0 : a ∣ m
    · rw [if_pos ha0, if_pos ha0]
      ring
    · rw [if_neg ha0, if_neg ha0]
      ring

/-- **A CHARACTER IS AN INTEGER POWER OF ITSELF.** -/
private theorem jsp87e_mul_nat (a : ℝ) (n : ℕ) : jsp87e (a * (n : ℝ)) = jsp87e a ^ n := by
  induction n with
  | zero => simp [jsp87e]
  | succ m ih =>
    have h1 : a * ((m + 1 : ℕ) : ℝ) = a * (m : ℝ) + a := by
      push_cast
      ring
    rw [h1, jsp87e_add, ih, pow_succ]/-! ## §2  The counting step: how many sample points carry a given subset -/

/-- **`a` IS COPRIME TO A PRODUCT OF NUMBERS IT IS COPRIME TO.** -/
private theorem jsp87cop_prod_right (a : ℕ) (S : Finset ℕ)
    (h : ∀ q ∈ S, Nat.Coprime a q) :
    Nat.Coprime a (∏ p ∈ S, (p : ℕ)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b S hb ih =>
    rw [Finset.prod_insert (s := S) (a := b) hb]
    exact (h b (Finset.mem_insert_self b S)).mul_right
      (ih fun q hq => h q (Finset.mem_insert_of_mem hq))

/-- **A PAIRWISE COPRIME SET: THE PRODUCT DIVIDES IFF EVERY FACTOR DOES.** -/
private theorem jsp87cop_prod (S : Finset ℕ)
    (hcp : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (m : ℕ) :
    (∀ p ∈ S, p ∣ m) ↔ (∏ p ∈ S, (p : ℕ)) ∣ m := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hca : ∀ q ∈ S, Nat.Coprime a q := fun q hq =>
      hcp a (Finset.mem_insert_self a S) q (Finset.mem_insert_of_mem hq) (by
        intro h
        exact ha (h ▸ hq))
    have hcop : Nat.Coprime a (∏ p ∈ S, (p : ℕ)) := jsp87cop_prod_right a S hca
    have hcpS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q :=
      fun p hp q hq hne => hcp p (Finset.mem_insert_of_mem hp) q
        (Finset.mem_insert_of_mem hq) hne
    have hconj : (∀ p ∈ insert a S, p ∣ m) ↔ a ∣ m ∧ (∀ p ∈ S, p ∣ m) := by
      constructor
      · intro h
        exact ⟨h a (Finset.mem_insert_self a S),
          fun p hp => h p (Finset.mem_insert_of_mem hp)⟩
      · rintro ⟨hda, hcon⟩ p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hda
        · exact hcon p hp
    rw [Finset.prod_insert (s := S) (a := a) ha]
    constructor
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (hconj.mp h).1 ((ih hcpS).mp (hconj.mp h).2)
    · intro hd
      refine hconj.mpr ?_
      refine ⟨Nat.dvd_trans (Nat.dvd_mul_right a (∏ p ∈ S, (p : ℕ))) hd, ?_⟩
      exact (ih hcpS).mpr (Nat.dvd_trans (Nat.dvd_mul_left (∏ p ∈ S, (p : ℕ)) a) hd)

/-- **THE COUNT OF THE SAMPLE POINTS WITH `d ∣ i + 1`, for a divisor `d` of the
product.**  This is the general form of `jsp87card_div_pair` of round 127: the
whole period contains exactly `N/d` multiples of every divisor `d` of `N`. -/
private theorem jsp87card_dvd_sample (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) {d : ℕ}
    (_hd : d ∣ jsp87Prod P) (hd0 : d ≠ 0) :
    ((jsp87ProgFull 0 1 P).filter (fun i => d ∣ i + 1)).card = jsp87Prod P / d := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  rw [jsp87ProgFull_eq_Icc hpos]
  have hshift : ((Finset.Icc 0 (jsp87Prod P - 1)).filter (fun i => d ∣ i + 1)).card
      = ((Finset.Ioc 0 (jsp87Prod P)).filter (fun t => d ∣ t)).card := by
    refine Finset.card_nbij' (fun i => i + 1) (fun t => t - 1) ?_ ?_ ?_ ?_
    · intro i hi
      have hi1 : i ≤ jsp87Prod P - 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
      have hi2 : d ∣ i + 1 := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine And.intro ?_ hi2
      rw [Finset.mem_Ioc]
      obtain ⟨c, hc⟩ := hi2
      omega
    · intro t ht
      have ht1 : t ∈ Finset.Ioc 0 (jsp87Prod P) := (Finset.mem_filter.mp ht).1
      have ht2 : d ∣ t := (Finset.mem_filter.mp ht).2
      have ht1' : (0 : ℕ) < t ∧ t ≤ jsp87Prod P := Finset.mem_Ioc.mp ht1
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine And.intro ?_ ?_
      · rw [Finset.mem_Icc]
        omega
      · show d ∣ (t - 1) + 1
        have h1 : (t - 1) + 1 = t := by omega
        rw [h1]
        exact ht2
    · intro i _
      change (i + 1) - 1 = i
      omega
    · intro t ht
      have ht2 : d ∣ t := (Finset.mem_filter.mp ht).2
      have htI : t ∈ Finset.Ioc 0 (jsp87Prod P) := (Finset.mem_filter.mp ht).1
      have ht0 : (0 : ℕ) < t := (Finset.mem_Ioc.mp htI).1
      change (t - 1) + 1 = t
      omega
  rw [hshift, Nat.Ioc_filter_dvd_card_eq_div]

/-- **THE COUNT OF THE SAMPLE POINTS DIVISIBLE BY EVERY PRIME OF A SUBSET.**

This is the counting lemma that round 127 needed for *pairs* and that the
closed form below needs for **all subsets**: `jsp87card_div_subset` with
`S = {p, q}` is `jsp87card_div_pair`. -/
theorem jsp87card_div_subset (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) {S : Finset ℕ}
    (hS : S ⊆ P) :
    ((jsp87ProgFull 0 1 P).filter (fun i => ∀ p ∈ S, p ∣ i + 1)).card
      = jsp87Prod P / (∏ p ∈ S, (p : ℕ)) := by
  have hcp : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (hpc p (hS hp)) (hpc q (hS hq))).mpr hne
  have hd : (∏ p ∈ S, (p : ℕ)) ∣ jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_dvd_prod_of_subset S P (fun p => p) hS
  have hd0 : (∏ p ∈ S, (p : ℕ)) ≠ 0 := by
    have hne : ∀ p ∈ S, (p : ℕ) ≠ 0 := fun p hp => (hpc p (hS hp)).ne_zero
    exact Finset.prod_ne_zero_iff.mpr hne
  have hkey : ∀ i : ℕ, (∀ p ∈ S, p ∣ i + 1) ↔ (∏ p ∈ S, (p : ℕ)) ∣ i + 1 :=
    fun i => jsp87cop_prod S hcp (i + 1)
  rw [show ((jsp87ProgFull 0 1 P).filter (fun i => ∀ p ∈ S, p ∣ i + 1))
      = ((jsp87ProgFull 0 1 P).filter (fun i => (∏ p ∈ S, (p : ℕ)) ∣ i + 1)) by
        exact Finset.filter_congr (fun i _ => hkey i)]
  exact jsp87card_dvd_sample P hpc hd hd0

/-- **THE SUM OF THE SUBSET INDICATOR IS AN EXACT COUNT.** -/
private theorem jsp87sum_sub_indicator (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime)
    {S : Finset ℕ} (hS : S ⊆ P) :
    (∑ i ∈ jsp87ProgFull 0 1 P, (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℕ) else 0))
      = jsp87Prod P / (∏ p ∈ S, (p : ℕ)) := by
  calc (∑ i ∈ jsp87ProgFull 0 1 P, (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℕ) else 0))
      = ∑ _i ∈ (jsp87ProgFull 0 1 P).filter (fun i => ∀ p ∈ S, p ∣ i + 1),
          (1 : ℕ) := by
        rw [← Finset.sum_filter]
    _ = (((jsp87ProgFull 0 1 P).filter (fun i => ∀ p ∈ S, p ∣ i + 1)).card : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
    _ = jsp87Prod P / (∏ p ∈ S, (p : ℕ)) := jsp87card_div_subset P hpc hS
/-! ## §3  THE CLOSED FORM -/

/-- **THE CHARACTERISTIC FUNCTION OF THE PRIME-DIVISOR COUNT**: the mean, over the
canonical sample, of the phase `θ · #{p ∈ P : p ∣ i+1}`.

At the ground-truth scale (`K = 0`, `H = 1`) this is the object `jsp87Mean` of
the endgame of arXiv:2512.01739. -/
noncomputable def jsp87CharFun (P : Finset ℕ) (θ : ℝ) : ℂ :=
  jsp87CAvg (jsp87ProgFull 0 1 P) (fun i => jsp87e (θ * (jsp87Cnt P (i + 1))))

/-- **THE CAST OF A PRODUCT OF NATURALS.** -/
private theorem jsp87cast_prod (S : Finset ℕ) :
    (↑(∏ p ∈ S, (p : ℕ)) : ℂ) = ∏ p ∈ S, ((p : ℕ) : ℂ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert (s := S) (a := a) ha, Nat.cast_mul, ih]
    rw [Finset.prod_insert (s := S) (a := a) ha]

/-- **THE SUBSET SUM OVER THE SAMPLE IS THE CARDINALITY TIMES THE PRODUCT OF THE
RECIPROCALS OF THE SUBSET.** -/
private theorem jsp87sum_sub_indicator_c (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime)
    {S : Finset ℕ} (hS : S ⊆ P) :
    (∑ i ∈ jsp87ProgFull 0 1 P, (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0))
      = (jsp87Prod P : ℂ) * (∏ p ∈ S, ((1 / (p : ℝ)) : ℂ)) := by
  have hd : (∏ p ∈ S, (p : ℕ)) ∣ jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_dvd_prod_of_subset S P (fun p => p) hS
  have hd0 : (∏ p ∈ S, (p : ℕ)) ≠ 0 := by
    have hne : ∀ p ∈ S, (p : ℕ) ≠ 0 := fun p hp => (hpc p (hS hp)).ne_zero
    exact Finset.prod_ne_zero_iff.mpr hne
  have hdC0 : (↑(∏ p ∈ S, (p : ℕ)) : ℂ) ≠ 0 := by
    exact_mod_cast hd0
  calc (∑ i ∈ jsp87ProgFull 0 1 P, (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0))
      = ((∑ i ∈ jsp87ProgFull 0 1 P, (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℕ) else 0)) : ℂ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : ∀ p ∈ S, p ∣ i + 1 <;> simp [h]
      _ = ((jsp87Prod P / (∏ p ∈ S, (p : ℕ)) : ℕ) : ℂ) := by
        have h1 := congrArg (fun n : ℕ => (n : ℂ)) (jsp87sum_sub_indicator P hpc hS)
        simpa using h1
      _ = (jsp87Prod P : ℂ) * (∏ p ∈ S, ((1 / (p : ℝ)) : ℂ)) := by
        have key : ((∏ p ∈ S, ((p : ℕ) : ℂ))⁻¹)
            = ∏ p ∈ S, (((p : ℕ) : ℂ)⁻¹) :=
          (Finset.prod_inv_distrib (f := fun p => ((p : ℕ) : ℂ))).symm
        rw [Nat.cast_div hd hdC0, jsp87cast_prod S, div_eq_mul_inv, key]
        refine congrArg (fun w => (jsp87Prod P : ℂ) * w) ?_
        refine Finset.prod_congr rfl fun p _ => ?_
        simp

/-- **THE CHARACTER, AS A SUM OVER SUBSETS.** -/
theorem jsp87CharFun_eq_powSum (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) :
    jsp87CharFun P θ = ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
        * (∏ p ∈ S, ((1 / (p : ℝ)) : ℂ)) := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hcard : (jsp87ProgFull 0 1 P).card = jsp87Prod P :=
    jsp87ProgFull_card (by norm_num) P hpos
  have hL0 : (jsp87Prod P : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hexp : ∀ i : ℕ,
      jsp87e (θ * (jsp87Cnt P (i + 1) : ℝ))
        = ∏ p ∈ P, (if p ∣ i + 1 then jsp87e θ else 1) := by
    intro i
    rw [jsp87e_mul_nat θ (jsp87Cnt P (i + 1)), jsp87pow_cnt]
  have hsum : (∑ i ∈ jsp87ProgFull 0 1 P,
        jsp87e (θ * (jsp87Cnt P (i + 1) : ℝ)))
      = ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
          * ((jsp87Prod P : ℂ) * (∏ p ∈ S, ((1 / (p : ℝ)) : ℂ))) := by
    calc (∑ i ∈ jsp87ProgFull 0 1 P,
          jsp87e (θ * (jsp87Cnt P (i + 1) : ℝ)))
        = ∑ i ∈ jsp87ProgFull 0 1 P,
            ∏ p ∈ P, (if p ∣ i + 1 then jsp87e θ else 1) :=
          Finset.sum_congr rfl fun i _ => hexp i
      _ = ∑ i ∈ jsp87ProgFull 0 1 P, ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
            * (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0) :=
          Finset.sum_congr rfl fun i _ => jsp87expand_prod P (jsp87e θ) (i + 1)
      _ = ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
            * (∑ i ∈ jsp87ProgFull 0 1 P,
              (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0)) := by
        calc (∑ i ∈ jsp87ProgFull 0 1 P, ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
              * (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0))
            = ∑ S ∈ P.powerset, ∑ i ∈ jsp87ProgFull 0 1 P, ((jsp87e θ - 1) ^ S.card)
              * (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0) := Finset.sum_comm
          _ = ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
              * (∑ i ∈ jsp87ProgFull 0 1 P,
                (if ∀ p ∈ S, p ∣ i + 1 then (1 : ℂ) else 0)) := by
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ S ∈ P.powerset, ((jsp87e θ - 1) ^ S.card)
            * ((jsp87Prod P : ℂ) * (∏ p ∈ S, ((1 / (p : ℝ)) : ℂ))) := by
        refine Finset.sum_congr rfl fun S hS' => ?_
        refine congrArg (fun w => ((jsp87e θ - 1) ^ S.card) * w) ?_
        exact jsp87sum_sub_indicator_c P hpc (Finset.mem_powerset.mp hS')
  unfold jsp87CharFun jsp87CAvg
  rw [hsum, hcard, div_eq_mul_inv, Finset.sum_mul]
  field_simp

/-- **★ THE CLOSED FORM ★**  For every set `P` of primes, every `θ`,

```
jsp87CharFun P θ  =  ∏_{p ∈ P} ( 1 − 1/p + e θ / p ) .
```

The mean of the phase `θ · cnt P (·)` over the canonical whole-period sample is
a *finite product that is evaluated*, with no analytic input whatsoever: the
divisibility events are independent by CRT (round 127 for pairs, this file for
all subsets). -/
theorem jsp87CharFun_eq_prod (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) :
    jsp87CharFun P θ = ∏ p ∈ P, (1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ) := by
  rw [jsp87CharFun_eq_powSum P hpc θ]
  have hstep : ∀ S : Finset ℕ, ((jsp87e θ - 1) ^ S.card)
      * (∏ p ∈ S, ((1 / (p : ℝ)) : ℂ))
      = ∏ p ∈ S, (((jsp87e θ - 1) * ((1 / (p : ℝ)) : ℂ))) := by
    intro S
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun S _ => hstep S)]
  rw [← jsp87prod_sum P (fun p => ((jsp87e θ - 1) * ((1 / (p : ℝ)) : ℂ)))]
  exact Finset.prod_congr rfl
    (fun p _ => (show (1 + (jsp87e θ - 1) * ((1 / (p : ℝ)) : ℂ))
      = (1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ) by ring))


/-- **THE EMPTY PRIME SET: THE MEAN IS `1`.** -/
theorem jsp87CharFun_empty (θ : ℝ) : jsp87CharFun ∅ θ = 1 := by
  rw [jsp87CharFun_eq_prod _ (by simp) θ]
  simp

/-- **ONE PRIME: THE MEAN IS THE TWO-CLASS MEAN.** -/
theorem jsp87CharFun_singleton (p : ℕ) (θ : ℝ) (hp : Nat.Prime p) :
    jsp87CharFun {p} θ = 1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ := by
  rw [jsp87CharFun_eq_prod _ (by simpa using hp) θ]
  simp

/-- **TWO PRIMES: THE MEAN IS THE PRODUCT OF TWO SUCH FACTORS.** -/
theorem jsp87CharFun_pair (p q : ℕ) (θ : ℝ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) :
    jsp87CharFun {p, q} θ
      = (1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ)
        * (1 - ((1 / (q : ℝ)) : ℂ) + ((1 / (q : ℝ)) : ℂ) * jsp87e θ) := by
  rw [jsp87CharFun_eq_prod _ (by simp [hp, hq]) θ]
  simp [hne]
/-! ## §4  THE MODULUS: AN EXACT FORMULA, AND THE EXPONENTIAL DECAY -/

/-- **THE DECAY FACTOR OF ONE PRIME**: the loss of modulus contributed by the
prime `p`, namely `2 (1/p)(1 − 1/p)(1 − cos 2πθ)`. -/
noncomputable def jsp87CFfactor (p : ℕ) (θ : ℝ) : ℝ :=
  2 * ((p : ℝ)⁻¹) * (1 - ((p : ℝ)⁻¹)) * (1 - Real.cos (2 * Real.pi * θ))

/-- **THE FACTOR OF THE CLOSED FORM, IN THE FORM OF THE DECAY FACTOR.** -/
private theorem jsp87factor_conv (p : ℕ) (θ : ℝ) :
    (1 - ((1 / (p : ℝ)) : ℂ) + ((1 / (p : ℝ)) : ℂ) * jsp87e θ : ℂ)
      = (1 - Complex.ofReal ((p : ℝ)⁻¹) + Complex.ofReal ((p : ℝ)⁻¹) * jsp87e θ) := by
  simp only [div_eq_mul_inv, one_mul, Complex.ofReal_inv]

/-- **THE POLARISATION IDENTITY.** -/
private theorem jsp87polar (a b c s : ℝ) (hs : s ^ 2 + c ^ 2 = 1) :
    (a + b * c) ^ 2 + (b * s) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * c := by
  have hs' : c ^ 2 + s ^ 2 = 1 := by simpa [add_comm] using hs
  calc (a + b * c) ^ 2 + (b * s) ^ 2
      = a ^ 2 + 2 * a * b * c + b ^ 2 * (c ^ 2 + s ^ 2) := by ring
    _ = a ^ 2 + 2 * a * b * c + b ^ 2 := by
        have h2 : a ^ 2 + 2 * a * b * c + b ^ 2 * (c ^ 2 + s ^ 2)
            = a ^ 2 + 2 * a * b * c + b ^ 2 * 1 :=
          congrArg (fun x => a ^ 2 + 2 * a * b * c + b ^ 2 * x) hs'
        rw [h2, mul_one]
    _ = a ^ 2 + b ^ 2 + 2 * a * b * c := by ring

/-- **THE MODULUS SQUARED OF ONE FACTOR IS `1` MINUS THE DECAY FACTOR.** -/
private theorem jsp87factor_p (p : ℕ) (θ : ℝ) :
    ‖(1 - Complex.ofReal ((p : ℝ)⁻¹) + Complex.ofReal ((p : ℝ)⁻¹) * jsp87e θ)‖ ^ 2
      = 1 - jsp87CFfactor p θ := by
  have hre :
      (1 - Complex.ofReal ((p : ℝ)⁻¹) + Complex.ofReal ((p : ℝ)⁻¹) * jsp87e θ : ℂ).re
      = 1 - (p : ℝ)⁻¹ + (p : ℝ)⁻¹ * Real.cos (2 * Real.pi * θ) := by
    rw [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, jsp87e_re]
    simp [one_mul]
  have him :
      (1 - Complex.ofReal ((p : ℝ)⁻¹) + Complex.ofReal ((p : ℝ)⁻¹) * jsp87e θ : ℂ).im
      = 0 + (p : ℝ)⁻¹ * Real.sin (2 * Real.pi * θ) := by
    rw [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, jsp87e_im]
    simp [one_mul]
  rw [jsp87norm_sq_re_im, hre, him]
  have hkey := jsp87polar (a := 1 - (p : ℝ)⁻¹) (b := (p : ℝ)⁻¹)
    (c := Real.cos (2 * Real.pi * θ)) (s := Real.sin (2 * Real.pi * θ))
    (Real.sin_sq_add_cos_sq (2 * Real.pi * θ))
  unfold jsp87CFfactor
  nlinarith [hkey]

/-- **THE MODULUS SQUARED OF A PRODUCT IS THE PRODUCT OF THE MODULI.** -/
private theorem jsp87normSq_prod (S : Finset ℕ) (f : ℕ → ℂ) :
    ‖∏ p ∈ S, f p‖ ^ 2 = ∏ p ∈ S, ‖f p‖ ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert (s := S) (a := a) ha]
    rw [Complex.norm_mul, mul_pow, ih]
    rw [Finset.prod_insert (s := S) (a := a) ha]

/-- **THE EXACT MODULUS OF THE MEAN.** -/
theorem jsp87CharFun_normSq (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) :
    ‖jsp87CharFun P θ‖ ^ 2 = ∏ p ∈ P, (1 - jsp87CFfactor p θ) := by
  rw [jsp87CharFun_eq_prod P hpc θ, jsp87normSq_prod]
  exact Finset.prod_congr rfl fun p _ => by
    rw [jsp87factor_conv p θ]
    exact jsp87factor_p p θ

/-- **THE DECAY FACTOR OF A PRIME IS AT MOST `1`.** -/
theorem jsp87CFfactor_le_one (p : ℕ) (hp : Nat.Prime p) (θ : ℝ) :
    jsp87CFfactor p θ ≤ 1 := by
  have h2 : (2 : ℕ) ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast h2
  have hp0 : (0 : ℝ) < p := by positivity
  have hInv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ (a := (p : ℝ)) (b := (2 : ℝ)) hp0 (by norm_num)).mpr hpR
  have hrec : 2 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹) ≤ (1 / 2 : ℝ) := by
    have h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith
  have hcos : -1 ≤ Real.cos (2 * Real.pi * θ) := Real.neg_one_le_cos _
  have h1 : 1 - (p : ℝ)⁻¹ ≤ 1 := by
    have := inv_pos.mpr hp0
    linarith
  have hge : 0 ≤ 1 - Real.cos (2 * Real.pi * θ) := by
    linarith [Real.cos_le_one (2 * Real.pi * θ)]
  have hmul : (1 - Real.cos (2 * Real.pi * θ))
      * (2 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹))
      ≤ (1 - Real.cos (2 * Real.pi * θ)) * (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hrec hge
  unfold jsp87CFfactor
  nlinarith [hmul, hcos]


/-- **A POINTWISE INEQUALITY OF THE FACTORS PASSES TO THE PRODUCT.** -/
private theorem jsp87prod_nonneg (S : Finset ℕ) (f : ℕ → ℝ) (h : ∀ p ∈ S, 0 ≤ f p) :
    0 ≤ ∏ p ∈ S, f p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert (s := S) (a := a) ha]
    exact mul_nonneg (h a (Finset.mem_insert_self a S))
      (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

private theorem jsp87prod_le (S : Finset ℕ) (f g : ℕ → ℝ)
    (h : ∀ p ∈ S, f p ≤ g p) (hf : ∀ p ∈ S, 0 ≤ f p) (hg : ∀ p ∈ S, 0 ≤ g p) :
    (∏ p ∈ S, f p) ≤ (∏ p ∈ S, g p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert (s := S) (a := a) ha]
    rw [Finset.prod_insert (s := S) (a := a) ha]
    have hrec : ∀ p ∈ insert a S, f p ≤ g p := fun p hp => h p hp
    have hfrec : ∀ p ∈ insert a S, 0 ≤ f p := fun p hp => hf p hp
    have hgrec : ∀ p ∈ insert a S, 0 ≤ g p := fun p hp => hg p hp
    exact mul_le_mul (hrec a (Finset.mem_insert_self a S))
      (ih (fun p hp => hrec p (Finset.mem_insert_of_mem hp))
        (fun p hp => hfrec p (Finset.mem_insert_of_mem hp))
        (fun p hp => hgrec p (Finset.mem_insert_of_mem hp)))
      (jsp87prod_nonneg S f fun p hp => hfrec p (Finset.mem_insert_of_mem hp))
      (hgrec a (Finset.mem_insert_self a S))

/-- **THE MEAN IS SMALLER THAN THE EXPONENTIAL OF THE VARIANCE TIMES THE
DILATATION OF THE PHASE**: with `jsp87SqDefect` the variance of round 127. -/
theorem jsp87CharFun_normSq_le_exp (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) (θ : ℝ) :
    ‖jsp87CharFun P θ‖ ^ 2
      ≤ Real.exp (-(1 - Real.cos (2 * Real.pi * θ)) * (2 * jsp87SqDefect P)) := by
  have h1 : ∀ p ∈ P, 0 ≤ 1 - jsp87CFfactor p θ := by
    intro p hp
    have hlt := jsp87CFfactor_le_one p (hpc p hp) θ
    linarith
  have h2 : ∀ p ∈ P, 1 - jsp87CFfactor p θ
      ≤ Real.exp (-jsp87CFfactor p θ) := by
    intro p hp
    have hx := Real.add_one_le_exp (-jsp87CFfactor p θ)
    linarith
  have h3 : (∑ p ∈ P, jsp87CFfactor p θ)
      = (1 - Real.cos (2 * Real.pi * θ)) * (2 * jsp87SqDefect P) := by
    unfold jsp87CFfactor jsp87SqDefect
    simp only [div_eq_mul_inv]
    calc (∑ p ∈ P, 2 * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹) * (1 - Real.cos (2 * Real.pi * θ)))
        = ∑ p ∈ P, (1 - Real.cos (2 * Real.pi * θ))
            * (2 * ((p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹))) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = (1 - Real.cos (2 * Real.pi * θ))
            * (∑ p ∈ P, 2 * ((p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹))) := by
          rw [← Finset.mul_sum]
      _ = (1 - Real.cos (2 * Real.pi * θ))
            * (2 * ∑ p ∈ P, ((p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹))) := by
          refine congrArg (fun w => (1 - Real.cos (2 * Real.pi * θ)) * w) ?_
          rw [Finset.mul_sum]
      _ = (1 - Real.cos (2 * Real.pi * θ)) * (2 * jsp87SqDefect P) := by
          simp only [jsp87SqDefect, div_eq_mul_inv, one_mul]
  calc ‖jsp87CharFun P θ‖ ^ 2 = ∏ p ∈ P, (1 - jsp87CFfactor p θ) :=
      jsp87CharFun_normSq P hpc θ
    _ ≤ ∏ p ∈ P, Real.exp (-jsp87CFfactor p θ) := by
      refine jsp87prod_le P _ _ h2 h1 ?_
      intro p hp
      exact le_of_lt (Real.exp_pos _)
    _ = Real.exp (-(∑ p ∈ P, jsp87CFfactor p θ)) := by
        rw [← Real.exp_sum P (fun p => -jsp87CFfactor p θ), Finset.sum_neg_distrib]
    _ = Real.exp (-(1 - Real.cos (2 * Real.pi * θ)) * (2 * jsp87SqDefect P)) := by
      rw [h3, neg_mul]

/-! ## §4.1  The mean tends to zero: Euler's divergence, in the variance -/

/-- **THE VARIANCE, TIMES A POSITIVE CONSTANT, TENDS TO INFINITY.** -/
private theorem jsp87c_mul_variance_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun Y : ℕ => c * jsp87SqDefect (jsp87PrimeSet 2 Y))
      Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop.2 fun b => by
    have h1 := Filter.Tendsto.eventually_ge_atTop jsp87SqDefect_tendsto (b / c)
    filter_upwards [h1] with Y hY
    have hmul := mul_le_mul_of_nonneg_left hY hc.le
    have hdiv : c * (b / c) = b := by field_simp
    rw [hdiv] at hmul
    linarith

/-- **THE MEAN OF THE PHASE AT THE GROUND-TRUTH SCALE TENDSTO TO ZERO.**

The whole prime harmonic mass of Euler (round 125) enters through the
**variance** of round 127, so no correlation input is needed: at the
ground-truth scale the mean of the phase is a product of two-class means, and
each factor loses a fixed fraction of its modulus per prime. -/
theorem jsp87CharFun_norm_tendsto (θ : ℝ) (hcos : Real.cos (2 * Real.pi * θ) < 1) :
    Filter.Tendsto (fun Y => ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖)
      Filter.atTop (nhds 0) := by
  have hcq : (0 : ℝ) < 2 * (1 - Real.cos (2 * Real.pi * θ)) := by
    have h1 := Real.cos_le_one (2 * Real.pi * θ)
    linarith
  have hexp : Filter.Tendsto (fun Y : ℕ =>
      Real.exp (-(1 - Real.cos (2 * Real.pi * θ)) * (2 * jsp87SqDefect (jsp87PrimeSet 2 Y))))
      Filter.atTop (nhds 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (jsp87c_mul_variance_tendsto _ hcq)).congr' ?_
    filter_upwards [] with Y
    apply congrArg (fun x => Real.exp x)
    ring
  have hle : ∀ Y : ℕ, ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖ ^ 2
      ≤ Real.exp (-(1 - Real.cos (2 * Real.pi * θ))
          * (2 * jsp87SqDefect (jsp87PrimeSet 2 Y))) := fun Y =>
    jsp87CharFun_normSq_le_exp _ (fun r hr => jsp87PrimeSet_prime hr) θ
  have hA : Filter.Tendsto (fun Y => ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖ ^ 2)
      Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hmin : (0 : ℝ) < min ε 1 := by positivity
    have h1 := Metric.tendsto_nhds.mp hexp (min ε 1) hmin
    filter_upwards [h1] with Y hY
    have h3 : Real.exp (-(1 - Real.cos (2 * Real.pi * θ))
        * (2 * jsp87SqDefect (jsp87PrimeSet 2 Y))) < min ε 1 := by simpa using hY
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖)]
    exact lt_of_le_of_lt (hle Y) (lt_of_lt_of_le h3 (min_le_left _ _))
  have hB : Filter.Tendsto (fun Y => ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖)
      Filter.atTop (nhds 0) := by
    have hC := Real.continuous_sqrt.continuousAt.tendsto.comp hA
    rw [Real.sqrt_zero] at hC
    refine hC.congr' ?_
    filter_upwards [] with Y
    exact Real.sqrt_sq (Complex.norm_nonneg _)
  exact hB
/-! ## §5  THE JOIN WITH THE ENDGAME OF ARXIV:2512.01739 -/

/-- **THE MEAN OF THE ENDGAME AT THE GROUND-TRUTH SCALE IS THE CHARACTERISTIC
FUNCTION OF THE PRIME-DIVISOR COUNT.** -/
theorem jsp87Mean_ground_eq_charFun (Y : ℕ) (q : ℝ) :
    jsp87Mean 0 1 Y q = jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2) := by
  have hsep : jsp87Separation 0 1 = 2 := by
    unfold jsp87Separation
    norm_num
  have hmean : jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => jsp87e (jsp87Phase 0 1 Y q i))
      = jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => jsp87e ((q / 2) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1)))) := by
    refine congrArg (fun z : ℂ => z / ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℂ)) ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    show jsp87e (q * ∑ p' ∈ jsp87PrimeSet 2 Y, jsp87Xp0 (jsp87BinV 0) p' i 1)
        = jsp87e ((q / 2) * (jsp87Cnt (jsp87PrimeSet 2 Y) (i + 1)))
    rw [jsp87Phase_zero_one_primeSet]
  rw [jsp87Mean, jsp87Sample, hsep, jsp87CharFun, hmean]

/-- **THE CAST OF A DIVISION IS THE CARDINALITY TIMES THE RECIPROCAL.** -/
private theorem jsp87cast_div_recip (N p : ℕ) (hd : p ∣ N) (hp0 : p ≠ 0) :
    ((N / p : ℕ) : ℂ) = (N : ℂ) * ((1 / (p : ℝ)) : ℂ) := by
  have key : (↑p : ℂ) = (((p : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast rfl
  rw [Nat.cast_div (K := ℂ) hd (by exact_mod_cast hp0 : (↑p : ℂ) ≠ 0), key]
  simp [div_eq_mul_inv]

/-- **THE MEAN OF A TWO-CLUE VARIABLE OVER THE WHOLE PERIOD**, with the exact
fractions of the two classes: the class `p ∣ i+1` occupies a fraction `1/p` of a
whole period. -/
private theorem jsp87CAvg_ite (P : Finset ℕ) (hpc : ∀ r ∈ P, r.Prime) {p : ℕ} (hp : p ∈ P)
    (z : ℂ) :
    jsp87CAvg (jsp87ProgFull 0 1 P) (fun i => if p ∣ i + 1 then z else 1)
      = (1 - ((1 / (p : ℝ)) : ℂ)) + ((1 / (p : ℝ)) : ℂ) * z := by
  have hpos : 0 < jsp87Prod P := by
    unfold jsp87Prod
    exact Finset.prod_pos fun i hi => (hpc i hi).pos
  have hcard : (jsp87ProgFull 0 1 P).card = jsp87Prod P :=
    jsp87ProgFull_card (by norm_num) P hpos
  have hsub : ({p} : Finset ℕ) ⊆ P := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact hp
  have hcnt : ((jsp87ProgFull 0 1 P).filter (fun i => p ∣ i + 1)).card = jsp87Prod P / p := by
    have h := jsp87card_div_subset P hpc (S := {p}) hsub
    rw [show ((jsp87ProgFull 0 1 P).filter
          (fun i => ∀ q ∈ ({p} : Finset ℕ), q ∣ i + 1))
        = ((jsp87ProgFull 0 1 P).filter (fun i => p ∣ i + 1)) by
          exact Finset.filter_congr (fun i _ => by simp [Finset.mem_singleton])] at h
    rw [Finset.prod_singleton] at h
    simpa using h
  have hsum : (∑ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then (1 : ℂ) else 0))
      = (((jsp87Prod P / p : ℕ) : ℕ) : ℂ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hcnt]
  have hcomp : (∑ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then (0 : ℂ) else 1))
      = (((jsp87ProgFull 0 1 P).card : ℕ) : ℂ) - (((jsp87Prod P / p : ℕ) : ℕ) : ℂ) := by
    have hkey2 : ∀ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then (0 : ℂ) else 1)
        = (1 : ℂ) - (if p ∣ i + 1 then (1 : ℂ) else 0) := by
      intro i _
      by_cases h : p ∣ i + 1 <;> simp [h]
    rw [Finset.sum_congr rfl hkey2, Finset.sum_sub_distrib]
    simp [hsum, hcard]
  have hdvd : p ∣ jsp87Prod P := by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (f := id) (s := P) (a := p) hp
    refine ⟨c, ?_⟩
    unfold jsp87Prod
    simpa only [id_eq] using hc
  have hrec := jsp87cast_div_recip (jsp87Prod P) p hdvd
    ((hpc p hp).ne_zero)
  have hkey : ∀ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then z else 1)
      = (if p ∣ i + 1 then (1 : ℂ) else 0) * z
        + (if p ∣ i + 1 then (0 : ℂ) else 1) := by
    intro i _
    by_cases h : p ∣ i + 1 <;> simp [h]
  have hA : (∑ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then z else 1))
      = (((jsp87Prod P / p : ℕ) : ℕ) : ℂ) * z
        + ((jsp87Prod P : ℕ) : ℂ) - (((jsp87Prod P / p : ℕ) : ℕ) : ℂ) := by
    have hz : (∑ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then (1 : ℂ) else 0) * z)
        = (∑ i ∈ jsp87ProgFull 0 1 P, (if p ∣ i + 1 then (1 : ℂ) else 0)) * z :=
      (Finset.sum_mul (jsp87ProgFull 0 1 P)
        (fun i => if p ∣ i + 1 then (1 : ℂ) else 0) z).symm
    rw [Finset.sum_congr rfl hkey, Finset.sum_add_distrib, hz]
    rw [hsum, hcomp, hcard]
    ring
  have hN0 : (jsp87Prod P : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  unfold jsp87CAvg
  rw [hA, hcard, hrec]
  rw [div_eq_iff hN0]
  simp only [div_eq_mul_inv]
  ring

/-- **THE MEAN OF THE ENDGAME AT THE GROUND-TRUTH SCALE, IN CLOSED FORM.** -/
theorem jsp87Mean_ground_eq_prod (Y : ℕ) (q : ℝ) :
    jsp87Mean 0 1 Y q = ∏ p' ∈ jsp87PrimeSet 2 Y,
      (1 - ((1 / (p' : ℝ)) : ℂ) + ((1 / (p' : ℝ)) : ℂ) * jsp87e (q / 2)) := by
  rw [jsp87Mean_ground_eq_charFun]
  exact jsp87CharFun_eq_prod _ (fun r hr => jsp87PrimeSet_prime hr) (q / 2)

/-- **THE SINGLE-PRIME FACTOR OF THE PRODUCT OF THE SINGLE-PRIME MEANS.** -/
private theorem jsp87CAvg_single (Y : ℕ) (p' : ℕ) (hp' : p' ∈ jsp87PrimeSet 2 Y) (q : ℝ) :
    jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => jsp87e (q * jsp87Xp0 (jsp87BinV 0) p' i 1))
      = jsp87CAvg (jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y))
        (fun i => if p' ∣ i + 1 then jsp87e (q / 2) else 1) := by
  refine congrArg (fun z : ℂ => z / ((jsp87ProgFull 0 1 (jsp87PrimeSet 2 Y)).card : ℂ)) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  show jsp87e (q * jsp87Xp0 (jsp87BinV 0) p' i 1) = (if p' ∣ i + 1 then jsp87e (q / 2) else 1)
  rw [jsp87Xp0_binV_zero_one]
  by_cases h : p' ∣ i + 1
  · rw [if_pos h, if_pos h]
    congr 1
    ring
  · rw [if_neg h, if_neg h]
    simp [jsp87e]

/-- **THE PRODUCT OF THE SINGLE-PRIME MEANS, IN CLOSED FORM.** -/
theorem jsp87ProdMean_ground_eq_prod (Y : ℕ) (q : ℝ) :
    jsp87ProdMean 0 1 Y q = ∏ p' ∈ jsp87PrimeSet 2 Y,
      (1 - ((1 / (p' : ℝ)) : ℂ) + ((1 / (p' : ℝ)) : ℂ) * jsp87e (q / 2)) := by
  have hsep : jsp87Separation 0 1 = 2 := by
    unfold jsp87Separation
    norm_num
  rw [jsp87ProdMean, hsep, jsp87Sample, hsep]
  refine Finset.prod_congr rfl fun p' hp' => ?_
  rw [jsp87CAvg_single Y p' hp' q]
  exact jsp87CAvg_ite _ (fun r hr => jsp87PrimeSet_prime hr) hp' (jsp87e (q / 2))

/-- **★ HYPOTHESES (5.16)–(5.17) HOLD WITH THE CONSTANTS EXACTLY `0` ★**

At the ground-truth scale the complex mean of the phase **is** the product of
the single-prime means: the two errors of arXiv:2512.01739 (5.16)–(5.17)
vanish identically, so **two of the five sharp constants of the endgame are
free**. -/
theorem jsp87Err2z_ground_zero (Y : ℕ) (q : ℝ) : jsp87Err2z 0 1 Y q = 0 := by
  unfold jsp87Err2z
  have h1 := jsp87Mean_ground_eq_prod Y q
  have h2 := jsp87ProdMean_ground_eq_prod Y q
  rw [h1, h2]
  ring

/-- **THE COMPLEX ERROR OF (5.16)–(5.17) VANISHES.** -/
theorem jsp87Err2_ground_zero (Y : ℕ) (q : ℝ) : jsp87Err2 0 1 Y q = 0 := by
  rw [jsp87Err2_eq, jsp87Err2z_ground_zero]
  norm_num

/-- **(5.16)–(5.17) IS SATISFIED WITH `κ₄ = κ₅ = 0`.** -/
theorem jsp87Hypothesis1617_ground (q : ℝ) :
    jsp87Hypothesis1617 0 1 q 0 0 := by
    intro Z
    rw [jsp87Err2_ground_zero]
    norm_num/-! ## §6  THE DECISIVE NEGATIVE RESULT: (5.15) IS REFUTED AT LARGE HEIGHTS -/

/-- **THE ERROR OF (5.15) IS AT LEAST `1` MINUS THE MODULUS OF THE MEAN.** -/
theorem jsp87Err1_ground_sub_one (Y : ℕ) (q : ℝ) :
    1 - ‖jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)‖ ≤ jsp87Err1 0 1 Y q := by
  have h1 := jsp87Err1_eq 0 1 Y q
  have h2 := jsp87Mean_ground_eq_charFun Y q
  rw [h1]
  unfold jsp87Err1z
  rw [h2]
  have h3 := dist_triangle (1 : ℂ) (jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)) 0
  have h6 : dist (1 : ℂ) 0 = 1 := by norm_num [dist_eq_norm]
  have h5 : dist (1 : ℂ) (jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2))
      = ‖1 - jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)‖ :=
    dist_eq_norm (a := (1 : ℂ)) (jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2))
  have h7 : dist (jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)) 0
      = ‖jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)‖ :=
    (dist_eq_norm (a := jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)) (0 : ℂ)).trans
      (by rw [sub_zero])
  rw [h6, h5, h7] at h3
  rw [norm_sub_rev]
  linarith

/-- **THE ERROR OF (5.15) IS AT MOST `1` PLUS THE MODULUS OF THE MEAN.** -/
theorem jsp87Err1_ground_add_one (Y : ℕ) (q : ℝ) :
    jsp87Err1 0 1 Y q ≤ 1 + ‖jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)‖ := by
  have h1 := jsp87Err1_eq 0 1 Y q
  have h2 := jsp87Mean_ground_eq_charFun Y q
  rw [h1]
  unfold jsp87Err1z
  rw [h2]
  have h4 : ‖(1 : ℂ)‖ = 1 := by norm_num
  have h3 := norm_sub_le (a := jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)) (b := (1 : ℂ))
  rw [h4] at h3
  linarith

/-- **THE MEAN OF THE PHASE IS SMALL AT A LARGE HEIGHT** (the existential form
of `jsp87CharFun_norm_tendsto`). -/
theorem jsp87CharFun_norm_small (θ : ℝ) (hcos : Real.cos (2 * Real.pi * θ) < 1) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ Y : ℕ, ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖ < ε := by
  have h1 := Metric.tendsto_nhds.mp (jsp87CharFun_norm_tendsto θ hcos) ε hε
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.1 h1
  refine ⟨Y, ?_⟩
  have h3 := hY Y le_rfl
  simpa using h3

/-- **★ HYPOTHESIS (5.15) IS REFUTED AT ALL SUFFICIENTLY LARGE HEIGHTS ★**

At the ground-truth scale the deviation of the complex mean of the phase from
`1` **tends to `1`**: the mean itself tends to `0` (Euler's divergence, through
the variance of round 127).  Consequently (5.15) of arXiv:2512.01739 fails at
all large heights for every total constant `< 1`, in particular for the sharpness
value `3/30` of the endgame: the canonical whole-period sample is **the wrong
sample** for the endgame, and no choice of the three constants `κ₁, κ₂, κ₃` can
repair it. -/
theorem jsp87Hypothesis15_ground_false (q : ℝ) (hcos : Real.cos (2 * Real.pi * (q / 2)) < 1)
    (κ1 κ2 κ3 : ℝ) (hκ : κ1 + κ2 + κ3 < 1) :
    ¬ jsp87Hypothesis15 0 1 q κ1 κ2 κ3 := by
  intro h
  have hsum0 : κ1 + κ2 + κ3 < 1 := hκ
  obtain ⟨Y, hY⟩ := jsp87CharFun_norm_small (q / 2) hcos
    ((1 - (κ1 + κ2 + κ3)) / 2) (by linarith)
  have hlow := jsp87Err1_ground_sub_one Y q
  have hupp := h Y
  have : 1 - ‖jsp87CharFun (jsp87PrimeSet 2 Y) (q / 2)‖ > κ1 + κ2 + κ3 := by
    linarith
  linarith

/-- **THE ENDGAME OF §§5.3–5.14 CANNOT BE RUN ON THE CANONICAL SAMPLE AT THE
GROUND-TRUTH SCALE**: for every five constants, the conjunction of (5.15),
(5.16)–(5.17) and the sharpness `κ_j < 1/30` is unsatisfiable at `K = 0`, `H = 1`.

This is a *machine-checked* obstruction to the sample choice of rounds 116–127,
not to the theorem: the published proof must use a different (non-periodic)
sample. -/
theorem jsp87_endgame_ground_blocked (q : ℝ) (hcos : Real.cos (2 * Real.pi * (q / 2)) < 1)
    (κ1 κ2 κ3 κ4 κ5 : ℝ) (hκ : jsp87KappaSharp κ1 κ2 κ3 κ4 κ5) :
    ¬ ((jsp87Hypothesis15 0 1 q κ1 κ2 κ3) ∧ (jsp87Hypothesis1617 0 1 q κ4 κ5)) := by
  intro hcon
  have h15 := hcon.1
  have hsum : κ1 + κ2 + κ3 < 1 := by linarith [hκ.1, hκ.2.1, hκ.2.2.1]
  exact jsp87Hypothesis15_ground_false q hcos κ1 κ2 κ3 hsum h15

/-- **THE SHARPNESS OF THE TWO FREE CONSTANTS IS FREE**: (5.16)–(5.17) hold with
`κ₄ = κ₅ = 0` while (5.15) cannot hold at all large heights.  The two sides of the
endgame therefore cannot be reconciled by shrinking `κ₄, κ₅`. -/
theorem jsp87_ground_dichotomy (q : ℝ) (hcos : Real.cos (2 * Real.pi * (q / 2)) < 1) :
    (jsp87Hypothesis1617 0 1 q 0 0)
      ∧ ¬ (∃ κ1 κ2 κ3 : ℝ, κ1 + κ2 + κ3 < 1 ∧ jsp87Hypothesis15 0 1 q κ1 κ2 κ3) :=
  ⟨jsp87Hypothesis1617_ground q, fun ⟨κ1, κ2, κ3, hκ, h15⟩ =>
    jsp87Hypothesis15_ground_false q hcos κ1 κ2 κ3 hκ h15⟩

/-- **SUMMARY OF ROUND 128.**  The endgame mean at the ground-truth scale is a
closed-form product; its modulus is exact; it tends to `0`; the error of (5.15)
tends to `1`; (5.16)–(5.17) is an identity; and the endgame cannot be run on the
canonical whole-period sample. -/
theorem jsp87_charFun_summary (θ : ℝ) (hcos : Real.cos (2 * Real.pi * θ) < 1) :
    Filter.Tendsto (fun Y => ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖)
        Filter.atTop (nhds 0)
      ∧ (∀ ε : ℝ, 0 < ε → ∃ Y : ℕ, ‖jsp87CharFun (jsp87PrimeSet 2 Y) θ‖ < ε) :=
  ⟨jsp87CharFun_norm_tendsto θ hcos,
    fun ε hε => jsp87CharFun_norm_small θ hcos ε hε⟩