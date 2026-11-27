import FormalConjectures.ErdosProblems.«688»

-- Reduction Erdos688.erdos_688.variants.lglglg_over_lglg_is_big_o.R1 of Erdős Problem 688 — lglglg over lglg is big o
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Rankin-type covering reduction of `ε_n ≫ logloglog n / loglog n`

Erdős [Er80, p. 106] says that `ε_n ≫ log log log n / log log n` is not difficult. We prove the
covering construction behind it and isolate its three analytic inputs as hypotheses:

1. `H1` (Mertens-type): `∑_{t < p ≤ t²} 1/p ≥ 1/20` for all large `t`
   (the truth is `→ log 2`).
2. `H2` (Rankin / de Bruijn smooth-number bound): for some `A > 0`, the number of
   `n^{logloglog n / (A loglog n)}`-smooth integers in `[1, n]` is at most `n / (16 log n)`
   for large `n` (the truth is `n (log n)^{-A(1+o(1))}`).
3. `H3` (Chebyshev-type): `[n/4, n]` contains at least `n / (4 log n)` primes for large `n`.

The construction (proved here, unconditionally): put `δ = logloglog n / (A' loglog n)`,
`ε = δ / 2^60`, `z = ⌊n^ε⌋`, `w = z^(2^60) ≤ n^δ`.
* every prime `p ∈ (w, n/4]` takes the class `0`; the integers of `[1, n]` left over are
  `w`-smooth or are multiples of a prime `q ∈ (n/4, n]` (at most `3` per `q`);
* the primes `p ∈ (z, w]` take greedy classes (pigeonhole), which multiplies the number of
  survivors by at most `∏ (1 - 1/p) ≤ exp (-∑ 1/p) ≤ exp (-3) ≤ 1/8` (by `H1`, iterated 60 times);
* each remaining survivor is matched injectively with its own prime `q ∈ (n/4, n]` (by `H2`, `H3`).
All primes used exceed `z ≥ n^ε - 1`, so `ε_n ≥ ε`, which gives the bound.
-/

namespace OMA.R_Erdos688_erdos_688_variants_lglglg_over_lglg_is_big_o_R1

open Real Filter Finset

/-- Mertens-type lower bound: the reciprocals of the primes in `(t, t²]` sum to at least `1/20`
for every sufficiently large `t`. -/
def H1 : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
    (1 : ℝ) / 20 ≤ ∑ p ∈ (Finset.Ioc t (t ^ 2)).filter Nat.Prime, ((p : ℝ))⁻¹

/-- Rankin-type smooth-number bound: for some `A > 0` and all large `n`, at most
`n / (16 log n)` integers `m ∈ [1, n]` have all their prime factors `≤ n ^ (logloglog n / (A loglog n))`. -/
def H2 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
    ((((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors,
        ((p : ℕ) : ℝ) ≤ (n : ℝ) ^ (Real.log (Real.log (Real.log (n : ℝ))) /
          (A * Real.log (Real.log (n : ℝ))))).card : ℕ) : ℝ) ≤
      (n : ℝ) / (16 * Real.log (n : ℝ))

/-- Chebyshev-type lower bound: for all large `n` there are at least `n / (4 log n)` primes in
`(⌊n/4⌋, n]`. -/
def H3 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (n : ℝ) / (4 * Real.log (n : ℝ)) ≤ (((Finset.Ioc (n / 4) n).filter Nat.Prime).card : ℝ)

/-- Greedy (pigeonhole) choice of classes: one class per modulus in `P` can be chosen so that the
survivors in `S` are at most `|S| ∏_{p ∈ P} (1 - 1/p)`. -/
lemma greedy (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (S : Finset ℕ) :
    ∃ a : ℕ → ℕ, (((S.filter fun m : ℕ => ∀ p ∈ P, ¬ (a p ≡ m [MOD p])).card : ℕ) : ℝ) ≤
      (S.card : ℝ) * ∏ p ∈ P, (1 - ((p : ℝ))⁻¹) := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert p P hpP ih =>
    obtain ⟨a, ha⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
    have hp : 0 < p := hP p (Finset.mem_insert_self p P)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    set T := S.filter fun m : ℕ => ∀ q ∈ P, ¬ (a q ≡ m [MOD q]) with hT
    obtain ⟨r, hr, hrT⟩ : ∃ r ∈ Finset.range p,
        (T.card : ℝ) / p ≤ (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ) := by
      apply Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      · intro m _
        exact Finset.mem_range.2 (Nat.mod_lt _ hp)
      · exact ⟨0, Finset.mem_range.2 hp⟩
      · rw [Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hpR.ne']
    have hrp : r < p := Finset.mem_range.1 hr
    refine ⟨Function.update a p r, ?_⟩
    have key : (S.filter fun m : ℕ => ∀ q ∈ insert p P, ¬ (Function.update a p r q ≡ m [MOD q])) =
        T.filter fun m : ℕ => ¬ (m % p = r) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp, hT,
        Function.update_self]
      have hrr : r % p = r := Nat.mod_eq_of_lt hrp
      constructor
      · rintro ⟨hmS, h1, h2⟩
        refine ⟨⟨hmS, fun q hq => ?_⟩, ?_⟩
        · have hqp : q ≠ p := fun h => hpP (h ▸ hq)
          simpa [Function.update_of_ne hqp] using h2 q hq
        · intro hm
          apply h1
          show r % p = m % p
          rw [hrr, hm]
      · rintro ⟨⟨hmS, h2⟩, h1⟩
        refine ⟨hmS, ?_, fun q hq => ?_⟩
        · intro h
          apply h1
          have : r % p = m % p := h
          rw [hrr] at this
          exact this.symm
        · have hqp : q ≠ p := fun h => hpP (h ▸ hq)
          simpa [Function.update_of_ne hqp] using h2 q hq
    rw [key]
    have hsub : T.filter (fun m : ℕ => m % p = r) ⊆ T := Finset.filter_subset _ _
    have hcard : (((T.filter fun m : ℕ => ¬ (m % p = r)).card : ℕ) : ℝ) =
        (T.card : ℝ) - (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not (s := T) (fun m : ℕ => m % p = r)
      have h' : (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ) +
          (((T.filter fun m : ℕ => ¬ (m % p = r)).card : ℕ) : ℝ) = (T.card : ℝ) := by
        exact_mod_cast h
      linarith
    rw [hcard, Finset.prod_insert hpP]
    have h1p : 0 ≤ 1 - ((p : ℝ))⁻¹ := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ this
    calc (T.card : ℝ) - (((T.filter fun m : ℕ => m % p = r).card : ℕ) : ℝ)
        ≤ T.card - T.card / p := by linarith
      _ = T.card * (1 - ((p : ℝ))⁻¹) := by ring
      _ ≤ (S.card * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)) * (1 - ((p : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_right ha h1p
      _ = S.card * ((1 - ((p : ℝ))⁻¹) * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)) := by ring

/-- `∏ (1 - 1/p) ≤ exp (-∑ 1/p)`. -/
lemma prod_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    ∏ p ∈ P, (1 - ((p : ℝ))⁻¹) ≤ Real.exp (-∑ p ∈ P, ((p : ℝ))⁻¹) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hP p hp
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ this
  · intro p _
    have := Real.add_one_le_exp (-((p : ℝ))⁻¹)
    linarith

/-- Iterating `H1` along `z, z², z⁴, …`. -/
lemma sum_recip_iter (T : ℕ)
    (hH1 : ∀ t : ℕ, T ≤ t → (1 : ℝ) / 20 ≤ ∑ p ∈ (Finset.Ioc t (t ^ 2)).filter Nat.Prime, ((p : ℝ))⁻¹)
    (z : ℕ) (hz : T ≤ z) (hz1 : 1 ≤ z) : ∀ k : ℕ,
    (k : ℝ) / 20 ≤ ∑ p ∈ (Finset.Ioc z (z ^ (2 ^ k))).filter Nat.Prime, ((p : ℝ))⁻¹
  | 0 => by simp
  | k + 1 => by
    have ih := sum_recip_iter T hH1 z hz hz1 k
    have hzk : z ≤ z ^ (2 ^ k) := Nat.le_self_pow (by positivity) z
    have hzk2 : z ^ (2 ^ k) ≤ (z ^ (2 ^ k)) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hpow : (z ^ (2 ^ k)) ^ 2 = z ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    have hsplit : Finset.Ioc z (z ^ (2 ^ (k + 1))) =
        Finset.Ioc z (z ^ (2 ^ k)) ∪ Finset.Ioc (z ^ (2 ^ k)) ((z ^ (2 ^ k)) ^ 2) := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc hzk hzk2, hpow]
    have hdisj : Disjoint (Finset.Ioc z (z ^ (2 ^ k))) (Finset.Ioc (z ^ (2 ^ k)) ((z ^ (2 ^ k)) ^ 2)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Ioc] at hx1 hx2
      omega
    rw [hsplit, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]
    have h2 := hH1 (z ^ (2 ^ k)) (le_trans hz hzk)
    push_cast
    linarith

/-- If `ε` is admissible then `ε ≤ ε_n`. -/
lemma le_epsilonFunction {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (h : Erdos688.Erdos688Prop n ε) :
    ε ≤ Erdos688.epsilonFunction n := by
  unfold Erdos688.epsilonFunction
  refine le_csSup ⟨1, fun ε' hε' => ?_⟩ h
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha⟩ := hε'
  obtain ⟨p, _, hlt', hpn, _⟩ := ha 1 le_rfl hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ ε' := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ ε' := Real.rpow_le_rpow_of_exponent_le hn1 hlt.le
  have h2 : (p : ℝ) ≤ n := by exact_mod_cast hpn
  linarith

/-- The covering construction: classes `0` on `(w, n/4]`, given classes `a₁` on `(z, w]`, and an
injective matching of the remaining survivors with the primes of `(n/4, n]`. -/
lemma cover (n z w u : ℕ) (ε : ℝ) (hzw : z ≤ w) (hw : w ≤ u) (hun : u ≤ n)
    (hz : (n : ℝ) ^ ε < (z : ℝ) + 1) (a₁ : ℕ → ℕ)
    (hS : (((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p])).card ≤
      ((Finset.Ioc u n).filter Nat.Prime).card) :
    Erdos688.Erdos688Prop n ε := by
  classical
  set S₂ := ((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p]) with hS₂
  set B := (Finset.Ioc u n).filter Nat.Prime with hB
  have hcardT : Fintype.card S₂ ≤ Fintype.card B := by
    simpa only [Fintype.card_coe] using hS
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardT
  let a₂ : ℕ → ℕ := fun q => if h : ∃ m : S₂, ((e m : B) : ℕ) = q then ((Classical.choose h : S₂) : ℕ) else 0
  have ha₂ : ∀ m (hm : m ∈ S₂), a₂ ((e ⟨m, hm⟩ : B) : ℕ) = m := by
    intro m hm
    have h : ∃ m' : S₂, ((e m' : B) : ℕ) = ((e ⟨m, hm⟩ : B) : ℕ) := ⟨⟨m, hm⟩, rfl⟩
    simp only [a₂, dif_pos h]
    have hc := Classical.choose_spec h
    have : Classical.choose h = (⟨m, hm⟩ : S₂) := e.injective (Subtype.ext hc)
    rw [this]
  refine ⟨fun p => if p ≤ w then a₁ p else if p ≤ u then 0 else a₂ p, ?_⟩
  have hbig : ∀ p : ℕ, z < p → (n : ℝ) ^ ε < p := by
    intro p hp
    have : (z : ℝ) + 1 ≤ p := by exact_mod_cast hp
    linarith
  have hn4 : u ≤ n := hun
  intro m hm1 hmn
  by_cases h1 : ∃ p ∈ (Finset.Ioc w u).filter Nat.Prime, p ∣ m
  · obtain ⟨p, hp, hpm⟩ := h1
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    refine ⟨p, hp.2, hbig p (by omega), by omega, ?_⟩
    have hnw : ¬ p ≤ w := by omega
    simp only [hnw, if_false, hp.1.2, if_true]
    exact (Nat.modEq_zero_iff_dvd.2 hpm).symm
  · by_cases h2 : ∃ p ∈ (Finset.Ioc z w).filter Nat.Prime, a₁ p ≡ m [MOD p]
    · obtain ⟨p, hp, hpm⟩ := h2
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      refine ⟨p, hp.2, hbig p hp.1.1, by omega, ?_⟩
      simp only [hp.1.2, if_true]
      exact hpm
    · have hmS : m ∈ S₂ := by
        rw [hS₂, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        push_neg at h1 h2
        exact ⟨⟨⟨hm1, hmn⟩, fun p hp => h1 p hp⟩, fun p hp => h2 p hp⟩
      set q : ℕ := ((e ⟨m, hmS⟩ : B) : ℕ) with hq
      have hqB : q ∈ B := (e ⟨m, hmS⟩ : B).2
      rw [hB, Finset.mem_filter, Finset.mem_Ioc] at hqB
      refine ⟨q, hqB.2, hbig q (by omega), hqB.1.2, ?_⟩
      have hnw : ¬ q ≤ w := by omega
      have hn4' : ¬ q ≤ u := by omega
      simp only [hnw, hn4', if_false]
      rw [hq, ha₂ m hmS]

/-- Survivors of the classes `0` on `(w, n/4]` are `w`-smooth or multiples of a prime of `(n/4, n]`. -/
lemma card_survivors_le (n w u : ℕ) (_hw : w ≤ u) (hu4 : n < 4 * (u + 1)) :
    (((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card : ℝ) ≤
      (((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card : ℝ) +
        3 * (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := by
  classical
  set B := (Finset.Ioc u n).filter Nat.Prime with hB
  have hsub : ((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m) ⊆
      ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w) ∪
        B.biUnion (fun q => (Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    by_cases hs : ∀ p ∈ m.primeFactors, p ≤ w
    · exact Or.inl ⟨Finset.mem_Icc.2 hm.1, hs⟩
    · push_neg at hs
      obtain ⟨p, hpf, hpw⟩ := hs
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpf
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hpf
      right
      have hpn : p ≤ n := le_trans (Nat.le_of_dvd (by omega) hpm) hm.1.2
      have hp4 : u < p := by
        by_contra hle
        push_neg at hle
        exact hm.2 p (by rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hpw, hle⟩, hp⟩) hpm
      refine ⟨p, ?_, ?_⟩
      · rw [hB, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hp4, hpn⟩, hp⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨hm.1, hpm⟩
  have hmult : ∀ q ∈ B, ((Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)).card ≤ 3 := by
    intro q hq
    rw [hB, Finset.mem_filter, Finset.mem_Ioc] at hq
    have hq0 : 0 < q := hq.2.pos
    have hnq : n / q ≤ 3 := by
      rw [Nat.div_le_iff_le_mul_add_pred hq0]
      omega
    calc ((Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)).card ≤ (Finset.Icc 1 (n / q)).card := by
          apply Finset.card_le_card_of_injOn (fun m : ℕ => m / q)
          · intro m hm
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
            rw [Finset.mem_coe, Finset.mem_Icc]
            obtain ⟨⟨hm1, hmn⟩, hqm⟩ := hm
            refine ⟨?_, Nat.div_le_div_right hmn⟩
            have : q ≤ m := Nat.le_of_dvd (by omega) hqm
            exact (Nat.one_le_div_iff hq0).2 this
          · intro m₁ hm₁ m₂ hm₂ h
            rw [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
            have e1 := Nat.mul_div_cancel' hm₁.2
            have e2 := Nat.mul_div_cancel' hm₂.2
            simp only at h
            rw [← e1, ← e2, h]
      _ = n / q := by simp
      _ ≤ 3 := hnq
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w)
    (B.biUnion (fun q => (Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)))
  have h3 := Finset.card_biUnion_le (s := B) (t := fun q => (Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m))
  have h4 : ∑ q ∈ B, ((Finset.Icc 1 n).filter (fun m : ℕ => q ∣ m)).card ≤ ∑ q ∈ B, 3 :=
    Finset.sum_le_sum hmult
  rw [Finset.sum_const, smul_eq_mul] at h4
  have : ((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card ≤
      ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card + 3 * B.card := by
    omega
  exact_mod_cast this

/-- Counting step: greedy classes on `(z, w]` leave at most as many survivors as there are primes
in `(u, n]`, provided `∏_{z < p ≤ w} (1 - 1/p) ≤ 1/8` and the `w`-smooth numbers are few. -/
lemma count_step (n z w u : ℕ) (hw : w ≤ u) (hu4 : n < 4 * (u + 1))
    (hprod : ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹) ≤ 1 / 8)
    (hsm : ((((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card : ℕ) : ℝ) ≤
      (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4) :
    ∃ a₁ : ℕ → ℕ, (((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p])).card ≤
      ((Finset.Ioc u n).filter Nat.Prime).card := by
  obtain ⟨a₁, ha₁⟩ := greedy ((Finset.Ioc z w).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.1 hp).2.pos)
    ((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m)
  refine ⟨a₁, ?_⟩
  have hsurv := card_survivors_le n w u hw hu4
  have hB0 : (0 : ℝ) ≤ (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := Nat.cast_nonneg _
  have key : (((((Finset.Icc 1 n).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).filter fun m : ℕ =>
        ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, ¬ (a₁ p ≡ m [MOD p])).card : ℕ) : ℝ) ≤
      (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := by
    refine le_trans ha₁ ?_
    calc ((((Finset.Icc 1 n).filter fun m : ℕ =>
          ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card : ℕ) : ℝ) *
          ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹)
        ≤ ((((Finset.Icc 1 n).filter fun m : ℕ =>
          ∀ p ∈ (Finset.Ioc w u).filter Nat.Prime, ¬ p ∣ m).card : ℕ) : ℝ) * (1 / 8) :=
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
      _ ≤ ((((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4 +
            3 * (((Finset.Ioc u n).filter Nat.Prime).card : ℝ)) * (1 / 8) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          linarith
      _ ≤ (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) := by nlinarith
  exact_mod_cast key

theorem main : H1 → H2 → H3 → type_of% @Erdos688.erdos_688.variants.lglglg_over_lglg_is_big_o := by
  rintro ⟨T, hT⟩ ⟨A, hA, hH2⟩ hH3
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 60 := ⟨60, rfl⟩
  set A' : ℝ := max A 2 with hA'
  have hA'2 : (2 : ℝ) ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  have hA'pos : 0 < A' := by linarith
  set K : ℝ := ((2 ^ k : ℕ) : ℝ) with hK
  have hKpos : 0 < K := by positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlog3 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog2
  have hT1 : (0 : ℝ) ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  set C : ℝ := K * A' * (Real.log ((T : ℝ) + 1) + 1) with hC
  have hCpos : 0 < C := by positivity
  have hlo : ∀ᶠ n : ℕ in atTop, C * Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    have hb := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / C by positivity)
    filter_upwards [hlog.eventually hb, hlog.eventually_ge_atTop 0] with n h1 h2
    simp only [Real.norm_eq_abs, id] at h1
    rw [abs_of_nonneg h2] at h1
    have h3 : Real.log (Real.log n) ≤ 1 / C * Real.log n :=
      le_trans (le_abs_self _) h1
    calc C * Real.log (Real.log n) ≤ C * (1 / C * Real.log n) :=
          mul_le_mul_of_nonneg_left h3 hCpos.le
      _ = Real.log n := by field_simp
  refine Asymptotics.IsBigO.of_bound (K * A') ?_
  filter_upwards [hlo, hlog3.eventually_ge_atTop 1, hlog2.eventually_ge_atTop 1,
    eventually_ge_atTop 25, hH2, hH3] with n hlo' hL3 hL2 hn25 hH2n hH3n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  set L2 := Real.log (Real.log (n : ℝ)) with hL2def
  set L3 := Real.log L2 with hL3def
  have hL2pos : 0 < L2 := by linarith
  have hL3nn : 0 ≤ L3 := by linarith
  have hL3L2 : L3 ≤ L2 := by
    have := Real.log_le_sub_one_of_pos hL2pos
    linarith
  set δ := L3 / (A' * L2) with hδ
  have hδnn : 0 ≤ δ := by positivity
  have hδle : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith
  have hδA : δ ≤ L3 / (A * L2) := by
    apply div_le_div_of_nonneg_left hL3nn (by positivity)
    exact mul_le_mul_of_nonneg_right hAA' hL2pos.le
  set ε := δ / K with hε
  have hεnn : 0 ≤ ε := by positivity
  -- `n ^ ε ≥ T + 1`
  have key : Real.log ((T : ℝ) + 1) ≤ Real.log n * ε := by
    have e1 : Real.log n * ε = L3 * Real.log n / (A' * L2 * K) := by
      rw [hε, hδ]; field_simp
    rw [e1, le_div_iff₀ (by positivity)]
    have h1 : Real.log n ≤ L3 * Real.log n := by nlinarith
    have h2 : Real.log ((T : ℝ) + 1) * (A' * L2 * K) ≤ C * L2 := by
      rw [hC]; nlinarith [mul_pos hA'pos hKpos]
    linarith
  have hzT' : ((T + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos hnpos]
    push_cast
    calc (T : ℝ) + 1 = Real.exp (Real.log ((T : ℝ) + 1)) := by
          rw [Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log n * ε) := Real.exp_le_exp.2 key
  set z := ⌊(n : ℝ) ^ ε⌋₊ with hz
  have hzT : T + 1 ≤ z := Nat.le_floor hzT'
  have hz1 : 1 ≤ z := by omega
  set w := z ^ (2 ^ k) with hw
  have hzw : z ≤ w := Nat.le_self_pow (by positivity) z
  have hwR : (w : ℝ) ≤ (n : ℝ) ^ δ := by
    have hfl : (z : ℝ) ≤ (n : ℝ) ^ ε := Nat.floor_le (by positivity)
    calc (w : ℝ) = (z : ℝ) ^ (2 ^ k : ℕ) := by rw [hw]; push_cast; ring
      _ ≤ ((n : ℝ) ^ ε) ^ (2 ^ k : ℕ) := pow_le_pow_left₀ (by positivity) hfl _
      _ = (n : ℝ) ^ (ε * ((2 ^ k : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      _ = (n : ℝ) ^ δ := by
          congr 1
          rw [hε, ← hK]; field_simp
  have hw4 : w ≤ n / 4 := by
    have hs : Real.sqrt n ≥ 5 := by
      rw [ge_iff_le, Real.le_sqrt (by norm_num) hnpos.le]
      have : (25 : ℝ) ≤ n := by exact_mod_cast hn25
      linarith
    have hsq := Real.sq_sqrt hnpos.le
    have h1 : (n : ℝ) ^ δ ≤ Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hn1 hδle
    have h2 : (w : ℝ) * 4 + 4 ≤ n := by nlinarith
    have h3 : w * 4 + 4 ≤ n := by exact_mod_cast h2
    omega
  set u := n / 4 with hu
  have hu4 : n < 4 * (u + 1) := by omega
  have hun : u ≤ n := by omega
  have hP₁pos : ∀ p ∈ (Finset.Ioc z w).filter Nat.Prime, 0 < p :=
    fun p hp => (Finset.mem_filter.1 hp).2.pos
  -- the product over `(z, w]` is at most `1/8`
  have hsum : (3 : ℝ) ≤ ∑ p ∈ (Finset.Ioc z w).filter Nat.Prime, ((p : ℝ))⁻¹ := by
    have := sum_recip_iter T hT z (by omega) hz1 k
    rw [hw]
    have hk3 : (3 : ℝ) ≤ (k : ℝ) / 20 := by rw [hk]; norm_num
    linarith
  have hprod : ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹) ≤ 1 / 8 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have he3 : (8 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
    calc ∏ p ∈ (Finset.Ioc z w).filter Nat.Prime, (1 - ((p : ℝ))⁻¹)
        ≤ Real.exp (-∑ p ∈ (Finset.Ioc z w).filter Nat.Prime, ((p : ℝ))⁻¹) := prod_le_exp _ hP₁pos
      _ ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp 3 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / 8 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- smooth numbers
  have hsm : ((((Finset.Icc 1 n).filter fun m : ℕ => ∀ p ∈ m.primeFactors, p ≤ w).card : ℕ) : ℝ) ≤
      (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4 := by
    have hBn : (n : ℝ) / (16 * Real.log (n : ℝ)) ≤ (((Finset.Ioc u n).filter Nat.Prime).card : ℝ) / 4 := by
      have : (n : ℝ) / (16 * Real.log (n : ℝ)) = ((n : ℝ) / (4 * Real.log (n : ℝ))) / 4 := by
        rw [div_div]; congr 1; ring
      rw [this]; linarith
    refine le_trans (le_trans ?_ hH2n) hBn
    exact_mod_cast Finset.card_le_card (by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, fun p hpf => ?_⟩
      have h1 : (p : ℝ) ≤ w := by exact_mod_cast hm.2 p hpf
      calc (p : ℝ) ≤ w := h1
        _ ≤ (n : ℝ) ^ δ := hwR
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hδA)
  obtain ⟨a₁, hS2⟩ := count_step n z w u hw4 hu4 hprod hsm
  have hcov := cover n z w u ε hzw hw4 hun (Nat.lt_floor_add_one _) a₁ hS2
  have hle := le_epsilonFunction (show 1 ≤ n by omega) hcov
  have hfn : L3 / L2 = K * A' * ε := by
    rw [hε, hδ]; field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L3 / L2), hfn]
  have : ε ≤ |Erdos688.epsilonFunction n| := le_trans hle (le_abs_self _)
  exact mul_le_mul_of_nonneg_left this (by positivity)

end OMA.R_Erdos688_erdos_688_variants_lglglg_over_lglg_is_big_o_R1
