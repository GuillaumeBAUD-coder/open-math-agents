import OMAStatements.S_mo_284994

-- Problem: A congruence involving roots of unity
-- Upstream: formal-conjectures statements/mo-284994.lean:0 (declaration OMA.S_mo_284994.main)
-- Credit: @julianibarz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

namespace RootCongruence

lemma eval_integral {z : ℂ} (hz : IsIntegral ℤ z) (f : ℤ[X]) :
    IsIntegral ℤ (aeval z f) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [map_add] using hf.add hg
  | monomial k a =>
    simpa only [aeval_monomial] using
      (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := a)).mul (hz.pow k)

lemma frobenius_quotient (p : ℕ) (hp : p.Prime) (f : ℤ[X]) :
    ∃ g : ℤ[X], f.comp (X ^ p) - f ^ p = C (p : ℤ) * g := by
  letI : Fact p.Prime := ⟨hp⟩
  have hF (F : (ZMod p)[X]) : F.comp (X ^ p) = F ^ p := by
    simpa only [ZMod.frobenius_zmod, map_id, expand_eq_comp_X_pow] using
      map_frobenius_expand p F
  have hm : (f.comp (X ^ p) - f ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    simp only [Polynomial.map_sub, map_comp, Polynomial.map_pow, map_X, hF, sub_self]
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have hi := congrArg (fun q : (ZMod p)[X] => q.coeff i) hm
  simpa only [coeff_map, Int.coe_castRingHom, coeff_zero] using hi

lemma pow_lift (p e : ℕ) (he : 1 ≤ e) (a b : ℤ)
    (h : (p : ℤ) ^ e ∣ a - b) : (p : ℤ) ^ (e + 1) ∣ a ^ p - b ^ p := by
  have hp : (p : ℤ) ∣ a - b := by
    simpa only [pow_one] using (pow_dvd_pow (p : ℤ) he).trans h
  have hg := dvd_geom_sum₂_self hp
  rw [pow_succ, ← geom_sum₂_mul]
  simpa only [mul_comm] using mul_dvd_mul hg h

lemma eval_relation (p : ℕ) (f g : ℤ[X])
    (hfg : f.comp (X ^ p) - f ^ p = C (p : ℤ) * g) (z : ℂ) :
    aeval (z ^ p) f - (aeval z f) ^ p = (p : ℂ) * aeval z g := by
  have h := congrArg (aeval z) hfg
  simpa only [map_sub, aeval_comp, map_pow, aeval_X, map_mul, aeval_C,
    map_natCast] using h

lemma quotient_values (p : ℕ) (hp : p.Prime) (f g : ℤ[X])
    (hfg : f.comp (X ^ p) - f ^ p = C (p : ℤ) * g)
    {z : ℂ} (hz : IsIntegral ℤ z)
    (hf : ∀ j : ℕ, ∃ a : ℤ, aeval (z ^ j) f = (a : ℂ)) :
    ∀ j : ℕ, ∃ a : ℤ, aeval (z ^ j) g = (a : ℂ) := by
  intro j
  obtain ⟨a, ha⟩ := hf (j * p)
  obtain ⟨b, hb⟩ := hf j
  have H := eval_relation p f g hfg (z ^ j)
  rw [← pow_mul, ha, hb] at H
  apply (eval_integral (hz.pow j) g).exists_int_iff_exists_rat.mp
  refine ⟨((a : ℚ) - b ^ p) / p, ?_⟩
  push_cast
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hp.ne_zero)).mpr
  linear_combination -H

lemma periodic_values {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ^ n = 1)
    (f : ℤ[X])
    (hf : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ a : ℤ, aeval (z ^ j) f = (a : ℂ)) :
    ∀ j : ℕ, ∃ a : ℤ, aeval (z ^ j) f = (a : ℂ) := by
  intro j
  rw [pow_eq_pow_mod j hz]
  by_cases hj : j % n = 0
  · simpa only [hj, pow_zero, hz] using hf n hn (le_refl n)
  · exact hf (j % n) (Nat.one_le_iff_ne_zero.mpr hj) (Nat.mod_lt j hn).le

lemma fermat_difference (p : ℕ) (hp : p.Prime) (b : ℤ) : (p : ℤ) ∣ b ^ p - b := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp only [Int.cast_sub, Int.cast_pow, ZMod.pow_card, sub_self]

lemma congruence {z : ℂ} (hz : IsIntegral ℤ z) (p : ℕ) (hp : p.Prime) :
    ∀ e : ℕ, 1 ≤ e → ∀ f : ℤ[X],
    (∀ j : ℕ, ∃ a : ℤ, aeval (z ^ j) f = (a : ℂ)) →
    ∀ a b : ℤ,
    aeval (z ^ (p ^ e)) f = (a : ℂ) →
    aeval (z ^ (p ^ (e - 1))) f = (b : ℂ) →
    (p : ℤ) ^ e ∣ a - b := by
  intro e
  induction e with
  | zero => intro he; omega
  | succ e ih =>
    intro he f hf a b ha hb
    have hb' : aeval (z ^ (p ^ e)) f = (b : ℂ) := by simpa only [Nat.add_sub_cancel] using hb
    obtain ⟨g, hfg⟩ := frobenius_quotient p hp f
    have hg := quotient_values p hp f g hfg hz hf
    obtain ⟨d, hd⟩ := hg (p ^ e)
    have hrel := eval_relation p f g hfg (z ^ (p ^ e))
    rw [← pow_mul, ← pow_succ, ha, hb', hd] at hrel
    have hab : a - b ^ p = (p : ℤ) * d := by exact_mod_cast hrel
    by_cases he0 : e = 0
    · subst e
      simp only [zero_add, pow_one]
      have hdiv : (p : ℤ) ∣ a - b ^ p := ⟨d, hab⟩
      have heq : a - b = (a - b ^ p) + (b ^ p - b) := by ring
      rw [heq]
      exact dvd_add hdiv (fermat_difference p hp b)
    · have he' : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
      obtain ⟨c, hc⟩ := hf (p ^ (e - 1))
      obtain ⟨t, ht⟩ := hg (p ^ (e - 1))
      have hfdiv := ih he' f hf b c hb' hc
      have hgdiv := ih he' g hg d t hd ht
      have hrel' := eval_relation p f g hfg (z ^ (p ^ (e - 1)))
      have hexp : p ^ (e - 1) * p = p ^ e := by
        rw [← pow_succ, Nat.sub_add_cancel he']
      rw [← pow_mul, hexp, hb', hc, ht] at hrel'
      have hbc : b - c ^ p = (p : ℤ) * t := by exact_mod_cast hrel'
      have hpow := pow_lift p e he' b c hfdiv
      have hmul : (p : ℤ) ^ (e + 1) ∣ (p : ℤ) * (d - t) := by
        simpa only [pow_succ, mul_comm] using mul_dvd_mul_left (p : ℤ) hgdiv
      have heq : a - b = (b ^ p - c ^ p) + (p : ℤ) * (d - t) := by
        linear_combination hab - hbc
      rw [heq]
      exact dvd_add hpow hmul

end RootCongruence

theorem OMA.solution : type_of% @OMA.S_mo_284994.main := by
  intro n hn f hf p e hp he
  have hz : IsPrimitiveRoot (OMA.S_mo_284994.root n) n :=
    Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)
  have hvals := RootCongruence.periodic_values hn hz.pow_eq_one f hf
  obtain ⟨a, ha⟩ := hvals (p ^ e)
  obtain ⟨b, hb⟩ := hvals (p ^ (e - 1))
  refine ⟨a, b, ha, hb, Int.modEq_iff_dvd.mpr ?_⟩
  have h := RootCongruence.congruence (hz.isIntegral hn) p hp e he f hvals a b ha hb
  simpa only [neg_sub] using h.neg_right
