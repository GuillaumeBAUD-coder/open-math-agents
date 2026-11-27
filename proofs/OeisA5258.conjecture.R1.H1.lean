import OMAReductions.R_OeisA5258_conjecture_R1

/-! The reciprocal Apéry polynomial is Eisenstein when n + 1 is prime. -/

open Polynomial Finset

namespace OMA.AperyPrime

noncomputable def polyZ (n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (((n.choose k) ^ 2 * (n + k).choose k : ℕ) : ℤ) * X ^ k

lemma coeff_polyZ (n k : ℕ) :
    (polyZ n).coeff k = if k ≤ n then
      (((n.choose k) ^ 2 * (n + k).choose k : ℕ) : ℤ) else 0 := by
  classical
  simp only [polyZ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

lemma coeff_zero (n : ℕ) : (polyZ n).coeff 0 = 1 := by
  simp [coeff_polyZ]

lemma degree_polyZ (n : ℕ) : (polyZ n).natDegree = n := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp [coeff_polyZ, not_le.mpr hk]
  · apply le_natDegree_of_ne_zero
    simpa [coeff_polyZ] using Nat.choose_ne_zero (show n ≤ n + n by omega)

lemma unit_of_reverse_unit {f : ℤ[X]} (h0 : f.coeff 0 ≠ 0) (hu : IsUnit f.reverse) :
    IsUnit f := by
  have ht : f.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hd : f.natDegree = 0 := by
    rw [natDegree_eq_reverse_natDegree_add_natTrailingDegree, ht,
      natDegree_eq_zero_of_isUnit hu, zero_add]
  have hC := eq_C_of_natDegree_eq_zero hd
  rw [hC, reverse_C] at hu
  exact hC.symm ▸ hu

lemma irreducible_of_reverse {f : ℤ[X]} (h0 : f.coeff 0 ≠ 0)
    (hi : Irreducible f.reverse) : Irreducible f := by
  refine ⟨?_, ?_⟩
  · intro hu
    apply hi.not_isUnit
    have hC := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu)
    rw [hC, reverse_C]
    rw [hC] at hu
    exact hu
  · intro a b hab
    have ha0 : a.coeff 0 ≠ 0 := by
      intro ha
      apply h0
      rw [hab, mul_coeff_zero, ha, zero_mul]
    have hb0 : b.coeff 0 ≠ 0 := by
      intro hb
      apply h0
      rw [hab, mul_coeff_zero, hb, mul_zero]
    rcases hi.isUnit_or_isUnit (by rw [hab, reverse_mul_of_domain]) with ha | hb
    · exact Or.inl (unit_of_reverse_unit ha0 ha)
    · exact Or.inr (unit_of_reverse_unit hb0 hb)

lemma central_valuation (n : ℕ) (hn : 1 ≤ n) (hp : (n + 1).Prime) :
    padicValNat (n + 1) ((n + n).choose n) = 1 := by
  have : Fact (n + 1).Prime := ⟨hp⟩
  have hlog : Nat.log (n + 1) (n + n) < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    nlinarith
  rw [padicValNat_choose' (b := 2) hlog]
  rw [show Finset.Ico 1 2 = {1} by decide]
  have hkeep : ∀ i ∈ ({1} : Finset ℕ),
      (n + 1) ^ i ≤ n % (n + 1) ^ i + n % (n + 1) ^ i := by
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    simpa only [pow_one, Nat.mod_eq_of_lt (Nat.lt_succ_self n)] using
      (show n + 1 ≤ n + n by omega)
  rw [Finset.filter_eq_self.mpr hkeep, Finset.card_singleton]

lemma reverse_degree (n : ℕ) : (polyZ n).reverse.natDegree = n := by
  have ht : (polyZ n).natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr (by rw [coeff_zero]; decide))
  rw [reverse_natDegree, ht, degree_polyZ, Nat.sub_zero]

lemma reverse_monic (n : ℕ) : (polyZ n).reverse.Monic := by
  change (polyZ n).reverse.leadingCoeff = 1
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by rw [coeff_zero]; decide), coeff_zero]

set_option maxHeartbeats 1000000 in
lemma reverse_irreducible (n : ℕ) (hn : 1 ≤ n) (hp : (n + 1).Prime) :
    Irreducible (polyZ n).reverse := by
  let I : Ideal ℤ := Ideal.span {((n + 1 : ℕ) : ℤ)}
  have hpZ : Prime ((n + 1 : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hI : I.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have heis : (polyZ n).reverse.IsEisensteinAt I := by
    refine ⟨?_, ?_, ?_⟩
    · change (polyZ n).reverse.leadingCoeff ∉ Ideal.span {((n + 1 : ℕ) : ℤ)}
      rw [(reverse_monic n).leadingCoeff, Ideal.mem_span_singleton]
      exact hpZ.not_dvd_one
    · intro k hk
      rw [reverse_degree] at hk
      change (polyZ n).reverse.coeff k ∈ Ideal.span {((n + 1 : ℕ) : ℤ)}
      rw [coeff_reverse, degree_polyZ, revAt_le hk.le, coeff_polyZ,
        if_pos (Nat.sub_le n k), Ideal.mem_span_singleton]
      have hd : n + 1 ∣ (n + (n - k)).choose (n - k) := by
        simpa only [Nat.add_comm] using hp.dvd_choose_add
          (show n - k < n + 1 by omega) (show n < n + 1 by omega)
          (show n + 1 ≤ (n - k) + n by omega)
      exact_mod_cast dvd_mul_of_dvd_right hd ((n.choose (n - k)) ^ 2)
    · change (polyZ n).reverse.coeff 0 ∉ (Ideal.span {((n + 1 : ℕ) : ℤ)}) ^ 2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_zero_reverse,
        leadingCoeff, degree_polyZ, coeff_polyZ]
      simp only [le_refl, if_pos, Nat.choose_self, one_pow, one_mul]
      intro hd
      have hdN : (n + 1) ^ 2 ∣ (n + n).choose n := by exact_mod_cast hd
      have : Fact (n + 1).Prime := ⟨hp⟩
      have hv := (padicValNat_dvd_iff_le (Nat.choose_ne_zero (show n ≤ n + n by omega))).mp hdN
      rw [central_valuation n hn hp] at hv
      omega
  exact heis.irreducible hI (reverse_monic n).isPrimitive (by rw [reverse_degree]; omega)

end OMA.AperyPrime

-- Step OeisA5258.conjecture.R1.H1: hypothesis H1 of reduction OeisA5258.conjecture.R1
-- Credit: @DeepDuke
-- H1 := ∀ n : ℕ, 1 ≤ n → (n + 1).Prime → Irreducible (OeisA5258.aperyPoly n)  /-- The case where n + 1 is not prime (open). -/

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := by
  intro n hn hp
  have h0 : (OMA.AperyPrime.polyZ n).coeff 0 ≠ 0 := by
    rw [OMA.AperyPrime.coeff_zero]
    decide
  have hiZ := OMA.AperyPrime.irreducible_of_reverse h0
    (OMA.AperyPrime.reverse_irreducible n hn hp)
  have hprim : (OMA.AperyPrime.polyZ n).IsPrimitive := by
    apply isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro r hr
    apply isUnit_of_dvd_one
    simpa only [OMA.AperyPrime.coeff_zero] using
      (C_dvd_iff_dvd_coeff r (OMA.AperyPrime.polyZ n)).mp hr 0
  have hiQ := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hiZ
  simpa [OMA.AperyPrime.polyZ, OeisA5258.aperyPoly,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow] using hiQ

