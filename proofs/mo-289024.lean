import OMAStatements.S_mo_289024
import Mathlib

open NumberField OMA.S_mo_289024

private theorem three_dvd_pair {a c : ℤ} (h : (3 : ℤ) ∣ a ^ 2 + c ^ 2) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ c := by
  have hz : (↑a : ZMod 3) ^ 2 + (↑c : ZMod 3) ^ 2 = 0 := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + c ^ 2) 3).2 h
  have htest : ∀ a c : ZMod 3, a ^ 2 + c ^ 2 = 0 → a = 0 ∧ c = 0 := by decide
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 (htest _ _ hz).1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).1 (htest _ _ hz).2⟩

private theorem noIntegralNormNegOne (a b c : ℤ) (h : a ^ 2 + c ^ 2 = 3 * b ^ 2) : c = 0 := by
  generalize hc : c.natAbs = n
  induction n using Nat.strong_induction_on generalizing a b c with
  | h n ih =>
    by_contra hne
    obtain ⟨⟨a', ha⟩, ⟨c', hc'⟩⟩ := three_dvd_pair (h ▸ dvd_mul_right (3 : ℤ) (b ^ 2))
    have hb2 : b ^ 2 = 3 * (a' ^ 2 + c' ^ 2) := by
      rw [ha, hc'] at h
      nlinarith
    obtain ⟨b', hb⟩ := (three_dvd_pair (a := b) (c := 0)
      (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, hb2] using
        (dvd_mul_right (3 : ℤ) (a' ^ 2 + c' ^ 2)))).1
    have hsmall : a' ^ 2 + c' ^ 2 = 3 * b' ^ 2 := by
      rw [hb] at hb2
      nlinarith
    have hcprod : 3 * c'.natAbs = n := by
      rw [← hc, hc', Int.natAbs_mul]
      rfl
    have hcne : c' ≠ 0 := fun h => hne (by simp [hc', h])
    have hlt : c'.natAbs < n := by
      have := Int.natAbs_pos.mpr hcne
      omega
    exact hcne (ih c'.natAbs hlt a' b' c' hsmall rfl)

private theorem noRationalNormNegOne (x y : ℚ) : x ^ 2 - 3 * y ^ 2 ≠ -1 := by
  intro h
  have hd (x : ℚ) : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hr : (x.num : ℚ) / x.den = x := Rat.num_div_den x
  have hs : (y.num : ℚ) / y.den = y := Rat.num_div_den y
  rw [← hr, ← hs] at h
  have hh : ((x.num : ℚ) * y.den) ^ 2 + ((x.den : ℚ) * y.den) ^ 2 =
      3 * ((y.num : ℚ) * x.den) ^ 2 := by
    field_simp [hd x, hd y] at h
    nlinarith
  have hi : (x.num * (y.den : ℤ)) ^ 2 + ((x.den : ℤ) * y.den) ^ 2 =
      3 * (y.num * (x.den : ℤ)) ^ 2 := by exact_mod_cast hh
  exact (mul_ne_zero (by exact_mod_cast x.den_ne_zero) (by exact_mod_cast y.den_ne_zero))
    (noIntegralNormNegOne _ _ _ hi)

private abbrev K := QuadraticAlgebra ℚ 3 0

private instance : Fact (∀ r : ℚ, r ^ 2 ≠ 3 + 0 * r) := ⟨by
  intro r hr
  have hsq : IsSquare (3 : ℚ) := ⟨r, by simpa [pow_two, eq_comm] using hr⟩
  exact (by decide : Nat.Prime 3).not_isSquare
    (Rat.isSquare_natCast_iff.mp (show IsSquare ((3 : ℕ) : ℚ) from hsq))⟩

private instance : NumberField K where

private instance : Algebra.IsQuadraticExtension ℚ K where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two 3 0

private theorem normFormula (x : K) :
    Algebra.norm ℚ x = x.re ^ 2 - 3 * x.im ^ 2 := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap ℚ K x).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

private abbrev U := (𝓞 K)ˣ

private theorem unitNorm (u : U) : QuadraticAlgebra.norm (u : K) = 1 := by
  have hn := NumberField.Units.norm K u
  have heq : Algebra.norm ℚ (u : K) = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℚ) ≤ 1)).mp hn with h | h
    · exact h
    · exact (noRationalNormNegOne (u : K).re (u : K).im
        ((normFormula (u : K)).symm.trans h)).elim
  rw [Algebra.norm_apply] at heq
  exact (QuadraticAlgebra.det_toLinearMap_eq_norm (u : K)).symm.trans heq

private theorem star_unit (u : U) : star (u : K) = (↑(u⁻¹) : K) := by
  have h := (QuadraticAlgebra.algebraMap_norm_eq_mul_star (u : K)).symm
  rw [unitNorm, map_one] at h
  have h' : star (u : K) = (u : K)⁻¹ := eq_inv_of_mul_eq_one_right h
  simpa [NumberField.Units.coe_zpow u (-1)] using h'

private theorem conj_in_zpowers (u : U) : conjugateSubgroup u ≤ Subgroup.zpowers u := by
  rw [conjugateSubgroup, Subgroup.closure_le]
  rintro v ⟨σ, hv⟩
  let z := (u : K)
  have h0 := QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero z
  rw [Algebra.smul_def] at h0
  have hz : z ^ 2 - algebraMap ℚ K (QuadraticAlgebra.trace z) * z +
      algebraMap ℚ K (QuadraticAlgebra.norm z) = 0 := h0
  have hσ : σ z ^ 2 - algebraMap ℚ K (QuadraticAlgebra.trace z) * σ z +
      algebraMap ℚ K (QuadraticAlgebra.norm z) = 0 := by
    simpa only [map_add, map_sub, map_pow, map_mul, AlgEquiv.commutes, map_zero] using congrArg σ hz
  have ht : algebraMap ℚ K (QuadraticAlgebra.trace z) = z + star z :=
    QuadraticAlgebra.algebraMap_trace_eq_add_star z
  have hn : algebraMap ℚ K (QuadraticAlgebra.norm z) = z * star z :=
    QuadraticAlgebra.algebraMap_norm_eq_mul_star z
  rw [ht, hn] at hσ
  have hprod : (σ z - z) * (σ z - star z) = 0 := by linear_combination hσ
  rcases mul_eq_zero.mp hprod with h | h
  · have he : v = u := NumberField.Units.coe_injective K (hv.trans (sub_eq_zero.mp h))
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simpa using he.symm⟩
  · have he : v = u⁻¹ := NumberField.Units.coe_injective K
      (hv.trans ((sub_eq_zero.mp h).trans (star_unit u)))
    exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simpa using he.symm⟩

private noncomputable def realEmbedding : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 3, by
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num [Algebra.smul_def]⟩

private theorem infiniteUnit : ∃ u : U, ¬ IsOfFinOrder u := by
  let ω : K := QuadraticAlgebra.omega
  have hωsq : ω ^ 2 = 3 := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    norm_num
  have hint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C 3,
      Polynomial.monic_X_pow_sub_C _ (by decide), ?_⟩
    simpa using sub_eq_zero.mpr hωsq
  let w : 𝓞 K := ⟨ω, hint⟩
  have hw : (w : K) = ω := rfl
  have heq : (2 + w : 𝓞 K) * (2 - w) = 1 := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_add, map_sub, map_ofNat, map_one]
    change (2 + ω) * (2 - ω) = 1
    linear_combination -hωsq
  let u : U := ⟨2 + w, 2 - w, heq, by rwa [mul_comm]⟩
  refine ⟨u, ?_⟩
  have hu : (u : K) = 2 + ω := by
    change algebraMap (𝓞 K) K (2 + w) = _
    rw [map_add, map_ofNat]
    rfl
  have hreal : realEmbedding (u : K) = 2 + Real.sqrt 3 := by
    rw [hu, map_add, map_ofNat]
    congr 1
    change (0 : ℚ) • (1 : ℝ) + (1 : ℚ) • Real.sqrt 3 = Real.sqrt 3
    simp
  have hgt : 1 < realEmbedding (u : K) := by
    rw [hreal]
    linarith [Real.sqrt_nonneg (3 : ℝ)]
  intro h
  obtain ⟨n, hn, he⟩ := h.exists_pow_eq_one
  have hc := congrArg (fun u : U => realEmbedding (u : K)) he
  simp only [NumberField.Units.coe_pow, NumberField.Units.coe_one, map_pow, map_one] at hc
  exact (ne_of_gt (one_lt_pow₀ hgt hn.ne')) hc

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_289024.main) := by
  intro h
  obtain ⟨ε, hpow, hodd⟩ := h K
  have hneg : (-1 : U) ∈ conjugateSubgroup ε := by
    have hmem := (conjugateSubgroup ε).pow_index_mem (-1 : U)
    have hpowNeg : (-1 : U) ^ (conjugateSubgroup ε).index = -1 := by
      apply NumberField.Units.coe_injective K
      change (↑((-1 : U) ^ (conjugateSubgroup ε).index) : K) = ((-1 : U) : K)
      rw [NumberField.Units.coe_pow, NumberField.Units.coe_neg_one, hodd.neg_one_pow]
    rwa [hpowNeg] at hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (conj_in_zpowers ε hneg)
  have hne : (-1 : U) ≠ 1 := by
    intro he
    have he' := congrArg (fun u : U => (u : K)) he
    have hbad : (-(1 : K)) = 1 := he'
    exact (by norm_num : (-(1 : K)) ≠ 1) hbad
  have hjne : j ≠ 0 := by rintro rfl; exact hne hj.symm
  have hε : IsOfFinOrder ε := by
    refine isOfFinOrder_iff_zpow_eq_one.mpr ⟨j * 2, by omega, ?_⟩
    rw [zpow_mul, hj]
    change (-1 : U) ^ ((2 : ℕ) : ℤ) = 1
    rw [zpow_natCast]
    apply NumberField.Units.coe_injective K
    change (↑((-1 : U) ^ (2 : ℕ)) : K) = ((1 : U) : K)
    rw [NumberField.Units.coe_pow, NumberField.Units.coe_neg_one, NumberField.Units.coe_one]
    ring
  obtain ⟨u, hu⟩ := infiniteUnit
  obtain ⟨n, hn, hmem⟩ := hpow u
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (conj_in_zpowers ε hmem)
  have hfinite : IsOfFinOrder (u ^ n) := hi ▸ hε.zpow
  exact hu (hfinite.of_pow hn.ne')
