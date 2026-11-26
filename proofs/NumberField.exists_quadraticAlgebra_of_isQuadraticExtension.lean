import FormalConjectures.Wikipedia.WallSunSun

-- Problem: Infinitude of Wall–Sun–Sun primes — exists quadraticAlgebra of isQuadraticExtension
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/WallSunSun.lean:78 (declaration NumberField.exists_quadraticAlgebra_of_isQuadraticExtension)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

theorem OMA.solution : type_of% @NumberField.exists_quadraticAlgebra_of_isQuadraticExtension := by
  intro K _ _ _
  have hfr : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hex : ∃ α : K, α ∉ (algebraMap ℚ K).range := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra ℚ K) = ⊤ := by
      ext x
      simp only [Algebra.mem_top, iff_true]
      obtain ⟨q, rfl⟩ := h x
      exact Subalgebra.algebraMap_mem _ q
    have h1 : Module.finrank ℚ (⊥ : Subalgebra ℚ K) = 1 := Subalgebra.finrank_bot
    rw [htop, Subalgebra.topEquiv.toLinearEquiv.finrank_eq, hfr] at h1
    omega
  obtain ⟨α, hα⟩ := hex
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hdeg : (minpoly ℚ α).natDegree = 2 := by
    have h1 := minpoly.natDegree_le (A := ℚ) α
    rw [hfr] at h1
    have h2 : (minpoly ℚ α).natDegree ≠ 1 := fun h => hα (minpoly.natDegree_eq_one_iff.mp h)
    have h3 : 0 < (minpoly ℚ α).natDegree := minpoly.natDegree_pos hint
    omega
  have hmon : (minpoly ℚ α).coeff 2 = 1 := by
    have := (minpoly.monic hint).leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  set c0 := (minpoly ℚ α).coeff 0
  set c1 := (minpoly ℚ α).coeff 1
  have hrel : α ^ 2 + algebraMap ℚ K c1 * α + algebraMap ℚ K c0 = 0 := by
    have := minpoly.aeval ℚ α
    rw [aeval_eq_sum_range, hdeg] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hmon, Algebra.smul_def] at this
    rw [← this]
    simp only [pow_zero, pow_one, map_one, mul_one, one_mul, zero_add]
    ring
  set β : K := 2 * α + algebraMap ℚ K c1 with hβdef
  set r : ℚ := c1 ^ 2 - 4 * c0 with hr
  have hβsq : β ^ 2 = algebraMap ℚ K r := by
    simp only [hβdef, hr, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hrel
  have hβ : β ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    apply hα
    refine ⟨(q - c1) / 2, ?_⟩
    rw [map_div₀, map_sub, hq, map_ofNat]
    simp only [hβdef]
    ring
  set N : ℤ := r.num * r.den with hN
  set δ : K := (r.den : K) * β with hδdef
  have hδsq : δ ^ 2 = (N : K) := by
    rw [hδdef, mul_pow, hβsq, hN]
    rw [show algebraMap ℚ K r = (r : K) from rfl]
    have hden : (r.den : K) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hδ : δ ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    apply hβ
    refine ⟨q / r.den, ?_⟩
    have hden : (r.den : K) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [map_div₀, hq, map_natCast, hδdef]
    field_simp
  have hN0 : N ≠ 0 := by
    intro h0
    apply hδ
    refine ⟨0, ?_⟩
    rw [map_zero]
    have : δ ^ 2 = 0 := by rw [hδsq, h0, Int.cast_zero]
    exact (pow_eq_zero_iff (by norm_num)).mp this |>.symm
  obtain ⟨m, s, hms, hsqf⟩ := Nat.sq_mul_squarefree N.natAbs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hms
    exact hN0 (Int.natAbs_eq_zero.mp hms.symm)
  set d : ℤ := N.sign * m with hd
  have hNd : N = (s : ℤ) ^ 2 * d := by
    rw [hd]
    conv_lhs => rw [← Int.sign_mul_natAbs N, ← hms]
    push_cast
    ring
  have hdsq : Squarefree d := by
    rw [← Int.squarefree_natAbs, hd, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hN0, one_mul,
      Int.natAbs_natCast]
    exact hsqf
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs0
  set γ : K := δ / s with hγdef
  have hγsq : γ * γ = (d : K) := by
    have : γ ^ 2 = (d : K) := by
      rw [hγdef, div_pow, hδsq, hNd]
      push_cast
      field_simp
    rw [← this]; ring
  have hγ : γ ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    apply hδ
    refine ⟨q * s, ?_⟩
    rw [map_mul, hq, map_natCast, hγdef]
    field_simp
  have hd1 : d ≠ 1 := by
    rintro h1
    rw [h1, Int.cast_one] at hγsq
    have : (γ - 1) * (γ + 1) = 0 := by linear_combination hγsq
    rcases mul_eq_zero.mp this with h | h
    · exact hγ ⟨1, by rw [map_one]; linear_combination -h⟩
    · exact hγ ⟨-1, by rw [map_neg, map_one]; linear_combination -h⟩
  let f : QuadraticAlgebra ℚ (d : ℚ) 0 →ₐ[ℚ] K :=
    QuadraticAlgebra.lift ⟨γ, by
      rw [hγsq, zero_smul, add_zero, Algebra.smul_def, mul_one]
      simp⟩
  have hf : ∀ x : QuadraticAlgebra ℚ (d : ℚ) 0, f x = x.re • 1 + x.im • γ := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hf] at hx
    by_cases him : x.im = 0
    · rw [him, zero_smul, add_zero, Algebra.smul_def, mul_one] at hx
      have hre : x.re = 0 := (algebraMap ℚ K).injective (by rw [hx, map_zero])
      ext <;> simp [hre, him]
    · exfalso
      apply hγ
      refine ⟨-(x.re / x.im), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hx
      have hK : algebraMap ℚ K x.im ≠ 0 := by simpa using him
      rw [map_neg, map_div₀]
      field_simp
      first | linear_combination hx | linear_combination -hx
  have hsurj : Function.Surjective f := by
    have := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) (by rw [QuadraticAlgebra.finrank_eq_two, hfr])
    exact this.mp hinj
  exact ⟨d, hd1, hdsq, ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.toRingEquiv⟩⟩
