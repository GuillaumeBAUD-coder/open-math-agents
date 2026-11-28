import OMAStatements.S_mo_393176

open scoped BigOperators

namespace OMA.QuadraticRank

open OMA.S_mo_393176 MvPolynomial

private theorem counterexample :
    ¬ ∃ a : Fin (count 5 2) → Fin 2 → Fin 5 → ℂ,
      (∑ i : Fin 5, X i ^ 2) = ∑ t, ∏ j, linear (a t j) := by
  rintro ⟨a, ha⟩
  let I := Fin (count 5 2) × Fin 2
  let M : Matrix I (Fin 5) ℂ := Matrix.of fun ij i => a ij.1 ij.2 i
  let L : (Fin 5 → ℂ) →ₗ[ℂ] (I → ℂ) := M.mulVecLin
  have evalForm (z : Fin 5 → ℂ) :
      (∑ i, z i ^ 2) = ∑ t, ∏ j, ∑ i, a t j i * z i := by
    have h := congrArg (MvPolynomial.eval z) ha
    simpa [linear] using h
  have injective : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    have annihilates (t : Fin (count 5 2)) (j : Fin 2) : ∑ i, a t j i * v i = 0 := by
      change (L v) (t, j) = 0
      rw [hv]
      rfl
    have translate (z : Fin 5 → ℂ) : (∑ i, (z + v) i ^ 2) = ∑ i, z i ^ 2 := by
      rw [evalForm (z + v), evalForm z]
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, annihilates, add_zero]
    have sumZero : (∑ i, v i ^ 2) = 0 := by simpa using translate 0
    funext i
    let e : Fin 5 → ℂ := Pi.single i 1
    have cross : (∑ j, 2 * e j * v j) = 2 * v i := by
      rw [Finset.sum_eq_single i]
      · simp [e]
      · intro j _ hn
        simp [e, Pi.single_eq_of_ne hn]
      · simp
    have h := translate e
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, sumZero, cross, add_zero] at h
    change v i = 0
    linear_combination (1 / 2 : ℂ) * h
  have countTwo : count 5 2 = 2 := by decide
  have cardI : Fintype.card I = 4 := by simp [I, countTwo]
  have dim := LinearMap.finrank_le_finrank_of_injective injective
  norm_num [Module.finrank_pi, cardI] at dim

end OMA.QuadraticRank

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_393176.main) := by
  intro h
  have homog : (∑ i : Fin 5, (MvPolynomial.X i : MvPolynomial (Fin 5) ℂ) ^ 2).IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact MvPolynomial.isHomogeneous_X_pow i 2
  exact OMA.QuadraticRank.counterexample (h 5 2 (by decide) (by decide) _ homog)