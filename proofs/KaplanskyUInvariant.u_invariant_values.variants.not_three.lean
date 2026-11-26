import FormalConjectures.Paper.KaplanskyUInvariant

-- Problem: KaplanskyUInvariant u_invariant_values variants not_three
-- Upstream: formal-conjectures FormalConjectures/Paper/KaplanskyUInvariant.lean (declaration KaplanskyUInvariant.u_invariant_values.variants.not_three)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)

/-!
Kaplansky's argument. If the diagonal form ⟨a, b, c⟩ is anisotropic then so is the
four-dimensional form ⟨a, b, c, abc⟩: the product formula for norms of the quadratic
extension defined by ⟨a, b⟩ turns an isotropic vector of the larger form into an isotropic
vector of ⟨a, b, c⟩. Hence no field has u-invariant 3.
-/

namespace OMA.KaplanskyNotThree

open QuadraticMap QuadraticForm

/-- The norm identity behind the argument. -/
lemma key {F : Type} [Field F] (a b c : F) (ha : a ≠ 0)
    (h : ∀ x y z : F, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (x y z w : F) (heq : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + a * b * c * w ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  by_cases hN : z ^ 2 + a * b * w ^ 2 = 0
  · have h1 : a * (z / a) ^ 2 + b * w ^ 2 + c * 0 ^ 2 = 0 := by
      have : a * (z / a) ^ 2 + b * w ^ 2 + c * 0 ^ 2 = (z ^ 2 + a * b * w ^ 2) / a := by
        field_simp
        ring
      rw [this, hN, zero_div]
    obtain ⟨hz, hw, -⟩ := h _ _ _ h1
    have hz' : z = 0 := by
      rcases div_eq_zero_iff.mp hz with h' | h'
      · exact h'
      · exact absurd h' ha
    subst hz' hw
    have h2 : a * x ^ 2 + b * y ^ 2 + c * 0 ^ 2 = 0 := by
      linear_combination heq
    obtain ⟨hx, hy, -⟩ := h _ _ _ h2
    exact ⟨hx, hy, rfl, rfl⟩
  · exfalso
    have h3 : a * (x * z + b * y * w) ^ 2 + b * (a * x * w - y * z) ^ 2 +
        c * (z ^ 2 + a * b * w ^ 2) ^ 2 = 0 := by
      linear_combination (z ^ 2 + a * b * w ^ 2) * heq
    exact hN (h _ _ _ h3).2.2

end OMA.KaplanskyNotThree

open QuadraticMap QuadraticForm OMA.KaplanskyNotThree in
theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.not_three := by
  rintro ⟨F, _, _, hmax, hub⟩
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmax
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hW : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    have := hQ _ h0
    simpa using this
  have hm : Module.finrank F (Fin 3 → F) = 3 := by simp
  generalize Module.finrank F (Fin 3 → F) = m at w hW hm
  subst hm
  set a := w 0
  set b := w 1
  set c := w 2
  have h3 : ∀ x y z : F, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z hxyz
    have hv := hW ![x, y, z] (by
      simp only [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination hxyz)
    refine ⟨?_, ?_, ?_⟩
    · simpa using congr_fun hv 0
    · simpa using congr_fun hv 1
    · simpa using congr_fun hv 2
  have ha : a ≠ 0 := by
    intro ha0
    have := (h3 1 0 0 (by rw [ha0]; ring)).1
    exact one_ne_zero this
  have h4 : 4 ∈ anisotropicDims F := by
    refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F ![a, b, c, a * b * c], ?_⟩
    intro v hv
    simp only [weightedSumSquares_apply, Fin.sum_univ_four, smul_eq_mul] at hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hv
    obtain ⟨h0, h1, h2, h3'⟩ := key a b c ha h3 (v 0) (v 1) (v 2) (v 3)
      (by linear_combination hv)
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3'
  have := hub h4
  omega
