import OMAStatements.S_mo_5041
import Mathlib

namespace OMA.P5041
open MvPolynomial OMA.S_mo_5041

noncomputable def G : MvPolynomial (Fin 5) ℂ := X 0 * X 2 * X 3 * X 4
noncomputable def H : MvPolynomial (Fin 5) ℂ := X 1 * X 2 * X 3 * X 4

lemma evalG (x : Fin 5 → ℂ) : eval x G = x 0 * x 2 * x 3 * x 4 := by simp [G]
lemma evalH (x : Fin 5 → ℂ) : eval x H = x 1 * x 2 * x 3 * x 4 := by simp [H]

lemma hG : G.IsHomogeneous 4 := by
  have := (((isHomogeneous_X ℂ (0 : Fin 5)).mul (isHomogeneous_X ℂ (2 : Fin 5))).mul
    (isHomogeneous_X ℂ (3 : Fin 5))).mul (isHomogeneous_X ℂ (4 : Fin 5))
  simpa [G] using this

lemma hH : H.IsHomogeneous 4 := by
  have := (((isHomogeneous_X ℂ (1 : Fin 5)).mul (isHomogeneous_X ℂ (2 : Fin 5))).mul
    (isHomogeneous_X ℂ (3 : Fin 5))).mul (isHomogeneous_X ℂ (4 : Fin 5))
  simpa [H] using this

lemma key (A : Matrix (Fin 5) (Fin 5) ℂ) (Q : MvPolynomial (Fin 5) ℂ) (z : Fin 5 → ℂ) :
    eval z (linSubst A Q) = eval (A.mulVec z) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [linSubst]
  | add p q hp hq => simp only [linSubst, map_add] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [linSubst, map_mul, aeval_X] at *
    rw [hp]
    simp [Matrix.mulVec, dotProduct]

lemma inv_zero (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsUnit A.det) (Q : MvPolynomial (Fin 5) ℂ)
    (hQ : 4 ∉ (linSubst A Q).vars) (y : Fin 5 → ℂ) :
    eval (y + fun i => A i 4) Q = eval y Q := by
  have hAi : A.mulVec (A⁻¹.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA]; simp
  set x := A⁻¹.mulVec y with hx
  have e1 : eval (Function.update x 4 (x 4 + 1)) (linSubst A Q) = eval x (linSubst A Q) := by
    have := MvPolynomial.eval₂Hom_congr' (f₁ := RingHom.id ℂ) (f₂ := RingHom.id ℂ)
      (g₁ := Function.update x 4 (x 4 + 1)) (g₂ := x) (p₁ := linSubst A Q) (p₂ := linSubst A Q)
      rfl (fun i hi _ => by
        have : i ≠ 4 := fun h => hQ (h ▸ hi)
        simp [Function.update_of_ne this]) rfl
    simpa [MvPolynomial.coe_eval₂Hom] using this
  rw [key, key, hAi] at e1
  have : A.mulVec (Function.update x 4 (x 4 + 1)) = y + fun i => A i 4 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
    have h2 := congrFun hAi i
    simp only [Matrix.mulVec, dotProduct] at h2
    have : ∀ j, A i j * Function.update x 4 (x 4 + 1) j = A i j * x j + (if j = 4 then A i 4 else 0) := by
      intro j
      by_cases h : j = 4
      · subst h; simp; ring
      · simp [Function.update_of_ne h, h]
    simp [this, Finset.sum_add_distrib, h2]
  rwa [this] at e1

lemma main_aux (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsUnit A.det)
    (h1 : 4 ∉ (linSubst A G).vars) (h2 : 4 ∉ (linSubst A H).vars) : False := by
  have hG' := inv_zero A hA G h1
  have hH' := inv_zero A hA H h2
  set v : Fin 5 → ℂ := fun i => A i 4 with hv
  have z0 : v 0 = 0 := by
    have := hG' (fun i => if i = 0 then 0 else 1 - v i)
    simpa [evalG] using this
  have z1 : v 1 = 0 := by
    have := hH' (fun i => if i = 1 then 0 else 1 - v i)
    simpa [evalH] using this
  have z2 : v 2 = 0 := by
    have := hG' (fun i => if i = 2 then 0 else 1 - v i)
    simpa [evalG] using this
  have z3 : v 3 = 0 := by
    have := hG' (fun i => if i = 3 then 0 else 1 - v i)
    simpa [evalG] using this
  have z4 : v 4 = 0 := by
    have := hG' (fun i => if i = 4 then 0 else 1 - v i)
    simpa [evalG] using this
  have hcol : ∀ i, A i 4 = 0 := by
    intro i; fin_cases i <;> assumption
  have := Matrix.det_eq_zero_of_column_eq_zero 4 hcol
  rw [this] at hA
  exact not_isUnit_zero hA

lemma poly_ne (P : MvPolynomial (Fin 5) ℂ) (x : Fin 5 → ℂ) (h : eval x P ≠ 0) : P ≠ 0 := by
  rintro rfl; simp at h

lemma lin (i : Fin 5) : (X i : MvPolynomial (Fin 5) ℂ).IsHomogeneous 1 := isHomogeneous_X ℂ i

lemma lin2 : (X 0 - X 1 : MvPolynomial (Fin 5) ℂ).IsHomogeneous 1 :=
  (lin 0).sub (lin 1)

end OMA.P5041

open OMA.S_mo_5041 in
theorem OMA.solution : type_of% @OMA.S_mo_5041.main := by
  open OMA.P5041 MvPolynomial in
  refine ⟨G, H, 4, ![(0, 1), (1, 0), (1, 1)], hG, hH, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have e1 := congrArg (eval ![1, 0, 1, 1, 1]) h
    have e2 := congrArg (eval ![0, 1, 1, 1, 1]) h
    simp [evalG, evalH] at e1 e2
    exact ⟨e1, e2.symm⟩
  · intro A hA h
    exact main_aux A hA h.1 h.2
  · intro i; fin_cases i <;> simp
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · intro i
    fin_cases i
    · -- G
      refine ⟨poly_ne _ (fun _ => 1) (by norm_num [evalG, evalH]), 1, [X 0, X 2, X 3, X 4], ?_, ?_⟩
      · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl | rfl <;> exact lin _
      · simp [G]; ring
    · refine ⟨poly_ne _ (fun _ => 1) (by norm_num [evalG, evalH]), -1, [X 1, X 2, X 3, X 4], ?_, ?_⟩
      · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl | rfl <;> exact lin _
      · simp [H]; ring
    · have h2 : (2 : Fin 5) ≠ 0 := by decide
      have h3 : (3 : Fin 5) ≠ 0 := by decide
      have h4 : (4 : Fin 5) ≠ 0 := by decide
      refine ⟨poly_ne _ (fun i => if i = 0 then 2 else 1) (by simp [evalG, evalH, h2, h3, h4]; norm_num), 1, [X 0 - X 1, X 2, X 3, X 4], ?_, ?_⟩
      · intro l hl; simp at hl; rcases hl with rfl | rfl | rfl | rfl
        · exact lin2
        all_goals exact lin _
      · simp [G, H]; ring
