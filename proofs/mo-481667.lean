import OMAStatements.S_mo_481667
import Mathlib

/-!
MathOverflow 481667: in dimension `2`, take the rotating reflection
`A(t) = 3π [[cos 10πt, sin 10πt], [sin 10πt, -cos 10πt]]` (symmetric, entries bounded by `3π`).
Writing `A(t) = R(5πt) D R(5πt)ᵀ` with `D = diag(3π, -3π)` and `Y = R(5πt) Z`, the equation
becomes `Z' = M Z` with the constant `M = [[3π, 5π], [-5π, -3π]]`, `M² = -(4π)² I`, so
`Z(t) = cos(4πt) I + sin(4πt) M / (4π)`. We verify `Y' = A Y` entrywise. At `t = 1`,
`R(5π) = -I` and `Z(1) = I`, so `Y(1) = -I` and `e₁ᵀ Y(1) e₁ = -1`. (The answer by Christian
Remling gives the same conclusion with a piecewise constant `A`.)
-/

namespace OMA.P481667

open Matrix Real

noncomputable section

/-- `A(t) = 3π [[cos 10πt, sin 10πt], [sin 10πt, -cos 10πt]]`, a rotating reflection. -/
def A (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 * π * cos (10 * π * t), 3 * π * sin (10 * π * t);
     3 * π * sin (10 * π * t), -(3 * π * cos (10 * π * t))]

def ca (t : ℝ) : ℝ := cos (5 * π * t)
def sa (t : ℝ) : ℝ := sin (5 * π * t)
def cb (t : ℝ) : ℝ := cos (4 * π * t)
def sb (t : ℝ) : ℝ := sin (4 * π * t)

def y00 (t : ℝ) : ℝ := ca t * cb t + 3 / 4 * (ca t * sb t) + 5 / 4 * (sa t * sb t)
def y01 (t : ℝ) : ℝ := 5 / 4 * (ca t * sb t) - sa t * cb t + 3 / 4 * (sa t * sb t)
def y10 (t : ℝ) : ℝ := sa t * cb t + 3 / 4 * (sa t * sb t) - 5 / 4 * (ca t * sb t)
def y11 (t : ℝ) : ℝ := 5 / 4 * (sa t * sb t) + ca t * cb t - 3 / 4 * (ca t * sb t)

/-- The solution `Y(t) = R(5πt) (cos 4πt · I + sin 4πt · M/4)`, written out. -/
def Y (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![y00 t, y01 t; y10 t, y11 t]

lemma hca (t : ℝ) : HasDerivAt ca (-sa t * (5 * π)) t := by
  have e : ca = fun x => cos (5 * π * x) := rfl
  rw [e]
  have := ((hasDerivAt_id' t).const_mul (5 * π)).cos
  simpa [sa] using this
lemma hsa (t : ℝ) : HasDerivAt sa (ca t * (5 * π)) t := by
  have e : sa = fun x => sin (5 * π * x) := rfl
  rw [e]
  have := ((hasDerivAt_id' t).const_mul (5 * π)).sin
  simpa [ca] using this
lemma hcb (t : ℝ) : HasDerivAt cb (-sb t * (4 * π)) t := by
  have e : cb = fun x => cos (4 * π * x) := rfl
  rw [e]
  have := ((hasDerivAt_id' t).const_mul (4 * π)).cos
  simpa [sb] using this
lemma hsb (t : ℝ) : HasDerivAt sb (cb t * (4 * π)) t := by
  have e : sb = fun x => sin (4 * π * x) := rfl
  rw [e]
  have := ((hasDerivAt_id' t).const_mul (4 * π)).sin
  simpa [cb] using this

lemma c10 (t : ℝ) : cos (10 * π * t) = 2 * ca t ^ 2 - 1 := by
  rw [show 10 * π * t = 2 * (5 * π * t) by ring, cos_two_mul]; rfl
lemma s10 (t : ℝ) : sin (10 * π * t) = 2 * sa t * ca t := by
  rw [show 10 * π * t = 2 * (5 * π * t) by ring, sin_two_mul]; rfl
lemma pyth (t : ℝ) : sa t ^ 2 + ca t ^ 2 = 1 := sin_sq_add_cos_sq _

lemma d00 (t : ℝ) : HasDerivAt y00 ((A t * Y t) 0 0) t := by
  have h := (((hca t).mul (hcb t)).add (((hca t).mul (hsb t)).const_mul (3 / 4))).add
    (((hsa t).mul (hsb t)).const_mul (5 / 4))
  refine h.congr_deriv ?_
  simp only [A, Y, mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, c10, s10, y00, y10]
  linear_combination (-3 * ca t * π * (4 * cb t + 3 * sb t) / 2) * pyth t

lemma d01 (t : ℝ) : HasDerivAt y01 ((A t * Y t) 0 1) t := by
  have h := ((((hca t).mul (hsb t)).const_mul (5 / 4)).sub ((hsa t).mul (hcb t))).add
    (((hsa t).mul (hsb t)).const_mul (3 / 4))
  refine h.congr_deriv ?_
  simp only [A, Y, mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, c10, s10, y01, y11]
  linear_combination (-15 * ca t * π * sb t / 2) * pyth t

lemma d10 (t : ℝ) : HasDerivAt y10 ((A t * Y t) 1 0) t := by
  have h := (((hsa t).mul (hcb t)).add (((hsa t).mul (hsb t)).const_mul (3 / 4))).sub
    (((hca t).mul (hsb t)).const_mul (5 / 4))
  refine h.congr_deriv ?_
  simp only [A, Y, mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, c10, s10, y00, y10]
  linear_combination (-15 * ca t * π * sb t / 2) * pyth t

lemma d11 (t : ℝ) : HasDerivAt y11 ((A t * Y t) 1 1) t := by
  have h := ((((hsa t).mul (hsb t)).const_mul (5 / 4)).add ((hca t).mul (hcb t))).sub
    (((hca t).mul (hsb t)).const_mul (3 / 4))
  refine h.congr_deriv ?_
  simp only [A, Y, mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, c10, s10, y01, y11]
  linear_combination (3 * ca t * π * (4 * cb t - 3 * sb t) / 2) * pyth t

theorem disproof_aux :
    ¬ ∀ (d : ℕ) (A Y : ℝ → Matrix (Fin d) (Fin d) ℝ),
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (A t)ᵀ = A t) →
      (∃ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j, |A t i j| ≤ a) →
      Y 0 = 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
        HasDerivWithinAt (fun s => Y s i j) ((A t * Y t) i j) (Set.Icc 0 1) t) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u : Fin d → ℝ, 0 ≤ u ⬝ᵥ (Y t *ᵥ u) := by
  intro h
  have hsymm : ∀ t ∈ Set.Icc (0 : ℝ) 1, (A t)ᵀ = A t := by
    intro t _
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  have hbd : ∃ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j, |A t i j| ≤ a := by
    refine ⟨3 * π, fun t _ i j => ?_⟩
    have hp : 0 < 3 * π := by positivity
    fin_cases i <;> fin_cases j <;>
      simp [A, abs_mul, abs_of_pos hp, abs_neg, mul_le_iff_le_one_right hp, abs_cos_le_one,
        abs_sin_le_one]
  have hY0 : Y 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Y, y00, y01, y10, y11, ca, sa, cb, sb]
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun s => Y s i j) ((A t * Y t) i j) (Set.Icc 0 1) t := by
    intro t _ i j
    fin_cases i <;> fin_cases j
    · exact (d00 t).hasDerivWithinAt
    · exact (d01 t).hasDerivWithinAt
    · exact (d10 t).hasDerivWithinAt
    · exact (d11 t).hasDerivWithinAt
  have key := h 2 A Y hsymm hbd hY0 hder 1 ⟨zero_le_one, le_rfl⟩ ![1, 0]
  have h5c : cos (5 * π) = -1 := by
    rw [show (5 : ℝ) * π = ((5 : ℕ) : ℝ) * π by norm_num, cos_nat_mul_pi]; norm_num
  have h5s : sin (5 * π) = 0 := by
    rw [show (5 : ℝ) * π = ((5 : ℕ) : ℝ) * π by norm_num, sin_nat_mul_pi]
  have h4c : cos (4 * π) = 1 := by
    rw [show (4 : ℝ) * π = ((4 : ℕ) : ℝ) * π by norm_num, cos_nat_mul_pi]; norm_num
  have h4s : sin (4 * π) = 0 := by
    rw [show (4 : ℝ) * π = ((4 : ℕ) : ℝ) * π by norm_num, sin_nat_mul_pi]
  simp [Y, y00, y01, y10, y11, ca, sa, cb, sb, h5c, h5s, h4c, h4s, dotProduct, mulVec,
    Fin.sum_univ_two] at key
  linarith

end

end OMA.P481667

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_481667.main) := OMA.P481667.disproof_aux
