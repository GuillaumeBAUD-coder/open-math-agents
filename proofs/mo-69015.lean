import OMAStatements.S_mo_69015
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Counterexample to the fixed-point claim in BharatRam's MathOverflow question
“Maximization of a matrix product by iterative methods.”
https://mathoverflow.net/questions/69015

The eigenvector observation is due to Pietro Majer (answer 69021, CC BY-SA 3.0).
https://mathoverflow.net/a/69021

Formalization credit: @grp06.
-/

open OMA.S_mo_69015

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_69015.main) := by
  let d : Fin 2 → ℝ := fun i => if i = 0 then 1 else 2
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal d
  let y : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
  let x : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hd0 : d 0 = 1 := by simp [d]
  have hd1 : d 1 = 2 := by simp [d, h10]
  have hy0 : y 0 = 1 := by simp [y, PiLp.toLp_apply]
  have hy1 : y 1 = 0 := by simp [y, PiLp.toLp_apply, h10]
  have hx0 : x 0 = 0 := by simp [x, PiLp.toLp_apply]
  have hx1 : x 1 = 1 := by simp [x, PiLp.toLp_apply, h10]

  have hbilinear (u v : EuclideanSpace ℝ (Fin 2)) :
      bilinear A u v = u 0 * (1 * v 0) + u 1 * (2 * v 1) := by
    simp only [bilinear, dotProduct, Fin.sum_univ_two, A, Matrix.mulVec_diagonal,
      hd0, hd1]
  have hlinear (w : EuclideanSpace ℝ (Fin 2)) : bilinear A w y = w 0 := by
    simp only [hbilinear, hy0, hy1, mul_one, mul_zero, add_zero]
  have hyobj : objective A y = 1 := by
    rw [objective, hlinear, hy0]
  have hxobj : objective A x = 2 := by
    norm_num [objective, hbilinear, hx0, hx1]

  have hy : unit y := by norm_num [unit, Fin.sum_univ_two, hy0, hy1]
  have hx : unit x := by norm_num [unit, Fin.sum_univ_two, hx0, hx1]
  have hstep : Step A y y := by
    refine ⟨hy, hy, fun w hw => ?_⟩
    simp only [hlinear, hy0]
    rw [unit, Fin.sum_univ_two] at hw
    by_cases h : w 0 ≤ 1
    · exact h
    · have hgt : 1 < w 0 := lt_of_not_ge h
      have hpos : 0 < (w 0 - 1) * (w 0 + 1) :=
        mul_pos (sub_pos.mpr hgt) (by linarith only [hgt])
      exfalso
      nlinarith only [hw, sq_nonneg (w 1), hpos]

  intro hclaim
  change FixedPointClaim ∧ MonotonicityClaim at hclaim
  have hle := hclaim.1 2 (by decide) A y hstep x hx
  rw [hxobj, hyobj] at hle
  norm_num at hle
