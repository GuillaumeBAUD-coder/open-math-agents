import OMAStatements.S_mo_67775
import Mathlib.Tactic.Ring

open OMA.S_mo_67775

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_67775.main) := by
  intro h
  let t (i : Fin 6) : ℤ := i.val
  let u (i : Fin 6) : Fin 3 → ℤ := ![1, t i, t i ^ 2]
  have hinj : Function.Injective t := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℤ) = (j.val : ℤ) at hij
    exact_mod_cast hij
  have hpos : GeneralPosition u := by
    intro i j k hij hik hjk
    have hdet : (tripleMatrix u i j k).det =
        (t j - t i) * (t k - t i) * (t k - t j) := by
      rw [Matrix.det_fin_three]
      simp [tripleMatrix, u]
      ring
    rw [hdet]
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr fun e => hij (hinj e.symm))
        (sub_ne_zero.mpr fun e => hik (hinj e.symm)))
      (sub_ne_zero.mpr fun e => hjk (hinj e.symm))
  apply h u hpos
  apply Matrix.det_zero_of_column_eq (i := 1) (j := 4) (by decide)
  intro i
  simp [quadraticMatrix, quadratic, u]