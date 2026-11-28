import OMAStatements.S_mo_445970
import Mathlib

-- Problem: mo-445970, if (sum x_i A_i)(sum x_i A_i)^* = (sum x_i B_i)(sum x_i B_i)^* for all x,
-- is there a unitary S with A_i = S B_i for all i?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take n = 1, d = 2, A = E_12 and B = E_11. Both sides of the hypothesis are |x|^2 E_11,
-- but the (1,2) entry of S B is 0 for every S, while the (1,2) entry of A is 1.

open Matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_445970.main) := by
  intro h
  have hyp : ∀ x : Fin 1 → ℂ,
      (∑ i, x i • (fun _ : Fin 1 => (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) i) *
        (∑ i, x i • (fun _ : Fin 1 => (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) i)ᴴ =
      (∑ i, x i • (fun _ : Fin 1 => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) i) *
        (∑ i, x i • (fun _ : Fin 1 => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) i)ᴴ := by
    intro x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  obtain ⟨U, -, hU⟩ := h 1 2 (fun _ => !![0, 1; 0, 0]) (fun _ => !![1, 0; 0, 0]) hyp
  have h01 := congrFun (congrFun (hU 0) 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
