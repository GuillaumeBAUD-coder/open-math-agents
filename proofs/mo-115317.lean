import OMAStatements.S_mo_115317

open OMA.S_mo_115317

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_115317.main) := by
  intro h
  let v (i : Fin 3 × Fin 2) : ℂ := if i.2 = 0 then 5 else 4 * Complex.I - 3
  have hv : v ≠ 0 := by
    intro he
    have hc := congrFun he (0, 0)
    norm_num [v] at hc
  have he :
      ((giuliaMatrix (n := 3) (fun _ => 1) (fun _ => 5 / 6) (fun _ _ => -9 / 10)).map
        Complex.ofReal).mulVec v = (Complex.I / 2) • v := by
    funext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [giuliaMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        Fin.sum_univ_succ, v, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  have hc := h 3 (fun _ => 1) (fun _ => 5 / 6) (fun _ _ => -9 / 10)
    (by intro i; norm_num) (by intro i j; norm_num) (Complex.I / 2) ⟨v, hv, he⟩
  norm_num [Complex.div_im] at hc
