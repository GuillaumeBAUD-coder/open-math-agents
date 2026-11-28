import OMAStatements.S_oeis_a114646

-- Problem: A114646: Let M(n) be the n X n matrix m(i,j)=min(i,j) for 1<=i,j<=n then a(n) is the trace of M(n)^(-4).
-- Upstream: formal-conjectures statements/oeis-a114646.lean:0 (declaration OMA.S_oeis_a114646.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: the recurrence part fails at n = 3. M(3) = [[1,1,1],[1,2,2],[1,2,3]] has the inverse
-- B = [[2,-1,0],[-1,2,-1],[0,-1,1]] (M(3) B = 1), B^4 = [[42,-47,19],[-47,61,-28],[19,-28,14]], and
-- trace(B^4) = 42 + 61 + 14 = 117, while the recurrence with a(1) = 1 and a(2) = 47 gives
-- a(3) = 2*47 - 1 = 93.

open OMA.S_oeis_a114646 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a114646.main) := by
  rintro ⟨-, h1, h2, h3⟩
  have hM3 : M 3 = !![(1 : ℚ), 1, 1; 1, 2, 2; 1, 2, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hB : M 3 * !![(2 : ℚ), -1, 0; -1, 2, -1; 0, -1, 1] = 1 := by
    rw [hM3, Matrix.mul_fin_three, Matrix.one_fin_three]
    norm_num
  have hinv : (M 3)⁻¹ = !![(2 : ℚ), -1, 0; -1, 2, -1; 0, -1, 1] := Matrix.inv_eq_right_inv hB
  have hC : (!![(2 : ℚ), -1, 0; -1, 2, -1; 0, -1, 1]) ^ 4 =
      !![(42 : ℚ), -47, 19; -47, 61, -28; 19, -28, 14] := by
    rw [pow_succ, pow_succ, pow_succ, pow_one, Matrix.mul_fin_three, Matrix.mul_fin_three,
      Matrix.mul_fin_three]
    norm_num
  have t := Matrix.trace_fin_three (!![(42 : ℚ), -47, 19; -47, 61, -28; 19, -28, 14])
  have e00 : (!![(42 : ℚ), -47, 19; -47, 61, -28; 19, -28, 14]) 0 0 = 42 := rfl
  have e11 : (!![(42 : ℚ), -47, 19; -47, 61, -28; 19, -28, 14]) 1 1 = 61 := rfl
  have e22 : (!![(42 : ℚ), -47, 19; -47, 61, -28; 19, -28, 14]) 2 2 = 14 := rfl
  rw [e00, e11, e22] at t
  have a3 : a 3 = 117 := by
    rw [show a 3 = Matrix.trace ((M 3)⁻¹ ^ 4) from rfl, hinv, hC]
    linarith
  have h := h3 3 (le_refl 3)
  norm_num [h1, h2, a3] at h
