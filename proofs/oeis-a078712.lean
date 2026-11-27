import OMAStatements.S_oeis_a078712

open Matrix

namespace OMA.P_oeis_a078712

/-- Companion matrix of `x^3 + x^2 - 1`; `a n = - trace (C ^ n)`. -/
def C : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 0; 0, 1, -1]

lemma C_trace : C.trace = -1 := by
  first
  | (rw [Matrix.trace_fin_three]; simp [C]; done)
  | decide
  | rfl

lemma C_cube : C ^ 3 = -C ^ 2 + 1 := by
  simp only [C, pow_succ, pow_zero, one_mul, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> first | (norm_num; done) | (simp; done) | decide | rfl

lemma a_eq : ∀ n, OMA.S_oeis_a078712.a n = -(C ^ n).trace
  | 0 => by
    show (-3 : ℤ) = _
    simp
  | 1 => by
    show (1 : ℤ) = _
    rw [pow_one, C_trace]; norm_num
  | 2 => by
    show (-1 : ℤ) = _
    first
    | (simp only [pow_two, C, Matrix.mul_fin_three, Matrix.trace_fin_three]; norm_num; done)
    | decide
    | rfl
  | n + 3 => by
    have h : C ^ (n + 3) = -C ^ (n + 2) + C ^ n := by
      rw [pow_add, C_cube, mul_add, mul_neg, ← pow_add, mul_one]
    rw [show OMA.S_oeis_a078712.a (n + 3) =
        -OMA.S_oeis_a078712.a (n + 2) + OMA.S_oeis_a078712.a n from rfl,
      a_eq (n + 2), a_eq n, h, Matrix.trace_add, Matrix.trace_neg]
    ring

end OMA.P_oeis_a078712

theorem OMA.solution : type_of% @OMA.S_oeis_a078712.main := by
  intro p hp
  haveI := Fact.mk hp
  rw [OMA.P_oeis_a078712.a_eq, ← ZMod.intCast_eq_intCast_iff]
  have h1 := ZMod.trace_pow_card (OMA.P_oeis_a078712.C.map (Int.castRingHom (ZMod p)))
  rw [← Matrix.map_pow, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace, ZMod.pow_card,
    eq_intCast, eq_intCast, OMA.P_oeis_a078712.C_trace] at h1
  rw [Int.cast_neg, h1]
  push_cast
  ring
