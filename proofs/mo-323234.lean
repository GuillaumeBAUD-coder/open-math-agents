import OMAStatements.S_mo_323234
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

open Matrix
open scoped ComplexOrder Matrix MatrixOrder

theorem OMA.solution : type_of% @OMA.S_mo_323234.main := by
  intro n A B hA hB
  let C := B ^ 2
  have hAstar : Aᴴ = A := hA.isHermitian
  have hCstar : Cᴴ = C := by
    simp [C, pow_two, hB.isHermitian.eq]
  have hleft : ((B * A * B) ^ 2).trace = ((A * C) * (A * C)).trace := by
    calc
      _ = (B * (A * C * A * B)).trace := by
        congr 1
        dsimp [C]
        noncomm_ring
      _ = ((A * C * A * B) * B).trace := trace_mul_comm _ _
      _ = _ := by
        congr 1
        dsimp [C]
        noncomm_ring
  have hright : (B ^ 2 * A ^ 2 * B ^ 2).trace = ((C * A) * (A * C)).trace := by
    congr 1
    dsimp [C]
    noncomm_ring
  have hcycle : ((C * A) * (C * A)).trace = ((A * C) * (A * C)).trace := by
    simpa only [Matrix.mul_assoc] using trace_mul_comm C (A * C * A)
  rw [hleft, hright]
  constructor
  · intro h
    let D := A * C - C * A
    have hD : Dᴴ = C * A - A * C := by
      simp [D, hAstar, hCstar]
    have hnorm : (Dᴴ * D).trace = 0 := by
      rw [hD]
      change ((C * A - A * C) * (A * C - C * A)).trace = 0
      rw [sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
        hcycle, trace_mul_comm (A * C) (C * A), h]
      ring
    have hcomm : Commute A C :=
      sub_eq_zero.mp (trace_conjTranspose_mul_self_eq_zero_iff.mp hnorm)
    have hsqrt : Commute (CFC.sqrt C) A := by
      rw [CFC.sqrt_eq_cfc]
      exact hcomm.symm.cfc_nnreal _
    rw [CFC.sqrt_sq B hB.nonneg] at hsqrt
    exact hsqrt.symm.eq
  · intro h
    have hcomm : Commute A B := h
    rw [(hcomm.pow_right 2).eq]