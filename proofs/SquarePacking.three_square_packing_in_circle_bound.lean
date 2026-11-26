import FormalConjectures.Wikipedia.SquarePacking

-- Problem: Packing — three square packing in circle bound
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SquarePacking.lean:155 (declaration SquarePacking.three_square_packing_in_circle_bound)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SquarePacking
open scoped NNReal

namespace OMA

/-- Offsets for the three squares: two side by side on the bottom, one centred on top. -/
noncomputable def offset : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[-1, -13 / 16], !₂[0, -13 / 16], !₂[-1 / 2, 3 / 16]]

end OMA

theorem OMA.solution : type_of% @SquarePacking.three_square_packing_in_circle_bound := by
  refine ⟨⟨fun i => IsometryEquiv.addRight (OMA.offset i), ?_, ?_⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    simp only [UnitSquare, Square, Set.mem_ofPred_eq] at ha hb
    have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hab
    have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hab
    simp only [IsometryEquiv.addRight_apply, PiLp.add_apply] at h0 h1
    fin_cases i <;> fin_cases j <;> simp [OMA.offset] at h0 h1 hij <;> linarith
  · intro i
    rintro _ ⟨a, ha, rfl⟩
    simp only [UnitSquare, Square, Set.mem_ofPred_eq] at ha
    simp only [SquarePacking.Circle, Set.mem_ofPred_eq, IsometryEquiv.addRight_apply, PiLp.add_apply]
    have hR : (((5 * NNReal.sqrt 17) / 16 : ℝ≥0) : ℝ) ^ 2 = 425 / 256 := by
      push_cast
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [hR]
    obtain ⟨hx0, hx1, hy0, hy1⟩ := ha
    fin_cases i <;> simp [OMA.offset] <;> nlinarith
