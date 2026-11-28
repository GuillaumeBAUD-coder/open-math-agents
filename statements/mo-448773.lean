import Mathlib

namespace OMA.S_mo_448773

open MeasureTheory

abbrev Axis := Fin 4
abbrev Mat := Matrix Axis Axis ℝ

def Skew (Ω : Mat) : Prop :=
  Ω.transpose = -Ω

noncomputable def momentum (M Ω : Mat) : Mat :=
  M * Ω + Ω * M

/-- Integral form of the forced Euler equation, for a nonnegative integrable
scalar input and a continuous skew-symmetric angular-velocity trajectory. -/
def CanReach (M T Ω₀ Ω₁ : Mat) : Prop :=
  ∃ (duration : ℝ) (throttle : ℝ → ℝ) (Ω : ℝ → Mat),
    0 < duration ∧ Ω 0 = Ω₀ ∧ Ω duration = Ω₁ ∧
    IntervalIntegrable throttle volume 0 duration ∧
    (∀ i j : Axis, ContinuousOn (fun t => Ω t i j) (Set.Icc 0 duration)) ∧
    (∀ t ∈ Set.Icc 0 duration, 0 ≤ throttle t ∧ Skew (Ω t)) ∧
    ∀ t ∈ Set.Icc 0 duration, ∀ i j : Axis,
      momentum M (Ω t) i j = momentum M Ω₀ i j +
        ∫ s in (0 : ℝ)..t,
          throttle s * T i j -
            (Ω s * momentum M (Ω s) - momentum M (Ω s) * Ω s) i j

/-- Does some positive-definite inertia and one fixed simple torque give
global angular-velocity controllability under a nonnegative throttle? -/
theorem main :
    ∃ (M : Mat) (force arm : Axis → ℝ), M.PosDef ∧
      let T := Matrix.vecMulVec force arm - Matrix.vecMulVec arm force
      ∀ Ω₀ Ω₁ : Mat, Skew Ω₀ → Skew Ω₁ → CanReach M T Ω₀ Ω₁ := by
  sorry

end OMA.S_mo_448773
