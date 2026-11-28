import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_164353

def Approximable (f : ℝ → ℝ) (a b : ℝ) (d : ℕ) (ε : ℝ) : Prop :=
  ∃ p : Polynomial ℝ, p.natDegree ≤ d ∧
    ∀ x ∈ Set.Icc a b, |f x - p.eval x| < ε

def StrictBounds (f : ℝ → ℝ) (a b : ℝ) (l u : Polynomial ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, l.eval x < f x ∧ f x < u.eval x

/-- The strict envelope problem reduces to usual uniform approximation.
On a compact interval, any strict pair can be shifted inward. -/
theorem main :
    ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Set.Icc a b) → ∀ d : ℕ,
      (∀ ε : ℝ, 0 < ε →
        (Approximable f a b d ε ↔
          ∃ l u : Polynomial ℝ, l.natDegree ≤ d ∧ u.natDegree ≤ d ∧
            StrictBounds f a b l u ∧
            ∀ x ∈ Set.Icc a b, f x - l.eval x < 2*ε ∧ u.eval x - f x < 2*ε)) ∧
      (∀ l u : Polynomial ℝ, l.natDegree ≤ d → u.natDegree ≤ d →
        StrictBounds f a b l u → ∃ δ : ℝ, 0 < δ ∧
          (l + Polynomial.C δ).natDegree ≤ d ∧
          (u - Polynomial.C δ).natDegree ≤ d ∧
          StrictBounds f a b (l + Polynomial.C δ) (u - Polynomial.C δ)) := by
  sorry

end OMA.S_mo_164353
