import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_395618

def OddPolynomial (p : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, p.eval (-x) = -p.eval x

/-- Uniform error when approximating the constant function 1 on `[0,1]`. -/
noncomputable def error (p : Polynomial ℝ) : ℝ :=
  sSup ((fun x : ℝ => |1-p.eval x|) '' Set.Icc (0 : ℝ) 1)

def BestOdd (d : ℕ) (p : Polynomial ℝ) : Prop :=
  p.natDegree ≤ d ∧ OddPolynomial p ∧
    ∀ q : Polynomial ℝ, q.natDegree ≤ d → OddPolynomial q → error p ≤ error q

/-- The odd-polynomial restriction allows nonunique minimizers. One
minimizer has only a single point of maximum absolute error. -/
theorem main :
    ∀ d : ℕ, Odd d →
      (∀ c : ℝ,
        BestOdd d (Polynomial.C c * Polynomial.X^d) ↔ 0 ≤ c ∧ c ≤ 2) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        |1-((Polynomial.X : Polynomial ℝ)^d).eval x| =
          error ((Polynomial.X : Polynomial ℝ)^d) → x = 0) := by
  sorry

end OMA.S_mo_395618
