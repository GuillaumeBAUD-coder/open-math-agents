import FormalConjectures.Mathoverflow.«339137»
import Mathlib

-- Reduction Mathoverflow339137.mathoverflow_339137.R1 of MathOverflow 339137: if P and Q are
-- monic real polynomials with nonnegative coefficients and P * Q has all coefficients in
-- {0, 1}, are P and Q themselves 0-1 polynomials?
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the problem itself. H1 is the case where one factor
-- has degree at most 1. For P = X + a the coefficients satisfy r_0 = a q_0 and
-- r_(k+1) = q_k + a q_(k+1); the top coefficient forces a at most 1, the first nonzero
-- coefficient of Q forces a at least 1 (or a = 0), and then q_k = r_k - q_(k-1) stays in {0, 1}
-- by induction. H2, where both factors have degree at least 2, carries the whole open difficulty.

namespace OMA.R_Mathoverflow339137_mathoverflow_339137_R1

open Polynomial Mathoverflow339137

/-- The question when one of the two factors is constant or linear. -/
def H1 : Prop :=
  ∀ (P Q R : ℝ[X]), P.Monic → Q.Monic → (∀ c ∈ P.coeffs, 0 ≤ c) → (∀ c ∈ Q.coeffs, 0 ≤ c) →
    R = P * Q → IsZeroOne R → (P.natDegree ≤ 1 ∨ Q.natDegree ≤ 1) →
    IsZeroOne P ∧ IsZeroOne Q

/-- The question when both factors have degree at least 2 (open). -/
def H2 : Prop :=
  ∀ (P Q R : ℝ[X]), P.Monic → Q.Monic → (∀ c ∈ P.coeffs, 0 ≤ c) → (∀ c ∈ Q.coeffs, 0 ≤ c) →
    R = P * Q → IsZeroOne R → 2 ≤ P.natDegree → 2 ≤ Q.natDegree →
    IsZeroOne P ∧ IsZeroOne Q

theorem main : H1 → H2 → type_of% @Mathoverflow339137.mathoverflow_339137 := by
  intro h1 h2 P Q R hP hQ hp hq h hR
  by_cases hd : P.natDegree ≤ 1 ∨ Q.natDegree ≤ 1
  · exact h1 P Q R hP hQ hp hq h hR hd
  · rw [not_or, not_le, not_le] at hd
    exact h2 P Q R hP hQ hp hq h hR (by omega) (by omega)

end OMA.R_Mathoverflow339137_mathoverflow_339137_R1
