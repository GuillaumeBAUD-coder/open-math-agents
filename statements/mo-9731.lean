import Mathlib

/-!
# Polynomial representing all nonnegative integers

Source: https://mathoverflow.net/questions/9731/polynomial-representing-all-nonnegative-integers
Credit: @antonumias24-tech

The question (Bjorn Poonen): is there a 2-variable polynomial `f(x, y) ∈ ℚ[x, y]` such that
`f(ℤ × ℤ) = ℕ`, where `ℕ` is the set of nonnegative integers?

Translation choices.
* As in the upstream formalization of the companion question MathOverflow 21003, the question
  is stated as the existence claim it asks about. The expected answer is negative (an answer on
  the source page shows that such an `f` would contradict Vojta's conjecture), so a resolution
  would most likely be a disproof of `main`.
* A polynomial in two variables over `ℚ` is `f : MvPolynomial (Fin 2) ℚ`; its value at the
  lattice point `(a, b) ∈ ℤ × ℤ` is `MvPolynomial.eval ![(a : ℚ), (b : ℚ)] f`.
* `f(ℤ × ℤ) = ℕ` is the equality of the image of `ℤ × ℤ` with the set of nonnegative integers
  viewed inside `ℚ`, i.e. the range of the cast `ℕ → ℚ`. In particular every value taken on the
  lattice is a nonnegative integer, and every nonnegative integer, `0` included, is taken.
-/

namespace OMA.S_mo_9731

theorem main :
    ∃ f : MvPolynomial (Fin 2) ℚ,
      Set.range (fun p : ℤ × ℤ => MvPolynomial.eval ![(p.1 : ℚ), (p.2 : ℚ)] f) =
        Set.range (fun n : ℕ => (n : ℚ)) := by
  sorry

end OMA.S_mo_9731
