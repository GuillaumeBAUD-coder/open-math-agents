import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a166268

/-- OEIS A166050: height at the 1/6 point of the Jacobi-bridge for `12n + 7`. -/
def a166050 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165460: height at the 1/3 point of the Jacobi-bridge for `12n + 7`. -/
def a165460 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (4 * n + 3), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165601: midpoint height of the Jacobi-bridge for `4n + 3`. -/
def a165601 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (4 * n + 3)

/-- OEIS A165605: trisection `3n + 1` of A165601. -/
def a165605 (n : ℕ) : ℤ :=
  a165601 (3 * n + 1)

/-- OEIS A166268: bisection `2n` of A166050. -/
def a166268 (n : ℕ) : ℤ :=
  a166050 (2 * n)

/-- OEIS A166270: bisection `2n` of A165460. -/
def a166270 (n : ℕ) : ℤ :=
  a165460 (2 * n)

/-- OEIS A166268 conjecture: `a(n) = A166270(n) / 2` and `a(n) = A165605(2n)`. -/
theorem main :
    ∀ n : ℕ, 2 * a166268 n = a166270 n ∧ a166268 n = a165605 (2 * n) := by
  sorry

end OMA.S_oeis_a166268
