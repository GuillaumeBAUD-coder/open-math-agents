import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Werner Schulte's convolution formulas for a triangle of gcd quotients

Source: https://oeis.org/A350900
Companion sequences: https://oeis.org/A057660 and https://oeis.org/A002618
Credit: @anmolspace

The indices in both sums run from 1 through n. Multiplication of arithmetic
functions is Dirichlet convolution, and `pmul` is their pointwise product.
-/

namespace OMA.S_oeis_a350900

open Finset ArithmeticFunction

/-- Euler's totient as an arithmetic function. -/
def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

/-- A002618 is n times its totient. -/
def weight : ArithmeticFunction ℕ := ArithmeticFunction.id.pmul phi

/-- A057660 sums the orders of the elements of the cyclic group of size n. -/
def orderSum : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ k ∈ range n, n / n.gcd (k + 1), by simp⟩

/-- Schulte's double sum, with the identity function giving the triangle's row sum. -/
def triangleSum {R : Type*} [CommSemiring R] (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => ∑ i ∈ range n, ∑ k ∈ range n,
    f (n.gcd (i + 1) / (n.gcd (i + 1)).gcd (k + 1)), by simp⟩

theorem main :
    (∀ (R : Type) [CommSemiring R] (f : ArithmeticFunction R),
      triangleSum f = f.pmul (phi : ArithmeticFunction R) * (orderSum : ArithmeticFunction R)) ∧
    (∀ (R : Type) [CommSemiring R] (f : ArithmeticFunction R),
      f.IsMultiplicative → (triangleSum f).IsMultiplicative) ∧
    triangleSum ArithmeticFunction.id = weight * orderSum := by
  sorry

end OMA.S_oeis_a350900
