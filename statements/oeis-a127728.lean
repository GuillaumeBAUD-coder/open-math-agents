import Mathlib

/-!
# A127728: sum of squared coefficients of the q-factorials (Kotesovec's asymptotic)

Source: https://oeis.org/A127728 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A127728 (offset 0): sum of squared coefficients of q in the q-factorials; data
1, 1, 2, 10, 106, 1930, 53612, ...
The entry's example: faq(n) = Product_{k=1..n} (1-q^k)/(1-q) for n > 0, faq(0) = 1;
faq(4) = 1 + 3q + 5q^2 + 6q^3 + 5q^4 + 3q^5 + q^6, so a(4) = 1 + 9 + 25 + 36 + 25 + 9 + 1 = 106.

The entry records (Vaclav Kotesovec, Oct 22 2020):

  Conjecture: a(n) ~ 6 * sqrt(Pi) * n^(2*n - 1/2) / exp(2*n).

Reading of the source:
* The q-factorial is the polynomial `∏_{k=1}^{n} (1 + q + ... + q^(k-1))` with natural-number
  coefficients (each factor `(1 - q^k)/(1 - q)` is this polynomial); the empty product is 1.
* `a n` is the sum of the squares of its coefficients.
* `a(n) ~ 6 √π n^(2n - 1/2) / e^(2n)` is asymptotic equivalence (`~[atTop]`, ratio tending to 1)
  as `n → ∞` over the naturals; `n^(2n - 1/2)` is the real power.
-/

namespace OMA.S_oeis_a127728

open Asymptotics Filter Polynomial

/-- The q-factorial `[n]_q! = ∏_{k=1}^{n} (1 + q + ... + q^(k-1))`. -/
noncomputable def qFactorial (n : ℕ) : ℕ[X] :=
  ∏ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), (X : ℕ[X]) ^ i

/-- A127728(n): the sum of the squared coefficients of the q-factorial of `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range ((qFactorial n).natDegree + 1), (qFactorial n).coeff i ^ 2

/-- Kotesovec's conjecture: `a(n) ~ 6 √π n^(2n - 1/2) / e^(2n)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      (fun n : ℕ => 6 * Real.sqrt Real.pi * (n : ℝ) ^ (2 * (n : ℝ) - 1 / 2) / Real.exp (2 * n)) := by
  sorry

end OMA.S_oeis_a127728
