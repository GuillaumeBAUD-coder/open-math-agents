import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# OEIS A395454: the row polynomial recurrence stated in the entry

Source: https://oeis.org/A395454, revision 30 (October 14, 2026), Peter
Luschny; the recurrence is a conjecture in the entry's formula section,
signed Per W. Alexandersson, June 27, 2026. The triangle is
T(n, k) = Sum_{j=0..n} C(-j-1, -n-1)*E2(j, n-k), with
rows numbered from 0 as in the entry. With P(n) the generating polynomial in
t of row n, the entry states as a conjecture: P(n) = (n - 2*t + n*t - 2)*P(n-1)
+ (t - t^2)*P'(n-1) + t*(2*n-4)*P(n-2). It is stated here for every n >= 2,
where P(n-2) is defined. Conventions: C(-j-1, -n-1) for j <= n is read as in
the entry's Maple code, by symmetry, which gives (-1)^(n-j) * C(n, j); E2 is
the second-order Eulerian number of A201637, by its recurrence, indexed from 0.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Sol and other OpenAI models, checked with Claude.
-/

namespace OMA.S_oeis_a395454

open Polynomial
open scoped BigOperators

/-- The A201637 recurrence, with zero entries beyond the row and with
`k + 1` as the index in the last equation. -/
def eulerian2 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => eulerian2 n 0
  | n + 1, k + 1 =>
      if k ≤ n then
        ((k : ℤ) + 2) * eulerian2 n (k + 1) + (2 * (n : ℤ) - (k : ℤ)) * eulerian2 n k
      else 0

/-- Maple's `binomial(-j - 1, -n - 1)` for `j ≤ n`, by symmetry and the
negative upper argument identity. -/
def signedBinomial (n j : ℕ) : ℤ :=
  (-1) ^ (n - j) * (n.choose j : ℤ)

/-- The entry of the triangle at row `n`, column `k`, for `k ≤ n`. -/
def triangle (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), signedBinomial n j * eulerian2 j (n - k)

noncomputable def rowPolynomial (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (triangle n k) * X ^ k

noncomputable def recurrenceRHS (n : ℕ) : ℤ[X] :=
  ((n : ℤ[X]) - 2 * X + (n : ℤ[X]) * X - 2) * rowPolynomial (n - 1) +
    (X - X ^ 2) * (rowPolynomial (n - 1)).derivative +
    X * (2 * (n : ℤ[X]) - 4) * rowPolynomial (n - 2)

theorem main : ∀ n : ℕ, 2 ≤ n → rowPolynomial n = recurrenceRHS n := by
  sorry

end OMA.S_oeis_a395454
