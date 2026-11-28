import Mathlib

/-!
# A013937: a(n) = Sum_{k=1..n} floor(n/k^3) (Cloitre's error exponent 1/4)

Source: https://oeis.org/A013937 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A013937 (offset 0): a(n) = Sum_{k=1..n} floor(n/k^3); data 0, 1, 2, 3, 4, 5, 6, 7, 9, ...
(a(36) = 36 + 4 + 1 = 41).

The entry records (Benoit Cloitre, Nov 05 2012):

  a(n) = Sum_{k=1..n} floor((n/k)^(1/3)) with asymptotic formula:
  a(n) = zeta(3)*n+zeta(1/3)*n^(1/3)+O(n^theta) where theta<1/3 and we conjecture that
  theta=1/4+epsilon is the best possible choice.

Reading of the source:
* `a n = ∑_{k=1}^{n} ⌊n / k^3⌋`, computed with natural division.
* `zeta(3)`, `zeta(1/3)` are values of the Riemann zeta function (Mathlib's `riemannZeta`, real
  at real arguments; `zeta(1/3)` is the analytically continued value); the statement uses real
  parts.
* "theta = 1/4 + epsilon is the best possible choice" is read as the usual two claims about the
  error `E(n) = a(n) - zeta(3) n - zeta(1/3) n^(1/3)`: `E(n) = O(n^(1/4 + ε))` for every `ε > 0`,
  and `E(n)` is not `O(n^θ)` for any `θ < 1/4`. Both are big-O as `n → ∞` over the naturals.
-/

namespace OMA.S_oeis_a013937

open Asymptotics Filter

/-- A013937(n) = ∑_{k=1}^{n} ⌊n / k^3⌋. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n / k ^ 3

/-- The error term `a(n) - ζ(3) n - ζ(1/3) n^(1/3)`. -/
noncomputable def E (n : ℕ) : ℝ :=
  (a n : ℝ) - (riemannZeta 3).re * n - (riemannZeta (1 / 3)).re * (n : ℝ) ^ ((1 : ℝ) / 3)

/-- Cloitre's conjecture: the error is `O(n^(1/4 + ε))` for every `ε > 0`, and this exponent is
best possible: it is not `O(n^θ)` for any `θ < 1/4`. -/
theorem main :
    (∀ ε : ℝ, 0 < ε → E =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 + ε))) ∧
      ∀ θ : ℝ, θ < 1 / 4 → ¬ E =O[atTop] (fun n : ℕ => (n : ℝ) ^ θ) := by
  sorry

end OMA.S_oeis_a013937
