import Mathlib

/-!
# A180000: lcm{1..n} / swinging_factorial(n) (error term O(n^(1/2+eps)) for its logarithm)

Source: https://oeis.org/A180000 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A180000 (offset 0): a(n) = lcm{1,2,...,n} / swinging_factorial(n) = A003418(n) / A056040(n);
data 1, 1, 1, 1, 2, 2, 3, 3, 12, 4, 10, 10, ...

The entry records:

  Asymptotics: log a(n) ~ n(1 - log 2). It is conjectured that
  log a(n) ~ n(1 - log 2) + O(n^{1/2+eps}) for all eps > 0.

Reading of the source:
* `lcm{1,...,n}` is `(Finset.Icc 1 n).lcm id` (equal to 1 for n = 0), and the swinging factorial
  (A056040) is `n! / (⌊n/2⌋!)^2`. The quotient is taken in `ℝ`, so the statement does not depend
  on the divisibility that makes the data integers.
* The conjecture: for every `ε > 0`, `log a(n) - n (1 - log 2) = O(n^(1/2 + ε))` as `n → ∞` over
  the naturals (natural logarithm). The first line (the leading asymptotic) is implied.
-/

namespace OMA.S_oeis_a180000

open Asymptotics Filter

/-- The swinging factorial `n! / (⌊n/2⌋!)^2` (A056040). -/
def swing (n : ℕ) : ℕ := n.factorial / (n / 2).factorial ^ 2

/-- A180000(n) = lcm{1, ..., n} / swing(n), as a real number. -/
noncomputable def a (n : ℕ) : ℝ := (((Finset.Icc 1 n).lcm id : ℕ) : ℝ) / swing n

/-- The conjecture: `log a(n) = n (1 - log 2) + O(n^(1/2 + ε))` for every `ε > 0`. -/
theorem main : ∀ ε : ℝ, 0 < ε →
    (fun n : ℕ => Real.log (a n) - n * (1 - Real.log 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by
  sorry

end OMA.S_oeis_a180000
