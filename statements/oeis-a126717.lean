import Mathlib

/-!
# A126717: least odd k such that k*2^n - 1 is prime (Ordowski's O(n log n) bound)

Source: https://oeis.org/A126717 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A126717 (offset 0): least odd k such that k*2^n-1 is prime; data 3, 3, 1, 1, 3, 1, 3, 1, 5, 7, 5,
... (a(10) = 5 because 5*2^10-1 is prime but 1*2^10-1 and 3*2^10-1 are not).

The entry records (Thomas Ordowski, Oct 15 2014):

  Conjecture: a(n) = O(n log n).

Reading of the source:
* `a n` is the least odd natural `k` with `k * 2^n - 1` prime. Such `k` exists for every `n`
  (Dirichlet's theorem for the progression of residue `-1` modulo `2^(n+1)`; the entry also
  cites the bound a(n) << 19^n), so the infimum is attained.
* `a(n) = O(n log n)` is a big-O as `n → ∞` over the naturals, with the natural logarithm.
-/

namespace OMA.S_oeis_a126717

open Asymptotics Filter

/-- A126717(n): the least odd `k` such that `k * 2^n - 1` is prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | Odd k ∧ (k * 2 ^ n - 1).Prime}

/-- Ordowski's conjecture: `a(n) = O(n log n)`. -/
theorem main : (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a126717
