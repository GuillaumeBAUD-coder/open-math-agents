import Mathlib

/-!
# OEIS A049096: numbers k such that 2^k + 1 is not squarefree

Source: https://oeis.org/A049096 (OEIS Foundation, CC BY-SA 4.0).

Entry: Numbers k such that 2^k + 1 is divisible by a square > 1 (offset 1,
data 3, 9, 10, 15, 21, 27, 30, ...).

Conjecture (Benoit Cloitre, Aug 20 2002): lim n -> infinity a(n)/n = C exists
and 4 < C < 9/2.

Formalization notes:
* "divisible by a square > 1" is `¬ Squarefree (2 ^ k + 1)`.
* The offset is 1, so `a n` is the n-th such k counted from `n = 1`, that is
  `Nat.nth _ (n - 1)`. The value at `n = 0` does not affect the limit.
* The sequence is infinite (every odd multiple of 3 is a term, since 9 divides
  2^(3m) + 1 for odd m), so `Nat.nth` enumerates all of it.
-/

namespace OMA.S_oeis_a049096

open Filter Topology

/-- A049096(n): the n-th number k (n ≥ 1) such that 2^k + 1 is divisible by a square > 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => ¬ Squarefree (2 ^ k + 1)) (n - 1)

/-- Cloitre's conjecture: a(n)/n converges to a limit C with 4 < C < 9/2. -/
theorem main :
    ∃ C : ℝ, 4 < C ∧ C < 9 / 2 ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a049096
