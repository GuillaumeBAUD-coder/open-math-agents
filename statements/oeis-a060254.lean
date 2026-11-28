import Mathlib

/-!
# A060254: primes which are the sum of two consecutive composite numbers (a(n) ~ n log n)

Source: https://oeis.org/A060254 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A060254 (offset 1): primes which are the sum of two consecutive composite numbers; data
17, 19, 29, 31, 41, 43, 53, 67, 71, 79, ... (19 = 9 + 10).

The entry records (Charles R Greathouse IV, Apr 29 2015):

  Conjecture: a(n) ~ n log n.

Reading of the source:
* A composite number is a natural number greater than 1 that is not prime.
* `p` is a term when `p` is prime and `p = c + (c + 1)` with `c` and `c + 1` both composite.
* `a n` (for `n ≥ 1`) is the `n`-th term in increasing order: `Nat.nth` (which counts from 0) at
  `n - 1`. The sequence is infinite (otherwise `Nat.nth` would make the statement degenerate);
  the asymptotic claim implies this.
* `a(n) ~ n log n` is asymptotic equivalence (`~[atTop]`, ratio tending to 1) over the naturals,
  with the natural logarithm.
-/

namespace OMA.S_oeis_a060254

open Asymptotics Filter

/-- `c` is composite: greater than 1 and not prime. -/
def Composite (c : ℕ) : Prop := 1 < c ∧ ¬ c.Prime

/-- `p` is a prime that is the sum of two consecutive composite numbers. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∃ c, Composite c ∧ Composite (c + 1) ∧ p = c + (c + 1)

/-- A060254(n), the `n`-th such prime (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Greathouse's conjecture: `a(n) ~ n log n`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a060254
