import Mathlib

/-!
# A193230: the "PrimeLatz" map always ends in a cycle (Angelini's conjecture)

Source: https://oeis.org/A193230 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A193230 (offset 1): start with 1; if even, divide by 2; if odd, add the next three primes;
data 1, 11, 60, 30, 15, 74, 37, 168, ... It is the trajectory of 1 under the map A174221
(1 -> 1 + 2 + 3 + 5 = 11, 11 -> 11 + 13 + 17 + 19 = 60).

The entry records:

  Angelini conjectures that the orbit under A174221 becomes periodic for any initial value. He
  calls this the PrimeLatz conjecture, as tribute to L. Collatz, known for the 3n+1 conjecture.

Reading of the source:
* The map `f` (A174221): `f x = x / 2` for even `x`, and for odd `x`, `f x = x + q₁ + q₂ + q₃`
  where `q₁ < q₂ < q₃` are the three smallest primes greater than `x` ("the next three primes";
  this matches 1 -> 11 and 11 -> 60).
* "any initial value": every natural number `x` (0 is a fixed point).
* "the orbit becomes periodic": there are `K` and `p > 0` with `f^[K + p] x = f^[K] x`.
-/

namespace OMA.S_oeis_a193230

/-- The `i`-th prime greater than `x` (counting from `i = 0`). -/
noncomputable def nextPrime (x i : ℕ) : ℕ := Nat.nth (fun q => q.Prime ∧ x < q) i

/-- A174221: halve even numbers; add the next three primes to odd numbers. -/
noncomputable def f (x : ℕ) : ℕ :=
  if Even x then x / 2 else x + nextPrime x 0 + nextPrime x 1 + nextPrime x 2

/-- Angelini's PrimeLatz conjecture: every orbit of `f` is eventually periodic. -/
theorem main : ∀ x : ℕ, ∃ K p : ℕ, 0 < p ∧ f^[K + p] x = f^[K] x := by
  sorry

end OMA.S_oeis_a193230
