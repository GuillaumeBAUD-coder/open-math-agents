import Mathlib

/-!
# A051783: Numbers k such that 3^k + 2 is prime

Source: https://oeis.org/A051783
Credit: @jrflga (agent: Claude Code, model claude-fable-5-2)

OEIS comment (Maheswara Rao Valluri, Jun 01 2020): Conjecture: The number `n = 3^k + 2` is prime
if and only if `2^((n-1)/2) == -1 (mod n)`. N. J. A. Sloane adds (Sep 07 2020): note that this is
an if and only if assertion, so it does not follow from Fermat's Little Theorem.

The entry has offset 1 and begins `0, 1, 2, 3, 4, 8, 10, 14, 15, 24, 26, 36, 63, ...`, so `k`
ranges over all natural numbers, `k = 0` included (`3^0 + 2 = 3` is prime and `2^1 = -1 (mod 3)`).

## Encoding

* `n k = 3^k + 2`. It is odd and at least `3`, so the natural-number subtraction `n k - 1` is
  exact and `(n k - 1) / 2` is an exact division.
* The congruence is stated in the integers with `Int.ModEq`:
  `Int.ModEq m x y` means that `x` and `y` leave the same remainder modulo `m`.
* `main` is the equivalence for every `k`. (For `k < 400` both sides agree, and `3^k + 2` is
  prime exactly for `k = 0, 1, 2, 3, 4, 8, 10, 14, 15, 24, 26, 36, 63, 98, 110, 123, 126, 139,
  235, 243, 315, 363, 386, 391`, as in the entry.)
-/

namespace OMA.S_oeis_a051783

/-- The number `n = 3^k + 2` of the conjecture. -/
def n (k : ℕ) : ℕ := 3 ^ k + 2

theorem main :
    ∀ k : ℕ, (n k).Prime ↔ Int.ModEq ((n k : ℕ) : ℤ) ((2 : ℤ) ^ ((n k - 1) / 2)) (-1) := by
  sorry

end OMA.S_oeis_a051783
