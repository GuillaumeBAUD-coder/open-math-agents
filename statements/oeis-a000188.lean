import Mathlib

/-!
# A000188: Number of solutions to x^2 == 0 (mod n).

Source: https://oeis.org/A000188
Credit: @rabdelaal

OEIS A000188 gives, as its first description, the number of solutions of `x ^ 2 = 0`
modulo `n`, and records the conjecture `a(n) = Sum_{k = 1..n} A010052(n k)`, where
`A010052(m)` is the characteristic function of the squares, i.e. the sum counts the
`k in [1, n]` such that `n * k` is a perfect square.
-/

namespace OMA.S_oeis_a000188

/-- The OEIS A000188 sequence: the number of residue classes `x mod n` with
`x ^ 2 ≡ 0 (mod n)`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n => (x : ℕ) ^ 2 % n = 0).card

/-- The conjecture recorded in OEIS A000188: `a(n)` equals the number of `k in [1, n]`
such that `n * k` is a square (the sum of the characteristic function of the squares
A010052 at `n k`). -/
theorem main : ∀ n > 0, a n =
    (Finset.Icc 1 n |>.filter fun k => Nat.sqrt (n * k) * Nat.sqrt (n * k) = n * k).card := by
  sorry

end OMA.S_oeis_a000188
