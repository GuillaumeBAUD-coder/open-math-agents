import Mathlib

/-!
# A003016: Number of occurrences of n as an entry in rows <= n of Pascal's triangle (A007318).

Source: https://oeis.org/A003016
Credit: @Olivier31200

OEIS defines a(n) as the number of occurrences of n as an entry in rows <= n of
Pascal's triangle, that is, the number of pairs (r, k) with r <= n, k <= r and
Nat.choose r k = n (row r has entries k = 0..r). Singmaster conjectures that this
sequence is bounded.
-/

namespace OMA.S_oeis_a003016

/-- Number of occurrences of `n` as an entry in rows `r <= n` of Pascal's
triangle: the number of pairs `(r, k)` with `r <= n`, `k <= r` and
`Nat.choose r k = n`. -/
def occ (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p : ℕ × ℕ => p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = n)).card

/-- Singmaster's conjecture, as recorded on OEIS A003016: the number of
occurrences of `n` as an entry in rows `r <= n` of Pascal's triangle is bounded,
uniformly in `n`. -/
theorem main : ∃ C : ℕ, ∀ n : ℕ, occ n ≤ C := by
  sorry

end OMA.S_oeis_a003016

