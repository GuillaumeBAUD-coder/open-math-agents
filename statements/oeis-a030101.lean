import Mathlib

/-!
# A030101: binary reversal

Source: https://oeis.org/A030101
Credit: @Moti1125

`a(n)` is the number produced when `n` is converted to binary digits, the binary digits are
reversed, and the result is converted back into a decimal number.

Conjecture (Velin Yanev, 2017): `a(n) = 2 w(n) - 2 w(A053645(n)) - 1` for `n > 0`, where
`w = A264596`.

The sequences used, as defined in the OEIS:
- A053645: `n - 2^⌊log₂ n⌋`, the distance from `n` to the largest power of `2` that is `≤ n`.
- A264596: let `S_n` be the list of the first nonnegative numbers up to `n`, written in binary
  with least significant bits on the left and sorted into lexicographic order; `w(n)` is the
  position of `n` in `S_n`, indexing from `0`.

Conventions:
- `S_n` consists of `0, 1, …, n`; this is what the data of A264596 requires (`w(1) = 1`,
  `w(2) = 1`). The binary word of `0` is `"0"`, the binary word of `m > 0` is its digit list with
  the least significant bit first (`Nat.digits 2 m`). The order is the lexicographic order on
  lists of digits, in which a proper prefix comes first.
- The position of `n` in the sorted list is the number of `m ≤ n` whose word is smaller.
- The identity is stated in `ℤ`, so the subtractions are not truncated.
-/

namespace OMA.S_oeis_a030101

/-- A030101: reverse the binary digits of `n`. -/
def binRev (n : ℕ) : ℕ := Nat.ofDigits 2 (Nat.digits 2 n).reverse

/-- A053645: `n - 2^⌊log₂ n⌋`. -/
def a053645 (n : ℕ) : ℕ := n - 2 ^ Nat.log 2 n

/-- The binary word of `n`, least significant bit first; the word of `0` is `[0]`. -/
def lsbWord (n : ℕ) : List ℕ := if n = 0 then [0] else Nat.digits 2 n

/-- A264596: the position of `n` among `0, …, n` sorted by the lexicographic order of their
binary words written least significant bit first. -/
def a264596 (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun m => lsbWord m < lsbWord n)).card

theorem main :
    ∀ n : ℕ, 0 < n →
      (binRev n : ℤ) = 2 * (a264596 n : ℤ) - 2 * (a264596 (a053645 n) : ℤ) - 1 := by
  sorry

end OMA.S_oeis_a030101
