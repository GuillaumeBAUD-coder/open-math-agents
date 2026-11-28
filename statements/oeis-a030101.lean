import Mathlib

/-!
# A030101: a(n) is the number produced when n is converted to binary digits, the binary digits are reversed and then converted back into a decimal number

Source: https://oeis.org/A030101
Credit: @Harsha0912

Conjecture (Velin Yanev, in A030101): a(n) = 2*w(n) - 2*w(A053645(n)) - 1 for n > 0,
where w = A264596.

Conventions:
* A030101 (offset 0): `a n = Nat.ofDigits 2 (Nat.digits 2 n).reverse`
  (`Nat.digits 2 n` lists the binary digits of n, least significant first).
* A053645: `n - 2 ^ Nat.log 2 n`, the distance from n to the largest power of 2 that is at most n.
* A264596 (offset 0), from its OEIS definition: write 0, 1, ..., n in binary with least
  significant bits on the left, sort lexicographically, and let w(n) be the 0-based position of n.
  Thus w(n) is the number of i in [0, n] whose least-significant-first binary word is
  lexicographically smaller than that of n. The binary word of i is `Nat.digits 2 i`, except that
  0 is written as the single digit 0 (`Nat.digits 2 0` is empty).
* The right-hand side is evaluated in the integers.
-/

namespace OMA.S_oeis_a030101

/-- A030101: binary reversal of `n`. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 2 (Nat.digits 2 n).reverse

/-- A053645: distance from `n` to the largest power of `2` less than or equal to `n`. -/
def a053645 (n : ℕ) : ℕ := n - 2 ^ Nat.log 2 n

/-- The binary word of `i`, least significant bit first, with `0` written as one digit `0`. -/
def word (i : ℕ) : List ℕ := if i = 0 then [0] else Nat.digits 2 i

/-- A264596: the 0-based position of `n` when the words of `0, 1, ..., n` are sorted
lexicographically. -/
def w (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter (fun i => word i < word n)).card

/-- Yanev's conjecture: for `n > 0`, `a(n) = 2 w(n) - 2 w(A053645(n)) - 1`. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n : ℤ) = 2 * (w n : ℤ) - 2 * (w (a053645 n) : ℤ) - 1 := by
  sorry

end OMA.S_oeis_a030101
