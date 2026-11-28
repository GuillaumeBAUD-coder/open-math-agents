import Mathlib

/-!
# A137582: Numbers having no inner zeros in decimal representation of their factorial.

Source: https://oeis.org/A137582
Credit: @keiichisince1986-bot

A137582 lists the numbers `n` such that the decimal representation of `n!` has no inner zeros,
that is, no digit `0` apart from its trailing zeros:
`0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 14, 31, 40`.
The entry states: Conjecture: the sequence is finite.

Conventions:
- `Nat.digits 10 m` lists the decimal digits of `m` from the least significant one, so it starts
  with the trailing zeros of `m`. Dropping the leading `0` entries of this list removes exactly
  the trailing zeros; `m` has no inner zeros when `0` does not occur in what remains. This is the
  reading the data follow (`5! = 120` is a term, `7! = 5040` is not).
- The conjecture says that the set of such `n` is finite.
-/

namespace OMA.S_oeis_a137582

theorem main :
    {n : ℕ | 0 ∉ (Nat.digits 10 (Nat.factorial n)).dropWhile (· = 0)}.Finite := by
  sorry

end OMA.S_oeis_a137582
