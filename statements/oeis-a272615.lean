import Mathlib

/-!
# A272615: Numbers with digits in descending numerical order in base 2, 3 and 4 expansions.

Source: https://oeis.org/A272615
Credit: @keiichisince1986-bot

A272615 lists the numbers whose digits are in descending order in each of their base-2, base-3
and base-4 expansions: `0, 1, 2, 3, 4, 8, 12, 63, 240`.
The entry states: a(10), if it exists, has more than 1000 decimal digits. Conjecture: there are
no more terms in this sequence.

Conventions:
- Descending means nonincreasing, read from the leading digit: this is the reading the data
  follow (`12 = 1100` in base 2 and `8 = 22` in base 3 have repeated digits).
  `Nat.digits b n` lists the digits from the least significant one, so
  `(Nat.digits b n).reverse` lists them from the leading digit, and the condition is that this
  list is pairwise `≥`.
- For `n = 0` the digit lists are empty, matching the first term `0`.
- No more terms means that the data list every term, so the conjecture says that the set of
  such numbers is exactly `{0, 1, 2, 3, 4, 8, 12, 63, 240}`.
-/

namespace OMA.S_oeis_a272615

/-- The base-`b` digits of `n`, read from the leading digit, are nonincreasing. -/
def DigitsDescending (b n : ℕ) : Prop :=
  (Nat.digits b n).reverse.Pairwise (· ≥ ·)

theorem main :
    {n : ℕ | DigitsDescending 2 n ∧ DigitsDescending 3 n ∧ DigitsDescending 4 n} =
      {0, 1, 2, 3, 4, 8, 12, 63, 240} := by
  sorry

end OMA.S_oeis_a272615
