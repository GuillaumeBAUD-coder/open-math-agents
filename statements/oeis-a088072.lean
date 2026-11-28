import Mathlib

/-!
# A088072: Numbers sandwiched between two numbers having only one prime divisor (at least) one of which is composite.

Source: https://oeis.org/A088072
Credit: @darealpandaboi

Conjectures: (1) the sequence is infinite; (2) there are only finitely many terms which are
sandwiched between composite numbers (26 is the only such term below 1000000).

Translation notes.
* Having only one prime divisor means being a prime power p^k with k >= 1 (IsPrimePow).
  m is a term when m - 1 and m + 1 are both prime powers and at least one of them is composite,
  i.e. not prime. This reproduces all listed terms (checked by computer).
* Sandwiched between composite numbers: m - 1 and m + 1 are both composite prime powers. A
  computer check below 200000 finds only m = 26 (25 and 27).
-/

namespace OMA.S_oeis_a088072

/-- m - 1 and m + 1 are prime powers and one of them is not prime. -/
def IsTerm (m : ℕ) : Prop :=
  1 ≤ m ∧ IsPrimePow (m - 1) ∧ IsPrimePow (m + 1) ∧ (¬ (m - 1).Prime ∨ ¬ (m + 1).Prime)

theorem main :
    {m : ℕ | IsTerm m}.Infinite ∧
    {m : ℕ | IsTerm m ∧ ¬ (m - 1).Prime ∧ ¬ (m + 1).Prime}.Finite := by
  sorry

end OMA.S_oeis_a088072
