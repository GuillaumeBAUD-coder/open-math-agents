import Mathlib

/-!
# A072348: Number of primes whose decimal representation has the form rns

Source: https://oeis.org/A072348
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Number of primes whose decimal representation has the form rns where r and s are single digits.
a(n) <= 16 for all n, a(5) = 16.
Conjecture: a(n) < 16 for n > 5.
-/

namespace OMA.S_oeis_a072348

/-- Number of primes formed by prepending a nonzero digit `r ∈ {1..9}` and appending
a digit `s ∈ {0..9}` to the base-10 representation of `n`. -/
def a (n : ℕ) : ℕ :=
  let d := (Nat.digits 10 n).length
  ((Finset.Icc 1 9 ×ˢ Finset.Icc 0 9).filter (fun rs =>
    Nat.Prime (rs.1 * 10 ^ (d + 1) + n * 10 + rs.2))).card

theorem main :
    ∀ n : ℕ, 5 < n → a n < 16 := by
  sorry

end OMA.S_oeis_a072348
