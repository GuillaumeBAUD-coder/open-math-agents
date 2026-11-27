import FormalConjectures.GreensOpenProblems.«95»

-- Reduction Green95.green_95.variants.three_palindromes.R1 of Cilleruelo, Luca and Baxter. — three palindromes
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Every positive integer is a sum of three base-`g` palindromes, split at the single-digit range

The theorem of Cilleruelo, Luca and Baxter is proved by strong induction on the number of base-`g`
digits of `n`, feeding a base case into a digit-by-digit construction.  The two ingredients are
genuinely separate:

* `H1` is the base case of that induction: a positive `n` below the base `g` has a single digit, so
  it is already a palindrome, and `n = n + 0 + 0` writes it as a sum of three palindromes (`0` is a
  palindrome in every base, since `Nat.digits g 0 = []`).  Nothing about the digits of `n` beyond
  `Nat.digits g n = [n]` is needed.
* `H2` is the induction step: every `n` with at least two base-`g` digits, i.e. `g ≤ n`, is a sum of
  three palindromes.  This is where the whole of the mathematical difficulty lies.

Splitting at `g` isolates the (base-free) single-digit case, which is uniform in `g`, from the
digit-manipulation argument for larger `n`.
-/

namespace OMA.R_Green95_green_95_variants_three_palindromes_R1

open Green95

/-- The single-digit case: every `n` with `0 < n < g` is a sum of three base-`g` palindromes. -/
def H1 : Prop :=
  ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, 0 < n → n < g →
    ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p + q + r = n

/-- The induction step: every `n ≥ g` is a sum of three base-`g` palindromes. -/
def H2 : Prop :=
  ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, g ≤ n →
    ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p + q + r = n

theorem main : H1 → H2 → type_of% @Green95.green_95.variants.three_palindromes := by
  intro h1 h2 g hg n hn
  by_cases h : n < g
  · exact h1 g hg n hn h
  · exact h2 g hg n (by omega)

end OMA.R_Green95_green_95_variants_three_palindromes_R1
