import Mathlib

/-
# Pillai's conjecture

Source: https://en.wikipedia.org/wiki/Pillai's_conjecture
Credit: @Porphyrios5273

Statement (authoritative source, Pillai's conjecture section):
  in 1931 Pillai conjectured that for fixed positive integers A, B, C the
  equation A x^n - B y^m = C has only finitely many solutions (x, y, m, n)
  with (m, n) not equal to (2, 2).

We state exactly this: for all positive integers A, B, C, the set of quadruples
(x, y, m, n) of natural numbers with (m, n) ≠ (2, 2) satisfying A*x^n - B*y^m = C
is finite. No range restriction beyond (m, n) ≠ (2, 2) is added, matching the source.
The theorem body is left as the placeholder proof: a person reviews the translation
before merging.
-/

namespace OMA.S_wp_pillai_s_conjecture

-- definitions the statement needs (complete, no placeholder, no axiom)

theorem main :
    ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
      { (x, y, m, n) : (ℕ × ℕ × ℕ × ℕ) |
        (m, n) ≠ (2, 2) ∧ A * x ^ n - B * y ^ m = C }.Finite := by
  sorry

end OMA.S_wp_pillai_s_conjecture