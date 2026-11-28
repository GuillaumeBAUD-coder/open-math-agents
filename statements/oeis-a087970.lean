import Mathlib

/-!
# A087970: Maximal term in Collatz iteration started at 2^n + 1

Source: https://oeis.org/A087970
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the maximal term in the Collatz (3x + 1) iteration started at 2^n + 1.
Conjecture (Chai Wah Wu, Sep 18 2025): a(n) = 3*a(n-1) - 2*a(n-2) for n > 13.
-/

namespace OMA.S_oeis_a087970

/-- One step of the Collatz map. -/
def collatzStep (m : ℕ) : ℕ :=
  if m % 2 = 0 then m / 2 else 3 * m + 1

/-- The Collatz orbit starting from `m`. -/
def collatzOrbit (m : ℕ) : Set ℕ :=
  Set.range (fun k : ℕ => collatzStep^[k] m)

theorem main :
    ∃ a : ℕ → ℕ,
      (∀ n : ℕ, IsGreatest (collatzOrbit (2 ^ n + 1)) (a n)) ∧
      (∀ n : ℕ, 13 < n → a n + 2 * a (n - 2) = 3 * a (n - 1)) := by
  sorry

end OMA.S_oeis_a087970
