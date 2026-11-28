import Mathlib

/-!
# A363198: a(n) shares a factor with a(n-1) + a(n-2) + a(n-3) (a permutation?)

Source: https://oeis.org/A363198 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A363198 (offset 1): a(n) = n for n <= 3; for n >= 4, a(n) is the smallest positive integer that
has not appeared previously in this sequence and shares a factor with a(n-1) + a(n-2) + a(n-3);
data 1, 2, 3, 4, 6, 13, 23, 7, 43, 73, 9, 5, 12, ...

The entry records:

  Conjecture: This sequence is a permutation of the natural numbers.

Reading of the source:
* The sequence is indexed from 1 (offset 1) and takes positive values; "the natural numbers" are
  the positive integers, the values the definition can produce (A363198(1) = 1).
* "shares a factor with s" means `gcd(m, s) > 1`.
* `IsA363198 f` says that `f` follows the definition on the indices `n ≥ 1` (values of `f` at 0
  are ignored). For `n ≥ 4` the sum `s` of the three previous terms is at least 6, so some unused
  multiple of `s` exists and the least admissible value is well defined: exactly one sequence on
  the indices `n ≥ 1` satisfies `IsA363198`, namely A363198. `main` quantifies over it.
* "is a permutation of the natural numbers": `f` maps `{n | 1 ≤ n}` bijectively onto itself.
-/

namespace OMA.S_oeis_a363198

/-- `f` satisfies the defining rule of A363198 at every index `n ≥ 1`. -/
def IsA363198 (f : ℕ → ℕ) : Prop :=
  (∀ n, 1 ≤ n → n ≤ 3 → f n = n) ∧
    ∀ n, 4 ≤ n →
      IsLeast {m : ℕ | 0 < m ∧ (∀ j, 1 ≤ j → j < n → f j ≠ m) ∧
          1 < Nat.gcd m (f (n - 1) + f (n - 2) + f (n - 3))} (f n)

/-- The sequence is a permutation of the positive integers. -/
theorem main : ∀ f : ℕ → ℕ, IsA363198 f → Set.BijOn f {n | 1 ≤ n} {n | 1 ≤ n} := by
  sorry

end OMA.S_oeis_a363198
