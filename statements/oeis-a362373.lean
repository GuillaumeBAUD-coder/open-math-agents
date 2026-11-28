import Mathlib

/-!
# A362373: sums of indices of previous appearances, else a recaman step (every integer appears?)

Source: https://oeis.org/A362373 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A362373 (offset 0): a(0) = 0; for n > 0, if n appears in the sequence then a(n) is the sum of the
indices of all previous appearances of n. Otherwise a(n) = a(n-1) - n if nonnegative and not
already in the sequence, otherwise a(n) = a(n-1) + n.
Data 0, 1, 3, 2, 6, 11, 4, 11, 19, 10, 9, 12, ...
(a(2) = 3, so a(3) = 2; a(5) = 11, since 5 has not appeared and a(4) - 5 = 1 has; a(5) = a(7) = 11
and 5 + 7 = 12, so a(11) = 12.)

The entry records (Yifan Xie, Apr 24 2023):

  Conjecture: All nonnegative integers appear in this sequence.

Reading of the source:
* "n appears in the sequence" at step n means: among the terms already defined, a(j) = n for
  some j < n (the examples confirm this reading); the new term is then the sum of all such j.
* Otherwise, with b = a(n-1): if b - n ≥ 0 and b - n is not among a(0), ..., a(n-1), then
  a(n) = b - n; else a(n) = b + n. Values are natural numbers (all terms are nonnegative).
* `IsA362373 f` says that `f` follows this rule; it determines `f` uniquely (by recursion on n),
  so `main` is a statement about A362373 itself.
* "All nonnegative integers appear": every `k : ℕ` equals `f n` for some `n`.
-/

namespace OMA.S_oeis_a362373

/-- `f` satisfies the defining rule of A362373. -/
def IsA362373 (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧
    ∀ n, 1 ≤ n →
      ((∃ j, j < n ∧ f j = n) →
          f n = ∑ j ∈ (Finset.range n).filter (fun j => f j = n), j) ∧
      ((¬ ∃ j, j < n ∧ f j = n) →
          f n = if n ≤ f (n - 1) ∧ ∀ j, j < n → f j ≠ f (n - 1) - n
            then f (n - 1) - n else f (n - 1) + n)

/-- Every nonnegative integer appears in the sequence. -/
theorem main : ∀ f : ℕ → ℕ, IsA362373 f → ∀ k : ℕ, ∃ n, f n = k := by
  sorry

end OMA.S_oeis_a362373
