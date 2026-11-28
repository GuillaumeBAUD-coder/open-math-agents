import Mathlib

/-!
# A252867: the binary "set" analogue of the EKG sequence is a permutation

Source: https://oeis.org/A252867 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A252867 (offset 0): a(n) = n if n <= 2, otherwise the smallest number not occurring earlier having
in its binary representation at least one bit in common with a(n-2), but none with a(n-1); data
0, 1, 2, 5, 10, 4, 3, 12, 17, 6, 9, 18, ...

The entry records (comment modified by N. J. A. Sloane, Jan 10 2015):

  Conjectured to be a permutation of the nonnegative integers.

Reading of the source:
* "having at least one bit in common with x" means the bitwise AND with `x` is nonzero
  (`m &&& x ≠ 0`); "none with y" means `m &&& y = 0`.
* `IsA252867 f` says that `f` follows the definition: `f n = n` for `n ≤ 2`, and for `n ≥ 3`,
  `f n` is the least `m` not among `f 0, ..., f (n-1)` with `m &&& f (n-2) ≠ 0` and
  `m &&& f (n-1) = 0`. This determines `f` (by recursion on `n`, granted that such an `m` exists
  at every step, which the source takes for granted); `main` quantifies over it.
* "a permutation of the nonnegative integers": `f` is a bijection `ℕ → ℕ`.
-/

namespace OMA.S_oeis_a252867

/-- `f` satisfies the defining rule of A252867. -/
def IsA252867 (f : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ 2 → f n = n) ∧
    ∀ n, 3 ≤ n →
      IsLeast {m : ℕ | (∀ j, j < n → f j ≠ m) ∧ m &&& f (n - 2) ≠ 0 ∧ m &&& f (n - 1) = 0} (f n)

/-- The sequence is a permutation of the nonnegative integers. -/
theorem main : ∀ f : ℕ → ℕ, IsA252867 f → Function.Bijective f := by
  sorry

end OMA.S_oeis_a252867
