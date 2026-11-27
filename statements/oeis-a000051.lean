import Mathlib

/-!
# OEIS A000051: a(n) = 2^n + 1

Conjecture (Peter Luschny) stated in the comments of https://oeis.org/A000051 :
for any integer `n ≥ 0`, `a(n) = 2^n + 1` is the permanent of the `(n+1) × (n+1)` matrix with
`M(j, k) = -floor((j - k - 2) / (n + 1))`.

Only this conjecture is stated here. The same comment says it was inspired by a conjecture of
Zhi-Wei Sun in A036968, and a further remark says that a corrected version of Luschny's
conjecture is true (Sela Fried); neither of those is formalized in this file.

Indexing: rows and columns are indexed by `Fin (n + 1)`, i.e. `j, k ∈ {0, ..., n}` (0-based).
Since `M(j, k)` depends only on the difference `j - k`, 1-based indexing gives the same matrix.

The floor is taken of the rational number `(j - k - 2) / (n + 1)` with `Int.floor`, which is the
mathematical floor also for negative arguments (no truncation toward zero).
-/

namespace OMA.S_oeis_a000051

/-- The `(n+1) × (n+1)` integer matrix with entries `M(j, k) = -⌊(j - k - 2) / (n + 1)⌋`,
for `j, k ∈ {0, ..., n}`, the floor being the floor of a rational number. -/
def luschnyMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun j k => -⌊(((j : ℕ) : ℚ) - ((k : ℕ) : ℚ) - 2) / ((n : ℚ) + 1)⌋

/-- Conjecture (OEIS A000051, Peter Luschny): for every `n ≥ 0`, the permanent of
`luschnyMatrix n` equals `2^n + 1`. -/
theorem main : ∀ n : ℕ, (luschnyMatrix n).permanent = 2 ^ n + 1 := by
  sorry

end OMA.S_oeis_a000051
