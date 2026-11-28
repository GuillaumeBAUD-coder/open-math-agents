import Mathlib

namespace OMA.S_oeis_a392694

/-- Recursive helper for 0-based partial alternating sums of a finite sequence `q`:
`pas0Aux acc [q₁, q₂, ...] = [q₁ - acc, q₂ - (q₁ - acc), ...]`. -/
def pas0Aux (acc : ℤ) : List ℕ → List ℤ
  | [] => []
  | q :: qs =>
    let acc' := (q : ℤ) - acc
    acc' :: pas0Aux acc' qs

/-- 0-based partial alternating sums `pas(q, 0)_j = ∑_{i=1}^j (-1)^(i+j) * q_i`
for `j = 1, ..., q.length`. -/
def pas0 (q : List ℕ) : List ℤ :=
  pas0Aux 0 q

/-- Count of reversed integer partitions of `n` (sorted weakly increasing) whose
0-based partial alternating sums are weakly increasing. -/
noncomputable def a392694Count (n : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition n // (0 :: pas0 (p.parts.sort (· ≤ ·))).Pairwise (· ≤ ·) }

/-- OEIS A392694 (Gus Wiseman): Reversed integer partitions of `n` with weakly increasing
0-based partial alternating sums are counted by `A000009(n)` (partitions into distinct parts). -/
theorem main : ∀ n : ℕ, a392694Count n = (Nat.Partition.distincts n).card := by sorry

end OMA.S_oeis_a392694
