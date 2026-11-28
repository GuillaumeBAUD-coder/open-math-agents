import Mathlib

namespace OMA.S_oeis_a392707

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
0-based partial alternating sums are strictly increasing (`0 < s₁ < s₂ < ...`). -/
noncomputable def a392707Count (n : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition n // (0 :: pas0 (p.parts.sort (· ≤ ·))).Pairwise (· < ·) }

/-- OEIS A053251 (`n ≥ 1`): number of partitions of `n` into odd parts such that
if an odd number occurs as a part then so do all smaller positive odd numbers. -/
noncomputable def a053251Count (n : ℕ) : ℕ :=
  Nat.card { r : Nat.Partition n //
    (∀ x ∈ r.parts, Odd x) ∧ (∀ x ∈ r.parts, ∀ y : ℕ, Odd y → y ≤ x → y ∈ r.parts) }

/-- OEIS A392707 (Gus Wiseman): For all `n ≥ 1`, reversed integer partitions of `n` with
strictly increasing 0-based partial alternating sums are counted by `A053251(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a392707Count n = a053251Count n := by sorry

end OMA.S_oeis_a392707
