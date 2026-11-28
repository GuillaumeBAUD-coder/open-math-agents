import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq

namespace OMA.S_oeis_a007837

/-- A set partition of `Fin m` into nonempty, pairwise disjoint blocks of pairwise distinct sizes. -/
def IsDistinctBlockPartition (m : ℕ) (P : Finset (Finset (Fin m))) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
  (∀ B₁ ∈ P, ∀ B₂ ∈ P, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
  (P.biUnion id = Finset.univ) ∧
  (∀ B₁ ∈ P, ∀ B₂ ∈ P, B₁.card = B₂.card → B₁ = B₂)

/-- OEIS A007837: number of partitions of an `m`-element set with distinct block sizes. -/
noncomputable def a007837 (m : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter (IsDistinctBlockPartition m)).card

/-- OEIS A007837 conjecture (Gauss congruences): for every prime `p` and positive integers
`n` and `k`, `a(n * p^k) ≡ a(n * p^(k - 1)) (mod p^k)`. -/
theorem main :
    ∀ (p n k : ℕ), p.Prime → 1 ≤ n → 1 ≤ k →
      a007837 (n * p ^ k) ≡ a007837 (n * p ^ (k - 1)) [MOD p ^ k] := by
  sorry

end OMA.S_oeis_a007837
