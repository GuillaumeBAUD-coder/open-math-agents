import Mathlib

namespace OMA.S_oeis_a000009

/-- The OEIS A000009 entry. -/
def a (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)).powerset.filter fun s : Finset ℕ => ∑ i ∈ s, i = n).card)

/-- `m` is a term of the sequence A000009. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ j, a j = m

theorem main : ∀ n ≥ 1, ∃ S : Finset ℕ,
    (∀ x ∈ S, IsTerm x) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ x ∣ y) ∧
    ∑ x ∈ S, x = n := by
  sorry

end OMA.S_oeis_a000009
