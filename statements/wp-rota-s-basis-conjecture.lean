import Mathlib

/-!
# Rota's basis conjecture

Source: https://en.wikipedia.org/wiki/Rota%27s_basis_conjecture
Credit: @Bondyboy2001

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_rota_s_basis_conjecture

/-- Rota's basis conjecture for rank `n`: given `n` pairwise disjoint bases `B` of a matroid
of rank `n`, there exist `n` further pairwise disjoint bases `C`, each of which consists of
exactly one element from each of the bases `B i`.

This matches the source's matrix formulation: the `n * n` elements can be arranged into an
`n × n` matrix whose rows are the given bases and whose columns are also bases. Under the
rank hypothesis, every base has exactly `n` elements (`Matroid.IsBase.encard_eq_eRank`), so
"takes one element from each `B i`" already forces each `C i` to lie in the union of the
given bases and to be their partition together with the other columns. -/
def RotaBasisConjectureFor (n : ℕ) : Prop :=
  ∀ {α : Type} (M : Matroid α) (B : Fin n → Set α),
    (∀ i, M.IsBase (B i)) → (∀ i j : Fin n, i ≠ j → Disjoint (B i) (B j)) → M.eRank = n →
    ∃ C : Fin n → Set α, (∀ i, M.IsBase (C i)) ∧ (∀ i j : Fin n, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ i j, ∃! x, x ∈ C i ∧ x ∈ B j

/-- **Rota's basis conjecture** (published by Huang and Rota in 1994, credited to Rota in
1989): for every `n`, any `n` pairwise disjoint bases of a rank-`n` matroid can be
rearranged into `n` further pairwise disjoint bases, each consisting of exactly one element
from every one of the given bases. -/
theorem main : ∀ n : ℕ, RotaBasisConjectureFor n := by
  sorry

end OMA.S_wp_rota_s_basis_conjecture
