import Mathlib

/-!
# Hamiltonicity of Cayley graphs

Source: https://www.openproblemgarden.org/op/hamiltonicity_of_cayley_graphs
Credit: @joshuadc11

Rapaport-Strasser / Lovász question: is every finite connected Cayley graph on at least three
vertices Hamiltonian?

## Encoding

* `G` is a finite group with `3 ≤ Fintype.card G` (graphs on 1 or 2 vertices have no simple cycle
  and hence cannot be Hamiltonian).
* `S : Set G` is a symmetric generating set (`Subgroup.closure S = ⊤`, `∀ s ∈ S, s⁻¹ ∈ S`,
  `1 ∉ S`), and `cayleyGraph S` is the undirected `SimpleGraph G` with `g` adjacent to `h` iff
  `g⁻¹ * h ∈ S`.
* Hamiltonian is Mathlib's `∃ (v : G) (p : (cayleyGraph S).Walk v v), p.IsHamiltonianCycle`.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer yes,
  and a disproof would answer no.
-/

namespace OMA.S_opg_hamiltonicity_of_cayley_graphs

/-- The undirected Cayley graph of a group `G` with respect to a symmetric subset `S` not
containing `1`. -/
def cayleyGraph {G : Type} [Group G] (S : Set G) : SimpleGraph G where
  Adj g h := g ≠ h ∧ (g⁻¹ * h ∈ S ∨ h⁻¹ * g ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every finite connected Cayley graph on at least 3 vertices has a Hamiltonian cycle. -/
theorem main : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (S : Set G),
    3 ≤ Fintype.card G →
    (1 : G) ∉ S →
    (∀ s ∈ S, s⁻¹ ∈ S) →
    Subgroup.closure S = ⊤ →
    ∃ (v : G) (p : (cayleyGraph S).Walk v v), p.IsHamiltonianCycle := by
  sorry

end OMA.S_opg_hamiltonicity_of_cayley_graphs
