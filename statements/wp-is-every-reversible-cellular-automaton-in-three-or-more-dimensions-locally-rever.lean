import Mathlib

namespace OMA.S_wp_is_every_reversible_cellular_automaton_in_three_or_more_dimensions_locally_rever

abbrev Position (d : ℕ) := Fin d → ℤ
abbrev Configuration (d q : ℕ) := Position d → Fin q

/-- The same finite-neighborhood rule is applied at every lattice site. -/
def IsCellularAutomaton {d q : ℕ} (F : Configuration d q → Configuration d q) : Prop :=
  ∃ (N : Finset (Position d)) (update : (↥N → Fin q) → Fin q),
    ∀ c i, F c i = update (fun j => c (i + j.val))

abbrev Cell {d : ℕ} (width : Fin d → ℕ) := ∀ j, Fin (width j)

def site {d : ℕ} (width : Fin d → ℕ) (origin block : Position d)
    (cell : Cell width) : Position d :=
  fun j => origin j + block j * (width j : ℤ) + (cell j).val

/-- Disjoint translated rectangles use one permutation of block contents. -/
def IsBlockPermutation {d q : ℕ} (F : Configuration d q → Configuration d q) : Prop :=
  ∃ (width : Fin d → ℕ) (origin : Position d)
    (perm : (Cell width → Fin q) ≃ (Cell width → Fin q)),
    (∀ j, 0 < width j) ∧
    ∀ c block cell,
      F c (site width origin block cell) = perm (fun i => c (site width origin block i)) cell

/-- The factors of a product alphabet can be translated independently. -/
def IsPartialShift {d q : ℕ} (F : Configuration d q → Configuration d q) : Prop :=
  ∃ (m : ℕ) (size : Fin m → ℕ) (e : Fin q ≃ (∀ j, Fin (size j)))
    (shift : Fin m → Position d),
    ∀ c i j, e (F c i) j = e (c (i + shift j)) j

theorem main :
    ∀ (d q : ℕ) (F : Configuration d q → Configuration d q),
      3 ≤ d → 0 < q → IsCellularAutomaton F → Function.Bijective F →
      ∃ operations : List (Configuration d q → Configuration d q),
        (∀ G ∈ operations, IsBlockPermutation G ∨ IsPartialShift G) ∧
        operations.foldr Function.comp id = F := by
  sorry

end OMA.S_wp_is_every_reversible_cellular_automaton_in_three_or_more_dimensions_locally_rever
