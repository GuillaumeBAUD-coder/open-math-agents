import Mathlib

/-!
# Tripod packing

Determine the maximum number of pairwise disjoint tripods whose apex cells
lie in an `n × n × n` grid cube. A tripod occupies the cells on all three
positive coordinate rays from its apex, including the apex itself. Two
tripods intersect when they occupy the same grid cell.

The apex uses coordinates from `0` through `n - 1`. The rays extend through
the unbounded grid.

Source: https://en.wikipedia.org/wiki/Tripod_packing
Reference: https://doi.org/10.37236/7224
Credit: @konradsiebor
-/

namespace OMA.S_wp_tripod_packing

def tripodCells {n : ℕ} (apex : Fin 3 → Fin n) : Set (Fin 3 → ℕ) :=
  {cell | ∃ axis : Fin 3, (apex axis).val ≤ cell axis ∧
      ∀ other : Fin 3, other ≠ axis → cell other = (apex other).val}

def IsPackingSize (n size : ℕ) : Prop :=
  ∃ apices : Finset (Fin 3 → Fin n),
    apices.card = size ∧
    (apices : Set (Fin 3 → Fin n)).Pairwise
      (fun apex₁ apex₂ => Disjoint (tripodCells apex₁) (tripodCells apex₂))

theorem main :
    ∃ maximum : ℕ → ℕ, ∀ n : ℕ, 0 < n →
      IsGreatest {size : ℕ | IsPackingSize n size} (maximum n) := by
  sorry

end OMA.S_wp_tripod_packing
