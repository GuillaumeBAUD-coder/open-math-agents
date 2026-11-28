import Mathlib

/-!
# Cereceda's conjecture on the diameter of the space of colorings of degenerate graphs

Source: https://en.wikipedia.org/wiki/Cereceda's_conjecture
Credit: @datdzrgb
-/

namespace OMA.S_wp_cereceda_s_conjecture_on_the_diameter_of_the_space_of_colorings_of_degenerate_gr

def IsDegenerate {V : Type*} [Finite V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty → ∃ v : S, ((G.induce S).neighborSet v).ncard ≤ d

def recoloringGraph {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (G.Coloring (Fin k)) where
  Adj c c' := ∃! v, c v ≠ c' v
  symm := ⟨fun _ _ h => by simpa only [ne_comm] using h⟩
  loopless := ⟨fun _ => by simp⟩

/-- For each fixed degeneracy bound, the diameter of the space of proper colorings
with `d + 2` colors is at most quadratic in the number of vertices. -/
theorem main :
    ∀ d : ℕ, ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsDegenerate G d →
      ∀ c c' : G.Coloring (Fin (d + 2)),
        (recoloringGraph G (d + 2)).edist c c' ≤ (C * n ^ 2 : ℕ) := by
  sorry

end OMA.S_wp_cereceda_s_conjecture_on_the_diameter_of_the_space_of_colorings_of_degenerate_gr
