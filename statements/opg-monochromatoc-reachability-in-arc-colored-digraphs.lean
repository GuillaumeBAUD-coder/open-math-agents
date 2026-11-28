import Mathlib

/-!
# Monochromatic reachability in arc-colored digraphs

Source: http://www.openproblemgarden.org/op/monochromatoc_reachability_in_arc_colored_digraphs
Credit: @shc261392

Conjecture (Sands, Sauer and Woodrow). For every `k`, there exists an integer `f(k)` such that if
`D` is a digraph whose arcs are colored with `k` colors, then `D` has a set `S` which is the
union of `f(k)` stable sets so that every vertex has a monochromatic path to some vertex in `S`.

Reading used here:
* `D` is a finite loopless digraph, given by an irreflexive arc relation on a finite type `V`;
  the arc colouring is `c : V → V → Fin k` (only its values on arcs matter).
* A stable set is a set of vertices with no arc between any two of them.
* A monochromatic path from `v` to `w` is a directed walk from `v` to `w` all of whose arcs have
  one colour; the empty walk is allowed, so vertices of `S` reach `S` trivially (a walk can
  always be shortened to a path).
-/

namespace OMA.S_opg_monochromatoc_reachability_in_arc_colored_digraphs

theorem main :
    ∀ k : ℕ, ∃ f : ℕ, ∀ (V : Type) [Fintype V] (D : V → V → Prop), (∀ v, ¬ D v v) →
      ∀ c : V → V → Fin k,
        ∃ I : Fin f → Set V, (∀ j, ∀ a ∈ I j, ∀ b ∈ I j, ¬ D a b) ∧
          ∀ v : V, ∃ w ∈ ⋃ j, I j, ∃ i : Fin k,
            Relation.ReflTransGen (fun a b => D a b ∧ c a b = i) v w := by
  sorry

end OMA.S_opg_monochromatoc_reachability_in_arc_colored_digraphs
