import Mathlib

/-!
# Cores of Cayley graphs

Source: https://www.openproblemgarden.org/op/cores_of_cayley_graphs
Credit: @joshuadc11

Problem (Šámal): let `M` be a finite abelian group. Is the core of every Cayley graph on a finite
power `M ^ k` isomorphic to a Cayley graph on some finite power `M ^ m`?

## Encoding

* `M` is a finite `AddCommGroup`, and a finite power of `M` is `Fin k → M` (with the pointwise
  `AddCommGroup` structure).
* For a symmetric subset `S : Set (Fin k → M)` not containing `0`, `cayleyGraph S` is the
  undirected Cayley graph on `Fin k → M`.
* A finite graph `H` is isomorphic to the core of `G` iff `H` is a core (every endomorphism
  `H →g H` is bijective) and `G` and `H` are homomorphically equivalent.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no
  (note that a comment on the source page observes a counterexample for `M = ZMod 15`).
-/

namespace OMA.S_opg_cores_of_cayley_graphs

/-- The undirected Cayley graph of an additive group `A` with respect to a subset `S`. -/
def cayleyGraph {A : Type} [AddCommGroup A] (S : Set A) : SimpleGraph A where
  Adj x y := x ≠ y ∧ (y - x ∈ S ∨ x - y ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- For every finite abelian group `M` and every Cayley graph on `M ^ k`, its core is isomorphic
to a Cayley graph on `M ^ m` for some `m`. -/
theorem main : ∀ (M : Type) [AddCommGroup M] [Fintype M] (k : ℕ) (S : Set (Fin k → M)),
    (0 : Fin k → M) ∉ S → (∀ s ∈ S, -s ∈ S) →
    ∃ (m : ℕ) (T : Set (Fin m → M)),
      (0 : Fin m → M) ∉ T ∧ (∀ t ∈ T, -t ∈ T) ∧
      (∀ f : cayleyGraph T →g cayleyGraph T, Function.Bijective f) ∧
      Nonempty (cayleyGraph S →g cayleyGraph T) ∧
      Nonempty (cayleyGraph T →g cayleyGraph S) := by
  sorry

end OMA.S_opg_cores_of_cayley_graphs
