import Mathlib

/-!
# Erdős–Pósa property for long directed cycles

Source: https://www.openproblemgarden.org/op/erdos_posa_property_for_long_directed_cycles
Credit: @ishaanzee

**Conjecture** (F. Havet, A. K. Maia). Let `ℓ ≥ 2` be an integer. For every integer `n ≥ 0`, there
exists an integer `tₙ = tₙ(ℓ)` such that for every digraph `D`, either `D` has `n` pairwise-disjoint
directed cycles of length at least `ℓ`, or there exists a set `T` of at most `tₙ` vertices such that
`D - T` has no directed cycles of length at least `ℓ`.

(The case `ℓ = 2` was proved by Reed, Robertson, Seymour and Thomas.)

Formalization:
* A digraph on a finite set `V` is a loopless relation `D` (`D u v` is the arc `u → v`).
* A directed cycle is a list of at least two distinct vertices `v₀, …, v_{m-1}` with an arc from
  each `vᵢ` to `v_{i+1 mod m}` (`finRotate`); its length is `m`. Pairwise-disjoint cycles share no
  vertex.
* `D - T` has no directed cycle of length at least `ℓ` iff every such cycle of `D` meets `T`.
-/

namespace OMA.S_opg_erdos_posa_property_for_long_directed_cycles

/-- `l` is a directed cycle of `D`. -/
def IsDirCycle {V : Type*} (D : V → V → Prop) (l : List V) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧ ∀ i : Fin l.length, D (l.get i) (l.get (finRotate _ i))

/-- **Havet–Maia conjecture.** -/
theorem main : ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ n : ℕ, ∃ t : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (D : V → V → Prop), (∀ v, ¬ D v v) →
      (∃ C : Fin n → List V, (∀ i, IsDirCycle D (C i) ∧ ℓ ≤ (C i).length) ∧
        ∀ i j, i ≠ j → (C i).Disjoint (C j)) ∨
      (∃ T : Finset V, T.card ≤ t ∧
        ∀ l, IsDirCycle D l → ℓ ≤ l.length → ∃ v ∈ l, v ∈ T) := by
  sorry

end OMA.S_opg_erdos_posa_property_for_long_directed_cycles
