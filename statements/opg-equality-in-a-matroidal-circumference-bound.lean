import Mathlib

/-!
# Equality in a matroidal circumference bound

Source: https://www.openproblemgarden.org/op/equality_in_a_matroidal_circumference_bound

For a 2-connected matroid `M` with at least two elements, `|E(M)| ≤ c(M) c(M*) / 2`, where
`c` is the circumference (largest circuit size). Question: is the binary affine cube
`AG(3,2)` the only 3-connected matroid attaining equality? We state the affirmative answer.

Conventions.
- Matroids are finite. `c(M)` is the supremum of circuit sizes (in `ℕ∞`); equality is
  `2 |E| = c(M) c(M*)`.
- 3-connected is Tutte's notion: no `k`-separation for `k ∈ {1, 2}`, where a `k`-separation
  is a partition `(X, E \ X)` with `|X|, |E \ X| ≥ k` and `r(X) + r(E \ X) < r(M) + k`.
- We assume `|E| ≥ 4`: the matroids on at most three elements are trivially 3-connected and
  some attain equality (e.g. `U_{2,3}`, with `c = 3`, `c* = 2`), so they are excluded as the
  degenerate cases the question ignores (it is reported true on up to 9 elements).
- `M ≅ AG(3,2)` means some bijection `E(M) → (ZMod 2)^3` takes the independent sets of `M`
  exactly to the affinely independent subsets of the affine space `(ZMod 2)^3`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_opg_equality_in_a_matroidal_circumference_bound

/-- The circumference: the supremum of the sizes of the circuits. -/
noncomputable def circumference {α : Type} (M : Matroid α) : ℕ∞ :=
  ⨆ C ∈ {C : Set α | M.IsCircuit C}, C.encard

/-- `M` has a `k`-separation (in Tutte's sense). -/
def HasSeparation {α : Type} (M : Matroid α) (k : ℕ) : Prop :=
  ∃ X ⊆ M.E, (k : ℕ∞) ≤ X.encard ∧ (k : ℕ∞) ≤ (M.E \ X).encard ∧
    M.eRk X + M.eRk (M.E \ X) < M.eRank + k

/-- Tutte 3-connectivity: no 1- or 2-separation. -/
def ThreeConnected {α : Type} (M : Matroid α) : Prop :=
  ¬ HasSeparation M 1 ∧ ¬ HasSeparation M 2

/-- `M` is isomorphic to the binary affine cube `AG(3,2)`. -/
def IsoAG32 {α : Type} (M : Matroid α) : Prop :=
  ∃ f : α → (Fin 3 → ZMod 2), Set.BijOn f M.E Set.univ ∧
    ∀ I ⊆ M.E, (M.Indep I ↔ AffineIndependent (ZMod 2) (fun x : I => f x))

theorem main :
    ∀ (α : Type) (M : Matroid α), M.Finite → 4 ≤ M.E.encard → ThreeConnected M →
      2 * M.E.encard = circumference M * circumference M✶ → IsoAG32 M := by
  sorry

end OMA.S_opg_equality_in_a_matroidal_circumference_bound
