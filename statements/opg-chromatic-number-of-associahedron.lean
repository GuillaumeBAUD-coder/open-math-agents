import Mathlib

/-!
# Chromatic number of associahedron

Source: https://www.openproblemgarden.org/op/chromatic_number_of_associahedron
Credit: @Moti1125

Conjecture (Fabila-Monroy, Flores-Peñaloza, Huemer, Hurtado, Urrutia, Wood): associahedra have
unbounded chromatic number.

The source describes the associahedron through flips: its vertices are the triangulations of a
convex polygon, and two triangulations are adjacent when one is obtained from the other by
removing a single diagonal and replacing it by a different diagonal. The chromatic number is that
of this graph (the 1-skeleton of the associahedron).

Conventions:
- The convex `n`-gon has vertices `0, 1, …, n - 1` in cyclic order. A diagonal is a pair `(i, j)`
  with `i < j` that is not a side: `j ≥ i + 2` and `(i, j) ≠ (0, n - 1)`.
- Two diagonals cross when their endpoints interleave strictly. Diagonals of a convex polygon
  cross in their interiors exactly in this case. Diagonals that share an endpoint do not cross.
- A triangulation is a maximal set of pairwise non-crossing diagonals.
- Two triangulations are adjacent in the flip graph when each contains exactly one diagonal that
  the other does not, which is the source's single flip.
- "Unbounded" means: for every `c` there is an `n` whose flip graph has chromatic number `> c`.
-/

namespace OMA.S_opg_chromatic_number_of_associahedron

/-- `(i, j)` is a diagonal of the convex `n`-gon with vertices `0, …, n - 1`. -/
def IsDiagonal (n : ℕ) (d : Fin n × Fin n) : Prop :=
  d.1.val + 2 ≤ d.2.val ∧ ¬ (d.1.val = 0 ∧ d.2.val = n - 1)

/-- The diagonals `d` and `e` cross: their endpoints interleave strictly. -/
def Crosses {n : ℕ} (d e : Fin n × Fin n) : Prop :=
  (d.1 < e.1 ∧ e.1 < d.2 ∧ d.2 < e.2) ∨ (e.1 < d.1 ∧ d.1 < e.2 ∧ e.2 < d.2)

/-- `T` is a triangulation of the convex `n`-gon: a maximal set of pairwise non-crossing
diagonals. -/
def IsTriangulation (n : ℕ) (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ T, IsDiagonal n d) ∧ (∀ d ∈ T, ∀ e ∈ T, ¬ Crosses d e) ∧
    ∀ d, IsDiagonal n d → d ∉ T → ∃ e ∈ T, Crosses d e

/-- The flip graph of the convex `n`-gon (the 1-skeleton of the associahedron): two
triangulations are adjacent when each has exactly one diagonal that the other lacks. -/
def flipGraph (n : ℕ) : SimpleGraph {T : Finset (Fin n × Fin n) // IsTriangulation n T} :=
  SimpleGraph.fromRel fun S T => (S.1 \ T.1).card = 1 ∧ (T.1 \ S.1).card = 1

theorem main : ∀ c : ℕ, ∃ n : ℕ, (c : ℕ∞) < (flipGraph n).chromaticNumber := by
  sorry

end OMA.S_opg_chromatic_number_of_associahedron
