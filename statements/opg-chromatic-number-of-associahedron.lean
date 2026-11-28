import Mathlib

/-!
# Chromatic number of associahedron

Source: https://www.openproblemgarden.org/op/chromatic_number_of_associahedron
Credit: @shun157

Conjecture (Fabila-Monroy, Flores-Peñaloza, Huemer, Hurtado, Urrutia, Wood):
associahedra have unbounded chromatic number.

The vertices of the associahedron correspond to the triangulations of a convex polygon, and its
edges (the 1-skeleton) to edge flips, in which a single diagonal is removed from a triangulation
and replaced by a different diagonal. The conjecture is about the chromatic number of this
1-skeleton, as the number of vertices of the polygon grows.

Conventions used here:
* the convex polygon has vertices `0, 1, …, n - 1` (as `Fin n`) in cyclic order; only the cyclic
  order of the vertices matters for diagonals, crossings and triangulations of a convex polygon;
* a diagonal is stored as an ordered pair `(i, j)` with `i < j`, joining two non-adjacent
  vertices;
* two diagonals cross when their endpoints alternate around the polygon (diagonals sharing an
  endpoint do not cross);
* a triangulation is a maximal set of pairwise non-crossing diagonals. For a convex polygon these
  are exactly the triangulations (each has `n - 3` diagonals), so two triangulations differing by
  exactly one diagonal on each side are related by one flip.

Known bounds: the chromatic number is `O(log n)` (Addario-Berry, Reed, Scott, Wood, 2018), and the
best known lower bound is `4`, for `n = 10`.
-/

namespace OMA.S_opg_chromatic_number_of_associahedron

/-- `d` is a diagonal of the convex `n`-gon with vertices `0, …, n - 1` in cyclic order:
`d.1 < d.2`, and the two endpoints are not adjacent on the polygon. -/
def IsDiagonal (n : ℕ) (d : Fin n × Fin n) : Prop :=
  d.1.val + 1 < d.2.val ∧ ¬ (d.1.val = 0 ∧ d.2.val + 1 = n)

/-- Two diagonals `(a, b)` and `(c, d)` (with `a < b`, `c < d`) cross when their endpoints
alternate around the polygon: `a < c < b < d` or `c < a < d < b`. -/
def Crosses {n : ℕ} (d e : Fin n × Fin n) : Prop :=
  (d.1 < e.1 ∧ e.1 < d.2 ∧ d.2 < e.2) ∨ (e.1 < d.1 ∧ d.1 < e.2 ∧ e.2 < d.2)

/-- A triangulation of the convex `n`-gon: a set of pairwise non-crossing diagonals to which no
further diagonal can be added without a crossing. -/
def IsTriangulation (n : ℕ) (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ T, IsDiagonal n d) ∧
  (∀ d ∈ T, ∀ e ∈ T, ¬ Crosses d e) ∧
  (∀ d : Fin n × Fin n, IsDiagonal n d → d ∉ T → ∃ e ∈ T, Crosses d e)

/-- The triangulations of the convex `n`-gon: the vertices of the associahedron. -/
abbrev Triangulation (n : ℕ) := {T : Finset (Fin n × Fin n) // IsTriangulation n T}

/-- The 1-skeleton of the associahedron (the flip graph): two triangulations are adjacent when
one is obtained from the other by removing a single diagonal and inserting a different one.
(`SimpleGraph.fromRel` adds `T ≠ T'` and symmetrizes; both are already implied by this relation.) -/
def flipGraph (n : ℕ) : SimpleGraph (Triangulation n) :=
  SimpleGraph.fromRel fun T T' => (T.1 \ T'.1).card = 1 ∧ (T'.1 \ T.1).card = 1

/-- **Conjecture.** Associahedra have unbounded chromatic number: for every `k` there is a convex
polygon whose flip graph is not `k`-colorable. -/
theorem main : ∀ k : ℕ, ∃ n : ℕ, ¬ (flipGraph n).Colorable k := by
  sorry

end OMA.S_opg_chromatic_number_of_associahedron
