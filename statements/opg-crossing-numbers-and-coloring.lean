import Mathlib

/-!
# Crossing numbers and coloring (Albertson's conjecture)

Source: https://www.openproblemgarden.org/op/crossing_numbers_and_coloring
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Albertson): every graph `G` with `χ(G) ≥ t` satisfies `cr(G) ≥ cr(K_t)`.

Conventions:
* Graphs are finite simple graphs; `t` ranges over all natural numbers.
* A drawing places the vertices at distinct points of the plane and each edge as an arc (an
  injective path) between its endpoints whose interior avoids all vertices. Only drawings in which
  any two distinct edges meet in finitely many interior points are allowed, and `cr` minimises the
  number of (unordered pair of distinct edges, common interior point) incidences. This is the
  standard crossing number.
* `χ(G) ≥ t` is `(t : ℕ∞) ≤ G.chromaticNumber`; `K_t` is `⊤ : SimpleGraph (Fin t)`.
-/

namespace OMA.S_opg_crossing_numbers_and_coloring

open Set

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- A drawing of `G` in the plane, with an arc for each dart. -/
structure Drawing {V : Type} (G : SimpleGraph V) where
  pos : V → P
  pos_inj : Function.Injective pos
  arc : (d : G.Dart) → Path (pos d.fst) (pos d.snd)
  arc_inj : ∀ d, Function.Injective (arc d)
  arc_symm : ∀ d, arc d.symm = (arc d).symm
  arc_avoids : ∀ d (t : unitInterval), (t : ℝ) ∈ Ioo (0 : ℝ) 1 → arc d t ∉ range pos

variable {V : Type} {G : SimpleGraph V}

/-- The interior of the arc of an edge `e`. -/
def Drawing.inner (D : Drawing G) (e : Sym2 V) : Set P :=
  ⋃ (d : G.Dart) (_ : d.edge = e), (D.arc d) '' {t | (t : ℝ) ∈ Ioo (0 : ℝ) 1}

/-- Triples (edge, edge, point) of two distinct edges and a common interior point. -/
def Drawing.crossings (D : Drawing G) : Set (Sym2 V × Sym2 V × P) :=
  {p | p.1 ∈ G.edgeSet ∧ p.2.1 ∈ G.edgeSet ∧ p.1 ≠ p.2.1 ∧ p.2.2 ∈ D.inner p.1 ∩ D.inner p.2.1}

/-- Admissible drawings: every two distinct edges meet in finitely many interior points. -/
def Drawing.Good (D : Drawing G) : Prop := D.crossings.Finite

/-- The crossing number (each crossing is counted once for each order of its two edges,
hence the division by `2`). -/
noncomputable def cr (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2}

/-- Albertson's conjecture: `χ(G) ≥ t` implies `cr(G) ≥ cr(K_t)`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (t : ℕ),
    (t : ℕ∞) ≤ G.chromaticNumber → cr (⊤ : SimpleGraph (Fin t)) ≤ cr G := by
  sorry

end OMA.S_opg_crossing_numbers_and_coloring
