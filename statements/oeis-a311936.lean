import Mathlib

/-!
# OEIS A311936: Wu's conjectures for the coordination sequence Gal.6.300.2

Source: https://oeis.org/A311936 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311936 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.300.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Sep 24 2020: (Start)
a(n) = 2*a(n-10) - a(n-20) for n > 23.
G.f.: (-x^23 - x^21 + 2*x^20 + 3*x^19 + 10*x^18 + 12*x^17 + 20*x^16 + 18*x^15 + 29*x^14 + 31*x^13 +
38*x^12 + 40*x^11 + 43*x^10 + 40*x^9 + 36*x^8 + 31*x^7 + 26*x^6 + 22*x^5 + 17*x^4 + 13*x^3 + 8*x^2 +
4*x + 1)/(x^20 - 2*x^10 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 300 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (321)/eu 4f 4g 4h 4k2 4u 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.6.3.6,
  3.6.3.6, 3.6.3.6, 3.4.4.6, 4.4.4.4. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 6-uniform
  catalog file in which every entry Gal.6.300.w of this tiling occurs (6 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 17) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.4.4.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311936

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 17 × Fin 17 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 4, (-1), 0),
    (0, 4, 0, 0),
    (0, 8, (-1), (-1)),
    (1, 0, 1, 0),
    (1, 2, 1, 0),
    (1, 3, 0, 0),
    (1, 4, 0, 0),
    (2, 1, (-1), 0),
    (2, 3, (-1), 0),
    (2, 3, 0, 0),
    (2, 5, 0, 0),
    (3, 1, 0, 0),
    (3, 2, 0, 0),
    (3, 2, 1, 0),
    (3, 6, 0, 0),
    (4, 0, 0, 0),
    (4, 0, 1, 0),
    (4, 1, 0, 0),
    (4, 7, 0, (-1)),
    (5, 2, 0, 0),
    (5, 6, (-1), 0),
    (5, 6, 0, 0),
    (5, 9, 0, 0),
    (6, 3, 0, 0),
    (6, 5, 0, 0),
    (6, 5, 1, 0),
    (6, 10, 0, 0),
    (7, 4, 0, 1),
    (7, 8, (-1), 0),
    (7, 8, 0, 0),
    (7, 11, 0, 0),
    (8, 0, 1, 1),
    (8, 7, 0, 0),
    (8, 7, 1, 0),
    (8, 12, 0, 0),
    (9, 5, 0, 0),
    (9, 10, (-1), 0),
    (9, 10, 0, 0),
    (9, 13, 0, 0),
    (10, 6, 0, 0),
    (10, 9, 0, 0),
    (10, 9, 1, 0),
    (10, 13, 0, 0),
    (11, 7, 0, 0),
    (11, 12, (-1), 0),
    (11, 12, 0, 0),
    (11, 14, 0, 0),
    (12, 8, 0, 0),
    (12, 11, 0, 0),
    (12, 11, 1, 0),
    (12, 14, 1, 0),
    (13, 9, 0, 0),
    (13, 10, 0, 0),
    (13, 15, 0, 0),
    (13, 16, 0, 0),
    (14, 11, 0, 0),
    (14, 12, (-1), 0),
    (14, 15, (-1), 0),
    (14, 16, 0, 0),
    (15, 13, 0, 0),
    (15, 14, 1, 0),
    (15, 16, 0, 0),
    (15, 16, 1, 0),
    (16, 13, 0, 0),
    (16, 14, 0, 0),
    (16, 15, (-1), 0),
    (16, 15, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 17) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 17) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 17 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 17 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 23. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 20 - 2 * X ^ 10 + 1) =
      -X ^ 23 - X ^ 21 + 2 * X ^ 20 + 3 * X ^ 19 + 10 * X ^ 18 + 12 * X ^ 17 + 20 * X ^ 16 + 18 * X ^ 15 + 29 * X ^ 14 + 31 * X ^ 13 + 38 * X ^ 12 + 40 * X ^ 11 + 43 * X ^ 10 + 40 * X ^ 9 + 36 * X ^ 8 + 31 * X ^ 7 + 26 * X ^ 6 + 22 * X ^ 5 + 17 * X ^ 4 + 13 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 23 < n → (a n : ℤ) = 2 * a (n - 10) - a (n - 20) := by
  sorry

end OMA.S_oeis_a311936
