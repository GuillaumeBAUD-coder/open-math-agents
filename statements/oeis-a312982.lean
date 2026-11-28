import Mathlib

/-!
# OEIS A312982: Wu's conjectures for the coordination sequence Gal.5.232.2

Source: https://oeis.org/A312982 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A312982 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.232.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 9, 13, 20, ...
Formula section:
Conjectures from Chai Wah Wu, May 16 2026: (Start)
a(n) = a(n-1) + a(n-9) - a(n-10) for n > 17.
G.f.: (-2*x^17 + 2*x^16 - x^14 - x^13 + 3*x^12 - 3*x^11 + 3*x^10 + 4*x^9 + 6*x^8 + 4*x^7 + 6*x^6 +
3*x^5 + 7*x^4 + 4*x^3 + 5*x^2 + 3*x + 1)/(x^10 - x^9 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 232 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 4e2 5b 6d 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.3.3.3.6, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 5-uniform
  catalog file in which every entry Gal.5.232.w of this tiling occurs (5 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 22) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.3.6.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a312982

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 22 × Fin 22 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (0, 20, (-1), 0),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, (-1)),
    (2, 10, 0, 0),
    (2, 11, 0, (-1)),
    (3, 2, 0, 1),
    (3, 4, 0, 0),
    (3, 11, 0, 0),
    (3, 12, 0, 0),
    (4, 3, 0, 0),
    (4, 5, (-1), 0),
    (4, 15, (-1), 0),
    (4, 16, (-1), 0),
    (5, 0, 1, 1),
    (5, 4, 1, 0),
    (5, 16, 0, 0),
    (5, 17, 0, 0),
    (6, 0, 0, 0),
    (6, 1, 0, 0),
    (6, 7, 0, 0),
    (6, 13, 0, 0),
    (6, 14, 0, 0),
    (6, 20, (-1), 0),
    (7, 1, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 13, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 16, 0, 0),
    (8, 17, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 15, 0, 0),
    (9, 16, 0, 0),
    (9, 21, 0, 0),
    (10, 2, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, (-1)),
    (10, 19, 0, 0),
    (10, 21, 0, 0),
    (11, 2, 0, 1),
    (11, 3, 0, 0),
    (11, 10, 0, 1),
    (11, 12, 0, 0),
    (11, 18, 0, 0),
    (11, 19, 0, 1),
    (12, 3, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 0, 0),
    (12, 18, 0, 0),
    (13, 6, 0, 0),
    (13, 7, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (14, 6, 0, 0),
    (14, 13, 0, 0),
    (14, 15, (-1), 0),
    (14, 20, (-1), 0),
    (14, 21, (-1), 0),
    (15, 4, 1, 0),
    (15, 9, 0, 0),
    (15, 14, 1, 0),
    (15, 16, 0, 0),
    (15, 21, 0, 0),
    (16, 4, 1, 0),
    (16, 5, 0, 0),
    (16, 8, 0, 0),
    (16, 9, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (17, 5, 0, 0),
    (17, 8, 0, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (18, 11, 0, 0),
    (18, 12, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 1),
    (19, 10, 0, 0),
    (19, 11, 0, (-1)),
    (19, 18, 0, (-1)),
    (19, 20, 0, 0),
    (19, 21, 0, 0),
    (20, 0, 1, 0),
    (20, 6, 1, 0),
    (20, 14, 1, 0),
    (20, 19, 0, 0),
    (20, 21, 0, 0),
    (21, 9, 0, 0),
    (21, 10, 0, 0),
    (21, 14, 1, 0),
    (21, 15, 0, 0),
    (21, 19, 0, 0),
    (21, 20, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 22) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 22) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 22 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 22 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 17. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - X ^ 9 - X + 1) =
      -2 * X ^ 17 + 2 * X ^ 16 - X ^ 14 - X ^ 13 + 3 * X ^ 12 - 3 * X ^ 11 + 3 * X ^ 10 + 4 * X ^ 9 + 6 * X ^ 8 + 4 * X ^ 7 + 6 * X ^ 6 + 3 * X ^ 5 + 7 * X ^ 4 + 4 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 17 < n → (a n : ℤ) = a (n - 1) + a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a312982
