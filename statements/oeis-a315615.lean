import Mathlib

/-!
# OEIS A315615: Wu's conjectures for the coordination sequence Gal.6.609.6

Source: https://oeis.org/A315615 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315615 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.609.6 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 12, 15, 18, ...
Formula section:
From Chai Wah Wu, Dec 20 2019: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 7*a(n-6) + 8*a(n-7) - 7*a(n-8) +
6*a(n-9) - 5*a(n-10) + 4*a(n-11) - 3*a(n-12) + 2*a(n-13) - a(n-14) for n > 14 (conjectured).
G.f.: (x^14 + 4*x^13 + 3*x^12 + 5*x^11 + 5*x^10 + 6*x^9 + 7*x^8 + 13*x^7 + 7*x^6 + 6*x^5 + 5*x^4 +
5*x^3 + 3*x^2 + 4*x + 1)/((x - 1)^2*(x^2 + 1)^2*(x^4 + 1)^2) (conjectured). (End)

Formalization notes:
* The tiling. The entry names tiling 609 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (321)/eu 4a 5c 5d 6d 6i 6j 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.4.12,
  3.3.3.4.4, 3.3.3.4.4, 3.3.3.3.3.3, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog
  files of all 1217 3- to 6-uniform tilings and computing 50 terms from every vertex class, this is
  the only 6-uniform catalog file in which every entry Gal.6.609.w of this tiling occurs (6
  entries), and the entry's 50 listed terms are those of the base vertex below (no other catalog
  file has them). The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 50) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 48) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the items of the entry's block, each marked (conjectured).
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315615

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 50 × Fin 50 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 11, (-1), (-1)),
    (0, 12, 0, 0),
    (0, 29, (-1), 0),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 12, 0, 0),
    (1, 13, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 14, 0, 0),
    (2, 15, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 15, 0, 0),
    (3, 16, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 17, 0, 0),
    (4, 18, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, (-1)),
    (5, 18, 0, 0),
    (5, 19, 0, 0),
    (6, 5, 0, 1),
    (6, 7, 0, 0),
    (6, 20, 0, 0),
    (6, 21, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 21, 0, 0),
    (7, 22, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 23, 0, 0),
    (8, 24, 0, 0),
    (9, 8, 0, 0),
    (9, 10, (-1), 0),
    (9, 24, 0, 0),
    (9, 25, (-1), 0),
    (10, 9, 1, 0),
    (10, 11, 0, 0),
    (10, 26, 0, 0),
    (10, 27, 0, 0),
    (11, 0, 1, 1),
    (11, 10, 0, 0),
    (11, 27, 0, 0),
    (11, 28, 0, 0),
    (12, 0, 0, 0),
    (12, 1, 0, 0),
    (12, 13, 0, 0),
    (12, 29, (-1), 0),
    (12, 36, 0, 0),
    (12, 37, (-1), 0),
    (13, 1, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 30, 0, 0),
    (13, 36, 0, 0),
    (14, 2, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 31, 0, 0),
    (14, 38, 0, 0),
    (15, 2, 0, 0),
    (15, 3, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (15, 38, 0, 0),
    (15, 39, 0, 0),
    (16, 3, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (16, 32, 0, 0),
    (16, 39, 0, 0),
    (17, 4, 0, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (17, 33, 0, 0),
    (17, 40, 0, 0),
    (18, 4, 0, 0),
    (18, 5, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 0),
    (18, 40, 0, 0),
    (18, 41, 0, 0),
    (19, 5, 0, 0),
    (19, 18, 0, 0),
    (19, 20, 0, (-1)),
    (19, 34, 0, 0),
    (19, 41, 0, 0),
    (20, 6, 0, 0),
    (20, 19, 0, 1),
    (20, 21, 0, 0),
    (20, 35, 0, 0),
    (20, 42, 0, 0),
    (21, 6, 0, 0),
    (21, 7, 0, 0),
    (21, 20, 0, 0),
    (21, 22, 0, 0),
    (21, 42, 0, 0),
    (21, 43, 0, 0),
    (22, 7, 0, 0),
    (22, 21, 0, 0),
    (22, 23, 0, 0),
    (22, 31, 0, 0),
    (22, 43, 0, 0),
    (23, 8, 0, 0),
    (23, 22, 0, 0),
    (23, 24, 0, 0),
    (23, 30, 0, 0),
    (23, 44, 0, 0),
    (24, 8, 0, 0),
    (24, 9, 0, 0),
    (24, 23, 0, 0),
    (24, 25, (-1), 0),
    (24, 44, 0, 0),
    (24, 45, (-1), 0),
    (25, 9, 1, 0),
    (25, 24, 1, 0),
    (25, 26, 0, 0),
    (25, 33, 0, 0),
    (25, 45, 0, 0),
    (26, 10, 0, 0),
    (26, 25, 0, 0),
    (26, 27, 0, 0),
    (26, 32, 0, 0),
    (26, 46, 0, 0),
    (27, 10, 0, 0),
    (27, 11, 0, 0),
    (27, 26, 0, 0),
    (27, 28, 0, 0),
    (27, 46, 0, 0),
    (27, 47, 0, 0),
    (28, 11, 0, 0),
    (28, 27, 0, 0),
    (28, 29, 0, 1),
    (28, 35, 0, 0),
    (28, 47, 0, 0),
    (29, 0, 1, 0),
    (29, 12, 1, 0),
    (29, 28, 0, (-1)),
    (29, 34, 0, 0),
    (29, 37, 0, 0),
    (30, 13, 0, 0),
    (30, 23, 0, 0),
    (30, 31, 0, 0),
    (30, 36, 0, 0),
    (30, 44, 0, 0),
    (31, 14, 0, 0),
    (31, 22, 0, 0),
    (31, 30, 0, 0),
    (31, 38, 0, 0),
    (31, 43, 0, 0),
    (32, 16, 0, 0),
    (32, 26, 0, 0),
    (32, 33, 0, 0),
    (32, 39, 0, 0),
    (32, 46, 0, 0),
    (33, 17, 0, 0),
    (33, 25, 0, 0),
    (33, 32, 0, 0),
    (33, 40, 0, 0),
    (33, 45, 0, 0),
    (34, 19, 0, 0),
    (34, 29, 0, 0),
    (34, 35, 0, (-1)),
    (34, 37, 0, 0),
    (34, 41, 0, 0),
    (35, 20, 0, 0),
    (35, 28, 0, 0),
    (35, 34, 0, 1),
    (35, 42, 0, 0),
    (35, 47, 0, 0),
    (36, 12, 0, 0),
    (36, 13, 0, 0),
    (36, 30, 0, 0),
    (36, 37, (-1), 0),
    (36, 44, 0, 0),
    (36, 48, (-1), 0),
    (37, 12, 1, 0),
    (37, 29, 0, 0),
    (37, 34, 0, 0),
    (37, 36, 1, 0),
    (37, 41, 0, 0),
    (37, 48, 0, 0),
    (38, 14, 0, 0),
    (38, 15, 0, 0),
    (38, 31, 0, 0),
    (38, 39, 0, 0),
    (38, 43, 0, 0),
    (38, 49, 0, 0),
    (39, 15, 0, 0),
    (39, 16, 0, 0),
    (39, 32, 0, 0),
    (39, 38, 0, 0),
    (39, 46, 0, 0),
    (39, 49, 0, 0),
    (40, 17, 0, 0),
    (40, 18, 0, 0),
    (40, 33, 0, 0),
    (40, 41, 0, 0),
    (40, 45, 0, 0),
    (40, 48, 0, 0),
    (41, 18, 0, 0),
    (41, 19, 0, 0),
    (41, 34, 0, 0),
    (41, 37, 0, 0),
    (41, 40, 0, 0),
    (41, 48, 0, 0),
    (42, 20, 0, 0),
    (42, 21, 0, 0),
    (42, 35, 0, 0),
    (42, 43, 0, 0),
    (42, 47, 0, 0),
    (42, 49, 0, 0),
    (43, 21, 0, 0),
    (43, 22, 0, 0),
    (43, 31, 0, 0),
    (43, 38, 0, 0),
    (43, 42, 0, 0),
    (43, 49, 0, 0),
    (44, 23, 0, 0),
    (44, 24, 0, 0),
    (44, 30, 0, 0),
    (44, 36, 0, 0),
    (44, 45, (-1), 0),
    (44, 48, (-1), 0),
    (45, 24, 1, 0),
    (45, 25, 0, 0),
    (45, 33, 0, 0),
    (45, 40, 0, 0),
    (45, 44, 1, 0),
    (45, 48, 0, 0),
    (46, 26, 0, 0),
    (46, 27, 0, 0),
    (46, 32, 0, 0),
    (46, 39, 0, 0),
    (46, 47, 0, 0),
    (46, 49, 0, 0),
    (47, 27, 0, 0),
    (47, 28, 0, 0),
    (47, 35, 0, 0),
    (47, 42, 0, 0),
    (47, 46, 0, 0),
    (47, 49, 0, 0),
    (48, 36, 1, 0),
    (48, 37, 0, 0),
    (48, 40, 0, 0),
    (48, 41, 0, 0),
    (48, 44, 1, 0),
    (48, 45, 0, 0),
    (49, 38, 0, 0),
    (49, 39, 0, 0),
    (49, 42, 0, 0),
    (49, 43, 0, 0),
    (49, 46, 0, 0),
    (49, 47, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 50) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 50) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 50 := (0, 0, 48)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 50 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) ^ 2) =
      X ^ 14 + 4 * X ^ 13 + 3 * X ^ 12 + 5 * X ^ 11 + 5 * X ^ 10 + 6 * X ^ 9 + 7 * X ^ 8 + 13 * X ^ 7 + 7 * X ^ 6 + 6 * X ^ 5 + 5 * X ^ 4 + 5 * X ^ 3 + 3 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 7 * a (n - 8) + 6 * a (n - 9) - 5 * a (n - 10) + 4 * a (n - 11) - 3 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a315615
