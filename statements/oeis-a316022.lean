import Mathlib

/-!
# OEIS A316022: Wu's conjectures for the coordination sequence Gal.6.377.6

Source: https://oeis.org/A316022 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A316022 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.377.6 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 9, 15, 15, ...
Formula section:
Conjectures from Chai Wah Wu, Aug 01 2021: (Start)
a(n) = a(n-1) - a(n-2) + a(n-3) - a(n-4) + a(n-5) - a(n-6) + a(n-7) + a(n-8) - a(n-9) + a(n-10) -
a(n-11) + a(n-12) - a(n-13) + a(n-14) - a(n-15) for n > 22.
G.f.: (-6*x^22 + 6*x^21 - 6*x^20 + 6*x^18 - 12*x^17 + 12*x^16 - 5*x^15 + 17*x^14 - 8*x^13 + 29*x^12
- 8*x^11 + 29*x^10 + 7*x^9 + 20*x^8 + 14*x^7 + 13*x^6 + 17*x^5 + 4*x^4 + 11*x^3 + 4*x^2 + 5*x +
1)/((x - 1)^2*(x + 1)*(x^2 + 1)^2*(x^4 + 1)^2). (End)

Formalization notes:
* The tiling. The entry names tiling 377 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/5 (21111)/eu 4k2 4l 5b 5c 6d 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.4.6,
  3.4.6.4, 3.3.3.3.6, 3.3.3.4.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all
  1217 3- to 6-uniform tilings and computing 50 terms from every vertex class, this is the only
  6-uniform catalog file in which every entry Gal.6.377.w of this tiling occurs (6 entries), and the
  entry's 50 listed terms are those of the base vertex below (no other catalog file has them). The
  listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 50) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 10) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a316022

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 50 × Fin 50 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, (-1), 0),
    (0, 6, 0, 0),
    (0, 13, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, (-1), 0),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (2, 1, 1, 0),
    (2, 3, 0, 0),
    (2, 8, 0, 0),
    (2, 9, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 9, 0, 0),
    (3, 10, 0, 0),
    (3, 21, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 10, 0, 0),
    (4, 11, 0, 0),
    (4, 22, 0, 0),
    (5, 0, 1, 0),
    (5, 4, 0, 0),
    (5, 11, 0, 0),
    (5, 12, 0, (-1)),
    (6, 0, 0, 0),
    (6, 1, 0, 0),
    (6, 14, 0, 0),
    (6, 15, 0, (-1)),
    (7, 1, 0, 0),
    (7, 8, (-1), 0),
    (7, 14, 0, 0),
    (7, 16, 0, 0),
    (8, 2, 0, 0),
    (8, 7, 1, 0),
    (8, 19, 0, 0),
    (8, 20, 0, 0),
    (9, 2, 0, 0),
    (9, 3, 0, 0),
    (9, 20, 0, 0),
    (9, 21, 0, 0),
    (9, 36, 0, 0),
    (10, 3, 0, 0),
    (10, 4, 0, 0),
    (10, 21, 0, 0),
    (10, 22, 0, 0),
    (10, 37, 0, 0),
    (10, 38, 0, 0),
    (11, 4, 0, 0),
    (11, 5, 0, 0),
    (11, 22, 0, 0),
    (11, 23, 0, (-1)),
    (11, 39, 0, 0),
    (12, 5, 0, 1),
    (12, 13, 1, 0),
    (12, 23, 0, 0),
    (12, 25, 0, 0),
    (13, 0, 0, 1),
    (13, 12, (-1), 0),
    (13, 15, 0, 0),
    (13, 24, 0, 0),
    (14, 6, 0, 0),
    (14, 7, 0, 0),
    (14, 16, 0, 0),
    (14, 30, 0, 0),
    (15, 6, 0, 1),
    (15, 13, 0, 0),
    (15, 24, 0, 0),
    (15, 28, 0, 0),
    (16, 7, 0, 0),
    (16, 14, 0, 0),
    (16, 17, 0, 0),
    (16, 31, 0, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (17, 32, 0, 0),
    (17, 33, 0, 0),
    (18, 17, 0, 0),
    (18, 19, (-1), 0),
    (18, 26, 0, 0),
    (18, 33, 0, 0),
    (18, 34, (-1), 0),
    (19, 8, 0, 0),
    (19, 18, 1, 0),
    (19, 20, 0, 0),
    (19, 34, 0, 0),
    (19, 48, 0, 0),
    (20, 8, 0, 0),
    (20, 9, 0, 0),
    (20, 19, 0, 0),
    (20, 35, 0, 0),
    (20, 48, 0, 0),
    (21, 3, 0, 0),
    (21, 9, 0, 0),
    (21, 10, 0, 0),
    (21, 36, 0, 0),
    (21, 38, 0, 0),
    (22, 4, 0, 0),
    (22, 10, 0, 0),
    (22, 11, 0, 0),
    (22, 37, 0, 0),
    (22, 39, 0, 0),
    (23, 11, 0, 1),
    (23, 12, 0, 0),
    (23, 25, 0, 0),
    (23, 40, 0, 0),
    (23, 49, 0, 0),
    (24, 13, 0, 0),
    (24, 15, 0, 0),
    (24, 27, 0, 0),
    (24, 42, 0, 0),
    (25, 12, 0, 0),
    (25, 23, 0, 0),
    (25, 26, 1, 0),
    (25, 34, 0, 0),
    (25, 49, 0, 0),
    (26, 18, 0, 0),
    (26, 25, (-1), 0),
    (26, 27, 0, 0),
    (26, 33, 0, 0),
    (26, 34, (-1), 0),
    (27, 24, 0, 0),
    (27, 26, 0, 0),
    (27, 33, 0, 0),
    (27, 41, 0, 0),
    (28, 15, 0, 0),
    (28, 29, 0, 0),
    (28, 42, 0, 0),
    (28, 43, 0, 0),
    (29, 28, 0, 0),
    (29, 30, 0, 1),
    (29, 44, 0, 0),
    (29, 45, 0, 0),
    (30, 14, 0, 0),
    (30, 29, 0, (-1)),
    (30, 31, 0, 0),
    (30, 46, 0, 0),
    (31, 16, 0, 0),
    (31, 30, 0, 0),
    (31, 32, 0, 0),
    (31, 46, 0, 0),
    (32, 17, 0, 0),
    (32, 31, 0, 0),
    (32, 37, 0, 0),
    (32, 47, 0, 0),
    (33, 17, 0, 0),
    (33, 18, 0, 0),
    (33, 26, 0, 0),
    (33, 27, 0, 0),
    (33, 47, 0, 0),
    (34, 18, 1, 0),
    (34, 19, 0, 0),
    (34, 25, 0, 0),
    (34, 26, 1, 0),
    (34, 48, 0, 0),
    (34, 49, 0, 0),
    (35, 20, 0, 0),
    (35, 36, 0, 0),
    (35, 44, 0, 0),
    (35, 48, 0, 0),
    (36, 9, 0, 0),
    (36, 21, 0, 0),
    (36, 35, 0, 0),
    (36, 43, 0, 0),
    (37, 10, 0, 0),
    (37, 22, 0, 0),
    (37, 32, 0, 0),
    (37, 38, 0, 0),
    (37, 47, 0, 0),
    (38, 10, 0, 0),
    (38, 21, 0, 0),
    (38, 37, 0, 0),
    (38, 41, 0, 0),
    (38, 47, 0, 0),
    (39, 11, 0, 0),
    (39, 22, 0, 0),
    (39, 40, 0, (-1)),
    (39, 46, 0, 0),
    (40, 23, 0, 0),
    (40, 39, 0, 1),
    (40, 45, 0, 0),
    (40, 49, 0, 0),
    (41, 27, 0, 0),
    (41, 38, 0, 0),
    (41, 42, 0, 0),
    (41, 47, 0, 0),
    (42, 24, 0, 0),
    (42, 28, 0, 0),
    (42, 41, 0, 0),
    (42, 43, 0, 0),
    (43, 28, 0, 0),
    (43, 36, 0, 0),
    (43, 42, 0, 0),
    (43, 44, 0, 0),
    (44, 29, 0, 0),
    (44, 35, 0, 0),
    (44, 43, 0, 0),
    (44, 45, 0, 0),
    (45, 29, 0, 0),
    (45, 40, 0, 0),
    (45, 44, 0, 0),
    (45, 46, 0, 1),
    (46, 30, 0, 0),
    (46, 31, 0, 0),
    (46, 39, 0, 0),
    (46, 45, 0, (-1)),
    (47, 32, 0, 0),
    (47, 33, 0, 0),
    (47, 37, 0, 0),
    (47, 38, 0, 0),
    (47, 41, 0, 0),
    (48, 19, 0, 0),
    (48, 20, 0, 0),
    (48, 34, 0, 0),
    (48, 35, 0, 0),
    (48, 49, 0, 0),
    (49, 23, 0, 0),
    (49, 25, 0, 0),
    (49, 34, 0, 0),
    (49, 40, 0, 0),
    (49, 48, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 50) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 50) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 50 := (0, 0, 10)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 50 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 22. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X + 1) * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) ^ 2) =
      -6 * X ^ 22 + 6 * X ^ 21 - 6 * X ^ 20 + 6 * X ^ 18 - 12 * X ^ 17 + 12 * X ^ 16 - 5 * X ^ 15 + 17 * X ^ 14 - 8 * X ^ 13 + 29 * X ^ 12 - 8 * X ^ 11 + 29 * X ^ 10 + 7 * X ^ 9 + 20 * X ^ 8 + 14 * X ^ 7 + 13 * X ^ 6 + 17 * X ^ 5 + 4 * X ^ 4 + 11 * X ^ 3 + 4 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 22 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) - a (n - 6) + a (n - 7) + a (n - 8) - a (n - 9) + a (n - 10) - a (n - 11) + a (n - 12) - a (n - 13) + a (n - 14) - a (n - 15) := by
  sorry

end OMA.S_oeis_a316022
