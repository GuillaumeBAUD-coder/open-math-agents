import Mathlib

/-!
# OEIS A313264: Wu's conjectures for the coordination sequence Gal.5.216.5

Source: https://oeis.org/A313264 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313264 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.216.5 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 9, 15, 20, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 28 2021: (Start)
a(n) = a(n-1) - a(n-4) + a(n-5) + a(n-7) - 2*a(n-8) + a(n-9) + a(n-11) - a(n-12) + a(n-15) - a(n-16)
for n > 19.
G.f.: (-x^19 + x^17 + x^16 + 2*x^15 + 6*x^14 + 6*x^13 + 7*x^12 + 8*x^11 + 11*x^10 + 10*x^9 + 7*x^8 +
9*x^7 + 12*x^6 + 8*x^5 + 6*x^4 + 6*x^3 + 5*x^2 + 3*x + 1)/(x^16 - x^15 + x^12 - x^11 - x^9 + 2*x^8 -
x^7 - x^5 + x^4 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 216 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/2 (32)/eu 4l3 5e 5f 2.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4, 3.3.4.3.4,
  3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, this is the only 5-uniform catalog file in which every
  entry Gal.5.216.w of this tiling occurs (5 entries), and the entry's 50 listed terms are those of
  the base vertex below (no other catalog file has them). The listed terms are proved as controls in
  the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 36) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 1) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313264

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 36 × Fin 36 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), (-1)),
    (0, 7, 0, 0),
    (0, 17, 0, 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 6, 0, 1),
    (1, 8, 0, 0),
    (2, 1, 0, 0),
    (2, 3, (-1), 0),
    (2, 9, 0, 0),
    (2, 11, 0, 0),
    (3, 2, 1, 0),
    (3, 4, 0, 0),
    (3, 10, 0, 0),
    (3, 12, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 13, 0, 0),
    (4, 15, 0, 0),
    (5, 0, 1, 1),
    (5, 4, 0, 0),
    (5, 14, 0, 0),
    (5, 16, 0, 1),
    (6, 1, 0, (-1)),
    (6, 7, 0, 0),
    (6, 8, 0, (-1)),
    (6, 18, 0, 0),
    (6, 24, 0, 0),
    (7, 0, 0, 0),
    (7, 6, 0, 0),
    (7, 17, 0, 0),
    (7, 18, 0, 0),
    (7, 25, 0, 0),
    (8, 1, 0, 0),
    (8, 6, 0, 1),
    (8, 9, 0, 0),
    (8, 19, 0, 0),
    (8, 24, 0, 1),
    (9, 2, 0, 0),
    (9, 8, 0, 0),
    (9, 11, 0, 0),
    (9, 19, 0, 0),
    (9, 29, 0, 0),
    (10, 3, 0, 0),
    (10, 11, 1, 0),
    (10, 12, 0, 0),
    (10, 20, 0, 0),
    (10, 31, 0, 0),
    (11, 2, 0, 0),
    (11, 9, 0, 0),
    (11, 10, (-1), 0),
    (11, 20, (-1), 0),
    (11, 30, 0, 0),
    (12, 3, 0, 0),
    (12, 10, 0, 0),
    (12, 13, 0, 0),
    (12, 21, 0, 0),
    (12, 31, 0, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 15, 0, 0),
    (13, 21, 0, 0),
    (13, 33, 0, 0),
    (14, 5, 0, 0),
    (14, 15, 0, 0),
    (14, 16, 0, 1),
    (14, 22, 0, 0),
    (14, 35, 0, 1),
    (15, 4, 0, 0),
    (15, 13, 0, 0),
    (15, 14, 0, 0),
    (15, 22, 0, 0),
    (15, 34, 0, 0),
    (16, 5, 0, (-1)),
    (16, 14, 0, (-1)),
    (16, 17, 1, 0),
    (16, 23, 0, 0),
    (16, 35, 0, 0),
    (17, 0, 0, 0),
    (17, 7, 0, 0),
    (17, 16, (-1), 0),
    (17, 23, (-1), 0),
    (17, 26, 0, 0),
    (18, 6, 0, 0),
    (18, 7, 0, 0),
    (18, 21, 0, 0),
    (18, 25, 0, 0),
    (18, 27, 0, 0),
    (19, 8, 0, 0),
    (19, 9, 0, 0),
    (19, 22, 0, 0),
    (19, 28, 0, 0),
    (19, 29, 0, 0),
    (20, 10, 0, 0),
    (20, 11, 1, 0),
    (20, 23, 0, 0),
    (20, 30, 1, 0),
    (20, 32, 0, 0),
    (21, 12, 0, 0),
    (21, 13, 0, 0),
    (21, 18, 0, 0),
    (21, 27, 0, 0),
    (21, 33, 0, 0),
    (22, 14, 0, 0),
    (22, 15, 0, 0),
    (22, 19, 0, 0),
    (22, 28, 0, 0),
    (22, 34, 0, 0),
    (23, 16, 0, 0),
    (23, 17, 1, 0),
    (23, 20, 0, 0),
    (23, 26, 1, 0),
    (23, 32, 0, 0),
    (24, 6, 0, 0),
    (24, 8, 0, (-1)),
    (24, 27, 0, 0),
    (24, 28, 0, (-1)),
    (25, 7, 0, 0),
    (25, 18, 0, 0),
    (25, 26, 0, 0),
    (25, 33, 0, 0),
    (26, 17, 0, 0),
    (26, 23, (-1), 0),
    (26, 25, 0, 0),
    (26, 30, 0, 0),
    (27, 18, 0, 0),
    (27, 21, 0, 0),
    (27, 24, 0, 0),
    (27, 31, 0, 0),
    (28, 19, 0, 0),
    (28, 22, 0, 0),
    (28, 24, 0, 1),
    (28, 35, 0, 1),
    (29, 9, 0, 0),
    (29, 19, 0, 0),
    (29, 30, 0, 0),
    (29, 34, 0, 0),
    (30, 11, 0, 0),
    (30, 20, (-1), 0),
    (30, 26, 0, 0),
    (30, 29, 0, 0),
    (31, 10, 0, 0),
    (31, 12, 0, 0),
    (31, 27, 0, 0),
    (31, 32, 0, 0),
    (32, 20, 0, 0),
    (32, 23, 0, 0),
    (32, 31, 0, 0),
    (32, 35, 0, 0),
    (33, 13, 0, 0),
    (33, 21, 0, 0),
    (33, 25, 0, 0),
    (33, 34, 0, 0),
    (34, 15, 0, 0),
    (34, 22, 0, 0),
    (34, 29, 0, 0),
    (34, 33, 0, 0),
    (35, 14, 0, (-1)),
    (35, 16, 0, 0),
    (35, 28, 0, (-1)),
    (35, 32, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 36) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 36) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 36 := (0, 0, 1)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 36 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 19. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 15 + X ^ 12 - X ^ 11 - X ^ 9 + 2 * X ^ 8 - X ^ 7 - X ^ 5 + X ^ 4 - X + 1) =
      -X ^ 19 + X ^ 17 + X ^ 16 + 2 * X ^ 15 + 6 * X ^ 14 + 6 * X ^ 13 + 7 * X ^ 12 + 8 * X ^ 11 + 11 * X ^ 10 + 10 * X ^ 9 + 7 * X ^ 8 + 9 * X ^ 7 + 12 * X ^ 6 + 8 * X ^ 5 + 6 * X ^ 4 + 6 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 19 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 7) - 2 * a (n - 8) + a (n - 9) + a (n - 11) - a (n - 12) + a (n - 15) - a (n - 16) := by
  sorry

end OMA.S_oeis_a313264
