import Mathlib

/-!
# OEIS A311665: Wu's conjectures for the coordination sequence Gal.6.481.6

Source: https://oeis.org/A311665 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311665 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.481.6 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 14, ...
Formula section:
Conjectures from Chai Wah Wu, Nov 18 2025: (Start)
a(n) = a(n-2) - a(n-4) + a(n-6) + a(n-7) - a(n-8) - a(n-9) + a(n-10) + a(n-11) - a(n-13) + a(n-15) -
a(n-17) for n > 19.
G.f.: (-2*x^19 + 5*x^17 + 5*x^16 + 7*x^15 + 7*x^14 + 5*x^13 + 17*x^12 + 21*x^11 + 16*x^10 + 10*x^9 +
11*x^8 + 18*x^7 + 21*x^6 + 11*x^5 + 7*x^4 + 9*x^3 + 7*x^2 + 4*x + 1)/(x^17 - x^15 + x^13 - x^11 -
x^10 + x^9 + x^8 - x^7 - x^6 + x^4 - x^2 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 481 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/4 (3111)/eu 4a 4c 4l2 4m 5f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.4.12,
  3.4.3.12, 3.4.6.4, 3.4.6.4, 3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3-
  to 6-uniform tilings and computing 50 terms from every vertex class, this is the only 6-uniform
  catalog file in which every entry Gal.6.481.w of this tiling occurs (6 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 16) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311665

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 11, 0, 0),
    (0, 12, (-1), (-1)),
    (0, 26, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 12, (-1), 0),
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
    (4, 16, 0, 0),
    (4, 17, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 17, 0, 0),
    (5, 18, 0, 0),
    (6, 5, 0, 0),
    (6, 7, 0, 1),
    (6, 19, 0, 0),
    (6, 20, 0, 0),
    (7, 6, 0, (-1)),
    (7, 8, 0, 0),
    (7, 20, 0, (-1)),
    (7, 21, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 21, 0, 0),
    (8, 22, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 22, 0, 0),
    (9, 23, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 24, 0, 0),
    (10, 25, (-1), 0),
    (11, 0, 0, 0),
    (11, 10, 0, 0),
    (11, 25, (-1), 0),
    (11, 26, (-1), 0),
    (12, 0, 1, 1),
    (12, 1, 1, 0),
    (12, 13, 1, 0),
    (12, 20, 0, 0),
    (12, 27, 0, 1),
    (13, 1, 0, 0),
    (13, 12, (-1), 0),
    (13, 14, 0, 0),
    (13, 19, (-1), 0),
    (14, 2, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 23, 0, 0),
    (15, 2, 0, 0),
    (15, 3, 0, 0),
    (15, 14, 0, 0),
    (15, 22, 0, 0),
    (15, 28, 0, 0),
    (16, 3, 0, 0),
    (16, 4, 0, 0),
    (16, 28, 0, 0),
    (16, 29, 0, 0),
    (17, 4, 0, 0),
    (17, 5, 0, 0),
    (17, 18, 0, 0),
    (17, 25, 0, 0),
    (17, 29, 0, 0),
    (18, 5, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 0),
    (18, 24, 1, 0),
    (19, 6, 0, 0),
    (19, 13, 1, 0),
    (19, 18, 0, 0),
    (19, 20, 0, 0),
    (20, 6, 0, 0),
    (20, 7, 0, 1),
    (20, 12, 0, 0),
    (20, 19, 0, 0),
    (20, 27, 0, 1),
    (21, 7, 0, 0),
    (21, 8, 0, 0),
    (21, 27, 0, 0),
    (21, 28, 0, 0),
    (22, 8, 0, 0),
    (22, 9, 0, 0),
    (22, 15, 0, 0),
    (22, 23, 0, 0),
    (22, 28, 0, 0),
    (23, 9, 0, 0),
    (23, 14, 0, 0),
    (23, 22, 0, 0),
    (23, 24, 0, 0),
    (24, 10, 0, 0),
    (24, 18, (-1), 0),
    (24, 23, 0, 0),
    (24, 25, (-1), 0),
    (25, 10, 1, 0),
    (25, 11, 1, 0),
    (25, 17, 0, 0),
    (25, 24, 1, 0),
    (25, 29, 0, 0),
    (26, 0, 1, 0),
    (26, 11, 1, 0),
    (26, 27, 0, 0),
    (26, 29, 0, 0),
    (27, 12, 0, (-1)),
    (27, 20, 0, (-1)),
    (27, 21, 0, 0),
    (27, 26, 0, 0),
    (28, 15, 0, 0),
    (28, 16, 0, 0),
    (28, 21, 0, 0),
    (28, 22, 0, 0),
    (29, 16, 0, 0),
    (29, 17, 0, 0),
    (29, 25, 0, 0),
    (29, 26, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 16)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 19. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 17 - X ^ 15 + X ^ 13 - X ^ 11 - X ^ 10 + X ^ 9 + X ^ 8 - X ^ 7 - X ^ 6 + X ^ 4 - X ^ 2 + 1) =
      -2 * X ^ 19 + 5 * X ^ 17 + 5 * X ^ 16 + 7 * X ^ 15 + 7 * X ^ 14 + 5 * X ^ 13 + 17 * X ^ 12 + 21 * X ^ 11 + 16 * X ^ 10 + 10 * X ^ 9 + 11 * X ^ 8 + 18 * X ^ 7 + 21 * X ^ 6 + 11 * X ^ 5 + 7 * X ^ 4 + 9 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 19 < n → (a n : ℤ) = a (n - 2) - a (n - 4) + a (n - 6) + a (n - 7) - a (n - 8) - a (n - 9) + a (n - 10) + a (n - 11) - a (n - 13) + a (n - 15) - a (n - 17) := by
  sorry

end OMA.S_oeis_a311665
