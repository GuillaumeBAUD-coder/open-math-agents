import Mathlib

/-!
# OEIS A313217: Wu's conjectures for the coordination sequence Gal.6.382.4

Source: https://oeis.org/A313217 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313217 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.382.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 9, 15, 19, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 06 2024: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 5*a(n-5) - 4*a(n-6) + 4*a(n-7) - 4*a(n-8) +
4*a(n-9) - 4*a(n-10) + 5*a(n-11) - 5*a(n-12) + 4*a(n-13) - 3*a(n-14) + 2*a(n-15) - a(n-16) for n >
19.
G.f.: (-x^19 + x^18 - x^17 + 2*x^16 + x^15 + 6*x^14 + 2*x^13 + 10*x^12 + 6*x^11 + 13*x^10 + 9*x^9 +
10*x^8 + 12*x^7 + 8*x^6 + 11*x^5 + 5*x^4 + 5*x^3 + 4*x^2 + 2*x + 1)/((x - 1)^2*(x^2 - x + 1)*(x^2 +
x + 1)*(x^4 - x^3 + x^2 - x + 1)*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 382 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (321)/eu 4k 4m2 5e2 5f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.4.6,
  3.4.6.4, 3.3.4.3.4, 3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 6-uniform
  catalog file in which every entry Gal.6.382.w of this tiling occurs (6 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 20) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 3) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313217

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 20 × Fin 20 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 5, 0, (-1)),
    (0, 6, (-1), 0),
    (0, 14, 0, 0),
    (1, 0, 1, 0),
    (1, 2, 0, (-1)),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (2, 1, 0, 1),
    (2, 3, 0, 0),
    (2, 8, 0, 0),
    (2, 9, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 1, 0),
    (3, 10, 0, 0),
    (3, 11, 0, 0),
    (4, 3, (-1), 0),
    (4, 5, 0, 0),
    (4, 12, 0, 0),
    (4, 13, 0, 0),
    (5, 0, 0, 1),
    (5, 4, 0, 0),
    (5, 8, 0, 0),
    (5, 9, 0, 0),
    (6, 0, 1, 0),
    (6, 1, 0, 0),
    (6, 15, 0, 0),
    (6, 16, 1, 0),
    (6, 17, 0, 0),
    (7, 1, 0, 0),
    (7, 8, 0, (-1)),
    (7, 14, 0, 0),
    (7, 15, 0, 0),
    (8, 2, 0, 0),
    (8, 5, 0, 0),
    (8, 7, 0, 1),
    (8, 9, 0, 0),
    (8, 14, 0, 1),
    (9, 2, 0, 0),
    (9, 5, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 13, 0, 0),
    (10, 3, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 13, 0, 0),
    (10, 18, 0, 0),
    (11, 3, 0, 0),
    (11, 10, 0, 0),
    (11, 12, 1, 0),
    (11, 17, 0, 0),
    (11, 18, 0, 0),
    (12, 4, 0, 0),
    (12, 11, (-1), 0),
    (12, 13, 0, 0),
    (12, 17, (-1), 0),
    (12, 19, 0, 0),
    (13, 4, 0, 0),
    (13, 9, 0, 0),
    (13, 10, 0, 0),
    (13, 12, 0, 0),
    (13, 19, 0, 0),
    (14, 0, 0, 0),
    (14, 7, 0, 0),
    (14, 8, 0, (-1)),
    (14, 16, 0, 0),
    (15, 6, 0, 0),
    (15, 7, 0, 0),
    (15, 17, 0, 0),
    (15, 18, 0, 0),
    (16, 6, (-1), 0),
    (16, 14, 0, 0),
    (16, 17, (-1), 0),
    (16, 19, 0, 0),
    (17, 6, 0, 0),
    (17, 11, 0, 0),
    (17, 12, 1, 0),
    (17, 15, 0, 0),
    (17, 16, 1, 0),
    (18, 10, 0, 0),
    (18, 11, 0, 0),
    (18, 15, 0, 0),
    (18, 19, 0, 0),
    (19, 12, 0, 0),
    (19, 13, 0, 0),
    (19, 16, 0, 0),
    (19, 18, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 20) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 20) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 20 := (0, 0, 3)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 20 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 19. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -X ^ 19 + X ^ 18 - X ^ 17 + 2 * X ^ 16 + X ^ 15 + 6 * X ^ 14 + 2 * X ^ 13 + 10 * X ^ 12 + 6 * X ^ 11 + 13 * X ^ 10 + 9 * X ^ 9 + 10 * X ^ 8 + 12 * X ^ 7 + 8 * X ^ 6 + 11 * X ^ 5 + 5 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 19 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 5 * a (n - 5) - 4 * a (n - 6) + 4 * a (n - 7) - 4 * a (n - 8) + 4 * a (n - 9) - 4 * a (n - 10) + 5 * a (n - 11) - 5 * a (n - 12) + 4 * a (n - 13) - 3 * a (n - 14) + 2 * a (n - 15) - a (n - 16) := by
  sorry

end OMA.S_oeis_a313217
