import Mathlib

/-!
# OEIS A315431: Wu's conjectures for the coordination sequence Gal.6.669.6

Source: https://oeis.org/A315431 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315431 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.669.6 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 11, 15, 22, ...
Formula section:
From Chai Wah Wu, Dec 20 2019: (Start)
a(n) = a(n-4) - a(n-5) + a(n-7) + a(n-9) - a(n-11) + a(n-12) - a(n-16) for n > 22 (conjectured).
G.f.: (-x^22 - x^17 + x^16 + 8*x^15 + 11*x^14 + 16*x^13 + 21*x^12 + 23*x^11 + 30*x^10 + 34*x^9 +
31*x^8 + 34*x^7 + 28*x^6 + 23*x^5 + 21*x^4 + 15*x^3 + 11*x^2 + 6*x + 1)/(x^16 - x^12 + x^11 - x^9 -
x^7 + x^5 - x^4 + 1) (conjectured). (End)

Formalization notes:
* The tiling. The entry names tiling 669 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/2 (42)/eu 5a 5b 6f 6h2 6j 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.3.6,
  3.3.3.3.6, 3.3.3.3.3.3, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of
  all 1217 3- to 6-uniform tilings and computing 50 terms from every vertex class, this is the only
  6-uniform catalog file in which every entry Gal.6.669.w of this tiling occurs (6 entries), and the
  entry's 50 listed terms are those of the base vertex below (no other catalog file has them). The
  listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 15) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 11) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the items of the entry's block, each marked (conjectured).
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315431

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 15 × Fin 15 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, 0, 0),
    (0, 6, (-1), (-1)),
    (0, 8, (-1), 0),
    (0, 12, (-1), (-1)),
    (1, 0, 0, 1),
    (1, 2, 0, 1),
    (1, 6, (-1), 0),
    (1, 7, 0, 0),
    (1, 11, 0, 0),
    (2, 1, 0, (-1)),
    (2, 3, 0, 0),
    (2, 7, 0, (-1)),
    (2, 8, 0, 0),
    (2, 12, 0, (-1)),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 8, 0, 0),
    (3, 9, 0, 0),
    (3, 13, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 9, 0, 0),
    (4, 10, 0, 0),
    (4, 14, 0, 0),
    (5, 0, 0, 0),
    (5, 4, 0, 0),
    (5, 8, (-1), 0),
    (5, 10, 0, 0),
    (5, 13, (-1), 0),
    (6, 0, 1, 1),
    (6, 1, 1, 0),
    (6, 9, 0, 0),
    (6, 11, 1, 0),
    (6, 12, 0, 0),
    (6, 14, 0, 0),
    (7, 1, 0, 0),
    (7, 2, 0, 1),
    (7, 10, 0, 0),
    (7, 11, 0, 0),
    (7, 12, 0, 0),
    (7, 14, 0, 0),
    (8, 0, 1, 0),
    (8, 2, 0, 0),
    (8, 3, 0, 0),
    (8, 5, 1, 0),
    (8, 12, 0, (-1)),
    (8, 13, 0, 0),
    (9, 3, 0, 0),
    (9, 4, 0, 0),
    (9, 6, 0, 0),
    (9, 11, 1, 0),
    (9, 13, 0, 0),
    (9, 14, 0, 0),
    (10, 4, 0, 0),
    (10, 5, 0, 0),
    (10, 7, 0, 0),
    (10, 11, 0, 0),
    (10, 13, (-1), 0),
    (10, 14, 0, 0),
    (11, 1, 0, 0),
    (11, 6, (-1), 0),
    (11, 7, 0, 0),
    (11, 9, (-1), 0),
    (11, 10, 0, 0),
    (11, 13, (-1), 0),
    (12, 0, 1, 1),
    (12, 2, 0, 1),
    (12, 6, 0, 0),
    (12, 7, 0, 0),
    (12, 8, 0, 1),
    (12, 14, 0, 0),
    (13, 3, 0, 0),
    (13, 5, 1, 0),
    (13, 8, 0, 0),
    (13, 9, 0, 0),
    (13, 10, 1, 0),
    (13, 11, 1, 0),
    (14, 4, 0, 0),
    (14, 6, 0, 0),
    (14, 7, 0, 0),
    (14, 9, 0, 0),
    (14, 10, 0, 0),
    (14, 12, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 15) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 15) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 15 := (0, 0, 11)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 15 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 22. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 12 + X ^ 11 - X ^ 9 - X ^ 7 + X ^ 5 - X ^ 4 + 1) =
      -X ^ 22 - X ^ 17 + X ^ 16 + 8 * X ^ 15 + 11 * X ^ 14 + 16 * X ^ 13 + 21 * X ^ 12 + 23 * X ^ 11 + 30 * X ^ 10 + 34 * X ^ 9 + 31 * X ^ 8 + 34 * X ^ 7 + 28 * X ^ 6 + 23 * X ^ 5 + 21 * X ^ 4 + 15 * X ^ 3 + 11 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 22 < n → (a n : ℤ) = a (n - 4) - a (n - 5) + a (n - 7) + a (n - 9) - a (n - 11) + a (n - 12) - a (n - 16) := by
  sorry

end OMA.S_oeis_a315431
