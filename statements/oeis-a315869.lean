import Mathlib

/-!
# OEIS A315869: Wu's conjectures for the coordination sequence Gal.5.247.5

Source: https://oeis.org/A315869 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315869 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.247.5 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 8, 12, 20, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 20 2026: (Start)
a(n) = a(n-7) + a(n-8) - a(n-15) for n > 17.
G.f.: (-2*x^17 + x^15 + 8*x^14 + 6*x^13 + 16*x^12 + 16*x^11 + 30*x^10 + 24*x^9 + 33*x^8 + 31*x^7 +
26*x^6 + 24*x^5 + 20*x^4 + 12*x^3 + 8*x^2 + 6*x + 1)/(x^15 - x^8 - x^7 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 247 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/4 (2111)/eu 4e 4i 5a 5b 6f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.6.3.6, 3.3.3.3.6, 3.3.3.3.6, 3.3.3.3.3.3. Identification: unfolding the catalog files of all
  1217 3- to 6-uniform tilings and computing 50 terms from every vertex class, this is the only
  5-uniform catalog file in which every entry Gal.5.247.w of this tiling occurs (5 entries), and the
  entry's 50 listed terms are those of the base vertex below (no other catalog file has them). The
  listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 13) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 12) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315869

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 13 × Fin 13 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (0, 11, (-1), 0),
    (0, 12, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 6, 0, 1),
    (1, 8, 0, 1),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 7, 0, 0),
    (2, 9, 0, 0),
    (3, 2, 0, 0),
    (3, 4, (-1), 0),
    (3, 9, 0, 0),
    (3, 10, 0, 0),
    (4, 3, 1, 0),
    (4, 5, 0, 0),
    (4, 7, 0, 0),
    (4, 10, 1, 0),
    (5, 0, 1, 1),
    (5, 4, 0, 0),
    (5, 8, 0, 1),
    (5, 11, 0, 1),
    (6, 0, 0, 0),
    (6, 1, 0, (-1)),
    (6, 8, 0, 0),
    (6, 10, 0, 0),
    (6, 12, (-1), 0),
    (7, 2, 0, 0),
    (7, 4, 0, 0),
    (7, 9, 0, 0),
    (7, 10, 1, 0),
    (7, 12, 0, 0),
    (8, 1, 0, (-1)),
    (8, 5, 0, (-1)),
    (8, 6, 0, 0),
    (8, 11, 0, 0),
    (9, 2, 0, 0),
    (9, 3, 0, 0),
    (9, 7, 0, 0),
    (9, 11, 0, 0),
    (9, 12, 0, 0),
    (10, 3, 0, 0),
    (10, 4, (-1), 0),
    (10, 6, 0, 0),
    (10, 7, (-1), 0),
    (10, 12, (-1), 0),
    (11, 0, 1, 0),
    (11, 5, 0, (-1)),
    (11, 8, 0, 0),
    (11, 9, 0, 0),
    (11, 12, 0, 0),
    (12, 0, 1, 0),
    (12, 6, 1, 0),
    (12, 7, 0, 0),
    (12, 9, 0, 0),
    (12, 10, 1, 0),
    (12, 11, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 13) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 13) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 13 := (0, 0, 12)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 13 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 17. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 15 - X ^ 8 - X ^ 7 + 1) =
      -2 * X ^ 17 + X ^ 15 + 8 * X ^ 14 + 6 * X ^ 13 + 16 * X ^ 12 + 16 * X ^ 11 + 30 * X ^ 10 + 24 * X ^ 9 + 33 * X ^ 8 + 31 * X ^ 7 + 26 * X ^ 6 + 24 * X ^ 5 + 20 * X ^ 4 + 12 * X ^ 3 + 8 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 17 < n → (a n : ℤ) = a (n - 7) + a (n - 8) - a (n - 15) := by
  sorry

end OMA.S_oeis_a315869
