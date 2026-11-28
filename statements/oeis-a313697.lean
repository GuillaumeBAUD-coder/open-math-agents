import Mathlib

/-!
# OEIS A313697: Wu's conjectures for the coordination sequence Gal.5.202.4

Source: https://oeis.org/A313697 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313697 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.202.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 10, 15, 19, ...
Formula section:
Conjectures from Chai Wah Wu, Sep 02 2025: (Start)
a(n) = 2*a(n-5) - a(n-10) for n > 17.
G.f.: (-x^17 - 2*x^14 + x^13 + x^12 - x^11 + 3*x^10 + 7*x^9 + 10*x^8 + 16*x^7 + 20*x^6 + 22*x^5 +
19*x^4 + 15*x^3 + 10*x^2 + 5*x + 1)/(x^10 - 2*x^5 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 202 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/4 (2111)/eu 4k 5b2 5d 6i 2.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.4.6,
  3.3.3.3.6, 3.3.3.4.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 5-uniform
  catalog file in which every entry Gal.5.202.w of this tiling occurs (5 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 18) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 4) is a vertex of type 3.3.3.3.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313697

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 18 × Fin 18 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, 0, (-1)),
    (0, 6, (-1), 0),
    (0, 12, (-1), (-1)),
    (0, 14, (-1), 0),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 6, (-1), 0),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 8, 0, 0),
    (2, 9, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, (-1)),
    (3, 9, 0, 0),
    (3, 10, 0, (-1)),
    (3, 14, 0, 0),
    (4, 3, 0, 1),
    (4, 5, 0, 0),
    (4, 10, 0, 0),
    (4, 11, 0, 0),
    (4, 16, 0, 0),
    (5, 0, 0, 1),
    (5, 4, 0, 0),
    (5, 11, 0, 0),
    (5, 12, (-1), 0),
    (5, 15, (-1), 0),
    (6, 0, 1, 0),
    (6, 1, 1, 0),
    (6, 9, 0, 0),
    (6, 13, 1, 0),
    (6, 14, 0, 0),
    (7, 1, 0, 0),
    (7, 8, 0, 0),
    (7, 13, 0, 0),
    (7, 16, 0, 0),
    (8, 2, 0, 0),
    (8, 7, 0, 0),
    (8, 15, 0, 0),
    (8, 17, 0, 0),
    (9, 2, 0, 0),
    (9, 3, 0, 0),
    (9, 6, 0, 0),
    (9, 14, 0, 0),
    (9, 17, 0, 0),
    (10, 3, 0, 1),
    (10, 4, 0, 0),
    (10, 12, 0, 0),
    (10, 14, 0, 1),
    (10, 16, 0, 0),
    (11, 4, 0, 0),
    (11, 5, 0, 0),
    (11, 13, 0, 0),
    (11, 15, (-1), 0),
    (11, 16, 0, 0),
    (11, 17, (-1), 0),
    (12, 0, 1, 1),
    (12, 5, 1, 0),
    (12, 10, 0, 0),
    (12, 14, 0, 1),
    (12, 15, 0, 0),
    (13, 6, (-1), 0),
    (13, 7, 0, 0),
    (13, 11, 0, 0),
    (13, 16, 0, 0),
    (13, 17, (-1), 0),
    (14, 0, 1, 0),
    (14, 3, 0, 0),
    (14, 6, 0, 0),
    (14, 9, 0, 0),
    (14, 10, 0, (-1)),
    (14, 12, 0, (-1)),
    (15, 5, 1, 0),
    (15, 8, 0, 0),
    (15, 11, 1, 0),
    (15, 12, 0, 0),
    (15, 17, 0, 0),
    (16, 4, 0, 0),
    (16, 7, 0, 0),
    (16, 10, 0, 0),
    (16, 11, 0, 0),
    (16, 13, 0, 0),
    (17, 8, 0, 0),
    (17, 9, 0, 0),
    (17, 11, 1, 0),
    (17, 13, 1, 0),
    (17, 15, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 18) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 18) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 18 := (0, 0, 4)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 18 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 17. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -X ^ 17 - 2 * X ^ 14 + X ^ 13 + X ^ 12 - X ^ 11 + 3 * X ^ 10 + 7 * X ^ 9 + 10 * X ^ 8 + 16 * X ^ 7 + 20 * X ^ 6 + 22 * X ^ 5 + 19 * X ^ 4 + 15 * X ^ 3 + 10 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 17 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := by
  sorry

end OMA.S_oeis_a313697
