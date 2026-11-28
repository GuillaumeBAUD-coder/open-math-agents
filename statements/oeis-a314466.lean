import Mathlib

/-!
# OEIS A314466: Wu's conjectures for the coordination sequence Gal.5.205.2

Source: https://oeis.org/A314466 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A314466 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.205.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 8, 13, 22, ...
Formula section:
Conjectures from Chai Wah Wu, Nov 19 2025: (Start)
a(n) = - a(n-1) - a(n-2) + a(n-3) + a(n-4) + a(n-5) - a(n-6) + 2*a(n-9) - a(n-12) + a(n-13) +
a(n-14) + a(n-15) - a(n-16) - a(n-17) - a(n-18) for n > 20.
G.f.: (-x^20 - 2*x^19 + 7*x^17 + 17*x^16 + 28*x^15 + 37*x^14 + 40*x^13 + 44*x^12 + 49*x^11 + 54*x^10
+ 53*x^9 + 50*x^8 + 46*x^7 + 45*x^6 + 42*x^5 + 37*x^4 + 25*x^3 + 14*x^2 + 6*x + 1)/((x - 1)^2*(x^2 +
1)*(x^2 + x + 1)^2*(x^4 - x^2 + 1)*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 205 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 4k2 5a2 5d 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.4.6,
  3.3.3.3.6, 3.3.3.4.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, this is the only 5-uniform catalog file in
  which every entry Gal.5.205.w of this tiling occurs (5 entries), and the entry's 50 listed terms
  are those of the base vertex below (no other catalog file has them). The listed terms are proved
  as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 16) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.3.3.3.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a314466

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 16 × Fin 16 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 3, 0, 0),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (0, 9, 0, (-1)),
    (1, 0, 1, 0),
    (1, 2, 0, 0),
    (1, 6, 1, 0),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 6, 0, 0),
    (2, 8, 0, 0),
    (3, 0, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, (-1)),
    (3, 6, 0, 0),
    (3, 9, 0, (-1)),
    (4, 3, 0, 1),
    (4, 5, 0, 0),
    (4, 9, 0, 0),
    (4, 11, 0, 0),
    (5, 0, 1, 1),
    (5, 4, 0, 0),
    (5, 9, 1, 0),
    (5, 10, 0, 0),
    (6, 0, 0, 0),
    (6, 1, (-1), 0),
    (6, 2, 0, 0),
    (6, 3, 0, 0),
    (6, 12, 0, 0),
    (7, 1, 0, 0),
    (7, 8, 0, 0),
    (7, 12, 1, 0),
    (7, 13, 0, 0),
    (8, 2, 0, 0),
    (8, 7, 0, 0),
    (8, 12, 0, 0),
    (8, 13, 0, 0),
    (8, 15, 0, 0),
    (9, 0, 0, 1),
    (9, 3, 0, 1),
    (9, 4, 0, 0),
    (9, 5, (-1), 0),
    (9, 14, 0, 0),
    (10, 5, 0, 0),
    (10, 11, 0, 0),
    (10, 13, 0, 0),
    (10, 14, 1, 0),
    (11, 4, 0, 0),
    (11, 10, 0, 0),
    (11, 13, 0, 0),
    (11, 14, 0, 0),
    (11, 15, 0, 0),
    (12, 6, 0, 0),
    (12, 7, (-1), 0),
    (12, 8, 0, 0),
    (12, 15, 0, 0),
    (13, 7, 0, 0),
    (13, 8, 0, 0),
    (13, 10, 0, 0),
    (13, 11, 0, 0),
    (13, 15, 0, 0),
    (14, 9, 0, 0),
    (14, 10, (-1), 0),
    (14, 11, 0, 0),
    (14, 15, 0, 0),
    (15, 8, 0, 0),
    (15, 11, 0, 0),
    (15, 12, 0, 0),
    (15, 13, 0, 0),
    (15, 14, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 16) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 16) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 16 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 16 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 20. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 2 + X + 1) ^ 2 * (X ^ 4 - X ^ 2 + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -X ^ 20 - 2 * X ^ 19 + 7 * X ^ 17 + 17 * X ^ 16 + 28 * X ^ 15 + 37 * X ^ 14 + 40 * X ^ 13 + 44 * X ^ 12 + 49 * X ^ 11 + 54 * X ^ 10 + 53 * X ^ 9 + 50 * X ^ 8 + 46 * X ^ 7 + 45 * X ^ 6 + 42 * X ^ 5 + 37 * X ^ 4 + 25 * X ^ 3 + 14 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 20 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) + a (n - 3) + a (n - 4) + a (n - 5) - a (n - 6) + 2 * a (n - 9) - a (n - 12) + a (n - 13) + a (n - 14) + a (n - 15) - a (n - 16) - a (n - 17) - a (n - 18) := by
  sorry

end OMA.S_oeis_a314466
