import Mathlib

/-!
# OEIS A311542: Wu's conjectures for the coordination sequence Gal.5.155.1

Source: https://oeis.org/A311542 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311542 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.155.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 12, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Sep 11 2025: (Start)
a(n) = - 3*a(n-2) + a(n-3) - 5*a(n-4) + 4*a(n-5) - 6*a(n-6) + 8*a(n-7) - 6*a(n-8) + 11*a(n-9) -
6*a(n-10) + 11*a(n-11) - 6*a(n-12) + 8*a(n-13) - 6*a(n-14) + 4*a(n-15) - 5*a(n-16) + a(n-17) -
3*a(n-18) - a(n-20) for n > 22.
G.f.: (-x^22 - x^21 - x^20 + 3*x^19 + 11*x^18 + 25*x^17 + 48*x^16 + 73*x^15 + 105*x^14 + 132*x^13 +
158*x^12 + 171*x^11 + 176*x^10 + 168*x^9 + 150*x^8 + 125*x^7 + 95*x^6 + 67*x^5 + 42*x^4 + 23*x^3 +
11*x^2 + 4*x + 1)/((x - 1)^2*(x^2 + 1)^2*(x^4 + 1)*(x^2 - x + 1)*(x^2 + x + 1)^2*(x^4 + x^3 + x^2 +
x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 155 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 4e2 4k2 5d 7.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.4.4.6, 3.3.3.4.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, this is the only 5-uniform catalog file in
  which every entry Gal.5.155.w of this tiling occurs (5 entries), and the entry's 50 listed terms
  are those of the base vertex below (no other catalog file has them). The listed terms are proved
  as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 10) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.4.4.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311542

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 10 × Fin 10 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, (-1), 0),
    (0, 6, 0, 0),
    (0, 7, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, (-1), 0),
    (1, 4, 0, 0),
    (1, 6, 0, 0),
    (2, 1, 1, 0),
    (2, 3, 0, 0),
    (2, 7, 1, 0),
    (2, 9, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 8, 0, 0),
    (3, 9, 0, 0),
    (4, 1, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 6, 0, 0),
    (5, 0, 1, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 9, 0, (-1)),
    (6, 0, 0, 0),
    (6, 1, 0, 0),
    (6, 4, 0, 0),
    (6, 5, 0, 0),
    (6, 8, 0, (-1)),
    (7, 0, 0, 1),
    (7, 2, (-1), 0),
    (7, 8, 0, 0),
    (7, 9, (-1), 0),
    (8, 3, 0, 0),
    (8, 6, 0, 1),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (9, 2, 0, 0),
    (9, 3, 0, 0),
    (9, 5, 0, 1),
    (9, 7, 1, 0),
    (9, 8, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 10) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 10) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 10 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 10 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 22. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -X ^ 22 - X ^ 21 - X ^ 20 + 3 * X ^ 19 + 11 * X ^ 18 + 25 * X ^ 17 + 48 * X ^ 16 + 73 * X ^ 15 + 105 * X ^ 14 + 132 * X ^ 13 + 158 * X ^ 12 + 171 * X ^ 11 + 176 * X ^ 10 + 168 * X ^ 9 + 150 * X ^ 8 + 125 * X ^ 7 + 95 * X ^ 6 + 67 * X ^ 5 + 42 * X ^ 4 + 23 * X ^ 3 + 11 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 22 < n → (a n : ℤ) = -3 * a (n - 2) + a (n - 3) - 5 * a (n - 4) + 4 * a (n - 5) - 6 * a (n - 6) + 8 * a (n - 7) - 6 * a (n - 8) + 11 * a (n - 9) - 6 * a (n - 10) + 11 * a (n - 11) - 6 * a (n - 12) + 8 * a (n - 13) - 6 * a (n - 14) + 4 * a (n - 15) - 5 * a (n - 16) + a (n - 17) - 3 * a (n - 18) - a (n - 20) := by
  sorry

end OMA.S_oeis_a311542
