import Mathlib

/-!
# OEIS A310025: Wu's conjectures for the coordination sequence Gal.4.31.2

Source: https://oeis.org/A310025 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310025 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.31.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 5, 8, 10, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 10 2018: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 7*a(n-6) + 8*a(n-7) - 7*a(n-8) +
6*a(n-9) - 5*a(n-10) + 4*a(n-11) - 3*a(n-12) + 2*a(n-13) - a(n-14) for n > 16.
G.f.: (-2*x^16 + 4*x^15 - 3*x^14 + 5*x^13 - 4*x^12 + 11*x^11 - 4*x^10 + 12*x^9 - 2*x^8 + 11*x^7 +
8*x^5 + 2*x^4 + 3*x^3 + 2*x^2 + x + 1)/((x - 1)^2*(x^2 + 1)^2*(x^4 + 1)^2). (End)

Formalization notes:
* The tiling. The entry names tiling 31 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 3a2 4a 4l 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.12.12,
  3.3.4.12, 3.4.6.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings
  and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file
  only, from the base vertex below; and this is the only 4-uniform file that holds the listed terms
  of every entry Gal.4.31.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 2) is a vertex of type 3.12.12; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a310025

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 11, (-1), 0),
    (0, 12, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 12, 0, (-1)),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 16, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 16, 0, 0),
    (3, 20, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 21, 0, 0),
    (4, 22, 0, 0),
    (5, 4, 0, 0),
    (5, 6, (-1), 0),
    (5, 22, 0, 0),
    (6, 5, 1, 0),
    (6, 7, 0, 0),
    (6, 13, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 13, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 19, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 19, 0, 0),
    (9, 26, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 24, 0, 0),
    (10, 27, 0, 0),
    (11, 0, 1, 0),
    (11, 10, 0, 0),
    (11, 24, 0, 0),
    (12, 0, 0, 1),
    (12, 1, 0, 1),
    (12, 17, 0, 0),
    (13, 6, 0, 0),
    (13, 7, 0, 0),
    (13, 14, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 1),
    (14, 25, 0, 1),
    (15, 14, 0, (-1)),
    (15, 16, 0, 0),
    (15, 25, 0, 0),
    (15, 28, 0, 0),
    (16, 2, 0, 0),
    (16, 3, 0, 0),
    (16, 15, 0, 0),
    (16, 20, 0, 0),
    (17, 12, 0, 0),
    (17, 18, 0, 0),
    (17, 23, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 0),
    (18, 23, 0, 0),
    (18, 29, 0, 0),
    (19, 8, 0, 0),
    (19, 9, 0, 0),
    (19, 18, 0, 0),
    (19, 26, 0, 0),
    (20, 3, 0, 0),
    (20, 16, 0, 0),
    (20, 21, 0, 0),
    (20, 28, 0, 0),
    (21, 4, 0, 0),
    (21, 20, 0, 0),
    (21, 22, 0, 0),
    (21, 29, 0, 0),
    (22, 4, 0, 0),
    (22, 5, 0, 0),
    (22, 21, 0, 0),
    (22, 23, 0, 0),
    (23, 17, 0, 0),
    (23, 18, 0, 0),
    (23, 22, 0, 0),
    (23, 29, 0, 0),
    (24, 10, 0, 0),
    (24, 11, 0, 0),
    (24, 25, 0, 0),
    (24, 27, 0, 0),
    (25, 14, 0, (-1)),
    (25, 15, 0, 0),
    (25, 24, 0, 0),
    (25, 28, 0, 0),
    (26, 9, 0, 0),
    (26, 19, 0, 0),
    (26, 27, 0, 0),
    (26, 29, 0, 0),
    (27, 10, 0, 0),
    (27, 24, 0, 0),
    (27, 26, 0, 0),
    (27, 28, 0, 0),
    (28, 15, 0, 0),
    (28, 20, 0, 0),
    (28, 25, 0, 0),
    (28, 27, 0, 0),
    (29, 18, 0, 0),
    (29, 21, 0, 0),
    (29, 23, 0, 0),
    (29, 26, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 2)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 16. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) ^ 2) =
      -2 * X ^ 16 + 4 * X ^ 15 - 3 * X ^ 14 + 5 * X ^ 13 - 4 * X ^ 12 + 11 * X ^ 11 - 4 * X ^ 10 + 12 * X ^ 9 - 2 * X ^ 8 + 11 * X ^ 7 + 8 * X ^ 5 + 2 * X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 7 * a (n - 8) + 6 * a (n - 9) - 5 * a (n - 10) + 4 * a (n - 11) - 3 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a310025
