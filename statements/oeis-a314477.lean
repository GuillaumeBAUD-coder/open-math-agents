import Mathlib

/-!
# OEIS A314477: Wu's conjectures for the coordination sequence Gal.5.193.4

Source: https://oeis.org/A314477 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A314477 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.193.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 8, 14, 17, ...
Formula section:
Conjectures from Chai Wah Wu, May 14 2026: (Start)
a(n) = - 2*a(n-1) - 2*a(n-2) - a(n-3) + a(n-6) + 3*a(n-7) + 4*a(n-8) + 3*a(n-9) + a(n-10) - a(n-13)
- 2*a(n-14) - 2*a(n-15) - a(n-16) for n > 18.
G.f.: (-x^18 - 3*x^17 - 2*x^16 + 7*x^15 + 24*x^14 + 47*x^13 + 72*x^12 + 100*x^11 + 127*x^10 +
146*x^9 + 148*x^8 + 137*x^7 + 116*x^6 + 92*x^5 + 66*x^4 + 41*x^3 + 20*x^2 + 7*x + 1)/((x - 1)^2*(x +
1)^2*(x^2 - x + 1)*(x^2 + x + 1)^2*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 193 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 4j 4k2 5b2 2.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.6.3.6,
  3.4.4.6, 3.3.3.3.6. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, this is the only 5-uniform catalog file in
  which every entry Gal.5.193.w of this tiling occurs (5 entries), and the entry's 50 listed terms
  are those of the base vertex below (no other catalog file has them). The listed terms are proved
  as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 10) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a314477

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 10 × Fin 10 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 4, (-1), 0),
    (0, 4, 0, 0),
    (0, 7, 0, (-1)),
    (0, 8, (-1), (-1)),
    (1, 0, 1, 0),
    (1, 2, 0, 0),
    (1, 3, 0, 0),
    (1, 4, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 3, 1, 0),
    (2, 5, 0, 0),
    (3, 1, 0, 0),
    (3, 2, (-1), 0),
    (3, 2, 0, 0),
    (3, 6, 0, 0),
    (4, 0, 0, 0),
    (4, 0, 1, 0),
    (4, 1, 0, 0),
    (4, 7, 0, (-1)),
    (4, 8, 0, (-1)),
    (5, 2, 0, 0),
    (5, 6, 0, 0),
    (5, 6, 1, 0),
    (5, 9, 0, 0),
    (6, 3, 0, 0),
    (6, 5, (-1), 0),
    (6, 5, 0, 0),
    (6, 9, 0, 0),
    (7, 0, 0, 1),
    (7, 4, 0, 1),
    (7, 8, (-1), 0),
    (7, 8, 0, 0),
    (7, 9, 0, 0),
    (8, 0, 1, 1),
    (8, 4, 0, 1),
    (8, 7, 0, 0),
    (8, 7, 1, 0),
    (8, 9, 0, 0),
    (9, 5, 0, 0),
    (9, 6, 0, 0),
    (9, 7, 0, 0),
    (9, 8, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 10) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 10) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 10 := (0, 0, 4)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 10 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 18. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) ^ 2 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -X ^ 18 - 3 * X ^ 17 - 2 * X ^ 16 + 7 * X ^ 15 + 24 * X ^ 14 + 47 * X ^ 13 + 72 * X ^ 12 + 100 * X ^ 11 + 127 * X ^ 10 + 146 * X ^ 9 + 148 * X ^ 8 + 137 * X ^ 7 + 116 * X ^ 6 + 92 * X ^ 5 + 66 * X ^ 4 + 41 * X ^ 3 + 20 * X ^ 2 + 7 * X + 1 ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = -2 * a (n - 1) - 2 * a (n - 2) - a (n - 3) + a (n - 6) + 3 * a (n - 7) + 4 * a (n - 8) + 3 * a (n - 9) + a (n - 10) - a (n - 13) - 2 * a (n - 14) - 2 * a (n - 15) - a (n - 16) := by
  sorry

end OMA.S_oeis_a314477
