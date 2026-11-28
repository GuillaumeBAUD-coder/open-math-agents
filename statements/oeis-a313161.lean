import Mathlib

/-!
# OEIS A313161: Wu's conjectures for the coordination sequence Gal.5.237.1

Source: https://oeis.org/A313161 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313161 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.237.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 9, 15, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 12 2025: (Start)
a(n) = - 2*a(n-2) + a(n-3) - 2*a(n-4) + 3*a(n-5) - 2*a(n-6) + 4*a(n-7) - 2*a(n-8) + 4*a(n-9) -
2*a(n-10) + 3*a(n-11) - 2*a(n-12) + a(n-13) - 2*a(n-14) - a(n-16) for n > 23.
G.f.: (-x^23 - 2*x^21 - x^20 - 3*x^19 - x^18 - 3*x^17 + 3*x^16 + 4*x^15 + 18*x^14 + 25*x^13 +
43*x^12 + 53*x^11 + 65*x^10 + 72*x^9 + 70*x^8 + 70*x^7 + 58*x^6 + 49*x^5 + 33*x^4 + 22*x^3 + 11*x^2
+ 4*x + 1)/((x - 1)^2*(x^2 + 1)^2*(x^4 + 1)*(x^2 + x + 1)*(x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 237 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 4e2 5b2 6j 11.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.3.3.3.6, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, this is the only 5-uniform catalog file in
  which every entry Gal.5.237.w of this tiling occurs (5 entries), and the entry's 50 listed terms
  are those of the base vertex below (no other catalog file has them). The listed terms are proved
  as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 20) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 1) is a vertex of type 3.3.6.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313161

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 20 × Fin 20 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, (-1), 0),
    (0, 6, 0, 0),
    (0, 10, (-1), (-1)),
    (0, 11, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 4, 0, 0),
    (1, 6, 0, 0),
    (2, 1, 0, 0),
    (2, 3, (-1), 0),
    (2, 8, 0, 0),
    (2, 9, (-1), 0),
    (3, 2, 1, 0),
    (3, 4, 0, 0),
    (3, 7, 0, 0),
    (3, 9, 0, 0),
    (4, 1, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 6, 0, 0),
    (5, 0, 1, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 10, 0, (-1)),
    (5, 13, 0, (-1)),
    (6, 0, 0, 0),
    (6, 1, 0, 0),
    (6, 4, 0, 0),
    (6, 5, 0, 0),
    (6, 11, 0, (-1)),
    (6, 13, 0, (-1)),
    (7, 3, 0, 0),
    (7, 8, 0, 0),
    (7, 9, 0, 0),
    (7, 12, 0, 0),
    (7, 14, 0, 0),
    (8, 2, 0, 0),
    (8, 7, 0, 0),
    (8, 9, (-1), 0),
    (8, 12, 0, 0),
    (8, 15, 0, 0),
    (9, 2, 1, 0),
    (9, 3, 0, 0),
    (9, 7, 0, 0),
    (9, 8, 1, 0),
    (9, 14, 0, 0),
    (9, 15, 1, 0),
    (10, 0, 1, 1),
    (10, 5, 0, 1),
    (10, 11, 1, 0),
    (10, 13, 0, 0),
    (10, 16, 0, 0),
    (11, 0, 0, 1),
    (11, 6, 0, 1),
    (11, 10, (-1), 0),
    (11, 13, 0, 0),
    (11, 19, 0, 0),
    (12, 7, 0, 0),
    (12, 8, 0, 0),
    (12, 14, 0, 0),
    (12, 15, 0, 0),
    (12, 18, 0, 0),
    (13, 5, 0, 1),
    (13, 6, 0, 1),
    (13, 10, 0, 0),
    (13, 11, 0, 0),
    (13, 16, 0, 0),
    (13, 19, 0, 0),
    (14, 7, 0, 0),
    (14, 9, 0, 0),
    (14, 12, 0, 0),
    (14, 15, 1, 0),
    (14, 17, 0, 0),
    (15, 8, 0, 0),
    (15, 9, (-1), 0),
    (15, 12, 0, 0),
    (15, 14, (-1), 0),
    (15, 17, (-1), 0),
    (15, 18, 0, 0),
    (16, 10, 0, 0),
    (16, 13, 0, 0),
    (16, 17, 0, 0),
    (16, 19, 0, 0),
    (17, 14, 0, 0),
    (17, 15, 1, 0),
    (17, 16, 0, 0),
    (17, 18, 1, 0),
    (18, 12, 0, 0),
    (18, 15, 0, 0),
    (18, 17, (-1), 0),
    (18, 19, 0, 0),
    (19, 11, 0, 0),
    (19, 13, 0, 0),
    (19, 16, 0, 0),
    (19, 18, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 20) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 20) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 20 := (0, 0, 1)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 20 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 23. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) * (X ^ 2 + X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -X ^ 23 - 2 * X ^ 21 - X ^ 20 - 3 * X ^ 19 - X ^ 18 - 3 * X ^ 17 + 3 * X ^ 16 + 4 * X ^ 15 + 18 * X ^ 14 + 25 * X ^ 13 + 43 * X ^ 12 + 53 * X ^ 11 + 65 * X ^ 10 + 72 * X ^ 9 + 70 * X ^ 8 + 70 * X ^ 7 + 58 * X ^ 6 + 49 * X ^ 5 + 33 * X ^ 4 + 22 * X ^ 3 + 11 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 23 < n → (a n : ℤ) = -2 * a (n - 2) + a (n - 3) - 2 * a (n - 4) + 3 * a (n - 5) - 2 * a (n - 6) + 4 * a (n - 7) - 2 * a (n - 8) + 4 * a (n - 9) - 2 * a (n - 10) + 3 * a (n - 11) - 2 * a (n - 12) + a (n - 13) - 2 * a (n - 14) - a (n - 16) := by
  sorry

end OMA.S_oeis_a313161
