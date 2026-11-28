import Mathlib

/-!
# OEIS A223687: Barker's g.f. and closed form for n X 3 colorings by the Petersen graph (8,2)

Source: https://oeis.org/A223687 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223687 (R. H. Hardin, Mar 25 2013), offset 1: Petersen graph (8,2) coloring a rectangular
array: number of n X 3 0..15 arrays where 0..15 label nodes of a graph with edges 0,1 0,8 8,14 8,10
1,2 1,9 9,15 9,11 2,3 2,10 10,12 3,4 3,11 11,13 4,5 4,12 12,14 5,6 5,13 13,15 6,7 6,14 7,0 7,15 and
every array movement to a horizontal or antidiagonal neighbor moves along an edge of this graph.
Column 3 of A223692.
Formula section:
Empirical: a(n) = 24*a(n-1) - 127*a(n-2).
Conjectures from Colin Barker, Aug 22 2018: (Start)
G.f.: 144*x*(1 - 8*x) / (1 - 24*x + 127*x^2).
a(n) = (72*((12-sqrt(17))^n*(-31+8*sqrt(17)) + (12+sqrt(17))^n*(31+8*sqrt(17)))) / (127*sqrt(17)).
(End)

Formalization notes:
* The labels 0..15 are the nodes of the graph with the 24 edges listed in the entry, kept in the
  entry's order in `edges`; two labels are adjacent when they are joined by an edge, in either
  order.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)). The neighbor pairs that must move
  along an edge are the horizontal pairs (x(i,j), x(i,j+1)) and the antidiagonal pairs
  (x(i,j+1), x(i+1,j)); vertical and diagonal neighbors are not constrained. The entry has no
  condition on the first entry, so every labeling is counted.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x)
  (1 - 24x + 127x^2) = 144x(1 - 8x) in the formal power series ring over the rationals, with A(x) =
  Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for
  every n >= 1, with sqrt(17) as Real.sqrt 17.
* Controls proved in the proof file: the definition gives 144, 2304, 37008, 595584, 9594000,
  154616832, 2492365968, 40180445568, 647800215696, 10444288589568, 168392298756240,
  2714990519274624, 43773950520548496, 705771016545286656, 11379212680977220752 for n = 1..15, the
  entry's data; the graph has 24 edges, with the listed number of neighbors for each label.
-/

namespace OMA.S_oeis_a223687

open PowerSeries Finset

/-- The edges of the graph on the labels 0..15, as listed in the entry. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 8), (8, 14), (8, 10), (1, 2), (1, 9), (9, 15), (9, 11), (2, 3), (2, 10), (10, 12),
  (3, 4), (3, 11), (11, 13), (4, 5), (4, 12), (12, 14), (5, 6), (5, 13), (13, 15), (6, 7), (6, 14),
  (7, 0), (7, 15)]

/-- Two labels are adjacent when they are joined by an edge. -/
def adj (x y : Fin 16) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2)) are between adjacent labels. -/
def hrow (r : Fin 16 × Fin 16 × Fin 16) : Prop :=
  adj r.1 r.2.1 ∧ adj r.2.1 r.2.2

/-- The row `s` may lie directly below the row `r`: the antidiagonal pairs (x(i,j+1), x(i+1,j)) hold
adjacent labels. -/
def ok (r s : Fin 16 × Fin 16 × Fin 16) : Prop :=
  adj r.2.1 s.1 ∧ adj r.2.2 s.2.1

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223687: the number of n X 3 arrays of labels 0..15, given by their rows f
i = (x(i,0), x(i,1), x(i,2)), in which every movement to a horizontal or antidiagonal neighbor moves
along an edge of the graph. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 16 × Fin 16 × Fin 16)).filter
    (fun f => (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 24 * X + 127 * X ^ 2) = 144 * X * (1 - 8 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (72 * ((12 - Real.sqrt 17) ^ n * (-31 + 8 * Real.sqrt 17) +
        (12 + Real.sqrt 17) ^ n * (31 + 8 * Real.sqrt 17))) / (127 * Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a223687
