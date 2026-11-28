import Mathlib

/-!
# A299910: Coordination sequence of point of type 3.3.4.3.4 in 3-uniform tiling #3.54 in the Galebach listing.

Source: https://oeis.org/A299910
Tiling: 3-uniform tiling #3.54 of the Galebach listing (Gal.3.54; this vertex is Gal.3.54.2).

Conjectures stated here (OEIS A299910):
  Conjectures from Chai Wah Wu, Jul 10 2025:
  G.f.: (x^10 + 4*x^9 + 6*x^8 + 11*x^7 + 11*x^6 + 12*x^5 + 11*x^4 + 11*x^3 + 6*x^2 + 4*x + 1)/(x^10 - x^9 + x^8 - x^7 - x^3 + x^2 - x + 1). (End)
  a(n) = a(n-1) - a(n-2) + a(n-3) + a(n-7) - a(n-8) + a(n-9) - a(n-10) for n > 10.

The tiling is Galebach's 3-uniform tiling 54 of 61 (tiling #85, standard notation [3^6; 3^3.4^2; 3^2.4.3.4]),
from Brian Galebach, k-uniform tilings (k <= 6) and their A-numbers,
https://oeis.org/A250120/a250120.html. Galebach gives each vertex type as its cyclic sequence of
polygons together with, for every edge, the type of the neighbour and its rotation (a prime marks
a reflection):
  Gal.3.54.1: A: 4^2.3^3; B 90; A 180; B 210; A 120; A 240
  Gal.3.54.2: B: 4.3.4.3^2; B 300; A 270; A 150; B 60; C 300
  Gal.3.54.3: C: 3^6; B 240; B 300; B 0; B 60; B 120; B 180
All edges have length 1. Rebuilding the tiling from this notation (exact coordinates in Z[ζ12])
gives a periodic graph with translation lattice basis t1 = ((-2 - √3)/2, (3 + 2√3)/2) and t2 = ((-2 - √3)/2, (-3 - 2√3)/2).
The vertex (x, y, i) is the point x t1 + y t2 + p_i, where p_i and the vertex type are:
  i = 0: p_i = ((-3 - √3)/2, (-1 - √3)/2), type A
  i = 1: p_i = ((-2 - √3)/2, (-1 - 2√3)/2), type A
  i = 2: p_i = ((-1 - √3)/2, (-1 - √3)/2), type A
  i = 3: p_i = ((-1 - √3)/2, (3 + √3)/2), type A
  i = 4: p_i = (-1/2, (-√3)/2), type A
  i = 5: p_i = (0, 0), type A
  i = 6: p_i = (-1 - √3, 0), type B
  i = 7: p_i = (-1 - √3, 1), type B
  i = 8: p_i = ((-2 - √3)/2, -1/2), type B
  i = 9: p_i = ((-2 - √3)/2, 3/2), type B
  i = 10: p_i = (-1, 0), type B
  i = 11: p_i = (-1, 1), type B
  i = 12: p_i = ((-2 - √3)/2, 1/2), type C
From each vertex type this graph reproduces the 50 terms of the coordination sequence in Galebach's table.
`adj i` lists the neighbours of (0, 0, i) as triples (dx, dy, j). The edge set is invariant
under the translations, so (x, y, i) is adjacent exactly to the (x + dx, y + dy, j).
From the base vertex (0, 0, 6) this graph reproduces all 56 terms of the OEIS data of A299910.
-/

namespace OMA.S_oeis_a299910

/-- `(x, y, i)` is the vertex `i` of the fundamental cell, translated by `x t1 + y t2`. -/
abbrev Vertex := ℤ × ℤ × Fin 13

/-- The neighbours of `(0, 0, i)`, as `(dx, dy, j)`. -/
def adj : Fin 13 → List (ℤ × ℤ × Fin 13) := ![
  [(0, 0, 1), (0, 0, 2), (0, 0, 8), (0, 1, 3), (0, 1, 11)],
  [(-1, 0, 7), (0, 0, 0), (0, 0, 2), (0, 1, 5), (0, 1, 11)],
  [(-1, 0, 7), (0, 0, 0), (0, 0, 1), (0, 0, 4), (0, 0, 8)],
  [(0, -1, 0), (0, -1, 6), (0, 0, 9), (1, 0, 4), (1, 0, 5)],
  [(-1, 0, 3), (-1, 0, 9), (0, 0, 2), (0, 0, 5), (0, 0, 10)],
  [(-1, -1, 6), (-1, 0, 3), (0, -1, 1), (0, 0, 4), (0, 0, 10)],
  [(0, 0, 7), (0, 0, 8), (0, 0, 12), (0, 1, 3), (1, 1, 5)],
  [(0, 0, 6), (0, 0, 9), (0, 0, 12), (1, 0, 1), (1, 0, 2)],
  [(0, 0, 0), (0, 0, 2), (0, 0, 6), (0, 0, 10), (0, 0, 12)],
  [(0, 0, 3), (0, 0, 7), (0, 0, 11), (0, 0, 12), (1, 0, 4)],
  [(0, 0, 4), (0, 0, 5), (0, 0, 8), (0, 0, 11), (0, 0, 12)],
  [(0, -1, 0), (0, -1, 1), (0, 0, 9), (0, 0, 10), (0, 0, 12)],
  [(0, 0, 6), (0, 0, 7), (0, 0, 8), (0, 0, 9), (0, 0, 10), (0, 0, 11)]]

def neighbors (v : Vertex) : Finset Vertex :=
  ((adj v.2.2).map (fun d => (v.1 + d.1, v.2.1 + d.2.1, d.2.2))).toFinset

/-- The vertices at graph distance at most `n` from the base vertex `(0, 0, 6)`. -/
def ball : ℕ → Finset Vertex
  | 0 => {(0, 0, 6)}
  | n + 1 => ball n ∪ (ball n).biUnion neighbors

/-- The coordination sequence: the number of vertices at distance exactly `n`. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => ((ball (n + 1)).card : ℤ) - (ball n).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 10 < n → a n = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 7) - a (n - 8) + a (n - 9) - a (n - 10)) ∧
    mk a * (X^10 - X^9 + X^8 - X^7 - X^3 + X^2 - X + 1 : PowerSeries ℤ) = X^10 + 4*X^9 + 6*X^8 + 11*X^7 + 11*X^6 + 12*X^5 + 11*X^4 + 11*X^3 + 6*X^2 + 4*X + 1 := by
  sorry

end OMA.S_oeis_a299910
