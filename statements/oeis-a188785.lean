import Mathlib

/-!
# A188785: Number of 2-step self-avoiding walks on an n X n X n X n 4-cube summed over all starting positions.

Source: https://oeis.org/A188785
Credit: @Salofe

Conjectures from Colin Barker, Apr 28 2018, quoted verbatim from the entry:
* "G.f.: 16*x^2*(4 + 7*x + x^2) / (1 - x)^5."
* "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5."

The entry also lists "Empirical: a(n) = 8*n^4 - 8*n^3." (row 2 of A188784); that closed form
is not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 0, 64, 432, 1536, 4000, 8640, 16464, ...). The value of
  `a 0` (the empty 4-cube) is never used.
* The n X n X n X n 4-cube is the set `Fin n × Fin n × Fin n × Fin n` of cells. Two cells are
  adjacent when three coordinates are equal and the fourth differs by 1
  (`|Δ1| + |Δ2| + |Δ3| + |Δ4| = 1`).
* In R. H. Hardin's convention a k-step walk visits k cells (row 1 of A188784 is k^4, one cell
  per walk). So a 2-step self-avoiding walk is a sequence of 2 distinct adjacent cells (one
  move). This reproduces the data, e.g. a(2) = 64 = 16 * 4, whereas walks making two moves
  number 192 on the 2 X 2 X 2 X 2 cube (that is row 3 of A188784).
* "Summed over all starting positions": every such sequence is counted, whatever its first cell,
  so a walk and its reverse count separately.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 5, as in the entry.
-/

namespace OMA.S_oeis_a188785

/-- Two cells of the `n × n × n × n` 4-cube are adjacent when they differ by 1 in one
coordinate and agree in the other three. -/
def Adj {n : ℕ} (p q : Fin n × Fin n × Fin n × Fin n) : Prop :=
  ((p.1 : ℤ) - q.1).natAbs + ((p.2.1 : ℤ) - q.2.1).natAbs + ((p.2.2.1 : ℤ) - q.2.2.1).natAbs +
    ((p.2.2.2 : ℤ) - q.2.2.2).natAbs = 1

/-- A 2-step self-avoiding walk: two distinct cells `w 0, w 1`, adjacent to each other. -/
def IsWalk {n : ℕ} (w : Fin 2 → Fin n × Fin n × Fin n × Fin n) : Prop :=
  Function.Injective w ∧ Adj (w 0) (w 1)

/-- A188785(n): the number of 2-step self-avoiding walks on the `n × n × n × n` 4-cube, summed
over all starting positions. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin 2 → Fin n × Fin n × Fin n × Fin n // IsWalk w}

open PowerSeries in
/-- Barker's conjectures: the generating function `16x^2(4 + 7x + x^2)/(1 - x)^5`, and the
recurrence `a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        16 * X ^ 2 * (4 + 7 * X + X ^ 2) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a188785
