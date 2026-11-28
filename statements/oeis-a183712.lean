import Mathlib

/-!
# A183712: 1/20 of the number of (n+1) X 3 0..4 arrays with every 2 X 2 subblock strictly increasing clockwise or counterclockwise with one decrease.

Source: https://oeis.org/A183712

The conjecture formalized here (Charles R Greathouse IV, Sep 15 2014, formula section):
* a(n) ~ c*k^n where k = 1.629316... is the largest root of x^3 - 3x^2 - x + 1 and c = 1.6293... is
  conjecturally the largest root of 148x^3 - 296x^2 + 90x - 1.

Only the value of c is marked as conjectural; the statement below asserts the whole asymptotic claim
with k and c given by their defining properties (the largest real roots of the two cubics). The
decimal printed for k in the entry is the decimal of c: the largest root of x^3 - 3x^2 - x + 1 is
k = 3.2143..., which is the growth rate of the data (5, 17, 54, 174, 559, ...), and k = 1.629316...
is not a root of that cubic. The formalization follows the defining property of k, not the printed
decimal.

Conventions:
* An (n+1) X 3 array with entries 0..4 is a map x : Fin (n + 1) → Fin 3 → Fin 5 (row i, column j).
  Its 2 X 2 subblocks are formed by two adjacent rows i, i+1 and two adjacent columns j, j+1. For
  the subblock [[p, q], [r, s]] (p, q in the upper row), the clockwise order of its entries is
  p -> q -> s -> r -> p and the counterclockwise order is p -> r -> s -> q -> p. A cyclic order
  w -> x -> y -> z -> w is "strictly increasing with one decrease" when, of its four steps
  x - w, y - x, z - y, w - z (as integers), three are positive and one is negative. A subblock is
  admissible when its clockwise or its counterclockwise order has this property.
* N(n) is the number of (n+1) X 3 arrays all of whose 2 X 2 subblocks are admissible, and
  a(n) = N(n)/20, as a rational number (offset 1).
* a(n) ~ c*k^n is stated as: a(n) / k^n tends to c as n tends to infinity.

Numerical check: a transfer-matrix enumeration of the compatible pairs of rows gives a(1..9) = 5,
17, 54, 174, 559, 1797, 5776, 18566, 59677, the DATA of the entry.
-/

namespace OMA.S_oeis_a183712

open Filter Topology

/-- The cyclic order w -> x -> y -> z -> w has three positive steps and one negative step. -/
abbrev OneDecrease (w x y z : Fin 5) : Prop :=
  [(x : ℤ) - w, (y : ℤ) - x, (z : ℤ) - y, (w : ℤ) - z].countP (fun d => decide (0 < d)) = 3 ∧
    [(x : ℤ) - w, (y : ℤ) - x, (z : ℤ) - y, (w : ℤ) - z].countP (fun d => decide (d < 0)) = 1

/-- The subblock [[p, q], [r, s]] is strictly increasing clockwise or counterclockwise with one
decrease. -/
abbrev Admissible (p q r s : Fin 5) : Prop := OneDecrease p q s r ∨ OneDecrease p r s q

/-- Every 2 X 2 subblock formed by the rows u (upper) and v (lower) is admissible. -/
abbrev BlockOK (u v : Fin 3 → Fin 5) : Prop :=
  ∀ j : Fin 2, Admissible (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- N(n): the number of (n+1) X 3 0..4 arrays all of whose 2 X 2 subblocks are admissible. -/
def N (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin (n + 1) → Fin 3 → Fin 5 =>
    ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)).card

/-- A183712: a(n) = N(n)/20. -/
def a (n : ℕ) : ℚ := (N n : ℚ) / 20

/-- Greathouse's asymptotic: a(n) ~ c*k^n, with k the largest root of x^3 - 3x^2 - x + 1 and c the
largest root of 148x^3 - 296x^2 + 90x - 1. -/
theorem main :
    ∃ k c : ℝ, IsGreatest {x : ℝ | x ^ 3 - 3 * x ^ 2 - x + 1 = 0} k ∧
      IsGreatest {x : ℝ | 148 * x ^ 3 - 296 * x ^ 2 + 90 * x - 1 = 0} c ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / k ^ n) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a183712
