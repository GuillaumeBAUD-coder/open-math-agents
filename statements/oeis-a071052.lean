import Mathlib

/-!
# A071052: Number of 0's in n-th row of triangle in A071036 (cellular automaton Rule 150).

Source: https://oeis.org/A071052
Credit: @agchua

Formula line of A071052 (by Ralf Stephan, Mar 03 2004):
  a(2n) = a(n) + 2n (conjectured).
A071036 is the triangle read by rows giving successive states of the cellular automaton
Rule 150 started with a single ON cell; row n has length 2n+1. As in the Mathematica program of
A071036 (by Michael Somos), T(0,0) = 1 and T(n,k) = T(n-1,k-2) + T(n-1,k-1) + T(n-1,k) mod 2, with
T(n,k) = 0 outside 0 <= k <= 2n (Rule 150: each new cell is the sum mod 2 of the three cells above
it). Here T is defined on all integer k by the same rule; the cells outside 0 <= k <= 2n are then
0 by themselves. a(n) counts the k with 0 <= k <= 2n and T(n,k) = 0. The offset is 0, and the
claim is stated for every n >= 0.
-/

namespace OMA.S_oeis_a071052

/-- Cell k of row n of the Rule 150 triangle A071036, values mod 2. -/
def T : ℕ → ℤ → ZMod 2
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => T n (k - 2) + T n (k - 1) + T n k

/-- A071052(n): the number of 0's among T(n,k), 0 <= k <= 2n. -/
def a (n : ℕ) : ℕ := ((Finset.range (2 * n + 1)).filter (fun k : ℕ => T n (k : ℤ) = 0)).card

/-- Stephan's conjecture: a(2n) = a(n) + 2n for all n >= 0. -/
theorem main : ∀ n : ℕ, a (2 * n) = a n + 2 * n := by
  sorry

end OMA.S_oeis_a071052
