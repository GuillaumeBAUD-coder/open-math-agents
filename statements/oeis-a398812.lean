import Mathlib

/-!
# A398812: a(n) = n^2 - A138808(n).

Source: https://oeis.org/A398812
Credit: @bnb9001

A138808(n) is the number of integer pairs `(x, y)` with `x > 0`, `y > 0` such that `x ≤ p` and
`y ≤ q` for some factorization `n = p * q`. Such pairs lie in `[1, n] × [1, n]`, and the
factorizations are `p ∣ n`, `q = n / p`, so A138808(n) counts the points of `[1, n]²` covered by
some box `[1, p] × [1, n / p]` with `p ∣ n`. Then a(n) = n^2 - A138808(n) counts the uncovered
lattice points of the square (offset 1).

Conjecture: a(n)/n^2 -> 1, that is, A138808(n) = o(n^2). The entry notes that the conjecture is
true.
-/

namespace OMA.S_oeis_a398812

open Filter Topology

/-- A138808: points of `[1, n]²` covered by some box `[1, p] × [1, n / p]` with `p ∣ n`. -/
def B (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun xy => ∃ p ∈ n.divisors, xy.1 ≤ p ∧ xy.2 ≤ n / p)).card

/-- A398812: `n ^ 2 - A138808(n)`. -/
def a (n : ℕ) : ℕ := n ^ 2 - B n

/-- `a n / n ^ 2 → 1`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a398812
