import Mathlib

/-!
# A011373: number of 1's in the binary expansion of Fibonacci(n) (Eldar's limit)

Source: https://oeis.org/A011373 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A011373 (offset 0): number of 1's in the binary expansion of Fibonacci(n); data
0, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5, 4, ... (a(8) = 3 because Fibonacci(8) = 21 = 10101 in binary).

The entry records (Amiram Eldar, May 13 2022):

  Conjecture: Limit_{n->oo} a(n)/n = log_2(phi)/2 = A242208/2 = 0.3471209568... .

Reading of the source:
* Fibonacci numbers are Mathlib's `Nat.fib` (fib 0 = 0, fib 1 = 1, fib 8 = 21).
* The number of 1's in the binary expansion of `x` is the count of the digit 1 in
  `Nat.digits 2 x`.
* `phi` is the golden ratio `(1 + √5)/2` (`Real.goldenRatio`), and `log_2` is `Real.logb 2`.
* The limit is taken in `ℝ` as `n → ∞`.
-/

namespace OMA.S_oeis_a011373

open Filter Topology

/-- A011373(n): the number of 1's in the binary expansion of Fibonacci(n). -/
def a (n : ℕ) : ℕ := (Nat.digits 2 (Nat.fib n)).count 1

/-- Eldar's conjecture: `a(n)/n → log_2(φ)/2`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (Real.logb 2 Real.goldenRatio / 2)) := by
  sorry

end OMA.S_oeis_a011373
