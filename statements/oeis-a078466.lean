import Mathlib

/-!
# A078466: the "Collatz-Fibonacci" transform always falls into one of two cycles

Source: https://oeis.org/A078466 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A078466: first cycle is reached under a "Collatz-Fibonacci" transform; data
1, 3, 7, 8, 11, 13, 14, 18, 24, ...

The entry defines (comments):

  Let x(1)=1 x(2)=n; x(k)=x(k-1)+x(k-2) if x(k-1) and x(k-2) have opposite parities;
  x(k)=abs(x(k-1)-x(k-2))/2 otherwise.
  Sequence gives values of n such that (1;1;0) is reached.
  Conjecture : for any n x(k) reaches a cycle among 2 cycles : (1;1;0) and (1;2;3;5).

Reading of the source:
* `x n k` is the k-th term (k ≥ 1) of the transform started from `n`: `x n 1 = 1`, `x n 2 = n`,
  and each later term is the sum of the two previous terms when they have opposite parities
  (equivalently, when their sum is odd), and half their absolute difference otherwise (the
  difference is then even, so the half is exact). `x n 0` is not part of the source; it is set
  to 0 and never used.
* "for any n": every positive integer `n` (the data are positive).
* "reaches the cycle (1;1;0)": from some index `K` on the terms are 1, 1, 0, 1, 1, 0, ...;
  "reaches the cycle (1;2;3;5)": from some `K` on they are 1, 2, 3, 5, 1, 2, 3, 5, ...
  (Both are cycles of the rule: 1, 1 -> 0; 1, 0 -> 1; 0, 1 -> 1, and 1, 2 -> 3; 2, 3 -> 5;
  3, 5 -> 1; 5, 1 -> 2.)
-/

namespace OMA.S_oeis_a078466

/-- One step of the transform: the next term after `p, q`. -/
def step (p q : ℕ) : ℕ := if (p + q) % 2 = 1 then p + q else (max p q - min p q) / 2

/-- `x n k`: the terms x(1) = 1, x(2) = n, x(k) = step (x(k-2)) (x(k-1)); `x n 0 = 0` is unused. -/
def x (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => n
  | k + 3 => step (x n (k + 1)) (x n (k + 2))

/-- For every positive `n`, the transform eventually runs through the cycle (1, 1, 0) or the
cycle (1, 2, 3, 5). -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, 1 ≤ K ∧
    ((∀ j, x n (K + j) = [1, 1, 0].getD (j % 3) 0) ∨
      (∀ j, x n (K + j) = [1, 2, 3, 5].getD (j % 4) 0)) := by
  sorry

end OMA.S_oeis_a078466
