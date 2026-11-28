import Mathlib.Init

/-!
# OEIS A305499 — antidiagonal sums of Schulte's array

Source: https://oeis.org/A305499
Reference sequence: https://oeis.org/A211538

The conjecture uses the published one-based A211538 values. We define these
independently using Wesley Ivan Hurt's arithmetic-sum formula. With the literal
ordered-triple count C(N) in A211538's description, the corresponding index is
n + 2. The first antidiagonal has sum 1, whereas C(4) = 3. This choice preserves
the n + 3 in Schulte's conjecture.
-/
namespace OMA.S_oeis_a305499

/-- The argument `r` counts row updates starting from the first row. -/
def arrayAfter : Nat → Nat → Nat
  | 0, k => k
  | r + 1, k =>
    if r + 1 < k then arrayAfter r k - ((r + 1 + k) % 2) else arrayAfter r k

/-- The OEIS array with its published one-based indices. -/
def array (r k : Nat) : Nat := arrayAfter (r - 1) k

/-- Sum of `f j` for `0 ≤ j < n`. -/
def sumFirst (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumFirst f n + f n

def diagonal (n : Nat) : Nat := sumFirst (fun j => array (n - j) (j+1)) n

/-- Hurt's A211538 arithmetic-sum formula: sum j from ceil((N-3)/2) to N-3.
The displayed data at the initial three indices are zero. -/
def indexed (N : Nat) : Nat :=
  let m := N - 3
  sumFirst (fun j => m - j) (m / 2 + 1)

/-- Schulte's conjecture for every positive antidiagonal number. -/
theorem main : ∀ n : Nat, 0 < n → diagonal n = indexed (n + 3) := by
  sorry

end OMA.S_oeis_a305499
