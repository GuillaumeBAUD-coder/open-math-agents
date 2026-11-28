import Mathlib

/-!
# Nested sums for the first column of the odd-power triangle

Source: https://oeis.org/A132616 and https://oeis.org/A132615.

The matrix acts on column vectors indexed from zero. Its leading block
through row n is retained at the next stage. Row n+1 copies row n of
the (2n-1)st matrix power and appends a diagonal 1. At n=0 the block
is [1], whose inverse and zeroth power are both [1]. Coordinates above
the leading block are acted on by the identity. Applying the matrix
to the first coordinate vector gives its zeroth column.

In the sums every index starts at 1. At depth r+2 the incoming upper
bound is increased by 2r; the chosen index becomes the next bound.
This gives the displayed bounds 1+6, i+4, j+2, k for a(5).
The proof checks the seven published terms from index 0 through 6.
-/

namespace OMA.S_oeis_a132616

def exponent (n : ℕ) : ℕ := 2*n - 1

def matrix : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0 => id
  | n+1 => fun v i =>
    if i = n+1 then v i + ((matrix n)^[exponent n] v) n
    else matrix n v i

def first (i : ℕ) : ℕ := if i = 0 then 1 else 0

def a (n : ℕ) : ℕ := matrix n first n

def nested : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | r+2, bound =>
    ∑ j ∈ Finset.range (bound + 2*r), nested (r+1) (j+1)

theorem main : ∀ n : ℕ, a n = nested n 1 := by
  sorry

end OMA.S_oeis_a132616
