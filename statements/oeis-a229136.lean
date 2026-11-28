import Mathlib

/-!
# The relation between OEIS A229136 and A131885

Source: https://oeis.org/A229136
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A229/A229136.seq
Reference sequence: https://oeis.org/A131885
Credit: @Heart-galaxy

The number a(n) counts tuples of n digits in 0 through 3 whose squared
entries sum to 1 modulo 4. The integer sequence b is A131885, with its
four initial values and third-order recurrence as recorded there.

Petros Hadjicostas corrected and proved this identity in the A229136
entry in December 2019.
-/

namespace OMA.S_oeis_a229136

open Finset

def digitSquare (x : Fin 4) : ZMod 4 := ((x : ℕ) : ZMod 4) ^ 2

abbrev solutions (n : ℕ) (r : ZMod 4) : Type :=
  {x : Fin n → Fin 4 // (∑ i, digitSquare (x i)) = r}

def count (n : ℕ) (r : ZMod 4) : ℕ := Fintype.card (solutions n r)

def a (n : ℕ) : ℕ := count n 1

def b : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | n + 4 => 4 * b (n + 3) - 6 * b (n + 2) + 4 * b (n + 1)

theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = b n * (2 : ℤ) ^ (n - 1) := by
  sorry

end OMA.S_oeis_a229136
