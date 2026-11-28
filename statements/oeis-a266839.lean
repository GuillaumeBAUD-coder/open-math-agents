import Mathlib

/-!
# A266839: Decimal representation of the n-th iteration of the Rule 67 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266839
Conjectures: Colin Barker, Jan 05 2016 and Apr 18 2019. Karl V. Keller, Jr., Dec 16 2021.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the displayed row left to right in base 2.
-/

namespace OMA.S_oeis_a266839

def update (l c r : Bool) : Bool :=
  (67 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Each step also updates the common value on both infinite tails. -/
def background : ℕ → Bool
  | 0 => false
  | n + 1 => let b := background n; update b b b

/-- Slide a three-cell window from left to right. -/
def scan (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: rs => update l c r :: scan c r rs

/-- Sites -n through n, represented in increasing order. -/
def row : ℕ → List Bool
  | 0 => [true]
  | n + 1 =>
    let b := background n
    scan b b (row n ++ [b, b])

def a (n : ℕ) : ℕ := Nat.ofDigits 2 ((row n).map Bool.toNat).reverse

open PowerSeries in
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 25 * (a (n - 2) : ℤ) - 152 * (a (n - 4) : ℤ) + 128 * (a (n - 6) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) = 1 + 4 * X - 15 * X ^ 2 - 3 * X ^ 3 - 6 * X ^ 4 - 14 * X ^ 5 - 172 * X ^ 6 - 28 * X ^ 7 + 192 * X ^ 8 - 64 * X ^ 9) ∧
    (∀ n : ℕ, 2 < n → Odd n → (a n : ℚ) = 2 * 4 ^ n - 61 * 8 ^ (⌊((n : ℚ) / 2 : ℚ)⌋).toNat / 16 - 1) ∧
    (∀ n : ℕ, 3 < n → Even n → (a n : ℚ) = 23 * 8 ^ (n / 2) / 16) := by sorry

end OMA.S_oeis_a266839
