import Mathlib

/-!
# A267058: Decimal representation of the n-th iteration of the Rule 97 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267058
Conjectures: Colin Barker, Jan 10 2016 and Apr 19 2019. Karl V. Keller, Jr., Jul 03 2022.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the displayed row left to right in base 2.
-/

namespace OMA.S_oeis_a267058

def update (l c r : Bool) : Bool :=
  (97 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

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
    (∀ n : ℕ, 5 < n → (a n : ℤ) = (a (n - 2) : ℤ) + 256 * (a (n - 4) : ℤ) - 256 * (a (n - 6) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 16 * X ^ 2)) = 1 + 19 * X ^ 2 + 19 * X ^ 3 - 20 * X ^ 4 + 236 * X ^ 5) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * ((((n - 1) / 2 + 1) % 2 : ℕ) : ℚ) + 20 * 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * (((n - 1) / 2 % 2 : ℕ) : ℚ) - 1) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * (((n / 2 + 1) % 2 : ℕ) : ℚ) + 20 * 256 ^ (⌊((n : ℚ) / 4 : ℚ)⌋).toNat * ((n / 2 % 2 : ℕ) : ℚ)) := by sorry

end OMA.S_oeis_a267058
