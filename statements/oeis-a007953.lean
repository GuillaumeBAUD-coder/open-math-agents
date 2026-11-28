import Mathlib

/-!
# The digit insertion interpretation of OEIS A007953

Source: https://oeis.org/A007953
Credit: @Heart-galaxy

For a positive integer `n`, insert one decimal digit at any position, allowing
each resulting integer just once and excluding an inserted leading zero.
Michel Marcus conjectured that the one-based rank of `10 * n` in the increasing
list is the digit sum of `n`. Sela Fried proved this in 2025, see
https://oeis.org/A007953/a007953.pdf, Theorem 1.
-/

namespace OMA.S_oeis_a007953

/-- Evaluate a list of decimal digits given most significant digit first. -/
def decimalValue (digits : List ℕ) : ℕ := Nat.ofDigits 10 digits.reverse

/-- Insert one digit before the first digit or at any position in the tail.
The intermediate set allows a leading zero. -/
def insertedValues : List ℕ → Finset ℕ
  | [] => Finset.range 10
  | d :: ds =>
      (Finset.range 10).image (fun x => x * 10 ^ (ds.length + 1) + decimalValue (d :: ds)) ∪
        (insertedValues ds).image (fun x => d * 10 ^ (ds.length + 1) + x)

/-- The insertion results after excluding each result with an inserted leading zero. -/
def insertions (n : ℕ) : Finset ℕ :=
  (insertedValues (Nat.digits 10 n).reverse).filter (fun x => 10 ^ (Nat.digits 10 n).length ≤ x)

/-- The rank of `10 * n` counts the results at most `10 * n`. -/
def position (n : ℕ) : ℕ := ((insertions n).filter (fun x => x ≤ 10 * n)).card

/-- Marcus's insertion-rank identity for the decimal digit sum. -/
theorem main : ∀ n : ℕ, 0 < n → (Nat.digits 10 n).sum = position n := by
  sorry

end OMA.S_oeis_a007953
