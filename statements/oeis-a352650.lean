import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Rat.Defs

/-!
# A352650: Schulte's two identities for the derangement triangle
Sources: https://oeis.org/A352650 and https://oeis.org/A326326.
Conjectures recorded by Werner Schulte in 2022. Credit: @rgoldman73-dev.

T follows the source's row recurrence, with zero outside the lower triangle.
The row-zero clause implements the source's zero negative rows. Rational arithmetic
embeds the integer recurrence and makes the division in Conjecture 2 exact.
R is the sum of rising-factorial polynomials defining A326326, and B is its coefficient.
Both conjectures retain their original ranges; the second sum is empty at n = k.
For each term of that sum, i + k - 1 is positive.
-/

open Finset Polynomial
namespace OMA.S_oeis_a352650

def T : ℕ → ℕ → ℚ
  | 0, k => if k = 0 then 1 else 0
  | n+1, k => if k ≤ n+1 then (n+1 : ℚ)*T n k + (-1)^(n+1-k) else 0

noncomputable def R (n : ℕ) : Polynomial ℚ :=
  ∑ j ∈ range (n+1), ascPochhammer ℚ j

noncomputable def B (n i : ℕ) : ℚ := (R n).coeff i


theorem main :
    (∀ n k : ℕ, k ≤ n →
      T n k = ∑ i ∈ range (n-k+1), (-1 : ℚ)^(n+k+i) * B (n-k) i * (n:ℚ)^i) ∧
    (∀ n k : ℕ, 0 < k → k ≤ n →
      T n k = T (n-k) 0 + ∑ i ∈ Icc 1 (n-k),
        T (n-k) i * T (i+k) k * k / (i+k-1 : ℚ)) := by
  sorry

end OMA.S_oeis_a352650
