import Mathlib

/-!
# A277930: Schulte's identity with Borel's triangle

Source: https://oeis.org/A277930
Credit: @rgoldman73-dev

This states Werner Schulte's August 3, 2017 conjecture for every k,n>=0.
`evenCoeff k n` is a(k,2*n+2), using the nonconjectural Catalan-sum
formula in A277930, also used by its Mathematica and Python programs.
`C n s` is Catalan's triangle A009766, using the binomial-difference
formula recorded there by R. J. Cano (July 22, 2014).
`B n i` is Borel's triangle A234950, with its defining binomial transform.
Terms s<i contribute zero, so the sum from 0 to n is the source's sum
from i to n. All arithmetic is in the integers, preserving signs.

Sources: https://oeis.org/A009766 and https://oeis.org/A234950.
The Catalan numbers are Mathlib's `catalan`.
-/

namespace OMA.S_oeis_a277930

open Finset

def C (n s : ℕ) : ℤ := (Nat.choose (n+s) n : ℤ) - Nat.choose (n+s) (n+1)

def B (n i : ℕ) : ℤ := ∑ s ∈ range (n+1), (Nat.choose s i : ℤ) * C n s

def evenCoeff (k n : ℕ) : ℤ :=
  1 - 2 * ∑ i ∈ range (n+1), (catalan i : ℤ) * (-(k : ℤ)*(k+1))^(i+1)

theorem main : ∀ k n : ℕ,
    evenCoeff k n = 1+2*(k : ℤ)+2*(-(k : ℤ))^(n+2)*
      (∑ i ∈ range (n+1), B n i*(k : ℤ)^i) := by
  sorry

end OMA.S_oeis_a277930
