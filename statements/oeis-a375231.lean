import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Nat.Factorial.Basic

/-!
# OEIS A375231

Source: https://oeis.org/A375231
Credit: @NOELOO6

Stefano Spezia's August 2024 conjecture compares the interleaving of
A006040 and A228229 with a checkerboard permanent. The sequences below
use A006040's defining factorial sum and A228229's defining recurrence.
The published interleaving formula and term table agree at the n = 2
counterexample. Translating both matrix indices by one preserves their
parity sum and equality.
-/

namespace OMA.S_oeis_a375231
open Finset

def balanced (n : ℕ) : ℕ := ∑ k ∈ range (n+1), (n.descFactorial k)^2

def adjacent : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1)*(n+2)*adjacent n+1

def a (n : ℕ) : ℕ :=
  if n%2=0 then adjacent (n/2) else balanced ((n+1)/2)

def checker (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if i=j ∨ (i.val+j.val)%2=1 then 1 else 0

theorem main : ∀ n, a n=(checker n).permanent := by
  sorry

end OMA.S_oeis_a375231
