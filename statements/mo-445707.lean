import Mathlib

/-!
# Cigler's band determinant

Source: Johann Cigler, MathOverflow 445707.
https://mathoverflow.net/questions/445707
Credit: @connoranderson.

Binomial coefficients with a negative lower index are zero. The pair
0 ≤ i < j < m in the product corresponds to Cigler's 1 ≤ i+1 ≤ j ≤ m−1.
-/

namespace OMA.S_mo_445707

def zchoose (a : ℕ) (b : ℤ) : ℚ := if 0 ≤ b then a.choose b.toNat else 0

def band (n m : ℕ) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j =>
  zchoose (2*m) ((j.val:ℤ) - i.val + m) - zchoose (2*m) ((m:ℤ) - i.val - j.val - 1)

theorem main : ∀ n m : ℕ, (band n m).det =
    ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
      ((2*(n:ℚ)+i.val+j.val+1)/(i.val+j.val+1:ℚ)) := by
  sorry
end OMA.S_mo_445707
