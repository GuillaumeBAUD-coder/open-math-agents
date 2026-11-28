import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic

/-!
# eigenvalues of a square block matrix

Source: MathOverflow question 311259, UserName, 23 September 2018.
https://mathoverflow.net/questions/311259/eigenvalues-of-a-square-block-matrix
Credit: @etaubman

The displayed tridiagonal family is viewed over the complex numbers.
Absence of defective eigenvalues means that each maximal generalized
eigenspace equals the ordinary eigenspace.
-/

namespace OMA.S_mo_311259

def damping (d : ℕ) (a : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val = j.val then
    (if i.val = 0 ∨ i.val + 1 = d then -(a : ℂ) else 0) else 0

def stiffness (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val = j.val then
    (if i.val = 0 ∨ i.val + 1 = d then 2 else 3)
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

def block (d : ℕ) (a : ℝ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Matrix.fromBlocks (damping d a) (stiffness d) (-stiffness d) 0

theorem main : ∀ d : ℕ, 2 ≤ d → ∀ a : ℝ, 0 < a → ∀ z : ℂ,
    Module.End.genEigenspace (block d a).mulVecLin z ⊤ = Module.End.eigenspace (block d a).mulVecLin z := by
  sorry

end OMA.S_mo_311259
