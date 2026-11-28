import OMAStatements.S_mo_206970
import Mathlib

/-!
# MathOverflow 206970: products of non-negative increasing supermodular functions

Write `f₀₀ = f x y`, `f₁₀ = f x' y`, `f₀₁ = f x y'`, `f₁₁ = f x' y'` (and likewise for `g`), and
`Δf = f₁₁ + f₀₀ - f₁₀ - f₀₁`.  Then

  `Δ(fg) = Δf · g₀₁ + (f₁₁ - f₁₀)(g₁₁ - g₀₁) + f₁₀ · Δg + (f₁₀ - f₀₀)(g₀₁ - g₀₀)`,

and all four terms are non-negative.  In the strict case `Δf, Δg > 0`: the first term is
positive if `g₀₁ > 0`, the third if `f₁₀ > 0`, and if `g₀₁ = f₁₀ = 0` then `f₁₁ > 0`, `g₁₁ > 0`
and the second term `f₁₁ g₁₁` is positive.
-/

open OMA.S_mo_206970 in
theorem OMA.solution : type_of% @OMA.S_mo_206970.main := by
  refine ⟨?_, ?_⟩
  · intro f g ⟨fn, fx, fy⟩ ⟨gn, gx, gy⟩ sf sg x x' y y' hx hy
    have hDf := sf x x' y y' hx hy
    have hDg := sg x x' y y' hx hy
    have a1 := fx x x' y hx.le
    have a4 := fy x' y y' hy.le
    have b2 := gx x x' y' hx.le
    have b3 := gy x y y' hy.le
    have T1 := mul_nonneg (show 0 ≤ f x' y' + f x y - f x' y - f x y' by linarith) (gn x y')
    have T2 := mul_nonneg (sub_nonneg.mpr a4) (sub_nonneg.mpr b2)
    have T3 := mul_nonneg (fn x' y) (show 0 ≤ g x' y' + g x y - g x' y - g x y' by linarith)
    have T4 := mul_nonneg (sub_nonneg.mpr a1) (sub_nonneg.mpr b3)
    show f x' y * g x' y + f x y' * g x y' ≤ f x' y' * g x' y' + f x y * g x y
    nlinarith
  · intro f g ⟨fn, fx, fy⟩ ⟨gn, gx, gy⟩ sf sg x x' y y' hx hy
    have hDf := sf x x' y y' hx hy
    have hDg := sg x x' y y' hx hy
    have a1 := fx x x' y hx.le
    have a4 := fy x' y y' hy.le
    have b1 := gx x x' y hx.le
    have b2 := gx x x' y' hx.le
    have b3 := gy x y y' hy.le
    have T1 := mul_nonneg (show 0 ≤ f x' y' + f x y - f x' y - f x y' by linarith) (gn x y')
    have T2 := mul_nonneg (sub_nonneg.mpr a4) (sub_nonneg.mpr b2)
    have T3 := mul_nonneg (fn x' y) (show 0 ≤ g x' y' + g x y - g x' y - g x y' by linarith)
    have T4 := mul_nonneg (sub_nonneg.mpr a1) (sub_nonneg.mpr b3)
    show f x' y * g x' y + f x y' * g x y' < f x' y' * g x' y' + f x y * g x y
    rcases (gn x y').lt_or_eq with hg | hg
    · -- `g₀₁ > 0`: the first term is positive
      have S1 := mul_pos (show 0 < f x' y' + f x y - f x' y - f x y' by linarith) hg
      nlinarith
    · rcases (fn x' y).lt_or_eq with hf | hf
      · -- `f₁₀ > 0`: the third term is positive
        have S3 := mul_pos hf (show 0 < g x' y' + g x y - g x' y - g x y' by linarith)
        nlinarith
      · -- `g₀₁ = f₁₀ = 0`: the second term is `f₁₁ g₁₁ > 0`
        have hf11 : 0 < f x' y' - f x' y := by linarith [fn x y']
        have hg11 : 0 < g x' y' - g x y' := by linarith [gn x y]
        have S2 := mul_pos hf11 hg11
        nlinarith
