import OMAStatements.S_mo_206970
import Mathlib

open OMA.S_mo_206970

theorem OMA.solution : type_of% @OMA.S_mo_206970.main := by
  refine ⟨?_, ?_⟩
  · intro f g hf hg sf sg x x' y y' hx hy
    obtain ⟨f0, fx, fy⟩ := hf
    obtain ⟨g0, gx, gy⟩ := hg
    have h1 := sf x x' y y' hx hy
    have h2 := sg x x' y y' hx hy
    have a1 := fx x x' y hx.le
    have a2 := fy x y y' hy.le
    have b1 := gx x x' y hx.le
    have b2 := gy x y y' hy.le
    have c1 := f0 x y
    have c2 := g0 x y
    have d1 := f0 x' y'
    have d2 := g0 x' y'
    show f x' y * g x' y + f x y' * g x y' ≤ f x' y' * g x' y' + f x y * g x y
    have hu : 0 ≤ f x' y + f x y' - f x y := by linarith
    have hv : 0 ≤ g x' y + g x y' - g x y := by linarith
    have key : (f x' y + f x y' - f x y) * (g x' y + g x y' - g x y) ≤ f x' y' * g x' y' :=
      mul_le_mul (by linarith) (by linarith) hv d1
    nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b2),
      mul_nonneg (sub_nonneg.2 a2) (sub_nonneg.2 b1)]
  · intro f g hf hg sf sg x x' y y' hx hy
    obtain ⟨f0, fx, fy⟩ := hf
    obtain ⟨g0, gx, gy⟩ := hg
    have h1 := sf x x' y y' hx hy
    have h2 := sg x x' y y' hx hy
    have a1 := fx x x' y hx.le
    have a2 := fy x y y' hy.le
    have b1 := gx x x' y hx.le
    have b2 := gy x y y' hy.le
    have c1 := f0 x y
    have c2 := g0 x y
    have d1 := f0 x' y'
    have d2 := g0 x' y'
    show f x' y * g x' y + f x y' * g x y' < f x' y' * g x' y' + f x y * g x y
    have hu : 0 ≤ f x' y + f x y' - f x y := by linarith
    have hv : 0 ≤ g x' y + g x y' - g x y := by linarith
    have key : (f x' y + f x y' - f x y) * (g x' y + g x y' - g x y) < f x' y' * g x' y' :=
      mul_lt_mul'' (by linarith) (by linarith) hu hv
    nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b2),
      mul_nonneg (sub_nonneg.2 a2) (sub_nonneg.2 b1)]
