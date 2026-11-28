import OMAStatements.S_oeis_a188646
import Mathlib

/-!
Let s = sqrt(x^2 + y), so k = (s + x)^2 and, since (s + x)(s - x) = y with y^2 = 1, 1/k = (s - x)^2.
Hence k + 1/k = 2s^2 + 2x^2 = 4x^2 + 2y is an integer. From the definition,
a(n + 2) - k a(n + 1) = (a(n + 1) - k a(n)) / k, that is a(n + 2) = (k + 1/k) a(n + 1) - a(n);
with a(0) = 1 and a(1) = k + 1/k - 1, every term is an integer by induction.
-/

namespace R188646
open OMA.S_oeis_a188646

theorem kpos (x : ℕ) (hx : 1 ≤ x) (y : ℤ) : 0 < k x y := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have := Real.sqrt_nonneg ((x : ℝ) ^ 2 + y)
  show 0 < (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ)) + (x : ℝ)) ^ 2
  exact pow_pos (by linarith) 2

theorem kinv (x : ℕ) (hx : 1 ≤ x) (y : ℤ) (hy : y = 1 ∨ y = -1) :
    k x y + (k x y)⁻¹ = 4 * (x : ℝ) ^ 2 + 2 * y := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hy' : (y : ℝ) ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hy1 : (-1 : ℝ) ≤ y := by rcases hy with rfl | rfl <;> norm_num
  have hrad : 0 ≤ (x : ℝ) ^ 2 + y := by nlinarith
  have hs2 : Real.sqrt ((x : ℝ) ^ 2 + y) ^ 2 = (x : ℝ) ^ 2 + y := Real.sq_sqrt hrad
  have hk : k x y = (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ)) + (x : ℝ)) ^ 2 := rfl
  rw [hk]
  generalize Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ)) = s at hs2 ⊢
  have hinv : ((s + x) ^ 2)⁻¹ = (s - x) ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination (s ^ 2 - (x : ℝ) ^ 2 + y) * hs2 + hy'
  rw [hinv]
  linear_combination 2 * hs2

theorem rec2 (x : ℕ) (y : ℤ) (hk0 : k x y ≠ 0) (n : ℕ) :
    a x y (n + 1 + 1) = (k x y + (k x y)⁻¹) * a x y (n + 1) - a x y n := by
  have h1 : a x y (n + 1 + 1) = a x y (n + 1) * k x y - (k x y - 1) / k x y ^ (n + 1 + 1) := rfl
  have h2 : a x y (n + 1) = a x y n * k x y - (k x y - 1) / k x y ^ (n + 1) := rfl
  have hKK : k x y * (k x y)⁻¹ = 1 := mul_inv_cancel₀ hk0
  rw [h1, h2]
  first
    | linear_combination (-(a x y n)) * hKK
    | (field_simp; ring)

end R188646

theorem OMA.solution : type_of% @OMA.S_oeis_a188646.main := by
  intro x hx y hy
  have hk0 : OMA.S_oeis_a188646.k x y ≠ 0 := (R188646.kpos x hx y).ne'
  have hc := R188646.kinv x hx y hy
  have key : ∀ n, (∃ m : ℤ, OMA.S_oeis_a188646.a x y n = m) ∧
      (∃ m : ℤ, OMA.S_oeis_a188646.a x y (n + 1) = m) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨1, by simp [OMA.S_oeis_a188646.a]⟩, ⟨4 * x ^ 2 + 2 * y - 1, ?_⟩⟩
      have hKK : OMA.S_oeis_a188646.k x y * (OMA.S_oeis_a188646.k x y)⁻¹ = 1 :=
        mul_inv_cancel₀ hk0
      show 1 * OMA.S_oeis_a188646.k x y - (OMA.S_oeis_a188646.k x y - 1) /
        OMA.S_oeis_a188646.k x y ^ (0 + 1) = _
      push_cast
      linear_combination hc - hKK
    | succ n ih =>
      obtain ⟨⟨m0, h0⟩, ⟨m1, h1⟩⟩ := ih
      refine ⟨⟨m1, h1⟩, ⟨(4 * x ^ 2 + 2 * y) * m1 - m0, ?_⟩⟩
      rw [R188646.rec2 x y hk0 n, hc, h0, h1]
      push_cast
      ring
  exact fun n => (key n).1
