import OMAStatements.S_mo_454212
import Mathlib

/-!
# MathOverflow 454212: the square root of a negative type function is subadditive

Let `d` be normalized and of negative type on a group, and put `x = d g`, `y = d h`,
`z = d (g h)`. Apply the negative type inequality to the three points `1, g, g h` with weights
`(s, -(s + t), t)` (their sum is `0`). The nine values `d (gᵢ⁻¹ gⱼ)` are `0, x, z, x, 0, y, z, y, 0`,
so the inequality reads

  `(z - x - y) · s t ≤ x s² + y t²`   for all real `s, t`.

* If `x, y > 0`, take `s = √y`, `t = √x`: this gives `z - x - y ≤ 2 √x √y`.
* If `x = 0`, taking `t = 1` and `s` large shows `z ≤ y`; similarly if `y = 0`.

In every case `z ≤ (√x + √y)²`, that is `√z ≤ √x + √y`.
-/

open OMA.S_mo_454212

namespace OMA.MO454212

variable {G : Type} [Group G]

/-- The negative type inequality for the points `1, g, g h` and the weights `(s, -(s+t), t)`. -/
lemma three_point {d : G → ℝ} (hd : IsNormalizedNegativeType d) (g h : G) (s t : ℝ) :
    (d (g * h) - d g - d h) * (s * t) ≤ d g * s ^ 2 + d h * t ^ 2 := by
  obtain ⟨-, h1, hinv, hneg⟩ := hd
  have key := hneg 3 ![1, g, g * h] ![s, -(s + t), t] (by simp [Fin.sum_univ_three])
  have e1 : (g * h)⁻¹ * g = h⁻¹ := by group
  simp [Fin.sum_univ_three, h1, hinv, e1, -mul_inv_rev] at key
  nlinarith [key]

end OMA.MO454212

open OMA.MO454212 in
theorem OMA.solution : type_of% @OMA.S_mo_454212.main := by
  intro G _ d hd g h
  have hx : 0 ≤ d g := hd.1 g
  have hy : 0 ≤ d h := hd.1 h
  have sx := Real.sq_sqrt hx
  have sy := Real.sq_sqrt hy
  have nx := Real.sqrt_nonneg (d g)
  have ny := Real.sqrt_nonneg (d h)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  -- it suffices to show `z - x - y ≤ 2 √x √y`
  suffices hkey : d (g * h) - d g - d h ≤ 2 * (Real.sqrt (d g) * Real.sqrt (d h)) by
    nlinarith
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have hw : 0 ≤ Real.sqrt (d g) * Real.sqrt (d h) := mul_nonneg nx ny
  rcases hw.eq_or_lt with hw0 | hwpos
  · -- one of `x, y` vanishes
    rcases mul_eq_zero.mp hw0.symm with h0 | h0
    · -- `x = 0`
      have hx0 : d g = 0 := (Real.sqrt_eq_zero hx).mp h0
      have hpos : 0 < d (g * h) - d h := by rw [h0] at hcon; linarith
      have h3 := three_point hd g h ((d h + 1) / (d (g * h) - d h)) 1
      rw [hx0] at h3
      have hS : (d (g * h) - d h) * ((d h + 1) / (d (g * h) - d h)) = d h + 1 := by
        field_simp
      nlinarith
    · -- `y = 0`
      have hy0 : d h = 0 := (Real.sqrt_eq_zero hy).mp h0
      have hpos : 0 < d (g * h) - d g := by rw [h0] at hcon; linarith
      have h3 := three_point hd g h 1 ((d g + 1) / (d (g * h) - d g))
      rw [hy0] at h3
      have hS : (d (g * h) - d g) * ((d g + 1) / (d (g * h) - d g)) = d g + 1 := by
        field_simp
      nlinarith
  · -- `x, y > 0`
    have h3 := three_point hd g h (Real.sqrt (d h)) (Real.sqrt (d g))
    rw [sx, sy] at h3
    nlinarith
