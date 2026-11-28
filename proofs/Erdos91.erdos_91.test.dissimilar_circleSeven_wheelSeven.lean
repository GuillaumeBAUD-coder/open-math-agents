import FormalConjectures.ErdosProblems.«91»

open Erdos91 EuclideanGeometry

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.dissimilar_circleSeven_wheelSeven := by
  rintro ⟨f, hf⟩
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  let c : ℝ² := !₂[cx, cy]
  have h (u : ℝ) (hu : !₂[u, Real.sqrt 3 / 2] ∈ wheelSeven) :
      (u - f c 0) ^ 2 + (Real.sqrt 3 / 2 - f c 1) ^ 2 = (Dilation.ratio f * r) ^ 2 := by
    obtain ⟨q, hq, eq⟩ : !₂[u, Real.sqrt 3 / 2] ∈ f '' (circleSeven : Set ℝ²) := hf ▸ hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    have hd := congrArg (dist · (f c) ^ 2) eq
    rw [Dilation.dist_eq, mul_pow, EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two] at hd
    simp only [Real.dist_eq, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one] at hd
    change (Dilation.ratio f : ℝ) ^ 2 * ((r * _ + cx - cx) ^ 2 + (r * _ + cy - cy) ^ 2) = _ at hd
    simp only [add_sub_cancel_right] at hd
    linear_combination -hd +
      (Dilation.ratio f : ℝ) ^ 2 * r ^ 2 * Real.sin_sq_add_cos_sq (2 * Real.pi * k / 7)
  nlinarith [h 0 (by simp [wheelSeven]), h 1 (by simp [wheelSeven]), h 2 (by simp [wheelSeven])]
