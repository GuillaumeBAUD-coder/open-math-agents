import FormalConjectures.ErdosProblems.«91»

open Erdos91 EuclideanGeometry

private lemma plane_dist_sq (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

private lemma heptagon_cospherical : Cospherical (circleSeven : Set ℝ²) := by
  let r : ℝ := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  refine ⟨!₂[cx, cy], |r|, ?_⟩
  intro p hp
  change p ∈ (Finset.range 7).image (fun k : ℕ =>
    !₂[r * Real.cos (2 * Real.pi * ↑k / 7) + cx,
       r * Real.sin (2 * Real.pi * ↑k / 7) + cy]) at hp
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
  let θ : ℝ := 2 * Real.pi * ↑k / 7
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg r)).mp
  rw [plane_dist_sq, sq_abs]
  change (r * Real.cos θ + cx - cx) ^ 2 + (r * Real.sin θ + cy - cy) ^ 2 = r ^ 2
  simp only [add_sub_cancel_right, mul_pow]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ

private lemma wheel_not_cospherical : ¬ Cospherical (wheelSeven : Set ℝ²) := by
  rintro ⟨c, R, h⟩
  let y := Real.sqrt 3 / 2
  have eqn (u : ℝ) (hu : !₂[u, y] ∈ wheelSeven) :
      (u - c 0) ^ 2 + (y - c 1) ^ 2 = R ^ 2 := by
    calc
      _ = dist (!₂[u, y]) c ^ 2 := (plane_dist_sq _ _).symm
      _ = R ^ 2 := by rw [h _ hu]
  have h0 := eqn 0 (by simp [wheelSeven, y])
  have h1 := eqn 1 (by simp [wheelSeven, y])
  have h2 := eqn 2 (by simp [wheelSeven, y])
  nlinarith only [h0, h1, h2]

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.dissimilar_circleSeven_wheelSeven := by
  rintro ⟨f, hf⟩
  obtain ⟨c, r, hc⟩ := heptagon_cospherical
  apply wheel_not_cospherical
  refine ⟨f c, (Dilation.ratio f : ℝ) * r, ?_⟩
  intro p hp
  rw [← hf] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [Dilation.dist_eq, hc q hq]
