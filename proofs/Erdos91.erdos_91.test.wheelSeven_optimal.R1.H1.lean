import OMAReductions.R_Erdos91_erdos_91_test_wheelSeven_optimal_R1

open EuclideanGeometry Erdos91

namespace WheelCoordinates

-- Integer coordinates in units of 1/2 horizontally and sqrt(3)/2 vertically.
private def sites : Finset (ℤ × ℤ) :=
  {(2, 1), (4, 1), (3, 2), (1, 2), (0, 1), (1, 0), (3, 0)}

private noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ) / 2, (p.2 : ℝ) * Real.sqrt 3 / 2]

private lemma point_injective : Function.Injective point := by
  intro p q h
  have hx := congrArg (fun v : ℝ² => v 0) h
  have hy := congrArg (fun v : ℝ² => v 1) h
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  simp [point, hs] at hx hy
  exact Prod.ext (by exact_mod_cast hx) (by simpa using hy)

private lemma wheel_eq : wheelSeven = sites.image point := by
  classical
  norm_num [sites, point, wheelSeven, Finset.image_insert, Finset.image_singleton]

private def normCode (p q : ℤ × ℤ) : ℕ :=
  ((p.1 - q.1) ^ 2 + 3 * (p.2 - q.2) ^ 2).toNat

private noncomputable def lengthOf (n : ℕ) : ℝ := Real.sqrt n / 2

private lemma length_injective : Function.Injective lengthOf := by
  intro m n h
  have he : Real.sqrt (m : ℝ) = Real.sqrt (n : ℝ) := by
    simpa [lengthOf] using h
  have hsq := congrArg (fun t : ℝ => t ^ 2) he
  simpa using hsq

private lemma dist_point (p q : ℤ × ℤ) :
    dist (point p) (point q) = lengthOf (normCode p q) := by
  have hpos : 0 ≤ (p.1 - q.1) ^ 2 + 3 * (p.2 - q.2) ^ 2 := by positivity
  have hc : (normCode p q : ℝ) =
      ((p.1 : ℝ) - q.1) ^ 2 + 3 * ((p.2 : ℝ) - q.2) ^ 2 := by
    unfold normCode
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hpos]
    push_cast
    ring
  have hd := EuclideanSpace.dist_sq_eq (point p) (point q)
  rw [Fin.sum_univ_two] at hd
  simp only [point, Real.dist_eq, Matrix.cons_val_zero, Matrix.cons_val_one, sq_abs] at hd
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdsq : dist (point p) (point q) ^ 2 = (normCode p q : ℝ) / 4 := by
    simp only [point]
    rw [hd, hc]
    linear_combination ((p.2 : ℝ) - q.2) ^ 2 / 4 * hs
  unfold lengthOf
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
  rw [hdsq, div_pow, Real.sq_sqrt (by positivity)]
  norm_num

private lemma lengths :
    distanceSet wheelSeven = (sites.offDiag.image (fun t => normCode t.1 t.2)).image lengthOf := by
  classical
  rw [wheel_eq]
  ext d
  constructor
  · intro hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, fun e => hne (congrArg point e)⟩, rfl⟩,
      (dist_point p q).symm⟩
  · intro hd
    obtain ⟨_, hn, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.mp hpq
    exact Finset.mem_image.mpr ⟨(point p, point q), Finset.mem_offDiag.mpr
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq, point_injective.ne hne⟩,
      dist_point p q⟩

end WheelCoordinates

open WheelCoordinates

theorem OMA.solution : OMA.R_Erdos91_erdos_91_test_wheelSeven_optimal_R1.H1 := by
  constructor
  · rw [wheel_eq, Finset.card_image_of_injective _ point_injective]
    decide
  · have codes : sites.offDiag.image (fun t => normCode t.1 t.2) = {4, 12, 16} := by decide
    rw [distinctDistances, lengths, Finset.card_image_of_injective _ length_injective, codes]
    decide
