import OMAStatements.S_mse_4265952
import Mathlib


namespace Pent

open OMA.S_mse_4265952

def Xpt : Fin 5 → Point2 :=
  ![!₂[(-47 : ℝ), 27], !₂[(-51 : ℝ), -18], !₂[(-44 : ℝ), -87], !₂[(143 : ℝ), -25],
    !₂[(-1 : ℝ), 103]]

lemma conv : IsConvexPentagon Xpt := by
  left
  intro i j hij hij1
  fin_cases i <;> fin_cases j <;> simp_all [cross2, Xpt] <;> norm_num

lemma cent : (∑ i : Fin 5, Xpt i) = 0 := by
  ext k
  fin_cases k <;> simp [Xpt, Fin.sum_univ_five] <;> norm_num

lemma hperp : 3 * Real.sqrt 38813 < perimeter Xpt := by
  have b1 : (45.17 : ℝ) < Real.sqrt 2041 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b2 : (69.35 : ℝ) < Real.sqrt 4810 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b3 : (192.66 : ℝ) < Real.sqrt 37120 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b4 : (88.83 : ℝ) < Real.sqrt 7892 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b0 : 2 * Real.sqrt 38813 < 394.1 := by
    have h4 : (2 : ℝ) * Real.sqrt 38813 = Real.sqrt 155252 := by
      rw [show (155252 : ℝ) = 4 * 38813 by norm_num,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
        show Real.sqrt 4 = 2 by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [h4, Real.sqrt_lt' (by norm_num : (0:ℝ) < 394.1)]
    norm_num
  have hp : perimeter Xpt = Real.sqrt 2041 + Real.sqrt 4810 + Real.sqrt 38813 + Real.sqrt 37120 + Real.sqrt 7892 := by
    rw [perimeter, Fin.sum_univ_five]
    simp [Xpt, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq]
    norm_num
  rw [hp]
  linarith

lemma hdmax : ∀ i j : Fin 5, dist (Xpt i) (Xpt j) ≤ Real.sqrt 38813 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    (rw [EuclideanSpace.dist_eq] <;> simp [Xpt, Fin.sum_univ_two, Real.dist_eq] <;> norm_num)

lemma hdist : ∀ i j : Fin 5, dist (Xpt i) (Xpt j) < perimeter Xpt / 3 := by
  have hp3 : Real.sqrt 38813 < perimeter Xpt / 3 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    rw [mul_comm]
    exact hperp
  intro i j
  exact lt_of_le_of_lt (hdmax i j) hp3

lemma hmax : ∀ i : Fin 5, ‖Xpt i‖ ≤ ‖Xpt 3‖ := by
  have h3 : ‖Xpt 3‖ = Real.sqrt 21074 := by
    rw [EuclideanSpace.norm_eq]
    simp [Xpt, Fin.sum_univ_two]
    norm_num
  intro i
  rw [h3]
  fin_cases i <;>
    (rw [EuclideanSpace.norm_eq] <;> simp [Xpt, Fin.sum_univ_two] <;> norm_num)

lemma dist_proj (u v : Point2) (hu : u ≠ 0) :
    dist u (projOnto u v) = |‖u‖ ^ 2 - inner ℝ v u| / ‖u‖ := by
  have hNpos : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hstep : u - (inner ℝ v u / ‖u‖ ^ 2) • u = (1 - inner ℝ v u / ‖u‖ ^ 2) • u := by
    rw [sub_smul, one_smul]
  rw [projOnto, dist_eq_norm, hstep, norm_smul, Real.norm_eq_abs]
  have hA : |1 - inner ℝ v u / ‖u‖ ^ 2| = |‖u‖ ^ 2 - inner ℝ v u| / ‖u‖ ^ 2 := by
    have : (1 : ℝ) - inner ℝ v u / ‖u‖ ^ 2 = (‖u‖ ^ 2 - inner ℝ v u) / ‖u‖ ^ 2 := by
      field_simp
    rw [this, abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖u‖ ^ 2)]
  rw [hA]
  field_simp

lemma hu : Xpt 3 ≠ 0 := by
  intro h
  have h0 : (Xpt 3) 0 = (0 : Point2) 0 := by rw [h]
  simp [Xpt] at h0

lemma hnorm : ‖Xpt 3‖ = Real.sqrt 21074 := by
  rw [EuclideanSpace.norm_eq]
  simp [Xpt, Fin.sum_univ_two]
  norm_num

lemma hnorm2 : ‖Xpt 3‖ ^ 2 = 21074 := by
  rw [hnorm, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21074)]

lemma hd0 : inner ℝ (Xpt 0) (Xpt 3) = -7396 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Xpt, dotProduct, Fin.sum_univ_two]
  norm_num

lemma hd1 : inner ℝ (Xpt 1) (Xpt 3) = -6843 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Xpt, dotProduct, Fin.sum_univ_two]
  norm_num

lemma hd2 : inner ℝ (Xpt 2) (Xpt 3) = -4117 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Xpt, dotProduct, Fin.sum_univ_two]
  norm_num

lemma hd3 : inner ℝ (Xpt 3) (Xpt 3) = 21074 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Xpt, dotProduct, Fin.sum_univ_two]
  norm_num

lemma hd4 : inner ℝ (Xpt 4) (Xpt 3) = -2718 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Xpt, dotProduct, Fin.sum_univ_two]
  norm_num

lemma e0 : dist (Xpt 3) (projOnto (Xpt 3) (Xpt 0)) = 28470 / Real.sqrt 21074 := by
  rw [dist_proj (Xpt 3) (Xpt 0) hu, hnorm2, hnorm, hd0]
  norm_num

lemma e1 : dist (Xpt 3) (projOnto (Xpt 3) (Xpt 1)) = 27917 / Real.sqrt 21074 := by
  rw [dist_proj (Xpt 3) (Xpt 1) hu, hnorm2, hnorm, hd1]
  norm_num

lemma e2 : dist (Xpt 3) (projOnto (Xpt 3) (Xpt 2)) = 25191 / Real.sqrt 21074 := by
  rw [dist_proj (Xpt 3) (Xpt 2) hu, hnorm2, hnorm, hd2]
  norm_num

lemma e3 : dist (Xpt 3) (projOnto (Xpt 3) (Xpt 3)) = 0 := by
  rw [dist_proj (Xpt 3) (Xpt 3) hu, hnorm2, hnorm, hd3]
  norm_num

lemma e4 : dist (Xpt 3) (projOnto (Xpt 3) (Xpt 4)) = 23792 / Real.sqrt 21074 := by
  rw [dist_proj (Xpt 3) (Xpt 4) hu, hnorm2, hnorm, hd4]
  norm_num

lemma hL : (∑ i : Fin 5, dist (Xpt 3) (projOnto (Xpt 3) (Xpt i))) = 105370 / Real.sqrt 21074 := by
  rw [Fin.sum_univ_five, e0, e1, e2, e3, e4]
  have hN : (Real.sqrt 21074) ≠ 0 := by positivity
  field_simp
  norm_num

lemma hLgt : (725:ℝ) < 105370 / Real.sqrt 21074 := by
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt 21074)]
  have h2 : Real.sqrt 21074 < 105370 / 725 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 105370 / 725)]
    norm_num
  nlinarith

lemma t0 : dist (Xpt 3) (Xpt 0) = Real.sqrt 38804 := by
  rw [EuclideanSpace.dist_eq]
  simp [Xpt, Fin.sum_univ_two, Real.dist_eq]
  norm_num

lemma t1 : dist (Xpt 3) (Xpt 1) = Real.sqrt 37685 := by
  rw [EuclideanSpace.dist_eq]
  simp [Xpt, Fin.sum_univ_two, Real.dist_eq]
  norm_num

lemma t2 : dist (Xpt 3) (Xpt 2) = Real.sqrt 38813 := by
  rw [EuclideanSpace.dist_eq]
  simp [Xpt, Fin.sum_univ_two, Real.dist_eq]
  norm_num

lemma t3 : dist (Xpt 3) (Xpt 3) = 0 := by
  simp

lemma t4 : dist (Xpt 3) (Xpt 4) = Real.sqrt 37120 := by
  rw [EuclideanSpace.dist_eq]
  simp [Xpt, Fin.sum_univ_two, Real.dist_eq]
  norm_num

lemma hT : (∑ i : Fin 5, dist (Xpt 3) (Xpt i)) < 783 := by
  rw [Fin.sum_univ_five, t0, t1, t2, t3, t4]
  have b0 : Real.sqrt 38804 < 197 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 197)]; norm_num
  have b1 : Real.sqrt 37685 < 195 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 195)]; norm_num
  have b2 : Real.sqrt 38813 < 198 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 198)]; norm_num
  have b4 : Real.sqrt 37120 < 193 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 193)]; norm_num
  linarith

lemma hsin : (11:ℝ)/20 < Real.sin (Real.pi/5) := by
  have h1 : Real.sin (3/5) < Real.sin (Real.pi/5) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_gt_three]
  have h2 : (3/5:ℝ) - (3/5)^3/6 < Real.sin (3/5) := Real.sin_gt_sub_cube (by norm_num)
  linarith

lemma hc : 1 / (2 * Real.sin (Real.pi/5)) < (10:ℝ)/11 := by
  have hsp : 0 < Real.sin (Real.pi/5) := by linarith [hsin]
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.sin (Real.pi/5))]
  have h2 : (10:ℝ)/11 * (2 * Real.sin (Real.pi/5)) = (20/11) * Real.sin (Real.pi/5) := by ring
  rw [h2]
  nlinarith [hsin]

lemma hRlt :
    (1 / (2 * Real.sin (Real.pi / 5))) * (∑ i : Fin 5, dist (Xpt 3) (Xpt i)) < 725 := by
  have hTnn : 0 ≤ (∑ i : Fin 5, dist (Xpt 3) (Xpt i)) :=
    Finset.sum_nonneg (fun i _ => dist_nonneg)
  have hsp : 0 < Real.sin (Real.pi/5) := by linarith [hsin]
  have hcpos : 0 < 1 / (2 * Real.sin (Real.pi / 5)) := by positivity
  calc (1 / (2 * Real.sin (Real.pi / 5))) * (∑ i : Fin 5, dist (Xpt 3) (Xpt i))
      ≤ (1 / (2 * Real.sin (Real.pi / 5))) * 783 :=
        mul_le_mul_of_nonneg_left hT.le hcpos.le
    _ < (10/11) * 783 := mul_lt_mul_of_pos_right hc (by norm_num)
    _ < 725 := by norm_num

lemma violation :
    ¬ ((∑ i : Fin 5, dist (Xpt 3) (projOnto (Xpt 3) (Xpt i))) ≤
        (1 / (2 * Real.sin (Real.pi / 5))) * ∑ i : Fin 5, dist (Xpt 3) (Xpt i)) := by
  intro hle
  have h1 : (725:ℝ) < ∑ i : Fin 5, dist (Xpt 3) (projOnto (Xpt 3) (Xpt i)) := by
    rw [hL]
    exact hLgt
  linarith [hRlt]

end Pent

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4265952.main) := by
  intro h
  exact Pent.violation (h Pent.Xpt 3 Pent.conv Pent.cent Pent.hdist Pent.hmax)
