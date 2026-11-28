import OMAStatements.S_mo_104224

open Filter Metric Set
open scoped Topology

namespace OMA.Mo104224

open OMA.S_mo_104224

private theorem neg_square (z : Circle) : (-z)^2 = z^2 := by
  apply Circle.ext
  simp

private theorem square_surjective : Function.Surjective (fun z : Circle ↦ z^2) := by
  intro x
  obtain ⟨t, rfl⟩ := Circle.exp_surjective x
  refine ⟨Circle.exp (t / 2), ?_⟩
  change Circle.exp (t / 2)^2 = Circle.exp t
  rw [← Circle.exp_natCast_mul]
  congr 1
  norm_num
  ring

private theorem roots_square (z : Circle) : roots (z^2) = {z, -z} := by
  ext w
  show w^2 = z^2 ↔ w ∈ ({z, -z} : Set Circle)
  rw [mem_insert_iff, mem_singleton_iff, ← Circle.coe_inj, Circle.coe_pow, Circle.coe_pow,
    sq_eq_sq_iff_eq_or_eq_neg, ← Circle.coe_neg, Circle.coe_inj, Circle.coe_inj]

private theorem roots_pair (x : Circle) : ∃ z, roots x = {z, -z} ∧ z ≠ -z := by
  obtain ⟨z, rfl⟩ := square_surjective x
  exact ⟨z, roots_square z, (Circle.neg_ne_self z).symm⟩

private theorem dist_coe (z w : Circle) : dist z w = ‖(z : ℂ) - (w : ℂ)‖ :=
  show dist (z : ℂ) (w : ℂ) = _ from dist_eq_norm _ _

private theorem nearby_root (x y : Circle) (u : Circle) (hu : u ∈ roots x) :
    ∃ w ∈ roots y, dist u w ≤ dist x y / Real.sqrt 2 := by
  obtain ⟨v, hv⟩ := square_surjective y
  change u^2 = x at hu
  let A := dist u v
  let B := dist u (-v)
  have hA : 0 ≤ A := dist_nonneg
  have hB : 0 ≤ B := dist_nonneg
  have hs : A^2 + B^2 = 4 := by
    have h := parallelogram_law_with_norm ℝ (u : ℂ) (v : ℂ)
    norm_num [A, B, dist_coe, sub_neg_eq_add, Circle.norm_coe, add_comm] at h ⊢
    exact h
  have hp : dist x y = A * B := by
    rw [← hu, ← hv, dist_coe, Circle.coe_pow, Circle.coe_pow, sq_sub_sq, norm_mul]
    simp [A, B, dist_coe, sub_neg_eq_add, mul_comm]
  have ht : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmax : Real.sqrt 2 ≤ max A B := by
    by_contra! h
    have h₁ := (sq_lt_sq₀ hA ht.le).mpr ((le_max_left _ _).trans_lt h)
    have h₂ := (sq_lt_sq₀ hB ht.le).mpr ((le_max_right _ _).trans_lt h)
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases h : A ≤ B
  · have hb : Real.sqrt 2 ≤ B := by simpa [max_eq_right h] using hmax
    refine ⟨v, hv, (le_div_iff₀ ht).2 ?_⟩
    rw [hp]
    exact mul_le_mul_of_nonneg_left hb hA
  · have ha : Real.sqrt 2 ≤ A := by simpa [max_eq_left (le_of_not_ge h)] using hmax
    refine ⟨-v, (neg_square v).trans hv, (le_div_iff₀ ht).2 ?_⟩
    rw [hp, mul_comm A B]
    exact mul_le_mul_of_nonneg_left ha hB

private theorem upper : UpperHemicontinuous roots :=
  isClosedMap_iff_upperHemicontinuous.mp ((continuous_id.pow 2).isClosedMap)

private theorem lower : LowerHemicontinuous roots := by
  refine lowerHemicontinuous_iff_isOpen_inter_nonempty.mpr fun U hU ↦
    isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  obtain ⟨z, hz, hzU⟩ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine Metric.mem_nhds_iff.mpr ⟨ε * Real.sqrt 2, mul_pos hε hs, ?_⟩
  intro y hy
  obtain ⟨w, hw, hdist⟩ := nearby_root x y z hz
  have hy' : dist x y < ε * Real.sqrt 2 := by
    rw [dist_comm]
    exact mem_ball.mp hy
  exact ⟨w, hw, hball (mem_ball.mpr (by
    rw [dist_comm]
    exact hdist.trans_lt ((div_lt_iff₀ hs).2 hy')))⟩

private theorem no_selection : ¬ ∃ g : Circle → Circle, Continuous g ∧ ∀ x, g x ∈ roots x := by
  rintro ⟨g, hg, hgroot⟩
  let A := {z : Circle | g (z^2) = z}
  let B := {z : Circle | g (z^2) = -z}
  have hclosedA : IsClosed A := isClosed_eq (hg.comp (continuous_id.pow 2)) continuous_id
  have hclosedB : IsClosed B := isClosed_eq (hg.comp (continuous_id.pow 2)) continuous_neg
  have hpre : ∀ z : Circle, g (z^2) = z ∨ g (z^2) = -z := by
    intro z
    have h := hgroot (z^2)
    rwa [roots_square, mem_insert_iff, mem_singleton_iff] at h
  have hAB : Aᶜ = B := by
    ext z
    change g (z^2) ≠ z ↔ g (z^2) = -z
    exact ⟨fun h ↦ (hpre z).resolve_left h, fun h ↦ h ▸ Circle.neg_ne_self z⟩
  have hFlip (z : Circle) : z ∉ A ↔ -z ∈ A := by
    change g (z^2) ≠ z ↔ g ((-z)^2) = -z
    rw [neg_square]
    exact ⟨fun h ↦ (hpre z).resolve_left h, fun h ↦ h ▸ Circle.neg_ne_self z⟩
  have hclopen : IsClopen A := ⟨hclosedA, isClosed_compl_iff.mp (hAB ▸ hclosedB)⟩
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · have hneg := (hFlip 1).1 (by simp [hempty])
    simp [hempty] at hneg
  · have hnot : (1 : Circle) ∉ A := (hFlip 1).2 (by simp [huniv])
    exact hnot (by simp [huniv])

private theorem result : type_of% @OMA.S_mo_104224.main := by
  refine ⟨roots_pair, upper, lower, ?_, no_selection⟩
  intro x y
  refine hausdorffDist_le_of_mem_dist
    (div_nonneg dist_nonneg (Real.sqrt_nonneg _)) (nearby_root x y) ?_
  simpa only [dist_comm y x] using nearby_root y x

end OMA.Mo104224

theorem OMA.solution : type_of% @OMA.S_mo_104224.main := OMA.Mo104224.result
