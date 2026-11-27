import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1

/-! The compactness direction of the uniform approximation criterion for a fixed word. -/

-- Problem: Green100.green_100.parts.ii.R1.H2.R1.H1
-- Credit: @sobrien032
-- Gao–Yu–Zhi, arXiv:2610.10248v2, Lemma 2.2.

namespace Green100.WordCompactness

open Filter
open scoped Topology
open scoped Matrix.Norms.Frobenius
abbrev UnitaryAt (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

theorem hsDist_eq_frobenius {n : ℕ} (u v : UnitaryAt n) :
    hsDist u v = ‖u.val - v.val‖ / Real.sqrt n := by
  rw [hsDist, Real.sqrt_div (by positivity), Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp [Matrix.sub_apply]

theorem hsDist_triangle {n : ℕ} (u v w : UnitaryAt n) :
    hsDist u w ≤ hsDist u v + hsDist v w := by
  simp only [hsDist_eq_frobenius, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  simpa only [dist_eq_norm] using dist_triangle u.val v.val w.val

private theorem sumSq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Matrix.trace (star M * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]

theorem hsDist_mul_left {n : ℕ} (a u v : UnitaryAt n) :
    hsDist (a * u) (a * v) = hsDist u v := by
  unfold hsDist
  congr 2
  change (∑ i, ∑ j, ‖((a.val * u.val - a.val * v.val) i j)‖ ^ 2) =
    ∑ i, ∑ j, ‖((u.val - v.val) i j)‖ ^ 2
  rw [← mul_sub, sumSq_trace, sumSq_trace, star_mul, mul_assoc,
    ← mul_assoc (star a.val), a.property.1, one_mul]

private theorem hsDist_inv {n : ℕ} (u v : UnitaryAt n) : hsDist u⁻¹ v⁻¹ = hsDist u v := by
  rw [hsDist_eq_frobenius, hsDist_eq_frobenius]
  change ‖star u.val - star v.val‖ / _ = _
  rw [← star_sub, Matrix.star_eq_conjTranspose, Matrix.frobenius_norm_conjTranspose]

private theorem hsDist_mul_right {n : ℕ} (a u v : UnitaryAt n) :
    hsDist (u * a) (v * a) = hsDist u v := by
  rw [← hsDist_inv (u * a), mul_inv_rev, mul_inv_rev, hsDist_mul_left, hsDist_inv]

/-- The normal subgroup of sequences whose normalized HS distance to identity tends to zero. -/
def nullSequences (d : ℕ → ℕ) (L : Filter ℕ) : Subgroup ((i : ℕ) → UnitaryAt (d i)) where
  carrier := {x | Tendsto (fun i => hsDist (x i) 1) L (𝓝 0)}
  one_mem' := by simp [hsDist, tendsto_const_nhds]
  mul_mem' {x y} hx hy := by
    apply squeeze_zero (fun i => Real.sqrt_nonneg _)
      (g := fun i => hsDist (y i) 1 + hsDist (x i) 1)
    · intro i
      have ht := hsDist_triangle (x i * y i) (x i * 1) 1
      rw [hsDist_mul_left, mul_one] at ht
      exact ht
    · simpa only [add_zero] using hy.add hx
  inv_mem' {x} hx := by
    change Tendsto (fun i => hsDist (x i)⁻¹ 1) L (𝓝 0)
    have eq (i : ℕ) : hsDist (x i)⁻¹ 1 = hsDist (x i) 1 := by
      simpa only [inv_one] using hsDist_inv (x i) 1
    change Tendsto (fun i => hsDist (x i) 1) L (𝓝 0) at hx
    simpa only [eq] using hx

instance (d : ℕ → ℕ) (L : Filter ℕ) : (nullSequences d L).Normal where
  conj_mem x hx a := by
    change Tendsto (fun i => hsDist (a i * x i * (a i)⁻¹) 1) L (𝓝 0)
    have eq (i : ℕ) : hsDist (a i * x i * (a i)⁻¹) 1 = hsDist (x i) 1 := by
      rw [← hsDist_mul_right (a i), one_mul, inv_mul_cancel_right]
      simpa using hsDist_mul_left (a i) (x i) 1
    change Tendsto (fun i => hsDist (x i) 1) L (𝓝 0) at hx
    simpa only [eq] using hx

/-- If the positive tolerances all fail, one countermodel at each accuracy gives
an exact quotient representation still detecting the marked word. -/
theorem compactness : OMA.R_Green100_green_100_parts_ii_R1_H2_R1.H1 := by
  classical
  intro k R w S vanishes η positive
  by_contra noTolerance
  push Not at noTolerance
  let e (i : ℕ) : ℝ := 1 / (i + 1 : ℝ)
  have he (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  choose d hd u rel separated using fun i => noTolerance (e i) (he i)
  let L : Filter ℕ := hyperfilter ℕ
  let N := Subgroup.normalClosure (nullSequences d L : Set ((i : ℕ) → UnitaryAt (d i)))
  let raw := MonoidHom.pi fun i => FreeGroup.lift (u i)
  let q := (QuotientGroup.mk' N).comp raw
  have hker : Subgroup.normalClosure S ≤ q.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨r, hr, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.subset_normalClosure
    change Tendsto (fun i => hsDist (FreeGroup.lift (u i) (FreeGroup.mk r)) 1) L (𝓝 0)
    apply squeeze_zero (fun _ => Real.sqrt_nonneg _) (fun i => rel i r hr)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left Nat.hyperfilter_le_atTop
  let ρ : PresentedGroup S →* ((i : ℕ) → UnitaryAt (d i)) ⧸ N :=
    QuotientGroup.lift _ q hker
  have hN : raw w ∈ N := (QuotientGroup.eq_one_iff _).mp (vanishes d hd ρ)
  have hsub : N ≤ nullSequences d L := Subgroup.normalClosure_le_normal (fun _ hx => hx)
  have hzero : Tendsto (fun i => hsDist (FreeGroup.lift (u i) w) 1) L (𝓝 0) := hsub hN
  have impossible : η ≤ 0 := ge_of_tendsto' hzero separated
  exact (not_le_of_gt positive) impossible

end Green100.WordCompactness

theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1_H2_R1.H1 :=
  Green100.WordCompactness.compactness
