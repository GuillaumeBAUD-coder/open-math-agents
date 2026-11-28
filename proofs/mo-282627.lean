import OMAStatements.S_mo_282627

open MeasureTheory Metric Set
open scoped ENNReal

namespace BallTransport

open OMA.S_mo_282627

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma ball_volume_ne_zero {n : ℕ} {r : ℝ} (hr : 0 < r) :
    volume (ball (0 : Space n) r) ≠ 0 :=
  (measure_ball_pos volume 0 hr).ne'

lemma uniform_ball_univ {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (uniform (ball (0 : Space n) r)) univ = 1 := by
  rw [uniform, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    ENNReal.inv_mul_cancel (ball_volume_ne_zero hr) measure_ball_lt_top.ne]

lemma map_uniform_ball {n : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (uniform (ball (0 : Space n) R)).map (fun x ↦ (r / R) • x) = uniform (ball (0 : Space n) r) := by
  let c := r / R
  let T := fun x : Space n ↦ c • x
  let k := ENNReal.ofReal |(c ^ Module.finrank ℝ (Space n))⁻¹|
  have hc : 0 < c := div_pos hr hR
  have hT : Measurable T := measurable_const_smul _
  have hk0 : k ≠ 0 := by dsimp [k]; positivity
  have hkT : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hpre : T ⁻¹' ball 0 r = ball 0 R := by
    ext x
    simp only [mem_preimage, T, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    change r / R * ‖x‖ < r ↔ ‖x‖ < R
    rw [div_mul_eq_mul_div, div_lt_iff₀ hR, mul_lt_mul_iff_right₀ hr]
  have hraw : ((volume : Measure (Space n)).restrict (ball 0 R)).map T =
      k • (volume : Measure (Space n)).restrict (ball 0 r) := by
    rw [← hpre, ← Measure.restrict_map hT measurableSet_ball]
    change ((volume : Measure (Space n)).map (c • ·)).restrict (ball 0 r) = _
    rw [Measure.map_addHaar_smul volume hc.ne', Measure.restrict_smul]
  have hvol : volume (ball (0 : Space n) R) = k * volume (ball (0 : Space n) r) := by
    have h := congrArg (fun μ : Measure (Space n) ↦ μ univ) hraw
    simpa only [Measure.map_apply hT MeasurableSet.univ, preimage_univ,
      Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using h
  change (uniform (ball (0 : Space n) R)).map T = uniform (ball (0 : Space n) r)
  rw [uniform, uniform, Measure.map_smul, hraw, smul_smul]
  congr 1
  rw [hvol, ENNReal.mul_inv (Or.inl hk0) (Or.inl hkT)]
  calc
    _ = (k⁻¹ * k) * (volume (ball (0 : Space n) r))⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hk0 hkT, one_mul]

lemma ball_moment_le {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) {R : ℝ}
    (hvol : volume A = volume (ball (0 : Space n) R)) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ x in ball (0 : Space n) R, ‖x‖ₑ ^ s ∂volume) ≤ ∫⁻ x in A, ‖x‖ₑ ^ s ∂volume := by
  let B := ball (0 : Space n) R
  let f : Space n → ℝ≥0∞ := fun x ↦ ‖x‖ₑ ^ s
  let v : Measure (Space n) := volume
  let q := ENNReal.ofReal R ^ s
  have hv : v (B ∩ A) ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top)
  have hd : v (B \ A) = v (A \ B) := by
    have hb := measure_inter_add_sdiff (μ := v) B hA
    have ha := measure_inter_add_sdiff (μ := v) A (measurableSet_ball (x := (0 : Space n)) (ε := R))
    change v (A ∩ B) + v (A \ B) = v A at ha
    have heq : v A = v B := hvol
    rw [inter_comm A B, heq, ← hb] at ha
    exact ((ENNReal.add_right_inj hv).mp ha).symm
  have h1 : (∫⁻ x in B \ A, f x ∂v) ≤ q * v (B \ A) := by
    rw [← Measure.restrict_apply_univ (μ := v) (s := B \ A), ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := v) (measurableSet_ball.diff hA)] with x hx
    have hn : ‖x‖ ≤ R := (mem_ball_zero_iff.mp hx.1).le
    exact ENNReal.rpow_le_rpow (by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hn) hs
  have h2 : q * v (A \ B) ≤ ∫⁻ x in A \ B, f x ∂v := by
    rw [← Measure.restrict_apply_univ (μ := v) (s := A \ B), ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := v) (hA.diff measurableSet_ball)] with x hx
    have hn : R ≤ ‖x‖ := le_of_not_gt (fun h ↦ hx.2 (mem_ball_zero_iff.mpr h))
    exact ENNReal.rpow_le_rpow (by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hn) hs
  change (∫⁻ x in B, f x ∂v) ≤ ∫⁻ x in A, f x ∂v
  rw [← lintegral_inter_add_sdiff f B hA, ← lintegral_inter_add_sdiff f A measurableSet_ball,
    inter_comm A B]
  exact add_le_add_right (h1.trans (hd ▸ h2)) _

lemma ball_norm_le {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) {R : ℝ}
    (hvol : volume A = volume (ball (0 : Space n) R)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    eLpNorm id p (uniform (ball (0 : Space n) R)) ≤ eLpNorm id p (uniform A) := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, uniform, lintegral_smul_measure,
    smul_eq_mul, id, hvol]
  exact ENNReal.rpow_le_rpow
    (mul_le_mul_right (ball_moment_le hA hvol ENNReal.toReal_nonneg) _)
    (by positivity)

lemma ball_norm_finite {n : ℕ} {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    eLpNorm id p (uniform (ball (0 : Space n) r)) ≠ ∞ := by
  have hbound : ∀ᵐ x ∂uniform (ball (0 : Space n) r), ‖id x‖ ≤ r := by
    have ha : uniform (ball (0 : Space n) r) ≪ volume.restrict (ball (0 : Space n) r) := by
      unfold uniform
      exact Measure.smul_absolutelyContinuous
    exact ha.ae_le (ae_restrict_mem (μ := (volume : Measure (Space n))) measurableSet_ball
      |>.mono (fun _ hx ↦ (mem_ball_zero_iff.mp hx).le))
  have h := eLpNorm_le_of_ae_bound (p := p) hbound
  rw [uniform_ball_univ hr, ENNReal.one_rpow, one_mul] at h
  exact ne_of_lt (h.trans_lt ENNReal.ofReal_lt_top)

lemma small_ball_norm {n : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (p : ℝ≥0∞) :
    eLpNorm id p (uniform (ball (0 : Space n) r)) =
      ENNReal.ofReal (r / R) * eLpNorm id p (uniform (ball (0 : Space n) R)) := by
  rw [← map_uniform_ball hr hR, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  change eLpNorm ((r / R) • (id : Space n → (Space n))) p _ = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (div_nonneg hr.le hR.le)]

lemma ball_cost_upper {n : ℕ} {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) (p : ℝ≥0∞) :
    wasserstein p (uniform (ball (0 : Space n) R)) (uniform (ball (0 : Space n) r)) ≤
      ENNReal.ofReal (1 - r / R) * eLpNorm id p (uniform (ball (0 : Space n) R)) := by
  let T : Space n → Space n × Space n := fun x ↦ (x, (r / R) • x)
  let π := (uniform (ball (0 : Space n) R)).map T
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hc : IsCoupling (uniform (ball (0 : Space n) R)) (uniform (ball (0 : Space n) r)) π := by
    constructor
    · dsimp only [π]
      rw [Measure.map_map measurable_fst hT]
      exact Measure.map_id
    · dsimp only [π]
      rw [Measure.map_map measurable_snd hT]
      exact map_uniform_ball hr (hr.trans_le hle)
  unfold wasserstein
  refine (iInf_le _ ⟨π, hc⟩).trans_eq ?_
  change eLpNorm (fun z : Space n × Space n ↦ z.1 - z.2) p π = _
  dsimp only [π]
  rw [eLpNorm_map_measure (by fun_prop) hT.aemeasurable]
  have heq : (fun z : Space n × (Space n) ↦ z.1 - z.2) ∘ T = (1 - r / R) • (id : Space n → (Space n)) := by
    funext x
    simp only [Function.comp_apply, T, Pi.smul_apply, id, sub_smul, one_smul]
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal
    (sub_nonneg.mpr ((div_le_one (hr.trans_le hle)).mpr hle))]

lemma ball_cost_lower {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) {r R : ℝ}
    (hr : 0 < r) (hle : r ≤ R) (hvol : volume A = volume (ball (0 : Space n) R))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    ENNReal.ofReal (1 - r / R) * eLpNorm id p (uniform (ball (0 : Space n) R)) ≤
      wasserstein p (uniform A) (uniform (ball (0 : Space n) r)) := by
  have hR := hr.trans_le hle
  unfold wasserstein
  apply le_iInf
  rintro ⟨π, hπ₁, hπ₂⟩
  have hf : eLpNorm (Prod.fst : Space n × (Space n) → (Space n)) p π = eLpNorm id p (uniform A) := by
    rw [← hπ₁, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
    rfl
  have hg : eLpNorm (Prod.snd : Space n × (Space n) → (Space n)) p π =
      eLpNorm id p (uniform (ball (0 : Space n) r)) := by
    rw [← hπ₂, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
    rfl
  have hM := eLpNorm_add_le (μ := π) (p := p) (f := fun z : Space n × (Space n) ↦ z.1 - z.2)
    (g := Prod.snd) (by fun_prop) (by fun_prop) hp
  have hadd : (fun z : Space n × (Space n) ↦ z.1 - z.2) + Prod.snd = Prod.fst := by
    funext z
    exact sub_add_cancel _ _
  rw [hadd, hf, hg] at hM
  apply (ENNReal.add_le_add_iff_right (ball_norm_finite hr p)).mp
  have hsplit : ENNReal.ofReal (1 - r / R) + ENNReal.ofReal (r / R) = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr ((div_le_one hR).mpr hle))
      (div_nonneg hr.le hR.le)]
    simp
  calc
    _ = eLpNorm id p (uniform (ball (0 : Space n) R)) := by
      rw [small_ball_norm hr hR p, ← add_mul, hsplit, one_mul]
    _ ≤ _ := (ball_norm_le hA hvol hp hpt).trans hM

end BallTransport

theorem OMA.solution : type_of% @OMA.S_mo_282627.main := by
  intro n p r R _ hp hpt hr hle A hA hvol
  exact (BallTransport.ball_cost_upper (n := n) hr hle p).trans
    (BallTransport.ball_cost_lower hA hr hle hvol hp hpt)
