import OMAStatements.S_mo_481234

/-!
Proof of `OMA.S_mo_481234.main` (MathOverflow 481234): an explicit distribution on
`{(x, y, z) ∈ [0,1]³ : x + y + z = 3/2}` with uniform marginals. With `U` uniform on `[0, 1]`, take
`X = U`, `Y = U + 1/2` if `U < 1/2` and `U - 1/2` otherwise, and `Z = 3/2 - X - Y`, which equals
`1 - 2U` on `[0, 1/2)` and `2 - 2U` on `[1/2, 1]`. Each coordinate is uniform: `Y` swaps the two
halves of `[0, 1]` by translations, and `Z` stretches each half onto `[0, 1]` with density `1/2`.
-/

namespace OMA.P_mo_481234

open MeasureTheory OMA.S_mo_481234

open MeasureTheory

/-- The second coordinate: shift `[0,1/2)` up and `[1/2,1]` down by `1/2`. -/
noncomputable def g (u : ℝ) : ℝ := if u < 1 / 2 then u + 1 / 2 else u - 1 / 2

noncomputable def φ (u : ℝ) : ℝ × ℝ × ℝ := (u, g u, 3 / 2 - u - g u)

lemma measurable_g : Measurable g :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_id.add_const _) (measurable_id.sub_const _)

lemma measurable_φ : Measurable φ := by
  unfold φ
  exact measurable_id.prodMk (measurable_g.prodMk ((measurable_const.sub measurable_id).sub measurable_g))

/-- Translating a restricted Lebesgue measure. -/
lemma map_restrict_add (a b c : ℝ) :
    (volume.restrict (Set.Icc a b)).map (· + c) = volume.restrict (Set.Icc (a + c) (b + c)) := by
  have hf : MeasurableEmbedding (· + c : ℝ → ℝ) := (Homeomorph.addRight c).measurableEmbedding
  have h := hf.restrict_map (μ := volume) (Set.Icc (a + c) (b + c))
  rw [map_add_right_eq_self volume c] at h
  have hpre : (· + c : ℝ → ℝ) ⁻¹' Set.Icc (a + c) (b + c) = Set.Icc a b := by
    ext x; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro hx <;> constructor <;>
      linarith [hx.1, hx.2]
  rw [hpre] at h
  exact h.symm

/-- Applying `u ↦ c - 2u` to a restricted Lebesgue measure. -/
lemma map_restrict_affine (a b c : ℝ) :
    (volume.restrict (Set.Icc a b)).map (fun u => c - 2 * u) =
      ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (c - 2 * b) (c - 2 * a)) := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ (-2 : ℝ) (by norm_num)).trans (Homeomorph.addLeft c)
  have he : ∀ u, e u = c - 2 * u := by intro u; simp [e]; ring
  have hfe : (fun u : ℝ => c - 2 * u) = e := by funext u; rw [he]
  have hf : MeasurableEmbedding (fun u : ℝ => c - 2 * u) := by
    rw [hfe]; exact e.measurableEmbedding
  have hvol : volume.map (fun u : ℝ => c - 2 * u) = ENNReal.ofReal (1 / 2) • volume := by
    have h1 : (fun u : ℝ => c - 2 * u) = (fun v => c + v) ∘ (fun u => (-2) * u) := by
      funext u; simp; ring
    rw [h1, ← Measure.map_map (measurable_const_add c) (measurable_const_mul _),
      Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0), Measure.map_smul,
      map_add_left_eq_self volume c]
    norm_num
  have h := hf.restrict_map (μ := volume) (Set.Icc (c - 2 * b) (c - 2 * a))
  rw [hvol, Measure.restrict_smul] at h
  have hpre : (fun u : ℝ => c - 2 * u) ⁻¹' Set.Icc (c - 2 * b) (c - 2 * a) = Set.Icc a b := by
    ext x; simp only [Set.mem_preimage, Set.mem_Icc]; constructor <;> intro hx <;> constructor <;>
      linarith [hx.1, hx.2]
  rw [hpre] at h
  exact h.symm

/-- `[0,1] = [0,1/2] ∪ [1/2,1]`, up to the null overlap. -/
lemma restrict_split :
    volume.restrict (Set.Icc (0 : ℝ) 1) =
      volume.restrict (Set.Icc (0 : ℝ) (1 / 2)) + volume.restrict (Set.Icc (1 / 2 : ℝ) 1) := by
  have hdisj : AEDisjoint volume (Set.Icc (0 : ℝ) (1 / 2)) (Set.Icc (1 / 2 : ℝ) 1) := by
    unfold AEDisjoint
    rw [Set.Icc_inter_Icc]
    norm_num
  rw [← Measure.restrict_union₀ hdisj measurableSet_Icc.nullMeasurableSet]
  congr 1; ext x; simp only [Set.mem_union, Set.mem_Icc]; constructor
  · intro h; by_cases hx : x ≤ 1 / 2
    · exact Or.inl ⟨h.1, hx⟩
    · exact Or.inr ⟨by linarith, h.2⟩
  · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]

lemma ae_ne_half : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 / 2 := by
  rw [ae_iff]; simp

lemma φ_mem (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : φ u ∈ S := by
  obtain ⟨h0, h1⟩ := hu
  simp only [S, φ, g, Set.mem_Icc]
  split_ifs with h
  · refine ⟨⟨h0, h1⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by ring⟩
  · push Not at h
    refine ⟨⟨h0, h1⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by ring⟩

lemma isClosed_S : IsClosed S := by
  have : S =
      (Prod.fst ⁻¹' Set.Icc (0 : ℝ) 1) ∩ ((fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' Set.Icc (0 : ℝ) 1) ∩
        ((fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' Set.Icc (0 : ℝ) 1) ∩
        {p : ℝ × ℝ × ℝ | p.1 + p.2.1 + p.2.2 = 3 / 2} := by
    ext p; simp [S, and_assoc]
  rw [this]
  refine (((isClosed_Icc.preimage continuous_fst).inter
    (isClosed_Icc.preimage (continuous_fst.comp continuous_snd))).inter
    (isClosed_Icc.preimage (continuous_snd.comp continuous_snd))).inter
    (isClosed_eq (by fun_prop) continuous_const)

/-- The second coordinate is uniform. -/
lemma map_g : (volume.restrict (Set.Icc (0 : ℝ) 1)).map g = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  conv_lhs => rw [restrict_split, Measure.map_add _ _ measurable_g]
  have h1 : (volume.restrict (Set.Icc (0 : ℝ) (1 / 2))).map g =
      volume.restrict (Set.Icc (1 / 2 : ℝ) 1) := by
    have hae : g =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (1 / 2))] (· + 1 / 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ae_ne_half]
        with u hu hne
      have hlt : u < 1 / 2 := lt_of_le_of_ne hu.2 hne
      simp only [g, hlt, if_true]
    rw [Measure.map_congr hae, map_restrict_add]
    norm_num
  have h2 : (volume.restrict (Set.Icc (1 / 2 : ℝ) 1)).map g =
      volume.restrict (Set.Icc (0 : ℝ) (1 / 2)) := by
    have hae : g =ᵐ[volume.restrict (Set.Icc (1 / 2 : ℝ) 1)] (· + (-1 / 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have : ¬ u < 1 / 2 := not_lt.mpr hu.1
      simp only [g, this, if_false]; ring
    rw [Measure.map_congr hae, map_restrict_add]
    norm_num
  rw [h1, h2, add_comm, ← restrict_split]

/-- The third coordinate is uniform. -/
lemma map_h :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun u => 3 / 2 - u - g u) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hm : Measurable (fun u : ℝ => 3 / 2 - u - g u) :=
    (measurable_const.sub measurable_id).sub measurable_g
  conv_lhs => rw [restrict_split, Measure.map_add _ _ hm]
  have h1 : (volume.restrict (Set.Icc (0 : ℝ) (1 / 2))).map (fun u => 3 / 2 - u - g u) =
      ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (0 : ℝ) 1) := by
    have hae : (fun u => 3 / 2 - u - g u) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (1 / 2))]
        (fun u => 1 - 2 * u) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ae_ne_half]
        with u hu hne
      have hlt : u < 1 / 2 := lt_of_le_of_ne hu.2 hne
      simp only [g, hlt, if_true]; ring
    rw [Measure.map_congr hae, map_restrict_affine]
    norm_num
  have h2 : (volume.restrict (Set.Icc (1 / 2 : ℝ) 1)).map (fun u => 3 / 2 - u - g u) =
      ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (0 : ℝ) 1) := by
    have hae : (fun u => 3 / 2 - u - g u) =ᵐ[volume.restrict (Set.Icc (1 / 2 : ℝ) 1)]
        (fun u => 2 - 2 * u) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have : ¬ u < 1 / 2 := not_lt.mpr hu.1
      simp only [g, this, if_false]; ring
    rw [Measure.map_congr hae, map_restrict_affine]
    norm_num
  rw [h1, h2, ← add_smul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem solution :
    ∃ ν : Measure (ℝ × ℝ × ℝ), IsProbabilityMeasure ν ∧ ν Sᶜ = 0 ∧
      ν.map (fun p => p.1) = volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      ν.map (fun p => p.2.1) = volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      ν.map (fun p => p.2.2) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine ⟨(volume.restrict (Set.Icc (0 : ℝ) 1)).map φ,
    Measure.isProbabilityMeasure_map measurable_φ.aemeasurable, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_φ isClosed_S.measurableSet.compl,
      Measure.restrict_apply (measurable_φ isClosed_S.measurableSet.compl)]
    apply measure_mono_null _ (measure_empty (μ := volume))
    intro u ⟨hu1, hu2⟩
    exact absurd (φ_mem u hu2) hu1
  · rw [Measure.map_map measurable_fst measurable_φ]
    exact Measure.map_id
  · rw [Measure.map_map (g := fun p : ℝ × ℝ × ℝ => p.2.1) (by fun_prop)
      measurable_φ]
    exact map_g
  · rw [Measure.map_map (g := fun p : ℝ × ℝ × ℝ => p.2.2) (by fun_prop)
      measurable_φ]
    exact map_h

end OMA.P_mo_481234

theorem OMA.solution : type_of% @OMA.S_mo_481234.main := OMA.P_mo_481234.solution
