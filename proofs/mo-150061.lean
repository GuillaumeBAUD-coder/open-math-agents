import OMAStatements.S_mo_150061
import Mathlib

open Set Filter
open scoped Topology

open OMA.S_mo_150061

private abbrev HeightInterval := Set.Icc (0 : ℝ) 1
private abbrev OrbitCircle := AddCircle (1 : ℝ)
private abbrev PhaseSpace := HeightInterval × OrbitCircle
private abbrev Shifts := Multiplicative ℝ

private abbrev shiftAction : MulAction Shifts PhaseSpace where
  smul g p := (p.1, (↑((p.1 : ℝ) * Multiplicative.toAdd g) : OrbitCircle) + p.2)
  one_smul p := by
    change (p.1, (↑((p.1 : ℝ) * 0) : OrbitCircle) + p.2) = p
    simp
  mul_smul g h p := by
    change (p.1, (↑((p.1 : ℝ) * (Multiplicative.toAdd g + Multiplicative.toAdd h)) : OrbitCircle) + p.2) =
      (p.1, (↑((p.1 : ℝ) * Multiplicative.toAdd g) : OrbitCircle) +
        ((↑((p.1 : ℝ) * Multiplicative.toAdd h) : OrbitCircle) + p.2))
    rw [mul_add, AddCircle.coe_add, add_assoc]

private theorem continuous_shift (g : Shifts) :
    Continuous (fun p : PhaseSpace => shiftAction.smul g p) := by
  apply continuous_fst.prodMk
  refine ((AddCircle.continuous_mk' (1 : ℝ)).comp ?_).add continuous_snd
  exact (continuous_subtype_val.comp continuous_fst).mul continuous_const

private noncomputable def height (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

private theorem height_pos (n : ℕ) : 0 < height n := by
  unfold height
  positivity

private theorem height_lt_one (n : ℕ) : height n < 1 := by
  apply (div_lt_iff₀ (by positivity)).2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem height_injective : Function.Injective height := by
  intro n m h
  simp only [height, one_div] at h
  have hd := inv_injective h
  exact_mod_cast (show (n : ℝ) = (m : ℝ) by linarith)

private theorem height_tendsto_zero : Tendsto height atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)
  simpa only [one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun (n : ℕ) => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
        tendsto_natCast_atTop_atTop)

private def origin : HeightInterval := ⟨0, by constructor <;> norm_num⟩

private noncomputable def positivePoint (n : ℕ) : HeightInterval :=
  ⟨height n, ⟨(height_pos n).le, (height_lt_one n).le⟩⟩

private theorem positive_fibre_has_limit (t : HeightInterval) (ht : 0 < (t : ℝ)) :
    let _ : MulAction Shifts PhaseSpace := shiftAction
    (t, (0 : OrbitCircle)) ∈ AccumulationOfOrbits Shifts PhaseSpace := by
  let _ : MulAction Shifts PhaseSpace := shiftAction
  let s (n : ℕ) : PhaseSpace := (t, (height n : OrbitCircle))
  refine ⟨(t, 0), s, ?_, ?_, ?_⟩
  · intro n m hnm
    have he : (height n : OrbitCircle) = (height m : OrbitCircle) := congrArg Prod.snd hnm
    have hmem (k : ℕ) : height k ∈ Ico (0 : ℝ) (0 + 1) :=
      ⟨(height_pos k).le, by simpa using height_lt_one k⟩
    exact height_injective ((AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem n) (hmem m)).mp he)
  · intro n
    refine ⟨Multiplicative.ofAdd (height n / (t : ℝ)), ?_⟩
    change (t, (↑((t : ℝ) * (height n / (t : ℝ))) : OrbitCircle) + 0) =
      (t, (height n : OrbitCircle))
    rw [show (t : ℝ) * (height n / (t : ℝ)) = height n by field_simp [ht.ne'], add_zero]
  · have hc : Tendsto (fun n => (height n : OrbitCircle)) atTop (𝓝 (0 : OrbitCircle)) := by
      let f : ℝ → OrbitCircle := fun x => (x : OrbitCircle)
      have hf : Continuous f := AddCircle.continuous_mk' (1 : ℝ)
      have hz : f 0 = 0 := AddCircle.coe_zero (1 : ℝ)
      rw [←hz]
      exact (hf.continuousAt (x := 0)).tendsto.comp height_tendsto_zero
    exact tendsto_const_nhds.prodMk_nhds hc

private theorem origin_fibre_has_no_limit :
    let _ : MulAction Shifts PhaseSpace := shiftAction
    (origin, (0 : OrbitCircle)) ∉ AccumulationOfOrbits Shifts PhaseSpace := by
  let _ : MulAction Shifts PhaseSpace := shiftAction
  change ¬ ((origin, (0 : OrbitCircle)) ∈ AccumulationOfOrbits Shifts PhaseSpace)
  rintro ⟨p, s, hinj, horbit, hs⟩
  have hproj (n : ℕ) : (s n).1 = p.1 := by
    obtain ⟨g,hg⟩ := horbit n
    exact (congrArg Prod.fst hg).symm
  have hc := (continuous_fst.continuousAt (x := (origin,(0 : OrbitCircle)))).tendsto.comp hs
  simp only [Function.comp_def,hproj] at hc
  have hp : p.1 = origin := tendsto_nhds_unique tendsto_const_nhds hc
  have horig : (p.1 : ℝ) = 0 := congrArg Subtype.val hp
  have hall (n : ℕ) : s n = p := by
    obtain ⟨g,hg⟩ := horbit n
    rw [←hg]
    change (p.1, (↑((p.1 : ℝ) * Multiplicative.toAdd g) : OrbitCircle) + p.2) = p
    rw [horig, zero_mul, AddCircle.coe_zero, zero_add]
  exact Nat.zero_ne_one (hinj ((hall 0).trans (hall 1).symm))

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_150061.main) := by
  intro h
  let _ : TopologicalSpace Shifts := ⊥
  let _ : DiscreteTopology Shifts := ⟨rfl⟩
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let _ : MulAction Shifts PhaseSpace := shiftAction
  let _ : ContinuousSMul Shifts PhaseSpace := ⟨
    continuous_prod_of_discrete_left.mpr continuous_shift⟩
  have hx : Tendsto positivePoint atTop (𝓝 origin) :=
    tendsto_subtype_rng.mpr height_tendsto_zero
  have ht : Tendsto (fun n => (positivePoint n, (0 : OrbitCircle))) atTop (𝓝 (origin, (0 : OrbitCircle))) :=
    hx.prodMk_nhds tendsto_const_nhds
  apply origin_fibre_has_no_limit
  exact (h Shifts PhaseSpace).mem_of_tendsto ht
    (Eventually.of_forall fun n => positive_fibre_has_limit (positivePoint n) (height_pos n))
