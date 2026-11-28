import OMAStatements.S_mo_369944
import Mathlib

open Set

open OMA.S_mo_369944

private abbrev ExtensionWitnessInterval := Set.Icc (-1 : ℝ) 1

private theorem linear_term_zero {a b : ℝ}
    (h : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ a * x^2 + b*x) : b = 0 := by
  by_contra hb
  let t := min 1 (|b| / (2 * (|a|+1)))
  have ha : 0 < 2 * (|a|+1) := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos (abs_pos.mpr hb) ha)
  have ht₁ : t ≤ 1 := min_le_left _ _
  have ht₂ : t ≤ |b| / (2 * (|a|+1)) := min_le_right _ _
  have hpos := h t ⟨by linarith,ht₁⟩
  have hneg := h (-t) ⟨by linarith,by linarith⟩
  have hLeft : 0 ≤ (a*t+b)*t := by nlinarith
  have hRight : 0 ≤ (a*t-b)*t := by nlinarith
  have hBL : -a*t ≤ b := by linarith [(mul_nonneg_iff_of_pos_right ht).mp hLeft]
  have hBR : b ≤ a*t := by linarith [(mul_nonneg_iff_of_pos_right ht).mp hRight]
  have hAbs : |b| ≤ a*t := abs_le.mpr ⟨by linarith,hBR⟩
  have hBound := (le_div_iff₀ ha).mp ht₂
  have hAt := mul_le_mul_of_nonneg_right (le_abs_self a) ht.le
  nlinarith [abs_nonneg a, mul_nonneg (abs_nonneg a) ht.le]

private def identityMap : C(ExtensionWitnessInterval,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩

private def squareMap : C(ExtensionWitnessInterval,ℝ) :=
  ⟨fun x => (x.val : ℝ)^2,continuous_subtype_val.pow 2⟩

private noncomputable def quadraticSubspace : Submodule ℝ C(ExtensionWitnessInterval,ℝ) :=
  Submodule.span ℝ {squareMap,identityMap}

private def rightEnd : ExtensionWitnessInterval := ⟨1,by norm_num⟩
private def leftEnd : ExtensionWitnessInterval := ⟨-1,by norm_num⟩

private noncomputable def difference : C(ExtensionWitnessInterval,ℝ) →L[ℝ] ℝ :=
  ContinuousMap.evalCLM ℝ rightEnd - ContinuousMap.evalCLM ℝ leftEnd

theorem OMA.solution : type_of% @OMA.S_mo_369944.main := by
  classical
  let M := quadraticSubspace
  let L := difference.domRestrict M
  have hI : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
  let compact : CompactSpace ExtensionWitnessInterval := isCompact_iff_compactSpace.mp hI
  refine ⟨ExtensionWitnessInterval,inferInstance,compact,M,L,?_,?_⟩
  · intro f hf
    have hMem : f.val ∈ Submodule.span ℝ ({squareMap,identityMap} : Set C(ExtensionWitnessInterval,ℝ)) := f.property
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hMem
    have hb : b = 0 := by
      apply linear_term_zero (a := a)
      intro x hx
      have hfx := hf ⟨x,hx⟩
      rw [← he] at hfx
      simpa [squareMap,identityMap,smul_eq_mul] using hfx
    have hzero : L f = 0 := by
      change difference f.val = 0
      rw [← he,hb,zero_smul,add_zero,map_smul]
      norm_num [difference,squareMap,rightEnd,leftEnd]
    exact hzero.ge
  · rintro ⟨E,hE,hEq⟩
    have hF : squareMap ∈ M := Submodule.subset_span (by simp)
    have hG : identityMap ∈ M := Submodule.subset_span (by simp)
    have hf : E squareMap = 0 := by
      rw [hEq ⟨squareMap,hF⟩]
      change difference squareMap = 0
      norm_num [difference,squareMap,rightEnd,leftEnd]
    have hg : E identityMap = 2 := by
      rw [hEq ⟨identityMap,hG⟩]
      change difference identityMap = 2
      norm_num [difference,identityMap,rightEnd,leftEnd]
    have hUnit : 0 ≤ E 1 := hE 1 (fun x => by simp)
    let r : ℝ := E 1 + 1
    let f : C(ExtensionWitnessInterval,ℝ) := 1 + (r^2) • squareMap - (2*r) • identityMap
    have hNonneg (x : ExtensionWitnessInterval) : 0 ≤ f x := by
      change 0 ≤ (1 : ℝ) + r^2 * x.val^2 - (2*r)*x.val
      nlinarith [sq_nonneg (1-r*x.val)]
    have hBad := hE f hNonneg
    dsimp [f] at hBad
    simp only [map_sub,map_add,map_smul,hf,hg,smul_eq_mul,mul_zero,add_zero] at hBad
    dsimp [r] at hBad
    linarith
