import OMAStatements.S_mo_253925

namespace OMA.P_mo_253925

open OMA.S_mo_253925 Set

private lemma slope_le_of_concave {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G)
    {u a v : ℝ} (hu : u < a) (hv : a < v) :
    (G v - G a) / (v - a) ≤ (G a - G u) / (a - u) := by
  have h1 : 0 < a - u := sub_pos.mpr hu
  have h2 : 0 < v - a := sub_pos.mpr hv
  have h3 : 0 < v - u := by linarith
  have hw1 : 0 ≤ (v - a) / (v - u) := div_nonneg h2.le h3.le
  have hw2 : 0 ≤ (a - u) / (v - u) := div_nonneg h1.le h3.le
  have hsum : (v - a) / (v - u) + (a - u) / (v - u) = 1 := by
    rw [← add_div]
    have : v - a + (a - u) = v - u := by ring
    rw [this, div_self h3.ne']
  have hcomb : (v - a) / (v - u) * u + (a - u) / (v - u) * v = a := by
    field_simp [h3.ne']
    ring
  have hconc := hG.2 (mem_univ u) (mem_univ v) hw1 hw2 hsum
  simp only [smul_eq_mul] at hconc
  rw [hcomb] at hconc
  rw [div_le_div_iff₀ h2 h1]
  have hmul : ((v - a) / (v - u) * G u + (a - u) / (v - u) * G v) * (v - u) ≤ G a * (v - u) :=
    mul_le_mul_of_nonneg_right hconc h3.le
  have hlhs : ((v - a) / (v - u) * G u + (a - u) / (v - u) * G v) * (v - u) =
      (v - a) * G u + (a - u) * G v := by
    field_simp [h3.ne']
  rw [hlhs] at hmul
  nlinarith

private lemma exists_supergradient_right {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) (a : ℝ) :
    let s := sSup {r : ℝ | ∃ v : ℝ, a < v ∧ r = (G v - G a) / (v - a)}
    (∀ y : ℝ, G y ≤ G a + s * (y - a)) ∧
      (∀ v : ℝ, a < v → (G v - G a) / (v - a) ≤ s) := by
  intro s
  set S : Set ℝ := {r : ℝ | ∃ v : ℝ, a < v ∧ r = (G v - G a) / (v - a)}
  have hne : S.Nonempty := ⟨(G (a + 1) - G a) / (a + 1 - a), a + 1, by linarith, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨(G a - G (a - 1)) / (a - (a - 1)), ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact slope_le_of_concave hG (by linarith) hv
  have hright : ∀ v : ℝ, a < v → (G v - G a) / (v - a) ≤ s := by
    intro v hv
    exact le_csSup hbdd ⟨v, hv, rfl⟩
  refine ⟨?_, hright⟩
  intro y
  rcases lt_trichotomy y a with hlt | rfl | hgt
  · have hsle : s ≤ (G a - G y) / (a - y) := by
      refine csSup_le hne ?_
      rintro r ⟨v, hv, rfl⟩
      exact slope_le_of_concave hG hlt hv
    have hpos : 0 < a - y := sub_pos.mpr hlt
    have hmul := mul_le_mul_of_nonneg_right hsle hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at hmul
    linarith
  · simp
  · have hpos : 0 < y - a := sub_pos.mpr hgt
    have hle := hright y hgt
    have hmul := mul_le_mul_of_nonneg_right hle hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at hmul
    linarith

private lemma exists_supergradient_left {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) (a : ℝ) :
    let s := sInf {r : ℝ | ∃ u : ℝ, u < a ∧ r = (G a - G u) / (a - u)}
    (∀ y : ℝ, G y ≤ G a + s * (y - a)) ∧
      (∀ u : ℝ, u < a → s ≤ (G a - G u) / (a - u)) := by
  intro s
  set S : Set ℝ := {r : ℝ | ∃ u : ℝ, u < a ∧ r = (G a - G u) / (a - u)}
  have hne : S.Nonempty := ⟨(G a - G (a - 1)) / (a - (a - 1)), a - 1, by linarith, rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨(G (a + 1) - G a) / (a + 1 - a), ?_⟩
    rintro r ⟨u, hu, rfl⟩
    exact slope_le_of_concave hG hu (by linarith)
  have hleft : ∀ u : ℝ, u < a → s ≤ (G a - G u) / (a - u) := by
    intro u hu
    exact csInf_le hbdd ⟨u, hu, rfl⟩
  refine ⟨?_, hleft⟩
  intro y
  rcases lt_trichotomy y a with hlt | rfl | hgt
  · have hpos : 0 < a - y := sub_pos.mpr hlt
    have hle := hleft y hlt
    have hmul := mul_le_mul_of_nonneg_right hle hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at hmul
    linarith
  · simp
  · have hsge : (G y - G a) / (y - a) ≤ s := by
      refine le_csInf hne ?_
      rintro r ⟨u, hu, rfl⟩
      exact slope_le_of_concave hG hu hgt
    have hpos : 0 < y - a := sub_pos.mpr hgt
    have hmul := mul_le_mul_of_nonneg_right hsge hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at hmul
    linarith

private lemma concave_continuous {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) : Continuous G := by
  have hconv : ConvexOn ℝ Set.univ (-G) := hG.neg
  have hcont : ContinuousOn (-G) Set.univ := hconv.continuousOn isOpen_univ
  have hcont' : Continuous (-G) := continuousOn_univ.mp hcont
  have hcont'' : Continuous (-(-G)) := hcont'.neg
  rwa [neg_neg] at hcont''

private lemma geps_attained {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℝ) :
    ∃ xstar ∈ Set.Icc (x - ε) (x + ε),
      Geps G ε x = G xstar ∧ ∀ z ∈ Set.Icc (x - ε) (x + ε), G z ≤ G xstar := by
  have hne : (Set.Icc (x - ε) (x + ε)).Nonempty := ⟨x, by linarith, by linarith⟩
  have hcont : ContinuousOn G (Set.Icc (x - ε) (x + ε)) := (concave_continuous hG).continuousOn
  obtain ⟨xstar, hxstar_mem, hxstar_max⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨xstar, hxstar_mem, ?_, hxstar_max⟩
  unfold Geps
  apply le_antisymm
  · refine csSup_le (hne.image G) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hxstar_max hz
  · refine le_csSup ?_ ⟨xstar, hxstar_mem, rfl⟩
    exact ⟨G xstar, fun _ ⟨z, hz, hzx⟩ => hzx ▸ hxstar_max hz⟩

private lemma exists_h_at {G : ℝ → ℝ} (hG : ConcaveOn ℝ Set.univ G) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℝ) :
    ∃ h : ℝ, ∀ y : ℝ, Geps G ε x + h * (y - x) - ε * |h| ≥ G y := by
  obtain ⟨xstar, hxstar_mem, hGeps, hmax⟩ := geps_attained hG hε x
  by_cases hglob : ∀ y : ℝ, G y ≤ G xstar
  · refine ⟨0, fun y => ?_⟩
    rw [hGeps]
    simpa using hglob y
  · push Not at hglob
    obtain ⟨y0, hy0⟩ := hglob
    have hnotmem : y0 ∉ Set.Icc (x - ε) (x + ε) := fun hm => not_lt.mpr (hmax y0 hm) hy0
    simp only [Set.mem_Icc, not_and_or, not_le] at hnotmem
    rcases hnotmem with hy0_lt | hy0_gt
    · -- y0 < x - ε, so xstar must be x - ε
      have hxstar_eq : xstar = x - ε := by
        by_contra hne
        have hlt : x - ε < xstar := lt_of_le_of_ne hxstar_mem.1 (Ne.symm hne)
        have h1 : 0 < xstar - (x - ε) := sub_pos.mpr hlt
        have h2 : 0 < (x - ε) - y0 := sub_pos.mpr hy0_lt
        have h3 : 0 < xstar - y0 := by linarith
        have hw1 : 0 ≤ (xstar - (x - ε)) / (xstar - y0) := div_nonneg h1.le h3.le
        have hw2 : 0 ≤ ((x - ε) - y0) / (xstar - y0) := div_nonneg h2.le h3.le
        have hsum : (xstar - (x - ε)) / (xstar - y0) + ((x - ε) - y0) / (xstar - y0) = 1 := by
          rw [← add_div]
          have : xstar - (x - ε) + ((x - ε) - y0) = xstar - y0 := by ring
          rw [this, div_self h3.ne']
        have hcomb :
            (xstar - (x - ε)) / (xstar - y0) * y0 +
              ((x - ε) - y0) / (xstar - y0) * xstar = x - ε := by
          field_simp [h3.ne']
          ring
        have hconc := hG.2 (mem_univ y0) (mem_univ xstar) hw1 hw2 hsum
        simp only [smul_eq_mul] at hconc
        rw [hcomb] at hconc
        have hle_end : G (x - ε) ≤ G xstar := hmax (x - ε) ⟨le_rfl, by linarith⟩
        have hw1_pos : 0 < (xstar - (x - ε)) / (xstar - y0) := div_pos h1 h3
        have hstrict :
            G xstar < (xstar - (x - ε)) / (xstar - y0) * G y0 +
              ((x - ε) - y0) / (xstar - y0) * G xstar := by
          have : (xstar - (x - ε)) / (xstar - y0) * G xstar +
              ((x - ε) - y0) / (xstar - y0) * G xstar = G xstar := by
            rw [← add_mul, hsum, one_mul]
          linarith [mul_lt_mul_of_pos_left hy0 hw1_pos]
        linarith
      obtain ⟨hsup, hleft⟩ := exists_supergradient_left hG (x - ε)
      set s := sInf {r : ℝ | ∃ u : ℝ, u < x - ε ∧ r = (G (x - ε) - G u) / (x - ε - u)}
      have hs_neg : s < 0 := by
        have hle := hleft y0 hy0_lt
        have hnum : G (x - ε) - G y0 < 0 := by rw [← hxstar_eq]; linarith
        have hden : 0 < x - ε - y0 := sub_pos.mpr hy0_lt
        exact lt_of_le_of_lt hle (div_neg_of_neg_of_pos hnum hden)
      refine ⟨s, fun y => ?_⟩
      have hy := hsup y
      rw [hGeps, hxstar_eq, abs_of_neg hs_neg]
      linarith
    · -- x + ε < y0, so xstar must be x + ε
      have hxstar_eq : xstar = x + ε := by
        by_contra hne
        have hlt : xstar < x + ε := lt_of_le_of_ne hxstar_mem.2 hne
        have h1 : 0 < y0 - (x + ε) := sub_pos.mpr hy0_gt
        have h2 : 0 < (x + ε) - xstar := sub_pos.mpr hlt
        have h3 : 0 < y0 - xstar := by linarith
        have hw1 : 0 ≤ (y0 - (x + ε)) / (y0 - xstar) := div_nonneg h1.le h3.le
        have hw2 : 0 ≤ ((x + ε) - xstar) / (y0 - xstar) := div_nonneg h2.le h3.le
        have hsum : (y0 - (x + ε)) / (y0 - xstar) + ((x + ε) - xstar) / (y0 - xstar) = 1 := by
          rw [← add_div]
          have : y0 - (x + ε) + ((x + ε) - xstar) = y0 - xstar := by ring
          rw [this, div_self h3.ne']
        have hcomb :
            (y0 - (x + ε)) / (y0 - xstar) * xstar +
              ((x + ε) - xstar) / (y0 - xstar) * y0 = x + ε := by
          field_simp [h3.ne']
          ring
        have hconc := hG.2 (mem_univ xstar) (mem_univ y0) hw1 hw2 hsum
        simp only [smul_eq_mul] at hconc
        rw [hcomb] at hconc
        have hle_end : G (x + ε) ≤ G xstar := hmax (x + ε) ⟨by linarith, le_rfl⟩
        have hw2_pos : 0 < ((x + ε) - xstar) / (y0 - xstar) := div_pos h2 h3
        have hstrict :
            G xstar < (y0 - (x + ε)) / (y0 - xstar) * G xstar +
              ((x + ε) - xstar) / (y0 - xstar) * G y0 := by
          have : (y0 - (x + ε)) / (y0 - xstar) * G xstar +
              ((x + ε) - xstar) / (y0 - xstar) * G xstar = G xstar := by
            rw [← add_mul, hsum, one_mul]
          linarith [mul_lt_mul_of_pos_left hy0 hw2_pos]
        linarith
      obtain ⟨hsup, hright⟩ := exists_supergradient_right hG (x + ε)
      set s := sSup {r : ℝ | ∃ v : ℝ, x + ε < v ∧ r = (G v - G (x + ε)) / (v - (x + ε))}
      have hs_pos : 0 < s := by
        have hge := hright y0 hy0_gt
        have hnum : 0 < G y0 - G (x + ε) := by rw [← hxstar_eq]; linarith
        have hden : 0 < y0 - (x + ε) := sub_pos.mpr hy0_gt
        exact lt_of_lt_of_le (div_pos hnum hden) hge
      refine ⟨s, fun y => ?_⟩
      have hy := hsup y
      rw [hGeps, hxstar_eq, abs_of_pos hs_pos]
      linarith

end OMA.P_mo_253925

theorem OMA.solution : type_of% @OMA.S_mo_253925.main := by
  intro G ε hG hε
  choose h hh using fun x => OMA.P_mo_253925.exists_h_at hG hε x
  exact ⟨h, hh⟩
