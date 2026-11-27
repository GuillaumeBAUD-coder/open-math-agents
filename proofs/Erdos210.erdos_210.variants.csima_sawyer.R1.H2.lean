import OMAReductions.R_Erdos210_erdos_210_variants_csima_sawyer_R1
import Mathlib.Tactic.Module

/-!
Algebraic form of the four-attachment lemma. At an ordinary point in the
dual arrangement, the two signed boundary coordinates and height determine
the incident sector up to an overall sign. Two triangular cells in the same
sector would force each third normal into the other's signed cone, so the
two third normals are proportional and determine the same line.
See Jonathan Lenchner, IBM Research Report RC24181, Lemma 1.
-/

-- Credit: @dk8827

open EuclideanGeometry Finset
open scoped BigOperators Classical

namespace OMA.OrdinaryAttachment

private abbrev HVec := Fin 3 → ℝ

private def homogeneous (p : ℝ²) : HVec := ![p 0, p 1, 1]

private def height (p q : ℝ²) : HVec →ₗ[ℝ] ℝ where
  toFun v := (q 0 - p 0) * (v 1 - p 1 * v 2) - (q 1 - p 1) * (v 0 - p 0 * v 2)
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem hp_height (p q : ℝ²) : height p q (homogeneous p) = 0 := by
  simp [height, homogeneous]

private theorem hq_height (p q : ℝ²) : height p q (homogeneous q) = 0 := by
  simp [height, homogeneous]
  ring

private theorem point_eq {p q : ℝ²} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem height_ne_zero {p q w : ℝ²} (hpq : p ≠ q)
    (hw : w ∉ line[ℝ, p, q]) : height p q (homogeneous w) ≠ 0 := by
  intro h
  apply hw
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.2
  have hh : (q 0 - p 0) * (w 1 - p 1) = (q 1 - p 1) * (w 0 - p 0) := by
    simpa [height, homogeneous, sub_eq_zero] using h
  by_cases h₀ : p 0 = q 0
  · have h₁ : q 1 - p 1 ≠ 0 := fun hz => hpq (point_eq h₀ (sub_eq_zero.1 hz).symm)
    have hw₀ : w 0 = p 0 := by
      have he : (q 1 - p 1) * (w 0 - p 0) = 0 := by simpa [h₀] using hh.symm
      exact sub_eq_zero.1 ((mul_eq_zero.1 he).resolve_left h₁)
    let t := (w 1 - p 1) / (q 1 - p 1)
    refine ⟨t, point_eq ?_ ?_⟩
    · rw [AffineMap.lineMap_apply_module']
      change t * (q 0 - p 0) + p 0 = w 0
      simp [h₀, hw₀]
    · rw [AffineMap.lineMap_apply_module']
      change ((w 1 - p 1) / (q 1 - p 1)) * (q 1 - p 1) + p 1 = w 1
      rw [div_mul_cancel₀ _ h₁, sub_add_cancel]
  · have h₀' : q 0 - p 0 ≠ 0 := sub_ne_zero.2 (Ne.symm h₀)
    let t := (w 0 - p 0) / (q 0 - p 0)
    refine ⟨t, point_eq ?_ ?_⟩
    · rw [AffineMap.lineMap_apply_module']
      change ((w 0 - p 0) / (q 0 - p 0)) * (q 0 - p 0) + p 0 = w 0
      rw [div_mul_cancel₀ _ h₀', sub_add_cancel]
    · rw [AffineMap.lineMap_apply_module']
      change ((w 0 - p 0) / (q 0 - p 0)) * (q 1 - p 1) + p 1 = w 1
      have hw₁ : ((w 0 - p 0) / (q 0 - p 0)) * (q 1 - p 1) = w 1 - p 1 := by
        apply (mul_right_cancel₀ h₀')
        calc
          _ = (q 1 - p 1) * (w 0 - p 0) := by
            rw [mul_right_comm, div_mul_cancel₀ _ h₀', mul_comm]
          _ = _ := by rw [← hh, mul_comm]
      rw [hw₁, sub_add_cancel]

private theorem pair_coeff {p q : ℝ²} (hpq : p ≠ q) {a b : ℝ}
    (h : a • homogeneous p + b • homogeneous q = 0) : a = 0 ∧ b = 0 := by
  have h2 : a + b = 0 := by simpa [homogeneous] using congrFun h 2
  have key (i : Fin 2) : b * (q i - p i) = 0 := by
    have hi : a * p i + b * q i = 0 := by
      fin_cases i
      · simpa [homogeneous] using congrFun h 0
      · simpa [homogeneous] using congrFun h 1
    linear_combination hi - (p i) * h2
  have hb : b = 0 := by
    by_contra hb
    exact hpq (point_eq ((sub_eq_zero.1 ((mul_eq_zero.1 (key 0)).resolve_left hb)).symm)
      ((sub_eq_zero.1 ((mul_eq_zero.1 (key 1)).resolve_left hb)).symm))
  exact ⟨by simpa [hb] using h2, hb⟩

private theorem sign_cases {a : ℝ} (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith only [ha]
  rcases mul_eq_zero.1 hz with h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (by linarith only [h])

private theorem orient_nonneg {p q w z : ℝ²} {ε δ δ' : ℝ}
    (hδ' : δ' ^ 2 = 1)
    (hsign : (δ' * height p q (homogeneous z)) * (δ * height p q (homogeneous w)) > 0)
    (hex : ∃ a b c : ℝ,
      homogeneous z = a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) :
    ∃ a b c : ℝ, δ' • homogeneous z =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c := by
  obtain ⟨a, b, c, hz, hcone⟩ := hex
  have hheight : height p q (homogeneous z) = c * (δ * height p q (homogeneous w)) := by
    conv_lhs => rw [hz]
    simp [hp_height, hq_height]
  have hcc : 0 < δ' * c := by
    have hs : 0 < (δ' * c) * (δ * height p q (homogeneous w)) ^ 2 := by
      calc
        _ < (δ' * height p q (homogeneous z)) * (δ * height p q (homogeneous w)) := hsign
        _ = _ := by rw [hheight]; ring
    exact pos_of_mul_pos_left hs (sq_nonneg _)
  have hab : 0 ≤ δ' * a ∧ 0 ≤ δ' * b := by
    rcases sign_cases hδ' with rfl | rfl
    · rw [one_mul, one_mul]
      rw [one_mul] at hcc
      rcases hcone with h | h
      · exact ⟨h.1, h.2.1⟩
      · exact (hcc.not_ge h.2.2).elim
    · simp only [neg_mul, one_mul] at hcc ⊢
      rcases hcone with h | h
      · exfalso
        linarith only [hcc, h.2.2]
      · exact ⟨by linarith only [h.1], by linarith only [h.2.1]⟩
  refine ⟨δ' * a, δ' * b, δ' * c, ?_, hab.1, hab.2, hcc⟩
  conv_lhs => rw [hz]
  module


private theorem cones_unique {p q w z : ℝ²} (hpq : p ≠ q)
    {ε δ δ' : ℝ} (hε : ε ≠ 0) (hδ' : δ' ≠ 0)
    (hw : δ * height p q (homogeneous w) ≠ 0)
    (hf : ∃ a b c : ℝ, δ' • homogeneous z =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c)
    (hg : ∃ a b c : ℝ, δ • homogeneous w =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ' • homogeneous z) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c) :
    w = z := by
  obtain ⟨a, b, c, hf, ha, hb, hc⟩ := hf
  obtain ⟨a', b', c', hg, ha', hb', hc'⟩ := hg
  have hzw : δ' * height p q (homogeneous z) = c * (δ * height p q (homogeneous w)) := by
    simpa [hp_height, hq_height] using congrArg (height p q) hf
  have hwz : δ * height p q (homogeneous w) = c' * (δ' * height p q (homogeneous z)) := by
    simpa [hp_height, hq_height] using congrArg (height p q) hg
  rw [hzw] at hwz
  have hcc : c' * c = 1 := by
    apply mul_right_cancel₀ hw
    simpa only [one_mul, mul_assoc] using hwz.symm
  have hsum : δ • homogeneous w =
      (a' + c' * a) • homogeneous p + (b' + c' * b) • (ε • homogeneous q) +
      (c' * c) • (δ • homogeneous w) := by
    calc
      _ = _ := hg
      _ = _ := by
        conv_lhs => rw [hf]
        module
  rw [hcc, one_smul] at hsum
  have hs0 : (a' + c' * a) • homogeneous p + (b' + c' * b) • (ε • homogeneous q) = 0 := by
    simpa using congrArg (fun v : HVec => v - δ • homogeneous w) hsum.symm
  obtain ⟨hsa, hsb⟩ := pair_coeff hpq (by simpa only [smul_smul] using hs0)
  have ha0 : a = 0 := by
    have hz : c' * a = 0 := le_antisymm (by linarith only [hsa, ha']) (mul_nonneg hc'.le ha)
    exact (mul_eq_zero.1 hz).resolve_left hc'.ne'
  have hb0 : b = 0 := by
    have hsb' := (mul_eq_zero.1 hsb).resolve_right hε
    have hz : c' * b = 0 := le_antisymm (by linarith only [hsb', hb']) (mul_nonneg hc'.le hb)
    exact (mul_eq_zero.1 hz).resolve_left hc'.ne'
  simp only [ha0, hb0, zero_smul, zero_add] at hf
  have he : δ' = c * δ := by
    simpa [homogeneous] using congrFun hf 2
  have hcoord (i : Fin 2) : δ' * z i = (c * δ) * w i := by
    fin_cases i
    · simpa [homogeneous, mul_assoc] using congrFun hf 0
    · simpa [homogeneous, mul_assoc] using congrFun hf 1
  have hwz (i : Fin 2) : w i = z i := by
    apply mul_left_cancel₀ hδ'
    rw [hcoord, he]
  exact point_eq (hwz 0) (hwz 1)

private theorem swap_order {s : Finset ℝ²} {p q w : ℝ²} {ε δ : ℝ}
    (hε : ε ^ 2 = 1)
    (h : ∀ z ∈ s, ∃ a b c : ℝ,
      homogeneous z = a • homogeneous q + b • (ε • homogeneous p) + c • (δ • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) :
    ∀ z ∈ s, ∃ a b c : ℝ,
      homogeneous z = a • homogeneous p + b • (ε • homogeneous q) + c • ((ε * δ) • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
  intro z hz
  obtain ⟨a, b, c, he, hs⟩ := h z hz
  rcases sign_cases hε with rfl | rfl
  · exact ⟨b, a, c, by simpa [add_comm] using he, hs.imp
      (fun h => ⟨h.2.1, h.1, h.2.2⟩) (fun h => ⟨h.2.1, h.1, h.2.2⟩)⟩
  · refine ⟨-b, -a, -c, ?_, ?_⟩
    · rw [he]
      module
    · rcases hs with h₀ | h₀
      · exact Or.inr ⟨neg_nonpos.2 h₀.2.1, neg_nonpos.2 h₀.1, neg_nonpos.2 h₀.2.2⟩
      · exact Or.inl ⟨neg_nonneg.2 h₀.2.1, neg_nonneg.2 h₀.1, neg_nonneg.2 h₀.2.2⟩


theorem four_attachments (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²)
    (hL : L ∈ ordinaryLines s) :
    (s.filter (fun w =>
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
              c • (δ • homogeneous w) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)))).card ≤ 4 := by
  classical
  obtain ⟨p, q, hpq, hpqL⟩ := card_eq_two.1 ((mem_ordinaryLines.1 hL).2)
  let W := s.filter (fun w =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
            c • (δ • homogeneous w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)))
  have hmem (x : ℝ²) : x ∈ s ∧ x ∈ L ↔ x = p ∨ x = q := by
    rw [← mem_filter, hpqL]
    simp
  have hpL : p ∈ L := ((hmem p).2 (Or.inl rfl)).2
  have hqL : q ∈ L := ((hmem q).2 (Or.inr rfl)).2
  have hchoice (w : W) : ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ (w : ℝ²) ∉ L ∧
      ∀ z ∈ s, ∃ a b c : ℝ,
        homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
          c • (δ • homogeneous w) ∧
        ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
    obtain ⟨p', hp', q', hq', hn, hp'L, hq'L, hw, ε, δ, hε, hδ, hcone⟩ := (mem_filter.1 w.2).2
    rcases (hmem p').1 ⟨hp', hp'L⟩ with rfl | rfl
    · rcases (hmem q').1 ⟨hq', hq'L⟩ with rfl | rfl
      · exact (hn rfl).elim
      · exact ⟨ε, δ, hε, hδ, hw, hcone⟩
    · rcases (hmem q').1 ⟨hq', hq'L⟩ with rfl | rfl
      · exact ⟨ε, ε * δ, hε, by rw [mul_pow, hε, hδ, one_mul], hw, swap_order hε hcone⟩
      · exact (hn rfl).elim
  choose ε δ hε hδ houtside hcone using hchoice
  let depth (w : W) := δ w * height p q (homogeneous w)
  have depth_ne (w : W) : depth w ≠ 0 := by
    have hd0 : δ w ≠ 0 := by
      intro hd
      simpa [hd] using hδ w
    exact mul_ne_zero hd0
      (height_ne_zero hpq (fun h => houtside w (affineSpan_pair_le_of_mem_of_mem hpL hqL h)))
  let label (w : W) : Bool × Bool := (decide (ε w = 1), decide (0 < depth w))
  have inj : Function.Injective label := by
    intro w z he
    have h₁ : decide (ε w = 1) = decide (ε z = 1) := congrArg Prod.fst he
    have h₂ : decide (0 < depth w) = decide (0 < depth z) := congrArg Prod.snd he
    have heps : ε w = ε z := by
      rcases sign_cases (hε w) with hw | hw <;> rcases sign_cases (hε z) with hz | hz
      · exact hw.trans hz.symm
      · norm_num [hw, hz] at h₁
      · norm_num [hw, hz] at h₁
      · exact hw.trans hz.symm
    have signs : 0 < depth z * depth w := by
      have hequiv : 0 < depth w ↔ 0 < depth z := by simpa using h₂
      rcases lt_or_gt_of_ne (depth_ne w) with hw | hw
      · have hz : depth z < 0 := lt_of_le_of_ne
          (le_of_not_gt (fun hz => hw.not_gt (hequiv.2 hz))) (depth_ne z)
        exact mul_pos_of_neg_of_neg hz hw
      · exact mul_pos (hequiv.1 hw) hw
    have hzS : (z : ℝ²) ∈ s := (mem_filter.1 z.2).1
    have hwS : (w : ℝ²) ∈ s := (mem_filter.1 w.2).1
    have hfor := orient_nonneg (hδ z) signs (hcone w z hzS)
    have hback := orient_nonneg (hδ w) (by simpa [mul_comm] using signs) (hcone z w hwS)
    rw [← heps] at hback
    have hε0 : ε w ≠ 0 := by
      intro h
      simpa [h] using hε w
    have hδ0 : δ z ≠ 0 := by
      intro h
      simpa [h] using hδ z
    exact Subtype.ext (cones_unique hpq hε0 hδ0 (depth_ne w) hfor hback)
  have hcard := Fintype.card_le_of_injective label inj
  change W.card ≤ 4
  simpa using hcard

end OMA.OrdinaryAttachment

theorem OMA.solution : OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.H2 := by
  intro s _ _
  dsimp only
  intro L hL
  exact OMA.OrdinaryAttachment.four_attachments s L hL
