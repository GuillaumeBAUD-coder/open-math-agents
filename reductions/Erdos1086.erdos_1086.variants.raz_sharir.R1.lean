import FormalConjectures.ErdosProblems.«1086»
import Mathlib

/-!
Reduction of the equal-area triangle bound to the counting estimates in Section 2 of
O. E. Raz and M. Sharir, The number of unit-area triangles in the plane: theme and variations,
https://arxiv.org/abs/1501.00379.

H1 is the weighted line-count estimate with threshold `k = n^(2/9)`.
H2 is the bound on pairs of directed segments that have the same offset line.
-/

open Filter Asymptotics
open scoped EuclideanGeometry Classical

namespace OMA.R_Erdos1086_erdos_1086_variants_raz_sharir_R1

open Erdos1086 EuclideanGeometry

private noncomputable def normalizeArea (a : ℝ) (ha : a ≠ 0) : ℝ² ≃ ℝ² where
  toFun p := !₂[p 0 / a, p 1]
  invFun p := !₂[p 0 * a, p 1]
  left_inv p := by
    ext i
    fin_cases i <;> simp [ha]
  right_inv p := by
    ext i
    fin_cases i <;> simp [ha]

private lemma normalizeArea_formula {a : ℝ} (ha : a ≠ 0) (p q r : ℝ²) :
    triangle_area (normalizeArea a ha p) (normalizeArea a ha q) (normalizeArea a ha r) =
      triangle_area p q r / a := by
  rw [triangle_area_eq_det, triangle_area_eq_det]
  simp [normalizeArea, Matrix.det_fin_three]
  field_simp

private lemma count_normalizeArea (P : Finset ℝ²) {a : ℝ} (ha : 0 < a) :
    triangleAreaCount (P.map (normalizeArea a ha.ne').toEmbedding) 1 = triangleAreaCount P a := by
  classical
  let e := (normalizeArea a ha.ne').toEmbedding
  change triangleAreaCount (P.map e) 1 = triangleAreaCount P a
  unfold triangleAreaCount
  rw [Finset.powersetCard_map, Finset.filter_map, Finset.card_map]
  congr 1
  ext T
  simp only [Finset.mem_filter, Function.comp_apply]
  apply and_congr_right
  intro _
  have harea (p q r : ℝ²) : |triangle_area (e p) (e q) (e r)| = 1 ↔ |triangle_area p q r| = a := by
    change |triangle_area (normalizeArea a ha.ne' p) (normalizeArea a ha.ne' q)
      (normalizeArea a ha.ne' r)| = 1 ↔ _
    rw [normalizeArea_formula, abs_div, abs_of_pos ha, div_eq_iff ha.ne', one_mul]
  constructor
  · rintro ⟨p, q, r, hpqr, h⟩
    let f := normalizeArea a ha.ne'
    have hem (x : ℝ²) : e (f.symm x) = x := f.apply_symm_apply x
    refine ⟨f.symm p, f.symm q, f.symm r, ?_, ?_⟩
    · apply Finset.map_injective e
      change T.map e = _ at hpqr
      simpa only [Finset.map_insert, Finset.map_singleton, hem] using hpqr
    · apply (harea _ _ _).1
      simpa only [hem] using h
  · rintro ⟨p, q, r, rfl, h⟩
    exact ⟨e p, e q, e r, by simp, (harea _ _ _).2 h⟩

private lemma combine_estimates {n q t C₁ C₂ : ℝ} (hn : 0 < n)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (htri : t ≤ C₁ * (n ^ (20 / 9 : ℝ) + n ^ (8 / 9 : ℝ) * Real.sqrt q))
    (hquad : q ≤ C₂ * n ^ (8 / 3 : ℝ)) :
    t ≤ C₁ * (1 + Real.sqrt C₂) * n ^ (20 / 9 : ℝ) := by
  have hs := Real.sqrt_le_sqrt hquad
  rw [Real.sqrt_mul hC₂, Real.sqrt_eq_rpow (n ^ (8 / 3 : ℝ)), ← Real.rpow_mul hn.le] at hs
  have hterm : n ^ (8 / 9 : ℝ) * Real.sqrt q ≤ Real.sqrt C₂ * n ^ (20 / 9 : ℝ) := by
    calc
      _ ≤ n ^ (8 / 9 : ℝ) * (Real.sqrt C₂ * n ^ ((8 / 3 : ℝ) * (1 / 2))) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hn]; norm_num
  calc
    _ ≤ C₁ * (n ^ (20 / 9 : ℝ) + n ^ (8 / 9 : ℝ) * Real.sqrt q) := htri
    _ ≤ C₁ * (n ^ (20 / 9 : ℝ) + Real.sqrt C₂ * n ^ (20 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm) hC₁
    _ = _ := by ring

def H1 : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℝ², 16 ≤ P.card →
  let S := (P ×ˢ P).filter fun s ↦ s.1 ≠ s.2 ∧
    ((P.filter fun x ↦ triangle_area s.1 s.2 x = 0).card : ℝ) ≤ Real.sqrt P.card
  let offset (s : ℝ² × ℝ²) : Set ℝ² := {x | triangle_area s.1 s.2 x = 1}
  let Q := (S ×ˢ S).filter fun st ↦
    let L := offset st.1
    let m := ((P.filter fun x ↦ x ∈ L).card : ℝ)
    L = offset st.2 ∧ (P.card : ℝ) ^ (2 / 9 : ℝ) ≤ m ∧
      m ≤ P.card / (P.card : ℝ) ^ (2 / 9 : ℝ)
  (triangleAreaCount P 1 : ℝ) ≤ C * ((P.card : ℝ) ^ (20 / 9 : ℝ) +
    (P.card : ℝ) ^ (8 / 9 : ℝ) * Real.sqrt Q.card)

def H2 : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℝ², 16 ≤ P.card →
  let S := (P ×ˢ P).filter fun s ↦ s.1 ≠ s.2 ∧
    ((P.filter fun x ↦ triangle_area s.1 s.2 x = 0).card : ℝ) ≤ Real.sqrt P.card
  let offset (s : ℝ² × ℝ²) : Set ℝ² := {x | triangle_area s.1 s.2 x = 1}
  let Q := (S ×ˢ S).filter fun st ↦
    let L := offset st.1
    let m := ((P.filter fun x ↦ x ∈ L).card : ℝ)
    L = offset st.2 ∧ (P.card : ℝ) ^ (2 / 9 : ℝ) ≤ m ∧
      m ≤ P.card / (P.card : ℝ) ^ (2 / 9 : ℝ)
  (Q.card : ℝ) ≤ C * (P.card : ℝ) ^ (8 / 3 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos1086.erdos_1086.variants.raz_sharir := by
  intro h1 h2
  obtain ⟨C₁, hC₁, htri⟩ := h1
  obtain ⟨C₂, hC₂, hquad⟩ := h2
  refine Asymptotics.isBigO_iff.mpr ⟨C₁ * (1 + Real.sqrt C₂), ?_⟩
  filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn
  have hn₀ : 0 ≤ (n : ℝ) := by positivity
  have hp : 0 ≤ (n : ℝ) ^ (20 / 9 : ℝ) := Real.rpow_nonneg hn₀ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs, abs_of_nonneg hp]
  have hbound : ∀ (P : Finset ℝ²), P.card = n →
      (triangleAreaCount P 1 : ℝ) ≤ C₁ * (1 + Real.sqrt C₂) * (n : ℝ) ^ (20 / 9 : ℝ) := by
    intro P hP
    have hPn : 16 ≤ P.card := by simpa only [hP] using hn
    have hpos : 0 < (P.card : ℝ) := by exact_mod_cast (show 0 < P.card by omega)
    simpa only [hP] using combine_estimates hpos hC₁ hC₂ (htri P hPn) (hquad P hPn)
  have hb : 0 ≤ C₁ * (1 + Real.sqrt C₂) * (n : ℝ) ^ (20 / 9 : ℝ) := by positivity
  rw [← Nat.le_floor_iff hb]
  unfold g
  apply csSup_le'
  rintro m ⟨P, a, hP, ha, rfl⟩
  rw [Nat.le_floor_iff hb, ← count_normalizeArea P ha]
  exact hbound _ (by simpa using hP)

end OMA.R_Erdos1086_erdos_1086_variants_raz_sharir_R1
