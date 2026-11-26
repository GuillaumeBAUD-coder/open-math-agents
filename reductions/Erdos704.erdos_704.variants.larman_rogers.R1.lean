import FormalConjectures.ErdosProblems.«704»

/-! Separate the geometric construction of a large independent set on a finite
periodic grid from the covering estimate for translates in a finite group.
The strategy follows Prosanov, https://arxiv.org/abs/1610.02846. -/

-- Reduction Erdos704.erdos_704.variants.larman_rogers.R1 of Erdős Problem 704 — larman rogers
-- Credit: @dk8827
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos704_erdos_704_variants_larman_rogers_R1

open Filter Erdos704 SimpleGraph
open scoped Topology

/-- A discretization in which every translate of the same large set lifts to a
unit-distance-free set. The logarithm bounds the size of the discretization. -/
def H1 : Prop :=
  ∀ D > (3 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A)
      (project : EuclideanSpace ℝ (Fin n) → A) (S : Finset A),
      S.Nonempty ∧
      Real.log (Fintype.card A : ℝ) ≤ (n : ℝ) ^ 3 ∧
      (Fintype.card A : ℝ) / S.card ≤ D ^ n ∧
      ∀ (t : A) (x y : EuclideanSpace ℝ (Fin n)),
        project x - t ∈ S → project y - t ∈ S → dist x y ≠ 1

/-- A finite-group covering bound with the usual logarithmic loss. -/
def H2 : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (S : Finset A), S.Nonempty →
    ∃ T : Finset A,
      (T.card : ℝ) ≤
        1 + (1 + Real.log (Fintype.card A : ℝ)) * ((Fintype.card A : ℝ) / S.card) ∧
      ∀ x : A, ∃ t ∈ T, x - t ∈ S

lemma polynomial_le_exponential {b : ℝ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, 2 + (n : ℝ) ^ 3 ≤ b ^ n := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hb
  have h3 := tendsto_pow_const_div_const_pow_of_one_lt 3 hb
  have hconst := h0.const_mul (2 : ℝ)
  have hlim : Tendsto (fun n : ℕ => (2 + (n : ℝ) ^ 3) / b ^ n) atTop (𝓝 0) := by
    simpa only [pow_zero, ← mul_div_assoc, mul_one, mul_zero, ← add_div, add_zero] using
      hconst.add h3
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  have h := (div_lt_iff₀ (pow_pos (by linarith : 0 < b) n)).mp hn
  simpa only [one_mul] using h.le

theorem main : H1 → H2 → type_of% @Erdos704.erdos_704.variants.larman_rogers := by
  intro hgeometry htranslate C hC
  let D := (3 + C) / 2
  have hD : 3 < D := by dsimp [D]; linarith
  have hDpos : 0 < D := by linarith
  have hDC : D < C := by dsimp [D]; linarith
  have hb : 1 < C / D := (one_lt_div hDpos).mpr hDC
  filter_upwards [hgeometry D hD, polynomial_le_exponential hb] with n hd hn
  obtain ⟨A, group, finite, project, S, hS, hlog, hratio, hsafe⟩ := hd
  letI := group
  letI := finite
  obtain ⟨T, hT, hcover⟩ := htranslate A S hS
  let colour (x : EuclideanSpace ℝ (Fin n)) : ↥T :=
    ⟨(hcover (project x)).choose, (hcover (project x)).choose_spec.1⟩
  have hc : (unitDistanceGraph n).Coloring ↥T := by
    apply Coloring.mk colour
    intro x y hxy he
    have hx : project x - (colour x : A) ∈ S := (hcover (project x)).choose_spec.2
    have hy : project y - (colour y : A) ∈ S := (hcover (project y)).choose_spec.2
    rw [← he] at hy
    exact hsafe (colour x : A) x y hx hy hxy
  refine ⟨T.card, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hc.colorable
  have hfrac : 0 ≤ (Fintype.card A : ℝ) / S.card := by positivity
  have hprod : (1 + Real.log (Fintype.card A : ℝ)) * ((Fintype.card A : ℝ) / S.card) ≤
      (1 + (n : ℝ) ^ 3) * D ^ n :=
    (mul_le_mul_of_nonneg_right (by linarith) hfrac).trans
      (mul_le_mul_of_nonneg_left hratio (by positivity))
  have hDpow : 1 ≤ D ^ n := one_le_pow₀ (by linarith)
  calc
    _ ≤ 1 + (1 + Real.log (Fintype.card A : ℝ)) * ((Fintype.card A : ℝ) / S.card) := hT
    _ ≤ 1 + (1 + (n : ℝ) ^ 3) * D ^ n := by linarith
    _ ≤ (2 + (n : ℝ) ^ 3) * D ^ n := by nlinarith only [hDpow]
    _ ≤ (C / D) ^ n * D ^ n := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = C ^ n := by rw [← mul_pow, div_mul_cancel₀ _ hDpos.ne']

end OMA.R_Erdos704_erdos_704_variants_larman_rogers_R1
