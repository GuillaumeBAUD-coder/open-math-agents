import OMAStatements.S_mo_389688
import Mathlib

/-!
# Proof of MathOverflow 389688 (3D Loomis-Whitney Inequality)

We prove that for every measurable set `V ⊆ R x R x R`,
  `(volume V)^2 <= volume (pi_12 '' V) * volume (pi_13 '' V) * volume (pi_23 '' V)`.

Proof:
Replace the three coordinate-plane projections by their measurable hulls `A`, `B`, `C`
via `toMeasurable` (which have identical Lebesgue outer measure by `measure_toMeasurable`).
Then apply Tonelli's theorem and two applications of Cauchy-Schwarz (`ENNReal.lintegral_mul_le_Lp_mul_Lq`
with conjugate exponents `2, 2`), which holds unconditionally in `ENNReal` including `0` and `top`.
-/

namespace MO389688Proof

open MeasureTheory Set
open scoped ENNReal

theorem main_proof :
    ∀ V : Set (ℝ × ℝ × ℝ), MeasurableSet V →
      volume V ^ 2 ≤ volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) *
        volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) *
        volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) := by
  intro V hV
  let A : Set (ℝ × ℝ) := toMeasurable (volume : Measure (ℝ × ℝ))
    ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V)
  let B : Set (ℝ × ℝ) := toMeasurable (volume : Measure (ℝ × ℝ))
    ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V)
  let C : Set (ℝ × ℝ) := toMeasurable (volume : Measure (ℝ × ℝ))
    ((fun p : ℝ × ℝ × ℝ => p.2) '' V)
  have hA_m : MeasurableSet A := measurableSet_toMeasurable _ _
  have hB_m : MeasurableSet B := measurableSet_toMeasurable _ _
  have hC_m : MeasurableSet C := measurableSet_toMeasurable _ _
  have hA_vol : volume A = volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) :=
    measure_toMeasurable _
  have hB_vol : volume B = volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) :=
    measure_toMeasurable _
  have hC_vol : volume C = volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) :=
    measure_toMeasurable _
  let ind (S : Set (ℝ × ℝ)) : ℝ × ℝ → ℝ≥0∞ := S.indicator 1
  have hind_rpow : ∀ (S : Set (ℝ × ℝ)) (p : ℝ × ℝ), ind S p ^ (2 : ℝ) = ind S p := fun S p => by
    by_cases hp : p ∈ S <;> simp [ind, hp]
  have hA_ind : Measurable (ind A) := measurable_const.indicator hA_m
  have hB_ind : Measurable (ind B) := measurable_const.indicator hB_m
  have hC_ind : Measurable (ind C) := measurable_const.indicator hC_m
  let f : ℝ → ℝ≥0∞ := fun y => ∫⁻ x : ℝ, ind A (x, y)
  let g : ℝ → ℝ≥0∞ := fun z => ∫⁻ x : ℝ, ind B (x, z)
  have hf_m : Measurable f :=
    Measurable.lintegral_prod_right (f := fun y x => ind A (x, y)) (hA_ind.comp measurable_swap)
  have hg_m : Measurable g :=
    Measurable.lintegral_prod_right (f := fun z x => ind B (x, z)) (hB_ind.comp measurable_swap)
  have hf_int : ∫⁻ y : ℝ, f y = volume A := by
    rw [← lintegral_indicator_one hA_m,
      show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
      lintegral_prod_symm (f := ind A) hA_ind.aemeasurable]
  have hg_int : ∫⁻ z : ℝ, g z = volume B := by
    rw [← lintegral_indicator_one hB_m,
      show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
      lintegral_prod_symm (f := ind B) hB_ind.aemeasurable]
  have hpq : Real.HolderConjugate (2 : ℝ) 2 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hV_eq : volume V = ∫⁻ p : ℝ × ℝ, ∫⁻ x : ℝ, V.indicator 1 (x, p) := by
    rw [← lintegral_indicator_one hV,
      show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) from rfl,
      lintegral_prod_symm (f := V.indicator 1) (measurable_const.indicator hV).aemeasurable]
  have hinner : ∀ p : ℝ × ℝ,
      (∫⁻ x : ℝ, V.indicator 1 (x, p)) ≤ ind C p * (f p.1 ^ (1 / 2 : ℝ) * g p.2 ^ (1 / 2 : ℝ)) := by
    rintro ⟨y, z⟩
    have hpt : ∀ x : ℝ, V.indicator 1 (x, (y, z)) ≤ ind C (y, z) * (ind A (x, y) * ind B (x, z)) := by
      intro x
      by_cases hx : (x, (y, z)) ∈ V
      · have h1 : (x, y) ∈ A := subset_toMeasurable _ _ ⟨(x, (y, z)), hx, rfl⟩
        have h2 : (x, z) ∈ B := subset_toMeasurable _ _ ⟨(x, (y, z)), hx, rfl⟩
        have h3 : (y, z) ∈ C := subset_toMeasurable _ _ ⟨(x, (y, z)), hx, rfl⟩
        simp [ind, Set.indicator, hx, h1, h2, h3]
      · simp [Set.indicator, hx]
    calc ∫⁻ x : ℝ, V.indicator 1 (x, (y, z))
        ≤ ∫⁻ x : ℝ, ind C (y, z) * (ind A (x, y) * ind B (x, z)) := lintegral_mono hpt
      _ = ind C (y, z) * ∫⁻ x : ℝ, ind A (x, y) * ind B (x, z) :=
          lintegral_const_mul _ ((hA_ind.comp (measurable_id.prodMk measurable_const)).mul
            (hB_ind.comp (measurable_id.prodMk measurable_const)))
      _ ≤ ind C (y, z) * (f y ^ (1 / 2 : ℝ) * g z ^ (1 / 2 : ℝ)) := by
          gcongr
          have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ) hpq
            (f := fun x => ind A (x, y)) (g := fun x => ind B (x, z))
            (hA_ind.comp (measurable_id.prodMk measurable_const)).aemeasurable
            (hB_ind.comp (measurable_id.prodMk measurable_const)).aemeasurable
          simpa [f, g, Pi.mul_apply, hind_rpow] using hcs
  have houter : volume V ≤ volume C ^ (1 / 2 : ℝ) * (volume A * volume B) ^ (1 / 2 : ℝ) := by
    rw [hV_eq]
    calc ∫⁻ p : ℝ × ℝ, ∫⁻ x : ℝ, V.indicator 1 (x, p)
        ≤ ∫⁻ p : ℝ × ℝ, ind C p * (f p.1 ^ (1 / 2 : ℝ) * g p.2 ^ (1 / 2 : ℝ)) :=
          lintegral_mono hinner
      _ ≤ (∫⁻ p : ℝ × ℝ, ind C p ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ p : ℝ × ℝ, (f p.1 ^ (1 / 2 : ℝ) * g p.2 ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          have hmeas_fg : Measurable (fun p : ℝ × ℝ => f p.1 ^ (1 / 2 : ℝ) * g p.2 ^ (1 / 2 : ℝ)) :=
            ((hf_m.comp measurable_fst).pow_const _).mul ((hg_m.comp measurable_snd).pow_const _)
          simpa [Pi.mul_apply] using ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (ℝ × ℝ))
            hpq hC_ind.aemeasurable hmeas_fg.aemeasurable
      _ = volume C ^ (1 / 2 : ℝ) * (volume A * volume B) ^ (1 / 2 : ℝ) := by
          have h1 : ∫⁻ p : ℝ × ℝ, ind C p ^ (2 : ℝ) = volume C := by
            simp_rw [hind_rpow]
            exact lintegral_indicator_one hC_m
          have h2 : ∫⁻ p : ℝ × ℝ, (f p.1 ^ (1 / 2 : ℝ) * g p.2 ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
              volume A * volume B := by
            have hsq : ∀ p : ℝ × ℝ,
                (f p.1 ^ (1 / 2 : ℝ) * g p.2 ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = f p.1 * g p.2 := fun p => by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
                ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
              norm_num
            simp_rw [hsq]
            rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
              lintegral_prod (f := fun p : ℝ × ℝ => f p.1 * g p.2)
                ((hf_m.comp measurable_fst).mul (hg_m.comp measurable_snd)).aemeasurable]
            simp_rw [lintegral_const_mul _ hg_m, hg_int]
            rw [lintegral_mul_const _ hf_m, hf_int]
            rfl
          rw [h1, h2]
  calc volume V ^ 2
      ≤ (volume C ^ (1 / 2 : ℝ) * (volume A * volume B) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' houter 2
    _ = (volume C ^ (1 / 2 : ℝ)) ^ 2 * ((volume A * volume B) ^ (1 / 2 : ℝ)) ^ 2 := mul_pow _ _ _
    _ = volume C * (volume A * volume B) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
    _ = volume A * volume B * volume C := by rw [mul_comm]
    _ = volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) *
        volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) *
        volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) := by rw [hA_vol, hB_vol, hC_vol]

end MO389688Proof

theorem OMA.solution : type_of% @OMA.S_mo_389688.main :=
  MO389688Proof.main_proof
