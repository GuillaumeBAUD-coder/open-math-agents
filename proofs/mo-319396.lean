import OMAStatements.S_mo_319396
import Mathlib

open MeasureTheory Set OMA.S_mo_319396
open scoped ENNReal

private def kernel (j : ℕ) (x : I) : ℝ :=
  x.val ^ 2 * (1 - x.val ^ 2) ^ j

private theorem kernel_eq (j : ℕ) (x : I) :
    kernel j x =
      ∑ i ∈ Finset.range (j + 1), (-1 : ℝ)^i * (j.choose i : ℝ) * x.val^(2*i+2) := by
  unfold kernel
  rw [sub_eq_add_neg, add_comm 1, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_pow, mul_one, neg_pow, ← pow_mul, pow_add]
  ring

private theorem kernel_nonneg (j : ℕ) (x : I) : 0 ≤ kernel j x := by
  have h : x.val ^ 2 ≤ 1 := by
    have h₁ := x.property.1
    have h₂ := x.property.2
    nlinarith [mul_nonneg (show 0 ≤ 1 - x.val by linarith)
      (show 0 ≤ 1 + x.val by linarith)]
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (sub_nonneg.mpr h) _)

private theorem sumKernel (x : I) :
    (∑' j, ENNReal.ofReal (kernel j x)) =
      ({origin} : Set I)ᶜ.indicator 1 x := by
  by_cases hz : x.val = 0
  · have hx : x = origin := Subtype.ext hz
    subst x
    simp [kernel, origin]
  · have hxo : x ∈ ({origin} : Set I)ᶜ := by
      intro hm
      exact hz (congrArg Subtype.val (Set.mem_singleton_iff.mp hm))
    rw [Set.indicator_of_mem hxo, Pi.one_apply]
    have h₂ : x.val ^ 2 ≤ 1 := by
      have hl := x.property.1
      have hu := x.property.2
      nlinarith [mul_nonneg (show 0 ≤ 1 - x.val by linarith)
        (show 0 ≤ 1 + x.val by linarith)]
    have hx2 : 0 < x.val ^ 2 := sq_pos_of_ne_zero hz
    have hG := (hasSum_geometric_of_lt_one (sub_nonneg.mpr h₂)
      (sub_lt_self (1 : ℝ) hx2)).mul_left (x.val ^ 2)
    have hA : x.val ^ 2 * (1 - (1 - x.val ^ 2))⁻¹ = 1 := by
      rw [sub_sub_cancel, mul_inv_cancel₀ hx2.ne']
    have hsum : HasSum (fun j => kernel j x) 1 := by
      simpa only [kernel, hA] using hG
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => kernel_nonneg j x) hsum.summable,
      hsum.tsum_eq, ENNReal.ofReal_one]

theorem OMA.solution : type_of% @OMA.S_mo_319396.main := by
  constructor
  · intro μ hμ
    have hi (j i : ℕ) :
        Integrable (fun x : I => (-1 : ℝ)^i * (j.choose i : ℝ) * x.val^(2*i+2)) μ :=
      (hμ (2*i+2) (by omega)).const_mul _
    have hk (j : ℕ) : Integrable (kernel j) μ := by
      rw [funext (kernel_eq j)]
      exact integrable_finsetSum _ (fun i _ => hi j i)
    have ht (j : ℕ) : term (moment μ) j = ∫ x, kernel j x ∂μ := by
      simp_rw [kernel_eq]
      rw [integral_finsetSum _ (fun i _ => hi j i)]
      simp only [term, moment, integral_const_mul]
    have hReal (j : ℕ) :
        ENNReal.ofReal (term (moment μ) j) = ∫⁻ x, ENNReal.ofReal (kernel j x) ∂μ := by
      rw [ht, ofReal_integral_eq_lintegral_ofReal (hk j)
        (Filter.Eventually.of_forall (kernel_nonneg j))]
    have hcomp : MeasurableSet (({origin} : Set I)ᶜ) := (measurableSet_singleton _).compl
    rw [← measure_add_measure_compl (μ := μ) (measurableSet_singleton origin)]
    simp_rw [hReal]
    rw [← lintegral_tsum (fun j => (hk j).aemeasurable.ennreal_ofReal)]
    simp_rw [sumKernel]
    rw [lintegral_indicator_one hcomp]
  · let μ : Measure I := Measure.dirac origin
    let ν : Measure I := (⊤ : ℝ≥0∞) • μ
    refine ⟨μ, ν, by simp [μ], by simp [ν, μ], ?_⟩
    intro n hn
    have hv : (fun x : I => x.val^n) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
      rw [show MeasureTheory.ae μ = pure origin from ae_dirac_eq _]
      simp [Filter.EventuallyEq, origin, hn.ne']
    have hw : (fun x : I => x.val^n) =ᵐ[ν] (fun _ => (0 : ℝ)) :=
      Measure.ae_smul_measure hv _
    refine ⟨(integrable_zero I ℝ μ).congr hv.symm, (integrable_zero I ℝ ν).congr hw.symm, ?_⟩
    unfold moment
    rw [integral_congr_ae hv, integral_congr_ae hw]
    simp