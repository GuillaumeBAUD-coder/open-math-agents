import OMAReductions.R_Erdos1038_erdos_1038_parts_ii_R1
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Separate the transport and finite sampling from the two outer
dual witnesses in Section 2 of Tao, Superlevel Sets of Logarithmic
Potentials (December 27, 2025). The origin is a selected point of the
large sublevel set after reflection and translation.
-/

-- Credit: @dk8827

open MeasureTheory Set
open scoped ENNReal

open Filter MeasureTheory Finset Set
open scoped BigOperators Topology ENNReal

namespace OMA.LogPotentialSampling

theorem finite_certificate (E : Set ℝ) (n : ℕ) (r : Fin n → ℝ) (μ : Measure ℝ)
    (hμ : IsProbabilityMeasure μ) (hE : μ Eᶜ = 0)
    (hlog : ∀ i, μ {r i} = 0 ∧ Integrable (fun x => Real.log |x - r i|) μ ∧
      0 < ∫ x, Real.log |x - r i| ∂μ) :
    ∃ (k : ℕ) (w : Fin (k + 1) → ℝ), (∀ j, w j ∈ E) ∧
      ∀ i, 1 ≤ ∏ j, |w j - r i| := by
  classical
  let _ : IsProbabilityMeasure μ := hμ
  let D := {x ∈ E | ∀ i, x ≠ r i}
  have haE : ∀ᵐ x ∂μ, x ∈ E := ae_iff.2 hE
  have haD : ∀ᵐ x ∂μ, x ∈ D := by
    have hd : ∀ i, ∀ᵐ x ∂μ, x ≠ r i := fun i => by
      rw [ae_iff]
      rw [show {x : ℝ | ¬ x ≠ r i} = {r i} by ext x; simp]
      exact (hlog i).1
    exact haE.and (ae_all_iff.2 hd)
  obtain ⟨x₀, hx₀⟩ := haD.exists
  by_cases hn : 0 < n
  swap
  · obtain rfl : n = 0 := by omega
    exact ⟨0, fun _ => x₀, fun _ => hx₀.1, fun i => i.elim0⟩
  let F : ℝ → Fin n → ℝ := fun x i => Real.log |x - r i|
  have hcoord (i : Fin n) : Integrable (fun x => F x i) μ := (hlog i).2.1
  let C := convexHull ℝ (F '' D)
  have hconv : Convex ℝ (closure C) := (convex_convexHull ℝ (F '' D)).closure
  have hFc : ∀ᵐ x ∂μ, F x ∈ closure C := haD.mono fun x hx =>
    subset_closure (subset_convexHull ℝ _ (mem_image_of_mem F hx))
  have hclose := hconv.integral_mem isClosed_closure hFc (Integrable.of_eval hcoord)
  let U : Set (Fin n → ℝ) := ⋂ i, {v | 0 < v i}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_apply i)
  have hmean : (∫ x, F x ∂μ) ∈ U := by
    apply mem_iInter.2
    intro i
    change 0 < (∫ x, F x ∂μ) i
    rw [eval_integral hcoord]
    exact (hlog i).2.2
  obtain ⟨v, hvU, hvC⟩ := (mem_closure_iff_nhds.1 hclose U (hU.mem_nhds hmean))
  change v ∈ convexHull ℝ (F '' D) at hvC
  rw [_root_.convexHull_eq] at hvC
  obtain ⟨I, T, a, z, ha, hasum, hz, hv⟩ := hvC
  have hz' : ∀ j ∈ T, ∃ y ∈ D, F y = z j := fun j hj => hz j hj
  choose y hy hzEq using hz'
  let Y (j : I) := if hj : j ∈ T then y j hj else x₀
  have hY (j : I) (hj : j ∈ T) : Y j ∈ D := by simpa [Y, hj] using hy j hj
  have hYZ (j : I) (hj : j ∈ T) : F (Y j) = z j := by simpa [Y, hj] using hzEq j hj
  have hv' : (∑ j ∈ T, a j • z j) = v := by simpa [Finset.centerMass, hasum] using hv
  let A (i : Fin n) := ∑ j ∈ T, a j * F (Y j) i
  have hA (i : Fin n) : 0 < A i := by
    have he : A i = v i := by
      rw [← hv']
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact sum_congr rfl fun j hj => by rw [hYZ j hj]
    rw [he]
    exact mem_iInter.1 hvU i
  have hlarge (i : Fin n) : ∀ᶠ M : ℕ in atTop,
      (∑ j ∈ T, |F (Y j) i|) < (M : ℝ) * A i := by
    obtain ⟨M₀, hM₀⟩ := exists_nat_gt ((∑ j ∈ T, |F (Y j) i|) / A i)
    filter_upwards [eventually_ge_atTop M₀] with M hM
    exact (div_lt_iff₀ (hA i)).1 (hM₀.trans_le (by exact_mod_cast hM))
  obtain ⟨M, hM, hMlarge⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (eventually_all.2 hlarge)).exists
  let b (j : I) := ⌈(M : ℝ) * a j⌉₊
  have hround (j : I) (hj : j ∈ T) (i : Fin n) :
      (M : ℝ) * a j * F (Y j) i - |F (Y j) i| ≤ (b j : ℝ) * F (Y j) i := by
    have hlo : (M : ℝ) * a j ≤ b j := Nat.le_ceil _
    have hhi : (b j : ℝ) < (M : ℝ) * a j + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (by positivity) (ha j hj))
    have hdist : |(b j : ℝ) - (M : ℝ) * a j| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.2 hlo)]
      linarith
    have hbound : |((b j : ℝ) - (M : ℝ) * a j) * F (Y j) i| ≤ |F (Y j) i| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hdist
    have hs := (neg_le_abs _).trans hbound
    nlinarith only [hs]
  have hsum (i : Fin n) : 0 < ∑ j ∈ T, (b j : ℝ) * F (Y j) i := by
    have hh := sum_le_sum fun j hj => hround j hj i
    simp_rw [mul_assoc] at hh
    rw [sum_sub_distrib, ← mul_sum] at hh
    exact (sub_pos.2 (hMlarge i)).trans_le hh
  let K : Multiset ℝ := ∑ j ∈ T, Multiset.replicate (b j) (Y j)
  have hKD (x : ℝ) (hx : x ∈ K) : x ∈ D := by
    obtain ⟨j, hj, hxj⟩ := Multiset.mem_sum.1 hx
    have he : x = Y j := (Multiset.mem_replicate.1 hxj).2
    exact he.symm ▸ hY j hj
  have hKlogs (i : Fin n) :
      (K.map fun x => F x i).sum = ∑ j ∈ T, (b j : ℝ) * F (Y j) i := by
    have aux (S : Finset I) :
        ((∑ j ∈ S, Multiset.replicate (b j) (Y j)).map fun x => F x i).sum =
          ∑ j ∈ S, (b j : ℝ) * F (Y j) i := by
      induction S using Finset.induction_on with
      | empty => simp
      | insert j S hj ih =>
        rw [sum_insert hj, sum_insert hj, Multiset.map_add, Multiset.sum_add, ih,
          Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    exact aux T
  let W := K.toList
  have hW : 0 < W.length := by
    by_contra! hh
    have hh' : K = 0 := by
      apply Multiset.card_eq_zero.1
      simpa [W] using (show W.length = 0 by omega)
    have hz := (hKlogs ⟨0, hn⟩).symm
    rw [hh'] at hz
    simp at hz
    linarith only [hsum ⟨0, hn⟩, hz]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hW.ne'
  let w : Fin (k + 1) → ℝ := fun j => W.get ⟨j, by omega⟩
  have hwM (j : Fin (k + 1)) : w j ∈ K := Multiset.mem_toList.1 (List.get_mem _ _)
  refine ⟨k, w, fun j => (hKD _ (hwM j)).1, fun i => ?_⟩
  have hne (j : Fin (k + 1)) : |w j - r i| ≠ 0 :=
    abs_ne_zero.2 (sub_ne_zero.2 ((hKD _ (hwM j)).2 i))
  have hlogs : (∑ j, Real.log |w j - r i|) = (K.map fun x => F x i).sum := by
    rw [← List.sum_ofFn]
    have hwList : List.ofFn w = W := by
      apply List.ext_get
      · simp [hk]
      · intro j hj₁ hj₂
        rw [List.get_ofFn]
        rfl
    change (List.ofFn (fun j => F (w j) i)).sum = _
    rw [List.ofFn_comp' w (fun x => F x i), hwList,
      show W = K.toList from rfl, Multiset.sum_map_toList]
  apply ((Real.log_pos_iff (prod_nonneg fun _ _ => abs_nonneg _)).1 ?_).le
  rw [Real.log_prod (fun j _ => hne j), hlogs, hKlogs]
  exact hsum i

end OMA.LogPotentialSampling

namespace OMA.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1

/-- Transport the template witness to the open set and normalize its mass. -/
def H1 : Prop :=
  ∀ E : Set ℝ, IsOpen E → E ⊆ Ioo (-2) 2 →
    ENNReal.ofReal (2 * Real.sqrt 2) < volume E →
    (∃ x ∈ E, (1.7624 : ℝ) < |x|) →
  ∃ a : ℝ, 0.7624 < a ∧ a ≤ 1 ∧
    ∀ ν : Measure ℝ, IsFiniteMeasure ν → ν ≠ 0 → ν ({0} ∪ Icc a (2 * Real.sqrt 2))ᶜ = 0 →
    (∀ t ∈ Icc a (a + 2), ν {t} = 0 ∧
      Integrable (fun s => Real.log |s - t|) ν ∧
      0 < ∫ s, Real.log |s - t| ∂ν) →
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ Eᶜ = 0 ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, μ {t} = 0 ∧
      Integrable (fun x => Real.log |x - t|) μ ∧
      0 < ∫ x, Real.log |x - t| ∂μ

/-- The intermediate witness uses atoms at 0 and 2√2 and the two interval
densities in equation (2.6) of Tao's note. -/
def H2 : Prop :=
  ∀ a : ℝ, 0.7624 < a → a ≤ 0.7987 →
  ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν ({0} ∪ Icc a (2 * Real.sqrt 2))ᶜ = 0 ∧
    ∀ t ∈ Icc a (a + 2), ν {t} = 0 ∧
      Integrable (fun s => Real.log |s - t|) ν ∧
      0 < ∫ s, Real.log |s - t| ∂ν

/-- The far witness uses the atom at 0 and the interval density in (2.5). -/
def H3 : Prop :=
  ∀ a : ℝ, 0.7987 < a → a ≤ 1 →
  ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν ({0} ∪ Icc a (2 * Real.sqrt 2))ᶜ = 0 ∧
    ∀ t ∈ Icc a (a + 2), ν {t} = 0 ∧
      Integrable (fun s => Real.log |s - t|) ν ∧
      0 < ∫ s, Real.log |s - t| ∂ν

theorem main : H1 → H2 → H3 → OMA.R_Erdos1038_erdos_1038_parts_ii_R1.H2 := by
  intro transfer mid far E hopen hbox hvol hfar n r hr
  obtain ⟨a, ha, ha₁, trans⟩ := transfer E hopen hbox hvol hfar
  have hw : ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν ({0} ∪ Icc a (2 * Real.sqrt 2))ᶜ = 0 ∧
        ∀ t ∈ Icc a (a + 2), ν {t} = 0 ∧
          Integrable (fun s => Real.log |s - t|) ν ∧
          0 < ∫ s, Real.log |s - t| ∂ν := by
    by_cases ha₂ : a ≤ 0.7987
    · exact mid a ha ha₂
    · exact far a (lt_of_not_ge ha₂) ha₁
  obtain ⟨ν, hn, hn₀, hs, hpos⟩ := hw
  obtain ⟨μ, hμ, hE, hμpos⟩ := trans ν hn hn₀ hs hpos
  exact OMA.LogPotentialSampling.finite_certificate E n r μ hμ hE (fun i => hμpos (r i) (hr i))

end OMA.R_Erdos1038_erdos_1038_parts_ii_R1_H2_R1
