import FormalConjectures.Arxiv.«2607.05349».MicroscopicWeighting
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Matrix

/-! A convergent microscopic weighting has total mass one. Dividing the
differences of the similarity rows by the scale and taking the right limit
shows that the distance matrix sends the limiting weighting to a constant. -/

open Filter Matrix
open scoped Topology
open Arxiv.«2607.05349»

private theorem similarity_det_eventually_ne {X : Type*} [Fintype X] [DecidableEq X]
    [MetricSpace X] :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (similarityMatrix X t).det ≠ 0 := by
  classical
  let f := fun t => (similarityMatrix X t).det
  have ha : AnalyticOnNhd ℝ f Set.univ := by
    intro t _
    unfold f
    rw [show (fun t => (similarityMatrix X t).det) =
        fun t => ∑ σ : Equiv.Perm X, (Equiv.Perm.sign σ : ℝ) *
          ∏ i, Real.exp (-t * dist (σ i) i) by
      ext t
      simp [Matrix.det_apply, similarityMatrix, Units.smul_def]]
    fun_prop
  have hmat : Tendsto (fun (t : ℝ) (i j : X) => Real.exp (-t * dist i j))
      atTop (𝓝 (fun i j => (1 : Matrix X X ℝ) i j)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · have hdist : 0 < dist i j := dist_pos.mpr hij
      have hneg : Tendsto (fun t : ℝ => -t * dist i j) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hdist)).congr
          fun t => by simp; ring
      simpa [Function.comp_def, Matrix.one_apply, hij] using Real.tendsto_exp_atBot.comp hneg
  have hlim : Tendsto f atTop (𝓝 1) := by
    have hc : Continuous (fun M : Matrix X X ℝ => M.det) := continuous_id.matrix_det
    have hmat' : Tendsto (similarityMatrix X) atTop (𝓝 (1 : Matrix X X ℝ)) := hmat
    simpa [f, Function.comp_def] using
      (hc.continuousAt (x := (1 : Matrix X X ℝ))).tendsto.comp hmat'
  have hnzero : ¬ Set.EqOn f 0 Set.univ := by
    intro h
    have hzero : Tendsto f atTop (𝓝 0) :=
      tendsto_const_nhds.congr fun t => (h (Set.mem_univ t)).symm
    exact one_ne_zero (tendsto_nhds_unique hlim hzero)
  rcases (ha 0 (Set.mem_univ 0)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact False.elim (hnzero (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) h))
  · exact h.filter_mono (nhdsGT_le_nhdsNE 0)

private theorem exp_slope_right (d : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (-t * d) - 1) / t)
      (𝓝[>] 0) (𝓝 (-d)) := by
  have h : HasDerivAt (fun t : ℝ => Real.exp (-t * d)) (-d) 0 := by
    have hlinear : HasDerivAt (fun t : ℝ => -t * d) (-d) 0 := by
      simpa [Pi.neg_apply, id] using ((hasDerivAt_id (0 : ℝ)).neg.mul_const d)
    simpa using hlinear.exp
  simpa [div_eq_mul_inv, mul_comm, smul_eq_mul] using h.tendsto_slope_zero_right

theorem OMA.solution : type_of% @Arxiv.«2607.05349».hasFiniteConcentration_of_hasMicroscopicWeighting := by
  intro X _ _ _ _ h
  obtain ⟨w, hw⟩ := h
  let W := weighting X
  have hw' (j : X) : Tendsto (fun t => W t j) (𝓝[>] 0) (𝓝 (w j)) :=
    (tendsto_pi_nhds.mp hw) j
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ), similarityMatrix X t *ᵥ W t = 1 := by
    filter_upwards [similarity_det_eventually_ne (X := X)] with t ht
    simp only [W, weighting, mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht),
      one_mulVec]
  let i₀ : X := Classical.choice inferInstance
  have hsum : ∑ j, w j = 1 := by
    have hlim : Tendsto (fun t => ∑ j, Real.exp (-t * dist i₀ j) * W t j)
        (𝓝[>] 0) (𝓝 (∑ j, w j)) := by
      have hterm (j : X) : Tendsto (fun t => Real.exp (-t * dist i₀ j))
          (𝓝[>] 0) (𝓝 1) := by
        have hc : Continuous fun t : ℝ => Real.exp (-t * dist i₀ j) := by fun_prop
        have hh := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using hh
      simpa using tendsto_finsetSum Finset.univ (fun j _ => (hterm j).mul (hw' j))
    have hone : Tendsto (fun t => ∑ j, Real.exp (-t * dist i₀ j) * W t j)
        (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [heq] with t ht
      exact (congrFun ht i₀).symm
    exact tendsto_nhds_unique hlim hone
  let D := distanceMatrix X
  refine ⟨w, (D *ᵥ w) i₀, hsum, ?_⟩
  funext i
  have hlim (a : X) : Tendsto
      (fun t => ∑ j, ((Real.exp (-t * dist a j) - 1) / t) * W t j)
      (𝓝[>] 0) (𝓝 (-(D *ᵥ w) a)) := by
    simpa [D, distanceMatrix, mulVec, dotProduct, Finset.sum_neg_distrib] using
      tendsto_finsetSum Finset.univ (fun j _ => (exp_slope_right (dist a j)).mul (hw' j))
  have hrows : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∑ j, ((Real.exp (-t * dist i j) - 1) / t) * W t j) =
      (∑ j, ((Real.exp (-t * dist i₀ j) - 1) / t) * W t j) := by
    filter_upwards [heq] with t ht
    have hr (a : X) : ∑ j, Real.exp (-t * dist a j) * W t j = 1 := congrFun ht a
    have simplify (a : X) :
        (∑ j, ((Real.exp (-t * dist a j) - 1) / t) * W t j) =
          (1 - ∑ j, W t j) / t := by
      simp only [div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, one_mul,
        Finset.sum_sub_distrib, hr]
    rw [simplify, simplify]
  exact neg_injective (tendsto_nhds_unique (hlim i) ((hlim i₀).congr' (hrows.mono fun _ ht => ht.symm)))
