import OMAReductions.R_mo_297054_R1_H2_R1

open Metric Complex Filter MeasureTheory intervalIntegral
open scoped Topology Real

namespace HerglotzAux

theorem c1 (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (j : ℕ) :
    ∫ θ in (0:ℝ)..2*π, L (circleMap 0 r θ) * (starRingEnd ℂ (circleMap 0 1 θ))^j
      = 2 * π * r^j * (iteratedDeriv j L 0 / j.factorial) := by
  have hd : DifferentiableOn ℂ L (closedBall 0 r) :=
    hL.mono (closedBall_subset_ball hr1)
  have h := hd.circleIntegral_one_div_sub_center_pow_smul hr0 j
  rw [circleIntegral] at h
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 r) θ • ((1 / (circleMap 0 r θ - 0) ^ (j+1)) • L (circleMap 0 r θ))
      = (I / (r:ℂ)^j) * (L (circleMap 0 r θ) * (starRingEnd ℂ (circleMap 0 1 θ))^j) := by
    intro θ
    rw [deriv_circleMap]
    simp only [circleMap_zero, smul_eq_mul, sub_zero, ofReal_one, one_mul]
    have he : (starRingEnd ℂ) (exp (θ * I)) = (exp (θ * I))⁻¹ := by
      rw [← exp_conj, ← exp_neg]; simp
    rw [he, inv_pow]
    have hr : (r:ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hE : exp (θ * I) ≠ 0 := exp_ne_zero _
    field_simp
    ring
  simp_rw [hpt] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hr : (r:ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have := congrArg (fun t => t * (r:ℂ)^j / I) h
  simp only [smul_eq_mul] at this
  field_simp at this ⊢
  linear_combination this

theorem c2 (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) :
    ∫ θ in (0:ℝ)..2*π, L (circleMap 0 r θ) * (circleMap 0 1 θ)^(k+1) = 0 := by
  have hd : DifferentiableOn ℂ (fun z => z^k * L z) (closedBall 0 r) :=
    (differentiableOn_pow k).mul (hL.mono (closedBall_subset_ball hr1))
  have h := (hd.diffContOnCl_ball (subset_refl _)).circleIntegral_eq_zero hr0.le
  rw [circleIntegral] at h
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 r) θ • ((fun z => z^k * L z) (circleMap 0 r θ))
      = (I * (r:ℂ)^(k+1)) * (L (circleMap 0 r θ) * (circleMap 0 1 θ)^(k+1)) := by
    intro θ
    rw [deriv_circleMap]
    simp only [circleMap_zero, smul_eq_mul, ofReal_one, one_mul]
    ring
  simp_rw [hpt] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hr : (r:ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rcases mul_eq_zero.mp h with h | h
  · exfalso; simp [I_ne_zero, hr] at h
  · exact h

theorem contL (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun θ => L (circleMap 0 r θ)) :=
  ((hL.mono (closedBall_subset_ball hr1)).continuousOn).comp_continuous (continuous_circleMap 0 r)
    (fun θ => circleMap_mem_closedBall 0 hr0.le θ)

theorem fourier (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (j : ℕ) :
    ∫ θ in (0:ℝ)..2*π, ((L (circleMap 0 r θ)).re : ℂ) * (starRingEnd ℂ (circleMap 0 1 θ))^j
      = (1/2) * (2 * π * r^j * (iteratedDeriv j L 0 / j.factorial)) + (1/2) * starRingEnd ℂ
          (∫ θ in (0:ℝ)..2*π, L (circleMap 0 r θ) * (circleMap 0 1 θ)^j) := by
  have hc := contL L hL r hr0 hr1
  have hpt : ∀ θ : ℝ, ((L (circleMap 0 r θ)).re : ℂ) * (starRingEnd ℂ (circleMap 0 1 θ))^j
      = (1/2) * (L (circleMap 0 r θ) * (starRingEnd ℂ (circleMap 0 1 θ))^j)
        + (1/2) * starRingEnd ℂ (L (circleMap 0 r θ) * (circleMap 0 1 θ)^j) := by
    intro θ
    rw [re_eq_add_conj]
    simp only [map_mul, map_pow]
    ring
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun θ : ℝ => (1/2 : ℂ) * (L (circleMap 0 r θ) *
      (starRingEnd ℂ (circleMap 0 1 θ))^j)) volume 0 (2*π) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (hc.mul ((continuous_conj.comp (continuous_circleMap 0 1)).pow j))
  have i2 : IntervalIntegrable (fun θ : ℝ => (1/2 : ℂ) * starRingEnd ℂ (L (circleMap 0 r θ) *
      (circleMap 0 1 θ)^j)) volume 0 (2*π) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_conj.comp (hc.mul ((continuous_circleMap 0 1).pow j)))
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, c1 L hL r hr0 hr1 j]
  congr 2
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity),
    integral_conj]

theorem fourier_zero (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∫ θ in (0:ℝ)..2*π, ((L (circleMap 0 r θ)).re : ℂ) * (starRingEnd ℂ (circleMap 0 1 θ))^0
      = 2 * π * (L 0).re := by
  rw [fourier L hL r hr0 hr1 0]
  have h0 := c1 L hL r hr0 hr1 0
  simp only [pow_zero, mul_one] at h0 ⊢
  rw [h0]
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_mul, map_ofNat,
    conj_ofReal]
  rw [re_eq_add_conj]
  ring

theorem fourier_succ (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :
    ∫ θ in (0:ℝ)..2*π, ((L (circleMap 0 r θ)).re : ℂ) * (starRingEnd ℂ (circleMap 0 1 θ))^(k+1)
      = π * r^(k+1) * (iteratedDeriv (k+1) L 0 / (k+1).factorial) := by
  rw [fourier L hL r hr0 hr1 (k+1), c2 L hL r hr0 hr1 k]
  simp only [map_zero, mul_zero, add_zero]
  ring

theorem intRe (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1)) (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∫ θ in (0:ℝ)..2*π, (L (circleMap 0 r θ)).re = 2 * π * (L 0).re := by
  have h := fourier_zero L hL r hr0 hr1
  simp only [pow_zero, mul_one] at h
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

theorem zero_case (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1))
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0) (h0 : (L 0).re = 0) (k : ℕ) :
    iteratedDeriv (k+1) L 0 = 0 := by
  have hr0 : (0:ℝ) < 1/2 := by norm_num
  have hr1 : (1/2:ℝ) < 1 := by norm_num
  have h := fourier_succ L hL (1/2) hr0 hr1 k
  have hc := contL L hL (1/2) hr0 hr1
  have hle := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun θ => ((L (circleMap 0 (1/2) θ)).re : ℂ) * (starRingEnd ℂ (circleMap 0 1 θ))^(k+1))
    (by positivity : (0:ℝ) ≤ 2*π)
  have hpt : ∀ θ : ℝ, ‖((L (circleMap 0 (1/2) θ)).re : ℂ) * (starRingEnd ℂ (circleMap 0 1 θ))^(k+1)‖
      = -(L (circleMap 0 (1/2) θ)).re := by
    intro θ
    have hz : circleMap 0 (1/2) θ ∈ ball (0:ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_circleMap_zero]; norm_num
    rw [norm_mul, norm_pow, RCLike.norm_conj, norm_circleMap_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (hre _ hz)]
    simp
  simp_rw [hpt] at hle
  rw [intervalIntegral.integral_neg, intRe L hL (1/2) hr0 hr1, h0, h] at hle
  simp only [mul_zero, neg_zero, norm_le_zero_iff, mul_eq_zero, div_eq_zero_iff] at hle
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf : ((k+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (k+1).factorial_ne_zero
  rcases hle with (h1 | h1) | h1 | h1
  · exact absurd h1 hpi
  · norm_num at h1
  · exact h1
  · exact absurd h1 hf

/-- The moment curve on the unit circle. -/
def Kset (n : ℕ) : Set (Fin n → ℂ) :=
  (fun u : ℂ => fun k : Fin n => u^((k:ℕ)+1)) '' sphere 0 1

theorem Kset_compact (n : ℕ) : IsCompact (Kset n) :=
  (isCompact_sphere 0 1).image (continuous_pi fun _ => continuous_pow _)

theorem memS (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (ball 0 1))
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0) (M : ℝ) (hMdef : M = -(L 0).re) (hpos : 0 < M)
    (n : ℕ) :
    (fun k : Fin n => -(iteratedDeriv ((k:ℕ)+1) L 0 / ((k:ℕ)+1).factorial) / (2 * (M : ℂ)))
      ∈ closure (convexHull ℝ (Kset n)) := by
  set a : ℕ → ℂ := fun j => iteratedDeriv j L 0 / j.factorial with ha
  set S := closure (convexHull ℝ (Kset n))
  by_contra hv
  obtain ⟨f, u, hfv, hfS⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ (Kset n)).closure
    isClosed_closure hv
  let vr : ℝ → (Fin n → ℂ) := fun r k => -((r:ℂ)^((k:ℕ)+1) * a ((k:ℕ)+1)) / (2 * (M : ℂ))
  have hA : ∀ r : ℝ, 0 < r → r < 1 → u ≤ f (vr r) := by
    intro r hr0 hr1
    let g : ℝ → (Fin n → ℂ) := fun θ k => (starRingEnd ℂ (circleMap 0 1 θ))^((k:ℕ)+1)
    let ρ : ℝ → ℝ := fun θ => -(L (circleMap 0 r θ)).re
    have hgK : ∀ θ, g θ ∈ S := fun θ =>
      subset_closure (subset_convexHull ℝ _ ⟨starRingEnd ℂ (circleMap 0 1 θ),
        by simp [norm_circleMap_zero], rfl⟩)
    have hρ : ∀ θ, 0 ≤ ρ θ := by
      intro θ
      have hz : circleMap 0 r θ ∈ ball (0:ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr0]; exact hr1
      simp only [ρ]
      linarith [hre _ hz]
    have hc := contL L hL r hr0 hr1
    have hgc : Continuous g :=
      continuous_pi fun k => (continuous_conj.comp (continuous_circleMap 0 1)).pow _
    have hρc : Continuous ρ := (continuous_re.comp hc).neg
    have hint : IntervalIntegrable (fun θ => ρ θ • g θ) volume 0 (2*π) :=
      (hρc.smul hgc).intervalIntegrable _ _
    have hI : ∫ θ in (0:ℝ)..2*π, ρ θ • g θ = (2*π*M) • vr r := by
      funext k
      have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k).intervalIntegral_comp_comm hint
      simp only [ContinuousLinearMap.proj_apply] at h1
      rw [← h1]
      have h2 : ∀ θ, (ρ θ • g θ) k = -(((L (circleMap 0 r θ)).re : ℂ) *
          (starRingEnd ℂ (circleMap 0 1 θ))^((k:ℕ)+1)) := by
        intro θ
        simp only [ρ, g, Pi.smul_apply, Complex.real_smul, ofReal_neg]
        ring
      simp_rw [h2]
      rw [intervalIntegral.integral_neg, fourier_succ L hL r hr0 hr1 k]
      simp only [vr, a, Pi.smul_apply, Complex.real_smul]
      have hM : (M:ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      push_cast
      field_simp
    have hfI : f (∫ θ in (0:ℝ)..2*π, ρ θ • g θ) = ∫ θ in (0:ℝ)..2*π, ρ θ * f (g θ) := by
      rw [← f.intervalIntegral_comp_comm hint]
      simp only [map_smul, smul_eq_mul]
    have hlow : ∫ θ in (0:ℝ)..2*π, ρ θ * u ≤ ∫ θ in (0:ℝ)..2*π, ρ θ * f (g θ) := by
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact (hρc.mul continuous_const).intervalIntegrable _ _
      · exact (hρc.mul (f.continuous.comp hgc)).intervalIntegrable _ _
      · intro θ _
        exact mul_le_mul_of_nonneg_left (hfS _ (hgK θ)).le (hρ θ)
    have hρint : ∫ θ in (0:ℝ)..2*π, ρ θ * u = (2*π*M) * u := by
      rw [intervalIntegral.integral_mul_const]
      simp only [ρ]
      rw [intervalIntegral.integral_neg, intRe L hL r hr0 hr1, hMdef]
      ring
    rw [hρint, ← hfI, hI, map_smul, smul_eq_mul] at hlow
    have h2pm : 0 < 2*π*M := by positivity
    exact le_of_mul_le_mul_left hlow h2pm
  have hcont : Continuous vr := by
    apply continuous_pi
    intro k
    exact ((Complex.continuous_ofReal.pow _).mul continuous_const).neg.div_const _
  have hlim : Tendsto (fun r => f (vr r)) (𝓝[<] 1) (𝓝 (f (vr 1))) :=
    ((f.continuous.comp hcont).tendsto 1).mono_left nhdsWithin_le_nhds
  have hv1 : vr 1 = (fun k : Fin n => -(iteratedDeriv ((k:ℕ)+1) L 0 / ((k:ℕ)+1).factorial) / (2 * (M : ℂ))) := by
    funext k
    simp [vr, a]
  have hge : u ≤ f (vr 1) := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with r hr
    exact hA r hr.1 hr.2
  rw [hv1] at hge
  exact absurd hfv (not_lt.mpr hge)

theorem exists_fin_convex_comb_of_mem_closure_convexHull (n : ℕ) (K : Set (Fin n → ℂ))
    (hK : IsCompact K) (v : Fin n → ℂ) (hv : v ∈ closure (convexHull ℝ K)) :
    ∃ (m : ℕ) (lam : Fin m → ℝ) (x : Fin m → (Fin n → ℂ)),
      m ≤ 2 * n + 1 ∧ (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧ (∀ i, x i ∈ K) ∧
      v = ∑ i, lam i • x i := by
  have hdim : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let Φ : (Fin (2*n+1) → ℝ) × (Fin (2*n+1) → (Fin n → ℂ)) → (Fin n → ℂ) :=
    fun p => ∑ i, p.1 i • p.2 i
  have hΦ : Continuous Φ := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
  have hT : IsCompact (Φ '' (stdSimplex ℝ (Fin (2*n+1)) ×ˢ Set.univ.pi (fun _ => K))) :=
    ((isCompact_stdSimplex ℝ (Fin (2*n+1))).prod (isCompact_univ_pi fun _ => hK)).image hΦ
  have hsub : convexHull ℝ K ⊆ Φ '' (stdSimplex ℝ (Fin (2*n+1)) ×ˢ Set.univ.pi (fun _ => K)) := by
    intro y hy
    obtain ⟨z₀, hz₀⟩ : K.Nonempty := convexHull_nonempty_iff.mp ⟨y, hy⟩
    obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hyw⟩ := eq_pos_convex_span_of_mem_convexHull hy
    have hcard : Fintype.card ι ≤ 2*n+1 := by
      refine hai.card_le_finrank_succ.trans ?_
      have := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      omega
    let e : ι ↪ Fin (2*n+1) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
    have hex : ∀ i : Fin (2*n+1), ¬ (∃ a, e a = i) →
        Function.extend e w 0 i = 0 := fun i h => by
      rw [Function.extend_apply' _ _ _ h]; rfl
    refine ⟨(Function.extend e w 0, Function.extend e z (fun _ => z₀)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro i
      by_cases h : ∃ a, e a = i
      · obtain ⟨a, rfl⟩ := h
        dsimp only
        rw [e.injective.extend_apply]
        exact (hw0 a).le
      · dsimp only
        rw [hex i h]
    · rw [← hw1]
      refine (Fintype.sum_of_injective e e.injective w _ (fun i hi => hex i hi) ?_).symm
      intro a
      rw [e.injective.extend_apply]
    · intro i _
      by_cases h : ∃ a, e a = i
      · obtain ⟨a, rfl⟩ := h
        simp only
        rw [e.injective.extend_apply]
        exact hzK ⟨a, rfl⟩
      · simp only
        rw [Function.extend_apply' _ _ _ h]
        exact hz₀
    · rw [← hyw]
      refine (Fintype.sum_of_injective e e.injective (fun a => w a • z a) _ ?_ ?_).symm
      · intro i hi
        simp only
        rw [hex i hi, zero_smul]
      · intro a
        simp only
        rw [e.injective.extend_apply, e.injective.extend_apply]
  have hvT := (closure_minimal hsub hT.isClosed) hv
  obtain ⟨⟨lam, x⟩, ⟨hlam, hx⟩, hvx⟩ := hvT
  exact ⟨2*n+1, lam, x, le_rfl, hlam.1, hlam.2, fun i => hx i (Set.mem_univ _), hvx.symm⟩

theorem final : ∀ (L : ℂ → ℂ), DifferentiableOn ℂ L (ball 0 1) →
    (∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0) → ∀ n : ℕ,
    ∃ (m : ℕ) (w : Fin m → ℝ) (u : Fin m → ℂ),
      m ≤ 2*n+1 ∧ (∀ i, 0 ≤ w i) ∧ (∀ i, ‖u i‖ = 1) ∧
      ∑ i, w i = -(L 0).re ∧
      ∀ j, 1 ≤ j → j ≤ n → iteratedDeriv j L 0 =
        -2 * (j.factorial : ℂ) * ∑ i, (w i : ℂ) * (u i)^j := by
  intro L hL hre n
  have hM : 0 ≤ -(L 0).re := by linarith [hre 0 (mem_ball_self one_pos)]
  rcases hM.eq_or_lt with h0 | hpos
  · refine ⟨0, Fin.elim0, Fin.elim0, by omega, fun i => i.elim0, fun i => i.elim0, ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact h0
    · intro j hj1 _
      obtain ⟨k, rfl⟩ : ∃ k, j = k+1 := ⟨j-1, by omega⟩
      rw [zero_case L hL hre (by linarith) k]
      simp
  · obtain ⟨m, lam, x, hm, hlam0, hlam1, hxK, hv⟩ :=
      exists_fin_convex_comb_of_mem_closure_convexHull n (Kset n) (Kset_compact n) _
        (memS L hL hre _ rfl hpos n)
    choose u hu hux using hxK
    refine ⟨m, fun i => -(L 0).re * lam i, u, hm, fun i => mul_nonneg hpos.le (hlam0 i),
      fun i => by simpa using hu i, ?_, ?_⟩
    · rw [← Finset.mul_sum, hlam1, mul_one]
    · intro j hj1 hjn
      obtain ⟨k, rfl⟩ : ∃ k, j = k+1 := ⟨j-1, by omega⟩
      have h := congrFun hv ⟨k, by omega⟩
      simp only [Finset.sum_apply, Pi.smul_apply, ← hux, Complex.real_smul] at h
      have hM' : ((-(L 0).re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      have hf : ((k+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (k+1).factorial_ne_zero
      have hs : ∑ i, (((-(L 0).re * lam i : ℝ)) : ℂ) * u i ^ (k+1)
          = ((-(L 0).re : ℝ) : ℂ) * ∑ i, (lam i : ℂ) * u i ^ (k+1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [hs, ← h]
      field_simp

end HerglotzAux

theorem OMA.solution : OMA.R_mo_297054_R1_H2_R1.H1 := by
  exact HerglotzAux.final
