import FormalConjectures.ErdosProblems.«114»

/-!
# Proof of Erdos114.erdos_114.variants.two (degree 2 case of Erdos Problem 114)
-/

open Polynomial MeasureTheory Filter Complex Real
open scoped Topology ENNReal NNReal

namespace Erdos114Two

/- Step 1: Reduction of monic quadratic to X^2 - C r with r ≥ 0 -/

lemma quadratic_eq_coeffs (p : ℂ[X]) (hp : p.Monic) (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have hsum := hp.as_sum
  rw [hdeg] at hsum
  rw [hsum]
  simp [Finset.sum_range_succ, pow_zero, pow_one, mul_one]
  ring

lemma lemniscateLength_eq_sub_ofReal (p : ℂ[X]) (hp : p.Monic) (hdeg : p.natDegree = 2) :
    ∃ r : ℝ, 0 ≤ r ∧ Erdos114.lemniscateLength p =
      Erdos114.lemniscateLength (X ^ 2 - C (r : ℂ)) := by
  have hpe := quadratic_eq_coeffs p hp hdeg
  let u : ℂ := p.coeff 1 / 2
  let w : ℂ := u ^ 2 - p.coeff 0
  let r : ℝ := ‖w‖
  let α : ℂ := if w = 0 then 1 else Complex.exp (((w.arg / 2 : ℝ) : ℂ) * Complex.I)
  have hα_norm : ‖α‖ = 1 := by
    by_cases hw : w = 0
    · simp [α, hw]
    · simp only [α, hw, ↓reduceIte]
      simpa using Complex.norm_exp_ofReal_mul_I (w.arg / 2)
  have hα_ne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα_norm
    norm_num at hα_norm
  have hα_sq : α ^ 2 * (r : ℂ) = w := by
    by_cases hw : w = 0
    · simp [α, r, hw]
    · simp only [α, hw, ↓reduceIte, r]
      rw [← Complex.exp_nat_mul]
      have harg : (2 : ℕ) * (((w.arg / 2 : ℝ) : ℂ) * Complex.I) = (w.arg : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, mul_comm, Complex.norm_mul_exp_arg_mul_I]
  let ef : ℂ → ℂ := fun z => α⁻¹ * (z + u)
  let e : ℂ ≃ᵢ ℂ :=
    { toFun := ef
      invFun := fun z => α * z - u
      left_inv := fun z => by dsimp [ef]; simp [hα_ne]
      right_inv := fun z => by dsimp [ef]; simp [mul_add, hα_ne]
      isometry_toFun := Isometry.of_dist_eq fun x y => by
        dsimp [ef]
        simp only [dist_eq_norm, ← mul_sub, norm_mul, norm_inv, hα_norm, inv_one, one_mul]
        congr 1
        ring }
  have hset : Erdos114.lemniscate p = e ⁻¹' Erdos114.lemniscate (X ^ 2 - C (r : ℂ)) := by
    ext z
    simp only [Erdos114.lemniscate, Set.mem_ofPred_eq, Set.mem_preimage, eval_sub, eval_pow,
      eval_X, eval_C]
    have heval : p.eval z = α ^ 2 * ((e z) ^ 2 - (r : ℂ)) := by
      rw [hpe]
      have hez : e z = α⁻¹ * (z + u) := rfl
      rw [hez]
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
      have h1 : α ^ 2 * ((α⁻¹ * (z + u)) ^ 2 - (r : ℂ)) = (z + u) ^ 2 - α ^ 2 * (r : ℂ) := by
        calc α ^ 2 * ((α⁻¹ * (z + u)) ^ 2 - (r : ℂ))
            = (α * α⁻¹) ^ 2 * (z + u) ^ 2 - α ^ 2 * (r : ℂ) := by ring
          _ = (z + u) ^ 2 - α ^ 2 * (r : ℂ) := by simp [hα_ne]
      rw [h1, hα_sq]
      simp only [u, w]
      ring
    rw [heval, norm_mul, norm_pow, hα_norm, one_pow, one_mul, eq_comm]
  refine ⟨r, norm_nonneg w, ?_⟩
  rw [Erdos114.lemniscateLength, Erdos114.lemniscateLength, hset,
    IsometryEquiv.hausdorffMeasure_preimage]

/- Step 2: Upper and lower Hausdorff 1-measure bounds for C^1 curves -/

lemma subdiv_mem_Icc {a b : ℝ} (hab : a ≤ b) {n k : ℕ} (hk : k < n) :
    Set.Icc (a + (k : ℝ) * (b - a) / n) (a + ((k + 1 : ℕ) : ℝ) * (b - a) / n) ⊆ Set.Icc a b := by
  intro s ⟨hs1, hs2⟩
  have hn : 0 < n := Nat.lt_of_le_of_lt k.zero_le hk
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have h1 : 0 ≤ (k : ℝ) * (b - a) / n := by positivity
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
  have h2 : ((k + 1 : ℕ) : ℝ) * (b - a) / n ≤ b - a := by rw [div_le_iff₀ hn0]; nlinarith
  exact ⟨by linarith, by linarith⟩

lemma interval_subdiv_cover {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) :
    Set.Icc a b ⊆ ⋃ k : Fin n,
      Set.Icc (a + (k : ℝ) * (b - a) / n) (a + ((k : ℝ) + 1) * (b - a) / n) := by
  intro t ⟨hat, htb⟩
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp only [sub_self, mul_zero, zero_div, add_zero, Set.mem_iUnion, Set.mem_Icc]
    exact ⟨⟨0, hn⟩, hat, htb⟩
  · have hpos : (0 : ℝ) < (b - a) / n := div_pos (sub_pos.2 hab_lt) (Nat.cast_pos.2 hn)
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rcases eq_or_lt_of_le htb with rfl | htb_lt
    · refine Set.mem_iUnion.2 ⟨⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩, ?_, ?_⟩
      · have hle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
        have hmul : ((n - 1 : ℕ) : ℝ) * (t - a) / n ≤ t - a := by
          rw [div_le_iff₀ (Nat.cast_pos.2 hn)]; nlinarith [sub_nonneg.2 hab]
        linarith
      · have hn1 : (((n - 1 : ℕ) : ℝ) + 1) = n := by rw [Nat.cast_sub hn]; ring
        rw [hn1, mul_comm (n : ℝ), mul_div_assoc, div_self hn_ne, mul_one]
        linarith
    · let m : ℕ := ⌊(t - a) / ((b - a) / n)⌋₊
      have hm_lt : m < n := by
        rw [Nat.floor_lt (div_nonneg (sub_nonneg.2 hat) hpos.le), div_lt_iff₀ hpos]
        calc t - a < b - a := by linarith
          _ = (n : ℝ) * ((b - a) / n) := by field_simp
      refine Set.mem_iUnion.2 ⟨⟨m, hm_lt⟩, ?_, ?_⟩
      · have hfl := Nat.floor_le (div_nonneg (sub_nonneg.2 hat) hpos.le)
        rw [le_div_iff₀ hpos] at hfl
        change (m : ℝ) * ((b - a) / n) ≤ t - a at hfl
        simp only [Fin.val_mk]
        rw [show (m : ℝ) * (b - a) / n = (m : ℝ) * ((b - a) / n) by ring]
        linarith
      · have hlt := Nat.lt_floor_add_one ((t - a) / ((b - a) / n))
        rw [div_lt_iff₀ hpos] at hlt
        change t - a < ((m : ℝ) + 1) * ((b - a) / n) at hlt
        simp only [Fin.val_mk]
        rw [show ((m : ℝ) + 1) * (b - a) / n = ((m : ℝ) + 1) * ((b - a) / n) by ring]
        linarith

lemma hausdorffMeasure_image_le_integral {a b : ℝ} (hab : a ≤ b) (γ γ' : ℝ → ℂ)
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt γ (γ' t) t)
    (hcont : ContinuousOn γ' (Set.Icc a b)) :
    μH[1] (γ '' Set.Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖γ' t‖) := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · have := MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ zero_lt_one
    simp
  have hcont_norm : ContinuousOn (fun t => ‖γ' t‖) (Set.Icc a b) := hcont.norm
  have hint : IntervalIntegrable (fun t => ‖γ' t‖) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont_norm
  have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖γ' t‖ ≤ M := by
    obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab) hcont_norm
    exact ⟨max 0 ‖γ' t₀‖, le_max_left _ _, fun t ht => (ht₀ ht).trans (le_max_right _ _)⟩
  obtain ⟨M, hM0, hM⟩ := hbdd
  have hlip : ∀ ε : ℝ, 0 < ε →
      μH[1] (γ '' Set.Icc a b) ≤ ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) + 2 * ε * (b - a)) := by
    intro ε hε
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hcont
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hucδ⟩ := huc ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    have hN_pos : 0 < N := by
      have : (0 : ℝ) < (b - a) / δ := div_pos (sub_pos.2 hab_lt) hδ
      exact_mod_cast this.trans hN
    let x : ℕ → ℕ → ℝ := fun n k => a + (k : ℝ) * (b - a) / n
    let t : (n : ℕ) → Fin n → Set ℂ := fun n k => γ '' Set.Icc (x n k) (x n (k + 1))
    let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (M * (b - a) / n)
    have hr : Tendsto r atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => M * (b - a) / n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [r, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h0
    have ht : ∀ᶠ n in atTop, ∀ k : Fin n, Metric.ediam (t n k) ≤ r n := by
      refine eventually_atTop.2 ⟨1, fun n hn k => ?_⟩
      refine Metric.ediam_le_of_forall_dist_le fun p hp q hq => ?_
      rcases hp with ⟨u, hu, rfl⟩
      rcases hq with ⟨v, hv, rfl⟩
      have hsub : Set.Icc (x n k) (x n (k + 1)) ⊆ Set.Icc a b :=
        subdiv_mem_Icc hab k.isLt
      have hdiff : ‖γ u - γ v‖ ≤ M * |u - v| := by
        have hmvt := (convex_Icc (x n k) (x n (k + 1))).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun s hs => (hderiv s (hsub hs)).hasDerivWithinAt)
          (fun s hs => hM s (hsub hs)) hv hu
        simpa [Real.norm_eq_abs] using hmvt
      have huv : |u - v| ≤ (b - a) / n := by
        rw [abs_le]
        have hx : x n (k + 1) - x n k = (b - a) / n := by
          simp only [x, Nat.cast_add, Nat.cast_one]; ring
        constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
      rw [dist_eq_norm]
      calc ‖γ u - γ v‖ ≤ M * |u - v| := hdiff
        _ ≤ M * ((b - a) / n) := mul_le_mul_of_nonneg_left huv hM0
        _ = M * (b - a) / n := by ring
    have hst : ∀ᶠ n in atTop, γ '' Set.Icc a b ⊆ ⋃ k : Fin n, t n k := by
      refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
      have hcov := interval_subdiv_cover hab (Nat.succ_le_iff.mp hn)
      intro p ⟨s, hs, hp⟩
      rw [← hp]
      rcases Set.mem_iUnion.1 (hcov hs) with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨k, s, by simpa [x] using hk, rfl⟩
    have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
      1 (γ '' Set.Icc a b) r hr t ht hst
    have hbound : ∀ᶠ n in atTop,
        (∑ k : Fin n, Metric.ediam (t n k) ^ (1 : ℝ)) ≤
          ENNReal.ofReal ((∫ s in a..b, ‖γ' s‖) + 2 * ε * (b - a)) := by
      refine eventually_atTop.2 ⟨max 1 N, fun n hn => ?_⟩
      have hn1 : 0 < n := Nat.succ_le_iff.mp (le_trans (le_max_left _ _) hn)
      have hnN : N ≤ n := le_trans (le_max_right _ _) hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      have hstep_pos : 0 ≤ (b - a) / n := div_nonneg (sub_nonneg.2 hab) hn0.le
      have hstep_lt : (b - a) / n < δ := by
        have hN_le : (N : ℝ) ≤ n := Nat.cast_le.2 hnN
        have : (b - a) / δ < n := hN.trans_le hN_le
        rw [div_lt_iff₀ hδ] at this
        rw [div_lt_iff₀ hn0]
        linarith
      have hstep_eq : ∀ k : ℕ, x n (k + 1) - x n k = (b - a) / n := fun k => by
        simp only [x, Nat.cast_add, Nat.cast_one]; ring
      have hdiam_k : ∀ k : Fin n,
          Metric.ediam (t n k) ^ (1 : ℝ) ≤
            ENNReal.ofReal ((‖γ' (x n k)‖ + ε) * ((b - a) / n)) := by
        intro k
        rw [ENNReal.rpow_one]
        refine Metric.ediam_le_of_forall_dist_le fun p hp q hq => ?_
        rcases hp with ⟨u, hu, rfl⟩
        rcases hq with ⟨v, hv, rfl⟩
        have hsub : Set.Icc (x n k) (x n (k + 1)) ⊆ Set.Icc a b := subdiv_mem_Icc hab k.isLt
        have hle : x n k ≤ x n (k + 1) := by linarith [hstep_eq k, hstep_pos]
        have hx_mem : x n k ∈ Set.Icc a b := hsub (Set.left_mem_Icc.2 hle)
        have hbound_s : ∀ s ∈ Set.Icc (x n k) (x n (k + 1)), ‖γ' s‖ ≤ ‖γ' (x n k)‖ + ε := by
          intro s hs
          have hdist : dist s (x n k) < δ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
            linarith [hs.2, hstep_eq k]
          have hdiff := hucδ s (hsub hs) (x n k) hx_mem hdist
          rw [dist_eq_norm] at hdiff
          linarith [norm_sub_norm_le (γ' s) (γ' (x n k))]
        have hmvt := (convex_Icc (x n k) (x n (k + 1))).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun s hs => (hderiv s (hsub hs)).hasDerivWithinAt) hbound_s hv hu
        have huv : ‖u - v‖ ≤ (b - a) / n := by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [hu.1, hu.2, hv.1, hv.2, hstep_eq k]
        rw [dist_eq_norm]
        exact hmvt.trans (mul_le_mul_of_nonneg_left huv (by positivity))
      have hint_k : ∀ k : Fin n,
          (‖γ' (x n k)‖ - ε) * ((b - a) / n) ≤ ∫ s in x n k..x n (k + 1), ‖γ' s‖ := by
        intro k
        have hsub : Set.Icc (x n k) (x n (k + 1)) ⊆ Set.Icc a b := subdiv_mem_Icc hab k.isLt
        have hle : x n k ≤ x n (k + 1) := by linarith [hstep_eq k, hstep_pos]
        have hmono : ∫ s in x n k..x n (k + 1), (‖γ' (x n k)‖ - ε) ≤
            ∫ s in x n k..x n (k + 1), ‖γ' s‖ := by
          refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
            (hint.mono_set (by rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]; exact hsub)) ?_
          intro s hs
          have hdist : dist s (x n k) < δ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
            linarith [hs.2, hstep_eq k]
          have hdiff := hucδ (x n k) (hsub (Set.left_mem_Icc.2 hle)) s (hsub hs) (by rwa [dist_comm])
          rw [dist_eq_norm] at hdiff
          linarith [norm_sub_norm_le (γ' (x n k)) (γ' s)]
        have hconst : ∫ s in x n k..x n (k + 1), (‖γ' (x n k)‖ - ε) =
            (‖γ' (x n k)‖ - ε) * ((b - a) / n) := by
          rw [intervalIntegral.integral_const, hstep_eq k, smul_eq_mul, mul_comm]
        linarith
      calc (∑ k : Fin n, Metric.ediam (t n k) ^ (1 : ℝ))
          ≤ ∑ k : Fin n, ENNReal.ofReal ((‖γ' (x n k)‖ + ε) * ((b - a) / n)) :=
            Finset.sum_le_sum fun k _ => hdiam_k k
        _ = ENNReal.ofReal (∑ k : Fin n, (‖γ' (x n k)‖ + ε) * ((b - a) / n)) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro k _; positivity
        _ ≤ ENNReal.ofReal ((∫ s in a..b, ‖γ' s‖) + 2 * ε * (b - a)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hsum_int : ∑ k : Fin n, ∫ s in x n k..x n (k + 1), ‖γ' s‖ =
                ∫ s in a..b, ‖γ' s‖ := by
              rw [Fin.sum_univ_eq_sum_range (fun k => ∫ s in x n k..x n (k + 1), ‖γ' s‖)]
              have h0 : x n 0 = a := by simp [x]
              have hn_end : x n n = b := by
                simp only [x]; rw [mul_comm (n : ℝ), mul_div_assoc, div_self hn0.ne', mul_one]; ring
              rw [← h0, ← hn_end]
              refine intervalIntegral.sum_integral_adjacent_intervals fun k hk => ?_
              have hle_k : x n k ≤ x n (k + 1) := by linarith [hstep_eq k, hstep_pos]
              refine hint.mono_set ?_
              rw [Set.uIcc_of_le hle_k, Set.uIcc_of_le hab]
              exact subdiv_mem_Icc hab hk
            have hsum_k : ∀ k : Fin n,
                (‖γ' (x n k)‖ + ε) * ((b - a) / n) ≤
                  (∫ s in x n k..x n (k + 1), ‖γ' s‖) + 2 * ε * ((b - a) / n) := by
              intro k; linarith [hint_k k]
            calc ∑ k : Fin n, (‖γ' (x n k)‖ + ε) * ((b - a) / n)
                ≤ ∑ k : Fin n, ((∫ s in x n k..x n (k + 1), ‖γ' s‖) + 2 * ε * ((b - a) / n)) :=
                  Finset.sum_le_sum fun k _ => hsum_k k
              _ = (∑ k : Fin n, ∫ s in x n k..x n (k + 1), ‖γ' s‖) +
                    ∑ _k : Fin n, 2 * ε * ((b - a) / n) := Finset.sum_add_distrib
              _ = (∫ s in a..b, ‖γ' s‖) + 2 * ε * (b - a) := by
                  rw [hsum_int, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  congr 1; field_simp
    refine hmain.trans (liminf_le_of_le (by isBoundedDefault) fun c hc => ?_)
    obtain ⟨n, hn1, hn2⟩ := (hc.and hbound).exists
    exact hn1.trans hn2
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) / (2 * (b - a)) := by
    have hba : 0 < b - a := sub_pos.2 hab_lt; positivity
  calc μH[1] (γ '' Set.Icc a b)
      ≤ ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) + 2 * ((ε : ℝ) / (2 * (b - a))) * (b - a)) :=
        hlip _ hε'
    _ = ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) + (ε : ℝ)) := by congr 1; field_simp
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖γ' t‖) + ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (∫ t in a..b, ‖γ' t‖) + ε := by simp

lemma measurableSet_image_Ico {a b c d : ℝ} (hab : a ≤ b) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc a b)) :
    MeasurableSet (γ '' Set.Ico c d) := by
  have hIco : Set.Ico c d = ⋃ m : ℕ, Set.Icc c (d - (d - c) / (m + 2 : ℝ)) := by
    ext t
    simp only [Set.mem_Ico, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · rintro ⟨hct, htd⟩
      obtain ⟨m, hm⟩ := exists_nat_gt ((d - c) / (d - t))
      refine ⟨m, hct, ?_⟩
      have hdt : 0 < d - t := sub_pos.2 htd
      have hdc : 0 < d - c := sub_pos.2 hcd
      have hm_pos : (0 : ℝ) < m := (div_pos hdc hdt).trans hm
      have hm2 : (m : ℝ) < m + 2 := by linarith
      have hdiv : (d - c) / ((m : ℝ) + 2) < (d - c) / m :=
        div_lt_div_of_pos_left hdc hm_pos hm2
      have hdiv2 : (d - c) / m < d - t := (div_lt_iff₀ hm_pos).2 (by
        have := (div_lt_iff₀ hdt).1 hm; linarith)
      linarith
    · rintro ⟨m, hct, htm⟩
      refine ⟨hct, ?_⟩
      have hdc : 0 < d - c := sub_pos.2 hcd
      have : 0 < (d - c) / (m + 2 : ℝ) := div_pos hdc (by positivity)
      linarith
  rw [hIco, Set.image_iUnion]
  refine MeasurableSet.iUnion fun m => ?_
  have hsub : Set.Icc c (d - (d - c) / (m + 2 : ℝ)) ⊆ Set.Icc a b := by
    intro t ⟨h1, h2⟩
    have hdc : 0 < d - c := sub_pos.2 hcd
    have : 0 ≤ (d - c) / (m + 2 : ℝ) := div_nonneg hdc.le (by positivity)
    exact ⟨hac.trans h1, h2.trans (by linarith)⟩
  exact (isCompact_Icc.image_of_continuousOn (hcont.mono hsub)).measurableSet

lemma integral_le_hausdorffMeasure_image {a b : ℝ} (hab : a ≤ b) (γ γ' : ℝ → ℂ)
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt γ (γ' t) t)
    (hcont : ContinuousOn γ' (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    ENNReal.ofReal (∫ t in a..b, ‖γ' t‖) ≤ μH[1] (γ '' Set.Icc a b) := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp
  have hcont_γ : ContinuousOn γ (Set.Icc a b) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hcont_norm : ContinuousOn (fun t => ‖γ' t‖) (Set.Icc a b) := hcont.norm
  have hint_norm : IntervalIntegrable (fun t => ‖γ' t‖) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont_norm
  have hint_γ' : IntervalIntegrable γ' volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcont
  have hlow : ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - 2 * ε * (b - a)) ≤ μH[1] (γ '' Set.Icc a b) := by
    intro ε hε
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hcont
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hucδ⟩ := huc ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    have hN_pos : 0 < N := by
      have : (0 : ℝ) < (b - a) / δ := div_pos (sub_pos.2 hab_lt) hδ
      exact_mod_cast this.trans hN
    let n := N
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hN_pos
    have hstep_pos : 0 < (b - a) / n := div_pos (sub_pos.2 hab_lt) hn0
    have hstep_lt : (b - a) / n < δ := by
      rw [div_lt_iff₀ hδ] at hN
      rw [div_lt_iff₀ hn0]
      linarith
    let x : ℕ → ℝ := fun k => a + (k : ℝ) * (b - a) / n
    let S : Fin n → Set ℂ := fun k => γ '' Set.Ico (x k) (x (k + 1))
    have hstep_eq : ∀ k : ℕ, x (k + 1) - x k = (b - a) / n := fun k => by
      simp only [x, Nat.cast_add, Nat.cast_one]; ring
    have hstep_le : ∀ k : ℕ, x k < x (k + 1) := fun k => by
      linarith [hstep_eq k, hstep_pos]
    have hsub : ∀ k : Fin n, Set.Icc (x k) (x (k + 1)) ⊆ Set.Icc a b :=
      fun k => subdiv_mem_Icc hab k.isLt
    have hmeas : ∀ k : Fin n, MeasurableSet (S k) := fun k => by
      have hx_ab := hsub k
      exact measurableSet_image_Ico hab (hx_ab (Set.left_mem_Icc.2 (hstep_le k).le)).1
        (hstep_le k) (hx_ab (Set.right_mem_Icc.2 (hstep_le k).le)).2 γ hcont_γ
    have hdisj : (Set.univ : Set (Fin n)).PairwiseDisjoint S := by
      intro i _ j _ hij
      rw [Function.onFun, Set.disjoint_iff]
      intro z ⟨⟨ti, hti, hti_eq⟩, ⟨tj, htj, htj_eq⟩⟩
      have hti_ab : ti ∈ Set.Icc a b := hsub i (Set.Ico_subset_Icc_self hti)
      have htj_ab : tj ∈ Set.Icc a b := hsub j (Set.Ico_subset_Icc_self htj)
      have hteq : ti = tj := hinj hti_ab htj_ab (hti_eq.trans htj_eq.symm)
      rw [hteq] at hti
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
        have hxij : x (i + 1) ≤ x j := by
          simp only [x, Nat.cast_add, Nat.cast_one]
          have hba : 0 ≤ b - a := sub_nonneg.2 hab
          have : ((i : ℝ) + 1) * (b - a) / n ≤ (j : ℝ) * (b - a) / n := by gcongr
          linarith
        linarith [hti.2, htj.1]
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
        have hxji : x (j + 1) ≤ x i := by
          simp only [x, Nat.cast_add, Nat.cast_one]
          have hba : 0 ≤ b - a := sub_nonneg.2 hab
          have : ((j : ℝ) + 1) * (b - a) / n ≤ (i : ℝ) * (b - a) / n := by gcongr
          linarith
        linarith [hti.1, htj.2]
    have hS_meas_k : ∀ k : Fin n, ENNReal.ofReal ‖γ (x (k + 1)) - γ (x k)‖ ≤ μH[1] (S k) := by
      intro k
      let v : ℂ := γ (x (k + 1)) - γ (x k)
      by_cases hv : v = 0
      · simp [v, hv]
      · let u : ℂ := (‖v‖ : ℂ)⁻¹ * v
        have hu_norm : ‖u‖ = 1 := by
          simp [u, norm_inv, norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
        let proj : ℂ → ℝ := fun z => (star u * z).re
        have hproj_lip : LipschitzWith 1 proj := by
          refine LipschitzWith.of_dist_le_mul fun z₁ z₂ => ?_
          rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
          dsimp [proj]
          rw [← Complex.sub_re, ← mul_sub]
          calc |(star u * (z₁ - z₂)).re| ≤ ‖star u * (z₁ - z₂)‖ := Complex.abs_re_le_norm _
            _ = ‖star u‖ * ‖z₁ - z₂‖ := norm_mul _ _
            _ = ‖z₁ - z₂‖ := by simp [hu_norm]
        have hproj_diff : proj (γ (x (k + 1))) - proj (γ (x k)) = ‖v‖ := by
          dsimp [proj]
          rw [← Complex.sub_re, ← mul_sub]
          change (star u * v).re = ‖v‖
          have hvu : star u * v = (‖v‖ : ℂ) := by
            dsimp [u]
            rw [map_mul, map_inv₀, Complex.conj_ofReal, mul_assoc,
              mul_comm ((starRingEnd ℂ) v) v, Complex.mul_conj']
            have hnv : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv)
            field_simp
          rw [hvu, Complex.ofReal_re]
        have hproj_cont : ContinuousOn (proj ∘ γ) (Set.Icc (x k) (x (k + 1))) :=
          hproj_lip.continuous.comp_continuousOn (hcont_γ.mono (hsub k))
        have hivt := intermediate_value_Ico (hstep_le k).le hproj_cont
        have himg_sub : Set.Ico (proj (γ (x k))) (proj (γ (x (k + 1)))) ⊆ proj '' S k := by
          intro y hy
          rcases hivt hy with ⟨t, ht, rfl⟩
          exact ⟨γ t, ⟨t, ht, rfl⟩, rfl⟩
        calc ENNReal.ofReal ‖v‖
            = ENNReal.ofReal (proj (γ (x (k + 1))) - proj (γ (x k))) := by rw [hproj_diff]
          _ = volume (Set.Ico (proj (γ (x k))) (proj (γ (x (k + 1))))) := by rw [Real.volume_Ico]
          _ = μH[1] (Set.Ico (proj (γ (x k))) (proj (γ (x (k + 1))))) := by
              rw [MeasureTheory.hausdorffMeasure_real]
          _ ≤ μH[1] (proj '' S k) := measure_mono himg_sub
          _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (S k) :=
              hproj_lip.hausdorffMeasure_image_le zero_le_one (S k)
          _ = μH[1] (S k) := by simp
    have hnorm_k : ∀ k : Fin n,
        (‖γ' (x k)‖ - ε) * ((b - a) / n) ≤ ‖γ (x (k + 1)) - γ (x k)‖ := by
      intro k
      have hle : x k ≤ x (k + 1) := (hstep_le k).le
      have hftc : ∫ t in x k..x (k + 1), γ' t = γ (x (k + 1)) - γ (x k) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle (hcont_γ.mono (hsub k))
          (fun t ht => hderiv t (hsub k (Set.Ioo_subset_Icc_self ht)))
          (hint_γ'.mono_set (by rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]; exact hsub k))
      have hconst : ∫ _t in x k..x (k + 1), γ' (x k) = ((b - a) / n) • γ' (x k) := by
        rw [intervalIntegral.integral_const, hstep_eq k]
      have hint_sub : ∫ t in x k..x (k + 1), (γ' t - γ' (x k)) =
          (γ (x (k + 1)) - γ (x k)) - ((b - a) / n) • γ' (x k) := by
        rw [intervalIntegral.integral_sub
          (hint_γ'.mono_set (by rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]; exact hsub k))
          intervalIntegrable_const, hftc, hconst]
      have hle_eps : ∀ t ∈ Set.Icc (x k) (x (k + 1)), ‖γ' t - γ' (x k)‖ ≤ ε := by
        intro t ht
        have hdist : dist t (x k) < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht.1)]
          linarith [ht.2, hstep_eq k]
        rw [← dist_eq_norm]
        exact (hucδ t (hsub k ht) (x k) (hsub k (Set.left_mem_Icc.2 hle)) hdist).le
      have hnorm_diff : ‖(γ (x (k + 1)) - γ (x k)) - ((b - a) / n) • γ' (x k)‖ ≤
          ε * ((b - a) / n) := by
        rw [← hint_sub]
        calc ‖∫ t in x k..x (k + 1), (γ' t - γ' (x k))‖
            ≤ ∫ t in x k..x (k + 1), ‖γ' t - γ' (x k)‖ :=
              intervalIntegral.norm_integral_le_integral_norm hle
          _ ≤ ∫ _t in x k..x (k + 1), ε := by
              refine intervalIntegral.integral_mono_on hle
                (ContinuousOn.intervalIntegrable_of_Icc hle
                  ((hcont.mono (hsub k)).sub continuousOn_const).norm)
                intervalIntegrable_const hle_eps
          _ = ε * ((b - a) / n) := by
              rw [intervalIntegral.integral_const, hstep_eq k, smul_eq_mul, mul_comm]
      have hrev := norm_sub_norm_le (((b - a) / n) • γ' (x k)) (γ (x (k + 1)) - γ (x k))
      have hnorm_smul : ‖((b - a) / n) • γ' (x k)‖ = ‖γ' (x k)‖ * ((b - a) / n) := by
        rw [norm_smul, Real.norm_of_nonneg hstep_pos.le, mul_comm]
      rw [norm_sub_rev (((b - a) / n) • γ' (x k)), hnorm_smul] at hrev
      have hle1 : ‖γ' (x k)‖ * ((b - a) / n) - ‖γ (x (k + 1)) - γ (x k)‖ ≤ ε * ((b - a) / n) :=
        hrev.trans hnorm_diff
      calc (‖γ' (x k)‖ - ε) * ((b - a) / n)
          = ‖γ' (x k)‖ * ((b - a) / n) - ε * ((b - a) / n) := by ring
        _ ≤ ‖γ (x (k + 1)) - γ (x k)‖ := by linarith [hle1]
    have hint_k : ∀ k : Fin n,
        ∫ t in x k..x (k + 1), ‖γ' t‖ ≤ (‖γ' (x k)‖ + ε) * ((b - a) / n) := by
      intro k
      have hle : x k ≤ x (k + 1) := (hstep_le k).le
      have hle_eps : ∀ t ∈ Set.Icc (x k) (x (k + 1)), ‖γ' t‖ ≤ ‖γ' (x k)‖ + ε := by
        intro t ht
        have hdist : dist t (x k) < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht.1)]
          linarith [ht.2, hstep_eq k]
        have hd := hucδ t (hsub k ht) (x k) (hsub k (Set.left_mem_Icc.2 hle)) hdist
        rw [dist_eq_norm] at hd
        linarith [norm_sub_norm_le (γ' t) (γ' (x k))]
      calc ∫ t in x k..x (k + 1), ‖γ' t‖
          ≤ ∫ _t in x k..x (k + 1), (‖γ' (x k)‖ + ε) :=
            intervalIntegral.integral_mono_on hle
              (hint_norm.mono_set (by rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]; exact hsub k))
              intervalIntegrable_const hle_eps
        _ = (‖γ' (x k)‖ + ε) * ((b - a) / n) := by
            rw [intervalIntegral.integral_const, hstep_eq k, smul_eq_mul, mul_comm]
    have hsum_int : ∑ k : Fin n, ∫ t in x k..x (k + 1), ‖γ' t‖ = ∫ t in a..b, ‖γ' t‖ := by
      rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in x k..x (k + 1), ‖γ' t‖)]
      have h0 : x 0 = a := by simp [x]
      have hn_end : x n = b := by
        simp only [x]; rw [mul_comm (n : ℝ), mul_div_assoc, div_self hn0.ne', mul_one]; ring
      rw [← h0, ← hn_end]
      refine intervalIntegral.sum_integral_adjacent_intervals fun k hk => ?_
      refine hint_norm.mono_set ?_
      rw [Set.uIcc_of_le (hstep_le k).le, Set.uIcc_of_le hab]
      exact subdiv_mem_Icc hab hk
    have hsum_S : ∑ k : Fin n, μH[1] (S k) ≤ μH[1] (γ '' Set.Icc a b) := by
      have hbi : μH[1] (⋃ k ∈ (Finset.univ : Finset (Fin n)), S k) =
          ∑ k ∈ (Finset.univ : Finset (Fin n)), μH[1] (S k) := by
        refine MeasureTheory.measure_biUnion_finset ?_ fun k _ => hmeas k
        simpa using hdisj
      rw [← hbi]
      refine measure_mono ?_
      refine Set.iUnion₂_subset fun k _ => ?_
      exact Set.image_mono (Set.Ico_subset_Icc_self.trans (hsub k))
    have hle_sum : (∫ t in a..b, ‖γ' t‖) - 2 * ε * (b - a) ≤
        ∑ k : Fin n, ‖γ (x (k + 1)) - γ (x k)‖ := by
      have h_each : ∀ k : Fin n,
          (∫ t in x k..x (k + 1), ‖γ' t‖) - 2 * ε * ((b - a) / n) ≤
            ‖γ (x (k + 1)) - γ (x k)‖ := fun k => by
        linarith [hint_k k, hnorm_k k]
      calc (∫ t in a..b, ‖γ' t‖) - 2 * ε * (b - a)
          = ∑ k : Fin n, ((∫ t in x k..x (k + 1), ‖γ' t‖) - 2 * ε * ((b - a) / n)) := by
            rw [Finset.sum_sub_distrib, hsum_int, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            congr 1; field_simp
        _ ≤ ∑ k : Fin n, ‖γ (x (k + 1)) - γ (x k)‖ := Finset.sum_le_sum fun k _ => h_each k
    calc ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - 2 * ε * (b - a))
        ≤ ENNReal.ofReal (∑ k : Fin n, ‖γ (x (k + 1)) - γ (x k)‖) :=
          ENNReal.ofReal_le_ofReal hle_sum
      _ = ∑ k : Fin n, ENNReal.ofReal ‖γ (x (k + 1)) - γ (x k)‖ := by
          rw [ENNReal.ofReal_sum_of_nonneg]; intro k _; exact norm_nonneg _
      _ ≤ ∑ k : Fin n, μH[1] (S k) := Finset.sum_le_sum fun k _ => hS_meas_k k
      _ ≤ μH[1] (γ '' Set.Icc a b) := hsum_S
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) / (2 * (b - a)) := by
    have hba : 0 < b - a := sub_pos.2 hab_lt; positivity
  have h1 := hlow _ hε'
  have h2 : (∫ t in a..b, ‖γ' t‖) - 2 * ((ε : ℝ) / (2 * (b - a))) * (b - a) =
      (∫ t in a..b, ‖γ' t‖) - (ε : ℝ) := by congr 1; field_simp
  rw [h2] at h1
  calc ENNReal.ofReal (∫ t in a..b, ‖γ' t‖)
      ≤ ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - (ε : ℝ) + (ε : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - (ε : ℝ)) + ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_add_le
    _ ≤ μH[1] (γ '' Set.Icc a b) + ε := by gcongr; simp

/- Step 3: Complex square root and parameterization of lemniscates -/

noncomputable def csqrt (w : ℂ) : ℂ := Complex.exp ((1 / 2 : ℂ) * Complex.log w)

lemma csqrt_sq {w : ℂ} (hw : w ≠ 0) : csqrt w ^ 2 = w := by
  rw [csqrt, ← Complex.exp_nat_mul]
  have h1 : (2 : ℕ) * ((1 / 2 : ℂ) * Complex.log w) = Complex.log w := by push_cast; ring
  rw [h1, Complex.exp_log hw]

lemma norm_csqrt {w : ℂ} (hw : w ≠ 0) : ‖csqrt w‖ = ‖w‖ ^ (1 / 2 : ℝ) := by
  rw [csqrt, Complex.norm_exp]
  have hre : ((1 / 2 : ℂ) * Complex.log w).re = Real.log ‖w‖ * (1 / 2 : ℝ) := by
    rw [Complex.mul_re]
    have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have h2 : (1 / 2 : ℂ).im = 0 := by norm_num
    rw [h1, h2, Complex.log_re]; ring
  rw [hre, Real.rpow_def_of_pos (norm_pos_iff.2 hw)]

lemma hasDerivAt_csqrt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt csqrt (1 / (2 * csqrt w)) w := by
  have hlog : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hw
  have hmul : HasDerivAt (fun z => (1 / 2 : ℂ) * Complex.log z) ((1 / 2 : ℂ) * w⁻¹) w :=
    hlog.const_mul (1 / 2 : ℂ)
  have hexp := hmul.cexp
  refine hexp.congr_deriv ?_
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hsq : csqrt w ^ 2 = w := csqrt_sq hw0
  have hc0 : csqrt w ≠ 0 := by
    intro h
    rw [h, sq, mul_zero] at hsq
    exact hw0 hsq.symm
  change csqrt w * ((1 / 2 : ℂ) * w⁻¹) = 1 / (2 * csqrt w)
  have h1 : csqrt w * w⁻¹ = (csqrt w)⁻¹ := by
    apply mul_left_cancel₀ hc0
    calc csqrt w * (csqrt w * w⁻¹) = csqrt w ^ 2 * w⁻¹ := by ring
      _ = w * w⁻¹ := by rw [hsq]
      _ = 1 := mul_inv_cancel₀ hw0
      _ = csqrt w * (csqrt w)⁻¹ := (mul_inv_cancel₀ hc0).symm
  rw [← mul_assoc, mul_comm (csqrt w) (1 / 2 : ℂ), mul_assoc, h1]
  ring

lemma re_csqrt_pos {w : ℂ} (hw : w ∈ Complex.slitPlane) : 0 < (csqrt w).re := by
  rw [csqrt, Complex.exp_re]
  have him : ((1 / 2 : ℂ) * Complex.log w).im = w.arg / 2 := by
    rw [Complex.mul_im]
    have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have him0 : (1 / 2 : ℂ).im = 0 := by norm_num
    rw [hre, him0, Complex.log_im]; ring
  rw [him]
  have harg_lt : w.arg < π := by
    refine lt_of_le_of_ne (Complex.arg_le_pi w) fun heq => ?_
    rw [Complex.arg_eq_pi_iff] at heq
    rw [Complex.mem_slitPlane_iff] at hw
    rcases hw with h | h
    · linarith [heq.1]
    · exact h heq.2
  have harg_gt : -π < w.arg := Complex.neg_pi_lt_arg w
  have hcos : 0 < Real.cos (w.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  exact mul_pos (Real.exp_pos _) hcos

noncomputable def ker (r θ : ℝ) : ℝ :=
  (r ^ 2 + 2 * r * Real.cos θ + 1) ^ (-(1 / 4 : ℝ))

lemma ker_periodic (r : ℝ) : Function.Periodic (ker r) (2 * π) := by
  intro θ; simp [ker, Real.cos_add_two_pi]

lemma ker_nonneg (r θ : ℝ) : 0 ≤ ker r θ := by
  have h1 : 0 ≤ r ^ 2 + 2 * r * Real.cos θ + 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (r + Real.cos θ)]
  exact Real.rpow_nonneg h1 _

lemma norm_add_exp_sq (r θ : ℝ) :
    ‖(r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = r ^ 2 + 2 * r * Real.cos θ + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)).re = r + Real.cos θ := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : ((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma norm_eq_sq_rpow_half (z : ℂ) : ‖z‖ = (‖z‖ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
  norm_num

lemma norm_add_exp_pos_of_ne {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≠ 1) (θ : ℝ) :
    0 < ‖(r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  rw [norm_pos_iff]
  intro h
  have hsq : r ^ 2 + 2 * r * Real.cos θ + 1 = 0 := by
    rw [← norm_add_exp_sq, h, norm_zero, sq, mul_zero]
  have hge : (r - 1) ^ 2 ≤ r ^ 2 + 2 * r * Real.cos θ + 1 := by
    nlinarith [Real.neg_one_le_cos θ]
  have : r - 1 = 0 := by nlinarith
  exact hr1 (sub_eq_zero.1 this)

lemma slitPlane_pos_half {r : ℝ} (hr0 : 0 ≤ r) {θ : ℝ} (hθ : θ ∈ Set.Icc (-(π / 2)) (π / 2)) :
    (r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.exp_ofReal_mul_I_re,
    Complex.add_im, Complex.ofReal_im, zero_add, Complex.exp_ofReal_mul_I_im]
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
  rcases eq_or_lt_of_le (add_nonneg hr0 hcos) with heq | hpos
  · right
    have hcos0 : Real.cos θ = 0 := by linarith
    intro hsin0
    have := Real.sin_sq_add_cos_sq θ
    rw [hcos0, hsin0] at this
    norm_num at this
  · exact Or.inl hpos

lemma slitPlane_neg_half {r : ℝ} (hr1 : r < 1) {θ : ℝ} (hθ : θ ∈ Set.Icc (π / 2) (3 * π / 2)) :
    -((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.exp_ofReal_mul_I_re,
    Complex.neg_im, Complex.add_im, Complex.ofReal_im, zero_add, Complex.exp_ofReal_mul_I_im]
  have hcos : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
  by_cases hsin : Real.sin θ = 0
  · left
    have hcs : Real.cos θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    have hcm1 : Real.cos θ = -1 := by nlinarith
    linarith
  · right; exact neg_ne_zero.2 hsin

lemma slitPlane_gt_one {r : ℝ} (hr1 : 1 < r) (θ : ℝ) :
    (r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.add_re, Complex.ofReal_re, Complex.exp_ofReal_mul_I_re]
  linarith [Real.neg_one_le_cos θ]

lemma norm_eq_one_exists_angle {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ θ ∈ Set.Icc (-(π / 2)) (3 * π / 2), Complex.exp ((θ : ℂ) * Complex.I) = w := by
  have hexp := Complex.norm_mul_exp_arg_mul_I w
  rw [hw, Complex.ofReal_one, one_mul] at hexp
  by_cases h : -(π / 2) ≤ w.arg
  · exact ⟨w.arg, ⟨h, (Complex.arg_le_pi w).trans (by linarith [Real.pi_pos])⟩, hexp⟩
  · refine ⟨w.arg + 2 * π, ⟨by linarith [Complex.neg_pi_lt_arg w], by linarith⟩, ?_⟩
    rw [show ((w.arg + 2 * π : ℝ) : ℂ) * Complex.I =
      (w.arg : ℂ) * Complex.I + (2 * π : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, hexp]

lemma hausdorffMeasure_neg_image (S : Set ℂ) : μH[1] ((fun z => -z) '' S) = μH[1] S :=
  (Isometry.of_dist_eq fun x y => dist_neg_neg x y).hausdorffMeasure_image (Or.inl zero_le_one) S

lemma norm_inv_two_csqrt (r θ : ℝ) (hw0 : (r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) ≠ 0) :
    ‖(Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) /
        (2 * csqrt ((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)))‖ =
      (1 / 2 : ℝ) * ker r θ := by
  simp only [norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_ofNat]
  rw [norm_csqrt hw0]
  have hpos : 0 < ‖(r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ := norm_pos_iff.2 hw0
  rw [one_div, mul_inv, mul_comm (2⁻¹ : ℝ), ← Real.rpow_neg hpos.le]
  rw [norm_eq_sq_rpow_half, norm_add_exp_sq]
  have hnn : 0 ≤ r ^ 2 + 2 * r * Real.cos θ + 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (r + Real.cos θ)]
  rw [← Real.rpow_mul hnn]
  norm_num [ker]
  ring

lemma lemniscateLength_sub_ofReal_le_lt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Erdos114.lemniscateLength (X ^ 2 - C (r : ℂ)) ≤ ENNReal.ofReal (∫ θ in -π..π, ker r θ) := by
  let γ₁ : ℝ → ℂ := fun θ => csqrt ((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I))
  let γ₁' : ℝ → ℂ := fun θ => (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) / (2 * γ₁ θ)
  let γ₂ : ℝ → ℂ := fun θ => Complex.I * csqrt (-((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)))
  let γ₂' : ℝ → ℂ := fun θ =>
    Complex.I * (-(Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) /
      (2 * csqrt (-((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)))))
  have hderiv₁ : ∀ θ ∈ Set.Icc (-(π / 2)) (π / 2), HasDerivAt γ₁ (γ₁' θ) θ := by
    intro θ hθ
    have hsp := slitPlane_pos_half hr0 hθ
    have hinner : HasDerivAt (fun t : ℝ => (r : ℂ) + Complex.exp ((t : ℂ) * Complex.I))
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
      exact (h1.cexp.const_add (r : ℂ)).congr_deriv (by ring)
    refine ((hasDerivAt_csqrt hsp).comp θ hinner).congr_deriv ?_
    dsimp only [γ₁', γ₁]; ring
  have hderiv₂ : ∀ θ ∈ Set.Icc (π / 2) (3 * π / 2), HasDerivAt γ₂ (γ₂' θ) θ := by
    intro θ hθ
    have hsp := slitPlane_neg_half hr1 hθ
    have hinner : HasDerivAt (fun t : ℝ => -((r : ℂ) + Complex.exp ((t : ℂ) * Complex.I)))
        (-(Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) θ := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
      exact ((h1.cexp.const_add (r : ℂ)).neg).congr_deriv (by ring)
    refine (((hasDerivAt_csqrt hsp).comp θ hinner).const_mul Complex.I).congr_deriv ?_
    dsimp only [γ₂']; ring
  have hcont₁ : ContinuousOn γ₁' (Set.Icc (-(π / 2)) (π / 2)) := by
    intro θ hθ
    have hsp := slitPlane_pos_half hr0 hθ
    have hc_ne : γ₁ θ ≠ 0 := by
      intro h
      have := csqrt_sq (Complex.slitPlane_ne_zero hsp)
      change γ₁ θ ^ 2 = _ at this
      rw [h, sq, mul_zero] at this
      exact Complex.slitPlane_ne_zero hsp this.symm
    have hnum : ContinuousAt (fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) θ := by
      fun_prop
    exact (hnum.div (continuousAt_const.mul (hderiv₁ θ hθ).continuousAt)
      (mul_ne_zero two_ne_zero hc_ne)).continuousWithinAt
  have hcont₂ : ContinuousOn γ₂' (Set.Icc (π / 2) (3 * π / 2)) := by
    intro θ hθ
    have hsp := slitPlane_neg_half hr1 hθ
    let g : ℝ → ℂ := fun t => csqrt (-((r : ℂ) + Complex.exp ((t : ℂ) * Complex.I)))
    have hg_deriv : HasDerivAt g (-(Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) / (2 * g θ)) θ := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
      have hinner : HasDerivAt (fun t : ℝ => -((r : ℂ) + Complex.exp ((t : ℂ) * Complex.I)))
          (-(Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) θ :=
        ((h1.cexp.const_add (r : ℂ)).neg).congr_deriv (by ring)
      refine ((hasDerivAt_csqrt hsp).comp θ hinner).congr_deriv ?_
      dsimp only [g]; ring
    have hg_ne : g θ ≠ 0 := by
      intro h
      have := csqrt_sq (Complex.slitPlane_ne_zero hsp)
      change g θ ^ 2 = _ at this
      rw [h, sq, mul_zero] at this
      exact Complex.slitPlane_ne_zero hsp this.symm
    have hnum : ContinuousAt (fun t : ℝ => -(Complex.I * Complex.exp ((t : ℂ) * Complex.I))) θ := by
      fun_prop
    exact (continuousAt_const.mul
      (hnum.div (continuousAt_const.mul hg_deriv.continuousAt)
        (mul_ne_zero two_ne_zero hg_ne))).continuousWithinAt
  have hnorm₁ : ∀ θ ∈ Set.Icc (-(π / 2)) (π / 2), ‖γ₁' θ‖ = (1 / 2 : ℝ) * ker r θ :=
    fun θ hθ => norm_inv_two_csqrt r θ (Complex.slitPlane_ne_zero (slitPlane_pos_half hr0 hθ))
  have hnorm₂ : ∀ θ ∈ Set.Icc (π / 2) (3 * π / 2), ‖γ₂' θ‖ = (1 / 2 : ℝ) * ker r θ := by
    intro θ hθ
    have hsp := slitPlane_neg_half hr1 hθ
    have hw0 := Complex.slitPlane_ne_zero hsp
    simp only [γ₂', norm_mul, Complex.norm_I, one_mul, norm_div, norm_neg,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_ofNat]
    rw [norm_csqrt hw0, norm_neg]
    have hpos : 0 < ‖(r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ :=
      norm_add_exp_pos_of_ne hr0 hr1.ne θ
    rw [one_div, mul_inv, mul_comm (2⁻¹ : ℝ), ← Real.rpow_neg hpos.le]
    rw [norm_eq_sq_rpow_half, norm_add_exp_sq]
    have hnn : 0 ≤ r ^ 2 + 2 * r * Real.cos θ + 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (r + Real.cos θ)]
    rw [← Real.rpow_mul hnn]
    norm_num [ker]
    ring
  have hcov : Erdos114.lemniscate (X ^ 2 - C (r : ℂ)) ⊆
      (γ₁ '' Set.Icc (-(π / 2)) (π / 2)) ∪ ((fun z => -z) '' (γ₁ '' Set.Icc (-(π / 2)) (π / 2))) ∪
      (γ₂ '' Set.Icc (π / 2) (3 * π / 2)) ∪ ((fun z => -z) '' (γ₂ '' Set.Icc (π / 2) (3 * π / 2))) := by
    intro z hz
    simp only [Erdos114.lemniscate, Set.mem_ofPred_eq, eval_sub, eval_pow, eval_X, eval_C] at hz
    obtain ⟨θ, hθ, hexp⟩ := norm_eq_one_exists_angle hz
    have hz2 : z ^ 2 = (r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) := by rw [hexp]; ring
    rcases le_total θ (π / 2) with hle | hge
    · have hθ1 : θ ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨hθ.1, hle⟩
      have hw0 := Complex.slitPlane_ne_zero (slitPlane_pos_half hr0 hθ1)
      have hsq : z ^ 2 = (γ₁ θ) ^ 2 := by rw [hz2, csqrt_sq hw0]
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨θ, hθ1, h.symm⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨γ₁ θ, ⟨θ, hθ1, rfl⟩, h.symm⟩))
    · have hθ2 : θ ∈ Set.Icc (π / 2) (3 * π / 2) := ⟨hge, hθ.2⟩
      have hw0 := Complex.slitPlane_ne_zero (slitPlane_neg_half hr1 hθ2)
      have hsq : z ^ 2 = (γ₂ θ) ^ 2 := by
        rw [hz2]; dsimp [γ₂]; rw [mul_pow, Complex.I_sq, csqrt_sq hw0]; ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
      · exact Or.inl (Or.inr ⟨θ, hθ2, h.symm⟩)
      · exact Or.inr ⟨γ₂ θ, ⟨θ, hθ2, rfl⟩, h.symm⟩
  have hm₁ := hausdorffMeasure_image_le_integral (by linarith [Real.pi_pos]) γ₁ γ₁' hderiv₁ hcont₁
  have hm₂ := hausdorffMeasure_image_le_integral (by linarith [Real.pi_pos]) γ₂ γ₂' hderiv₂ hcont₂
  have hi₁ : ∫ θ in -(π / 2)..(π / 2), ‖γ₁' θ‖ = (1 / 2 : ℝ) * ∫ θ in -(π / 2)..(π / 2), ker r θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ hθ =>
      hnorm₁ θ (by rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ))
  have hi₂ : ∫ θ in (π / 2)..(3 * π / 2), ‖γ₂' θ‖ = (1 / 2 : ℝ) * ∫ θ in (π / 2)..(3 * π / 2), ker r θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ hθ =>
      hnorm₂ θ (by rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ))
  have hker_cont : Continuous (ker r) := by
    refine Continuous.rpow (by fun_prop) continuous_const fun θ => Or.inl ?_
    rw [← norm_add_exp_sq]
    exact (sq_pos_of_pos (norm_add_exp_pos_of_ne hr0 hr1.ne θ)).ne'
  have hker_int1 : IntervalIntegrable (ker r) volume (-(π / 2)) (π / 2) :=
    hker_cont.intervalIntegrable _ _
  have hker_int2 : IntervalIntegrable (ker r) volume (π / 2) (3 * π / 2) :=
    hker_cont.intervalIntegrable _ _
  have hker_split : (∫ θ in -(π / 2)..(π / 2), ker r θ) + (∫ θ in (π / 2)..(3 * π / 2), ker r θ) =
      ∫ θ in -π..π, ker r θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals hker_int1 hker_int2]
    have hp := (ker_periodic r).intervalIntegral_add_eq (-(π / 2)) (-π)
    convert hp using 2 <;> ring
  have h_nn1 : 0 ≤ ∫ θ in -(π / 2)..(π / 2), ker r θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => ker_nonneg r θ
  have h_nn2 : 0 ≤ ∫ θ in (π / 2)..(3 * π / 2), ker r θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => ker_nonneg r θ
  calc Erdos114.lemniscateLength (X ^ 2 - C (r : ℂ))
      = μH[1] (Erdos114.lemniscate (X ^ 2 - C (r : ℂ))) := rfl
    _ ≤ μH[1] ((γ₁ '' Set.Icc (-(π / 2)) (π / 2)) ∪
          ((fun z => -z) '' (γ₁ '' Set.Icc (-(π / 2)) (π / 2))) ∪
          (γ₂ '' Set.Icc (π / 2) (3 * π / 2)) ∪
          ((fun z => -z) '' (γ₂ '' Set.Icc (π / 2) (3 * π / 2)))) := measure_mono hcov
    _ ≤ μH[1] (γ₁ '' Set.Icc (-(π / 2)) (π / 2)) +
          μH[1] ((fun z => -z) '' (γ₁ '' Set.Icc (-(π / 2)) (π / 2))) +
          μH[1] (γ₂ '' Set.Icc (π / 2) (3 * π / 2)) +
          μH[1] ((fun z => -z) '' (γ₂ '' Set.Icc (π / 2) (3 * π / 2))) := by
        refine (measure_union_le _ _).trans ?_; gcongr
        refine (measure_union_le _ _).trans ?_; gcongr
        exact measure_union_le _ _
    _ = 2 * μH[1] (γ₁ '' Set.Icc (-(π / 2)) (π / 2)) +
          2 * μH[1] (γ₂ '' Set.Icc (π / 2) (3 * π / 2)) := by
        rw [hausdorffMeasure_neg_image, hausdorffMeasure_neg_image]; ring
    _ ≤ 2 * ENNReal.ofReal ((1 / 2 : ℝ) * ∫ θ in -(π / 2)..(π / 2), ker r θ) +
          2 * ENNReal.ofReal ((1 / 2 : ℝ) * ∫ θ in (π / 2)..(3 * π / 2), ker r θ) := by
        rw [← hi₁, ← hi₂]; gcongr
    _ = ENNReal.ofReal ((∫ θ in -(π / 2)..(π / 2), ker r θ) +
          (∫ θ in (π / 2)..(3 * π / 2), ker r θ)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ = ENNReal.ofReal (∫ θ in -π..π, ker r θ) := by rw [hker_split]

lemma lemniscateLength_sub_ofReal_le_gt {r : ℝ} (hr1 : 1 < r) :
    Erdos114.lemniscateLength (X ^ 2 - C (r : ℂ)) ≤ ENNReal.ofReal (∫ θ in -π..π, ker r θ) := by
  let γ₁ : ℝ → ℂ := fun θ => csqrt ((r : ℂ) + Complex.exp ((θ : ℂ) * Complex.I))
  let γ₁' : ℝ → ℂ := fun θ => (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) / (2 * γ₁ θ)
  have hderiv₁ : ∀ θ ∈ Set.Icc (-π) π, HasDerivAt γ₁ (γ₁' θ) θ := by
    intro θ _
    have hsp := slitPlane_gt_one hr1 θ
    have hinner : HasDerivAt (fun t : ℝ => (r : ℂ) + Complex.exp ((t : ℂ) * Complex.I))
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
      exact (h1.cexp.const_add (r : ℂ)).congr_deriv (by ring)
    refine ((hasDerivAt_csqrt hsp).comp θ hinner).congr_deriv ?_
    dsimp only [γ₁', γ₁]; ring
  have hcont₁ : ContinuousOn γ₁' (Set.Icc (-π) π) := by
    intro θ hθ
    have hsp := slitPlane_gt_one hr1 θ
    have hc_ne : γ₁ θ ≠ 0 := by
      intro h
      have := csqrt_sq (Complex.slitPlane_ne_zero hsp)
      change γ₁ θ ^ 2 = _ at this
      rw [h, sq, mul_zero] at this
      exact Complex.slitPlane_ne_zero hsp this.symm
    have hnum : ContinuousAt (fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) θ := by
      fun_prop
    exact (hnum.div (continuousAt_const.mul (hderiv₁ θ hθ).continuousAt)
      (mul_ne_zero two_ne_zero hc_ne)).continuousWithinAt
  have hnorm₁ : ∀ θ ∈ Set.Icc (-π) π, ‖γ₁' θ‖ = (1 / 2 : ℝ) * ker r θ :=
    fun θ _ => norm_inv_two_csqrt r θ (Complex.slitPlane_ne_zero (slitPlane_gt_one hr1 θ))
  have hcov : Erdos114.lemniscate (X ^ 2 - C (r : ℂ)) ⊆
      (γ₁ '' Set.Icc (-π) π) ∪ ((fun z => -z) '' (γ₁ '' Set.Icc (-π) π)) := by
    intro z hz
    simp only [Erdos114.lemniscate, Set.mem_ofPred_eq, eval_sub, eval_pow, eval_X, eval_C] at hz
    have hexp := Complex.norm_mul_exp_arg_mul_I (z ^ 2 - (r : ℂ))
    rw [hz, Complex.ofReal_one, one_mul] at hexp
    have hθ : (z ^ 2 - (r : ℂ)).arg ∈ Set.Icc (-π) π :=
      ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    have hw0 := Complex.slitPlane_ne_zero (slitPlane_gt_one hr1 (z ^ 2 - (r : ℂ)).arg)
    have hsq : z ^ 2 = (γ₁ (z ^ 2 - (r : ℂ)).arg) ^ 2 := by
      rw [csqrt_sq hw0, hexp]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact Or.inl ⟨_, hθ, h.symm⟩
    · exact Or.inr ⟨γ₁ _, ⟨_, hθ, rfl⟩, h.symm⟩
  have hm := hausdorffMeasure_image_le_integral (by linarith [Real.pi_pos]) γ₁ γ₁' hderiv₁ hcont₁
  have hi : ∫ θ in -π..π, ‖γ₁' θ‖ = (1 / 2 : ℝ) * ∫ θ in -π..π, ker r θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ hθ =>
      hnorm₁ θ (by rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ))
  have h_nn : 0 ≤ ∫ θ in -π..π, ker r θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => ker_nonneg r θ
  calc Erdos114.lemniscateLength (X ^ 2 - C (r : ℂ))
      = μH[1] (Erdos114.lemniscate (X ^ 2 - C (r : ℂ))) := rfl
    _ ≤ μH[1] ((γ₁ '' Set.Icc (-π) π) ∪ ((fun z => -z) '' (γ₁ '' Set.Icc (-π) π))) :=
        measure_mono hcov
    _ ≤ μH[1] (γ₁ '' Set.Icc (-π) π) + μH[1] ((fun z => -z) '' (γ₁ '' Set.Icc (-π) π)) :=
        measure_union_le _ _
    _ = 2 * μH[1] (γ₁ '' Set.Icc (-π) π) := by rw [hausdorffMeasure_neg_image, two_mul]
    _ ≤ 2 * ENNReal.ofReal ((1 / 2 : ℝ) * ∫ θ in -π..π, ker r θ) := by rw [← hi]; gcongr
    _ = ENNReal.ofReal (∫ θ in -π..π, ker r θ) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

lemma ker_inv_le {r : ℝ} (hr1 : 1 < r) (θ : ℝ) : ker r θ ≤ ker (1 / r) θ := by
  have hr0 : 0 < r := by linarith
  have hid : r ^ 2 + 2 * r * Real.cos θ + 1 =
      r ^ 2 * ((1 / r) ^ 2 + 2 * (1 / r) * Real.cos θ + 1) := by field_simp; ring
  have hinv1 : 1 / r < 1 := (one_div_lt_one_div_of_lt zero_lt_one hr1).trans_eq one_div_one
  have hpos_inv : 0 < (1 / r) ^ 2 + 2 * (1 / r) * Real.cos θ + 1 := by
    have hpos_e := norm_add_exp_pos_of_ne (by positivity) hinv1.ne θ
    rw [← norm_add_exp_sq]; exact sq_pos_of_pos hpos_e
  have hpos_r : 0 < r ^ 2 := sq_pos_of_pos hr0
  simp only [ker, hid]
  rw [Real.mul_rpow hpos_r.le hpos_inv.le]
  have hr_pow : (r ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr1.le (by norm_num)
  nlinarith [Real.rpow_nonneg hpos_inv.le (-(1 / 4 : ℝ))]

lemma cos_ne_neg_one_of_mem_Icc {δ θ : ℝ} (hδ0 : 0 < δ) (hθ : θ ∈ Set.Icc (-(π - δ)) (π - δ)) :
    Real.cos θ ≠ -1 := by
  intro heq
  have hsin : Real.sin θ = 0 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hθ0 : θ = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hθ.1]) (by linarith [hθ.2])).1 hsin
  rw [hθ0, Real.cos_zero] at heq
  norm_num at heq

lemma lemniscateLength_one_ge {δ : ℝ} (hδ0 : 0 < δ) (hδpi : δ < π) :
    ENNReal.ofReal (∫ θ in -(π - δ)..(π - δ), ker 1 θ) ≤
      Erdos114.lemniscateLength (X ^ 2 - 1) := by
  let a := -(π - δ)
  let b := π - δ
  have hab : a ≤ b := by dsimp [a, b]; linarith
  let γ₁ : ℝ → ℂ := fun θ => csqrt (1 + Complex.exp ((θ : ℂ) * Complex.I))
  let γ₁' : ℝ → ℂ := fun θ => (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) / (2 * γ₁ θ)
  have hsp : ∀ θ ∈ Set.Icc a b, (1 : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro θ hθ
    rw [Complex.mem_slitPlane_iff]
    simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.add_im, Complex.one_im, zero_add, Complex.exp_ofReal_mul_I_im]
    by_cases hsin : Real.sin θ = 0
    · left
      have hθ0 : θ = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hθ.1]) (by linarith [hθ.2])).1 hsin
      simp [hθ0]
    · exact Or.inr hsin
  have hderiv : ∀ θ ∈ Set.Icc a b, HasDerivAt γ₁ (γ₁' θ) θ := by
    intro θ hθ
    have hinner : HasDerivAt (fun t : ℝ => (1 : ℂ) + Complex.exp ((t : ℂ) * Complex.I))
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
      exact (h1.cexp.const_add (1 : ℂ)).congr_deriv (by ring)
    refine ((hasDerivAt_csqrt (hsp θ hθ)).comp θ hinner).congr_deriv ?_
    dsimp only [γ₁', γ₁]; ring
  have hcont : ContinuousOn γ₁' (Set.Icc a b) := by
    intro θ hθ
    have hc_ne : γ₁ θ ≠ 0 := by
      intro h
      have := csqrt_sq (Complex.slitPlane_ne_zero (hsp θ hθ))
      change γ₁ θ ^ 2 = _ at this
      rw [h, sq, mul_zero] at this
      exact Complex.slitPlane_ne_zero (hsp θ hθ) this.symm
    have hnum : ContinuousAt (fun t : ℝ => Complex.I * Complex.exp ((t : ℂ) * Complex.I)) θ := by
      fun_prop
    exact (hnum.div (continuousAt_const.mul (hderiv θ hθ).continuousAt)
      (mul_ne_zero two_ne_zero hc_ne)).continuousWithinAt
  have hinj : Set.InjOn γ₁ (Set.Icc a b) := by
    intro θ₁ hθ₁ θ₂ hθ₂ hEq
    have hsq1 := csqrt_sq (Complex.slitPlane_ne_zero (hsp θ₁ hθ₁))
    have hsq2 := csqrt_sq (Complex.slitPlane_ne_zero (hsp θ₂ hθ₂))
    have hexp : Complex.exp ((θ₁ : ℂ) * Complex.I) = Complex.exp ((θ₂ : ℂ) * Complex.I) := by
      have hsq : (γ₁ θ₁) ^ 2 = (γ₁ θ₂) ^ 2 := by rw [hEq]
      dsimp [γ₁] at hsq
      rw [hsq1, hsq2] at hsq
      exact add_left_cancel hsq
    rw [Complex.exp_eq_exp_iff_exists_int] at hexp
    obtain ⟨k, hk⟩ := hexp
    have hk_real : (θ₁ : ℝ) = θ₂ + k * (2 * π) := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hlt1 : -(2 * π) < (k : ℝ) * (2 * π) := by linarith [hθ₁.1, hθ₂.2]
    have hlt2 : (k : ℝ) * (2 * π) < 2 * π := by linarith [hθ₁.2, hθ₂.1]
    have hk_int : -1 < k ∧ k < 1 := by
      constructor
      · exact_mod_cast (by nlinarith [Real.pi_pos] : (-1 : ℝ) < k)
      · exact_mod_cast (by nlinarith [Real.pi_pos] : (k : ℝ) < 1)
    have hk0 : k = 0 := by omega
    rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk_real
    exact hk_real
  have hnorm : ∀ θ ∈ Set.Icc a b, ‖γ₁' θ‖ = (1 / 2 : ℝ) * ker 1 θ := by
    intro θ hθ
    dsimp [γ₁', γ₁]
    simpa using norm_inv_two_csqrt 1 θ (Complex.slitPlane_ne_zero (hsp θ hθ))
  have hm := integral_le_hausdorffMeasure_image hab γ₁ γ₁' hderiv hcont hinj
  have hi : ∫ θ in a..b, ‖γ₁' θ‖ = (1 / 2 : ℝ) * ∫ θ in a..b, ker 1 θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ hθ => hnorm θ (by rwa [Set.uIcc_of_le hab] at hθ))
  have hS1 : γ₁ '' Set.Icc a b ⊆ Erdos114.lemniscate (X ^ 2 - 1) := by
    rintro z ⟨θ, hθ, rfl⟩
    simp only [Erdos114.lemniscate, Set.mem_ofPred_eq, eval_sub, eval_pow, eval_X, eval_one]
    rw [csqrt_sq (Complex.slitPlane_ne_zero (hsp θ hθ))]
    simp [Complex.norm_exp_ofReal_mul_I]
  have hS2 : (fun z => -z) '' (γ₁ '' Set.Icc a b) ⊆ Erdos114.lemniscate (X ^ 2 - 1) := by
    rintro z ⟨w, hw, rfl⟩
    have hw_mem := hS1 hw
    simp only [Erdos114.lemniscate, Set.mem_ofPred_eq, eval_sub, eval_pow, eval_X, eval_one,
      neg_sq] at hw_mem ⊢
    exact hw_mem
  have hdisj : Disjoint (γ₁ '' Set.Icc a b) ((fun z => -z) '' (γ₁ '' Set.Icc a b)) := by
    rw [Set.disjoint_iff]
    rintro z ⟨⟨θ₁, hθ₁, hz₁⟩, ⟨w, ⟨θ₂, hθ₂, rfl⟩, hz₂⟩⟩
    have hp1 : 0 < z.re := by rw [← hz₁]; exact re_csqrt_pos (hsp θ₁ hθ₁)
    have hp2 : z.re < 0 := by
      rw [← hz₂, Complex.neg_re, neg_lt_zero]
      exact re_csqrt_pos (hsp θ₂ hθ₂)
    linarith
  have hmeas1 : MeasurableSet (γ₁ '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn
      (fun θ hθ => (hderiv θ hθ).continuousAt.continuousWithinAt)).measurableSet
  have hmeas2 : MeasurableSet ((fun z => -z) '' (γ₁ '' Set.Icc a b)) := by
    have heq : (fun z : ℂ => -z) '' (γ₁ '' Set.Icc a b) = (fun z : ℂ => -z) ⁻¹' (γ₁ '' Set.Icc a b) := by
      ext z; simp [eq_comm]
    rw [heq]
    exact hmeas1.preimage continuous_neg.measurable
  have hunion : μH[1] ((γ₁ '' Set.Icc a b) ∪ ((fun z => -z) '' (γ₁ '' Set.Icc a b))) =
      2 * μH[1] (γ₁ '' Set.Icc a b) := by
    rw [measure_union hdisj hmeas2, hausdorffMeasure_neg_image, two_mul]
  calc ENNReal.ofReal (∫ θ in a..b, ker 1 θ)
      = 2 * ENNReal.ofReal ((1 / 2 : ℝ) * ∫ θ in a..b, ker 1 θ) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    _ = 2 * ENNReal.ofReal (∫ θ in a..b, ‖γ₁' θ‖) := by rw [← hi]
    _ ≤ 2 * μH[1] (γ₁ '' Set.Icc a b) := by gcongr
    _ = μH[1] ((γ₁ '' Set.Icc a b) ∪ ((fun z => -z) '' (γ₁ '' Set.Icc a b))) := hunion.symm
    _ ≤ μH[1] (Erdos114.lemniscate (X ^ 2 - 1)) := measure_mono (Set.union_subset hS1 hS2)
    _ = Erdos114.lemniscateLength (X ^ 2 - 1) := rfl

/- Step 4: Parseval monotonicity for 0 ≤ r ≤ s < 1 and double limit -/

noncomputable def binomCoeff (n : ℕ) : ℝ := Ring.choose (-1 / 4 : ℝ) n

lemma binomCoeff_succ (n : ℕ) :
    (n + 1 : ℝ) * binomCoeff (n + 1) = binomCoeff n * (-1 / 4 - n) := by
  have hp : (descPochhammer ℤ (n + 1)).smeval (-1 / 4 : ℝ) =
      (descPochhammer ℤ n).smeval (-1 / 4 : ℝ) * (-1 / 4 - n) := by
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast]
    simp
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
  have h1 : ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ)⁻¹ * (n.factorial : ℝ)⁻¹) =
      (n.factorial : ℝ)⁻¹ := by
    rw [← mul_assoc, mul_inv_cancel₀ hn1, one_mul]
  calc (n + 1 : ℝ) * binomCoeff (n + 1)
      = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ)⁻¹ * (n.factorial : ℝ)⁻¹ *
          ((descPochhammer ℤ n).smeval (-1 / 4 : ℝ) * (-1 / 4 - n))) := by
        simp only [binomCoeff, Ring.choose_eq_smul, smul_eq_mul, hp, Nat.factorial_succ,
          Nat.cast_mul, mul_inv]
        push_cast; rfl
    _ = (n.factorial : ℝ)⁻¹ * (descPochhammer ℤ n).smeval (-1 / 4 : ℝ) * (-1 / 4 - n) := by
        rw [← mul_assoc, h1]; ring
    _ = binomCoeff n * (-1 / 4 - n) := by
        simp only [binomCoeff, Ring.choose_eq_smul, smul_eq_mul]

lemma abs_binomCoeff_le_one (n : ℕ) : |binomCoeff n| ≤ 1 := by
  induction n with
  | zero => simp [binomCoeff, Ring.choose_zero_right]
  | succ n ih =>
    have hrec := binomCoeff_succ n
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hle : |-1 / 4 - (n : ℝ)| ≤ n + 1 := by rw [abs_le]; constructor <;> linarith
    have habs : (n + 1 : ℝ) * |binomCoeff (n + 1)| = |binomCoeff n| * |-1 / 4 - (n : ℝ)| := by
      rw [← abs_of_pos hn1, ← abs_mul, hrec, abs_mul]
    nlinarith [abs_nonneg (binomCoeff n), abs_nonneg (binomCoeff (n + 1))]

lemma integral_exp_int_mul_I (k : ℤ) :
    ∫ θ in -π..π, Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) =
      if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · simp [hk, two_mul]
  · have hk_ne : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) Complex.I_ne_zero
    let F : ℝ → ℂ := fun θ => Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) / ((k : ℂ) * Complex.I)
    have hderiv : ∀ θ ∈ Set.uIcc (-π) π,
        HasDerivAt F (Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => (k : ℂ) * (t : ℂ) * Complex.I) ((k : ℂ) * Complex.I) θ := by
        have hre := (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (k : ℂ)
        simpa using hre.mul_const Complex.I
      exact (h1.cexp.div_const ((k : ℂ) * Complex.I)).congr_deriv (by field_simp)
    have hcont : Continuous (fun θ : ℝ => Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) := by
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
    have hexp_eq : Complex.exp ((k : ℂ) * (π : ℂ) * Complex.I) =
        Complex.exp ((k : ℂ) * ((-π : ℝ) : ℂ) * Complex.I) := by
      rw [show (k : ℂ) * (π : ℂ) * Complex.I =
        (k : ℂ) * ((-π : ℝ) : ℂ) * Complex.I + k * (2 * π * Complex.I) by push_cast; ring]
      rw [Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]
    simp [F, hexp_eq]

lemma integral_partialSum_norm_sq (N : ℕ) (r : ℝ) :
    ∫ θ in -π..π,
      ‖∑ n ∈ Finset.range N, (binomCoeff n : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖ ^ 2 =
      2 * π * ∑ n ∈ Finset.range N, binomCoeff n ^ 2 * r ^ (2 * n) := by
  let S : ℝ → ℂ := fun θ =>
    ∑ n ∈ Finset.range N, (binomCoeff n : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n
  have hS_norm : ∀ θ : ℝ, ‖S θ‖ ^ 2 = (S θ * star (S θ)).re := by
    intro θ
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
    simp [Complex.star_def]
  have hS_cont1 : Continuous S :=
    continuous_finset_sum _ fun n _ => Continuous.mul continuous_const
      ((continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))).pow n)
  have hS_cont : Continuous fun θ => S θ * star (S θ) :=
    hS_cont1.mul (continuous_star.comp hS_cont1)
  have hre : ∫ θ in -π..π, ‖S θ‖ ^ 2 = (∫ θ in -π..π, S θ * star (S θ)).re := by
    simp_rw [hS_norm]
    exact intervalIntegral.intervalIntegral_re (hS_cont.intervalIntegrable _ _)
  have hexpand : ∀ θ : ℝ, S θ * star (S θ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((binomCoeff n * binomCoeff m * r ^ (n + m) : ℝ) : ℂ) *
          Complex.exp (((n : ℤ) - (m : ℤ) : ℤ) * (θ : ℂ) * Complex.I) := by
    intro θ
    dsimp [S]
    change (∑ n ∈ Finset.range N, (binomCoeff n : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n) *
        (starRingEnd ℂ) (∑ m ∈ Finset.range N, (binomCoeff m : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ m) = _
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    have h1 : Complex.exp ((θ : ℂ) * Complex.I) ^ n *
        Complex.exp ((θ : ℂ) * -Complex.I) ^ m =
        Complex.exp (((n : ℤ) - (m : ℤ) : ℤ) * (θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    have h2 : (r : ℂ) ^ n * (r : ℂ) ^ m = (r ^ (n + m) : ℝ) := by
      push_cast; rw [pow_add]
    calc ((binomCoeff n : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n) *
          ((binomCoeff m : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * -Complex.I)) ^ m)
        = (binomCoeff n : ℂ) * (binomCoeff m : ℂ) * ((r : ℂ) ^ n * (r : ℂ) ^ m) *
            (Complex.exp ((θ : ℂ) * Complex.I) ^ n * Complex.exp ((θ : ℂ) * -Complex.I) ^ m) := by
          ring
      _ = ((binomCoeff n * binomCoeff m * r ^ (n + m) : ℝ) : ℂ) *
            Complex.exp (((n : ℤ) - (m : ℤ) : ℤ) * (θ : ℂ) * Complex.I) := by
          rw [h1, h2]; push_cast; ring
  have hint_prod : ∫ θ in -π..π, S θ * star (S θ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ((binomCoeff n * binomCoeff m * r ^ (n + m) : ℝ) : ℂ) *
          (if (n : ℤ) - (m : ℤ) = 0 then (2 * π : ℂ) else 0) := by
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
      · intro m _
        exact (Continuous.mul continuous_const
          (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _
    · intro n _
      exact (continuous_finset_sum _ fun m _ => Continuous.mul continuous_const
        (Complex.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _
  rw [hre, hint_prod]
  have hdiag : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ((binomCoeff n * binomCoeff m * r ^ (n + m) : ℝ) : ℂ) *
        (if (n : ℤ) - (m : ℤ) = 0 then (2 * π : ℂ) else 0) =
      ((2 * π * ∑ n ∈ Finset.range N, binomCoeff n ^ 2 * r ^ (2 * n) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnm : ∀ m ∈ Finset.range N,
        ((binomCoeff n : ℂ) * (binomCoeff m : ℂ) * (r : ℂ) ^ (n + m)) *
          (if (n : ℤ) - (m : ℤ) = 0 then (2 * π : ℂ) else 0) =
        if m = n then (2 * π : ℂ) * ((binomCoeff n : ℂ) ^ 2 * (r : ℂ) ^ (2 * n)) else 0 := by
      intro m _
      by_cases heq : m = n
      · subst heq; simp [two_mul, pow_add]; ring
      · have hne : (n : ℤ) - (m : ℤ) ≠ 0 := by omega
        simp [heq, hne]
    rw [Finset.sum_congr rfl hnm, Finset.sum_ite_eq', if_pos hn]
  rw [hdiag, Complex.ofReal_re]

lemma integral_ker_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1) :
    ∫ θ in -π..π, ker r θ ≤ ∫ θ in -π..π, ker s θ := by
  have hr1 : r < 1 := hrs.trans_lt hs1
  have hlim : ∀ (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1),
      Tendsto (fun N : ℕ =>
        ∫ θ in -π..π, ‖∑ n ∈ Finset.range N,
          (binomCoeff n : ℂ) * ((u : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖ ^ 2)
        atTop (𝓝 (∫ θ in -π..π, ker u θ)) := by
    intro u hu0 hu1
    let F : ℕ → ℝ → ℝ := fun N θ =>
      ‖∑ n ∈ Finset.range N,
        (binomCoeff n : ℂ) * ((u : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖ ^ 2
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (1 - u)⁻¹ ^ 2) ?_ ?_ intervalIntegrable_const ?_
    · refine Eventually.of_forall fun N => ?_
      have hcontF : Continuous (F N) :=
        ((continuous_finset_sum _ fun n _ => Continuous.mul continuous_const
          ((continuous_const.mul (Complex.continuous_exp.comp
            (Complex.continuous_ofReal.mul continuous_const))).pow n)).norm).pow 2
      exact hcontF.aestronglyMeasurable
    · refine Eventually.of_forall fun N => Eventually.of_forall fun θ _ => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      gcongr
      calc ‖∑ n ∈ Finset.range N,
              (binomCoeff n : ℂ) * ((u : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖
          ≤ ∑ n ∈ Finset.range N,
              ‖(binomCoeff n : ℂ) * ((u : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖ :=
            norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range N, u ^ n := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [norm_mul, norm_pow, norm_mul, Complex.norm_of_nonneg hu0,
              Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
            calc |binomCoeff n| * u ^ n ≤ 1 * u ^ n :=
                  mul_le_mul_of_nonneg_right (abs_binomCoeff_le_one n) (pow_nonneg hu0 n)
              _ = u ^ n := one_mul _
        _ ≤ (1 - u)⁻¹ := by
            rw [geom_sum_eq hu1.ne, ← neg_div_neg_eq, neg_sub, neg_sub,
              div_le_iff₀ (sub_pos.2 hu1), inv_mul_cancel₀ (sub_ne_zero.2 hu1.ne')]
            linarith [pow_nonneg hu0 N]
    · refine Eventually.of_forall fun θ _ => ?_
      let w : ℂ := (u : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      have hw_norm : ‖w‖ = u := by
        dsimp [w]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hw_mem : w ∈ Metric.eball (0 : ℂ) 1 := by
        rw [Metric.mem_eball, edist_dist, dist_zero_right, hw_norm, ← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hu1
      have hsum := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (-1 / 4 : ℂ))).hasSum hw_mem
      have hterm : (fun n => binomialSeries ℂ (-1 / 4 : ℂ) n (fun _ => w)) =
          fun n => (binomCoeff n : ℂ) * w ^ n := by
        ext n
        simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
          binomCoeff]
        congr 1
        rw [show (-1 / 4 : ℂ) = ((-1 / 4 : ℝ) : ℂ) by norm_num]
        exact (Complex.ofReal_choose (-1 / 4 : ℝ) n).symm
      rw [hterm, zero_add] at hsum
      have htend := ((hsum.tendsto_sum_nat).norm.pow 2)
      have hker_eq : ‖(1 + w) ^ (-1 / 4 : ℂ)‖ ^ 2 = ker u θ := by
        have hw1_ne : 1 + w ≠ 0 := by
          intro h
          have : ‖w‖ = 1 := by
            have : w = -1 := eq_neg_of_add_eq_zero_right h
            rw [this, norm_neg, norm_one]
          linarith [hw_norm]
        rw [Complex.cpow_def_of_ne_zero hw1_ne, Complex.norm_exp]
        have hre : (Complex.log (1 + w) * (-1 / 4 : ℂ)).re =
            Real.log ‖1 + w‖ * (-1 / 4 : ℝ) := by
          have h1 : (-1 / 4 : ℂ) = ((-1 / 4 : ℝ) : ℂ) := by norm_num
          rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.log_re]
          ring
        rw [hre, ← Real.rpow_def_of_pos (norm_pos_iff.2 hw1_ne) (-1 / 4 : ℝ)]
        have hsq : ‖1 + w‖ = (u ^ 2 + 2 * u * Real.cos θ + 1) ^ (1 / 2 : ℝ) := by
          have h1w : ‖(1 : ℂ) + w‖ = ‖(u : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ := by
            have hre1 : ((1 : ℂ) + w).re = 1 + u * Real.cos θ := by
              simp [w, Complex.exp_ofReal_mul_I_re]
            have him1 : ((1 : ℂ) + w).im = u * Real.sin θ := by
              simp [w, Complex.exp_ofReal_mul_I_im]
            have hsq1 : ‖(1 : ℂ) + w‖ ^ 2 = u ^ 2 + 2 * u * Real.cos θ + 1 := by
              rw [Complex.sq_norm, Complex.normSq_apply, hre1, him1]
              nlinarith [Real.sin_sq_add_cos_sq θ]
            have hpos_lhs : 0 ≤ ‖(1 : ℂ) + w‖ := norm_nonneg _
            have hpos_rhs : 0 ≤ ‖(u : ℂ) + Complex.exp ((θ : ℂ) * Complex.I)‖ := norm_nonneg _
            nlinarith [norm_add_exp_sq u θ]
          rw [h1w, norm_eq_sq_rpow_half, norm_add_exp_sq]
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _), hsq]
        have hnn : 0 ≤ u ^ 2 + 2 * u * Real.cos θ + 1 := by
          nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (u + Real.cos θ)]
        rw [← Real.rpow_mul hnn]
        norm_num [ker]
      simpa [F, w, hker_eq] using htend
  have hle_N : ∀ N : ℕ,
      ∫ θ in -π..π, ‖∑ n ∈ Finset.range N,
        (binomCoeff n : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖ ^ 2 ≤
      ∫ θ in -π..π, ‖∑ n ∈ Finset.range N,
        (binomCoeff n : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n‖ ^ 2 := by
    intro N
    rw [integral_partialSum_norm_sq N r, integral_partialSum_norm_sq N s]
    gcongr
  exact le_of_tendsto_of_tendsto (hlim r hr0 hr1) (hlim s (hr0.trans hrs) hs1)
    (Eventually.of_forall hle_N)

lemma ker_le_of_pos_lt_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {θ : ℝ} (hcos : Real.cos θ ≠ -1) :
    ker s θ ≤ s ^ (-(1 / 4 : ℝ)) * ker 1 θ := by
  have hpos1 : 0 < 1 ^ 2 + 2 * 1 * Real.cos θ + 1 := by
    have : -1 < Real.cos θ := lt_of_le_of_ne (Real.neg_one_le_cos θ) (Ne.symm hcos)
    linarith
  have hge : s * (1 ^ 2 + 2 * 1 * Real.cos θ + 1) ≤ s ^ 2 + 2 * s * Real.cos θ + 1 := by
    nlinarith [sq_nonneg (1 - s)]
  have h1 : (s ^ 2 + 2 * s * Real.cos θ + 1) ^ (-(1 / 4 : ℝ)) ≤
      (s * (1 ^ 2 + 2 * 1 * Real.cos θ + 1)) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hs0 hpos1) hge (by norm_num)
  rw [Real.mul_rpow hs0.le hpos1.le] at h1
  exact h1

lemma ofReal_integral_ker_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ENNReal.ofReal (∫ θ in -π..π, ker r θ) ≤ Erdos114.lemniscateLength (X ^ 2 - 1) := by
  have hs_bound : ∀ s : ℝ, max r (1 / 2) < s → s < 1 →
      ENNReal.ofReal (∫ θ in -π..π, ker r θ) ≤
        ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) := by
    intro s hs_gt hs1
    have hs0 : 0 < s := by linarith [le_max_right r (1 / 2)]
    have hrs : r ≤ s := (le_max_left r (1 / 2)).trans hs_gt.le
    have hmono := integral_ker_mono hr0 hrs hs1
    have hker_cont : Continuous (ker s) := by
      refine Continuous.rpow (by fun_prop) continuous_const fun θ => Or.inl ?_
      rw [← norm_add_exp_sq]
      exact (sq_pos_of_pos (norm_add_exp_pos_of_ne hs0.le hs1.ne θ)).ne'
    have htail : ∀ θ : ℝ, ker s θ ≤ (1 - s) ^ (-(1 / 2 : ℝ)) := by
      intro θ
      have hge : (1 - s) ^ 2 ≤ s ^ 2 + 2 * s * Real.cos θ + 1 := by
        nlinarith [Real.neg_one_le_cos θ]
      have hpos : 0 < (1 - s) ^ 2 := sq_pos_of_pos (sub_pos.2 hs1)
      have h1 : (s ^ 2 + 2 * s * Real.cos θ + 1) ^ (-(1 / 4 : ℝ)) ≤
          ((1 - s) ^ 2) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos hge (by norm_num)
      rw [← Real.rpow_natCast (1 - s) 2, ← Real.rpow_mul (sub_pos.2 hs1).le] at h1
      norm_num [ker] at h1 ⊢
      exact h1
    have hδ_bound : ∀ δ : ℝ, 0 < δ → δ < π →
        ENNReal.ofReal (∫ θ in -π..π, ker r θ) ≤
          ENNReal.ofReal (2 * δ * (1 - s) ^ (-(1 / 2 : ℝ))) +
            ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) := by
      intro δ hδ0 hδpi
      have hi1 : IntervalIntegrable (ker s) volume (-π) (-(π - δ)) :=
        hker_cont.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (ker s) volume (-(π - δ)) (π - δ) :=
        hker_cont.intervalIntegrable _ _
      have hi3 : IntervalIntegrable (ker s) volume (π - δ) π :=
        hker_cont.intervalIntegrable _ _
      have h12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      have h123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
      have hsplit : ∫ θ in -π..π, ker s θ =
          (∫ θ in -π..-(π - δ), ker s θ) + (∫ θ in -(π - δ)..(π - δ), ker s θ) +
          (∫ θ in (π - δ)..π, ker s θ) := by linarith
      have ht1 : ∫ θ in -π..-(π - δ), ker s θ ≤ δ * (1 - s) ^ (-(1 / 2 : ℝ)) := by
        calc ∫ θ in -π..-(π - δ), ker s θ
            ≤ ∫ _θ in -π..-(π - δ), (1 - s) ^ (-(1 / 2 : ℝ)) :=
              intervalIntegral.integral_mono_on (by linarith) hi1 intervalIntegrable_const
                fun θ _ => htail θ
          _ = δ * (1 - s) ^ (-(1 / 2 : ℝ)) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      have ht3 : ∫ θ in (π - δ)..π, ker s θ ≤ δ * (1 - s) ^ (-(1 / 2 : ℝ)) := by
        calc ∫ θ in (π - δ)..π, ker s θ
            ≤ ∫ _θ in (π - δ)..π, (1 - s) ^ (-(1 / 2 : ℝ)) :=
              intervalIntegral.integral_mono_on (by linarith) hi3 intervalIntegrable_const
                fun θ _ => htail θ
          _ = δ * (1 - s) ^ (-(1 / 2 : ℝ)) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      have hker1_cont : ContinuousOn (ker 1) (Set.Icc (-(π - δ)) (π - δ)) := by
        refine ContinuousOn.rpow (by fun_prop) continuousOn_const fun θ hθ => Or.inl ?_
        have hlt : -1 < Real.cos θ :=
          lt_of_le_of_ne (Real.neg_one_le_cos θ) (Ne.symm (cos_ne_neg_one_of_mem_Icc hδ0 hθ))
        linarith
      have hm_mid : ∫ θ in -(π - δ)..(π - δ), ker s θ ≤
          s ^ (-(1 / 4 : ℝ)) * ∫ θ in -(π - δ)..(π - δ), ker 1 θ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on (by linarith) hi2
          (ContinuousOn.intervalIntegrable_of_Icc (by linarith)
            (hker1_cont.const_smul (s ^ (-(1 / 4 : ℝ)))))
          fun θ hθ => ker_le_of_pos_lt_one hs0 hs1 (cos_ne_neg_one_of_mem_Icc hδ0 hθ)
      have h_all : ∫ θ in -π..π, ker r θ ≤
          2 * δ * (1 - s) ^ (-(1 / 2 : ℝ)) +
            s ^ (-(1 / 4 : ℝ)) * ∫ θ in -(π - δ)..(π - δ), ker 1 θ := by
        linarith [hmono, hsplit, ht1, ht3, hm_mid]
      calc ENNReal.ofReal (∫ θ in -π..π, ker r θ)
          ≤ ENNReal.ofReal (2 * δ * (1 - s) ^ (-(1 / 2 : ℝ)) +
              s ^ (-(1 / 4 : ℝ)) * ∫ θ in -(π - δ)..(π - δ), ker 1 θ) :=
            ENNReal.ofReal_le_ofReal h_all
        _ ≤ ENNReal.ofReal (2 * δ * (1 - s) ^ (-(1 / 2 : ℝ))) +
              ENNReal.ofReal (s ^ (-(1 / 4 : ℝ)) * ∫ θ in -(π - δ)..(π - δ), ker 1 θ) :=
            ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (2 * δ * (1 - s) ^ (-(1 / 2 : ℝ))) +
              ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * ENNReal.ofReal (∫ θ in -(π - δ)..(π - δ), ker 1 θ) := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
        _ ≤ ENNReal.ofReal (2 * δ * (1 - s) ^ (-(1 / 2 : ℝ))) +
              ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) := by
            gcongr; exact lemniscateLength_one_ge hδ0 hδpi
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hCpos : 0 < 2 * (1 - s) ^ (-(1 / 2 : ℝ)) := by
      have : 0 < (1 - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (sub_pos.2 hs1) _
      positivity
    let δ := min (π / 2) ((ε : ℝ) / (2 * (1 - s) ^ (-(1 / 2 : ℝ))))
    have hδ0 : 0 < δ := lt_min (by positivity) (div_pos hε hCpos)
    have hδpi : δ < π := (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
    have h1 := hδ_bound δ hδ0 hδpi
    have h2 : 2 * δ * (1 - s) ^ (-(1 / 2 : ℝ)) ≤ ε := by
      have hle : δ ≤ (ε : ℝ) / (2 * (1 - s) ^ (-(1 / 2 : ℝ))) := min_le_right _ _
      calc 2 * δ * (1 - s) ^ (-(1 / 2 : ℝ))
          = δ * (2 * (1 - s) ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ ((ε : ℝ) / (2 * (1 - s) ^ (-(1 / 2 : ℝ)))) * (2 * (1 - s) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_right hle hCpos.le
        _ = ε := div_mul_cancel₀ _ hCpos.ne'
    calc ENNReal.ofReal (∫ θ in -π..π, ker r θ)
        ≤ ENNReal.ofReal (2 * δ * (1 - s) ^ (-(1 / 2 : ℝ))) +
            ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) := h1
      _ ≤ ENNReal.ofReal (ε : ℝ) +
            ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) := by gcongr
      _ = ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) + ε := by
          rw [add_comm, ENNReal.ofReal_coe_nnreal]
  have htend : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) *
      Erdos114.lemniscateLength (X ^ 2 - 1)) (𝓝[<] 1)
      (𝓝 (1 * Erdos114.lemniscateLength (X ^ 2 - 1))) := by
    have h1 : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ (-(1 / 4 : ℝ)))) (𝓝[<] 1) (𝓝 1) := by
      have hrp : Tendsto (fun s : ℝ => s ^ (-(1 / 4 : ℝ))) (𝓝[<] 1) (𝓝 ((1 : ℝ) ^ (-(1 / 4 : ℝ)))) :=
        ((Real.continuousAt_rpow_const 1 (-(1 / 4 : ℝ)) (Or.inl one_ne_zero)).tendsto).mono_left
          nhdsWithin_le_nhds
      rw [Real.one_rpow] at hrp
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp hrp
    exact ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
  have hev : ∀ᶠ s in 𝓝[<] 1,
      ENNReal.ofReal (∫ θ in -π..π, ker r θ) ≤
        ENNReal.ofReal (s ^ (-(1 / 4 : ℝ))) * Erdos114.lemniscateLength (X ^ 2 - 1) := by
    have hmem : Set.Ioo (max r (1 / 2)) 1 ∈ 𝓝[<] (1 : ℝ) :=
      Ioo_mem_nhdsLT (max_lt hr1 (by norm_num))
    filter_upwards [hmem] with s hs
    exact hs_bound s hs.1 hs.2
  simpa using ge_of_tendsto htend hev

theorem solution (p : ℂ[X]) (hp : p.Monic) (hdeg : p.natDegree = 2) :
    Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength (X ^ 2 - 1) := by
  obtain ⟨r, hr0, hlen⟩ := lemniscateLength_eq_sub_ofReal p hp hdeg
  rw [hlen]
  rcases lt_trichotomy r 1 with hr_lt | rfl | hr_gt
  · exact (lemniscateLength_sub_ofReal_le_lt hr0 hr_lt).trans (ofReal_integral_ker_le_one hr0 hr_lt)
  · simp
  · have hinv0 : 0 ≤ 1 / r := by positivity
    have hinv1 : 1 / r < 1 := (one_div_lt_one_div_of_lt zero_lt_one hr_gt).trans_eq one_div_one
    have hker_int : ∫ θ in -π..π, ker r θ ≤ ∫ θ in -π..π, ker (1 / r) θ := by
      refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) ?_ ?_ fun θ _ =>
        ker_inv_le hr_gt θ
      · refine (Continuous.rpow (by fun_prop) continuous_const fun θ => Or.inl ?_).intervalIntegrable _ _
        rw [← norm_add_exp_sq]
        exact (sq_pos_of_pos (norm_add_exp_pos_of_ne hr0 hr_gt.ne' θ)).ne'
      · refine (Continuous.rpow (by fun_prop) continuous_const fun θ => Or.inl ?_).intervalIntegrable _ _
        rw [← norm_add_exp_sq]
        exact (sq_pos_of_pos (norm_add_exp_pos_of_ne hinv0 hinv1.ne θ)).ne'
    calc Erdos114.lemniscateLength (X ^ 2 - C (r : ℂ))
        ≤ ENNReal.ofReal (∫ θ in -π..π, ker r θ) := lemniscateLength_sub_ofReal_le_gt hr_gt
      _ ≤ ENNReal.ofReal (∫ θ in -π..π, ker (1 / r) θ) := ENNReal.ofReal_le_ofReal hker_int
      _ ≤ Erdos114.lemniscateLength (X ^ 2 - 1) := ofReal_integral_ker_le_one hinv0 hinv1

end Erdos114Two

theorem OMA.solution : type_of% @Erdos114.erdos_114.variants.two := by
  intro p hp hdeg
  exact Erdos114Two.solution p hp hdeg
