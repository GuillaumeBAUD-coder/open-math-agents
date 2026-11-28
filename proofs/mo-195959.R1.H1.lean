import OMAReductions.R_mo_195959_R1
import Mathlib.Tactic

open MeasureTheory Set Filter Topology Polynomial
open scoped unitInterval NNReal ENNReal Polynomial
noncomputable section


private def D (h : ℝ) (g : ℝ → ℝ) (x : ℝ) := g x - g (x+h)

private theorem sign_tower (h : ℝ) (hh : 0 ≤ h) (g : ℕ → ℝ → ℝ)
    (hg : ∀ j x, 0 < x → 0 ≤ g j x)
    (dg : ∀ j x, 0 < x → HasDerivAt (g j) (-g (j+1) x) x)
    (k : ℕ) : ∀ j x, 0 < x → 0 ≤ (D h)^[k] (g j) x := by
  induction k generalizing g with
  | zero => simpa using hg
  | succ k ih =>
    have der (j : ℕ) (x : ℝ) (hx : 0 < x) :
        HasDerivAt (D h (g j)) (-(D h (g (j+1)) x)) x := by
      rw [show -(D h (g (j+1)) x) = -g (j+1) x - -g (j+1) (x+h) by unfold D; ring]
      exact (dg j x hx).sub ((dg j (x+h) (by linarith)).comp_add_const x h)
    have pos (j : ℕ) (x : ℝ) (hx : 0 < x) : 0 ≤ D h (g j) x := by
      have anti : AntitoneOn (g j) (Ioi 0) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => -g (j+1) y) (convex_Ioi _)
        · exact fun y hy => (dg j y hy).continuousAt.continuousWithinAt
        · intro y hy
          exact (dg j y (interior_subset hy)).hasDerivWithinAt
        · exact fun y hy => neg_nonpos.mpr (hg _ _ (interior_subset hy))
      exact sub_nonneg.mpr (anti hx (show 0 < x+h by linarith) (by linarith))
    simpa only [Function.iterate_succ_apply] using ih (fun j => D h (g j)) pos der

private theorem posD {f : ℝ → ℝ} (hc : ContinuousOn f (Ici 0))
    (hd : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0))
    (hs : ∀ j : ℕ, ∀ x ∈ Ioi (0:ℝ), 0 ≤ (-1:ℝ)^j * iteratedDerivWithin j f (Ioi 0) x)
    (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (D h)^[k] f x := by
  let g (j : ℕ) (y : ℝ) := (-1:ℝ)^j * iteratedDerivWithin j f (Ioi 0) y
  have dg (j : ℕ) (y : ℝ) (hy : 0 < y) : HasDerivAt (g j) (-g (j+1) y) y := by
    have hd' := hd.differentiableOn_iteratedDerivWithin (m := j) (by exact_mod_cast ENat.natCast_lt_top j) (uniqueDiffOn_Ioi (0:ℝ))
    have dh := (hd' y hy).hasDerivWithinAt.hasDerivAt (isOpen_Ioi.mem_nhds hy)
    simpa [g, iteratedDerivWithin_succ, pow_succ] using dh.const_mul ((-1:ℝ)^j)
  have pos (y : ℝ) (hy : 0 < y) : 0 ≤ (D h)^[k] f y := by
    simpa [g] using sign_tower h hh g hs dg k 0 y hy
  have cont : ContinuousOn ((D h)^[k] f) (Ici 0) := by
    clear pos
    induction k with
    | zero => exact hc
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.sub (ih.comp (continuous_id.add continuous_const).continuousOn
        (fun y hy => show 0 ≤ y + h from add_nonneg hy hh))
  have : (𝓝[Ioi (0:ℝ)] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by rwa [closure_Ioi])
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((cont x hx).mono Ioi_subset_Ici_self) (by filter_upwards [self_mem_nhdsWithin] with y hy using pos y hy)


private theorem expandBin (L : ℝ[X] →ₗ[ℝ] ℝ) (N : ℕ) (A B : ℝ[X]) (c d : ℝ) :
    L ((C c * A + C d * B)^N) =
      ∑ k ∈ Finset.range (N+1),
        ((N.choose k : ℝ)*c^k*d^(N-k))*L (A^k*B^(N-k)) := by
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← smul_eq_mul (α := ℝ), ← L.map_smul]
  congr 1
  simp only [smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow]
  ring

private def shift (h : ℝ) : Module.End ℝ (ℝ → ℝ) where
  toFun g x := g (x + h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def moment (h : ℝ) (f : ℝ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ((aeval (shift h) p) f) 0
  map_add' p q := by simp
  map_smul' c p := by simp

private lemma shift_pow (h : ℝ) (j : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    ((shift h ^ j) f) x = f (x + j*h) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; change ((shift h ^ j) f) (x+h) = _
                 rw [ih]; congr 1; push_cast; ring

private lemma on_weight (h : ℝ) (f : ℝ → ℝ) (j k : ℕ) :
    moment h f ((1-X)^k*X^j) =
      ((fun g x => g x - g (x+h))^[k] f) (j*h) := by
  rw [mul_comm]
  simp only [moment, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_pow, map_sub, map_one, aeval_X,
    Module.End.mul_apply, shift_pow, zero_add]
  rw [Module.End.pow_apply]
  rfl

private lemma on_power (h : ℝ) (f : ℝ → ℝ) (j : ℕ) :
    moment h f (X^j) = f (j*h) := by simpa using on_weight h f j 0

private theorem pgf (h : ℝ) (f : ℝ → ℝ) (N : ℕ) (z : ℝ) :
    ∑ k ∈ Finset.range (N+1), ((N.choose k : ℝ)*z^k) *
      ((fun g x => g x - g (x+h))^[k] f) ((N-k:ℕ)*h) =
    ∑ j ∈ Finset.range (N+1), ((N.choose j : ℝ)*(1-z)^j*z^(N-j)) * f (j*h) := by
  let L := moment h f
  have e : C z*(1-X) + C (1:ℝ)*X = C (1-z)*X + C z*1 := by simp only [map_sub, map_one]; ring
  have e' := congrArg (fun p : ℝ[X] => L (p^N)) e
  rw [expandBin, expandBin] at e'
  simpa [L, on_weight, on_power] using e'



private theorem chooseDegree (a : ℕ) (ha : 0 < a) (F : C(I, ℝ)) :
    ∃ m : ℕ, 0 < m ∧ ∀ v : I,
      |bernsteinApproximation (a*m) F v - F v| < 1/(a:ℝ) := by
  have H := (Metric.tendsto_atTop.mp (bernsteinApproximation_uniform F)) (1/(a:ℝ)) (by positivity)
  obtain ⟨K, hK⟩ := H
  refine ⟨K+1, by omega, fun v => ?_⟩
  change dist (bernsteinApproximation (a * (K + 1)) F v) (F v) < _
  exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist v)
    (hK _ (by nlinarith [Nat.zero_le K] : K ≤ a*(K+1)))

private theorem limitExp (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (n:ℝ)*(1 - Real.exp (-t/n))) atTop (𝓝 t) := by
  have hy := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (-t)
  have hn : Tendsto (fun n : ℕ => -t/(n:ℝ)) atTop (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hy, (eventually_gt_atTop 0).mono fun n h => div_ne_zero (neg_ne_zero.mpr ht.ne') (by positivity)⟩
  have ds := ((Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hn).const_mul t
  simp only [Real.exp_zero, zero_add, mul_one] at ds
  apply ds.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn'
  dsimp [Function.comp_def]
  field_simp [ht.ne']
  all_goals ring


private def atom (a : ℕ) (k : ℕ) : I :=
  ⟨Real.exp (-(k:ℝ)/a), (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _))⟩
private def disc (a N : ℕ) (w : ℕ → ℝ) : Measure I :=
  ∑ k ∈ Finset.range (N+1), ENNReal.ofReal (w k) • Measure.dirac (atom a k)

private theorem disc_prob (a N : ℕ) (w : ℕ → ℝ) (h : ∀ k ∈ Finset.range (N+1), 0 ≤ w k)
    (hw : ∑ k ∈ Finset.range (N+1), w k = 1) : IsProbabilityMeasure (disc a N w) := by
  constructor
  simp [disc, Measure.coe_finsetSum, ← ENNReal.ofReal_sum_of_nonneg h, hw]

private theorem disc_moment (a N : ℕ) (w : ℕ → ℝ) (h : ∀ k ∈ Finset.range (N+1), 0 ≤ w k)
    (t : ℝ) (_ht : 0 < t) :
    ∫ u : I, (u:ℝ)^t ∂disc a N w =
      ∑ k ∈ Finset.range (N+1), w k * Real.exp (-t/a)^k := by
  rw [disc, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (h k hk), smul_eq_mul]
    congr 1
    change (Real.exp (-(k:ℝ)/a))^t = Real.exp (-t/a)^k
    rw [← Real.exp_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  · intro k hk
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top



private theorem obtainLimit (ρ : ℕ → ProbabilityMeasure I) (f : ℝ → ℝ)
    (h : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => ∫ u : I, (u : ℝ)^t ∂(ρ n)) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure I, ∀ t : ℝ, 0 < t →
      f t = ∫ u : I, (u : ℝ)^t ∂ν := by
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq ρ
  refine ⟨ν, fun t ht => ?_⟩
  let g : C(I, ℝ) :=
    ⟨fun u => (u : ℝ)^t, (Real.continuous_rpow_const ht.le).comp continuous_subtype_val⟩
  exact tendsto_nhds_unique ((h t ht).comp hφ.tendsto_atTop)
    ((ProbabilityMeasure.continuous_integral_continuousMap g).continuousAt.tendsto.comp hν)

private theorem transport (ν : ProbabilityMeasure I) (f : ℝ → ℝ)
    (hν : ∀ t : ℝ, 0 < t → f t = ∫ u : I, (u : ℝ)^t ∂ν) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 < t → f t = ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ := by
  let S : Set I := {u | 0 < (u : ℝ)}
  let L : I → ℝ≥0 := fun u => (-Real.log (u : ℝ)).toNNReal
  have hS : MeasurableSet S := isOpen_lt continuous_const continuous_subtype_val |>.measurableSet
  have hL : Measurable L := by dsimp [L]; fun_prop
  refine ⟨Measure.map L ((ν : Measure I).restrict S), inferInstance, fun t ht => ?_⟩
  rw [hν t ht, integral_map hL.aemeasurable (by fun_prop)]
  calc
    _ = ∫ u in S, (u : ℝ)^t ∂(ν : Measure I) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hz : (u : ℝ) = 0 := le_antisymm (le_of_not_gt hu) u.2.1
      simp [hz, ht.ne']
    _ = _ := by
      apply setIntegral_congr_fun hS
      intro u hu
      have hlog : Real.log (u : ℝ) ≤ 0 := Real.log_nonpos u.2.1 u.2.2
      simp [L, Real.coe_toNNReal _ (by linarith : 0 ≤ -Real.log (u : ℝ)),
        Real.rpow_def_of_pos (show 0 < (u : ℝ) from hu)]

private def scaled (f : ℝ → ℝ) (hc : ContinuousOn f (Ici 0)) (a : ℕ) : C(I,ℝ) where
  toFun v := f (a*(v:ℝ))
  continuous_toFun := hc.comp_continuous (continuous_const.mul continuous_subtype_val)
    (fun v => mul_nonneg (Nat.cast_nonneg _) v.2.1)

private def wt (f : ℝ → ℝ) (h : ℝ) (N k : ℕ) :=
  (N.choose k : ℝ) * ((D h)^[k] f) ((N-k : ℕ)*h)

private lemma asBernstein (f : ℝ → ℝ) (hc : ContinuousOn f (Ici 0)) (a m : ℕ) (ha : 0 < a)
    (hm : 0 < m) (p : I) :
    ∑ k ∈ Finset.range (a*m+1), wt f (1/(m:ℝ)) (a*m) k * (1-(p:ℝ))^k =
      bernsteinApproximation (a*m) (scaled f hc a) p := by
  let N := a*m
  let h := 1/(m:ℝ)
  have H := pgf h f N (1-(p:ℝ))
  rw [bernsteinApproximation.apply]
  simp only [sub_sub_cancel] at H
  convert H using 1
  · apply Finset.sum_congr rfl
    intro k hk
    exact mul_right_comm _ _ _
  · rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [bernstein_apply, smul_eq_mul, scaled, ContinuousMap.coe_mk, bernstein.z, h, N,
      Nat.cast_mul]
    congr 2
    field_simp

private lemma oneScale (f : ℝ → ℝ) (hc : ContinuousOn f (Ici 0)) (hf : f 0 = 1)
    (hp : ∀ h, 0 ≤ h → ∀ k x, 0 ≤ x → 0 ≤ (D h)^[k] f x) (a : ℕ) (ha : 0 < a) :
    ∃ ρ : ProbabilityMeasure I, ∀ t : ℝ, 0 < t →
      |(∫ u : I, (u:ℝ)^t ∂ρ) - f (a*(1-Real.exp (-t/a)))| < 1/(a:ℝ) := by
  obtain ⟨m, hm, hM⟩ := chooseDegree a ha (scaled f hc a)
  let N := a*m
  let h := 1/(m:ℝ)
  let w := wt f h N
  have wpos (k : ℕ) (_ : k ∈ Finset.range (N+1)) : 0 ≤ w k :=
    mul_nonneg (Nat.cast_nonneg _) (hp h (by dsimp [h]; positivity) k _ (by dsimp [h]; positivity))
  have sw : ∑ k ∈ Finset.range (N+1), w k = 1 := by
    simpa [N,h,w,scaled,hf] using asBernstein f hc a m ha hm 0
  let ρ : ProbabilityMeasure I := ⟨disc a N w, disc_prob a N w wpos sw⟩
  refine ⟨ρ, fun t ht => ?_⟩
  let z := Real.exp (-t/a)
  have hz : z ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (Nat.cast_nonneg _))
  let p : I := ⟨1-z, by linarith, by linarith [Real.exp_pos (-t/a)]⟩
  change |(∫ u : I, (u:ℝ)^t ∂disc a N w) - _| < _
  rw [disc_moment a N w wpos t ht]
  have HB := asBernstein f hc a m ha hm p
  have HH := hM p
  change |bernsteinApproximation (a*m) (scaled f hc a) p - f (a*(1-z))| < _ at HH
  rw [← HB] at HH
  simpa [w, N, h, p, z] using HH


open OMA.S_mo_195959
theorem OMA.solution : OMA.R_mo_195959_R1.H1 := by
  intro f hc hf hcm
  have hp := posD hc hcm.1 hcm.2
  choose ρ hρ using fun n : ℕ => oneScale f hc hf hp (n+1) (Nat.succ_pos _)
  apply Exists.elim (obtainLimit ρ f ?_) (fun ν hν => transport ν f hν)
  intro t ht
  let A (n : ℕ) := (n:ℝ)*(1-Real.exp (-t/n))
  have H : Tendsto (fun n : ℕ => f (A (n+1))) atTop (𝓝 (f t)) :=
    ((hc t ht.le).continuousAt (Ici_mem_nhds ht)).tendsto.comp
      ((limitExp t ht).comp (tendsto_add_atTop_nat 1))
  apply H.congr_dist
  apply squeeze_zero (fun n => dist_nonneg)
    (g := fun n : ℕ => 1/(((n+1:ℕ):ℝ)))
  · intro n
    rw [dist_comm, Real.dist_eq]
    exact (hρ n t ht).le
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

