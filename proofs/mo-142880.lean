import OMAStatements.S_mo_142880
import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ArgmaxGaussianBarrier
theorem gaussian_upper_tail (n : ℕ) (d K : ℝ) (hd : 0 ≤ d) :
    (gaussianReal (-(n : ℝ) * d) (n : NNReal)).real (Set.Ioi K) ≤
      Real.exp (-d * K) * Real.exp (-(d ^ 2 / 2) * (n : ℝ)) := by
  have h := measure_ge_le_exp_mul_mgf
    (μ := gaussianReal (-(n : ℝ) * d) (n : NNReal)) (X := id) K hd
    (integrable_exp_mul_gaussianReal d)
  rw [mgf_id_gaussianReal] at h
  simp only [NNReal.coe_natCast] at h
  have heq : (-(n : ℝ) * d) * d + (n : ℝ) * d ^ 2 / 2 =
      -(d ^ 2 / 2) * (n : ℝ) := by ring
  rw [heq] at h
  exact (measureReal_mono (fun x hx => (show K < x from hx).le)).trans h
theorem geometric_union_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hA : ∀ n, P.real (A n) ≤ C * q ^ n) :
    P.real (⋃ n, A n) ≤ C / (1 - q) := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hsum : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_norm_lt_one hnorm).mul_left C
  have htotal : (∑' n : ℕ, C * q ^ n) = C / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm, div_eq_mul_inv]
  have hbound : P (⋃ n, A n) ≤ ENNReal.ofReal (C / (1 - q)) := by
    calc
      _ ≤ ∑' n, P (A n) := measure_iUnion_le _
      _ ≤ ∑' n, ENNReal.ofReal (C * q ^ n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
          ENNReal.ofReal_le_ofReal (hA n)
      _ = ENNReal.ofReal (C / (1 - q)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hC (pow_nonneg hq0 n)) hsum,
          htotal]
  have hnonneg : 0 ≤ C / (1 - q) := div_nonneg hC (sub_nonneg.mpr hq1.le)
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
lemma exists_barrier_scale (d q : ℝ) (hd : 0 < d) (hq : q < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ Real.exp (-d * K) / (1 - q) ≤ 1 / 2 := by
  let c := (1 - q) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let K := max 0 (-Real.log c / d)
  have hK : 0 ≤ K := le_max_left _ _
  have hlog : -Real.log c ≤ K * d :=
    (div_le_iff₀ hd).mp (le_max_right _ _)
  have he : Real.exp (-d * K) ≤ c := by
    calc
      _ ≤ Real.exp (Real.log c) := Real.exp_le_exp.mpr (by nlinarith)
      _ = c := Real.exp_log hc
  refine ⟨K, hK, ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
  dsimp [c] at he
  linarith
theorem exists_uniform_gaussian_barrier (d : ℝ) (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (S : ℕ → Ω → ℝ),
        (∀ n, HasLaw (S n) (gaussianReal (-(n : ℝ) * d) (n : NNReal)) P) →
        (1 / 2 : ℝ) ≤ P.real {ω | ∀ n, S n ω ≤ K} := by
  let q := Real.exp (-(d ^ 2 / 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  obtain ⟨K, hK, hscale⟩ := exists_barrier_scale d q hd hq1
  refine ⟨K, hK, ?_⟩
  intro Ω _ P _ S hS
  let A : ℕ → Set Ω := fun n => {ω | K < S n ω}
  have hA (n : ℕ) : P.real (A n) ≤ Real.exp (-d * K) * q ^ n := by
    have h := gaussian_upper_tail n d K hd.le
    rw [show Real.exp (-(d ^ 2 / 2) * (n : ℝ)) = q ^ n by
      dsimp [q]; rw [mul_comm, Real.exp_nat_mul]] at h
    exact ((hS n).measureReal_eq measurableSet_Ioi).trans_le h
  have hunion : P.real (⋃ n, A n) ≤ 1 / 2 :=
    (geometric_union_bound P A (Real.exp (-d * K)) q (Real.exp_pos _).le hq0 hq1 hA).trans hscale
  have hnull : NullMeasurableSet (⋃ n, A n) P :=
    NullMeasurableSet.iUnion (fun n =>
      (hS n).aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi)
  have hcompl : (⋃ n, A n)ᶜ = {ω | ∀ n, S n ω ≤ K} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt, A]
  rw [← hcompl, measureReal_compl₀ hnull, probReal_univ]
  linarith
end ArgmaxGaussianBarrier
namespace ArgmaxNegativeWalkSurvival
lemma gaussian_iic_real_pos (m a : ℝ) :
    0 < (gaussianReal m 1).real (Set.Iic a) := by
  apply ENNReal.toReal_pos
  · intro hzero
    have h := (gaussianReal_absolutelyContinuous' m one_ne_zero) hzero
    simp at h
  · exact measure_ne_top _ _
theorem exists_uniform_negative_walk_survival (d : ℝ) (hd : 0 < d) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : NNReal → Ω → ℝ), IsPreBrownianReal B P →
        r ≤ P.real {ω | ∀ n : ℕ,
          B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) ≤ 0} := by
  obtain ⟨K, hK, hbarrier⟩ := ArgmaxGaussianBarrier.exists_uniform_gaussian_barrier d hd
  let α := (gaussianReal (-d) 1).real (Set.Iic (-K))
  have hα : 0 < α := gaussian_iic_real_pos (-d) (-K)
  refine ⟨α / 2, half_pos hα, ?_⟩
  intro Ω _ P _ B hB
  let S : ℕ → Ω → ℝ := fun n ω => B (1 + (n : NNReal)) ω - B 1 ω - d * (n : ℝ)
  let X : Ω → ℝ := fun ω => B 1 ω - d
  have hSlaw (n : ℕ) : HasLaw (S n)
      (gaussianReal (-(n : ℝ) * d) (n : NNReal)) P := by
    have h := gaussianReal_sub_const ((hB.shift 1).hasLaw_eval (n : NNReal)) (d * (n : ℝ))
    convert h using 1; congr 1; ring
  have hXlaw : HasLaw X (gaussianReal (-d) 1) P := by
    simpa only [zero_sub] using gaussianReal_sub_const (hB.hasLaw_eval 1) d
  let E : Set (ℕ → ℝ) := {f | ∀ n, f n ≤ K}
  have hE : MeasurableSet E := by
    simp only [E, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_le (measurable_pi_apply n) measurable_const
  let F : Set Ω := (fun ω n => S n ω) ⁻¹' E
  let A : Set Ω := X ⁻¹' Set.Iic (-K)
  have hF : (1 / 2 : ℝ) ≤ P.real F := hbarrier Ω P S hSlaw
  have hA : P.real A = α := hXlaw.measureReal_eq measurableSet_Iic
  have hInd : IndepFun (fun ω n => S n ω) X P := by
    exact (hB.indepFun_shift 1).comp
      (φ := fun f : NNReal → ℝ => fun n : ℕ => f (n : NNReal) - d * (n : ℝ))
      (ψ := fun g : Set.Iic (1 : NNReal) → ℝ => g ⟨1, by simp⟩ - d)
      (by fun_prop) (by fun_prop)
  have hinter : P.real (F ∩ A) = P.real F * P.real A := by
    have h := hInd.measure_inter_preimage_eq_mul E (Set.Iic (-K)) hE measurableSet_Iic
    simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
  have hsub : F ∩ A ⊆ {ω | ∀ n : ℕ,
      B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) ≤ 0} := by
    intro ω hω n
    have hf : B (1 + (n : NNReal)) ω - B 1 ω - d * (n : ℝ) ≤ K := hω.1 n
    have ha : B 1 ω - d ≤ -K := hω.2
    have ht : ((n + 1 : ℕ) : NNReal) = 1 + (n : NNReal) := by simp [add_comm]
    rw [ht]
    push_cast
    nlinarith
  calc
    α / 2 ≤ P.real F * α := by nlinarith
    _ = P.real (F ∩ A) := by rw [hinter, hA]
    _ ≤ _ := measureReal_mono hsub
end ArgmaxNegativeWalkSurvival
open MeasureTheory ProbabilityTheory
namespace ArgmaxStrictSurvival
lemma gaussian_hasLaw_ae_ne
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {m : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal m v) P)
    (hv : v ≠ 0) (a : ℝ) : ∀ᵐ ω ∂P, X ω ≠ a := by
  let := nullSingletonClass_gaussianReal (μ := m) hv
  have hzero : P {ω | X ω = a} = 0 := by
    have h := hX.measure_eq (p := fun x => x = a) (measurableSet_singleton a)
    simpa using h
  apply ae_iff.mpr
  simpa only [not_not] using hzero
lemma weak_strict_survival_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (S : ℕ → Ω → ℝ)
    (hS : ∀ᵐ ω ∂P, ∀ n, S n ω ≠ 0) :
    {ω | ∀ n, S n ω ≤ 0} =ᵐ[P] {ω | ∀ n, S n ω < 0} := by
  filter_upwards [hS] with ω hω
  change (∀ n, S n ω ≤ 0) = (∀ n, S n ω < 0)
  apply propext
  constructor
  · intro h n
    exact lt_of_le_of_ne (h n) (hω n)
  · intro h n
    exact (h n).le
lemma weak_strict_survival_real_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (S : ℕ → Ω → ℝ)
    (hS : ∀ᵐ ω ∂P, ∀ n, S n ω ≠ 0) :
    P.real {ω | ∀ n, S n ω ≤ 0} = P.real {ω | ∀ n, S n ω < 0} := by
  exact congrArg ENNReal.toReal (measure_congr (weak_strict_survival_ae S hS))
theorem sampled_drifted_values_ae_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) ≠ 0 := by
  apply ae_all_iff.mpr
  intro n
  have hLaw : HasLaw
      (fun ω => B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ))
      (gaussianReal (-((n + 1 : ℕ) : ℝ) * d) ((n + 1 : ℕ) : NNReal)) P := by
    have h := gaussianReal_sub_const (hB.hasLaw_eval ((n + 1 : ℕ) : NNReal))
      (d * (n + 1 : ℕ))
    convert h using 1; congr 1; ring
  exact gaussian_hasLaw_ae_ne hLaw (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) 0
theorem sampled_weak_strict_survival_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) :
    {ω | ∀ n : ℕ, B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) ≤ 0} =ᵐ[P]
      {ω | ∀ n : ℕ, B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) < 0} :=
  weak_strict_survival_ae _ (sampled_drifted_values_ae_ne_zero hB d)
theorem sampled_weak_strict_survival_real_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) :
    P.real {ω | ∀ n : ℕ, B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) ≤ 0} =
      P.real {ω | ∀ n : ℕ, B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) < 0} := by
  exact congrArg ENNReal.toReal (measure_congr (sampled_weak_strict_survival_ae hB d))
end ArgmaxStrictSurvival
namespace ArgmaxStrictSurvival
theorem exists_uniform_strict_negative_walk_survival (d : ℝ) (hd : 0 < d) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : NNReal → Ω → ℝ), IsPreBrownianReal B P →
        r ≤ P.real {ω | ∀ n : ℕ,
          B ((n + 1 : ℕ) : NNReal) ω - d * (n + 1 : ℕ) < 0} := by
  obtain ⟨r, hr, hsurvival⟩ :=
    ArgmaxNegativeWalkSurvival.exists_uniform_negative_walk_survival d hd
  refine ⟨r, hr, ?_⟩
  intro Ω _ P _ B hB
  rw [← sampled_weak_strict_survival_real_eq hB d]
  exact hsurvival Ω P B hB
end ArgmaxStrictSurvival
open MeasureTheory ProbabilityTheory
namespace ArgmaxBrownianIncrements
theorem unit_increment_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (k : ℕ) :
    HasLaw (fun ω => B ((k + 1 : ℕ) : NNReal) ω - B (k : NNReal) ω)
      (gaussianReal 0 1) P := by
  have hvar : nndist (((k + 1 : ℕ) : NNReal).1) ((k : NNReal).1) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_one, coe_nndist, Real.dist_eq]
    change |((k + 1 : ℕ) : ℝ) - (k : ℝ)| = 1
    simp
  have h := hB.hasLaw_sub ((k + 1 : ℕ) : NNReal) (k : NNReal)
  rw [hvar] at h
  exact h
theorem unit_increments_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (n : ℕ) :
    iIndepFun (fun (i : Fin n) ω =>
      B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω) P := by
  have ht : Monotone (fun i : Fin (n + 1) => (i.val : NNReal)) := by
    intro i j hij
    exact Nat.cast_le.mpr (Fin.val_fin_le.mpr hij)
  simpa only [Fin.val_succ, Fin.val_castSucc] using
    hB.hasIndepIncrements n (fun i : Fin (n + 1) => (i.val : NNReal)) ht
theorem unit_increments_hasLaw_pi
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (n : ℕ) :
    HasLaw (fun ω (i : Fin n) =>
      B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) P := by
  exact (unit_increments_iIndepFun hB n).hasLaw_pi
    (fun i => unit_increment_hasLaw hB i.val)
theorem drifted_unit_increment_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (k : ℕ) :
    HasLaw (fun ω => B ((k + 1 : ℕ) : NNReal) ω - B (k : NNReal) ω - d)
      (gaussianReal (-d) 1) P := by
  simpa only [zero_sub] using gaussianReal_sub_const (unit_increment_hasLaw hB k) d
theorem drifted_unit_increments_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (n : ℕ) :
    iIndepFun (fun (i : Fin n) ω =>
      B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω - d) P := by
  exact (unit_increments_iIndepFun hB n).comp (fun _ x => x - d) (by fun_prop)
theorem drifted_unit_increments_hasLaw_pi
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (n : ℕ) :
    HasLaw (fun ω (i : Fin n) =>
      B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω - d)
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)) P := by
  exact (drifted_unit_increments_iIndepFun hB d n).hasLaw_pi
    (fun i => drifted_unit_increment_hasLaw hB d i.val)
end ArgmaxBrownianIncrements
namespace ArgmaxPastRecord
lemma prefix_sum_reversed_increments (f : ℕ → ℝ) (n : ℕ) (k : Fin n) (d : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
      (f (i.rev.val + 1) - f i.rev.val - d)) =
      (f n - d * (n : ℝ)) -
        (f (n - (k.val + 1)) - d * ((n - (k.val + 1) : ℕ) : ℝ)) := by
  let g : Fin (n + 1) → ℝ := fun j => -f (n - j.val) + d * ((n - j.val : ℕ) : ℝ)
  have hfilter : Finset.univ.filter (fun j : Fin n => j ≤ k) = Finset.Iic k := by
    ext i
    simp
  rw [hfilter]
  calc
    _ = ∑ i ∈ Finset.Iic k, (g i.succ - g i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      have hidx : n - (i.val + 1) + 1 = n - i.val := by omega
      simp only [g, Fin.val_succ, Fin.val_castSucc, Fin.val_rev]
      rw [← hidx]
      push_cast
      ring
    _ = g k.succ - g 0 := Fin.sum_Iic_sub k g
    _ = _ := by simp only [g, Fin.val_succ, Fin.val_zero, Nat.sub_zero]; ring
lemma positive_reversed_prefixes_iff_past_record (f : ℕ → ℝ) (n : ℕ) (d : ℝ) :
    (∀ k : Fin n, 0 < ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
      (f (i.rev.val + 1) - f i.rev.val - d)) ↔
      (∀ k : Fin n, f k.val - d * (k.val : ℝ) < f n - d * (n : ℝ)) := by
  constructor
  · intro h k
    have hk := h k.rev
    rw [prefix_sum_reversed_increments] at hk
    have hidx : n - (k.rev.val + 1) = k.val := by
      simpa only [Fin.val_rev] using congrArg Fin.val (Fin.rev_rev k)
    rw [hidx] at hk
    linarith
  · intro h k
    rw [prefix_sum_reversed_increments]
    have hk := h k.rev
    simpa only [Fin.val_rev, sub_pos] using hk
theorem reversed_drifted_unit_increments_hasLaw_pi
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (n : ℕ) :
    HasLaw (fun ω (i : Fin n) =>
      B ((i.rev.val + 1 : ℕ) : NNReal) ω - B (i.rev.val : NNReal) ω - d)
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)) P := by
  exact ((ArgmaxBrownianIncrements.drifted_unit_increments_iIndepFun hB d n).precomp
    (g := Fin.rev) Fin.rev_injective).hasLaw_pi
    (fun i => ArgmaxBrownianIncrements.drifted_unit_increment_hasLaw hB d i.rev.val)
lemma measurableSet_positive_prefixes (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
theorem past_record_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (d : ℝ) (n : ℕ) :
    P.real {ω | ∀ k : Fin n,
      B (k.val : NNReal) ω - d * (k.val : ℝ) < B (n : NNReal) ω - d * (n : ℝ)} =
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  have hevent :
      {ω | ∀ k : Fin n,
        B (k.val : NNReal) ω - d * (k.val : ℝ) < B (n : NNReal) ω - d * (n : ℝ)} =
      {ω | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
          (B ((i.rev.val + 1 : ℕ) : NNReal) ω - B (i.rev.val : NNReal) ω - d)} := by
    ext ω
    exact (positive_reversed_prefixes_iff_past_record (fun j => B (j : NNReal) ω) n d).symm
  rw [hevent]
  exact (reversed_drifted_unit_increments_hasLaw_pi hB d n).measureReal_eq
    (measurableSet_positive_prefixes n)
end ArgmaxPastRecord
open MeasureTheory ProbabilityTheory
namespace ArgmaxRecordFactorization
lemma measurableSet_past_record_path (n : ℕ) (d : ℝ) :
    MeasurableSet {f : NNReal → ℝ | ∀ k : Fin n,
      f (k.val : NNReal) - d * (k.val : ℝ) < f (n : NNReal) - d * (n : ℝ)} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt (by fun_prop) (by fun_prop)
lemma measurableSet_strict_future_path (n : ℕ) (d : ℝ) :
    MeasurableSet {f : NNReal → ℝ | ∀ m : ℕ,
      f ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) - f (n : NNReal) -
        d * (m + 1 : ℕ) < 0} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro m
  exact measurableSet_lt (by fun_prop) measurable_const
lemma measurableSet_weak_survival_path (d : ℝ) :
    MeasurableSet {f : NNReal → ℝ | ∀ m : ℕ,
      f ((m + 1 : ℕ) : NNReal) - d * (m + 1 : ℕ) ≤ 0} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro m
  exact measurableSet_le (by fun_prop) measurable_const
theorem past_record_strict_future_factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (n : ℕ) (d : ℝ) :
    P.real
      ({ω | ∀ k : Fin n,
        B (k.val : NNReal) ω - d * (k.val : ℝ) < B (n : NNReal) ω - d * (n : ℝ)} ∩
      {ω | ∀ m : ℕ,
        B ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - B (n : NNReal) ω -
          d * (m + 1 : ℕ) < 0}) =
      P.real {ω | ∀ k : Fin n,
        B (k.val : NNReal) ω - d * (k.val : ℝ) < B (n : NNReal) ω - d * (n : ℝ)} *
      P.real {ω | ∀ m : ℕ,
        B ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - B (n : NNReal) ω -
          d * (m + 1 : ℕ) < 0} := by
  let F : Set (NNReal → ℝ) := {f | ∀ m : ℕ,
    f ((m + 1 : ℕ) : NNReal) - d * (m + 1 : ℕ) < 0}
  let E : Set (Set.Iic (n : NNReal) → ℝ) := {g | ∀ k : Fin n,
    g ⟨(k.val : NNReal), by
      change (k.val : NNReal) ≤ (n : NNReal)
      exact Nat.cast_le.mpr k.isLt.le⟩ - d * (k.val : ℝ) <
      g ⟨(n : NNReal), by simp⟩ - d * (n : ℝ)}
  have hF : MeasurableSet F := by
    simp only [F, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro m
    exact measurableSet_lt (by fun_prop) measurable_const
  have hE : MeasurableSet E := by
    simp only [E, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have h := (hB.indepFun_shift (n : NNReal)).measure_inter_preimage_eq_mul F E hF hE
  have hr := congrArg ENNReal.toReal h
  simpa only [F, E, Set.preimage_ofPred_eq, measureReal_def, ENNReal.toReal_mul, Set.inter_comm, mul_comm] using hr
theorem two_arm_record_event_factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U V : NNReal → Ω → ℝ} (hU : IsPreBrownianReal U P)
    (hUV : IndepFun (fun ω t => U t ω) (fun ω t => V t ω) P)
    (n : ℕ) (d : ℝ) :
    P.real
      (({ω | ∀ k : Fin n,
        U (k.val : NNReal) ω - d * (k.val : ℝ) < U (n : NNReal) ω - d * (n : ℝ)} ∩
      {ω | ∀ m : ℕ,
        U ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - U (n : NNReal) ω -
          d * (m + 1 : ℕ) < 0}) ∩
      {ω | ∀ m : ℕ, V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) ≤ 0}) =
      P.real {ω | ∀ k : Fin n,
        U (k.val : NNReal) ω - d * (k.val : ℝ) < U (n : NNReal) ω - d * (n : ℝ)} *
      P.real {ω | ∀ m : ℕ,
        U ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - U (n : NNReal) ω -
          d * (m + 1 : ℕ) < 0} *
      P.real {ω | ∀ m : ℕ, V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) ≤ 0} := by
  let E : Set (NNReal → ℝ) := {f | ∀ k : Fin n,
    f (k.val : NNReal) - d * (k.val : ℝ) < f (n : NNReal) - d * (n : ℝ)}
  let F : Set (NNReal → ℝ) := {f | ∀ m : ℕ,
    f ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) - f (n : NNReal) - d * (m + 1 : ℕ) < 0}
  let L : Set (NNReal → ℝ) := {f | ∀ m : ℕ,
    f ((m + 1 : ℕ) : NNReal) - d * (m + 1 : ℕ) ≤ 0}
  have h := hUV.measure_inter_preimage_eq_mul (E ∩ F) L
    ((measurableSet_past_record_path n d).inter (measurableSet_strict_future_path n d))
    (measurableSet_weak_survival_path d)
  have hr := congrArg ENNReal.toReal h
  have hreal :
      P.real
        (({ω | ∀ k : Fin n,
          U (k.val : NNReal) ω - d * (k.val : ℝ) < U (n : NNReal) ω - d * (n : ℝ)} ∩
        {ω | ∀ m : ℕ,
          U ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - U (n : NNReal) ω -
            d * (m + 1 : ℕ) < 0}) ∩
        {ω | ∀ m : ℕ, V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) ≤ 0}) =
        P.real
          ({ω | ∀ k : Fin n,
            U (k.val : NNReal) ω - d * (k.val : ℝ) < U (n : NNReal) ω - d * (n : ℝ)} ∩
          {ω | ∀ m : ℕ,
            U ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - U (n : NNReal) ω -
              d * (m + 1 : ℕ) < 0}) *
        P.real {ω | ∀ m : ℕ, V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) ≤ 0} := by
    simpa only [E, F, L, Set.preimage_ofPred_eq, measureReal_def, ENNReal.toReal_mul, Set.preimage_inter] using hr
  rw [hreal, past_record_strict_future_factorization hU n d]
end ArgmaxRecordFactorization
namespace ArgmaxRecordDeterministic
theorem strict_global_record (H : ℤ → ℝ) (n : ℕ) (hn : 0 < n)
    (hzero : H 0 = 0)
    (hpast : ∀ k : ℕ, k < n → H (k : ℤ) < H (n : ℤ))
    (hfuture : ∀ m : ℕ, H ((n : ℤ) + (m : ℤ) + 1) < H (n : ℤ))
    (hopposite : ∀ m : ℕ, H (-((m : ℤ) + 1)) ≤ 0) :
    ∀ z : ℤ, z ≠ (n : ℤ) → H z < H (n : ℤ) := by
  have hpositive : 0 < H (n : ℤ) := by
    simpa only [Nat.cast_zero, hzero] using hpast 0 hn
  intro z hzn
  cases z with
  | ofNat k =>
      simp only [Int.ofNat_eq_natCast] at hzn ⊢
      by_cases hkn : k < n
      · exact hpast k hkn
      · have hnk : n < k := by omega
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = n + m + 1 :=
          ⟨k - n - 1, by omega⟩
        simpa only [Nat.cast_add, Nat.cast_one] using hfuture m
  | negSucc m =>
      have hnonpositive : H (Int.negSucc m) ≤ 0 := by
        simpa only [Int.negSucc_eq] using hopposite m
      exact lt_of_le_of_lt hnonpositive hpositive
theorem maximizer_eq_record (H : ℤ → ℝ) (n : ℕ) (hn : 0 < n)
    (hzero : H 0 = 0)
    (hpast : ∀ k : ℕ, k < n → H (k : ℤ) < H (n : ℤ))
    (hfuture : ∀ m : ℕ, H ((n : ℤ) + (m : ℤ) + 1) < H (n : ℤ))
    (hopposite : ∀ m : ℕ, H (-((m : ℤ) + 1)) ≤ 0)
    (D : ℤ) (hmax : ∀ z : ℤ, H z ≤ H D) : D = (n : ℤ) := by
  by_contra hDn
  have hstrict := strict_global_record H n hn hzero hpast hfuture hopposite D hDn
  exact (not_lt_of_ge (hmax (n : ℤ))) hstrict
end ArgmaxRecordDeterministic
namespace ArgmaxAtomLower
theorem exists_uniform_positive_atom_lower (d : ℝ) (hd : 0 < d) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsPreBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ D : Ω → ℤ,
          (∀ᵐ ω ∂P, ∀ z : ℤ,
            B (z : ℝ) ω - d * |(z : ℝ)| ≤
              B (D ω : ℝ) ω - d * |(D ω : ℝ)|) →
          ∀ n : ℕ, 0 < n →
            r ^ 2 * (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
              {x : Fin n → ℝ | ∀ k : Fin n,
                0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} ≤
              P.real {ω | D ω = (n : ℤ)} := by
  obtain ⟨r, hr, hstay⟩ :=
    ArgmaxStrictSurvival.exists_uniform_strict_negative_walk_survival d hd
  refine ⟨r, hr, ?_⟩
  intro Ω _ P _ B hplus hminus hInd D hmax n hn
  let U : NNReal → Ω → ℝ := fun t ω => B (t : ℝ) ω
  let V : NNReal → Ω → ℝ := fun t ω => B (-(t : ℝ)) ω
  let E : Set Ω := {ω | ∀ k : Fin n,
    U (k.val : NNReal) ω - d * (k.val : ℝ) < U (n : NNReal) ω - d * (n : ℝ)}
  let F : Set Ω := {ω | ∀ m : ℕ,
    U ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - U (n : NNReal) ω -
      d * (m + 1 : ℕ) < 0}
  let L : Set Ω := {ω | ∀ m : ℕ,
    V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) ≤ 0}
  have hF : r ≤ P.real F := hstay Ω P
    (fun t ω => U ((n : NNReal) + t) ω - U (n : NNReal) ω) (hplus.shift n)
  have hL : r ≤ P.real L := by
    have h := hstay Ω P V hminus
    refine h.trans (measureReal_mono ?_)
    intro ω hω
    change (∀ m : ℕ, V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) < 0) at hω
    exact fun m => (hω m).le
  have hpast := ArgmaxPastRecord.past_record_probability hplus d n
  change P.real E =
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} at hpast
  have hfactor := ArgmaxRecordFactorization.two_arm_record_event_factorization hplus hInd n d
  change P.real ((E ∩ F) ∩ L) = P.real E * P.real F * P.real L at hfactor
  have hAE : ∀ᵐ ω ∂P, ω ∈ ((E ∩ F) ∩ L) → D ω = (n : ℤ) := by
    filter_upwards [hmax, hplus.eval_zero_ae_eq_zero] with ω hmaxω hzeroω
    intro hω
    rcases hω with ⟨⟨hp, hf⟩, hl⟩
    change (∀ k : Fin n,
      U (k.val : NNReal) ω - d * (k.val : ℝ) < U (n : NNReal) ω - d * (n : ℝ)) at hp
    change (∀ m : ℕ,
      U ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) ω - U (n : NNReal) ω -
        d * (m + 1 : ℕ) < 0) at hf
    change (∀ m : ℕ, V ((m + 1 : ℕ) : NNReal) ω - d * (m + 1 : ℕ) ≤ 0) at hl
    let H : ℤ → ℝ := fun z => B (z : ℝ) ω - d * |(z : ℝ)|
    have hnat (k : ℕ) : H (k : ℤ) = U (k : NNReal) ω - d * (k : ℝ) := by
      simp [H, U, NNReal.coe_natCast]
    have hnegative (k : ℕ) : H (-((k : ℤ) + 1)) =
        V ((k + 1 : ℕ) : NNReal) ω - d * (k + 1 : ℕ) := by
      dsimp only [H, V]
      simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    have hzero : H 0 = 0 := by simpa [H] using hzeroω
    have hpastω : ∀ k : ℕ, k < n → H (k : ℤ) < H (n : ℤ) := by
      intro k hk
      rw [hnat k, hnat n]
      exact hp ⟨k, hk⟩
    have hfutureω : ∀ m : ℕ, H ((n : ℤ) + (m : ℤ) + 1) < H (n : ℤ) := by
      intro m
      have h := hf m
      have hidx : ((n : NNReal) + ((m + 1 : ℕ) : NNReal)) =
          ((n + m + 1 : ℕ) : NNReal) := by push_cast; ring
      rw [hidx] at h
      have hz : (n : ℤ) + (m : ℤ) + 1 = ((n + m + 1 : ℕ) : ℤ) := by omega
      rw [hz, hnat (n + m + 1), hnat n]
      push_cast at h ⊢
      nlinarith
    have hoppositeω : ∀ m : ℕ, H (-((m : ℤ) + 1)) ≤ 0 := by
      intro m
      rw [hnegative m]
      exact hl m
    exact ArgmaxRecordDeterministic.maximizer_eq_record H n hn hzero hpastω
      hfutureω hoppositeω (D ω) hmaxω
  have hsubset : P.real ((E ∩ F) ∩ L) ≤ P.real {ω | D ω = (n : ℤ)} := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hAE)
  have hprod : r ^ 2 * P.real E ≤ P.real E * P.real F * P.real L := by
    have hFL : r * r ≤ P.real F * P.real L :=
      mul_le_mul hF hL hr.le (measureReal_nonneg (μ := P) (s := F))
    calc
      _ = P.real E * (r * r) := by ring
      _ ≤ P.real E * (P.real F * P.real L) :=
        mul_le_mul_of_nonneg_left hFL (measureReal_nonneg (μ := P) (s := E))
      _ = _ := by ring
  calc
    _ = r ^ 2 * P.real E := by rw [hpast]
    _ ≤ P.real E * P.real F * P.real L := hprod
    _ = P.real ((E ∩ F) ∩ L) := hfactor.symm
    _ ≤ _ := hsubset
end ArgmaxAtomLower
open scoped BigOperators ENNReal
open MeasureTheory
namespace FiniteProductDensity
theorem pi_eq_withDensity_ofReal_prod
    {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)]
    (μ ν : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → X i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i))
    (hnonneg : ∀ i x, 0 ≤ f i x)
    (hν : ∀ i, ν i = (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) :
    Measure.pi ν = (Measure.pi μ).withDensity
      (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hprod : Integrable (fun x : (i : ι) → X i => ∏ i, f i (x i))
      ((Measure.pi μ).restrict (Set.univ.pi s)) := by
    rw [Measure.restrict_pi_pi]
    exact Integrable.fintype_prod_dep (fun i => (hf i).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hnonneg i (x i))))]
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [hν i, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict
    (Filter.Eventually.of_forall (hnonneg i))
end FiniteProductDensity
open MeasureTheory ProbabilityTheory
namespace ArgmaxGaussianTilt
lemma pdf_real_unit_shift (μ t x : ℝ) :
    gaussianPDFReal (μ + t) 1 x =
      Real.exp (t * x - t * μ - t ^ 2 / 2) * gaussianPDFReal μ 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring
lemma pdf_unit_shift (μ t x : ℝ) :
    gaussianPDF (μ + t) 1 x = gaussianPDF μ 1 x *
      ENNReal.ofReal (Real.exp (t * x - t * μ - t ^ 2 / 2)) := by
  simp only [gaussianPDF, pdf_real_unit_shift]
  rw [mul_comm, ENNReal.ofReal_mul (gaussianPDFReal_nonneg μ 1 x)]
theorem gaussian_unit_shift (μ t : ℝ) :
    gaussianReal (μ + t) 1 =
      (gaussianReal μ 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (t * x - t * μ - t ^ 2 / 2))) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul volume (measurable_gaussianPDF μ 1) (by fun_prop)]
  congr 1
  funext x
  exact pdf_unit_shift μ t x
theorem integral_gaussian_unit_shift (μ t : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂gaussianReal (μ + t) 1) =
      ∫ x, Real.exp (t * x - t * μ - t ^ 2 / 2) * f x ∂gaussianReal μ 1 := by
  rw [gaussian_unit_shift]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
end ArgmaxGaussianTilt
open scoped BigOperators
namespace ArgmaxGaussianTilt
lemma integrable_unit_weight (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x - t ^ 2 / 2)) (gaussianReal 0 1) := by
  simp_rw [sub_eq_add_neg, Real.exp_add]
  exact (integrable_exp_mul_gaussianReal t).mul_const _
lemma prod_unit_weight {ι : Type*} [Fintype ι] (t : ℝ) (x : ι → ℝ) :
    (∏ i, Real.exp (t * x i - t ^ 2 / 2)) =
      Real.exp (t * (∑ i, x i) - (Fintype.card ι : ℝ) * t ^ 2 / 2) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring
theorem pi_gaussian_unit_shift {ι : Type*} [Fintype ι] (t : ℝ) :
    Measure.pi (fun _ : ι => gaussianReal t 1) =
      (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun x : ι → ℝ => ENNReal.ofReal
          (Real.exp (t * (∑ i, x i) - (Fintype.card ι : ℝ) * t ^ 2 / 2))) := by
  have h := FiniteProductDensity.pi_eq_withDensity_ofReal_prod
    (fun _ : ι => gaussianReal 0 1) (fun _ : ι => gaussianReal t 1)
    (fun _ x => Real.exp (t * x - t ^ 2 / 2))
    (fun _ => integrable_unit_weight t)
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => by simpa using gaussian_unit_shift 0 t)
  rw [h]
  congr 1
  funext x
  rw [prod_unit_weight]
theorem integral_pi_gaussian_unit_shift {ι : Type*} [Fintype ι]
    (t : ℝ) (f : (ι → ℝ) → ℝ) :
    (∫ x, f x ∂Measure.pi (fun _ : ι => gaussianReal t 1)) =
      ∫ x, Real.exp (t * (∑ i, x i) - (Fintype.card ι : ℝ) * t ^ 2 / 2) * f x
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  rw [pi_gaussian_unit_shift]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
theorem event_pi_gaussian_negative_shift {ι : Type*} [Fintype ι]
    (d : ℝ) (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : ι => gaussianReal (-d) 1)).real A =
      Real.exp (-(Fintype.card ι : ℝ) * d ^ 2 / 2) *
        ∫ x in A, Real.exp (-d * (∑ i, x i))
          ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  calc
    _ = ∫ _ in A, (1 : ℝ) ∂Measure.pi (fun _ : ι => gaussianReal (-d) 1) := by simp
    _ = ∫ x in A, Real.exp ((-d) * (∑ i, x i) - (Fintype.card ι : ℝ) * (-d) ^ 2 / 2)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
      rw [pi_gaussian_unit_shift]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hA]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_one]
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun hA
      intro x _
      dsimp only
      rw [← Real.exp_add]
      congr 1
      ring
lemma integrable_exp_sum {ι : Type*} [Fintype ι] (t : ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (t * ∑ i, x i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have h := Integrable.fintype_prod
    (μ := fun _ : ι => gaussianReal 0 1)
    (fun _ : ι => integrable_exp_mul_gaussianReal t)
  simpa only [← Real.exp_sum, ← Finset.mul_sum] using h
lemma measurableSet_positive_prefixes (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
theorem positive_prefixes_negative_shift (n : ℕ) (d : ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} =
      Real.exp (-(n : ℝ) * d ^ 2 / 2) *
        ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
          Real.exp (-d * ∑ i, x i)
          ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  simpa only [Fintype.card_fin] using
    event_pi_gaussian_negative_shift d _ (measurableSet_positive_prefixes n)
end ArgmaxGaussianTilt
open MeasureTheory ProbabilityTheory
namespace ArgmaxBrownianTilt
lemma prefix_sum_drifted_increments (f : ℕ → ℝ) (n : ℕ) (k : Fin n) (d : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
      (f (i.val + 1) - f i.val - d)) =
      f (k.val + 1) - d * (k.val + 1 : ℕ) - f 0 := by
  have hfilter : Finset.univ.filter (fun j : Fin n => j ≤ k) = Finset.Iic k := by
    ext i
    simp
  rw [hfilter]
  calc
    _ = ∑ i ∈ Finset.Iic k,
        ((f (i.val + 1) - d * (i.val + 1 : ℕ)) - (f i.val - d * (i.val : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    _ = _ := by
      have h := Fin.sum_Iic_sub k (fun j : Fin (n + 1) => f j.val - d * (j.val : ℝ))
      simpa only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Nat.cast_zero,
        mul_zero, sub_zero] using h
theorem positive_drifted_increments_survival
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (n : ℕ) (d : ℝ) :
    P.real {ω | ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k),
        (B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω - d)} =
      Real.exp (-(n : ℝ) * d ^ 2 / 2) *
        ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
          Real.exp (-d * ∑ i, x i)
          ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  calc
    _ = (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} :=
      (ArgmaxBrownianIncrements.drifted_unit_increments_hasLaw_pi hB d n).measureReal_eq
        (ArgmaxGaussianTilt.measurableSet_positive_prefixes n)
    _ = _ := ArgmaxGaussianTilt.positive_prefixes_negative_shift n d
theorem positive_brownian_values_survival
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P) (n : ℕ) (d : ℝ) :
    P.real {ω | ∀ k : Fin n,
      0 < B ((k.val + 1 : ℕ) : NNReal) ω - d * (k.val + 1 : ℕ)} =
      Real.exp (-(n : ℝ) * d ^ 2 / 2) *
        ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
          Real.exp (-d * ∑ i, x i)
          ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hevent :
      {ω | ∀ k : Fin n,
        0 < B ((k.val + 1 : ℕ) : NNReal) ω - d * (k.val + 1 : ℕ)} =ᵐ[P]
      {ω | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k),
          (B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω - d)} := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
    change (∀ k : Fin n,
      0 < B ((k.val + 1 : ℕ) : NNReal) ω - d * (k.val + 1 : ℕ)) =
      (∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k),
          (B ((i.val + 1 : ℕ) : NNReal) ω - B (i.val : NNReal) ω - d))
    apply propext
    simp_rw [prefix_sum_drifted_increments (fun j => B (j : NNReal) ω)]
    simp only [Nat.cast_zero, hzero, sub_zero]
  have heq := congrArg ENNReal.toReal (measure_congr hevent)
  exact heq.trans (positive_drifted_increments_survival hB n d)
end ArgmaxBrownianTilt
namespace ArgmaxPositiveRotation
lemma exists_last_min_on_range (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ r < n, (∀ j < n, f r ≤ f j) ∧
      (∀ j, r < j → j < n → f r < f j) := by
  classical
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.range n) f
    ⟨0, Finset.mem_range.mpr hn⟩
  let I := (Finset.range n).filter (fun j => f j = f i)
  have hI : I.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  let r := I.max' hI
  have hrmem : r ∈ I := Finset.max'_mem I hI
  have hrlt : r < n := Finset.mem_range.mp (Finset.mem_filter.mp hrmem).1
  have hreq : f r = f i := (Finset.mem_filter.mp hrmem).2
  refine ⟨r, hrlt, ?_, ?_⟩
  · intro j hj
    rw [hreq]
    exact hmin j (Finset.mem_range.mpr hj)
  · intro j hrj hj
    have hle : f r ≤ f j := by
      rw [hreq]
      exact hmin j (Finset.mem_range.mpr hj)
    apply lt_of_le_of_ne hle
    intro heq
    have hjI : j ∈ I := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hj, heq.symm.trans hreq⟩
    have hjr : j ≤ r := Finset.le_max' I j hjI
    omega
lemma sum_take_rotate_no_wrap (l : List ℝ) (r k : ℕ)
    (hr : r ≤ l.length) (hk : r + k ≤ l.length) :
    ((l.rotate r).take k).sum + (l.take r).sum = (l.take (r + k)).sum := by
  rw [List.rotate_eq_drop_append_take hr,
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
  have hs := congrArg List.sum (List.take_add (l := l) (i := r) (j := k))
  simpa only [List.sum_append, add_comm] using hs.symm
lemma sum_take_rotate_wrap (l : List ℝ) (r k : ℕ)
    (hr : r ≤ l.length) (hwrap : l.length - r ≤ k) (hk : k ≤ l.length) :
    ((l.rotate r).take k).sum + (l.take r).sum =
      l.sum + (l.take (k - (l.length - r))).sum := by
  have hj : k - (l.length - r) ≤ r := by omega
  have htake : ((l.drop r ++ l.take r).take k) =
      l.drop r ++ l.take (k - (l.length - r)) := by
    rw [List.take_append, List.take_of_length_le (by simpa only [List.length_drop] using hwrap),
      List.length_drop, List.take_take, Nat.min_eq_left hj]
  rw [List.rotate_eq_drop_append_take hr, htake, List.sum_append]
  have hs := List.sum_take_add_sum_drop l r
  linarith
lemma exists_rotate_strictly_positive_prefixes (l : List ℝ) (hsum : 0 < l.sum) :
    ∃ r < l.length, ∀ k, 0 < k → k ≤ l.length →
      0 < ((l.rotate r).take k).sum := by
  have hn : 0 < l.length := by
    by_contra h
    have hempty : l = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hempty] at hsum
  obtain ⟨r, hr, hmin, hlast⟩ :=
    exists_last_min_on_range (fun j => (l.take j).sum) l.length hn
  have hrzero : (l.take r).sum ≤ 0 := by
    simpa using hmin 0 hn
  have hafter : ∀ j, r < j → j ≤ l.length → (l.take r).sum < (l.take j).sum := by
    intro j hrj hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hlast j hrj hj
    · simpa using lt_of_le_of_lt hrzero hsum
  refine ⟨r, hr, ?_⟩
  intro k hkpos hk
  by_cases hnowrap : r + k ≤ l.length
  · have heq := sum_take_rotate_no_wrap l r k hr.le hnowrap
    have hstrict := hafter (r + k) (by omega) hnowrap
    linarith
  · have hwrap : l.length - r ≤ k := by omega
    have heq := sum_take_rotate_wrap l r k hr.le hwrap hk
    have hj : k - (l.length - r) < l.length := by omega
    have hlow := hmin (k - (l.length - r)) hj
    linarith
end ArgmaxPositiveRotation
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace ArgmaxCyclicSurvival
lemma ofFn_rotate_eq {n : ℕ} (x : Fin n → ℝ) (r : Fin n) :
    (List.ofFn x).rotate r.val = List.ofFn (fun i => x (i + r)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_rotate, List.length_ofFn, List.getElem_ofFn]
    congr 1
lemma exists_positive_prefix_rotation {n : ℕ} (x : Fin n → ℝ)
    (hx : 0 < ∑ i, x i) :
    ∃ r : Fin n, ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x (i + r) := by
  obtain ⟨r, hr, hp⟩ := ArgmaxPositiveRotation.exists_rotate_strictly_positive_prefixes
    (List.ofFn x) (by simpa only [List.sum_ofFn] using hx)
  have hrn : r < n := by simpa only [List.length_ofFn] using hr
  let r' : Fin n := ⟨r, hrn⟩
  refine ⟨r', ?_⟩
  intro k
  have h := hp (k.val + 1) (Nat.succ_pos _) (by simpa only [List.length_ofFn] using Nat.succ_le_of_lt k.isLt)
  rw [show r = r'.val from rfl, ofFn_rotate_eq, List.sum_take_ofFn] at h
  simpa only [Fin.le_def, Nat.lt_succ_iff] using h
lemma measurableSet_positive_prefixes (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
lemma measurePreserving_pi_precomp {n : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun (x : Fin n → ℝ) i => x (e i))
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
  convert measurePreserving_piCongrLeft (α := fun _ : Fin n => ℝ)
    (fun _ : Fin n => μ) e.symm using 1
  ext x i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
theorem total_positive_le_card_mul_survival (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (Measure.pi (fun _ : Fin n => μ)).real {x : Fin n → ℝ | 0 < ∑ i, x i} ≤
      (n : ℝ) * (Measure.pi (fun _ : Fin n => μ)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  let A : Set (Fin n → ℝ) := {x | ∀ k : Fin n,
    0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i}
  let rot (r : Fin n) (x : Fin n → ℝ) : Fin n → ℝ := fun i => x (i + r)
  have hsub : {x : Fin n → ℝ | 0 < ∑ i, x i} ⊆ ⋃ r : Fin n, rot r ⁻¹' A := by
    intro x hx
    obtain ⟨r, hr⟩ := exists_positive_prefix_rotation x hx
    exact Set.mem_iUnion.mpr ⟨r, hr⟩
  have hmeasure (r : Fin n) :
      (Measure.pi (fun _ : Fin n => μ)).real (rot r ⁻¹' A) =
        (Measure.pi (fun _ : Fin n => μ)).real A := by
    exact (measurePreserving_pi_precomp μ (finCycle r)).measureReal_preimage
      (measurableSet_positive_prefixes n).nullMeasurableSet
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => μ)).real (⋃ r : Fin n, rot r ⁻¹' A) :=
      measureReal_mono hsub
    _ ≤ ∑ r : Fin n, (Measure.pi (fun _ : Fin n => μ)).real (rot r ⁻¹' A) :=
      measureReal_iUnion_fintype_le _
    _ = _ := by simp_rw [hmeasure]; simp [A]
theorem gaussian_survival_ge_endpoint_div (n : ℕ) (hn : 0 < n) (d : ℝ) :
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | 0 < ∑ i, x i} / (n : ℝ) ≤
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ hn').mpr
  simpa only [mul_comm] using total_positive_le_card_mul_survival n (gaussianReal (-d) 1)
end ArgmaxCyclicSurvival
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace ArgmaxGaussianEndpointLaw
lemma gaussian_endpoint_hasLaw (n : ℕ) (d : ℝ) :
    HasLaw (fun x : Fin n → ℝ => ∑ i, x i)
      (gaussianReal (-(n : ℝ) * d) (n : ℝ≥0))
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply, charFun_gaussianReal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
end ArgmaxGaussianEndpointLaw
open MeasureTheory ProbabilityTheory
namespace ArgmaxGaussianEndpoint
lemma unit_interval_exponent_bound (d v x : ℝ) (hd : 0 ≤ d) (hv : 1 ≤ v)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -(v * d) ^ 2 / (2 * v) - d - 1 / 2 ≤ -(x + v * d) ^ 2 / (2 * v) := by
  have hvpos : 0 < v := by linarith
  have hdx : d * x ≤ d := by nlinarith
  have hdxv : v * (d * x) ≤ v * d := mul_le_mul_of_nonneg_left hdx hvpos.le
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * v)).2
    at hx2
  field_simp
  nlinarith
lemma pdf_lower_on_unit_interval (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d)
    (x : ℝ) (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / Real.sqrt (n : ℝ) ≤
      gaussianPDFReal (-(n : ℝ) * d) (n : NNReal) x := by
  have hnreal : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hexp : -(d ^ 2 / 2) * (n : ℝ) - d - 1 / 2 ≤
      -(x + (n : ℝ) * d) ^ 2 / (2 * (n : ℝ)) := by
    have h := unit_interval_exponent_bound d n x hd hnreal hx.1.le hx.2
    have heq : -((n : ℝ) * d) ^ 2 / (2 * (n : ℝ)) =
        -(d ^ 2 / 2) * (n : ℝ) := by field_simp
    simpa only [heq] using h
  have hfactor :
      (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / Real.sqrt (n : ℝ) =
        (Real.sqrt (2 * Real.pi * (n : ℝ)))⁻¹ *
          Real.exp (-(d ^ 2 / 2) * (n : ℝ) - d - 1 / 2) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 * Real.pi by positivity) (n : ℝ)]
    rw [show -(d ^ 2 / 2) * (n : ℝ) - d - 1 / 2 =
      (-d - 1 / 2) + (-(d ^ 2 / 2) * (n : ℝ)) by ring, Real.exp_add]
    ring
  rw [hfactor]
  simp only [gaussianPDFReal, NNReal.coe_natCast]
  rw [show x - (-(n : ℝ) * d) = x + (n : ℝ) * d by ring]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
theorem gaussian_endpoint_lower (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d) :
    (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / Real.sqrt (n : ℝ) ≤
      (gaussianReal (-(n : ℝ) * d) (n : NNReal)).real (Set.Ioi 0) := by
  have hn0 : (n : NNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpdf := integrable_gaussianPDFReal (-(n : ℝ) * d) (n : NNReal)
  have hlow := setIntegral_ge_of_const_le_real
    (μ := volume) measurableSet_Ioc (by simp)
    (pdf_lower_on_unit_interval n hn d hd) hpdf.integrableOn
  have hlow' :
      (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / Real.sqrt (n : ℝ) ≤
        ∫ x in Set.Ioc (0 : ℝ) 1, gaussianPDFReal (-(n : ℝ) * d) (n : NNReal) x := by
    simpa only [Real.volume_real_Ioc, sub_zero, max_eq_left zero_le_one, mul_one] using hlow
  calc
    _ ≤ ∫ x in Set.Ioc (0 : ℝ) 1, gaussianPDFReal (-(n : ℝ) * d) (n : NNReal) x := hlow'
    _ = (gaussianReal (-(n : ℝ) * d) (n : NNReal)).real (Set.Ioc 0 1) := by
      rw [measureReal_def, gaussianReal_apply_eq_integral _ hn0]
      rw [ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]
    _ ≤ _ := measureReal_mono (fun _ hx => hx.1)
end ArgmaxGaussianEndpoint
namespace ArgmaxSurvivalLower
theorem gaussian_survival_lower (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d) :
    (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * (n : ℝ)) /
          ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  have hendpoint := ArgmaxGaussianEndpoint.gaussian_endpoint_lower n hn d hd
  have hlaw := (ArgmaxGaussianEndpointLaw.gaussian_endpoint_hasLaw n d).measureReal_eq
    (p := fun x : ℝ => 0 < x) measurableSet_Ioi
  have hendpoint' :
      (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / Real.sqrt (n : ℝ) ≤
        (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
          {x : Fin n → ℝ | 0 < ∑ i, x i} := by
    rw [hlaw]
    exact hendpoint
  calc
    _ = ((Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / Real.sqrt (n : ℝ)) / (n : ℝ) := by
      rw [div_div, mul_comm (n : ℝ) (Real.sqrt (n : ℝ))]
    _ ≤ _ := (div_le_div_of_nonneg_right hendpoint' (Nat.cast_nonneg n)).trans
      (ArgmaxCyclicSurvival.gaussian_survival_ge_endpoint_div n (by omega) d)
theorem gaussian_survival_profile_lower (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d) :
    (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) ≤
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have heq : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hnpos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hden : (n : ℝ) * Real.sqrt (n : ℝ) ≤ (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) := by
    rw [← heq]
    exact Real.rpow_le_rpow hnpos.le (by linarith) (by norm_num)
  have hdenpos : 0 < (n : ℝ) * Real.sqrt (n : ℝ) :=
    mul_pos hnpos (Real.sqrt_pos.mpr hnpos)
  exact (div_le_div_of_nonneg_left (by positivity) hdenpos hden).trans
    (gaussian_survival_lower n hn d hd)
theorem brownian_survival_profile_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d) :
    (Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) ≤
      P.real {ω | ∀ k : Fin n,
        0 < B ((k.val + 1 : ℕ) : NNReal) ω - d * (k.val + 1 : ℕ)} := by
  have heq := (ArgmaxBrownianTilt.positive_brownian_values_survival hB n d).trans
    (ArgmaxGaussianTilt.positive_prefixes_negative_shift n d).symm
  rw [heq]
  exact gaussian_survival_profile_lower n hn d hd
end ArgmaxSurvivalLower
namespace ArgmaxDiscreteLeftTail
theorem exists_uniform_negative_atom_lower (d : ℝ) (hd : 0 < d) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsPreBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ D : Ω → ℤ,
          (∀ᵐ ω ∂P, ∀ z : ℤ,
            B (z : ℝ) ω - d * |(z : ℝ)| ≤
              B (D ω : ℝ) ω - d * |(D ω : ℝ)|) →
          ∀ n : ℕ, 0 < n →
            r ^ 2 * (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
              {x : Fin n → ℝ | ∀ k : Fin n,
                0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} ≤
              P.real {ω | D ω = -(n : ℤ)} := by
  obtain ⟨r, hr, hatom⟩ := ArgmaxAtomLower.exists_uniform_positive_atom_lower d hd
  refine ⟨r, hr, ?_⟩
  intro Ω _ P _ B hplus hminus hInd D hmax n hn
  have hmax' : ∀ᵐ ω ∂P, ∀ z : ℤ,
      B (-(z : ℝ)) ω - d * |(z : ℝ)| ≤
        B (-((-D ω : ℤ) : ℝ)) ω - d * |((-D ω : ℤ) : ℝ)| := by
    filter_upwards [hmax] with ω hω
    intro z
    simpa only [Int.cast_neg, neg_neg, abs_neg] using hω (-z)
  have h := hatom Ω P (fun t ω => B (-t) ω) hminus
    (by simpa only [neg_neg] using hplus)
    (by simpa only [neg_neg] using hInd.symm) (fun ω => -D ω) hmax' n hn
  simpa only [neg_eq_iff_eq_neg] using h
lemma ceil_survival_profile_comparison (a x : ℝ) (ha : 0 ≤ a) (hx : 1 ≤ x) :
    Real.exp (-a) * Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2) ≤
      Real.exp (-a * (Nat.ceil x : ℝ)) /
        ((Nat.ceil x : ℝ) * Real.sqrt (Nat.ceil x : ℝ)) := by
  have hx0 : 0 ≤ x := by linarith
  have hn : (0 : ℝ) < Nat.ceil x := Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by linarith))
  have hnle : (Nat.ceil x : ℝ) ≤ 1 + x := by
    have h := (Nat.ceil_lt_add_one hx0).le
    linarith
  have hnum : Real.exp (-a) * Real.exp (-a * x) ≤ Real.exp (-a * (Nat.ceil x : ℝ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hpow : (Nat.ceil x : ℝ) ^ ((3 : ℝ) / 2) =
      (Nat.ceil x : ℝ) * Real.sqrt (Nat.ceil x : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hn,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hden : (Nat.ceil x : ℝ) * Real.sqrt (Nat.ceil x : ℝ) ≤
      (1 + x) ^ ((3 : ℝ) / 2) := by
    rw [← hpow]
    exact Real.rpow_le_rpow hn.le hnle (by norm_num)
  calc
    _ ≤ Real.exp (-a * (Nat.ceil x : ℝ)) / (1 + x) ^ ((3 : ℝ) / 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
theorem exists_uniform_discrete_left_tail_lower (d : ℝ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsPreBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ D : Ω → ℤ, AEMeasurable D P →
          (∀ᵐ ω ∂P, ∀ z : ℤ,
            B (z : ℝ) ω - d * |(z : ℝ)| ≤
              B (D ω : ℝ) ω - d * |(D ω : ℝ)|) →
          ∀ x : ℝ, 1 ≤ x →
            c * Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) ≤
              1 - P.real {ω | -x < (D ω : ℝ)} := by
  obtain ⟨r, hr, hatom⟩ := exists_uniform_negative_atom_lower d hd
  let a := d ^ 2 / 2
  let c0 := Real.exp (-d - 1 / 2) / Real.sqrt (2 * Real.pi)
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  let c := r ^ 2 * c0 * Real.exp (-a)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro Ω _ P _ B hplus hminus hInd D hD hmax x hx
  let n := Nat.ceil x
  have hn : 1 ≤ n := Nat.one_le_ceil_iff.mpr (by linarith)
  have hsurvival := ArgmaxSurvivalLower.gaussian_survival_lower n hn d hd.le
  change c0 * Real.exp (-a * (n : ℝ)) / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} at hsurvival
  have hatomn := hatom Ω P B hplus hminus hInd D hmax n (by omega)
  have hceil := ceil_survival_profile_comparison a x (by dsimp [a]; positivity) hx
  have hsubset : {ω | D ω = -(n : ℤ)} ⊆ {ω | (D ω : ℝ) ≤ -x} := by
    intro ω hω
    change (D ω : ℝ) ≤ -x
    rw [hω]
    simp only [Int.cast_neg, Int.cast_natCast]
    exact neg_le_neg (Nat.le_ceil x)
  have hmeas : NullMeasurableSet {ω | -x < (D ω : ℝ)} P := by
    have hDr : AEMeasurable (fun ω => (D ω : ℝ)) P := by fun_prop
    exact hDr.nullMeasurableSet_preimage measurableSet_Ioi
  have hcompl : {ω | (D ω : ℝ) ≤ -x} = {ω | -x < (D ω : ℝ)}ᶜ := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  calc
    _ = (r ^ 2 * c0) *
        (Real.exp (-a) * Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
      dsimp [c, a]
      ring
    _ ≤ (r ^ 2 * c0) * (Real.exp (-a * (n : ℝ)) /
        ((n : ℝ) * Real.sqrt (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hceil (mul_nonneg (sq_nonneg r) hc0.le)
    _ = r ^ 2 * (c0 * Real.exp (-a * (n : ℝ)) /
        ((n : ℝ) * Real.sqrt (n : ℝ))) := by ring
    _ ≤ r ^ 2 * (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} :=
      mul_le_mul_of_nonneg_left hsurvival (sq_nonneg r)
    _ ≤ P.real {ω | D ω = -(n : ℤ)} := hatomn
    _ ≤ P.real {ω | (D ω : ℝ) ≤ -x} := measureReal_mono hsubset
    _ = _ := by rw [hcompl, measureReal_compl₀ hmeas, probReal_univ]
end ArgmaxDiscreteLeftTail
namespace ArgmaxAtomUpper
lemma gaussian_hasLaw_ae_ne
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {m : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal m v) P)
    (hv : v ≠ 0) (a : ℝ) : ∀ᵐ ω ∂P, X ω ≠ a := by
  let := nullSingletonClass_gaussianReal (μ := m) hv
  have hzero : P {ω | X ω = a} = 0 := by
    have h := hX.measure_eq (p := fun x => x = a) (measurableSet_singleton a)
    simpa using h
  apply ae_iff.mpr
  simpa only [not_not] using hzero
theorem fixed_past_ties_ae_ne
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ → Ω → ℝ}
    (hB : IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P)
    (d : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ k : Fin n,
      B (k.val : ℝ) ω - d * (k.val : ℝ) ≠ B (n : ℝ) ω - d * (n : ℝ) := by
  apply ae_all_iff.mpr
  intro k
  have hLaw := hB.hasLaw_sub (n : NNReal) (k.val : NNReal)
  have hv : nndist ((n : NNReal).1) ((k.val : NNReal).1) ≠ 0 := by
    change nndist (n : ℝ) (k.val : ℝ) ≠ 0
    rw [ne_eq, nndist_eq_zero]
    exact ne_of_gt (Nat.cast_lt.mpr k.isLt)
  have h := gaussian_hasLaw_ae_ne hLaw hv (d * (n : ℝ) - d * (k.val : ℝ))
  filter_upwards [h] with ω hω
  change B (n : ℝ) ω - B (k.val : ℝ) ω ≠ d * (n : ℝ) - d * (k.val : ℝ) at hω
  intro heq
  apply hω
  linarith
theorem positive_atom_le_survival
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → ℝ)
    (hB : IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P)
    (d : ℝ) (D : Ω → ℤ)
    (hmax : ∀ᵐ ω ∂P, ∀ z : ℤ,
      B (z : ℝ) ω - d * |(z : ℝ)| ≤ B (D ω : ℝ) ω - d * |(D ω : ℝ)|)
    (n : ℕ) :
    P.real {ω | D ω = (n : ℤ)} ≤
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  let E : Set Ω := {ω | ∀ k : Fin n,
    B (k.val : ℝ) ω - d * (k.val : ℝ) < B (n : ℝ) ω - d * (n : ℝ)}
  have hAE : ∀ᵐ ω ∂P, D ω = (n : ℤ) → ω ∈ E := by
    filter_upwards [hmax, fixed_past_ties_ae_ne hB d n] with ω hω htie
    intro hDn k
    have hle := hω (k.val : ℤ)
    have hle' : B (k.val : ℝ) ω - d * (k.val : ℝ) ≤
        B (n : ℝ) ω - d * (n : ℝ) := by
      simpa [hDn] using hle
    exact lt_of_le_of_ne hle' (htie k)
  have hprob : P.real {ω | D ω = (n : ℤ)} ≤ P.real E := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hAE)
  have hrecord := ArgmaxPastRecord.past_record_probability hB d n
  have hrecord' : P.real E =
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
    simpa only [NNReal.coe_natCast] using hrecord
  exact hprob.trans_eq hrecord'
end ArgmaxAtomUpper
namespace ArgmaxAtomUpper
lemma gaussian_endpoint_hasLaw (n : ℕ) (d : ℝ) :
    HasLaw (fun x : Fin n → ℝ => ∑ i, x i)
      (gaussianReal (-(n : ℝ) * d) (n : NNReal))
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply, charFun_gaussianReal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma gaussian_upper_tail (n : ℕ) (d K : ℝ) (hd : 0 ≤ d) :
    (gaussianReal (-(n : ℝ) * d) (n : NNReal)).real (Set.Ioi K) ≤
      Real.exp (-d * K) * Real.exp (-(d ^ 2 / 2) * (n : ℝ)) := by
  have h := measure_ge_le_exp_mul_mgf
    (μ := gaussianReal (-(n : ℝ) * d) (n : NNReal)) (X := id) K hd
    (integrable_exp_mul_gaussianReal d)
  rw [mgf_id_gaussianReal] at h
  simp only [NNReal.coe_natCast] at h
  have heq : (-(n : ℝ) * d) * d + (n : ℝ) * d ^ 2 / 2 =
      -(d ^ 2 / 2) * (n : ℝ) := by ring
  rw [heq] at h
  exact (measureReal_mono (fun x hx => (show K < x from hx).le)).trans h
theorem canonical_survival_crude_upper (n : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} ≤
      Real.exp (-(d ^ 2 / 2) * (n : ℝ)) := by
  cases n with
  | zero =>
    have hevent : {x : Fin 0 → ℝ | ∀ k : Fin 0,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} = Set.univ := by
      ext x
      simp
    rw [hevent]
    simp
  | succ n =>
    have hsub : {x : Fin (n + 1) → ℝ | ∀ k : Fin (n + 1),
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} ⊆
        {x : Fin (n + 1) → ℝ | 0 < ∑ i, x i} := by
      intro x hx
      have h := hx (Fin.last n)
      have heq : Finset.univ.filter (fun i : Fin (n + 1) => i ≤ Fin.last n) = Finset.univ :=
        Finset.filter_eq_self.mpr (fun i _ => Fin.le_last i)
      rw [heq] at h
      exact h
    calc
      _ ≤ (Measure.pi (fun _ : Fin (n + 1) => gaussianReal (-d) 1)).real
          {x : Fin (n + 1) → ℝ | 0 < ∑ i, x i} := measureReal_mono hsub
      _ = (gaussianReal (-((n + 1 : ℕ) : ℝ) * d) ((n + 1 : ℕ) : NNReal)).real
          (Set.Ioi 0) := (gaussian_endpoint_hasLaw (n + 1) d).measureReal_eq measurableSet_Ioi
      _ ≤ _ := by simpa using gaussian_upper_tail (n + 1) d 0 hd
lemma filtered_survival_summable (d : ℝ) (hd : 0 < d) (x : ℝ) :
    Summable (fun n : ℕ => if x < (n : ℝ) then
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {y : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} else 0) := by
  have hnorm : ‖Real.exp (-(d ^ 2 / 2))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  refine (summable_geometric_of_norm_lt_one hnorm).of_nonneg_of_le ?_ ?_
  · intro n
    split_ifs
    · exact measureReal_nonneg
    · exact le_rfl
  · intro n
    split_ifs
    · have h := canonical_survival_crude_upper n d hd.le
      rw [show Real.exp (-(d ^ 2 / 2) * (n : ℝ)) = Real.exp (-(d ^ 2 / 2)) ^ n by
        rw [mul_comm, Real.exp_nat_mul]] at h
      exact h
    · exact (pow_pos (Real.exp_pos _) _).le
lemma positive_right_tail_eq_iUnion
    {Ω : Type*} (D : Ω → ℤ) (x : ℝ) (hx : 0 ≤ x) :
    {ω | x < (D ω : ℝ)} =
      ⋃ n : ℕ, if x < (n : ℝ) then {ω | D ω = (n : ℤ)} else ∅ := by
  ext ω
  constructor
  · intro hω
    have hD : 0 ≤ D ω := by exact_mod_cast (hx.trans hω.le)
    let n := (D ω).toNat
    have hn : (n : ℤ) = D ω := Int.toNat_of_nonneg hD
    have hxn : x < (n : ℝ) := by
      have hω' : x < (D ω : ℝ) := hω
      rw [← hn] at hω'
      simpa only [Int.cast_natCast] using hω'
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [if_pos hxn]
    exact hn.symm
  · intro hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
    by_cases hxn : x < (n : ℝ)
    · rw [if_pos hxn] at hn
      change D ω = (n : ℤ) at hn
      change x < (D ω : ℝ)
      rw [hn]
      simpa only [Int.cast_natCast] using hxn
    · simp only [if_neg hxn, Set.mem_empty_iff_false] at hn
theorem positive_right_tail_le_survival_tsum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → ℝ)
    (hB : IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P)
    (d : ℝ) (hd : 0 < d) (D : Ω → ℤ)
    (hmax : ∀ᵐ ω ∂P, ∀ z : ℤ,
      B (z : ℝ) ω - d * |(z : ℝ)| ≤ B (D ω : ℝ) ω - d * |(D ω : ℝ)|)
    (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | x < (D ω : ℝ)} ≤
      ∑' n : ℕ, if x < (n : ℝ) then
        (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
          {y : Fin n → ℝ | ∀ k : Fin n,
            0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} else 0 := by
  let p : ℕ → ℝ := fun n => if x < (n : ℝ) then
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {y : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} else 0
  have hp : ∀ n, 0 ≤ p n := by
    intro n
    dsimp [p]
    split_ifs
    · exact measureReal_nonneg
    · exact le_rfl
  have hsum : Summable p := filtered_survival_summable d hd x
  have hbound : P {ω | x < (D ω : ℝ)} ≤ ENNReal.ofReal (∑' n, p n) := by
    rw [positive_right_tail_eq_iUnion D x hx]
    calc
      _ ≤ ∑' n : ℕ, P (if x < (n : ℝ) then {ω | D ω = (n : ℤ)} else ∅) :=
        measure_iUnion_le _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (p n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        dsimp [p]
        by_cases hxn : x < (n : ℝ)
        · rw [if_pos hxn, if_pos hxn]
          have h := positive_atom_le_survival P B hB d D hmax n
          simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
            ENNReal.ofReal_le_ofReal h
        · simp only [if_neg hxn, measure_empty, ENNReal.ofReal_zero, le_refl]
      _ = ENNReal.ofReal (∑' n, p n) := (ENNReal.ofReal_tsum_of_nonneg hp hsum).symm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (tsum_nonneg hp)] at hreal
  simpa only [p, measureReal_def] using hreal
end ArgmaxAtomUpper
namespace ArgmaxSurvivalToRightTail
lemma profile_tail_constant_pos (d C : ℝ) (hd : 0 < d) (hC : 0 < C) :
    0 < C / (1 - Real.exp (-(d ^ 2 / 2))) := by
  apply div_pos hC
  have hq : Real.exp (-(d ^ 2 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith
theorem survival_tsum_profile_upper (d : ℝ) (hd : 0 < d) (C : ℝ) (hC : 0 < C)
    (hprofile : ∀ n : ℕ, 1 ≤ n →
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {y : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} ≤
        C * Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2))
    (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℕ, if x < (n : ℝ) then
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {y : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} else 0) ≤
      (C / (1 - Real.exp (-(d ^ 2 / 2)))) *
        Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) := by
  let a := d ^ 2 / 2
  let q := Real.exp (-a)
  let u : ℕ → ℝ := fun n => if x < (n : ℝ) then
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {y : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} else 0
  let N := Nat.floor x + 1
  let K := C * Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)
  have hx0 : 0 ≤ x := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : ‖q‖ < 1 := by
    dsimp [q]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hsum : Summable u := ArgmaxAtomUpper.filtered_survival_summable d hd x
  have hxN : x < (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hlow : ∑ i ∈ Finset.range N, u i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ Nat.floor x := by
      have h := Finset.mem_range.mp hi
      dsimp [N] at h
      omega
    have hix : (i : ℝ) ≤ x := (Nat.cast_le.mpr hi').trans (Nat.floor_le hx0)
    simp only [u, if_neg (not_lt_of_ge hix)]
  have hshift : (∑' n, u n) = ∑' m : ℕ, u (m + N) := by
    have h := hsum.sum_add_tsum_nat_add N
    rw [hlow, zero_add] at h
    exact h.symm
  have hbound (m : ℕ) : u (m + N) ≤ K * q ^ m := by
    have hmN : 1 ≤ m + N := by dsimp [N]; omega
    have hxm : x < ((m + N : ℕ) : ℝ) :=
      hxN.trans_le (Nat.cast_le.mpr (Nat.le_add_left N m))
    have hden : (1 + x) ^ ((3 : ℝ) / 2) ≤
        (1 + ((m + N : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have hexp : Real.exp (-a * ((m + N : ℕ) : ℝ)) ≤ Real.exp (-a * x) * q ^ m := by
      rw [show q ^ m = Real.exp ((m : ℝ) * (-a)) by
        dsimp [q]; rw [Real.exp_nat_mul], ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    calc
      _ = (Measure.pi (fun _ : Fin (m + N) => gaussianReal (-d) 1)).real
          {y : Fin (m + N) → ℝ | ∀ k : Fin (m + N),
            0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} := by simp only [u, if_pos hxm]
      _ ≤ C * Real.exp (-a * ((m + N : ℕ) : ℝ)) /
          (1 + ((m + N : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) := hprofile (m + N) hmN
      _ ≤ C * Real.exp (-a * ((m + N : ℕ) : ℝ)) / (1 + x) ^ ((3 : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ C * (Real.exp (-a * x) * q ^ m) / (1 + x) ^ ((3 : ℝ) / 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC.le) (by positivity)
      _ = K * q ^ m := by dsimp [K]; ring
  have hsumshift : Summable (fun m : ℕ => u (m + N)) := (summable_nat_add_iff N).mpr hsum
  have hsumgeo : Summable (fun m : ℕ => K * q ^ m) :=
    (summable_geometric_of_norm_lt_one hq).mul_left K
  calc
    _ = ∑' m : ℕ, u (m + N) := hshift
    _ ≤ ∑' m : ℕ, K * q ^ m := hsumshift.tsum_le_tsum hbound hsumgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]
      dsimp [K, q, a]
      simp only [div_eq_mul_inv]
      ring
theorem positive_right_tail_le_profile
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → ℝ)
    (hB : IsPreBrownianReal (fun t : NNReal => B (t : ℝ)) P)
    (d : ℝ) (hd : 0 < d) (C : ℝ) (hC : 0 < C)
    (hprofile : ∀ n : ℕ, 1 ≤ n →
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {y : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} ≤
        C * Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2))
    (D : Ω → ℤ)
    (hmax : ∀ᵐ ω ∂P, ∀ z : ℤ,
      B (z : ℝ) ω - d * |(z : ℝ)| ≤ B (D ω : ℝ) ω - d * |(D ω : ℝ)|)
    (x : ℝ) (hx : 1 ≤ x) :
    P.real {ω | x < (D ω : ℝ)} ≤
      (C / (1 - Real.exp (-(d ^ 2 / 2)))) *
        Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) :=
  (ArgmaxAtomUpper.positive_right_tail_le_survival_tsum P B hB d hd D hmax x (by linarith)).trans
    (survival_tsum_profile_upper d hd C hC hprofile x hx)
end ArgmaxSurvivalToRightTail
open scoped BigOperators Polynomial
open Polynomial
namespace ArgmaxCoefficientAssembly
theorem triangular_recurrence_unique_up_to
    (b u v : ℕ → ℝ) (N : ℕ) (hzero : u 0 = v 0)
    (hu : ∀ n : ℕ, n < N →
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * b (p.1 + 1) * u p.2)
    (hv : ∀ n : ℕ, n < N →
      ((n : ℝ) + 1) * v (n + 1) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * b (p.1 + 1) * v p.2) :
    ∀ n : ℕ, n ≤ N → u n = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact hzero
    | succ m =>
      have hm : m < N := by omega
      have hsum :
          (∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, ((p.1 : ℝ) + 1) * b (p.1 + 1) * u p.2) =
            ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, ((p.1 : ℝ) + 1) * b (p.1 + 1) * v p.2 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [ih p.2 (by omega) (by omega)]
      have h := (hu m hm).trans (hsum.trans (hv m hm).symm)
      exact mul_left_cancel₀ (by positivity : (m : ℝ) + 1 ≠ 0) h
lemma derivative_scaled_power (P : ℝ[X]) (m : ℕ) :
    derivative (C (1 / ((m + 1).factorial : ℝ)) * P ^ (m + 1)) =
      derivative P * (C (1 / (m.factorial : ℝ)) * P ^ m) := by
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow_succ]
  have hfac : (1 / ((m + 1).factorial : ℝ)) * ((m : ℝ) + 1) =
      1 / (m.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  calc
    _ = (C (1 / ((m + 1).factorial : ℝ)) * C ((m : ℝ) + 1)) *
        (derivative P * P ^ m) := by ring
    _ = C (1 / (m.factorial : ℝ)) * (derivative P * P ^ m) := by rw [← C_mul, hfac]
    _ = _ := by ring
theorem derivative_truncated_exponential (P : ℝ[X]) (N : ℕ) :
    derivative (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m) =
      derivative P * (∑ m ∈ Finset.range N, C (1 / (m.factorial : ℝ)) * P ^ m) := by
  rw [derivative_sum, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, C_1, pow_zero, mul_one,
    derivative_one, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact derivative_scaled_power P m
lemma truncated_exponential_derivative_coeff (P : ℝ[X]) (hP : P.coeff 0 = 0)
    (N n : ℕ) (hn : n < N) :
    (derivative (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m)).coeff n =
      (derivative P * (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m)).coeff n := by
  have hdiv : (X : ℝ[X]) ^ N ∣ P ^ N :=
    pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr hP) N
  have hvanish : (P ^ N * derivative P).coeff n = 0 :=
    Polynomial.X_pow_dvd_iff.mp (dvd_mul_of_dvd_left hdiv (derivative P)) n hn
  have htail : (derivative P * (C (1 / (N.factorial : ℝ)) * P ^ N)).coeff n = 0 := by
    rw [show derivative P * (C (1 / (N.factorial : ℝ)) * P ^ N) =
      C (1 / (N.factorial : ℝ)) * (P ^ N * derivative P) by ring,
      coeff_C_mul, hvanish, mul_zero]
  rw [derivative_truncated_exponential]
  conv_rhs => rw [Finset.sum_range_succ]
  rw [mul_add, coeff_add, htail, add_zero]
lemma truncated_exponential_constant_coeff (P : ℝ[X]) (hP : P.coeff 0 = 0) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m).coeff 0 = 1 := by
  have hpow0 (m : ℕ) : (P ^ m).coeff 0 = (P.coeff 0) ^ m := by
    induction m with
    | zero => simp
    | succ m ih => simp only [pow_succ, mul_coeff_zero, ih]
  rw [finsetSum_coeff, Finset.sum_range_succ']
  simp [hpow0, hP]
theorem truncated_exponential_coefficient_recurrence
    (P : ℝ[X]) (hP : P.coeff 0 = 0) (N n : ℕ) (hn : n < N) :
    let E := ∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m
    ((n : ℝ) + 1) * E.coeff (n + 1) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * P.coeff (p.1 + 1) * E.coeff p.2 := by
  dsimp only
  let E := ∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m
  change ((n : ℝ) + 1) * E.coeff (n + 1) =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * P.coeff (p.1 + 1) * E.coeff p.2
  calc
    _ = (derivative E).coeff n := by rw [coeff_derivative]; ring
    _ = (derivative P * E).coeff n := truncated_exponential_derivative_coeff P hP N n hn
    _ = _ := by
      rw [coeff_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [coeff_derivative]
      ring
theorem recurrence_eq_truncated_exponential_coeff
    (P : ℝ[X]) (hP : P.coeff 0 = 0) (u : ℕ → ℝ) (N : ℕ) (hu0 : u 0 = 1)
    (hrec : ∀ n : ℕ, n < N →
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * P.coeff (p.1 + 1) * u p.2) :
    ∀ n : ℕ, n ≤ N →
      u n = (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m).coeff n := by
  apply triangular_recurrence_unique_up_to P.coeff u
    (fun n => (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m).coeff n) N
  · exact hu0.trans (truncated_exponential_constant_coeff P hP N).symm
  · exact hrec
  · intro n hn
    exact truncated_exponential_coefficient_recurrence P hP N n hn
theorem recurrence_eq_finite_power_coefficient_sum
    (P : ℝ[X]) (hP : P.coeff 0 = 0) (u : ℕ → ℝ) (N : ℕ) (hu0 : u 0 = 1)
    (hrec : ∀ n : ℕ, n < N →
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * P.coeff (p.1 + 1) * u p.2) :
    ∀ n : ℕ, n ≤ N → u n =
      ∑ m ∈ Finset.range (N + 1), (P ^ m).coeff n / (m.factorial : ℝ) := by
  intro n hn
  have h := recurrence_eq_truncated_exponential_coeff P hP u N hu0 hrec n hn
  calc
    _ = (∑ m ∈ Finset.range (N + 1), C (1 / (m.factorial : ℝ)) * P ^ m).coeff n := h
    _ = _ := by
      rw [finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro m _
      rw [coeff_C_mul]
      ring
end ArgmaxCoefficientAssembly
open scoped BigOperators
open Polynomial
namespace ArgmaxPolynomialMass
lemma coeff_mul_nonneg (P Q : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k) (hQ : ∀ k, 0 ≤ Q.coeff k) (n : ℕ) :
    0 ≤ (P * Q).coeff n := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hP k.1) (hQ k.2))
theorem coeff_pow_nonneg (P : Polynomial ℝ) (hP : ∀ k, 0 ≤ P.coeff k)
    (m n : ℕ) : 0 ≤ (P ^ m).coeff n := by
  induction m generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [hn, Polynomial.coeff_one]
  | succ m ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg (P ^ m) P (fun k => ih k) hP n
lemma eval_one_eq_sum_coeff (P : Polynomial ℝ) :
    P.eval 1 = ∑ k ∈ P.support, P.coeff k := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, one_pow, mul_one]
theorem sum_coeff_le_eval_one (P : Polynomial ℝ) (hP : ∀ k, 0 ≤ P.coeff k)
    (s : Finset ℕ) : (∑ k ∈ s, P.coeff k) ≤ P.eval 1 := by
  classical
  rw [eval_one_eq_sum_coeff]
  calc
    _ ≤ ∑ k ∈ s ∪ P.support, P.coeff k :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun k _ _ => hP k)
    _ = ∑ k ∈ P.support, P.coeff k := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro k _ hk
      exact Polynomial.notMem_support_iff.mp hk
theorem sum_pow_coeff_le_eval_pow (P : Polynomial ℝ) (hP : ∀ k, 0 ≤ P.coeff k)
    (m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (P ^ m).coeff k) ≤ (P.eval 1) ^ m := by
  have h := sum_coeff_le_eval_one (P ^ m) (fun k => coeff_pow_nonneg P hP m k)
    (Finset.range (n + 1))
  simpa only [Polynomial.eval_pow] using h
theorem coefficients_summable (P : Polynomial ℝ) : Summable (fun k : ℕ => P.coeff k) := by
  exact summable_of_hasFiniteSupport P.toFinsupp.coeff.hasFiniteSupport
lemma pow_coeff_mul_antidiagonal (P : Polynomial ℝ) (m n : ℕ) :
    (P ^ (m + 1)).coeff n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, P.coeff ij.1 * (P ^ m).coeff ij.2 := by
  rw [pow_succ', Polynomial.coeff_mul]
theorem truncated_coefficient (b : ℕ → ℝ) (N k : ℕ) :
    (∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)).coeff k =
      if k ≤ N then b k else 0 := by
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
lemma truncated_coeff_nonneg (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) (N k : ℕ) :
    0 ≤ (∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)).coeff k := by
  rw [truncated_coefficient]
  split_ifs
  · exact hb k
  · exact le_rfl
lemma truncated_eval_one (b : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)).eval 1 =
      ∑ i ∈ Finset.range (N + 1), b i := by
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one]
theorem truncated_eval_one_le_tsum (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hs : Summable b) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)).eval 1 ≤ ∑' i, b i := by
  rw [truncated_eval_one]
  exact hs.sum_le_tsum _ (fun i _ => hb i)
lemma eval_one_nonneg (P : Polynomial ℝ) (hP : ∀ k, 0 ≤ P.coeff k) :
    0 ≤ P.eval 1 := by
  rw [eval_one_eq_sum_coeff]
  exact Finset.sum_nonneg (fun k _ => hP k)
theorem truncated_pow_coeff_mass_le (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hs : Summable b) (N m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      ((∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)) ^ m).coeff k) ≤
      (∑' i, b i) ^ m := by
  let P : Polynomial ℝ := ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)
  have hP : ∀ k, 0 ≤ P.coeff k := truncated_coeff_nonneg b hb N
  have hmass : P.eval 1 ≤ ∑' i, b i := truncated_eval_one_le_tsum b hb hs N
  exact (sum_pow_coeff_le_eval_pow P hP m n).trans
    (pow_le_pow_left₀ (eval_one_nonneg P hP) hmass m)
end ArgmaxPolynomialMass
open scoped BigOperators
namespace ArgmaxConvolution
lemma antidiagonal_sum_fst (f : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1) = ∑ i ∈ Finset.range (n + 1), f i := by
  simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p : ℕ × ℕ => f p.1) n
lemma antidiagonal_sum_snd (f : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.2) = ∑ i ∈ Finset.range (n + 1), f i := by
  calc
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 :=
      Finset.Nat.sum_antidiagonal_swap (f := fun p : ℕ × ℕ => f p.1)
    _ = _ := antidiagonal_sum_fst f n
lemma convolution_le_of_profile_split
    (f g w : ℕ → ℝ) (n : ℕ) (K Bf Bg : ℝ)
    (hK : 0 ≤ K) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hwn : 0 ≤ w n)
    (hf0 : ∀ i, i ≤ n → 0 ≤ f i) (hg0 : ∀ j, j ≤ n → 0 ≤ g j)
    (hf : ∀ i, i ≤ n → f i ≤ Bf * w i)
    (hg : ∀ j, j ≤ n → g j ≤ Bg * w j)
    (hprofile : ∀ i j : ℕ, i + j = n → w i ≤ K * w n ∨ w j ≤ K * w n) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2) ≤
      K * w n * (Bf * (∑ j ∈ Finset.range (n + 1), g j) +
        Bg * (∑ i ∈ Finset.range (n + 1), f i)) := by
  have hKwn : 0 ≤ K * w n := mul_nonneg hK hwn
  calc
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, K * w n * (Bf * g p.2 + Bg * f p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hi : p.1 ≤ n := by omega
      have hj : p.2 ≤ n := by omega
      rcases hprofile p.1 p.2 hsum with hwi | hwj
      · calc
          _ ≤ (Bf * (K * w n)) * g p.2 :=
            mul_le_mul_of_nonneg_right ((hf p.1 hi).trans
              (mul_le_mul_of_nonneg_left hwi hBf)) (hg0 p.2 hj)
          _ = K * w n * (Bf * g p.2) := by ring
          _ ≤ K * w n * (Bf * g p.2 + Bg * f p.1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hBg (hf0 p.1 hi))) hKwn
      · calc
          _ ≤ f p.1 * (Bg * (K * w n)) :=
            mul_le_mul_of_nonneg_left ((hg p.2 hj).trans
              (mul_le_mul_of_nonneg_left hwj hBg)) (hf0 p.1 hi)
          _ = K * w n * (Bg * f p.1) := by ring
          _ ≤ K * w n * (Bf * g p.2 + Bg * f p.1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hBf (hg0 p.2 hj))) hKwn
    _ = K * w n * (Bf * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, g p.2) +
        Bg * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1)) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [antidiagonal_sum_snd, antidiagonal_sum_fst]
lemma polynomial_profile_half_bound (p : ℝ) (hp : 0 ≤ p) (i n : ℕ) (hni : n ≤ 2 * i) :
    1 / (1 + (i : ℝ)) ^ p ≤ (2 : ℝ) ^ p * (1 / (1 + (n : ℝ)) ^ p) := by
  have hi : 0 < 1 + (i : ℝ) := by have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hn : 0 < 1 + (n : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hbase : 1 + (n : ℝ) ≤ 2 * (1 + (i : ℝ)) := by
    have hc : (n : ℝ) ≤ 2 * (i : ℝ) := by exact_mod_cast hni
    linarith
  have hpow : (1 + (n : ℝ)) ^ p ≤ (2 : ℝ) ^ p * (1 + (i : ℝ)) ^ p := by
    calc
      _ ≤ (2 * (1 + (i : ℝ))) ^ p := Real.rpow_le_rpow hn.le hbase hp
      _ = _ := Real.mul_rpow (by norm_num) hi.le
  rw [mul_one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hi _) (Real.rpow_pos_of_pos hn _)]
  simpa only [one_mul] using hpow
lemma polynomial_profile_split (p : ℝ) (hp : 0 ≤ p) (n i j : ℕ) (hij : i + j = n) :
    (1 / (1 + (i : ℝ)) ^ p ≤ (2 : ℝ) ^ p * (1 / (1 + (n : ℝ)) ^ p)) ∨
      (1 / (1 + (j : ℝ)) ^ p ≤ (2 : ℝ) ^ p * (1 / (1 + (n : ℝ)) ^ p)) := by
  by_cases hi : n ≤ 2 * i
  · exact Or.inl (polynomial_profile_half_bound p hp i n hi)
  · exact Or.inr (polynomial_profile_half_bound p hp j n (by omega))
lemma scalar_envelope_induction (c : ℕ → ℝ) (K B S : ℝ)
    (hK : 1 ≤ K) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hc1 : c 1 ≤ B)
    (hcstep : ∀ m : ℕ, 1 ≤ m → c (m + 1) ≤ K * (c m * S + B * S ^ m)) :
    ∀ m : ℕ, c (m + 1) ≤ ((m : ℝ) + 1) * K ^ m * B * S ^ m := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  intro m
  induction m with
  | zero => simpa using hc1
  | succ m ih =>
      calc
        _ ≤ K * (c (m + 1) * S + B * S ^ (m + 1)) := hcstep (m + 1) (by omega)
        _ ≤ K * ((((m : ℝ) + 1) * K ^ m * B * S ^ m) * S + B * S ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left
            (by linarith [mul_le_mul_of_nonneg_right ih hS]) hK0
        _ = (((m : ℝ) + 1) * K ^ (m + 1) + K) * B * S ^ (m + 1) := by
          simp only [pow_succ]
          ring
        _ ≤ ((((m : ℝ) + 1) + 1) * K ^ (m + 1)) * B * S ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hS _)
          apply mul_le_mul_of_nonneg_right _ hB
          have hkpow : K ≤ K ^ (m + 1) := le_self_pow₀ hK (Nat.succ_ne_zero m)
          nlinarith
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]
lemma scalar_envelope_factorial_sum_le_exp (c : ℕ → ℝ) (K B S : ℝ)
    (hK : 1 ≤ K) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hc1 : c 1 ≤ B)
    (hcstep : ∀ m : ℕ, 1 ≤ m → c (m + 1) ≤ K * (c m * S + B * S ^ m))
    (N : ℕ) :
    (∑ m ∈ Finset.range N, c (m + 1) / ((m + 1).factorial : ℝ)) ≤
      B * Real.exp (K * S) := by
  have hc := scalar_envelope_induction c K B S hK hB hS hc1 hcstep
  calc
    _ ≤ ∑ m ∈ Finset.range N, B * ((K * S) ^ m / (m.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro m _
      calc
        _ ≤ (((m : ℝ) + 1) * K ^ m * B * S ^ m) / ((m + 1).factorial : ℝ) :=
          div_le_div_of_nonneg_right (hc m) (Nat.cast_nonneg _)
        _ = B * ((K * S) ^ m / (m.factorial : ℝ)) := by
          have hm : (m : ℝ) + 1 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
          rw [show ((m : ℝ) + 1) * K ^ m * B * S ^ m =
            ((m : ℝ) + 1) * (B * (K * S) ^ m) by rw [mul_pow]; ring]
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            mul_div_mul_left _ _ hm, mul_div_assoc]
    _ = B * (∑ m ∈ Finset.range N, (K * S) ^ m / (m.factorial : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ B * Real.exp (K * S) :=
      mul_le_mul_of_nonneg_left
        (Real.sum_le_exp_of_nonneg (mul_nonneg (zero_le_one.trans hK) hS) N) hB
end ArgmaxConvolution
namespace ArgmaxPolynomialEnvelope
theorem pow_coeff_profile_bound (P : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (K B S : ℝ) (hK : 1 ≤ K) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hbound : ∀ k, P.coeff k ≤ B * w k) (hmass : P.eval 1 ≤ S)
    (hsplit : ∀ n i j : ℕ, i + j = n → w i ≤ K * w n ∨ w j ≤ K * w n)
    (m n : ℕ) :
    (P ^ (m + 1)).coeff n ≤ (((m : ℝ) + 1) * K ^ m * B * S ^ m) * w n := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  induction m generalizing n with
  | zero => simpa only [zero_add, pow_one, Nat.cast_zero, pow_zero, one_mul, mul_one] using hbound n
  | succ m ih =>
    let E := ((m : ℝ) + 1) * K ^ m * B * S ^ m
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hmassP : (∑ i ∈ Finset.range (n + 1), P.coeff i) ≤ S :=
      (ArgmaxPolynomialMass.sum_coeff_le_eval_one P hP _).trans hmass
    have hmassPow : (∑ i ∈ Finset.range (n + 1), (P ^ (m + 1)).coeff i) ≤ S ^ (m + 1) :=
      (ArgmaxPolynomialMass.sum_pow_coeff_le_eval_pow P hP (m + 1) n).trans
        (pow_le_pow_left₀ (ArgmaxPolynomialMass.eval_one_nonneg P hP) hmass _)
    have hconv := ArgmaxConvolution.convolution_le_of_profile_split
      (fun k => P.coeff k) (fun k => (P ^ (m + 1)).coeff k) w n K B E
      hK0 hB hE (hw n) (fun i _ => hP i)
      (fun j _ => ArgmaxPolynomialMass.coeff_pow_nonneg P hP (m + 1) j)
      (fun i _ => hbound i) (fun j _ => ih j) (hsplit n)
    have hinside : B * (∑ j ∈ Finset.range (n + 1), (P ^ (m + 1)).coeff j) +
        E * (∑ i ∈ Finset.range (n + 1), P.coeff i) ≤
        B * S ^ (m + 1) + E * S :=
      add_le_add (mul_le_mul_of_nonneg_left hmassPow hB)
        (mul_le_mul_of_nonneg_left hmassP hE)
    have hscalar : K * (B * S ^ (m + 1) + E * S) ≤
        ((((m + 1 : ℕ) : ℝ) + 1) * K ^ (m + 1) * B * S ^ (m + 1)) := by
      dsimp [E]
      calc
        _ = (((m : ℝ) + 1) * K ^ (m + 1) + K) * B * S ^ (m + 1) := by
          simp only [pow_succ]
          ring
        _ ≤ ((((m : ℝ) + 1) + 1) * K ^ (m + 1)) * B * S ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hS _)
          apply mul_le_mul_of_nonneg_right _ hB
          have hkpow : K ≤ K ^ (m + 1) := le_self_pow₀ hK (Nat.succ_ne_zero m)
          nlinarith
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, P.coeff ij.1 * (P ^ (m + 1)).coeff ij.2 :=
        ArgmaxPolynomialMass.pow_coeff_mul_antidiagonal P (m + 1) n
      _ ≤ K * w n * (B * (∑ j ∈ Finset.range (n + 1), (P ^ (m + 1)).coeff j) +
          E * (∑ i ∈ Finset.range (n + 1), P.coeff i)) := hconv
      _ ≤ K * w n * (B * S ^ (m + 1) + E * S) :=
        mul_le_mul_of_nonneg_left hinside (mul_nonneg hK0 (hw n))
      _ = w n * (K * (B * S ^ (m + 1) + E * S)) := by ring
      _ ≤ w n * ((((m + 1 : ℕ) : ℝ) + 1) * K ^ (m + 1) * B * S ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hscalar (hw n)
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring
theorem factorial_coeff_sum_bound (P : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (K B S : ℝ) (hK : 1 ≤ K) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hbound : ∀ k, P.coeff k ≤ B * w k) (hmass : P.eval 1 ≤ S)
    (hsplit : ∀ n i j : ℕ, i + j = n → w i ≤ K * w n ∨ w j ≤ K * w n)
    (N n : ℕ) :
    (∑ m ∈ Finset.range N, (P ^ (m + 1)).coeff n / ((m + 1).factorial : ℝ)) ≤
      B * Real.exp (K * S) * w n := by
  calc
    _ ≤ ∑ m ∈ Finset.range N,
        ((((m : ℝ) + 1) * K ^ m * B * S ^ m) * w n) / ((m + 1).factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      exact div_le_div_of_nonneg_right
        (pow_coeff_profile_bound P hP w hw K B S hK hB hS hbound hmass hsplit m n)
        (Nat.cast_nonneg _)
    _ = (B * w n) * (∑ m ∈ Finset.range N, (K * S) ^ m / (m.factorial : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      have hm : (m : ℝ) + 1 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
      rw [show (((m : ℝ) + 1) * K ^ m * B * S ^ m) * w n =
        ((m : ℝ) + 1) * ((B * w n) * (K * S) ^ m) by rw [mul_pow]; ring]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_div_mul_left _ _ hm, mul_div_assoc]
    _ ≤ (B * w n) * Real.exp (K * S) :=
      mul_le_mul_of_nonneg_left
        (Real.sum_le_exp_of_nonneg (mul_nonneg (zero_le_one.trans hK) hS) N)
        (mul_nonneg hB (hw n))
    _ = _ := by ring
theorem polynomial_profile_power_bound (P : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k) (p : ℝ) (hp : 0 ≤ p)
    (B S : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hbound : ∀ k, P.coeff k ≤ B / (1 + (k : ℝ)) ^ p) (hmass : P.eval 1 ≤ S)
    (m n : ℕ) :
    (P ^ (m + 1)).coeff n ≤
      (((m : ℝ) + 1) * ((2 : ℝ) ^ p) ^ m * B * S ^ m) / (1 + (n : ℝ)) ^ p := by
  have hK : 1 ≤ (2 : ℝ) ^ p := Real.one_le_rpow (by norm_num) hp
  have h := pow_coeff_profile_bound P hP (fun k => 1 / (1 + (k : ℝ)) ^ p)
    (fun k => by positivity) ((2 : ℝ) ^ p) B S hK hB hS
    (fun k => by simpa only [mul_one_div] using hbound k) hmass
    (fun n i j hij => ArgmaxConvolution.polynomial_profile_split p hp n i j hij) m n
  simpa only [mul_one_div] using h
theorem polynomial_profile_factorial_sum_bound (P : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k) (p : ℝ) (hp : 0 ≤ p)
    (B S : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hbound : ∀ k, P.coeff k ≤ B / (1 + (k : ℝ)) ^ p) (hmass : P.eval 1 ≤ S)
    (N n : ℕ) :
    (∑ m ∈ Finset.range N, (P ^ (m + 1)).coeff n / ((m + 1).factorial : ℝ)) ≤
      B * Real.exp ((2 : ℝ) ^ p * S) / (1 + (n : ℝ)) ^ p := by
  have hK : 1 ≤ (2 : ℝ) ^ p := Real.one_le_rpow (by norm_num) hp
  have h := factorial_coeff_sum_bound P hP (fun k => 1 / (1 + (k : ℝ)) ^ p)
    (fun k => by positivity) ((2 : ℝ) ^ p) B S hK hB hS
    (fun k => by simpa only [mul_one_div] using hbound k) hmass
    (fun n i j hij => ArgmaxConvolution.polynomial_profile_split p hp n i j hij) N n
  simpa only [mul_one_div] using h
end ArgmaxPolynomialEnvelope
namespace ArgmaxRecurrenceToProfile
theorem recurrence_eq_truncated_power_sum (b u : ℕ → ℝ)
    (hb0 : b 0 = 0) (hu0 : u 0 = 1)
    (hrec : ∀ n : ℕ,
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + 1) * b (p.1 + 1) * u p.2)
    (N n : ℕ) (hn : n ≤ N) :
    u n = ∑ m ∈ Finset.range (N + 1),
      ((∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)) ^ m).coeff n /
        (m.factorial : ℝ) := by
  let P : Polynomial ℝ := ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (b i)
  have hP0 : P.coeff 0 = 0 := by
    simpa only [P, ArgmaxPolynomialMass.truncated_coefficient, if_pos (Nat.zero_le N)] using hb0
  have hrecP : ∀ k : ℕ, k < N →
      ((k : ℝ) + 1) * u (k + 1) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ((p.1 : ℝ) + 1) * P.coeff (p.1 + 1) * u p.2 := by
    intro k hk
    rw [hrec k]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hpN : p.1 + 1 ≤ N := by omega
    have hcoeff : P.coeff (p.1 + 1) = b (p.1 + 1) := by
      simp only [P, ArgmaxPolynomialMass.truncated_coefficient, if_pos hpN]
    rw [hcoeff]
  exact ArgmaxCoefficientAssembly.recurrence_eq_finite_power_coefficient_sum P hP0 u N hu0 hrecP n hn
theorem recurrence_polynomial_profile_upper
    (b u : ℕ → ℝ) (hb0 : b 0 = 0) (hb : ∀ k, 0 ≤ b k) (hs : Summable b)
    (p : ℝ) (hp : 0 ≤ p) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ k, b k ≤ B / (1 + (k : ℝ)) ^ p)
    (hu0 : u 0 = 1)
    (hrec : ∀ n : ℕ,
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ((ij.1 : ℝ) + 1) * b (ij.1 + 1) * u ij.2)
    (n : ℕ) (hn : 1 ≤ n) :
    u n ≤ B * Real.exp ((2 : ℝ) ^ p * (∑' k, b k)) / (1 + (n : ℝ)) ^ p := by
  let P : Polynomial ℝ := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (b i)
  have hP : ∀ k, 0 ≤ P.coeff k := ArgmaxPolynomialMass.truncated_coeff_nonneg b hb n
  have hPbound : ∀ k, P.coeff k ≤ B / (1 + (k : ℝ)) ^ p := by
    intro k
    dsimp [P]
    rw [ArgmaxPolynomialMass.truncated_coefficient]
    split_ifs
    · exact hbound k
    · positivity
  have hmass : P.eval 1 ≤ ∑' k, b k :=
    ArgmaxPolynomialMass.truncated_eval_one_le_tsum b hb hs n
  have heq := recurrence_eq_truncated_power_sum b u hb0 hu0 hrec n n le_rfl
  change u n = ∑ m ∈ Finset.range (n + 1), (P ^ m).coeff n / (m.factorial : ℝ) at heq
  have hzero : (P ^ 0).coeff n / (Nat.factorial 0 : ℝ) = 0 := by
    simp [Polynomial.coeff_one, show n ≠ 0 by omega]
  rw [Finset.sum_range_succ', hzero, add_zero] at heq
  rw [heq]
  exact ArgmaxPolynomialEnvelope.polynomial_profile_factorial_sum_bound P hP p hp B
    (∑' k, b k) hB (tsum_nonneg hb) hPbound hmass n n
end ArgmaxRecurrenceToProfile
open MeasureTheory ProbabilityTheory
namespace ArgmaxWeightedEndpoint
lemma weighted_endpoint_integrable (n : ℕ) (d : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-d * y)) (Set.Ioi 0)
      (gaussianReal 0 (n : NNReal)) :=
  (integrable_exp_mul_gaussianReal (-d)).integrableOn
lemma gaussian_zero_pdf_le_cap (n : ℕ) (y : ℝ) :
    gaussianPDFReal 0 (n : NNReal) y ≤
      (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ))⁻¹ := by
  simp only [gaussianPDFReal, NNReal.coe_natCast, sub_zero]
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 * Real.pi by positivity) (n : ℝ)]
  apply mul_le_of_le_one_right (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg y)) (by positivity)
theorem weighted_endpoint_nonneg (n : ℕ) (d : ℝ) :
    0 ≤ ∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal) :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)
theorem weighted_endpoint_upper (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 < d) :
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) ≤
      1 / (d * Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)) := by
  have hn0 : (n : NNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let C := (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ))⁻¹
  have hdom : IntegrableOn (fun y : ℝ => C * Real.exp (-d * y)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0).const_mul C
  have hbound (y : ℝ) : gaussianPDFReal 0 (n : NNReal) y * Real.exp (-d * y) ≤
      C * Real.exp (-d * y) :=
    mul_le_mul_of_nonneg_right (gaussian_zero_pdf_le_cap n y) (Real.exp_pos _).le
  have hint : IntegrableOn
      (fun y : ℝ => gaussianPDFReal 0 (n : NNReal) y * Real.exp (-d * y)) (Set.Ioi 0) := by
    apply hdom.mono_nonneg (by fun_prop)
    · exact Filter.Eventually.of_forall (fun y =>
        mul_nonneg (gaussianPDFReal_nonneg 0 (n : NNReal) y) (Real.exp_pos _).le)
    · exact Filter.Eventually.of_forall hbound
  have heq :
      (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) =
        ∫ y in Set.Ioi (0 : ℝ), gaussianPDFReal 0 (n : NNReal) y * Real.exp (-d * y) := by
    rw [gaussianReal_of_var_ne_zero 0 hn0,
      setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF 0 (n : NNReal))
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top)) _ measurableSet_Ioi]
    simp only [toReal_gaussianPDF, smul_eq_mul]
  calc
    _ = ∫ y in Set.Ioi (0 : ℝ), gaussianPDFReal 0 (n : NNReal) y * Real.exp (-d * y) := heq
    _ ≤ ∫ y in Set.Ioi (0 : ℝ), C * Real.exp (-d * y) :=
      setIntegral_mono_on hint hdom measurableSet_Ioi (fun y _ => hbound y)
    _ = 1 / (d * Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hd) 0]
      simp only [mul_zero, Real.exp_zero, C, div_eq_mul_inv, mul_inv_rev]
      ring
lemma weighted_coefficient_zero (d : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (0 : NNReal)) / (0 : ℝ) = 0 := by
  simp
lemma weighted_coefficient_nonneg (n : ℕ) (d : ℝ) :
    0 ≤ (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) / (n : ℝ) :=
  div_nonneg (weighted_endpoint_nonneg n d) (Nat.cast_nonneg n)
theorem weighted_coefficient_upper (n : ℕ) (d : ℝ) (hd : 0 < d) :
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) / (n : ℝ) ≤
      (1 / (d * Real.sqrt (2 * Real.pi))) * (n : ℝ) ^ (-((3 : ℝ) / 2)) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt (n : ℝ) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add hnpos,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    calc
      _ ≤ (1 / (d * Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ))) / (n : ℝ) :=
        div_le_div_of_nonneg_right (weighted_endpoint_upper n (by omega) d hd) hnpos.le
      _ = _ := by
        rw [Real.rpow_neg hnpos.le, hpow]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
theorem weighted_coefficients_summable (d : ℝ) (hd : 0 < d) :
    Summable (fun n : ℕ =>
      (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) / (n : ℝ)) := by
  have hsum : Summable (fun n : ℕ =>
      (1 / (d * Real.sqrt (2 * Real.pi))) * (n : ℝ) ^ (-((3 : ℝ) / 2))) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  exact hsum.of_nonneg_of_le (fun n => weighted_coefficient_nonneg n d)
    (fun n => weighted_coefficient_upper n d hd)
end ArgmaxWeightedEndpoint
namespace ArgmaxWeightedEndpointProfile
lemma profile_constant_pos (d : ℝ) (hd : 0 < d) :
    0 < (2 : ℝ) ^ ((3 : ℝ) / 2) / (d * Real.sqrt (2 * Real.pi)) := by
  positivity
theorem weighted_coefficient_shifted_profile (n : ℕ) (d : ℝ) (hd : 0 < d) :
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) / (n : ℝ) ≤
      ((2 : ℝ) ^ ((3 : ℝ) / 2) / (d * Real.sqrt (2 * Real.pi))) /
        (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, div_zero, add_zero, Real.one_rpow, div_one]
    exact (profile_constant_pos d hd).le
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
    have hpow : (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) ≤
        (2 : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      calc
        _ ≤ (2 * (n : ℝ)) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ = _ := Real.mul_rpow (by norm_num) hnpos.le
    have hscale : (n : ℝ) ^ (-((3 : ℝ) / 2)) ≤
        (2 : ℝ) ^ ((3 : ℝ) / 2) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) := by
      rw [Real.rpow_neg hnpos.le, ← one_div]
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hnpos _)
        (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + (n : ℝ)) _)).mpr
      simpa only [one_mul] using hpow
    calc
      _ ≤ (1 / (d * Real.sqrt (2 * Real.pi))) * (n : ℝ) ^ (-((3 : ℝ) / 2)) :=
        ArgmaxWeightedEndpoint.weighted_coefficient_upper n d hd
      _ ≤ (1 / (d * Real.sqrt (2 * Real.pi))) *
          ((2 : ℝ) ^ ((3 : ℝ) / 2) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by simp only [div_eq_mul_inv]; ring
end ArgmaxWeightedEndpointProfile
namespace ArgmaxWeightedRecurrence
theorem weighted_gaussian_recurrence_profile (d : ℝ) (hd : 0 < d)
    (u : ℕ → ℝ) (hu0 : u 0 = 1)
    (hrec : ∀ n : ℕ,
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y)
            ∂gaussianReal 0 ((ij.1 + 1 : ℕ) : NNReal)) * u ij.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      u n ≤ C / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) := by
  let b : ℕ → ℝ := fun n =>
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)) / (n : ℝ)
  let B := (2 : ℝ) ^ ((3 : ℝ) / 2) / (d * Real.sqrt (2 * Real.pi))
  let S := ∑' k, b k
  let C := B * Real.exp ((2 : ℝ) ^ ((3 : ℝ) / 2) * S)
  have hB : 0 < B := ArgmaxWeightedEndpointProfile.profile_constant_pos d hd
  have hb0 : b 0 = 0 := by simp [b]
  have hb : ∀ k, 0 ≤ b k := fun k => ArgmaxWeightedEndpoint.weighted_coefficient_nonneg k d
  have hs : Summable b := ArgmaxWeightedEndpoint.weighted_coefficients_summable d hd
  have hbound : ∀ k, b k ≤ B / (1 + (k : ℝ)) ^ ((3 : ℝ) / 2) :=
    fun k => ArgmaxWeightedEndpointProfile.weighted_coefficient_shifted_profile k d hd
  have hcancel (k : ℕ) : ((k : ℝ) + 1) * b (k + 1) =
      (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y)
        ∂gaussianReal 0 ((k + 1 : ℕ) : NNReal)) := by
    simp only [b, Nat.cast_add, Nat.cast_one]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hrecb : ∀ n : ℕ,
      ((n : ℝ) + 1) * u (n + 1) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((ij.1 : ℝ) + 1) * b (ij.1 + 1) * u ij.2 := by
    intro n
    rw [hrec n]
    apply Finset.sum_congr rfl
    intro ij _
    rw [hcancel]
  have hC : 0 < C := mul_pos hB (Real.exp_pos _)
  refine ⟨C, hC, ?_⟩
  intro n hn
  exact ArgmaxRecurrenceToProfile.recurrence_polynomial_profile_upper b u hb0 hb hs
    ((3 : ℝ) / 2) (by norm_num) B hB.le hbound hu0 hrecb n hn
end ArgmaxWeightedRecurrence
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ArgmaxCanonicalSurvivalProfile
theorem canonical_survival_profile_of_weighted_recurrence
    (d : ℝ) (hd : 0 < d)
    (hrec : ∀ n : ℕ,
      ((n : ℝ) + 1) *
        (∫ x in {x : Fin (n + 1) → ℝ | ∀ k : Fin (n + 1),
            0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
          Real.exp (-d * ∑ i, x i)
          ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y)
            ∂gaussianReal 0 ((ij.1 + 1 : ℕ) : NNReal)) *
          (∫ x in {x : Fin ij.2 → ℝ | ∀ k : Fin ij.2,
              0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
            Real.exp (-d * ∑ i, x i)
            ∂Measure.pi (fun _ : Fin ij.2 => gaussianReal 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
        {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} ≤
      C * Real.exp (-(d ^ 2 / 2) * (n : ℝ)) /
        (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) := by
  let u : ℕ → ℝ := fun n =>
    ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
      Real.exp (-d * ∑ i, x i)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  have hu0 : u 0 = 1 := by simp [u]
  obtain ⟨C, hC, hbound⟩ :=
    ArgmaxWeightedRecurrence.weighted_gaussian_recurrence_profile d hd u hu0 hrec
  refine ⟨C, hC, fun n hn => ?_⟩
  rw [ArgmaxGaussianTilt.positive_prefixes_negative_shift]
  have hexp : -(n : ℝ) * d ^ 2 / 2 = -(d ^ 2 / 2) * (n : ℝ) := by ring
  rw [hexp]
  calc
    _ ≤ Real.exp (-(d ^ 2 / 2) * (n : ℝ)) *
        (C / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (hbound n hn) (Real.exp_pos _).le
    _ = _ := by ring
end ArgmaxCanonicalSurvivalProfile
namespace OMA.R_mo_142880_R1
open MeasureTheory ProbabilityTheory
def H1 : Prop :=
  ∀ d : ℝ, 0 < d →
    let u : ℕ → ℝ := fun n =>
      ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)
    let h : ℕ → ℝ := fun n =>
      ∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (n : NNReal)
    ∀ n : ℕ, ((n : ℝ) + 1) * u (n + 1) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2
def H2 : Prop :=
  ∀ d : ℝ, 0 < d →
    let q : ℝ → ℝ := fun x => Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)
    ∃ c C R : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ R ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ T : Ω → ℝ, AEMeasurable T P →
          (∀ᵐ ω ∂P, ∀ t : ℝ,
            OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (T ω) ω) →
          ∀ x : ℝ, R ≤ x →
            c * q x ≤ P.real {ω | x < T ω} ∧
            1 - P.real {ω | -x < T ω} ≤ C * q x
lemma canonical_survival_of_weighted_recurrence : H1 →
∀ d : ℝ, 0 < d → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    (Measure.pi (fun _ : Fin n => gaussianReal (-d) 1)).real
      {y : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), y i} ≤
      C * Real.exp (-(d ^ 2 / 2) * (n : ℝ)) / (1 + (n : ℝ)) ^ ((3 : ℝ) / 2) := by
  intro hrec d hd
  exact ArgmaxCanonicalSurvivalProfile.canonical_survival_profile_of_weighted_recurrence
    d hd (hrec d hd)
lemma discrete_upper_of_canonical : H1 →
∀ d : ℝ, 0 < d →
    let q : ℝ → ℝ := fun x => Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)
    ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ D : Ω → ℤ, AEMeasurable D P →
          (∀ᵐ ω ∂P, ∀ t : ℤ,
            OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (D ω) ω) →
          ∀ x : ℝ, R ≤ x → P.real {ω | x < (D ω : ℝ)} ≤ C * q x := by
  intro hrec
  have hcanonical := canonical_survival_of_weighted_recurrence hrec
  intro d hd
  obtain ⟨C, hC, hprofile⟩ := hcanonical d hd
  refine ⟨C / (1 - Real.exp (-(d ^ 2 / 2))), 1,
    ArgmaxSurvivalToRightTail.profile_tail_constant_pos d C hd hC, by norm_num, ?_⟩
  intro Ω _ P _ B hplus hminus hInd D hD hmax x hx
  have hmax' := hmax
  change (∀ᵐ ω ∂P, ∀ z : ℤ,
    B (z : ℝ) ω - d * |(z : ℝ)| ≤
      B (D ω : ℝ) ω - d * |(D ω : ℝ)|) at hmax'
  have h := ArgmaxSurvivalToRightTail.positive_right_tail_le_profile P B
    hplus.toIsPreBrownianReal d hd C hC hprofile D hmax' x hx
  simpa only [mul_div_assoc] using h
lemma discrete_directional_bounds_of_upper : H1 →
∀ d : ℝ, 0 < d →
    let q : ℝ → ℝ := fun x => Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)
    ∃ c C R : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ R ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ D : Ω → ℤ, AEMeasurable D P →
          (∀ᵐ ω ∂P, ∀ t : ℤ,
            OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (D ω) ω) →
          ∀ x : ℝ, R ≤ x →
            P.real {ω | x < (D ω : ℝ)} ≤ C * q x ∧
            c * q x ≤ 1 - P.real {ω | -x < (D ω : ℝ)} := by
  intro hcanonical
  have hupper := discrete_upper_of_canonical hcanonical
  intro d hd
  obtain ⟨C, R, hC, hR, hu⟩ := hupper d hd
  obtain ⟨c, hc, hl⟩ := ArgmaxDiscreteLeftTail.exists_uniform_discrete_left_tail_lower d hd
  refine ⟨c, C, max R 1, hc, hC, hR.trans (le_max_left _ _), ?_⟩
  intro Ω _ P _ B hplus hminus hInd D hD hmax x hx
  constructor
  · exact hu Ω P B hplus hminus hInd D hD hmax x ((le_max_left _ _).trans hx)
  · have hmax' := hmax
    change (∀ᵐ ω ∂P, ∀ z : ℤ,
      B (z : ℝ) ω - d * |(z : ℝ)| ≤
        B (D ω : ℝ) ω - d * |(D ω : ℝ)|) at hmax'
    have h := hl Ω P B hplus.toIsPreBrownianReal hminus.toIsPreBrownianReal
      hInd D hD hmax' x ((le_max_right _ _).trans hx)
    simpa only [mul_div_assoc] using h
lemma exists_exponential_scale (rate CF cG CG cF : ℝ)
    (hrate : 0 < rate) (hCF : 0 < CF) (hcG : 0 < cG) (hCG : 0 < CG) (hcF : 0 < cF) :
    ∃ s : ℝ, 0 ≤ s ∧ CF * Real.exp (-rate * s) ≤ cG ∧ CG * Real.exp (-rate * s) ≤ cF := by
  let t := min (cG / CF) (cF / CG)
  have ht : 0 < t := lt_min (div_pos hcG hCF) (div_pos hcF hCG)
  let s := max 0 (-Real.log t / rate)
  have hs : 0 ≤ s := le_max_left _ _
  have hsl : -Real.log t / rate ≤ s := le_max_right _ _
  have hmul : -Real.log t ≤ s * rate := (div_le_iff₀ hrate).mp hsl
  have he : Real.exp (-rate * s) ≤ t := by
    calc
      _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr (by nlinarith)
      _ = t := Real.exp_log ht
  refine ⟨s, hs, ?_, ?_⟩
  · have h := (le_div_iff₀ hCF).mp (he.trans (min_le_left _ _))
    simpa only [mul_comm] using h
  · have h := (le_div_iff₀ hCG).mp (he.trans (min_le_right _ _))
    simpa only [mul_comm] using h
lemma survival_comparison_at_shift
    (F G q : ℝ → ℝ) (R rate cF CF cG CG s : ℝ)
    (hFanti : Antitone F) (hGanti : Antitone G)
    (hR : 0 ≤ R) (hrate : 0 < rate)
    (_hcF : 0 < cF) (hCF : 0 < CF) (_hcG : 0 < cG) (hCG : 0 < CG)
    (hq : ∀ x : ℝ, R ≤ x → 0 ≤ q x)
    (hshift : ∀ x t : ℝ, R ≤ x → 0 ≤ t →
      q (x + t) ≤ Real.exp (-rate * t) * q x)
    (hF : ∀ x : ℝ, R ≤ x →
      F x ≤ CF * q x ∧ cF * q x ≤ 1 - F (-x))
    (hG : ∀ x : ℝ, R ≤ x →
      cG * q x ≤ G x ∧ 1 - G (-x) ≤ CG * q x)
    (hs : 0 ≤ s)
    (hCFs : CF * Real.exp (-rate * s) ≤ cG)
    (hCGs : CG * Real.exp (-rate * s) ≤ cF) :
    ∀ x : ℝ, F x ≤ G (x - 2 * (R + s)) := by
  let b := 2 * (R + s)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hbs : s ≤ b := by dsimp [b]; linarith
  have he : Real.exp (-rate * b) ≤ Real.exp (-rate * s) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hCFb : CF * Real.exp (-rate * b) ≤ cG :=
    (mul_le_mul_of_nonneg_left he hCF.le).trans hCFs
  have hCGb : CG * Real.exp (-rate * b) ≤ cF :=
    (mul_le_mul_of_nonneg_left he hCG.le).trans hCGs
  have hRs : R ≤ R + s := by linarith
  have hqR : 0 ≤ q R := hq R le_rfl
  have hsmallG : CG * q (R + s) ≤ cF * q R := by
    calc
      _ ≤ CG * (Real.exp (-rate * s) * q R) :=
        mul_le_mul_of_nonneg_left (hshift R s le_rfl hs) hCG.le
      _ = (CG * Real.exp (-rate * s)) * q R := by ring
      _ ≤ cF * q R := mul_le_mul_of_nonneg_right hCGs hqR
  have hsmallF : CF * q (R + s) ≤ cG * q R := by
    calc
      _ ≤ CF * (Real.exp (-rate * s) * q R) :=
        mul_le_mul_of_nonneg_left (hshift R s le_rfl hs) hCF.le
      _ = (CF * Real.exp (-rate * s)) * q R := by ring
      _ ≤ cG * q R := mul_le_mul_of_nonneg_right hCFs hqR
  have hmiddleLeft : F (-R) ≤ G (-(R + s)) := by
    have hFl := (hF R le_rfl).2
    have hGl := (hG (R + s) hRs).2
    linarith
  have hmiddleRight : F (R + s) ≤ G R :=
    ((hF (R + s) hRs).1.trans hsmallF).trans (hG R le_rfl).1
  intro x
  change F x ≤ G (x - b)
  by_cases hleft : x ≤ -R
  · have hz : R ≤ -x := by linarith
    have hzb : R ≤ -x + b := by linarith
    have hFl : cF * q (-x) ≤ 1 - F x := by
      simpa only [neg_neg] using (hF (-x) hz).2
    have hGl := (hG (-x + b) hzb).2
    have hneg : -(-x + b) = x - b := by ring
    rw [hneg] at hGl
    have hqstep : CG * q (-x + b) ≤ cF * q (-x) := by
      calc
        _ ≤ CG * (Real.exp (-rate * b) * q (-x)) :=
          mul_le_mul_of_nonneg_left (hshift (-x) b hz hb) hCG.le
        _ = (CG * Real.exp (-rate * b)) * q (-x) := by ring
        _ ≤ cF * q (-x) := mul_le_mul_of_nonneg_right hCGb (hq (-x) hz)
    linarith
  · by_cases hright : b + R ≤ x
    · have hz : R ≤ x - b := by linarith
      have hFx := (hF x (by linarith)).1
      have hGy := (hG (x - b) hz).1
      have hqstep : CF * q x ≤ cG * q (x - b) := by
        have hp := hshift (x - b) b hz hb
        rw [sub_add_cancel] at hp
        calc
          _ ≤ CF * (Real.exp (-rate * b) * q (x - b)) :=
            mul_le_mul_of_nonneg_left hp hCF.le
          _ = (CF * Real.exp (-rate * b)) * q (x - b) := by ring
          _ ≤ cG * q (x - b) := mul_le_mul_of_nonneg_right hCFb (hq (x - b) hz)
      exact (hFx.trans hqstep).trans hGy
    · by_cases hmid : x ≤ R + s
      · have hFx : F x ≤ F (-R) := hFanti (by linarith)
        have hGy : G (-(R + s)) ≤ G (x - b) := hGanti (by dsimp [b]; linarith)
        exact (hFx.trans hmiddleLeft).trans hGy
      · have hFx : F x ≤ F (R + s) := hFanti (by linarith)
        have hGy : G R ≤ G (x - b) := hGanti (by linarith)
        exact (hFx.trans hmiddleRight).trans hGy
lemma exists_survival_shift
    (F G q : ℝ → ℝ) (R rate cF CF cG CG : ℝ)
    (hFanti : Antitone F) (hGanti : Antitone G)
    (hR : 0 ≤ R) (hrate : 0 < rate)
    (hcF : 0 < cF) (hCF : 0 < CF) (hcG : 0 < cG) (hCG : 0 < CG)
    (hq : ∀ x : ℝ, R ≤ x → 0 ≤ q x)
    (hshift : ∀ x t : ℝ, R ≤ x → 0 ≤ t →
      q (x + t) ≤ Real.exp (-rate * t) * q x)
    (hF : ∀ x : ℝ, R ≤ x →
      F x ≤ CF * q x ∧ cF * q x ≤ 1 - F (-x))
    (hG : ∀ x : ℝ, R ≤ x →
      cG * q x ≤ G x ∧ 1 - G (-x) ≤ CG * q x) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x : ℝ, F x ≤ G (x - b) := by
  obtain ⟨s, hs, hCFs, hCGs⟩ := exists_exponential_scale rate CF cG CG cF hrate hCF hcG hCG hcF
  refine ⟨2 * (R + s), by linarith, ?_⟩
  exact survival_comparison_at_shift F G q R rate cF CF cG CG s hFanti hGanti hR hrate
    hcF hCF hcG hCG hq hshift hF hG hs hCFs hCGs
lemma q_pos (a x : ℝ) (hx : 0 ≤ x) : 0 < (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
  apply div_pos (Real.exp_pos _)
  exact Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + x) _
lemma q_shift_le (a x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    (Real.exp (-a * (x + s)) / (1 + (x + s)) ^ ((3 : ℝ) / 2)) ≤ Real.exp (-a * s) * (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
  have hden : 0 < (1 + x) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + x) _
  have hmono : (1 + x) ^ ((3 : ℝ) / 2) ≤ (1 + (x + s)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith) (by norm_num)
  calc
    _ = Real.exp (-a * s) *
        (Real.exp (-a * x) / (1 + (x + s)) ^ ((3 : ℝ) / 2)) := by
      rw [show -a * (x + s) = -a * s + -a * x by ring, Real.exp_add, mul_div_assoc]
    _ ≤ Real.exp (-a * s) *
        (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hden hmono
lemma q_shift_le_above (a x R s : ℝ) (hR : 0 ≤ R) (hx : R ≤ x) (hs : 0 ≤ s) :
    (Real.exp (-a * (x + s)) / (1 + (x + s)) ^ ((3 : ℝ) / 2)) ≤ Real.exp (-a * s) * (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) :=
  q_shift_le a x s (hR.trans hx) hs
theorem main : H1 → H2 → type_of% @OMA.S_mo_142880.main := by
  intro hupper h₂
  have h₁ := discrete_directional_bounds_of_upper hupper
  intro d hd
  obtain ⟨cF, CF, RF, hcF, hCF, hRF, hD⟩ := h₁ d hd
  obtain ⟨cG, CG, RG, hcG, hCG, hRG, hT⟩ := h₂ d hd
  let R := max RF RG
  let rate : ℝ := d ^ 2 / 2
  let q : ℝ → ℝ := fun x => Real.exp (-rate * x) / (1 + x) ^ ((3 : ℝ) / 2)
  have hR : 0 ≤ R := hRF.trans (le_max_left _ _)
  have hrate : 0 < rate := by dsimp [rate]; nlinarith [mul_pos hd hd]
  obtain ⟨s, hs, hCFs, hCGs⟩ := exists_exponential_scale rate CF cG CG cF hrate hCF hcG hCG hcF
  let b := 2 * (R + s)
  refine ⟨1, b, by norm_num, ?_⟩
  intro Ω mΩ P hP B hBp hBn hind D T hDmeas hTmeas hDmax hTmax x
  let F : ℝ → ℝ := fun t => P.real {ω | t < (D ω : ℝ)}
  let G : ℝ → ℝ := fun t => P.real {ω | t < T ω}
  have hFanti : Antitone F := by
    intro u v huv
    exact measureReal_mono (by intro ω hω; exact lt_of_le_of_lt huv hω)
  have hGanti : Antitone G := by
    intro u v huv
    exact measureReal_mono (by intro ω hω; exact lt_of_le_of_lt huv hω)
  have hDf := hD Ω P B hBp hBn hind D hDmeas hDmax
  have hTf := hT Ω P B hBp hBn hind T hTmeas hTmax
  have hq : ∀ t : ℝ, R ≤ t → 0 ≤ q t := by
    intro t ht
    exact (q_pos rate t (hR.trans ht)).le
  have hshift : ∀ t u : ℝ, R ≤ t → 0 ≤ u →
      q (t + u) ≤ Real.exp (-rate * u) * q t := by
    intro t u ht hu
    exact q_shift_le rate t u (hR.trans ht) hu
  have hF : ∀ t : ℝ, R ≤ t →
      F t ≤ CF * q t ∧ cF * q t ≤ 1 - F (-t) := by
    intro t ht
    exact hDf t ((le_max_left RF RG).trans ht)
  have hG : ∀ t : ℝ, R ≤ t →
      cG * q t ≤ G t ∧ 1 - G (-t) ≤ CG * q t := by
    intro t ht
    exact hTf t ((le_max_right RF RG).trans ht)
  have hx := survival_comparison_at_shift F G q R rate cF CF cG CG s
    hFanti hGanti hR hrate hcF hCF hcG hCG hq hshift hF hG hs hCFs hCGs x
  have hxReal : P.real {ω | x < (D ω : ℝ)} ≤ P.real {ω | x - b < T ω} := hx
  have hxMeasure : P {ω | x < (D ω : ℝ)} ≤ P {ω | x - b < T ω} := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
    simpa only [measureReal_def] using hxReal
  simpa only [one_mul, sub_lt_iff_lt_add] using hxMeasure
end OMA.R_mo_142880_R1
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace ArgmaxGaussianGenericPosition
theorem weighted_sum_hasLaw {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun x : ι → ℝ => ∑ i, a i * x i)
      (gaussianReal 0 (∑ i, (NNReal.mk ((a i) ^ 2) (sq_nonneg _))))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  classical
  let P := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have hlaw (i : ι) : HasLaw (fun x : ι → ℝ => a i * x i)
      (gaussianReal 0 (NNReal.mk ((a i) ^ 2) (sq_nonneg _))) P := by
    simpa only [P, Function.eval_apply, mul_zero, mul_one] using
      gaussianReal_const_mul (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw (a i)
  have hind : iIndepFun (fun (i : ι) (x : ι → ℝ) => a i * x i) P := by
    exact (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).comp
      (fun i x => a i * x) (by fun_prop)
  refine ⟨?_, ?_⟩
  · simpa only [Finset.sum_apply, P] using
      Finset.aemeasurable_fun_sum Finset.univ (fun i _ => (hlaw i).aemeasurable)
  apply Measure.ext_of_charFun
  ext t
  rw [hind.charFun_map_fun_sum_eq_prod (fun i => (hlaw i).aemeasurable)]
  simp only [Finset.prod_apply]
  simp_rw [(fun i => (hlaw i).map_eq)]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp [Complex.ofReal_zero, NNReal.coe_sum, NNReal.coe_mk,
    Complex.ofReal_sum, Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_mul]
theorem weighted_sum_ae_ne {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∃ i, a i ≠ 0) (b : ℝ) :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => gaussianReal 0 1), (∑ i, a i * x i) ≠ b := by
  classical
  have hv : (∑ i, NNReal.mk ((a i) ^ 2) (sq_nonneg _)) ≠ 0 := by
    rcases ha with ⟨i, hi⟩
    intro hzero
    have hzero' : (∑ j, (a j) ^ 2) = 0 := by
      have h := congrArg (fun y : ℝ≥0 => (y : ℝ)) hzero
      simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_zero] using h
    have hle : (a i) ^ 2 ≤ ∑ j, (a j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
    rw [hzero'] at hle
    exact (not_le_of_gt (sq_pos_of_ne_zero hi)) hle
  let := nullSingletonClass_gaussianReal (μ := 0) hv
  have hzero : (Measure.pi (fun _ : ι => gaussianReal 0 1))
      {x | (∑ i, a i * x i) = b} = 0 := by
    have h := (weighted_sum_hasLaw a).measure_eq (p := fun y => y = b)
      (measurableSet_singleton b)
    simpa using h
  apply ae_iff.mpr
  simpa only [not_not] using hzero
lemma sum_indicator_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (c : ℝ) (x : ι → ℝ) :
    (∑ i, (if i ∈ s then c else 0) * x i) = c * ∑ i ∈ s, x i := by
  classical
  simp [ite_mul, ← Finset.mul_sum]
theorem disjoint_averages_ae_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty) (hd : Disjoint A B) :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => gaussianReal 0 1),
      (∑ i ∈ A, x i) / (A.card : ℝ) ≠ (∑ i ∈ B, x i) / (B.card : ℝ) := by
  classical
  let a : ι → ℝ := fun i =>
    (if i ∈ A then (B.card : ℝ) else 0) - (if i ∈ B then (A.card : ℝ) else 0)
  have hAc : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hBc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have ha : ∃ i, a i ≠ 0 := by
    obtain ⟨i, hi⟩ := hA
    have hinB : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    exact ⟨i, by simpa only [a, if_pos hi, if_neg hinB, sub_zero] using hBc⟩
  filter_upwards [weighted_sum_ae_ne a ha 0] with x hx
  intro heq
  have hcross := (div_eq_div_iff hAc hBc).mp heq
  have hid : (∑ i, a i * x i) =
      (B.card : ℝ) * (∑ i ∈ A, x i) - (A.card : ℝ) * (∑ i ∈ B, x i) := by
    simp only [a, sub_mul, Finset.sum_sub_distrib, sum_indicator_mul]
  apply hx
  rw [hid]
  nlinarith
theorem disjoint_averages_generic_ae {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => gaussianReal 0 1),
      ∀ A B : Finset ι, A.Nonempty → B.Nonempty → Disjoint A B →
        (∑ i ∈ A, x i) / (A.card : ℝ) ≠ (∑ i ∈ B, x i) / (B.card : ℝ) := by
  classical
  apply ae_all_iff.mpr
  intro A
  apply ae_all_iff.mpr
  intro B
  by_cases h : A.Nonempty ∧ B.Nonempty ∧ Disjoint A B
  · filter_upwards [disjoint_averages_ae_ne A B h.1 h.2.1 h.2.2] with x hx
    exact fun _ _ _ => hx
  · exact Filter.Eventually.of_forall fun x hA hB hd => False.elim (h ⟨hA, hB, hd⟩)
end ArgmaxGaussianGenericPosition
open scoped BigOperators
namespace ArgmaxPrefixAverageGenericity
theorem prefix_averages_ne_of_lt {α : Type*} [DecidableEq α]
    (l : List α) (hnodup : l.Nodup) (w : α → ℝ)
    (hgeneric : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ a ∈ A, w a) / (A.card : ℝ) ≠ (∑ b ∈ B, w b) / (B.card : ℝ))
    (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ l.length) :
    ((l.take i).map w).sum / (i : ℝ) ≠ ((l.take j).map w).sum / (j : ℝ) := by
  have hil : i ≤ l.length := (Nat.le_of_lt hij).trans hj
  have hsegment : j - i ≤ (l.drop i).length := by
    simpa only [List.length_drop] using Nat.sub_le_sub_right hj i
  have hdecomp : l.take i ++ (l.drop i).take (j - i) = l.take j := by
    rw [← List.take_add, Nat.add_sub_of_le (Nat.le_of_lt hij)]
  have hndj : (l.take j).Nodup := hnodup.sublist (List.take_sublist j l)
  have hndboth : (l.take i ++ (l.drop i).take (j - i)).Nodup := by
    rw [hdecomp]
    exact hndj
  obtain ⟨hndA, hndB, hdisjoint⟩ := List.nodup_append'.mp hndboth
  let A := (l.take i).toFinset
  let B := ((l.drop i).take (j - i)).toFinset
  have hcardA : A.card = i := by
    rw [List.toFinset_card_of_nodup hndA, List.length_take_of_le hil]
  have hcardB : B.card = j - i := by
    rw [List.toFinset_card_of_nodup hndB, List.length_take_of_le hsegment]
  have hA : A.Nonempty := Finset.card_pos.mp (by rw [hcardA]; omega)
  have hB : B.Nonempty := Finset.card_pos.mp (by rw [hcardB]; omega)
  have hd : Disjoint A B := List.disjoint_toFinset_iff_disjoint.mpr hdisjoint
  have hsumA : (∑ a ∈ A, w a) = ((l.take i).map w).sum :=
    List.sum_toFinset w hndA
  have hsumB : (∑ b ∈ B, w b) = (((l.drop i).take (j - i)).map w).sum :=
    List.sum_toFinset w hndB
  have hsum : ((l.take j).map w).sum =
      ((l.take i).map w).sum + (((l.drop i).take (j - i)).map w).sum := by
    rw [← hdecomp, List.map_append, List.sum_append]
  have hiReal : 0 < (i : ℝ) := Nat.cast_pos.mpr (by omega)
  have hjReal : 0 < (j : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsegmentReal : 0 < ((j - i : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcast : (j : ℝ) = (i : ℝ) + ((j - i : ℕ) : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le (Nat.le_of_lt hij)]
  intro heq
  have hcross := (div_eq_div_iff (ne_of_gt hiReal) (ne_of_gt hjReal)).mp heq
  rw [hsum, hcast, mul_add, add_mul] at hcross
  have hcrossAB : ((l.take i).map w).sum * ((j - i : ℕ) : ℝ) =
      (((l.drop i).take (j - i)).map w).sum * (i : ℝ) :=
    add_left_cancel hcross
  have hmeanAB := (div_eq_div_iff (ne_of_gt hiReal) (ne_of_gt hsegmentReal)).mpr hcrossAB
  apply hgeneric A B hA hB hd
  simpa only [hsumA, hsumB, hcardA, hcardB] using hmeanAB
theorem prefix_averages_distinct {α : Type*} [DecidableEq α]
    (l : List α) (hnodup : l.Nodup) (w : α → ℝ)
    (hgeneric : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ a ∈ A, w a) / (A.card : ℝ) ≠ (∑ b ∈ B, w b) / (B.card : ℝ)) :
    ∀ i j : ℕ, 1 ≤ i → i ≤ l.length → 1 ≤ j → j ≤ l.length →
      ((l.take i).map w).sum / (i : ℝ) = ((l.take j).map w).sum / (j : ℝ) → i = j := by
  intro i j hi hil hj hjl heq
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim ((prefix_averages_ne_of_lt l hnodup w hgeneric i j hi hij hjl) heq)
  · exact hij
  · exact False.elim ((prefix_averages_ne_of_lt l hnodup w hgeneric j i hj hji hil) heq.symm)
theorem mapped_prefix_averages_distinct {α : Type*} [DecidableEq α]
    (l : List α) (hnodup : l.Nodup) (w : α → ℝ)
    (hgeneric : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ a ∈ A, w a) / (A.card : ℝ) ≠ (∑ b ∈ B, w b) / (B.card : ℝ)) :
    ∀ i j : ℕ, 1 ≤ i → i ≤ (l.map w).length → 1 ≤ j → j ≤ (l.map w).length →
      ((l.map w).take i).sum / (i : ℝ) = ((l.map w).take j).sum / (j : ℝ) → i = j := by
  intro i j hi hil hj hjl heq
  apply prefix_averages_distinct l hnodup w hgeneric i j hi
    (by simpa only [List.length_map] using hil) hj
    (by simpa only [List.length_map] using hjl)
  simpa only [← List.map_take] using heq
end ArgmaxPrefixAverageGenericity
namespace ArgmaxMinimumMeanExistence
theorem exists_strict_minimum_prefix_average (l : List ℝ) (hne : l ≠ [])
    (hdistinct : ∀ i j : ℕ, 1 ≤ i → i ≤ l.length → 1 ≤ j → j ≤ l.length →
      (l.take i).sum / (i : ℝ) = (l.take j).sum / (j : ℝ) → i = j) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ l.length ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ l.length → j ≠ r →
        (l.take r).sum / (r : ℝ) < (l.take j).sum / (j : ℝ) := by
  classical
  have hlen : 1 ≤ l.length := by
    cases l with
    | nil => exact False.elim (hne rfl)
    | cons x l => simp
  let s := Finset.Icc 1 l.length
  let avg : ℕ → ℝ := fun i => (l.take i).sum / (i : ℝ)
  have hs : s.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hlen⟩⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image s avg hs
  obtain ⟨hrpos, hrlen⟩ := Finset.mem_Icc.mp hr
  refine ⟨r, hrpos, hrlen, ?_⟩
  intro j hjpos hjlen hjne
  have hle := hmin j (Finset.mem_Icc.mpr ⟨hjpos, hjlen⟩)
  have hneavg : avg r ≠ avg j := by
    intro heq
    have hrj := hdistinct r j hrpos hrlen hjpos hjlen heq
    exact hjne hrj.symm
  exact lt_of_le_of_ne hle hneavg
theorem exists_minimum_mean_prefix_block_data (l : List ℝ) (hne : l ≠ [])
    (hdistinct : ∀ i j : ℕ, 1 ≤ i → i ≤ l.length → 1 ≤ j → j ≤ l.length →
      (l.take i).sum / (i : ℝ) = (l.take j).sum / (j : ℝ) → i = j) :
    ∃ r : ℕ, ∃ μ : ℝ, 1 ≤ r ∧ r ≤ l.length ∧
      μ = (l.take r).sum / (r : ℝ) ∧
      (l.take r).sum = (r : ℝ) * μ ∧
      ∀ j : ℕ, 0 < j → j ≤ l.length → j ≠ r →
        (j : ℝ) * μ < (l.take j).sum := by
  obtain ⟨r, hrpos, hrlen, hstrict⟩ :=
    exists_strict_minimum_prefix_average l hne hdistinct
  let μ := (l.take r).sum / (r : ℝ)
  have hrreal : 0 < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  refine ⟨r, μ, hrpos, hrlen, rfl, ?_, ?_⟩
  · have hdiv : (l.take r).sum / (r : ℝ) = μ := rfl
    have heq := (div_eq_iff (ne_of_gt hrreal)).mp hdiv
    simpa only [mul_comm] using heq
  · intro j hjpos hjlen hjne
    have hjreal : 0 < (j : ℝ) := Nat.cast_pos.mpr hjpos
    have hlt : μ < (l.take j).sum / (j : ℝ) :=
      hstrict j (by omega) hjlen hjne
    have hlinear := (lt_div_iff₀ hjreal).mp hlt
    simpa only [mul_comm] using hlinear
end ArgmaxMinimumMeanExistence
namespace ArgmaxMinimumMeanBlock
theorem remaining_prefix_mean_gt (l : List ℝ) (r : ℕ) (μ : ℝ)
    (hr : r ≤ l.length) (hmean : (l.take r).sum = (r : ℝ) * μ)
    (hminimum : ∀ j : ℕ, 0 < j → j ≤ l.length → j ≠ r →
      (j : ℝ) * μ < (l.take j).sum) :
    ∀ k : ℕ, 0 < k → k ≤ l.length - r →
      (k : ℝ) * μ < ((l.drop r).take k).sum := by
  intro k hkpos hklen
  have hsum : (l.take (r + k)).sum = (l.take r).sum + ((l.drop r).take k).sum := by
    rw [List.take_add, List.sum_append]
  have hgt := hminimum (r + k) (by omega) (by omega) (by omega)
  have hcancel : (r : ℝ) * μ + (k : ℝ) * μ <
      (r : ℝ) * μ + ((l.drop r).take k).sum := by
    simpa only [hsum, hmean, Nat.cast_add, add_mul] using hgt
  exact (add_lt_add_iff_left ((r : ℝ) * μ)).mp hcancel
end ArgmaxMinimumMeanBlock
namespace ArgmaxOrderedBlockExistence
lemma exists_ordered_canonical_blocks {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hl : l.Nodup)
    (hgen : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ x ∈ A, w x) / (A.card : ℝ) ≠ (∑ x ∈ B, w x) / (B.card : ℝ)) :
    ∃ blocks : List (List α), blocks.flatten = l ∧
      (∀ b ∈ blocks, b ≠ [] ∧
        ∀ k : ℕ, 0 < k → k < b.length →
          (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum) ∧
      blocks.Pairwise (fun b c =>
        (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ)) := by
  classical
  let mean : List α → ℝ := fun b => (b.map w).sum / (b.length : ℝ)
  let good : List α → Prop := fun b => b ≠ [] ∧
    ∀ k : ℕ, 0 < k → k < b.length → (k : ℝ) * mean b < ((b.take k).map w).sum
  change ∃ blocks : List (List α), blocks.flatten = l ∧
    (∀ b ∈ blocks, good b) ∧ blocks.Pairwise (fun b c => mean b < mean c)
  have build : ∀ n : ℕ, ∀ v : List α, v.length = n → v.Nodup →
      ∃ blocks : List (List α), blocks.flatten = v ∧
        (∀ b ∈ blocks, good b) ∧ blocks.Pairwise (fun b c => mean b < mean c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hvlen hvnodup
      by_cases hvnil : v = []
      · subst v
        exact ⟨[], rfl, by simp, by simp⟩
      · have hvmap : v.map w ≠ [] := by simpa using hvnil
        have hdistinct :=
          ArgmaxPrefixAverageGenericity.mapped_prefix_averages_distinct v hvnodup w hgen
        obtain ⟨r, μ, hrpos, hrlen, hmudef, hmean, hminimum⟩ :=
          ArgmaxMinimumMeanExistence.exists_minimum_mean_prefix_block_data (v.map w) hvmap hdistinct
        have hrlenV : r ≤ v.length := by simpa only [List.length_map] using hrlen
        let b := v.take r
        have hblen : b.length = r := List.length_take_of_le hrlenV
        have hbne : b ≠ [] := by
          intro hbzero
          have hz : b.length = 0 := by simp [hbzero]
          omega
        have hbmean : mean b = μ := by
          simpa only [mean, b, List.map_take, List.length_take_of_le hrlenV] using hmudef.symm
        have hbgood : good b := by
          refine ⟨hbne, ?_⟩
          intro k hkpos hklen
          have hkr : k < r := by omega
          have hprefix : (b.take k).map w = (v.map w).take k := by
            dsimp only [b]
            rw [List.take_take, Nat.min_eq_left hkr.le, List.map_take]
          rw [hbmean, hprefix]
          exact hminimum k hkpos (by simpa only [List.length_map] using hkr.le.trans hrlenV) (by omega)
        have htail : ∀ k : ℕ, 0 < k → k ≤ (v.drop r).length →
            (k : ℝ) * μ < (((v.drop r).take k).map w).sum := by
          intro k hkpos hklen
          have hh := ArgmaxMinimumMeanBlock.remaining_prefix_mean_gt
            (v.map w) r μ hrlen hmean hminimum k hkpos
            (by simpa only [List.length_drop, List.length_map] using hklen)
          simpa only [List.map_take, List.map_drop] using hh
        have hdropLess : (v.drop r).length < n := by
          simp only [List.length_drop]
          omega
        have hdropNodup : (v.drop r).Nodup :=
          hvnodup.sublist (List.drop_sublist r v)
        obtain ⟨bs, hflat, hgood, hsorted⟩ :=
          ih (v.drop r).length hdropLess (v.drop r) rfl hdropNodup
        refine ⟨b :: bs, ?_, ?_, ?_⟩
        · simp only [List.flatten_cons, hflat, b, List.take_append_drop]
        · intro c hc
          rcases List.mem_cons.mp hc with hc | hc
          · subst c
            exact hbgood
          · exact hgood c hc
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hsorted⟩
          intro c hc
          cases bs with
          | nil => simp at hc
          | cons d ds =>
            have hdgood := hgood d (by simp)
            have hdpos : 0 < d.length := List.length_pos_iff.mpr hdgood.1
            have hdlen : d.length ≤ (v.drop r).length := by
              have hh := congrArg List.length hflat
              simp only [List.flatten_cons, List.length_append] at hh
              omega
            have hdprefix : (v.drop r).take d.length = d := by
              rw [← hflat, List.flatten_cons, List.take_append_length]
            have hdgt := htail d.length hdpos hdlen
            rw [hdprefix] at hdgt
            have hmd : μ < mean d := by
              apply (lt_div_iff₀ (Nat.cast_pos.mpr hdpos : (0 : ℝ) < (d.length : ℝ))).mpr
              simpa only [mul_comm] using hdgt
            have hbd : mean b < mean d := by rw [hbmean]; exact hmd
            rcases List.mem_cons.mp hc with hc | hc
            · subst c
              exact hbd
            · exact hbd.trans ((List.pairwise_cons.mp hsorted).1 c hc)
  exact build l.length l rfl hl
end ArgmaxOrderedBlockExistence
namespace ArgmaxMinimumMeanGluing
lemma append_prefix_strict_above_mean (b c : List ℝ) (μ : ℝ)
    (hmean : b.sum = (b.length : ℝ) * μ)
    (hproper : ∀ k : ℕ, 0 < k → k < b.length →
      (k : ℝ) * μ < (b.take k).sum)
    (htail : ∀ k : ℕ, 0 < k → k ≤ c.length →
      (k : ℝ) * μ < (c.take k).sum) :
    ∀ j : ℕ, 0 < j → j ≤ (b ++ c).length → j ≠ b.length →
      (j : ℝ) * μ < ((b ++ c).take j).sum := by
  intro j hjpos hjlen hjne
  by_cases hjbefore : j < b.length
  · rw [List.take_append_of_le_length hjbefore.le]
    exact hproper j hjpos hjbefore
  · have hjafter : b.length < j := by omega
    have hkpos : 0 < j - b.length := by omega
    have hklen : j - b.length ≤ c.length := by
      simp only [List.length_append] at hjlen
      omega
    have hgt := htail (j - b.length) hkpos hklen
    have hsplit : j = b.length + (j - b.length) := by omega
    rw [hsplit, List.take_length_add_append, List.sum_append, hmean,
      Nat.cast_add, add_mul]
    simpa only [add_comm] using add_lt_add_left hgt ((b.length : ℝ) * μ)
lemma append_unique_minimum_mean_prefix (b c : List ℝ) (μ : ℝ) (hb : b ≠ [])
    (hmean : b.sum = (b.length : ℝ) * μ)
    (hproper : ∀ k : ℕ, 0 < k → k < b.length →
      (k : ℝ) * μ < (b.take k).sum)
    (htail : ∀ k : ℕ, 0 < k → k ≤ c.length →
      (k : ℝ) * μ < (c.take k).sum) :
    0 < b.length ∧ b.length ≤ (b ++ c).length ∧
      ((b ++ c).take b.length).sum = (b.length : ℝ) * μ ∧
      (∀ j : ℕ, 0 < j → j ≤ (b ++ c).length → j ≠ b.length →
        (j : ℝ) * μ < ((b ++ c).take j).sum) := by
  have hbpos : 0 < b.length := by
    by_contra h
    exact hb (List.length_eq_zero_iff.mp (by omega))
  refine ⟨hbpos, ?_, ?_, append_prefix_strict_above_mean b c μ hmean hproper htail⟩
  · simp
  · simpa only [List.take_append_length] using hmean
end ArgmaxMinimumMeanGluing
namespace ArgmaxOrderedBlockUniqueness
lemma block_sum_eq_length_mul_mean {α : Type*} (b : List α) (w : α → ℝ)
    (hb : b ≠ []) :
    (b.map w).sum = (b.length : ℝ) * ((b.map w).sum / (b.length : ℝ)) := by
  have hlen : 0 < b.length := List.length_pos_iff.mpr hb
  have hreal : 0 < (b.length : ℝ) := Nat.cast_pos.mpr hlen
  have hdiv : (b.map w).sum / (b.length : ℝ) =
      (b.map w).sum / (b.length : ℝ) := rfl
  simpa only [mul_comm] using (div_eq_iff (ne_of_gt hreal)).mp hdiv
theorem block_prefix_mean_gt {α : Type*} (b : List α) (w : α → ℝ) (μ : ℝ)
    (hb : b ≠ []) (hmean : μ < (b.map w).sum / (b.length : ℝ))
    (hchord : ∀ k : ℕ, 0 < k → k < b.length →
      (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum) :
    ∀ k : ℕ, 0 < k → k ≤ b.length →
      (k : ℝ) * μ < ((b.take k).map w).sum := by
  intro k hkpos hklen
  have hkreal : 0 < (k : ℝ) := Nat.cast_pos.mpr hkpos
  have hbase := mul_lt_mul_of_pos_left hmean hkreal
  by_cases hkeq : k = b.length
  · subst k
    rw [List.take_length]
    exact hbase.trans_eq (block_sum_eq_length_mul_mean b w hb).symm
  · exact hbase.trans (hchord k hkpos (lt_of_le_of_ne hklen hkeq))
theorem flatten_prefix_mean_gt {α : Type*} (blocks : List (List α)) (w : α → ℝ)
    (μ : ℝ)
    (hblocks : ∀ b ∈ blocks, b ≠ [] ∧ μ < (b.map w).sum / (b.length : ℝ) ∧
      ∀ k : ℕ, 0 < k → k < b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum) :
    ∀ k : ℕ, 0 < k → k ≤ blocks.flatten.length →
      (k : ℝ) * μ < ((blocks.flatten.take k).map w).sum := by
  revert hblocks
  induction blocks with
  | nil =>
      intro hblocks k hkpos hklen
      simp only [List.flatten_nil, List.length_nil] at hklen
      omega
  | cons b bs ih =>
      intro hblocks k hkpos hklen
      have hb := hblocks b (by simp)
      have htail : ∀ c ∈ bs, c ≠ [] ∧ μ < (c.map w).sum / (c.length : ℝ) ∧
          ∀ j : ℕ, 0 < j → j < c.length →
            (j : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take j).map w).sum := by
        intro c hc
        exact hblocks c (by simp [hc])
      by_cases hkhead : k ≤ b.length
      · rw [List.flatten_cons, List.take_append_of_le_length hkhead]
        exact block_prefix_mean_gt b w μ hb.1 hb.2.1 hb.2.2 k hkpos hkhead
      · have hbpos : 0 < b.length := List.length_pos_iff.mpr hb.1
        have hkremain : 0 < k - b.length := by omega
        have hkremainlen : k - b.length ≤ bs.flatten.length := by
          simp only [List.flatten_cons, List.length_append] at hklen
          omega
        have hhead := block_prefix_mean_gt b w μ hb.1 hb.2.1 hb.2.2
          b.length hbpos le_rfl
        simp only [List.take_length] at hhead
        have hrest := ih htail (k - b.length) hkremain hkremainlen
        have hsplit : k = b.length + (k - b.length) := by omega
        rw [hsplit, List.flatten_cons, List.take_length_add_append, List.map_append,
          List.sum_append, Nat.cast_add, add_mul]
        exact add_lt_add hhead hrest
theorem first_block_strict_minimum {α : Type*} (b : List α) (bs : List (List α))
    (w : α → ℝ)
    (hcanonical : ∀ c ∈ b :: bs, c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum)
    (hordered : (b :: bs).Pairwise (fun c d =>
      (c.map w).sum / (c.length : ℝ) < (d.map w).sum / (d.length : ℝ))) :
    0 < b.length ∧ b.length ≤ (b :: bs).flatten.length ∧
      (((b :: bs).flatten.take b.length).map w).sum =
        (b.length : ℝ) * ((b.map w).sum / (b.length : ℝ)) ∧
      (∀ k : ℕ, 0 < k → k ≤ (b :: bs).flatten.length → k ≠ b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) <
          (((b :: bs).flatten.take k).map w).sum) := by
  have hb := hcanonical b (by simp)
  have hheadmean := (List.pairwise_cons.mp hordered).1
  have htail : ∀ c ∈ bs, c ≠ [] ∧
      (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ) ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum := by
    intro c hc
    have hcan := hcanonical c (by simp [hc])
    exact ⟨hcan.1, hheadmean c hc, hcan.2⟩
  have htailprefix := flatten_prefix_mean_gt bs w
    ((b.map w).sum / (b.length : ℝ)) htail
  have hglue := ArgmaxMinimumMeanGluing.append_unique_minimum_mean_prefix
    (b.map w) (bs.flatten.map w) ((b.map w).sum / (b.length : ℝ))
    (by intro hempty; exact hb.1 (List.map_eq_nil_iff.mp hempty))
    (by simpa only [List.length_map] using block_sum_eq_length_mul_mean b w hb.1)
    (by simpa only [List.length_map, ← List.map_take] using hb.2)
    (by simpa only [List.length_map, ← List.map_take] using htailprefix)
  simpa only [List.length_map, List.length_append, List.flatten_cons, List.map_take,
    List.map_append] using hglue
theorem strict_minimum_prefix_index_unique {α : Type*} (l : List α) (w : α → ℝ)
    (r s : ℕ) (μ ν : ℝ) (hrpos : 0 < r) (hspos : 0 < s)
    (hrlen : r ≤ l.length) (hslen : s ≤ l.length)
    (hrsum : ((l.take r).map w).sum = (r : ℝ) * μ)
    (hssum : ((l.take s).map w).sum = (s : ℝ) * ν)
    (hrstrict : ∀ k : ℕ, 0 < k → k ≤ l.length → k ≠ r →
      (k : ℝ) * μ < ((l.take k).map w).sum)
    (hsstrict : ∀ k : ℕ, 0 < k → k ≤ l.length → k ≠ s →
      (k : ℝ) * ν < ((l.take k).map w).sum) : r = s := by
  by_contra hne
  have hμν := hrstrict s hspos hslen (Ne.symm hne)
  have hνμ := hsstrict r hrpos hrlen hne
  rw [hssum] at hμν
  rw [hrsum] at hνμ
  have hrreal : 0 < (r : ℝ) := Nat.cast_pos.mpr hrpos
  have hsreal : 0 < (s : ℝ) := Nat.cast_pos.mpr hspos
  have hlt : μ < ν := (mul_lt_mul_iff_right₀ hsreal).mp hμν
  have hgt : ν < μ := (mul_lt_mul_iff_right₀ hrreal).mp hνμ
  exact lt_asymm hlt hgt
theorem ordered_canonical_blocks_unique {α : Type*}
    (blocks₁ blocks₂ : List (List α)) (w : α → ℝ)
    (hflat : blocks₁.flatten = blocks₂.flatten)
    (hcanonical₁ : ∀ b ∈ blocks₁, b ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum)
    (hcanonical₂ : ∀ b ∈ blocks₂, b ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum)
    (hordered₁ : blocks₁.Pairwise (fun b c =>
      (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ)))
    (hordered₂ : blocks₂.Pairwise (fun b c =>
      (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ))) :
    blocks₁ = blocks₂ := by
  revert hflat hcanonical₁ hcanonical₂ hordered₁ hordered₂
  induction blocks₁ generalizing blocks₂ with
  | nil =>
      intro hflat hcanonical₁ hcanonical₂ hordered₁ hordered₂
      cases blocks₂ with
      | nil => rfl
      | cons c cs =>
          have hc := (hcanonical₂ c (by simp)).1
          have hcpos : 0 < c.length := List.length_pos_iff.mpr hc
          have hlen := congrArg List.length hflat
          simp only [List.flatten_nil, List.flatten_cons, List.length_append, List.length_nil] at hlen
          omega
  | cons b bs ih =>
      intro hflat hcanonical₁ hcanonical₂ hordered₁ hordered₂
      cases blocks₂ with
      | nil =>
          have hb := (hcanonical₁ b (by simp)).1
          have hbpos : 0 < b.length := List.length_pos_iff.mpr hb
          have hlen := congrArg List.length hflat
          simp only [List.flatten_nil, List.flatten_cons, List.length_append, List.length_nil] at hlen
          omega
      | cons c cs =>
          have hbdata := first_block_strict_minimum b bs w hcanonical₁ hordered₁
          have hcdata := first_block_strict_minimum c cs w hcanonical₂ hordered₂
          simp only [← hflat] at hcdata
          have hlength : b.length = c.length :=
            strict_minimum_prefix_index_unique (b :: bs).flatten w b.length c.length
              ((b.map w).sum / (b.length : ℝ)) ((c.map w).sum / (c.length : ℝ))
              hbdata.1 hcdata.1 hbdata.2.1 hcdata.2.1
              hbdata.2.2.1 hcdata.2.2.1 hbdata.2.2.2 hcdata.2.2.2
          have hbTake : (b :: bs).flatten.take b.length = b := by
            simp only [List.flatten_cons, List.take_append_length]
          have hcTake : (c :: cs).flatten.take b.length = c := by
            rw [hlength]
            simp only [List.flatten_cons, List.take_append_length]
          have hhead : b = c := hbTake.symm.trans
            ((congrArg (fun l : List α => l.take b.length) hflat).trans hcTake)
          subst c
          have htailflat : bs.flatten = cs.flatten :=
            List.append_cancel_left (by simpa only [List.flatten_cons] using hflat)
          have htailcan₁ : ∀ d ∈ bs, d ≠ [] ∧
              ∀ k : ℕ, 0 < k → k < d.length →
                (k : ℝ) * ((d.map w).sum / (d.length : ℝ)) < ((d.take k).map w).sum := by
            intro d hd
            exact hcanonical₁ d (by simp [hd])
          have htailcan₂ : ∀ d ∈ cs, d ≠ [] ∧
              ∀ k : ℕ, 0 < k → k < d.length →
                (k : ℝ) * ((d.map w).sum / (d.length : ℝ)) < ((d.take k).map w).sum := by
            intro d hd
            exact hcanonical₂ d (by simp [hd])
          have htail := ih cs htailflat htailcan₁ htailcan₂
            (List.pairwise_cons.mp hordered₁).2 (List.pairwise_cons.mp hordered₂).2
          exact congrArg (List.cons b) htail
end ArgmaxOrderedBlockUniqueness
namespace ArgmaxOrderedBlockDecomposition
theorem existsUnique_ordered_canonical_blocks {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hl : l.Nodup)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ i ∈ U, w i) / (U.card : ℝ) ≠ (∑ i ∈ V, w i) / (V.card : ℝ)) :
    ∃! blocks : List (List α), blocks.flatten = l ∧
      (∀ b ∈ blocks, b ≠ [] ∧
        ∀ k : ℕ, 0 < k → k < b.length →
          (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum) ∧
      blocks.Pairwise (fun b c =>
        (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ)) := by
  obtain ⟨blocks, hflat, hcanonical, hsorted⟩ :=
    ArgmaxOrderedBlockExistence.exists_ordered_canonical_blocks l w hl hgen
  refine ⟨blocks, ⟨hflat, hcanonical, hsorted⟩, ?_⟩
  rintro other ⟨hotherflat, hothercanonical, hothersorted⟩
  exact ArgmaxOrderedBlockUniqueness.ordered_canonical_blocks_unique other blocks w
    (hotherflat.trans hflat.symm) hothercanonical hcanonical hothersorted hsorted
theorem gaussian_ordered_canonical_blocks_ae {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => gaussianReal 0 1),
      ∀ l : List ι, l.Nodup →
        ∃! blocks : List (List ι), blocks.flatten = l ∧
          (∀ b ∈ blocks, b ≠ [] ∧
            ∀ k : ℕ, 0 < k → k < b.length →
              (k : ℝ) * ((b.map x).sum / (b.length : ℝ)) < ((b.take k).map x).sum) ∧
          blocks.Pairwise (fun b c =>
            (b.map x).sum / (b.length : ℝ) < (c.map x).sum / (c.length : ℝ)) := by
  filter_upwards [ArgmaxGaussianGenericPosition.disjoint_averages_generic_ae] with x hgen
  intro l hl
  exact existsUnique_ordered_canonical_blocks l x hl hgen
end ArgmaxOrderedBlockDecomposition
namespace ArgmaxPositiveCanonicalBlocks
lemma positive_prefixes_iff_positive_block_means {α : Type*}
    (l : List α) (blocks : List (List α)) (w : α → ℝ)
    (hflat : blocks.flatten = l)
    (hcanonical : ∀ b ∈ blocks, b ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum)
    (hordered : blocks.Pairwise (fun b c =>
      (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ))) :
    (∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum) ↔
      (∀ b ∈ blocks, 0 < (b.map w).sum / (b.length : ℝ)) := by
  constructor
  · intro hprefix
    cases blocks with
    | nil => simp
    | cons b bs =>
      have hb := hcanonical b (by simp)
      have hbpos : 0 < b.length := List.length_pos_iff.mpr hb.1
      have hblen : b.length ≤ l.length := by
        rw [← hflat, List.flatten_cons, List.length_append]
        omega
      have hbprefix : l.take b.length = b := by
        rw [← hflat, List.flatten_cons, List.take_append_length]
      have hbsum := hprefix b.length hbpos hblen
      rw [hbprefix] at hbsum
      have hbmean : 0 < (b.map w).sum / (b.length : ℝ) :=
        div_pos hbsum (Nat.cast_pos.mpr hbpos)
      intro c hc
      rcases List.mem_cons.mp hc with hc | hc
      · subst c
        exact hbmean
      · exact hbmean.trans ((List.pairwise_cons.mp hordered).1 c hc)
  · intro hmean
    have hblocks : ∀ b ∈ blocks, b ≠ [] ∧
        (0 : ℝ) < (b.map w).sum / (b.length : ℝ) ∧
        ∀ k : ℕ, 0 < k → k < b.length →
          (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum := by
      intro b hb
      exact ⟨(hcanonical b hb).1, hmean b hb, (hcanonical b hb).2⟩
    have hh := ArgmaxOrderedBlockUniqueness.flatten_prefix_mean_gt blocks w 0 hblocks
    intro k hkpos hklen
    have hstep := hh k hkpos (by simpa only [hflat] using hklen)
    simpa only [mul_zero, hflat] using hstep
end ArgmaxPositiveCanonicalBlocks
namespace ArgmaxDistinguishedBlockRemoval
lemma block_nodup_of_mem {α : Type*} (blocks : List (List α))
    (hnd : blocks.flatten.Nodup) (b : List α) (hb : b ∈ blocks) : b.Nodup :=
  hnd.sublist (List.sublist_flatten_of_mem hb)
lemma block_labels_subset_flatten {α : Type*} [DecidableEq α]
    (blocks : List (List α)) (b : List α) (hb : b ∈ blocks) :
    b.toFinset ⊆ blocks.flatten.toFinset := by
  intro x hx
  exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨b, hb, List.mem_toFinset.mp hx⟩)
theorem context_removal_label_data {α : Type*} [DecidableEq α]
    (pre : List (List α)) (b : List α) (post : List (List α))
    (hnd : (pre ++ b :: post).flatten.Nodup) :
    b.Nodup ∧ (pre ++ post).flatten.Nodup ∧
      Disjoint b.toFinset (pre ++ post).flatten.toFinset ∧
      (pre ++ post).flatten.toFinset = (pre ++ b :: post).flatten.toFinset \ b.toFinset := by
  have hsub : (pre ++ post).Sublist (pre ++ b :: post) :=
    (List.sublist_cons_self b post).append_left pre
  have hsubflat : (pre ++ post).flatten.Sublist (pre ++ b :: post).flatten := hsub.flatten
  have hndrem := hnd.sublist hsubflat
  have hndexpanded : (pre.flatten ++ (b ++ post.flatten)).Nodup := by
    simpa only [List.flatten_append, List.flatten_cons] using hnd
  obtain ⟨hndpre, hndbpost, hdpre⟩ := List.nodup_append'.mp hndexpanded
  obtain ⟨hndb, hndpost, hdbpost⟩ := List.nodup_append'.mp hndbpost
  have hd : Disjoint b.toFinset (pre ++ post).flatten.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hxb hxr
    have hxb' := List.mem_toFinset.mp hxb
    have hxr' := List.mem_toFinset.mp hxr
    simp only [List.flatten_append, List.mem_append] at hxr'
    rcases hxr' with hxpre | hxpost
    · exact (List.disjoint_left.mp hdpre hxpre) (List.mem_append.mpr (Or.inl hxb'))
    · exact (List.disjoint_left.mp hdbpost hxb') hxpost
  refine ⟨hndb, hndrem, hd, ?_⟩
  ext x
  constructor
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact List.mem_toFinset.mpr (hsubflat.subset (List.mem_toFinset.mp hx))
    · intro hxb
      exact Finset.disjoint_left.mp hd hxb hx
  · intro hx
    obtain ⟨hxwhole, hxnotb⟩ := Finset.mem_sdiff.mp hx
    have hxwhole' := List.mem_toFinset.mp hxwhole
    simp only [List.flatten_append, List.flatten_cons, List.mem_append] at hxwhole'
    rcases hxwhole' with hxpre | hxb | hxpost
    · exact List.mem_toFinset.mpr (by
        simpa only [List.flatten_append, List.mem_append] using
          (Or.inl hxpre : x ∈ pre.flatten ∨ x ∈ post.flatten))
    · exact False.elim (hxnotb (List.mem_toFinset.mpr hxb))
    · exact List.mem_toFinset.mpr (by
        simpa only [List.flatten_append, List.mem_append] using
          (Or.inr hxpost : x ∈ pre.flatten ∨ x ∈ post.flatten))
theorem exists_distinguished_block_context {α : Type*} [DecidableEq α]
    (blocks : List (List α)) (hnd : blocks.flatten.Nodup) (d : α)
    (hd : d ∈ blocks.flatten) :
    ∃ pre : List (List α), ∃ b : List α, ∃ post : List (List α),
      blocks = pre ++ b :: post ∧ d ∈ b ∧
        ∀ c ∈ blocks, d ∈ c → c = b := by
  obtain ⟨b, hb, hdb⟩ := List.mem_flatten.mp hd
  obtain ⟨pre, post, hcontext⟩ := List.mem_iff_append.mp hb
  have hndcontext : (pre ++ b :: post).flatten.Nodup := by
    rw [← hcontext]
    exact hnd
  have hdata := context_removal_label_data pre b post hndcontext
  have hnorem : d ∉ (pre ++ post).flatten := by
    intro hmem
    exact Finset.disjoint_left.mp hdata.2.2.1
      (List.mem_toFinset.mpr hdb) (List.mem_toFinset.mpr hmem)
  refine ⟨pre, b, post, hcontext, hdb, ?_⟩
  intro c hc hdc
  rw [hcontext] at hc
  rcases List.mem_append.mp hc with hcpre | hcpost
  · exact False.elim (hnorem (List.mem_flatten.mpr
      ⟨c, List.mem_append.mpr (Or.inl hcpre), hdc⟩))
  · rcases List.mem_cons.mp hcpost with hcb | hcpost
    · exact hcb
    · exact False.elim (hnorem (List.mem_flatten.mpr
        ⟨c, List.mem_append.mpr (Or.inr hcpost), hdc⟩))
theorem exists_unique_containing_block {α : Type*} [DecidableEq α]
    (blocks : List (List α)) (hnd : blocks.flatten.Nodup) (d : α)
    (hd : d ∈ blocks.flatten) :
    ∃! b : List α, b ∈ blocks ∧ d ∈ b := by
  obtain ⟨pre, b, post, hcontext, hdb, huniq⟩ :=
    exists_distinguished_block_context blocks hnd d hd
  refine ⟨b, ⟨?_, hdb⟩, ?_⟩
  · rw [hcontext]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
  · intro c hc
    exact huniq c hc.1 hc.2
theorem context_removal_preserves_conditions {α : Type*}
    (pre : List (List α)) (b : List α) (post : List (List α)) (w : α → ℝ)
    (hcanonical : ∀ c ∈ pre ++ b :: post, c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum)
    (hordered : (pre ++ b :: post).Pairwise (fun c e =>
      (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)))
    (hpositive : ∀ c ∈ pre ++ b :: post, 0 < (c.map w).sum / (c.length : ℝ)) :
    (∀ c ∈ pre ++ post, c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) ∧
      (pre ++ post).Pairwise (fun c e =>
        (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)) ∧
      (∀ c ∈ pre ++ post, 0 < (c.map w).sum / (c.length : ℝ)) := by
  have hsub : (pre ++ post).Sublist (pre ++ b :: post) :=
    (List.sublist_cons_self b post).append_left pre
  refine ⟨?_, hordered.sublist hsub, ?_⟩
  · intro c hc
    exact hcanonical c (hsub.subset hc)
  · intro c hc
    exact hpositive c (hsub.subset hc)
end ArgmaxDistinguishedBlockRemoval
open scoped BigOperators
namespace ArgmaxCanonicalBlockInsertion
lemma block_mean_ne_of_disjoint_labels {α : Type*} [DecidableEq α]
    (b : List α) (bs : List (List α)) (w : α → ℝ)
    (hb : b ≠ []) (hbNodup : b.Nodup) (hflatNodup : bs.flatten.Nodup)
    (hdisjoint : List.Disjoint b bs.flatten)
    (hblocks : ∀ c ∈ bs, c ≠ [])
    (hgen : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ x ∈ A, w x) / (A.card : ℝ) ≠ (∑ x ∈ B, w x) / (B.card : ℝ)) :
    ∀ c ∈ bs, (b.map w).sum / (b.length : ℝ) ≠
      (c.map w).sum / (c.length : ℝ) := by
  intro c hc
  have hcsub := List.sublist_flatten_of_mem hc
  have hcNodup : c.Nodup := hflatNodup.sublist hcsub
  have hB : b.toFinset.Nonempty := Finset.card_pos.mp (by
    rw [List.toFinset_card_of_nodup hbNodup]
    exact List.length_pos_iff.mpr hb)
  have hC : c.toFinset.Nonempty := Finset.card_pos.mp (by
    rw [List.toFinset_card_of_nodup hcNodup]
    exact List.length_pos_iff.mpr (hblocks c hc))
  have hd : Disjoint b.toFinset c.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hxb hxc
    exact List.disjoint_left.mp hdisjoint (List.mem_toFinset.mp hxb)
      (hcsub.subset (List.mem_toFinset.mp hxc))
  simpa only [List.sum_toFinset w hbNodup, List.sum_toFinset w hcNodup,
    List.toFinset_card_of_nodup hbNodup, List.toFinset_card_of_nodup hcNodup] using
    hgen b.toFinset c.toFinset hB hC hd
lemma exists_ordered_gap {β : Type*} (bs : List β) (f : β → ℝ) (v : ℝ)
    (hsorted : bs.Pairwise (fun x y => f x < f y))
    (hne : ∀ x ∈ bs, v ≠ f x) :
    ∃ pre post : List β, bs = pre ++ post ∧
      (∀ x ∈ pre, f x < v) ∧ (∀ x ∈ post, v < f x) := by
  induction bs with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x xs ih =>
    have htail := (List.pairwise_cons.mp hsorted).2
    by_cases hx : f x < v
    · obtain ⟨pre, post, hsplit, hpre, hpost⟩ := ih htail (fun y hy => hne y (by simp [hy]))
      refine ⟨x :: pre, post, ?_, ?_, hpost⟩
      · simp only [List.cons_append, ← hsplit]
      · intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · subst y
          exact hx
        · exact hpre y hy
    · have hvx : v < f x := lt_of_le_of_ne (le_of_not_gt hx) (hne x (by simp))
      refine ⟨[], x :: xs, rfl, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with hy | hy
      · subst y
        exact hvx
      · exact hvx.trans ((List.pairwise_cons.mp hsorted).1 y hy)
lemma gap_prefix_eq_takeWhile {β : Type*} (pre post : List β) (f : β → ℝ) (v : ℝ)
    (hpre : ∀ x ∈ pre, f x < v) (hpost : ∀ x ∈ post, v < f x) :
    (pre ++ post).takeWhile (fun x => decide (f x < v)) = pre := by
  rw [List.takeWhile_append_of_pos (by intro x hx; simpa using hpre x hx)]
  have hstop : post.takeWhile (fun x => decide (f x < v)) = [] := by
    cases post with
    | nil => rfl
    | cons x xs =>
      have hx := hpost x (by simp)
      simp [not_lt_of_ge hx.le]
  rw [hstop, List.append_nil]
lemma ordered_gap_unique {β : Type*} (bs pre post pre' post' : List β)
    (f : β → ℝ) (v : ℝ) (hsplit : bs = pre ++ post) (hsplit' : bs = pre' ++ post')
    (hpre : ∀ x ∈ pre, f x < v) (hpost : ∀ x ∈ post, v < f x)
    (hpre' : ∀ x ∈ pre', f x < v) (hpost' : ∀ x ∈ post', v < f x) :
    pre = pre' ∧ post = post' := by
  have hp : pre = pre' := by
    calc
      pre = bs.takeWhile (fun x => decide (f x < v)) := by
        rw [hsplit, gap_prefix_eq_takeWhile pre post f v hpre hpost]
      _ = pre' := by rw [hsplit', gap_prefix_eq_takeWhile pre' post' f v hpre' hpost']
  refine ⟨hp, ?_⟩
  rw [← hp] at hsplit'
  exact List.append_cancel_left (hsplit.symm.trans hsplit')
lemma pairwise_insert_context {β : Type*} (pre post : List β) (b : β) (f : β → ℝ)
    (hsorted : (pre ++ post).Pairwise (fun x y => f x < f y))
    (hpre : ∀ x ∈ pre, f x < f b) (hpost : ∀ x ∈ post, f b < f x) :
    (pre ++ b :: post).Pairwise (fun x y => f x < f y) := by
  obtain ⟨hp, hq, hcross⟩ := List.pairwise_append.mp hsorted
  apply List.pairwise_append.mpr
  refine ⟨hp, List.pairwise_cons.mpr ⟨hpost, hq⟩, ?_⟩
  intro x hx y hy
  rcases List.mem_cons.mp hy with hy | hy
  · subst y
    exact hpre x hx
  · exact hcross x hx y hy
lemma forall_insert_context {β : Type*} (pre post : List β) (b : β) (P : β → Prop)
    (hold : ∀ x ∈ pre ++ post, P x) (hb : P b) :
    ∀ x ∈ pre ++ b :: post, P x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hold x (List.mem_append.mpr (Or.inl hx))
  · rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact hb
    · exact hold x (List.mem_append.mpr (Or.inr hx))
lemma canonical_block_insertion {α : Type*} [DecidableEq α]
    (b : List α) (bs : List (List α)) (w : α → ℝ)
    (hb : b ≠ [] ∧ ∀ k : ℕ, 0 < k → k < b.length →
      (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum)
    (hcanonical : ∀ c ∈ bs, c ≠ [] ∧ ∀ k : ℕ, 0 < k → k < c.length →
      (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum)
    (hordered : bs.Pairwise (fun c d =>
      (c.map w).sum / (c.length : ℝ) < (d.map w).sum / (d.length : ℝ)))
    (hbNodup : b.Nodup) (hflatNodup : bs.flatten.Nodup)
    (hdisjoint : List.Disjoint b bs.flatten)
    (hgen : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ x ∈ A, w x) / (A.card : ℝ) ≠ (∑ x ∈ B, w x) / (B.card : ℝ)) :
    ∃ pre post : List (List α), bs = pre ++ post ∧
      (∀ c ∈ pre, (c.map w).sum / (c.length : ℝ) < (b.map w).sum / (b.length : ℝ)) ∧
      (∀ c ∈ post, (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ)) ∧
      (∀ c ∈ pre ++ b :: post, c ≠ [] ∧ ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) ∧
      (pre ++ b :: post).Pairwise (fun c d =>
        (c.map w).sum / (c.length : ℝ) < (d.map w).sum / (d.length : ℝ)) ∧
      (∀ pre' post' : List (List α), bs = pre' ++ post' →
        (∀ c ∈ pre', (c.map w).sum / (c.length : ℝ) < (b.map w).sum / (b.length : ℝ)) →
        (∀ c ∈ post', (b.map w).sum / (b.length : ℝ) < (c.map w).sum / (c.length : ℝ)) →
        pre' = pre ∧ post' = post) ∧
      (0 < (b.map w).sum / (b.length : ℝ) →
        (∀ c ∈ bs, 0 < (c.map w).sum / (c.length : ℝ)) →
        ∀ c ∈ pre ++ b :: post, 0 < (c.map w).sum / (c.length : ℝ)) := by
  let mean : List α → ℝ := fun c => (c.map w).sum / (c.length : ℝ)
  have hne : ∀ c ∈ bs, mean b ≠ mean c :=
    block_mean_ne_of_disjoint_labels b bs w hb.1 hbNodup hflatNodup hdisjoint
      (fun c hc => (hcanonical c hc).1) hgen
  obtain ⟨pre, post, hsplit, hpre, hpost⟩ := exists_ordered_gap bs mean (mean b) hordered hne
  refine ⟨pre, post, hsplit, hpre, hpost, ?_, ?_, ?_, ?_⟩
  · refine forall_insert_context pre post b
      (fun c => c ≠ [] ∧ ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) ?_ hb
    simpa only [← hsplit] using hcanonical
  · apply pairwise_insert_context pre post b mean _ hpre hpost
    simpa only [← hsplit] using hordered
  · intro pre' post' hsplit' hpre' hpost'
    exact ordered_gap_unique bs pre' post' pre post mean (mean b)
      hsplit' hsplit hpre' hpost' hpre hpost
  · intro hbpos holdpos
    refine forall_insert_context pre post b (fun c => 0 < mean c) ?_ hbpos
    simpa only [← hsplit] using holdpos
end ArgmaxCanonicalBlockInsertion
namespace ArgmaxZeroTotalRotation
lemma positive_proper_prefixes_iff_strict_minimum (l : List ℝ) (r : ℕ)
    (hr : r < l.length) (hsum : l.sum = 0) :
    (∀ k, 0 < k → k < l.length → 0 < ((l.rotate r).take k).sum) ↔
      (∀ j, j < l.length → j ≠ r → (l.take r).sum < (l.take j).sum) := by
  constructor
  · intro hpos j hj hjr
    by_cases hrj : r < j
    · have hkpos : 0 < j - r := by omega
      have hklt : j - r < l.length := by omega
      have heq := ArgmaxPositiveRotation.sum_take_rotate_no_wrap l r (j - r) hr.le (by omega)
      rw [show r + (j - r) = j by omega] at heq
      have hh := hpos (j - r) hkpos hklt
      linarith
    · have hjrlt : j < r := by omega
      have hkpos : 0 < l.length - r + j := by omega
      have hklt : l.length - r + j < l.length := by omega
      have heq := ArgmaxPositiveRotation.sum_take_rotate_wrap l r
        (l.length - r + j) hr.le (by omega) (by omega)
      rw [hsum, zero_add, show l.length - r + j - (l.length - r) = j by omega] at heq
      have hh := hpos (l.length - r + j) hkpos hklt
      linarith
  · intro hmin k hkpos hklt
    by_cases hnowrap : r + k ≤ l.length
    · have heq := ArgmaxPositiveRotation.sum_take_rotate_no_wrap l r k hr.le hnowrap
      rcases lt_or_eq_of_le hnowrap with hproper | hfinal
      · have hh := hmin (r + k) hproper (by omega)
        linarith
      · rw [hfinal, List.take_length, hsum] at heq
        have hrpos : 0 < r := by omega
        have hh := hmin 0 (by omega) (by omega)
        simp only [List.take_zero, List.sum_nil] at hh
        linarith
    · have hwrap : l.length - r ≤ k := by omega
      have heq := ArgmaxPositiveRotation.sum_take_rotate_wrap l r k hr.le hwrap hklt.le
      rw [hsum, zero_add] at heq
      have hh := hmin (k - (l.length - r)) (by omega) (by omega)
      linarith
lemma existsUnique_rotate_positive_proper_prefixes (l : List ℝ) (hne : l ≠ [])
    (hsum : l.sum = 0)
    (hinj : ∀ i j, i < l.length → j < l.length →
      (l.take i).sum = (l.take j).sum → i = j) :
    ∃! r : ℕ, r < l.length ∧
      (∀ k, 0 < k → k < l.length → 0 < ((l.rotate r).take k).sum) := by
  have hn : 0 < l.length := by
    by_contra h
    exact hne (List.length_eq_zero_iff.mp (by omega))
  obtain ⟨r, hr, hmin, _⟩ :=
    ArgmaxPositiveRotation.exists_last_min_on_range (fun j => (l.take j).sum) l.length hn
  have hstrict : ∀ j, j < l.length → j ≠ r → (l.take r).sum < (l.take j).sum := by
    intro j hj hjr
    apply lt_of_le_of_ne (hmin j hj)
    intro heq
    exact hjr (hinj j r hj hr heq.symm)
  refine ⟨r, ⟨hr, (positive_proper_prefixes_iff_strict_minimum l r hr hsum).mpr hstrict⟩, ?_⟩
  rintro s ⟨hs, hspos⟩
  by_contra hne
  have hrs := hstrict s hs hne
  have hsr := (positive_proper_prefixes_iff_strict_minimum l s hs hsum).mp hspos r hr (Ne.symm hne)
  exact lt_asymm hrs hsr
end ArgmaxZeroTotalRotation
open scoped BigOperators
namespace ArgmaxCycleGenericity
lemma sum_centered_weights {α : Type*} (l : List α) (w : α → ℝ) (μ : ℝ) :
    (l.map (fun x => w x - μ)).sum = (l.map w).sum - (l.length : ℝ) * μ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, ih]
    ring
lemma average_eq_of_centered_sum_zero {α : Type*} (A : Finset α) (w : α → ℝ) (μ : ℝ)
    (hA : A.Nonempty) (hsum : (∑ x ∈ A, (w x - μ)) = 0) :
    (∑ x ∈ A, w x) / (A.card : ℝ) = μ := by
  have hcard : (A.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Finset.card_pos.mpr hA))
  apply (div_eq_iff hcard).mpr
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  simpa only [mul_comm] using sub_eq_zero.mp hsum
lemma proper_subset_centered_sum_ne_zero {α : Type*} [DecidableEq α]
    (L A : Finset α) (w : α → ℝ) (μ : ℝ)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ x ∈ U, w x) / (U.card : ℝ) ≠ (∑ x ∈ V, w x) / (V.card : ℝ))
    (hA : A.Nonempty) (hsub : A ⊆ L) (hcard : A.card < L.card)
    (htotal : (∑ x ∈ L, (w x - μ)) = 0) :
    (∑ x ∈ A, (w x - μ)) ≠ 0 := by
  intro hzero
  have hB : (L \ A).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  have hsplit := Finset.sum_sdiff (f := fun x => w x - μ) hsub
  have hzeroB : (∑ x ∈ L \ A, (w x - μ)) = 0 := by
    rw [hzero, add_zero, htotal] at hsplit
    exact hsplit
  have hmeanA := average_eq_of_centered_sum_zero A w μ hA hzero
  have hmeanB := average_eq_of_centered_sum_zero (L \ A) w μ hB hzeroB
  exact hgen A (L \ A) hA hB Finset.disjoint_sdiff (hmeanA.trans hmeanB.symm)
lemma centered_prefix_ne_of_lt {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hl : l.Nodup)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ x ∈ U, w x) / (U.card : ℝ) ≠ (∑ x ∈ V, w x) / (V.card : ℝ))
    (i j : ℕ) (hij : i < j) (hj : j < l.length) :
    ((l.map (fun x => w x - (l.map w).sum / (l.length : ℝ))).take i).sum ≠
      ((l.map (fun x => w x - (l.map w).sum / (l.length : ℝ))).take j).sum := by
  intro heq
  let μ := (l.map w).sum / (l.length : ℝ)
  let f := fun x => w x - μ
  let y := l.map f
  let a := (l.drop i).take (j - i)
  let L := l.toFinset
  let A := a.toFinset
  have hn : 0 < l.length := by omega
  have hn0 : (l.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hasub : a.Sublist l :=
    (List.take_sublist (j - i) (l.drop i)).trans (List.drop_sublist i l)
  have haNodup : a.Nodup := hl.sublist hasub
  have halen : a.length = j - i := by
    dsimp only [a]
    simp only [List.length_take, List.length_drop]
    omega
  have hcardA : A.card = j - i := by
    rw [List.toFinset_card_of_nodup haNodup, halen]
  have hcardL : L.card = l.length := List.toFinset_card_of_nodup hl
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcardA]
    omega
  have hsub : A ⊆ L := by
    intro x hx
    exact List.mem_toFinset.mpr (hasub.subset (List.mem_toFinset.mp hx))
  have hcard : A.card < L.card := by rw [hcardA, hcardL]; omega
  have htotal : (∑ x ∈ L, f x) = 0 := by
    rw [List.sum_toFinset f hl]
    dsimp only [f]
    rw [sum_centered_weights]
    dsimp only [μ]
    rw [mul_comm (l.length : ℝ), div_mul_cancel₀ _ hn0, sub_self]
  have hamap : a.map f = (y.drop i).take (j - i) := by
    dsimp only [a, y]
    rw [List.map_take, List.map_drop]
  have hsplit := congrArg List.sum (List.take_add (l := y) (i := i) (j := j - i))
  rw [show i + (j - i) = j by omega, List.sum_append, ← hamap] at hsplit
  have hzeroList : (a.map f).sum = 0 := by
    change (y.take i).sum = (y.take j).sum at heq
    linarith
  have hzeroA : (∑ x ∈ A, f x) = 0 := by
    rw [List.sum_toFinset f haNodup]
    exact hzeroList
  exact proper_subset_centered_sum_ne_zero L A w μ hgen hA hsub hcard htotal hzeroA
lemma centered_proper_prefix_injective {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hl : l.Nodup)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ x ∈ U, w x) / (U.card : ℝ) ≠ (∑ x ∈ V, w x) / (V.card : ℝ)) :
    ∀ i j, i < l.length → j < l.length →
      ((l.map (fun x => w x - (l.map w).sum / (l.length : ℝ))).take i).sum =
        ((l.map (fun x => w x - (l.map w).sum / (l.length : ℝ))).take j).sum → i = j := by
  intro i j hi hj heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (centered_prefix_ne_of_lt l w hl hgen i j hij hj heq).elim
  · exact hij
  · exact (centered_prefix_ne_of_lt l w hl hgen j i hij hi heq.symm).elim
end ArgmaxCycleGenericity
namespace ArgmaxCanonicalLabelCycle
lemma weighted_mean_rotate {α : Type*} (l : List α) (w : α → ℝ) (r : ℕ) :
    ((l.rotate r).map w).sum / ((l.rotate r).length : ℝ) =
      (l.map w).sum / (l.length : ℝ) := by
  rw [((List.rotate_perm l r).map w).sum_eq, List.length_rotate]
lemma centered_rotation_prefix_sum {α : Type*} (l : List α) (w : α → ℝ)
    (μ : ℝ) (r k : ℕ) (hk : k ≤ l.length) :
    (((l.map (fun x => w x - μ)).rotate r).take k).sum =
      (((l.rotate r).take k).map w).sum - (k : ℝ) * μ := by
  rw [← List.map_rotate, ← List.map_take, ArgmaxCycleGenericity.sum_centered_weights,
    List.length_take_of_le (by simpa only [List.length_rotate] using hk)]
lemma centered_rotation_chord_iff {α : Type*} (l : List α) (w : α → ℝ) (r : ℕ) :
    (∀ k : ℕ, 0 < k → k < l.length →
      0 < (((l.map (fun x => w x - (l.map w).sum / (l.length : ℝ))).rotate r).take k).sum) ↔
    (∀ k : ℕ, 0 < k → k < (l.rotate r).length →
      (k : ℝ) * (((l.rotate r).map w).sum / ((l.rotate r).length : ℝ)) <
        (((l.rotate r).take k).map w).sum) := by
  constructor
  · intro h k hkpos hklen
    have hk : k < l.length := by simpa only [List.length_rotate] using hklen
    have hh := h k hkpos hk
    rw [centered_rotation_prefix_sum l w ((l.map w).sum / (l.length : ℝ)) r k hk.le] at hh
    rw [weighted_mean_rotate]
    exact sub_pos.mp hh
  · intro h k hkpos hklen
    have hh := h k hkpos (by simpa only [List.length_rotate] using hklen)
    rw [weighted_mean_rotate] at hh
    rw [centered_rotation_prefix_sum l w ((l.map w).sum / (l.length : ℝ)) r k hklen.le]
    exact sub_pos.mpr hh
lemma existsUnique_canonical_label_rotation {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hne : l ≠ []) (hl : l.Nodup)
    (hgen : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ x ∈ A, w x) / (A.card : ℝ) ≠ (∑ x ∈ B, w x) / (B.card : ℝ)) :
    ∃! b : List α, (∃ r : ℕ, b = l.rotate r) ∧ b ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum := by
  let y := l.map (fun x => w x - (l.map w).sum / (l.length : ℝ))
  have hyne : y ≠ [] := fun h => hne (List.map_eq_nil_iff.mp h)
  have hn : 0 < l.length := List.length_pos_iff.mpr hne
  have hn0 : (l.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : y.sum = 0 := by
    dsimp only [y]
    rw [ArgmaxCycleGenericity.sum_centered_weights,
      mul_comm (l.length : ℝ), div_mul_cancel₀ _ hn0, sub_self]
  have hinj := ArgmaxCycleGenericity.centered_proper_prefix_injective l w hl hgen
  obtain ⟨r, hr, hunique⟩ :=
    ArgmaxZeroTotalRotation.existsUnique_rotate_positive_proper_prefixes y hyne hsum
      (by simpa only [y, List.length_map] using hinj)
  have hraw := (centered_rotation_chord_iff l w r).mp
    (by simpa only [y, List.length_map] using hr.2)
  have hrotne : l.rotate r ≠ [] := fun h => hne (List.rotate_eq_nil_iff.mp h)
  refine ⟨l.rotate r, ⟨⟨r, rfl⟩, hrotne, hraw⟩, ?_⟩
  rintro b ⟨⟨s, hs⟩, hbne, hbraw⟩
  have hrawS : ∀ k : ℕ, 0 < k → k < (l.rotate s).length →
      (k : ℝ) * (((l.rotate s).map w).sum / ((l.rotate s).length : ℝ)) <
        (((l.rotate s).take k).map w).sum := by simpa only [hs] using hbraw
  have hposS := (centered_rotation_chord_iff l w s).mpr hrawS
  let t := s % l.length
  have ht : t < y.length := by simpa only [y, List.length_map] using Nat.mod_lt s hn
  have hyrot : y.rotate t = y.rotate s := by
    simpa only [t, y, List.length_map] using List.rotate_mod y s
  have htr : t = r := hunique t ⟨ht, by
    intro k hkpos hklen
    rw [hyrot]
    exact hposS k hkpos (by simpa only [y, List.length_map] using hklen)⟩
  calc
    b = l.rotate s := hs
    _ = l.rotate t := (List.rotate_mod l s).symm
    _ = l.rotate r := by rw [htr]
lemma rotation_witness_iff_input_rotate {α : Type*} (l b : List α) (s : ℕ) :
    (∃ r : ℕ, b = l.rotate r) ↔ (∃ r : ℕ, b = (l.rotate s).rotate r) := by
  constructor
  · rintro ⟨r, hr⟩
    have hforward : List.IsRotated l b := ⟨r, hr.symm⟩
    have hback : List.IsRotated (l.rotate s) l := List.IsRotated.forall l s
    obtain ⟨t, ht⟩ := hback.trans hforward
    exact ⟨t, ht.symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨s + r, by simpa only [List.rotate_rotate] using hr⟩
lemma canonical_label_rotation_invariant {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hne : l ≠ []) (hl : l.Nodup)
    (hgen : ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B →
      (∑ x ∈ A, w x) / (A.card : ℝ) ≠ (∑ x ∈ B, w x) / (B.card : ℝ))
    (s : ℕ) (b c : List α)
    (hb : (∃ r : ℕ, b = l.rotate r) ∧ b ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < b.length →
        (k : ℝ) * ((b.map w).sum / (b.length : ℝ)) < ((b.take k).map w).sum)
    (hc : (∃ r : ℕ, c = (l.rotate s).rotate r) ∧ c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) :
    b = c := by
  obtain ⟨u, hu, hunique⟩ := existsUnique_canonical_label_rotation l w hne hl hgen
  have hc' : (∃ r : ℕ, c = l.rotate r) ∧ c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum :=
    ⟨(rotation_witness_iff_input_rotate l c s).mpr hc.1, hc.2⟩
  exact (hunique b hb).trans (hunique c hc').symm
end ArgmaxCanonicalLabelCycle
namespace ArgmaxDistinguishedCycleRepresentative
theorem rotate_eq_of_head_eq {α : Type*} (l : List α) (hnd : l.Nodup)
    (hne : l ≠ []) (i j : ℕ) (hhead : (l.rotate i).head? = (l.rotate j).head?) :
    l.rotate i = l.rotate j := by
  rw [← List.rotate_mod l i, ← List.rotate_mod l j] at hhead
  have hmod : i % l.length = j % l.length := by
    simpa only [List.head?_rotate, Nat.mod_lt, List.length_pos_of_ne_nil hne,
      List.getElem?_eq_getElem, Option.some_inj, hnd.getElem_inj_iff, Fin.ext_iff] using hhead
  exact hnd.rotate_congr_iff.mpr (Or.inl hmod)
theorem rotate_idxOf_head {α : Type*} [DecidableEq α]
    (l : List α) (d : α) (hd : d ∈ l) :
    (l.rotate (l.idxOf d)).head? = some d := by
  rw [List.head?_rotate (List.idxOf_lt_length_of_mem hd), List.getElem?_idxOf hd]
theorem exists_unique_distinguished_rotation {α : Type*} [DecidableEq α]
    (l : List α) (hnd : l.Nodup) (d : α) (hd : d ∈ l) :
    ∃! b : List α, (∃ r : ℕ, b = l.rotate r) ∧ b.head? = some d := by
  have hne : l ≠ [] := List.ne_nil_of_mem hd
  have hhead := rotate_idxOf_head l d hd
  refine ⟨l.rotate (l.idxOf d), ⟨⟨l.idxOf d, rfl⟩, hhead⟩, ?_⟩
  intro b hb
  obtain ⟨r, rfl⟩ := hb.1
  exact rotate_eq_of_head_eq l hnd hne r (l.idxOf d) (hb.2.trans hhead.symm)
theorem exists_unique_distinguished_rotation_index {α : Type*} [DecidableEq α]
    (l : List α) (hnd : l.Nodup) (d : α) (hd : d ∈ l) :
    ∃! r : Fin l.length, (l.rotate r.val).head? = some d := by
  have hne : l ≠ [] := List.ne_nil_of_mem hd
  have hidx : l.idxOf d < l.length := List.idxOf_lt_length_of_mem hd
  have hhead := rotate_idxOf_head l d hd
  refine ⟨⟨l.idxOf d, hidx⟩, hhead, ?_⟩
  intro r hr
  have heq := rotate_eq_of_head_eq l hnd hne r.val (l.idxOf d) (hr.trans hhead.symm)
  have hmod := hnd.rotate_congr hne r.val (l.idxOf d) heq
  apply Fin.ext
  simpa only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt hidx] using hmod
end ArgmaxDistinguishedCycleRepresentative
namespace ArgmaxDistinguishedRootedWordCount
theorem mem_rooted_words_iff {α : Type*} [DecidableEq α]
    (A : Finset α) (d : α) (l : List α) :
    l ∈ A.toList.permutations.toFinset.filter (fun v => v.head? = some d) ↔
      l.Nodup ∧ l.toFinset = A ∧ l.head? = some d := by
  classical
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hperm, hhead⟩
    exact ⟨hperm.symm.nodup A.nodup_toList,
      (List.toFinset_eq_of_perm l A.toList hperm).trans A.toList_toFinset, hhead⟩
  · rintro ⟨hnd, hset, hhead⟩
    exact ⟨List.perm_of_nodup_nodup_toFinset_eq hnd A.nodup_toList
      (hset.trans A.toList_toFinset.symm), hhead⟩
theorem rooted_words_eq_cons_image {α : Type*} [DecidableEq α]
    (A : Finset α) (d : α) (hd : d ∈ A) :
    A.toList.permutations.toFinset.filter (fun v => v.head? = some d) =
      ((A.erase d).toList.permutations.toFinset.image (List.cons d)) := by
  classical
  ext l
  rw [mem_rooted_words_iff]
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hnd, hset, hhead⟩
    cases l with
    | nil => simp at hhead
    | cons a v =>
        have had : a = d := Option.some.inj hhead
        subst a
        have hndv := List.nodup_cons.mp hnd
        have htailset : v.toFinset = A.erase d := by
          ext x
          simp only [Finset.mem_erase, List.mem_toFinset]
          constructor
          · intro hxv
            refine ⟨?_, ?_⟩
            · intro hxd
              subst x
              exact hndv.1 hxv
            · have hx : x ∈ (d :: v).toFinset :=
                List.mem_toFinset.mpr (List.mem_cons.mpr (Or.inr hxv))
              simpa only [hset] using hx
          · rintro ⟨hxd, hxA⟩
            have hx : x ∈ (d :: v).toFinset := by simpa only [hset] using hxA
            rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with hxd' | hxv
            · exact False.elim (hxd hxd')
            · exact hxv
        refine ⟨v, ?_, rfl⟩
        apply List.perm_of_nodup_nodup_toFinset_eq hndv.2 (A.erase d).nodup_toList
        exact htailset.trans (A.erase d).toList_toFinset.symm
  · rintro ⟨v, hperm, rfl⟩
    have hndv : v.Nodup := hperm.symm.nodup (A.erase d).nodup_toList
    have htailset : v.toFinset = A.erase d :=
      (List.toFinset_eq_of_perm v (A.erase d).toList hperm).trans (A.erase d).toList_toFinset
    have hdnot : d ∉ v := by
      intro hdv
      have hx := List.mem_toFinset.mpr hdv
      rw [htailset] at hx
      exact (Finset.mem_erase.mp hx).1 rfl
    refine ⟨List.nodup_cons.mpr ⟨hdnot, hndv⟩, ?_, rfl⟩
    rw [List.toFinset_cons, htailset, Finset.insert_erase hd]
theorem card_rooted_words {α : Type*} [DecidableEq α]
    (A : Finset α) (d : α) (hd : d ∈ A) :
    (A.toList.permutations.toFinset.filter (fun v => v.head? = some d)).card =
      (A.card - 1).factorial := by
  classical
  rw [rooted_words_eq_cons_image A d hd]
  have hinj : Function.Injective (List.cons d : List α → List α) := by
    intro v z h
    exact (List.cons.inj h).2
  rw [Finset.card_image_of_injective _ hinj,
    List.toFinset_card_of_nodup
      (List.nodup_permutations (A.erase d).toList (A.erase d).nodup_toList),
    List.length_permutations, Finset.length_toList, Finset.card_erase_of_mem hd]
end ArgmaxDistinguishedRootedWordCount
open scoped BigOperators
namespace ArgmaxFiniteRelationCount
theorem card_eq_of_unique_relation {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) (hX : ∀ x, ∃! y, R x y) (hY : ∀ y, ∃! x, R x y) :
    Fintype.card X = Fintype.card Y := by
  classical
  let f : X → Y := fun x => (hX x).exists.choose
  have hf (x : X) : R x (f x) := (hX x).exists.choose_spec
  have hinj : Function.Injective f := by
    intro x₁ x₂ heq
    apply (hY (f x₁)).unique (hf x₁)
    simpa only [heq] using hf x₂
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hxy, _⟩ := hY y
    exact ⟨x, (hX x).unique (hf x) hxy⟩
  exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
theorem card_eq_sum_fibers_of_unique_relation {X A Y Z : Type*}
    (L : Finset X) (S : Finset A) (V : A → Finset Y) (W : A → Finset Z)
    (R : X → A → Y → Z → Prop)
    (hforward : ∀ l ∈ L, ∃! p : A × Y × Z,
      (p.1 ∈ S ∧ p.2.1 ∈ V p.1 ∧ p.2.2 ∈ W p.1) ∧ R l p.1 p.2.1 p.2.2)
    (hinverse : ∀ a ∈ S, ∀ v ∈ V a, ∀ z ∈ W a,
      ∃! l : X, l ∈ L ∧ R l a v z) :
    L.card = ∑ a ∈ S, (V a).card * (W a).card := by
  classical
  let D := (a : S) × ((V (a : A)) × (W (a : A)))
  let raw : D → A × Y × Z := fun p => ((p.1 : A), (p.2.1 : Y), (p.2.2 : Z))
  have hraw : Function.Injective raw := by
    rintro ⟨⟨a, ha⟩, ⟨v, hv⟩, ⟨z, hz⟩⟩ ⟨⟨a', ha'⟩, ⟨v', hv'⟩, ⟨z', hz'⟩⟩ heq
    have haeq : a = a' := congrArg Prod.fst heq
    subst a'
    have hveq : v = v' := congrArg (fun p : A × Y × Z => p.2.1) heq
    subst v'
    have hzeq : z = z' := congrArg (fun p : A × Y × Z => p.2.2) heq
    subst z'
    rfl
  let rel : L → D → Prop := fun l p => R (l : X) (p.1 : A) (p.2.1 : Y) (p.2.2 : Z)
  have hleft : ∀ l : L, ∃! p : D, rel l p := by
    intro l
    obtain ⟨⟨a, v, z⟩, ⟨⟨ha, hv, hz⟩, hr⟩, hu⟩ := hforward (l : X) l.property
    refine ⟨⟨⟨a, ha⟩, ⟨v, hv⟩, ⟨z, hz⟩⟩, hr, ?_⟩
    intro q hq
    apply hraw
    exact hu (raw q) ⟨⟨q.1.property, q.2.1.property, q.2.2.property⟩, hq⟩
  have hright : ∀ p : D, ∃! l : L, rel l p := by
    intro p
    obtain ⟨l, ⟨hl, hr⟩, hu⟩ := hinverse (p.1 : A) p.1.property
      (p.2.1 : Y) p.2.1.property (p.2.2 : Z) p.2.2.property
    refine ⟨⟨l, hl⟩, hr, ?_⟩
    intro q hq
    apply Subtype.ext
    exact hu (q : X) ⟨q.property, hq⟩
  have hcard := card_eq_of_unique_relation rel hleft hright
  have hcard' : L.card = ∑ a : S, (V (a : A)).card * (W (a : A)).card := by
    simpa only [D, Fintype.card_coe, Fintype.card_sigma, Fintype.card_prod] using hcard
  have hsum : (∑ a : S, (V (a : A)).card * (W (a : A)).card) =
      ∑ a ∈ S, (V a).card * (W a).card :=
    Finset.sum_coe_sort S (fun a => (V a).card * (W a).card)
  exact hcard'.trans hsum
end ArgmaxFiniteRelationCount
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace ArgmaxCountingForward
open scoped BigOperators
lemma nodup_context_unique {β : Type*} (pre pre' post post' : List β) (b : β)
    (hnd : (pre ++ b :: post).Nodup)
    (heq : pre ++ b :: post = pre' ++ b :: post') :
    pre = pre' ∧ post = post' := by
  revert hnd heq
  induction pre generalizing pre' with
  | nil =>
      intro hnd heq
      cases pre' with
      | nil =>
          simp only [List.nil_append] at heq
          exact ⟨rfl, (List.cons.inj heq).2⟩
      | cons c pre' =>
          simp only [List.nil_append, List.cons_append] at heq
          have hbc := (List.cons.inj heq).1
          subst c
          have hpost := (List.cons.inj heq).2
          have hnot := (List.nodup_cons.mp hnd).1
          apply False.elim
          apply hnot
          rw [hpost]
          exact List.mem_append_cons_self
  | cons a pre ih =>
      intro hnd heq
      cases pre' with
      | nil =>
          simp only [List.cons_append, List.nil_append] at heq
          have hab := (List.cons.inj heq).1
          subst a
          have hnot := (List.nodup_cons.mp hnd).1
          exact False.elim (hnot List.mem_append_cons_self)
      | cons c pre' =>
          simp only [List.cons_append] at heq hnd
          have hac := (List.cons.inj heq).1
          subst c
          obtain ⟨hpre, hpost⟩ := ih pre' (List.nodup_cons.mp hnd).2 (List.cons.inj heq).2
          exact ⟨congrArg (List.cons a) hpre, hpost⟩
lemma canonical_distinguished_context_unique {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (d : α) (w : α → ℝ)
    (pre pre' : List (List α)) (b b' : List α) (post post' : List (List α))
    (hflat : (pre ++ b :: post).flatten = l)
    (hflat' : (pre' ++ b' :: post').flatten = l)
    (hcanonical : ∀ c ∈ pre ++ b :: post, c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum)
    (hcanonical' : ∀ c ∈ pre' ++ b' :: post', c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum)
    (hordered : (pre ++ b :: post).Pairwise (fun c e =>
      (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)))
    (hordered' : (pre' ++ b' :: post').Pairwise (fun c e =>
      (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)))
    (hdb : d ∈ b) (hdb' : d ∈ b') : pre = pre' ∧ b = b' ∧ post = post' := by
  have hblocks := ArgmaxOrderedBlockUniqueness.ordered_canonical_blocks_unique
    (pre ++ b :: post) (pre' ++ b' :: post') w (hflat.trans hflat'.symm)
    hcanonical hcanonical' hordered hordered'
  have hndflat : (pre ++ b :: post).flatten.Nodup := by rw [hflat]; exact hl
  have hdflat : d ∈ (pre ++ b :: post).flatten :=
    List.mem_flatten.mpr ⟨b, List.mem_append_cons_self, hdb⟩
  obtain ⟨selected, hselected, hselectedUnique⟩ :=
    ArgmaxDistinguishedBlockRemoval.exists_unique_containing_block
      (pre ++ b :: post) hndflat d hdflat
  have hbsel : b = selected := hselectedUnique b ⟨List.mem_append_cons_self, hdb⟩
  have hb'sel : b' = selected := by
    apply hselectedUnique b'
    refine ⟨?_, hdb'⟩
    rw [hblocks]
    exact List.mem_append_cons_self
  have hbb' : b = b' := hbsel.trans hb'sel.symm
  have hblocks' : pre ++ b :: post = pre' ++ b :: post' := by
    simpa only [← hbb'] using hblocks
  have hndblocks : (pre ++ b :: post).Nodup := by
    apply hordered.imp
    intro c e hce heq
    subst e
    exact (lt_irrefl _) hce
  obtain ⟨hpre, hpost⟩ := nodup_context_unique pre pre' post post' b hndblocks hblocks'
  exact ⟨hpre, hbb', hpost⟩
theorem existsUnique_raw_data
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (w : α → ℝ)
    (hd : d ∈ I)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ i ∈ U, w i) / (U.card : ℝ) ≠ (∑ i ∈ V, w i) / (V.card : ℝ))
    (R : List α → Finset α → List α → List α → Prop)
    (hR : ∀ l A v z, R l A v z ↔
      ∃ pre : List (List α), ∃ b : List α, ∃ post : List (List α),
        (pre ++ b :: post).flatten = l ∧
        (∀ c ∈ pre ++ b :: post, c ≠ [] ∧
          ∀ k : ℕ, 0 < k → k < c.length →
            (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) ∧
        (pre ++ b :: post).Pairwise (fun c e =>
          (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)) ∧
        d ∈ b ∧ A = b.toFinset ∧ (∃ r : ℕ, v = b.rotate r) ∧
        v.head? = some d ∧ z = (pre ++ post).flatten)
    (l : List α) (hl : l.Nodup) (hI : l.toFinset = I)
    (hpositive : ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum) :
    ∃! p : Finset α × List α × List α,
      (p.1 ⊆ I ∧ d ∈ p.1 ∧ 0 < ∑ i ∈ p.1, w i ∧
        p.2.1.Nodup ∧ p.2.1.toFinset = p.1 ∧ p.2.1.head? = some d ∧
        p.2.2.Nodup ∧ p.2.2.toFinset = I \ p.1 ∧
        (∀ k : ℕ, 0 < k → k ≤ p.2.2.length → 0 < ((p.2.2.take k).map w).sum)) ∧
      R l p.1 p.2.1 p.2.2 := by
  classical
  obtain ⟨blocks, hflat, hcanonical, hordered⟩ :=
    ArgmaxOrderedBlockExistence.exists_ordered_canonical_blocks l w hl hgen
  have hpositiveMeans :=
    (ArgmaxPositiveCanonicalBlocks.positive_prefixes_iff_positive_block_means
      l blocks w hflat hcanonical hordered).mp hpositive
  have hndflat : blocks.flatten.Nodup := by rw [hflat]; exact hl
  have hdl : d ∈ l := List.mem_toFinset.mp (by simpa only [hI] using hd)
  have hdflat : d ∈ blocks.flatten := by rw [hflat]; exact hdl
  obtain ⟨pre, b, post, hcontext, hdb, hselectedUnique⟩ :=
    ArgmaxDistinguishedBlockRemoval.exists_distinguished_block_context blocks hndflat d hdflat
  have hctxflat : (pre ++ b :: post).flatten = l := by simpa only [hcontext] using hflat
  have hctxnd : (pre ++ b :: post).flatten.Nodup := by rw [hctxflat]; exact hl
  have hctxcan : ∀ c ∈ pre ++ b :: post, c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum := by
    simpa only [hcontext] using hcanonical
  have hctxordered : (pre ++ b :: post).Pairwise (fun c e =>
      (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)) := by
    simpa only [hcontext] using hordered
  have hctxpositive : ∀ c ∈ pre ++ b :: post, 0 < (c.map w).sum / (c.length : ℝ) := by
    simpa only [hcontext] using hpositiveMeans
  have hlabels := ArgmaxDistinguishedBlockRemoval.context_removal_label_data pre b post hctxnd
  have hbnd := hlabels.1
  obtain ⟨v, hv, hvUnique⟩ :=
    ArgmaxDistinguishedCycleRepresentative.exists_unique_distinguished_rotation b hbnd d hdb
  have hvnd : v.Nodup := by
    obtain ⟨r, hr⟩ := hv.1
    rw [hr]
    exact List.nodup_rotate.mpr hbnd
  have hvlabels : v.toFinset = b.toFinset := by
    obtain ⟨r, hr⟩ := hv.1
    rw [hr]
    exact List.toFinset_eq_of_perm _ _ (List.rotate_perm b r)
  have hsubset : b.toFinset ⊆ I := by
    have hsub := ArgmaxDistinguishedBlockRemoval.block_labels_subset_flatten
      (pre ++ b :: post) b List.mem_append_cons_self
    simpa only [hctxflat, hI] using hsub
  have hbpositive := hctxpositive b List.mem_append_cons_self
  have hbne : b ≠ [] := List.ne_nil_of_mem hdb
  have hbReal : 0 < (b.length : ℝ) := Nat.cast_pos.mpr (List.length_pos_iff.mpr hbne)
  have hAsumPositive : 0 < ∑ i ∈ b.toFinset, w i := by
    rw [List.sum_toFinset w hbnd,
      ArgmaxOrderedBlockUniqueness.block_sum_eq_length_mul_mean b w hbne]
    exact mul_pos hbReal hbpositive
  have hrem := ArgmaxDistinguishedBlockRemoval.context_removal_preserves_conditions
    pre b post w hctxcan hctxordered hctxpositive
  have hzpositive :=
    (ArgmaxPositiveCanonicalBlocks.positive_prefixes_iff_positive_block_means
      (pre ++ post).flatten (pre ++ post) w rfl hrem.1 hrem.2.1).mpr hrem.2.2
  have hzlabels : (pre ++ post).flatten.toFinset = I \ b.toFinset := by
    simpa only [hctxflat, hI] using hlabels.2.2.2
  have hrelation : R l b.toFinset v (pre ++ post).flatten := by
    apply (hR l b.toFinset v (pre ++ post).flatten).mpr
    exact ⟨pre, b, post, hctxflat, hctxcan, hctxordered, hdb, rfl, hv.1, hv.2, rfl⟩
  refine ⟨⟨b.toFinset, v, (pre ++ post).flatten⟩,
    ⟨⟨hsubset, List.mem_toFinset.mpr hdb, hAsumPositive, hvnd, hvlabels, hv.2,
      hlabels.2.1, hzlabels, hzpositive⟩, hrelation⟩, ?_⟩
  rintro ⟨A', v', z'⟩ ⟨hvalid', hrelation'⟩
  obtain ⟨pre', b', post', hflat', hcanonical', hordered', hdb', hA', hvrot', hvhead', hz'⟩ :=
    (hR l A' v' z').mp hrelation'
  obtain ⟨hpre, hblock, hpost⟩ := canonical_distinguished_context_unique
    l hl d w pre pre' b b' post post' hctxflat hflat'
    hctxcan hcanonical' hctxordered hordered' hdb hdb'
  subst pre'
  subst b'
  subst post'
  have hveq : v' = v := hvUnique v' ⟨hvrot', hvhead'⟩
  exact Prod.ext hA' (Prod.ext hveq hz')
end ArgmaxCountingForward
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace ArgmaxInsertionLabelData
theorem context_insertion_label_data {α : Type*} [DecidableEq α]
    (pre post : List (List α)) (b : List α)
    (hb : b.Nodup) (hrem : (pre ++ post).flatten.Nodup)
    (hdis : List.Disjoint b (pre ++ post).flatten) :
    (pre ++ b :: post).flatten.Nodup ∧
      (pre ++ b :: post).flatten.toFinset =
        b.toFinset ∪ (pre ++ post).flatten.toFinset := by
  have hperm : (pre ++ b :: post).flatten.Perm (b ++ (pre ++ post).flatten) := by
    simpa only [List.flatten_append, List.flatten_cons] using
      List.perm_append_comm_assoc pre.flatten b post.flatten
  refine ⟨hperm.nodup_iff.mpr (hb.append hrem hdis), ?_⟩
  ext x
  simp [List.flatten_append, List.flatten_cons, or_left_comm]
end ArgmaxInsertionLabelData
namespace ArgmaxCountingInverse
theorem existsUnique_good_word
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (w : α → ℝ)
    (hd : d ∈ I)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ i ∈ U, w i) / (U.card : ℝ) ≠ (∑ i ∈ V, w i) / (V.card : ℝ))
    (R : List α → Finset α → List α → List α → Prop)
    (hR : ∀ l A v z, R l A v z ↔
      ∃ pre : List (List α), ∃ b : List α, ∃ post : List (List α),
        (pre ++ b :: post).flatten = l ∧
        (∀ c ∈ pre ++ b :: post, c ≠ [] ∧
          ∀ k : ℕ, 0 < k → k < c.length →
            (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) ∧
        (pre ++ b :: post).Pairwise (fun c e =>
          (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)) ∧
        d ∈ b ∧ A = b.toFinset ∧ (∃ r : ℕ, v = b.rotate r) ∧
        v.head? = some d ∧ z = (pre ++ post).flatten)
    (A : Finset α) (v z : List α)
    (hA : A ⊆ I) (hdA : d ∈ A) (hApositive : 0 < ∑ i ∈ A, w i)
    (hv : v.Nodup) (hvA : v.toFinset = A) (hvhead : v.head? = some d)
    (hz : z.Nodup) (hzA : z.toFinset = I \ A)
    (hzpositive : ∀ k : ℕ, 0 < k → k ≤ z.length → 0 < ((z.take k).map w).sum) :
    ∃! l : List α,
      (l.Nodup ∧ l.toFinset = I ∧
        (∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum)) ∧
      R l A v z := by
  classical
  let mean : List α → ℝ := fun b => (b.map w).sum / (b.length : ℝ)
  have hvne : v ≠ [] := List.ne_nil_of_mem (List.mem_of_head? hvhead)
  obtain ⟨b, hbdata, hbunique⟩ :=
    ArgmaxCanonicalLabelCycle.existsUnique_canonical_label_rotation v w hvne hv hgen
  obtain ⟨hborbit, hbne, hbchord⟩ := hbdata
  obtain ⟨r, hr⟩ := hborbit
  have hbperm : b.Perm v := by rw [hr]; exact List.rotate_perm v r
  have hbNodup : b.Nodup := hbperm.nodup_iff.mpr hv
  have hbA : b.toFinset = A := (List.toFinset_eq_of_perm b v hbperm).trans hvA
  have hdb : d ∈ b := List.mem_toFinset.mp (by rw [hbA]; exact hdA)
  have hbsumpositive : 0 < (b.map w).sum := by
    rw [← List.sum_toFinset w hbNodup, hbA]
    exact hApositive
  have hbmeanpositive : 0 < mean b :=
    div_pos hbsumpositive (Nat.cast_pos.mpr (List.length_pos_iff.mpr hbne))
  have hvb : ∃ s : ℕ, v = b.rotate s := by
    have hforward : List.IsRotated v b := ⟨r, hr.symm⟩
    obtain ⟨s, hs⟩ := hforward.symm
    exact ⟨s, hs.symm⟩
  have hdisjointSets : Disjoint b.toFinset z.toFinset := by
    rw [hbA, hzA]
    exact Finset.disjoint_sdiff
  have hdisjoint : List.Disjoint b z := List.disjoint_toFinset_iff_disjoint.mp hdisjointSets
  obtain ⟨bs, hbsdata, hbsunique⟩ :=
    ArgmaxOrderedBlockDecomposition.existsUnique_ordered_canonical_blocks z w hz hgen
  obtain ⟨hbsflat, hbscanonical, hbsordered⟩ := hbsdata
  have hbspositive := (ArgmaxPositiveCanonicalBlocks.positive_prefixes_iff_positive_block_means
    z bs w hbsflat hbscanonical hbsordered).mp hzpositive
  have hflatNodup : bs.flatten.Nodup := by rw [hbsflat]; exact hz
  have hdisjointFlat : List.Disjoint b bs.flatten := by rw [hbsflat]; exact hdisjoint
  obtain ⟨pre, post, hsplit, hpre, hpost, hnewcanonical, hnewordered, hgapunique, hnewpositive⟩ :=
    ArgmaxCanonicalBlockInsertion.canonical_block_insertion b bs w ⟨hbne, hbchord⟩
      hbscanonical hbsordered hbNodup hflatNodup hdisjointFlat hgen
  have hremflat : (pre ++ post).flatten = z := by rw [← hsplit]; exact hbsflat
  have hremNodup : (pre ++ post).flatten.Nodup := by rw [hremflat]; exact hz
  have hdisjointRem : List.Disjoint b (pre ++ post).flatten := by rw [hremflat]; exact hdisjoint
  have hlabels := ArgmaxInsertionLabelData.context_insertion_label_data pre post b
    hbNodup hremNodup hdisjointRem
  let l := (pre ++ b :: post).flatten
  have hlI : l.toFinset = I := by
    calc
      l.toFinset = b.toFinset ∪ (pre ++ post).flatten.toFinset := hlabels.2
      _ = A ∪ (I \ A) := by rw [hbA, hremflat, hzA]
      _ = I := Finset.union_sdiff_of_subset hA
  have hlpositive : ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum :=
    (ArgmaxPositiveCanonicalBlocks.positive_prefixes_iff_positive_block_means
      l (pre ++ b :: post) w rfl hnewcanonical hnewordered).mpr
      (hnewpositive hbmeanpositive hbspositive)
  have hRl : R l A v z := (hR l A v z).mpr
    ⟨pre, b, post, rfl, hnewcanonical, hnewordered, hdb, hbA.symm, hvb, hvhead, hremflat.symm⟩
  refine ⟨l, ⟨⟨hlabels.1, hlI, hlpositive⟩, hRl⟩, ?_⟩
  rintro l' ⟨hgood', hRl'⟩
  obtain ⟨pre', b', post', hflat', hcanonical', hordered', hdb', hAb', hvrot', hvhead', hzflat'⟩ :=
    (hR l' A v z).mp hRl'
  have hb'canonical := hcanonical' b' (by simp)
  have hb'orbit : ∃ s : ℕ, b' = v.rotate s := by
    obtain ⟨s, hs⟩ := hvrot'
    have hforward : List.IsRotated b' v := ⟨s, hs.symm⟩
    obtain ⟨t, ht⟩ := hforward.symm
    exact ⟨t, ht.symm⟩
  have hbb' : b' = b := hbunique b' ⟨hb'orbit, hb'canonical.1, hb'canonical.2⟩
  subst b'
  have hsub : (pre' ++ post').Sublist (pre' ++ b :: post') :=
    (List.sublist_cons_self b post').append_left pre'
  have hremcanonical' : ∀ c ∈ pre' ++ post', c ≠ [] ∧
      ∀ k : ℕ, 0 < k → k < c.length →
        (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum := by
    intro c hc
    exact hcanonical' c (hsub.subset hc)
  have hremEq : pre' ++ post' = bs := hbsunique (pre' ++ post')
    ⟨hzflat'.symm, hremcanonical', hordered'.sublist hsub⟩
  have hparts := List.pairwise_append.mp hordered'
  have hpre' : ∀ c ∈ pre', mean c < mean b := by
    intro c hc
    exact hparts.2.2 c hc b (by simp)
  have hpost' : ∀ c ∈ post', mean b < mean c := (List.pairwise_cons.mp hparts.2.1).1
  obtain ⟨hpreEq, hpostEq⟩ := hgapunique pre' post' hremEq.symm hpre' hpost'
  calc
    l' = (pre' ++ b :: post').flatten := hflat'.symm
    _ = (pre ++ b :: post).flatten := by rw [hpreEq, hpostEq]
    _ = l := rfl
end ArgmaxCountingInverse
open scoped BigOperators Classical
namespace ArgmaxWordPrefixBridge
lemma sum_take_succ_ofFn {n : ℕ} (f : Fin n → ℝ) (k : Fin n) :
    ((List.ofFn f).take (k.val + 1)).sum =
      ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), f i := by
  rw [List.sum_take_ofFn]
  simp only [Fin.le_def, Nat.lt_succ_iff]
theorem positive_prefixes_ofFn_iff {n : ℕ} (f : Fin n → ℝ) :
    (∀ m : ℕ, 0 < m → m ≤ n → 0 < ((List.ofFn f).take m).sum) ↔
      ∀ k : Fin n, 0 < ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), f i := by
  constructor
  · intro h k
    rw [← sum_take_succ_ofFn f k]
    exact h (k.val + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt k.isLt)
  · intro h m hm hmn
    let k : Fin n := ⟨m - 1, by omega⟩
    have hkm : k.val + 1 = m := by dsimp [k]; omega
    rw [← hkm, sum_take_succ_ofFn f k]
    exact h k
theorem positive_mapped_prefixes_ofFn_iff {α : Type*} {n : ℕ}
    (p : Fin n → α) (w : α → ℝ) :
    (∀ m : ℕ, 0 < m → m ≤ (List.ofFn p).length →
      0 < (((List.ofFn p).take m).map w).sum) ↔
      ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), w (p i) := by
  simp only [List.length_ofFn, List.map_take, List.map_ofFn]
  exact positive_prefixes_ofFn_iff (fun i => w (p i))
end ArgmaxWordPrefixBridge
namespace ArgmaxGoodWordInterface
theorem mem_good_words_iff {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℝ) (l : List α) :
    l ∈ A.toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum) ↔
      l.Nodup ∧ l.toFinset = A ∧
        (∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum) := by
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨hperm, hpositive⟩
    exact ⟨hperm.symm.nodup A.nodup_toList,
      (List.toFinset_eq_of_perm l A.toList hperm).trans A.toList_toFinset, hpositive⟩
  · rintro ⟨hnd, hset, hpositive⟩
    exact ⟨List.perm_of_nodup_nodup_toFinset_eq hnd A.nodup_toList
      (hset.trans A.toList_toFinset.symm), hpositive⟩
theorem good_words_empty_eq_singleton {α : Type*} [DecidableEq α] (w : α → ℝ) :
    (∅ : Finset α).toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum) =
        {[]} := by
  ext l
  rw [mem_good_words_iff]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨_, hset, _⟩
    simpa using hset
  · intro hl
    subst l
    refine ⟨by simp, by simp, ?_⟩
    intro k hk hlen
    simp only [List.length_nil] at hlen
    omega
theorem card_good_words_empty {α : Type*} [DecidableEq α] (w : α → ℝ) :
    ((∅ : Finset α).toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)).card = 1 := by
  rw [good_words_empty_eq_singleton]
  simp
theorem length_eq_card_of_labels {α : Type*} [DecidableEq α]
    (A : Finset α) (l : List α) (hl : l.Nodup) (hset : l.toFinset = A) :
    l.length = A.card := by
  rw [← List.toFinset_card_of_nodup hl, hset]
theorem sum_map_eq_sum_labels {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℝ) (l : List α) (hl : l.Nodup) (hset : l.toFinset = A) :
    (l.map w).sum = ∑ i ∈ A, w i := by
  simpa only [hset] using (List.sum_toFinset w hl).symm
theorem length_of_mem_good_words {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℝ) (l : List α)
    (h : l ∈ A.toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)) :
    l.length = A.card := by
  rcases (mem_good_words_iff A w l).mp h with ⟨hnd, hset, _⟩
  exact length_eq_card_of_labels A l hnd hset
theorem sum_of_mem_good_words {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℝ) (l : List α)
    (h : l ∈ A.toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)) :
    (l.map w).sum = ∑ i ∈ A, w i := by
  rcases (mem_good_words_iff A w l).mp h with ⟨hnd, hset, _⟩
  exact sum_map_eq_sum_labels A w l hnd hset
theorem sum_pos_of_mem_good_words {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℝ) (l : List α) (hA : A.Nonempty)
    (h : l ∈ A.toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)) :
    0 < ∑ i ∈ A, w i := by
  rcases (mem_good_words_iff A w l).mp h with ⟨hnd, hset, hpositive⟩
  have hlen := length_eq_card_of_labels A l hnd hset
  have hlenpos : 0 < l.length := by rw [hlen]; exact hA.card_pos
  have hp := hpositive l.length hlenpos le_rfl
  rw [List.take_length, sum_map_eq_sum_labels A w l hnd hset] at hp
  exact hp
theorem existsUnique_perm_of_nodup_univ {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hset : l.toFinset = Finset.univ) :
    ∃! p : Equiv.Perm (Fin n), l = List.ofFn (fun i => p i) := by
  have hlen : l.length = n := by
    simpa using length_eq_card_of_labels Finset.univ l hl hset
  let f : Fin n → Fin n := fun i => l.get (Fin.cast hlen.symm i)
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin l.length => k.val) (hl.injective_get hij)
  let p : Equiv.Perm (Fin n) := Equiv.ofBijective f hf.bijective_of_finite
  have hfl : List.ofFn f = l :=
    (List.ofFn_congr hlen l.get).symm.trans (List.ofFn_get l)
  have hp : l = List.ofFn (fun i => p i) := hfl.symm
  refine ⟨p, hp, ?_⟩
  intro q hq
  apply Equiv.ext
  intro i
  exact congrFun (List.ofFn_injective (hq.symm.trans hp)) i
theorem nodup_labels_of_perm_word {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (List.ofFn (fun i => p i)).Nodup ∧
      (List.ofFn (fun i => p i)).toFinset = Finset.univ := by
  refine ⟨List.nodup_ofFn.mpr p.injective, ?_⟩
  ext i
  simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_univ, iff_true]
  exact p.surjective i
theorem sum_perm_word {n : ℕ} (w : Fin n → ℝ) (p : Equiv.Perm (Fin n)) :
    ((List.ofFn (fun i => p i)).map w).sum = ∑ i, w i := by
  rcases nodup_labels_of_perm_word p with ⟨hnd, hset⟩
  exact sum_map_eq_sum_labels Finset.univ w _ hnd hset
theorem nodup_univ_iff_existsUnique_perm {n : ℕ} (l : List (Fin n)) :
    (l.Nodup ∧ l.toFinset = Finset.univ) ↔
      ∃! p : Equiv.Perm (Fin n), l = List.ofFn (fun i => p i) := by
  constructor
  · rintro ⟨hnd, hset⟩
    exact existsUnique_perm_of_nodup_univ l hnd hset
  · rintro ⟨p, hp, _⟩
    rw [hp]
    exact nodup_labels_of_perm_word p
theorem existsUnique_perm_of_mem_good_words {n : ℕ} (w : Fin n → ℝ)
    (l : List (Fin n))
    (h : l ∈ (Finset.univ : Finset (Fin n)).toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)) :
    ∃! p : Equiv.Perm (Fin n), l = List.ofFn (fun i => p i) := by
  rcases (mem_good_words_iff Finset.univ w l).mp h with ⟨hnd, hset, _⟩
  exact existsUnique_perm_of_nodup_univ l hnd hset
theorem card_good_words_univ_eq_perm_filter {n : ℕ} (w : Fin n → ℝ) :
    ((Finset.univ : Finset (Fin n)).toList.permutations.toFinset.filter
      (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)).card =
      (Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
        ∀ k : Fin n, 0 < ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), w (p i))).card := by
  let Good := (Finset.univ : Finset (Fin n)).toList.permutations.toFinset.filter
    (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length → 0 < ((v.take k).map w).sum)
  let GoodPerm := Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
    ∀ k : Fin n, 0 < ∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), w (p i))
  have hEq : Good = GoodPerm.image (fun p => List.ofFn (fun i => p i)) := by
    ext l
    constructor
    · intro hl
      obtain ⟨p, hp, _⟩ := existsUnique_perm_of_mem_good_words w l hl
      refine Finset.mem_image.mpr ⟨p, ?_, hp.symm⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hpositive := ((mem_good_words_iff Finset.univ w l).mp hl).2.2
      rw [hp] at hpositive
      exact (ArgmaxWordPrefixBridge.positive_mapped_prefixes_ofFn_iff (fun i => p i) w).mp hpositive
    · intro hl
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
      apply (mem_good_words_iff Finset.univ w _).mpr
      obtain ⟨hnd, hset⟩ := nodup_labels_of_perm_word p
      refine ⟨hnd, hset, ?_⟩
      exact (ArgmaxWordPrefixBridge.positive_mapped_prefixes_ofFn_iff (fun i => p i) w).mpr
        (Finset.mem_filter.mp hp).2
  change Good.card = GoodPerm.card
  rw [hEq]
  apply Finset.card_image_of_injective
  intro p q hpq
  apply Equiv.ext
  intro i
  exact congrFun (List.ofFn_injective hpq) i
end ArgmaxGoodWordInterface
namespace ArgmaxDistinguishedCountingIdentity
theorem card_good_words_eq_sum
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (w : α → ℝ)
    (hd : d ∈ I)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ i ∈ U, w i) / (U.card : ℝ) ≠ (∑ i ∈ V, w i) / (V.card : ℝ)) :
    (I.toList.permutations.toFinset.filter
      (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum)).card =
      ∑ A ∈ I.powerset.filter (fun A => d ∈ A),
        if 0 < ∑ i ∈ A, w i then (A.card - 1).factorial *
          ((I \ A).toList.permutations.toFinset.filter
            (fun z => ∀ k : ℕ, 0 < k → k ≤ z.length → 0 < ((z.take k).map w).sum)).card
        else 0 := by
  classical
  let G : Finset α → Finset (List α) := fun A =>
    A.toList.permutations.toFinset.filter
      (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum)
  let V : Finset α → Finset (List α) := fun A =>
    A.toList.permutations.toFinset.filter (fun v => v.head? = some d)
  let S := I.powerset.filter (fun A => d ∈ A ∧ 0 < ∑ i ∈ A, w i)
  let R : List α → Finset α → List α → List α → Prop := fun l A v z =>
    ∃ pre : List (List α), ∃ b : List α, ∃ post : List (List α),
      (pre ++ b :: post).flatten = l ∧
      (∀ c ∈ pre ++ b :: post, c ≠ [] ∧
        ∀ k : ℕ, 0 < k → k < c.length →
          (k : ℝ) * ((c.map w).sum / (c.length : ℝ)) < ((c.take k).map w).sum) ∧
      (pre ++ b :: post).Pairwise (fun c e =>
        (c.map w).sum / (c.length : ℝ) < (e.map w).sum / (e.length : ℝ)) ∧
      d ∈ b ∧ A = b.toFinset ∧ (∃ r : ℕ, v = b.rotate r) ∧
      v.head? = some d ∧ z = (pre ++ post).flatten
  have hdata (p : Finset α × List α × List α) :
      (p.1 ∈ S ∧ p.2.1 ∈ V p.1 ∧ p.2.2 ∈ G (I \ p.1)) ↔
      (p.1 ⊆ I ∧ d ∈ p.1 ∧ 0 < ∑ i ∈ p.1, w i ∧
        p.2.1.Nodup ∧ p.2.1.toFinset = p.1 ∧ p.2.1.head? = some d ∧
        p.2.2.Nodup ∧ p.2.2.toFinset = I \ p.1 ∧
        (∀ k : ℕ, 0 < k → k ≤ p.2.2.length → 0 < ((p.2.2.take k).map w).sum)) := by
    constructor
    · rintro ⟨hS, hv, hz⟩
      obtain ⟨hA, hdA, hAp⟩ : p.1 ⊆ I ∧ d ∈ p.1 ∧ 0 < ∑ i ∈ p.1, w i := by
        simpa only [S, Finset.mem_filter, Finset.mem_powerset, and_assoc] using hS
      obtain ⟨hvnd, hvA, hvhead⟩ :=
        (ArgmaxDistinguishedRootedWordCount.mem_rooted_words_iff p.1 d p.2.1).mp hv
      obtain ⟨hznd, hzA, hzp⟩ :=
        (ArgmaxGoodWordInterface.mem_good_words_iff (I \ p.1) w p.2.2).mp hz
      exact ⟨hA, hdA, hAp, hvnd, hvA, hvhead, hznd, hzA, hzp⟩
    · rintro ⟨hA, hdA, hAp, hvnd, hvA, hvhead, hznd, hzA, hzp⟩
      refine ⟨?_, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hdA, hAp⟩
      · exact (ArgmaxDistinguishedRootedWordCount.mem_rooted_words_iff p.1 d p.2.1).mpr
          ⟨hvnd, hvA, hvhead⟩
      · exact (ArgmaxGoodWordInterface.mem_good_words_iff (I \ p.1) w p.2.2).mpr
          ⟨hznd, hzA, hzp⟩
  have hforward : ∀ l ∈ G I, ∃! p : Finset α × List α × List α,
      (p.1 ∈ S ∧ p.2.1 ∈ V p.1 ∧ p.2.2 ∈ G (I \ p.1)) ∧ R l p.1 p.2.1 p.2.2 := by
    intro l hl
    obtain ⟨hnd, hlabels, hpos⟩ := (ArgmaxGoodWordInterface.mem_good_words_iff I w l).mp hl
    have h := ArgmaxCountingForward.existsUnique_raw_data I d w hd hgen R
      (fun _ _ _ _ => Iff.rfl) l hnd hlabels hpos
    simpa only [hdata] using h
  have hinverse : ∀ A ∈ S, ∀ v ∈ V A, ∀ z ∈ G (I \ A),
      ∃! l : List α, l ∈ G I ∧ R l A v z := by
    intro A hAS v hv z hz
    obtain ⟨hA, hdA, hAp⟩ : A ⊆ I ∧ d ∈ A ∧ 0 < ∑ i ∈ A, w i := by
      simpa only [S, Finset.mem_filter, Finset.mem_powerset, and_assoc] using hAS
    obtain ⟨hvnd, hvA, hvhead⟩ :=
      (ArgmaxDistinguishedRootedWordCount.mem_rooted_words_iff A d v).mp hv
    obtain ⟨hznd, hzA, hzp⟩ :=
      (ArgmaxGoodWordInterface.mem_good_words_iff (I \ A) w z).mp hz
    have h := ArgmaxCountingInverse.existsUnique_good_word I d w hd hgen R
      (fun _ _ _ _ => Iff.rfl) A v z hA hdA hAp hvnd hvA hvhead hznd hzA hzp
    simpa only [G, ArgmaxGoodWordInterface.mem_good_words_iff] using h
  have hcard := ArgmaxFiniteRelationCount.card_eq_sum_fibers_of_unique_relation
    (G I) S V (fun A => G (I \ A)) R hforward hinverse
  have hS : S = (I.powerset.filter (fun A => d ∈ A)).filter
      (fun A => 0 < ∑ i ∈ A, w i) := by
    ext A
    simp only [S, Finset.mem_filter, and_assoc]
  change (G I).card = _
  rw [hcard, hS, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hp : 0 < ∑ i ∈ A, w i
  · simp only [hp, ↓reduceIte]
    have hdA : d ∈ A := (Finset.mem_filter.mp hA).2
    rw [show (V A).card = (A.card - 1).factorial from
      ArgmaxDistinguishedRootedWordCount.card_rooted_words A d hdA]
  · simp only [hp, ↓reduceIte]
theorem card_good_words_eq_sum_real
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (w : α → ℝ)
    (hd : d ∈ I)
    (hgen : ∀ U V : Finset α, U.Nonempty → V.Nonempty → Disjoint U V →
      (∑ i ∈ U, w i) / (U.card : ℝ) ≠ (∑ i ∈ V, w i) / (V.card : ℝ)) :
    ((I.toList.permutations.toFinset.filter
      (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum)).card : ℝ) =
      ∑ A ∈ I.powerset.filter (fun A => d ∈ A),
        if 0 < ∑ i ∈ A, w i then ((A.card - 1).factorial : ℝ) *
          (((I \ A).toList.permutations.toFinset.filter
            (fun z => ∀ k : ℕ, 0 < k → k ≤ z.length → 0 < ((z.take k).map w).sum)).card : ℝ)
        else 0 := by
  have h := card_good_words_eq_sum I d w hd hgen
  exact_mod_cast h
theorem gaussian_card_good_words_eq_sum_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Finset ι) (d : ι) (hd : d ∈ I) :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => gaussianReal 0 1),
      ((I.toList.permutations.toFinset.filter
        (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ) =
        ∑ A ∈ I.powerset.filter (fun A => d ∈ A),
          if 0 < ∑ i ∈ A, x i then ((A.card - 1).factorial : ℝ) *
            (((I \ A).toList.permutations.toFinset.filter
              (fun z => ∀ k : ℕ, 0 < k → k ≤ z.length → 0 < ((z.take k).map x).sum)).card : ℝ)
          else 0 := by
  filter_upwards [ArgmaxGaussianGenericPosition.disjoint_averages_generic_ae (ι := ι)] with x hx
  exact card_good_words_eq_sum_real I d x hd hx
end ArgmaxDistinguishedCountingIdentity
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace ArgmaxGaussianWordExchangeability
theorem gaussian_permutation_hasLaw (n : ℕ) (p : Equiv.Perm (Fin n)) :
    HasLaw (fun x : Fin n → ℝ => fun i => x (p i))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i : Fin n => fun x : Fin n → ℝ => x i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id)
  exact iIndepFun.hasLaw_pi
    (fun i => (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) (p i)).hasLaw)
    (hi.precomp p.injective)
theorem gaussian_permutation_integral (n : ℕ) (p : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    (∫ x, f (fun i => x (p i)) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  exact (gaussian_permutation_hasLaw n p).integral_comp hf.aestronglyMeasurable
lemma sum_permuted (n : ℕ) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    ∑ i, x (p i) = ∑ i, x i := Equiv.sum_comp p x
theorem weighted_event_permutation_integral (n : ℕ) (d : ℝ)
    (p : Equiv.Perm (Fin n)) (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (∫ x in {x : Fin n → ℝ | (fun i => x (p i)) ∈ A},
      Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∫ x in A, Real.exp (-d * ∑ i, x i)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let w : (Fin n → ℝ) → ℝ := fun x => Real.exp (-d * ∑ i, x i)
  have hw : Measurable w := by fun_prop
  have hpre : MeasurableSet {x : Fin n → ℝ | (fun i => x (p i)) ∈ A} :=
    hA.preimage (by fun_prop)
  rw [← integral_indicator hpre, ← integral_indicator hA]
  have heq (x : Fin n → ℝ) :
      {x : Fin n → ℝ | (fun i => x (p i)) ∈ A}.indicator w x =
        A.indicator w (fun i => x (p i)) := by
    simp [Set.indicator, w, sum_permuted]
  change (∫ x, {x : Fin n → ℝ | (fun i => x (p i)) ∈ A}.indicator w x
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = _
  simp_rw [heq]
  exact gaussian_permutation_integral n p (A.indicator w) (hw.indicator hA)
lemma measurableSet_positive_prefixes (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
theorem weighted_positive_prefixes_permutation (n : ℕ) (d : ℝ)
    (p : Equiv.Perm (Fin n)) :
    (∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x (p i)},
      Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  exact weighted_event_permutation_integral n d p _ (measurableSet_positive_prefixes n)
end ArgmaxGaussianWordExchangeability
namespace ArgmaxGaussianWordNormalization
lemma integrable_endpoint_weight (n : ℕ) (d : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-d * ∑ i, x i))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have h := Integrable.fintype_prod
    (μ := fun _ : Fin n => gaussianReal 0 1)
    (fun _ : Fin n => integrable_exp_mul_gaussianReal (-d))
  simpa only [← Real.exp_sum, ← Finset.mul_sum] using h
theorem weighted_good_permutation_count_integral (n : ℕ) (d : ℝ) :
    (∫ x : Fin n → ℝ,
      Real.exp (-d * ∑ i, x i) *
        ((Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
          ∀ k : Fin n, 0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x (p i))).card : ℝ)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
    (n.factorial : ℝ) *
      ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  classical
  let w : (Fin n → ℝ) → ℝ := fun x => Real.exp (-d * ∑ i, x i)
  let A : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun p =>
    {x : Fin n → ℝ | ∀ k : Fin n,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x (p i)}
  have hA (p : Equiv.Perm (Fin n)) : MeasurableSet (A p) :=
    (ArgmaxGaussianWordExchangeability.measurableSet_positive_prefixes n).preimage
      (by fun_prop)
  have hw : Integrable w (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    integrable_endpoint_weight n d
  have hpoint (x : Fin n → ℝ) :
      w x * ((Finset.univ.filter (fun p : Equiv.Perm (Fin n) => x ∈ A p)).card : ℝ) =
        ∑ p : Equiv.Perm (Fin n), (A p).indicator w x := by
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : x ∈ A p <;> simp [hp, Set.indicator]
  calc
    _ = ∫ x, ∑ p : Equiv.Perm (Fin n), (A p).indicator w x
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ p : Equiv.Perm (Fin n), ∫ x, (A p).indicator w x
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) :=
      integral_finsetSum Finset.univ (fun p _ => hw.indicator (hA p))
    _ = ∑ _p : Equiv.Perm (Fin n),
        ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
            0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
          Real.exp (-d * ∑ i, x i)
          ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_indicator (hA p)]
      exact ArgmaxGaussianWordExchangeability.weighted_positive_prefixes_permutation n d p
    _ = _ := by simp [Fintype.card_perm]
end ArgmaxGaussianWordNormalization
open scoped BigOperators Classical
namespace ArgmaxGaussianWordNormalization
theorem weighted_permutation_word_integral (n : ℕ) (d : ℝ)
    (p : Equiv.Perm (Fin n)) :
    (∫ x in {x : Fin n → ℝ | ∀ k : ℕ, 0 < k →
        k ≤ (List.ofFn (fun i => p i)).length →
        0 < (((List.ofFn (fun i => p i)).take k).map x).sum},
      Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  simp only [ArgmaxWordPrefixBridge.positive_mapped_prefixes_ofFn_iff]
  exact ArgmaxGaussianWordExchangeability.weighted_positive_prefixes_permutation n d p
theorem weighted_good_word_count_integral (n : ℕ) (d : ℝ) :
    (∫ x : Fin n → ℝ,
      Real.exp (-d * ∑ i, x i) *
        (((Finset.univ : Finset (Fin n)).toList.permutations.toFinset.filter
          (fun v => ∀ k : ℕ, 0 < k → k ≤ v.length →
            0 < ((v.take k).map x).sum)).card : ℝ)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
    (n.factorial : ℝ) *
      ∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  calc
    _ = ∫ x : Fin n → ℝ, Real.exp (-d * ∑ i, x i) *
          ((Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
            ∀ k : Fin n, 0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x (p i))).card : ℝ)
          ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [ArgmaxGoodWordInterface.card_good_words_univ_eq_perm_filter x])
    _ = _ := weighted_good_permutation_count_integral n d
end ArgmaxGaussianWordNormalization
namespace ArgmaxIntegratedDistinguishedCount
lemma continuous_word_sum {ι : Type*} (l : List ι) :
    Continuous (fun x : ι → ℝ => (l.map x).sum) := by
  induction l with
  | nil => simpa using (continuous_const : Continuous (fun _ : ι → ℝ => (0 : ℝ)))
  | cons i l ih =>
    change Continuous (fun x : ι → ℝ => x i + (l.map x).sum)
    exact (continuous_apply i).add ih
lemma measurableSet_word_positive_prefixes {ι : Type*} [Fintype ι] (l : List ι) :
    MeasurableSet {x : ι → ℝ | ∀ k : ℕ, 0 < k → k ≤ l.length →
      0 < ((l.take k).map x).sum} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : 0 < k ∧ k ≤ l.length
  · simpa only [hk.1, hk.2, true_implies] using
      (isOpen_lt continuous_const (continuous_word_sum (l.take k))).measurableSet
  · have heq : {x : ι → ℝ | 0 < k → k ≤ l.length →
        0 < ((l.take k).map x).sum} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro h0 hlen
      exact (hk ⟨h0, hlen⟩).elim
    rw [heq]
    exact MeasurableSet.univ
lemma integrable_weighted_good_subset_count (n : ℕ) (d : ℝ) (A : Finset (Fin n)) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-d * ∑ i, x i) *
      ((A.toList.permutations.toFinset.filter (fun l =>
        ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  classical
  let w : (Fin n → ℝ) → ℝ := fun x => Real.exp (-d * ∑ i, x i)
  let E : List (Fin n) → Set (Fin n → ℝ) := fun l =>
    {x | ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum}
  have hw := ArgmaxGaussianWordNormalization.integrable_endpoint_weight n d
  have hE (l : List (Fin n)) : MeasurableSet (E l) :=
    measurableSet_word_positive_prefixes l
  have hpoint (x : Fin n → ℝ) :
      w x * ((A.toList.permutations.toFinset.filter (fun l => x ∈ E l)).card : ℝ) =
        ∑ l ∈ A.toList.permutations.toFinset, (E l).indicator w x := by
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : x ∈ E l <;> simp [hl, Set.indicator]
  have hi : Integrable
      (fun x => ∑ l ∈ A.toList.permutations.toFinset, (E l).indicator w x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    integrable_finsetSum _ (fun l _ => hw.indicator (hE l))
  exact hi.congr (Filter.Eventually.of_forall (fun x => (hpoint x).symm))
lemma integrable_weighted_positive_subset_good_count (n : ℕ) (d : ℝ)
    (A : Finset (Fin n)) (c : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-d * ∑ i, x i) *
      (if 0 < ∑ i ∈ A, x i then c *
        ((((Finset.univ : Finset (Fin n)) \ A).toList.permutations.toFinset.filter (fun l =>
          ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ)
        else 0))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  classical
  have hE : MeasurableSet {x : Fin n → ℝ | 0 < ∑ i ∈ A, x i} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hi := ((integrable_weighted_good_subset_count n d (Finset.univ \ A)).const_mul c).indicator hE
  apply hi.congr
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hx : 0 < ∑ i ∈ A, x i <;> simp [Set.indicator, hx, mul_left_comm])
theorem weighted_good_count_eq_sum_integrals (n : ℕ) (d : ℝ) (dist : Fin n) :
    (n.factorial : ℝ) *
      (∫ x in {x : Fin n → ℝ | ∀ k : Fin n,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun A => dist ∈ A),
        ∫ x : Fin n → ℝ, Real.exp (-d * ∑ i, x i) *
          (if 0 < ∑ i ∈ A, x i then ((A.card - 1).factorial : ℝ) *
            ((((Finset.univ : Finset (Fin n)) \ A).toList.permutations.toFinset.filter (fun l =>
              ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ)
            else 0) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  classical
  rw [← ArgmaxGaussianWordNormalization.weighted_good_word_count_integral n d]
  calc
    _ = ∫ x : Fin n → ℝ,
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun A => dist ∈ A),
          Real.exp (-d * ∑ i, x i) *
            (if 0 < ∑ i ∈ A, x i then ((A.card - 1).factorial : ℝ) *
              ((((Finset.univ : Finset (Fin n)) \ A).toList.permutations.toFinset.filter (fun l =>
                ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ)
              else 0) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [ArgmaxDistinguishedCountingIdentity.gaussian_card_good_words_eq_sum_ae
        (Finset.univ : Finset (Fin n)) dist (Finset.mem_univ dist)] with x hx
      rw [hx, Finset.mul_sum]
    _ = _ := integral_finsetSum _ (fun A _ =>
      integrable_weighted_positive_subset_good_count n d A ((A.card - 1).factorial : ℝ))
end ArgmaxIntegratedDistinguishedCount
open scoped BigOperators Classical
namespace ArgmaxGoodWordRelabelingRoot
lemma exists_list_preimage {α β : Type*} (e : α → β) (A : Set α) (l : List β)
    (h : ∀ b ∈ l, ∃ a ∈ A, e a = b) :
    ∃ v : List α, v.map e = l ∧ ∀ a ∈ v, a ∈ A := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨a, ha, he⟩ := h b (by simp)
    obtain ⟨v, hv, hvA⟩ := ih (fun c hc => h c (by simp [hc]))
    refine ⟨a :: v, by simp [he, hv], ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · exact hvA c hc
theorem card_good_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (e : α → β) (he : Function.Injective e) (w : β → ℝ) :
    (((A.image e).toList.permutations.toFinset.filter (fun l =>
      ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum)).card) =
    ((A.toList.permutations.toFinset.filter (fun l =>
      ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map (fun i => w (e i))).sum)).card) := by
  classical
  let G : Finset (List α) := A.toList.permutations.toFinset.filter (fun l =>
    ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map (fun i => w (e i))).sum)
  let H : Finset (List β) := (A.image e).toList.permutations.toFinset.filter (fun l =>
    ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map w).sum)
  have hfin (v : List α) : (v.map e).toFinset = v.toFinset.image e := by
    ext b
    simp
  have himage : H = G.image (List.map e) := by
    ext l
    constructor
    · intro hl
      obtain ⟨hnd, hlabels, hpos⟩ :=
        (ArgmaxGoodWordInterface.mem_good_words_iff (A.image e) w l).mp hl
      have hpre : ∀ b ∈ l, ∃ a ∈ (A : Set α), e a = b := by
        intro b hb
        exact Finset.mem_image.mp (by rw [← hlabels]; exact List.mem_toFinset.mpr hb)
      obtain ⟨v, hmap, _⟩ := exists_list_preimage e (A : Set α) l hpre
      refine Finset.mem_image.mpr ⟨v, ?_, hmap⟩
      apply (ArgmaxGoodWordInterface.mem_good_words_iff A (fun i => w (e i)) v).mpr
      refine ⟨List.Nodup.of_map e (hmap.symm ▸ hnd), ?_, ?_⟩
      · apply Finset.image_injective he
        rw [← hfin, hmap, hlabels]
      · intro k hk hlen
        have hp := hpos k hk (by simpa only [← hmap, List.length_map] using hlen)
        simpa only [← hmap, ← List.map_take, List.map_map, Function.comp_def] using hp
    · intro hl
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨hnd, hlabels, hpos⟩ :=
        (ArgmaxGoodWordInterface.mem_good_words_iff A (fun i => w (e i)) v).mp hv
      apply (ArgmaxGoodWordInterface.mem_good_words_iff (A.image e) w _).mpr
      refine ⟨hnd.map he, by rw [hfin, hlabels], ?_⟩
      intro k hk hlen
      have hp := hpos k hk (by simpa only [List.length_map] using hlen)
      simpa only [← List.map_take, List.map_map, Function.comp_def] using hp
  change H.card = G.card
  rw [himage, Finset.card_image_of_injective _ he.list_map]
theorem card_good_subset_eq_subtype {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (x : ι → ℝ) :
    ((A.toList.permutations.toFinset.filter (fun l =>
      ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card) =
    (((Finset.univ : Finset A).toList.permutations.toFinset.filter (fun l =>
      ∀ k : ℕ, 0 < k → k ≤ l.length →
        0 < ((l.take k).map (fun i : A => x i)).sum)).card) := by
  classical
  have himage : (Finset.univ : Finset A).image (fun i : A => (i : ι)) = A := by
    ext i
    simp
  have h := card_good_image (Finset.univ : Finset A)
    (fun i : A => (i : ι)) Subtype.val_injective x
  simpa only [himage] using h
end ArgmaxGoodWordRelabelingRoot
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace ArgmaxGeneralGoodNormalizationRoot
theorem weighted_good_word_count_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℝ) :
    (∫ x : ι → ℝ, Real.exp (-d * ∑ i, x i) *
      (((Finset.univ : Finset ι).toList.permutations.toFinset.filter (fun l =>
        ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ((Fintype.card ι).factorial : ℝ) *
      ∫ x in {x : Fin (Fintype.card ι) → ℝ | ∀ k : Fin (Fintype.card ι),
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i)
        ∂Measure.pi (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let f : (ι → ℝ) → ℝ := fun x => Real.exp (-d * ∑ i, x i) *
    (((Finset.univ : Finset ι).toList.permutations.toFinset.filter (fun l =>
      ∀ k : ℕ, 0 < k → k ≤ l.length → 0 < ((l.take k).map x).sum)).card : ℝ)
  have himage : (Finset.univ : Finset (Fin (Fintype.card ι))).image e =
      (Finset.univ : Finset ι) := by
    ext i
    simp
  have hpoint (y : Fin (Fintype.card ι) → ℝ) :
      f ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) y) =
        Real.exp (-d * ∑ i, y i) *
          (((Finset.univ : Finset (Fin (Fintype.card ι))).toList.permutations.toFinset.filter
            (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length →
              0 < ((l.take k).map y).sum)).card : ℝ) := by
    let x : ι → ℝ := (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) y
    have hx (j : Fin (Fintype.card ι)) : x (e j) = y j :=
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e y j
    have hxy : (fun j => x (e j)) = y := funext hx
    have hs : (∑ i, x i) = ∑ j, y j := by
      rw [← Equiv.sum_comp e x]
      exact congrArg (fun z : Fin (Fintype.card ι) → ℝ => ∑ j, z j) hxy
    have hc := ArgmaxGoodWordRelabelingRoot.card_good_image
      (Finset.univ : Finset (Fin (Fintype.card ι))) e e.injective x
    rw [himage, hxy] at hc
    change Real.exp (-d * ∑ i, x i) * _ = _
    rw [hs, hc]
  calc
    _ = ∫ y : Fin (Fintype.card ι) → ℝ,
        f ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) y)
        ∂Measure.pi (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1) :=
      ((measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e).integral_comp' f).symm
    _ = _ := by
      simp_rw [hpoint]
      exact ArgmaxGaussianWordNormalization.weighted_good_word_count_integral (Fintype.card ι) d
end ArgmaxGeneralGoodNormalizationRoot
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace ArgmaxGaussianFiniteSumLaw
lemma gaussian_finite_sum_hasLaw {ι : Type*} [Fintype ι] (d : ℝ) :
    HasLaw (fun x : ι → ℝ => ∑ i, x i)
      (gaussianReal (-(Fintype.card ι : ℝ) * d) (Fintype.card ι : ℝ≥0))
      (Measure.pi (fun _ : ι => gaussianReal (-d) 1)) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply, charFun_gaussianReal, Finset.prod_const,
    Finset.card_univ]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
theorem centered_gaussian_finite_sum_hasLaw {ι : Type*} [Fintype ι] :
    HasLaw (fun x : ι → ℝ => ∑ i, x i)
      (gaussianReal 0 (Fintype.card ι : ℝ≥0))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [neg_zero, mul_zero] using gaussian_finite_sum_hasLaw (ι := ι) 0
end ArgmaxGaussianFiniteSumLaw
namespace ArgmaxGaussianSubsetFactorization
theorem gaussian_partition_integral {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p]
    (f : ({i : ι // p i} → ℝ) → ℝ)
    (g : ({i : ι // ¬ p i} → ℝ) → ℝ) :
    (∫ x : ι → ℝ, f (fun i => x i) * g (fun i => x i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (∫ x, f x ∂Measure.pi (fun _ : {i : ι // p i} => gaussianReal 0 1)) *
      (∫ x, g x ∂Measure.pi (fun _ : {i : ι // ¬ p i} => gaussianReal 0 1)) := by
  calc
    _ = ∫ z : ({i : ι // p i} → ℝ) × ({i : ι // ¬ p i} → ℝ), f z.1 * g z.2
        ∂((Measure.pi (fun _ : {i : ι // p i} => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : {i : ι // ¬ p i} => gaussianReal 0 1))) := by
      exact (measurePreserving_piEquivPiSubtypeProd
        (fun _ : ι => gaussianReal 0 1) p).integral_comp'
          (fun z : ({i : ι // p i} → ℝ) × ({i : ι // ¬ p i} → ℝ) => f z.1 * g z.2)
    _ = _ := integral_prod_mul f g
theorem weighted_positive_subset_integral {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (d : ℝ)
    (G : ({i : ι // ¬ p i} → ℝ) → ℝ) :
    (∫ x : ι → ℝ, Real.exp (-d * ∑ i, x i) *
        (if 0 < ∑ i : {i : ι // p i}, x i then (1 : ℝ) else 0) *
        G (fun i => x i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y)
        ∂gaussianReal 0 (Fintype.card {i : ι // p i} : NNReal)) *
      (∫ x : {i : ι // ¬ p i} → ℝ, Real.exp (-d * ∑ i, x i) * G x
        ∂Measure.pi (fun _ : {i : ι // ¬ p i} => gaussianReal 0 1)) := by
  let f : ({i : ι // p i} → ℝ) → ℝ := fun x =>
    Real.exp (-d * ∑ i, x i) * (if 0 < ∑ i, x i then (1 : ℝ) else 0)
  let g : ({i : ι // ¬ p i} → ℝ) → ℝ := fun x =>
    Real.exp (-d * ∑ i, x i) * G x
  have hf : (∫ x, f x ∂Measure.pi (fun _ : {i : ι // p i} => gaussianReal 0 1)) =
      ∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y)
        ∂gaussianReal 0 (Fintype.card {i : ι // p i} : NNReal) := by
    rw [← integral_indicator measurableSet_Ioi]
    have hmeas : Measurable ((Set.Ioi (0 : ℝ)).indicator (fun y => Real.exp (-d * y))) :=
      (by fun_prop : Measurable (fun y : ℝ => Real.exp (-d * y))).indicator measurableSet_Ioi
    have h := (ArgmaxGaussianFiniteSumLaw.centered_gaussian_finite_sum_hasLaw
      (ι := {i : ι // p i})).integral_comp hmeas.aestronglyMeasurable
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [Function.comp_def, f]
    by_cases hx : 0 < ∑ i, x i <;> simp [Set.indicator, hx]
  calc
    _ = ∫ x : ι → ℝ, f (fun i => x i) * g (fun i => x i)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hs := Fintype.sum_subtype_add_sum_subtype p x
      dsimp only [f, g]
      rw [← hs, mul_add, Real.exp_add]
      ring
    _ = _ := by rw [gaussian_partition_integral, hf]
end ArgmaxGaussianSubsetFactorization
namespace ArgmaxGaussianSubsetCountRoot
theorem weighted_positive_subset_good_count_integral
    (n : ℕ) (d c : ℝ) (A : Finset (Fin n)) :
    (∫ x : Fin n → ℝ, Real.exp (-d * ∑ i, x i) *
      (if 0 < ∑ i ∈ A, x i then c *
        ((((Finset.univ : Finset (Fin n)) \ A).toList.permutations.toFinset.filter
          (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length →
            0 < ((l.take k).map x).sum)).card : ℝ)
        else 0) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      c * ((n - A.card).factorial : ℝ) *
        (∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (A.card : NNReal)) *
        (∫ x in {x : Fin (n - A.card) → ℝ | ∀ k : Fin (n - A.card),
          0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
          Real.exp (-d * ∑ i, x i)
          ∂Measure.pi (fun _ : Fin (n - A.card) => gaussianReal 0 1)) := by
  classical
  let J := {i : Fin n // i ∉ A}
  let G : (J → ℝ) → ℝ := fun x =>
    (((Finset.univ : Finset J).toList.permutations.toFinset.filter
      (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length →
        0 < ((l.take k).map x).sum)).card : ℝ)
  have himage : (Finset.univ : Finset J).image (fun i : J => (i : Fin n)) =
      (Finset.univ : Finset (Fin n)) \ A := by
    ext i
    simp [J]
  have hgood (x : Fin n → ℝ) :
      ((((Finset.univ : Finset (Fin n)) \ A).toList.permutations.toFinset.filter
        (fun l => ∀ k : ℕ, 0 < k → k ≤ l.length →
          0 < ((l.take k).map x).sum)).card : ℝ) = G (fun i => x i) := by
    have hc := ArgmaxGoodWordRelabelingRoot.card_good_image (Finset.univ : Finset J)
      (fun i : J => (i : Fin n)) Subtype.val_injective x
    rw [himage] at hc
    simpa only [G] using congrArg (fun m : ℕ => (m : ℝ)) hc
  have hAc : Fintype.card {i : Fin n // i ∈ A} = A.card := Fintype.card_coe A
  have hJc : Fintype.card J = n - A.card := by
    simp only [J, Fintype.card_subtype_compl, hAc, Fintype.card_fin]
  let u : ℕ → ℝ := fun m =>
    ∫ x in {x : Fin m → ℝ | ∀ k : Fin m,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
      Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  have hnorm : (∫ x : J → ℝ, Real.exp (-d * ∑ i, x i) * G x
      ∂Measure.pi (fun _ : J => gaussianReal 0 1)) =
      ((Fintype.card J).factorial : ℝ) * u (Fintype.card J) :=
    ArgmaxGeneralGoodNormalizationRoot.weighted_good_word_count_integral (ι := J) d
  have hsplit := ArgmaxGaussianSubsetFactorization.weighted_positive_subset_integral
    (fun i : Fin n => i ∈ A) d G
  rw [hnorm] at hsplit
  simp only [Fintype.card_eq_nat_card] at hAc hJc
  simp_rw [Fintype.card_eq_nat_card, hAc, hJc] at hsplit
  calc
    _ = c * ∫ x : Fin n → ℝ, Real.exp (-d * ∑ i, x i) *
        (if 0 < ∑ i : {i : Fin n // i ∈ A}, x i then (1 : ℝ) else 0) *
        G (fun i => x i) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        have hs := Finset.sum_coe_sort A (fun i => x i)
        rw [hs]
        by_cases hp : 0 < ∑ i ∈ A, x i
        · simp only [hp, ↓reduceIte, mul_one]
          rw [hgood]
          ring
        · simp only [hp, ↓reduceIte, mul_zero, zero_mul])
    _ = _ := by
      change c * _ = c * ((n - A.card).factorial : ℝ) * _ * u (n - A.card)
      convert congrArg (fun t : ℝ => c * t) hsplit using 1
      · congr 2
        funext x
        congr 5
        ext i
        simp
      · ring
end ArgmaxGaussianSubsetCountRoot
open scoped BigOperators
namespace ArgmaxSAFactorialCancellation
theorem choose_factorials_nat (n k : ℕ) (hk : k ≤ n) :
    n.choose k * k.factorial * (n - k).factorial = n.factorial :=
  Nat.choose_mul_factorial_mul_factorial hk
theorem choose_factorials_real (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by
  exact_mod_cast choose_factorials_nat n k hk
theorem weighted_range_sum (n : ℕ) (h u : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.factorial : ℝ) *
      ((n - k).factorial : ℝ) * h (k + 1) * u (n - k)) =
      (n.factorial : ℝ) * ∑ k ∈ Finset.range (n + 1), h (k + 1) * u (n - k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [choose_factorials_real n k (by have := Finset.mem_range.mp hk; omega)]
  ring
theorem cancel_factorial (n : ℕ) (a S : ℝ)
    (heq : ((n + 1).factorial : ℝ) * a = (n.factorial : ℝ) * S) :
    ((n : ℝ) + 1) * a = S := by
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have heq' : (n.factorial : ℝ) * (((n : ℝ) + 1) * a) =
      (n.factorial : ℝ) * S := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at heq
    nlinarith [heq]
  exact mul_left_cancel₀ hfac heq'
theorem range_sum_eq_antidiagonal (n : ℕ) (h u : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), h (k + 1) * u (n - k)) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2 := by
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k j => h (k + 1) * u j) n).symm
theorem recurrence_of_factorial_weighted_sum (n : ℕ) (h u : ℕ → ℝ)
    (heq : ((n + 1).factorial : ℝ) * u (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.factorial : ℝ) *
        ((n - k).factorial : ℝ) * h (k + 1) * u (n - k)) :
    ((n : ℝ) + 1) * u (n + 1) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2 := by
  rw [weighted_range_sum] at heq
  exact (cancel_factorial n (u (n + 1)) _ heq).trans (range_sum_eq_antidiagonal n h u)
end ArgmaxSAFactorialCancellation
namespace ArgmaxSASubsetGrouping
theorem distinguished_subsets_eq_insert_image
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (hd : d ∈ I) :
    I.powerset.filter (fun A => d ∈ A) = (I.erase d).powerset.image (insert d) := by
  classical
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hAI, hdA⟩
    refine ⟨A.erase d, ?_, Finset.insert_erase hdA⟩
    intro i hi
    obtain ⟨hid, hiA⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_erase.mpr ⟨hid, hAI hiA⟩
  · rintro ⟨B, hB, rfl⟩
    refine ⟨Finset.insert_subset hd (hB.trans (Finset.erase_subset _ _)), Finset.mem_insert_self _ _⟩
theorem sum_distinguished_subsets_by_card
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (hd : d ∈ I)
    (f : ℕ → ℝ) :
    (∑ A ∈ I.powerset.filter (fun A => d ∈ A), f A.card) =
      ∑ k ∈ Finset.range I.card, ((I.card - 1).choose k : ℝ) * f (k + 1) := by
  classical
  rw [distinguished_subsets_eq_insert_image I d hd, Finset.sum_image]
  · calc
      (∑ A ∈ (I.erase d).powerset, f (insert d A).card) =
          ∑ A ∈ (I.erase d).powerset, f (A.card + 1) := by
        apply Finset.sum_congr rfl
        intro A hA
        have hdA : d ∉ A := fun h => Finset.notMem_erase d I (Finset.mem_powerset.mp hA h)
        rw [Finset.card_insert_of_notMem hdA]
      _ = _ := by
        rw [Finset.sum_powerset]
        have hpos : 0 < I.card := Finset.card_pos.mpr ⟨d, hd⟩
        have hcard : I.card - 1 + 1 = I.card := by omega
        calc
          (∑ k ∈ Finset.range ((I.erase d).card + 1),
              ∑ A ∈ Finset.powersetCard k (I.erase d), f (A.card + 1)) =
              ∑ k ∈ Finset.range ((I.erase d).card + 1),
                (((I.erase d).card).choose k : ℝ) * f (k + 1) := by
            apply Finset.sum_congr rfl
            intro k _
            simpa only [nsmul_eq_mul] using
              Finset.sum_powersetCard k (I.erase d) (fun j => f (j + 1))
          _ = _ := by rw [Finset.card_erase_of_mem hd, hcard]
  · intro A hA B hB heq
    have hdA : d ∉ A := fun h => Finset.notMem_erase d I (Finset.mem_powerset.mp hA h)
    have hdB : d ∉ B := fun h => Finset.notMem_erase d I (Finset.mem_powerset.mp hB h)
    simpa [Finset.erase_insert, hdA, hdB] using congrArg (fun S : Finset α => S.erase d) heq
theorem distinguished_subset_factorial_sum
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (hd : d ∈ I)
    (n : ℕ) (hI : I.card = n + 1) (h u : ℕ → ℝ) :
    (∑ A ∈ I.powerset.filter (fun A => d ∈ A),
      ((A.card - 1).factorial : ℝ) * ((I.card - A.card).factorial : ℝ) *
        h A.card * u (I.card - A.card)) =
      (n.factorial : ℝ) *
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2 := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k.factorial : ℝ) *
          ((n - k).factorial : ℝ) * h (k + 1) * u (n - k) := by
      rw [sum_distinguished_subsets_by_card I d hd
        (fun k => ((k - 1).factorial : ℝ) * ((I.card - k).factorial : ℝ) *
          h k * u (I.card - k))]
      simp only [hI, Nat.add_sub_cancel, Nat.add_sub_add_right]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1), h (k + 1) * u (n - k) :=
      ArgmaxSAFactorialCancellation.weighted_range_sum n h u
    _ = _ := by rw [ArgmaxSAFactorialCancellation.range_sum_eq_antidiagonal]
theorem recurrence_of_distinguished_subset_sum
    {α : Type*} [DecidableEq α] (I : Finset α) (d : α) (hd : d ∈ I)
    (n : ℕ) (hI : I.card = n + 1) (h u : ℕ → ℝ)
    (heq : ((n + 1).factorial : ℝ) * u (n + 1) =
      ∑ A ∈ I.powerset.filter (fun A => d ∈ A),
        ((A.card - 1).factorial : ℝ) * ((I.card - A.card).factorial : ℝ) *
          h A.card * u (I.card - A.card)) :
    ((n : ℝ) + 1) * u (n + 1) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2 := by
  exact ArgmaxSAFactorialCancellation.cancel_factorial n (u (n + 1)) _
    (heq.trans (distinguished_subset_factorial_sum I d hd n hI h u))
end ArgmaxSASubsetGrouping
namespace ArgmaxActualWeightedSA
theorem weighted_gaussian_survival_recurrence (d : ℝ) (n : ℕ) :
    let u : ℕ → ℝ := fun m =>
      ∫ x in {x : Fin m → ℝ | ∀ k : Fin m,
        0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
        Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
    let h : ℕ → ℝ := fun m =>
      ∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (m : NNReal)
    ((n : ℝ) + 1) * u (n + 1) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2 := by
  classical
  let u : ℕ → ℝ := fun m =>
    ∫ x in {x : Fin m → ℝ | ∀ k : Fin m,
      0 < ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), x i},
      Real.exp (-d * ∑ i, x i) ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let h : ℕ → ℝ := fun m =>
    ∫ y in Set.Ioi (0 : ℝ), Real.exp (-d * y) ∂gaussianReal 0 (m : NNReal)
  change ((n : ℝ) + 1) * u (n + 1) =
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, h (ij.1 + 1) * u ij.2
  let dist : Fin (n + 1) := 0
  have heq : ((n + 1).factorial : ℝ) * u (n + 1) =
      ∑ A ∈ (Finset.univ : Finset (Fin (n + 1))).powerset.filter (fun A => dist ∈ A),
        ((A.card - 1).factorial : ℝ) * (((n + 1) - A.card).factorial : ℝ) *
          h A.card * u ((n + 1) - A.card) := by
    calc
      _ = _ := ArgmaxIntegratedDistinguishedCount.weighted_good_count_eq_sum_integrals
        (n + 1) d dist
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        exact ArgmaxGaussianSubsetCountRoot.weighted_positive_subset_good_count_integral
          (n + 1) d ((A.card - 1).factorial : ℝ) A
  have hrec := ArgmaxSASubsetGrouping.recurrence_of_distinguished_subset_sum
    (Finset.univ : Finset (Fin (n + 1))) dist (Finset.mem_univ dist) n (by simp) h u
  exact hrec (by simpa only [Finset.card_univ, Fintype.card_fin] using heq)
end ArgmaxActualWeightedSA
namespace OMA.R_mo_142880_R1
lemma finite_gaussian_recurrence : H1 := by
  intro d _hd
  dsimp only
  intro n
  exact ArgmaxActualWeightedSA.weighted_gaussian_survival_recurrence d n
theorem main_of_continuous : H2 → type_of% @OMA.S_mo_142880.main := by
  intro hcontinuous
  exact main finite_gaussian_recurrence hcontinuous
end OMA.R_mo_142880_R1
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology
namespace ArgmaxContinuousSupremumFunctional
theorem isLUB_range_denseSeq_of_bddAbove
    {K : Type*} [TopologicalSpace K] [SeparableSpace K] [Nonempty K]
    (f : K → ℝ) (hf : Continuous f) (hb : BddAbove (Set.range f)) :
    IsLUB (Set.range f) (⨆ n : ℕ, f (denseSeq K n)) := by
  have hbounded : BddAbove (Set.range (fun n : ℕ => f (denseSeq K n))) := by
    apply hb.mono
    rintro y ⟨n, rfl⟩
    exact Set.mem_range_self (denseSeq K n)
  have hupper (t : K) : f t ≤ ⨆ n : ℕ, f (denseSeq K n) :=
    (denseRange_denseSeq K).induction_on
      (p := fun t => f t ≤ ⨆ n : ℕ, f (denseSeq K n)) t
      (isClosed_le hf continuous_const) (fun n => le_ciSup hbounded n)
  refine ⟨?_, ?_⟩
  · rintro y ⟨t, rfl⟩
    exact hupper t
  · intro y hy
    exact ciSup_le (fun n => hy (Set.mem_range_self (denseSeq K n)))
lemma measurable_dense_sup
    (K : Type*) [TopologicalSpace K] [SeparableSpace K] [Nonempty K] :
    Measurable (fun f : K → ℝ => ⨆ n : ℕ, f (denseSeq K n)) :=
  Measurable.iSup (fun n => measurable_pi_apply (denseSeq K n))
theorem ae_dense_sup_eq_version
    {K Ω : Type*} [TopologicalSpace K] [SeparableSpace K] [Nonempty K]
    [MeasurableSpace Ω] (P : Measure Ω) (X : K → Ω → ℝ) (M : Ω → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hM : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t => X t ω)) (M ω)) :
    (fun ω => ⨆ n : ℕ, X (denseSeq K n) ω) =ᵐ[P] M := by
  filter_upwards [hcont, hM] with ω hc hm
  exact (isLUB_range_denseSeq_of_bddAbove (fun t => X t ω) hc ⟨M ω, hm.1⟩).unique hm
theorem aemeasurable_supremum_version
    {K Ω : Type*} [TopologicalSpace K] [SeparableSpace K] [Nonempty K]
    [MeasurableSpace Ω] (P : Measure Ω) (X : K → Ω → ℝ) (M : Ω → ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hM : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t => X t ω)) (M ω)) :
    AEMeasurable M P :=
  (AEMeasurable.iSup (fun n => hX (denseSeq K n))).congr
    (ae_dense_sup_eq_version P X M hcont hM)
theorem indepFun_supremum_versions
    {K J Ω : Type*} [TopologicalSpace K] [SeparableSpace K] [Nonempty K]
    [TopologicalSpace J] [SeparableSpace J] [Nonempty J] [MeasurableSpace Ω]
    (P : Measure Ω) (X : K → Ω → ℝ) (Z : J → Ω → ℝ) (A C : Ω → ℝ)
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Z t ω) P)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hA : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t => X t ω)) (A ω))
    (hC : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t => Z t ω)) (C ω)) :
    IndepFun A C P := by
  have hi := hind.comp (measurable_dense_sup K) (measurable_dense_sup J)
  exact hi.congr (ae_dense_sup_eq_version P X A hXc hA)
    (ae_dense_sup_eq_version P Z C hZc hC)
end ArgmaxContinuousSupremumFunctional
open scoped NNReal
namespace ArgmaxBrownianMaximumIndependence
lemma ae_past_dense_sup_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (s : ℝ≥0) (d : ℝ) (A : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω)) :
    (fun ω => ⨆ n : ℕ, B (denseSeq (Set.Iic s) n) ω -
      d * (((denseSeq (Set.Iic s) n : Set.Iic s) : ℝ≥0) : ℝ)) =ᵐ[P] A := by
  have hc : ∀ᵐ ω ∂P, Continuous (fun t : Set.Iic s => B t ω - d * ((t : ℝ≥0) : ℝ)) := by
    filter_upwards [hB.cont] with ω hω
    exact (hω.comp continuous_subtype_val).sub
      (continuous_const.mul (NNReal.continuous_coe.comp continuous_subtype_val))
  have hl : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : Set.Iic s =>
      B t ω - d * ((t : ℝ≥0) : ℝ))) (A ω) := by
    filter_upwards [hA] with ω ha
    have heq : Set.range (fun t : Set.Iic s => B t ω - d * ((t : ℝ≥0) : ℝ)) =
        ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, ⟨by simp, t.property⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht.2⟩, rfl⟩
    rw [heq]
    exact ha
  exact ArgmaxContinuousSupremumFunctional.ae_dense_sup_eq_version P _ A hc hl
lemma ae_future_dense_sup_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (s : ℝ≥0) (d : ℝ) (Y : Ω → ℝ)
    (hY : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 =>
      B (s + t) ω - B s ω - d * (t : ℝ))) (Y ω)) :
    (fun ω => ⨆ n : ℕ, B (s + denseSeq ℝ≥0 n) ω - B s ω -
      d * (denseSeq ℝ≥0 n : ℝ)) =ᵐ[P] Y := by
  have hc : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => B (s + t) ω - B s ω - d * (t : ℝ)) := by
    filter_upwards [(hB.shift s).cont] with ω hω
    exact hω.sub (continuous_const.mul NNReal.continuous_coe)
  exact ArgmaxContinuousSupremumFunctional.ae_dense_sup_eq_version P _ Y hc hY
theorem past_future_maximum_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (s : ℝ≥0) (d : ℝ) (A Y : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω))
    (hY : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 =>
      B (s + t) ω - B s ω - d * (t : ℝ))) (Y ω)) :
    IndepFun (fun ω => (A ω, B s ω - d * (s : ℝ))) Y P := by
  let F : (ℝ≥0 → ℝ) → ℝ := fun f => ⨆ n : ℕ,
    f (denseSeq ℝ≥0 n) - d * (denseSeq ℝ≥0 n : ℝ)
  let G : (Set.Iic s → ℝ) → ℝ × ℝ := fun f =>
    (⨆ n : ℕ, f (denseSeq (Set.Iic s) n) -
      d * (((denseSeq (Set.Iic s) n : Set.Iic s) : ℝ≥0) : ℝ),
      f ⟨s, by simp⟩ - d * (s : ℝ))
  have hF : Measurable F := Measurable.iSup (fun n => (measurable_pi_apply _).sub_const _)
  have hG : Measurable G := by
    dsimp only [G]
    apply Measurable.prodMk
    · exact Measurable.iSup (fun n =>
        (measurable_pi_apply (denseSeq (Set.Iic s) n)).sub_const _)
    · exact (measurable_pi_apply (⟨s, by simp⟩ : Set.Iic s)).sub_const _
  have hi := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp hG hF
  apply hi.congr _ (ae_future_dense_sup_eq hB s d Y hY)
  filter_upwards [ae_past_dense_sup_eq hB s d A hA] with ω ha
  exact Prod.ext ha rfl
theorem arm_opposite_maximum_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B C : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hind : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (s : ℝ≥0) (d : ℝ) (A Y L : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω))
    (hY : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 =>
      B (s + t) ω - B s ω - d * (t : ℝ))) (Y ω))
    (hL : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => C t ω - d * (t : ℝ))) (L ω)) :
    IndepFun (fun ω => ((A ω, B s ω - d * (s : ℝ)), Y ω)) L P := by
  let F : (ℝ≥0 → ℝ) → ((ℝ × ℝ) × ℝ) := fun f =>
    ((⨆ n : ℕ, f (denseSeq (Set.Iic s) n) -
        d * (((denseSeq (Set.Iic s) n : Set.Iic s) : ℝ≥0) : ℝ), f s - d * (s : ℝ)),
      ⨆ n : ℕ, f (s + denseSeq ℝ≥0 n) - f s - d * (denseSeq ℝ≥0 n : ℝ))
  let G : (ℝ≥0 → ℝ) → ℝ := fun f => ⨆ n : ℕ,
    f (denseSeq ℝ≥0 n) - d * (denseSeq ℝ≥0 n : ℝ)
  have hF : Measurable F := by
    dsimp only [F]
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · exact Measurable.iSup (fun n =>
          (measurable_pi_apply ((denseSeq (Set.Iic s) n : Set.Iic s) : ℝ≥0)).sub_const _)
      · exact (measurable_pi_apply s).sub_const _
    · exact Measurable.iSup (fun n =>
        ((measurable_pi_apply (s + denseSeq ℝ≥0 n)).fun_sub (measurable_pi_apply s)).sub_const _)
  have hG : Measurable G := Measurable.iSup (fun n => (measurable_pi_apply _).sub_const _)
  have hi := hind.comp hF hG
  have hLc : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => C t ω - d * (t : ℝ)) := by
    filter_upwards [hC.cont] with ω hω
    exact hω.sub (continuous_const.mul NNReal.continuous_coe)
  apply hi.congr _ (ArgmaxContinuousSupremumFunctional.ae_dense_sup_eq_version P _ L hLc hL)
  filter_upwards [ae_past_dense_sup_eq hB s d A hA, ae_future_dense_sup_eq hB s d Y hY]
    with ω ha hy
  exact Prod.ext (Prod.ext ha rfl) hy
lemma past_maximum_measurable_and_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (s : ℝ≥0) (d : ℝ) (A : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω)) :
    AEMeasurable (fun ω => (A ω, B s ω - d * (s : ℝ))) P ∧
      (∀ᵐ ω ∂P, 0 ≤ A ω ∧ B s ω - d * (s : ℝ) ≤ A ω) := by
  have hm : AEMeasurable A P :=
    (AEMeasurable.iSup (fun n => (hB.aemeasurable (denseSeq (Set.Iic s) n)).sub_const _)).congr
      (ae_past_dense_sup_eq hB s d A hA)
  refine ⟨hm.prodMk ((hB.aemeasurable s).sub_const _), ?_⟩
  filter_upwards [hA, hB.eval_zero_ae_eq_zero] with ω ha hzero
  constructor
  · have hb := ha.1 (Set.mem_image_of_mem (fun t : ℝ≥0 => B t ω - d * (t : ℝ))
      (show (0 : ℝ≥0) ∈ Set.Icc 0 s by simp))
    simpa only [hzero, NNReal.coe_zero, mul_zero, sub_zero] using hb
  · exact ha.1 (Set.mem_image_of_mem _ (show s ∈ Set.Icc (0 : ℝ≥0) s by simp))
end ArgmaxBrownianMaximumIndependence
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ArgmaxExponentialMaxComparison
noncomputable def comparisonEvent (a s : ℝ) : Set (ℝ × ℝ) :=
  {p | max a p.2 < s + p.1}
lemma expMeasure_nullSingleton (r : ℝ) : NullSingletonClass (expMeasure r) := by
  unfold expMeasure gammaMeasure
  infer_instance
lemma expMeasure_real_Iic (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (expMeasure r).real (Iic a) = 1 - exp (-(r * a)) := by
  let := isProbabilityMeasure_expMeasure hr
  rw [← cdf_eq_real, cdf_expMeasure_eq hr, if_pos ha]
lemma expMeasure_real_Iio (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (expMeasure r).real (Iio a) = 1 - exp (-(r * a)) := by
  let := expMeasure_nullSingleton r
  rw [measureReal_congr Iio_ae_eq_Iic]
  exact expMeasure_real_Iic r a hr ha
lemma expMeasure_real_Ioi (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (expMeasure r).real (Ioi a) = exp (-(r * a)) := by
  let := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
    expMeasure_real_Iic r a hr ha]
  ring
lemma measurableSet_comparisonEvent (a s : ℝ) : MeasurableSet (comparisonEvent a s) := by
  exact measurableSet_lt (measurable_const.max measurable_snd)
    (measurable_const.add measurable_fst)
lemma comparison_measure_eq_integral (r a s : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    ((expMeasure r).prod (expMeasure r)).real (comparisonEvent a s) =
      ∫ y : ℝ in Ioi (a - s), 1 - exp (-(r * (s + y))) ∂expMeasure r := by
  let := isProbabilityMeasure_expMeasure hr
  have hE := measurableSet_comparisonEvent a s
  have hI : Integrable ((comparisonEvent a s).indicator (1 : ℝ × ℝ → ℝ))
      ((expMeasure r).prod (expMeasure r)) := (integrable_const 1).indicator hE
  rw [← integral_indicator_one hE]
  rw [integral_prod _ hI]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : a - s < y
  · have hy' : a < s + y := by linarith
    have hfun : (fun l : ℝ => (comparisonEvent a s).indicator (1 : ℝ × ℝ → ℝ) (y, l)) =
        (Iio (s + y)).indicator (1 : ℝ → ℝ) := by
      funext l
      simp [comparisonEvent, Set.indicator_apply, hy']
    rw [hfun, integral_indicator_one measurableSet_Iio]
    rw [expMeasure_real_Iio r (s + y) hr (by linarith)]
    simp [hy]
  · have hy' : ¬ a < s + y := by linarith
    have hfun : (fun l : ℝ => (comparisonEvent a s).indicator (1 : ℝ × ℝ → ℝ) (y, l)) = 0 := by
      funext l
      simp [comparisonEvent, hy']
    rw [hfun]
    change (∫ _ : ℝ, (0 : ℝ) ∂expMeasure r) = _
    rw [integral_zero]
    simp [hy]
lemma setIntegral_expMeasure_Ioi (r c : ℝ) (hr : 0 < r) (hc : 0 ≤ c) (f : ℝ → ℝ) :
    (∫ y in Ioi c, f y ∂expMeasure r) =
      ∫ y in Ioi c, (r * exp (-(r * y))) * f y := by
  change (∫ y in Ioi c, f y ∂volume.withDensity (exponentialPDF r)) = _
  have hm : Measurable (exponentialPDF r) := by
    unfold exponentialPDF
    fun_prop
  have ht : ∀ᵐ y ∂volume.restrict (Ioi c), exponentialPDF r y < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hm ht f measurableSet_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change (exponentialPDF r y).toReal * f y = (r * exp (-(r*y))) * f y
  rw [exponentialPDF_of_nonneg (hc.trans hy.le),
    ENNReal.toReal_ofReal (mul_nonneg hr.le (exp_pos _).le)]
lemma integral_rate_exp_Ioi (r c : ℝ) (hr : 0 < r) :
    (∫ y : ℝ in Ioi c, r * exp (-(r * y))) = exp (-(r * c)) := by
  simp_rw [← neg_mul]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -r < 0)]
  field_simp
lemma integral_comparison_density (r a s : ℝ) (hr : 0 < r) :
    (∫ y : ℝ in Ioi (a-s), (r * exp (-(r*y))) * (1 - exp (-(r*(s+y))))) =
      exp (-(r*(a-s))) * (1 - (1/2 : ℝ) * exp (-(r*a))) := by
  have hfun (y : ℝ) :
      (r * exp (-(r*y))) * (1 - exp (-(r*(s+y)))) =
        r * exp ((-r)*y) - (r * exp (-(r*s))) * exp ((-(2*r))*y) := by
    have hsum : exp (-(r*(s+y))) = exp (-(r*s)) * exp (-(r*y)) := by
      rw [← exp_add]
      congr 1
      ring
    have hsq : exp (-(r*y)) * exp (-(r*y)) = exp ((-(2*r))*y) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hsum, ← hsq]
    simp only [neg_mul]
    ring
  simp_rw [hfun]
  rw [integral_sub
    ((integrableOn_exp_mul_Ioi (by linarith : -r < 0) (a-s)).const_mul r)
    ((integrableOn_exp_mul_Ioi (by linarith : -(2*r) < 0) (a-s)).const_mul
      (r * exp (-(r*s))))]
  rw [integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -r < 0),
    integral_exp_mul_Ioi (by linarith : -(2*r) < 0)]
  have hexp : exp (-(r*s)) * exp ((-(2*r))*(a-s)) =
      exp (-(r*(a-s))) * exp (-(r*a)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hr0 : r ≠ 0 := ne_of_gt hr
  have heq : (-r) * (a-s) = -(r*(a-s)) := by ring
  rw [heq]
  field_simp
  have htwo : (-(2*r))*(a-s) = -(r*(a-s)*2) := by ring
  rw [htwo] at hexp
  nlinarith [hexp]
theorem comparison_measure_eq (r a s : ℝ) (hr : 0 < r) (ha : 0 ≤ a) (hs : s ≤ a) :
    ((expMeasure r).prod (expMeasure r)).real (comparisonEvent a s) =
      exp (-(r*(a-s))) * (1 - (1/2 : ℝ) * exp (-(r*a))) := by
  rw [comparison_measure_eq_integral r a s hr ha,
    setIntegral_expMeasure_Ioi r (a-s) hr (by linarith),
    integral_comparison_density r a s hr]
lemma comparison_value_eq_exp_form (r a s : ℝ) :
    exp (-(r*(a-s))) * (1 - (1/2 : ℝ) * exp (-(r*a))) =
      exp (r*s) * (exp (-(r*a)) - (1/2 : ℝ) * exp (-(2*r*a))) := by
  have hgap : exp (-(r*(a-s))) = exp (r*s) * exp (-(r*a)) := by
    rw [← exp_add]
    congr 1
    ring
  have hdouble : exp (-(2*r*a)) = exp (-(r*a)) * exp (-(r*a)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hgap, hdouble]
  ring
theorem comparison_measure_eq_exp_form (r a s : ℝ) (hr : 0 < r)
    (ha : 0 ≤ a) (hs : s ≤ a) :
    ((expMeasure r).prod (expMeasure r)).real (comparisonEvent a s) =
      exp (r*s) * (exp (-(r*a)) - (1/2 : ℝ) * exp (-(2*r*a))) := by
  rw [comparison_measure_eq r a s hr ha hs, comparison_value_eq_exp_form]
theorem comparison_measure_sandwich (r a s : ℝ) (hr : 0 < r)
    (ha : 0 ≤ a) (hs : s ≤ a) :
    (1/2 : ℝ) * exp (-(r*(a-s))) ≤
        ((expMeasure r).prod (expMeasure r)).real (comparisonEvent a s) ∧
      ((expMeasure r).prod (expMeasure r)).real (comparisonEvent a s) ≤
        exp (-(r*(a-s))) := by
  rw [comparison_measure_eq r a s hr ha hs]
  have hfactor : 0 < exp (-(r*(a-s))) := exp_pos _
  have hexp0 : 0 < exp (-(r*a)) := exp_pos _
  have hexp1 : exp (-(r*a)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  constructor <;> nlinarith
theorem indep_exp_comparison_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y L : Ω → ℝ)
    (hY : AEMeasurable Y μ) (hL : AEMeasurable L μ) (hIndep : IndepFun Y L μ)
    (r a s : ℝ) (hr : 0 < r) (ha : 0 ≤ a) (hs : s ≤ a)
    (hYlaw : μ.map Y = expMeasure r) (hLlaw : μ.map L = expMeasure r) :
    μ.real {ω | max a (L ω) < s + Y ω} =
      exp (-(r*(a-s))) * (1 - (1/2 : ℝ) * exp (-(r*a))) := by
  have hmap := hIndep.map_prod_eq_prod_map_map hY hL
  rw [hYlaw, hLlaw] at hmap
  have h := comparison_measure_eq r a s hr ha hs
  rw [← hmap, map_measureReal_apply_of_aemeasurable (hY.prodMk hL)
    (measurableSet_comparisonEvent a s)] at h
  exact h
end ArgmaxExponentialMaxComparison
namespace ArgmaxRandomThresholdExpComparison
lemma product_probability_eq_integral
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (r : ℝ) (hr : 0 < r) :
    (ν.prod ((expMeasure r).prod (expMeasure r))).real
      {q : (ℝ × ℝ) × (ℝ × ℝ) | max q.1.1 q.2.2 < q.1.2 + q.2.1} =
      ∫ p : ℝ × ℝ,
        ((expMeasure r).prod (expMeasure r)).real
          (ArgmaxExponentialMaxComparison.comparisonEvent p.1 p.2) ∂ν := by
  let := isProbabilityMeasure_expMeasure hr
  let E : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {q | max q.1.1 q.2.2 < q.1.2 + q.2.1}
  have hE : MeasurableSet E := by
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hi : Integrable (E.indicator (1 : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ))
      (ν.prod ((expMeasure r).prod (expMeasure r))) :=
    (integrable_const 1).indicator hE
  have hinner (p : ℝ × ℝ) :
      (∫ z : ℝ × ℝ, E.indicator (1 : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) (p, z)
        ∂((expMeasure r).prod (expMeasure r))) =
      ((expMeasure r).prod (expMeasure r)).real
        (ArgmaxExponentialMaxComparison.comparisonEvent p.1 p.2) := by
    exact integral_indicator_one (ArgmaxExponentialMaxComparison.measurableSet_comparisonEvent p.1 p.2)
  rw [← integral_indicator_one hE, integral_prod _ hi]
  simp_rw [hinner]
lemma integrable_product_probability
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (r : ℝ) (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      ((expMeasure r).prod (expMeasure r)).real
        (ArgmaxExponentialMaxComparison.comparisonEvent p.1 p.2)) ν := by
  let := isProbabilityMeasure_expMeasure hr
  let E : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {q | max q.1.1 q.2.2 < q.1.2 + q.2.1}
  have hE : MeasurableSet E := measurableSet_lt (by fun_prop) (by fun_prop)
  have hi : Integrable (E.indicator (1 : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ))
      (ν.prod ((expMeasure r).prod (expMeasure r))) :=
    (integrable_const 1).indicator hE
  have hinner (p : ℝ × ℝ) :
      (∫ z : ℝ × ℝ, E.indicator (1 : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) (p, z)
        ∂((expMeasure r).prod (expMeasure r))) =
      ((expMeasure r).prod (expMeasure r)).real
        (ArgmaxExponentialMaxComparison.comparisonEvent p.1 p.2) :=
    integral_indicator_one (ArgmaxExponentialMaxComparison.measurableSet_comparisonEvent p.1 p.2)
  simpa only [hinner] using hi.integral_prod_left
theorem product_random_threshold_sandwich
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (r : ℝ) (hr : 0 < r)
    (hsupport : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ p.2 ≤ p.1) :
    (1 / 2 : ℝ) * (∫ p : ℝ × ℝ, Real.exp (-(r * (p.1 - p.2))) ∂ν) ≤
        (ν.prod ((expMeasure r).prod (expMeasure r))).real
          {q : (ℝ × ℝ) × (ℝ × ℝ) | max q.1.1 q.2.2 < q.1.2 + q.2.1} ∧
      (ν.prod ((expMeasure r).prod (expMeasure r))).real
          {q : (ℝ × ℝ) × (ℝ × ℝ) | max q.1.1 q.2.2 < q.1.2 + q.2.1} ≤
        ∫ p : ℝ × ℝ, Real.exp (-(r * (p.1 - p.2))) ∂ν := by
  have hgap : Integrable (fun p : ℝ × ℝ => Real.exp (-(r * (p.1 - p.2)))) ν := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [hsupport] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hp.2)]
  have hint := integrable_product_probability ν r hr
  rw [product_probability_eq_integral ν r hr]
  constructor
  · rw [← integral_const_mul]
    apply integral_mono_ae (hgap.const_mul (1 / 2 : ℝ)) hint
    filter_upwards [hsupport] with p hp
    exact (ArgmaxExponentialMaxComparison.comparison_measure_sandwich r p.1 p.2 hr hp.1 hp.2).1
  · apply integral_mono_ae hint hgap
    filter_upwards [hsupport] with p hp
    exact (ArgmaxExponentialMaxComparison.comparison_measure_sandwich r p.1 p.2 hr hp.1 hp.2).2
lemma product_tie_measure_zero (r a s : ℝ) (hr : 0 < r) :
    ((expMeasure r).prod (expMeasure r)) {z : ℝ × ℝ | max a z.2 = s + z.1} = 0 := by
  let := isProbabilityMeasure_expMeasure hr
  let := ArgmaxExponentialMaxComparison.expMeasure_nullSingleton r
  have hE : MeasurableSet {z : ℝ × ℝ | max a z.2 = s + z.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  rw [Measure.prod_apply_symm hE]
  have hs (l : ℝ) : {y : ℝ | max a l = s + y} = {max a l - s} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor <;> intro h <;> linarith
  change (∫⁻ l : ℝ, (expMeasure r) {y : ℝ | max a l = s + y} ∂expMeasure r) = 0
  simp_rw [hs]
  simp
lemma random_product_tie_measure_zero
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (r : ℝ) (hr : 0 < r) :
    (ν.prod ((expMeasure r).prod (expMeasure r)))
      {q : (ℝ × ℝ) × (ℝ × ℝ) | max q.1.1 q.2.2 = q.1.2 + q.2.1} = 0 := by
  let := isProbabilityMeasure_expMeasure hr
  have hE : MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) |
      max q.1.1 q.2.2 = q.1.2 + q.2.1} := measurableSet_eq_fun (by fun_prop) (by fun_prop)
  rw [Measure.prod_apply hE]
  change (∫⁻ p : ℝ × ℝ, ((expMeasure r).prod (expMeasure r))
    {z : ℝ × ℝ | max p.1 z.2 = p.2 + z.1} ∂ν) = 0
  simp_rw [product_tie_measure_zero r _ _ hr]
  simp
end ArgmaxRandomThresholdExpComparison
namespace ArgmaxRandomThresholdExpComparison
theorem joint_random_threshold_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (A S Y L : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hPast : HasLaw (fun ω => (A ω, S ω)) ν P)
    (hJoint : HasLaw (fun ω => ((A ω, S ω), (Y ω, L ω)))
      (ν.prod ((expMeasure r).prod (expMeasure r))) P)
    (hsupport : ∀ᵐ ω ∂P, 0 ≤ A ω ∧ S ω ≤ A ω) :
    (1 / 2 : ℝ) * (∫ ω, Real.exp (-(r * (A ω - S ω))) ∂P) ≤
        P.real {ω | max (A ω) (L ω) < S ω + Y ω} ∧
      P.real {ω | max (A ω) (L ω) < S ω + Y ω} ≤
        ∫ ω, Real.exp (-(r * (A ω - S ω))) ∂P := by
  have hsν : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ p.2 ≤ p.1 :=
    (hPast.ae_iff (by fun_prop)).mp hsupport
  have hp := hJoint.measureReal_eq
    (show MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) |
      max q.1.1 q.2.2 < q.1.2 + q.2.1} from measurableSet_lt (by fun_prop) (by fun_prop))
  have hi := hPast.integral_comp
    (show AEStronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-(r * (p.1 - p.2)))) ν by fun_prop)
  dsimp only [Function.comp_def] at hi
  rw [hp, hi]
  exact product_random_threshold_sandwich ν r hr hsν
theorem joint_random_threshold_tie_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (A S Y L : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hJoint : HasLaw (fun ω => ((A ω, S ω), (Y ω, L ω)))
      (ν.prod ((expMeasure r).prod (expMeasure r))) P) :
    ∀ᵐ ω ∂P, max (A ω) (L ω) ≠ S ω + Y ω := by
  have hp := hJoint.measure_eq
    (show MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) |
      max q.1.1 q.2.2 = q.1.2 + q.2.1} from measurableSet_eq_fun (by fun_prop) (by fun_prop))
  have hz : P {ω | max (A ω) (L ω) = S ω + Y ω} = 0 :=
    hp.trans (random_product_tie_measure_zero ν r hr)
  rw [ae_iff]
  simpa only [not_not] using hz
theorem independent_random_threshold_sandwich_and_tie
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A S Y L : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hAS : AEMeasurable (fun ω => (A ω, S ω)) P)
    (hY : HasLaw Y (expMeasure r) P) (hL : HasLaw L (expMeasure r) P)
    (hPastY : IndepFun (fun ω => (A ω, S ω)) Y P)
    (hArmL : IndepFun (fun ω => ((A ω, S ω), Y ω)) L P)
    (hsupport : ∀ᵐ ω ∂P, 0 ≤ A ω ∧ S ω ≤ A ω) :
    ((1 / 2 : ℝ) * (∫ ω, Real.exp (-(r * (A ω - S ω))) ∂P) ≤
        P.real {ω | max (A ω) (L ω) < S ω + Y ω} ∧
      P.real {ω | max (A ω) (L ω) < S ω + Y ω} ≤
        ∫ ω, Real.exp (-(r * (A ω - S ω))) ∂P) ∧
      (∀ᵐ ω ∂P, max (A ω) (L ω) ≠ S ω + Y ω) := by
  let ν := P.map (fun ω => (A ω, S ω))
  have hPast : HasLaw (fun ω => (A ω, S ω)) ν P := ⟨hAS, rfl⟩
  have : IsProbabilityMeasure ν := hPast.isProbabilityMeasure_iff.mp inferInstance
  have := isProbabilityMeasure_expMeasure hr
  have hPY := hPastY.hasLaw_prod hPast hY
  have hPYL := hArmL.hasLaw_prod hPY hL
  have hJoint : HasLaw (fun ω => ((A ω, S ω), (Y ω, L ω)))
      (ν.prod ((expMeasure r).prod (expMeasure r))) P :=
    (measurePreserving_prodAssoc ν (expMeasure r) (expMeasure r)).fun_comp_hasLaw hPYL
  exact ⟨joint_random_threshold_sandwich P ν A S Y L r hr hPast hJoint hsupport,
    joint_random_threshold_tie_ae P ν A S Y L r hr hJoint⟩
end ArgmaxRandomThresholdExpComparison
open Set MeasureTheory
namespace ArgmaxRegionComparison
lemma maximizer_gt_iff_region_lub_lt (H : ℝ → ℝ) (x T A F : ℝ)
    (hA : IsLUB (H '' Iic x) A) (hF : IsLUB (H '' Ioi x) F)
    (hne : A ≠ F) (hmax : ∀ t : ℝ, H t ≤ H T) :
    x < T ↔ A < F := by
  have hAupper : A ≤ H T := hA.2 (by rintro y ⟨t, ht, rfl⟩; exact hmax t)
  have hFupper : F ≤ H T := hF.2 (by rintro y ⟨t, ht, rfl⟩; exact hmax t)
  constructor
  · intro hT
    have hTF : H T ≤ F := hF.1 ⟨T, hT, rfl⟩
    exact lt_of_le_of_ne (hAupper.trans hTF) hne
  · intro hAF
    by_contra hT
    have hTA : H T ≤ A := hA.1 ⟨T, le_of_not_gt hT, rfl⟩
    exact (not_lt_of_ge (hFupper.trans hTA)) hAF
lemma maximizer_ne_of_future_lub_gt (H : ℝ → ℝ) (x T F : ℝ)
    (hF : IsLUB (H '' Ioi x) F) (hgain : H x < F)
    (hmax : ∀ t : ℝ, H t ≤ H T) : T ≠ x := by
  intro hTx
  have hFupper : F ≤ H T := hF.2 (by rintro y ⟨t, ht, rfl⟩; exact hmax t)
  rw [hTx] at hFupper
  exact not_lt_of_ge hFupper hgain
theorem maximizer_region_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → Ω → ℝ) (x : ℝ) (T A F : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Iic x) (A ω))
    (hF : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Ioi x) (F ω))
    (hne : ∀ᵐ ω ∂P, A ω ≠ F ω)
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    {ω | x < T ω} =ᵐ[P] {ω | A ω < F ω} := by
  filter_upwards [hA, hF, hne, hmax] with ω hAω hFω hneω hmaxω
  exact propext (maximizer_gt_iff_region_lub_lt (fun t => H t ω) x (T ω) (A ω) (F ω)
    hAω hFω hneω hmaxω)
theorem maximizer_region_probability_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → Ω → ℝ) (x : ℝ) (T A F : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Iic x) (A ω))
    (hF : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Ioi x) (F ω))
    (hne : ∀ᵐ ω ∂P, A ω ≠ F ω)
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    P.real {ω | x < T ω} = P.real {ω | A ω < F ω} :=
  congrArg ENNReal.toReal (measure_congr (maximizer_region_ae P H x T A F hA hF hne hmax))
theorem maximizer_ne_fixed_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → Ω → ℝ) (x : ℝ) (T F : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Ioi x) (F ω))
    (hgain : ∀ᵐ ω ∂P, H x ω < F ω)
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    ∀ᵐ ω ∂P, T ω ≠ x := by
  filter_upwards [hF, hgain, hmax] with ω hFω hgainω hmaxω
  exact maximizer_ne_of_future_lub_gt (fun t => H t ω) x (T ω) (F ω) hFω hgainω hmaxω
end ArgmaxRegionComparison
namespace ArgmaxRegionLaplaceBridge
lemma hasLaw_exp_ae_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (r : ℝ) (hr : 0 < r) (hY : HasLaw Y (expMeasure r) P) :
    ∀ᵐ ω ∂P, 0 < Y ω := by
  have := isProbabilityMeasure_expMeasure hr
  have hzero : (expMeasure r) (Set.Iic (0 : ℝ)) = 0 := by
    apply (measureReal_eq_zero_iff (μ := expMeasure r) (s := Set.Iic (0 : ℝ))).mp
    simpa using ArgmaxExponentialMaxComparison.expMeasure_real_Iic r 0 hr (le_refl 0)
  have hz : P {ω | Y ω ≤ 0} = 0 :=
    (hY.measure_eq (show MeasurableSet {y : ℝ | y ≤ 0} from measurableSet_Iic)).trans hzero
  rw [ae_iff]
  simpa only [not_lt] using hz
theorem maximizer_tail_laplace_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ → Ω → ℝ) (x : ℝ) (T A S Y L : Ω → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hAS : AEMeasurable (fun ω => (A ω, S ω)) P)
    (hY : HasLaw Y (expMeasure r) P) (hL : HasLaw L (expMeasure r) P)
    (hPastY : IndepFun (fun ω => (A ω, S ω)) Y P)
    (hArmL : IndepFun (fun ω => ((A ω, S ω), Y ω)) L P)
    (hsupport : ∀ᵐ ω ∂P, 0 ≤ A ω ∧ S ω ≤ A ω)
    (hRest : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Iic x) (max (A ω) (L ω)))
    (hFuture : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Ioi x) (S ω + Y ω))
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    (1 / 2 : ℝ) * (∫ ω, Real.exp (-(r * (A ω - S ω))) ∂P) ≤ P.real {ω | x < T ω} ∧
      P.real {ω | x < T ω} ≤ ∫ ω, Real.exp (-(r * (A ω - S ω))) ∂P := by
  have hb := ArgmaxRandomThresholdExpComparison.independent_random_threshold_sandwich_and_tie
    P A S Y L r hr hAS hY hL hPastY hArmL hsupport
  have hp := ArgmaxRegionComparison.maximizer_region_probability_eq P H x T
    (fun ω => max (A ω) (L ω)) (fun ω => S ω + Y ω) hRest hFuture hb.2 hmax
  rw [hp]
  exact hb.1
theorem maximizer_ne_fixed_of_exp_future
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → Ω → ℝ) (x : ℝ) (T S Y : Ω → ℝ)
    (r : ℝ) (hr : 0 < r) (hY : HasLaw Y (expMeasure r) P)
    (hPoint : ∀ᵐ ω ∂P, H x ω = S ω)
    (hFuture : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Ioi x) (S ω + Y ω))
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    ∀ᵐ ω ∂P, T ω ≠ x := by
  apply ArgmaxRegionComparison.maximizer_ne_fixed_ae P H x T (fun ω => S ω + Y ω)
    hFuture _ hmax
  filter_upwards [hPoint, hasLaw_exp_ae_pos P Y r hr hY] with ω hx hy
  rw [hx]
  linarith
end ArgmaxRegionLaplaceBridge
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ArgmaxTimeReversalCovarianceAlgebra
theorem max_sub_tsub (T s : ℝ≥0) :
    ((max T s : ℝ≥0) : ℝ) - ((T - s : ℝ≥0) : ℝ) = (s : ℝ) := by
  by_cases hs : s ≤ T
  · rw [max_eq_left hs, NNReal.coe_sub hs]
    ring
  · have hTs : T ≤ s := le_of_not_ge hs
    rw [max_eq_right hTs, tsub_eq_zero_of_le hTs, NNReal.coe_zero, sub_zero]
theorem covariance_expansion_of_le (T s t : ℝ≥0) (hst : s ≤ t) :
    ((min (max T s) (max T t) : ℝ≥0) : ℝ) -
      ((min (max T s) (T - t) : ℝ≥0) : ℝ) -
      ((min (T - s) (max T t) : ℝ≥0) : ℝ) +
      ((min (T - s) (T - t) : ℝ≥0) : ℝ) = (s : ℝ) := by
  have hmax : max T s ≤ max T t := max_le_max_left T hst
  have htt : T - t ≤ max T s := tsub_le_self.trans (le_max_left T s)
  have hst' : T - s ≤ max T t := tsub_le_self.trans (le_max_left T t)
  have hsub : T - t ≤ T - s := tsub_le_tsub_left hst T
  rw [min_eq_left hmax, min_eq_right htt, min_eq_left hst', min_eq_right hsub]
  have hm := max_sub_tsub T s
  linarith
theorem covariance_expansion (T s t : ℝ≥0) :
    ((min (max T s) (max T t) : ℝ≥0) : ℝ) -
      ((min (max T s) (T - t) : ℝ≥0) : ℝ) -
      ((min (T - s) (max T t) : ℝ≥0) : ℝ) +
      ((min (T - s) (T - t) : ℝ≥0) : ℝ) = ((min s t : ℝ≥0) : ℝ) := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact covariance_expansion_of_le T s t hst
  · have h := covariance_expansion_of_le T t s hts
    rw [min_eq_right hts]
    rw [min_comm (max T s) (max T t), min_comm (max T s) (T - t),
      min_comm (T - s) (max T t), min_comm (T - s) (T - t)]
    linarith
end ArgmaxTimeReversalCovarianceAlgebra
namespace ArgmaxBrownianTimeReversal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
lemma reversed_extension_isGaussianProcess (hB : IsGaussianProcess B P) (T : ℝ≥0) :
    IsGaussianProcess (fun s ω => B (max T s) ω - B (T - s) ω) P := by
  classical
  apply hB.of_isGaussianProcess
  intro s
  let I : Finset ℝ≥0 := {max T s, T - s}
  let a : I := ⟨max T s, by simp [I]⟩
  let b : I := ⟨T - s, by simp [I]⟩
  refine ⟨I, (ContinuousLinearMap.proj a : (I → ℝ) →L[ℝ] ℝ) -
    ContinuousLinearMap.proj b, ?_⟩
  intro ω
  rfl
lemma reversed_extension_integral (hB : IsPreBrownianReal B P) (T s : ℝ≥0) :
    (∫ ω, B (max T s) ω - B (T - s) ω ∂P) = 0 := by
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
    hB.integral_eval, hB.integral_eval, sub_self]
lemma reversed_extension_covariance (hB : IsPreBrownianReal B P) (T s t : ℝ≥0)
    (hst : s ≤ t) :
    cov[fun ω => B (max T s) ω - B (T - s) ω,
      fun ω => B (max T t) ω - B (T - t) ω; P] = (s : ℝ) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [covariance_fun_sub_fun_sub
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two]
  simp_rw [hB.covariance_eval]
  exact ArgmaxTimeReversalCovarianceAlgebra.covariance_expansion_of_le T s t hst
theorem isPreBrownianReal_reversed_extension (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IsPreBrownianReal (fun s ω => B (max T s) ω - B (T - s) ω) P := by
  exact (reversed_extension_isGaussianProcess hB.isGaussianProcess T).isPreBrownianReal_of_covariance
    (fun s => reversed_extension_integral hB T s)
    (fun s t hst => reversed_extension_covariance hB T s t hst)
lemma reversed_extension_continuous (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Continuous (fun s => B (max T s) ω - B (T - s) ω) := by
  filter_upwards [hB.cont] with ω hω
  exact (hω.comp (continuous_const.max continuous_id)).fun_sub
    (hω.comp (continuous_const.fun_sub continuous_id))
theorem isBrownianReal_reversed_extension (hB : IsBrownianReal B P) (T : ℝ≥0) :
    IsBrownianReal (fun s ω => B (max T s) ω - B (T - s) ω) P where
  toIsPreBrownianReal := isPreBrownianReal_reversed_extension hB.toIsPreBrownianReal T
  cont := reversed_extension_continuous hB T
lemma reversed_extension_on_horizon (T s : ℝ≥0) (hs : s ≤ T) (ω : Ω) :
    B (max T s) ω - B (T - s) ω = B T ω - B (T - s) ω := by
  rw [max_eq_left hs]
lemma reversed_extension_after_horizon (T s : ℝ≥0) (hs : T ≤ s) (ω : Ω) :
    B (max T s) ω - B (T - s) ω = B s ω - B 0 ω := by
  rw [max_eq_right hs, tsub_eq_zero_of_le hs]
end ArgmaxBrownianTimeReversal
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal
namespace ArgmaxBrownianFiniteMaximum
theorem isLUB_range_denseSeq {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [SeparableSpace K] [Nonempty K] (f : K → ℝ) (hf : Continuous f) :
    IsLUB (Set.range f) (⨆ n : ℕ, f (denseSeq K n)) := by
  have hbounded : BddAbove (Set.range (fun n : ℕ => f (denseSeq K n))) := by
    apply ((isCompact_range hf).bddAbove).mono
    rintro y ⟨n, rfl⟩
    exact Set.mem_range_self (denseSeq K n)
  have hupper (t : K) : f t ≤ ⨆ n : ℕ, f (denseSeq K n) := by
    exact (denseRange_denseSeq K).induction_on
      (p := fun t => f t ≤ ⨆ n : ℕ, f (denseSeq K n)) t
      (isClosed_le hf continuous_const) (fun n => le_ciSup hbounded n)
  constructor
  · rintro y ⟨t, rfl⟩
    exact hupper t
  · intro y hy
    exact ciSup_le (fun n => hy (Set.mem_range_self (denseSeq K n)))
theorem exists_aemeasurable_finite_maximum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (d : ℝ) :
    ∃ A : Ω → ℝ, AEMeasurable A P ∧
      (∀ᵐ ω ∂P,
        IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) (A ω) ∧
        0 ≤ A ω ∧ B T ω - d * (T : ℝ) ≤ A ω) := by
  classical
  let K := Set.Icc (0 : ℝ≥0) T
  let : Nonempty K := ⟨⟨0, by simp [K]⟩⟩
  let A : Ω → ℝ := fun ω => ⨆ n : ℕ,
    B (denseSeq K n) ω - d * ((denseSeq K n : ℝ≥0) : ℝ)
  have hA : AEMeasurable A P :=
    AEMeasurable.iSup (fun n => (hB.aemeasurable (denseSeq K n)).sub_const _)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hcont hzero
  let f : K → ℝ := fun t => B t ω - d * ((t : ℝ≥0) : ℝ)
  have hf : Continuous f := by
    exact (hcont.comp continuous_subtype_val).sub
      (continuous_const.mul (NNReal.continuous_coe.comp continuous_subtype_val))
  have hrange : Set.range f =
      ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hLUB : IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) (A ω) := by
    rw [← hrange]
    exact isLUB_range_denseSeq f hf
  refine ⟨hLUB, ?_, ?_⟩
  · have hbound := hLUB.1 (Set.mem_image_of_mem (fun t : ℝ≥0 => B t ω - d * (t : ℝ))
      (show (0 : ℝ≥0) ∈ Set.Icc 0 T by simp))
    simpa [hzero] using hbound
  · exact hLUB.1 (Set.mem_image_of_mem (fun t : ℝ≥0 => B t ω - d * (t : ℝ)) (by simp))
end ArgmaxBrownianFiniteMaximum
namespace ArgmaxReversedMaximumTransfer
theorem isLUB_reversed_maximum (f : ℝ≥0 → ℝ) (T : ℝ≥0) (d A : ℝ)
    (hA : IsLUB ((fun s : ℝ≥0 => f s - d * (s : ℝ)) '' Set.Icc 0 T) A) :
    IsLUB ((fun t : ℝ≥0 => -(f (max T t) - f (T - t)) + d * (t : ℝ)) ''
      Set.Icc 0 T) (A - (f T - d * (T : ℝ))) := by
  constructor
  · rintro y ⟨t, ht, rfl⟩
    have hb := hA.1 (Set.mem_image_of_mem
      (fun s : ℝ≥0 => f s - d * (s : ℝ))
      (show T - t ∈ Set.Icc 0 T from ⟨by positivity, tsub_le_self⟩))
    dsimp only at hb ⊢
    rw [NNReal.coe_sub ht.2] at hb
    rw [max_eq_left ht.2]
    linarith
  · intro U hU
    have hbound : A ≤ U + (f T - d * (T : ℝ)) := by
      apply hA.2
      rintro y ⟨s, hs, rfl⟩
      have hr := hU (Set.mem_image_of_mem
        (fun t : ℝ≥0 => -(f (max T t) - f (T - t)) + d * (t : ℝ))
        (show T - s ∈ Set.Icc 0 T from ⟨by positivity, tsub_le_self⟩))
      rw [max_eq_left (show T - s ≤ T from tsub_le_self),
        tsub_tsub_cancel_of_le hs.2, NNReal.coe_sub hs.2] at hr
      linarith
    linarith
theorem ae_isLUB_reversed_maximum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (d : ℝ) (A : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P,
      IsLUB ((fun s : ℝ≥0 => B s ω - d * (s : ℝ)) '' Set.Icc 0 T) (A ω)) :
    ∀ᵐ ω ∂P,
      IsLUB ((fun t : ℝ≥0 => -(B (max T t) ω - B (T - t) ω) + d * (t : ℝ)) ''
        Set.Icc 0 T) (A ω - (B T ω - d * (T : ℝ))) := by
  filter_upwards [hA] with ω hω
  exact isLUB_reversed_maximum (fun t => B t ω) T d (A ω) hω
theorem exists_aemeasurable_reversed_maximum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (d : ℝ) :
    ∃ A : Ω → ℝ, AEMeasurable A P ∧
      AEMeasurable (fun ω => A ω - (B T ω - d * (T : ℝ))) P ∧
      IsBrownianReal (fun t ω => -(B (max T t) ω - B (T - t) ω)) P ∧
      (∀ᵐ ω ∂P,
        IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) (A ω) ∧
        IsLUB ((fun t : ℝ≥0 => -(B (max T t) ω - B (T - t) ω) + d * (t : ℝ)) ''
          Set.Icc 0 T) (A ω - (B T ω - d * (T : ℝ))) ∧
        0 ≤ A ω ∧ 0 ≤ A ω - (B T ω - d * (T : ℝ))) := by
  obtain ⟨A, hAm, hA⟩ :=
    ArgmaxBrownianFiniteMaximum.exists_aemeasurable_finite_maximum hB T d
  refine ⟨A, hAm, hAm.sub ((hB.aemeasurable T).sub_const _), ?_, ?_⟩
  · exact (ArgmaxBrownianTimeReversal.isBrownianReal_reversed_extension hB T).neg
  · filter_upwards [hA] with ω hω
    refine ⟨hω.1, isLUB_reversed_maximum (fun t => B t ω) T d (A ω) hω.1,
      hω.2.1, ?_⟩
    exact sub_nonneg.mpr hω.2.2
theorem sampled_process_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} {D : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hD : IsPreBrownianReal D Q) (τ : ℕ → ℝ≥0) :
    IdentDistrib (fun ω n => B (τ n) ω) (fun η n => D (τ n) η) P Q := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hpae : AEMeasurable (fun ω n => B (τ n) ω) P :=
    aemeasurable_pi_lambda _ (fun n => hB.aemeasurable (τ n))
  have hqae : AEMeasurable (fun η n => D (τ n) η) Q :=
    aemeasurable_pi_lambda _ (fun n => hD.aemeasurable (τ n))
  have hfinite (I : Finset ℕ) :
      IdentDistrib (fun ω => I.restrict (fun n => B (τ n) ω))
        (fun η => I.restrict (fun n => D (τ n) η)) P Q := by
    let J := I.image τ
    let L : (J → ℝ) → (I → ℝ) := fun x i =>
      x ⟨τ i, Finset.mem_image_of_mem τ i.property⟩
    have hL : Measurable L := by fun_prop
    exact ((hB.hasLaw J).identDistrib (hD.hasLaw J)).comp hL
  refine ⟨hpae, hqae, ?_⟩
  have hproj := isProjectiveLimit_map hpae
  apply hproj.unique
  intro I
  rw [(isProjectiveLimit_map hqae) I]
  exact (hfinite I).map_eq.symm
theorem ae_isLUB_dense_interval
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (d : ℝ)
    (τ : ℕ → Set.Icc (0 : ℝ≥0) T) (hτ : DenseRange τ) :
    ∀ᵐ ω ∂P,
      IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T)
        (⨆ n : ℕ, B (τ n) ω - d * ((τ n : ℝ≥0) : ℝ)) := by
  filter_upwards [hB.cont] with ω hcont
  let K := Set.Icc (0 : ℝ≥0) T
  let f : K → ℝ := fun t => B t ω - d * ((t : ℝ≥0) : ℝ)
  have hf : Continuous f := by
    exact (hcont.comp continuous_subtype_val).sub
      (continuous_const.mul (NNReal.continuous_coe.comp continuous_subtype_val))
  have hb : BddAbove (Set.range (fun n : ℕ => f (τ n))) := by
    apply ((isCompact_range hf).bddAbove).mono
    rintro y ⟨n, rfl⟩
    exact Set.mem_range_self (τ n)
  have hl : IsLUB (Set.range f) (⨆ n : ℕ, f (τ n)) := by
    constructor
    · rintro y ⟨t, rfl⟩
      exact hτ.induction_on
        (p := fun t => f t ≤ ⨆ n : ℕ, f (τ n)) t
        (isClosed_le hf continuous_const) (fun n => le_ciSup hb n)
    · intro y hy
      exact ciSup_le (fun n => hy (Set.mem_range_self (τ n)))
  have hrange : Set.range f =
      ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hrange]
  exact hl
theorem finite_maximum_identDistrib
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} {D : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P) (hD : IsBrownianReal D Q) (T : ℝ≥0) (d : ℝ)
    (A : Ω → ℝ) (M : Ω' → ℝ)
    (hA : ∀ᵐ ω ∂P,
      IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) (A ω))
    (hM : ∀ᵐ η ∂Q,
      IsLUB ((fun t : ℝ≥0 => D t η - d * (t : ℝ)) '' Set.Icc 0 T) (M η)) :
    IdentDistrib A M P Q := by
  classical
  let K := Set.Icc (0 : ℝ≥0) T
  let : Nonempty K := ⟨⟨0, by simp [K]⟩⟩
  let τ : ℕ → ℝ≥0 := fun n => denseSeq K n
  let F : (ℕ → ℝ) → ℝ := fun x => ⨆ n : ℕ, x n - d * (τ n : ℝ)
  have hF : Measurable F :=
    Measurable.iSup (fun n => (measurable_pi_apply n).sub_const _)
  have hlaw := (sampled_process_identDistrib hB.toIsPreBrownianReal
    hD.toIsPreBrownianReal τ).comp hF
  have heqB : (F ∘ (fun ω n => B (τ n) ω)) =ᵐ[P] A := by
    filter_upwards [ae_isLUB_dense_interval hB T d (denseSeq K) (denseRange_denseSeq K), hA]
      with ω hc ha
    exact hc.unique ha
  have heqD : (F ∘ (fun η n => D (τ n) η)) =ᵐ[Q] M := by
    filter_upwards [ae_isLUB_dense_interval hD T d (denseSeq K) (denseRange_denseSeq K), hM]
      with η hc hm
    exact hc.unique hm
  exact (IdentDistrib.of_ae_eq hlaw.aemeasurable_fst heqB).symm.trans
    (hlaw.trans (IdentDistrib.of_ae_eq hlaw.aemeasurable_snd heqD))
theorem exists_reversed_maximum_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (d : ℝ) :
    ∃ A M : Ω → ℝ, AEMeasurable A P ∧ AEMeasurable M P ∧
      (∀ᵐ ω ∂P,
        IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) (A ω) ∧
        IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Set.Icc 0 T) (M ω) ∧
        0 ≤ A ω ∧ 0 ≤ A ω - (B T ω - d * (T : ℝ)) ∧ 0 ≤ M ω) ∧
      IdentDistrib (fun ω => A ω - (B T ω - d * (T : ℝ))) M P P := by
  obtain ⟨A, hAm, hGapm, hRev, hA⟩ := exists_aemeasurable_reversed_maximum hB T d
  obtain ⟨M, hMm, hM⟩ :=
    ArgmaxBrownianFiniteMaximum.exists_aemeasurable_finite_maximum hB T (-d)
  refine ⟨A, M, hAm, hMm, ?_, ?_⟩
  · filter_upwards [hA, hM] with ω ha hm
    refine ⟨ha.1, ?_, ha.2.2.1, ha.2.2.2, hm.2.1⟩
    simpa only [neg_mul, sub_neg_eq_add] using hm.1
  · apply finite_maximum_identDistrib hRev hB T (-d)
      (fun ω => A ω - (B T ω - d * (T : ℝ))) M
    · filter_upwards [hA] with ω ha
      simpa only [neg_mul, sub_neg_eq_add] using ha.2.1
    · filter_upwards [hM] with ω hm
      exact hm.1
end ArgmaxReversedMaximumTransfer
namespace ArgmaxBrownianTailLaplaceBridge
theorem brownian_maxima_tail_laplace_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hArms : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (s : ℝ≥0) (d : ℝ) (hd : 0 < d) (H : ℝ → Ω → ℝ) (T A Y L : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω))
    (hY : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 =>
      B (s + t) ω - B s ω - d * (t : ℝ))) (Y ω))
    (hL : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => C t ω - d * (t : ℝ))) (L ω))
    (hYlaw : HasLaw Y (expMeasure (2 * d)) P) (hLlaw : HasLaw L (expMeasure (2 * d)) P)
    (hRest : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Iic (s : ℝ)) (max (A ω) (L ω)))
    (hFuture : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Ioi (s : ℝ))
      (B s ω - d * (s : ℝ) + Y ω))
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    (1 / 2 : ℝ) * (∫ ω, Real.exp (-((2 * d) * (A ω - (B s ω - d * (s : ℝ))))) ∂P) ≤
        P.real {ω | (s : ℝ) < T ω} ∧
      P.real {ω | (s : ℝ) < T ω} ≤
        ∫ ω, Real.exp (-((2 * d) * (A ω - (B s ω - d * (s : ℝ))))) ∂P := by
  obtain ⟨hAS, hs⟩ := ArgmaxBrownianMaximumIndependence.past_maximum_measurable_and_support hB s d A hA
  exact ArgmaxRegionLaplaceBridge.maximizer_tail_laplace_sandwich P H s T A
    (fun ω => B s ω - d * (s : ℝ)) Y L (2 * d) (by positivity) hAS hYlaw hLlaw
    (ArgmaxBrownianMaximumIndependence.past_future_maximum_independent hB s d A Y hA hY)
    (ArgmaxBrownianMaximumIndependence.arm_opposite_maximum_independent hB hC hArms s d A Y L hA hY hL)
    hs hRest hFuture hmax
theorem exists_positive_maximum_tail_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hArms : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (s : ℝ≥0) (d : ℝ) (hd : 0 < d) (H : ℝ → Ω → ℝ) (T A Y L : Ω → ℝ)
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω))
    (hY : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 =>
      B (s + t) ω - B s ω - d * (t : ℝ))) (Y ω))
    (hL : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => C t ω - d * (t : ℝ))) (L ω))
    (hYlaw : HasLaw Y (expMeasure (2 * d)) P) (hLlaw : HasLaw L (expMeasure (2 * d)) P)
    (hRest : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Iic (s : ℝ)) (max (A ω) (L ω)))
    (hFuture : ∀ᵐ ω ∂P, IsLUB ((fun t => H t ω) '' Set.Ioi (s : ℝ))
      (B s ω - d * (s : ℝ) + Y ω))
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    ∃ M : Ω → ℝ, AEMeasurable M P ∧
      (∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Set.Icc 0 s) (M ω) ∧ 0 ≤ M ω) ∧
      (1 / 2 : ℝ) * (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) ≤ P.real {ω | (s : ℝ) < T ω} ∧
      P.real {ω | (s : ℝ) < T ω} ≤ ∫ ω, Real.exp (-((2 * d) * M ω)) ∂P := by
  have hb := brownian_maxima_tail_laplace_sandwich P B C hB hC hArms s d hd H T A Y L
    hA hY hL hYlaw hLlaw hRest hFuture hmax
  obtain ⟨A₀, M, _, hMm, hprops, hid⟩ :=
    ArgmaxReversedMaximumTransfer.exists_reversed_maximum_identDistrib hB s d
  have hAA : A =ᵐ[P] A₀ := by
    filter_upwards [hA, hprops] with ω ha hp
    exact ha.unique hp.1
  have heq : (∫ ω, Real.exp (-((2 * d) * (A ω - (B s ω - d * (s : ℝ))))) ∂P) =
      ∫ ω, Real.exp (-((2 * d) * M ω)) ∂P := by
    calc
      _ = ∫ ω, Real.exp (-((2 * d) * (A₀ ω - (B s ω - d * (s : ℝ))))) ∂P :=
        integral_congr_ae (hAA.mono (fun ω h => by dsimp only; rw [h]))
      _ = _ := (hid.comp (show Measurable (fun z : ℝ => Real.exp (-((2 * d) * z))) by fun_prop)).integral_eq
  rw [heq] at hb
  refine ⟨M, hMm, ?_, hb.1, hb.2⟩
  filter_upwards [hprops] with ω hp
  exact ⟨hp.2.1, hp.2.2.2.2⟩
end ArgmaxBrownianTailLaplaceBridge
open Set
open scoped NNReal
namespace ArgmaxTwoArmRegionLUBs
lemma isLUB_add_image {α : Type*} (f : α → ℝ) (K : Set α) (a c : ℝ)
    (h : IsLUB (f '' K) a) : IsLUB ((fun t => c + f t) '' K) (c + a) := by
  constructor
  · rintro v ⟨t, ht, rfl⟩
    have hb := h.1 ⟨t, ht, rfl⟩
    dsimp only
    linarith
  · intro b hb
    have hh : a ≤ b - c := h.2 (by
      rintro v ⟨t, ht, rfl⟩
      have := hb ⟨t, ht, rfl⟩
      linarith)
    linarith
lemma isLUB_positive_times_of_positive_lub (f : ℝ≥0 → ℝ) (Y : ℝ)
    (h0 : f 0 = 0) (h : IsLUB (Set.range f) Y) (hY : 0 < Y) :
    IsLUB (f '' Set.Ioi 0) Y := by
  have hex : ∃ t, 0 < f t := by
    by_contra hn
    have hb : Y ≤ 0 := h.2 (by
      rintro v ⟨t, rfl⟩
      exact le_of_not_gt (not_exists.mp hn t))
    linarith
  obtain ⟨u, hu⟩ := hex
  have hu0 : u ≠ 0 := by intro heq; rw [heq, h0] at hu; exact lt_irrefl _ hu
  refine ⟨?_, ?_⟩
  · rintro v ⟨t, ht, rfl⟩
    exact h.1 (Set.mem_range_self t)
  · intro b hb
    have hb0 : 0 < b := hu.trans_le (hb ⟨u, pos_iff_ne_zero.mpr hu0, rfl⟩)
    apply h.2
    rintro v ⟨t, rfl⟩
    by_cases ht : t = 0
    · simpa only [ht, h0] using hb0.le
    · exact hb ⟨t, pos_iff_ne_zero.mpr ht, rfl⟩
lemma rest_image_eq_union
    (H : ℝ → ℝ) (U V : ℝ≥0 → ℝ) (s : ℝ≥0) (d : ℝ)
    (hplus : ∀ t : ℝ≥0, H (t : ℝ) = U t - d * (t : ℝ))
    (hminus : ∀ t : ℝ≥0, H (-(t : ℝ)) = V t - d * (t : ℝ)) :
    H '' Set.Iic (s : ℝ) =
      ((fun t : ℝ≥0 => U t - d * (t : ℝ)) '' Set.Icc 0 s) ∪
        Set.range (fun t : ℝ≥0 => V t - d * (t : ℝ)) := by
  ext v
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h0 : 0 ≤ t
    · let u : ℝ≥0 := ⟨t, h0⟩
      exact Or.inl ⟨u, ⟨by simp, by exact_mod_cast ht⟩, (hplus u).symm⟩
    · let u : ℝ≥0 := ⟨-t, by linarith⟩
      have heq : -(u : ℝ) = t := by change -(-t) = t; exact neg_neg t
      exact Or.inr ⟨u, (hminus u).symm.trans (congrArg H heq)⟩
  · rintro (⟨t, ht, hv⟩ | ⟨t, hv⟩)
    · exact ⟨(t : ℝ), by exact_mod_cast ht.2, (hplus t).trans hv⟩
    · refine ⟨-(t : ℝ), ?_, (hminus t).trans hv⟩
      change -(t : ℝ) ≤ (s : ℝ)
      have ht0 := t.property
      have hs0 := s.property
      linarith
lemma future_image_eq_shift
    (H : ℝ → ℝ) (U : ℝ≥0 → ℝ) (s : ℝ≥0) (d : ℝ)
    (hplus : ∀ t : ℝ≥0, H (t : ℝ) = U t - d * (t : ℝ)) :
    H '' Set.Ioi (s : ℝ) =
      ((fun u : ℝ≥0 => (U s - d * (s : ℝ)) + (U (s + u) - U s - d * (u : ℝ))) ''
        Set.Ioi 0) := by
  ext v
  constructor
  · rintro ⟨t, ht, rfl⟩
    change (s : ℝ) < t at ht
    let u : ℝ≥0 := ⟨t - s, by linarith⟩
    have hu : 0 < u := by change (0 : ℝ) < t - s; linarith
    have heq : ((s + u : ℝ≥0) : ℝ) = t := by change (s : ℝ) + (t - (s : ℝ)) = t; ring
    have hh : H t = U (s + u) - d * ((s + u : ℝ≥0) : ℝ) := by
      rw [← heq]
      exact hplus (s + u)
    refine ⟨u, hu, ?_⟩
    rw [hh]
    push_cast
    ring
  · rintro ⟨u, hu, hv⟩
    refine ⟨((s + u : ℝ≥0) : ℝ), ?_, ?_⟩
    · simp only [Set.mem_Ioi, NNReal.coe_add]
      exact lt_add_of_pos_right _ (by exact_mod_cast hu)
    · rw [hplus]
      simp only [NNReal.coe_add]
      have heq : U (s + u) - d * ((s : ℝ) + u) =
          (U s - d * (s : ℝ)) + (U (s + u) - U s - d * (u : ℝ)) := by ring
      exact heq.trans hv
theorem rest_and_future_lubs
    (H : ℝ → ℝ) (U V : ℝ≥0 → ℝ) (s : ℝ≥0) (d A Y L : ℝ)
    (hplus : ∀ t : ℝ≥0, H (t : ℝ) = U t - d * (t : ℝ))
    (hminus : ∀ t : ℝ≥0, H (-(t : ℝ)) = V t - d * (t : ℝ))
    (hA : IsLUB ((fun t : ℝ≥0 => U t - d * (t : ℝ)) '' Set.Icc 0 s) A)
    (hY : IsLUB (Set.range (fun t : ℝ≥0 => U (s + t) - U s - d * (t : ℝ))) Y)
    (hL : IsLUB (Set.range (fun t : ℝ≥0 => V t - d * (t : ℝ))) L)
    (hYpos : 0 < Y) :
    IsLUB (H '' Set.Iic (s : ℝ)) (max A L) ∧
      IsLUB (H '' Set.Ioi (s : ℝ)) (U s - d * (s : ℝ) + Y) := by
  constructor
  · rw [rest_image_eq_union H U V s d hplus hminus]
    exact hA.union hL
  · rw [future_image_eq_shift H U s d hplus]
    exact isLUB_add_image _ _ Y _ (isLUB_positive_times_of_positive_lub _ Y (by simp) hY hYpos)
end ArgmaxTwoArmRegionLUBs
namespace ArgmaxBrownianTailLaplaceBridge
theorem two_arm_tail_sandwich_from_maximum_laws
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hArms : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (s : ℝ≥0) (d : ℝ) (hd : 0 < d) (H : ℝ → Ω → ℝ) (T A Y L : Ω → ℝ)
    (hplus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H (t : ℝ) ω = B t ω - d * (t : ℝ))
    (hminus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H (-(t : ℝ)) ω = C t ω - d * (t : ℝ))
    (hA : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 s) (A ω))
    (hY : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 =>
      B (s + t) ω - B s ω - d * (t : ℝ))) (Y ω))
    (hL : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => C t ω - d * (t : ℝ))) (L ω))
    (hYlaw : HasLaw Y (expMeasure (2 * d)) P) (hLlaw : HasLaw L (expMeasure (2 * d)) P)
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    ∃ M : Ω → ℝ, AEMeasurable M P ∧
      (∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Set.Icc 0 s) (M ω) ∧ 0 ≤ M ω) ∧
      (1 / 2 : ℝ) * (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) ≤ P.real {ω | (s : ℝ) < T ω} ∧
      P.real {ω | (s : ℝ) < T ω} ≤ (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) ∧
      (∀ᵐ ω ∂P, T ω ≠ (s : ℝ)) := by
  have hpos := ArgmaxRegionLaplaceBridge.hasLaw_exp_ae_pos P Y (2 * d) (by positivity) hYlaw
  have hlubs : ∀ᵐ ω ∂P,
      IsLUB ((fun t => H t ω) '' Set.Iic (s : ℝ)) (max (A ω) (L ω)) ∧
      IsLUB ((fun t => H t ω) '' Set.Ioi (s : ℝ)) (B s ω - d * (s : ℝ) + Y ω) := by
    filter_upwards [hplus, hminus, hA, hY, hL, hpos] with ω hp hm ha hy hl hypos
    exact ArgmaxTwoArmRegionLUBs.rest_and_future_lubs (fun t => H t ω)
      (fun t => B t ω) (fun t => C t ω) s d (A ω) (Y ω) (L ω) hp hm ha hy hl hypos
  have hr := hlubs.mono (fun ω h => h.1)
  have hf := hlubs.mono (fun ω h => h.2)
  obtain ⟨M, hMm, hMl, hlo, hup⟩ := exists_positive_maximum_tail_sandwich
    P B C hB hC hArms s d hd H T A Y L hA hY hL hYlaw hLlaw hr hf hmax
  refine ⟨M, hMm, hMl, hlo, hup, ?_⟩
  exact ArgmaxRegionLaplaceBridge.maximizer_ne_fixed_of_exp_future P H s T
    (fun ω => B s ω - d * (s : ℝ)) Y (2 * d) (by positivity) hYlaw
    (hplus.mono (fun ω h => h s)) hf hmax
end ArgmaxBrownianTailLaplaceBridge
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace ArgmaxBrownianExponentialIncrement
lemma normalized_increment_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (a : ℝ) :
    Integrable (fun ω => Real.exp (a * (B (s + t) ω - B s ω) - a ^ 2 * (t : ℝ) / 2)) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlaw := (hB.shift s).hasLaw_eval t
  have hmgf := mgf_gaussianReal hlaw.map_eq a
  have hi : Integrable (fun ω => Real.exp (a * (B (s + t) ω - B s ω))) P := by
    apply (mgf_pos_iff).mp
    rw [hmgf]
    exact Real.exp_pos _
  apply (hi.const_mul (Real.exp (-(a ^ 2 * (t : ℝ) / 2)))).congr
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only
    simp only [Real.exp_sub, Real.exp_neg]
    ring)
lemma normalized_increment_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (a : ℝ) :
    (∫ ω, Real.exp (a * (B (s + t) ω - B s ω) - a ^ 2 * (t : ℝ) / 2) ∂P) = 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlaw := (hB.shift s).hasLaw_eval t
  have hmgf := mgf_gaussianReal hlaw.map_eq a
  calc
    _ = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) *
        mgf (fun ω => B (s + t) ω - B s ω) P a := by
      change _ = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) *
        (∫ ω, Real.exp (a * (B (s + t) ω - B s ω)) ∂P)
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        dsimp only
        simp only [Real.exp_sub, Real.exp_neg]
        ring)
    _ = 1 := by
      rw [hmgf]
      simp only [zero_mul, zero_add]
      rw [← Real.exp_add]
      have hz : -(a ^ 2 * (t : ℝ) / 2) + (t : ℝ) * a ^ 2 / 2 = 0 := by ring
      rw [hz, Real.exp_zero]
theorem past_integral_normalized_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (a : ℝ)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (fun r : Set.Iic s => B r ω)) P) :
    (∫ ω, F (fun r : Set.Iic s => B r ω) *
      Real.exp (a * (B (s + t) ω - B s ω) - a ^ 2 * (t : ℝ) / 2) ∂P) =
      ∫ ω, F (fun r : Set.Iic s => B r ω) ∂P := by
  have hind : IndepFun (fun ω => F (fun r : Set.Iic s => B r ω))
      (fun ω => Real.exp (a * (B (s + t) ω - B s ω) - a ^ 2 * (t : ℝ) / 2)) P :=
    by
      have hfuture : Measurable (fun y : ℝ≥0 → ℝ =>
          Real.exp (a * y t - a ^ 2 * (t : ℝ) / 2)) := by fun_prop
      simpa only [Function.comp_def] using (hB.indepFun_shift s).symm.comp hF hfuture
  rw [hind.integral_fun_mul_eq_mul_integral hFi.aestronglyMeasurable
    (normalized_increment_integrable hB s t a).aestronglyMeasurable,
    normalized_increment_integral hB s t a, mul_one]
end ArgmaxBrownianExponentialIncrement
namespace ArgmaxBrownianGridInfrastructure
theorem grid_increment_indep_past
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) (n : ℕ) :
    IndepFun (fun ω => B (((n + 1 : ℕ) : ℝ≥0) * h) ω - B ((n : ℝ≥0) * h) ω)
      (fun ω (j : Set.Iic n) => B ((j.val : ℝ≥0) * h) ω) P := by
  let past : (Set.Iic ((n : ℝ≥0) * h) → ℝ) → (Set.Iic n → ℝ) :=
    fun f j => f ⟨(j.val : ℝ≥0) * h, by
      change (j.val : ℝ≥0) * h ≤ (n : ℝ≥0) * h
      gcongr
      exact_mod_cast (show j.val ≤ n from j.property)⟩
  have hfuture : Measurable (fun f : ℝ≥0 → ℝ => f h) := by fun_prop
  have hpast : Measurable past := by fun_prop
  have hi := (hB.indepFun_shift ((n : ℝ≥0) * h)).comp hfuture hpast
  have hstep : (n : ℝ≥0) * h + h = ((n + 1 : ℕ) : ℝ≥0) * h := by
    push_cast
    ring
  simpa only [Function.comp_def, past, hstep] using hi
theorem exists_stronglyMeasurable_grid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) :
    ∃ b : ℕ → Ω → ℝ,
      (∀ n, StronglyMeasurable (b n)) ∧
      (∀ᵐ ω ∂P, ∀ n, b n ω = B ((n : ℝ≥0) * h) ω) ∧
      (∀ n, IndepFun (fun ω => b (n + 1) ω - b n ω)
        (fun ω (j : Set.Iic n) => b j ω) P) := by
  let b : ℕ → Ω → ℝ := fun n =>
    (hB.aemeasurable ((n : ℝ≥0) * h)).mk (B ((n : ℝ≥0) * h))
  have hb (n : ℕ) : StronglyMeasurable (b n) :=
    (hB.aemeasurable ((n : ℝ≥0) * h)).measurable_mk.stronglyMeasurable
  have heq (n : ℕ) : b n =ᵐ[P] B ((n : ℝ≥0) * h) :=
    (hB.aemeasurable ((n : ℝ≥0) * h)).ae_eq_mk.symm
  have hall : ∀ᵐ ω ∂P, ∀ n, b n ω = B ((n : ℝ≥0) * h) ω := ae_all_iff.mpr heq
  refine ⟨b, hb, hall, ?_⟩
  intro n
  apply (grid_increment_indep_past hB h n).congr
  · filter_upwards [hall] with ω hω
    rw [hω (n + 1), hω n]
  · filter_upwards [hall] with ω hω
    exact funext (fun j => (hω j).symm)
theorem exists_grid_exponential_martingale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) (a : ℝ) :
    ∃ M : ℕ → Ω → ℝ, ∃ ℱ : Filtration ℕ ‹MeasurableSpace Ω›,
      Martingale M ℱ P ∧ (∀ n ω, 0 ≤ M n ω) ∧
      (∀ᵐ ω ∂P, ∀ n, M n ω =
        Real.exp (a * B ((n : ℝ≥0) * h) ω - a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ∧
      (∀ n, (∫ ω, M n ω ∂P) = 1) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨b, hb, hall, _⟩ := exists_stronglyMeasurable_grid hB h
  let ℱ := Filtration.natural b hb
  let M : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (a * b n ω - a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)
  have hadpB : StronglyAdapted ℱ b := Filtration.stronglyAdapted_natural hb
  have hadp : StronglyAdapted ℱ M := by
    intro n
    have hbn := (hadpB n).measurable
    exact (by fun_prop : Measurable[ℱ n] (M n)).stronglyMeasurable
  have hnorm (n : ℕ) : M n =ᵐ[P] (fun ω =>
      Real.exp (a * (B (0 + (n : ℝ≥0) * h) ω - B 0 ω) -
        a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) := by
    filter_upwards [hall, hB.eval_zero_ae_eq_zero] with ω hω hzero
    simp only [M, hω n, zero_add, hzero, sub_zero]
  have hint (n : ℕ) : Integrable (M n) P :=
    (ArgmaxBrownianExponentialIncrement.normalized_increment_integrable hB 0 ((n : ℝ≥0) * h) a).congr
      (hnorm n).symm
  have hexpect (n : ℕ) : (∫ ω, M n ω ∂P) = 1 :=
    (integral_congr_ae (hnorm n)).trans
      (ArgmaxBrownianExponentialIncrement.normalized_increment_integral hB 0 ((n : ℝ≥0) * h) a)
  have hstep (n : ℕ) : (n : ℝ≥0) * h + h = ((n + 1 : ℕ) : ℝ≥0) * h := by
    push_cast
    ring
  have hmart : Martingale M ℱ P := by
    apply martingale_of_setIntegral_eq_succ hadp hint
    intro n E hE
    have hEambient : MeasurableSet E := ℱ.le n E hE
    change MeasurableSet[Filtration.natural b hb n] E at hE
    rw [Filtration.natural_eq_comap b hb n] at hE
    obtain ⟨S, hS, hpre⟩ := hE
    let past : (Set.Iic ((n : ℝ≥0) * h) → ℝ) → (Set.Iic n → ℝ) :=
      fun f j => f ⟨(j.val : ℝ≥0) * h, by
        change (j.val : ℝ≥0) * h ≤ (n : ℝ≥0) * h
        gcongr
        exact_mod_cast (show j.val ≤ n from j.property)⟩
    let F : (Set.Iic ((n : ℝ≥0) * h) → ℝ) → ℝ := fun f =>
      S.indicator (fun z : Set.Iic n → ℝ =>
        Real.exp (a * z ⟨n, show n ≤ n from le_rfl⟩ -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) (past f)
    have hF : Measurable F := by
      dsimp only [F]
      exact ((by fun_prop : Measurable (fun z : Set.Iic n → ℝ =>
        Real.exp (a * z ⟨n, show n ≤ n from le_rfl⟩ -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2))).indicator hS).comp
        (by fun_prop : Measurable past)
    have hFae : (fun ω => F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω)) =ᵐ[P]
        E.indicator (M n) := by
      filter_upwards [hall] with ω hω
      have hv : past (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) =
          (fun j : Set.Iic n => b j ω) := by
        funext j
        exact (hω j).symm
      dsimp only [F]
      rw [hv]
      rw [← hpre]
      by_cases hs : (fun j : Set.Iic n => b j ω) ∈ S <;>
        simp [Set.indicator, hs, M]
    have hFi : Integrable (fun ω => F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω)) P :=
      ((hint n).indicator hEambient).congr hFae.symm
    have hproduct : M (n + 1) =ᵐ[P] (fun ω => M n ω *
        Real.exp (a * (B ((n : ℝ≥0) * h + h) ω - B ((n : ℝ≥0) * h) ω) -
          a ^ 2 * (h : ℝ) / 2)) := by
      filter_upwards [hall] with ω hω
      dsimp only [M]
      rw [hω (n + 1), hω n, hstep n, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hweighted : (fun ω => F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) *
        Real.exp (a * (B ((n : ℝ≥0) * h + h) ω - B ((n : ℝ≥0) * h) ω) -
          a ^ 2 * (h : ℝ) / 2)) =ᵐ[P] E.indicator (M (n + 1)) := by
      filter_upwards [hFae, hproduct] with ω hf hp
      rw [hf]
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω, hp]
    rw [← integral_indicator hEambient, ← integral_indicator hEambient]
    calc
      _ = ∫ ω, F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) ∂P :=
        (integral_congr_ae hFae).symm
      _ = ∫ ω, F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) *
          Real.exp (a * (B ((n : ℝ≥0) * h + h) ω - B ((n : ℝ≥0) * h) ω) -
            a ^ 2 * (h : ℝ) / 2) ∂P :=
        (ArgmaxBrownianExponentialIncrement.past_integral_normalized_increment
          hB ((n : ℝ≥0) * h) h a F hF hFi).symm
      _ = _ := integral_congr_ae hweighted
  refine ⟨M, ℱ, hmart, ?_, ?_, hexpect⟩
  · intro n ω
    exact (Real.exp_pos _).le
  · filter_upwards [hall] with ω hω
    intro n
    dsimp only [M]
    rw [hω n]
theorem finite_grid_crossing_exponential_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (d m : ℝ) (hd : 0 < d) (N : ℕ) :
    ENNReal.ofReal (Real.exp (2 * d * m)) *
      P {ω | ∃ k : ℕ, k ≤ N ∧
        m ≤ B ((k : ℝ≥0) * h) ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)} ≤ 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨M, ℱ, hmart, hnonneg, hAE, hexpect⟩ :=
    exists_grid_exponential_martingale hB h (2 * d)
  let ε : ℝ≥0 := ⟨Real.exp (2 * d * m), (Real.exp_pos _).le⟩
  let E := {ω | (ε : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    (fun k => M k ω)}
  have hnonneg' : (0 : ℕ → Ω → ℝ) ≤ M := fun n ω => hnonneg n ω
  have hmax := maximal_ineq (ε := ε) hmart.submartingale hnonneg' N
  change (ε : ℝ≥0∞) * P E ≤ ENNReal.ofReal (∫ ω in E, M N ω ∂P) at hmax
  have hI : (∫ ω in E, M N ω ∂P) ≤ 1 :=
    (setIntegral_le_integral (hmart.integrable N)
      (Filter.Eventually.of_forall (hnonneg N))).trans_eq (hexpect N)
  have hmax' : (ε : ℝ≥0∞) * P E ≤ 1 := by
    exact hmax.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hI)
  have hcompare : P {ω | ∃ k : ℕ, k ≤ N ∧
      m ≤ B ((k : ℝ≥0) * h) ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)} ≤ P E := by
    apply measure_mono_ae
    filter_upwards [hAE] with ω hω
    rintro ⟨k, hk, hcross⟩
    apply (Finset.le_sup'_iff _).mpr
    refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    rw [hω k]
    change Real.exp (2 * d * m) ≤ _
    apply Real.exp_le_exp.mpr
    calc
      2 * d * m ≤ 2 * d *
          (B ((k : ℝ≥0) * h) ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcross (by positivity)
      _ = _ := by ring
  have hmul : (ε : ℝ≥0∞) *
      P {ω | ∃ k : ℕ, k ≤ N ∧
        m ≤ B ((k : ℝ≥0) * h) ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)} ≤
      (ε : ℝ≥0∞) * P E := by
    gcongr
  have hfinal := hmul.trans hmax'
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
  exact hfinal
theorem finite_grid_crossing_measure_le_exp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (d m : ℝ) (hd : 0 < d) (N : ℕ) :
    P {ω | ∃ k : ℕ, k ≤ N ∧
      m ≤ B ((k : ℝ≥0) * h) ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(2 * d * m))) := by
  have hb := finite_grid_crossing_exponential_bound hB h d m hd N
  have hp : ENNReal.ofReal (Real.exp (2 * d * m)) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (Real.exp (2 * d * m)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hle : P {ω | ∃ k : ℕ, k ≤ N ∧
      m ≤ B ((k : ℝ≥0) * h) ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)} ≤
      1 / ENNReal.ofReal (Real.exp (2 * d * m)) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl ht)).mpr (by simpa only [mul_comm] using hb)
  have hinv : 1 / ENNReal.ofReal (Real.exp (2 * d * m)) =
      ENNReal.ofReal (Real.exp (-(2 * d * m))) := by
    rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  exact hle.trans_eq hinv
end ArgmaxBrownianGridInfrastructure
namespace ArgmaxBrownianGridExponentialFamily
theorem exists_common_grid_exponential_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) :
    ∃ b : ℕ → Ω → ℝ, ∃ hb : ∀ n, StronglyMeasurable (b n),
      (∀ᵐ ω ∂P, ∀ n, b n ω = B ((n : ℝ≥0) * h) ω) ∧
      ∀ a : ℝ,
        Martingale (fun n ω => Real.exp (a * b n ω -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) (Filtration.natural b hb) P ∧
        ∀ n, (∫ ω, Real.exp (a * b n ω -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2) ∂P) = 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨b, hb, hall, _⟩ := ArgmaxBrownianGridInfrastructure.exists_stronglyMeasurable_grid hB h
  refine ⟨b, hb, hall, ?_⟩
  intro a
  let ℱ := Filtration.natural b hb
  let M : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (a * b n ω - a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)
  have hadpB : StronglyAdapted ℱ b := Filtration.stronglyAdapted_natural hb
  have hadp : StronglyAdapted ℱ M := by
    intro n
    have hbn := (hadpB n).measurable
    exact (by fun_prop : Measurable[ℱ n] (M n)).stronglyMeasurable
  have hnorm (n : ℕ) : M n =ᵐ[P] (fun ω =>
      Real.exp (a * (B (0 + (n : ℝ≥0) * h) ω - B 0 ω) -
        a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) := by
    filter_upwards [hall, hB.eval_zero_ae_eq_zero] with ω hω hzero
    simp only [M, hω n, zero_add, hzero, sub_zero]
  have hint (n : ℕ) : Integrable (M n) P :=
    (ArgmaxBrownianExponentialIncrement.normalized_increment_integrable hB 0 ((n : ℝ≥0) * h) a).congr
      (hnorm n).symm
  have hexpect (n : ℕ) : (∫ ω, M n ω ∂P) = 1 :=
    (integral_congr_ae (hnorm n)).trans
      (ArgmaxBrownianExponentialIncrement.normalized_increment_integral hB 0 ((n : ℝ≥0) * h) a)
  have hstep (n : ℕ) : (n : ℝ≥0) * h + h = ((n + 1 : ℕ) : ℝ≥0) * h := by
    push_cast
    ring
  have hmart : Martingale M ℱ P := by
    apply martingale_of_setIntegral_eq_succ hadp hint
    intro n E hE
    have hEambient : MeasurableSet E := ℱ.le n E hE
    change MeasurableSet[Filtration.natural b hb n] E at hE
    rw [Filtration.natural_eq_comap b hb n] at hE
    obtain ⟨S, hS, hpre⟩ := hE
    let past : (Set.Iic ((n : ℝ≥0) * h) → ℝ) → (Set.Iic n → ℝ) :=
      fun f j => f ⟨(j.val : ℝ≥0) * h, by
        change (j.val : ℝ≥0) * h ≤ (n : ℝ≥0) * h
        gcongr
        exact_mod_cast (show j.val ≤ n from j.property)⟩
    let F : (Set.Iic ((n : ℝ≥0) * h) → ℝ) → ℝ := fun f =>
      S.indicator (fun z : Set.Iic n → ℝ =>
        Real.exp (a * z ⟨n, show n ≤ n from le_rfl⟩ -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) (past f)
    have hF : Measurable F := by
      dsimp only [F]
      exact ((by fun_prop : Measurable (fun z : Set.Iic n → ℝ =>
        Real.exp (a * z ⟨n, show n ≤ n from le_rfl⟩ -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2))).indicator hS).comp
        (by fun_prop : Measurable past)
    have hFae : (fun ω => F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω)) =ᵐ[P]
        E.indicator (M n) := by
      filter_upwards [hall] with ω hω
      have hv : past (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) =
          (fun j : Set.Iic n => b j ω) := by
        funext j
        exact (hω j).symm
      dsimp only [F]
      rw [hv]
      rw [← hpre]
      by_cases hs : (fun j : Set.Iic n => b j ω) ∈ S <;>
        simp [Set.indicator, hs, M]
    have hFi : Integrable (fun ω => F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω)) P :=
      ((hint n).indicator hEambient).congr hFae.symm
    have hproduct : M (n + 1) =ᵐ[P] (fun ω => M n ω *
        Real.exp (a * (B ((n : ℝ≥0) * h + h) ω - B ((n : ℝ≥0) * h) ω) -
          a ^ 2 * (h : ℝ) / 2)) := by
      filter_upwards [hall] with ω hω
      dsimp only [M]
      rw [hω (n + 1), hω n, hstep n, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hweighted : (fun ω => F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) *
        Real.exp (a * (B ((n : ℝ≥0) * h + h) ω - B ((n : ℝ≥0) * h) ω) -
          a ^ 2 * (h : ℝ) / 2)) =ᵐ[P] E.indicator (M (n + 1)) := by
      filter_upwards [hFae, hproduct] with ω hf hp
      rw [hf]
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω, hp]
    rw [← integral_indicator hEambient, ← integral_indicator hEambient]
    calc
      _ = ∫ ω, F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) ∂P :=
        (integral_congr_ae hFae).symm
      _ = ∫ ω, F (fun r : Set.Iic ((n : ℝ≥0) * h) => B r ω) *
          Real.exp (a * (B ((n : ℝ≥0) * h + h) ω - B ((n : ℝ≥0) * h) ω) -
            a ^ 2 * (h : ℝ) / 2) ∂P :=
        (ArgmaxBrownianExponentialIncrement.past_integral_normalized_increment
          hB ((n : ℝ≥0) * h) h a F hF hFi).symm
      _ = _ := integral_congr_ae hweighted
  exact ⟨hmart, hexpect⟩
end ArgmaxBrownianGridExponentialFamily
namespace ArgmaxGridStoppedExponentialL2
theorem stopped_exponential_square_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (b : ℕ → Ω → ℝ) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℝ≥0) (a : ℝ)
    (hm : Martingale (fun n ω => Real.exp (a * b n ω -
      a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ℱ P)
    (hr : Martingale (fun n ω => Real.exp ((2 * a) * b n ω -
      (2 * a) ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ℱ P)
    (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : ℕ∞)))
    (N : ℕ) (hbound : ∀ ω, τ ω ≤ N)
    (hmean : (∫ ω, Real.exp ((2 * a) * b N ω -
      (2 * a) ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ) / 2) ∂P) = 1) :
    Integrable (fun ω =>
      (Real.exp (a * b (τ ω) ω - a ^ 2 * (((τ ω : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ^ 2) P ∧
    (∫ ω, (Real.exp (a * b (τ ω) ω -
      a ^ 2 * (((τ ω : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ^ 2 ∂P) ≤
      Real.exp (a ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ)) := by
  let M : ℕ → Ω → ℝ := fun n ω => Real.exp (a * b n ω -
    a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)
  let R : ℕ → Ω → ℝ := fun n ω => Real.exp ((2 * a) * b n ω -
    (2 * a) ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)
  let C := Real.exp (a ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ))
  have hbdd : ∀ ω, (τ ω : ℕ∞) ≤ N := fun ω => by exact_mod_cast hbound ω
  have hstopM : stoppedValue M (fun ω => (τ ω : ℕ∞)) = fun ω => M (τ ω) ω := by
    funext ω
    simp [stoppedValue]
  have hstopR : stoppedValue R (fun ω => (τ ω : ℕ∞)) = fun ω => R (τ ω) ω := by
    funext ω
    simp [stoppedValue]
  have hm' : Martingale M ℱ P := hm
  have hr' : Martingale R ℱ P := hr
  have hMi : Integrable (fun ω => M (τ ω) ω) P := by
    simpa only [hstopM] using hm'.submartingale.integrable_stoppedValue hτ hbdd
  have hRi : Integrable (fun ω => R (τ ω) ω) P := by
    simpa only [hstopR] using hr'.submartingale.integrable_stoppedValue hτ hbdd
  have hupper : (∫ ω, R (τ ω) ω ∂P) ≤ 1 := by
    have hi := hr'.submartingale.expected_stoppedValue_mono hτ
      (isStoppingTime_const ℱ N) hbdd (fun _ => le_rfl)
    rw [hstopR, stoppedValue_const] at hi
    exact hi.trans_eq hmean
  have hdom (ω : Ω) : M (τ ω) ω ^ 2 ≤ C * R (τ ω) ω := by
    have hfactor : M (τ ω) ω ^ 2 =
        Real.exp (a ^ 2 * (((τ ω : ℝ≥0) * h : ℝ≥0) : ℝ)) * R (τ ω) ω := by
      dsimp only [M, R]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    push_cast
    gcongr
    exact_mod_cast hbound ω
  have hCi : Integrable (fun ω => C * R (τ ω) ω) P := hRi.const_mul C
  have hsqi : Integrable (fun ω => M (τ ω) ω ^ 2) P := by
    have hsmeas : AEStronglyMeasurable (fun ω => M (τ ω) ω ^ 2) P := by
      convert hMi.aestronglyMeasurable.pow 2 using 1
      funext ω
      rfl
    apply hCi.mono' (f := fun ω => M (τ ω) ω ^ 2) hsmeas
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖M (τ ω) ω ^ 2‖ ≤ C * R (τ ω) ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (M (τ ω) ω))]
      exact hdom ω)
  refine ⟨hsqi, ?_⟩
  calc
    _ ≤ ∫ ω, C * R (τ ω) ω ∂P := integral_mono hsqi hCi hdom
    _ = C * ∫ ω, R (τ ω) ω ∂P := integral_const_mul C _
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hupper (Real.exp_pos _).le
    _ = C := mul_one C
theorem exists_actual_grid_family_with_stopped_l2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) :
    ∃ b : ℕ → Ω → ℝ, ∃ hb : ∀ n, StronglyMeasurable (b n),
      (∀ᵐ ω ∂P, ∀ n, b n ω = B ((n : ℝ≥0) * h) ω) ∧
      (∀ a : ℝ,
        Martingale (fun n ω => Real.exp (a * b n ω -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) (Filtration.natural b hb) P ∧
        ∀ n, (∫ ω, Real.exp (a * b n ω -
          a ^ 2 * (((n : ℝ≥0) * h : ℝ≥0) : ℝ) / 2) ∂P) = 1) ∧
      ∀ (a : ℝ) (τ : Ω → ℕ) (N : ℕ),
        IsStoppingTime (Filtration.natural b hb) (fun ω => (τ ω : ℕ∞)) →
        (∀ ω, τ ω ≤ N) →
        Integrable (fun ω => (Real.exp (a * b (τ ω) ω -
          a ^ 2 * (((τ ω : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ^ 2) P ∧
        (∫ ω, (Real.exp (a * b (τ ω) ω -
          a ^ 2 * (((τ ω : ℝ≥0) * h : ℝ≥0) : ℝ) / 2)) ^ 2 ∂P) ≤
          Real.exp (a ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨b, hb, hAE, hfamily⟩ :=
    ArgmaxBrownianGridExponentialFamily.exists_common_grid_exponential_family hB h
  refine ⟨b, hb, hAE, hfamily, ?_⟩
  intro a τ N hτ hbound
  exact stopped_exponential_square_bound b (Filtration.natural b hb) h a
    (hfamily a).1 (hfamily (2 * a)).1 τ hτ N hbound ((hfamily (2 * a)).2 N)
end ArgmaxGridStoppedExponentialL2
open MeasureTheory
open scoped NNReal ENNReal
namespace ArgmaxSecondMomentUniformIntegrability
theorem uniformIntegrable_of_second_moment
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : ι → Ω → ℝ) (hf : ∀ i, StronglyMeasurable (f i))
    (hfi : ∀ i, Integrable (f i) P)
    (hfsq : ∀ i, Integrable (fun ω => f i ω ^ 2) P)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, (∫ ω, f i ω ^ 2 ∂P) ≤ C) :
    UniformIntegrable f 1 P := by
  apply uniformIntegrable_of (by norm_num : (1 : ℝ≥0∞) ≤ 1) (by norm_num)
    (fun i => (hf i).aestronglyMeasurable)
  intro ε hε
  let r : ℝ := (C + 1) / ε
  have hrpos : 0 < r := div_pos (by linarith) hε
  let R : ℝ≥0 := ⟨r, hrpos.le⟩
  refine ⟨R, ?_⟩
  intro i
  let E := {ω | R ≤ ‖f i ω‖₊}
  have hE : MeasurableSet E := measurableSet_le measurable_const (hf i).nnnorm.measurable
  have htail : Integrable (E.indicator (f i)) P := (hfi i).indicator hE
  have hsqdiv : Integrable (fun ω => f i ω ^ 2 / r) P := (hfsq i).div_const r
  have hdom (ω : Ω) : ‖E.indicator (f i) ω‖ ≤ f i ω ^ 2 / r := by
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      apply (le_div_iff₀ hrpos).mpr
      have hR : r ≤ ‖f i ω‖ := by
        have hnn : (R : ℝ) ≤ (‖f i ω‖₊ : ℝ) := by exact_mod_cast (show R ≤ ‖f i ω‖₊ from hω)
        change r ≤ ‖f i ω‖ at hnn
        exact hnn
      calc
        ‖f i ω‖ * r ≤ ‖f i ω‖ * ‖f i ω‖ :=
          mul_le_mul_of_nonneg_left hR (norm_nonneg _)
        _ = f i ω ^ 2 := by rw [← sq, Real.norm_eq_abs, sq_abs]
    · rw [Set.indicator_of_notMem hω, norm_zero]
      exact div_nonneg (sq_nonneg _) hrpos.le
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm htail]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ ω, f i ω ^ 2 / r ∂P := integral_mono htail.norm hsqdiv hdom
    _ = (∫ ω, f i ω ^ 2 ∂P) / r := integral_div r _
    _ ≤ C / r := div_le_div_of_nonneg_right (hbound i) hrpos.le
    _ ≤ ε := by
      apply (div_le_iff₀ hrpos).mpr
      have hrformula : ε * r = C + 1 := by
        dsimp only [r]
        field_simp [hε.ne']
      rw [hrformula]
      linarith
theorem uniformIntegrable_of_integrable_second_moment
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : ι → Ω → ℝ) (hfi : ∀ i, Integrable (f i) P)
    (hfsq : ∀ i, Integrable (fun ω => f i ω ^ 2) P)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, (∫ ω, f i ω ^ 2 ∂P) ≤ C) :
    UniformIntegrable f 1 P := by
  let g : ι → Ω → ℝ := fun i => (hfi i).aestronglyMeasurable.mk (f i)
  have hg (i : ι) : StronglyMeasurable (g i) :=
    (hfi i).aestronglyMeasurable.stronglyMeasurable_mk
  have heq (i : ι) : g i =ᵐ[P] f i := (hfi i).aestronglyMeasurable.ae_eq_mk.symm
  have hgsq (i : ι) : (fun ω => g i ω ^ 2) =ᵐ[P] (fun ω => f i ω ^ 2) := by
    filter_upwards [heq i] with ω hω
    rw [hω]
  have hgi (i : ι) : Integrable (g i) P := (hfi i).congr (heq i).symm
  have hgsqi (i : ι) : Integrable (fun ω => g i ω ^ 2) P :=
    (hfsq i).congr (hgsq i).symm
  have hgbound (i : ι) : (∫ ω, g i ω ^ 2 ∂P) ≤ C :=
    (integral_congr_ae (hgsq i)).trans_le (hbound i)
  exact (uniformIntegrable_of_second_moment g hg hgi hgsqi C hC hgbound).ae_eq heq
end ArgmaxSecondMomentUniformIntegrability
namespace ArgmaxStoppedGridUniformIntegrability
theorem exists_actual_grids_with_uniformIntegrability
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ι → ℝ≥0) :
    ∃ b : ι → ℕ → Ω → ℝ, ∃ hb : ∀ i n, StronglyMeasurable (b i n),
      (∀ i, ∀ᵐ ω ∂P, ∀ n, b i n ω = B ((n : ℝ≥0) * h i) ω) ∧
      ∀ (a : ℝ) (τ : ι → Ω → ℕ) (N : ι → ℕ) (T : ℝ≥0),
        (∀ i, IsStoppingTime (Filtration.natural (b i) (hb i))
          (fun ω => (τ i ω : ℕ∞))) →
        (∀ i ω, τ i ω ≤ N i) →
        (∀ i, (N i : ℝ≥0) * h i ≤ T) →
        UniformIntegrable (fun i ω => Real.exp (a * b i (τ i ω) ω -
          a ^ 2 * (((τ i ω : ℝ≥0) * h i : ℝ≥0) : ℝ) / 2)) 1 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  choose b hb hAE hfamily hL2 using
    (fun i : ι => ArgmaxGridStoppedExponentialL2.exists_actual_grid_family_with_stopped_l2 hB (h i))
  refine ⟨b, hb, hAE, ?_⟩
  intro a τ N T hτ hbound htime
  let f : ι → Ω → ℝ := fun i ω => Real.exp (a * b i (τ i ω) ω -
    a ^ 2 * (((τ i ω : ℝ≥0) * h i : ℝ≥0) : ℝ) / 2)
  have hfi (i : ι) : Integrable (f i) P := by
    have hbdd : ∀ ω, (τ i ω : ℕ∞) ≤ N i := fun ω => by exact_mod_cast hbound i ω
    have hi := (hfamily i a).1.submartingale.integrable_stoppedValue (hτ i) hbdd
    convert hi using 1
    funext ω
    simp [f, stoppedValue]
  have hfsq (i : ι) : Integrable (fun ω => f i ω ^ 2) P :=
    (hL2 i a (τ i) (N i) (hτ i) (hbound i)).1
  have hmoment (i : ι) : (∫ ω, f i ω ^ 2 ∂P) ≤ Real.exp (a ^ 2 * (T : ℝ)) := by
    apply (hL2 i a (τ i) (N i) (hτ i) (hbound i)).2.trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    exact_mod_cast htime i
  exact ArgmaxSecondMomentUniformIntegrability.uniformIntegrable_of_integrable_second_moment
    f hfi hfsq (Real.exp (a ^ 2 * (T : ℝ))) (Real.exp_pos _).le hmoment
end ArgmaxStoppedGridUniformIntegrability
open scoped NNReal Topology
open Filter
namespace ArgmaxDyadicGridPathApproximation
theorem exists_uniform_crossing_mesh (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (T : ℝ≥0) (m ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
      dist s t < δ → f s ≤ m → f t < m + ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (show ContinuousOn f (Set.Icc (0 : ℝ≥0) T) from hf.continuousOn)
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht hdist hfs
  have hd := hmod t ⟨by positivity, ht⟩ s ⟨by positivity, hs⟩
    (by simpa only [dist_comm] using hdist)
  rw [Real.dist_eq] at hd
  have hlt := (abs_sub_lt_iff.mp hd).1
  linarith
theorem uniform_first_crossing_overshoot (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (T : ℝ≥0) (m ε : ℝ) (hε : 0 < ε) (h0 : f 0 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (g : ℕ → ℝ≥0),
      g 0 = 0 → (∀ i, i ≤ N → g i ≤ T) →
      (∀ i, i < N → dist (g (i + 1)) (g i) < δ) →
      ∀ k, k ≤ N → m < f (g k) →
        (∀ i, i < k → f (g i) ≤ m) → f (g k) < m + ε := by
  obtain ⟨δ, hδ, hcross⟩ := exists_uniform_crossing_mesh f hf T m ε hε
  refine ⟨δ, hδ, ?_⟩
  intro N g hg0 hgT hgstep k hk hhit hprev
  cases k with
  | zero =>
    rw [hg0] at hhit
    exact (not_lt_of_ge h0 hhit).elim
  | succ k =>
    apply hcross (g k) (g (k + 1)) (hgT k (by omega)) (hgT (k + 1) hk)
    · simpa only [dist_comm] using hgstep k (by omega)
    · exact hprev k (by omega)
theorem exists_grid_point_near (T h : ℝ≥0) (N : ℕ) (hh : 0 < h)
    (hT : T ≤ (N : ℝ≥0) * h) (t : ℝ≥0) (ht : t ≤ T) :
    ∃ k : ℕ, k ≤ N ∧ (k : ℝ≥0) * h ≤ t ∧ dist t ((k : ℝ≥0) * h) < (h : ℝ) := by
  let k := Nat.floor (t / h)
  have hratio : t / h ≤ (N : ℝ≥0) := (div_le_iff₀ hh).mpr (ht.trans hT)
  have hkN : k ≤ N := Nat.floor_le_of_le hratio
  have hkle : (k : ℝ≥0) * h ≤ t :=
    (le_div_iff₀ hh).mp (Nat.floor_le (by positivity))
  have hklt : t < ((k : ℝ≥0) + 1) * h :=
    (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (t / h))
  refine ⟨k, hkN, hkle, ?_⟩
  have hkle' : (((k : ℝ≥0) * h : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkle
  have hklt' : (t : ℝ) < ((k : ℝ) + 1) * (h : ℝ) := by exact_mod_cast hklt
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hkle'), NNReal.coe_mul,
    NNReal.coe_natCast]
  nlinarith
lemma uniform_grid_below_horizon (T : ℝ≥0) (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    (k : ℝ≥0) * (T / (N : ℝ≥0)) ≤ T := by
  have hkn : (k : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hk
  have hNne : (N : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    _ ≤ (N : ℝ≥0) * (T / (N : ℝ≥0)) := mul_le_mul_of_nonneg_right hkn (by positivity)
    _ = T := by field_simp
lemma uniform_grid_endpoint (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    (N : ℝ≥0) * (T / (N : ℝ≥0)) = T := by
  have hNne : (N : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
lemma uniform_grid_step_dist (h : ℝ≥0) (k : ℕ) :
    dist (((k + 1 : ℕ) : ℝ≥0) * h) ((k : ℝ≥0) * h) = (h : ℝ) := by
  rw [NNReal.dist_eq, NNReal.coe_mul, NNReal.coe_mul]
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one]
  have heq : ((k : ℝ) + 1) * (h : ℝ) - (k : ℝ) * (h : ℝ) = (h : ℝ) := by ring
  rw [heq, abs_of_nonneg h.coe_nonneg]
lemma dyadic_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ => T / ((2 ^ n : ℕ) : ℝ≥0)) atTop (𝓝 0) := by
  exact (tendsto_const_div_atTop_nhds_zero_nat T).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
lemma dyadic_mesh_coe_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ((T / ((2 ^ n : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) :=
  (NNReal.continuous_coe.tendsto 0).comp (dyadic_mesh_tendsto T)
theorem eventually_dyadic_first_crossing_overshoot
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m ε : ℝ)
    (hε : 0 < ε) (h0 : f 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, k ≤ 2 ^ n → m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) →
        (∀ i : ℕ, i < k → f ((i : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m) →
        f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) < m + ε := by
  obtain ⟨δ, hδ, hcross⟩ := uniform_first_crossing_overshoot f hf T m ε hε h0
  filter_upwards [(dyadic_mesh_coe_tendsto T).eventually (eventually_lt_nhds hδ)] with n hn
  refine hcross (2 ^ n) (fun k => (k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) (by simp) ?_ ?_
  · intro i hi
    exact uniform_grid_below_horizon T (2 ^ n) i (by positivity) hi
  · intro i _
    simpa only [uniform_grid_step_dist] using hn
theorem eventually_dyadic_hit_of_hit (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (T : ℝ≥0) (m : ℝ) (hhit : ∃ t : ℝ≥0, t ≤ T ∧ m < f t) :
    ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, k ≤ 2 ^ n ∧
      m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
  obtain ⟨t, htT, hhit⟩ := hhit
  by_cases hT : T = 0
  · subst T
    have ht : t = 0 := by simpa using htT
    subst t
    exact Filter.Eventually.of_forall (fun n => ⟨0, by positivity, by simpa using hhit⟩)
  have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (show ContinuousOn f (Set.Icc (0 : ℝ≥0) T) from hf.continuousOn)
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) (f t - m) (sub_pos.mpr hhit)
  filter_upwards [(dyadic_mesh_coe_tendsto T).eventually (eventually_lt_nhds hδ)] with n hn
  let h : ℝ≥0 := T / ((2 ^ n : ℕ) : ℝ≥0)
  have hh : 0 < h := div_pos hTpos (by positivity)
  have hcover : T ≤ ((2 ^ n : ℕ) : ℝ≥0) * h :=
    (uniform_grid_endpoint T (2 ^ n) (by positivity)).symm.le
  obtain ⟨k, hkN, hkt, hdist⟩ := exists_grid_point_near T h (2 ^ n) hh hcover t htT
  refine ⟨k, hkN, ?_⟩
  have hnear := hmod t ⟨by positivity, htT⟩ ((k : ℝ≥0) * h)
    ⟨by positivity, hkt.trans htT⟩ (hdist.trans hn)
  rw [Real.dist_eq] at hnear
  have hlt := (abs_sub_lt_iff.mp hnear).1
  change m < f ((k : ℝ≥0) * h)
  linarith
theorem continuous_hit_iff_eventually_dyadic_hit (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (T : ℝ≥0) (m : ℝ) :
    (∃ t : ℝ≥0, t ≤ T ∧ m < f t) ↔
      ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, k ≤ 2 ^ n ∧
        m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
  constructor
  · exact eventually_dyadic_hit_of_hit f hf T m
  · intro hh
    obtain ⟨n, k, hkN, hhit⟩ := hh.exists
    exact ⟨(k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)),
      uniform_grid_below_horizon T (2 ^ n) k (by positivity) hkN, hhit⟩
theorem continuous_hit_iff_exists_dyadic_hit (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (T : ℝ≥0) (m : ℝ) :
    (∃ t : ℝ≥0, t ≤ T ∧ m < f t) ↔
      ∃ n k : ℕ, k ≤ 2 ^ n ∧ m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
  constructor
  · intro hhit
    exact (eventually_dyadic_hit_of_hit f hf T m hhit).exists
  · rintro ⟨n, k, hkN, hhit⟩
    exact ⟨(k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)),
      uniform_grid_below_horizon T (2 ^ n) k (by positivity) hkN, hhit⟩
lemma dyadic_grid_nested (T : ℝ≥0) (n k : ℕ) :
    (k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)) =
      ((2 * k : ℕ) : ℝ≥0) * (T / ((2 ^ (n + 1) : ℕ) : ℝ≥0)) := by
  have hpow : ((2 ^ n : ℕ) : ℝ≥0) ≠ 0 := by positivity
  push_cast
  rw [pow_succ]
  field_simp
lemma dyadic_hit_mono (f : ℝ≥0 → ℝ) (T : ℝ≥0) (m : ℝ) (n : ℕ)
    (hhit : ∃ k : ℕ, k ≤ 2 ^ n ∧ m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) :
    ∃ k : ℕ, k ≤ 2 ^ (n + 1) ∧
      m < f ((k : ℝ≥0) * (T / ((2 ^ (n + 1) : ℕ) : ℝ≥0))) := by
  obtain ⟨k, hk, hhit⟩ := hhit
  refine ⟨2 * k, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left 2 hk
    simpa only [pow_succ, Nat.mul_comm] using hmul
  · rw [← dyadic_grid_nested]
    exact hhit
lemma uniform_fin_grid_monotone (h : ℝ≥0) (N : ℕ) :
    Monotone (fun k : Fin (N + 1) => (k.val : ℝ≥0) * h) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)
lemma dyadic_fin_hit_iff_nat_hit (f : ℝ≥0 → ℝ) (T : ℝ≥0) (m : ℝ) (n : ℕ) :
    (∃ k : Fin (2 ^ n + 1), m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) ↔
      ∃ k : ℕ, k ≤ 2 ^ n ∧ m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
  constructor
  · rintro ⟨k, hhit⟩
    exact ⟨k.val, Nat.le_of_lt_succ k.isLt, hhit⟩
  · rintro ⟨k, hk, hhit⟩
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, hhit⟩
theorem eventually_dyadic_fin_first_crossing_overshoot
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m ε : ℝ)
    (hε : 0 < ε) (h0 : f 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin (2 ^ n + 1),
        m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) →
        (∀ i : Fin (2 ^ n + 1), i < k →
          f ((i.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m) →
        f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) < m + ε := by
  filter_upwards [eventually_dyadic_first_crossing_overshoot f hf T m ε hε h0] with n hn
  intro k hhit hprev
  apply hn k.val (Nat.le_of_lt_succ k.isLt) hhit
  intro i hi
  exact hprev ⟨i, hi.trans k.isLt⟩ hi
theorem continuous_hit_iff_eventually_dyadic_fin_hit
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m : ℝ) :
    (∃ t : ℝ≥0, t ≤ T ∧ m < f t) ↔
      ∀ᶠ n : ℕ in atTop,
        ∃ k : Fin (2 ^ n + 1), m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
  simpa only [dyadic_fin_hit_iff_nat_hit] using
    continuous_hit_iff_eventually_dyadic_hit f hf T m
end ArgmaxDyadicGridPathApproximation
namespace ArgmaxBrownianStoppedHitting
open scoped Classical
theorem first_strict_crossing_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] (b : ℕ → Ω → ℝ)
    (hb : ∀ n, StronglyMeasurable (b n)) (h : ℝ≥0) (d m : ℝ) (N : ℕ) :
    IsStoppingTime (Filtration.natural b hb)
      (fun ω => (hittingBtwn (ι := ℕ) (fun (k : ℕ) ω => b k ω -
        d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)) (Set.Ioi m) 0 N ω : ℕ∞)) := by
  have hadp := Filtration.stronglyAdapted_natural hb
  have hadpX : Adapted (Filtration.natural b hb)
      (fun k ω => b k ω - d * (((k : ℝ≥0) * h : ℝ≥0) : ℝ)) := by
    intro k
    exact (hadp k).measurable.sub measurable_const
  exact hadpX.isStoppingTime_hittingBtwn measurableSet_Ioi
theorem first_strict_crossing_properties {Ω : Type*}
    (u : ℕ → Ω → ℝ) (ω : Ω) (m : ℝ) (N : ℕ) :
    let τ := hittingBtwn u (Set.Ioi m) 0 N ω
    τ ≤ N ∧
      ((∃ k : ℕ, k ≤ N ∧ m < u k ω) → m < u τ ω) ∧
      (∀ i : ℕ, i < τ → u i ω ≤ m) ∧
      ((¬ ∃ k : ℕ, k ≤ N ∧ m < u k ω) → τ = N) := by
  classical
  dsimp only
  refine ⟨hittingBtwn_le ω, ?_, ?_, ?_⟩
  · rintro ⟨k, hk, hhit⟩
    exact hittingBtwn_mem_set (u := u) (s := Set.Ioi m)
      ⟨k, ⟨Nat.zero_le k, hk⟩, hhit⟩
  · intro i hi
    exact le_of_not_gt (notMem_of_lt_hittingBtwn hi (Nat.zero_le i))
  · intro hnone
    have hnone' : ¬ ∃ k ∈ Set.Icc 0 N, u k ω ∈ Set.Ioi m := by
      simpa only [Set.mem_Icc, Nat.zero_le, true_and, Set.mem_Ioi] using hnone
    simp only [hittingBtwn, hnone', ↓reduceIte]
theorem dyadic_stopped_heights_tendsto
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m : ℝ) (h0 : f 0 ≤ m)
    (τ : ℕ → ℕ)
    (hbound : ∀ n, τ n ≤ 2 ^ n)
    (hhit : ∀ n, (∃ k : ℕ, k ≤ 2 ^ n ∧
        m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) →
      m < f ((τ n : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))))
    (hprev : ∀ n i, i < τ n →
      f ((i : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m)
    (hnone : ∀ n, (¬ ∃ k : ℕ, k ≤ 2 ^ n ∧
        m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) → τ n = 2 ^ n) :
    Tendsto (fun n : ℕ => f ((τ n : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) atTop
      (𝓝 (if ∃ t : ℝ≥0, t ≤ T ∧ m < f t then m else f T)) := by
  classical
  by_cases H : ∃ t : ℝ≥0, t ≤ T ∧ m < f t
  · simp only [H, ↓reduceIte]
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    apply Filter.eventually_atTop.mp
    filter_upwards [ArgmaxDyadicGridPathApproximation.eventually_dyadic_hit_of_hit f hf T m H,
      ArgmaxDyadicGridPathApproximation.eventually_dyadic_first_crossing_overshoot f hf T m ε hε h0]
      with n hn hover
    have hlo := hhit n hn
    have hup := hover (τ n) (hbound n) hlo (hprev n)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo.le)]
    linarith
  · simp only [H, ↓reduceIte]
    have hno (n : ℕ) : ¬ ∃ k : ℕ, k ≤ 2 ^ n ∧
        m < f ((k : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
      rintro ⟨k, hk, hhit⟩
      exact H ⟨_, ArgmaxDyadicGridPathApproximation.uniform_grid_below_horizon
        T (2 ^ n) k (by positivity) hk, hhit⟩
    have heq : (fun n : ℕ => f ((τ n : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) =
        (fun _ : ℕ => f T) := by
      funext n
      rw [hnone n (hno n), ArgmaxDyadicGridPathApproximation.uniform_grid_endpoint T (2 ^ n) (by positivity)]
    rw [heq]
    exact tendsto_const_nhds
theorem integral_one_of_uniformIntegrable_ae_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (hUI : UniformIntegrable f 1 P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hmean : ∀ n, (∫ ω, f n ω ∂P) = 1) :
    Integrable g P ∧ (∫ ω, g ω ∂P) = 1 := by
  have hg : Integrable g P := hUI.integrable_of_ae_tendsto hlim
  have hlp := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hUI.1 (memLp_one_iff_integrable.mpr hg) hUI.2.1 hlim
  have hlt := tendsto_integral_of_L1' g hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hUI.memLp n))) hlp
  have hconst : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (1 : ℝ)) := by
    simp only [hmean]
    exact tendsto_const_nhds
  exact ⟨hg, tendsto_nhds_unique hlt hconst⟩
theorem bounded_stopped_martingale_integral_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (hM : Martingale M ℱ P)
    (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : ℕ∞)))
    (N : ℕ) (hbound : ∀ ω, τ ω ≤ N) (hmean : ∀ n, (∫ ω, M n ω ∂P) = 1) :
    Integrable (fun ω => M (τ ω) ω) P ∧ (∫ ω, M (τ ω) ω ∂P) = 1 := by
  have hbdd : ∀ ω, (τ ω : ℕ∞) ≤ N := fun ω => by exact_mod_cast hbound ω
  have hstop : stoppedValue M (fun ω => (τ ω : ℕ∞)) = fun ω => M (τ ω) ω := by
    funext ω
    simp [stoppedValue]
  have hi := hM.submartingale.integrable_stoppedValue hτ hbdd
  rw [hstop] at hi
  have hupper := hM.submartingale.expected_stoppedValue_mono hτ
    (isStoppingTime_const ℱ N) hbdd (fun _ => le_rfl)
  rw [hstop, stoppedValue_const, hmean N] at hupper
  have hlower := hM.submartingale.expected_stoppedValue_mono
    (isStoppingTime_const ℱ 0) hτ (fun ω => WithTop.coe_le_coe.mpr (Nat.zero_le (τ ω))) hbdd
  rw [stoppedValue_const, hstop, hmean 0] at hlower
  exact ⟨hi, le_antisymm hupper hlower⟩
theorem finite_horizon_stopped_identity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (d m : ℝ) (hm : 0 ≤ m) :
    Integrable (fun ω =>
      if ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)
      then Real.exp (2 * d * m) else Real.exp (2 * d * (B T ω - d * (T : ℝ)))) P ∧
    (∫ ω, if ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)
      then Real.exp (2 * d * m) else Real.exp (2 * d * (B T ω - d * (T : ℝ))) ∂P) = 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let h : ℕ → ℝ≥0 := fun n => T / ((2 ^ n : ℕ) : ℝ≥0)
  let N : ℕ → ℕ := fun n => 2 ^ n
  choose b hb hAE hfamily hL2 using
    (fun n : ℕ => ArgmaxGridStoppedExponentialL2.exists_actual_grid_family_with_stopped_l2
      hB.toIsPreBrownianReal (h n))
  let ℱ : ℕ → Filtration ℕ ‹MeasurableSpace Ω› := fun n => Filtration.natural (b n) (hb n)
  let X : ℕ → ℕ → Ω → ℝ := fun n k ω => b n k ω - d * (((k : ℝ≥0) * h n : ℝ≥0) : ℝ)
  let τ : ℕ → Ω → ℕ := fun n => hittingBtwn (X n) (Set.Ioi m) 0 (N n)
  let M : ℕ → ℕ → Ω → ℝ := fun n k ω => Real.exp ((2 * d) * b n k ω -
    (2 * d) ^ 2 * (((k : ℝ≥0) * h n : ℝ≥0) : ℝ) / 2)
  let F : ℕ → Ω → ℝ := fun n ω => Real.exp (2 * d * X n (τ n ω) ω)
  let G : Ω → ℝ := fun ω =>
    if ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)
    then Real.exp (2 * d * m) else Real.exp (2 * d * (B T ω - d * (T : ℝ)))
  have hStop (n : ℕ) : IsStoppingTime (ℱ n) (fun ω => (τ n ω : ℕ∞)) :=
    first_strict_crossing_isStoppingTime (b n) (hb n) (h n) d m (N n)
  have hBound (n : ℕ) (ω : Ω) : τ n ω ≤ N n := hittingBtwn_le ω
  have hFnorm (n : ℕ) (ω : Ω) : F n ω = M n (τ n ω) ω := by
    dsimp only [F, M, X]
    congr 1
    ring
  have hMean (n : ℕ) : Integrable (F n) P ∧ (∫ ω, F n ω ∂P) = 1 := by
    have hs := bounded_stopped_martingale_integral_one (M n) (ℱ n)
      (hfamily n (2 * d)).1 (τ n) (hStop n) (N n) (hBound n) (hfamily n (2 * d)).2
    refine ⟨hs.1.congr (Filter.Eventually.of_forall (fun ω => (hFnorm n ω).symm)), ?_⟩
    exact (integral_congr_ae (Filter.Eventually.of_forall (hFnorm n))).trans hs.2
  have hTime (n : ℕ) : (((N n : ℝ≥0) * h n : ℝ≥0) : ℝ) = (T : ℝ) := by
    exact congrArg (fun t : ℝ≥0 => (t : ℝ))
      (ArgmaxDyadicGridPathApproximation.uniform_grid_endpoint T (2 ^ n) (by positivity))
  have hSquare (n : ℕ) : Integrable (fun ω => F n ω ^ 2) P := by
    have hs := (hL2 n (2 * d) (τ n) (N n) (hStop n) (hBound n)).1
    simpa only [hFnorm, M] using hs
  have hMoment (n : ℕ) : (∫ ω, F n ω ^ 2 ∂P) ≤ Real.exp ((2 * d) ^ 2 * (T : ℝ)) := by
    have hs := (hL2 n (2 * d) (τ n) (N n) (hStop n) (hBound n)).2
    simpa only [hFnorm, M, hTime n] using hs
  have hUI : UniformIntegrable F 1 P :=
    ArgmaxSecondMomentUniformIntegrability.uniformIntegrable_of_integrable_second_moment
      F (fun n => (hMean n).1) hSquare _ (Real.exp_pos _).le hMoment
  have hAll : ∀ᵐ ω ∂P, ∀ n k, b n k ω = B ((k : ℝ≥0) * h n) ω := ae_all_iff.mpr hAE
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hAll, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hcont hzero
    let f : ℝ≥0 → ℝ := fun t => B t ω - d * (t : ℝ)
    have hf : Continuous f := hcont.sub (continuous_const.mul NNReal.continuous_coe)
    have h0 : f 0 ≤ m := by simpa only [f, hzero, NNReal.coe_zero, mul_zero, sub_zero] using hm
    have hgrid (n k : ℕ) : X n k ω = f ((k : ℝ≥0) * h n) := by
      dsimp only [X, f]
      rw [hω n k]
    have hp (n : ℕ) := first_strict_crossing_properties (X n) ω m (N n)
    have hheight := dyadic_stopped_heights_tendsto f hf T m h0 (fun n => τ n ω)
      (fun n => (hp n).1)
      (by
        intro n hn
        have hh : ∃ k : ℕ, k ≤ N n ∧ m < X n k ω := by
          obtain ⟨k, hk, hhit⟩ := hn
          exact ⟨k, hk, by rw [hgrid]; exact hhit⟩
        have hh' := (hp n).2.1 hh
        rw [hgrid] at hh'
        exact hh')
      (by
        intro n i hi
        have hh := (hp n).2.2.1 i hi
        rw [hgrid] at hh
        exact hh)
      (by
        intro n hn
        apply (hp n).2.2.2
        rintro ⟨k, hk, hh⟩
        apply hn
        exact ⟨k, hk, by rw [← hgrid]; exact hh⟩)
    have heqF : (fun n => F n ω) =
        (fun n => Real.exp (2 * d * f ((τ n ω : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))))) := by
      funext n
      exact congrArg (fun x => Real.exp (2 * d * x)) (hgrid n (τ n ω))
    have heqG : G ω = Real.exp (2 * d *
        (if ∃ t : ℝ≥0, t ≤ T ∧ m < f t then m else f T)) := by
      change (if ∃ t : ℝ≥0, t ≤ T ∧ m < f t then Real.exp (2 * d * m)
        else Real.exp (2 * d * f T)) = _
      split_ifs <;> rfl
    rw [heqF, heqG]
    exact Real.continuous_exp.tendsto _ |>.comp (tendsto_const_nhds.mul hheight)
  exact integral_one_of_uniformIntegrable_ae_limit F G hUI hlim (fun n => (hMean n).2)
end ArgmaxBrownianStoppedHitting
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ArgmaxBrownianTerminalRemainder
lemma exp_drift_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (d a : ℝ) :
    Integrable (fun ω => Real.exp (a * (B T ω - d * (T : ℝ)))) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmgf := mgf_gaussianReal (hB.hasLaw_eval T).map_eq a
  have hi : Integrable (fun ω => Real.exp (a * B T ω)) P := by
    apply mgf_pos_iff.mp
    rw [hmgf]
    exact Real.exp_pos _
  apply (hi.const_mul (Real.exp (-a * d * (T : ℝ)))).congr
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only
    rw [← Real.exp_add]
    congr 1
    ring)
lemma integral_exp_drift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (d a : ℝ) :
    (∫ ω, Real.exp (a * (B T ω - d * (T : ℝ))) ∂P) =
      Real.exp ((a ^ 2 / 2 - a * d) * (T : ℝ)) := by
  have hmgf := mgf_gaussianReal (hB.hasLaw_eval T).map_eq a
  calc
    _ = Real.exp (-a * d * (T : ℝ)) * mgf (B T) P a := by
      change _ = Real.exp (-a * d * (T : ℝ)) * (∫ ω, Real.exp (a * B T ω) ∂P)
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        dsimp only
        rw [← Real.exp_add]
        congr 1
        ring)
    _ = _ := by
      rw [hmgf, ← Real.exp_add]
      congr 1
      simp only [zero_mul, zero_add]
      ring
theorem truncated_terminal_exponential_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (d m : ℝ) (hd : 0 ≤ d) :
    (∫ ω in {ω | B T ω - d * (T : ℝ) ≤ m},
      Real.exp ((2 * d) * (B T ω - d * (T : ℝ))) ∂P) ≤
      Real.exp (d * m - d ^ 2 * (T : ℝ) / 2) := by
  let X : Ω → ℝ := fun ω => B T ω - d * (T : ℝ)
  let E : Set Ω := {ω | X ω ≤ m}
  have hE : NullMeasurableSet E P :=
    nullMeasurableSet_le ((hB.aemeasurable T).sub_const _) aemeasurable_const
  change (∫ ω in E, Real.exp ((2 * d) * X ω) ∂P) ≤ _
  rw [← integral_indicator₀ hE]
  calc
    _ ≤ ∫ ω, Real.exp (d * m) * Real.exp (d * X ω) ∂P := by
      apply integral_mono_ae ((exp_drift_integrable hB T d (2 * d)).indicator₀ hE)
        ((exp_drift_integrable hB T d d).const_mul (Real.exp (d * m)))
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω]
          change Real.exp ((2 * d) * X ω) ≤ Real.exp (d * m) * Real.exp (d * X ω)
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hb : X ω ≤ m := hω
          nlinarith [mul_nonneg hd (sub_nonneg.mpr hb)]
        · rw [Set.indicator_of_notMem hω]
          exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by
      rw [integral_const_mul, integral_exp_drift hB T d d, ← Real.exp_add]
      congr 1
      ring
end ArgmaxBrownianTerminalRemainder
namespace ArgmaxBrownianTerminalRemainder
theorem truncated_terminal_exponential_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (d m : ℝ) (hd : 0 < d) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ ω in {ω | B (n : ℝ≥0) ω - d * (n : ℝ) ≤ m},
        Real.exp ((2 * d) * (B (n : ℝ≥0) ω - d * (n : ℝ))) ∂P)
      Filter.atTop (nhds 0) := by
  have hc : 0 < d ^ 2 / 2 := by positivity
  have hg : Filter.Tendsto (fun n : ℕ => Real.exp (-((d ^ 2 / 2) * (n : ℝ))))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop).const_mul_atTop hc)
  have hconst : Filter.Tendsto (fun _ : ℕ => Real.exp (d * m)) Filter.atTop
      (nhds (Real.exp (d * m))) := tendsto_const_nhds
  have hproduct := hconst.mul hg
  have heq : (fun n : ℕ => Real.exp (d * m) * Real.exp (-((d ^ 2 / 2) * (n : ℝ)))) =
      (fun n : ℕ => Real.exp (d * m - d ^ 2 * (n : ℝ) / 2)) := by
    funext n
    rw [← Real.exp_add]
    congr 1
    ring
  have hdecay : Filter.Tendsto (fun n : ℕ => Real.exp (d * m - d ^ 2 * (n : ℝ) / 2))
      Filter.atTop (nhds 0) := by
    simpa only [heq, mul_zero] using hproduct
  apply squeeze_zero (fun n => integral_nonneg (fun ω => (Real.exp_pos _).le)) _ hdecay
  intro n
  simpa only [NNReal.coe_natCast] using
    truncated_terminal_exponential_le hB (n : ℝ≥0) d m hd.le
end ArgmaxBrownianTerminalRemainder
namespace ArgmaxBrownianCrossingProbability
open scoped Classical
theorem finite_horizon_hit_nullMeasurableSet
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (d m : ℝ) :
    NullMeasurableSet {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)} P := by
  obtain ⟨A, hA, hmax⟩ := ArgmaxBrownianFiniteMaximum.exists_aemeasurable_finite_maximum hB T d
  have hmeas : NullMeasurableSet {ω | m < A ω} P :=
    hA.nullMeasurableSet_preimage measurableSet_Ioi
  apply hmeas.congr
  filter_upwards [hmax] with ω hω
  apply propext
  constructor
  · intro hmA
    by_contra hnone
    have hupper : m ∈ upperBounds ((fun t : ℝ≥0 => B t ω - d * (t : ℝ)) '' Set.Icc 0 T) := by
      rintro y ⟨t, ht, rfl⟩
      exact le_of_not_gt (fun hhit => hnone ⟨t, ht.2, hhit⟩)
    exact (not_le_of_gt hmA) (hω.1.2 hupper)
  · rintro ⟨t, ht, hhit⟩
    exact hhit.trans_le (hω.1.1 ⟨t, ⟨bot_le, ht⟩, rfl⟩)
theorem finite_horizon_hit_decomposition
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (d m : ℝ) (hm : 0 ≤ m) :
    Real.exp (2 * d * m) *
      P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)} +
      (∫ ω in {ω | ¬ ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)},
        Real.exp ((2 * d) * (B T ω - d * (T : ℝ))) ∂P) = 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let E := {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)}
  let c := Real.exp (2 * d * m)
  let Z : Ω → ℝ := fun ω => Real.exp ((2 * d) * (B T ω - d * (T : ℝ)))
  let G : Ω → ℝ := fun ω => if ω ∈ E then c else Z ω
  have hE : NullMeasurableSet E P := finite_horizon_hit_nullMeasurableSet hB T d m
  have hc : Integrable (E.indicator (fun _ : Ω => c)) P := (integrable_const c).indicator₀ hE
  have hz : Integrable (Eᶜ.indicator Z) P :=
    (ArgmaxBrownianTerminalRemainder.exp_drift_integrable hB.toIsPreBrownianReal T d (2 * d)).indicator₀ hE.compl
  have hpoint : G = fun ω => E.indicator (fun _ : Ω => c) ω + Eᶜ.indicator Z ω := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [G, Set.indicator, hω]
  have hIntegral : (∫ ω, G ω ∂P) = P.real E * c + ∫ ω in Eᶜ, Z ω ∂P := by
    rw [hpoint, integral_add hc hz, integral_indicator₀ hE, integral_indicator₀ hE.compl]
    simp only [setIntegral_const, smul_eq_mul, measureReal_def]
  have hMean : (∫ ω, G ω ∂P) = 1 :=
    (ArgmaxBrownianStoppedHitting.finite_horizon_stopped_identity hB T d m hm).2
  change c * P.real E + (∫ ω in Eᶜ, Z ω ∂P) = 1
  rw [mul_comm c, ← hIntegral, hMean]
theorem finite_horizon_hit_residual_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (d m : ℝ) (hm : 0 ≤ m) :
    0 ≤ 1 - Real.exp (2 * d * m) *
      P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)} ∧
    1 - Real.exp (2 * d * m) *
      P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)} ≤
      ∫ ω in {ω | B T ω - d * (T : ℝ) ≤ m},
        Real.exp ((2 * d) * (B T ω - d * (T : ℝ))) ∂P := by
  let E := {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω - d * (t : ℝ)}
  let A := {ω | B T ω - d * (T : ℝ) ≤ m}
  let Z : Ω → ℝ := fun ω => Real.exp ((2 * d) * (B T ω - d * (T : ℝ)))
  have hsub : Eᶜ ⊆ A := by
    intro ω hω
    exact le_of_not_gt (fun hhit => hω ⟨T, le_rfl, hhit⟩)
  have hnonneg : 0 ≤ ∫ ω in Eᶜ, Z ω ∂P := integral_nonneg (fun ω => (Real.exp_pos _).le)
  have hmono : (∫ ω in Eᶜ, Z ω ∂P) ≤ ∫ ω in A, Z ω ∂P :=
    setIntegral_mono_set
      (ArgmaxBrownianTerminalRemainder.exp_drift_integrable hB.toIsPreBrownianReal T d (2 * d)).integrableOn
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall hsub)
  have hdecomp := finite_horizon_hit_decomposition hB T d m hm
  change Real.exp (2 * d * m) * P.real E + (∫ ω in Eᶜ, Z ω ∂P) = 1 at hdecomp
  constructor <;> linarith
theorem integer_horizon_hit_probability_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (d m : ℝ) (hd : 0 < d) (hm : 0 ≤ m) :
    Tendsto (fun n : ℕ => P.real {ω | ∃ t : ℝ≥0, t ≤ (n : ℝ≥0) ∧
      m < B t ω - d * (t : ℝ)}) atTop (𝓝 (Real.exp (-(2 * d * m)))) := by
  let p : ℕ → ℝ := fun n => P.real {ω | ∃ t : ℝ≥0, t ≤ (n : ℝ≥0) ∧
    m < B t ω - d * (t : ℝ)}
  let c := Real.exp (2 * d * m)
  have hc : c ≠ 0 := (Real.exp_pos _).ne'
  have herr : Tendsto (fun n : ℕ => 1 - c * p n) atTop (𝓝 0) := by
    apply squeeze_zero (fun (n : ℕ) => (finite_horizon_hit_residual_bound hB (n : ℝ≥0) d m hm).1)
      (fun (n : ℕ) => (finite_horizon_hit_residual_bound hB (n : ℝ≥0) d m hm).2)
    simpa only [NNReal.coe_natCast] using
      ArgmaxBrownianTerminalRemainder.truncated_terminal_exponential_tendsto_zero
        hB.toIsPreBrownianReal d m hd
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have ht := (hconst.sub herr).div_const c
  have hident : (fun n : ℕ => (1 - (1 - c * p n)) / c) = p := by
    funext n
    field_simp
    ring
  rw [hident] at ht
  have hlimit : ((1 : ℝ) - 0) / c = Real.exp (-(2 * d * m)) := by
    dsimp only [c]
    rw [sub_zero, one_div, Real.exp_neg]
  simpa only [hlimit] using ht
theorem alltime_hit_nullMeasurableSet
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (d m : ℝ) :
    NullMeasurableSet {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)} P := by
  have hUnion : (⋃ n : ℕ, {ω | ∃ t : ℝ≥0, t ≤ (n : ℝ≥0) ∧ m < B t ω - d * (t : ℝ)}) =
      {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨n, t, ht, hhit⟩ := Set.mem_iUnion.mp hω
      exact ⟨t, hhit⟩
    · rintro ⟨t, hhit⟩
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact Set.mem_iUnion.mpr ⟨n, t, hn, hhit⟩
  rw [← hUnion]
  exact NullMeasurableSet.iUnion (fun n => finite_horizon_hit_nullMeasurableSet hB (n : ℝ≥0) d m)
theorem alltime_strict_crossing_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (d m : ℝ) (hd : 0 < d) (hm : 0 ≤ m) :
    P.real {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)} =
      Real.exp (-(2 * d * m)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let E : ℕ → Set Ω := fun n => {ω | ∃ t : ℝ≥0, t ≤ (n : ℝ≥0) ∧ m < B t ω - d * (t : ℝ)}
  have hmono : Monotone E := by
    intro n k hnk ω hω
    obtain ⟨t, ht, hhit⟩ := hω
    exact ⟨t, ht.trans (by exact_mod_cast hnk), hhit⟩
  have hUnion : (⋃ n : ℕ, E n) = {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨n, t, ht, hhit⟩ := Set.mem_iUnion.mp hω
      exact ⟨t, hhit⟩
    · rintro ⟨t, hhit⟩
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact Set.mem_iUnion.mpr ⟨n, t, hn, hhit⟩
  have hprob := (ENNReal.tendsto_toReal (measure_ne_top P (⋃ n : ℕ, E n))).comp
    (tendsto_measure_iUnion_atTop hmono)
  have hprob' : Tendsto (fun n : ℕ => P.real (E n)) atTop
      (𝓝 (P.real {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)})) := by
    simpa only [Function.comp_def, measureReal_def, hUnion] using hprob
  exact tendsto_nhds_unique hprob' (integer_horizon_hit_probability_tendsto hB d m hd hm)
theorem alltime_strict_crossing_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (d m : ℝ) (hd : 0 < d) (hm : 0 ≤ m) :
    P {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)} =
      ENNReal.ofReal (Real.exp (-(2 * d * m))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  calc
    _ = ENNReal.ofReal (P.real {ω | ∃ t : ℝ≥0, m < B t ω - d * (t : ℝ)}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := congrArg ENNReal.ofReal (alltime_strict_crossing_tail hB d m hd hm)
end ArgmaxBrownianCrossingProbability
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology
namespace ArgmaxBrownianNegativeDriftMaximumLaw
open TopologicalSpace
open scoped Classical
theorem negative_drift_bddAbove_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (d : ℝ) (hd : 0 < d) :
    ∀ᵐ ω ∂P, BddAbove (Set.range (fun t : ℝ≥0 => B t ω - d * (t : ℝ))) := by
  let E := {ω | ¬ BddAbove (Set.range (fun t : ℝ≥0 => B t ω - d * (t : ℝ)))}
  have hbound (n : ℕ) : P E ≤ ENNReal.ofReal (Real.exp (-(2 * d * (n : ℝ)))) := by
    calc
      _ ≤ P {ω | ∃ t : ℝ≥0, (n : ℝ) < B t ω - d * (t : ℝ)} := by
        apply measure_mono
        intro ω hω
        obtain ⟨y, ⟨t, rfl⟩, hhit⟩ := not_bddAbove_iff.mp hω (n : ℝ)
        exact ⟨t, hhit⟩
      _ = _ := ArgmaxBrownianCrossingProbability.alltime_strict_crossing_measure
        hB d (n : ℝ) hd (Nat.cast_nonneg n)
  have hreal : Tendsto (fun n : ℕ => Real.exp (-(2 * d * (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop (by positivity : 0 < 2 * d))
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(2 * d * (n : ℝ)))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  have hzero : P E = 0 := le_antisymm
    (ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)) bot_le
  exact ae_iff.mpr hzero
theorem maximum_hasLaw_expMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (d : ℝ) (hd : 0 < d)
    (M : Ω → ℝ) (hM : AEMeasurable M P)
    (hmax : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => B t ω - d * (t : ℝ))) (M ω)) :
    HasLaw M (expMeasure (2 * d)) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure (P.map M) := Measure.isProbabilityMeasure_map hM
  have : IsProbabilityMeasure (expMeasure (2 * d)) := isProbabilityMeasure_expMeasure (by positivity)
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ M ω := by
    filter_upwards [hmax, hB.eval_zero_ae_eq_zero] with ω hω hzero
    have hb := hω.1 (Set.mem_range_self (0 : ℝ≥0))
    simpa only [hzero, NNReal.coe_zero, mul_zero, sub_zero] using hb
  have hEvent (a : ℝ) : {ω | a < M ω} =ᵐ[P]
      {ω | ∃ t : ℝ≥0, a < B t ω - d * (t : ℝ)} := by
    filter_upwards [hmax] with ω hω
    apply propext
    constructor
    · intro haM
      by_contra hnone
      have hupper : a ∈ upperBounds (Set.range (fun t : ℝ≥0 => B t ω - d * (t : ℝ))) := by
        rintro y ⟨t, rfl⟩
        exact le_of_not_gt (fun hhit => hnone ⟨t, hhit⟩)
      exact (not_le_of_gt haM) (hω.2 hupper)
    · rintro ⟨t, hhit⟩
      exact hhit.trans_le (hω.1 (Set.mem_range_self t))
  have htail (a : ℝ) (ha : 0 ≤ a) : P.real {ω | a < M ω} = Real.exp (-(2 * d * a)) :=
    (measureReal_congr (hEvent a)).trans
      (ArgmaxBrownianCrossingProbability.alltime_strict_crossing_tail hB d a hd ha)
  refine ⟨hM, ?_⟩
  apply Measure.eq_of_cdf
  ext a
  rw [cdf_eq_real, cdf_expMeasure_eq (by positivity : 0 < 2 * d)]
  rw [measureReal_def, Measure.map_apply_of_aemeasurable hM measurableSet_Iic]
  change P.real {ω | M ω ≤ a} = if 0 ≤ a then 1 - Real.exp (-((2 * d) * a)) else 0
  by_cases ha : 0 ≤ a
  · rw [if_pos ha]
    have hE : NullMeasurableSet {ω | a < M ω} P := nullMeasurableSet_lt aemeasurable_const hM
    have hcompl : {ω | M ω ≤ a} = {ω | a < M ω}ᶜ := by
      ext ω
      simp
    rw [hcompl, measureReal_compl₀ hE, probReal_univ, htail a ha]
  · rw [if_neg ha]
    have heq : {ω | M ω ≤ a} =ᵐ[P] (∅ : Set Ω) := by
      filter_upwards [hnonneg] with ω hω
      apply propext
      change (M ω ≤ a ↔ False)
      constructor
      · intro hle
        linarith
      · exact False.elim
    rw [measureReal_congr heq]
    simp
theorem exists_negative_drift_maximum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (d : ℝ) (hd : 0 < d) :
    ∃ M : Ω → ℝ, AEMeasurable M P ∧
      (∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => B t ω - d * (t : ℝ))) (M ω) ∧ 0 ≤ M ω) ∧
      HasLaw M (expMeasure (2 * d)) P := by
  let M : Ω → ℝ := fun ω => ⨆ n : ℕ,
    B (denseSeq ℝ≥0 n) ω - d * ((denseSeq ℝ≥0 n : ℝ≥0) : ℝ)
  have hM : AEMeasurable M P :=
    AEMeasurable.iSup (fun n => (hB.aemeasurable (denseSeq ℝ≥0 n)).sub_const _)
  have hLUB : ∀ᵐ ω ∂P, IsLUB (Set.range (fun t : ℝ≥0 => B t ω - d * (t : ℝ))) (M ω) := by
    filter_upwards [hB.cont, negative_drift_bddAbove_ae hB d hd] with ω hcont hbounded
    exact ArgmaxContinuousSupremumFunctional.isLUB_range_denseSeq_of_bddAbove
      (fun t : ℝ≥0 => B t ω - d * (t : ℝ))
      (hcont.sub (continuous_const.mul NNReal.continuous_coe)) hbounded
  refine ⟨M, hM, ?_, maximum_hasLaw_expMeasure hB d hd M hM hLUB⟩
  filter_upwards [hLUB, hB.eval_zero_ae_eq_zero] with ω hω hzero
  refine ⟨hω, ?_⟩
  have hb := hω.1 (Set.mem_range_self (0 : ℝ≥0))
  simpa only [hzero, NNReal.coe_zero, mul_zero, sub_zero] using hb
end ArgmaxBrownianNegativeDriftMaximumLaw
namespace ArgmaxActualTwoArmLaplace
theorem actual_two_arm_tail_laplace_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hArms : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (s : ℝ≥0) (d : ℝ) (hd : 0 < d) (H : ℝ → Ω → ℝ) (T : Ω → ℝ)
    (hplus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H (t : ℝ) ω = B t ω - d * (t : ℝ))
    (hminus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H (-(t : ℝ)) ω = C t ω - d * (t : ℝ))
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω) :
    ∃ M : Ω → ℝ, AEMeasurable M P ∧
      (∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Set.Icc 0 s) (M ω) ∧ 0 ≤ M ω) ∧
      (1 / 2 : ℝ) * (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) ≤ P.real {ω | (s : ℝ) < T ω} ∧
      P.real {ω | (s : ℝ) < T ω} ≤ (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) ∧
      (∀ᵐ ω ∂P, T ω ≠ (s : ℝ)) := by
  obtain ⟨A, _, hAp⟩ := ArgmaxBrownianFiniteMaximum.exists_aemeasurable_finite_maximum hB s d
  have hA := hAp.mono (fun ω h => h.1)
  obtain ⟨Y, _, hYp, hYlaw⟩ :=
    ArgmaxBrownianNegativeDriftMaximumLaw.exists_negative_drift_maximum (hB.shift s) d hd
  obtain ⟨L, _, hLp, hLlaw⟩ :=
    ArgmaxBrownianNegativeDriftMaximumLaw.exists_negative_drift_maximum hC d hd
  have hY := hYp.mono (fun ω h => h.1)
  have hL := hLp.mono (fun ω h => h.1)
  exact ArgmaxBrownianTailLaplaceBridge.two_arm_tail_sandwich_from_maximum_laws
    P B C hB hC hArms s d hd H T A Y L hplus hminus hA hY hL hYlaw hLlaw hmax
lemma complement_strict_tail_eq_mirrored_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : AEMeasurable T P) (x : ℝ)
    (hne : ∀ᵐ ω ∂P, T ω ≠ -x) :
    1 - P.real {ω | -x < T ω} = P.real {ω | x < -T ω} := by
  have hE : NullMeasurableSet {ω | -x < T ω} P :=
    nullMeasurableSet_lt aemeasurable_const hT
  have heq : {ω | -x < T ω}ᶜ =ᵐ[P] {ω | x < -T ω} := by
    filter_upwards [hne] with ω hω
    apply propext
    change (¬ -x < T ω) ↔ x < -T ω
    constructor
    · intro hn
      have hle := le_of_not_gt hn
      have hlt : T ω < -x := lt_of_le_of_ne hle hω
      linarith
    · intro hlt hn
      linarith
  have hc := measureReal_compl₀ hE
  rw [probReal_univ] at hc
  exact hc.symm.trans (measureReal_congr heq)
end ArgmaxActualTwoArmLaplace
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical
namespace ArgmaxPositiveMaximumLaplace
lemma exponential_nullSingleton (r : ℝ) : NullSingletonClass (expMeasure r) := by
  unfold expMeasure gammaMeasure
  infer_instance
lemma exponential_real_Iic (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (expMeasure r).real (Iic a) = 1 - Real.exp (-(r * a)) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← cdf_eq_real, cdf_expMeasure_eq hr, if_pos ha]
lemma exponential_real_Ici (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (expMeasure r).real (Ici a) = Real.exp (-(r * a)) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have : NullSingletonClass (expMeasure r) := exponential_nullSingleton r
  have hIio : (expMeasure r).real (Iio a) = 1 - Real.exp (-(r * a)) := by
    rw [measureReal_congr Iio_ae_eq_Iic]
    exact exponential_real_Iic r a hr ha
  rw [← compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ, hIio]
  ring
lemma setIntegral_exponential_Ioi (r c : ℝ) (hr : 0 < r) (hc : 0 ≤ c) (f : ℝ → ℝ) :
    (∫ y in Ioi c, f y ∂expMeasure r) =
      ∫ y in Ioi c, (r * Real.exp (-(r * y))) * f y := by
  change (∫ y in Ioi c, f y ∂volume.withDensity (exponentialPDF r)) = _
  have hm : Measurable (exponentialPDF r) := by unfold exponentialPDF; fun_prop
  have ht : ∀ᵐ y ∂volume.restrict (Ioi c), exponentialPDF r y < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hm ht f measurableSet_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change (exponentialPDF r y).toReal * f y = _
  rw [exponentialPDF_of_nonneg (hc.trans hy.le),
    ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos _).le)]
theorem integral_laplace_eq_exponential_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) :
    (∫ x, Real.exp (-(r * x)) ∂μ) =
      ∫ y, μ.real (Iic y) ∂expMeasure r := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  let E : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}
  let H : ℝ → ℝ → ℝ := fun x y => if x ≤ y then 1 else 0
  have hE : MeasurableSet E := measurableSet_le measurable_fst measurable_snd
  have hI : Integrable (Function.uncurry H) (μ.prod (expMeasure r)) :=
    (integrable_const (1 : ℝ)).indicator hE
  have hright (x : ℝ) : (∫ y, H x y ∂expMeasure r) = (expMeasure r).real (Ici x) := by
    change (∫ y, (Ici x).indicator (fun _ : ℝ => (1 : ℝ)) y ∂expMeasure r) = _
    exact integral_indicator_one measurableSet_Ici
  have hleft (y : ℝ) : (∫ x, H x y ∂μ) = μ.real (Iic y) := by
    change (∫ x, (Iic y).indicator (fun _ : ℝ => (1 : ℝ)) x ∂μ) = _
    exact integral_indicator_one measurableSet_Iic
  calc
    _ = ∫ x, (expMeasure r).real (Ici x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hnonneg] with x hx
      exact (exponential_real_Ici r x hr hx).symm
    _ = ∫ x, ∫ y, H x y ∂expMeasure r ∂μ := by simp_rw [hright]
    _ = ∫ y, ∫ x, H x y ∂μ ∂expMeasure r := integral_integral_swap hI
    _ = _ := by simp_rw [hleft]
theorem integral_laplace_eq_cdf_integral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) :
    (∫ x, Real.exp (-(r * x)) ∂μ) =
      ∫ m : ℝ in Ioi 0, (r * Real.exp (-(r * m))) * μ.real (Iic m) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hzero : (expMeasure r) (Iic (0 : ℝ)) = 0 := by
    have hz : ((expMeasure r) (Iic (0 : ℝ))).toReal = 0 := by
      have h := exponential_real_Iic r 0 hr le_rfl
      simpa only [measureReal_def, mul_zero, neg_zero, Real.exp_zero, sub_self] using h
    exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)
  have hpos : ∀ᵐ y ∂expMeasure r, y ∈ Ioi (0 : ℝ) := by
    apply ae_iff.mpr
    have heq : {y : ℝ | ¬ y ∈ Ioi (0 : ℝ)} = Iic 0 := by
      ext y
      simp
    rw [heq]
    exact hzero
  calc
    _ = ∫ y, μ.real (Iic y) ∂expMeasure r := integral_laplace_eq_exponential_cdf μ r hr hnonneg
    _ = ∫ y in Ioi 0, μ.real (Iic y) ∂expMeasure r :=
      (setIntegral_eq_integral_of_ae_compl_eq_zero
        (hpos.mono (fun _ hy hnot => (hnot hy).elim))).symm
    _ = _ := setIntegral_exponential_Ioi r 0 hr le_rfl _
theorem random_laplace_eq_cdf_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : AEMeasurable M P) (hnonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (r : ℝ) (hr : 0 < r) :
    (∫ ω, Real.exp (-(r * M ω)) ∂P) =
      ∫ m : ℝ in Ioi 0, (r * Real.exp (-(r * m))) * P.real {ω | M ω ≤ m} := by
  let μ := P.map M
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hM
  have hLaw : HasLaw M μ P := ⟨hM, rfl⟩
  have hsupport : ∀ᵐ x ∂μ, 0 ≤ x := (ae_map_iff hM measurableSet_Ici).mpr hnonneg
  calc
    _ = ∫ x, Real.exp (-(r * x)) ∂μ := hLaw.integral_comp (by fun_prop)
    _ = ∫ m : ℝ in Ioi 0, (r * Real.exp (-(r * m))) * μ.real (Iic m) :=
      integral_laplace_eq_cdf_integral μ r hr hsupport
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro m _
      dsimp only
      congr 1
      change (P.map M).real (Iic m) = _
      rw [map_measureReal_apply_of_aemeasurable hM measurableSet_Iic]
      congr 1
end ArgmaxPositiveMaximumLaplace
open MeasureTheory Set
namespace ArgmaxContinuousLaplaceIntegral
lemma integral_sq_exp (d : ℝ) (hd : 0 < d) :
    (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-(d * m))) = 2 / d ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := d) (by norm_num) hd
  norm_num at h
  simpa only [one_div_pow, one_pow, mul_comm, div_eq_mul_inv] using h
lemma integrableOn_sq_exp (d : ℝ) (hd : 0 < d) :
    IntegrableOn (fun m : ℝ => m ^ 2 * Real.exp (-(d * m))) (Ioi 0) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_sq_exp d hd] at hz
  exact (ne_of_gt (div_pos (by norm_num) (pow_pos hd 3))) hz
lemma laplace_integrand_le (d x m : ℝ) (hx : 0 < x) :
    m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x)) ≤ m ^ 2 * Real.exp (-(d * m)) := by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg m)
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ m ^ 2 / (2 * x) := by positivity
  linarith
theorem laplace_integrable (d x : ℝ) (hd : 0 < d) (hx : 0 < x) :
    IntegrableOn (fun m : ℝ => m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x))) (Ioi 0) := by
  apply (integrableOn_sq_exp d hd).mono_nonneg (by fun_prop)
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · exact Filter.Eventually.of_forall (laplace_integrand_le d x · hx)
theorem laplace_integral_upper (d x : ℝ) (hd : 0 < d) (hx : 0 < x) :
    (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x))) ≤ 2 / d ^ 3 := by
  rw [← integral_sq_exp d hd]
  exact setIntegral_mono_on (laplace_integrable d x hd hx) (integrableOn_sq_exp d hd)
    measurableSet_Ioi (fun m _ => laplace_integrand_le d x m hx)
lemma laplace_integrand_lower_unit (d x m : ℝ) (hd : 0 < d) (hx : 1 ≤ x)
    (hm : m ∈ Ioc 1 2) :
    Real.exp (-2 * d - 2) ≤ m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x)) := by
  have hm1 : 1 < m := hm.1
  have hm2 : m ≤ 2 := hm.2
  have hdiv : m ^ 2 / (2 * x) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * x)).mpr
    nlinarith
  have hdm : d * m ≤ 2 * d := by nlinarith
  have he : Real.exp (-2 * d - 2) ≤ Real.exp (-d * m - m ^ 2 / (2 * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hs : (1 : ℝ) ≤ m ^ 2 := by nlinarith
  exact he.trans (by nlinarith [Real.exp_pos (-d * m - m ^ 2 / (2 * x))])
theorem laplace_integral_lower (d x : ℝ) (hd : 0 < d) (hx : 1 ≤ x) :
    Real.exp (-2 * d - 2) ≤
      ∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x)) := by
  have hi := laplace_integrable d x hd (by linarith)
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioi 0 := by intro m hm; exact lt_trans zero_lt_one hm.1
  have hu := setIntegral_ge_of_const_le_real (μ := volume) measurableSet_Ioc (by simp)
    (fun m hm => laplace_integrand_lower_unit d x m hd hx hm) (hi.mono_set hsub)
  have hu' : Real.exp (-2 * d - 2) ≤
      ∫ m : ℝ in Ioc 1 2, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x)) := by
    simpa only [Real.volume_real_Ioc, sub_self, max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using hu
  refine hu'.trans (setIntegral_mono_set hi ?_ ?_)
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · exact Filter.Eventually.of_forall (fun m hm => hsub hm)
end ArgmaxContinuousLaplaceIntegral
namespace ArgmaxLaplaceKernelIntegrationByParts
open MeasureTheory Set Filter
open scoped Topology
lemma integral_mul_exp (d : ℝ) (hd : 0 < d) :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-d * x)) = 1 / d ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := d) (by norm_num) hd
  norm_num at h
  simpa only [← neg_mul, one_div] using h
lemma integrableOn_mul_exp (d : ℝ) (hd : 0 < d) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-d * x)) (Ioi 0) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_mul_exp d hd] at hz
  exact (ne_of_gt (div_pos (by norm_num) (pow_pos hd 2))) hz
lemma kernel_le_exp (d T x : ℝ) (hT : 0 < T) :
    Real.exp (-d * x - x ^ 2 / (2 * T)) ≤ Real.exp (-d * x) := by
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ x ^ 2 / (2 * T) := by positivity
  linarith
lemma integrableOn_kernel (d T : ℝ) (hd : 0 < d) (hT : 0 < T) :
    IntegrableOn (fun x : ℝ => Real.exp (-d * x - x ^ 2 / (2 * T))) (Ioi 0) := by
  have hi := integrableOn_exp_mul_Ioi (by linarith : -d < 0) (0 : ℝ)
  exact hi.mono_nonneg (by fun_prop)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (kernel_le_exp d T · hT))
lemma integrableOn_mul_kernel (d T : ℝ) (hd : 0 < d) (hT : 0 < T) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-d * x - x ^ 2 / (2 * T))) (Ioi 0) := by
  apply (integrableOn_mul_exp d hd).mono_nonneg (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hx.le (Real.exp_pos _).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_le_mul_of_nonneg_left (kernel_le_exp d T x hT) hx.le
theorem signed_kernel_integral_eq_positive_second_moment
    (d T : ℝ) (hd : 0 < d) (hT : 0 < T) :
    (∫ x : ℝ in Ioi 0, (1 - d * x) * Real.exp (-d * x - x ^ 2 / (2 * T))) =
      (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-d * x - x ^ 2 / (2 * T))) / T := by
  let K : ℝ → ℝ := fun x => Real.exp (-d * x - x ^ 2 / (2 * T))
  have hK0 : IntegrableOn K (Ioi 0) := integrableOn_kernel d T hd hT
  have hK1 : IntegrableOn (fun x => x * K x) (Ioi 0) := integrableOn_mul_kernel d T hd hT
  have hK2 : IntegrableOn (fun x => x ^ 2 * K x) (Ioi 0) :=
    ArgmaxContinuousLaplaceIntegral.laplace_integrable d T hd hT
  have hderiv (x : ℝ) : HasDerivAt (fun y => y * K y)
      ((1 - d * x - x ^ 2 / T) * K x) x := by
    dsimp only [K]
    convert (hasDerivAt_id x).mul
      (((hasDerivAt_id x).const_mul (-d)).sub
        (((hasDerivAt_id x).pow 2).div_const (2 * T))).exp using 1
    · rfl
    · rfl
    · funext y
      rfl
    · dsimp only [id_eq, Pi.sub_apply, Pi.pow_apply]
      norm_num
      field_simp [hT.ne']
      ring
  have hdi : IntegrableOn (fun x => (1 - d * x - x ^ 2 / T) * K x) (Ioi 0) := by
    convert (hK0.sub (hK1.const_mul d)).sub (hK2.div_const T) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hupper : Tendsto (fun x : ℝ => x * Real.exp (-d * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) d hd
  have hlim : Tendsto (fun x : ℝ => x * K x) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hupper
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact mul_nonneg hx (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact mul_le_mul_of_nonneg_left (kernel_le_exp d T x hT) hx
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (m := (0 : ℝ)) (fun x _ => hderiv x) hdi hlim
  simp only [zero_mul, sub_self] at hFTC
  have hsplit : (∫ x : ℝ in Ioi 0, (1 - d * x - x ^ 2 / T) * K x) =
      (∫ x : ℝ in Ioi 0, K x) - d * (∫ x : ℝ in Ioi 0, x * K x) -
        (∫ x : ℝ in Ioi 0, x ^ 2 * K x) / T := by
    calc
      _ = ∫ x : ℝ in Ioi 0, K x - d * (x * K x) - (x ^ 2 * K x) / T := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := by
        have heq1 := integral_sub (hK0.sub (hK1.const_mul d)) (hK2.div_const T)
        have heq2 := integral_sub hK0 (hK1.const_mul d)
        simp only [Pi.sub_apply] at heq1 heq2
        rw [heq1, heq2, integral_const_mul, integral_div]
  have hleft : (∫ x : ℝ in Ioi 0, (1 - d * x) * K x) =
      (∫ x : ℝ in Ioi 0, K x) - d * (∫ x : ℝ in Ioi 0, x * K x) := by
    calc
      _ = ∫ x : ℝ in Ioi 0, K x - d * (x * K x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = _ := by
        have heq := integral_sub hK0 (hK1.const_mul d)
        rw [heq, integral_const_mul]
  change (∫ x : ℝ in Ioi 0, (1 - d * x) * K x) = _
  rw [hleft]
  rw [hsplit] at hFTC
  linarith
end ArgmaxLaplaceKernelIntegrationByParts
namespace ArgmaxGaussianLaplaceJNormalization
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
lemma reflected_gaussian_pdf_kernel (d : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (u : ℝ) :
    gaussianPDFReal (d * (v : ℝ)) v (-u) =
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(d ^ 2 * (v : ℝ) / 2))) *
        Real.exp (-d * u - u ^ 2 / (2 * (v : ℝ))) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have he : -(-u - d * (v : ℝ)) ^ 2 / (2 * (v : ℝ)) =
      -(d ^ 2 * (v : ℝ) / 2) + (-d * u - u ^ 2 / (2 * (v : ℝ))) := by
    field_simp
    ring
  rw [gaussianPDFReal, he, Real.exp_add]
  ring
lemma sqrt_denominator_identity (v : ℝ≥0) (hv : v ≠ 0) :
    Real.sqrt (2 * Real.pi * (v : ℝ)) * (v : ℝ) =
      Real.sqrt (2 * Real.pi) * (v : ℝ) ^ ((3 : ℝ) / 2) := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hpow : (v : ℝ) ^ ((3 : ℝ) / 2) = (v : ℝ) * Real.sqrt (v : ℝ) := by
    calc
      _ = (v : ℝ) ^ ((1 : ℝ) + 1 / 2) := by congr 1; norm_num
      _ = (v : ℝ) ^ (1 : ℝ) * (v : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_add hvpos _ _
      _ = _ := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), hpow]
  ring
theorem signed_gaussian_integral_eq_J
    (d : ℝ) (hd : 0 < d) (v : ℝ≥0) (hv : v ≠ 0) :
    2 * (∫ u : ℝ in Ioi 0, (1 - d * u) * gaussianPDFReal (d * (v : ℝ)) v (-u)) =
      (2 * Real.exp (-(d ^ 2 * (v : ℝ) / 2)) /
        (Real.sqrt (2 * Real.pi) * (v : ℝ) ^ ((3 : ℝ) / 2))) *
      (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-d * u - u ^ 2 / (2 * (v : ℝ)))) := by
  let C := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(d ^ 2 * (v : ℝ) / 2))
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hfun : (fun u : ℝ => (1 - d * u) * gaussianPDFReal (d * (v : ℝ)) v (-u)) =
      (fun u : ℝ => C * ((1 - d * u) * Real.exp (-d * u - u ^ 2 / (2 * (v : ℝ))))) := by
    funext u
    rw [reflected_gaussian_pdf_kernel d v hv u]
    dsimp only [C]
    ring
  rw [hfun, integral_const_mul,
    ArgmaxLaplaceKernelIntegrationByParts.signed_kernel_integral_eq_positive_second_moment d (v : ℝ) hd hvpos]
  have hcoef : 2 * C / (v : ℝ) =
      2 * Real.exp (-(d ^ 2 * (v : ℝ) / 2)) /
        (Real.sqrt (2 * Real.pi) * (v : ℝ) ^ ((3 : ℝ) / 2)) := by
    rw [← sqrt_denominator_identity v hv]
    dsimp only [C]
    field_simp
  calc
    _ = (2 * C / (v : ℝ)) *
        (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-d * u - u ^ 2 / (2 * (v : ℝ)))) := by ring
    _ = _ := by rw [hcoef]
end ArgmaxGaussianLaplaceJNormalization
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace ArgmaxGaussianCDFCancellation
theorem integral_negative_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hi : Integrable (fun y : ℝ => y) μ) :
    (∫ m : ℝ in Ioi 0, μ.real (Iic (-m))) = ∫ y : ℝ in Iio 0, -y ∂μ := by
  have hf : Integrable (fun y : ℝ => max (-y) 0) μ := by
    apply (hi.neg.sup (integrable_const (0 : ℝ))).congr
    exact Filter.Eventually.of_forall (fun y => rfl)
  have hsets (m : ℝ) (hm : 0 < m) : {y : ℝ | m ≤ max (-y) 0} = Iic (-m) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Iic, le_max_iff]
    constructor
    · rintro (hy | hz) <;> linarith
    · intro hy
      exact Or.inl (by linarith)
  calc
    _ = ∫ m : ℝ in Ioi 0, μ.real {y : ℝ | m ≤ max (-y) 0} := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro m hm
      dsimp only
      rw [hsets m hm]
    _ = ∫ y : ℝ, max (-y) 0 ∂μ :=
      (hf.integral_eq_integral_meas_le (Filter.Eventually.of_forall (fun y => le_max_right (-y) 0))).symm
    _ = _ := by
      rw [← integral_indicator measurableSet_Iio]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only
        by_cases hy : y < 0
        · simp [Set.indicator, hy, max_eq_left (by linarith : 0 ≤ -y)]
        · simp [Set.indicator, hy, max_eq_right (by linarith : -y ≤ 0)])
lemma setIntegral_gaussian_density
    (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (E : Set ℝ) (hE : MeasurableSet E) (f : ℝ → ℝ) :
    (∫ y in E, f y ∂gaussianReal a v) = ∫ y in E, gaussianPDFReal a v y * f y := by
  rw [← integral_indicator hE, integral_gaussianReal_eq_integral_smul hv, ← integral_indicator hE]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    by_cases hy : y ∈ E <;> simp [Set.indicator, hy, smul_eq_mul])
lemma reflected_gaussian_density_tilt (v : ℝ≥0) (hv : v ≠ 0) (d y : ℝ) :
    Real.exp (-(2 * d * y)) * gaussianPDFReal (d * (v : ℝ)) v y =
      gaussianPDFReal (d * (v : ℝ)) v (-y) := by
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  field_simp
  ring
lemma gaussian_real_Iic_eq_density (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (b : ℝ) :
    (gaussianReal a v).real (Iic b) = ∫ y in Iic b, gaussianPDFReal a v y := by
  rw [measureReal_def, gaussianReal_apply_eq_integral a hv]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun y => gaussianPDFReal_nonneg a v y))
theorem gaussian_weighted_positive_tail
    (v : ℝ≥0) (hv : v ≠ 0) (d : ℝ) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-((2 * d) * y)) ∂gaussianReal (d * (v : ℝ)) v) =
      (gaussianReal (d * (v : ℝ)) v).real (Iic 0) := by
  rw [setIntegral_gaussian_density _ _ hv _ measurableSet_Ioi]
  have hp (y : ℝ) : gaussianPDFReal (d * (v : ℝ)) v y * Real.exp (-((2 * d) * y)) =
      gaussianPDFReal (d * (v : ℝ)) v (-y) := by
    rw [mul_comm]
    exact reflected_gaussian_density_tilt v hv d y
  simp_rw [hp]
  rw [integral_comp_neg_Ioi, neg_zero, gaussian_real_Iic_eq_density _ _ hv]
theorem gaussian_negative_cdf_moment
    (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ m : ℝ in Ioi 0, (gaussianReal a v).real (Iic (-m))) =
      ∫ u : ℝ in Ioi 0, u * gaussianPDFReal a v (-u) := by
  rw [integral_negative_cdf (gaussianReal a v) IsGaussian.integrable_fun_id,
    setIntegral_gaussian_density a v hv _ measurableSet_Iio]
  rw [← integral_Iic_eq_integral_Iio]
  calc
    _ = ∫ u : ℝ in Ioi 0, gaussianPDFReal a v (-u) * u := by
      have hn := integral_comp_neg_Ioi (0 : ℝ) (fun y : ℝ => gaussianPDFReal a v y * -y)
      simpa only [neg_zero, neg_neg] using hn.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      ring
end ArgmaxGaussianCDFCancellation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Classical
namespace ArgmaxClampedCDFLaplace
theorem clamped_laplace_eq_cdf_integral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r) :
    (∫ x, Real.exp (-(r * max 0 x)) ∂μ) =
      ∫ m : ℝ in Ioi 0, (r * Real.exp (-(r * m))) * μ.real (Iic m) := by
  have hM : AEMeasurable (fun x : ℝ => max 0 x) μ := by fun_prop
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ max 0 x := Filter.Eventually.of_forall (fun x => le_max_left 0 x)
  calc
    _ = ∫ m : ℝ in Ioi 0, (r * Real.exp (-(r * m))) * μ.real {x | max 0 x ≤ m} :=
      ArgmaxPositiveMaximumLaplace.random_laplace_eq_cdf_integral
        (fun x : ℝ => max 0 x) hM hnonneg r hr
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro m hm
      have hset : {x : ℝ | max 0 x ≤ m} = Iic m := by
        ext x
        change (max 0 x ≤ m ↔ x ≤ m)
        exact ⟨fun hx => (le_max_right 0 x).trans hx,
          fun hx => max_le (show 0 < m from hm).le hx⟩
      dsimp only
      rw [hset]
theorem weighted_cdf_integral_eq_split
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r) :
    (∫ m : ℝ in Ioi 0, (r * Real.exp (-(r * m))) * μ.real (Iic m)) =
      μ.real (Iic 0) + ∫ x : ℝ in Ioi 0, Real.exp (-(r * x)) ∂μ := by
  let f : ℝ → ℝ := fun x => Real.exp (-(r * max 0 x))
  have hi : Integrable f μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg hr.le (le_max_left 0 x)))
  rw [← clamped_laplace_eq_cdf_integral μ r hr]
  calc
    _ = (∫ x in Iic 0, f x ∂μ) + ∫ x in Ioi 0, f x ∂μ := by
      symm
      simpa only [compl_Iic] using integral_add_compl (μ := μ) (s := Iic (0 : ℝ)) measurableSet_Iic hi
    _ = _ := by
      congr 1
      · calc
          _ = ∫ x : ℝ in Iic 0, (1 : ℝ) ∂μ := by
            apply setIntegral_congr_fun measurableSet_Iic
            intro x hx
            dsimp only [f]
            rw [max_eq_left (show x ≤ 0 from hx)]
            norm_num
          _ = _ := by simp
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only [f]
        rw [max_eq_right (show 0 < x from hx).le]
end ArgmaxClampedCDFLaplace
namespace ArgmaxGaussianCDFCancellation
lemma weighted_cdf_integrableOn
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun m : ℝ => (r * Real.exp (-(r * m))) * μ.real (Iic m)) (Ioi 0) := by
  have hmeas : Measurable (fun m : ℝ => μ.real (Iic m)) := by
    have heq : (fun m : ℝ => μ.real (Iic m)) = (fun m : ℝ => cdf μ m) :=
      funext (fun m => (cdf_eq_real μ m).symm)
    rw [heq]
    exact (monotone_cdf (μ := μ)).measurable
  have hw : IntegrableOn (fun m : ℝ => r * Real.exp (-(r * m))) (Ioi 0) := by
    apply ((exp_neg_integrableOn_Ioi (0 : ℝ) hr).const_mul r).congr
    exact Filter.Eventually.of_forall (fun m => by
      change r * Real.exp (-r * m) = r * Real.exp (-(r * m))
      rw [neg_mul])
  apply hw.mono' (((by fun_prop : Measurable (fun m : ℝ => r * Real.exp (-(r * m)))).mul hmeas).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun m => by
    have hc0 : 0 ≤ μ.real (Iic m) := measureReal_nonneg
    have hc1 : μ.real (Iic m) ≤ 1 := by rw [← cdf_eq_real]; exact cdf_le_one μ m
    have hw0 : 0 ≤ r * Real.exp (-(r * m)) := mul_nonneg hr.le (Real.exp_pos _).le
    change ‖(r * Real.exp (-(r * m))) * μ.real (Iic m)‖ ≤ r * Real.exp (-(r * m))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 hc0)]
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hc1)])
lemma integrable_gaussian_density_mul
    (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal a v)) :
    Integrable (fun y => gaussianPDFReal a v y * f y) := by
  rw [gaussianReal_of_var_ne_zero a hv] at hf
  have h := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF a v)
    (Filter.Eventually.of_forall (fun y => gaussianPDF_lt_top))).mp hf
  simp_rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg a v _), smul_eq_mul] at h
  exact h
lemma integrable_reflected_gaussian_density_and_moment
    (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun u : ℝ => gaussianPDFReal a v (-u)) ∧
      Integrable (fun u : ℝ => u * gaussianPDFReal a v (-u)) := by
  have hneg : MeasurePreserving (fun y : ℝ => -y) volume volume :=
    ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  have hp := hneg.integrable_comp_of_integrable (integrable_gaussianPDFReal a v)
  have hm := hneg.integrable_comp_of_integrable
    (integrable_gaussian_density_mul a v hv (fun y => y) IsGaussian.integrable_fun_id)
  refine ⟨hp, ?_⟩
  apply hm.neg.congr
  exact Filter.Eventually.of_forall (fun u => by
    change -(gaussianPDFReal a v (-u) * (-u)) = u * gaussianPDFReal a v (-u)
    ring)
theorem gaussian_weighted_cdf_integral
    (v : ℝ≥0) (hv : v ≠ 0) (d : ℝ) (hd : 0 < d) :
    (∫ m : ℝ in Ioi 0, ((2 * d) * Real.exp (-((2 * d) * m))) *
      (gaussianReal (d * (v : ℝ)) v).real (Iic m)) =
        2 * (gaussianReal (d * (v : ℝ)) v).real (Iic 0) := by
  rw [ArgmaxClampedCDFLaplace.weighted_cdf_integral_eq_split _ (2 * d) (by positivity),
    gaussian_weighted_positive_tail v hv d]
  ring
end ArgmaxGaussianCDFCancellation
open MeasureTheory Set
open scoped ENNReal
namespace ArgmaxCDFIntegrability
theorem integrableOn_negative_cdf
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hi : Integrable (fun y : ℝ => y) μ) :
    IntegrableOn (fun m : ℝ => μ.real (Iic (-m))) (Ioi 0) := by
  let f : ℝ → ℝ := fun y => max (-y) 0
  have hf : Integrable f μ := by
    apply (hi.neg.sup (integrable_const (0 : ℝ))).congr
    exact Filter.Eventually.of_forall (fun y => rfl)
  have hsets (m : ℝ) (hm : 0 < m) : {y : ℝ | m ≤ f y} = Iic (-m) := by
    ext y
    simp only [f, Set.mem_ofPred_eq, Set.mem_Iic, le_max_iff]
    constructor
    · rintro (hy | hz) <;> linarith
    · intro hy
      exact Or.inl (by linarith)
  have hcake := lintegral_eq_lintegral_meas_le μ
    (Filter.Eventually.of_forall (fun y => le_max_right (-y) 0)) hf.aemeasurable
  have hfinite : (∫⁻ m : ℝ in Ioi 0, μ {y : ℝ | m ≤ f y}) < ∞ := by
    rw [← hcake]
    exact hf.lintegral_lt_top
  have hanti : Antitone (fun m : ℝ => μ.real (Iic (-m))) := by
    intro x y hxy
    exact measureReal_mono (Iic_subset_Iic.mpr (neg_le_neg hxy))
  have hnonneg : ∀ m : ℝ, 0 ≤ μ.real (Iic (-m)) := fun _ => measureReal_nonneg
  refine ⟨hanti.measurable.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mpr
  convert hfinite using 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro m hm
  dsimp only
  rw [hsets m hm]
  change ENNReal.ofReal ((μ (Iic (-m))).toReal) = μ (Iic (-m))
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)
end ArgmaxCDFIntegrability
namespace ArgmaxGaussianCDFCancellation
lemma reflected_gaussian_density_integral
    (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ u : ℝ in Ioi 0, gaussianPDFReal a v (-u)) = (gaussianReal a v).real (Iic 0) := by
  rw [integral_comp_neg_Ioi, neg_zero, gaussian_real_Iic_eq_density a v hv]
lemma signed_gaussian_integral_as_moments
    (v : ℝ≥0) (hv : v ≠ 0) (d : ℝ) :
    2 * (∫ u : ℝ in Ioi 0, (1 - d * u) * gaussianPDFReal (d * (v : ℝ)) v (-u)) =
      2 * (gaussianReal (d * (v : ℝ)) v).real (Iic 0) -
        (2 * d) * (∫ u : ℝ in Ioi 0, u * gaussianPDFReal (d * (v : ℝ)) v (-u)) := by
  have h := integrable_reflected_gaussian_density_and_moment (d * (v : ℝ)) v hv
  have hp : IntegrableOn (fun u : ℝ => gaussianPDFReal (d * (v : ℝ)) v (-u)) (Ioi 0) := h.1.integrableOn
  have hm : IntegrableOn (fun u : ℝ => u * gaussianPDFReal (d * (v : ℝ)) v (-u)) (Ioi 0) := h.2.integrableOn
  calc
    _ = 2 * (∫ u : ℝ in Ioi 0, gaussianPDFReal (d * (v : ℝ)) v (-u) -
        d * (u * gaussianPDFReal (d * (v : ℝ)) v (-u))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      ring
    _ = _ := by
      rw [integral_sub hp (hm.const_mul d), integral_const_mul,
        reflected_gaussian_density_integral _ v hv]
      ring
theorem reflected_gaussian_cdf_cancellation
    (v : ℝ≥0) (hv : v ≠ 0) (d : ℝ) (hd : 0 < d) :
    (∫ m : ℝ in Ioi 0, ((2 * d) * Real.exp (-((2 * d) * m))) *
      ((gaussianReal (d * (v : ℝ)) v).real (Iic m) -
        Real.exp ((2 * d) * m) * (gaussianReal (d * (v : ℝ)) v).real (Iic (-m)))) =
      2 * (∫ u : ℝ in Ioi 0, (1 - d * u) * gaussianPDFReal (d * (v : ℝ)) v (-u)) := by
  have hneg := ArgmaxCDFIntegrability.integrableOn_negative_cdf
    (gaussianReal (d * (v : ℝ)) v) IsGaussian.integrable_fun_id
  have hpoint (m : ℝ) :
      ((2 * d) * Real.exp (-((2 * d) * m))) *
        ((gaussianReal (d * (v : ℝ)) v).real (Iic m) -
          Real.exp ((2 * d) * m) * (gaussianReal (d * (v : ℝ)) v).real (Iic (-m))) =
      ((2 * d) * Real.exp (-((2 * d) * m))) * (gaussianReal (d * (v : ℝ)) v).real (Iic m) -
        (2 * d) * (gaussianReal (d * (v : ℝ)) v).real (Iic (-m)) := by
    have he : Real.exp (-((2 * d) * m)) * Real.exp ((2 * d) * m) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      _ = ((2 * d) * Real.exp (-((2 * d) * m))) * (gaussianReal (d * (v : ℝ)) v).real (Iic m) -
          (2 * d) * (Real.exp (-((2 * d) * m)) * Real.exp ((2 * d) * m)) *
            (gaussianReal (d * (v : ℝ)) v).real (Iic (-m)) := by ring
      _ = _ := by rw [he, mul_one]
  simp_rw [hpoint]
  rw [integral_sub (weighted_cdf_integrableOn _ (2 * d) (by positivity)) (hneg.const_mul (2 * d)),
    integral_const_mul, gaussian_weighted_cdf_integral v hv d hd,
    gaussian_negative_cdf_moment _ v hv]
  exact (signed_gaussian_integral_as_moments v hv d).symm
end ArgmaxGaussianCDFCancellation
namespace ArgmaxPositiveMaximumLaplaceAssembly
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
theorem laplace_eq_gaussian_cdf_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : AEMeasurable M P) (hnonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (d : ℝ) (hd : 0 < d) (v : ℝ≥0)
    (hCDF : ∀ m : ℝ, 0 ≤ m →
      P.real {ω | M ω ≤ m} = (gaussianReal (d * (v : ℝ)) v).real (Iic m) -
        Real.exp ((2 * d) * m) * (gaussianReal (d * (v : ℝ)) v).real (Iic (-m))) :
    (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) =
      ∫ m : ℝ in Ioi 0, ((2 * d) * Real.exp (-((2 * d) * m))) *
        ((gaussianReal (d * (v : ℝ)) v).real (Iic m) -
          Real.exp ((2 * d) * m) * (gaussianReal (d * (v : ℝ)) v).real (Iic (-m))) := by
  rw [ArgmaxPositiveMaximumLaplace.random_laplace_eq_cdf_integral M hM hnonneg
    (2 * d) (by positivity)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro m hm
  dsimp only
  rw [hCDF m (show 0 < m from hm).le]
theorem laplace_eq_J_of_gaussian_cdf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : AEMeasurable M P) (hnonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (d : ℝ) (hd : 0 < d) (v : ℝ≥0) (hv : v ≠ 0)
    (hCDF : ∀ m : ℝ, 0 ≤ m →
      P.real {ω | M ω ≤ m} = (gaussianReal (d * (v : ℝ)) v).real (Iic m) -
        Real.exp ((2 * d) * m) * (gaussianReal (d * (v : ℝ)) v).real (Iic (-m))) :
    (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) =
      (2 * Real.exp (-(d ^ 2 * (v : ℝ) / 2)) /
        (Real.sqrt (2 * Real.pi) * (v : ℝ) ^ ((3 : ℝ) / 2))) *
      (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-d * u - u ^ 2 / (2 * (v : ℝ)))) := by
  rw [laplace_eq_gaussian_cdf_integral M hM hnonneg d hd v hCDF]
  exact (ArgmaxGaussianCDFCancellation.reflected_gaussian_cdf_cancellation v hv d hd).trans
    (ArgmaxGaussianLaplaceJNormalization.signed_gaussian_integral_eq_J d hd v hv)
end ArgmaxPositiveMaximumLaplaceAssembly
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ArgmaxBrownianReflection
theorem finite_past_increment_neg_identDistrib
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s T : ℝ≥0) (hsT : s ≤ T) (τ : ι → ℝ≥0) (hτ : ∀ i, τ i ≤ s) :
    IdentDistrib
      (fun ω => (((fun i => B (τ i) ω), B s ω), B T ω - B s ω))
      (fun ω => (((fun i => B (τ i) ω), B s ω), -(B T ω - B s ω))) P P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let F : Ω → (ι → ℝ) × ℝ := fun ω => ((fun i => B (τ i) ω), B s ω)
  let Y : Ω → ℝ := fun ω => B T ω - B s ω
  have hF : AEMeasurable F P :=
    (aemeasurable_pi_lambda _ (fun i => hB.aemeasurable (τ i))).prodMk (hB.aemeasurable s)
  have hYlaw : HasLaw Y (gaussianReal 0 (T - s)) P := by
    simpa only [Y, add_tsub_cancel_of_le hsT] using (hB.shift s).hasLaw_eval (T - s)
  have hYsymm : IdentDistrib Y (fun ω => -Y ω) P P :=
    hYlaw.identDistrib (by simpa only [neg_zero, Pi.neg_def] using gaussianReal_neg hYlaw)
  have hpast : Measurable (fun f : Set.Iic s → ℝ =>
      ((fun i => f ⟨τ i, hτ i⟩), f ⟨s, by simp⟩)) := by fun_prop
  have hfuture : Measurable (fun f : ℝ≥0 → ℝ => f (T - s)) := measurable_pi_apply _
  have hi : IndepFun F Y P := by
    simpa only [F, Y, Function.comp_def, add_tsub_cancel_of_le hsT] using
      (hB.indepFun_shift s).symm.comp hpast hfuture
  exact (IdentDistrib.refl hF).prodMk hYsymm hi
    (hi.comp measurable_id measurable_neg)
theorem finite_past_terminal_reflection
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s T : ℝ≥0) (hsT : s ≤ T) (τ : ι → ℝ≥0) (hτ : ∀ i, τ i ≤ s)
    (E : Set ((ι → ℝ) × ℝ)) (hE : MeasurableSet E) (b : ℝ) :
    P {ω | ((fun i => B (τ i) ω), B s ω) ∈ E ∧ B T ω ≤ b} =
      P {ω | ((fun i => B (τ i) ω), B s ω) ∈ E ∧ 2 * B s ω - b ≤ B T ω} := by
  have hid := finite_past_increment_neg_identDistrib hB s T hsT τ hτ
  let S : Set (((ι → ℝ) × ℝ) × ℝ) := {p | p.1 ∈ E ∧ p.1.2 + p.2 ≤ b}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : (((ι → ℝ) × ℝ) × ℝ) | p.1 ∈ E ∧ p.1.2 + p.2 ≤ b}
    exact (hE.preimage measurable_fst).inter
      (measurableSet_le
        (by fun_prop : Measurable (fun p : (((ι → ℝ) × ℝ) × ℝ) => p.1.2 + p.2))
        measurable_const)
  have heq := hid.measure_mem_eq hS
  convert heq using 1 <;> congr 1 <;> ext ω <;>
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S] <;>
    constructor <;> rintro ⟨hmem, hb⟩ <;> exact ⟨hmem, by linarith⟩
theorem first_crossing_terminal_reflection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {N : ℕ} (τ : Fin N → ℝ≥0) (hmono : Monotone τ) (T : ℝ≥0)
    (hτT : ∀ i, τ i ≤ T) (k : Fin N) (m b : ℝ) :
    P {ω | m < B (τ k) ω ∧ (∀ i : Fin N, i < k → B (τ i) ω ≤ m) ∧ B T ω ≤ b} =
      P {ω | m < B (τ k) ω ∧ (∀ i : Fin N, i < k → B (τ i) ω ≤ m) ∧
        2 * B (τ k) ω - b ≤ B T ω} := by
  classical
  let I := {i : Fin N // i < k}
  let E : Set ((I → ℝ) × ℝ) := {p | m < p.2 ∧ ∀ i : I, p.1 i ≤ m}
  have hE : MeasurableSet E := by
    change MeasurableSet ({p : (I → ℝ) × ℝ | m < p.2} ∩
      {p : (I → ℝ) × ℝ | ∀ i : I, p.1 i ≤ m})
    apply MeasurableSet.inter (measurableSet_lt measurable_const measurable_snd)
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)
  have h := finite_past_terminal_reflection hB (τ k) T (hτT k)
    (fun i : I => τ i) (fun i => hmono (le_of_lt i.property)) E hE b
  simpa only [E, I, Set.mem_ofPred_eq, Subtype.forall, and_assoc] using h
theorem first_crossing_pairwise_disjoint {Ω : Type*} {N : ℕ}
    (v : Fin N → Ω → ℝ) (m : ℝ) :
    Pairwise (fun k l => Disjoint
      {ω | m < v k ω ∧ ∀ i : Fin N, i < k → v i ω ≤ m}
      {ω | m < v l ω ∧ ∀ i : Fin N, i < l → v i ω ≤ m}) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro ω hk hl
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · exact (not_lt_of_ge (hl.2 k hlt)) hk.1
  · exact (not_lt_of_ge (hk.2 l hlt)) hl.1
lemma measurableSet_first_crossing {N : ℕ} (k : Fin N) (m : ℝ) :
    MeasurableSet {x : Fin N → ℝ | m < x k ∧ ∀ i : Fin N, i < k → x i ≤ m} := by
  have hprev : MeasurableSet {x : Fin N → ℝ | ∀ i : Fin N, i < k → x i ≤ m} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < k
    · simpa only [hi, true_implies] using
        (measurableSet_le (measurable_pi_apply i) (measurable_const : Measurable (fun _ : Fin N → ℝ => m)))
    · simp only [hi, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ
  exact (measurableSet_lt measurable_const (measurable_pi_apply k)).inter hprev
theorem first_crossing_union {Ω : Type*} {N : ℕ}
    (v : Fin N → Ω → ℝ) (Z : Ω → ℝ) (m b : ℝ) :
    {ω | (∃ i : Fin N, m < v i ω) ∧ Z ω ≤ b} =
      ⋃ k : Fin N, {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧ Z ω ≤ b} := by
  classical
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, hZ⟩
    let S := Finset.univ.filter (fun j : Fin N => m < v j ω)
    have hne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let k := S.min' hne
    have hk : m < v k ω := (Finset.mem_filter.mp (Finset.min'_mem S hne)).2
    refine ⟨k, hk, ?_, hZ⟩
    intro j hj
    by_contra hn
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_of_not_ge hn⟩
    have hkj : k ≤ j := Finset.min'_le S j hjS
    exact (not_lt_of_ge hkj) hj
  · rintro ⟨k, hk, _, hZ⟩
    exact ⟨⟨k, hk⟩, hZ⟩
theorem measure_hit_eq_sum_first_crossing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    (v : Fin N → Ω → ℝ) (hv : ∀ i, AEMeasurable (v i) P)
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (m b : ℝ) :
    P {ω | (∃ i : Fin N, m < v i ω) ∧ Z ω ≤ b} =
      ∑ k : Fin N, P {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧ Z ω ≤ b} := by
  have hvec : AEMeasurable (fun ω i => v i ω) P := aemeasurable_pi_lambda _ hv
  have hfirst (k : Fin N) :
      NullMeasurableSet {ω | m < v k ω ∧ ∀ i : Fin N, i < k → v i ω ≤ m} P :=
    hvec.nullMeasurableSet_preimage (measurableSet_first_crossing k m)
  have hle : NullMeasurableSet {ω | Z ω ≤ b} P :=
    hZ.nullMeasurableSet_preimage measurableSet_Iic
  have hnull (k : Fin N) :
      NullMeasurableSet {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧ Z ω ≤ b} P := by
    have heq : {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧ Z ω ≤ b} =
        {ω | m < v k ω ∧ ∀ i : Fin N, i < k → v i ω ≤ m} ∩ {ω | Z ω ≤ b} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [heq]
    exact (hfirst k).inter hle
  have hdisj : Pairwise (fun k l => Disjoint
      {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧ Z ω ≤ b}
      {ω | m < v l ω ∧ (∀ i : Fin N, i < l → v i ω ≤ m) ∧ Z ω ≤ b}) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro ω hk hl
    exact Set.disjoint_left.mp (first_crossing_pairwise_disjoint v m hkl)
      ⟨hk.1, hk.2.1⟩ ⟨hl.1, hl.2.1⟩
  rw [first_crossing_union]
  simpa only [tsum_fintype] using
    (measure_iUnion₀ (μ := P) (fun k l hkl => (hdisj hkl).aedisjoint) hnull)
theorem finite_grid_reflection_sum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {N : ℕ} (τ : Fin N → ℝ≥0) (hmono : Monotone τ) (T : ℝ≥0)
    (hτT : ∀ i, τ i ≤ T) (m b : ℝ) :
    P {ω | (∃ i : Fin N, m < B (τ i) ω) ∧ B T ω ≤ b} =
      ∑ k : Fin N, P {ω | m < B (τ k) ω ∧ (∀ i : Fin N, i < k → B (τ i) ω ≤ m) ∧
        2 * B (τ k) ω - b ≤ B T ω} := by
  rw [measure_hit_eq_sum_first_crossing (fun i ω => B (τ i) ω)
    (fun i => hB.aemeasurable (τ i)) (B T) (hB.aemeasurable T) m b]
  apply Finset.sum_congr rfl
  intro k _
  exact first_crossing_terminal_reflection hB τ hmono T hτT k m b
end ArgmaxBrownianReflection
open scoped NNReal Topology
open Filter
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
open scoped ENNReal
namespace ArgmaxBrownianContinuousReflection
lemma nullMeasurableSet_reflected_piece
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    (v : Fin N → Ω → ℝ) (hv : ∀ i, AEMeasurable (v i) P)
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (k : Fin N) (m b : ℝ) :
    NullMeasurableSet {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧
      2 * v k ω - b ≤ Z ω} P := by
  have hvec : AEMeasurable (fun ω i => v i ω) P := aemeasurable_pi_lambda _ hv
  have hfirst := hvec.nullMeasurableSet_preimage
    (ArgmaxBrownianReflection.measurableSet_first_crossing k m)
  have hgate : NullMeasurableSet {ω | 2 * v k ω - Z ω ≤ b} P :=
    ((hv k).const_mul 2 |>.sub hZ).nullMeasurableSet_preimage measurableSet_Iic
  have heq : {ω | m < v k ω ∧ (∀ i : Fin N, i < k → v i ω ≤ m) ∧
      2 * v k ω - b ≤ Z ω} =
      {ω | m < v k ω ∧ ∀ i : Fin N, i < k → v i ω ≤ m} ∩
        {ω | 2 * v k ω - Z ω ≤ b} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨⟨h₁, h₂⟩, by linarith⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨h₁, h₂, by linarith⟩
  rw [heq]
  exact hfirst.inter hgate
theorem finite_grid_reflection_union
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {N : ℕ} (τ : Fin N → ℝ≥0) (hmono : Monotone τ) (T : ℝ≥0)
    (hτT : ∀ i, τ i ≤ T) (m b : ℝ) :
    P {ω | (∃ i : Fin N, m < B (τ i) ω) ∧ B T ω ≤ b} =
      P {ω | ∃ k : Fin N, m < B (τ k) ω ∧
        (∀ i : Fin N, i < k → B (τ i) ω ≤ m) ∧ 2 * B (τ k) ω - b ≤ B T ω} := by
  rw [ArgmaxBrownianReflection.finite_grid_reflection_sum hB τ hmono T hτT m b]
  let R : Fin N → Set Ω := fun k => {ω | m < B (τ k) ω ∧
    (∀ i : Fin N, i < k → B (τ i) ω ≤ m) ∧ 2 * B (τ k) ω - b ≤ B T ω}
  have hnull (k : Fin N) : NullMeasurableSet (R k) P :=
    nullMeasurableSet_reflected_piece (fun i ω => B (τ i) ω)
      (fun i => hB.aemeasurable (τ i)) (B T) (hB.aemeasurable T) k m b
  have hdisj : Pairwise (fun k l => Disjoint (R k) (R l)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro ω hk hl
    exact Set.disjoint_left.mp
      (ArgmaxBrownianReflection.first_crossing_pairwise_disjoint (fun i ω => B (τ i) ω) m hkl)
      ⟨hk.1, hk.2.1⟩ ⟨hl.1, hl.2.1⟩
  have hm := measure_iUnion₀ (μ := P) (fun k l hkl => (hdisj hkl).aedisjoint) hnull
  simpa only [tsum_fintype, Set.mem_iUnion, Set.ofPred_exists] using hm.symm
theorem tendsto_measure_of_ae_eventually_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (C : Set Ω)
    (hA : ∀ n, NullMeasurableSet (A n) P) (hC : NullMeasurableSet C P)
    (hlim : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, (ω ∈ A n ↔ ω ∈ C)) :
    Tendsto (fun n => P (A n)) atTop (𝓝 (P C)) := by
  have hm (n : ℕ) : AEMeasurable ((A n).indicator (fun _ : Ω => (1 : ℝ≥0∞))) P :=
    aemeasurable_const.indicator₀ (hA n)
  have hb (n : ℕ) : (A n).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ≤ᵐ[P] (fun _ => 1) :=
    Filter.Eventually.of_forall (fun ω => by by_cases h : ω ∈ A n <;> simp [Set.indicator, h])
  have hc : ∀ᵐ ω ∂P, Tendsto
      (fun n => (A n).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω) atTop
      (𝓝 (C.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω)) := by
    filter_upwards [hlim] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    by_cases h : ω ∈ C
    · simp [Set.indicator, h, hn.mpr h]
    · have hn' : ω ∉ A n := fun hx => h (hn.mp hx)
      simp [Set.indicator, h, hn']
  have h := tendsto_lintegral_of_dominated_convergence' (fun _ : Ω => (1 : ℝ≥0∞))
    hm hb (by simp) hc
  have heqA (n : ℕ) : (∫⁻ ω, (A n).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P) = P (A n) :=
    lintegral_indicator_one₀ (hA n)
  have heqC : (∫⁻ ω, C.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P) = P C :=
    lintegral_indicator_one₀ hC
  simpa only [heqA, heqC] using h
lemma exists_first_crossing {N : ℕ} (v : Fin N → ℝ) (m : ℝ)
    (hhit : ∃ i, m < v i) :
    ∃ k : Fin N, m < v k ∧ ∀ i : Fin N, i < k → v i ≤ m := by
  have hunit : () ∈ {u : Unit | (∃ i : Fin N, m < v i) ∧ (0 : ℝ) ≤ 0} := ⟨hhit, le_rfl⟩
  rw [ArgmaxBrownianReflection.first_crossing_union
    (fun i (_ : Unit) => v i) (fun _ : Unit => (0 : ℝ)) m 0] at hunit
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hunit
  exact ⟨k, hk.1, hk.2.1⟩
theorem eventually_reflected_dyadic_iff
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m b : ℝ)
    (h0 : f 0 ≤ m) (hb : b ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      ((∃ k : Fin (2 ^ n + 1),
        m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ∧
        (∀ i : Fin (2 ^ n + 1), i < k →
          f ((i.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m) ∧
        2 * f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) - b ≤ f T) ↔
        2 * m - b < f T) := by
  by_cases htail : 2 * m - b < f T
  · have hε : 0 < (f T - (2 * m - b)) / 2 := by linarith
    filter_upwards [ArgmaxDyadicGridPathApproximation.eventually_dyadic_fin_first_crossing_overshoot
      f hf T m ((f T - (2 * m - b)) / 2) hε h0] with n hn
    constructor
    · intro _
      exact htail
    · intro _
      have hhit : ∃ k : Fin (2 ^ n + 1),
          m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
        refine ⟨Fin.last (2 ^ n), ?_⟩
        rw [Fin.val_last, ArgmaxDyadicGridPathApproximation.uniform_grid_endpoint T (2 ^ n) (by positivity)]
        linarith
      obtain ⟨k, hk, hprev⟩ := exists_first_crossing
        (fun k : Fin (2 ^ n + 1) => f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) m hhit
      refine ⟨k, hk, hprev, ?_⟩
      have ho := hn k hk hprev
      linarith
  · exact Filter.Eventually.of_forall (fun n => by
      constructor
      · rintro ⟨k, hk, _, hterm⟩
        linarith
      · intro h
        exact (htail h).elim)
theorem eventually_dyadic_hit_iff_continuous_hit
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ((∃ k : Fin (2 ^ n + 1), m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) ↔
        ∃ t : ℝ≥0, t ≤ T ∧ m < f t) := by
  by_cases hhit : ∃ t : ℝ≥0, t ≤ T ∧ m < f t
  · filter_upwards [(ArgmaxDyadicGridPathApproximation.continuous_hit_iff_eventually_dyadic_fin_hit
      f hf T m).mp hhit] with n hn
    exact ⟨fun _ => hhit, fun _ => hn⟩
  · exact Filter.Eventually.of_forall (fun n => by
      have hn : ¬ ∃ k : Fin (2 ^ n + 1),
          m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) := by
        rintro ⟨k, hk⟩
        exact hhit ⟨(k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)),
          ArgmaxDyadicGridPathApproximation.uniform_grid_below_horizon T (2 ^ n) k.val
            (by positivity) (Nat.le_of_lt_succ k.isLt), hk⟩
      exact iff_of_false hn hhit)
theorem finite_horizon_reflection_strict
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (m b : ℝ) (hm : 0 ≤ m) (hb : b ≤ m) :
    P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b} =
      P {ω | 2 * m - b < B T ω} := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let τ (n : ℕ) (k : Fin (2 ^ n + 1)) : ℝ≥0 :=
    (k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))
  let L : ℕ → Set Ω := fun n => {ω | (∃ k : Fin (2 ^ n + 1), m < B (τ n k) ω) ∧ B T ω ≤ b}
  let R : ℕ → Set Ω := fun n => {ω | ∃ k : Fin (2 ^ n + 1), m < B (τ n k) ω ∧
    (∀ i : Fin (2 ^ n + 1), i < k → B (τ n i) ω ≤ m) ∧ 2 * B (τ n k) ω - b ≤ B T ω}
  let H : Set Ω := {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b}
  let C : Set Ω := {ω | 2 * m - b < B T ω}
  have heq (n : ℕ) : P (L n) = P (R n) := by
    apply finite_grid_reflection_union hB.toIsPreBrownianReal (τ n)
      (ArgmaxDyadicGridPathApproximation.uniform_fin_grid_monotone _ _) T
    intro k
    exact ArgmaxDyadicGridPathApproximation.uniform_grid_below_horizon T (2 ^ n) k.val
      (by positivity) (Nat.le_of_lt_succ k.isLt)
  have hLmono : Monotone L := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    refine ⟨?_, hω.2⟩
    have hn := (ArgmaxDyadicGridPathApproximation.dyadic_fin_hit_iff_nat_hit
      (fun t => B t ω) T m n).mp hω.1
    have hnext := ArgmaxDyadicGridPathApproximation.dyadic_hit_mono
      (fun t => B t ω) T m n hn
    exact (ArgmaxDyadicGridPathApproximation.dyadic_fin_hit_iff_nat_hit
      (fun t => B t ω) T m (n + 1)).mpr hnext
  have hU : (⋃ n : ℕ, L n) =ᵐ[P] H := by
    filter_upwards [hB.cont] with ω hc
    have hhit : (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ↔
        ∃ n : ℕ, ∃ k : Fin (2 ^ n + 1), m < B (τ n k) ω := by
      have hnat := ArgmaxDyadicGridPathApproximation.continuous_hit_iff_exists_dyadic_hit
        (fun t => B t ω) hc T m
      constructor
      · intro hhit
        obtain ⟨n, k, hk, hval⟩ := hnat.mp hhit
        exact ⟨n, ⟨k, Nat.lt_succ_of_le hk⟩, hval⟩
      · rintro ⟨n, k, hval⟩
        exact hnat.mpr ⟨n, k.val, Nat.le_of_lt_succ k.isLt, hval⟩
    apply propext
    change (ω ∈ ⋃ n : ℕ, L n) ↔ ω ∈ H
    simp only [Set.mem_iUnion, L, H, Set.mem_ofPred_eq]
    rw [exists_and_right]
    exact and_congr hhit.symm Iff.rfl
  have hPH := measure_congr hU
  have hlimL : Tendsto (fun n => P (L n)) atTop (𝓝 (P H)) := by
    simpa only [Function.comp_def, hPH] using
      (tendsto_measure_iUnion_atTop (μ := P) hLmono)
  have hRnull (n : ℕ) : NullMeasurableSet (R n) P := by
    have hparts (k : Fin (2 ^ n + 1)) := nullMeasurableSet_reflected_piece
      (fun i ω => B (τ n i) ω) (fun i => hB.aemeasurable (τ n i))
      (B T) (hB.aemeasurable T) k m b
    simpa only [R, Set.ofPred_exists] using NullMeasurableSet.iUnion hparts
  have hCnull : NullMeasurableSet C P :=
    (hB.aemeasurable T).nullMeasurableSet_preimage measurableSet_Ioi
  have hconvR : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, (ω ∈ R n ↔ ω ∈ C) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
    exact eventually_reflected_dyadic_iff (fun t => B t ω) hc T m b (by simpa only [hz] using hm) hb
  have hlimR := tendsto_measure_of_ae_eventually_iff R C hRnull hCnull hconvR
  rw [show (fun n => P (L n)) = (fun n => P (R n)) from funext heq] at hlimL
  exact tendsto_nhds_unique hlimL hlimR
lemma brownian_endpoint_ae_ne
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (c : ℝ) :
    ∀ᵐ ω ∂P, B T ω ≠ c := by
  let := nullSingletonClass_gaussianReal (μ := 0) hT.ne'
  have hz : P {ω | B T ω = c} = 0 := by
    have h := (hB.hasLaw_eval T).measure_eq (p := fun x => x = c) (measurableSet_singleton c)
    simpa using h
  apply ae_iff.mpr
  simpa only [not_not] using hz
theorem finite_horizon_reflection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (m b : ℝ) (hm : 0 ≤ m) (hb : b ≤ m) :
    P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b} =
      P {ω | 2 * m - b ≤ B T ω} := by
  rw [finite_horizon_reflection_strict hB T m b hm hb]
  apply measure_congr
  filter_upwards [brownian_endpoint_ae_ne hB.toIsPreBrownianReal T hT (2 * m - b)] with ω hne
  apply propext
  constructor
  · exact le_of_lt
  · intro hle
    exact lt_of_le_of_ne hle hne.symm
end ArgmaxBrownianContinuousReflection
namespace ArgmaxBrownianWeightedReflection
open ArgmaxBrownianContinuousReflection
lemma finite_hit_nullMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (m : ℝ) :
    NullMeasurableSet {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω} P := by
  let G : ℕ → Set Ω := fun n => {ω | ∃ k : Fin (2 ^ n + 1),
    m < B ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ω}
  have hG (n : ℕ) : NullMeasurableSet (G n) P := by
    have hk (k : Fin (2 ^ n + 1)) : NullMeasurableSet
        {ω | m < B ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ω} P :=
      (hB.aemeasurable ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))).nullMeasurableSet_preimage
        (measurableSet_Ioi (a := m))
    simpa only [G, Set.ofPred_exists] using NullMeasurableSet.iUnion hk
  have hUnion : NullMeasurableSet (⋃ n : ℕ, G n) P := NullMeasurableSet.iUnion hG
  apply hUnion.congr
  filter_upwards [hB.cont] with ω hc
  apply propext
  change (ω ∈ ⋃ n : ℕ, G n) ↔ ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω
  simp only [Set.mem_iUnion, G, Set.mem_ofPred_eq]
  have hnat := ArgmaxDyadicGridPathApproximation.continuous_hit_iff_exists_dyadic_hit
    (fun t => B t ω) hc T m
  constructor
  · rintro ⟨n, k, hval⟩
    exact hnat.mpr ⟨n, k.val, Nat.le_of_lt_succ k.isLt, hval⟩
  · intro hhit
    obtain ⟨n, k, hk, hval⟩ := hnat.mp hhit
    exact ⟨n, ⟨k, Nat.lt_succ_of_le hk⟩, hval⟩
theorem eventually_reflected_dyadic_iff_hit
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m b : ℝ) (h0 : f 0 ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      ((∃ k : Fin (2 ^ n + 1),
        m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ∧
        (∀ i : Fin (2 ^ n + 1), i < k →
          f ((i.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m) ∧
        2 * f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) - b ≤ f T) ↔
        (∃ t : ℝ≥0, t ≤ T ∧ m < f t) ∧ 2 * m - b < f T) := by
  by_cases htarget : (∃ t : ℝ≥0, t ≤ T ∧ m < f t) ∧ 2 * m - b < f T
  · have hε : 0 < (f T - (2 * m - b)) / 2 := by linarith [htarget.2]
    filter_upwards [ArgmaxDyadicGridPathApproximation.eventually_dyadic_fin_first_crossing_overshoot
      f hf T m ((f T - (2 * m - b)) / 2) hε h0,
      (ArgmaxDyadicGridPathApproximation.continuous_hit_iff_eventually_dyadic_fin_hit
        f hf T m).mp htarget.1] with n hn hhit
    constructor
    · intro _
      exact htarget
    · intro _
      obtain ⟨k, hk, hprev⟩ := ArgmaxBrownianContinuousReflection.exists_first_crossing
        (fun k : Fin (2 ^ n + 1) => f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)))) m hhit
      refine ⟨k, hk, hprev, ?_⟩
      have ho := hn k hk hprev
      linarith
  · exact Filter.Eventually.of_forall (fun n => by
      have hn : ¬ ∃ k : Fin (2 ^ n + 1),
          m < f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ∧
          (∀ i : Fin (2 ^ n + 1), i < k →
            f ((i.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m) ∧
          2 * f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) - b ≤ f T := by
        rintro ⟨k, hk, _, hterm⟩
        apply htarget
        refine ⟨⟨(k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0)),
          ArgmaxDyadicGridPathApproximation.uniform_grid_below_horizon T (2 ^ n) k.val
            (by positivity) (Nat.le_of_lt_succ k.isLt), hk⟩, ?_⟩
        linarith
      exact iff_of_false hn htarget)
theorem finite_horizon_reflection_on_hit_strict
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (m b : ℝ) (hm : 0 ≤ m) :
    P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b} =
      P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ 2 * m - b < B T ω} := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let τ (n : ℕ) (k : Fin (2 ^ n + 1)) : ℝ≥0 :=
    (k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))
  let L : ℕ → Set Ω := fun n => {ω | (∃ k : Fin (2 ^ n + 1), m < B (τ n k) ω) ∧ B T ω ≤ b}
  let R : ℕ → Set Ω := fun n => {ω | ∃ k : Fin (2 ^ n + 1), m < B (τ n k) ω ∧
    (∀ i : Fin (2 ^ n + 1), i < k → B (τ n i) ω ≤ m) ∧ 2 * B (τ n k) ω - b ≤ B T ω}
  let H : Set Ω := {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b}
  let C : Set Ω := {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ 2 * m - b < B T ω}
  have heq (n : ℕ) : P (L n) = P (R n) := by
    apply finite_grid_reflection_union hB.toIsPreBrownianReal (τ n)
      (ArgmaxDyadicGridPathApproximation.uniform_fin_grid_monotone _ _) T
    intro k
    exact ArgmaxDyadicGridPathApproximation.uniform_grid_below_horizon T (2 ^ n) k.val
      (by positivity) (Nat.le_of_lt_succ k.isLt)
  have hLmono : Monotone L := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    refine ⟨?_, hω.2⟩
    have hn := (ArgmaxDyadicGridPathApproximation.dyadic_fin_hit_iff_nat_hit
      (fun t => B t ω) T m n).mp hω.1
    have hnext := ArgmaxDyadicGridPathApproximation.dyadic_hit_mono
      (fun t => B t ω) T m n hn
    exact (ArgmaxDyadicGridPathApproximation.dyadic_fin_hit_iff_nat_hit
      (fun t => B t ω) T m (n + 1)).mpr hnext
  have hU : (⋃ n : ℕ, L n) =ᵐ[P] H := by
    filter_upwards [hB.cont] with ω hc
    have hhit : (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ↔
        ∃ n : ℕ, ∃ k : Fin (2 ^ n + 1), m < B (τ n k) ω := by
      have hnat := ArgmaxDyadicGridPathApproximation.continuous_hit_iff_exists_dyadic_hit
        (fun t => B t ω) hc T m
      constructor
      · intro hhit
        obtain ⟨n, k, hk, hval⟩ := hnat.mp hhit
        exact ⟨n, ⟨k, Nat.lt_succ_of_le hk⟩, hval⟩
      · rintro ⟨n, k, hval⟩
        exact hnat.mpr ⟨n, k.val, Nat.le_of_lt_succ k.isLt, hval⟩
    apply propext
    change (ω ∈ ⋃ n : ℕ, L n) ↔ ω ∈ H
    simp only [Set.mem_iUnion, L, H, Set.mem_ofPred_eq]
    rw [exists_and_right]
    exact and_congr hhit.symm Iff.rfl
  have hPH := measure_congr hU
  have hlimL : Tendsto (fun n => P (L n)) atTop (𝓝 (P H)) := by
    simpa only [Function.comp_def, hPH] using
      (tendsto_measure_iUnion_atTop (μ := P) hLmono)
  have hRnull (n : ℕ) : NullMeasurableSet (R n) P := by
    have hparts (k : Fin (2 ^ n + 1)) := nullMeasurableSet_reflected_piece
      (fun i ω => B (τ n i) ω) (fun i => hB.aemeasurable (τ n i))
      (B T) (hB.aemeasurable T) k m b
    simpa only [R, Set.ofPred_exists] using NullMeasurableSet.iUnion hparts
  have hCnull : NullMeasurableSet C P := by
    change NullMeasurableSet
      ({ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω} ∩ {ω | 2 * m - b < B T ω}) P
    exact (finite_hit_nullMeasurable hB T m).inter
      ((hB.aemeasurable T).nullMeasurableSet_preimage measurableSet_Ioi)
  have hconvR : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, (ω ∈ R n ↔ ω ∈ C) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
    exact eventually_reflected_dyadic_iff_hit (fun t => B t ω) hc T m b (by simpa only [hz] using hm)
  have hlimR := tendsto_measure_of_ae_eventually_iff R C hRnull hCnull hconvR
  rw [show (fun n => P (L n)) = (fun n => P (R n)) from funext heq] at hlimL
  exact tendsto_nhds_unique hlimL hlimR
theorem finite_horizon_reflection_on_hit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (m b : ℝ) (hm : 0 ≤ m) :
    P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b} =
      P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ 2 * m - b ≤ B T ω} := by
  rw [finite_horizon_reflection_on_hit_strict hB T m b hm]
  apply measure_congr
  filter_upwards [brownian_endpoint_ae_ne hB.toIsPreBrownianReal T hT (2 * m - b)] with ω hne
  apply propext
  exact and_congr Iff.rfl ⟨le_of_lt, fun hle => lt_of_le_of_ne hle hne.symm⟩
theorem endpoint_restricted_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (m : ℝ) (hm : 0 ≤ m) :
    IdentDistrib (B T) (fun ω => 2 * m - B T ω)
      (P.restrict {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω})
      (P.restrict {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω}) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let H : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω}
  let Q := P.restrict H
  have hX : AEMeasurable (B T) Q := (hB.aemeasurable T).restrict
  have hY : AEMeasurable (fun ω => 2 * m - B T ω) Q := aemeasurable_const.sub hX
  refine ⟨hX, hY, ?_⟩
  apply Measure.ext_of_Iic
  intro b
  calc
    (Measure.map (B T) Q) (Set.Iic b) = Q ((B T) ⁻¹' Set.Iic b) :=
      Measure.map_apply_of_aemeasurable hX measurableSet_Iic
    _ = P (((B T) ⁻¹' Set.Iic b) ∩ H) :=
      Measure.restrict_apply₀ (hX.nullMeasurableSet_preimage measurableSet_Iic)
    _ = P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ B T ω ≤ b} := by
      congr 1
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, H, Set.mem_ofPred_eq, and_comm]
    _ = P {ω | (∃ t : ℝ≥0, t ≤ T ∧ m < B t ω) ∧ 2 * m - b ≤ B T ω} :=
      finite_horizon_reflection_on_hit hB T hT m b hm
    _ = P (((fun ω => 2 * m - B T ω) ⁻¹' Set.Iic b) ∩ H) := by
      congr 1
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, H, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hhit, hle⟩
        exact ⟨by linarith, hhit⟩
      · rintro ⟨hle, hhit⟩
        exact ⟨hhit, by linarith⟩
    _ = Q ((fun ω => 2 * m - B T ω) ⁻¹' Set.Iic b) :=
      (Measure.restrict_apply₀ (hY.nullMeasurableSet_preimage measurableSet_Iic)).symm
    _ = (Measure.map (fun ω => 2 * m - B T ω) Q) (Set.Iic b) :=
      (Measure.map_apply_of_aemeasurable hY measurableSet_Iic).symm
theorem endpoint_integral_reflection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (m : ℝ) (hm : 0 ≤ m)
    (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ ω in {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω}, F (B T ω) ∂P) =
      ∫ ω in {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω}, F (2 * m - B T ω) ∂P := by
  simpa only [Function.comp_def] using
    ((endpoint_restricted_identDistrib hB T hT m hm).comp hF).integral_eq
lemma normalized_endpoint_weight_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (T : ℝ≥0) (d : ℝ) :
    Integrable (fun ω => Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2)) P := by
  have hg : Integrable (fun x : ℝ => Real.exp (d * x)) (Measure.map (B T) P) := by
    rw [(hB.hasLaw_eval T).map_eq]
    exact integrable_exp_mul_gaussianReal d
  have hb := hg.comp_aemeasurable (hB.aemeasurable T)
  have hw := hb.mul_const (Real.exp (-(d ^ 2 * (T : ℝ) / 2)))
  simpa only [Function.comp_def, sub_eq_add_neg, Real.exp_add] using hw
theorem endpoint_weighted_reflection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (m : ℝ) (hm : 0 ≤ m) (d : ℝ) :
    (∫ ω in {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω},
      Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2) ∂P) =
      ∫ ω in {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω},
        Real.exp (d * (2 * m - B T ω) - d ^ 2 * (T : ℝ) / 2) ∂P := by
  exact endpoint_integral_reflection hB T hT m hm
    (fun x : ℝ => Real.exp (d * x - d ^ 2 * (T : ℝ) / 2)) (by fun_prop)
theorem endpoint_weighted_terminal_reflection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (m : ℝ) (hm : 0 ≤ m) (d b : ℝ) :
    (∫ ω in {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω},
      (if B T ω ≤ b then Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2) else 0) ∂P) =
      ∫ ω in {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω},
        (if 2 * m - b ≤ B T ω then
          Real.exp (d * (2 * m - B T ω) - d ^ 2 * (T : ℝ) / 2) else 0) ∂P := by
  let F : ℝ → ℝ := (Set.Iic b).indicator (fun x => Real.exp (d * x - d ^ 2 * (T : ℝ) / 2))
  have hF : Measurable F := (by fun_prop : Measurable
    (fun x : ℝ => Real.exp (d * x - d ^ 2 * (T : ℝ) / 2))).indicator measurableSet_Iic
  have h := endpoint_integral_reflection hB T hT m hm F hF
  have hiff (ω : Ω) : 2 * m - B T ω ≤ b ↔ 2 * m - b ≤ B T ω := by constructor <;> intro h <;> linarith
  simpa only [F, Set.indicator, Set.mem_Iic, hiff] using h
end ArgmaxBrownianWeightedReflection
namespace ArgmaxBrownianDriftedMaximumTilt
open scoped BigOperators
lemma pdf_real_variance_shift (h : ℝ≥0) (hh : h ≠ 0) (d x : ℝ) :
    gaussianPDFReal (d * (h : ℝ)) h x =
      Real.exp (d * x - d ^ 2 * (h : ℝ) / 2) * gaussianPDFReal 0 h x := by
  simp only [gaussianPDFReal, sub_zero]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  have hh' : (h : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hh
  field_simp
  ring
lemma pdf_variance_shift (h : ℝ≥0) (hh : h ≠ 0) (d x : ℝ) :
    gaussianPDF (d * (h : ℝ)) h x = gaussianPDF 0 h x *
      ENNReal.ofReal (Real.exp (d * x - d ^ 2 * (h : ℝ) / 2)) := by
  simp only [gaussianPDF, pdf_real_variance_shift h hh]
  rw [mul_comm, ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 h x)]
theorem gaussian_variance_shift (h : ℝ≥0) (hh : h ≠ 0) (d : ℝ) :
    gaussianReal (d * (h : ℝ)) h = (gaussianReal 0 h).withDensity
      (fun x => ENNReal.ofReal (Real.exp (d * x - d ^ 2 * (h : ℝ) / 2))) := by
  rw [gaussianReal_of_var_ne_zero _ hh, gaussianReal_of_var_ne_zero _ hh,
    ← withDensity_mul volume (measurable_gaussianPDF 0 h) (by fun_prop)]
  congr 1
  funext x
  exact pdf_variance_shift h hh d x
lemma integrable_variance_weight (h : ℝ≥0) (d : ℝ) :
    Integrable (fun x => Real.exp (d * x - d ^ 2 * (h : ℝ) / 2)) (gaussianReal 0 h) := by
  simp_rw [sub_eq_add_neg, Real.exp_add]
  exact (integrable_exp_mul_gaussianReal d).mul_const _
lemma prod_variance_weight {ι : Type*} [Fintype ι] (h : ℝ≥0) (d : ℝ) (x : ι → ℝ) :
    (∏ i, Real.exp (d * x i - d ^ 2 * (h : ℝ) / 2)) =
      Real.exp (d * ∑ i, x i - (Fintype.card ι : ℝ) * d ^ 2 * (h : ℝ) / 2) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring
theorem pi_gaussian_variance_shift {ι : Type*} [Fintype ι]
    (h : ℝ≥0) (hh : h ≠ 0) (d : ℝ) :
    Measure.pi (fun _ : ι => gaussianReal (d * (h : ℝ)) h) =
      (Measure.pi (fun _ : ι => gaussianReal 0 h)).withDensity
        (fun x => ENNReal.ofReal
          (Real.exp (d * ∑ i, x i - (Fintype.card ι : ℝ) * d ^ 2 * (h : ℝ) / 2))) := by
  have hp := FiniteProductDensity.pi_eq_withDensity_ofReal_prod
    (fun _ : ι => gaussianReal 0 h) (fun _ : ι => gaussianReal (d * (h : ℝ)) h)
    (fun _ x => Real.exp (d * x - d ^ 2 * (h : ℝ) / 2))
    (fun _ => integrable_variance_weight h d)
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => gaussian_variance_shift h hh d)
  rw [hp]
  congr 1
  funext x
  rw [prod_variance_weight]
theorem integral_pi_gaussian_variance_shift {ι : Type*} [Fintype ι]
    (h : ℝ≥0) (hh : h ≠ 0) (d : ℝ) (F : (ι → ℝ) → ℝ) :
    (∫ x, F x ∂Measure.pi (fun _ : ι => gaussianReal (d * (h : ℝ)) h)) =
      ∫ x, Real.exp (d * ∑ i, x i - (Fintype.card ι : ℝ) * d ^ 2 * (h : ℝ) / 2) * F x
        ∂Measure.pi (fun _ : ι => gaussianReal 0 h) := by
  rw [pi_gaussian_variance_shift h hh d,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
lemma grid_increment_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) (k : ℕ) :
    HasLaw (fun ω => B (((k + 1 : ℕ) : ℝ≥0) * h) ω - B ((k : ℝ≥0) * h) ω)
      (gaussianReal 0 h) P := by
  have hstep : (k : ℝ≥0) * h + h = (((k + 1 : ℕ) : ℝ≥0) * h) := by
    push_cast
    ring
  simpa only [hstep] using (hB.shift ((k : ℝ≥0) * h)).hasLaw_eval h
lemma grid_increments_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) (N : ℕ) :
    iIndepFun (fun (i : Fin N) ω =>
      B (((i.val + 1 : ℕ) : ℝ≥0) * h) ω - B ((i.val : ℝ≥0) * h) ω) P := by
  have ht := ArgmaxDyadicGridPathApproximation.uniform_fin_grid_monotone h N
  simpa only [Fin.val_succ, Fin.val_castSucc] using
    hB.hasIndepIncrements N (fun i : Fin (N + 1) => (i.val : ℝ≥0) * h) ht
lemma grid_increments_hasLaw_pi
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) (N : ℕ) :
    HasLaw (fun ω (i : Fin N) =>
      B (((i.val + 1 : ℕ) : ℝ≥0) * h) ω - B ((i.val : ℝ≥0) * h) ω)
      (Measure.pi (fun _ : Fin N => gaussianReal 0 h)) P := by
  exact (grid_increments_iIndepFun hB h N).hasLaw_pi
    (fun i => grid_increment_hasLaw hB h i.val)
lemma shifted_grid_increments_hasLaw_pi
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (h : ℝ≥0) (N : ℕ) (d : ℝ) :
    HasLaw (fun ω (i : Fin N) =>
      B (((i.val + 1 : ℕ) : ℝ≥0) * h) ω - B ((i.val : ℝ≥0) * h) ω + d * (h : ℝ))
      (Measure.pi (fun _ : Fin N => gaussianReal (d * (h : ℝ)) h)) P := by
  have hi := (grid_increments_iIndepFun hB h N).comp
    (fun _ x => x + d * (h : ℝ)) (by fun_prop)
  exact hi.hasLaw_pi (fun i => by
    simpa only [zero_add] using gaussianReal_add_const (grid_increment_hasLaw hB h i.val) (d * (h : ℝ)))
lemma prefix_increment_sum {N : ℕ} (f : ℕ → ℝ) (k : Fin (N + 1)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k.val),
      (f (i.val + 1) - f i.val)) = f k.val - f 0 := by
  classical
  by_cases hk : k.val = 0
  · simp [hk]
  let p : Fin N := ⟨k.val - 1, by omega⟩
  have hfilter : Finset.univ.filter (fun i : Fin N => i.val < k.val) = Finset.Iic p := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    change i.val < k.val ↔ i.val ≤ p.val
    dsimp only [p]
    omega
  rw [hfilter]
  have hs := Fin.sum_Iic_sub p (fun j : Fin (N + 1) => f j.val)
  have hk' : k.val - 1 + 1 = k.val := by omega
  simpa only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, p, hk'] using hs
lemma total_increment_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, (f (i.val + 1) - f i.val)) = f N - f 0 := by
  have hs := prefix_increment_sum f (Fin.last N)
  have hfilter : Finset.univ.filter (fun i : Fin N => i.val < (Fin.last N).val) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, iff_true]
    exact i.isLt
  rw [hfilter] at hs
  simpa only [Fin.val_last] using hs
lemma prefix_drifted_grid_increments {N : ℕ} (f : ℝ≥0 → ℝ) (h : ℝ≥0)
    (d : ℝ) (k : Fin (N + 1)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k.val),
      (f (((i.val + 1 : ℕ) : ℝ≥0) * h) - f ((i.val : ℝ≥0) * h) + d * (h : ℝ))) =
      f ((k.val : ℝ≥0) * h) + d * (((k.val : ℝ≥0) * h : ℝ≥0) : ℝ) - f 0 := by
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k.val),
        ((f (((i.val + 1 : ℕ) : ℝ≥0) * h) + d * ((((i.val + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) : ℝ)) -
          (f ((i.val : ℝ≥0) * h) + d * (((i.val : ℝ≥0) * h : ℝ≥0) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    _ = _ := by
      have hs := prefix_increment_sum
        (fun j => f ((j : ℝ≥0) * h) + d * (((j : ℝ≥0) * h : ℝ≥0) : ℝ)) k
      simpa only [Nat.cast_zero, zero_mul, NNReal.coe_zero, mul_zero, add_zero] using hs
theorem finite_grid_endpoint_tilt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (hh : h ≠ 0) (N : ℕ) (d : ℝ)
    (F : (Fin (N + 1) → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω, F (fun k => B ((k.val : ℝ≥0) * h) ω +
      d * (((k.val : ℝ≥0) * h : ℝ≥0) : ℝ)) ∂P) =
      ∫ ω, Real.exp (d * B ((N : ℝ≥0) * h) ω -
        d ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ) / 2) *
        F (fun k => B ((k.val : ℝ≥0) * h) ω) ∂P := by
  classical
  let K : (Fin N → ℝ) → (Fin (N + 1) → ℝ) := fun x k =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k.val), x i
  let G : (Fin N → ℝ) → ℝ := fun x => F (K x)
  let inc : Ω → (Fin N → ℝ) := fun ω i =>
    B (((i.val + 1 : ℕ) : ℝ≥0) * h) ω - B ((i.val : ℝ≥0) * h) ω
  let incD : Ω → (Fin N → ℝ) := fun ω i => inc ω i + d * (h : ℝ)
  let W : (Fin N → ℝ) → ℝ := fun x =>
    Real.exp (d * ∑ i, x i - (N : ℝ) * d ^ 2 * (h : ℝ) / 2)
  have hK : Measurable K := by fun_prop
  have hG : Measurable G := hF.comp hK
  have hWG : Measurable (fun x => W x * G x) := (by fun_prop : Measurable W).mul hG
  have hpath (ω : Ω) : K (inc ω) =
      (fun k : Fin (N + 1) => B ((k.val : ℝ≥0) * h) ω - B 0 ω) := by
    funext k
    simpa only [K, inc, Nat.cast_zero, zero_mul] using
      prefix_increment_sum (fun j => B ((j : ℝ≥0) * h) ω) k
  have hpathD (ω : Ω) : K (incD ω) =
      (fun k : Fin (N + 1) => B ((k.val : ℝ≥0) * h) ω +
        d * (((k.val : ℝ≥0) * h : ℝ≥0) : ℝ) - B 0 ω) := by
    funext k
    exact prefix_drifted_grid_increments (fun t => B t ω) h d k
  have hsum (ω : Ω) : (∑ i : Fin N, inc ω i) =
      B ((N : ℝ≥0) * h) ω - B 0 ω := by
    simpa only [inc, Nat.cast_zero, zero_mul] using
      total_increment_sum N (fun j => B ((j : ℝ≥0) * h) ω)
  have hd : (∫ ω, G (incD ω) ∂P) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin N => gaussianReal (d * (h : ℝ)) h) := by
    simpa only [Function.comp_def] using
      (shifted_grid_increments_hasLaw_pi hB h N d).integral_comp hG.aestronglyMeasurable
  have hz : (∫ ω, W (inc ω) * G (inc ω) ∂P) =
      ∫ x, W x * G x ∂Measure.pi (fun _ : Fin N => gaussianReal 0 h) := by
    simpa only [Function.comp_def] using
      (grid_increments_hasLaw_pi hB h N).integral_comp hWG.aestronglyMeasurable
  calc
    _ = ∫ ω, G (incD ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
      dsimp only [G]
      rw [hpathD ω]
      simp only [hzero, sub_zero]
    _ = _ := hd
    _ = ∫ x, W x * G x ∂Measure.pi (fun _ : Fin N => gaussianReal 0 h) := by
      simpa only [W, Fintype.card_fin] using integral_pi_gaussian_variance_shift h hh d G
    _ = ∫ ω, W (inc ω) * G (inc ω) ∂P := hz.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
      dsimp only [W, G]
      rw [hsum ω, hpath ω]
      simp only [hzero, sub_zero, NNReal.coe_mul, NNReal.coe_natCast]
      congr 2
      ring
end ArgmaxBrownianDriftedMaximumTilt
open TopologicalSpace
namespace ArgmaxBrownianContinuousMaximumTilt
open scoped Classical
lemma isLUB_bound_iff (f : ℝ≥0 → ℝ) (T : ℝ≥0) (A m : ℝ)
    (hA : IsLUB (f '' Set.Icc 0 T) A) :
    (∀ t : ℝ≥0, t ≤ T → f t ≤ m) ↔ A ≤ m := by
  constructor
  · intro h
    apply hA.2
    rintro y ⟨t, ht, rfl⟩
    exact h t ht.2
  · intro h t ht
    exact (hA.1 ⟨t, ⟨by positivity, ht⟩, rfl⟩).trans h
lemma finite_path_bound_nullMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (d m : ℝ) :
    NullMeasurableSet {ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m} P := by
  obtain ⟨M, hMm, hM⟩ := ArgmaxBrownianFiniteMaximum.exists_aemeasurable_finite_maximum hB T (-d)
  have hnull : NullMeasurableSet {ω | M ω ≤ m} P :=
    hMm.nullMeasurableSet_preimage measurableSet_Iic
  apply hnull.congr
  filter_upwards [hM] with ω hω
  apply propext
  have hlub : IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Set.Icc 0 T) (M ω) := by
    simpa only [neg_mul, sub_neg_eq_add] using hω.1
  exact (isLUB_bound_iff (fun t => B t ω + d * (t : ℝ)) T (M ω) m hlub).symm
lemma eventually_dyadic_bounds_iff
    (f : ℝ≥0 → ℝ) (hf : Continuous f) (T : ℝ≥0) (m : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ((∀ k : Fin (2 ^ n + 1), f ((k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))) ≤ m) ↔
        ∀ t : ℝ≥0, t ≤ T → f t ≤ m) := by
  filter_upwards [ArgmaxBrownianContinuousReflection.eventually_dyadic_hit_iff_continuous_hit
    f hf T m] with n hn
  simpa only [not_exists, not_and, not_lt] using hn.not
lemma measurableSet_finite_bounds {ι : Type*} [Fintype ι] (m : ℝ) :
    MeasurableSet {x : ι → ℝ | ∀ i, x i ≤ m} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i) measurable_const)
lemma nullMeasurableSet_finite_bounds
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    (X : ι → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) P) (m : ℝ) :
    NullMeasurableSet {ω | ∀ i, X i ω ≤ m} P :=
  (aemeasurable_pi_lambda _ hX).nullMeasurableSet_preimage (measurableSet_finite_bounds m)
lemma finite_grid_bound_indicator_tilt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (hh : h ≠ 0) (N : ℕ) (d m : ℝ) :
    (∫ ω, (if ∀ k : Fin (N + 1), B ((k.val : ℝ≥0) * h) ω +
      d * (((k.val : ℝ≥0) * h : ℝ≥0) : ℝ) ≤ m then (1 : ℝ) else 0) ∂P) =
      ∫ ω, Real.exp (d * B ((N : ℝ≥0) * h) ω - d ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ) / 2) *
        (if ∀ k : Fin (N + 1), B ((k.val : ℝ≥0) * h) ω ≤ m then (1 : ℝ) else 0) ∂P := by
  let E : Set (Fin (N + 1) → ℝ) := {x | ∀ k, x k ≤ m}
  let F : (Fin (N + 1) → ℝ) → ℝ := E.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator (measurableSet_finite_bounds m)
  have htilt := ArgmaxBrownianDriftedMaximumTilt.finite_grid_endpoint_tilt hB h hh N d F hF
  calc
    _ = ∫ ω, F (fun k => B ((k.val : ℝ≥0) * h) ω +
        d * (((k.val : ℝ≥0) * h : ℝ≥0) : ℝ)) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : ∀ k : Fin (N + 1), B ((k.val : ℝ≥0) * h) ω +
            d * (((k.val : ℝ≥0) * h : ℝ≥0) : ℝ) ≤ m <;>
          simp only [F, E, Set.indicator, Set.mem_ofPred_eq, hc, ↓reduceIte])
    _ = ∫ ω, Real.exp (d * B ((N : ℝ≥0) * h) ω - d ^ 2 * (((N : ℝ≥0) * h : ℝ≥0) : ℝ) / 2) *
        F (fun k => B ((k.val : ℝ≥0) * h) ω) ∂P := htilt
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : ∀ k : Fin (N + 1), B ((k.val : ℝ≥0) * h) ω ≤ m <;>
          simp only [F, E, Set.indicator, Set.mem_ofPred_eq, hc, ↓reduceIte])
theorem continuous_maximum_tilt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (d m : ℝ) :
    P.real {ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m} =
      ∫ ω in {ω | ∀ t : ℝ≥0, t ≤ T → B t ω ≤ m},
        Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2) ∂P := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let τ (n : ℕ) (k : Fin (2 ^ n + 1)) : ℝ≥0 :=
    (k.val : ℝ≥0) * (T / ((2 ^ n : ℕ) : ℝ≥0))
  let W : Ω → ℝ := fun ω => Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2)
  let U : ℕ → Ω → ℝ := fun n ω =>
    if ∀ k : Fin (2 ^ n + 1), B (τ n k) ω + d * (τ n k : ℝ) ≤ m then 1 else 0
  let V : ℕ → Ω → ℝ := fun n ω => W ω *
    (if ∀ k : Fin (2 ^ n + 1), B (τ n k) ω ≤ m then 1 else 0)
  let Ulimit : Ω → ℝ := fun ω => if ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m then 1 else 0
  let Vlimit : Ω → ℝ := fun ω => W ω *
    (if ∀ t : ℝ≥0, t ≤ T → B t ω ≤ m then 1 else 0)
  have hW : Integrable W P :=
    ArgmaxBrownianWeightedReflection.normalized_endpoint_weight_integrable hB.toIsPreBrownianReal T d
  have hWpos (ω : Ω) : 0 < W ω := Real.exp_pos _
  have hDnull (n : ℕ) : NullMeasurableSet
      {ω | ∀ k : Fin (2 ^ n + 1), B (τ n k) ω + d * (τ n k : ℝ) ≤ m} P :=
    nullMeasurableSet_finite_bounds (fun k ω => B (τ n k) ω + d * (τ n k : ℝ))
      (fun k => (hB.aemeasurable (τ n k)).add_const _) m
  have hNnull (n : ℕ) : NullMeasurableSet
      {ω | ∀ k : Fin (2 ^ n + 1), B (τ n k) ω ≤ m} P :=
    nullMeasurableSet_finite_bounds (fun k ω => B (τ n k) ω)
      (fun k => hB.aemeasurable (τ n k)) m
  have hUmeas (n : ℕ) : AEStronglyMeasurable (U n) P := by
    have hi := (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) P).indicator₀ (hDnull n)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hc : ∀ k : Fin (2 ^ n + 1), B (τ n k) ω + d * (τ n k : ℝ) ≤ m <;>
        simp only [U, Set.indicator, Set.mem_ofPred_eq, hc, ↓reduceIte])
  have hVmeas (n : ℕ) : AEStronglyMeasurable (V n) P := by
    have hi := (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) P).indicator₀ (hNnull n)
    apply (hW.aestronglyMeasurable.mul hi).congr
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hc : ∀ k : Fin (2 ^ n + 1), B (τ n k) ω ≤ m <;>
        simp [V, Pi.mul_apply, Set.indicator, hc])
  have hUbound (n : ℕ) : ∀ᵐ ω ∂P, ‖U n ω‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun ω => by dsimp only [U]; split_ifs <;> norm_num)
  have hVbound (n : ℕ) : ∀ᵐ ω ∂P, ‖V n ω‖ ≤ W ω :=
    Filter.Eventually.of_forall (fun ω => by
      dsimp only [V]
      split_ifs
      · simpa only [mul_one, Real.norm_eq_abs, abs_of_pos (hWpos ω)] using (le_rfl : W ω ≤ W ω)
      · simp only [mul_zero, norm_zero]
        exact (hWpos ω).le)
  have hUlim : ∀ᵐ ω ∂P, Tendsto (fun n => U n ω) atTop (𝓝 (Ulimit ω)) := by
    filter_upwards [hB.cont] with ω hc
    have hp : Continuous (fun t : ℝ≥0 => B t ω + d * (t : ℝ)) :=
      hc.fun_add (continuous_const.fun_mul NNReal.continuous_coe)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_dyadic_bounds_iff (fun t => B t ω + d * (t : ℝ)) hp T m]
      with n hn
    dsimp only [U, Ulimit, τ]
    simp only [hn]
  have hVlim : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (Vlimit ω)) := by
    filter_upwards [hB.cont] with ω hc
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_dyadic_bounds_iff (fun t => B t ω) hc T m] with n hn
    dsimp only [V, Vlimit, τ]
    simp only [hn]
  have heq (n : ℕ) : (∫ ω, U n ω ∂P) = ∫ ω, V n ω ∂P := by
    have hh : T / ((2 ^ n : ℕ) : ℝ≥0) ≠ 0 := div_ne_zero hT.ne' (by positivity)
    have ht := finite_grid_bound_indicator_tilt hB.toIsPreBrownianReal
      (T / ((2 ^ n : ℕ) : ℝ≥0)) hh (2 ^ n) d m
    have hend := ArgmaxDyadicGridPathApproximation.uniform_grid_endpoint T (2 ^ n) (by positivity)
    simpa only [U, V, W, τ, hend] using ht
  have hlimU := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    hUmeas (integrable_const 1) hUbound hUlim
  have hlimV := tendsto_integral_of_dominated_convergence W hVmeas hW hVbound hVlim
  rw [show (fun n => ∫ ω, U n ω ∂P) = (fun n => ∫ ω, V n ω ∂P) from funext heq] at hlimU
  have hUV : (∫ ω, Ulimit ω ∂P) = ∫ ω, Vlimit ω ∂P := tendsto_nhds_unique hlimU hlimV
  have hDlimit := finite_path_bound_nullMeasurable hB T d m
  have hNlimit : NullMeasurableSet {ω | ∀ t : ℝ≥0, t ≤ T → B t ω ≤ m} P := by
    simpa only [zero_mul, add_zero] using finite_path_bound_nullMeasurable hB T 0 m
  have hIU : (∫ ω, Ulimit ω ∂P) =
      P.real {ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m} := by
    calc
      _ = ∫ ω, ({ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m}).indicator
          (fun _ : Ω => (1 : ℝ)) ω ∂P := rfl
      _ = ∫ _ in {ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m}, (1 : ℝ) ∂P :=
        integral_indicator₀ hDlimit
      _ = _ := by simp
  have hIV : (∫ ω, Vlimit ω ∂P) =
      ∫ ω in {ω | ∀ t : ℝ≥0, t ≤ T → B t ω ≤ m}, W ω ∂P := by
    rw [← integral_indicator₀ hNlimit]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hbound : ∀ t : ℝ≥0, t ≤ T → B t ω ≤ m <;>
        simp [Vlimit, Set.indicator, hbound])
  exact hIU.symm.trans (hUV.trans hIV)
end ArgmaxBrownianContinuousMaximumTilt
namespace ArgmaxBrownianDriftedMaximumCDF
open scoped Classical
lemma gaussian_shift_weighted_setIntegral (T : ℝ≥0) (hT : 0 < T) (d : ℝ)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (∫ x in E, Real.exp (d * x - d ^ 2 * (T : ℝ) / 2) ∂gaussianReal 0 T) =
      (gaussianReal (d * (T : ℝ)) T).real E := by
  symm
  calc
    _ = ∫ _ in E, (1 : ℝ) ∂gaussianReal (d * (T : ℝ)) T := by simp
    _ = _ := by
      rw [ArgmaxBrownianDriftedMaximumTilt.gaussian_variance_shift T hT.ne' d]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hE]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_one]
theorem endpoint_weighted_setIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (d : ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    (∫ ω in {ω | B T ω ∈ E}, Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2) ∂P) =
      (gaussianReal (d * (T : ℝ)) T).real E := by
  let W : ℝ → ℝ := fun x => Real.exp (d * x - d ^ 2 * (T : ℝ) / 2)
  have hW : Measurable W := by fun_prop
  have hpre : NullMeasurableSet {ω | B T ω ∈ E} P :=
    (hB.aemeasurable T).nullMeasurableSet_preimage hE
  calc
    _ = ∫ ω, E.indicator W (B T ω) ∂P := by
      rw [← integral_indicator₀ hpre]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases he : B T ω ∈ E <;> simp [Set.indicator, he, W])
    _ = ∫ x, E.indicator W x ∂gaussianReal 0 T := by
      simpa only [Function.comp_def] using
        (hB.hasLaw_eval T).integral_comp (hW.indicator hE).aestronglyMeasurable
    _ = ∫ x in E, W x ∂gaussianReal 0 T := integral_indicator hE
    _ = _ := gaussian_shift_weighted_setIntegral T hT d E hE
lemma gaussian_neg_tail_eq_cdf (μ : ℝ) (v : ℝ≥0) (m : ℝ) :
    (gaussianReal (-μ) v).real (Set.Ici m) =
      (gaussianReal μ v).real (Set.Iic (-m)) := by
  have hmap := gaussianReal_map_neg (μ := -μ) (v := v)
  have heq := congrArg (fun Q : Measure ℝ => Q (Set.Iic (-m))) hmap
  simp only [neg_neg] at heq
  rw [Measure.map_apply measurable_neg measurableSet_Iic] at heq
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iic (-m) = Set.Ici m := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]
  rw [hpre] at heq
  exact congrArg ENNReal.toReal heq
theorem continuous_bound_cdf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (d m : ℝ) (hm : 0 ≤ m) :
    P.real {ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m} =
      (gaussianReal (d * (T : ℝ)) T).real (Set.Iic m) -
        Real.exp (2 * d * m) * (gaussianReal (d * (T : ℝ)) T).real (Set.Iic (-m)) := by
  classical
  let W : Ω → ℝ := fun ω => Real.exp (d * B T ω - d ^ 2 * (T : ℝ) / 2)
  let V : Ω → ℝ := fun ω => Real.exp ((-d) * B T ω - (-d) ^ 2 * (T : ℝ) / 2)
  let R : Ω → ℝ := fun ω => Real.exp (d * (2 * m - B T ω) - d ^ 2 * (T : ℝ) / 2)
  let H : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ m < B t ω}
  let C : Set Ω := {ω | ∀ t : ℝ≥0, t ≤ T → B t ω ≤ m}
  let E : Set Ω := {ω | B T ω ≤ m}
  let G : Set Ω := {ω | m ≤ B T ω}
  have hW : Integrable W P :=
    ArgmaxBrownianWeightedReflection.normalized_endpoint_weight_integrable hB.toIsPreBrownianReal T d
  have hH : NullMeasurableSet H P := ArgmaxBrownianWeightedReflection.finite_hit_nullMeasurable hB T m
  have hC : NullMeasurableSet C P := by
    simpa only [C, zero_mul, add_zero] using
      ArgmaxBrownianContinuousMaximumTilt.finite_path_bound_nullMeasurable hB T 0 m
  have hE : NullMeasurableSet E P := (hB.aemeasurable T).nullMeasurableSet_preimage measurableSet_Iic
  have hG : NullMeasurableSet G P := (hB.aemeasurable T).nullMeasurableSet_preimage measurableSet_Ici
  have hpoint (ω : Ω) : E.indicator W ω =
      C.indicator W ω + H.indicator (E.indicator W) ω := by
    by_cases hh : ω ∈ H
    · have hc : ω ∉ C := by
        obtain ⟨t, ht, hhitt⟩ := hh
        intro hb
        exact (not_lt_of_ge (hb t ht)) hhitt
      simp [Set.indicator, hh, hc]
    · have hc : ω ∈ C := by
        intro t ht
        by_contra hn
        exact hh ⟨t, ht, lt_of_not_ge hn⟩
      have he : ω ∈ E := hc T le_rfl
      simp [Set.indicator, hh, hc, he]
  have hsplit : (∫ ω in E, W ω ∂P) =
      (∫ ω in C, W ω ∂P) + ∫ ω in H, E.indicator W ω ∂P := by
    rw [← integral_indicator₀ hE, ← integral_indicator₀ hC, ← integral_indicator₀ hH,
      ← integral_add (hW.indicator₀ hC) ((hW.indicator₀ hE).indicator₀ hH)]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hlow : (∫ ω in E, W ω ∂P) =
      (gaussianReal (d * (T : ℝ)) T).real (Set.Iic m) := by
    simpa only [E, W, Set.mem_Iic] using
      endpoint_weighted_setIntegral hB.toIsPreBrownianReal T hT d (Set.Iic m) measurableSet_Iic
  have hfactor (ω : Ω) : R ω = Real.exp (2 * d * m) * V ω := by
    dsimp only [R, V]
    rw [← Real.exp_add]
    congr 1
    ring
  have hcenter : 2 * m - m = m := by ring
  have href := ArgmaxBrownianWeightedReflection.endpoint_weighted_terminal_reflection
    hB T hT m hm d m
  simp only [hcenter] at href
  have hwhole : (∫ ω in H, (if m ≤ B T ω then R ω else 0) ∂P) =
      ∫ ω, (if m ≤ B T ω then R ω else 0) ∂P := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ArgmaxBrownianContinuousReflection.brownian_endpoint_ae_ne
      hB.toIsPreBrownianReal T hT m] with ω hne
    intro hnot
    by_cases hge : m ≤ B T ω
    · exact (hnot ⟨T, le_rfl, lt_of_le_of_ne hge hne.symm⟩).elim
    · simp only [if_neg hge]
  have hminus : (∫ ω in G, V ω ∂P) =
      (gaussianReal ((-d) * (T : ℝ)) T).real (Set.Ici m) := by
    simpa only [G, V, Set.mem_Ici] using
      endpoint_weighted_setIntegral hB.toIsPreBrownianReal T hT (-d) (Set.Ici m) measurableSet_Ici
  have hneg : (gaussianReal ((-d) * (T : ℝ)) T).real (Set.Ici m) =
      (gaussianReal (d * (T : ℝ)) T).real (Set.Iic (-m)) := by
    simpa only [neg_mul] using gaussian_neg_tail_eq_cdf (d * (T : ℝ)) T m
  have hJ : (∫ ω in H, E.indicator W ω ∂P) =
      Real.exp (2 * d * m) * (gaussianReal (d * (T : ℝ)) T).real (Set.Iic (-m)) := by
    calc
      _ = ∫ ω in H, (if B T ω ≤ m then W ω else 0) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          by_cases he : B T ω ≤ m <;> simp [E, Set.indicator, he])
      _ = ∫ ω in H, (if m ≤ B T ω then R ω else 0) ∂P := href
      _ = ∫ ω, (if m ≤ B T ω then R ω else 0) ∂P := hwhole
      _ = Real.exp (2 * d * m) * ∫ ω in G, V ω ∂P := by
        rw [← integral_const_mul, ← integral_indicator₀ hG]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          by_cases hge : m ≤ B T ω <;> simp [G, Set.indicator, hge, hfactor])
      _ = _ := by rw [hminus, hneg]
  have hnohit : (∫ ω in C, W ω ∂P) =
      (gaussianReal (d * (T : ℝ)) T).real (Set.Iic m) -
        Real.exp (2 * d * m) * (gaussianReal (d * (T : ℝ)) T).real (Set.Iic (-m)) := by
    rw [hlow, hJ] at hsplit
    linarith
  exact (ArgmaxBrownianContinuousMaximumTilt.continuous_maximum_tilt hB T hT d m).trans hnohit
theorem drifted_maximum_cdf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (d : ℝ) (M : Ω → ℝ) (hMm : AEMeasurable M P)
    (hM : ∀ᵐ ω ∂P,
      IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Set.Icc 0 T) (M ω))
    (m : ℝ) (hm : 0 ≤ m) :
    P.real {ω | M ω ≤ m} =
      (gaussianReal (d * (T : ℝ)) T).real (Set.Iic m) -
        Real.exp (2 * d * m) * (gaussianReal (d * (T : ℝ)) T).real (Set.Iic (-m)) := by
  have hnullM : NullMeasurableSet {ω | M ω ≤ m} P :=
    hMm.nullMeasurableSet_preimage measurableSet_Iic
  have hnullPath := ArgmaxBrownianContinuousMaximumTilt.finite_path_bound_nullMeasurable hB T d m
  calc
    _ = ∫ ω, ({ω | M ω ≤ m}).indicator (fun _ : Ω => (1 : ℝ)) ω ∂P := by
      rw [integral_indicator₀ hnullM]
      simp
    _ = ∫ ω, ({ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m}).indicator
        (fun _ : Ω => (1 : ℝ)) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hM] with ω hω
      have hiff := (ArgmaxBrownianContinuousMaximumTilt.isLUB_bound_iff
        (fun t => B t ω + d * (t : ℝ)) T (M ω) m hω).symm
      by_cases hb : M ω ≤ m
      · have hp := hiff.mp hb
        simp only [Set.indicator, Set.mem_ofPred_eq, if_pos hb, if_pos hp]
      · have hp : ¬ ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m := fun h => hb (hiff.mpr h)
        simp only [Set.indicator, Set.mem_ofPred_eq, if_neg hb, if_neg hp]
    _ = P.real {ω | ∀ t : ℝ≥0, t ≤ T → B t ω + d * (t : ℝ) ≤ m} := by
      rw [integral_indicator₀ hnullPath]
      simp
    _ = _ := continuous_bound_cdf hB T hT d m hm
end ArgmaxBrownianDriftedMaximumCDF
namespace ArgmaxBrownianPositiveMaximumLaplace
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
theorem maximum_laplace_eq_J
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (d : ℝ) (hd : 0 < d)
    (M : Ω → ℝ) (hMm : AEMeasurable M P)
    (hM : ∀ᵐ ω ∂P, IsLUB ((fun t : ℝ≥0 => B t ω + d * (t : ℝ)) '' Icc 0 T) (M ω)) :
    (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) =
      (2 * Real.exp (-(d ^ 2 * (T : ℝ) / 2)) /
        (Real.sqrt (2 * Real.pi) * (T : ℝ) ^ ((3 : ℝ) / 2))) *
      (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-d * u - u ^ 2 / (2 * (T : ℝ)))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ M ω := by
    filter_upwards [hM, hB.eval_zero_ae_eq_zero] with ω hω hzero
    have hb := hω.1 ⟨0, by simp, rfl⟩
    simpa only [hzero, NNReal.coe_zero, mul_zero, add_zero] using hb
  apply ArgmaxPositiveMaximumLaplaceAssembly.laplace_eq_J_of_gaussian_cdf
    M hMm hnonneg d hd T (ne_of_gt hT)
  intro m hm
  exact ArgmaxBrownianDriftedMaximumCDF.drifted_maximum_cdf hB T hT d M hMm hM m hm
end ArgmaxBrownianPositiveMaximumLaplace
open MeasureTheory Set
namespace ArgmaxContinuousLaplaceProfile
lemma profile_denominator_comparison (x : ℝ) (hx : 1 ≤ x) :
    1 / x ^ ((3 : ℝ) / 2) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) / (1 + x) ^ ((3 : ℝ) / 2) := by
  have hp : (1 + x) ^ ((3 : ℝ) / 2) ≤
      (2 : ℝ) ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) := by
    calc
      _ ≤ (2 * x) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = _ := Real.mul_rpow (by norm_num) (by linarith)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < x) _)
    (Real.rpow_pos_of_pos (by linarith : 0 < 1 + x) _)).mpr
  simpa only [one_mul] using hp
theorem laplace_expression_lower (d x : ℝ) (hd : 0 < d) (hx : 1 ≤ x) :
    (2 * Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) ≤
      (2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) *
        (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x))) := by
  have hden : x ^ ((3 : ℝ) / 2) ≤ (1 + x) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hj := ArgmaxContinuousLaplaceIntegral.laplace_integral_lower d x hd hx
  calc
    _ ≤ (2 * Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi)) *
        Real.exp (-(d ^ 2 / 2) * x) / x ^ ((3 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) * Real.exp (-2 * d - 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)
theorem laplace_expression_upper (d x : ℝ) (hd : 0 < d) (hx : 1 ≤ x) :
    (2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) *
        (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x))) ≤
      (4 * (2 : ℝ) ^ ((3 : ℝ) / 2) / (d ^ 3 * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) := by
  have hj := ArgmaxContinuousLaplaceIntegral.laplace_integral_upper d x hd (by linarith)
  have hp := profile_denominator_comparison x hx
  calc
    _ ≤ (2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) * (2 / d ^ 3) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = (4 * Real.exp (-(d ^ 2 / 2) * x) / (d ^ 3 * Real.sqrt (2 * Real.pi))) *
        (1 / x ^ ((3 : ℝ) / 2)) := by ring
    _ ≤ (4 * Real.exp (-(d ^ 2 / 2) * x) / (d ^ 3 * Real.sqrt (2 * Real.pi))) *
        ((2 : ℝ) ^ ((3 : ℝ) / 2) / (1 + x) ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring
theorem tail_profile_of_laplace_comparison (d : ℝ) (hd : 0 < d) (F : ℝ → ℝ)
    (hF : ∀ x : ℝ, 1 ≤ x →
      (1 / 2 : ℝ) * ((2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) *
        (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x)))) ≤ F x ∧
      F x ≤ ((2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) *
        (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x))))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      c * Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) ≤ F x ∧
      F x ≤ C * Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) := by
  refine ⟨Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi),
    4 * (2 : ℝ) ^ ((3 : ℝ) / 2) / (d ^ 3 * Real.sqrt (2 * Real.pi)),
    by positivity, by positivity, ?_⟩
  intro x hx
  have hl := laplace_expression_lower d x hd hx
  have hu := laplace_expression_upper d x hd hx
  refine ⟨?_, (hF x hx).2.trans hu⟩
  have hs := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hs' : (Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi)) *
      Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2) ≤
      (1 / 2 : ℝ) * ((2 * Real.exp (-(d ^ 2 / 2) * x) /
        (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) *
        (∫ m : ℝ in Ioi 0, m ^ 2 * Real.exp (-d * m - m ^ 2 / (2 * x)))) := by
    calc
      _ = (1 / 2 : ℝ) * ((2 * Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ _ := hs
  exact hs'.trans (hF x hx).1
end ArgmaxContinuousLaplaceProfile
namespace ArgmaxContinuousH2
theorem two_arm_profile
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hArms : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (d : ℝ) (hd : 0 < d) (H : ℝ → Ω → ℝ) (T : Ω → ℝ)
    (hplus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H (t : ℝ) ω = B t ω - d * (t : ℝ))
    (hminus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H (-(t : ℝ)) ω = C t ω - d * (t : ℝ))
    (hmax : ∀ᵐ ω ∂P, ∀ t : ℝ, H t ω ≤ H (T ω) ω)
    (x : ℝ) (hx : 1 ≤ x) :
    (Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi)) *
        (Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)) ≤ P.real {ω | x < T ω} ∧
      P.real {ω | x < T ω} ≤
        (4 * (2 : ℝ) ^ ((3 : ℝ) / 2) / (d ^ 3 * Real.sqrt (2 * Real.pi))) *
          (Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)) ∧
      (∀ᵐ ω ∂P, T ω ≠ x) := by
  let s : ℝ≥0 := NNReal.mk x (by linarith)
  have hs : 0 < s := by change (0 : ℝ) < x; linarith
  obtain ⟨M, hMm, hMp, hlo, hhi, hne⟩ :=
    ArgmaxActualTwoArmLaplace.actual_two_arm_tail_laplace_sandwich
      P B C hB hC hArms s d hd H T hplus hminus hmax
  have hLap := ArgmaxBrownianPositiveMaximumLaplace.maximum_laplace_eq_J hB s hs d hd M hMm
    (hMp.mono (fun ω h => h.1))
  have hexp : -(d ^ 2 * x / 2) = -(d ^ 2 / 2) * x := by ring
  have hLap' : (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) =
      (2 * Real.exp (-(d ^ 2 / 2) * x) / (Real.sqrt (2 * Real.pi) * x ^ ((3 : ℝ) / 2))) *
        (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-d * u - u ^ 2 / (2 * x))) := by
    simpa only [s, NNReal.coe_mk, hexp] using hLap
  have hJlo := ArgmaxContinuousLaplaceProfile.laplace_expression_lower d x hd hx
  have hJhi := ArgmaxContinuousLaplaceProfile.laplace_expression_upper d x hd hx
  rw [← hLap'] at hJlo hJhi
  have hlo' : (1 / 2 : ℝ) * (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) ≤
      P.real {ω | x < T ω} := by simpa only [s, NNReal.coe_mk] using hlo
  have hhi' : P.real {ω | x < T ω} ≤ (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) := by
    simpa only [s, NNReal.coe_mk] using hhi
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (1 / 2 : ℝ) * ((2 * Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by ring
      _ ≤ (1 / 2 : ℝ) * (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) :=
        mul_le_mul_of_nonneg_left hJlo (by norm_num)
      _ ≤ _ := hlo'
  · calc
      _ ≤ (∫ ω, Real.exp (-((2 * d) * M ω)) ∂P) := hhi'
      _ ≤ _ := hJhi
      _ = _ := by ring
  · simpa only [s, NNReal.coe_mk] using hne
theorem continuous_directional_bounds :
  ∀ d : ℝ, 0 < d →
    let q : ℝ → ℝ := fun x => Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)
    ∃ c C R : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ R ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ T : Ω → ℝ, AEMeasurable T P →
          (∀ᵐ ω ∂P, ∀ t : ℝ,
            OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (T ω) ω) →
          ∀ x : ℝ, R ≤ x →
            c * q x ≤ P.real {ω | x < T ω} ∧
            1 - P.real {ω | -x < T ω} ≤ C * q x := by
  intro d hd
  dsimp only
  refine ⟨Real.exp (-2 * d - 2) / Real.sqrt (2 * Real.pi),
    4 * (2 : ℝ) ^ ((3 : ℝ) / 2) / (d ^ 3 * Real.sqrt (2 * Real.pi)),
    1, by positivity, by positivity, by norm_num, ?_⟩
  intro Ω _ P _ B hB hC hArms T hT hmax x hx
  let H : ℝ → Ω → ℝ := OMA.S_mo_142880.height B d
  have hplus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      H (t : ℝ) ω = B (t : ℝ) ω - d * (t : ℝ) := by
    exact Filter.Eventually.of_forall (fun ω t => by
      simp only [H, OMA.S_mo_142880.height, abs_of_nonneg t.coe_nonneg])
  have hminus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      H (-(t : ℝ)) ω = B (-(t : ℝ)) ω - d * (t : ℝ) := by
    exact Filter.Eventually.of_forall (fun ω t => by
      simp only [H, OMA.S_mo_142880.height, abs_neg, abs_of_nonneg t.coe_nonneg])
  have hright := two_arm_profile P
    (fun t : ℝ≥0 => B (t : ℝ)) (fun t : ℝ≥0 => B (-(t : ℝ)))
    hB hC hArms d hd H T hplus hminus hmax x hx
  have hmirrorPlus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      H (-(t : ℝ)) ω = B (-(t : ℝ)) ω - d * (t : ℝ) := hminus
  have hmirrorMinus : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      H (-(-(t : ℝ))) ω = B (t : ℝ) ω - d * (t : ℝ) := by
    simpa only [neg_neg] using hplus
  have hmirrorMax : ∀ᵐ ω ∂P, ∀ t : ℝ,
      H (-t) ω ≤ H (-(-T ω)) ω := by
    filter_upwards [hmax] with ω hω
    intro t
    simpa only [neg_neg] using hω (-t)
  have hleft := two_arm_profile P
    (fun t : ℝ≥0 => B (-(t : ℝ))) (fun t : ℝ≥0 => B (t : ℝ))
    hC hB hArms.symm d hd (fun t ω => H (-t) ω) (fun ω => -T ω)
    hmirrorPlus hmirrorMinus hmirrorMax x hx
  have hne : ∀ᵐ ω ∂P, T ω ≠ -x := by
    filter_upwards [hleft.2.2] with ω hω
    intro heq
    apply hω
    rw [heq, neg_neg]
  have hcomp := ArgmaxActualTwoArmLaplace.complement_strict_tail_eq_mirrored_tail
    P T hT x hne
  refine ⟨hright.1, ?_⟩
  rw [hcomp]
  exact hleft.2.1
end ArgmaxContinuousH2
theorem OMA.solution : type_of% @OMA.S_mo_142880.main := by
  exact OMA.R_mo_142880_R1.main_of_continuous
    ArgmaxContinuousH2.continuous_directional_bounds
