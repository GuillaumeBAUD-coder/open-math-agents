import FormalConjectures.Arxiv.«2303.01089».FurstenbergTimesPTimesQ
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
Periodic probability measures on the additive circle return under arbitrarily
large powers of multiplication by three when their periods are coprime to three.
A finite average over a doubling orbit with small mean distance from zero
spreads the atoms while preserving periodicity and invariance. Baire category then
gives an atomless invariant measure whose orbit repeatedly avoids Haar measure.
-/

namespace OMA.Furstenberg

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
open Arxiv.id2303_01089


abbrev Torus := UnitAddCircle
abbrev Law := ProbabilityMeasure Torus

noncomputable def push (n : ℕ) (μ : Law) : Law :=
  μ.map (Tn_continuous n).aemeasurable

theorem continuous_push (n : ℕ) : Continuous (push n) :=
  ProbabilityMeasure.continuous_map (Tn_continuous n)

def periodicLaws : Set Law :=
  { μ | push 2 μ = μ ∧ ∃ d : ℕ, 0 < d ∧ Nat.Coprime 3 d ∧
    ∀ᵐ x ∂μ.toMeasure, d • x = 0 }

noncomputable def pointLaw : Law := ⟨Measure.dirac 0, inferInstance⟩

theorem pointLaw_periodic : pointLaw ∈ periodicLaws := by
  refine ⟨?_, 1, by decide, by decide, ?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    change (Measure.dirac (0 : Torus)).map (Tn 2) = Measure.dirac 0
    rw [Measure.map_dirac' (Tn_continuous 2).measurable]
    simp [Tn]
  · change ∀ᵐ x ∂Measure.dirac (0 : Torus), (1 : ℕ) • x = 0
    simp [ae_dirac_eq]

theorem push_periodic {μ : Law} (h : μ ∈ periodicLaws) (N : ℕ) :
    ∃ n ≥ N, push (3 ^ n) μ = μ := by
  obtain ⟨_, d, hd, hcop, hs⟩ := h
  let n := d.totient * (N + 1)
  have hn : N ≤ n := by
    dsimp [n]
    have ht := Nat.totient_pos.mpr hd
    calc
      N ≤ N + 1 := Nat.le_succ N
      _ = 1 * (N + 1) := (one_mul _).symm
      _ ≤ d.totient * (N + 1) := Nat.mul_le_mul_right _ ht
  refine ⟨n, hn, ProbabilityMeasure.toMeasure_injective ?_⟩
  change μ.toMeasure.map (Tn (3 ^ n)) = μ.toMeasure
  conv_rhs => rw [← Measure.map_id (μ := μ.toMeasure)]
  apply Measure.map_congr
  filter_upwards [hs] with x hx
  have he : 3 ^ n ≡ 1 [MOD d] := by
    simpa [n, pow_mul] using (Nat.ModEq.pow_totient hcop).pow (N + 1)
  change (3 ^ n) • x = x
  have eqmod (a : ℕ) : a • x = (a % d) • x := by
    conv_lhs => rw [← Nat.mod_add_div a d, add_nsmul, mul_nsmul, hx, nsmul_zero, add_zero]
  exact (eqmod _).trans (by rw [show 3 ^ n % d = 1 % d from he, ← eqmod 1, one_nsmul])

noncomputable def orbit (k : ℕ) (i : Fin k) : Torus :=
  ((2 : ℝ) ^ i.val / ((2 : ℝ) ^ k - 1) : ℝ)

theorem orbit_den_pos {k : ℕ} (hk : 0 < k) : 0 < (2 : ℝ) ^ k - 1 :=
  sub_pos.mpr (one_lt_pow₀ (by norm_num) hk.ne')

theorem orbit_rep_mem {k : ℕ} (hk : 1 < k) (i : Fin k) :
    (2 : ℝ) ^ i.val / ((2 : ℝ) ^ k - 1) ∈ Ico (0 : ℝ) 1 := by
  have hi : i.val ≤ k - 1 := by omega
  have hp : (2 : ℝ) ^ i.val ≤ 2 ^ (k - 1) :=
    pow_le_pow_right₀ (by norm_num) hi
  have hbig : (1 : ℝ) < 2 ^ (k - 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hpow : (2 : ℝ) ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  refine ⟨div_nonneg (by positivity) (orbit_den_pos (by omega)).le,
    (div_lt_one (orbit_den_pos (by omega))).2 ?_⟩
  linarith

theorem orbit_injective {k : ℕ} (hk : 1 < k) : Function.Injective (orbit k) := by
  intro i j h
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (by simpa using orbit_rep_mem hk i) (by simpa using orbit_rep_mem hk j)).mp h
  have hp : (2 : ℝ) ^ i.val = 2 ^ j.val :=
    (div_left_inj' (orbit_den_pos (k := k) (by omega)).ne').mp he
  exact Fin.ext ((pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num)) hp)

theorem orbit_torsion {k : ℕ} (hk : 0 < k) (i : Fin k) :
    (2 ^ k - 1 : ℕ) • orbit k i = 0 := by
  have hnat : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow
  have hden : ((2 ^ k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
    simp [Nat.cast_sub hnat]
  have he : (2 ^ k - 1 : ℕ) • ((2 : ℝ) ^ i.val / (2 ^ k - 1)) = ((2 ^ i.val : ℕ) : ℝ) := by
    rw [nsmul_eq_mul, hden, Nat.cast_pow, Nat.cast_ofNat]
    field_simp [(orbit_den_pos hk).ne']
  rw [orbit, ← AddCircle.coe_nsmul, he, AddCircle.coe_eq_zero_iff]
  exact ⟨((2 : ℕ) ^ i.val : ℤ), by simp [zsmul_eq_mul]⟩

theorem orbit_rotate {k : ℕ} (hk : 0 < k) (i : Fin k) :
    (2 : ℕ) • orbit k i = orbit k (finRotate k i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hd := (orbit_den_pos hk).ne'
  by_cases hi : i.val < m
  · have hr : (finRotate (m + 1) i).val = i.val + 1 := by
      obtain ⟨j, hj⟩ := i
      exact congrArg Fin.val (finRotate_of_lt hi)
    simp only [orbit, hr, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_ofNat, pow_succ]
    congr 1
    ring
  · have he : i = Fin.last m := Fin.ext (by simp; omega)
    subst i
    rw [finRotate_last]
    simp only [orbit, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_ofNat, Fin.val_last,
      Fin.val_zero, pow_zero]
    have he : (2 : ℝ) * (2 ^ m / (2 ^ (m + 1) - 1)) = 1 + 1 / (2 ^ (m + 1) - 1) := by
      field_simp [hd]
      ring
    rw [he, AddCircle.coe_add]
    simp

theorem orbit_norm_sum {k : ℕ} (hk : 0 < k) :
    ∑ i : Fin k, ‖orbit k i‖ ≤ 1 := by
  calc
    _ ≤ ∑ i : Fin k, (2 : ℝ) ^ i.val / (2 ^ k - 1) := by
      apply Finset.sum_le_sum
      intro i _
      have h := QuotientAddGroup.norm_mk_le_norm
        (S := AddSubgroup.zmultiples (1 : ℝ))
        (m := (2 : ℝ) ^ i.val / (2 ^ k - 1))
      have hnonneg : 0 ≤ (2 : ℝ) ^ i.val / ((2 : ℝ) ^ k - 1) :=
        div_nonneg (by positivity) (orbit_den_pos hk).le
      simpa only [orbit, Real.norm_eq_abs, abs_of_nonneg hnonneg] using h
    _ = 1 := by
      rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun i : ℕ => (2 : ℝ) ^ i),
        geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      norm_num
      exact (orbit_den_pos hk).ne'

noncomputable def translateLaw (a : Torus) (μ : Law) : Law :=
  μ.map (f := fun x => x + a) (by fun_prop)

noncomputable def spread {k : ℕ} (hk : 0 < k) (μ : Law) : Law :=
  ⟨(k : ℝ≥0∞)⁻¹ • ∑ i : Fin k, (translateLaw (orbit k i) μ).toMeasure,
    ⟨by
      simp [Measure.smul_apply, Measure.finsetSum_apply]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hk.ne') (ENNReal.natCast_ne_top k)⟩⟩

theorem spread_singleton {k : ℕ} (hk : 1 < k) (μ : Law) (x : Torus) :
    (spread (k := k) (by omega) μ).toMeasure {x} ≤ (k : ℝ≥0∞)⁻¹ := by
  change ((k : ℝ≥0∞)⁻¹ • ∑ i : Fin k, (translateLaw (orbit k i) μ).toMeasure) {x} ≤ _
  rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  conv_rhs => rw [← mul_one ((k : ℝ≥0∞)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ bot_le
  simp only [translateLaw, ProbabilityMeasure.toMeasure_map]
  have hm (a : Torus) : Measurable (fun x : Torus => x + a) := by fun_prop
  simp_rw [Measure.map_apply (hm _) (measurableSet_singleton x)]
  rw [← measure_univ (μ := μ.toMeasure)]
  apply sum_measure_le_measure_univ
  · intro i _
    exact ((measurableSet_singleton x).preimage (by fun_prop)).nullMeasurableSet
  · intro i _ j _ hij
    apply Disjoint.aedisjoint
    refine Set.disjoint_left.mpr fun y hi hj => hij (orbit_injective hk ?_)
    simp only [mem_preimage, mem_singleton_iff] at hi hj
    exact add_left_cancel (hi.trans hj.symm)

theorem spread_invariant {k : ℕ} (hk : 0 < k) {μ : Law} (hμ : push 2 μ = μ) :
    push 2 (spread hk μ) = spread hk μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (Tn 2)
    ((k : ℝ≥0∞)⁻¹ • ∑ i : Fin k, (translateLaw (orbit k i) μ).toMeasure) = _
  rw [Measure.map_smul, Measure.map_finset_sum' (Tn_continuous 2).aemeasurable]
  congr 1
  have hm := congrArg ProbabilityMeasure.toMeasure hμ
  change Measure.map (Tn 2) μ.toMeasure = μ.toMeasure at hm
  have aux (i : Fin k) : Measure.map (Tn 2) (translateLaw (orbit k i) μ).toMeasure =
      (translateLaw (orbit k (finRotate k i)) μ).toMeasure := by
    simp only [translateLaw, ProbabilityMeasure.toMeasure_map]
    nth_rw 2 [← hm]
    rw [Measure.map_map (Tn_continuous 2).measurable (by fun_prop),
      Measure.map_map (by fun_prop) (Tn_continuous 2).measurable]
    congr 1
    funext x
    simp [Tn, orbit_rotate hk i]
  simp_rw [aux]
  exact Equiv.sum_comp (finRotate k) (fun i => (translateLaw (orbit k i) μ).toMeasure)

theorem spread_periodic {k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime 3 (2 ^ k - 1))
    {μ : Law} (hμ : μ ∈ periodicLaws) : spread hk μ ∈ periodicLaws := by
  obtain ⟨hm, d, hd, hc, hs⟩ := hμ
  let e : ℕ := 2 ^ k - 1
  have he : 0 < e := by dsimp [e]; exact Nat.sub_pos_of_lt (one_lt_pow₀ (by decide) hk.ne')
  refine ⟨spread_invariant hk hm, d * e, Nat.mul_pos hd he, hc.mul_right hcop, ?_⟩
  have hclosed : IsClosed {x : Torus | (d * e) • x = 0} :=
    isClosed_eq (continuous_nsmul _) continuous_const
  rw [ae_iff_measure_eq hclosed.measurableSet.nullMeasurableSet, measure_univ]
  change ((k : ℝ≥0∞)⁻¹ • ∑ i : Fin k, (translateLaw (orbit k i) μ).toMeasure)
    {x : Torus | (d * e) • x = 0} = 1
  rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  have H (i : Fin k) : (translateLaw (orbit k i) μ).toMeasure
      {x : Torus | (d * e) • x = 0} = 1 := by
    rw [← measure_univ (μ := (translateLaw (orbit k i) μ).toMeasure)]
    apply (ae_iff_measure_eq hclosed.measurableSet.nullMeasurableSet).mp
    change ∀ᵐ x ∂μ.toMeasure.map (fun x => x + orbit k i), (d * e) • x = 0
    apply (ae_map_iff (by fun_prop) hclosed.measurableSet).mpr
    filter_upwards [hs] with x hx
    rw [nsmul_add]
    have h1 : (d * e) • x = 0 := by rw [mul_nsmul, hx, nsmul_zero]
    have h2 : (d * e) • orbit k i = 0 := by
      rw [mul_comm d e, mul_nsmul, show e • orbit k i = 0 from orbit_torsion hk i, nsmul_zero]
    simp [h1, h2]
  simp only [H, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hk.ne') (ENNReal.natCast_ne_top k)

theorem spread_tendsto (μ : Law) :
    Tendsto (fun n : ℕ => spread (k := 2 * n + 3) (by omega) μ) atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f _ ⟨L, hL⟩
  let I : ℝ := ∫ x, f x ∂μ.toMeasure
  have bound (k : ℕ) (hk : 0 < k) :
      dist (∫ x, f x ∂(spread hk μ).toMeasure) I ≤ (L : ℝ) / k := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hterm (i : Fin k) :
        |(∫ x, f x ∂(translateLaw (orbit k i) μ).toMeasure) - I| ≤ (L : ℝ) * ‖orbit k i‖ := by
      simp only [translateLaw, ProbabilityMeasure.toMeasure_map]
      have hf : Integrable f μ.toMeasure :=
        hL.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hft : Integrable (fun x : Torus => f (x + orbit k i)) μ.toMeasure :=
        (hL.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      dsimp [I]
      rw [integral_map (by fun_prop) hL.continuous.aestronglyMeasurable, ← integral_sub hft hf,
        ← Real.norm_eq_abs]
      simpa using norm_integral_le_of_norm_le_const (μ := μ.toMeasure)
        (Filter.Eventually.of_forall fun x =>
          show ‖f (x + orbit k i) - f x‖ ≤ (L : ℝ) * ‖orbit k i‖ by
            simpa [dist_eq_norm] using hL.dist_le_mul (x + orbit k i) x)
    change dist (∫ x, f x ∂((k : ℝ≥0∞)⁻¹ •
      ∑ i : Fin k, (translateLaw (orbit k i) μ).toMeasure)) I ≤ _
    rw [integral_smul_measure, integral_finsetSum_measure (fun i _ =>
      hL.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, Real.dist_eq]
    have hrew : (k : ℝ)⁻¹ * ∑ i : Fin k, ((∫ x, f x ∂(translateLaw (orbit k i) μ).toMeasure) - I) =
        (k : ℝ)⁻¹ * (∑ i : Fin k, ∫ x, f x ∂(translateLaw (orbit k i) μ).toMeasure) - I := by
      simp [Finset.sum_sub_distrib, mul_sub, hkR]
    rw [← hrew, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ)⁻¹)]
    calc
      _ ≤ (k : ℝ)⁻¹ * ∑ i : Fin k, |(∫ x, f x ∂(translateLaw (orbit k i) μ).toMeasure) - I| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (k : ℝ)⁻¹ * ∑ i : Fin k, (L : ℝ) * ‖orbit k i‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
      _ ≤ (L : ℝ) / k := by
        rw [← Finset.mul_sum, div_eq_inv_mul]
        gcongr
        simpa using mul_le_mul_of_nonneg_left (orbit_norm_sum hk) L.coe_nonneg
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => bound _ (by omega)) ?_
  have htop : Tendsto (fun n : ℕ => (2 * n + 3 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  simpa [div_eq_mul_inv, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp htop).const_mul (L : ℝ)

theorem odd_den_coprime (n : ℕ) : Nat.Coprime 3 (2 ^ (2 * n + 3) - 1) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  have hfour : 4 ≡ 1 [MOD 3] := by decide
  have hp : 2 ^ (2 * n + 3) ≡ 2 [MOD 3] := by
    have heq : (2 : ℕ) ^ (2 * n + 3) = 4 ^ n * 8 := by rw [pow_add, pow_mul]; rfl
    rw [heq]
    exact ((hfour.pow n).mul_right 8).trans (by simpa only [one_pow, one_mul] using
      (show 8 ≡ 2 [MOD 3] by decide))
  have hp0 : (2 : ℕ) ^ (2 * n + 3) % 3 = 2 := hp
  have hpos : 1 ≤ (2 : ℕ) ^ (2 * n + 3) := Nat.one_le_two_pow
  intro hbad
  have hmod : (2 ^ (2 * n + 3) - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hbad
  omega

theorem closed_mass_lt_open {K : Set Torus} (hK : IsClosed K) (ε : ℝ≥0∞) :
    IsOpen { μ : Law | μ.toMeasure K < ε } := by
  apply isOpen_iff_mem_nhds.mpr
  intro μ hμ
  have ht : Tendsto (id : Law → Law) (𝓝 μ) (𝓝 μ) := tendsto_id
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto ht hK
  exact eventually_lt_of_limsup_lt (hlim.trans_lt hμ)

theorem exists_small_ball (μ : Law) (x : Torus) {ε : ℝ≥0∞} (h : μ.toMeasure {x} < ε) :
    ∃ r : ℝ, 0 < r ∧ μ.toMeasure (closedBall x r) < ε := by
  let r : ℕ → ℝ := fun n => 1 / (n + 1)
  have hpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hanti : Antitone r := by
    intro i j hij
    dsimp [r]
    gcongr
  have ht : Tendsto r atTop (𝓝 0) := by
    have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [r, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop
  have hi : (⋂ n, closedBall x (r n)) = {x} := by
    ext y
    simp only [mem_iInter, mem_closedBall, mem_singleton_iff]
    refine ⟨fun hy => dist_le_zero.mp (le_of_tendsto_of_tendsto' tendsto_const_nhds ht hy), ?_⟩
    rintro rfl n
    simpa using (hpos n).le
  have hμ := tendsto_measure_iInter_atTop (μ := μ.toMeasure)
    (fun n => (show IsClosed (closedBall x (r n)) from isClosed_closedBall).measurableSet.nullMeasurableSet)
    (fun _ _ hij => closedBall_subset_closedBall (hanti hij)) ⟨0, measure_ne_top _ _⟩
  rw [hi] at hμ
  obtain ⟨n, hn⟩ := (hμ.eventually_lt_const h).exists
  exact ⟨r n, hpos n, hn⟩

def smallAtoms (ε : ℝ≥0∞) : Set Law :=
  { μ | ∀ x : Torus, μ.toMeasure {x} < ε }

theorem smallAtoms_open (ε : ℝ≥0∞) : IsOpen (smallAtoms ε) := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro μ hμ
  choose r hr hmass using fun x => exists_small_ball μ x (hμ x)
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun x => ball x (r x))
    (fun x => ball_mem_nhds _ (hr x))
  have H : ∀ᶠ ν in 𝓝 μ, ∀ x ∈ s, ν.toMeasure (closedBall x (r x)) < ε := by
    rw [Filter.eventually_all_finset]
    exact fun x _ => (closed_mass_lt_open isClosed_closedBall ε).mem_nhds (hmass x)
  filter_upwards [H] with ν hν
  intro y
  have hx : y ∈ ⋃ x ∈ s, ball x (r x) := by simp [hs]
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp hx
  exact (measure_mono (singleton_subset_iff.mpr (ball_subset_closedBall hy))).trans_lt (hν x hx)

theorem atomless_of_singletons {μ : Law} (h : ∀ x : Torus, μ.toMeasure {x} = 0) :
    Arxiv.id2303_01089.MeasureTheory.IsAtomLess μ.toMeasure := by
  classical
  refine ⟨fun A hA hAtom => ?_⟩
  obtain ⟨hpos, hatom⟩ := hAtom
  choose r hr he using fun x => exists_small_ball μ x ((h x).trans_lt hpos)
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun x => ball x (r x))
    (fun x => ball_mem_nhds _ (hr x))
  have hzero (x : Torus) : μ.toMeasure (A ∩ ball x (r x)) = 0 := by
    refine (hatom _ inter_subset_left (hA.inter measurableSet_ball)).resolve_right ?_
    intro hh
    have hle : μ.toMeasure (A ∩ ball x (r x)) ≤ μ.toMeasure (closedBall x (r x)) :=
      measure_mono (inter_subset_right.trans ball_subset_closedBall)
    exact (he x).not_ge (hh ▸ hle)
  have hsub : A ⊆ ⋃ x ∈ s, A ∩ ball x (r x) := by
    intro x hx
    have hh : x ∈ ⋃ y ∈ s, ball y (r y) := by simp [hs]
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hh
    exact mem_iUnion₂.mpr ⟨y, hy, hx, hxy⟩
  have hle := (measure_mono (μ := μ.toMeasure) hsub).trans (measure_biUnion_finset_le _ _)
  simp only [hzero, Finset.sum_const_zero] at hle
  exact hpos.not_ge hle

theorem independent_two_three : Nat.MultiplicativelyIndependent 2 3 := by
  change Irrational (Real.log 2 / Real.log 3)
  rintro ⟨q, hq⟩
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hqpos : 0 < q := by
    exact_mod_cast (show 0 < (q : ℝ) by rw [hq]; positivity)
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have he : Real.log (2 : ℝ) * q.den = Real.log (3 : ℝ) * q.num.natAbs := by
    rw [Rat.cast_def] at hq
    have hqn : ((q.num.natAbs : ℕ) : ℝ) = q.num := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum.le]
    rw [hqn]
    have heq := (div_eq_div_iff hden.ne' h3.ne').mp hq
    linarith
  have hpow : (2 : ℕ) ^ q.den = 3 ^ q.num.natAbs := by
    have he' : (2 : ℝ) ^ q.den = 3 ^ q.num.natAbs := by
      apply Real.log_injOn_pos
      · change 0 < (2 : ℝ) ^ q.den
        positivity
      · change 0 < (3 : ℝ) ^ q.num.natAbs
        positivity
      · simpa [Real.log_pow, mul_comm] using he
    exact_mod_cast he'
  have hdvd : 2 ∣ (3 : ℕ) ^ q.num.natAbs := hpow ▸ dvd_pow_self _ q.den_pos.ne'
  have hdvd' := Nat.prime_two.dvd_of_dvd_pow hdvd
  norm_num at hdvd'

abbrev PeriodicClosure := closure periodicLaws

theorem periodic_dense :
    Dense { μ : PeriodicClosure | (μ : Law) ∈ periodicLaws } := by
  apply dense_iff_inter_open.mpr
  rintro W hW ⟨x, hx⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hW
  obtain ⟨y, hyV, hyP⟩ := mem_closure_iff.mp x.property V hV hx
  exact ⟨⟨y, subset_closure hyP⟩, hyV, hyP⟩

theorem smallAtoms_dense (ε : ℝ≥0∞) (hε : 0 < ε) :
    Dense { μ : PeriodicClosure | (μ : Law) ∈ smallAtoms ε } := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨x, hxW, hxP⟩ := dense_iff_inter_open.mp periodic_dense W hW hWne
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hW
  have ht := spread_tendsto x.val
  have hin : ∀ᶠ n : ℕ in atTop, spread (k := 2 * n + 3) (by omega) x.val ∈ V :=
    ht.eventually (hV.mem_nhds hxW)
  have ht' : Tendsto (fun n : ℕ => ((2 * n + 3 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have hu : Tendsto (fun n : ℕ => 2 * n + 3) atTop atTop :=
      tendsto_atTop.mpr fun a => eventually_atTop.mpr ⟨a, fun b hb => by omega⟩
    simpa using tendsto_inv_iff.mpr (ENNReal.tendsto_nat_nhds_top.comp hu)
  obtain ⟨n, hnV, hnε⟩ := (hin.and (ht'.eventually_lt_const hε)).exists
  let y := spread (k := 2 * n + 3) (by omega) x.val
  have hy : y ∈ periodicLaws := spread_periodic (by omega) (odd_den_coprime n) hxP
  exact ⟨⟨y, subset_closure hy⟩, hnV, fun z => (spread_singleton (by omega) x.val z).trans_lt hnε⟩

def returns (U : Set Law) (N : ℕ) : Set PeriodicClosure :=
  (closure { μ : PeriodicClosure | (μ : Law) ∈ U })ᶜ ∪
    ⋃ n ≥ N, { μ : PeriodicClosure | push (3 ^ n) μ.val ∈ U }

theorem returns_open {U : Set Law} (hU : IsOpen U) (N : ℕ) : IsOpen (returns U N) := by
  apply isClosed_closure.isOpen_compl.union
  refine isOpen_iUnion fun n => isOpen_iUnion fun _ => ?_
  exact hU.preimage ((continuous_push _).comp continuous_subtype_val)

theorem returns_dense {U : Set Law} (hU : IsOpen U) (N : ℕ) : Dense (returns U N) := by
  apply dense_iff_inter_open.mpr
  rintro W hW ⟨x, hx⟩
  let A : Set PeriodicClosure := { μ | (μ : Law) ∈ U }
  by_cases h : x ∈ closure A
  · have hne : (W ∩ A).Nonempty := mem_closure_iff.mp h W hW hx
    obtain ⟨y, ⟨hyW, hyA⟩, hyP⟩ := dense_iff_inter_open.mp periodic_dense
      (W ∩ A) (hW.inter (hU.preimage continuous_subtype_val)) hne
    obtain ⟨n, hn, he⟩ := push_periodic hyP N
    refine ⟨y, hyW, Or.inr (mem_iUnion₂.mpr ⟨n, hn, ?_⟩)⟩
    change push (3 ^ n) y.val ∈ U
    rw [he]
    exact hyA
  · exact ⟨x, hx, Or.inl h⟩

theorem point_ne_haar : pointLaw ≠ Arxiv.id2303_01089.UnitAddCircle.ProbabilityMeasure := by
  intro h
  have he := congrArg (fun μ : Law => μ.toMeasure ({0} : Set Torus)) h
  change Measure.dirac (0 : Torus) {0} = volume ({0} : Set Torus) at he
  have hzero : volume ({0} : Set Torus) = 0 := by
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    norm_num
  simp [hzero] at he

theorem counterexample :
    ¬ ∀ p q : ℕ, 2 ≤ p → 2 ≤ q → Nat.MultiplicativelyIndependent p q →
      ∀ μ : Law, Arxiv.id2303_01089.MeasureTheory.IsAtomLess μ.toMeasure →
        MeasurePreserving (Tn p) μ.toMeasure μ.toMeasure →
        Tendsto (fun n : ℕ => push (q ^ n) μ) atTop
          (𝓝 Arxiv.id2303_01089.UnitAddCircle.ProbabilityMeasure) := by
  intro H
  let : CompactSpace PeriodicClosure :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  obtain ⟨U, V, hU, hV, hpoint, hhaar, hdis⟩ := t2_separation point_ne_haar
  let A : Set PeriodicClosure := { μ | (μ : Law) ∈ U }
  have hA : IsOpen A := hU.preimage continuous_subtype_val
  have hAne : A.Nonempty := ⟨⟨pointLaw, subset_closure pointLaw_periodic⟩, hpoint⟩
  let ε : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hε (n : ℕ) : 0 < ε n := by simp [ε, ENNReal.inv_pos]
  have hlim : Tendsto ε atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
      tendsto_atTop.mpr fun a => eventually_atTop.mpr ⟨a, fun b hb => by omega⟩
    simpa [ε] using tendsto_inv_iff.mpr (ENNReal.tendsto_nat_nhds_top.comp ht)
  let events : ℕ → Set PeriodicClosure := fun n =>
    returns U n ∩ { μ | (μ : Law) ∈ smallAtoms (ε n) }
  have hDense : Dense (⋂ n, events n) := dense_iInter_of_isOpen_nat
    (fun n => (returns_open hU n).inter ((smallAtoms_open _).preimage continuous_subtype_val))
    (fun n => (returns_dense hU n).inter_of_isOpen_right (smallAtoms_dense _ (hε n))
      ((smallAtoms_open _).preimage continuous_subtype_val))
  obtain ⟨μ, hμA, hμall⟩ := dense_iff_inter_open.mp hDense A hA hAne
  have hh (n : ℕ) : μ ∈ events n := mem_iInter.mp hμall n
  have hs (x : Torus) : μ.val.toMeasure {x} = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun n => ((hh n).2 x).le)) bot_le
  have hclosed : IsClosed { ν : Law | push 2 ν = ν } :=
    isClosed_eq (continuous_push 2) continuous_id
  have hfix : push 2 μ.val = μ.val :=
    closure_minimal (s := periodicLaws) (fun _ hν => hν.1) hclosed μ.property
  have hpres : MeasurePreserving (Tn 2) μ.val.toMeasure μ.val.toMeasure :=
    ⟨(Tn_continuous 2).measurable, congrArg ProbabilityMeasure.toMeasure hfix⟩
  have hconv := H 2 3 (by decide) (by decide) independent_two_three μ.val
    (atomless_of_singletons hs) hpres
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv.eventually (hV.mem_nhds hhaar))
  have hR : μ ∈ returns U N := (hh N).1
  rcases hR with hbad | hret
  · exact hbad (subset_closure hμA)
  · obtain ⟨n, hn, hnu⟩ := mem_iUnion₂.mp hret
    exact Set.disjoint_left.mp hdis hnu (hN n hn)

end OMA.Furstenberg

theorem OMA.solution : type_of% @Arxiv.id2303_01089.conjecture_1_4 := by
  exact OMA.Furstenberg.counterexample
