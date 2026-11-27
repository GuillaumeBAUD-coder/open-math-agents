import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1
import Mathlib.Analysis.MellinTransform

/-! The Mellin transform of the centered partial sums is holomorphic to the right of the
one-quarter line. Splitting the integral at a fixed cutoff shows that multiplying by the
horizontal increment makes the transform tend to zero even on that line. Analytic
continuation along a horizontal ray then allows cancellation at any zero of the denominator.
-/
open Filter Asymptotics MeasureTheory Set Finset Complex
open scoped Topology
namespace Analytic969
noncomputable section
private def coeff (A : ℕ → ℕ) (c : ℝ) (n : ℕ) : ℂ := (A n : ℂ) - A (n-1) - c
private def err (A : ℕ → ℕ) (c : ℝ) (t : ℝ) : ℂ := ∑ k ∈ Icc 1 ⌊t⌋₊, coeff A c k
private lemma partial_sum (A : ℕ → ℕ) (c : ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, coeff A c k = (A n : ℂ) - A 0 - (c:ℂ)*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega),ih]
    simp [coeff]
    ring
private lemma err_zero (A : ℕ → ℕ) (c : ℝ) {t : ℝ} (ht : t < 1) : err A c t = 0 := by
  simp [err,Nat.floor_eq_zero.mpr ht]

private lemma err_local (A : ℕ → ℕ) (c : ℝ) : LocallyIntegrableOn (err A c) (Ici 0) := by
  unfold err
  simpa only [one_mul] using locallyIntegrableOn_mul_sum_Icc (m:=1) (coeff A c) (le_refl (0:ℝ))
    (locallyIntegrableOn_const (1:ℂ))

private lemma error_small (A : ℕ → ℕ) (c : ℝ)
    (hs : (fun n : ℕ => |(A n:ℝ)-c*n|) =o[atTop] fun n : ℕ => (n:ℝ)^(1/4:ℝ)) :
    (err A c) =o[atTop] fun t : ℝ => t^(1/4:ℝ) := by
  have h1 : (fun n : ℕ => (A n : ℂ) - (c:ℂ)*n) =o[atTop] fun n : ℕ => (n:ℝ)^(1/4:ℝ) := by
    apply Asymptotics.IsLittleO.of_norm_left
    simpa only [← ofReal_natCast, ← ofReal_mul, ← ofReal_sub, norm_real,Real.norm_eq_abs] using hs
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have h0 : (fun _ : ℕ => (A 0 : ℂ)) =o[atTop] fun n : ℕ => (n:ℝ)^(1/4:ℝ) :=
    isLittleO_const_left.mpr (Or.inr (by simpa [Function.comp_def,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using ht))
  have hn := (h1.sub h0).comp_tendsto (tendsto_nat_floor_atTop : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop)
  have hh : err A c =o[atTop] (fun t : ℝ => (⌊t⌋₊:ℝ)^(1/4:ℝ)) := by
    apply hn.congr_left
    intro t
    simp [err,partial_sum]
    ring
  apply hh.trans_isBigO
  refine isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),Real.norm_of_nonneg (Real.rpow_nonneg ht _),one_mul]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht) (by norm_num)

private lemma bot_bound (A : ℕ → ℕ) (c b : ℝ) : err A c =O[𝓝[>] 0] fun t : ℝ => t^(-b) := by
  refine isBigO_iff.mpr ⟨0,?_⟩
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht
  simp [err_zero A c ht]

private lemma mellin_diff {A : ℕ → ℕ} {c : ℝ}
    (hg : err A c =o[atTop] fun t : ℝ => t^(1/4:ℝ)) {s : ℂ} (hs : 1/4 < s.re) :
    DifferentiableAt ℂ (fun w : ℂ => mellin (err A c) (-w)) s := by
  have hh := mellin_differentiableAt_of_isBigO_rpow (s := -s) (a := -(1/4:ℝ))
    ((err_local A c).mono_set Set.Ioi_subset_Ici_self) (by simpa only [neg_neg] using hg.isBigO)
    (by simpa only [neg_re,neg_lt_neg_iff] using hs) (bot_bound A c ((-s).re-1)) (by linarith)
  exact hh.comp s differentiableAt_id.neg

private lemma mellin_int {A : ℕ → ℕ} {c : ℝ}
    (hg : err A c =o[atTop] fun t : ℝ => t^(1/4:ℝ)) {s : ℂ} (hs : 1/4 < s.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(-s-1)*err A c t) (Set.Ioi 0) := by
  exact mellinConvergent_of_isBigO_rpow (s := -s) (a := -(1/4:ℝ))
    ((err_local A c).mono_set Set.Ioi_subset_Ici_self) (by simpa only [neg_neg] using hg.isBigO)
    (by simpa only [neg_re,neg_lt_neg_iff] using hs) (bot_bound A c ((-s).re-1)) (by linarith)

private lemma mellin_eq (A : ℕ → ℕ) (c : ℝ) (s : ℂ) :
    mellin (err A c) (-s) = ∫ t : ℝ in Set.Ioi 1, (t:ℂ)^(-s-1)*err A c t := by
  change (∫ t : ℝ in Set.Ioi 0, (t:ℂ)^(-s-1)*err A c t) = _
  conv_rhs => rw [← integral_Ici_eq_integral_Ioi]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Set.Ici_subset_Ioi.mpr zero_lt_one)
  intro t ht
  simp [err_zero A c (lt_of_not_ge ht.2)]

private lemma right_side (A : ℕ → ℕ) (c : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hg : err A c =o[atTop] fun t : ℝ => t^(1/4:ℝ))
    (hid : LSeries (fun n : ℕ => (A n : ℂ)-A (n-1)) s * riemannZeta (2*s) = riemannZeta s) :
    (s*mellin (err A c) (-s)+(c:ℂ)*riemannZeta s)*riemannZeta (2*s)=riemannZeta s := by
  let f := fun n : ℕ => (A n : ℂ)-A (n-1)
  have hf : LSeriesSummable f s := by
    by_contra hn
    have hz := LSeries.eq_zero_of_not_LSeriesSummable f s hn
    change LSeries f s * _ = _ at hid
    rw [hz,zero_mul] at hid
    exact riemannZeta_ne_zero_of_one_lt_re hs hid.symm
  have hc := (LSeriesSummable_one_iff.mpr hs).smul (c:ℂ)
  have he : coeff A c = f - (c:ℂ) • (1 : ℕ → ℂ) := by ext n; simp [f,coeff]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, coeff A c k) =O[atTop] fun n : ℕ => (n:ℝ)^(1/4:ℝ) := by
    simpa only [Function.comp_def,err,Nat.floor_natCast] using hg.isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  have hl := LSeries_eq_mul_integral (coeff A c) (by norm_num : (0:ℝ)≤1/4) (by linarith : 1/4<s.re)
    (he ▸ hf.sub hc) hO
  have hml : LSeries (coeff A c) s = s*mellin (err A c) (-s) := by
    rw [hl,mellin_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [neg_add']
    exact mul_comm _ _
  rw [←hml,he,LSeries_sub hf hc,LSeries_smul,LSeries_one_eq_riemannZeta hs,sub_add_cancel]
  exact hid

private lemma boundary {A : ℕ → ℕ} {c : ℝ} {z : ℂ} (hz : 1/4 ≤ z.re)
    (hg : err A c =o[atTop] fun t : ℝ => t^(1/4:ℝ)) :
    Tendsto (fun h : ℝ => (h:ℂ)*mellin (err A c) (-(z+h))) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (hg.bound (by positivity : 0<ε/2))
  let T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  let C := ∫ t : ℝ in Set.Ioc 1 T, ‖err A c t‖
  have hCint : IntegrableOn (fun t => ‖err A c t‖) (Set.Ioc 1 T) := by
    exact (((err_local A c).norm.integrableOn_compact_subset (fun t ht => zero_le_one.trans ht.1) isCompact_Icc)).mono_set Set.Ioc_subset_Icc_self
  have hlim : Tendsto (fun h : ℝ => h*C) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq,zero_mul] using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.mul_const C) : Tendsto _ (𝓝[>] (0:ℝ)) _)
  filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2)),eventually_mem_nhdsWithin] with h hC hh
  change 0<h at hh
  let f := fun t : ℝ => (t:ℂ)^(-(z+(h:ℂ))-1)*err A c t
  have hf := mellin_int hg (s:=z+h) (by simp only [add_re,ofReal_re]; linarith)
  change IntegrableOn f (Set.Ioi 0) at hf
  have hnf (t : ℝ) (ht : 0<t) : ‖f t‖ = t^(-z.re-h-1)*‖err A c t‖ := by
    simp only [f,norm_mul,norm_cpow_eq_rpow_re_of_pos ht,sub_re,neg_re,add_re,ofReal_re,one_re]
    congr 2; ring
  have hcut : IntegrableOn f (Set.Ioc 1 T) := hf.mono_set (fun t ht => zero_lt_one.trans ht.1)
  have htail : IntegrableOn f (Set.Ioi T) := hf.mono_set (fun t ht => (zero_lt_one.trans_le hT1).trans ht)
  have hshort : (∫ t in Set.Ioc 1 T, ‖f t‖) ≤ C := by
    refine setIntegral_mono_on hcut.norm hCint measurableSet_Ioc fun t ht => ?_
    rw [hnf t (zero_lt_one.trans ht.1)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by linarith))
  have hmajor := integrableOn_Ioi_rpow_of_lt (by linarith : -h-1 < -1) zero_lt_one
  have hlong : (∫ t in Set.Ioi T, ‖f t‖) ≤ ε/2 * (∫ t : ℝ in Set.Ioi 1, t^(-h-1)) := by
    calc
      _ ≤ ∫ t : ℝ in Set.Ioi T, (ε/2)*t^(-h-1) := by
        apply setIntegral_mono_on htail.norm ((hmajor.mono_set (Set.Ioi_subset_Ioi hT1)).const_mul _) measurableSet_Ioi
        intro t ht
        have ht1 : 1 ≤ t := hT1.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        rw [hnf t ht0]
        have hv := hT t ((le_max_left _ _).trans ht.le)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)] at hv
        calc
          _ ≤ t^(-z.re-h-1)*((ε/2)*t^(1/4:ℝ)) := mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg ht0.le _)
          _ = ε/2 * t^((-z.re-h-1)+(1/4:ℝ)) := by rw [Real.rpow_add ht0]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by positivity)
      _ ≤ _ := by
        rw [integral_const_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply setIntegral_mono_set hmajor _ (Set.Ioi_subset_Ioi hT1).eventuallyLE
        exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  have hint : h*(∫ t : ℝ in Set.Ioi 1, t^(-h-1))=1 := by
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,Real.one_rpow]
    rw [show -h-1+1 = -h by ring]
    field_simp [hh.ne']
  rw [dist_zero_right,norm_mul,Complex.norm_real,Real.norm_of_nonneg hh.le,mellin_eq]
  change h * ‖∫ t in Set.Ioi 1, f t‖ < ε
  have hs : ‖∫ t in Set.Ioi 1, f t‖ ≤ C+ε/2*(∫ t : ℝ in Set.Ioi 1, t^(-h-1)) := by
    apply (norm_integral_le_integral_norm _).trans
    conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi hT1,setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hcut.norm htail.norm]
    exact add_le_add hshort hlong
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hh.le
    _ = h*C+ε/2 := by rw [mul_add,mul_left_comm h (ε/2), hint,mul_one]
    _ < _ := by linarith

private lemma ne_one_im {s : ℂ} (hi : s.im ≠ 0) : s ≠ 1 := by rintro rfl; exact hi one_im
private lemma twice_ne_one {s : ℂ} (hi : s.im ≠ 0) : 2*s ≠ 1 := by
  apply ne_one_im
  simpa [two_mul] using (show s.im + s.im ≠ 0 by intro h; exact hi (by linarith))

private lemma result (A : ℕ → ℕ) (c : ℝ) (z : ℂ) (hz : 1/4 ≤ z.re) (hi : z.im ≠ 0)
    (hzero : riemannZeta (2*z)=0)
    (hid : ∀ s : ℂ, 1<s.re → LSeries (fun n : ℕ => (A n : ℂ)-A (n-1)) s * riemannZeta (2*s)=riemannZeta s)
    (hsmall : (fun n : ℕ => |(A n:ℝ)-c*n|) =o[atTop] fun n : ℕ => (n:ℝ)^(1/4:ℝ)) :
    riemannZeta z=0 := by
  have hg := error_small A c hsmall
  let F := fun s : ℂ => (s*mellin (err A c) (-s)+(c:ℂ)*riemannZeta s)*riemannZeta (2*s)
  let D := {s : ℂ | 1/4 < s.re ∧ s.im ≠ 0}
  have hD : IsOpen D := (isOpen_lt continuous_const continuous_re).inter (isOpen_ne.preimage continuous_im)
  have hf : DifferentiableOn ℂ F D := by
    intro s hs
    have h1 := differentiableAt_riemannZeta (ne_one_im hs.2)
    have h2 := (differentiableAt_riemannZeta (twice_ne_one hs.2)).comp s (show DifferentiableAt ℂ (fun w : ℂ => 2*w) s by fun_prop)
    exact (((differentiableAt_id.mul (mellin_diff hg hs.1)).add (h1.const_mul (c:ℂ))).mul h2).differentiableWithinAt
  have hζ : DifferentiableOn ℂ riemannZeta D := fun s hs => (differentiableAt_riemannZeta (ne_one_im hs.2)).differentiableWithinAt
  let path := fun x : ℝ => z+(x:ℂ)
  have hx (x : ℝ) (h : 0<x) : path x ∈ D := by
    change 1/4 < (z+(x:ℂ)).re ∧ (z+(x:ℂ)).im ≠ 0
    simpa only [add_re,add_im,ofReal_re,ofReal_im,add_zero] using And.intro (by linarith : 1/4 < z.re+x) hi
  have hap (x : ℝ) : AnalyticAt ℝ path x := analyticAt_const.add (ofRealCLM.analyticAt x)
  have cont : EqOn (F ∘ path) (riemannZeta ∘ path) (Set.Ioi 0) := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜:=ℝ) (z₀ := (2:ℝ))
      (fun x h => (hf.analyticAt (hD.mem_nhds (hx x h))).restrictScalars.comp (hap x))
      (fun x h => (hζ.analyticAt (hD.mem_nhds (hx x h))).restrictScalars.comp (hap x))
      isPreconnected_Ioi (by norm_num : (2:ℝ) ∈ Set.Ioi 0)
    filter_upwards [lt_mem_nhds (by norm_num : (1:ℝ)<2)] with x hx'
    have hs : 1 < (path x).re := by change 1<z.re+x; linarith
    exact right_side A c hs hg (hid _ hs)
  let g := fun v : ℂ => riemannZeta (2*(z+v))
  have hg0 : g 0=0 := by simpa [g] using hzero
  have gd : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.comp (g := riemannZeta)
    · exact differentiableAt_riemannZeta (by simpa using twice_ne_one hi)
    · fun_prop
  have hcast : Tendsto (fun h : ℝ => (h:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_ofReal.continuousAt (x := (0:ℝ))).continuousWithinAt.tendsto (s:=Set.Ioi 0)
  have hdlim := (continuousAt_dslope_same.mpr gd).tendsto.comp hcast
  have hpath : Tendsto path (𝓝[>] 0) (𝓝 z) := by simpa [path] using hcast.const_add z
  have hzlim := (differentiableAt_riemannZeta (ne_one_im hi)).continuousAt.tendsto.comp hpath
  have hglim := gd.continuousAt.tendsto.comp hcast
  have hb := boundary hz hg
  have hproduct := ((hpath.mul hb).mul hdlim).add ((hzlim.const_mul (c:ℂ)).mul hglim)
  simp only [mul_zero,zero_mul,hg0,add_zero] at hproduct
  have hz' : Tendsto (riemannZeta ∘ path) (𝓝[>] 0) (𝓝 0) := by
    apply hproduct.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have he := cont hh
    change (path h*mellin (err A c) (-(path h))+(c:ℂ)*riemannZeta (path h))*g h=riemannZeta (path h) at he
    have hds : (h:ℂ)*dslope g 0 (h:ℂ)=g h := by simpa [hg0] using sub_smul_dslope g 0 (h:ℂ)
    change (path h*((h:ℂ)*mellin (err A c) (-(path h))))*dslope g 0 h+((c:ℂ)*riemannZeta (path h))*g h=riemannZeta (path h)
    apply Eq.trans _ he
    linear_combination (path h*mellin (err A c) (-(path h)))*hds
  exact tendsto_nhds_unique hzlim hz'

end
end Analytic969

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H3 := Analytic969.result
