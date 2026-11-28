import OMAStatements.S_mo_197896
import Mathlib

open MeasureTheory Set Filter
open scoped Topology Interval

namespace OMA.P197896

noncomputable def cc (k : ℕ) : ℝ := ((k:ℝ)+1)*((k:ℝ)+2)

noncomputable def Q (k : ℕ) (u : ℝ) : ℝ := if k = 0 then Real.log u else -((u^k)⁻¹)/k

noncomputable def al (k : ℕ) (u : ℝ) : ℝ :=
  cc k * u^(2*k+1) * ((1-u)*(u+((k:ℝ)+2)*(1-u)))

noncomputable def be (k : ℕ) (u : ℝ) : ℝ :=
  cc k * (if k = 0 then -(u * Real.log u) else (u^(k+1) - u^(2*k+1))/k)

noncomputable def De (k : ℕ) (u : ℝ) : ℝ := al k u - be k u

noncomputable def P (k : ℕ) (u : ℝ) : ℝ := if k = 0 then 3/4 - u + u^2/4 + Real.log u / 2 else
  -1/((k:ℝ)*((k:ℝ)+2)) + ((k:ℝ)+1)/(2*k) * u^k - u^(k+1) + ((k:ℝ)+1)/(2*((k:ℝ)+2)) * u^(k+2)

noncomputable def H (k : ℕ) (u : ℝ) : ℝ := if k = 0 then
  cc k * (u^2*(3/4 - u + u^2/4) + u*(u*Real.log u)/2) else cc k * u^(k+2) * P k u

lemma Q_deriv (k : ℕ) {u : ℝ} (hu : 0 < u) : HasDerivAt (Q k) ((u^(k+1))⁻¹) u := by
  have hu0 := hu.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Q 0 = Real.log := by funext v; simp [Q]
    rw [this]; simpa using Real.hasDerivAt_log hu.ne'
  · have hk0 : k ≠ 0 := by omega
    have : Q k = fun v => -((v^k)⁻¹)/(k:ℝ) := by funext v; simp [Q, hk0]
    rw [this]
    have h : HasDerivAt (fun v => -((v^k)⁻¹)/(k:ℝ)) _ u :=
      (((hasDerivAt_pow k u).inv (pow_ne_zero _ hu.ne')).neg).div_const (k:ℝ)
    refine h.congr_deriv ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

lemma P_deriv (k : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (P k) (((k:ℝ)+1)/2 * u^(k+1) * (1-u)^2 / u^2) u := by
  have hu0 := hu.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : P 0 = fun v => 3/4 - v + v^2/4 + Real.log v / 2 := by funext v; simp [P]
    rw [this]
    have h : HasDerivAt (fun v => 3/4 - v + v^2/4 + Real.log v / 2) _ u :=
      ((((hasDerivAt_const u (3/4:ℝ)).sub (hasDerivAt_id u)).add
      ((hasDerivAt_pow 2 u).div_const 4)).add ((Real.hasDerivAt_log hu.ne').div_const 2))
    refine h.congr_deriv ?_
    simp
    field_simp
    ring
  · have hk0 : k ≠ 0 := by omega
    have : P k = fun v => -1/((k:ℝ)*((k:ℝ)+2)) + ((k:ℝ)+1)/(2*k) * v^k - v^(k+1) +
        ((k:ℝ)+1)/(2*((k:ℝ)+2)) * v^(k+2) := by funext v; simp [P, hk0]
    rw [this]
    have h : HasDerivAt (fun v => -1/((k:ℝ)*((k:ℝ)+2)) + ((k:ℝ)+1)/(2*k) * v^k - v^(k+1) +
        ((k:ℝ)+1)/(2*((k:ℝ)+2)) * v^(k+2)) _ u :=
      (((hasDerivAt_const u (-1/((k:ℝ)*((k:ℝ)+2)))).add
      ((hasDerivAt_pow k u).const_mul (((k:ℝ)+1)/(2*k)))).sub
      (hasDerivAt_pow (k+1) u)).add
      ((hasDerivAt_pow (k+2) u).const_mul (((k:ℝ)+1)/(2*((k:ℝ)+2))))
    refine h.congr_deriv ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.add_succ_sub_one]
    push_cast
    field_simp
    ring

lemma H_deriv (k : ℕ) {u : ℝ} (hu : 0 < u) : HasDerivAt (H k) (De k u) u := by
  have hu0 := hu.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : H 0 = fun v => cc 0 * (v^2*(3/4 - v + v^2/4) + v*(v*Real.log v)/2) := by
      funext v; simp [H]
    rw [this]
    have h : HasDerivAt (fun v => cc 0 * (v^2*(3/4 - v + v^2/4) + v*(v*Real.log v)/2)) _ u :=
      (((hasDerivAt_pow 2 u).mul (((hasDerivAt_const u (3/4:ℝ)).sub
      (hasDerivAt_id u)).add ((hasDerivAt_pow 2 u).div_const 4))).add
      (((hasDerivAt_id u).mul ((hasDerivAt_id u).mul
        (Real.hasDerivAt_log hu.ne'))).div_const 2)).const_mul (cc 0)
    refine h.congr_deriv ?_
    simp [De, al, be]
    field_simp
    ring
  · have hk0 : k ≠ 0 := by omega
    have : H k = fun v => cc k * v^(k+2) * P k v := by funext v; simp [H, hk0]
    rw [this]
    have h : HasDerivAt (fun v => cc k * v^(k+2) * P k v) _ u :=
      ((hasDerivAt_pow (k+2) u).const_mul (cc k)).mul (P_deriv k hu)
    refine h.congr_deriv ?_
    simp only [De, al, be, P, cc, Nat.add_sub_cancel, if_neg hk0]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    push_cast
    field_simp
    ring

lemma H_cont (k : ℕ) : Continuous (H k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : H 0 = fun v => cc 0 * (v^2*(3/4 - v + v^2/4) + v*(v*Real.log v)/2) := by
      funext v; simp [H]
    rw [this]
    exact continuous_const.mul ((by fun_prop : Continuous fun v : ℝ => v^2*(3/4 - v + v^2/4)).add
      ((continuous_id.mul Real.continuous_mul_log).div_const 2))
  · have hk0 : k ≠ 0 := by omega
    have : H k = fun v => cc k * v^(k+2) * P k v := by funext v; simp [H, hk0]
    rw [this]
    simp only [P, if_neg hk0]
    fun_prop

lemma De_cont (k : ℕ) : Continuous (De k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : De 0 = fun v => al 0 v - cc 0 * (-(v * Real.log v)) := by
      funext v; simp [De, be]
    rw [this]
    exact (by unfold al; fun_prop : Continuous (al 0)).sub
      (continuous_const.mul Real.continuous_mul_log.neg)
  · have hk0 : k ≠ 0 := by omega
    have : De k = fun v => al k v - cc k * ((v^(k+1) - v^(2*k+1))/k) := by
      funext v; simp [De, be, hk0]
    rw [this]
    unfold al
    fun_prop

lemma P_one (k : ℕ) : P k 1 = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [P]; norm_num
  · have hk0 : k ≠ 0 := by omega
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    simp only [P, if_neg hk0, one_pow]
    field_simp
    ring

lemma H_one (k : ℕ) : H k 1 = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [H]; norm_num
  · have hk0 : k ≠ 0 := by omega
    simp [H, hk0, P_one]

lemma H_eq (k : ℕ) (u : ℝ) : H k u = cc k * u^(k+2) * P k u := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [H, P]; ring
  · have hk0 : k ≠ 0 := by omega
    simp [H, hk0]

lemma cc_pos (k : ℕ) : 0 < cc k := by unfold cc; positivity

lemma P_neg (k : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : P k u < 0 := by
  have hmono : StrictMonoOn (P k) (Ioc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 1)
    · intro x hx; exact (P_deriv k hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(P_deriv k hx.1).deriv]
      have := hx.1; have := hx.2
      apply div_pos _ (pow_pos hx.1 2)
      apply mul_pos (mul_pos (by positivity) (pow_pos hx.1 _))
      exact pow_pos (by linarith) 2
  have := hmono ⟨hu0, hu1.le⟩ ⟨one_pos, le_rfl⟩ hu1
  rwa [P_one] at this

lemma H_neg (k : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : H k u < 0 := by
  rw [H_eq]
  exact mul_neg_of_pos_of_neg (mul_pos (cc_pos k) (pow_pos hu0 _)) (P_neg k hu0 hu1)

lemma be_eq (k : ℕ) {u : ℝ} (hu : 0 < u) : cc k * u^(2*k+1) * (Q k 1 - Q k u) = be k u := by
  have hu0 := hu.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Q, be]; ring
  · have hk0 : k ≠ 0 := by omega
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    simp only [Q, be, if_neg hk0, one_pow, inv_one]
    field_simp
    ring

lemma De_neg_small (k : ℕ) : ∃ u0 > 0, ∀ u, 0 < u → u < u0 → De k u < 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨Real.exp (-3), Real.exp_pos _, fun u hu hu0 => ?_⟩
    have hlog : Real.log u < -3 := by
      rw [Real.log_lt_iff_lt_exp hu]; exact hu0
    have hu1 : u < 1 := lt_trans hu0 (Real.exp_lt_one_iff.2 (by norm_num))
    have : De 0 u = cc 0 * u * ((1-u)*(u+2*(1-u)) + Real.log u) := by
      simp [De, al, be]; ring
    rw [this]
    apply mul_neg_of_pos_of_neg (mul_pos (cc_pos 0) hu)
    nlinarith
  · have hk0 : k ≠ 0 := by omega
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨1/((k:ℝ)+2)^2, by positivity, fun u hu hu0 => ?_⟩
    have hu1 : u < 1 := by
      calc u < 1/((k:ℝ)+2)^2 := hu0
        _ ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    set A := (1-u)*(u+((k:ℝ)+2)*(1-u)) with hA
    have hA0 : 0 ≤ A := mul_nonneg (by linarith) (by nlinarith)
    have hA1 : A ≤ (k:ℝ)+2 := by
      have h1 : u+((k:ℝ)+2)*(1-u) ≤ (k:ℝ)+2 := by nlinarith
      calc A ≤ 1 * ((k:ℝ)+2) := by
            apply mul_le_mul (by linarith) h1 (by nlinarith) (by norm_num)
        _ = _ := one_mul _
    have hpow : u^k ≤ u := pow_le_of_le_one hu.le hu1.le hk0
    have : De k u = cc k * u^(k+1) * (u^k * (A + 1/k) - 1/k) := by
      simp only [De, al, be, if_neg hk0, hA]; ring
    rw [this]
    apply mul_neg_of_pos_of_neg (mul_pos (cc_pos k) (pow_pos hu _))
    have hkpos : (0:ℝ) < k := by linarith
    have h2 : u^k * (A + 1/k) ≤ u * ((k:ℝ)+2+1/k) := by
      apply mul_le_mul hpow (by linarith) (by positivity) hu.le
    have h3 : u * ((k:ℝ)+2+1/k) < 1/k := by
      have e : u * ((k:ℝ)+2+1/k) = (u * ((k:ℝ)+1)^2) / k := by field_simp; ring
      rw [e, div_lt_div_iff_of_pos_right hkpos]
      have : u * ((k:ℝ)+2)^2 < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hu0
      nlinarith
    linarith

end OMA.P197896

namespace OMA.P197896
open OMA.S_mo_197896

noncomputable def psi (k : ℕ) (F f : ℝ → ℝ) (x : ℝ) : ℝ := f x * (F x ^ (k+1))⁻¹
noncomputable def phi (k : ℕ) (F f : ℝ → ℝ) (s : ℝ) : ℝ := s * F s ^ (2*k+1) * f s

section
variable {k : ℕ} {T : ℝ} {F f : ℝ → ℝ}

lemma F_strict (hD : Distribution T F f) : StrictMonoOn F (Icc 0 T) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 T) hD.cdf_cont.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hD.hasDeriv x hx).deriv]
  exact hD.density_pos x (Ioo_subset_Icc_self hx)

lemma F_pos (hD : Distribution T F f) {x : ℝ} (hx : x ∈ Ioc 0 T) : 0 < F x := by
  have := F_strict hD ⟨le_rfl, (hx.1.trans_le hx.2).le⟩ ⟨hx.1.le, hx.2⟩ hx.1
  rwa [hD.left] at this

lemma F_lt_one (hD : Distribution T F f) {x : ℝ} (hx : x ∈ Ico 0 T) : F x < 1 := by
  have := F_strict hD ⟨hx.1, hx.2.le⟩ ⟨hx.1.trans hx.2.le, le_rfl⟩ hx.2
  rwa [hD.right] at this

lemma B_pointwise (t x : ℝ) :
    maxDensity k F f x * (∫ s in 0..min t x, givenCDF k F x s * s * givenDensity k F f x s) =
      cc k * psi k F f x * ∫ s in 0..min t x, phi k F f s := by
  have h1 : ∀ s, givenCDF k F x s * s * givenDensity k F f x s =
      (((k:ℝ)+1) * ((F x ^ (k+1))⁻¹)^2) * phi k F f s := by
    intro s; simp only [givenCDF, givenDensity, phi, div_eq_mul_inv]; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul]
  simp only [maxDensity, psi, cc]
  by_cases ha : F x ^ (k+1) = 0
  · simp [ha]
  · field_simp

lemma A_eq (t : ℝ) : ∫ s in 0..t, secondCDF k F s * s * secondDensity k F f s =
    ∫ s in 0..t, s * f s * al k (F s) := by
  congr 1; funext s; simp only [secondCDF, secondDensity, al, cc]; ring

lemma L_eq (hD : Distribution T F f) {s : ℝ} (hs : s ∈ Ioc 0 T) :
    ∫ x in s..T, psi k F f x = Q k 1 - Q k (F s) := by
  have hFpos : ∀ x ∈ Icc s T, 0 < F x := fun x hx => F_pos hD ⟨hs.1.trans_le hx.1, hx.2⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2 (f := fun x => Q k (F x))]
  · rw [hD.right]
  · intro x hx
    exact ((Q_deriv k (hFpos x hx)).continuousAt.comp
      (hD.cdf_cont.continuousAt)).continuousWithinAt
  · intro x hx
    have := (Q_deriv k (hFpos x (Ioo_subset_Icc_self hx))).comp x
      (hD.hasDeriv x ⟨hs.1.trans hx.1, hx.2⟩)
    exact this.congr_deriv (by simp only [psi]; ring)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.2]
    exact (hD.density_cont.mono (Icc_subset_Icc hs.1.le le_rfl)).mul
      ((hD.cdf_cont.continuousOn.pow _).inv₀ (fun x hx => pow_ne_zero _ (hFpos x hx).ne'))

lemma B_eq (hT : 0 < T) (hD : Distribution T F f) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    ∫ x in 0..T, maxDensity k F f x *
      (∫ s in 0..min t x, givenCDF k F x s * s * givenDensity k F f x s) =
    ∫ s in 0..t, s * f s * be k (F s) := by
  simp_rw [B_pointwise]
  rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le ht0.le]
  set g : ℝ → ℝ → ℝ := fun x s => if s ≤ min t x then psi k F f x * phi k F f s else 0 with hg
  have step1 : ∫ x in Ioc 0 T, cc k * psi k F f x * ∫ s in 0..min t x, phi k F f s =
      cc k * ∫ x in Ioc 0 T, ∫ s in Ioc 0 T, g x s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [mul_assoc]; congr 1
    have hm0 : 0 ≤ min t x := le_min ht0.le hx.1.le
    have hmT : min t x ≤ T := (min_le_left _ _).trans htT
    rw [intervalIntegral.integral_of_le hm0, ← integral_const_mul]
    have : Ioc 0 (min t x) = Ioc 0 T ∩ Iic (min t x) := by
      rw [Ioc_inter_Iic, min_eq_right hmT]
    rw [this, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    simp only [hg, indicator, mem_Iic]
  have hint : Integrable (Function.uncurry g) ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))) := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hD.density_cont
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
    refine Integrable.of_bound ?_ (M*M*T) ?_
    · have hpsi : Measurable (psi k F f) :=
        hD.density_meas.mul ((hD.cdf_cont.measurable.pow_const _).inv)
      have hphi : Measurable (phi k F f) :=
        (measurable_id.mul (hD.cdf_cont.measurable.pow_const _)).mul hD.density_meas
      apply Measurable.aestronglyMeasurable
      change Measurable (fun p : ℝ × ℝ =>
        if p.2 ≤ min t p.1 then psi k F f p.1 * phi k F f p.2 else 0)
      exact Measurable.ite (measurableSet_le measurable_snd (measurable_const.min measurable_fst))
        ((hpsi.comp measurable_fst).mul (hphi.comp measurable_snd)) measurable_const
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      rcases p with ⟨x, s⟩
      obtain ⟨⟨hx0, hxT⟩, ⟨hs0, hsT⟩⟩ := hp
      simp only [Function.uncurry_apply_pair, hg]
      split_ifs with h
      · have hFx := F_pos hD ⟨hx0, hxT⟩
        have hFs := F_pos hD ⟨hs0, hsT⟩
        have hFsx : F s ≤ F x := hD.cdf_mono (h.trans (min_le_right _ _))
        have hFx1 := hD.cdf_le_one x
        have key : F s^(2*k+1) * (F x^(k+1))⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (pow_pos hFx _)]
          calc F s^(2*k+1) ≤ F x^(2*k+1) := pow_le_pow_left₀ hFs.le hFsx _
            _ ≤ F x^(k+1) := pow_le_pow_of_le_one hFx.le hFx1 (by omega)
        have hfx : |f x| ≤ M := by simpa using hM x ⟨hx0.le, hxT⟩
        have hfs : |f s| ≤ M := by simpa using hM s ⟨hs0.le, hsT⟩
        rw [Real.norm_eq_abs, show psi k F f x * phi k F f s =
          (f x * f s) * s * (F s^(2*k+1) * (F x^(k+1))⁻¹) by simp only [psi, phi]; ring]
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hs0,
          abs_of_nonneg (by positivity : 0 ≤ F s^(2*k+1) * (F x^(k+1))⁻¹)]
        have h1 : |f x| * |f s| ≤ M*M := mul_le_mul hfx hfs (abs_nonneg _) hM0
        have h2 : |f x| * |f s| * s ≤ M*M*T := mul_le_mul h1 hsT hs0.le (by positivity)
        calc |f x| * |f s| * s * (F s^(2*k+1) * (F x^(k+1))⁻¹) ≤ M*M*T*1 :=
              mul_le_mul h2 key (by positivity) (by positivity)
          _ = M*M*T := mul_one _
      · simp only [norm_zero]; positivity
  rw [step1, integral_integral_swap hint]
  have step2 : ∀ s ∈ Ioc 0 T, ∫ x in Ioc 0 T, g x s =
      (Iic t).indicator (fun s => phi k F f s * ∫ x in s..T, psi k F f x) s := by
    intro s hs
    by_cases hst : s ≤ t
    · have : ∀ x, g x s = (Ici s).indicator (fun x => psi k F f x * phi k F f s) x := by
        intro x
        simp only [hg, indicator, mem_Ici, le_min_iff, hst, true_and]
      simp_rw [this]
      rw [setIntegral_indicator measurableSet_Ici]
      have e : Ioc 0 T ∩ Ici s = Icc s T := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩; exact ⟨⟨hs.1.trans_le h3, h2⟩, h3⟩
      rw [e, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
        intervalIntegral.integral_mul_const, indicator_of_mem (show s ∈ Iic t from hst)]
      ring
    · have : ∀ x, g x s = 0 := by
        intro x
        have : ¬ s ≤ min t x := fun h => hst (h.trans (min_le_left _ _))
        simp only [hg, this, if_false]
      simp_rw [this]
      rw [integral_zero, indicator_of_notMem (show s ∉ Iic t from hst)]
  rw [setIntegral_congr_fun measurableSet_Ioc step2, setIntegral_indicator measurableSet_Iic,
    Ioc_inter_Iic, min_eq_right htT, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  have hs' : s ∈ Ioc 0 T := ⟨hs.1, hs.2.trans htT⟩
  rw [L_eq hD hs', ← be_eq k (F_pos hD hs')]
  simp only [phi]
  ring

end

end OMA.P197896

namespace OMA.P197896
open OMA.S_mo_197896

lemma al_cont (k : ℕ) : Continuous (al k) := by unfold al; fun_prop

lemma be_cont (k : ℕ) : Continuous (be k) := by
  have : be k = fun u => al k u - De k u := by funext u; simp [De]
  rw [this]; exact (al_cont k).sub (De_cont k)

lemma cont_of {T : ℝ} {F f : ℝ → ℝ} (hD : Distribution T F f) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun s => s * f s * g (F s)) (Icc 0 T) :=
  (continuousOn_id.mul hD.density_cont).mul (hg.comp_continuousOn hD.cdf_cont.continuousOn)

lemma intg_of {T : ℝ} {F f : ℝ → ℝ} (hD : Distribution T F f) {g : ℝ → ℝ} (hg : Continuous g)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun s => s * f s * g (F s)) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht0]
  exact (cont_of hD hg).mono (Icc_subset_Icc le_rfl htT)

lemma gap_eq {k : ℕ} {T : ℝ} {F f : ℝ → ℝ} (hT : 0 < T) (hD : Distribution T F f) {t : ℝ}
    (ht0 : 0 < t) (htT : t ≤ T) :
    gap k F f T t = ∫ s in 0..t, s * f s * De k (F s) := by
  unfold gap
  rw [A_eq, B_eq hT hD ht0 htT, ← intervalIntegral.integral_sub (intg_of hD (al_cont k) ht0.le htT)
    (intg_of hD (be_cont k) ht0.le htT)]
  congr 1; funext s; simp only [De]; ring

lemma main_proof : ∀ (k : ℕ) (T : ℝ) (F f : ℝ → ℝ), 0 < T → Distribution T F f →
    ∃ t ∈ Ioo 0 T, gap k F f T t = 0 := by
  intro k T F f hT hD
  obtain ⟨u0, hu0, hneg⟩ := De_neg_small k
  have h1 : ∀ᶠ x in 𝓝 (0:ℝ), F x < u0 :=
    (hD.cdf_cont.tendsto 0).eventually (gt_mem_nhds (by rw [hD.left]; exact hu0))
  have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), (F x < u0 ∧ x < T) ∧ x ∈ Ioi 0 :=
    ((h1.filter_mono nhdsWithin_le_nhds).and
      (eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hT))).and self_mem_nhdsWithin
  obtain ⟨t1, ⟨hFt1, ht1T⟩, ht1pos⟩ := hev.exists
  have ht1pos' : (0:ℝ) < t1 := ht1pos
  have gap_t1 : gap k F f T t1 < 0 := by
    rw [gap_eq hT hD ht1pos' ht1T.le]
    have := intervalIntegral.intervalIntegral_pos_of_pos_on (f := fun s => -(s * f s * De k (F s)))
      (intg_of hD (De_cont k) ht1pos'.le ht1T.le).neg (fun s hs => ?_) ht1pos'
    · rw [intervalIntegral.integral_neg] at this; linarith
    · have hFs : 0 < F s := F_pos hD ⟨hs.1, (hs.2.trans ht1T).le⟩
      have hFst : F s < F t1 :=
        F_strict hD ⟨hs.1.le, (hs.2.trans ht1T).le⟩ ⟨ht1pos'.le, ht1T.le⟩ hs.2
      have hDe : De k (F s) < 0 := hneg _ hFs (hFst.trans hFt1)
      have hfs : 0 < f s := hD.density_pos s ⟨hs.1.le, (hs.2.trans ht1T).le⟩
      exact neg_pos.2 (mul_neg_of_pos_of_neg (mul_pos hs.1 hfs) hDe)
  have gap_T : 0 < gap k F f T T := by
    rw [gap_eq hT hD hT le_rfl]
    have hHc : Continuous fun s => H k (F s) := (H_cont k).comp hD.cdf_cont
    have hHint : IntervalIntegrable (fun s => H k (F s)) volume 0 T :=
      hHc.continuousOn.intervalIntegrable
    have hIint := intg_of hD (De_cont k) hT.le le_rfl
    have hFTC : ∫ s in 0..T, (H k (F s) + s * f s * De k (F s)) = 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
        (f := fun s => s * H k (F s))]
      · simp [hD.right, H_one]
      · exact (continuous_id.mul hHc).continuousOn
      · intro s hs
        have hF := F_pos hD ⟨hs.1, hs.2.le⟩
        have h := (hasDerivAt_id s).mul ((H_deriv k hF).comp s (hD.hasDeriv s hs))
        exact h.congr_deriv (by simp only [id, Function.comp]; ring)
      · exact hHint.add hIint
    rw [intervalIntegral.integral_add hHint hIint] at hFTC
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (f := fun s => -H k (F s)) hHint.neg
      (fun s hs => neg_pos.2 (H_neg k (F_pos hD ⟨hs.1, hs.2.le⟩)
        (F_lt_one hD ⟨hs.1.le, hs.2⟩))) hT
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  have hcont : ContinuousOn (gap k F f T) (Icc t1 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun s => s * f s * De k (F s)) (a := 0) (b := T)
      (by rw [uIcc_of_le hT.le]; exact (cont_of hD (De_cont k)).integrableOn_Icc)
    rw [uIcc_of_le hT.le] at h
    exact (h.mono (Icc_subset_Icc ht1pos'.le le_rfl)).congr
      (fun t ht => gap_eq hT hD (ht1pos'.trans_le ht.1) ht.2)
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc ht1T.le hcont ⟨gap_t1.le, gap_T.le⟩
  refine ⟨t, ⟨ht1pos'.trans_le ht.1, lt_of_le_of_ne ht.2 ?_⟩, hgt⟩
  rintro rfl; linarith

end OMA.P197896

theorem OMA.solution : type_of% @OMA.S_mo_197896.main := OMA.P197896.main_proof
