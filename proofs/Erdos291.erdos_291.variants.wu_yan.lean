import FormalConjectures.ErdosProblems.«291»
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
Wu and Yan’s conditional upper density statement.

The top leading digit in base `p` forces cancellation modulo `p` in the harmonic numerator.
Rational independence lets the logarithmic phases of finitely many primes recur simultaneously.
Divergence of the prime reciprocal series gives enough logarithmic intervals to cover a fixed
fraction of every sufficiently large recurrent initial segment.
-/

open Finset Filter
open scoped BigOperators Classical Topology

noncomputable section

namespace HarmonicDigits

private lemma dvd_L {n t : ℕ} (ht₀ : 1 ≤ t) (ht : t ≤ n) : t ∣ Erdos291.L n := by
  unfold Erdos291.L
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨ht₀, ht⟩)

private lemma sum_inverse_eq_zero {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (∑ m ∈ Icc 1 (p-1), ((m : ZMod p)⁻¹)) = 0 := by
  have he : (∑ m ∈ Icc 1 (p-1), ((m : ZMod p)⁻¹)) =
      ∑ m ∈ Icc 1 (p-1), -((m : ZMod p)⁻¹) := by
    refine Finset.sum_bij (fun m _ => p-m) ?_ ?_ ?_ ?_
    · intro m hm
      obtain ⟨hm₁, hm₂⟩ := mem_Icc.mp hm
      exact mem_Icc.mpr (by omega)
    · intro a ha b hb h
      have := (mem_Icc.mp ha).2
      have := (mem_Icc.mp hb).2
      omega
    · intro b hb
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hb
      exact ⟨p-b, mem_Icc.mpr (by omega), by omega⟩
    · intro m hm
      have hm' : m ≤ p := ((mem_Icc.mp hm).2).trans (Nat.sub_le _ _)
      rw [Nat.cast_sub hm', ZMod.natCast_self, zero_sub, inv_neg, neg_neg]
  rw [sum_neg_distrib] at he
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp (show ((2:ℕ):ZMod p) = 0 from h)
    exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) hd)
  apply mul_left_cancel₀ h₂
  linear_combination he

/-- A top leading digit in an odd prime base forces a common prime divisor. -/
private lemma good_digit {p n e : ℕ} (hp : p.Prime) (hp₂ : 2 < p)
    (he : 1 ≤ e) (hn₁ : (p-1)*p^e ≤ n) (hn₂ : n < p*p^e) :
    1 < (Erdos291.a n).gcd (Erdos291.L n) := by
  let : Fact p.Prime := ⟨hp⟩
  let D := p^e
  let C := Erdos291.L n
  have hD : 0 < D := pow_pos hp.pos _
  have hDn : D ≤ n := (show D ≤ (p-1)*D from by
    simpa using Nat.mul_le_mul_right D (show 1 ≤ p-1 by omega)).trans hn₁
  have hpD : p ∣ D := dvd_pow_self p (by omega)
  have hDC : D ∣ C := dvd_L (by omega) hDn
  have hC (k : ℕ) (hk : k ∈ Icc 1 n) : k ∣ C := dvd_L (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
  have hdiv : n / D = p-1 := by
    apply le_antisymm
    · have H := (Nat.div_lt_iff_lt_mul hD).mpr (show n < p*D from hn₂)
      omega
    · exact (Nat.le_div_iff_mul_le hD).mpr hn₁
  have hzero (k : ℕ) (hk : k ∈ Icc 1 n) (h : ¬ D ∣ k) : ((C / k : ℕ) : ZMod p) = 0 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    by_contra! hc
    have hcop : D.Coprime (C / k) :=
      ((hp.coprime_iff_not_dvd.mpr hc).pow_left e)
    have hmul : D ∣ k * (C / k) := by rw [Nat.mul_div_cancel' (hC k hk)]; exact hDC
    exact h (hcop.dvd_of_dvd_mul_right hmul)
  have hnonzero (m : ℕ) (hm : m ∈ Icc 1 (p-1)) :
      ((C/(m*D) : ℕ) : ZMod p) = ((C/D : ℕ) : ZMod p) * (m : ZMod p)⁻¹ := by
    obtain ⟨hm₁,hm₂⟩ := mem_Icc.mp hm
    have hmn : m*D ≤ n := (Nat.mul_le_mul_right D hm₂).trans hn₁
    have hmd : m*D ∣ C := dvd_L (Nat.mul_pos (by omega) hD) hmn
    have hmZ : (m : ZMod p) ≠ 0 := by
      intro H
      exact (show ¬ p ∣ m from Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
        ((ZMod.natCast_eq_zero_iff _ _).mp H)
    apply mul_right_cancel₀ hmZ
    rw [mul_assoc, inv_mul_cancel₀ hmZ, mul_one]
    rw [← Nat.cast_mul]
    congr 1
    have H : (m * D) * (C/(m*D)) = C := Nat.mul_div_cancel' hmd
    have H' : D * (C/D) = C := Nat.mul_div_cancel' hDC
    apply Nat.eq_of_mul_eq_mul_left hD
    calc
      _ = (m*D)*(C/(m*D)) := by ring
      _ = C := H
      _ = _ := H'.symm
  have hsum : ((Erdos291.a n : ℕ) : ZMod p) = 0 := by
    classical
    simp only [Erdos291.a, Nat.cast_sum]
    change (∑ k ∈ Icc 1 n, ((C/k : ℕ) : ZMod p)) = 0
    rw [← sum_filter_add_sum_filter_not (Icc 1 n) (fun k => D ∣ k)]
    rw [sum_eq_zero (fun k hk => hzero k (mem_filter.mp hk).1 (mem_filter.mp hk).2), add_zero]
    have ssum : (∑ k ∈ (Icc 1 n).filter (fun k => D ∣ k), ((C/k : ℕ) : ZMod p)) =
        ∑ m ∈ Icc 1 (p-1), ((C/(m*D) : ℕ) : ZMod p) := by
      symm
      refine Finset.sum_bij (fun m _ => m*D) ?_ ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm₁,hm₂⟩ := mem_Icc.mp hm
        exact mem_filter.mpr ⟨mem_Icc.mpr
          ⟨Nat.mul_pos (by omega) hD, (Nat.mul_le_mul_right D hm₂).trans hn₁⟩,
          dvd_mul_left _ _⟩
      · intro a ha b hb h
        exact Nat.eq_of_mul_eq_mul_right hD h
      · intro k hk
        obtain ⟨hm, hd⟩ := mem_filter.mp hk
        obtain ⟨h₁,h₂⟩ := mem_Icc.mp hm
        obtain ⟨m,rfl⟩ := hd
        refine ⟨m, mem_Icc.mpr ⟨?_, ?_⟩, mul_comm _ _⟩
        · by_contra! h
          have : m = 0 := by omega
          simp [this] at h₁
        · rw [← hdiv, Nat.le_div_iff_mul_le hD, mul_comm]
          exact h₂
      · intros
        rfl
    rw [ssum]
    rw [sum_congr rfl hnonzero, ← mul_sum, sum_inverse_eq_zero hp₂, mul_zero]
  have ha : p ∣ Erdos291.a n := (ZMod.natCast_eq_zero_iff _ _).mp hsum
  exact lt_of_lt_of_le (by omega : 1 < p) (Nat.le_of_dvd
    (Nat.gcd_pos_of_pos_right _ (by
       unfold Erdos291.L
       apply Nat.pos_of_ne_zero
       apply Finset.lcm_ne_zero_iff.mpr
       intro k hk
       exact Nat.ne_of_gt (mem_Icc.mp hk).1))
    (Nat.dvd_gcd ha (hpD.trans hDC)))

end HarmonicDigits

open Set Filter Finset MeasureTheory UnitAddTorus
open scoped Topology BigOperators Classical

noncomputable section

namespace HarmonicFlow

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

private def flow {ι : Type*} (α : ι → ℝ) (t : ℝ) : UnitAddTorus ι :=
  fun i => ((t * α i : ℝ) : UnitAddCircle)

private lemma flow_add {ι : Type*} (α : ι → ℝ) (s t : ℝ) :
    flow α (s+t) = flow α s + flow α t := by
  ext i
  change (((s+t) * α i : ℝ) : UnitAddCircle) = ↑(s * α i) + ↑(t * α i)
  rw [add_mul, QuotientAddGroup.mk_add]

private lemma frequency_nontrivial {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (hα : LinearIndependent ℚ α) (n : ι → ℤ) (hn : n ≠ 0) :
    ∃ t : ℝ, mFourier n (flow α t) ≠ 1 := by
  have hfreq : (∑ i : ι, (n i : ℝ) * α i) ≠ 0 := by
    intro h
    have hQ : ∑ i : ι, (n i : ℚ) • α i = 0 := by
      simpa [Rat.smul_def] using h
    have hZ := (linearIndependent_iff'.mp hα) univ (fun i => (n i : ℚ)) hQ
    apply hn
    ext i
    exact_mod_cast hZ i (mem_univ i)
  let t := 1 / (2 * (∑ i : ι, (n i : ℝ) * α i))
  refine ⟨t, ?_⟩
  have he : (∑ i : ι, 2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) *
      ((t * α i : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I := by
    calc
      _ = (Real.pi : ℂ) * Complex.I * (2*(t : ℂ) *
          ∑ i : ι, (n i : ℂ) * (α i : ℂ)) := by
        simp only [mul_sum, Complex.ofReal_mul]
        apply sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        have ht' : 2*t*(∑ i : ι, (n i : ℝ)*α i) = 1 := by
          dsimp [t]
          field_simp
        have htC := congrArg (fun x : ℝ => (x : ℂ)) ht'
        push_cast at htC
        rw [htC, mul_one]
  simp only [flow, mFourier, ContinuousMap.coe_mk, fourier_coe_apply, Complex.ofReal_one,
    div_one, ← Complex.exp_sum, he, Complex.exp_pi_mul_I]
  norm_num

private def tailSet {ι : Type*} (α : ι → ℝ) (R : ℝ) : Set (UnitAddTorus ι) :=
  closure { z | ∃ t ≥ R, flow α t = z }

private def limitSet {ι : Type*} (α : ι → ℝ) : Set (UnitAddTorus ι) :=
  ⋂ R : ℝ, tailSet α R

private lemma limitSet_nonempty {ι : Type*} [Fintype ι] (α : ι → ℝ) :
    (limitSet α).Nonempty := by
  unfold limitSet
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro R S
    refine ⟨max R S, ?_, ?_⟩
    · apply closure_mono
      rintro x ⟨t,ht,rfl⟩
      exact ⟨t, (le_max_left _ _).trans ht, rfl⟩
    · apply closure_mono
      rintro x ⟨t,ht,rfl⟩
      exact ⟨t, (le_max_right _ _).trans ht, rfl⟩
  · intro R
    exact ⟨flow α R, subset_closure ⟨R,le_rfl,rfl⟩⟩
  · intro R
    exact isClosed_closure.isCompact
  · intro R
    exact isClosed_closure

private lemma limitSet_shift {ι : Type*} (α : ι → ℝ) (t : ℝ) :
    (fun x => x + flow α t) '' limitSet α = limitSet α := by
  have hmaps (s : ℝ) : MapsTo (fun x => x + flow α s) (limitSet α) (limitSet α) := by
    intro z hz
    apply mem_iInter.mpr
    intro R
    have hM : MapsTo (fun x => x + flow α s)
        {x | ∃ u ≥ R-s, flow α u = x} {x | ∃ u ≥ R, flow α u = x} := by
      rintro x ⟨u, hu,rfl⟩
      exact ⟨u+s, by linarith, flow_add α u s⟩
    exact hM.closure (continuous_id.add continuous_const) (mem_iInter.mp hz (R-s))
  apply subset_antisymm (hmaps t).image_subset
  intro x hx
  use x + flow α (-t), hmaps (-t) hx
  change (x + flow α (-t)) + flow α t = x
  rw [add_assoc, ← flow_add α, neg_add_cancel]
  have h0 : flow α 0 = 0 := by
    ext i
    change (((0:ℝ)*α i : ℝ) : UnitAddCircle) = 0
    simp
  rw [h0, add_zero]

private lemma invariant_constant {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (hα : LinearIndependent ℚ α) (g : C(UnitAddTorus ι, ℂ))
    (hg : ∀ z t, g (z + flow α t) = g z) :
    ∀ z, g z = mFourierCoeff g 0 := by
  have hzero (n : ι → ℤ) (hn : n ≠ 0) : mFourierCoeff g n = 0 := by
    obtain ⟨t, ht⟩ := frequency_nontrivial α hα (-n) (neg_ne_zero.mpr hn)
    unfold mFourierCoeff
    have H := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus ι)))
      (fun x => mFourier (-n) x • g x) (flow α t)
    simp only [hg, smul_eq_mul] at H
    have hmul (x : UnitAddTorus ι) : mFourier (-n) (x + flow α t) =
        mFourier (-n) (flow α t) * mFourier (-n) x := by
      simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
        AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]
      exact mul_comm _ _
    simp only [hmul, mul_assoc, integral_const_mul] at H
    have hz : (∫ x : UnitAddTorus ι, mFourier (-n) x * g x) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr ht)
      linear_combination H
    simpa [smul_eq_mul] using hz
  have hs : Summable (mFourierCoeff g) := (hasSum_single 0 hzero).summable
  intro z
  have hz := hasSum_mFourier_series_apply_of_summable hs z
  have hsum : HasSum (fun n => mFourierCoeff g n • mFourier n z)
      (mFourierCoeff g 0) := by
    have H : HasSum (fun n => mFourierCoeff g n • mFourier n z)
        (mFourierCoeff g 0 • mFourier 0 z) := hasSum_single 0 fun n hn => by rw [hzero n hn, zero_smul]
    simpa [mFourier_zero] using H
  exact hz.unique hsum

private lemma all_limit {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : LinearIndependent ℚ α) :
    limitSet α = Set.univ := by
  let K := limitSet α
  let g : C(UnitAddTorus ι, ℂ) :=
    ⟨fun z => (Metric.infDist z K : ℂ), Complex.continuous_ofReal.comp (Metric.continuous_infDist_pt K)⟩
  have hK : K.Nonempty := limitSet_nonempty α
  have hKc : IsClosed K := isClosed_iInter fun _ => isClosed_closure
  have hconst := invariant_constant α hα g (fun x t => by
    change (Metric.infDist (x + flow α t) K : ℂ) = (Metric.infDist x K : ℂ)
    congr 1
    have ht := Metric.infDist_image (x := x) (t := K) (isometry_add_right (flow α t))
    rwa [limitSet_shift α t] at ht)
  apply Set.eq_univ_of_forall
  obtain ⟨y,hy⟩ := hK
  intro x
  have h := (hconst x).trans (hconst y).symm
  apply (hKc.mem_iff_infDist_zero ⟨y, hy⟩).mpr
  change (↑(Metric.infDist x K) : ℂ) = ↑(Metric.infDist y K) at h
  exact Complex.ofReal_injective h |>.trans (Metric.infDist_zero_of_mem hy)

/-- A torus flow with no zero integer frequency visits every nonempty open set arbitrarily late. -/
private lemma flow_eventually_hits {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : LinearIndependent ℚ α)
    {U : Set (UnitAddTorus ι)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ᶠ t : ℝ in atTop, flow α t ∈ U := by
  rw [Filter.frequently_atTop]
  intro R
  obtain ⟨z,hz⟩ := hne
  have hmem : z ∈ limitSet α := by simp [all_limit α hα]
  have hc := mem_iInter.mp hmem R
  obtain ⟨y,hy, t,ht,rfl⟩ := mem_closure_iff.mp hc U hU hz
  exact ⟨t,ht,hy⟩

end HarmonicFlow

open Set Filter Finset UnitAddTorus
open scoped Topology BigOperators Classical

noncomputable section

namespace HarmonicBands

private lemma longBands (X : ℝ) :
    ∃ S : Finset Nat.Primes, (∀ p ∈ S, 2 < (p : ℕ)) ∧
      X ≤ ∑ p ∈ S, 1 / (2 * (p : ℝ)) := by
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  have h : ∃ S : Finset Nat.Primes, 2 * X + 1 < ∑ p ∈ S, 1 / (p : ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨S,hS⟩ := h
  refine ⟨S.erase two, ?_, ?_⟩
  · intro p hp
    have hne : p ≠ two := (mem_erase.mp hp).1
    have hne' : (p : ℕ) ≠ 2 := fun h => hne (Subtype.ext h)
    have := p.property.two_le
    omega
  · have h' : (∑ p ∈ S, 1 / (p : ℝ)) ≤
        (∑ p ∈ S.erase two, 1 / (p : ℝ)) + 1 := by
      by_cases ht : two ∈ S
      · rw [← sum_erase_add _ _ ht]
        apply add_le_add_right
        norm_num [two]
      · rw [erase_eq_of_notMem ht]
        linarith
    have h'' : (∑ p ∈ S.erase two, 1 / (p : ℝ)) =
         2 * (∑ p ∈ S.erase two, 1 / (2 * (p : ℝ))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
      field_simp
    linarith

/-- Arrange the intervals consecutively, with rightmost endpoint zero. -/
private lemma placeBands {α : Type*} (S : Finset α) (d : α → ℝ) :
    ∃ b : α → ℝ, ∀ u ∈ Set.Ico (-(∑ i ∈ S, d i)) 0,
      ∃ i ∈ S, u ∈ Set.Icc (b i - d i) (b i) := by
  induction S using Finset.induction with
  | empty =>
    refine ⟨fun _ => 0, ?_⟩
    simp
  | insert i S hi ih =>
    obtain ⟨b,hb⟩ := ih
    let T := ∑ j ∈ S, d j
    refine ⟨Function.update b i (-T), ?_⟩
    intro u hu
    have lo : -(d i + T) ≤ u := by simpa [sum_insert hi, T] using hu.1
    by_cases h : -T ≤ u
    · obtain ⟨j,hj,hU⟩ := hb u ⟨h,hu.2⟩
      have hj' : j ≠ i := fun e => hi (e ▸ hj)
      exact ⟨j, mem_insert_of_mem hj, by simpa [Function.update_of_ne hj'] using hU⟩
    · refine ⟨i,mem_insert_self _ _,?_⟩
      rw [Function.update_self]
      exact ⟨by linarith, le_of_not_ge h⟩

private lemma unitCircle_difference {v w : ℝ}
    (h : (v : UnitAddCircle) = (w : UnitAddCircle)) :
    ∃ k : ℤ, v = w + k := by
  have hh : v - w ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    QuotientAddGroup.eq_iff_sub_mem.mp h
  obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
  refine ⟨k,?_⟩
  rw [zsmul_eq_mul, mul_one] at hk
  linarith

private lemma log_band {p k n : ℕ} (hp : 2 < p) (hk : 2 ≤ k) (hn : 0 < n)
    (hlo : (k : ℝ) * Real.log p - 1 / (p : ℝ) ≤ Real.log n)
    (hhi : Real.log n < (k : ℝ) * Real.log p) :
    (p-1)*p^(k-1) ≤ n ∧ n < p*p^(k-1) := by
  have pp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp' : 0 < (p : ℝ)-1 := by exact_mod_cast (show 0 < (p : ℤ)-1 by omega)
  have hsub : (p : ℝ)-1 = (p : ℝ) * (1 - 1 / (p : ℝ)) := by field_simp
  have hr : 0 < 1 - 1 / (p : ℝ) := by
    exact sub_pos.mpr ((div_lt_one pp).mpr (by linarith))
  have hl : Real.log ((p : ℝ)-1) ≤ Real.log p - 1 / (p : ℝ) := by
    have H := Real.log_le_sub_one_of_pos hr
    rw [hsub, Real.log_mul pp.ne' hr.ne']
    linarith
  have hkc : ((k-1 : ℕ):ℝ) + 1 = k := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
  have hnc : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · have hpr : 1 ≤ p := by omega
    have h : Real.log ((((p-1)*p^(k-1) : ℕ) : ℝ)) ≤ Real.log n := by
      rw [Nat.cast_mul, Nat.cast_sub hpr, Nat.cast_one, Nat.cast_pow,
        Real.log_mul hp'.ne' (pow_ne_zero _ pp.ne'), Real.log_pow]
      nlinarith only [hl, hlo, congrArg (fun x : ℝ => x * Real.log p) hkc]
    have hpos : 0 < ((((p-1)*p^(k-1) : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (show 0 < p-1 by omega) (pow_pos (show 0 < p by omega) _)
    exact_mod_cast (Real.strictMonoOn_log.le_iff_le hpos hnc).mp h
  · have h : Real.log n < Real.log (((p*p^(k-1) : ℕ) : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul pp.ne' (pow_ne_zero _ pp.ne'), Real.log_pow]
      nlinarith only [hhi, congrArg (fun x : ℝ => x * Real.log p) hkc]
    have hpos : 0 < (((p*p^(k-1) : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (show 0 < p by omega) (pow_pos (show 0 < p by omega) _)
    exact_mod_cast (Real.strictMonoOn_log.lt_iff_lt hnc hpos).mp h

end HarmonicBands

open HarmonicDigits HarmonicFlow HarmonicBands

private lemma frequently_bands (S : Finset Nat.Primes) (b : Nat.Primes → ℝ)
    (hα : LinearIndependent ℚ (fun p : Nat.Primes => 1 / Real.log (p : ℝ))) :
    ∃ᶠ t : ℝ in atTop, ∀ p ∈ S, ∃ k : ℕ, 2 ≤ k ∧
      (k : ℝ) * Real.log (p : ℝ) - 1 / (p : ℝ) ≤ t + b p - 1 / (2 * (p : ℝ)) ∧
      t + b p < (k : ℝ) * Real.log (p : ℝ) := by
  let α (p : ↥S) : ℝ := 1 / Real.log ((p : Nat.Primes) : ℝ)
  have hα' : LinearIndependent ℚ α := hα.comp _ Subtype.val_injective
  let center (p : ↥S) := (- b p - 1 / (4 * ((p : Nat.Primes) : ℝ))) * α p
  let radius (p : ↥S) := (1 / (8 * ((p : Nat.Primes) : ℝ))) * α p
  have hlog (p : ↥S) : 0 < Real.log ((p : Nat.Primes) : ℝ) :=
    Real.log_pos (by exact_mod_cast (p : Nat.Primes).property.one_lt)
  have hrad (p : ↥S) : 0 < radius p := by
    have hp : 0 < ((p : Nat.Primes) : ℝ) := by exact_mod_cast (p : Nat.Primes).property.pos
    exact mul_pos (by positivity) (one_div_pos.mpr (hlog p))
  let B (p : ↥S) : Set UnitAddCircle :=
    (fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (center p - radius p) (center p + radius p)
  let U := Set.pi Set.univ B
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ (fun p _ =>
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
  have hUne : U.Nonempty := by
    use fun p => (center p : UnitAddCircle)
    intro p _
    exact ⟨center p, ⟨by linarith [hrad p], by linarith [hrad p]⟩, rfl⟩
  have hlarge : ∀ᶠ t : ℝ in atTop, ∀ p : ↥S, Real.log ((p : Nat.Primes) : ℝ) ≤ t + b p := by
    have H := (Filter.eventually_all_finite (I := (Set.univ : Set ↥S)) Set.finite_univ).mpr
      (fun p _ => (eventually_ge_atTop (Real.log ((p : Nat.Primes) : ℝ) - b p)).mono
        (fun t ht => show Real.log ((p : Nat.Primes) : ℝ) ≤ t + b p by linarith))
    simpa using H
  refine ((flow_eventually_hits α hα' hU hUne).and_eventually hlarge).mono ?_
  rintro t ⟨ht, hlarge'⟩ p hp
  let i : ↥S := ⟨p,hp⟩
  obtain ⟨v, hv, hvEq⟩ := ht i (Set.mem_univ i)
  have hEq : ((t * α i : ℝ) : UnitAddCircle) = (v : UnitAddCircle) := hvEq.symm
  obtain ⟨k, hk⟩ := unitCircle_difference hEq
  have hl : 0 < Real.log (p : ℝ) := hlog i
  have hc : center i * Real.log (p : ℝ) = -b p - 1 / (4 * (p : ℝ)) := by
    dsimp [center, α, i]
    field_simp
  have hr : radius i * Real.log (p : ℝ) = 1 / (8 * (p : ℝ)) := by
    dsimp [radius, α, i]
    field_simp
  have hk' : t = v * Real.log (p : ℝ) + (k : ℝ) * Real.log (p : ℝ) := by
    have h := congrArg (fun u : ℝ => u * Real.log (p : ℝ)) hk
    change t * (1 / Real.log (p : ℝ)) * Real.log (p : ℝ) =
      (v + (k : ℝ)) * Real.log (p : ℝ) at h
    rw [mul_assoc, one_div_mul_cancel hl.ne', mul_one, add_mul] at h
    exact h
  have hlow := mul_lt_mul_of_pos_right hv.1 hl
  have hhigh := mul_lt_mul_of_pos_right hv.2 hl
  rw [sub_mul, hc, hr] at hlow
  rw [add_mul, hc, hr] at hhigh
  have hpR : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hfrac : 0 < 1 / (8 * (p : ℝ)) := by positivity
  have hf₂ : (1 : ℝ) / (2 * (p : ℝ)) = 4 * (1 / (8 * (p : ℝ))) := by field_simp; norm_num
  have hf₄ : (1 : ℝ) / (4 * (p : ℝ)) = 2 * (1 / (8 * (p : ℝ))) := by field_simp; norm_num
  have hf₈ : (1 : ℝ) / (p : ℝ) = 8 * (1 / (8 * (p : ℝ))) := by field_simp
  have hku : t + b p < (k : ℝ) * Real.log (p : ℝ) := by linarith
  have hk₂ : 2 ≤ k := by
    by_contra! h
    have h1 : (k : ℝ) ≤ 1 := by exact_mod_cast (show k ≤ 1 by omega)
    exact (not_lt_of_ge <| mul_le_of_le_one_left hl.le h1)
      ((hlarge' i).trans_lt hku)
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ k)
  refine ⟨k.toNat, by omega, ?_, ?_⟩
  · rw [hcast, hf₂, hf₈]
    linarith
  · rw [hcast]
    exact hku

private def goodCount (N : ℕ) :=
  ((Finset.Icc 1 N).filter (fun n => 1 < Nat.gcd (Erdos291.a n) (Erdos291.L n))).card

private lemma frequently_good (hα : LinearIndependent ℚ (fun p : Nat.Primes =>
    1 / Real.log (p : ℝ))) (η : ℝ) (hη : 0 < η) (hη' : η < 1/2) :
    ∃ᶠ N : ℕ in atTop, 1 - 2 * η ≤ (goodCount N : ℝ) / N := by
  obtain ⟨S, hS, hsum⟩ := longBands (-Real.log η)
  let d (p : Nat.Primes) := 1 / (2 * (p : ℝ))
  obtain ⟨b, hb⟩ := placeBands S d
  rw [Filter.frequently_atTop]
  intro M
  have hEt : ∀ᶠ t : ℝ in atTop, 3/η + (M : ℝ) + 2 ≤ Real.exp t :=
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨t, hbands, ht⟩ := ((frequently_bands S b hα).and_eventually hEt).exists
  let E := Real.exp t
  let N := ⌊E⌋₊
  let L := ⌈η*E⌉₊
  change 3/η + (M : ℝ) + 2 ≤ E at ht
  have hE : 0 < E := Real.exp_pos t
  have hE₁ : E < (N : ℝ) + 1 := Nat.lt_floor_add_one E
  have hE₂ : (N : ℝ) ≤ E := Nat.floor_le hE.le
  have hL₁ : η * E ≤ (L : ℝ) := Nat.le_ceil _
  have hL₂ : (L : ℝ) < η * E + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnM : (M : ℝ) ≤ (N : ℝ) := by linarith [show 0 < 3/η by positivity]
  have hM₀ : 0 ≤ (M : ℝ) := by positivity
  have hηN : 3 ≤ η * (N : ℝ) := by
    have h3 := (div_le_iff₀ hη).mp (show 3 / η ≤ (N : ℝ) by linarith)
    linarith
  have hL : 1 ≤ L := by
    have hh : 0 < (L : ℝ) := (mul_pos hη hE).trans_le hL₁
    exact_mod_cast (show 0 < L from by exact_mod_cast hh)
  have hLle : (L : ℝ) ≤ 2 * η * (N : ℝ) := by
    have H := mul_lt_mul_of_pos_left hE₁ hη
    nlinarith
  have hLN : L ≤ N := by
    exact_mod_cast (hLle.trans <| mul_le_of_le_one_left (by positivity) (by linarith))
  have hN : 0 < (N : ℝ) := by
    by_contra! h
    linarith [mul_nonpos_of_nonneg_of_nonpos hη.le h]
  have hsub : Finset.Ico L N ⊆
      (Finset.Icc 1 N).filter (fun n => 1 < Nat.gcd (Erdos291.a n) (Erdos291.L n)) := by
    intro n hn
    obtain ⟨hln, hnn⟩ := Finset.mem_Ico.mp hn
    have hn₀ : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn₀
    have hlo : Real.log η + t ≤ Real.log n := by
      have h := (Real.strictMonoOn_log.le_iff_le (mul_pos hη hE) hnR).mpr
        (hL₁.trans (by exact_mod_cast hln))
      rwa [Real.log_mul hη.ne' hE.ne', Real.log_exp] at h
    have hhi : Real.log n < t := by
      have hh := Real.log_lt_log hnR ((show (n : ℝ) < (N : ℝ) by exact_mod_cast hnn).trans_le hE₂)
      simpa [E] using hh
    have hu : Real.log n - t ∈ Set.Ico (-(∑ p ∈ S, d p)) 0 :=
      ⟨by linarith, by linarith⟩
    obtain ⟨p,hp,hpu⟩ := hb _ hu
    obtain ⟨k,hk,hkl,hkh⟩ := hbands p hp
    obtain ⟨hrlo,hrhi⟩ := log_band (hS p hp) hk hn₀
      (hkl.trans (by have := hpu.1; change b p - d p ≤ _ at this; linarith))
      ((show Real.log n ≤ t + b p by have := hpu.2; linarith).trans_lt hkh)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), good_digit p.property
      (hS p hp) (by omega) hrlo hrhi⟩
  have hcard : (N-L : ℕ) ≤ goodCount N := by
    simpa [goodCount, Nat.card_Ico] using Finset.card_le_card hsub
  refine ⟨N, by exact_mod_cast hnM, (le_div_iff₀ hN).mpr ?_⟩
  have hR : ((N-L : ℕ) : ℝ) ≤ (goodCount N : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hLN] at hR
  nlinarith

theorem OMA.solution : type_of% @Erdos291.erdos_291.variants.wu_yan := by
  intro hα
  change atTop.limsup (fun N : ℕ => ((goodCount N : ℝ) / (N : ℝ) : EReal)) = 1
  apply le_antisymm
  · refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hcard : goodCount N ≤ N := by
      simpa [goodCount, Nat.card_Icc] using Finset.card_filter_le (s := Finset.Icc 1 N)
        (fun n => 1 < Nat.gcd (Erdos291.a n) (Erdos291.L n))
    rw [← EReal.coe_div, ← EReal.coe_one, EReal.coe_le_coe_iff]
    exact (div_le_one (by exact_mod_cast (show 0 < N by omega))).mpr (by exact_mod_cast hcard)
  · by_contra! h
    obtain ⟨y, hyl, hyu⟩ := EReal.exists_between_coe_real h
    have hy : y < 1 := EReal.coe_lt_coe_iff.mp (by simpa using hyu)
    let η := min (1/4 : ℝ) ((1-y)/4)
    have hη : 0 < η := lt_min (by norm_num) (by linarith)
    have hη' : η < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
    have hle : y ≤ 1-2*η := by linarith [min_le_right (1/4 : ℝ) ((1-y)/4)]
    have hf : ∃ᶠ N : ℕ in atTop, (y : EReal) ≤ ((goodCount N : ℝ) / (N : ℝ) : EReal) :=
      (frequently_good hα η hη hη').mono (fun _ hn => EReal.coe_le_coe_iff.mpr (hle.trans hn))
    exact (not_le_of_gt hyl) (Filter.le_limsup_of_frequently_le' hf)