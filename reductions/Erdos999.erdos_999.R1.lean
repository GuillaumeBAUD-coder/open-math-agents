import FormalConjectures.ErdosProblems.«999»

-- Reduction of: Erdős Problem 999 (the Duffin and Schaeffer conjecture)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/999.lean:55 (declaration Erdos999.erdos_999)
-- Source: D. Koukoulopoulos and J. Maynard, On the Duffin-Schaeffer conjecture, Ann. of Math. 192 (2020),
-- Section 5 (the deduction of Theorem 1 from the second moment bound). This file formalizes that
-- deduction: the easy half by Borel and Cantelli, and the hard half from Gallagher's zero-one law
-- (in Mathlib), a Cauchy-Schwarz argument and the two inputs H1 and H2 below.

namespace OMA.R_Erdos999_erdos_999_R1

open MeasureTheory Filter Set Metric
open scoped Topology

-- Bridge: the problem's notion is membership of the class of x in Mathlib's limsup set.
lemma approx_iff (f : ℕ → ℝ) (x : ℝ) :
    Erdos999.IsApproximable f x ↔
      (x : UnitAddCircle) ∈ addWellApproximable UnitAddCircle (fun q => f q / q) := by
  rw [UnitAddCircle.mem_addWellApproximable_iff]
  unfold Erdos999.IsApproximable
  refine iff_of_eq (congr_arg Set.Infinite (Set.ext fun n => ?_))
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, p, hp, hx⟩
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h0 : 0 ≤ p % n := Int.emod_nonneg p hnZ.ne'
    have h1 : p % n < n := Int.emod_lt_of_pos p hnZ
    have hcast : (((p % n).toNat : ℕ) : ℤ) = p % n := Int.toNat_of_nonneg h0
    refine ⟨(p % n).toNat, ?_, ?_, ?_⟩
    · omega
    · have h2 : Int.gcd (p % n) n = 1 := by
        rw [Int.emod_def, Int.gcd_sub_mul_left_left]
        exact hp
      rw [← hcast, Int.gcd_natCast_natCast] at h2
      exact h2
    · have hsplit : (((p % n).toNat : ℕ) : ℝ) / n + ((p / n : ℤ) : ℝ) = (p : ℝ) / n := by
        have h3 : (((p % n).toNat : ℕ) : ℤ) + n * (p / n) = p := by
          rw [hcast]; exact Int.emod_add_mul_ediv p n
        have h4 : ((((p % n).toNat : ℕ) : ℤ) : ℝ) + (n : ℝ) * ((p / n : ℤ) : ℝ) = (p : ℝ) := by
          exact_mod_cast h3
        rw [Int.cast_natCast] at h4
        field_simp
        linarith
      rw [← AddCircle.coe_sub, UnitAddCircle.norm_eq]
      refine lt_of_le_of_lt (round_le _ (p / n)) ?_
      have : x - (((p % n).toNat : ℕ) : ℝ) / n - ((p / n : ℤ) : ℝ) = x - (p : ℝ) / n := by
        rw [← hsplit]; ring
      rw [this]
      exact hx
  · rintro ⟨m, hm, hg, hx⟩
    have hn : 0 < n := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← AddCircle.coe_sub, UnitAddCircle.norm_eq] at hx
    refine ⟨hn, (m : ℤ) + round (x - (m : ℝ) / n) * n, ?_, ?_⟩
    · rw [Int.gcd_add_mul_right_left, Int.gcd_natCast_natCast]
      exact hg
    · have : x - (((m : ℤ) + round (x - (m : ℝ) / n) * n : ℤ) : ℝ) / n
          = x - (m : ℝ) / n - (round (x - (m : ℝ) / n) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [this]
      exact hx

-- Almost everywhere statements on the circle pull back to the real line.
lemma ae_real_of_ae_circle (P : UnitAddCircle → Prop) (h : ∀ᵐ y : UnitAddCircle, P y) :
    ∀ᵐ x : ℝ, P (x : UnitAddCircle) := by
  have key : ∀ n : ℤ, ∀ᵐ (x : ℝ) ∂((volume : Measure ℝ).restrict (Ioc (n : ℝ) (n + 1))), P (x : UnitAddCircle) := by
    intro n
    exact (UnitAddCircle.measurePreserving_mk (n : ℝ)).quasiMeasurePreserving.tendsto_ae.eventually h
  have h2 := (ae_restrict_iUnion_iff (fun n : ℤ => Ioc (n : ℝ) (n + 1))
    (fun x : ℝ => P (x : UnitAddCircle))).2 key
  rw [iUnion_Ioc_intCast, Measure.restrict_univ] at h2
  exact h2

lemma approx_eq_biUnion (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    approxAddOrderOf UnitAddCircle q δ =
      ⋃ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset, ball y δ := by
  unfold approxAddOrderOf
  rw [thickening_eq_biUnion_ball]
  ext x
  simp

lemma card_order_eq (q : ℕ) (hq : 0 < q) :
    (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset.card = Nat.totient q := by
  rw [← Set.ncard_eq_toFinset_card _ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq),
    ← Nat.card_coe_set_eq]
  exact AddCircle.card_addOrderOf_eq_totient 1

-- Union bound: the q-th set has measure at most 2 δ φ(q).
lemma volume_approx_le (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    volume (approxAddOrderOf UnitAddCircle q δ) ≤
      (Nat.totient q : ENNReal) * ENNReal.ofReal (2 * δ) := by
  rw [approx_eq_biUnion q hq δ]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hball : ∀ y : UnitAddCircle, volume (ball y δ) ≤ ENNReal.ofReal (2 * δ) := by
    intro y
    calc volume (ball y δ) ≤ volume (closedBall y δ) := measure_mono ball_subset_closedBall
      _ = ENNReal.ofReal (min 1 (2 * δ)) := AddCircle.volume_closedBall (T := 1) (x := y) δ
      _ ≤ ENNReal.ofReal (2 * δ) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
  calc ∑ y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset, volume (ball y δ)
      ≤ ∑ _y ∈ (AddCircle.finite_setOfPred_addOrderOf_eq (p := (1 : ℝ)) hq).toFinset,
          ENNReal.ofReal (2 * δ) := Finset.sum_le_sum (fun y _ => hball y)
    _ = (Nat.totient q : ENNReal) * ENNReal.ofReal (2 * δ) := by
      rw [Finset.sum_const, card_order_eq q hq, nsmul_eq_mul]

-- Two distinct points of order q on the circle are at distance at least 1 / q.
lemma order_sep (q : ℕ) (hq : 0 < q) (y z : UnitAddCircle) (hy : addOrderOf y = q)
    (hz : addOrderOf z = q) (hne : y ≠ z) : 1 ≤ (q : ℝ) * dist y z := by
  have hu0 : y - z ≠ 0 := sub_ne_zero.mpr hne
  have hq0 : q • (y - z) = 0 := by
    rw [smul_sub]
    have h1 : q • y = 0 := by rw [← hy]; exact addOrderOf_nsmul_eq_zero y
    have h2 : q • z = 0 := by rw [← hz]; exact addOrderOf_nsmul_eq_zero z
    rw [h1, h2, sub_zero]
  have hfin : IsOfFinAddOrder (y - z) := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q, hq, hq0⟩
  have hdvd : addOrderOf (y - z) ∣ q := addOrderOf_dvd_of_nsmul_eq_zero hq0
  have hle : addOrderOf (y - z) ≤ q := Nat.le_of_dvd hq hdvd
  have h1 := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hfin hu0
  rw [nsmul_eq_mul] at h1
  rw [dist_eq_norm]
  have hle' : (addOrderOf (y - z) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
  calc (1 : ℝ) ≤ (addOrderOf (y - z) : ℝ) * ‖y - z‖ := h1
    _ ≤ (q : ℝ) * ‖y - z‖ := mul_le_mul_of_nonneg_right hle' (norm_nonneg _)

-- Exact measure when the balls are disjoint.
lemma volume_approx_eq (q : ℕ) (hq : 0 < q) (δ : ℝ) (h0 : 0 ≤ δ) (hδ : 2 * δ * q ≤ 1) :
    volume (approxAddOrderOf UnitAddCircle q δ) =
      (Nat.totient q : ENNReal) * ENNReal.ofReal (2 * δ) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have h2δ : 2 * δ ≤ 1 := by nlinarith
  rw [approx_eq_biUnion q hq δ, measure_biUnion_finset]
  · have hball : ∀ y : UnitAddCircle, volume (ball y δ) = ENNReal.ofReal (2 * δ) := by
      intro y
      rw [← measure_congr (AddCircle.closedBall_ae_eq_ball (x := y) (ε := δ)),
        AddCircle.volume_closedBall, min_eq_right h2δ]
    rw [Finset.sum_congr rfl (fun y _ => hball y), Finset.sum_const, card_order_eq q hq,
      nsmul_eq_mul]
  · intro y hy z hz hne
    have hy' : addOrderOf y = q := by simpa using hy
    have hz' : addOrderOf z = q := by simpa using hz
    have hsep := order_sep q hq y z hy' hz' hne
    apply ball_disjoint_ball
    have : 2 * δ * q ≤ dist y z * q := by nlinarith
    have := le_of_mul_le_mul_right this hqpos
    linarith
  · intro y _
    exact measurableSet_ball

-- Easy half (Borel and Cantelli): a convergent series gives a null limsup set.
lemma ae_notMem_of_summable (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q)
    (hs : Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q) :
    ∀ᵐ y : UnitAddCircle, y ∉ addWellApproximable UnitAddCircle (fun q => f q / q) := by
  rw [← measure_eq_zero_iff_ae_notMem]
  have hle : addWellApproximable UnitAddCircle (fun q => f q / q) ≤
      limsup (fun n => approxAddOrderOf UnitAddCircle n (f n / n)) atTop :=
    (blimsup_mono (fun _ _ => trivial)).trans_eq (blimsup_true _ _)
  refine measure_mono_null hle (measure_limsup_atTop_eq_zero ?_)
  have hb : ∀ n, volume (approxAddOrderOf UnitAddCircle n (f n / n)) ≤
      ENNReal.ofReal (2 * ((Nat.totient n : ℝ) * f n / n)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have he : approxAddOrderOf UnitAddCircle 0 (f 0 / ((0 : ℕ) : ℝ)) = ∅ := by
        unfold approxAddOrderOf
        exact Metric.thickening_of_nonpos (by simp) _
      rw [he]
      simp
    · refine (volume_approx_le n hn _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_natCast (Nat.totient n), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring
  have hnn : ∀ n : ℕ, 0 ≤ 2 * ((Nat.totient n : ℝ) * f n / n) := fun n =>
    mul_nonneg zero_le_two (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf n)) (Nat.cast_nonneg _))
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hb) ?_)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hs.mul_left 2)]
  exact ENNReal.ofReal_lt_top

-- Second moment inequality: for every real s,
-- 2 s (sum of measures) - s^2 (sum of pairwise overlaps) is at most the measure of the union.
lemma union_lower_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : Finset ℕ) (E : ℕ → Set α) (hE : ∀ q, MeasurableSet (E q)) (s : ℝ) :
    2 * s * (∑ q ∈ S, (μ (E q)).toReal) -
        s ^ 2 * (∑ q ∈ S, ∑ r ∈ S, (μ (E q ∩ E r)).toReal) ≤
      (μ (⋃ q ∈ S, E q)).toReal := by
  have hUm : MeasurableSet (⋃ q ∈ S, E q) := Finset.measurableSet_biUnion _ (fun q _ => hE q)
  obtain ⟨g, hg⟩ : ∃ g : α → ℝ, ∀ x, g x = ∑ q ∈ S, (E q).indicator (fun _ => (1 : ℝ)) x :=
    ⟨_, fun _ => rfl⟩
  have hpt : ∀ x, 2 * s * g x - s ^ 2 * (g x * g x) ≤
      (⋃ q ∈ S, E q).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ ⋃ q ∈ S, E q
    · rw [Set.indicator_of_mem hx]
      nlinarith [sq_nonneg (1 - s * g x)]
    · have hg0 : g x = 0 := by
        rw [hg]
        apply Finset.sum_eq_zero
        intro q hq
        apply Set.indicator_of_notMem
        intro hxq
        exact hx (Set.mem_biUnion hq hxq)
      rw [Set.indicator_of_notMem hx, hg0]
      simp
  have hint : ∀ q, Integrable ((E q).indicator (fun _ => (1 : ℝ))) μ :=
    fun q => (integrable_const 1).indicator (hE q)
  have hint2 : ∀ q r, Integrable ((E q ∩ E r).indicator (fun _ => (1 : ℝ))) μ :=
    fun q r => (integrable_const 1).indicator ((hE q).inter (hE r))
  have hgfun : g = fun x => ∑ q ∈ S, (E q).indicator (fun _ => (1 : ℝ)) x := funext hg
  have hgg : (fun x => g x * g x) =
      fun x => ∑ q ∈ S, ∑ r ∈ S, (E q ∩ E r).indicator (fun _ => (1 : ℝ)) x := by
    funext x
    rw [hg, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ => ?_))
    by_cases h1 : x ∈ E q <;> by_cases h2 : x ∈ E r <;> simp [Set.indicator, h1, h2]
  have hg_int : Integrable g μ := by
    rw [hgfun]
    exact integrable_finsetSum _ (fun q _ => hint q)
  have hgg_int : Integrable (fun x => g x * g x) μ := by
    rw [hgg]
    exact integrable_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ => hint2 q r))
  have hone : ∀ A : Set α, MeasurableSet A →
      ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ = (μ A).toReal := by
    intro A hA
    rw [integral_indicator_const _ hA]
    simp [measureReal_def]
  have h1 : ∫ x, g x ∂μ = ∑ q ∈ S, (μ (E q)).toReal := by
    rw [hgfun, integral_finsetSum _ (fun q _ => hint q)]
    exact Finset.sum_congr rfl (fun q _ => hone _ (hE q))
  have h2 : ∫ x, g x * g x ∂μ = ∑ q ∈ S, ∑ r ∈ S, (μ (E q ∩ E r)).toReal := by
    rw [hgg, integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ => hint2 q r))]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [integral_finsetSum _ (fun r _ => hint2 q r)]
    exact Finset.sum_congr rfl (fun r _ => hone _ ((hE q).inter (hE r)))
  have h3 : ∫ x, (2 * s * g x - s ^ 2 * (g x * g x)) ∂μ =
      2 * s * (∑ q ∈ S, (μ (E q)).toReal) -
        s ^ 2 * (∑ q ∈ S, ∑ r ∈ S, (μ (E q ∩ E r)).toReal) := by
    rw [integral_sub (hg_int.const_mul _) (hgg_int.const_mul _), integral_const_mul,
      integral_const_mul, h1, h2]
  rw [← h3, ← hone _ hUm]
  exact integral_mono ((hg_int.const_mul _).sub (hgg_int.const_mul _))
    ((integrable_const 1).indicator hUm) hpt

-- A divergent series of terms in [0, 1] has a block beyond any N with sum between 1 and 2.
lemma exists_block (a : ℕ → ℝ) (h0 : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n ≤ 1) (hns : ¬ Summable a)
    (N : ℕ) : ∃ S : Finset ℕ, (∀ q ∈ S, N ≤ q) ∧ 1 ≤ ∑ q ∈ S, a q ∧ ∑ q ∈ S, a q ≤ 2 := by
  have hex : ∃ n, 1 ≤ ∑ q ∈ Finset.Ico N n, a q := by
    by_contra hcon
    have hcon : ∀ n, ∑ q ∈ Finset.Ico N n, a q < 1 := fun n => not_le.1 (fun h => hcon ⟨n, h⟩)
    apply hns
    apply summable_of_sum_range_le (c := ∑ q ∈ Finset.range N, a q + 1) h0
    intro n
    rcases le_total n N with hnN | hnN
    · have : ∑ q ∈ Finset.range n, a q ≤ ∑ q ∈ Finset.range N, a q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hnN)
          (fun q _ _ => h0 q)
      linarith
    · have := Finset.sum_range_add_sum_Ico a hnN
      linarith [hcon n]
  obtain ⟨n0, hn0, hmin⟩ : ∃ n0, 1 ≤ ∑ q ∈ Finset.Ico N n0, a q ∧
      ∀ m < n0, ¬ (1 ≤ ∑ q ∈ Finset.Ico N m, a q) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨Finset.Ico N n0, fun q hq => (Finset.mem_Ico.1 hq).1, hn0, ?_⟩
  have hN : N < n0 := by
    by_contra hle
    have hle : n0 ≤ N := not_lt.1 hle
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty] at hn0
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n0 = k + 1 := ⟨n0 - 1, by omega⟩
  have hk := hmin k (by omega)
  rw [Finset.sum_Ico_succ_top (by omega)]
  linarith [h1 k]

-- (1) Pollington and Vaughan (1990), Theorem 2, quoted as Lemma 5.2 by Koukoulopoulos and
-- Maynard: the conjecture when every nonzero value of the function is at least 1/2.
def H1 : Prop :=
  ∀ f : ℕ → ℝ, (∀ q, f q = 0 ∨ 1 / 2 ≤ f q) →
    (¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q) →
    ∀ᵐ x : ℝ, Erdos999.IsApproximable f x

-- (2) Quasi-independence on average, the second moment bound (5.6) of Koukoulopoulos and
-- Maynard (Pollington and Vaughan overlap estimate plus their Proposition 5.4), on the circle:
-- for values in [0, 1/2] and any finite set of denominators with total weight between 1 and 2,
-- the sum of the measures of all pairwise intersections is bounded by an absolute constant.
def H2 : Prop :=
  ∃ C : ℝ, ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1 / 2) →
    ∀ S : Finset ℕ, (∀ q ∈ S, 0 < q) →
      1 ≤ ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q →
      ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q ≤ 2 →
      ∑ q ∈ S, ∑ r ∈ S,
        (volume (approxAddOrderOf UnitAddCircle q (ψ q / q) ∩
          approxAddOrderOf UnitAddCircle r (ψ r / r))).toReal ≤ C

-- Divergence plus the second moment bound gives a limsup set of positive measure.
lemma volume_wellApprox_ne_zero (h2 : H2) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1 / 2)
    (hns : ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * ψ q / q) :
    volume (addWellApproximable UnitAddCircle (fun q => ψ q / q)) ≠ 0 := by
  obtain ⟨C, hC⟩ := h2
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Set UnitAddCircle,
      ∀ n, E n = approxAddOrderOf UnitAddCircle n (ψ n / n) := ⟨_, fun _ => rfl⟩
  have hEm : ∀ n, MeasurableSet (E n) := by
    intro n
    rw [hEdef]
    exact isOpen_thickening.measurableSet
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ → Set UnitAddCircle,
      ∀ i, B i = ⋃ j, ⋃ (_ : 0 < j ∧ i ≤ j), E j := ⟨_, fun _ => rfl⟩
  have hWA : addWellApproximable UnitAddCircle (fun q => ψ q / q) = ⋂ i, B i := by
    unfold addWellApproximable
    rw [blimsup_eq_iInf_biSup_of_nat]
    simp only [iInf_eq_iInter, iSup_eq_iUnion, hBdef, hEdef]
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i
    rw [hBdef]
    exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hEm j))
  have hBanti : Antitone B := by
    intro i j hij x hx
    rw [hBdef] at hx ⊢
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨n, ⟨hn0, hjn⟩, hxn⟩ := hx
    exact ⟨n, ⟨hn0, le_trans hij hjn⟩, hxn⟩
  have hCpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcpos : (0 : ℝ) < 4 / max C 1 := div_pos (by norm_num) hCpos
  have hBlow : ∀ i, ENNReal.ofReal (4 / max C 1) ≤ volume (B i) := by
    intro i
    have ha0 : ∀ n : ℕ, 0 ≤ (Nat.totient n : ℝ) * ψ n / n := fun n =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ n).1) (Nat.cast_nonneg _)
    have ha1 : ∀ n : ℕ, (Nat.totient n : ℝ) * ψ n / n ≤ 1 := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have htot : (Nat.totient n : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
        rw [div_le_one hnR]
        nlinarith [(hψ n).1, (hψ n).2]
    obtain ⟨S, hSN, hS1, hS2⟩ := exists_block _ ha0 ha1 hns (i + 1)
    have hSpos : ∀ q ∈ S, 0 < q := fun q hq => by have := hSN q hq; omega
    have hvol : ∀ q ∈ S, (volume (E q)).toReal = 2 * ((Nat.totient q : ℝ) * ψ q / q) := by
      intro q hq
      have hq0 := hSpos q hq
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      have hδ0 : 0 ≤ ψ q / q := div_nonneg (hψ q).1 hqR.le
      have hδ1 : 2 * (ψ q / q) * q ≤ 1 := by
        have : 2 * (ψ q / q) * q = 2 * ψ q := by field_simp
        rw [this]
        linarith [(hψ q).2]
      rw [hEdef, volume_approx_eq q hq0 _ hδ0 hδ1, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hsum1 : ∑ q ∈ S, (volume (E q)).toReal =
        2 * ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hvol
    have hsum2 : ∑ q ∈ S, ∑ r ∈ S, (volume (E q ∩ E r)).toReal ≤ max C 1 := by
      have := hC ψ hψ S hSpos hS1 hS2
      simp only [hEdef]
      exact this.trans (le_max_left _ _)
    have hlow := union_lower_bound volume S E hEm (2 / max C 1)
    have hnum : 4 / max C 1 ≤ (volume (⋃ q ∈ S, E q)).toReal := by
      refine le_trans ?_ hlow
      rw [hsum1]
      have hs : (0 : ℝ) < 2 / max C 1 := div_pos (by norm_num) hCpos
      have e1 : 4 / max C 1 = 2 * (2 / max C 1) * (2 * 1) - (2 / max C 1) ^ 2 * max C 1 := by
        field_simp
        ring
      rw [e1]
      have t1 : 2 * (2 / max C 1) * (2 * 1) ≤
          2 * (2 / max C 1) * (2 * ∑ q ∈ S, (Nat.totient q : ℝ) * ψ q / q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have t2 : (2 / max C 1) ^ 2 * (∑ q ∈ S, ∑ r ∈ S, (volume (E q ∩ E r)).toReal) ≤
          (2 / max C 1) ^ 2 * max C 1 :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
      linarith
    have hsub : (⋃ q ∈ S, E q) ⊆ B i := by
      intro x hx
      rw [hBdef]
      simp only [mem_iUnion] at hx ⊢
      obtain ⟨q, hq, hxq⟩ := hx
      have := hSN q hq
      exact ⟨q, ⟨by omega, by omega⟩, hxq⟩
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hnum.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  have hlim := tendsto_measure_iInter_atTop (μ := (volume : Measure UnitAddCircle))
    (fun i => (hBm i).nullMeasurableSet) hBanti ⟨0, measure_ne_top _ _⟩
  have hge : ENNReal.ofReal (4 / max C 1) ≤ volume (⋂ i, B i) :=
    ge_of_tendsto' hlim hBlow
  rw [hWA]
  intro hzero
  rw [hzero] at hge
  exact absurd (ENNReal.ofReal_pos.2 hcpos) (not_lt.2 hge)

theorem main : H1 → H2 → type_of% @Erdos999.erdos_999 := by
  intro h1 h2 f hf
  constructor
  · intro hae hsum
    have hc := ae_real_of_ae_circle _ (ae_notMem_of_summable f hf hsum)
    obtain ⟨x, hx1, hx2⟩ := (hae.and hc).exists
    exact hx2 ((approx_iff f x).1 hx1)
  · intro hns
    obtain ⟨f1, hf1⟩ : ∃ f1 : ℕ → ℝ, ∀ q, f1 q = if 1 / 2 < f q then f q else 0 :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨f2, hf2⟩ : ∃ f2 : ℕ → ℝ, ∀ q, f2 q = if 1 / 2 < f q then 0 else f q :=
      ⟨_, fun _ => rfl⟩
    have hf1le : ∀ q, f1 q ≤ f q := by
      intro q
      rw [hf1]
      split_ifs
      · exact le_rfl
      · exact hf q
    have hf2le : ∀ q, f2 q ≤ f q := by
      intro q
      rw [hf2]
      split_ifs
      · exact hf q
      · exact le_rfl
    have hmono : ∀ g : ℕ → ℝ, (∀ q, g q ≤ f q) →
        ∀ x, Erdos999.IsApproximable g x → Erdos999.IsApproximable f x := by
      intro g hg x hx
      refine Set.Infinite.mono ?_ hx
      rintro q ⟨hq, p, hp, hlt⟩
      exact ⟨hq, p, hp, lt_of_lt_of_le hlt
        (div_le_div_of_nonneg_right (hg q) (Nat.cast_nonneg q))⟩
    by_cases hs1 : Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f1 q / q
    · have hs2 : ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f2 q / q := by
        intro hs2
        apply hns
        refine (hs1.add hs2).congr (fun q => ?_)
        rw [hf1, hf2]
        split_ifs <;> ring
      have hψ : ∀ q, 0 ≤ f2 q ∧ f2 q ≤ 1 / 2 := by
        intro q
        rw [hf2]
        split_ifs with h
        · norm_num
        · exact ⟨hf q, not_lt.1 h⟩
      have hpos := volume_wellApprox_ne_zero h2 f2 hψ hs2
      have htend : Tendsto (fun q : ℕ => f2 q / q) atTop (𝓝 0) :=
        squeeze_zero (fun q => div_nonneg (hψ q).1 (Nat.cast_nonneg q))
          (fun q => div_le_div_of_nonneg_right (hψ q).2 (Nat.cast_nonneg q))
          (tendsto_const_div_atTop_nhds_zero_nat (1 / 2))
      rcases AddCircle.addWellApproximable_ae_empty_or_univ (T := 1)
        (fun q : ℕ => f2 q / q) htend with hG | hG
      · exact absurd (measure_eq_zero_iff_ae_notMem.2 hG) hpos
      · have hc := ae_real_of_ae_circle _ hG
        filter_upwards [hc] with x hx
        exact hmono f2 hf2le x ((approx_iff f2 x).2 hx)
    · have hz : ∀ q, f1 q = 0 ∨ 1 / 2 ≤ f1 q := by
        intro q
        rw [hf1]
        split_ifs with h
        · exact Or.inr h.le
        · exact Or.inl rfl
      filter_upwards [h1 f1 hz hs1] with x hx
      exact hmono f1 hf1le x hx

end OMA.R_Erdos999_erdos_999_R1
