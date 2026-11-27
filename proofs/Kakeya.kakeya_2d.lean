import FormalConjectures.Wikipedia.Kakeya
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proof of `Kakeya.kakeya_2d` (Davies 1971)
-/

noncomputable section

open MeasureTheory Metric Set
open scoped EuclideanGeometry ENNReal

namespace Kakeya2DProof

lemma dist_le_two_mul_of_coord_le {p q : ℝ^2} {L : ℝ} (hL : 0 ≤ L)
    (h0 : |p 0 - q 0| ≤ L) (h1 : |p 1 - q 1| ≤ L) :
    dist p q ≤ 2 * L := by
  rw [dist_eq_norm, ← Real.sqrt_sq (by linarith : 0 ≤ 2 * L)]
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_two]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  have h0sq : (p 0 - q 0) ^ 2 ≤ L ^ 2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hL])
  have h1sq : (p 1 - q 1) ^ 2 ≤ L ^ 2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hL])
  nlinarith

lemma dimH_le_two (S : Set (ℝ^2)) : dimH S ≤ 2 := by
  refine (dimH_mono (Set.subset_univ S)).trans ?_
  let cube : ℕ → Set (ℝ^2) := fun N => {p | |p 0| ≤ (N : ℝ) ∧ |p 1| ≤ (N : ℝ)}
  have huniv : (Set.univ : Set (ℝ^2)) = ⋃ N : ℕ, cube N := by
    ext p
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff, cube, Set.mem_ofPred_eq]
    obtain ⟨N, hN⟩ := exists_nat_ge (max |p 0| |p 1|)
    exact ⟨N, (le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
  rw [huniv, dimH_iUnion]
  refine iSup_le fun N => ?_
  refine dimH_le_of_hausdorffMeasure_ne_top ?_
  have hle : μH[(2 : ℝ)] (cube N) ≤ ENNReal.ofReal (4 * (2 * (N : ℝ) + 1) ^ 2) := by
    rw [Measure.hausdorffMeasure_apply]
    refine iSup₂_le fun r hr => ?_
    have hr1_pos : 0 < (min r 1).toReal :=
      ENNReal.toReal_pos (lt_min hr one_pos).ne' (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne
    set r' := (min r 1).toReal
    have hr'_le : ENNReal.ofReal r' ≤ r := by
      rw [ENNReal.ofReal_toReal (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne]
      exact min_le_left _ _
    obtain ⟨k, hk_ge⟩ := exists_nat_gt (2 * (2 * (N : ℝ) + 1) / r')
    have hk_pos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst hk0'
      have : 0 < 2 * (2 * (N : ℝ) + 1) / r' := by positivity
      linarith
    have hk_real_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
    set L : ℝ := (2 * (N : ℝ) + 1) / k
    have hL_pos : 0 < L := by positivity
    have h2L_le : 2 * L ≤ r' := by
      rw [show 2 * L = 2 * (2 * (N : ℝ) + 1) / k by ring]
      rw [div_le_iff₀ hk_real_pos]
      have h1 : 2 * (2 * (N : ℝ) + 1) / r' < k := hk_ge
      rw [div_lt_iff₀ hr1_pos] at h1
      linarith
    let sq : ℕ → ℕ → Set (ℝ^2) := fun i j =>
      {p | -(N : ℝ) + (i : ℝ) * L ≤ p 0 ∧ p 0 ≤ -(N : ℝ) + ((i : ℝ) + 1) * L ∧
           -(N : ℝ) + (j : ℝ) * L ≤ p 1 ∧ p 1 ≤ -(N : ℝ) + ((j : ℝ) + 1) * L}
    let t : ℕ → Set (ℝ^2) := fun n =>
      if n < k * k then sq (n / k) (n % k) else ∅
    have hcov : cube N ⊆ ⋃ n : ℕ, t n := by
      intro p hp
      have hp0 : -(N : ℝ) ≤ p 0 ∧ p 0 ≤ N := abs_le.mp hp.1
      have hp1 : -(N : ℝ) ≤ p 1 ∧ p 1 ≤ N := abs_le.mp hp.2
      have hcoord : ∀ x : ℝ, -(N : ℝ) ≤ x → x ≤ N →
          ∃ i : ℕ, i < k ∧ -(N : ℝ) + (i : ℝ) * L ≤ x ∧ x ≤ -(N : ℝ) + ((i : ℝ) + 1) * L := by
        intro x hx0 hx1
        have hnonneg : 0 ≤ (x + N) / L := div_nonneg (by linarith) hL_pos.le
        refine ⟨Nat.floor ((x + N) / L), ?_, ?_, ?_⟩
        · rw [Nat.floor_lt hnonneg]
          rw [div_lt_iff₀ hL_pos]
          have : (k : ℝ) * L = 2 * (N : ℝ) + 1 := by
            dsimp [L]
            field_simp
          linarith
        · have hfl := Nat.floor_le hnonneg
          rw [le_div_iff₀ hL_pos] at hfl
          linarith
        · have hfl := Nat.lt_floor_add_one ((x + N) / L)
          rw [div_lt_iff₀ hL_pos] at hfl
          linarith
      obtain ⟨i, hi, hi0, hi1⟩ := hcoord (p 0) hp0.1 hp0.2
      obtain ⟨j, hj, hj0, hj1⟩ := hcoord (p 1) hp1.1 hp1.2
      refine Set.mem_iUnion.mpr ⟨i * k + j, ?_⟩
      have hlt : i * k + j < k * k := by nlinarith
      have hdiv : (i * k + j) / k = i := by
        rw [Nat.mul_comm i k, Nat.mul_add_div hk_pos, Nat.div_eq_of_lt hj, add_zero]
      have hmod : (i * k + j) % k = j := by
        rw [Nat.mul_comm i k, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      simp only [t, if_pos hlt, hdiv, hmod, sq, Set.mem_ofPred_eq]
      exact ⟨hi0, hi1, hj0, hj1⟩
    have hdiam : ∀ n : ℕ, ediam (t n) ≤ r := by
      intro n
      by_cases hn : n < k * k
      · simp only [t, if_pos hn]
        refine le_trans ?_ hr'_le
        refine (ediam_le_of_forall_dist_le fun p hp q hq => ?_).trans (ENNReal.ofReal_le_ofReal h2L_le)
        simp only [sq, Set.mem_ofPred_eq] at hp hq
        refine dist_le_two_mul_of_coord_le hL_pos.le ?_ ?_
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      · simp only [t, if_neg hn, ediam_empty, zero_le]
    refine le_trans (iInf₂_le t hcov) (le_trans (iInf_le _ hdiam) ?_)
    have hterm : ∀ n : ℕ, (⨆ (_ : (t n).Nonempty), ediam (t n) ^ (2 : ℝ)) ≤
        if n < k * k then ENNReal.ofReal ((2 * L) ^ 2) else 0 := by
      intro n
      by_cases hn : n < k * k
      · rw [if_pos hn]
        refine iSup_le fun _ => ?_
        have h1 : ediam (t n) ≤ ENNReal.ofReal (2 * L) := by
          simp only [t, if_pos hn]
          refine ediam_le_of_forall_dist_le fun p hp q hq => ?_
          simp only [sq, Set.mem_ofPred_eq] at hp hq
          refine dist_le_two_mul_of_coord_le hL_pos.le ?_ ?_
          · rw [abs_le]; constructor <;> linarith
          · rw [abs_le]; constructor <;> linarith
        calc ediam (t n) ^ (2 : ℝ)
            ≤ (ENNReal.ofReal (2 * L)) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = (ENNReal.ofReal (2 * L)) ^ (2 : ℕ) := ENNReal.rpow_two _
          _ = ENNReal.ofReal ((2 * L) ^ 2) := (ENNReal.ofReal_pow (by positivity) 2).symm
      · rw [if_neg hn]
        refine iSup_le fun hne => ?_
        exfalso
        simp only [t, if_neg hn, Set.not_nonempty_empty] at hne
    refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
    rw [tsum_eq_sum (s := Finset.range (k * k)) (fun n hn => by simp [Finset.mem_range.not.mp hn])]
    have hsum : ∑ n ∈ Finset.range (k * k), (if n < k * k then ENNReal.ofReal ((2 * L) ^ 2) else 0) =
        (k * k : ℕ) • ENNReal.ofReal ((2 * L) ^ 2) := by
      trans ∑ _n ∈ Finset.range (k * k), ENNReal.ofReal ((2 * L) ^ 2)
      · exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)
      · simp
    rw [hsum, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcalc : ((k * k : ℕ) : ℝ) * (2 * L) ^ 2 = 4 * (2 * (N : ℝ) + 1) ^ 2 := by
      push_cast
      dsimp [L]
      field_simp
      ring
    linarith
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/- ... Elementary analytic helpers ... -/

lemma exp_beats_poly (c C : ℝ) (hc : 0 < c) :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ m ≥ M, C * (m : ℝ) ^ 9 < (2 : ℝ) ^ (c * m) := by
  set b : ℝ := (2 : ℝ) ^ c
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hc
  set ε : ℝ := b - 1
  have hε : 0 < ε := sub_pos.mpr hb
  set K0 : ℝ := ε ^ 10 / ((2 : ℝ) ^ 10 * (Nat.factorial 10 : ℝ))
  have hK0 : 0 < K0 := by positivity
  obtain ⟨M0, hM0⟩ := exists_nat_gt (C / K0)
  refine ⟨max 20 M0, by omega, fun m hm => ?_⟩
  have hm20 : 20 ≤ m := le_trans (le_max_left _ _) hm
  have hmM0 : M0 ≤ m := le_trans (le_max_right _ _) hm
  have hm_pos : (0 : ℝ) < m := by positivity
  have hpow : (2 : ℝ) ^ (c * (m : ℝ)) = (1 + ε) ^ m := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    congr 1
    dsimp [b, ε]
    ring
  have hbin : ε ^ 10 * (m.choose 10 : ℝ) ≤ (1 + ε) ^ m := by
    rw [add_comm, add_pow]
    have hmem : 10 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun k => ε ^ k * 1 ^ (m - k) * (m.choose k : ℝ))
      (fun k _ => by positivity) hmem
    simpa using hle
  have hchoose : (m : ℝ) ^ 10 / ((2 : ℝ) ^ 10 * (Nat.factorial 10 : ℝ)) ≤ (m.choose 10 : ℝ) := by
    have hdesc : (m.choose 10 : ℝ) * (Nat.factorial 10 : ℝ) =
        ∏ i ∈ Finset.range 10, ((m : ℝ) - i) := by
      have hnat := Nat.descFactorial_eq_factorial_mul_choose m 10
      have hcast : ((m.choose 10 * Nat.factorial 10 : ℕ) : ℝ) = (m.descFactorial 10 : ℝ) := by
        exact_mod_cast (by linarith [mul_comm (m.choose 10) (Nat.factorial 10)])
      rw [Nat.cast_mul] at hcast
      rw [hcast, Nat.descFactorial_eq_prod_range]
      push_cast
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi10 : i < 10 := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega)]
    have hprod : (m : ℝ) ^ 10 / (2 : ℝ) ^ 10 ≤ ∏ i ∈ Finset.range 10, ((m : ℝ) - i) := by
      have h2 : ∀ i ∈ Finset.range 10, (m : ℝ) / 2 ≤ (m : ℝ) - i := by
        intro i hi
        have hi10 : (i : ℝ) < 10 := by exact_mod_cast Finset.mem_range.mp hi
        have hm20' : (20 : ℝ) ≤ m := by exact_mod_cast hm20
        linarith
      calc (m : ℝ) ^ 10 / (2 : ℝ) ^ 10
          = ∏ _i ∈ Finset.range 10, ((m : ℝ) / 2) := by
            rw [Finset.prod_const, Finset.card_range, div_pow]
        _ ≤ ∏ i ∈ Finset.range 10, ((m : ℝ) - i) :=
            Finset.prod_le_prod (fun _ _ => by positivity) h2
    rw [div_le_iff₀ (by positivity)]
    calc (m : ℝ) ^ 10 = ((m : ℝ) ^ 10 / (2 : ℝ) ^ 10) * (2 : ℝ) ^ 10 := by field_simp
      _ ≤ (∏ i ∈ Finset.range 10, ((m : ℝ) - i)) * (2 : ℝ) ^ 10 := by
          gcongr
      _ = (m.choose 10 : ℝ) * (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ 10 := by rw [hdesc]
      _ = (m.choose 10 : ℝ) * ((2 : ℝ) ^ 10 * (Nat.factorial 10 : ℝ)) := by ring
  have hlower : K0 * (m : ℝ) ^ 10 ≤ (2 : ℝ) ^ (c * (m : ℝ)) := by
    rw [hpow]
    calc K0 * (m : ℝ) ^ 10
        = ε ^ 10 * ((m : ℝ) ^ 10 / ((2 : ℝ) ^ 10 * (Nat.factorial 10 : ℝ))) := by
          dsimp [K0]; ring
      _ ≤ ε ^ 10 * (m.choose 10 : ℝ) := by gcongr
      _ ≤ (1 + ε) ^ m := hbin
  have hCM : C < K0 * (m : ℝ) := by
    have h1 : C / K0 < m := lt_of_lt_of_le hM0 (by exact_mod_cast hmM0)
    rwa [div_lt_iff₀ hK0, mul_comm] at h1
  calc C * (m : ℝ) ^ 9 < (K0 * (m : ℝ)) * (m : ℝ) ^ 9 := by gcongr
    _ = K0 * (m : ℝ) ^ 10 := by ring
    _ ≤ (2 : ℝ) ^ (c * (m : ℝ)) := hlower

lemma geom_tail_lt (s : ℝ) (hs : 0 < s) :
    ∃ M : ℕ, 4 ≤ M ∧
      (2 : ℝ) ^ s * (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * s) / (1 - (2 : ℝ) ^ (-s)) < 1 / 4 := by
  set q : ℝ := (2 : ℝ) ^ (-s)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  set C : ℝ := (2 : ℝ) ^ s / (1 - q)
  have hC : 0 < C := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (4 * C)) hq1
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  have hM : N ≤ max 4 N + 3 := by omega
  have hpow_le : q ^ (max 4 N + 3) ≤ q ^ N := pow_le_pow_of_le_one hq0.le hq1.le hM
  have hpow_eq : (2 : ℝ) ^ (-((max 4 N + 3 : ℕ) : ℝ) * s) = q ^ (max 4 N + 3) := by
    rw [show -((max 4 N + 3 : ℕ) : ℝ) * s = (-s) * ((max 4 N + 3 : ℕ) : ℝ) by ring]
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [hpow_eq, show (2 : ℝ) ^ s * q ^ (max 4 N + 3) / (1 - q) = C * q ^ (max 4 N + 3) by
    dsimp [C]; ring]
  calc C * q ^ (max 4 N + 3) ≤ C * q ^ N := by gcongr
    _ < C * (1 / (4 * C)) := by gcongr
    _ = 1 / 4 := by field_simp

lemma sum_inv_sq_ge_four_le :
    ∑' m : {m : ℕ // 4 ≤ m}, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / 3 := by
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have _hsub : Summable (fun m : {m : ℕ // 4 ≤ m} => (1 : ℝ) / (m : ℝ) ^ 2) :=
    hsum.subtype _
  let e : ℕ ≃ {m : ℕ // 4 ≤ m} :=
    { toFun := fun k => ⟨k + 4, by omega⟩
      invFun := fun m => m.1 - 4
      left_inv := fun k => Nat.add_sub_cancel k 4
      right_inv := fun m => by ext; dsimp; omega }
  rw [← Equiv.tsum_eq e]
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) fun n => ?_
  have hterm : ∀ k : ℕ, (1 : ℝ) / ((e k : ℕ) : ℝ) ^ 2 ≤
      1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4) := by
    intro k
    have hk : (e k : ℕ) = k + 4 := rfl
    rw [hk]
    push_cast
    have h1 : 0 < (k : ℝ) + 3 := by positivity
    have h2 : 0 < (k : ℝ) + 4 := by positivity
    rw [div_sub_div _ _ h1.ne' h2.ne']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑ k ∈ Finset.range n, (1 : ℝ) / ((e k : ℕ) : ℝ) ^ 2
      ≤ ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 4)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 1 / (3 : ℝ) - 1 / ((n : ℝ) + 3) := by
        clear hterm hsum _hsub e
        induction n with
        | zero => norm_num
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring
    _ ≤ 1 / 3 := by
        have : 0 ≤ 1 / ((n : ℝ) + 3) := by positivity
        linarith

lemma harmonic_dyadic_bound :
    ∀ k : ℕ, ∑ d ∈ Finset.Icc (1 : ℕ) (2 ^ k), (1 : ℝ) / (d : ℝ) ≤ 1 + (k : ℝ) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hsplit : Finset.Icc (1 : ℕ) (2 ^ (k + 1)) =
        Finset.Icc (1 : ℕ) (2 ^ k) ∪ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      have hpow : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdisj : Disjoint (Finset.Icc (1 : ℕ) (2 ^ k)) (Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1))) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      simp only [Finset.mem_Icc] at hd1
      simp only [Finset.mem_Ioc] at hd2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have h2 : ∑ d ∈ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)), (1 : ℝ) / (d : ℝ) ≤ 1 := by
      have hle : ∀ d ∈ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)), (1 : ℝ) / (d : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
        intro d hd
        have hd' : 2 ^ k < d := (Finset.mem_Ioc.mp hd).1
        gcongr
      calc ∑ d ∈ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)), (1 : ℝ) / (d : ℝ)
          ≤ ∑ _d ∈ Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1)), (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
            Finset.sum_le_sum hle
        _ = ((Finset.Ioc ((2 : ℕ) ^ k) (2 ^ (k + 1))).card : ℝ) * (1 / ((2 ^ k : ℕ) : ℝ)) := by
            simp [Finset.sum_const]
        _ = 1 := by
            rw [Nat.card_Ioc, Nat.sub_eq_of_eq_add (by ring : 2 ^ (k + 1) = 2 ^ k + 2 ^ k)]
            have hpos : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
            field_simp
    push_cast
    linarith

lemma cauchy_schwarz_finite {U : Set (ℝ^2)} (hU : volume U < ⊤) {F : ℝ^2 → ℝ}
    (hF1 : IntegrableOn F U volume) (hF2 : IntegrableOn (fun p => F p ^ 2) U volume) :
    (∫ p in U, F p) ^ 2 ≤ (∫ p in U, F p ^ 2) * (volume U).toReal := by
  by_cases hU0 : (volume U).toReal = 0
  · have hvol0 : volume U = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (volume U)).mp hU0 with h | h
      · exact h
      · exact absurd h hU.ne
    have hInt0 : ∫ p in U, F p = 0 := by
      rw [Measure.restrict_eq_zero.mpr hvol0, integral_zero_measure]
    rw [hInt0, hU0]
    norm_num
  · have hvol_pos : 0 < (volume U).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hU0)
    set μ := volume.restrict U
    have : IsFiniteMeasure μ := ⟨by simpa [μ] using hU⟩
    set c : ℝ := (∫ p, F p ∂μ) / (μ Set.univ).toReal
    have hnonneg : 0 ≤ ∫ p, (F p - c) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    have h2cF : Integrable (fun p => 2 * c * F p) μ := hF1.const_mul (2 * c)
    have hsub : Integrable (fun p => F p ^ 2 - 2 * c * F p) μ := hF2.sub h2cF
    have hsq_eq : (fun p => (F p - c) ^ 2) = fun p => F p ^ 2 - 2 * c * F p + c ^ 2 := by
      ext p; ring
    rw [hsq_eq, integral_add hsub (integrable_const (c ^ 2)),
        integral_sub hF2 h2cF, integral_const_mul, integral_const] at hnonneg
    simp only [smul_eq_mul, Measure.real_def] at hnonneg
    have hμU : (μ Set.univ).toReal = (volume U).toReal := by
      simp [μ]
    rw [hμU] at hnonneg
    have hcalc : (∫ p, F p ^ 2 ∂μ) - 2 * c * (∫ p, F p ∂μ) + (volume U).toReal * c ^ 2 =
        (∫ p, F p ^ 2 ∂μ) - (∫ p, F p ∂μ) ^ 2 / (volume U).toReal := by
      dsimp [c]
      rw [hμU]
      field_simp
      ring
    rw [hcalc] at hnonneg
    have hle : (∫ p, F p ∂μ) ^ 2 / (volume U).toReal ≤ ∫ p, F p ^ 2 ∂μ := by linarith
    rwa [div_le_iff₀ hvol_pos] at hle

/- ... Geometry and volume helpers ... -/

def v (θ : ℝ) : ℝ^2 := !₂[Real.cos θ, Real.sin θ]
def vPerp (θ : ℝ) : ℝ^2 := !₂[-Real.sin θ, Real.cos θ]

lemma norm_v (θ : ℝ) : ‖v θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]

lemma inner_v_vPerp (θ : ℝ) : inner ℝ (v θ) (vPerp θ) = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [v, vPerp, RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inner_vPerp_self (θ : ℝ) : inner ℝ (vPerp θ) (vPerp θ) = 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [vPerp, RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

def box2 (s₀ s₁ : Set ℝ) : Set (ℝ^2) := {p | p 0 ∈ s₀ ∧ p 1 ∈ s₁}

lemma measurableSet_box2 {s₀ s₁ : Set ℝ} (h₀ : MeasurableSet s₀) (h₁ : MeasurableSet s₁) :
    MeasurableSet (box2 s₀ s₁) := by
  change MeasurableSet {p : ℝ^2 | p 0 ∈ s₀ ∧ p 1 ∈ s₁}
  exact (h₀.preimage (PiLp.continuous_apply 2 (fun _ => ℝ) 0).measurable).inter
    (h₁.preimage (PiLp.continuous_apply 2 (fun _ => ℝ) 1).measurable)

lemma volume_box2 {s₀ s₁ : Set ℝ} (h₀ : MeasurableSet s₀) (h₁ : MeasurableSet s₁) :
    volume (box2 s₀ s₁) = volume s₀ * volume s₁ := by
  have heq : box2 s₀ s₁ = (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' (Set.univ.pi ![s₀, s₁]) := by
    ext p
    simp only [box2, Set.mem_ofPred_eq, Set.mem_preimage, MeasurableEquiv.toLp_symm_apply,
      Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨hp0, hp1⟩ i
      fin_cases i
      · exact hp0
      · exact hp1
    · intro hp
      exact ⟨hp 0, hp 1⟩
  rw [heq]
  have hmeas : MeasurableSet (Set.univ.pi ![s₀, s₁]) := by
    refine MeasurableSet.univ_pi fun i => ?_
    fin_cases i
    · exact h₀
    · exact h₁
  rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).measure_preimage
    hmeas.nullMeasurableSet]
  change Measure.pi (fun _ : Fin 2 => volume) (Set.univ.pi ![s₀, s₁]) = volume s₀ * volume s₁
  rw [Measure.pi_pi, Fin.prod_univ_two]
  rfl

lemma volume_square (c : ℝ^2) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume {p : ℝ^2 | |p 0 - c 0| ≤ ρ ∧ |p 1 - c 1| ≤ ρ} = ENNReal.ofReal (4 * ρ ^ 2) := by
  have heq : {p : ℝ^2 | |p 0 - c 0| ≤ ρ ∧ |p 1 - c 1| ≤ ρ} =
      box2 (Set.Icc (c 0 - ρ) (c 0 + ρ)) (Set.Icc (c 1 - ρ) (c 1 + ρ)) := by
    ext p
    simp only [box2, Set.mem_ofPred_eq, Set.mem_Icc, abs_sub_le_iff]
    constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;> exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [heq, volume_box2 measurableSet_Icc measurableSet_Icc, Real.volume_Icc, Real.volume_Icc]
  rw [show c 0 + ρ - (c 0 - ρ) = 2 * ρ by ring, show c 1 + ρ - (c 1 - ρ) = 2 * ρ by ring]
  rw [← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

def orthoMap (θ : ℝ) : ℝ^2 →ₗ[ℝ] ℝ^2 where
  toFun p := p 0 • v θ + p 1 • vPerp θ
  map_add' p q := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' r p := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

lemma det_orthoMap (θ : ℝ) : LinearMap.det (orthoMap θ) = 1 := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, b, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  simp only [orthoMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.single_apply, v, vPerp]
  norm_num
  nlinarith [Real.cos_sq_add_sin_sq θ]

def projMap (θ₁ θ₂ : ℝ) : ℝ^2 →ₗ[ℝ] ℝ^2 where
  toFun p := !₂[inner ℝ p (vPerp θ₁), inner ℝ p (vPerp θ₂)]
  map_add' p q := by
    ext i; fin_cases i <;> simp [inner_add_left]
  map_smul' r p := by
    ext i; fin_cases i <;> simp [inner_smul_left]

lemma det_projMap (θ₁ θ₂ : ℝ) : LinearMap.det (projMap θ₁ θ₂) = Real.sin (θ₂ - θ₁) := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, b, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  simp only [projMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    PiLp.single_apply, vPerp]
  norm_num
  rw [Real.sin_sub]
  ring

lemma well_separated_angles
    (m : ℕ) (hm4 : 4 ≤ m) (N : ℕ) (δ : ℝ) (_hδ_pos : 0 < δ) (hN_δ : (N : ℝ) * δ = 1)
    (Θ : Set ℝ) (hΘ_sub : Θ ⊆ Set.Ico (0 : ℝ) (Real.pi / 2))
    (hΘ_vol : ENNReal.ofReal (1 / (m : ℝ) ^ 2) ≤ volume Θ) :
    ∃ (S_idx : Finset (Fin N)) (θ : Fin N → ℝ),
      (N : ℝ) / (Real.pi * (m : ℝ) ^ 2) ≤ (S_idx.card : ℝ) ∧
      (∀ j ∈ S_idx, θ j ∈ Θ) ∧
      (∀ j₁ ∈ S_idx, ∀ j₂ ∈ S_idx, j₁ ≠ j₂ →
        |((j₁.1 : ℝ) - (j₂.1 : ℝ))| * δ / 2 ≤ |Real.sin (θ j₂ - θ j₁)|) := by
  classical
  have hm_pos : (0 : ℝ) < m := by positivity
  have hN_pos : 0 < N := by
    by_contra h0
    have h0' : N = 0 := Nat.eq_zero_of_not_pos h0
    rw [h0'] at hN_δ
    norm_num at hN_δ
  set L : ℝ := Real.pi / (2 * (N : ℝ))
  have hL_pos : 0 < L := by positivity
  let J : Fin N → Set ℝ := fun j => Set.Ico ((j.1 : ℝ) * L) (((j.1 : ℝ) + 1) * L)
  let Good : Finset (Fin N) := Finset.univ.filter (fun j => (Θ ∩ J j).Nonempty)
  have hΘ_cov : Θ ⊆ ⋃ j ∈ Good, J j := fun θ hθ => by
    have hθ0 : 0 ≤ θ := (hΘ_sub hθ).1
    have hθpi : θ < Real.pi / 2 := (hΘ_sub hθ).2
    have hfloor : Nat.floor (θ / L) < N := by
      rw [Nat.floor_lt (div_nonneg hθ0 hL_pos.le), div_lt_iff₀ hL_pos]
      have : (N : ℝ) * L = Real.pi / 2 := by dsimp [L]; field_simp
      linarith
    have hJ : θ ∈ J ⟨Nat.floor (θ / L), hfloor⟩ := by
      refine ⟨?_, ?_⟩
      · have hfl := Nat.floor_le (div_nonneg hθ0 hL_pos.le)
        rw [le_div_iff₀ hL_pos] at hfl
        exact hfl
      · have hfl := Nat.lt_floor_add_one (θ / L)
        rw [div_lt_iff₀ hL_pos] at hfl
        exact hfl
    exact Set.mem_iUnion₂.mpr
      ⟨⟨Nat.floor (θ / L), hfloor⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨θ, hθ, hJ⟩⟩, hJ⟩
  have hGood_card : 2 * (N : ℝ) / (Real.pi * (m : ℝ) ^ 2) ≤ (Good.card : ℝ) := by
    have hvol_Θ : ENNReal.ofReal (1 / (m : ℝ) ^ 2) ≤ ∑ j ∈ Good, volume (J j) :=
      hΘ_vol.trans ((measure_mono hΘ_cov).trans (measure_biUnion_finset_le _ _))
    have hvol_J : ∀ j : Fin N, volume (J j) = ENNReal.ofReal L := fun j => by
      dsimp [J]; rw [Real.volume_Ico]; congr 1; ring
    simp only [hvol_J, Finset.sum_const, nsmul_eq_mul] at hvol_Θ
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hvol_Θ
    have hreal : 1 / (m : ℝ) ^ 2 ≤ (Good.card : ℝ) * L := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_Θ
      rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at this
    rw [div_le_iff₀ (by positivity)]
    calc 2 * (N : ℝ) = 2 * (N : ℝ) * (1 / (m : ℝ) ^ 2) * (m : ℝ) ^ 2 := by field_simp
      _ ≤ 2 * (N : ℝ) * ((Good.card : ℝ) * L) * (m : ℝ) ^ 2 := by gcongr
      _ = (Good.card : ℝ) * (Real.pi * (m : ℝ) ^ 2) := by
          dsimp [L]; field_simp
  let GoodEven : Finset (Fin N) := Good.filter (fun j => Even j.1)
  let GoodOdd : Finset (Fin N) := Good.filter (fun j => ¬ Even j.1)
  let S_idx : Finset (Fin N) := if GoodOdd.card ≤ GoodEven.card then GoodEven else GoodOdd
  have hK_ge : (N : ℝ) / (Real.pi * (m : ℝ) ^ 2) ≤ (S_idx.card : ℝ) := by
    have hsplit_Good : Good.card = GoodEven.card + GoodOdd.card := by
      rw [Finset.card_filter_add_card_filter_not]
    have h2K : Good.card ≤ 2 * S_idx.card := by
      dsimp [S_idx]
      split_ifs <;> omega
    have h2K' : (Good.card : ℝ) ≤ 2 * (S_idx.card : ℝ) := by exact_mod_cast h2K
    rw [div_le_iff₀ (by positivity)]
    have hG' := hGood_card
    rw [div_le_iff₀ (by positivity)] at hG'
    calc (N : ℝ) = 2 * (N : ℝ) / 2 := by ring
      _ ≤ (Good.card : ℝ) * (Real.pi * (m : ℝ) ^ 2) / 2 := by linarith
      _ ≤ (2 * (S_idx.card : ℝ)) * (Real.pi * (m : ℝ) ^ 2) / 2 := by gcongr
      _ = (S_idx.card : ℝ) * (Real.pi * (m : ℝ) ^ 2) := by ring
  have hS_sub_Good : S_idx ⊆ Good := by
    dsimp [S_idx]
    split_ifs <;> exact Finset.filter_subset _ _
  have hS_parity : ∀ j₁ ∈ S_idx, ∀ j₂ ∈ S_idx, j₁ ≠ j₂ →
      (2 : ℝ) ≤ |((j₁.1 : ℝ) - (j₂.1 : ℝ))| := by
    intro j₁ hj₁ j₂ hj₂ hne
    have hne1 : j₁.1 ≠ j₂.1 := fun h => hne (Fin.ext h)
    have hpar : Even j₁.1 ↔ Even j₂.1 := by
      dsimp [S_idx] at hj₁ hj₂
      split_ifs at hj₁ hj₂
      · exact ⟨fun _ => (Finset.mem_filter.mp hj₂).2, fun _ => (Finset.mem_filter.mp hj₁).2⟩
      · exact ⟨fun h => absurd h (Finset.mem_filter.mp hj₁).2,
          fun h => absurd h (Finset.mem_filter.mp hj₂).2⟩
    have hdist2 : (2 : ℤ) ≤ |((j₁.1 : ℤ) - (j₂.1 : ℤ))| := by
      rcases Nat.even_or_odd j₁.1 with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨b, hb⟩ := hpar.mp ⟨a, ha⟩
        have h1 : (j₁.1 : ℤ) = 2 * a := by exact_mod_cast (by omega : j₁.1 = 2 * a)
        have h2 : (j₂.1 : ℤ) = 2 * b := by exact_mod_cast (by omega : j₂.1 = 2 * b)
        have hab : a ≠ b := by omega
        rw [h1, h2]
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · rw [abs_of_neg (by linarith)]; omega
        · rw [abs_of_pos (by linarith)]; omega
      · have h2' : Odd j₂.1 :=
          Nat.not_even_iff_odd.mp fun h => (Nat.not_even_iff_odd.mpr ⟨a, ha⟩) (hpar.mpr h)
        obtain ⟨b, hb⟩ := h2'
        have h1 : (j₁.1 : ℤ) = 2 * a + 1 := by exact_mod_cast (by omega : j₁.1 = 2 * a + 1)
        have h2 : (j₂.1 : ℤ) = 2 * b + 1 := by exact_mod_cast (by omega : j₂.1 = 2 * b + 1)
        have hab : a ≠ b := by omega
        rw [h1, h2]
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · rw [abs_of_neg (by linarith)]; omega
        · rw [abs_of_pos (by linarith)]; omega
    exact_mod_cast hdist2
  let θ : Fin N → ℝ := fun j =>
    if h : j ∈ Good then (Finset.mem_filter.mp h).2.some else 0
  have hθ_mem : ∀ j ∈ S_idx, θ j ∈ Θ ∩ J j := fun j hj => by
    have hjG := hS_sub_Good hj
    dsimp [θ]
    rw [dif_pos hjG]
    exact (Finset.mem_filter.mp hjG).2.some_mem
  refine ⟨S_idx, θ, hK_ge, fun j hj => (hθ_mem j hj).1, fun j₁ hj₁ j₂ hj₂ hne => ?_⟩
  have h1 := hθ_mem j₁ hj₁
  have h2 := hθ_mem j₂ hj₂
  have hpar := hS_parity j₁ hj₁ j₂ hj₂ hne
  have hdiff_lb : (1 / 2 : ℝ) * |((j₁.1 : ℝ) - (j₂.1 : ℝ))| * L ≤ |θ j₂ - θ j₁| := by
    rcases lt_trichotomy j₁.1 j₂.1 with hlt | heq | hgt
    · have hle : (j₁.1 : ℝ) + 2 ≤ (j₂.1 : ℝ) := by
        have : (j₁.1 : ℝ) < (j₂.1 : ℝ) := by exact_mod_cast hlt
        rw [abs_of_neg (by linarith)] at hpar
        linarith
      have hsub : ((j₂.1 : ℝ) - ((j₁.1 : ℝ) + 1)) * L ≤ θ j₂ - θ j₁ := by
        have := h1.2.2; have := h2.2.1
        calc ((j₂.1 : ℝ) - ((j₁.1 : ℝ) + 1)) * L
            = (j₂.1 : ℝ) * L - ((j₁.1 : ℝ) + 1) * L := by ring
          _ ≤ θ j₂ - θ j₁ := by linarith
      have hsub2 : (1 / 2 : ℝ) * ((j₂.1 : ℝ) - (j₁.1 : ℝ)) * L ≤ ((j₂.1 : ℝ) - ((j₁.1 : ℝ) + 1)) * L := by
        have : (1 / 2 : ℝ) * ((j₂.1 : ℝ) - (j₁.1 : ℝ)) ≤ (j₂.1 : ℝ) - ((j₁.1 : ℝ) + 1) := by linarith
        exact mul_le_mul_of_nonneg_right this hL_pos.le
      rw [abs_of_neg (by
        have : (j₁.1 : ℝ) < (j₂.1 : ℝ) := by exact_mod_cast hlt
        linarith), abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (Fin.ext heq) hne
    · have hle : (j₂.1 : ℝ) + 2 ≤ (j₁.1 : ℝ) := by
        have : (j₂.1 : ℝ) < (j₁.1 : ℝ) := by exact_mod_cast hgt
        rw [abs_of_pos (by linarith)] at hpar
        linarith
      have hsub : ((j₁.1 : ℝ) - ((j₂.1 : ℝ) + 1)) * L ≤ θ j₁ - θ j₂ := by
        have := h2.2.2; have := h1.2.1
        calc ((j₁.1 : ℝ) - ((j₂.1 : ℝ) + 1)) * L
            = (j₁.1 : ℝ) * L - ((j₂.1 : ℝ) + 1) * L := by ring
          _ ≤ θ j₁ - θ j₂ := by linarith
      have hsub2 : (1 / 2 : ℝ) * ((j₁.1 : ℝ) - (j₂.1 : ℝ)) * L ≤ ((j₁.1 : ℝ) - ((j₂.1 : ℝ) + 1)) * L := by
        have : (1 / 2 : ℝ) * ((j₁.1 : ℝ) - (j₂.1 : ℝ)) ≤ (j₁.1 : ℝ) - ((j₂.1 : ℝ) + 1) := by linarith
        exact mul_le_mul_of_nonneg_right this hL_pos.le
      rw [abs_of_pos (by
        have : (j₂.1 : ℝ) < (j₁.1 : ℝ) := by exact_mod_cast hgt
        linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  have hdiff_ub : |θ j₂ - θ j₁| ≤ Real.pi / 2 := by
    have ha1 := hΘ_sub h1.1; have ha2 := hΘ_sub h2.1
    rw [abs_le]
    constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]
  have hle_pi : |θ j₂ - θ j₁| ≤ Real.pi := by linarith [Real.pi_pos]
  have hsin_eq : |Real.sin (θ j₂ - θ j₁)| = Real.sin |θ j₂ - θ j₁| := by
    rcases le_total 0 (θ j₂ - θ j₁) with h | h
    · rw [abs_of_nonneg h] at hle_pi ⊢
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h hle_pi)
    · rw [abs_of_nonpos h] at hle_pi ⊢
      rw [← abs_neg, ← Real.sin_neg]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hle_pi)
  rw [hsin_eq]
  calc |((j₁.1 : ℝ) - (j₂.1 : ℝ))| * δ / 2
      = (2 / Real.pi) * ((1 / 2 : ℝ) * |((j₁.1 : ℝ) - (j₂.1 : ℝ))| * L) := by
        dsimp [L]
        have : (N : ℝ) * δ = 1 := hN_δ
        field_simp
        nlinarith [Real.pi_pos]
    _ ≤ (2 / Real.pi) * |θ j₂ - θ j₁| := by gcongr
    _ ≤ Real.sin |θ j₂ - θ j₁| := Real.mul_le_sin (abs_nonneg _) hdiff_ub

lemma cauchy_schwarz_step
    (m : ℕ) (hm4 : 4 ≤ m) (s : ℝ) (hs_lt_two : s < 2)
    (N : ℕ) (hN : N = 2 ^ m) (δ : ℝ) (hδ : δ = (2 : ℝ) ^ (-(m : ℤ)))
    (hδ_pos : 0 < δ) (hN_δ : (N : ℝ) * δ = 1)
    (A_card : ℝ) (hA_card : A_card ≤ (2 : ℝ) ^ s * (2 : ℝ) ^ ((m : ℝ) * s))
    (S_idx : Finset (Fin N)) (T : Fin N → Set (ℝ^2))
    (hT_meas : ∀ j, MeasurableSet (T j))
    (hK_ge : (N : ℝ) / (Real.pi * (m : ℝ) ^ 2) ≤ (S_idx.card : ℝ))
    (hU_tubes_vol_ub : (volume (⋃ j ∈ S_idx, T j)).toReal ≤ A_card * (16 * δ ^ 2))
    (hU_tubes_lt_top : volume (⋃ j ∈ S_idx, T j) < ⊤)
    (hT_vol_lb : ∀ j ∈ S_idx, 2 * δ / (m : ℝ) ^ 2 ≤ (volume (T j)).toReal)
    (hT_vol_ub : ∀ j, (volume (T j)).toReal ≤ 2 * δ)
    (hT_inter_ub : ∀ j₁ ∈ S_idx, ∀ j₂ ∈ S_idx, j₁ ≠ j₂ →
      (volume (T j₁ ∩ T j₂)).toReal ≤ 8 * δ / |((j₁.1 : ℝ) - (j₂.1 : ℝ))|)
    (hexp : 336 * Real.pi ^ 2 * (m : ℝ) ^ 9 < (2 : ℝ) ^ ((2 - s) * (m : ℝ))) : False := by
  let U_tubes : Set (ℝ^2) := ⋃ j ∈ S_idx, T j
  set K : ℕ := S_idx.card
  let F : ℝ^2 → ℝ := fun p => ∑ j ∈ S_idx, (T j).indicator (fun _ => (1 : ℝ)) p
  have hF_int : IntegrableOn F U_tubes volume := by
    refine integrable_finsetSum S_idx fun j _ => ?_
    exact (integrableOn_const (C := (1 : ℝ)) (hs := hU_tubes_lt_top.ne)).indicator (hT_meas j)
  have hF2_int : IntegrableOn (fun p => F p ^ 2) U_tubes volume := by
    have hF_bdd : ∀ p, ‖F p‖ ≤ (K : ℝ) := fun p => by
      change |∑ j ∈ S_idx, (T j).indicator (fun _ => (1 : ℝ)) p| ≤ (K : ℝ)
      rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) p)]
      calc ∑ j ∈ S_idx, (T j).indicator (fun _ => (1 : ℝ)) p
          ≤ ∑ _j ∈ S_idx, (1 : ℝ) := Finset.sum_le_sum fun j _ => Set.indicator_le' (fun _ _ => le_rfl) (fun _ _ => zero_le_one) p
        _ = (K : ℝ) := by simp [K]
    have hmeasF : AEStronglyMeasurable F (volume.restrict U_tubes) :=
      Finset.aestronglyMeasurable_fun_sum S_idx fun j _ =>
        (measurable_const.indicator (hT_meas j)).aestronglyMeasurable
    exact IntegrableOn.of_bound hU_tubes_lt_top (hmeasF.pow 2) ((K : ℝ) ^ 2)
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_sq]
        have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
        exact sq_le_sq.mpr (by rw [abs_of_nonneg hK0]; exact hF_bdd p))
  have hIntF_eq : ∫ p in U_tubes, F p = ∑ j ∈ S_idx, (volume (T j)).toReal := by
    dsimp [F]
    rw [integral_finsetSum S_idx fun j _ =>
      (integrableOn_const (C := (1 : ℝ)) (hs := hU_tubes_lt_top.ne)).indicator (hT_meas j)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hinter : U_tubes ∩ T j = T j := Set.inter_eq_right.mpr (Set.subset_biUnion_of_mem hj)
    rw [setIntegral_indicator (hT_meas j), hinter]
    simp [Measure.real_def]
  have hIntF_lb : 2 / (Real.pi * (m : ℝ) ^ 4) ≤ ∫ p in U_tubes, F p := by
    rw [hIntF_eq]
    calc 2 / (Real.pi * (m : ℝ) ^ 4)
        = ((N : ℝ) / (Real.pi * (m : ℝ) ^ 2)) * (2 * δ / (m : ℝ) ^ 2) := by
          have : (N : ℝ) * δ = 1 := hN_δ
          field_simp; nlinarith [Real.pi_pos]
      _ ≤ (K : ℝ) * (2 * δ / (m : ℝ) ^ 2) := by gcongr
      _ = ∑ _j ∈ S_idx, (2 * δ / (m : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ S_idx, (volume (T j)).toReal := Finset.sum_le_sum hT_vol_lb
  have hIntF2_eq : ∫ p in U_tubes, F p ^ 2 =
      ∑ j₁ ∈ S_idx, ∑ j₂ ∈ S_idx, (volume (T j₁ ∩ T j₂)).toReal := by
    have hF2_eq : (fun p => F p ^ 2) = fun p =>
        ∑ j₁ ∈ S_idx, ∑ j₂ ∈ S_idx, (T j₁ ∩ T j₂).indicator (fun _ => (1 : ℝ)) p := by
      ext p
      dsimp [F]
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
      by_cases h1 : p ∈ T j₁ <;> by_cases h2 : p ∈ T j₂ <;> simp [h1, h2]
    rw [hF2_eq, integral_finsetSum S_idx fun j₁ _ => by
      refine integrable_finsetSum S_idx fun j₂ _ => ?_
      exact (integrableOn_const (C := (1 : ℝ)) (hs := hU_tubes_lt_top.ne)).indicator ((hT_meas j₁).inter (hT_meas j₂))]
    refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
    rw [integral_finsetSum S_idx fun j₂ _ =>
      (integrableOn_const (C := (1 : ℝ)) (hs := hU_tubes_lt_top.ne)).indicator ((hT_meas j₁).inter (hT_meas j₂))]
    refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
    have hinter : U_tubes ∩ (T j₁ ∩ T j₂) = T j₁ ∩ T j₂ :=
      Set.inter_eq_right.mpr (Set.inter_subset_left.trans (Set.subset_biUnion_of_mem hj₁))
    rw [setIntegral_indicator ((hT_meas j₁).inter (hT_meas j₂)), hinter]
    simp [Measure.real_def]
  have hIntF2_ub : ∫ p in U_tubes, F p ^ 2 ≤ 21 * (m : ℝ) := by
    rw [hIntF2_eq]
    have hrow : ∀ j₁ ∈ S_idx, ∑ j₂ ∈ S_idx, (volume (T j₁ ∩ T j₂)).toReal ≤
        2 * δ + 16 * δ * (1 + (m : ℝ)) := by
      intro j₁ hj₁
      rw [← Finset.add_sum_erase S_idx _ hj₁, Set.inter_self]
      have hdiag : (volume (T j₁)).toReal ≤ 2 * δ := hT_vol_ub j₁
      have hoff : ∑ j₂ ∈ S_idx.erase j₁, (volume (T j₁ ∩ T j₂)).toReal ≤
          16 * δ * (1 + (m : ℝ)) := by
        have hsum_ub : ∑ j₂ ∈ S_idx.erase j₁, (volume (T j₁ ∩ T j₂)).toReal ≤
            ∑ j₂ ∈ S_idx.erase j₁, 8 * δ / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| :=
          Finset.sum_le_sum fun j₂ hj₂ =>
            hT_inter_ub j₁ hj₁ j₂ (Finset.mem_of_mem_erase hj₂) (Finset.ne_of_mem_erase hj₂).symm
        have hrec_sum : ∑ j₂ ∈ S_idx.erase j₁, (1 : ℝ) / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| ≤
            2 * (1 + (m : ℝ)) := by
          let S_lt := (S_idx.erase j₁).filter (fun j₂ : Fin N => j₂.1 < j₁.1)
          let S_gt := (S_idx.erase j₁).filter (fun j₂ : Fin N => j₁.1 < j₂.1)
          have hsplit : S_idx.erase j₁ = S_lt ∪ S_gt := by
            ext j₂
            simp only [S_lt, S_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro ⟨hne, hj₂⟩
              rcases lt_trichotomy j₂.1 j₁.1 with h | h | h
              · exact Or.inl ⟨⟨hne, hj₂⟩, h⟩
              · exact absurd (Fin.ext h) hne
              · exact Or.inr ⟨⟨hne, hj₂⟩, h⟩
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          have hdisj : Disjoint S_lt S_gt := by
            rw [Finset.disjoint_left]
            intro j₂ h1 h2
            simp only [S_lt, S_gt, Finset.mem_filter] at h1 h2
            omega
          rw [hsplit, Finset.sum_union hdisj]
          have hlt_bound : ∑ j₂ ∈ S_lt, (1 : ℝ) / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| ≤ 1 + (m : ℝ) := by
            have hrew : ∑ j₂ ∈ S_lt, (1 : ℝ) / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| =
                ∑ d ∈ S_lt.image (fun j₂ => j₁.1 - j₂.1), (1 : ℝ) / (d : ℝ) := by
              rw [Finset.sum_image]
              · refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
                simp only [S_lt, Finset.mem_filter] at hj₂
                have hlt : (j₂.1 : ℝ) < (j₁.1 : ℝ) := Nat.cast_lt.mpr hj₂.2
                rw [abs_of_pos (sub_pos.mpr hlt), Nat.cast_sub hj₂.2.le]
              · intro j₂ hj₂ j₃ hj₃ heq
                simp only [S_lt, Finset.coe_filter, Set.mem_ofPred_eq] at hj₂ hj₃
                dsimp only at heq
                exact Fin.ext (by omega)
            rw [hrew]
            refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans (harmonic_dyadic_bound m)
            intro d hd
            obtain ⟨j₂, hj₂, rfl⟩ := Finset.mem_image.mp hd
            simp only [S_lt, Finset.mem_filter] at hj₂
            simp only [Finset.mem_Icc]
            exact ⟨by omega, by have := j₁.2; rw [← hN]; omega⟩
          have hgt_bound : ∑ j₂ ∈ S_gt, (1 : ℝ) / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| ≤ 1 + (m : ℝ) := by
            have hrew : ∑ j₂ ∈ S_gt, (1 : ℝ) / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| =
                ∑ d ∈ S_gt.image (fun j₂ => j₂.1 - j₁.1), (1 : ℝ) / (d : ℝ) := by
              rw [Finset.sum_image]
              · refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
                simp only [S_gt, Finset.mem_filter] at hj₂
                have hlt : (j₁.1 : ℝ) < (j₂.1 : ℝ) := Nat.cast_lt.mpr hj₂.2
                rw [abs_of_neg (sub_neg.mpr hlt), neg_sub, Nat.cast_sub hj₂.2.le]
              · intro j₂ hj₂ j₃ hj₃ heq
                simp only [S_gt, Finset.coe_filter, Set.mem_ofPred_eq] at hj₂ hj₃
                dsimp only at heq
                exact Fin.ext (by omega)
            rw [hrew]
            refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans (harmonic_dyadic_bound m)
            intro d hd
            obtain ⟨j₂, hj₂, rfl⟩ := Finset.mem_image.mp hd
            simp only [S_gt, Finset.mem_filter] at hj₂
            simp only [Finset.mem_Icc]
            exact ⟨by omega, by have := j₂.2; rw [← hN]; omega⟩
          linarith
        calc ∑ j₂ ∈ S_idx.erase j₁, (volume (T j₁ ∩ T j₂)).toReal
            ≤ ∑ j₂ ∈ S_idx.erase j₁, 8 * δ * (1 / |((j₁.1 : ℝ) - (j₂.1 : ℝ))|) := by
              simp only [mul_one_div]; exact hsum_ub
          _ = 8 * δ * ∑ j₂ ∈ S_idx.erase j₁, (1 : ℝ) / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| := by
              rw [Finset.mul_sum]
          _ ≤ 8 * δ * (2 * (1 + (m : ℝ))) := by gcongr
          _ = 16 * δ * (1 + (m : ℝ)) := by ring
      linarith
    have hK_le_N : (K : ℝ) ≤ (N : ℝ) := by
      have : K ≤ Fintype.card (Fin N) := Finset.card_le_univ S_idx
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    calc ∑ j₁ ∈ S_idx, ∑ j₂ ∈ S_idx, (volume (T j₁ ∩ T j₂)).toReal
        ≤ ∑ _j₁ ∈ S_idx, (2 * δ + 16 * δ * (1 + (m : ℝ))) := Finset.sum_le_sum hrow
      _ = (K : ℝ) * (2 * δ + 16 * δ * (1 + (m : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * δ + 16 * δ * (1 + (m : ℝ))) := by gcongr
      _ = 2 * ((N : ℝ) * δ) + 16 * ((N : ℝ) * δ) * (1 + (m : ℝ)) := by ring
      _ = 2 + 16 * (1 + (m : ℝ)) := by rw [hN_δ]; ring
      _ ≤ 21 * (m : ℝ) := by
          have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
          linarith
  have hCS := cauchy_schwarz_finite hU_tubes_lt_top hF_int hF2_int
  have hvol_lb : 4 / (21 * Real.pi ^ 2 * (m : ℝ) ^ 9) ≤ (volume U_tubes).toReal := by
    have h1 : (2 / (Real.pi * (m : ℝ) ^ 4)) ^ 2 ≤ (21 * (m : ℝ)) * (volume U_tubes).toReal := by
      calc (2 / (Real.pi * (m : ℝ) ^ 4)) ^ 2
          ≤ (∫ p in U_tubes, F p) ^ 2 := by gcongr
        _ ≤ (∫ p in U_tubes, F p ^ 2) * (volume U_tubes).toReal := hCS
        _ ≤ (21 * (m : ℝ)) * (volume U_tubes).toReal := by gcongr
    rw [div_pow, div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    have hmul : (21 * (m : ℝ)) * (volume U_tubes).toReal * (Real.pi * (m : ℝ) ^ 4) ^ 2 =
        (volume U_tubes).toReal * (21 * Real.pi ^ 2 * (m : ℝ) ^ 9) := by ring
    linarith
  have hvol_ub : (volume U_tubes).toReal ≤ 64 * (2 : ℝ) ^ (-(2 - s) * (m : ℝ)) := by
    have h2s_le : (2 : ℝ) ^ s ≤ 4 := by
      calc (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_lt_two.le
        _ = 4 := by norm_num
    have hδ_sq : δ ^ 2 = (2 : ℝ) ^ (-2 * (m : ℝ)) := by
      rw [hδ, ← Real.rpow_intCast, ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul (by norm_num)]
      congr 1; push_cast; ring
    calc (volume U_tubes).toReal
        ≤ (A_card : ℝ) * (16 * δ ^ 2) := hU_tubes_vol_ub
      _ ≤ ((2 : ℝ) ^ s * (2 : ℝ) ^ ((m : ℝ) * s)) * (16 * (2 : ℝ) ^ (-2 * (m : ℝ))) := by
          rw [← hδ_sq]; gcongr
      _ ≤ (4 * (2 : ℝ) ^ ((m : ℝ) * s)) * (16 * (2 : ℝ) ^ (-2 * (m : ℝ))) := by gcongr
      _ = 64 * ((2 : ℝ) ^ ((m : ℝ) * s) * (2 : ℝ) ^ (-2 * (m : ℝ))) := by ring
      _ = 64 * (2 : ℝ) ^ (-(2 - s) * (m : ℝ)) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 2; ring
  have hcontra : (2 : ℝ) ^ ((2 - s) * (m : ℝ)) ≤ 336 * Real.pi ^ 2 * (m : ℝ) ^ 9 := by
    have hcomb := hvol_lb.trans hvol_ub
    rw [neg_mul, Real.rpow_neg (by norm_num), ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (by positivity)] at hcomb
    have h2 : 4 * (2 : ℝ) ^ ((2 - s) * (m : ℝ)) ≤ 64 * (21 * Real.pi ^ 2 * (m : ℝ) ^ 9) := by
      linarith
    linarith
  exact absurd hexp hcontra.not_gt

lemma kakeya_contradiction_of_m
    (m : ℕ) (hm4 : 4 ≤ m) (s : ℝ) (hs_lt_two : s < 2)
    (A_fin : Finset ℕ) (x : ℕ → ℝ^2) (r : ℕ → ℝ)
    (hA_card : (A_fin.card : ℝ) ≤ (2 : ℝ) ^ s * (2 : ℝ) ^ ((m : ℝ) * s))
    (hr_le : ∀ k ∈ A_fin, r k ≤ (2 : ℝ) ^ (-(m : ℤ)))
    (a : ℝ → ℝ^2) (I : ℝ → Set ℝ)
    (hI_meas : ∀ θ, MeasurableSet (I θ))
    (hI_sub : ∀ θ, I θ ⊆ Set.Icc (0 : ℝ) 1)
    (hI_cov : ∀ θ, ∀ t ∈ I θ, ∃ k ∈ A_fin, a θ + t • v θ ∈ Metric.ball (x k) (r k))
    (Θ : Set ℝ)
    (hΘ_sub : Θ ⊆ Set.Ico (0 : ℝ) (Real.pi / 2))
    (hΘ_vol : ENNReal.ofReal (1 / (m : ℝ) ^ 2) ≤ volume Θ)
    (hΘ_I : ∀ θ ∈ Θ, 1 / (m : ℝ) ^ 2 ≤ (volume (I θ)).toReal)
    (hexp : 336 * Real.pi ^ 2 * (m : ℝ) ^ 9 < (2 : ℝ) ^ ((2 - s) * (m : ℝ))) : False := by
  classical
  have hm_pos : (0 : ℝ) < m := by positivity
  set δ : ℝ := (2 : ℝ) ^ (-(m : ℤ))
  have hδ_pos : 0 < δ := by positivity
  set N : ℕ := 2 ^ m
  have hN_pos : 0 < N := pow_pos (by norm_num) m
  have hN_δ : (N : ℝ) * δ = 1 := by
    dsimp [N, δ]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
    norm_num
  obtain ⟨S_idx, θ, hK_ge, hθ_mem, hsin_lb⟩ :=
    well_separated_angles m hm4 N δ hδ_pos hN_δ Θ hΘ_sub hΘ_vol
  set K : ℕ := S_idx.card
  let Φ : Fin N → ℝ^2 → ℝ^2 := fun j p => a (θ j) + orthoMap (θ j) p
  let T : Fin N → Set (ℝ^2) := fun j => Φ j '' box2 (I (θ j)) (Set.Icc (-δ) δ)
  let R : Fin N → Set (ℝ^2) := fun j => Φ j '' box2 (Set.Icc 0 1) (Set.Icc (-δ) δ)
  have hT_sub_R : ∀ j, T j ⊆ R j := fun j =>
    Set.image_mono fun p hp => ⟨hI_sub (θ j) hp.1, hp.2⟩
  have hT_meas : ∀ j, MeasurableSet (T j) := fun j => by
    have hbox : MeasurableSet (box2 (I (θ j)) (Set.Icc (-δ) δ)) :=
      measurableSet_box2 (hI_meas (θ j)) measurableSet_Icc
    let e_lin : ℝ^2 ≃ₗ[ℝ] ℝ^2 :=
      LinearMap.equivOfDetNeZero (orthoMap (θ j)) (by rw [det_orthoMap]; norm_num)
    let e_homeo : ℝ^2 ≃ₜ ℝ^2 :=
      e_lin.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft (a (θ j)))
    have heq : Φ j '' box2 (I (θ j)) (Set.Icc (-δ) δ) =
        e_homeo '' box2 (I (θ j)) (Set.Icc (-δ) δ) := by
      ext p; simp [Φ, e_homeo, e_lin]
    dsimp [T]
    rw [heq]
    exact e_homeo.measurableEmbedding.measurableSet_image.mpr hbox
  let U_tubes : Set (ℝ^2) := ⋃ j ∈ S_idx, T j
  have hU_tubes_vol_le : volume U_tubes ≤ ENNReal.ofReal ((A_fin.card : ℝ) * (16 * δ ^ 2)) := by
    have hcov : U_tubes ⊆ ⋃ k ∈ A_fin,
        {p : ℝ^2 | |p 0 - (x k) 0| ≤ 2 * δ ∧ |p 1 - (x k) 1| ≤ 2 * δ} := by
      intro p hp
      obtain ⟨j, _, q, hq, rfl⟩ := Set.mem_iUnion₂.mp hp
      have hq0 : q 0 ∈ I (θ j) := hq.1
      have hq1 : q 1 ∈ Set.Icc (-δ) δ := hq.2
      obtain ⟨k, hk_fin, hball⟩ := hI_cov (θ j) (q 0) hq0
      refine Set.mem_biUnion hk_fin ?_
      have hrk_le : r k ≤ δ := hr_le k hk_fin
      have hdist1 : dist (a (θ j) + q 0 • v (θ j)) (x k) < δ :=
        lt_of_lt_of_le (Metric.mem_ball.mp hball) hrk_le
      have hdist2 : ‖q 1 • vPerp (θ j)‖ ≤ δ := by
        rw [norm_smul, Real.norm_eq_abs]
        have hvp : ‖vPerp (θ j)‖ = 1 := by
          rw [← Real.sqrt_one, ← inner_vPerp_self (θ j), real_inner_self_eq_norm_sq,
            Real.sqrt_sq (norm_nonneg _)]
        rw [hvp, mul_one, abs_le]
        exact hq1
      have hΦ_eq : Φ j q = (a (θ j) + q 0 • v (θ j)) + q 1 • vPerp (θ j) := by
        change a (θ j) + (q 0 • v (θ j) + q 1 • vPerp (θ j)) =
          (a (θ j) + q 0 • v (θ j)) + q 1 • vPerp (θ j)
        rw [add_assoc]
      have hdist_total : dist (Φ j q) (x k) ≤ 2 * δ := by
        rw [hΦ_eq, dist_eq_norm, add_sub_right_comm]
        calc ‖(a (θ j) + q 0 • v (θ j) - x k) + q 1 • vPerp (θ j)‖
            ≤ ‖a (θ j) + q 0 • v (θ j) - x k‖ + ‖q 1 • vPerp (θ j)‖ := norm_add_le _ _
          _ ≤ δ + δ := add_le_add hdist1.le hdist2
          _ = 2 * δ := by ring
      have hcoord_le : ∀ i : Fin 2, |(Φ j q) i - (x k) i| ≤ ‖Φ j q - x k‖ := fun i => by
        simpa [PiLp.sub_apply] using PiLp.norm_apply_le (Φ j q - x k) i
      rw [dist_eq_norm] at hdist_total
      exact ⟨(hcoord_le 0).trans hdist_total, (hcoord_le 1).trans hdist_total⟩
    have hvol_le : volume U_tubes ≤ ∑ k ∈ A_fin,
        volume {p : ℝ^2 | |p 0 - (x k) 0| ≤ 2 * δ ∧ |p 1 - (x k) 1| ≤ 2 * δ} :=
      (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    have hsq_eq : ∀ k ∈ A_fin,
        volume {p : ℝ^2 | |p 0 - (x k) 0| ≤ 2 * δ ∧ |p 1 - (x k) 1| ≤ 2 * δ} =
        ENNReal.ofReal (4 * (2 * δ) ^ 2) := fun k _ => volume_square (x k) (by positivity)
    rw [Finset.sum_congr rfl hsq_eq, Finset.sum_const, nsmul_eq_mul] at hvol_le
    calc volume U_tubes
        ≤ (A_fin.card : ℝ≥0∞) * ENNReal.ofReal (4 * (2 * δ) ^ 2) := hvol_le
      _ = ENNReal.ofReal (A_fin.card : ℝ) * ENNReal.ofReal (4 * (2 * δ) ^ 2) := by
          rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ((A_fin.card : ℝ) * (16 * δ ^ 2)) := by
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; ring
  have hU_tubes_lt_top : volume U_tubes < ⊤ := lt_of_le_of_lt hU_tubes_vol_le ENNReal.ofReal_lt_top
  have hU_tubes_vol_ub : (volume U_tubes).toReal ≤ (A_fin.card : ℝ) * (16 * δ ^ 2) :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hU_tubes_vol_le).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hT_vol : ∀ j, volume (T j) = volume (I (θ j)) * ENNReal.ofReal (2 * δ) := fun j => by
    have heq : T j = (fun p => a (θ j) + p) '' (orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ)) := by
      dsimp [T, Φ]
      rw [Set.image_image]
    rw [heq]
    have hadd : volume ((fun p => a (θ j) + p) ''
        (orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ))) =
        volume (orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ)) := by
      have hmeas_img : MeasurableSet (orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ)) := by
        let e_lin : ℝ^2 ≃ₗ[ℝ] ℝ^2 :=
          LinearMap.equivOfDetNeZero (orthoMap (θ j)) (by rw [det_orthoMap]; norm_num)
        have heq_lin : orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ) =
            e_lin '' box2 (I (θ j)) (Set.Icc (-δ) δ) := rfl
        rw [heq_lin]
        exact e_lin.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
          (measurableSet_box2 (hI_meas (θ j)) measurableSet_Icc)
      have himg_pre : (fun p => a (θ j) + p) ''
          (orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ)) =
          (fun p => -a (θ j) + p) ⁻¹' (orthoMap (θ j) '' box2 (I (θ j)) (Set.Icc (-δ) δ)) := by
        ext p
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨q, hq, rfl⟩
          simpa [add_assoc] using hq
        · intro hp
          exact ⟨-a (θ j) + p, hp, by simp⟩
      rw [himg_pre]
      exact (measurePreserving_add_left volume (-a (θ j))).measure_preimage hmeas_img.nullMeasurableSet
    rw [hadd, Measure.addHaar_image_linearMap volume (orthoMap (θ j)), det_orthoMap]
    simp only [abs_one, ENNReal.ofReal_one, one_mul]
    rw [volume_box2 (hI_meas (θ j)) measurableSet_Icc, Real.volume_Icc]
    congr 2; ring
  have hT_vol_lb : ∀ j ∈ S_idx, 2 * δ / (m : ℝ) ^ 2 ≤ (volume (T j)).toReal := fun j hj => by
    rw [hT_vol j, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hI_lb : 1 / (m : ℝ) ^ 2 ≤ (volume (I (θ j))).toReal := hΘ_I (θ j) (hθ_mem j hj)
    calc 2 * δ / (m : ℝ) ^ 2 = (1 / (m : ℝ) ^ 2) * (2 * δ) := by ring
      _ ≤ (volume (I (θ j))).toReal * (2 * δ) := by gcongr
  have hT_vol_ub : ∀ j, (volume (T j)).toReal ≤ 2 * δ := fun j => by
    rw [hT_vol j, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hI_ub : (volume (I (θ j))).toReal ≤ 1 := by
      have hle : volume (I (θ j)) ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono (hI_sub (θ j))
      have := ENNReal.toReal_mono (by simp) hle
      simpa using this
    calc (volume (I (θ j))).toReal * (2 * δ) ≤ 1 * (2 * δ) := by gcongr
      _ = 2 * δ := one_mul _
  have hT_inter_ub : ∀ j₁ ∈ S_idx, ∀ j₂ ∈ S_idx, j₁ ≠ j₂ →
      (volume (T j₁ ∩ T j₂)).toReal ≤ 8 * δ / |((j₁.1 : ℝ) - (j₂.1 : ℝ))| := by
    intro j₁ hj₁ j₂ hj₂ hne
    have hsin_pos : 0 < |Real.sin (θ j₂ - θ j₁)| := by
      have hne_real : (j₁.1 : ℝ) ≠ (j₂.1 : ℝ) := by exact_mod_cast Fin.val_ne_of_ne hne
      have hpos_diff : 0 < |((j₁.1 : ℝ) - (j₂.1 : ℝ))| := abs_pos.mpr (sub_ne_zero.mpr hne_real)
      have hlb := hsin_lb j₁ hj₁ j₂ hj₂ hne
      have : 0 < |((j₁.1 : ℝ) - (j₂.1 : ℝ))| * δ / 2 := by positivity
      linarith
    have hdet_ne : LinearMap.det (projMap (θ j₁) (θ j₂)) ≠ 0 := by
      rw [det_projMap]
      exact abs_pos.mp hsin_pos
    let L12 : ℝ^2 ≃ₗ[ℝ] ℝ^2 := LinearMap.equivOfDetNeZero (projMap (θ j₁) (θ j₂)) hdet_ne
    let c₁ : ℝ := inner ℝ (a (θ j₁)) (vPerp (θ j₁))
    let c₂ : ℝ := inner ℝ (a (θ j₂)) (vPerp (θ j₂))
    let B : Set (ℝ^2) := box2 (Set.Icc (c₁ - δ) (c₁ + δ)) (Set.Icc (c₂ - δ) (c₂ + δ))
    have hsub_pre : T j₁ ∩ T j₂ ⊆ L12 ⁻¹' B := fun p hp => by
      have hp1 : p ∈ R j₁ := hT_sub_R j₁ hp.1
      have hp2 : p ∈ R j₂ := hT_sub_R j₂ hp.2
      obtain ⟨q₁, hq₁, rfl⟩ := hp1
      obtain ⟨q₂, hq₂, hpeq⟩ := hp2
      have hcoord0 : inner ℝ (Φ j₁ q₁) (vPerp (θ j₁)) = c₁ + q₁ 1 := by
        change inner ℝ (a (θ j₁) + (q₁ 0 • v (θ j₁) + q₁ 1 • vPerp (θ j₁))) (vPerp (θ j₁)) = c₁ + q₁ 1
        dsimp [c₁]
        rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
          inner_v_vPerp, inner_vPerp_self]
        simp only [conj_trivial]
        ring
      have hcoord1 : inner ℝ (Φ j₁ q₁) (vPerp (θ j₂)) = c₂ + q₂ 1 := by
        rw [← hpeq]
        change inner ℝ (a (θ j₂) + (q₂ 0 • v (θ j₂) + q₂ 1 • vPerp (θ j₂))) (vPerp (θ j₂)) = c₂ + q₂ 1
        dsimp [c₂]
        rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
          inner_v_vPerp, inner_vPerp_self]
        simp only [conj_trivial]
        ring
      simp only [Set.mem_preimage, B, box2, Set.mem_ofPred_eq, Set.mem_Icc]
      change inner ℝ (Φ j₁ q₁) (vPerp (θ j₁)) ∈ Set.Icc (c₁ - δ) (c₁ + δ) ∧
             inner ℝ (Φ j₁ q₁) (vPerp (θ j₂)) ∈ Set.Icc (c₂ - δ) (c₂ + δ)
      rw [hcoord0, hcoord1]
      exact ⟨⟨by linarith [hq₁.2.1], by linarith [hq₁.2.2]⟩,
             ⟨by linarith [hq₂.2.1], by linarith [hq₂.2.2]⟩⟩
    have hvol_pre : volume (L12 ⁻¹' B) = ENNReal.ofReal (4 * δ ^ 2 / |Real.sin (θ j₂ - θ j₁)|) := by
      rw [Measure.addHaar_preimage_linearEquiv volume L12 B]
      have hdet_symm : LinearMap.det (L12.symm : ℝ^2 →ₗ[ℝ] ℝ^2) = (Real.sin (θ j₂ - θ j₁))⁻¹ := by
        rw [LinearEquiv.det_coe_symm]
        change (LinearMap.det (projMap (θ j₁) (θ j₂)))⁻¹ = _
        rw [det_projMap]
      rw [hdet_symm, abs_inv]
      have hvolB : volume B = ENNReal.ofReal (4 * δ ^ 2) := by
        dsimp [B]
        rw [volume_box2 measurableSet_Icc measurableSet_Icc, Real.volume_Icc, Real.volume_Icc]
        rw [show c₁ + δ - (c₁ - δ) = 2 * δ by ring, show c₂ + δ - (c₂ - δ) = 2 * δ by ring,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      rw [hvolB, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    have hvol_inter : volume (T j₁ ∩ T j₂) ≤ ENNReal.ofReal (4 * δ ^ 2 / |Real.sin (θ j₂ - θ j₁)|) :=
      (measure_mono hsub_pre).trans hvol_pre.le
    have hreal_inter : (volume (T j₁ ∩ T j₂)).toReal ≤ 4 * δ ^ 2 / |Real.sin (θ j₂ - θ j₁)| := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_inter
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    refine hreal_inter.trans ?_
    have hlb := hsin_lb j₁ hj₁ j₂ hj₂ hne
    have hne_real : (j₁.1 : ℝ) ≠ (j₂.1 : ℝ) := by exact_mod_cast Fin.val_ne_of_ne hne
    have hpos_diff : 0 < |((j₁.1 : ℝ) - (j₂.1 : ℝ))| := abs_pos.mpr (sub_ne_zero.mpr hne_real)
    rw [div_le_div_iff₀ hsin_pos (by positivity)]
    calc 4 * δ ^ 2 * |((j₁.1 : ℝ) - (j₂.1 : ℝ))|
        = 8 * δ * (|((j₁.1 : ℝ) - (j₂.1 : ℝ))| * δ / 2) := by ring
      _ ≤ 8 * δ * |Real.sin (θ j₂ - θ j₁)| := by gcongr
  exact cauchy_schwarz_step m hm4 s hs_lt_two N rfl δ rfl hδ_pos hN_δ (A_fin.card : ℝ) hA_card
    S_idx T hT_meas hK_ge hU_tubes_vol_ub hU_tubes_lt_top hT_vol_lb hT_vol_ub hT_inter_ub hexp

lemma two_le_dimH (S : Set (ℝ^2)) (hS : Kakeya.IsKakeya S) : 2 ≤ dimH S := by
  classical
  by_contra hlt
  push Not at hlt
  have hne_top : dimH S ≠ ⊤ := (lt_trans hlt (by norm_num)).ne
  have htoReal_lt : (dimH S).toReal < 2 := by
    have := ENNReal.toReal_strict_mono (by norm_num) hlt
    simpa using this
  set s_val : ℝ := max 1 (((dimH S).toReal + 2) / 2)
  have hs_pos : 0 < s_val := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hs_lt_two : s_val < 2 := max_lt (by norm_num) (by linarith)
  set s : NNReal := ⟨s_val, hs_pos.le⟩
  have hs_coe : (s : ℝ) = s_val := rfl
  have hdim_lt_s : dimH S < (s : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hne_top, ENNReal.coe_nnreal_eq]
    refine ENNReal.ofReal_lt_ofReal_iff (hs_coe ▸ hs_pos) |>.mpr ?_
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hμ0 : μH[(s : ℝ)] S = 0 := by
    by_contra hne0
    exact absurd (le_dimH_of_hausdorffMeasure_ne_zero hne0) hdim_lt_s.not_ge
  obtain ⟨M₁, hM₁_ge, hM₁⟩ := exp_beats_poly (2 - (s : ℝ)) (336 * Real.pi ^ 2) (by linarith)
  obtain ⟨M₂, hM₂_ge, hM₂⟩ := geom_tail_lt (s : ℝ) hs_pos
  set M : ℕ := max M₁ M₂
  have hM4 : 4 ≤ M := le_trans hM₁_ge (le_max_left _ _)
  have hM_exp : ∀ m ≥ M, 336 * Real.pi ^ 2 * (m : ℝ) ^ 9 < (2 : ℝ) ^ ((2 - (s : ℝ)) * m) :=
    fun m hm => hM₁ m (le_trans (le_max_left _ _) hm)
  have hM_geom : (2 : ℝ) ^ (s : ℝ) * (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) /
      (1 - (2 : ℝ) ^ (-(s : ℝ))) < 1 / 4 := by
    have hq0 : 0 < (2 : ℝ) ^ (-(s : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hq1 : (2 : ℝ) ^ (-(s : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs_pos)
    have hpow_le : (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) ≤
        (2 : ℝ) ^ (-((M₂ + 3 : ℕ) : ℝ) * (s : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hM2_le : (M₂ : ℝ) ≤ M := by exact_mod_cast le_max_right M₁ M₂
      push_cast
      nlinarith [hs_pos]
    have hden : 0 < 1 - (2 : ℝ) ^ (-(s : ℝ)) := sub_pos.mpr hq1
    calc (2 : ℝ) ^ (s : ℝ) * (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) / (1 - (2 : ℝ) ^ (-(s : ℝ)))
        ≤ (2 : ℝ) ^ (s : ℝ) * (2 : ℝ) ^ (-((M₂ + 3 : ℕ) : ℝ) * (s : ℝ)) / (1 - (2 : ℝ) ^ (-(s : ℝ))) := by
          gcongr
      _ < 1 / 4 := hM₂
  set r₀ : ℝ := (2 : ℝ) ^ (-(M : ℤ))
  have hr₀_pos : 0 < r₀ := by positivity
  have hinf_lt : (⨅ (t : ℕ → Set (ℝ^2)) (_ : S ⊆ ⋃ k, t k)
      (_ : ∀ k, ediam (t k) ≤ ENNReal.ofReal (r₀ / 2)),
      ∑' k, ⨆ (_ : (t k).Nonempty), ediam (t k) ^ (s : ℝ)) <
      ENNReal.ofReal (1 / (4 * (2 : ℝ) ^ (s : ℝ))) := by
    have h0 : (⨅ (t : ℕ → Set (ℝ^2)) (_ : S ⊆ ⋃ k, t k)
        (_ : ∀ k, ediam (t k) ≤ ENNReal.ofReal (r₀ / 2)),
        ∑' k, ⨆ (_ : (t k).Nonempty), ediam (t k) ^ (s : ℝ)) ≤ μH[(s : ℝ)] S := by
      rw [Measure.hausdorffMeasure_apply]
      exact le_iSup_of_le (ENNReal.ofReal (r₀ / 2))
        (le_iSup_of_le (ENNReal.ofReal_pos.mpr (by positivity)) le_rfl)
    rw [hμ0] at h0
    exact lt_of_le_of_lt h0 (ENNReal.ofReal_pos.mpr (by positivity))
  simp only [iInf_lt_iff] at hinf_lt
  obtain ⟨t, ht_cov, ht_diam, ht_sum⟩ := hinf_lt
  let x : ℕ → ℝ^2 := fun k => if h : (t k).Nonempty then h.some else 0
  let r : ℕ → ℝ := fun k =>
    (if (t k).Nonempty then (ediam (t k)).toReal else 0) + (2 : ℝ) ^ (-(M + k + 3 : ℤ))
  have hr_pos : ∀ k, 0 < r k := fun k => by
    dsimp [r]
    have : 0 ≤ if (t k).Nonempty then (ediam (t k)).toReal else 0 := by
      split_ifs <;> positivity
    positivity
  have hr_le : ∀ k, r k ≤ r₀ := fun k => by
    dsimp [r]
    have h1 : (if (t k).Nonempty then (ediam (t k)).toReal else 0) ≤ r₀ / 2 := by
      split_ifs
      · exact ENNReal.toReal_le_of_le_ofReal (by positivity) (ht_diam k)
      · positivity
    have h2 : (2 : ℝ) ^ (-(M + k + 3 : ℤ)) ≤ r₀ / 2 := by
      rw [show r₀ / 2 = (2 : ℝ) ^ (-(M + 1 : ℤ)) by
        dsimp [r₀]
        rw [show -(M + 1 : ℤ) = -(M : ℤ) + (-1 : ℤ) by omega, zpow_add₀ (by norm_num)]
        norm_num
        ring]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have ht_sub_ball : ∀ k, t k ⊆ Metric.ball (x k) (r k) := fun k y hy => by
    have hne : (t k).Nonempty := ⟨y, hy⟩
    have hxk : x k ∈ t k := by
      dsimp [x]
      rw [dif_pos hne]
      exact hne.some_mem
    rw [Metric.mem_ball, dist_edist]
    have hed : edist y (x k) ≤ ediam (t k) := edist_le_ediam_of_mem hy hxk
    have hne_top : ediam (t k) ≠ ⊤ :=
      (lt_of_le_of_lt (ht_diam k) ENNReal.ofReal_lt_top).ne
    have hle_toReal : edist y (x k) ≤ ENNReal.ofReal (ediam (t k)).toReal := by
      rwa [ENNReal.ofReal_toReal hne_top]
    have hdist_le : (edist y (x k)).toReal ≤ (ediam (t k)).toReal :=
      ENNReal.toReal_le_of_le_ofReal ENNReal.toReal_nonneg hle_toReal
    have hrk_eq : r k = (ediam (t k)).toReal + (2 : ℝ) ^ (-(M + k + 3 : ℤ)) := by
      dsimp [r]; rw [if_pos hne]
    linarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (-(M + k + 3 : ℤ))]
  have hs_ne : (s : ℝ) ≠ 0 := hs_pos.ne'
  have ha_sum : (∑' k, (if (t k).Nonempty then (ediam (t k)).toReal else 0) ^ (s : ℝ)) <
      1 / (4 * (2 : ℝ) ^ (s : ℝ)) := by
    let f : ℕ → ℝ≥0∞ := fun k => ⨆ (_ : (t k).Nonempty), ediam (t k) ^ (s : ℝ)
    have hf_eq : ∀ k, (f k).toReal =
        (if (t k).Nonempty then (ediam (t k)).toReal else 0) ^ (s : ℝ) := fun k => by
      dsimp [f]
      by_cases hne : (t k).Nonempty
      · simp only [hne, ciSup_pos, if_pos]; rw [ENNReal.toReal_rpow]
      · simp [hne, Real.zero_rpow hs_ne]
    have hsum_ne_top : (∑' k, f k) ≠ ⊤ :=
      (lt_of_lt_of_le ht_sum le_top).ne
    have hle_tsum : (∑' k, (f k).toReal) ≤ (∑' k, f k).toReal := by
      refine Real.tsum_le_of_sum_range_le (fun _ => ENNReal.toReal_nonneg) fun n => ?_
      rw [← ENNReal.toReal_sum fun k _ => (ne_top_of_le_ne_top hsum_ne_top (ENNReal.le_tsum k))]
      exact ENNReal.toReal_mono hsum_ne_top (ENNReal.sum_le_tsum _)
    rw [← tsum_congr hf_eq]
    refine lt_of_le_of_lt hle_tsum ?_
    have hlt_real : (∑' k, f k).toReal < (ENNReal.ofReal (1 / (4 * (2 : ℝ) ^ (s : ℝ)))).toReal :=
      ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top ht_sum
    rwa [ENNReal.toReal_ofReal (by positivity)] at hlt_real
  have ha_summ : Summable (fun k => (if (t k).Nonempty then (ediam (t k)).toReal else 0) ^ (s : ℝ)) := by
    let f : ℕ → ℝ≥0∞ := fun k => ⨆ (_ : (t k).Nonempty), ediam (t k) ^ (s : ℝ)
    have hf_eq : ∀ k, (f k).toReal =
        (if (t k).Nonempty then (ediam (t k)).toReal else 0) ^ (s : ℝ) := fun k => by
      dsimp [f]
      by_cases hne : (t k).Nonempty
      · simp only [hne, ciSup_pos, if_pos]; rw [ENNReal.toReal_rpow]
      · simp [hne, Real.zero_rpow hs_ne]
    rw [← funext hf_eq]
    exact ENNReal.summable_toReal (lt_of_lt_of_le ht_sum le_top).ne
  have hb_summ : Summable (fun k : ℕ => ((2 : ℝ) ^ (-(M + k + 3 : ℤ))) ^ (s : ℝ)) := by
    have hq_eq : (fun k : ℕ => ((2 : ℝ) ^ (-(M + k + 3 : ℤ))) ^ (s : ℝ)) =
        fun k : ℕ => (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) * ((2 : ℝ) ^ (-(s : ℝ))) ^ k := by
      ext k
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(s : ℝ))) k, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hq_eq]
    refine Summable.mul_left _ (summable_geometric_of_lt_one ?_ ?_)
    · positivity
    · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs_pos)
  have hb_sum : (∑' k : ℕ, ((2 : ℝ) ^ (-(M + k + 3 : ℤ))) ^ (s : ℝ)) =
      (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) / (1 - (2 : ℝ) ^ (-(s : ℝ))) := by
    have hq_eq : (fun k : ℕ => ((2 : ℝ) ^ (-(M + k + 3 : ℤ))) ^ (s : ℝ)) =
        fun k : ℕ => (2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) * ((2 : ℝ) ^ (-(s : ℝ))) ^ k := by
      ext k
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(s : ℝ))) k, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; ring
    rw [hq_eq, tsum_mul_left]
    have hgeom : (∑' k : ℕ, ((2 : ℝ) ^ (-(s : ℝ))) ^ k) = (1 - (2 : ℝ) ^ (-(s : ℝ)))⁻¹ :=
      tsum_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs_pos))
    rw [hgeom]
    ring
  have hr_rpow_le : ∀ k, (r k) ^ (s : ℝ) ≤ (2 : ℝ) ^ (s : ℝ) *
      ((if (t k).Nonempty then (ediam (t k)).toReal else 0) ^ (s : ℝ) +
       ((2 : ℝ) ^ (-(M + k + 3 : ℤ))) ^ (s : ℝ)) := fun k => by
    set ak := if (t k).Nonempty then (ediam (t k)).toReal else 0
    set bk := (2 : ℝ) ^ (-(M + k + 3 : ℤ))
    have hak : 0 ≤ ak := by dsimp [ak]; split_ifs <;> positivity
    have hbk : 0 ≤ bk := by positivity
    have hsum_le : ak + bk ≤ 2 * max ak bk := by linarith [le_max_left ak bk, le_max_right ak bk]
    calc (r k) ^ (s : ℝ) = (ak + bk) ^ (s : ℝ) := rfl
      _ ≤ (2 * max ak bk) ^ (s : ℝ) := Real.rpow_le_rpow (by linarith) hsum_le hs_pos.le
      _ = (2 : ℝ) ^ (s : ℝ) * (max ak bk) ^ (s : ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ (2 : ℝ) ^ (s : ℝ) * (ak ^ (s : ℝ) + bk ^ (s : ℝ)) := by
          gcongr
          rcases le_total ak bk with h | h
          · rw [max_eq_right h]; linarith [Real.rpow_nonneg hak (s : ℝ)]
          · rw [max_eq_left h]; linarith [Real.rpow_nonneg hbk (s : ℝ)]
  have hr_summ : Summable (fun k => (r k) ^ (s : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (hr_pos k).le _) hr_rpow_le
      ((ha_summ.add hb_summ).mul_left _)
  have hr_sum_lt : (∑' k, (r k) ^ (s : ℝ)) < 1 / 2 := by
    have h1 := Summable.tsum_le_tsum hr_rpow_le hr_summ ((ha_summ.add hb_summ).mul_left _)
    rw [tsum_mul_left, Summable.tsum_add ha_summ hb_summ, hb_sum] at h1
    have h2s_pos : 0 < (2 : ℝ) ^ (s : ℝ) := by positivity
    have hbound1 : (2 : ℝ) ^ (s : ℝ) * (∑' k, (if (t k).Nonempty then (ediam (t k)).toReal else 0) ^ (s : ℝ)) < 1 / 4 := by
      calc (2 : ℝ) ^ (s : ℝ) * _ < (2 : ℝ) ^ (s : ℝ) * (1 / (4 * (2 : ℝ) ^ (s : ℝ))) := by gcongr
        _ = 1 / 4 := by field_simp
    have hbound2 : (2 : ℝ) ^ (s : ℝ) * ((2 : ℝ) ^ (-((M + 3 : ℕ) : ℝ) * (s : ℝ)) / (1 - (2 : ℝ) ^ (-(s : ℝ)))) < 1 / 4 := by
      rw [← mul_div_assoc]; exact hM_geom
    linarith
  -- Dyadic grouping
  let A : ℕ → Set ℕ := fun m => {k | (2 : ℝ) ^ (-(m + 1 : ℤ)) < r k ∧ r k ≤ (2 : ℝ) ^ (-(m : ℤ))}
  let U : ℕ → Set (ℝ^2) := fun m => ⋃ k ∈ A m, Metric.ball (x k) (r k)
  have hU_open : ∀ m, IsOpen (U m) := fun m =>
    isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hk_mem_A : ∀ k, ∃ m ≥ M, k ∈ A m := fun k => by
    have hex : ∃ n : ℕ, (2 : ℝ) ^ (-((M + n + 1 : ℕ) : ℤ)) < r k := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hr_pos k) (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨n, lt_of_le_of_lt ?_ hn⟩
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    let n₀ := Nat.find hex
    refine ⟨M + n₀, by omega, ?_, ?_⟩
    · exact Nat.find_spec hex
    · by_cases hn0 : n₀ = 0
      · rw [hn0, add_zero]
        exact hr_le k
      · have hprev : ¬ (2 : ℝ) ^ (-((M + (n₀ - 1) + 1 : ℕ) : ℤ)) < r k :=
          Nat.find_min hex (by omega)
        push Not at hprev
        rwa [show -((M + (n₀ - 1) + 1 : ℕ) : ℤ) = -((M + n₀ : ℕ) : ℤ) by omega] at hprev
  have hS_sub_U : S ⊆ ⋃ m : {m : ℕ // M ≤ m}, U m.1 := fun y hy => by
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (ht_cov hy)
    obtain ⟨m, hm, hkAm⟩ := hk_mem_A k
    exact Set.mem_iUnion.mpr ⟨⟨m, hm⟩, Set.mem_biUnion hkAm (ht_sub_ball k hk)⟩
  have hA_fin_card : ∀ m, (A m).Finite ∧ ((A m).ncard : ℝ) ≤ (2 : ℝ) ^ (s : ℝ) * (2 : ℝ) ^ ((m : ℝ) * (s : ℝ)) := by
    intro m
    have hfinset_bound : ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ A m →
        (F.card : ℝ) ≤ (2 : ℝ) ^ (s : ℝ) * (2 : ℝ) ^ ((m : ℝ) * (s : ℝ)) := by
      intro F hFA
      have hterm_le : ∀ k ∈ F, (2 : ℝ) ^ (-((m + 1 : ℤ) : ℝ) * (s : ℝ)) ≤ (r k) ^ (s : ℝ) := by
        intro k hkF
        have hkA := hFA hkF
        have h1 : (2 : ℝ) ^ (-(m + 1 : ℤ)) ≤ r k := hkA.1.le
        have h2 := Real.rpow_le_rpow (by positivity) h1 hs_pos.le
        rw [← hs_coe, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)] at h2
        simpa using h2
      have hsum_F : (F.card : ℝ) * (2 : ℝ) ^ (-((m + 1 : ℤ) : ℝ) * (s : ℝ)) ≤ 1 := by
        calc (F.card : ℝ) * (2 : ℝ) ^ (-((m + 1 : ℤ) : ℝ) * (s : ℝ))
            = ∑ _k ∈ F, (2 : ℝ) ^ (-((m + 1 : ℤ) : ℝ) * (s : ℝ)) := by simp [Finset.sum_const]
          _ ≤ ∑ k ∈ F, (r k) ^ (s : ℝ) := Finset.sum_le_sum hterm_le
          _ ≤ ∑' k, (r k) ^ (s : ℝ) := hr_summ.sum_le_tsum F (fun k _ => Real.rpow_nonneg (hr_pos k).le _)
          _ ≤ 1 := by linarith
      have hpow_pos : 0 < (2 : ℝ) ^ (-((m + 1 : ℤ) : ℝ) * (s : ℝ)) := by positivity
      have hdiv : (F.card : ℝ) ≤ 1 / (2 : ℝ) ^ (-((m + 1 : ℤ) : ℝ) * (s : ℝ)) :=
        (le_div_iff₀ hpow_pos).mpr hsum_F
      refine hdiv.trans_eq ?_
      rw [one_div, ← Real.rpow_neg (by norm_num)]
      rw [show -(-((m + 1 : ℤ) : ℝ) * (s : ℝ)) = (s : ℝ) + (m : ℝ) * (s : ℝ) by
        push_cast; ring]
      rw [Real.rpow_add (by norm_num)]
    have hfin : (A m).Finite := by
      by_contra hinf
      obtain ⟨N0, hN0⟩ := exists_nat_gt ((2 : ℝ) ^ (s : ℝ) * (2 : ℝ) ^ ((m : ℝ) * (s : ℝ)))
      obtain ⟨F, hFA, hFcard⟩ := (Set.Infinite.exists_subset_card_eq hinf N0)
      have hb := hfinset_bound F hFA
      rw [hFcard] at hb
      linarith
    refine ⟨hfin, ?_⟩
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact hfinset_bound hfin.toFinset (by simp)
  -- Directions & Pigeonhole
  have hseg : ∀ θ : ℝ, ∃ a : ℝ^2, ∀ t ∈ Set.Icc (0 : ℝ) 1, a + t • v θ ∈ S := fun θ => by
    obtain ⟨a, ha⟩ := hS (v θ) (norm_v θ)
    refine ⟨a, fun t ht => ha ?_⟩
    refine ⟨t, ht, ?_⟩
    simp only [AffineMap.lineMap_apply_module]
    module
  let a : ℝ → ℝ^2 := fun θ => (hseg θ).choose
  have ha_spec : ∀ θ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → a θ + t • v θ ∈ S :=
    fun θ t ht => (hseg θ).choose_spec t ht
  let I : ℕ → ℝ → Set ℝ := fun m θ => {t ∈ Set.Icc (0 : ℝ) 1 | a θ + t • v θ ∈ U m}
  have hI_meas : ∀ m θ, MeasurableSet (I m θ) := fun m θ => by
    refine measurableSet_Icc.inter ((hU_open m).measurableSet.preimage ?_)
    exact (continuous_const.add (continuous_id.smul continuous_const)).measurable
  have hm_of_ex : ∀ θ : ℝ, ∃ m : {m : ℕ // M ≤ m}, 1 / (m.1 : ℝ) ^ 2 ≤ (volume (I m.1 θ)).toReal := by
    intro θ
    by_contra hnone
    push Not at hnone
    have hcov_I : Set.Icc (0 : ℝ) 1 ⊆ ⋃ m : {m : ℕ // M ≤ m}, I m.1 θ := fun t ht => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hS_sub_U (ha_spec θ t ht))
      exact Set.mem_iUnion.mpr ⟨m, ht, hm⟩
    have hvol_le : volume (Set.Icc (0 : ℝ) 1) ≤ ∑' m : {m : ℕ // M ≤ m}, volume (I m.1 θ) :=
      (measure_mono hcov_I).trans (measure_iUnion_le _)
    have hI_lt : ∀ m : {m : ℕ // M ≤ m}, volume (I m.1 θ) ≤ ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2) :=
      fun m => (ENNReal.le_ofReal_iff_toReal_le
        (ne_top_of_le_ne_top (by simp) (measure_mono (fun _ h => h.1)))
        (by positivity)).mpr (hnone m).le
    have hsum_le : (∑' m : {m : ℕ // M ≤ m}, volume (I m.1 θ)) ≤
        ∑' m : {m : ℕ // M ≤ m}, ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2) :=
      ENNReal.tsum_le_tsum hI_lt
    have hsum_4 : (∑' m : {m : ℕ // M ≤ m}, ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2)) ≤
        ENNReal.ofReal (1 / 3) := by
      let f4 : {m : ℕ // 4 ≤ m} → ℝ≥0∞ := fun m => ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2)
      let g : {m : ℕ // M ≤ m} → {m : ℕ // 4 ≤ m} := fun m => ⟨m.1, le_trans hM4 m.2⟩
      have hg_inj : Function.Injective g := fun m₁ m₂ h => by
        cases m₁; cases m₂; simp only [g, Subtype.mk.injEq] at h; subst h; rfl
      have h1 : (∑' m : {m : ℕ // M ≤ m}, f4 (g m)) ≤ ∑' m : {m : ℕ // 4 ≤ m}, f4 m :=
        ENNReal.tsum_comp_le_tsum_of_injective hg_inj f4
      have hsumm4 : Summable (fun m : {m : ℕ // 4 ≤ m} => (1 : ℝ) / (m.1 : ℝ) ^ 2) :=
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).subtype _
      have h2 : (∑' m : {m : ℕ // 4 ≤ m}, f4 m) =
          ENNReal.ofReal (∑' m : {m : ℕ // 4 ≤ m}, (1 : ℝ) / (m.1 : ℝ) ^ 2) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsumm4]
      exact h1.trans (h2 ▸ ENNReal.ofReal_le_ofReal sum_inv_sq_ge_four_le)
    have h1_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 3) := by
      calc (1 : ℝ≥0∞) = volume (Set.Icc (0 : ℝ) 1) := by simp
        _ ≤ ENNReal.ofReal (1 / 3) := hvol_le.trans (hsum_le.trans hsum_4)
    have : (1 : ℝ) ≤ 1 / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1_le
      simpa using this
    linarith
  let m_of : ℝ → ℕ := fun θ => (hm_of_ex θ).choose.1
  have hm_of_ge : ∀ θ, M ≤ m_of θ := fun θ => (hm_of_ex θ).choose.2
  have hm_of_vol : ∀ θ, 1 / (m_of θ : ℝ) ^ 2 ≤ (volume (I (m_of θ) θ)).toReal :=
    fun θ => (hm_of_ex θ).choose_spec
  let Θ : ℕ → Set ℝ := fun m => {θ ∈ Set.Ico (0 : ℝ) (Real.pi / 2) | m_of θ = m}
  have hm_good_ex : ∃ m : {m : ℕ // M ≤ m}, ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2) ≤ volume (Θ m.1) := by
    by_contra hnone
    push Not at hnone
    have hcov_Θ : Set.Ico (0 : ℝ) (Real.pi / 2) ⊆ ⋃ m : {m : ℕ // M ≤ m}, Θ m.1 := fun θ hθ =>
      Set.mem_iUnion.mpr ⟨⟨m_of θ, hm_of_ge θ⟩, hθ, rfl⟩
    have hvol_le : volume (Set.Ico (0 : ℝ) (Real.pi / 2)) ≤
        ∑' m : {m : ℕ // M ≤ m}, volume (Θ m.1) :=
      (measure_mono hcov_Θ).trans (measure_iUnion_le _)
    have hsum_le : (∑' m : {m : ℕ // M ≤ m}, volume (Θ m.1)) ≤
        ∑' m : {m : ℕ // M ≤ m}, ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2) :=
      ENNReal.tsum_le_tsum fun m => (hnone m).le
    have hsum_4 : (∑' m : {m : ℕ // M ≤ m}, ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2)) ≤
        ENNReal.ofReal (1 / 3) := by
      let f4 : {m : ℕ // 4 ≤ m} → ℝ≥0∞ := fun m => ENNReal.ofReal (1 / (m.1 : ℝ) ^ 2)
      let g : {m : ℕ // M ≤ m} → {m : ℕ // 4 ≤ m} := fun m => ⟨m.1, le_trans hM4 m.2⟩
      have hg_inj : Function.Injective g := fun m₁ m₂ h => by
        cases m₁; cases m₂; simp only [g, Subtype.mk.injEq] at h; subst h; rfl
      have h1 : (∑' m : {m : ℕ // M ≤ m}, f4 (g m)) ≤ ∑' m : {m : ℕ // 4 ≤ m}, f4 m :=
        ENNReal.tsum_comp_le_tsum_of_injective hg_inj f4
      have hsumm4 : Summable (fun m : {m : ℕ // 4 ≤ m} => (1 : ℝ) / (m.1 : ℝ) ^ 2) :=
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).subtype _
      have h2 : (∑' m : {m : ℕ // 4 ≤ m}, f4 m) =
          ENNReal.ofReal (∑' m : {m : ℕ // 4 ≤ m}, (1 : ℝ) / (m.1 : ℝ) ^ 2) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsumm4]
      exact h1.trans (h2 ▸ ENNReal.ofReal_le_ofReal sum_inv_sq_ge_four_le)
    have hpi_le : ENNReal.ofReal (Real.pi / 2) ≤ ENNReal.ofReal (1 / 3) := by
      calc ENNReal.ofReal (Real.pi / 2) = volume (Set.Ico (0 : ℝ) (Real.pi / 2)) := by
            rw [Real.volume_Ico, sub_zero]
        _ ≤ ENNReal.ofReal (1 / 3) := hvol_le.trans (hsum_le.trans hsum_4)
    have hpi_real : Real.pi / 2 ≤ 1 / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpi_le
      rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at this
    linarith [Real.pi_gt_three]
  obtain ⟨⟨m, hm_ge⟩, hm_vol⟩ := hm_good_ex
  exact kakeya_contradiction_of_m m (le_trans hM4 hm_ge) (s : ℝ) hs_lt_two
    (hA_fin_card m).1.toFinset x r
    (by
      rw [← Set.ncard_eq_toFinset_card _ (hA_fin_card m).1]
      exact (hA_fin_card m).2)
    (fun k hk => (((hA_fin_card m).1.mem_toFinset).mp hk).2)
    a (I m) (hI_meas m) (fun θ _ ht => ht.1)
    (fun θ t ht => by
      obtain ⟨k, hkA, hball⟩ := Set.mem_iUnion₂.mp ht.2
      exact ⟨k, ((hA_fin_card m).1.mem_toFinset).mpr hkA, hball⟩)
    (Θ m) (fun θ hθ => hθ.1) hm_vol
    (fun θ hθ => by
      rw [← hθ.2]
      exact hm_of_vol θ)
    (hM_exp m hm_ge)

end Kakeya2DProof

theorem OMA.solution : type_of% @Kakeya.kakeya_2d := by
  intro S hS
  exact le_antisymm (Kakeya2DProof.dimH_le_two S) (Kakeya2DProof.two_le_dimH S hS)
