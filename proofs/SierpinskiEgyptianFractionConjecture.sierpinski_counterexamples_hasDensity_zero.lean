import FormalConjectures.Wikipedia.SierpinskiEgyptianFractionConjecture
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

-- Credit: @DavidLi-Waibibabo

namespace OMA.Sieve

open Filter

lemma totient_product_bound (P : Set ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    (((∏ p ∈ s, p.val).totient : ℕ) : ℝ) * (1 + ∑ p ∈ s, (p.val : ℝ)⁻¹) ≤
      (∏ p ∈ s, p.val : ℕ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    let q : ℕ := ∏ a ∈ s, a.val
    let z : ℝ := ∑ a ∈ s, (a.val : ℝ)⁻¹
    have hp := hP p.val p.property
    have hcop : p.val.Coprime q := by
      apply Nat.coprime_prod_right_iff.mpr
      intro a ha
      apply (Nat.coprime_primes hp (hP a.val a.property)).mpr
      intro he
      have hpa : p = a := Subtype.ext he
      exact hps (hpa.symm ▸ ha)
    have hp1 : 1 ≤ p.val := hp.one_lt.le
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    have hz : 0 ≤ z := Finset.sum_nonneg fun _ _ => by positivity
    have hz' : ((p.val : ℝ) - 1) * (1 + ((p.val : ℝ)⁻¹ + z)) ≤ (p.val : ℝ) * (1 + z) := by
      nlinarith [mul_inv_cancel₀ hp0.ne', inv_nonneg.mpr hp0.le]
    have hi : (q.totient : ℝ) * (1 + z) ≤ q := ih
    rw [Finset.prod_insert hps, Finset.sum_insert hps, Nat.totient_mul hcop, Nat.totient_prime hp]
    simp only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
    change ((p.val : ℝ) - 1) * (q.totient : ℝ) * (1 + ((p.val : ℝ)⁻¹ + z)) ≤ p.val * (q : ℝ)
    calc
      _ = q.totient * (((p.val : ℝ) - 1) * (1 + ((p.val : ℝ)⁻¹ + z))) := by ring
      _ ≤ q.totient * ((p.val : ℝ) * (1 + z)) := mul_le_mul_of_nonneg_left hz' (Nat.cast_nonneg _)
      _ = (p.val : ℝ) * ((q.totient : ℝ) * (1 + z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hi hp0.le

lemma count_coprime (q N : ℕ) (hq : 0 < q) :
    ((Finset.range N).filter (fun n => q.Coprime n)).card ≤
      (N / q + 1) * q.totient := by
  simpa only [zero_add, Nat.Ico_zero_eq_range, mul_comm q.totient] using
    (Nat.Ico_filter_coprime_le 0 N hq.ne')

lemma sieve_H1 (P : Set ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hdiv : ¬ Summable (fun p : P => ((p.val : ℝ)⁻¹))) :
    {n : ℕ | ∀ p ∈ P, ∀ k : ℕ, n ≠ p * (k + 1)}.HasDensity 0 := by
  classical
  let A : Set ℕ := {n | ∀ p ∈ P, ∀ k : ℕ, n ≠ p * (k + 1)}
  change A.HasDensity 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : ∃ s : Finset P, 3 / ε < ∑ p ∈ s, (p.val : ℝ)⁻¹ := by
    by_contra! h
    exact hdiv (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨s, hs⟩ := hs
  let q : ℕ := ∏ p ∈ s, p.val
  let z : ℝ := ∑ p ∈ s, (p.val : ℝ)⁻¹
  have hq : 0 < q := Finset.prod_pos fun p _ => (hP p.val p.property).pos
  have ht : 0 < q.totient := Nat.totient_pos.mpr hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htR : (0 : ℝ) < q.totient := by exact_mod_cast ht
  have hfin : (q.totient : ℝ) * (1 + z) ≤ q := totient_product_bound P hP s
  have hεz : 3 < ε * (1 + z) := by
    have := (div_lt_iff₀ hε).mp hs
    change 3 < z * ε at this
    linarith
  have hratio : 3 * (q.totient : ℝ) < ε * (q : ℝ) := by
    calc
      _ < (ε * (1 + z)) * q.totient := mul_lt_mul_of_pos_right hεz htR
      _ = ε * ((q.totient : ℝ) * (1 + z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfin hε.le
  filter_upwards [eventually_ge_atTop q] with N hN
  have hNpos : 0 < N := hq.trans_le hN
  let S := (Finset.range N).filter (fun x => x ∈ A)
  let C := (Finset.range N).filter (fun x => q.Coprime x)
  have hsub : S ⊆ insert 0 C := by
    intro x hx
    obtain ⟨hxN, hxA⟩ := Finset.mem_filter.mp hx
    by_cases hzero : x = 0
    · simp [hzero]
    apply Finset.mem_insert_of_mem
    refine Finset.mem_filter.mpr ⟨hxN,Nat.coprime_prod_left_iff.mpr ?_⟩
    intro p hp
    apply (hP p.val p.property).coprime_iff_not_dvd.mpr
    rintro ⟨k, hk⟩
    cases k with
    | zero => simp_all
    | succ k => exact hxA p.val p.property k hk
  have hcard : S.card ≤ (N / q + 1) * q.totient + 1 :=
    (Finset.card_le_card hsub).trans ((Finset.card_insert_le 0 C).trans
      (Nat.add_le_add_right (count_coprime q N hq) 1))
  have hcq : S.card * q ≤ 3 * N * q.totient := by
    calc
      _ ≤ ((N / q + 1) * q.totient + 1) * q := Nat.mul_le_mul_right q hcard
      _ = (N / q * q + q) * q.totient + q := by ring
      _ ≤ (N + N) * q.totient + N :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.div_mul_le_self N q) hN)) hN
      _ ≤ 3 * N * q.totient := by
        have hh : N ≤ N * q.totient := Nat.le_mul_of_pos_right N ht
        nlinarith
  have hreal : (S.card : ℝ) * q ≤ 3 * (N : ℝ) * q.totient := by exact_mod_cast hcq
  have hset : (S : Set ℕ) = A ∩ Set.Iio N := by
    ext x
    simp [S, and_comm]
  have hpd : A.partialDensity Set.univ N = (S.card : ℝ) / N := by
    simp [Set.partialDensity, ← hset]
  rw [hpd, Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  apply (div_lt_iff₀ hNR).mpr
  apply (lt_of_mul_lt_mul_right (a := (q : ℝ)) · hqR.le)
  calc
    _ ≤ 3 * (N : ℝ) * q.totient := hreal
    _ = N * (3 * (q.totient : ℝ)) := by ring
    _ < N * (ε * (q : ℝ)) := mul_lt_mul_of_pos_left hratio hNR
    _ = _ := by ring

end OMA.Sieve

namespace OMA.WebbVaughan

open Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Topology

lemma prime_reciprocals_four_mod_five :
    ¬ Summable (fun p : {p : ℕ // Nat.Prime p ∧ p % 5 = 4} => ((p.val : ℝ)⁻¹)) := by
  classical
  intro H
  let P : Set ℕ := {p | p.Prime ∧ p % 5 = 4}
  let a : ZMod 5 := 4
  let R : ℕ → ℝ := residueClass a
  let U : ℕ → ℝ := P.indicator (fun n : ℕ => (n : ℝ)⁻¹)
  let V : ℕ → ℝ := fun n => (if n.Prime then 0 else R n) / n
  have hU : Summable U := summable_subtype_iff_indicator.mp H
  have hV : Summable V := summable_residueClass_non_primes_div a
  have hr (n : ℕ) : 0 ≤ R n := residueClass_nonneg a n
  have ha : IsUnit a := by
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    change IsUnit (4 : ZMod 5)
    exact isUnit_iff_ne_zero.mpr (by decide)
  have haeq (n : ℕ) : (n : ZMod 5) = a ↔ n % 5 = 4 := by
    exact ZMod.natCast_eq_natCast_iff' n 4 5
  let f : ℝ → ℕ → ℝ := fun t n => t * (R n / (n : ℝ) ^ (1 + t))
  have da (n : ℕ) : Tendsto (fun t => f t n) (𝓝[>] 0) (𝓝 0) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · have hz : R 0 = 0 := residueClass_apply_zero a
      simp [f, hz]
    · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hc : ContinuousAt (fun t : ℝ => t * (R n / (n : ℝ) ^ (1 + t))) 0 := by
        apply continuousAt_id.mul
        apply continuousAt_const.div
        · exact (Real.continuousAt_const_rpow hpos.ne').comp
            (continuousAt_const.add continuousAt_id)
        · exact (Real.rpow_pos_of_pos hpos _).ne'
      simpa [f] using hc.tendsto.mono_left (nhdsWithin_le_nhds)
  have db : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ n, ‖f t n‖ ≤ U n + V n := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht n
    obtain ⟨ht0, ht1⟩ := ht
    have hn0 : 0 ≤ f t n := mul_nonneg ht0.le (div_nonneg (hr n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    rw [Real.norm_eq_abs, abs_of_nonneg hn0]
    rcases n.eq_zero_or_pos with rfl | hn
    · have hz : R 0 = 0 := residueClass_apply_zero a
      simp [f, U, V, P, hz, Set.indicator]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : 0 < (n : ℝ) ^ t := Real.rpow_pos_of_pos hn' t
    have hpow1 : 1 ≤ (n : ℝ) ^ t := Real.one_le_rpow hn1 ht0.le
    by_cases hprime : n.Prime
    · by_cases hclass : n % 5 = 4
      · have hmem : n ∈ P := ⟨hprime,hclass⟩
        have he : R n = Real.log n := by
          change ({m : ℕ | (m : ZMod 5) = a}.indicator (ArithmeticFunction.vonMangoldt ·)) n = _
          rw [Set.indicator_of_mem (show n ∈ {m : ℕ | (m : ZMod 5) = a} from (haeq n).mpr hclass)]
          exact vonMangoldt_apply_prime hprime
        simp only [f, U, V, he, Set.indicator_of_mem hmem, if_pos hprime, zero_div, add_zero,
          Real.rpow_add hn', Real.rpow_one, ← one_div]
        have hh : t * Real.log n ≤ (n : ℝ) ^ t := by
          rw [Real.rpow_def_of_pos hn', mul_comm t]
          linarith [Real.add_one_le_exp (Real.log n * t)]
        rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos hn' hpow) hn']
        nlinarith [mul_le_mul_of_nonneg_right hh hn'.le]
      · have hnmem : n ∉ P := fun h => hclass h.2
        have he : R n = 0 := by
          change ({m : ℕ | (m : ZMod 5) = a}.indicator _) n = 0
          rw [Set.indicator_of_notMem (show n ∉ {m : ℕ | (m : ZMod 5) = a} from fun h => hclass ((haeq n).mp h))]
        simp [U, V, f, he, hnmem, hprime]
    · have hnmem : n ∉ P := fun h => hprime h.1
      simp only [U, V, f, Set.indicator_of_notMem hnmem, if_neg hprime, zero_add]
      rw [Real.rpow_add hn', Real.rpow_one, ← mul_div_assoc, div_le_div_iff₀ (mul_pos hn' hpow) hn']
      have hcomp := mul_le_mul_of_nonneg_right (ht1.le.trans hpow1) (mul_nonneg (hr n) hn'.le)
      nlinarith only [hcomp]
  have he : Tendsto (fun t => ∑' n, f t n) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence (f := f) (g := fun _ => (0 : ℝ))
      (hU.add hV) da db
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  have hz : Tendsto (fun t : ℝ => (∑' n, f t n) + t * C) (𝓝[>] 0) (𝓝 0) := by
    simpa using he.add ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const C)
  have hh : ((5 : ℕ).totient : ℝ)⁻¹ ≤ 0 := by
    apply ge_of_tendsto hz
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    have hx : 1 + t ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hb := hC hx
    rw [add_sub_cancel_left] at hb
    have hb' := (div_le_iff₀ ht.1).mp (sub_le_iff_le_add.mp hb)
    simp only [f, tsum_mul_left]
    dsimp [R]
    linarith only [hb']
  exact (inv_pos.mpr (show (0 : ℝ) < (5 : ℕ).totient by exact_mod_cast Nat.totient_pos.mpr (by decide : 0 < 5))).not_ge hh

lemma decompose_multiple {p : ℕ} (hp : 0 < p) (hr : p % 5 = 4) (k : ℕ) :
    SierpinskiEgyptianFractionConjecture.HasSierpinskiDecomposition (p * (k + 1)) := by
  let t := p / 5 + 1
  have ht : 0 < t := by dsimp [t]; omega
  have he : p + 1 = 5 * t := by dsimp [t]; omega
  have heq : (p : ℚ) + 1 = 5 * (t : ℚ) := by exact_mod_cast he
  refine ⟨t * (k + 1), 2 * t * p * (k + 1), 2 * t * p * (k + 1),
    by change 0 < t * (k + 1); positivity,
    by change 0 < 2 * t * p * (k + 1); positivity,
    by change 0 < 2 * t * p * (k + 1); positivity, ?_⟩
  push_cast
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have ht0 : (t : ℚ) ≠ 0 := by positivity
  have hk0 : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hp0, ht0, hk0]
  rw [show (p : ℚ) = 5 * (t : ℚ) - 1 by linarith]
  ring

end OMA.WebbVaughan

open Filter

theorem OMA.solution : type_of% @SierpinskiEgyptianFractionConjecture.sierpinski_counterexamples_hasDensity_zero := by
  let P : Set ℕ := {p | p.Prime ∧ p % 5 = 4}
  let B : Set ℕ := {n | ∀ p ∈ P, ∀ k : ℕ, n ≠ p * (k + 1)}
  let E : Set ℕ := {n | ¬ SierpinskiEgyptianFractionConjecture.HasSierpinskiDecomposition n}
  have hB : B.HasDensity 0 :=
    OMA.Sieve.sieve_H1 P (fun _ hp => hp.1) OMA.WebbVaughan.prime_reciprocals_four_mod_five
  have hEB : E ⊆ B := by
    intro n hn p hp k h
    apply hn
    rw [h]
    exact OMA.WebbVaughan.decompose_multiple hp.1.pos hp.2 k
  change E.HasDensity 0
  unfold Set.HasDensity at hB ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB ?_ ?_
  · intro b
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro b
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard
      (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ hEB))
      ((Set.finite_Iio b).inter_of_right _)
