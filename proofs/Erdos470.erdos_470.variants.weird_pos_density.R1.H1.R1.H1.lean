import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1
import Mathlib
/-!
# Large-divisor tail for the abundancy index

Credit: @marcusbuffett. Divisors at most K already divide K factorial.
Count the multiples of each remaining divisor before taking the reciprocal-square tail.
-/
open Filter Finset
open scoped Topology
namespace Tail470
lemma index_sum {n : ℕ} (hn : 0<n) :
    (n.abundancyIndex:ℝ) = ∑ d ∈ n.divisors, (1:ℝ)/d := by
  simp only [Nat.abundancyIndex,Rat.cast_div,Rat.cast_natCast,Nat.cast_sum,Rat.cast_sum]
  rw [←Nat.sum_div_divisors n (fun d : ℕ => (d:ℝ)),Finset.sum_div]
  apply sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  have hn' : (n:ℝ) ≠ 0 := by positivity
  field_simp
lemma point {K n b : ℕ} (hn : 0<n) (hnb : n≤b) :
    |(n.abundancyIndex:ℝ) - ((n.gcd K.factorial).abundancyIndex:ℝ)| ≤
      ∑ d ∈ Ioc K b, if d∣n then (1:ℝ)/d else 0 := by
  let g := n.gcd K.factorial
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ hn
  have hsub : g.divisors ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left ..),hn.ne'⟩
  have hmono : (g.abundancyIndex:ℝ) ≤ n.abundancyIndex := by
    exact_mod_cast Nat.abundancyIndex_le_of_dvd hn.ne' (Nat.gcd_dvd_left n K.factorial)
  change |(n.abundancyIndex:ℝ) - (g.abundancyIndex:ℝ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.2 hmono),index_sum hn,index_sum hg,
    ← sum_sdiff hsub (f:=fun d : ℕ => (1:ℝ)/d),add_sub_cancel_right,←sum_filter]
  apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
  intro d hd
  obtain ⟨hd,hdg⟩ := Finset.mem_sdiff.1 hd
  have hdn := Nat.dvd_of_mem_divisors hd
  have hdp := Nat.pos_of_dvd_of_pos hdn hn
  have hKd : K<d := by
    by_contra! h
    exact hdg (Nat.mem_divisors.2 ⟨Nat.dvd_gcd hdn (Nat.dvd_factorial hdp h),hg.ne'⟩)
  exact mem_filter.2 ⟨mem_Ioc.2 ⟨hKd,(Nat.le_of_dvd hn hdn).trans hnb⟩,hdn⟩
noncomputable abbrev err (K n : ℕ) := |(n.abundancyIndex:ℝ) - ((n.gcd K.factorial).abundancyIndex:ℝ)|
lemma total {b K : ℕ} (hK : 0<K) (hb : K≤b) :
    ∑ n ∈ Ioc 0 b, err K n ≤ (b:ℝ)/K := by
  calc _ ≤ ∑ n ∈ Ioc 0 b, ∑ d ∈ Ioc K b, if d∣n then (1:ℝ)/d else 0 :=
          sum_le_sum fun n hn => point (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2
       _ = ∑ d ∈ Ioc K b, ∑ n ∈ Ioc 0 b, if d∣n then (1:ℝ)/d else 0 := sum_comm
       _ ≤ ∑ d ∈ Ioc K b, (b:ℝ)*((d:ℝ)^2)⁻¹ := by
          apply sum_le_sum
          intro d _
          rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
          calc ((b/d:ℕ):ℝ)*(1/d) ≤ ((b:ℝ)/d)*(1/d) := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
               _ = _ := by ring
       _ ≤ _ := by
          rw [← mul_sum,div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have := sum_Ioc_inv_sq_le_sub (α:=ℝ) hK.ne' hb
          linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) b)]
end Tail470

open Tail470 in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1_H1_R1.H1 := by
  classical
  intro δ hδ ε hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (2/(δ*ε)), eventually_gt_atTop 0] with K hKe hK
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (2/ε),eventually_ge_atTop K] with b hbe hKb
  let B := (Ioc 0 b).filter fun n => δ ≤ err K n
  let A := {n : ℕ | δ ≤ err K n}
  have hmark : δ*(B.card:ℝ) ≤ (b:ℝ)/K := by
    calc _ = ∑ _ ∈ B, δ := by simp [mul_comm]
         _ ≤ ∑ n ∈ B, err K n := sum_le_sum fun n hn => (mem_filter.1 hn).2
         _ ≤ ∑ n ∈ Ioc 0 b, err K n := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => abs_nonneg _)
         _ ≤ _ := total hK hKb
  have hsub : A ∩ Set.Iio b ⊆ (↑(insert 0 B) : Set ℕ) := by
    rintro n ⟨hn,hn'⟩
    apply Finset.mem_insert.2
    rcases Nat.eq_zero_or_pos n with h|h
    · exact Or.inl h
    · exact Or.inr (mem_filter.2 ⟨mem_Ioc.2 ⟨h,hn'.le⟩,hn⟩)
  have hcard : (A ∩ Set.Iio b).ncard ≤ B.card+1 := by
    have h := Set.ncard_le_ncard hsub (insert 0 B).finite_toSet
    rw [Set.ncard_coe_finset] at h
    exact h.trans (card_insert_le ..)
  have hcard' : ((A ∩ Set.Iio b).ncard:ℝ) ≤ B.card+1 := by exact_mod_cast hcard
  change A.partialDensity Set.univ b < ε
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Set.ncard_Iio_nat]
  have hb' := Nat.cast_pos (α:=ℝ).2 (hK.trans_le hKb)
  have hk' := Nat.cast_pos (α:=ℝ).2 hK
  apply (div_lt_iff₀ hb').2
  have heK := (div_lt_iff₀ (mul_pos hδ hε)).1 hKe
  have heb := (div_lt_iff₀ hε).1 hbe
  have hmid : (b:ℝ)/K < δ*(ε*b/2) := by
    apply (div_lt_iff₀ hk').2
    nlinarith only [mul_lt_mul_of_pos_right heK hb']
  have hsmall : (B.card:ℝ) < ε*b/2 := (mul_lt_mul_iff_right₀ hδ).1 (hmark.trans_lt hmid)
  linarith
