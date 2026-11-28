import OMAReductions.R_Erdos945_erdos_945_variants_constant_R1_H1_R1
import Mathlib

namespace OMA.E945

open Finset

lemma cnt (n H d : ℕ) (hd : 0 < d) :
    ((Ioc n (n + H)).filter (fun q => d ∣ q)).card ≤ H / d + 1 := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (n + H) d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div n d
  have hu : (Ioc 0 (n + H)).filter (fun q => d ∣ q) =
      (Ioc 0 n).filter (fun q => d ∣ q) ∪ (Ioc n (n + H)).filter (fun q => d ∣ q) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le n) (Nat.le_add_right n H)]
  have hdisj : Disjoint ((Ioc 0 n).filter (fun q => d ∣ q))
      ((Ioc n (n + H)).filter (fun q => d ∣ q)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Ioc] at hx hx'
    omega
  have hc := Finset.card_union_of_disjoint hdisj
  rw [← hu, h1, h2] at hc
  have h3 : (n + H) / d ≤ n / d + H / d + 1 := by
    rw [Nat.add_div hd]
    split_ifs <;> omega
  omega

lemma tele (M : ℕ) (hM : 3 ≤ M) :
    ∑ k ∈ Ioc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 25 / 36 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : Ioc 1 3 = ({2, 3} : Finset ℕ) := by decide
    rw [this]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
    have hstep : 1 / ((M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
      rw [div_sub_div _ _ hM0.ne' hM1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

end OMA.E945

open OMA.E945 Finset in
theorem OMA.solution : OMA.R_Erdos945_erdos_945_variants_constant_R1_H1_R1.H1 := by
  intro n H hH
  classical
  set M := H / 8 with hMdef
  have hM8 : 8 ≤ M := by omega
  set P := (Ioc 1 M).filter Nat.Prime with hP
  have hsub : ((Ioc n (n + H)).filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q) ⊆
      P.biUnion (fun p => (Ioc n (n + H)).filter (fun q => p * p ∣ q)) := by
    intro q hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hq1, p, hp, hpM, hpq⟩ := hq
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.one_lt, hpM⟩, hp⟩,
      Finset.mem_filter.mpr ⟨hq1, hpq⟩⟩
  have h1 : ((Ioc n (n + H)).filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q).card ≤
      ∑ p ∈ P, (H / (p * p) + 1) := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    apply Finset.sum_le_sum
    intro p hp
    simp only [hP, Finset.mem_filter] at hp
    exact cnt n H (p * p) (Nat.mul_pos hp.2.pos hp.2.pos)
  have hPcard : P.card ≤ M := by
    calc P.card ≤ (Ioc 1 M).card := Finset.card_filter_le _ _
      _ = M - 1 := Nat.card_Ioc 1 M
      _ ≤ M := Nat.sub_le _ _
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have h2 : ((∑ p ∈ P, (H / (p * p) + 1) : ℕ) : ℝ) ≤ (H : ℝ) * (25 / 36) + (H : ℝ) / 8 := by
    push_cast
    rw [Finset.sum_add_distrib]
    have ha : ∑ p ∈ P, (((H / (p * p) : ℕ)) : ℝ) ≤ (H : ℝ) * (25 / 36) := by
      calc ∑ p ∈ P, (((H / (p * p) : ℕ)) : ℝ) ≤ ∑ p ∈ P, (H : ℝ) * (1 / (p : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro p _
            have := @Nat.cast_div_le ℝ _ _ _ H (p * p)
            calc (((H / (p * p) : ℕ)) : ℝ) ≤ (H : ℝ) / ((p * p : ℕ) : ℝ) := this
              _ = (H : ℝ) * (1 / (p : ℝ) ^ 2) := by push_cast; ring
        _ = (H : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ (H : ℝ) * ∑ k ∈ Ioc 1 M, 1 / (k : ℝ) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hH0
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro k _ _
            positivity
        _ ≤ (H : ℝ) * (25 / 36) := by
            apply mul_le_mul_of_nonneg_left _ hH0
            have := tele M (by omega)
            have hpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
            linarith
    have hb : ∑ p ∈ P, (1 : ℝ) ≤ (H : ℝ) / 8 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have h3 : (P.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPcard
      have h4 : (M : ℝ) ≤ (H : ℝ) / 8 := by
        rw [hMdef]
        have := @Nat.cast_div_le ℝ _ _ _ H 8
        simpa using this
      linarith
    linarith
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h5 : (((Ioc n (n + H)).filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q).card : ℝ)
      ≤ (H : ℝ) * (25 / 36) + (H : ℝ) / 8 := by
    refine le_trans ?_ h2
    exact_mod_cast h1
  have h6 : ((((Ioc n (n + H)).filter fun q => ∃ p : ℕ, p.Prime ∧ p ≤ H / 8 ∧ p * p ∣ q).card * 8 : ℕ) : ℝ)
      ≤ ((7 * H : ℕ) : ℝ) := by
    push_cast
    nlinarith [h5, hH0]
  exact_mod_cast h6
