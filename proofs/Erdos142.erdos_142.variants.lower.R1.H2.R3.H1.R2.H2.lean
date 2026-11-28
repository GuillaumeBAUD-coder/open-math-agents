import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2
import Mathlib

namespace OMA.Cov

open Finset

theorem pick (N : ℕ) (S U : Finset ℕ) (hS : S ⊆ Icc 1 N) (hU : U ⊆ Icc 1 N) :
    ∃ t : ℕ, U.card * S.card ≤ 2 * N * (U.filter (fun x => ∃ b ∈ S, x + N = t + b)).card := by
  classical
  by_contra hc
  push Not at hc
  have h1 : ∑ t ∈ Icc 1 (2 * N), (U.filter (fun x => ∃ b ∈ S, x + N = t + b)).card
      = ∑ x ∈ U, ((Icc 1 (2 * N)).filter (fun t => ∃ b ∈ S, x + N = t + b)).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := fun t x => ∃ b ∈ S, x + N = t + b)
  have h2 : ∀ x ∈ U, S.card ≤ ((Icc 1 (2 * N)).filter (fun t => ∃ b ∈ S, x + N = t + b)).card := by
    intro x hx
    have hx' := mem_Icc.mp (hU hx)
    apply card_le_card_of_injOn (fun b => x + N - b)
    · intro b hb
      have hb' := mem_Icc.mp (hS hb)
      change x + N - b ∈ _
      rw [mem_coe, mem_filter, mem_Icc]
      exact ⟨⟨by omega, by omega⟩, b, hb, by omega⟩
    · intro b hb b' hb' h
      have h1 := mem_Icc.mp (hS hb)
      have h2 := mem_Icc.mp (hS hb')
      change x + N - b = x + N - b' at h
      omega
  have h3 : U.card * S.card ≤ ∑ x ∈ U, ((Icc 1 (2 * N)).filter (fun t => ∃ b ∈ S, x + N = t + b)).card := by
    calc U.card * S.card = ∑ x ∈ U, S.card := by simp
      _ ≤ _ := sum_le_sum h2
  rw [← h1] at h3
  have h4 : ∑ t ∈ Icc 1 (2 * N), (2 * N * (U.filter (fun x => ∃ b ∈ S, x + N = t + b)).card + 1)
      ≤ ∑ t ∈ Icc 1 (2 * N), U.card * S.card := sum_le_sum (fun t _ => hc t)
  rw [sum_add_distrib, ← mul_sum] at h4
  simp only [sum_const, Nat.card_Icc, smul_eq_mul, mul_one, add_tsub_cancel_right] at h4
  have h5 : 2 * N * (U.card * S.card) ≤ 2 * N * ∑ t ∈ Icc 1 (2 * N), (U.filter (fun x => ∃ b ∈ S, x + N = t + b)).card :=
    Nat.mul_le_mul_left _ h3
  have hN : N = 0 := by omega
  subst hN
  have hU0 : U = ∅ := by
    apply subset_empty.mp
    intro x hx
    have := mem_Icc.mp (hU hx)
    omega
  subst hU0
  have := hc 0
  simp at this

end OMA.Cov

open Finset in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 := by
  classical
  intro N hN A U hA hU
  obtain ⟨t, ht⟩ := OMA.Cov.pick N A U hA hU
  refine ⟨N, t, U.filter (fun x => ¬ ∃ b ∈ A, x + N = t + b), filter_subset _ _, ?_, ?_⟩
  · have hcard := card_filter_add_card_filter_not (s := U) (fun x => ∃ b ∈ A, x + N = t + b)
    have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have e0 : ((U.filter (fun x => ∃ b ∈ A, x + N = t + b)).card : ℝ)
        + (U.filter (fun x => ¬ ∃ b ∈ A, x + N = t + b)).card = U.card := by exact_mod_cast hcard
    have e2 : (U.card : ℝ) * A.card ≤ 2 * N * (U.filter (fun x => ∃ b ∈ A, x + N = t + b)).card := by
      exact_mod_cast ht
    have e4 : (A.card : ℝ) / (2 * N) * U.card ≤ (U.filter (fun x => ∃ b ∈ A, x + N = t + b)).card := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  · intro x hx hxV
    by_contra hc
    exact hxV (mem_filter.mpr ⟨hx, fun ⟨b, hb, h⟩ => hc ⟨b, hb, by omega⟩⟩)
