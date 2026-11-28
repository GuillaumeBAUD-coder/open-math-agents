import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Averaging over shifts: the |U||A| pairs (x, y) in U x A split by the value y + N - x in
-- [0, 2N), so some shift d covers at least |U||A|/(2N) points of U; V is the uncovered rest.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2
  intro N hN A U hA hU
  classical
  set C : ℕ → Finset ℕ := fun d => U.filter (fun x => ∃ y ∈ A, x + d = y + N) with hC
  have hsum : U.card * A.card ≤ ∑ d ∈ Finset.range (2*N), (C d).card := by
    rw [← Finset.card_product]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.2 + N - p.1)
      (t := Finset.range (2*N))]
    · apply Finset.sum_le_sum
      intro d hd
      apply Finset.card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp
        obtain ⟨⟨hx, hy⟩, hpd⟩ := hp
        have h1 := Finset.mem_Icc.mp (hU hx)
        have h2 := Finset.mem_Icc.mp (hA hy)
        simp only [hC, Finset.coe_filter, Set.mem_ofPred_eq]
        exact ⟨hx, p.2, hy, by omega⟩
      · intro p hp q hq hpq
        simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp hq
        have a1 := Finset.mem_Icc.mp (hU hp.1.1)
        have a3 := Finset.mem_Icc.mp (hA hp.1.2)
        have a4 := Finset.mem_Icc.mp (hA hq.1.2)
        simp only at hpq
        have : p.2 = q.2 := by omega
        exact Prod.ext hpq this
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_product] at hp
      have h1 := Finset.mem_Icc.mp (hU hp.1)
      have h2 := Finset.mem_Icc.mp (hA hp.2)
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range]
      omega
  have hex : ∃ d ∈ Finset.range (2*N), U.card * A.card ≤ (C d).card * (2*N) := by
    by_contra hcon
    push_neg at hcon
    have hne : (Finset.range (2*N)).Nonempty := ⟨0, by simp; omega⟩
    have := Finset.sum_lt_sum_of_nonempty hne hcon
    rw [← Finset.sum_mul] at this
    simp at this
    nlinarith
  obtain ⟨d, -, hd⟩ := hex
  refine ⟨d, N, U.filter (fun x => ¬ ∃ y ∈ A, x + d = y + N), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard := Finset.card_filter_add_card_filter_not
      (s := U) (fun x => ∃ y ∈ A, x + d = y + N)
    have hcR : ((U.filter (fun x => ¬ ∃ y ∈ A, x + d = y + N)).card : ℝ)
        = U.card - (C d).card := by
      rw [← hcard]; push_cast; simp [hC]
    have hdR : (U.card : ℝ) * A.card ≤ (C d).card * (2*N) := by exact_mod_cast hd
    rw [hcR]
    have hNp : (0:ℝ) < 2 * N := by
      have : (2:ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [sub_mul, one_mul, div_mul_eq_mul_div, sub_le_sub_iff_left, div_le_iff₀ hNp]
    linarith
  · intro x hx hxV
    simp only [Finset.mem_filter, not_and, not_not] at hxV
    exact hxV hx
