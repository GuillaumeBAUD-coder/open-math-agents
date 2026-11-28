import OMAStatements.S_mo_412446
import Mathlib

-- Problem: mo-412446, the product of all Boltzmann weights is smaller than the product of the
-- Boltzmann weights renormalized on a proper nonempty subset S.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- With Z the full partition sum and Z_S the partial one, 0 < Z_S < Z. Each factor with i in S
-- satisfies e_i / Z < e_i / Z_S, and each factor with i outside S satisfies e_i / Z <= 1.

theorem OMA.solution : type_of% @OMA.S_mo_412446.main := by
  intro n E β S hS hne
  have hpos : ∀ i, 0 < Real.exp (-β * E i) := fun i => Real.exp_pos _
  unfold OMA.S_mo_412446.boltzmann
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ j ∈ Finset.univ, Real.exp (-β * E j) := ⟨_, rfl⟩
  obtain ⟨ZS, hZS⟩ : ∃ ZS, ZS = ∑ j ∈ S, Real.exp (-β * E j) := ⟨_, rfl⟩
  rw [← hZ, ← hZS]
  have hZS_pos : 0 < ZS := by
    rw [hZS]
    exact Finset.sum_pos (fun i _ => hpos i) hS
  have hlt : ZS < Z := by
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra hcon
      exact hne (Finset.eq_univ_iff_forall.mpr fun i => not_not.mp fun hi => hcon ⟨i, hi⟩)
    have h1 : ZS + Real.exp (-β * E i) ≤ Z := by
      rw [hZS, hZ, add_comm, ← Finset.sum_insert (f := fun j => Real.exp (-β * E j)) hi]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => (hpos j).le)
    linarith [hpos i]
  have hZpos : 0 < Z := hZS_pos.trans hlt
  rw [← Finset.prod_mul_prod_compl S (fun i => Real.exp (-β * E i) / Z)]
  have h1 : ∏ i ∈ S, Real.exp (-β * E i) / Z < ∏ i ∈ S, Real.exp (-β * E i) / ZS := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      exact div_pos (hpos i) hZpos
    · intro i _
      exact div_lt_div_of_pos_left (hpos i) hZS_pos hlt
    · exact hS
  have h2 : ∏ i ∈ Sᶜ, Real.exp (-β * E i) / Z ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact (div_pos (hpos i) hZpos).le
    · intro i _
      rw [div_le_one hZpos, hZ]
      exact Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)
  have h3 : 0 < ∏ i ∈ S, Real.exp (-β * E i) / Z :=
    Finset.prod_pos (fun i _ => div_pos (hpos i) hZpos)
  calc (∏ i ∈ S, Real.exp (-β * E i) / Z) * ∏ i ∈ Sᶜ, Real.exp (-β * E i) / Z
      ≤ (∏ i ∈ S, Real.exp (-β * E i) / Z) * 1 := mul_le_mul_of_nonneg_left h2 h3.le
    _ = ∏ i ∈ S, Real.exp (-β * E i) / Z := mul_one _
    _ < ∏ i ∈ S, Real.exp (-β * E i) / ZS := h1
