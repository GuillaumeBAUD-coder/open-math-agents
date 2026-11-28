import OMAStatements.S_mo_412446
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_412446.main := by
  intro n E β S hS hne
  have hZS : 0 < ∑ j ∈ S, Real.exp (-β * E j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) hS
  obtain ⟨k, hk⟩ : ∃ k, k ∉ S := by
    by_contra h
    apply hne
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hlt : ∑ j ∈ S, Real.exp (-β * E j) < ∑ j, Real.exp (-β * E j) := by
    apply Finset.sum_lt_sum_of_subset (Finset.subset_univ S) (Finset.mem_univ k) hk (Real.exp_pos _)
    intro j _ _
    exact (Real.exp_pos _).le
  have hZ : 0 < ∑ j, Real.exp (-β * E j) := lt_trans hZS hlt
  have hb0 : ∀ i, 0 < OMA.S_mo_412446.boltzmann E β Finset.univ i :=
    fun i => div_pos (Real.exp_pos _) hZ
  have hb1 : ∀ i, OMA.S_mo_412446.boltzmann E β Finset.univ i ≤ 1 := by
    intro i
    unfold OMA.S_mo_412446.boltzmann
    rw [div_le_one hZ]
    exact Finset.single_le_sum (f := fun j => Real.exp (-β * E j))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hA : ∏ i ∈ S, OMA.S_mo_412446.boltzmann E β Finset.univ i
      < ∏ i ∈ S, OMA.S_mo_412446.boltzmann E β S i := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      exact hb0 i
    · intro i _
      unfold OMA.S_mo_412446.boltzmann
      exact div_lt_div_of_pos_left (Real.exp_pos _) hZS hlt
    · exact hS
  have hB : ∏ i ∈ Sᶜ, OMA.S_mo_412446.boltzmann E β Finset.univ i ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hb0 i).le) (fun i _ => hb1 i)
  have hA0 : 0 < ∏ i ∈ S, OMA.S_mo_412446.boltzmann E β Finset.univ i :=
    Finset.prod_pos (fun i _ => hb0 i)
  rw [← Finset.prod_mul_prod_compl S]
  calc (∏ i ∈ S, OMA.S_mo_412446.boltzmann E β Finset.univ i)
        * ∏ i ∈ Sᶜ, OMA.S_mo_412446.boltzmann E β Finset.univ i
      ≤ (∏ i ∈ S, OMA.S_mo_412446.boltzmann E β Finset.univ i) * 1 :=
        mul_le_mul_of_nonneg_left hB hA0.le
    _ = ∏ i ∈ S, OMA.S_mo_412446.boltzmann E β Finset.univ i := mul_one _
    _ < ∏ i ∈ S, OMA.S_mo_412446.boltzmann E β S i := hA
