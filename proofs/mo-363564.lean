import OMAStatements.S_mo_363564
import Mathlib

open OMA.S_mo_363564 Cardinal

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_363564.main) := by
  intro h
  have key := h (aleph 1).ord.ToType (aleph 1).ord.ToType ℕ (fun i => Set.Iic i)
    (fun _ => Set.univ) (fun i j hij => Set.Iic_subset_Iic.mpr hij) (fun _ _ _ => le_rfl) ?_
  · have hU : (⋃ i : (aleph 1).ord.ToType, Set.Iic i) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, Set.mem_Iic.mpr le_rfl⟩
    have hne : Nonempty (aleph 1).ord.ToType := by
      rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
      exact (aleph0_pos.trans aleph0_lt_aleph_one).ne'
    obtain ⟨i0⟩ := hne
    have hV : (⋃ _i : (aleph 1).ord.ToType, (Set.univ : Set ℕ)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_iUnion.mpr ⟨i0, Set.mem_univ x⟩
    rw [hU, hV, Cardinal.mk_univ, Cardinal.mk_univ, Cardinal.mk_ord_toType, Cardinal.mk_nat] at key
    exact absurd key (not_le.mpr aleph0_lt_aleph_one)
  · intro i
    rw [Cardinal.mk_univ, Cardinal.mk_nat]
    have hIio : Cardinal.mk (Set.Iio i) < aleph 1 := by
      have := Cardinal.mk_Iio_lt i (by simp)
      simpa using this
    have hc : (Set.Iio i).Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hIio)
    have hc2 : (Set.Iic i).Countable := by
      rw [← Set.Iio_insert]; exact hc.insert i
    exact Cardinal.le_aleph0_iff_set_countable.mpr hc2
