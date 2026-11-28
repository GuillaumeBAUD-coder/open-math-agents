import OMAStatements.S_oeis_a390246

open OMA.S_oeis_a390246

theorem OMA.solution : type_of% @OMA.S_oeis_a390246.main := by
  intro n hn
  have hne_end : (endpoints n).Nonempty := by
    refine ⟨n * (n + 1), fun i => (i.val + 1) * (n + 1), ?_, ?_⟩
    · intro i j hij
      have hval : i.val + 1 = j.val + 1 := Nat.eq_of_mul_eq_mul_right (by omega) hij
      exact Fin.ext (by omega)
    · intro i
      refine ⟨Nat.dvd_mul_right _ _, ?_, ?_⟩
      · exact Nat.le_mul_of_pos_left (n + 1) (by omega)
      · exact Nat.mul_le_mul_right (n + 1) (by omega)
  have he_mem : sInf (endpoints n) ∈ endpoints n := Nat.sInf_mem hne_end
  have he_in_w : sInf (endpoints n) - (n - 1) ∈ widths n := by
    rcases he_mem with ⟨b, hinj, hb⟩
    have h0 := hb ⟨0, by omega⟩
    refine ⟨b, hinj, fun i => ?_⟩
    rcases hb i with ⟨hdvd, hlo, hhi⟩
    exact ⟨hdvd, by omega, by omega⟩
  have hw_le : sInf (widths n) ≤ sInf (endpoints n) - (n - 1) := Nat.sInf_le he_in_w
  have hw_mem : sInf (widths n) ∈ widths n := Nat.sInf_mem ⟨_, he_in_w⟩
  have hw_in_e : n + sInf (widths n) - 1 ∈ endpoints n := by
    rcases hw_mem with ⟨b, hinj, hb⟩
    refine ⟨b, hinj, fun i => ?_⟩
    rcases hb i with ⟨hdvd, hlo, hhi⟩
    exact ⟨hdvd, by omega, by omega⟩
  have he_le : sInf (endpoints n) ≤ n + sInf (widths n) - 1 := Nat.sInf_le hw_in_e
  omega
