import OMAStatements.S_oeis_a401759

open OMA.S_oeis_a401759 in
theorem OMA.solution : type_of% @OMA.S_oeis_a401759.main := by
  refine (fun h => ⟨h, fun H m _ ⟨r, e⟩ => e ▸ two_mul r ▸ (h r).1 (H r (by omega)), fun G n _ => (h n).2 (G _ (by omega) (by simp))⟩) fun n => ?_
  unfold a; split_ifs with h <;> simp [good] at h <;> grind
