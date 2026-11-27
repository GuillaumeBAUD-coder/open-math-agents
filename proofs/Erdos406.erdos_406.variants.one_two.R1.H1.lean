import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  have check : ∀ k : Fin 1001, 15 < k.val → (Nat.digits 3 (2 ^ k.val)).contains 0 = true := by
    decide +kernel
  intro k hlow hhigh hall
  have hz : 0 ∈ Nat.digits 3 (2 ^ k) :=
    List.contains_iff_mem.mp (check ⟨k, Nat.lt_succ_of_le hhigh⟩ hlow)
  simpa using hall hz
