import OMAStatements.S_oeis_a091892

-- Problem: A091892: Numbers k having only one partition into parts which are a sum of exactly as many distinct powers of 2 as there are 1's in the bin
-- Upstream: formal-conjectures statements/oeis-a091892.lean:0 (declaration OMA.S_oeis_a091892.main)
-- Credit: @julianibarz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open OMA.S_oeis_a091892

def badPartition : Nat.Partition 331775 where
  parts := {55295, 48127, 32759, 32751, 32735, 32703, 32639, 32511, 32255}
  parts_pos := by
    intro i hi
    simp at hi
    omega
  parts_sum := by norm_num

theorem badPartition_good : ∀ j ∈ badPartition.parts, weight j = weight 331775 := by
  intro j hj
  simp [badPartition] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold weight <;> decide

theorem bad_threshold : threshold 331775 := by unfold threshold; decide

theorem bad_nonmember : ¬ member 331775 := by
  rintro ⟨p, hp, hu⟩
  have h₁ : Nat.Partition.indiscrete 331775 = p := hu _ (by simp)
  have h₂ : badPartition = p := hu _ badPartition_good
  have h := congrArg (fun q : Nat.Partition 331775 => q.parts.card) (h₁.trans h₂.symm)
  norm_num [badPartition, Nat.Partition.indiscrete_parts] at h

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a091892.main) := by
  intro h
  exact bad_nonmember ((h.2 331775 (by omega)).mpr bad_threshold)
