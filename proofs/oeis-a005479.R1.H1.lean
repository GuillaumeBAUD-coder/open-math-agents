import OMAReductions.R_oeis_a005479_R1

/-!
# Proof of `oeis-a005479.R1.H1`

Verifies that `7 = lucas 4`, `47 = lucas 8`, and `2207 = lucas 16` are prime Lucas numbers
congruent to `7` modulo `10`, and that their indices `4, 8, 16` are composite (`≥ 1`, not prime).
-/

open OMA.S_oeis_a005479

theorem OMA.solution : OMA.R_oeis_a005479_R1.H1 := by
  have hL4 : lucas 4 = 7 := by decide
  have hL8 : lucas 8 = 47 := by decide
  have hL16 : lucas 16 = 2207 := by decide
  have hp7 : Nat.Prime 7 := by norm_num
  have hp47 : Nat.Prime 47 := by norm_num
  have hp2207 : Nat.Prime 2207 := by norm_num
  constructor
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨⟨4, hL4⟩, hp7, by decide⟩
    · exact ⟨⟨8, hL8⟩, hp47, by decide⟩
    · exact ⟨⟨16, hL16⟩, hp2207, by decide⟩
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨4, by decide, by decide, hL4, hp7⟩
    · exact ⟨8, by decide, by decide, hL8, hp47⟩
    · exact ⟨16, by decide, by decide, hL16, hp2207⟩
