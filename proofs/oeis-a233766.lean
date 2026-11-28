import OMAStatements.S_oeis_a233766

open OMA.S_oeis_a233766

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a233766.main) := by
  rintro ⟨-, h⟩
  have h25 := h 25 (by norm_num)
  have e1 : A007775 25 = 91 := by
    have c : Nat.count (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m) 91 = 24 := by decide
    unfold A007775
    rw [show 25 - 1 = 24 from rfl, ← c]
    exact Nat.nth_count (p := fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m) (by decide)
  have e2 : A007775 1 = 1 := by
    have c : Nat.count (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m) 1 = 0 := by decide
    unfold A007775
    rw [show 1 - 1 = 0 from rfl, ← c]
    exact Nat.nth_count (p := fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m) (by decide)
  have v : A030133 90 = 9 := by norm_num [A030133]
  have w : A030133 0 = 2 := rfl
  simp [a, e1, e2, v, w] at h25
