import OMAStatements.S_oeis_a038867

namespace OMA.S_oeis_a038867

lemma a_eq (n : ℕ) : a n = 15 * n ^ 2 + 75 * n + 125 := by
  unfold a
  rw [show (n + 5) ^ 3 = n ^ 3 + (15 * n ^ 2 + 75 * n + 125) by ring, Nat.add_sub_cancel_left]

lemma five_dvd_of_sq {m : ℕ} (h : 5 ∣ m ^ 2) : 5 ∣ m :=
  Nat.prime_five.dvd_of_dvd_pow h

lemma no_root (t : ZMod 5) : 3 * t ^ 2 + 3 * t + 1 ≠ 0 := by
  revert t
  decide

end OMA.S_oeis_a038867

open OMA.S_oeis_a038867 in
theorem OMA.solution : type_of% @OMA.S_oeis_a038867.main := by
  intro n ⟨m, hm⟩
  rw [a_eq, ← sq] at hm
  -- 5 ∣ m
  obtain ⟨y, rfl⟩ : 5 ∣ m := five_dvd_of_sq ⟨3 * n ^ 2 + 15 * n + 25, by rw [← hm]; ring⟩
  have h1 : 5 * y ^ 2 = 3 * n ^ 2 + 15 * n + 25 := by nlinarith
  -- 5 ∣ n
  have h3n : 5 ∣ 3 * n ^ 2 := ⟨y ^ 2 - 3 * n - 5, by omega⟩
  have hn2 : 5 ∣ n ^ 2 := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3n)
  obtain ⟨t, rfl⟩ : 5 ∣ n := five_dvd_of_sq hn2
  have h2 : y ^ 2 = 15 * t ^ 2 + 15 * t + 5 := by nlinarith
  -- 5 ∣ y
  obtain ⟨z, rfl⟩ : 5 ∣ y := five_dvd_of_sq ⟨3 * t ^ 2 + 3 * t + 1, by rw [h2]; ring⟩
  have h3 : 5 * z ^ 2 = 3 * t ^ 2 + 3 * t + 1 := by nlinarith
  have h4 : ((5 * z ^ 2 : ℕ) : ZMod 5) = ((3 * t ^ 2 + 3 * t + 1 : ℕ) : ZMod 5) := by rw [h3]
  push_cast at h4
  have h5 : (5 : ZMod 5) = 0 := rfl
  rw [h5, zero_mul] at h4
  exact no_root (t : ZMod 5) h4.symm
