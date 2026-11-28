import OMAStatements.S_oeis_a249969

theorem OMA.solution : type_of% @OMA.S_oeis_a249969.main := by
  rintro k ⟨hk, m, hm⟩
  have P : ∀ x < 100, (x ^ 2 % 100 + x) % 100 ∈ [0, 2, 6, 10, 12, 20, 22, 30, 32, 40, 42, 50, 52, 56, 60, 62, 70, 72, 80, 82, 90, 92] := by decide
  have Q : ∀ x < 100, x ^ 2 % 100 ∈ [0, 1, 4, 9, 16, 21, 24, 25, 29, 36, 41, 44, 49, 56, 61, 64, 69, 76, 81, 84, 89, 96] := by decide
  have R : ∀ x < 100, x * x % 100 = 25 → x % 10 = 5 := by decide
  have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := k ^ 2) (by norm_num)
  rw [OMA.S_oeis_a249969.extend, Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits] at hm
  simp [Nat.ofDigits, pow_add] at hm
  generalize (Nat.digits 10 (k ^ 2)).length = L at *
  obtain ⟨j, rfl⟩ : ∃ j, m = 10 * j + 5 :=
    ⟨m / 10, by have := R (m % 100) (by omega) (by rw [← Nat.mul_mod]; omega); omega⟩
  have hp := P (j % 100) (by omega)
  have hq := Q (k % 100) (by omega)
  rw [← Nat.pow_mod, ← Nat.add_mod] at hp
  rw [← Nat.pow_mod] at hq
  have : k ^ 2 + 10 ^ L * 3 = j ^ 2 + j := by nlinarith
  simp at hp hq
  rcases L with _ | _ | L
  · simp at h1; omega
  · omega
  · rw [pow_add] at *; omega
