import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1

-- Step Erdos242.erdos_242.R1.H1.R1.H2: hypothesis H2 of reduction Erdos242.erdos_242.R1.H1.R1
-- Credit: @<your GitHub handle>

set_option maxRecDepth 4096 in
theorem OMA.solution : OMA.R_Erdos242_erdos_242_R1_H1_R1.H2 := by
  intro p hp h24 hnot
  have hp5 : p % 5 ≠ 0 := by
    intro h
    have h5 : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    have heq : 5 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5
    omega
  have hp7 : p % 7 ≠ 0 := by
    intro h
    have h7 : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
    have heq : 7 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h7
    omega
  have hcases :
      p % 120 = 73 ∨ p % 120 = 97 ∨ p % 168 = 73 ∨ p % 168 = 145 ∨ p % 168 = 97 := by
    let r : Fin 840 := ⟨p % 840, Nat.mod_lt _ (by decide)⟩
    have finite : ∀ a : Fin 840, (a : ℕ) % 24 = 1 → (a : ℕ) % 5 ≠ 0 →
        (a : ℕ) % 7 ≠ 0 →
        ¬ ((a : ℕ) = 1 ∨ (a : ℕ) = 121 ∨ (a : ℕ) = 169 ∨
          (a : ℕ) = 289 ∨ (a : ℕ) = 361 ∨ (a : ℕ) = 529) →
        (a : ℕ) % 120 = 73 ∨ (a : ℕ) % 120 = 97 ∨ (a : ℕ) % 168 = 73 ∨
          (a : ℕ) % 168 = 145 ∨ (a : ℕ) % 168 = 97 := by decide
    have rem (d : ℕ) (hd : d ∣ 840) : (r : ℕ) % d = p % d :=
      Nat.mod_mod_of_dvd p hd
    have hh := finite r ((rem 24 (by decide)).trans h24)
      (fun h => hp5 ((rem 5 (by decide)).symm.trans h))
      (fun h => hp7 ((rem 7 (by decide)).symm.trans h)) hnot
    simpa only [rem 120 (by decide), rem 168 (by decide)] using hh
  rcases hcases with h | h | h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, p = 120 * k + 73 := ⟨p / 120, by omega⟩
    refine ⟨30 * k + 20, (6 * k + 4) * (120 * k + 73), (15 * k + 10) * (120 * k + 73),
      by omega, by nlinarith, by nlinarith, ?_⟩
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, p = 120 * k + 97 := ⟨p / 120, by omega⟩
    refine ⟨30 * k + 25, (12 * k + 10) * (120 * k + 97), (60 * k + 50) * (120 * k + 97),
      by omega, by nlinarith, by nlinarith, ?_⟩
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, p = 168 * k + 73 := ⟨p / 168, by omega⟩
    refine ⟨42 * k + 21, (4 * k + 2) * (168 * k + 73), (84 * k + 42) * (168 * k + 73),
      by omega, by nlinarith, by nlinarith, ?_⟩
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, p = 168 * k + 145 := ⟨p / 168, by omega⟩
    refine ⟨42 * k + 38, (24 * k + 21) * (42 * k + 38),
      (24 * k + 21) * (21 * k + 19) * (168 * k + 145),
      by omega, by nlinarith, ?_, ?_⟩
    · rw [show 42 * k + 38 = (21 * k + 19) * 2 by omega, mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left (by omega) (by omega)) (by omega)
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, p = 168 * k + 97 := ⟨p / 168, by omega⟩
    refine ⟨42 * k + 26, (24 * k + 14) * (42 * k + 26),
      (24 * k + 14) * (42 * k + 26) * (168 * k + 97),
      by omega, by nlinarith, ?_, ?_⟩
    · conv_lhs => rw [← Nat.mul_one ((24 * k + 14) * (42 * k + 26))]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    push_cast
    field_simp
    ring

