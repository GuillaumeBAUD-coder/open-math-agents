import OMAReductions.R_OeisA238585_conjecture_1_R1

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA238585_conjecture_1_R1.H1 := by
  intro n hn
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos hn (by decide)
  have hle : n ≤ 6 := Nat.le_of_dvd (by decide) hn
  have hmem : n ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    have h : ∀ m ∈ Finset.Icc 1 6, m ∣ 6 → m ∈ ({1, 2, 3, 6} : Finset ℕ) := by decide
    exact h n (Finset.mem_Icc.mpr ⟨hpos, hle⟩) hn
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    have hc : Nat.count Nat.Prime 13 = 5 := by decide
    have h := (13).nth_count (by decide : Nat.Prime 13)
    rw [hc] at h; exact h
  have key : ∀ p ∈ Finset.Ico 1 6,
      ¬ (p.Prime ∧ Nat.Prime (Nat.nth Nat.Prime (p - 1) ^ 2 + (Nat.nth Nat.Prime 5 - 1) ^ 2)) := by
    intro p hp
    have h1 : 1 ≤ p := (Finset.mem_Ico.mp hp).1
    have h2 : p < 6 := (Finset.mem_Ico.mp hp).2
    interval_cases p <;>
      simp [Nat.reduceSub, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven, h5] <;>
      decide
  fin_cases hmem
  · exact OeisA238585.a_1
  · exact OeisA238585.a_2
  · exact OeisA238585.a_3
  · simp only [OeisA238585.a]
    apply Finset.sum_eq_zero
    intro p hp
    rw [if_neg (key p hp)]
