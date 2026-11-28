import OMAReductions.R_Erdos396_erdos_396_R1

theorem descFactorial_dvd_of_le {n k l : ℕ} (h : k ≤ l) :
    n.descFactorial k ∣ n.descFactorial l := by
  induction l, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ l _ ih =>
    rw [Nat.descFactorial_succ]
    exact ih.trans (dvd_mul_left _ _)

set_option maxRecDepth 4000 in
theorem OMA.solution : OMA.R_Erdos396_erdos_396_R1.H1 := by
  intro k hk
  have h : Nat.descFactorial 45153 5 ∣ Nat.centralBinom 45153 := by
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.choose_eq_factorial_div_factorial (by decide),
      Nat.factorial_eq_factorialBinarySplitting]
    decide +kernel
  exact ⟨45153, (descFactorial_dvd_of_le (n := 45153) (show k + 1 ≤ 5 by omega)).trans h⟩
