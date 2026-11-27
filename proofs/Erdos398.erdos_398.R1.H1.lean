import OMAReductions.R_Erdos398_erdos_398_R1

-- Step Erdos398.erdos_398.R1.H1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 := by
  intro n hn
  have h4 : 4 ∣ n.factorial :=
    dvd_trans (by decide : 4 ∣ Nat.factorial 4) (Nat.factorial_dvd_factorial hn)
  have hdiv : 4 * (n.factorial / 4) = n.factorial := Nat.mul_div_cancel' h4
  constructor
  · rintro ⟨m, hm⟩
    have hmod : m % 2 = 1 := by
      by_contra h
      have h0 : m % 2 = 0 := by omega
      have hsq : (m ^ 2) % 2 = 0 := by
        rw [sq, Nat.mul_mod, h0]
      omega
    set x := m / 2
    refine ⟨x, ?_⟩
    have hm_eq : m = 2 * x + 1 := by omega
    have hsq : m ^ 2 = 4 * (x * (x + 1)) + 1 := by
      rw [hm_eq]
      ring
    omega
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have hsq : (2 * x + 1) ^ 2 = 4 * (x * (x + 1)) + 1 := by ring
    omega
