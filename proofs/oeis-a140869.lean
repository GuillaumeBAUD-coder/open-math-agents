import OMAStatements.S_oeis_a140869

theorem OMA.solution : type_of% @OMA.S_oeis_a140869.main := by
  intro h hh
  by_contra hp
  apply hh
  set N := 4 * h + 5 with hN
  have hN1 : N ≠ 1 := by omega
  have hpr : (Nat.minFac N).Prime := Nat.minFac_prime hN1
  set p := Nat.minFac N with hpdef
  have hpd : p ∣ N := Nat.minFac_dvd N
  have hsq : p ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hp
  obtain ⟨q, hq⟩ := hpd
  have hp2 : 2 ≤ p := hpr.two_le
  have hpodd : p % 2 = 1 := by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have : N = 2 * (k * q) := by rw [hq, hk]; ring
      omega
    · omega
  have hqodd : q % 2 = 1 := by
    rcases Nat.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have : N = 2 * (p * k) := by rw [hq, hk]; ring
      omega
    · omega
  have hpq : p ≤ q := by
    by_contra hlt
    rw [not_le] at hlt
    have : p * q < p * p := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    nlinarith
  clear_value p N
  refine ⟨q / 2, p / 2, by omega, by omega, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, p = 2 * n + 1 := ⟨p / 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have e1 : (2 * n + 1) / 2 = n := by omega
  have e2 : (2 * m + 1) / 2 = m := by omega
  rw [e1, e2]
  unfold OMA.S_oeis_a140869.T
  have key : 4 * (m * n) + 2 * m + 2 * n + 1 = 4 * h + 5 := by
    rw [← hN, hq]; ring
  have e3 : 2 * m * n = 2 * (m * n) := by ring
  rw [e3]
  omega
