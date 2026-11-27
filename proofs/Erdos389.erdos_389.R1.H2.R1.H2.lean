import OMAReductions.R_Erdos389_erdos_389_R1_H2_R1

theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1_H2_R1.H2 := by
  intro n k hn hk hval
  let A : ℕ := ∏ i ∈ Finset.range k, (n + i)
  let B : ℕ := ∏ i ∈ Finset.range k, (n + k + i)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by omega
  have hB : B ≠ 0 := by
    dsimp [B]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by omega
  change A ∣ B
  rw [← Nat.factorization_le_iff_dvd hA hB]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def A hp, Nat.factorization_def B hp]
    exact hval p hp
  · rw [Nat.factorization_eq_zero_of_not_prime A hp,
      Nat.factorization_eq_zero_of_not_prime B hp]
