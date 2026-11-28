import OMAStatements.S_oeis_a049094

-- Disproof at n = 364 (the counterexample recorded in OEIS A049094): 364 = 4 * 7 * 13 is coprime
-- to 2^364 - 1, but 1093^2 divides 2^364 - 1 (1093 is a Wieferich prime and the order of 2
-- modulo 1093^2 is 364), so 2^364 - 1 is not squarefree.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a049094.main) := by
  intro h
  have hc : Nat.Coprime 364 (2 ^ 364 - 1) := by
    unfold Nat.Coprime
    decide
  have hd : 1093 * 1093 ∣ 2 ^ 364 - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    decide
  have hns : ¬ Squarefree (2 ^ 364 - 1) := by
    intro hsq
    have hu := hsq 1093 hd
    rw [Nat.isUnit_iff] at hu
    omega
  exact hns ((h 364 (by norm_num)).mpr hc)
