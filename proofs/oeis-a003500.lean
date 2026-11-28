import OMAStatements.S_oeis_a003500

-- Problem: oeis-a003500
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

open OMA.S_oeis_a003500

private lemma consecutive : ∀ n : ℕ, 2 ∣ a n ∧ 2 ∣ a (n + 1) ∧ 2 ≤ a n ∧ a n < a (n + 1)
  | 0 => by decide
  | n + 1 => by
    obtain ⟨ha, hb, hle, hlt⟩ := consecutive n
    change 2 ∣ a (n + 1) ∧ 2 ∣ a (n + 2) ∧ 2 ≤ a (n + 1) ∧ a (n + 1) < a (n + 2)
    rw [a]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a003500.main := by
  intro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  obtain ⟨-, hdvd, hle, hlt⟩ := consecutive n
  change 1 < a (n + 1) ∧ ¬ Prime (a (n + 1))
  refine ⟨by omega, ?_⟩
  rw [Int.prime_iff_natAbs_prime]
  intro hprime
  have hd : 2 ∣ (a (n + 1)).natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
  have := hprime.eq_one_or_self_of_dvd 2 hd
  rw [← Int.natAbs_of_nonneg (show 0 ≤ a (n + 1) by omega)] at hlt
  omega
