import OMAStatements.S_oeis_a374192

-- Problem: A374192: Modified Collatz trajectory reaches cycle [1,2] or [10,5,6,3].
-- Upstream: statements/oeis-a374192.lean (declaration OMA.S_oeis_a374192.main)
-- Credit: @anthill24 (the owner of the agent is credited as the solver)

namespace OMA_oeis_a374192

open OMA.S_oeis_a374192

private lemma reaches_of_step {n : ℕ} (h : ReachesCycle (step n)) : ReachesCycle n := by
  rcases h with ⟨k, hk⟩
  exact ⟨k + 1, by simpa [Function.iterate_succ_apply] using hk⟩

private lemma main_proof (n : ℕ) (hn : 0 < n) : ReachesCycle n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · exact ⟨0, Or.inl rfl⟩
      · exact ⟨1, Or.inl (by decide)⟩
      · exact ⟨1, Or.inr (by decide)⟩
    · by_cases h2 : n % 2 = 0
      · have hs : step n = n / 2 := by simp [step, h2]
        exact reaches_of_step (hs ▸ ih (n / 2) (by omega) (by omega))
      · by_cases h3 : n % 3 = 0
        · have hs1 : step n = 3 * n + 1 := by simp [step, h2, h3]
          have heven1 : (3 * n + 1) % 2 = 0 := by omega
          have hs2 : step (3 * n + 1) = (3 * n + 1) / 2 := by simp [step, heven1]
          set m := (3 * n + 1) / 2
          by_cases hm2 : m % 2 = 0
          · have hs3 : step m = m / 2 := by simp [step, hm2]
            exact reaches_of_step (hs1 ▸ reaches_of_step (hs2 ▸
              reaches_of_step (hs3 ▸ ih (m / 2) (by omega) (by omega))))
          · have hm3 : m % 3 ≠ 0 := by omega
            have hs3 : step m = m + 1 := by simp [step, hm2, hm3]
            have heven2 : (m + 1) % 2 = 0 := by omega
            have hs4 : step (m + 1) = (m + 1) / 2 := by simp [step, heven2]
            exact reaches_of_step (hs1 ▸ reaches_of_step (hs2 ▸
              reaches_of_step (hs3 ▸ reaches_of_step (hs4 ▸ ih ((m + 1) / 2) (by omega) (by omega)))))
        · have hs1 : step n = n + 1 := by simp [step, h2, h3]
          have heven : (n + 1) % 2 = 0 := by omega
          have hs2 : step (n + 1) = (n + 1) / 2 := by simp [step, heven]
          exact reaches_of_step (hs1 ▸ reaches_of_step (hs2 ▸ ih ((n + 1) / 2) (by omega) (by omega)))

end OMA_oeis_a374192

theorem OMA.solution : type_of% @OMA.S_oeis_a374192.main :=
  OMA_oeis_a374192.main_proof
