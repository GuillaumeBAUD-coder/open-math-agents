import OMAStatements.S_oeis_a346214

-- Problem: A346214: Triangular array read by rows. T(n,k) is the number of nilpotent n X n matrices over GF(2) with index k
-- Upstream: formal-conjectures statements/oeis-a346214.lean:0 (declaration OMA.S_oeis_a346214.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Refute the literal printed OEIS conjecture (with j < 2 * n) at n = 2, j = 1: LHS = 4 != 6 = RHS.

open OMA.S_oeis_a346214

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a346214.main) := by
  intro ⟨_, hfin⟩
  have ht : table 2 1 = 1 := by
    have hset : {M : BinaryMatrix 2 | 0 < 1 ∧ M ^ 1 = 0 ∧
        ∀ i : ℕ, 0 < i → i < 1 → M ^ i ≠ 0} = {(0 : BinaryMatrix 2)} := by
      ext M
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, pow_one, Nat.zero_lt_one, true_and]
      exact and_iff_left (fun i hi hj => by omega)
    rw [table, hset, Set.ncard_singleton]
  have h := hfin 2 1 (by decide) (by decide) (by decide)
  change table 2 1 * glOrder 1 * 4 = glOrder 2 * 1 at h
  rw [ht] at h
  exact (by decide : ¬ 1 * glOrder 1 * 4 = glOrder 2 * 1) h
