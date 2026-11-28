import OMAStatements.S_oeis_a296159

-- Problem: A296159: Sum of the smaller parts in the partitions of n into two distinct parts with the larger part odd.
-- Upstream: formal-conjectures statements/oeis-a296159.lean:0 (declaration OMA.S_oeis_a296159.main)
-- Credit: @jarrettbranch (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a296159

open OMA.S_oeis_a296159

/-- Shifting `n` by 4 adds `2 * (n / 4) + 1 + n % 2`. -/
theorem step (n : ℕ) : a (n + 4) = a n + (2 * (n / 4) + 1 + n % 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  unfold a
  rw [show (n + 4 - 1) / 2 = (n - 1) / 2 + 1 + 1 by omega,
    Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  have hsum : ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), i * ((n + 4 - i) % 2) =
      ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), i * ((n - i) % 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    congr 1
    omega
  rw [hsum]
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · rw [show (n + 4 - ((n - 1) / 2 + 1)) % 2 = 0 by omega,
      show (n + 4 - ((n - 1) / 2 + 1 + 1)) % 2 = 1 by omega]
    omega
  · rw [show (n + 4 - ((n - 1) / 2 + 1)) % 2 = 0 by omega,
      show (n + 4 - ((n - 1) / 2 + 1 + 1)) % 2 = 1 by omega]
    omega
  · rw [show (n + 4 - ((n - 1) / 2 + 1)) % 2 = 1 by omega,
      show (n + 4 - ((n - 1) / 2 + 1 + 1)) % 2 = 0 by omega]
    omega
  · rw [show (n + 4 - ((n - 1) / 2 + 1)) % 2 = 1 by omega,
      show (n + 4 - ((n - 1) / 2 + 1 + 1)) % 2 = 0 by omega]
    omega

end OMA.P_oeis_a296159

theorem OMA.solution : type_of% @OMA.S_oeis_a296159.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  have e1 := OMA.P_oeis_a296159.step (k + 5)
  have e2 := OMA.P_oeis_a296159.step (k + 1)
  have e3 := OMA.P_oeis_a296159.step (k + 4)
  have e4 := OMA.P_oeis_a296159.step k
  rw [show k + 5 + 4 = k + 9 by omega] at e1
  rw [show k + 1 + 4 = k + 5 by omega] at e2
  rw [show k + 4 + 4 = k + 8 by omega] at e3
  rw [show k + 9 - 1 = k + 8 by omega, show k + 9 - 4 = k + 5 by omega,
    show k + 9 - 5 = k + 4 by omega, show k + 9 - 8 = k + 1 by omega,
    show k + 9 - 9 = k by omega]
  omega
