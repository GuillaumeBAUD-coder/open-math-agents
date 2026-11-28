import OMAStatements.S_oeis_a092960

-- Problem: A092960: Least square of the form 'sum of n successive terms of a geometric progression + 1', or 0 if no such square exists.
-- Upstream: formal-conjectures statements/oeis-a092960.lean:0 (declaration OMA.S_oeis_a092960.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea (from the entry, Opao 2005 and Su 2026): n = 1: 3 + 1 = 2^2. n >= 2: with 2^n = k + 4,
-- the progression (k+1), 2(k+1), ..., 2^(n-1)(k+1) has sum (k+1)(k+3), and (k+1)(k+3) + 1 = (k+2)^2.

namespace H07A092960

theorem geom2 (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

end H07A092960

open OMA.S_oeis_a092960 H07A092960 in
theorem OMA.solution : type_of% @OMA.S_oeis_a092960.main := by
  intro n hn
  by_cases h1 : n = 1
  · subst h1
    refine ⟨3, 2, 2, by norm_num, le_refl 2, ?_⟩
    norm_num [gpSumPlusOne]
  · have h : 2 ≤ n := by omega
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 4 := ⟨2 ^ n - 4, by omega⟩
    refine ⟨k + 1, 2, k + 2, by omega, le_refl 2, ?_⟩
    have g := geom2 n
    rw [hk] at g
    have hs : ∑ i ∈ Finset.range n, (k + 1) * 2 ^ i = (k + 1) * (k + 3) := by
      rw [← Finset.mul_sum]
      congr 1
      omega
    unfold gpSumPlusOne
    rw [hs]
    ring
