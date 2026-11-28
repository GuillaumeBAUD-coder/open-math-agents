import OMAReductions.R_erdos_301_R1
import Mathlib

-- Step erdos-301.R1.H1: hypothesis H1 of reduction erdos-301.R1 (Erdős Problem 301).
-- For every N, N <= 2 f(N), where f(N) is the largest size of a subset A of {1..N} with no solution of
-- 1/a = 1/b_1 + ... + 1/b_k in distinct elements of A.
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: take A = (N/2, N]. For a in A we have 1/a < 2/N. A set B of at least two elements of A has reciprocal
-- sum at least 2/N, an empty B has sum 0, and a single b gives 1/b = 1/a only for b = a, which is excluded.
-- So A has no solution, and it has N - N/2 >= N/2 elements.

open OMA.S_erdos_301

theorem OMA.solution : OMA.R_erdos_301_R1.H1 := by
  intro N
  have hsub : Finset.Ioc (N / 2) N ⊆ Finset.Icc 1 N := by
    intro x hx
    rw [Finset.mem_Ioc] at hx
    rw [Finset.mem_Icc]
    omega
  have hno : NoUnitFractionSolution (Finset.Ioc (N / 2) N) := by
    intro a ha B hB haB heq
    rw [Finset.mem_Ioc] at ha
    have hapos : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    have hNpos : (0 : ℚ) < N := by exact_mod_cast (show 0 < N by omega)
    have h1 : (1 : ℚ) / a < 2 / N := by
      rw [div_lt_div_iff₀ hapos hNpos]
      have h2 : 1 * N < 2 * a := by omega
      exact_mod_cast h2
    rcases Nat.lt_or_ge B.card 2 with hc | hc
    · have hc' : B.card = 0 ∨ B.card = 1 := by omega
      rcases hc' with h0 | h1c
      · rw [Finset.card_eq_zero] at h0
        subst h0
        rw [Finset.sum_empty] at heq
        have hp : (0 : ℚ) < 1 / a := by positivity
        linarith
      · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h1c
        rw [Finset.sum_singleton] at heq
        have hq : (a : ℚ) = b := by
          have h := congrArg (fun x : ℚ => 1 / x) heq
          simpa using h
        have hab : a = b := by exact_mod_cast hq
        exact haB (by rw [hab]; exact Finset.mem_singleton_self b)
    · have hterm : ∀ b ∈ B, (1 : ℚ) / N ≤ 1 / (b : ℚ) := by
        intro b hb
        have hb' := hB hb
        rw [Finset.mem_Ioc] at hb'
        have hbpos : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
        apply one_div_le_one_div_of_le hbpos
        exact_mod_cast hb'.2
      have hsum : (2 : ℚ) / N ≤ ∑ b ∈ B, 1 / (b : ℚ) := by
        calc (2 : ℚ) / N = 2 * (1 / N) := by ring
          _ ≤ (B.card : ℚ) * (1 / N) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hc
          _ = ∑ b ∈ B, (1 : ℚ) / N := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ b ∈ B, 1 / (b : ℚ) := Finset.sum_le_sum hterm
      rw [heq] at h1
      linarith
  have hmem : Finset.Ioc (N / 2) N ∈ (Finset.Icc 1 N).powerset.filter NoUnitFractionSolution :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hno⟩
  have hle : (Finset.Ioc (N / 2) N).card ≤ f N := Finset.le_sup (f := Finset.card) hmem
  rw [Nat.card_Ioc] at hle
  omega
