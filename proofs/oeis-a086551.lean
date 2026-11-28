import OMAStatements.S_oeis_a086551
import Mathlib

/-!
# OEIS A086551: disproof of the formalised conjecture

For n = 2 the least k with 2 ≤ k and tau(k) = 2 * tau(k - 1) is k = 2
(tau(2) = 2, tau(1) = 1), so a 2 = 2 and a 2 - 1 = 1 is not prime.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a086551.main) := by
  intro h
  have hmem : (2 : ℕ) ∈ {k : ℕ | 2 ≤ k ∧
      (Nat.divisors k).card = 2 * (Nat.divisors (k - 1)).card} := by
    refine ⟨le_refl 2, ?_⟩
    decide
  have hle : OMA.S_oeis_a086551.a 2 ≤ 2 := Nat.sInf_le hmem
  have hge : 2 ≤ OMA.S_oeis_a086551.a 2 := (Nat.sInf_mem ⟨2, hmem⟩).1
  have heq : OMA.S_oeis_a086551.a 2 = 2 := le_antisymm hle hge
  have hp := (h 2 (by norm_num)).2
  rw [heq] at hp
  exact Nat.not_prime_one hp
