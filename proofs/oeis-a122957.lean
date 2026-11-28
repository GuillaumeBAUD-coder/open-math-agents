import OMAStatements.S_oeis_a122957

-- Problem: A122957: Numbers n such that if m > n, phi(m) >= phi(n).
-- Upstream: formal-conjectures statements/oeis-a122957.lean:0 (declaration OMA.S_oeis_a122957.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: m = 22 is a counterexample. phi(21) = 12 and phi(22) = 10, so A066362(21) = 22 (no
-- integer lies strictly between 21 and 22), and 22 is a nonzero value of A066362. But
-- phi(30) = 8 < 10 = phi(22), so 22 is not a term of A122957.

namespace L05A122957

open OMA.S_oeis_a122957

theorem t2 : Nat.totient 2 = 1 := Nat.totient_prime Nat.prime_two

theorem t3 : Nat.totient 3 = 2 := Nat.totient_prime Nat.prime_three

theorem t5 : Nat.totient 5 = 4 := Nat.totient_prime (by norm_num)

theorem t7 : Nat.totient 7 = 6 := Nat.totient_prime (by norm_num)

theorem t11 : Nat.totient 11 = 10 := Nat.totient_prime (by norm_num)

theorem t21 : Nat.totient 21 = 12 := by
  have e : Nat.totient (3 * 7) = Nat.totient 3 * Nat.totient 7 := Nat.totient_mul (by norm_num)
  rw [t3, t7] at e
  exact e

theorem t22 : Nat.totient 22 = 10 := by
  have e : Nat.totient (2 * 11) = Nat.totient 2 * Nat.totient 11 := Nat.totient_mul (by norm_num)
  rw [t2, t11] at e
  exact e

theorem t6 : Nat.totient 6 = 2 := by
  have e : Nat.totient (2 * 3) = Nat.totient 2 * Nat.totient 3 := Nat.totient_mul (by norm_num)
  rw [t2, t3] at e
  exact e

theorem t30 : Nat.totient 30 = 8 := by
  have e : Nat.totient (5 * 6) = Nat.totient 5 * Nat.totient 6 := Nat.totient_mul (by norm_num)
  rw [t5, t6] at e
  exact e

theorem lt2221 : Nat.totient 22 < Nat.totient 21 := by
  rw [t22, t21]
  norm_num

theorem hex : ∃ k : ℕ, 21 < k ∧ Nat.totient k < Nat.totient 21 :=
  ⟨22, by norm_num, lt2221⟩

theorem hA : A066362 21 = 22 := by
  unfold A066362
  rw [dif_pos hex]
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, lt2221⟩, ?_⟩
  intro k hk hk2
  have h1 := hk2.1
  omega

end L05A122957

open OMA.S_oeis_a122957 L05A122957 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a122957.main) := by
  intro H
  have h := (H 22).2 ⟨by norm_num, 21, by norm_num, hA⟩
  obtain ⟨⟨_, hall⟩, _⟩ := h
  have h30 := hall 30 (by norm_num)
  rw [t22, t30] at h30
  omega
