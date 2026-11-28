import OMAStatements.S_oeis_a215462
import Mathlib

/-!
OEIS A215462: every even number 2n > 38 is a sum of two odd numbers that are not prime.

Choose a in {15, 27, 9, 21, 33} according to n mod 5 so that b = 2n - a ends in the digit 5.
Then b is odd, divisible by 5 and at least 7, so b is not prime; and a is odd and composite.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a215462.main := by
  intro n hn
  have key : ∀ a : ℕ, Odd a → ¬ a.Prime → a ≤ 33 → (2 * n - a) % 10 = 5 →
      ∃ a b : ℕ, Odd a ∧ Odd b ∧ ¬ a.Prime ∧ ¬ b.Prime ∧ a + b = 2 * n := by
    intro a ha hna ha33 hmod
    have ha2 := Nat.odd_iff.mp ha
    refine ⟨a, 2 * n - a, ha, ?_, hna, ?_, by omega⟩
    · rw [Nat.odd_iff]
      omega
    · intro hp
      have h5 : 5 ∣ 2 * n - a := by omega
      rcases (Nat.dvd_prime hp).mp h5 with h | h
      · omega
      · omega
  have h10 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases h10 with h | h | h | h | h
  · exact key 15 ⟨7, by norm_num⟩ (by norm_num) (by norm_num) (by omega)
  · exact key 27 ⟨13, by norm_num⟩ (by norm_num) (by norm_num) (by omega)
  · exact key 9 ⟨4, by norm_num⟩ (by norm_num) (by norm_num) (by omega)
  · exact key 21 ⟨10, by norm_num⟩ (by norm_num) (by norm_num) (by omega)
  · exact key 33 ⟨16, by norm_num⟩ (by norm_num) (by norm_num) (by omega)
