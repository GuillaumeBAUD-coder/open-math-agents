import OMAStatements.S_oeis_a164704
import Mathlib

/-
A164704: every Kaprekar number is 0 or 1 modulo 9.

If n^2 = q * 10^m + r and n = q + r then, since 10^m is 1 modulo 9, n^2 is congruent to n
modulo 9, and the only residues r with r^2 = r modulo 9 are 0 and 1.
-/

namespace OMA.P164704

lemma main' :
    ∀ n : ℕ, (1 ≤ n ∧
      (∃ m q r : ℕ, 1 ≤ m ∧ r < 10 ^ m ∧ n = q + r ∧ n ^ 2 = q * 10 ^ m + r) ∧
      (∀ a : ℕ, 1 ≤ a → n ≠ 10 ^ a)) → n % 9 = 0 ∨ n % 9 = 1 := by
  rintro n ⟨-, ⟨m, q, r, -, -, hn, hsq⟩, -⟩
  have h10 : 10 ^ m % 9 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h1 : q * 10 ^ m % 9 = q % 9 := by
    rw [Nat.mul_mod, h10, mul_one, Nat.mod_mod]
  have h2 : n ^ 2 % 9 = n % 9 := by
    rw [hsq, Nat.add_mod, h1, ← Nat.add_mod, ← hn]
  have h3 : n ^ 2 % 9 = (n % 9) ^ 2 % 9 := Nat.pow_mod n 2 9
  have hlt : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 9 <;> omega

end OMA.P164704

theorem OMA.solution : type_of% @OMA.S_oeis_a164704.main := OMA.P164704.main'
