import OMAStatements.S_oeis_a164704
import Mathlib

/-!
Since 10 ≡ 1 (mod 9), n^2 = q·10^m + r ≡ q + r = n (mod 9), so n(n - 1) ≡ 0 (mod 9); checking the
nine residues, n ≡ 0 or 1 (mod 9).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a164704.main := by
  rintro n ⟨-, ⟨m, q, r, -, -, hn, hsq⟩, -⟩
  have h10 : 10 ^ m % 9 = 1 := by
    rw [Nat.pow_mod]
    simp
  have hsq9 : n ^ 2 % 9 = n % 9 := by
    rw [hsq, hn, Nat.add_mod, Nat.mul_mod, h10, Nat.add_mod q r]
    simp
  have key : (n % 9) ^ 2 % 9 = n % 9 := by
    rw [← Nat.pow_mod]
    exact hsq9
  have hlt : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  generalize n % 9 = t at key hlt ⊢
  interval_cases t <;> simp_all
