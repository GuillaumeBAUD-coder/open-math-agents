import OMAStatements.S_mo_206157
import Mathlib

/-!
MathOverflow 206157: for a prime `p ≥ 13`, `p^2 - 1 = 8xy` with `x, y ≥ 2` and `⌊xy/2⌋ = wz` with
`w, z ≥ 2`, according to `p mod 8`; so none of the first four quotients is prime.
-/

namespace OMA.P206157

lemma key (p : ℕ) (hp : p.Prime) (h13 : 13 ≤ p) :
    ∃ x y w z : ℕ, 2 ≤ x ∧ 2 ≤ y ∧ 2 ≤ w ∧ 2 ≤ z ∧ p ^ 2 = 8 * (x * y) + 1 ∧
      (x * y = 2 * (w * z) ∨ x * y = 2 * (w * z) + 1) := by
  have h2 : ¬ 2 ∣ p := fun h => by
    rcases hp.eq_one_or_self_of_dvd 2 h with h | h <;> omega
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  have ha : p = 8 * (p / 8) + p % 8 := (Nat.div_add_mod p 8).symm
  generalize p / 8 = a at ha
  rcases hr with h | h | h | h <;> rw [h] at ha <;> subst ha
  · exact ⟨2 * a, 4 * a + 1, a, 4 * a + 1, by omega, by omega, by omega, by omega,
      by ring, Or.inl (by ring)⟩
  · exact ⟨2 * a + 1, 4 * a + 1, a, 4 * a + 3, by omega, by omega, by omega, by omega,
      by ring, Or.inr (by ring)⟩
  · exact ⟨2 * a + 1, 4 * a + 3, a + 1, 4 * a + 1, by omega, by omega, by omega, by omega,
      by ring, Or.inr (by ring)⟩
  · exact ⟨2 * a + 2, 4 * a + 3, a + 1, 4 * a + 3, by omega, by omega, by omega, by omega,
      by ring, Or.inl (by ring)⟩

theorem solve :
    ∀ p : ℕ, p.Prime → 13 ≤ p → ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ¬ ((p ^ 2 - 1) / 2 ^ k).Prime := by
  intro p hp h13 k hk1 hk4
  obtain ⟨x, y, w, z, hx, hy, hw, hz, hsq, hxy⟩ := key p hp h13
  generalize p ^ 2 = N at hsq ⊢
  subst hsq
  have hxy2 : 4 ≤ x * y := Nat.mul_le_mul hx hy
  interval_cases k
  · have : (8 * (x * y) + 1 - 1) / 2 ^ 1 = (4 * x) * y := by
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num, Nat.mul_assoc]; omega
    rw [this]; exact Nat.not_prime_mul (by omega) (by omega)
  · have : (8 * (x * y) + 1 - 1) / 2 ^ 2 = (2 * x) * y := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, Nat.mul_assoc]; omega
    rw [this]; exact Nat.not_prime_mul (by omega) (by omega)
  · have : (8 * (x * y) + 1 - 1) / 2 ^ 3 = x * y := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; omega
    rw [this]; exact Nat.not_prime_mul (by omega) (by omega)
  · have : (8 * (x * y) + 1 - 1) / 2 ^ 4 = w * z := by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
      generalize x * y = X at hxy ⊢
      generalize w * z = W at hxy ⊢
      omega
    rw [this]; exact Nat.not_prime_mul (by omega) (by omega)

end OMA.P206157

theorem OMA.solution : type_of% @OMA.S_mo_206157.main := OMA.P206157.solve
