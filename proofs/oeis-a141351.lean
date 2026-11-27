import OMAStatements.S_oeis_a141351
import Mathlib

/-!
Credit: @ivillar
Proof: the Catalan recurrence (k+2) C(k+1) = 2(2k+1) C(k) (from Mathlib central binomial facts);
the recurrence operator is a combination of shifts of it, and annihilates the remaining terms.
-/

namespace OMAA141351Helpers

theorem cat_rec (k j : ℕ) (hj : j = k + 1) :
    ((k : ℤ) + 2) * (catalan j : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  subst hj
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k)
    calc (k + 1) * ((k + 2) * catalan (k + 1))
        = (k + 1) * Nat.centralBinom (k + 1) := by rw [← h1]
      _ = 2 * (2 * k + 1) * Nat.centralBinom k := h3
      _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by rw [← h2]; ring
  exact_mod_cast h

theorem a_pos (k : ℕ) (hk : 0 < k) : OMA.S_oeis_a141351.a k = (catalan k : ℤ) + 1 := by
  simp [OMA.S_oeis_a141351.a, zero_pow hk.ne']

end OMAA141351Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a141351.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega,
    show m + 4 - 3 = m + 1 from by omega, OMAA141351Helpers.a_pos (m + 4) (by omega),
    OMAA141351Helpers.a_pos (m + 3) (by omega), OMAA141351Helpers.a_pos (m + 2) (by omega),
    OMAA141351Helpers.a_pos (m + 1) (by omega)]
  have h3 := OMAA141351Helpers.cat_rec (m + 3) (m + 4) rfl
  have h2 := OMAA141351Helpers.cat_rec (m + 2) (m + 3) rfl
  have h1 := OMAA141351Helpers.cat_rec (m + 1) (m + 2) rfl
  push_cast at h1 h2 h3 ⊢
  linear_combination h3 - 2 * h2 + h1
