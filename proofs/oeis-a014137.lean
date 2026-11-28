import OMAStatements.S_oeis_a014137
import Mathlib

/-!
Credit: @ivillar
Proof idea (Peter J. Taylor's remark in the OEIS entry): writing a(n) = a(n-2) + C(n-1) + C(n),
Mathar's recurrence reduces to (n+1)*C(n) = 2*(2*n-1)*C(n-1), which follows from Mathlib's
central binomial coefficient facts.
-/

namespace OMAA014137Helpers

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

theorem a_succ (n : ℕ) : OMA.S_oeis_a014137.a (n + 1) =
    OMA.S_oeis_a014137.a n + (catalan (n + 1) : ℤ) := by
  unfold OMA.S_oeis_a014137.a
  rw [Finset.sum_range_succ]

end OMAA014137Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a014137.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega,
    show m + 2 = (m + 1) + 1 from rfl, OMAA014137Helpers.a_succ (m + 1),
    OMAA014137Helpers.a_succ m]
  have h' := OMAA014137Helpers.cat_rec (m + 1) (m + 1 + 1) rfl
  push_cast at h' ⊢
  linear_combination h'
