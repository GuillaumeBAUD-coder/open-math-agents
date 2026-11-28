import OMAStatements.S_oeis_a155587
import Mathlib

/-!
Credit: @ivillar
Proof (as in Petros Hadjicostas's argument in the OEIS entry): multiplying by 1/(1-x) takes partial
sums, so a(m+1) = a(m) + C(m); Mathar's recurrence then reduces to the Catalan recurrence
(m+2)*C(m+1) = 2*(2m+1)*C(m).
-/

namespace OMAA155587Helpers
open PowerSeries OMA.S_oeis_a155587

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

theorem a_eq (n : ℕ) : a n = ∑ j ∈ Finset.range (n + 1), coeff j (1 + X * c) := by
  unfold a
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk, mul_one]

theorem a_succ (m : ℕ) : a (m + 1) = a m + (catalan m : ℤ) := by
  rw [a_eq, a_eq (m), Finset.sum_range_succ (n := m + 1), map_add, coeff_succ_X_mul, coeff_one]
  simp [c, coeff_mk]

end OMAA155587Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a155587.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega,
    show m + 2 = (m + 1) + 1 from rfl, OMAA155587Helpers.a_succ (m + 1),
    OMAA155587Helpers.a_succ m]
  have h := OMAA155587Helpers.cat_rec m (m + 1) rfl
  push_cast at h ⊢
  linear_combination h
