import OMAStatements.S_oeis_a101602
import Mathlib

/-!
From c = 1 + X c^2 one gets X^3 c^4 = (1 - 2X) c - (1 - X), so the coefficient of x^n in c^4 is
catalan(n+3) - 2 catalan(n+2). With (k+2) catalan(k+1) = 2(2k+1) catalan(k) every term becomes a
rational multiple of catalan(n), and the recurrence is a rational identity.
-/

namespace R101602
open OMA.S_oeis_a101602 PowerSeries

theorem hc : c ^ 2 * X + 1 = c := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have hm : PowerSeries.map (Nat.castRingHom ℤ) catalanSeries = c := by
    ext n
    simp [c]
  rw [map_add, map_mul, map_pow, PowerSeries.map_X, map_one, hm] at h
  exact h

theorem coeff_c (n : ℕ) : coeff n c = (catalan n : ℤ) := by simp [c]

theorem hid : X ^ 3 * c ^ 4 + 1 + X * c + X * c = c + X := by
  linear_combination (1 - X + X * c + X ^ 2 * c ^ 2) * hc

theorem coeff4 (k : ℕ) : coeff k (c ^ 4) = (catalan (k + 2 + 1) : ℤ) - 2 * catalan (k + 2) := by
  have h : coeff (k + 3) (X ^ 3 * c ^ 4 + 1 + X * c + X * c) = coeff (k + 3) (c + X) := by
    rw [hid]
  simp only [map_add] at h
  rw [coeff_X_pow_mul] at h
  rw [show k + 3 = (k + 2) + 1 from rfl, coeff_succ_X_mul] at h
  simp only [coeff_c, coeff_one, coeff_X] at h
  try split_ifs at h
  all_goals first | contradiction | omega | linarith

theorem a_eq (k : ℕ) : a k = 3 ^ k * ((catalan (k + 2 + 1) : ℤ) - 2 * catalan (k + 2)) := by
  unfold a
  rw [← map_pow, coeff_rescale, coeff4]

theorem catdiv (k j : ℕ) (h : j = k + 1) :
    (catalan j : ℚ) = 2 * (2 * k + 1) / (k + 2) * catalan k := by
  subst h
  have h1 : ((k : ℚ) + 1 + 1) * (catalan (k + 1) : ℚ) = (Nat.centralBinom (k + 1) : ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 : ((k : ℚ) + 1) * (catalan k : ℚ) = (Nat.centralBinom k : ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom k
  have h3 : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
      2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hk : (k : ℚ) + 2 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have key : ((k : ℚ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
    apply mul_left_cancel₀ hk1
    linear_combination ((k : ℚ) + 1) * h1 + h3 - 2 * (2 * (k : ℚ) + 1) * h2
  rw [div_mul_eq_mul_div, eq_div_iff hk]
  linear_combination key

end R101602

theorem OMA.solution : type_of% @OMA.S_oeis_a101602.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    R101602.a_eq, R101602.a_eq, R101602.a_eq]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  rw [R101602.catdiv (m + 4) (m + 5) rfl, R101602.catdiv (m + 3) (m + 4) rfl,
    R101602.catdiv (m + 2) (m + 3) rfl]
  push_cast
  field_simp
  ring
