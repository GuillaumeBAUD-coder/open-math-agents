import OMAStatements.S_oeis_a071722
import Mathlib

/-!
From C = 1 + X C^2 one gets X^2 (1 + X^2 C^2) C^3 = (2 - 4X + X^2) C - 2 + 2X, so
a(n) = 2 catalan(n+2) - 4 catalan(n+1) + catalan(n). With (k+2) catalan(k+1) = 2(2k+1) catalan(k)
every term becomes a rational multiple of catalan(n-3), and the recurrence is a rational identity.
-/

namespace R071722
open OMA.S_oeis_a071722 PowerSeries

theorem hc : catGF ^ 2 * X + 1 = catGF := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have hm : PowerSeries.map (Nat.castRingHom ℤ) catalanSeries = catGF := by
    ext n
    simp [catGF]
  rw [map_add, map_mul, map_pow, PowerSeries.map_X, map_one, hm] at h
  exact h

theorem coeff_c (n : ℕ) : coeff n catGF = (catalan n : ℤ) := by simp [catGF]

theorem hid : X ^ 2 * ((1 + X ^ 2 * catGF ^ 2) * catGF ^ 3) + 1 + 1 + X * catGF + X * catGF +
    X * catGF + X * catGF = catGF + catGF + X ^ 2 * catGF + X + X := by
  linear_combination (2 - 2 * X + 2 * X * catGF - X ^ 2 * catGF + X ^ 2 * catGF ^ 2 +
    X ^ 3 * catGF ^ 3) * hc

theorem a_eq (k : ℕ) :
    a k = 2 * (catalan (k + 1 + 1) : ℤ) - 4 * catalan (k + 1) + catalan k := by
  have h : coeff (k + 2) (X ^ 2 * ((1 + X ^ 2 * catGF ^ 2) * catGF ^ 3) + 1 + 1 + X * catGF +
      X * catGF + X * catGF + X * catGF) =
      coeff (k + 2) (catGF + catGF + X ^ 2 * catGF + X + X) := by
    rw [hid]
  simp only [map_add, coeff_X_pow_mul] at h
  rw [show k + 2 = (k + 1) + 1 from rfl, coeff_succ_X_mul] at h
  simp only [coeff_c, coeff_one, coeff_X] at h
  unfold a
  try split_ifs at h
  all_goals first | contradiction | omega | linarith

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

end R071722

theorem OMA.solution : type_of% @OMA.S_oeis_a071722.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, R071722.a_eq, R071722.a_eq, R071722.a_eq, R071722.a_eq]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  rw [R071722.catdiv (m + 4) (m + 5) rfl, R071722.catdiv (m + 3) (m + 4) rfl,
    R071722.catdiv (m + 2) (m + 3) rfl, R071722.catdiv (m + 1) (m + 2) rfl,
    R071722.catdiv m (m + 1) rfl]
  push_cast
  field_simp
  ring
