import OMAStatements.S_oeis_a144135
import Mathlib

namespace OMA.P144135

open OMA.S_oeis_a144135

/-- The three-term recurrence of the Gegenbauer polynomials at lam = 2, x = 8. -/
lemma rec2 (n : ℕ) :
    ((n : ℚ) + 2) * a (n + 2) = 16 * ((n : ℚ) + 3) * a (n + 1) - ((n : ℚ) + 4) * a n := by
  have h : a (n + 2) = (2 * 8 * ((n : ℚ) + 1 + 2) * a (n + 1) - ((n : ℚ) + 2 * 2) * a n) / ((n : ℚ) + 2) := rfl
  rw [h]
  have hn : ((n : ℚ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The constant-coefficient recurrence, obtained as L2(n+2) - 16*L2(n+1) + L2(n). -/
lemma rec4 (m : ℕ) :
    a (m + 4) = 32 * a (m + 3) - 258 * a (m + 2) + 32 * a (m + 1) - a m := by
  have h0 := rec2 m
  have h1 := rec2 (m + 1)
  have h2 := rec2 (m + 2)
  push_cast at h1 h2
  have hm : ((m : ℚ) + 4) ≠ 0 := by positivity
  have key : ((m : ℚ) + 4) * (a (m + 4) - (32 * a (m + 3) - 258 * a (m + 2) + 32 * a (m + 1) - a m)) = 0 := by
    linear_combination h2 - 16 * h1 + h0
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hm
  · linarith

lemma rec (n : ℕ) (hn : 4 ≤ n) :
    a n = 32 * a (n - 1) - 258 * a (n - 2) + 32 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 - 4 = m := by omega
  rw [e1, e2, e3, e4]
  exact rec4 m

lemma va0 : a 0 = 1 := by norm_num [a, gegenbauer]
lemma va1 : a 1 = 32 := by norm_num [a, gegenbauer]
lemma va2 : a 2 = 766 := by norm_num [a, gegenbauer]
lemma va3 : a 3 = 16288 := by norm_num [a, gegenbauer]

end OMA.P144135

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a144135.main := by
  refine ⟨OMA.P144135.rec, ?_⟩
  have key : (PowerSeries.C (1 : ℚ) * PowerSeries.mk OMA.S_oeis_a144135.a)
      - (PowerSeries.C (32 : ℚ) * (PowerSeries.mk OMA.S_oeis_a144135.a * PowerSeries.X ^ 1))
      + (PowerSeries.C (258 : ℚ) * (PowerSeries.mk OMA.S_oeis_a144135.a * PowerSeries.X ^ 2))
      - (PowerSeries.C (32 : ℚ) * (PowerSeries.mk OMA.S_oeis_a144135.a * PowerSeries.X ^ 3))
      + (PowerSeries.C (1 : ℚ) * (PowerSeries.mk OMA.S_oeis_a144135.a * PowerSeries.X ^ 4))
      - (PowerSeries.C (1 : ℚ)) = 0 := by
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, map_zero]
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n <;> norm_num [OMA.P144135.va0, OMA.P144135.va1, OMA.P144135.va2,
        OMA.P144135.va3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h := OMA.P144135.rec (m + 4) (by omega)
      have z0 : ¬ (m + 4 = 0) := by omega
      have w1 : 1 ≤ m + 4 := by omega
      have w2 : 2 ≤ m + 4 := by omega
      have w3 : 3 ≤ m + 4 := by omega
      have w4 : 4 ≤ m + 4 := by omega
      simp only [z0, w1, w2, w3, w4, if_true, if_false, sub_zero]
      linear_combination h
  simp only [map_ofNat, map_one] at key
  linear_combination X * key
