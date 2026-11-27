import OMAStatements.S_oeis_a191821
import Mathlib

namespace A191821Aux
open OMA.S_oeis_a191821

noncomputable def F : PowerSeries ℚ := PowerSeries.mk (fun n => a (n + 1))

lemma b_eq (n : ℕ) : a (n + 1) = 2 ^ n * ((n : ℚ) ^ 2 + n + 2) - (n : ℚ) ^ 2 - n := by
  unfold a
  rw [Nat.add_sub_cancel]
  push_cast
  ring

lemma coeff_F_mul_X (k n : ℕ) :
    PowerSeries.coeff n (F * PowerSeries.X ^ k) = if k ≤ n then a (n - k + 1) else 0 := by
  simp only [PowerSeries.coeff_mul_X_pow', F, PowerSeries.coeff_mk]

lemma coeff_lhs (n : ℕ) :
    PowerSeries.coeff n (F * (1 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2) ^ 3) =
      a (n + 1) - 9 * (if 1 ≤ n then a (n - 1 + 1) else 0)
        + 33 * (if 2 ≤ n then a (n - 2 + 1) else 0)
        - 63 * (if 3 ≤ n then a (n - 3 + 1) else 0)
        + 66 * (if 4 ≤ n then a (n - 4 + 1) else 0)
        - 36 * (if 5 ≤ n then a (n - 5 + 1) else 0)
        + 8 * (if 6 ≤ n then a (n - 6 + 1) else 0) := by
  have expand : F * (1 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2) ^ 3 =
      F - PowerSeries.C 9 * (F * PowerSeries.X ^ 1) + PowerSeries.C 33 * (F * PowerSeries.X ^ 2)
        - PowerSeries.C 63 * (F * PowerSeries.X ^ 3) + PowerSeries.C 66 * (F * PowerSeries.X ^ 4)
        - PowerSeries.C 36 * (F * PowerSeries.X ^ 5)
        + PowerSeries.C 8 * (F * PowerSeries.X ^ 6) := by
    simp only [map_ofNat, pow_one]
    ring
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_F_mul_X]
  simp only [F, PowerSeries.coeff_mk]

lemma coeff_rhs (n : ℕ) :
    PowerSeries.coeff n (-(2 * (-1 + 6 * PowerSeries.X - 19 * PowerSeries.X ^ 2
        + 31 * PowerSeries.X ^ 3 - 22 * PowerSeries.X ^ 4
        + 4 * (PowerSeries.X : PowerSeries ℚ) ^ 5))) =
      (if n = 0 then 2 else 0) - 12 * (if n = 1 then 1 else 0) + 38 * (if n = 2 then 1 else 0)
        - 62 * (if n = 3 then 1 else 0) + 44 * (if n = 4 then 1 else 0)
        - 8 * (if n = 5 then 1 else 0) := by
  have expand : (-(2 * (-1 + 6 * PowerSeries.X - 19 * PowerSeries.X ^ 2
        + 31 * PowerSeries.X ^ 3 - 22 * PowerSeries.X ^ 4
        + 4 * (PowerSeries.X : PowerSeries ℚ) ^ 5))) =
      PowerSeries.C 2 - PowerSeries.C 12 * PowerSeries.X ^ 1 + PowerSeries.C 38 * PowerSeries.X ^ 2
        - PowerSeries.C 62 * PowerSeries.X ^ 3 + PowerSeries.C 44 * PowerSeries.X ^ 4
        - PowerSeries.C 8 * PowerSeries.X ^ 5 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_C]

end A191821Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a191821.main := by
  apply PowerSeries.ext
  intro n
  have hF : PowerSeries.mk (fun n => OMA.S_oeis_a191821.a (n + 1)) = A191821Aux.F := rfl
  rw [hF, A191821Aux.coeff_lhs, A191821Aux.coeff_rhs]
  by_cases hn : 6 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have e1 : m + 6 - 1 = m + 5 := by omega
    have e2 : m + 6 - 2 = m + 4 := by omega
    have e3 : m + 6 - 3 = m + 3 := by omega
    have e4 : m + 6 - 4 = m + 2 := by omega
    have e5 : m + 6 - 5 = m + 1 := by omega
    have e6 : m + 6 - 6 = m := by omega
    have c1 : 1 ≤ m + 6 := by omega
    have c2 : 2 ≤ m + 6 := by omega
    have c3 : 3 ≤ m + 6 := by omega
    have c4 : 4 ≤ m + 6 := by omega
    have c5 : 5 ≤ m + 6 := by omega
    have c6 : 6 ≤ m + 6 := by omega
    have d0 : ¬ (m + 6 = 0) := by omega
    have d1 : ¬ (m + 6 = 1) := by omega
    have d2 : ¬ (m + 6 = 2) := by omega
    have d3 : ¬ (m + 6 = 3) := by omega
    have d4 : ¬ (m + 6 = 4) := by omega
    have d5 : ¬ (m + 6 = 5) := by omega
    rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6, if_neg d0, if_neg d1,
      if_neg d2, if_neg d3, if_neg d4, if_neg d5, e1, e2, e3, e4, e5, e6]
    rw [A191821Aux.b_eq, A191821Aux.b_eq, A191821Aux.b_eq, A191821Aux.b_eq, A191821Aux.b_eq,
      A191821Aux.b_eq, A191821Aux.b_eq]
    push_cast
    ring
  · have hn' : n < 6 := by omega
    interval_cases n <;> norm_num [OMA.S_oeis_a191821.a]
