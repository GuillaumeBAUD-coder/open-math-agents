import OMAStatements.S_oeis_a032088
import Mathlib

namespace A032088
open OMA.S_oeis_a032088 PowerSeries

lemma a_even (m : ℕ) (hm : 1 ≤ m) : a (2 * m) = ((5 : ℚ) ^ (2 * m) - 5 ^ m) / 2 := by
  unfold a
  have h1 : 2 * m ≠ 0 := by omega
  have h2 : 2 * m ≠ 1 := by omega
  have h3 : (2 * m + 1) / 2 = m := by omega
  rw [if_neg h1, if_neg h2, h3]

lemma a_odd (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 1) = ((5 : ℚ) ^ (2 * m + 1) - 5 ^ (m + 1)) / 2 := by
  unfold a
  have h1 : 2 * m + 1 ≠ 0 := by omega
  have h2 : 2 * m + 1 ≠ 1 := by omega
  have h3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [if_neg h1, if_neg h2, h3]

lemma rec1 (n : ℕ) (hn : 4 < n) : a n = 5 * a (n - 1) + 5 * a (n - 2) - 25 * a (n - 3) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    have e1 : 2 * (j + 2) - 1 = 2 * (j + 1) + 1 := by omega
    have e2 : 2 * (j + 2) - 2 = 2 * (j + 1) := by omega
    have e3 : 2 * (j + 2) - 3 = 2 * j + 1 := by omega
    rw [e1, e2, e3, a_even (j + 2) (by omega), a_odd (j + 1) (by omega),
      a_even (j + 1) (by omega), a_odd j (by omega)]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have e1 : 2 * (j + 1) + 1 - 1 = 2 * (j + 1) := by omega
    have e2 : 2 * (j + 1) + 1 - 2 = 2 * j + 1 := by omega
    have e3 : 2 * (j + 1) + 1 - 3 = 2 * j := by omega
    rw [e1, e2, e3, a_odd (j + 1) (by omega), a_even (j + 1) (by omega),
      a_odd j (by omega), a_even j (by omega)]
    ring

lemma coeff_lhs (f : PowerSeries ℚ) (n : ℕ) :
    coeff n ((1 - C 5 * X) * (1 - C 5 * X ^ 2) * f)
      = coeff n f - 5 * (if 1 ≤ n then coeff (n - 1) f else 0)
        - 5 * (if 2 ≤ n then coeff (n - 2) f else 0)
        + 25 * (if 3 ≤ n then coeff (n - 3) f else 0) := by
  have h25 : (C 25 : PowerSeries ℚ) = C 5 * C 5 := by
    rw [← map_mul]
    norm_num
  have e : (1 - C 5 * X) * (1 - C 5 * X ^ 2) * f
      = f - C 5 * (X ^ 1 * f) - C 5 * (X ^ 2 * f) + C 25 * (X ^ 3 * f) := by
    rw [h25]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

lemma coeff_rhs (n : ℕ) :
    coeff n (C 5 * X - C 15 * X ^ 2 - C 25 * X ^ 3 + C 125 * X ^ 4 : PowerSeries ℚ)
      = (if n = 1 then 5 else 0) - (if n = 2 then 15 else 0) - (if n = 3 then 25 else 0)
        + (if n = 4 then 125 else 0) := by
  have e : (C 5 * X - C 15 * X ^ 2 - C 25 * X ^ 3 + C 125 * X ^ 4 : PowerSeries ℚ)
      = C 5 * X ^ 1 - C 15 * X ^ 2 - C 25 * X ^ 3 + C 125 * X ^ 4 := by ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A032088

theorem OMA.solution : type_of% @OMA.S_oeis_a032088.main := by
  refine ⟨A032088.rec1, ?_, ?_, ?_⟩
  · ext n
    rw [A032088.coeff_lhs, A032088.coeff_rhs]
    simp only [OMA.S_oeis_a032088.series, PowerSeries.coeff_mk]
    rcases n with _ | _ | _ | _ | _ | k
    · norm_num [OMA.S_oeis_a032088.a]
    · norm_num [OMA.S_oeis_a032088.a]
    · norm_num [OMA.S_oeis_a032088.a]
    · norm_num [OMA.S_oeis_a032088.a]
    · norm_num [OMA.S_oeis_a032088.a]
    · have h := A032088.rec1 (k + 5) (by omega)
      have e1 : k + 5 - 1 = k + 4 := by omega
      have e2 : k + 5 - 2 = k + 3 := by omega
      have e3 : k + 5 - 3 = k + 2 := by omega
      rw [e1, e2, e3] at h
      have c1 : (1 : ℕ) ≤ k + 1 + 1 + 1 + 1 + 1 := by omega
      have c2 : (2 : ℕ) ≤ k + 1 + 1 + 1 + 1 + 1 := by omega
      have c3 : (3 : ℕ) ≤ k + 1 + 1 + 1 + 1 + 1 := by omega
      have d1 : k + 1 + 1 + 1 + 1 + 1 ≠ 1 := by omega
      have d2 : k + 1 + 1 + 1 + 1 + 1 ≠ 2 := by omega
      have d3 : k + 1 + 1 + 1 + 1 + 1 ≠ 3 := by omega
      have d4 : k + 1 + 1 + 1 + 1 + 1 ≠ 4 := by omega
      rw [if_pos c1, if_pos c2, if_pos c3, if_neg d1, if_neg d2, if_neg d3, if_neg d4]
      have f1 : k + 1 + 1 + 1 + 1 + 1 - 1 = k + 4 := by omega
      have f2 : k + 1 + 1 + 1 + 1 + 1 - 2 = k + 3 := by omega
      have f3 : k + 1 + 1 + 1 + 1 + 1 - 3 = k + 2 := by omega
      have f0 : k + 1 + 1 + 1 + 1 + 1 = k + 5 := by omega
      rw [f1, f2, f3, f0, h]
      ring
  · intro n hn he
    obtain ⟨m, rfl⟩ := he
    have e : m + m = 2 * m := by ring
    have e2 : 2 * m / 2 = m := by omega
    rw [e, e2, A032088.a_even m (by omega)]
    ring
  · intro n hn ho
    obtain ⟨m, rfl⟩ := ho
    have e2 : (2 * m + 1 - 1) / 2 = m := by omega
    have e3 : 2 * m + 1 - 1 = 2 * m := by omega
    rw [e2, e3, A032088.a_odd m (by omega)]
    ring
