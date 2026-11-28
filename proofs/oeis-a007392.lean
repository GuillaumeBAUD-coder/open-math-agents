import OMAStatements.S_oeis_a007392
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a007392

lemma he (k : ℕ) : e (k + 9) = e (k + 7) + e (k + 4) := rfl

lemma hb (k : ℕ) : b (k + 6) - 2 * b (k + 4) + b (k + 2) = 0 := by
  unfold b
  split_ifs <;> push_cast <;> omega

lemma rec13 (k : ℕ) : a (k + 13) = 3 * a (k + 11) - 3 * a (k + 9) + a (k + 8) + a (k + 7)
    - 2 * a (k + 6) + a (k + 4) := by
  simp only [a]
  have h1 := he (k + 4)
  have h2 := he (k + 2)
  have h3 := he k
  have g1 := hb (k + 7)
  have g2 := hb (k + 5)
  have g3 := hb (k + 2)
  have g4 := hb (k + 3)
  have g5 := hb (k + 1)
  have g6 := hb k
  simp only [show k + 4 + 9 = k + 13 by ring, show k + 4 + 7 = k + 11 by ring,
    show k + 2 + 9 = k + 11 by ring, show k + 2 + 7 = k + 9 by ring,
    show k + 7 + 6 = k + 13 by ring, show k + 7 + 4 = k + 11 by ring, show k + 7 + 2 = k + 9 by ring,
    show k + 5 + 6 = k + 11 by ring, show k + 5 + 4 = k + 9 by ring, show k + 5 + 2 = k + 7 by ring,
    show k + 2 + 6 = k + 8 by ring, show k + 2 + 4 = k + 6 by ring,
    show k + 3 + 6 = k + 9 by ring, show k + 3 + 4 = k + 7 by ring, show k + 3 + 2 = k + 5 by ring,
    show k + 1 + 6 = k + 7 by ring, show k + 1 + 4 = k + 5 by ring, show k + 1 + 2 = k + 3 by ring] at *
  linarith

lemma poly : ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2 : ℤ⟦X⟧) =
    X ^ 9 + C (-2) * X ^ 7 + X ^ 6 + X ^ 5 + C (-3) * X ^ 4 + C 3 * X ^ 2 + C (-1) * X ^ 0 := by
  simp only [map_neg, pow_zero, mul_one]
  have h2 : (C 2 : ℤ⟦X⟧) = 2 := by simp
  have h3 : (C 3 : ℤ⟦X⟧) = 3 := by simp
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := by simp
  rw [h2, h3, h1]; ring

lemma rhs : (X ^ 10 * (-5 + 3 * X ^ 2) : ℤ⟦X⟧) = C (-5) * X ^ 10 + C 3 * X ^ 12 := by
  simp only [map_neg]
  have h2 : (C 5 : ℤ⟦X⟧) = 5 := by simp
  have h3 : (C 3 : ℤ⟦X⟧) = 3 := by simp
  rw [h2, h3]; ring

lemma cm (f : ℤ⟦X⟧) (c : ℤ) (d n : ℕ) :
    coeff n (f * (C c * X ^ d)) = c * if d ≤ n then coeff (n - d) f else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']

lemma cx (f : ℤ⟦X⟧) (d n : ℕ) :
    coeff n (f * X ^ d) = if d ≤ n then coeff (n - d) f else 0 := coeff_mul_X_pow' _ _ _

lemma coeffs (n : ℕ) : coeff n (PowerSeries.mk (fun n => a n) * ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2 : ℤ⟦X⟧)) =
    (if 9 ≤ n then a (n - 9) else 0) + (-2) * (if 7 ≤ n then a (n - 7) else 0) + (if 6 ≤ n then a (n - 6) else 0)
    + (if 5 ≤ n then a (n - 5) else 0) + (-3) * (if 4 ≤ n then a (n - 4) else 0)
    + 3 * (if 2 ≤ n then a (n - 2) else 0) + (-1) * a n := by
  rw [poly]
  simp only [mul_add, map_add, cm, cx, coeff_mk]
  simp

lemma rhs_coeff (n : ℕ) : coeff n (X ^ 10 * (-5 + 3 * X ^ 2) : ℤ⟦X⟧) = (if n = 10 then -5 else 0) + (if n = 12 then 3 else 0) := by
  rw [rhs, map_add, mul_comm (C (-5)), mul_comm (C 3), coeff_mul_C, coeff_mul_C, coeff_X_pow, coeff_X_pow]
  split_ifs <;> simp

end OMA.S_oeis_a007392

theorem OMA.solution : type_of% @OMA.S_oeis_a007392.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
    have := OMA.S_oeis_a007392.rec13 k
    simpa using this
  · ext n
    rw [OMA.S_oeis_a007392.coeffs, OMA.S_oeis_a007392.rhs_coeff]
    by_cases hn : 13 ≤ n
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
      have := OMA.S_oeis_a007392.rec13 k
      simp [show k + 13 - 9 = k + 4 by omega, show k + 13 - 7 = k + 6 by omega,
        show k + 13 - 6 = k + 7 by omega, show k + 13 - 5 = k + 8 by omega,
        show k + 13 - 4 = k + 9 by omega, show k + 13 - 2 = k + 11 by omega]
      linarith
    · replace hn : n < 13 := not_le.mp hn
      interval_cases n <;> simp [OMA.S_oeis_a007392.a, OMA.S_oeis_a007392.e, OMA.S_oeis_a007392.b]
