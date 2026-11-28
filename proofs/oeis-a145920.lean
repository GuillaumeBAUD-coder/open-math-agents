import OMAStatements.S_oeis_a145920
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a145920

lemma ae (m : ℕ) : a (2 * m) = (27 * (m : ℚ) ^ 4 - 18 * m ^ 3 - 3 * m ^ 2 + 2 * m) / 8 := by
  have : 2 * m / 2 = m := by omega
  simp [a, x, this, pow_mul]

lemma ao (m : ℕ) : a (2 * m + 1) = (27 * (m : ℚ) ^ 4 + 18 * m ^ 3 - 3 * m ^ 2 - 2 * m) / 8 := by
  have : (2 * m + 1) / 2 = m := by omega
  simp [a, x, this, pow_succ, pow_mul]
  ring

lemma rec10 (n : ℕ) (hn : 10 ≤ n) :
    a n - (a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) - 6 * a (n - 4) + 6 * a (n - 5) + 4 * a (n - 6) -
        4 * a (n - 7) - a (n - 8) + a (n - 9)) = 0 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [show 2 * (k + 5) - 1 = 2 * (k + 4) + 1 by omega, show 2 * (k + 5) - 2 = 2 * (k + 4) by omega,
      show 2 * (k + 5) - 3 = 2 * (k + 3) + 1 by omega, show 2 * (k + 5) - 4 = 2 * (k + 3) by omega,
      show 2 * (k + 5) - 5 = 2 * (k + 2) + 1 by omega, show 2 * (k + 5) - 6 = 2 * (k + 2) by omega,
      show 2 * (k + 5) - 7 = 2 * (k + 1) + 1 by omega, show 2 * (k + 5) - 8 = 2 * (k + 1) by omega,
      show 2 * (k + 5) - 9 = 2 * k + 1 by omega]
    simp only [ae, ao]
    push_cast
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [show 2 * (k + 5) + 1 - 1 = 2 * (k + 5) by omega, show 2 * (k + 5) + 1 - 2 = 2 * (k + 4) + 1 by omega,
      show 2 * (k + 5) + 1 - 3 = 2 * (k + 4) by omega, show 2 * (k + 5) + 1 - 4 = 2 * (k + 3) + 1 by omega,
      show 2 * (k + 5) + 1 - 5 = 2 * (k + 3) by omega, show 2 * (k + 5) + 1 - 6 = 2 * (k + 2) + 1 by omega,
      show 2 * (k + 5) + 1 - 7 = 2 * (k + 2) by omega, show 2 * (k + 5) + 1 - 8 = 2 * (k + 1) + 1 by omega,
      show 2 * (k + 5) + 1 - 9 = 2 * (k + 1) by omega]
    simp only [ae, ao]
    push_cast
    ring

lemma poly : ((1 + X) ^ 4 * (1 - X) ^ 5 : ℚ⟦X⟧) =
    C 1 * X ^ 0 + C (-1) * X ^ 1 + C (-4) * X ^ 2 + C 4 * X ^ 3 + C 6 * X ^ 4 + C (-6) * X ^ 5
      + C (-4) * X ^ 6 + C 4 * X ^ 7 + C 1 * X ^ 8 + C (-1) * X ^ 9 := by
  simp only [map_neg, map_one, map_ofNat]
  ring

lemma rhs : (X ^ 2 * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 26 * X ^ 4 + 4 * X ^ 5 + X ^ 6) : ℚ⟦X⟧) =
    C 1 * X ^ 2 + C 4 * X ^ 3 + C 26 * X ^ 4 + C 19 * X ^ 5 + C 26 * X ^ 6 + C 4 * X ^ 7 + C 1 * X ^ 8 := by
  simp only [map_one, map_ofNat]
  ring

lemma cm (f : ℚ⟦X⟧) (c : ℚ) (d n : ℕ) :
    coeff n (f * (C c * X ^ d)) = c * if d ≤ n then coeff (n - d) f else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']

lemma cm' (c : ℚ) (d n : ℕ) :
    coeff n ((C c * X ^ d : ℚ⟦X⟧)) = c * if n = d then 1 else 0 := by
  rw [coeff_C_mul, coeff_X_pow]

end OMA.S_oeis_a145920

theorem OMA.solution : type_of% @OMA.S_oeis_a145920.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · have := OMA.S_oeis_a145920.rec10 n hn
    linarith
  · ext n
    rw [OMA.S_oeis_a145920.poly, OMA.S_oeis_a145920.rhs]
    simp only [mul_add, map_add, OMA.S_oeis_a145920.cm, OMA.S_oeis_a145920.cm', coeff_mk]
    by_cases hn : 10 ≤ n
    · have := OMA.S_oeis_a145920.rec10 n hn
      have e : ∀ d : ℕ, d ≤ 9 → (d ≤ n) := fun d hd => by omega
      simp [e, hn, show ¬ n = 2 by omega, show ¬ n = 3 by omega, show ¬ n = 4 by omega,
        show ¬ n = 5 by omega, show ¬ n = 6 by omega, show ¬ n = 7 by omega, show ¬ n = 8 by omega]
      linarith
    · replace hn : n < 10 := not_le.mp hn
      interval_cases n <;> simp [OMA.S_oeis_a145920.a, OMA.S_oeis_a145920.x] <;> norm_num
