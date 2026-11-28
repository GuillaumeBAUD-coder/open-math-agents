import OMAStatements.S_oeis_a268898

-- Credit: @Dariusthedoggie
-- Proof: closed form count k x 0 = 2^k and count (k+1) x 1 = (k+1) * 2^k by induction on k.

namespace OMA.P268898

open OMA.S_oeis_a268898 PowerSeries

lemma count_zero (k : ℕ) (x : Color) : count k x 0 = 2 ^ k := by
  induction k generalizing x with
  | zero => simp [count]
  | succ k ih =>
    fin_cases x <;> simp [count, colors, ih, pow_succ] <;> ring

lemma count_one (k : ℕ) (x : Color) : count (k + 1) x 1 = (k + 1) * 2 ^ k := by
  induction k generalizing x with
  | zero =>
    fin_cases x <;> decide
  | succ k ih =>
    fin_cases x <;>
    · rw [count]
      simp only [colors, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd, Nat.reduceEqDiff,
        ↓reduceIte, count_zero, ih]
      ring

lemma a_closed (n : ℕ) : a (n + 1) = 4 ^ n * (6 * n + 3) := by
  simp only [a, colors, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [count_one (2 * n) 0, count_one (2 * n) 1, count_one (2 * n) 2]
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4]
  ring

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 3 := by simpa using a_closed 0
lemma a_2 : a 2 = 36 := by simpa using a_closed 1

theorem main_proof : type_of% @OMA.S_oeis_a268898.main := by
  refine ⟨?_, ?_, a_closed⟩
  · intro n
    rw [a_closed (n + 2), a_closed (n + 1), a_closed n]
    have h1 : 4 ^ (n + 1) = 4 * 4 ^ n := by ring
    have h2 : 4 ^ (n + 2) = 16 * 4 ^ n := by ring
    rw [h1, h2]
    ring
  · set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
    have hL : (1 - 4 * X : PowerSeries ℚ) ^ 2 * F =
        F - C 8 * (F * X ^ 1) + C 16 * (F * X ^ 2) := by
      simp only [map_ofNat]; ring
    have hR : (3 * X * (1 + 4 * X) : PowerSeries ℚ) =
        C 3 * X ^ 1 + C 12 * X ^ 2 := by
      simp only [map_ofNat]; ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, F, coeff_mk]
    rcases n with _ | _ | _ | m
    · simp [a_0]
    · simp [a_0, a_1]
    · simp [a_0, a_1, a_2]; norm_num
    · have ha3 : (a (m + 3) : ℚ) = 4 ^ (m + 2) * (6 * (m + 2) + 3) := by exact_mod_cast a_closed (m + 2)
      have ha2 : (a (m + 2) : ℚ) = 4 ^ (m + 1) * (6 * (m + 1) + 3) := by exact_mod_cast a_closed (m + 1)
      have ha1 : (a (m + 1) : ℚ) = 4 ^ m * (6 * m + 3) := by exact_mod_cast a_closed m
      have c1 : 1 ≤ m + 3 := by omega
      have c2 : 2 ≤ m + 3 := by omega
      simp only [c1, c2, ↓reduceIte, show m + 3 - 1 = m + 2 by omega,
        show m + 3 - 2 = m + 1 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega]
      rw [ha3, ha2, ha1]
      ring

end OMA.P268898

theorem OMA.solution : type_of% @OMA.S_oeis_a268898.main := OMA.P268898.main_proof
