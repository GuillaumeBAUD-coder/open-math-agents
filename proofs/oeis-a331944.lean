import OMAStatements.S_oeis_a331944
import Mathlib

namespace OMA.S_oeis_a331944

lemma E_big (e : ℕ) : E (e + 6) = (6 + (E (e+5) + E (e+4) + E (e+3) + E (e+2) + E (e+1) + E e)) / 6 := by
  rw [show e + 6 = (e + 5) + 1 by rfl, E]
  have : min (e + 5 + 1) 6 = 6 := by omega
  rw [this]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h : ∀ k, k < 6 → k + 1 ≤ e + 5 + 1 := fun k hk => by omega
  simp only [if_pos (h 0 (by norm_num)), if_pos (h 1 (by norm_num)), if_pos (h 2 (by norm_num)),
    if_pos (h 3 (by norm_num)), if_pos (h 4 (by norm_num)), if_pos (h 5 (by norm_num))]
  rw [show e + 5 - 0 = e + 5 by omega, show e + 5 - 1 = e + 4 by omega,
    show e + 5 - 2 = e + 3 by omega, show e + 5 - 3 = e + 2 by omega,
    show e + 5 - 4 = e + 1 by omega, show e + 5 - 5 = e by omega]
  push_cast
  ring

lemma E_step (e : ℕ) : E (e + 7) = (7 * E (e + 6) - E e) / 6 := by
  have h1 := E_big (e + 1)
  have h2 := E_big e
  rw [show e + 1 + 6 = e + 7 by rfl] at h1
  simp only [show e + 1 + 5 = e + 6 by rfl, show e + 1 + 4 = e + 5 by rfl,
    show e + 1 + 3 = e + 4 by rfl, show e + 1 + 2 = e + 3 by rfl, show e + 1 + 1 = e + 2 by rfl] at h1
  linarith

lemma a_eq (n : ℕ) (hn : 7 ≤ n) : a n = E n * 6 ^ (n - 7) := by
  unfold a
  have : (6 : ℚ) ^ ((n : ℤ) - 7) = ((6 ^ (n - 7) : ℕ) : ℚ) := by
    rw [show ((n : ℤ) - 7) = ((n - 7 : ℕ) : ℤ) by omega, zpow_natCast]; push_cast; rfl
  rw [this, Int.ceil_natCast]; push_cast; rfl

lemma rec_a (n : ℕ) (hn : 14 ≤ n) : a n = 7 * a (n - 1) - 46656 * a (n - 7) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 14 := ⟨n - 14, by omega⟩
  have h1 : a (e + 14) = E (e + 14) * 6 ^ (e + 7) := by
    rw [a_eq _ (by omega)]; rfl
  have h2 : a (e + 14 - 1) = E (e + 13) * 6 ^ (e + 6) := by
    rw [a_eq _ (by omega)]; rfl
  have h3 : a (e + 14 - 7) = E (e + 7) * 6 ^ e := by
    rw [a_eq _ (by omega)]; rfl
  have h' : E (e + 14) = (7 * E (e + 13) - E (e + 7)) / 6 := E_step (e + 7)
  rw [h1, h2, h3, h']
  rw [pow_add, pow_add]
  ring

lemma a_small (n : ℕ) (hn : n ≤ 7) : a n = E n := by
  unfold a
  have : ⌈(6 : ℚ) ^ ((n : ℤ) - 7)⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    interval_cases n <;> norm_num
  rw [this]; simp

lemma E1 : E 1 = 6 := by simp [E, Finset.sum_range_succ]
lemma E2 : E 2 = 6 := by simp [E, Finset.sum_range_succ, E1] <;> norm_num
lemma E3 : E 3 = 6 := by simp [E, Finset.sum_range_succ, E1, E2] <;> norm_num
lemma E4 : E 4 = 6 := by simp [E, Finset.sum_range_succ, E1, E2, E3] <;> norm_num
lemma E5 : E 5 = 6 := by simp [E, Finset.sum_range_succ, E1, E2, E3, E4] <;> norm_num
lemma E6 : E 6 = 6 := by simp [E, Finset.sum_range_succ, E1, E2, E3, E4, E5] <;> norm_num
lemma E0 : E 0 = 0 := by simp [E]
lemma E7 : E 7 = 7 := by
  have := E_big 1; simp only [show 1 + 6 = 7 from rfl, show 1 + 5 = 6 from rfl, show 1 + 4 = 5 from rfl,
    show 1 + 3 = 4 from rfl, show 1 + 2 = 3 from rfl] at this
  rw [this, E6, E5, E4, E3, E2, E1]; norm_num
lemma E8 : E 8 = 43/6 := by
  have := E_big 2; simp only [show 2 + 6 = 8 from rfl, show 2 + 5 = 7 from rfl, show 2 + 4 = 6 from rfl,
    show 2 + 3 = 5 from rfl, show 2 + 2 = 4 from rfl, show 2 + 1 = 3 from rfl] at this
  rw [this, E7, E6, E5, E4, E3, E2]; norm_num
lemma E9 : E 9 = 265/36 := by
  have := E_big 3; simp only [show 3 + 6 = 9 from rfl, show 3 + 5 = 8 from rfl, show 3 + 4 = 7 from rfl,
    show 3 + 3 = 6 from rfl, show 3 + 2 = 5 from rfl, show 3 + 1 = 4 from rfl] at this
  rw [this, E8, E7, E6, E5, E4, E3]; norm_num
lemma E10 : E 10 = 1639/216 := by
  have := E_big 4; simp only [show 4 + 6 = 10 from rfl, show 4 + 5 = 9 from rfl, show 4 + 4 = 8 from rfl,
    show 4 + 3 = 7 from rfl, show 4 + 2 = 6 from rfl, show 4 + 1 = 5 from rfl] at this
  rw [this, E9, E8, E7, E6, E5, E4]; norm_num
lemma E11 : E 11 = 10177/1296 := by
  have := E_big 5; simp only [show 5 + 6 = 11 from rfl, show 5 + 5 = 10 from rfl, show 5 + 4 = 9 from rfl,
    show 5 + 3 = 8 from rfl, show 5 + 2 = 7 from rfl, show 5 + 1 = 6 from rfl] at this
  rw [this, E10, E9, E8, E7, E6, E5]; norm_num
lemma E12 : E 12 = 63463/7776 := by
  have := E_big 6; simp only [show 6 + 6 = 12 from rfl, show 6 + 5 = 11 from rfl, show 6 + 4 = 10 from rfl,
    show 6 + 3 = 9 from rfl, show 6 + 2 = 8 from rfl, show 6 + 1 = 7 from rfl] at this
  rw [this, E11, E10, E9, E8, E7, E6]; norm_num
lemma E13 : E 13 = 397585/46656 := by
  have := E_big 7; simp only [show 7 + 6 = 13 from rfl, show 7 + 5 = 12 from rfl, show 7 + 4 = 11 from rfl,
    show 7 + 3 = 10 from rfl, show 7 + 2 = 9 from rfl, show 7 + 1 = 8 from rfl] at this
  rw [this, E12, E11, E10, E9, E8, E7]; norm_num

lemma a1 : a 1 = 6 := by rw [a_small 1 (by norm_num), E1]
lemma a2 : a 2 = 6 := by rw [a_small 2 (by norm_num), E2]
lemma a3 : a 3 = 6 := by rw [a_small 3 (by norm_num), E3]
lemma a4 : a 4 = 6 := by rw [a_small 4 (by norm_num), E4]
lemma a5 : a 5 = 6 := by rw [a_small 5 (by norm_num), E5]
lemma a6 : a 6 = 6 := by rw [a_small 6 (by norm_num), E6]
lemma a7 : a 7 = 7 := by rw [a_small 7 (by norm_num), E7]
lemma a8 : a 8 = 43 := by rw [a_eq 8 (by norm_num), E8]; norm_num
lemma a9 : a 9 = 265 := by rw [a_eq 9 (by norm_num), E9]; norm_num
lemma a10 : a 10 = 1639 := by rw [a_eq 10 (by norm_num), E10]; norm_num
lemma a11 : a 11 = 10177 := by rw [a_eq 11 (by norm_num), E11]; norm_num
lemma a12 : a 12 = 63463 := by rw [a_eq 12 (by norm_num), E12]; norm_num
lemma a13 : a 13 = 397585 := by rw [a_eq 13 (by norm_num), E13]; norm_num

open PowerSeries in
theorem cm (g : ℕ → ℚ) (n : ℕ) : coeff n (mk g * (1 - 7 * X + 46656 * X ^ 7)) =
   g n - 7 * (if 1 ≤ n then g (n-1) else 0) + 46656 * (if 7 ≤ n then g (n-7) else 0) := by
  have e : (1 - 7 * X + 46656 * X ^ 7 : PowerSeries ℚ) = 1 - C (7:ℚ) * X ^ 1 + C (46656:ℚ) * X ^ 7 := by
    simp only [map_ofNat, pow_one]
  have e2 : ∀ (c : ℚ) (k : ℕ), mk g * (C c * X ^ k) = C c * (mk g * X ^ k) := by
    intros; ring
  rw [e, mul_add, mul_sub, map_add, map_sub, mul_one, e2, e2]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]

open PowerSeries in
theorem num (n : ℕ) : coeff n (X * (6 - 36 * X - 36 * X ^ 2 - 36 * X ^ 3 -
        36 * X ^ 4 - 36 * X ^ 5 - 35 * X ^ 6 +
        279930 * X ^ 7 + 279900 * X ^ 8 + 279720 * X ^ 9 +
        278640 * X ^ 10 + 272160 * X ^ 11 + 233280 * X ^ 12 : PowerSeries ℚ)) =
    6 * (if n = 1 then 1 else 0) - 36 * (if n = 2 then 1 else 0) - 36 * (if n = 3 then 1 else 0)
    - 36 * (if n = 4 then 1 else 0) - 36 * (if n = 5 then 1 else 0) - 36 * (if n = 6 then 1 else 0)
    - 35 * (if n = 7 then 1 else 0) + 279930 * (if n = 8 then 1 else 0)
    + 279900 * (if n = 9 then 1 else 0) + 279720 * (if n = 10 then 1 else 0)
    + 278640 * (if n = 11 then 1 else 0) + 272160 * (if n = 12 then 1 else 0)
    + 233280 * (if n = 13 then 1 else 0) := by
  have e : (X * (6 - 36 * X - 36 * X ^ 2 - 36 * X ^ 3 -
        36 * X ^ 4 - 36 * X ^ 5 - 35 * X ^ 6 +
        279930 * X ^ 7 + 279900 * X ^ 8 + 279720 * X ^ 9 +
        278640 * X ^ 10 + 272160 * X ^ 11 + 233280 * X ^ 12 : PowerSeries ℚ)) =
     C (6:ℚ) * X ^ 1 - C (36:ℚ) * X ^ 2 - C (36:ℚ) * X ^ 3 - C (36:ℚ) * X ^ 4 - C (36:ℚ) * X ^ 5
     - C (36:ℚ) * X ^ 6 - C (35:ℚ) * X ^ 7 + C (279930:ℚ) * X ^ 8 + C (279900:ℚ) * X ^ 9
     + C (279720:ℚ) * X ^ 10 + C (278640:ℚ) * X ^ 11 + C (272160:ℚ) * X ^ 12 + C (233280:ℚ) * X ^ 13 := by
    simp only [map_ofNat]; ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]

end OMA.S_oeis_a331944

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a331944.main := by
  refine ⟨?_, fun n hn => OMA.S_oeis_a331944.rec_a n hn⟩
  have hD : ((1 - 6 * (X : PowerSeries ℚ)) ^ 2 *
          (1 + 5 * X + 24 * X ^ 2 + 108 * X ^ 3 + 432 * X ^ 4 + 1296 * X ^ 5)) =
      1 - 7 * X + 46656 * X ^ 7 := by ring
  rw [hD]
  ext n
  rw [OMA.S_oeis_a331944.cm, OMA.S_oeis_a331944.num]
  rcases Nat.lt_or_ge n 14 with hn | hn
  · interval_cases n <;>
      simp [OMA.S_oeis_a331944.a1, OMA.S_oeis_a331944.a2, OMA.S_oeis_a331944.a3,
        OMA.S_oeis_a331944.a4, OMA.S_oeis_a331944.a5, OMA.S_oeis_a331944.a6,
        OMA.S_oeis_a331944.a7, OMA.S_oeis_a331944.a8, OMA.S_oeis_a331944.a9,
        OMA.S_oeis_a331944.a10, OMA.S_oeis_a331944.a11, OMA.S_oeis_a331944.a12,
        OMA.S_oeis_a331944.a13] <;> norm_num
  · have hr := OMA.S_oeis_a331944.rec_a n hn
    have h1 : n ≠ 0 := by omega
    have h2 : n - 1 ≠ 0 := by omega
    have h3 : n - 7 ≠ 0 := by omega
    simp [h1, h2, h3, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
      show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega,
      show n ≠ 12 by omega, show n ≠ 13 by omega, show 1 ≤ n by omega, show 7 ≤ n by omega]
    linarith
