import OMAStatements.S_oeis_a175784
import Mathlib
open OMA.S_oeis_a175784

lemma cop4 (x y : ℕ) (hy : y % 2 = 1) (h : Nat.Coprime x y) : Nat.Coprime (4 * x) y := by
  apply Nat.Coprime.mul_left _ h
  have : Nat.Coprime 2 y := by
    rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hy
  simpa using Nat.Coprime.pow_left 2 this

lemma gcd5 (n : ℕ) : Nat.gcd (n + 2) 5 = if (n + 2) % 5 = 0 then 5 else 1 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  have : (n + 2) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (n + 2) % 5 <;> simp

lemma part1 (n : ℕ) : a n = 4 * (((n + 2) / Nat.gcd (n + 2) 5 : ℕ) : ℤ) := by
  have hq : q n = (4 * ((n : ℚ) + 2)) / (2 * n + 9) := by
    unfold q
    have : (2 * (n : ℚ) + 9) ≠ 0 := by positivity
    field_simp; ring
  by_cases h5 : 5 ∣ n + 2
  · obtain ⟨t, ht⟩ := h5
    have hg : Nat.gcd (n + 2) 5 = 5 := by rw [ht]; simp
    rw [hg, ht, Nat.mul_div_cancel_left t (by norm_num)]
    have htq : (n : ℚ) + 2 = 5 * t := by exact_mod_cast ht
    have : q n = ((4 * t : ℤ) : ℚ) / ((2 * t + 1 : ℤ) : ℚ) := by
      rw [hq, div_eq_div_iff (by positivity) (by push_cast; positivity)]
      push_cast
      linear_combination (4 : ℚ) * htq
    unfold a
    rw [this, Rat.num_div_eq_of_coprime (by positivity)]
    · have : Int.natAbs (2 * (t : ℤ) + 1) = 2 * t + 1 := by omega
      rw [this]
      have : Int.natAbs (4 * (t : ℤ)) = 4 * t := by omega
      rw [this]
      apply cop4 _ _ (by omega)
      simp
  · have hg : Nat.gcd (n + 2) 5 = 1 := by
      rw [gcd5]; simp; omega
    rw [hg, Nat.div_one]
    have : q n = ((4 * (n + 2 : ℕ) : ℤ) : ℚ) / ((2 * n + 9 : ℕ) : ℤ) := by
      rw [hq]; push_cast; ring
    unfold a
    rw [this, Rat.num_div_eq_of_coprime (by positivity)]
    · have : Int.natAbs (((2 * n + 9 : ℕ) : ℤ)) = 2 * n + 9 := by omega
      rw [this]
      have : Int.natAbs (4 * ((n + 2 : ℕ) : ℤ)) = 4 * (n + 2) := by omega
      rw [this]
      apply cop4 _ _ (by omega)
      have e : 2 * n + 9 = 5 + (n + 2) * 2 := by ring
      rw [Nat.Coprime, e, Nat.gcd_add_mul_left_right, gcd5]
      simp; omega

lemma part2 (n : ℕ) (hn : 11 ≤ n) : a n = 2 * a (n - 5) - a (n - 10) := by
  rw [part1 n, part1 (n - 5), part1 (n - 10), gcd5, gcd5, gcd5]
  split_ifs <;> omega

open PowerSeries in
lemma part3 : series * ((X - 1)^2 * (X^4 + X^3 + X^2 + X + 1)^2) =
      -4 * X * (-3 - 4*X - X^2 - 6*X^3 - 7*X^4 - 2*X^5 - X^6 + X^8 + 2*X^9) := by
  have e1 : ((X : PowerSeries ℚ) - 1)^2 * (X^4 + X^3 + X^2 + X + 1)^2 = 1 - 2 * X^5 + X^10 := by ring
  have e2 : (-4 * X * (-3 - 4*X - X^2 - 6*X^3 - 7*X^4 - 2*X^5 - X^6 + X^8 + 2*X^9) : PowerSeries ℚ)
     = C (12:ℚ) * X^1 + C (16:ℚ) * X^2 + C (4:ℚ) * X^3 + C (24:ℚ) * X^4 + C (28:ℚ) * X^5 + C (8:ℚ) * X^6
       + C (4:ℚ) * X^7 - C (4:ℚ) * X^9 - C (8:ℚ) * X^10 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  have e3 : (1 - 2 * X^5 + X^10 : PowerSeries ℚ) = 1 - C (2:ℚ) * X^5 + X^10 := by simp only [map_ofNat]
  have e4 : series * (1 - C (2:ℚ) * X^5 + X^10) = series - C (2:ℚ) * (series * X^5) + series * X^10 := by ring
  rw [e3, e4]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', series, coeff_mk]
  by_cases hn : n ≤ 10
  · interval_cases n <;> simp [part1] <;> norm_num
  · have h2 := part2 n (by omega)
    have h2' : ((a n : ℤ) : ℚ) = 2 * a (n - 5) - a (n - 10) := by exact_mod_cast h2
    have f1 : n - 1 ≠ 0 := by omega
    have f2 : n - 2 ≠ 0 := by omega
    have f3 : n - 3 ≠ 0 := by omega
    have f4 : n - 4 ≠ 0 := by omega
    have f5 : n - 5 ≠ 0 := by omega
    have f6 : n - 6 ≠ 0 := by omega
    have f7 : n - 7 ≠ 0 := by omega
    have f9 : n - 9 ≠ 0 := by omega
    have f10 : n - 10 ≠ 0 := by omega
    simp [coeff_C, f1, f2, f3, f4, f5, f6, f7, f9, f10, show n ≠ 0 by omega, show 1 ≤ n by omega,
      show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show 6 ≤ n by omega, show 7 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega]
    rw [h2']; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a175784.main :=
  ⟨fun n _ => part1 n, part2, part3⟩
