import OMAStatements.S_oeis_a291502
import Mathlib

namespace OMA.S_oeis_a291502

open Finset PowerSeries

private theorem ceil_one (m d : ℕ) (hm : 0 < m) (hmd : m ≤ d) :
    ⌈(m : ℚ) / d⌉ = 1 := by
  apply Int.ceil_eq_iff.mpr
  have hd : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hmd' : (m : ℚ) ≤ d := by exact_mod_cast hmd
  constructor
  · simpa using div_pos hm' hd
  · simpa using (div_le_iff₀ hd).mpr (by simpa using hmd')

private theorem large_divisor (n d : ℕ) (hd : 8 < d) :
    val n 1 8 d = -6 * (d : ℤ) := by
  have h1 := ceil_one 1 d (by decide) (by omega)
  have h8 := ceil_one 8 d (by decide) (by omega)
  have h1' : ⌈(1 : ℚ) / (d : ℚ)⌉ = 1 := h1
  have h8' : ⌈(8 : ℚ) / (d : ℚ)⌉ = 1 := h8
  have hd' : (8 : ℤ) < d := by exact_mod_cast hd
  have hs : ¬ (8 : ℤ) ≤ min 1 ((d : ℤ) - 1) := by
    intro h
    have bound := h.trans (min_le_left _ _)
    norm_num at bound
  unfold val
  norm_num only [Nat.cast_ofNat, h1', h8', mul_one, sub_add_cancel, if_neg hs]
  unfold delta
  simp only [show ¬ (8 : ℤ) < 1 by decide, show (1 : ℤ) < 8 by decide,
    hd', true_and, if_true, if_false]
  have he : (-55 : ℤ) - ((d - 8) * (8 - 1) - (d - 1)) = -6 * (d : ℤ) := by
    ring
  rw [he, min_eq_right (by omega)]

private theorem small_value (n d : ℕ) (hd : 0 < d) (hsmall : d ≤ 8) :
    val n 1 8 d = min (n : ℤ) (if d = 3 ∨ d = 6 then -54 else -55) := by
  interval_cases d
  · have h₁ : ⌈(1 : ℚ) / 1⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 1⌉ = 8 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 2⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 2⌉ = 4 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 3⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 3⌉ = 3 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 4⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 4⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 5⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 5⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 6⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 6⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 7⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 7⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]
  · have h₁ : ⌈(1 : ℚ) / 8⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    have h₈ : ⌈(8 : ℚ) / 8⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, h₁, h₈]

private theorem unit_divisor (n : ℕ) : val n 1 8 1 = -55 := by
  rw [small_value n 1 (by decide) (by decide)]
  norm_num

private theorem small_divisor (n d : ℕ) (hd : 0 < d) (hsmall : d ≤ 8) :
    (-55 : ℤ) ≤ val n 1 8 d := by
  rw [small_value n d hd hsmall]
  refine le_min (by omega) ?_
  split_ifs <;> decide

private theorem closed (n : ℕ) (hn : 0 < n) :
    a n = min (-55) (-6 * (n : ℤ)) := by
  have hne : n ≠ 0 := by omega
  unfold a uhat
  apply le_antisymm
  · have base : n.divisors.fold min (n : ℤ) (val n 1 8) ≤ -55 := by
      rw [fold_min_le]
      exact Or.inr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hne⟩, (unit_divisor n).le⟩
    by_cases h : 8 < n
    · refine le_min base ?_
      rw [fold_min_le]
      exact Or.inr ⟨n, Nat.mem_divisors_self n hne, (large_divisor n n h).le⟩
    · rw [min_eq_left (by omega : (-55 : ℤ) ≤ -6 * n)]
      exact base
  · rw [le_fold_min]
    refine ⟨(min_le_left _ _).trans (by omega), ?_⟩
    intro d hd
    have dvd := (Nat.mem_divisors.mp hd).1
    have dpos := Nat.pos_of_dvd_of_pos dvd hn
    have dn := Nat.le_of_dvd hn dvd
    by_cases h : 8 < d
    · rw [large_divisor n d h]
      exact (min_le_right _ _).trans (by omega)
    · exact (min_le_left _ _).trans (small_divisor n d dpos (by omega))

private theorem linear_tail (n : ℕ) (hn : 10 ≤ n) : a n = -6 * (n : ℤ) := by
  rw [closed n (by omega), min_eq_right (by omega)]

private theorem recurrence (n : ℕ) (hn : 11 < n) :
    a n - 2 * a (n - 1) + a (n - 2) = 0 := by
  rw [linear_tail n (by omega), linear_tail (n - 1) (by omega), linear_tail (n - 2) (by omega)]
  omega

set_option maxHeartbeats 1200000 in
private theorem series_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((X - 1) ^ 2) =
      X * (-X ^ 10 - 5 * X ^ 9 + 55 * X - 55) := by
  have hd : ((X - 1) ^ 2 : ℤ⟦X⟧) = 1 - C 2 * X ^ 1 + X ^ 2 := by
    simp only [map_ofNat, pow_one]
    ring
  have hp : (X * (-X ^ 10 - 5 * X ^ 9 + 55 * X - 55) : ℤ⟦X⟧) =
      C (-55) * X ^ 1 + C 55 * X ^ 2 - C 5 * X ^ 10 - X ^ 11 := by
    simp only [map_ofNat, map_neg, pow_one]
    ring
  rw [mul_comm, hd, hp]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : 11 < n
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn10 : n ≠ 10 := by omega
    have hn11 : n ≠ 11 := by omega
    have s1 : n - 1 ≠ 0 := by omega
    have s2 : n - 2 ≠ 0 := by omega
    simpa only [if_pos h1, if_pos h2, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn10,
      if_neg hn11, if_neg s1, if_neg s2, mul_zero, add_zero, sub_zero] using recurrence n hn
  · interval_cases n <;> norm_num [closed]

end OMA.S_oeis_a291502

open OMA.S_oeis_a291502 in
theorem OMA.solution : type_of% @OMA.S_oeis_a291502.main := by
  refine ⟨?_, series_identity⟩
  intro n hn
  linarith only [recurrence n hn]