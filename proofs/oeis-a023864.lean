import OMAStatements.S_oeis_a023864
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a023864

open OMA.S_oeis_a023864 Finset PowerSeries

/-- First difference `b(n) = a(n) - a(n-1) - a(n-2)` (for `n ≥ 2`). -/
private def b (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n = 1 then a023864 1
  else a023864 n - a023864 (n - 1) - a023864 (n - 2)

private lemma b_odd (m : ℕ) (hm : 1 ≤ m) :
    b (2 * m + 1) = ((m + 1 : ℕ) : ℤ) * (Nat.fib (m + 2) : ℤ) := by
  have h1 : 2 * m + 1 ≠ 0 := by omega
  have h2 : 2 * m + 1 ≠ 1 := by omega
  have h3 : 2 * m ≠ 0 := by omega
  have h4 : 2 * m - 1 ≠ 0 := by omega
  unfold b a023864
  simp only [h1, h2, h3, h4, ↓reduceIte, show 2 * m + 1 - 1 = 2 * m by omega,
    show 2 * m + 1 - 2 = 2 * m - 1 by omega]
  have hk1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have hk2 : (2 * m + 1) / 2 = m := by omega
  have hk3 : (2 * m - 1 + 1) / 2 = m := by omega
  rw [hk1, hk2, hk3]
  have hsplit : ∑ i ∈ Icc 1 (m + 1), (i : ℤ) * (Nat.fib (2 * m + 1 + 2 - i) : ℤ) =
      (∑ i ∈ Icc 1 m, (i : ℤ) * (Nat.fib (2 * m + 1 + 2 - i) : ℤ)) +
        ((m + 1 : ℕ) : ℤ) * (Nat.fib (m + 2) : ℤ) := by
    rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) by ext x; simp only [mem_Icc, mem_insert]; omega,
        sum_insert (by simp)]
    rw [show 2 * m + 1 + 2 - (m + 1) = m + 2 by omega]
    ring
  rw [hsplit]
  have hcancel : (∑ i ∈ Icc 1 m, (i : ℤ) * (Nat.fib (2 * m + 1 + 2 - i) : ℤ)) -
      (∑ i ∈ Icc 1 m, (i : ℤ) * (Nat.fib (2 * m + 2 - i) : ℤ)) -
      (∑ i ∈ Icc 1 m, (i : ℤ) * (Nat.fib (2 * m - 1 + 2 - i) : ℤ)) = 0 := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_eq_zero
    intro i hi
    rw [mem_Icc] at hi
    have hf : Nat.fib (2 * m + 1 + 2 - i) = Nat.fib (2 * m + 2 - i) + Nat.fib (2 * m - 1 + 2 - i) := by
      have h1' : 2 * m + 1 + 2 - i = (2 * m - 1 + 2 - i) + 2 := by omega
      have h2' : 2 * m + 2 - i = (2 * m - 1 + 2 - i) + 1 := by omega
      rw [h1', h2', Nat.fib_add_two, add_comm]
    have hfZ : (Nat.fib (2 * m + 1 + 2 - i) : ℤ) =
        (Nat.fib (2 * m + 2 - i) : ℤ) + (Nat.fib (2 * m - 1 + 2 - i) : ℤ) := by exact_mod_cast hf
    rw [hfZ]; ring
  linarith

private lemma b_even (m : ℕ) (hm : 2 ≤ m) :
    b (2 * m) = (m : ℤ) * (Nat.fib m : ℤ) := by
  have h1 : 2 * m ≠ 0 := by omega
  have h2 : 2 * m ≠ 1 := by omega
  have h3 : 2 * m - 1 ≠ 0 := by omega
  have h4 : 2 * m - 2 ≠ 0 := by omega
  unfold b a023864
  simp only [h1, h2, h3, h4, ↓reduceIte]
  have hk1 : (2 * m + 1) / 2 = m := by omega
  have hk2 : (2 * m - 1 + 1) / 2 = m := by omega
  have hk3 : (2 * m - 2 + 1) / 2 = m - 1 := by omega
  rw [hk1, hk2, hk3]
  have hsplit1 : ∑ i ∈ Icc 1 m, (i : ℤ) * (Nat.fib (2 * m + 2 - i) : ℤ) =
      (∑ i ∈ Icc 1 (m - 1), (i : ℤ) * (Nat.fib (2 * m + 2 - i) : ℤ)) +
        (m : ℤ) * (Nat.fib (m + 2) : ℤ) := by
    rw [show Icc 1 m = insert m (Icc 1 (m - 1)) by ext x; simp only [mem_Icc, mem_insert]; omega,
        sum_insert (by simp; omega)]
    rw [show 2 * m + 2 - m = m + 2 by omega]
    ring
  have hsplit2 : ∑ i ∈ Icc 1 m, (i : ℤ) * (Nat.fib (2 * m - 1 + 2 - i) : ℤ) =
      (∑ i ∈ Icc 1 (m - 1), (i : ℤ) * (Nat.fib (2 * m - 1 + 2 - i) : ℤ)) +
        (m : ℤ) * (Nat.fib (m + 1) : ℤ) := by
    rw [show Icc 1 m = insert m (Icc 1 (m - 1)) by ext x; simp only [mem_Icc, mem_insert]; omega,
        sum_insert (by simp; omega)]
    rw [show 2 * m - 1 + 2 - m = m + 1 by omega]
    ring
  rw [hsplit1, hsplit2]
  have hcancel : (∑ i ∈ Icc 1 (m - 1), (i : ℤ) * (Nat.fib (2 * m + 2 - i) : ℤ)) -
      (∑ i ∈ Icc 1 (m - 1), (i : ℤ) * (Nat.fib (2 * m - 1 + 2 - i) : ℤ)) -
      (∑ i ∈ Icc 1 (m - 1), (i : ℤ) * (Nat.fib (2 * m - 2 + 2 - i) : ℤ)) = 0 := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_eq_zero
    intro i hi
    rw [mem_Icc] at hi
    have hf : Nat.fib (2 * m + 2 - i) = Nat.fib (2 * m - 1 + 2 - i) + Nat.fib (2 * m - 2 + 2 - i) := by
      have h1' : 2 * m + 2 - i = (2 * m - 2 + 2 - i) + 2 := by omega
      have h2' : 2 * m - 1 + 2 - i = (2 * m - 2 + 2 - i) + 1 := by omega
      rw [h1', h2', Nat.fib_add_two, add_comm]
    have hfZ : (Nat.fib (2 * m + 2 - i) : ℤ) =
        (Nat.fib (2 * m - 1 + 2 - i) : ℤ) + (Nat.fib (2 * m - 2 + 2 - i) : ℤ) := by exact_mod_cast hf
    rw [hfZ]; ring
  have hfm : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
    exact_mod_cast Nat.fib_add_two (n := m)
  linear_combination hcancel + (m : ℤ) * hfm

private lemma coeff_one_sub_X_sub_Xsq (f : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (((1 - X - X ^ 2 : PowerSeries ℤ) * PowerSeries.mk f)) =
      if n = 0 then f 0
      else if n = 1 then f 1 - f 0
      else f n - f (n - 1) - f (n - 2) := by
  have hexp : ((1 - X - X ^ 2 : PowerSeries ℤ) * PowerSeries.mk f) =
      PowerSeries.mk f - X ^ 1 * PowerSeries.mk f - X ^ 2 * PowerSeries.mk f := by ring
  rw [hexp, map_sub, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
  rcases n with _ | _ | k
  · simp
  · simp [PowerSeries.coeff_mk]
  · simp [PowerSeries.coeff_mk]

private lemma coeff_one_sub_X2_sub_X4 (f : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (((1 - X ^ 2 - X ^ 4 : PowerSeries ℤ) * PowerSeries.mk f)) =
      if n < 2 then f n
      else if n < 4 then f n - f (n - 2)
      else f n - f (n - 2) - f (n - 4) := by
  have hexp : ((1 - X ^ 2 - X ^ 4 : PowerSeries ℤ) * PowerSeries.mk f) =
      PowerSeries.mk f - X ^ 2 * PowerSeries.mk f - X ^ 4 * PowerSeries.mk f := by ring
  rw [hexp, map_sub, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
  split_ifs with h1 h2 h3 h4
  all_goals (try simp only [PowerSeries.coeff_mk])
  all_goals omega

private lemma step1_eq :
    ((1 - X - X ^ 2 : PowerSeries ℤ) * PowerSeries.mk a023864) = PowerSeries.mk b := by
  ext n
  rw [coeff_one_sub_X_sub_Xsq, PowerSeries.coeff_mk]
  unfold b
  cases n with
  | zero => simp [a023864]
  | succ k =>
    cases k with
    | zero => simp [a023864]
    | succ k' => simp

/-- Second difference `c(n)` = coeff of `(1 - X^2 - X^4) * mk b`. -/
private def c (n : ℕ) : ℤ :=
  if n < 2 then b n
  else if n < 4 then b n - b (n - 2)
  else b n - b (n - 2) - b (n - 4)

private lemma c_odd (m : ℕ) (hm : 3 ≤ m) :
    c (2 * m + 1) = (Nat.fib (m + 2) : ℤ) + (Nat.fib m : ℤ) := by
  unfold c
  simp only [show ¬ 2 * m + 1 < 2 by omega, show ¬ 2 * m + 1 < 4 by omega, ↓reduceIte,
    show 2 * m + 1 - 2 = 2 * (m - 1) + 1 by omega, show 2 * m + 1 - 4 = 2 * (m - 2) + 1 by omega]
  rw [b_odd m (by omega), b_odd (m - 1) (by omega), b_odd (m - 2) (by omega)]
  have hm1 : m - 1 + 2 = m + 1 := by omega
  have hm2 : m - 2 + 2 = m := by omega
  have hm1' : ((m - 1 + 1 : ℕ) : ℤ) = (m : ℤ) := by omega
  have hm2' : ((m - 2 + 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hm1, hm2, hm1', hm2']
  have hf : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
    exact_mod_cast Nat.fib_add_two (n := m)
  push_cast
  linear_combination (m : ℤ) * hf

private lemma c_even (m : ℕ) (hm : 4 ≤ m) :
    c (2 * m) = (Nat.fib m : ℤ) + (Nat.fib (m - 2) : ℤ) := by
  unfold c
  simp only [show ¬ 2 * m < 2 by omega, show ¬ 2 * m < 4 by omega, ↓reduceIte,
    show 2 * m - 2 = 2 * (m - 1) by omega, show 2 * m - 4 = 2 * (m - 2) by omega]
  rw [b_even m (by omega), b_even (m - 1) (by omega), b_even (m - 2) (by omega)]
  have hm1' : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hm2' : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
  rw [hm1', hm2']
  have hf : (Nat.fib m : ℤ) = (Nat.fib (m - 2) : ℤ) + (Nat.fib (m - 1) : ℤ) := by
    have h := Nat.fib_add_two (n := m - 2)
    have h1 : m - 2 + 2 = m := by omega
    have h2 : m - 2 + 1 = m - 1 := by omega
    rw [h1, h2] at h
    exact_mod_cast h
  linear_combination ((m : ℤ) - 1) * hf

private lemma prove_a023864 :
    ((1 - X - X ^ 2) * (1 - X ^ 2 - X ^ 4) ^ 2 : PowerSeries ℤ) *
        PowerSeries.mk a023864 =
      X + X ^ 2 + 2 * X ^ 3 + X ^ 6 := by
  have h1 : ((1 - X - X ^ 2) * (1 - X ^ 2 - X ^ 4) ^ 2 : PowerSeries ℤ) * PowerSeries.mk a023864 =
      (1 - X ^ 2 - X ^ 4) * ((1 - X ^ 2 - X ^ 4) * ((1 - X - X ^ 2) * PowerSeries.mk a023864)) := by
    ring
  rw [h1, step1_eq]
  have h2 : ((1 - X ^ 2 - X ^ 4 : PowerSeries ℤ) * PowerSeries.mk b) = PowerSeries.mk c := by
    ext n
    rw [coeff_one_sub_X2_sub_X4, PowerSeries.coeff_mk]
    rfl
  rw [h2]
  ext n
  rw [coeff_one_sub_X2_sub_X4]
  have hcoeff : ∀ k : ℕ, PowerSeries.coeff k (X + X ^ 2 + 2 * X ^ 3 + X ^ 6 : PowerSeries ℤ) =
      (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) +
      ((if k = 3 then 1 else 0) + (if k = 3 then 1 else 0)) + (if k = 6 then 1 else 0) := by
    intro k
    rw [two_mul (X ^ 3 : PowerSeries ℤ)]
    simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hn : n < 12
  · rw [hcoeff]
    interval_cases n <;> decide
  · -- For n ≥ 12, the RHS coeff is 0 and c n - c (n - 2) - c (n - 4) = 0
    have hrhs : PowerSeries.coeff n (X + X ^ 2 + 2 * X ^ 3 + X ^ 6 : PowerSeries ℤ) = 0 := by
      rw [hcoeff]; omega
    rw [hrhs]
    simp only [show ¬ n < 2 by omega, show ¬ n < 4 by omega, ↓reduceIte]
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm : 6 ≤ m := by omega
      rw [show m + m = 2 * m by omega,
          show 2 * m - 2 = 2 * (m - 1) by omega,
          show 2 * m - 4 = 2 * (m - 2) by omega]
      rw [c_even m (by omega), c_even (m - 1) (by omega), c_even (m - 2) (by omega)]
      have hf1 : (Nat.fib m : ℤ) = (Nat.fib (m - 2) : ℤ) + (Nat.fib (m - 1) : ℤ) := by
        have h := Nat.fib_add_two (n := m - 2)
        rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at h
        exact_mod_cast h
      have hf2 : (Nat.fib (m - 2) : ℤ) = (Nat.fib (m - 2 - 2) : ℤ) + (Nat.fib (m - 1 - 2) : ℤ) := by
        have h := Nat.fib_add_two (n := m - 4)
        rw [show m - 4 + 2 = m - 2 by omega, show m - 4 + 1 = m - 1 - 2 by omega,
            show m - 4 = m - 2 - 2 by omega] at h
        exact_mod_cast h
      linarith
    · have hm : 5 ≤ m := by omega
      rw [show 2 * m + 1 - 2 = 2 * (m - 1) + 1 by omega,
          show 2 * m + 1 - 4 = 2 * (m - 2) + 1 by omega]
      rw [c_odd m (by omega), c_odd (m - 1) (by omega), c_odd (m - 2) (by omega)]
      have hf1 : (Nat.fib (m + 2) : ℤ) = (Nat.fib (m - 2 + 2) : ℤ) + (Nat.fib (m - 1 + 2) : ℤ) := by
        have h1' : m - 2 + 2 = m := by omega
        have h2' : m - 1 + 2 = m + 1 := by omega
        rw [h1', h2']
        exact_mod_cast Nat.fib_add_two (n := m)
      have hf2 : (Nat.fib m : ℤ) = (Nat.fib (m - 2) : ℤ) + (Nat.fib (m - 1) : ℤ) := by
        have h := Nat.fib_add_two (n := m - 2)
        rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at h
        exact_mod_cast h
      linarith

end OMA.P_oeis_a023864

theorem OMA.solution : type_of% @OMA.S_oeis_a023864.main :=
  OMA.P_oeis_a023864.prove_a023864
