import OMAStatements.S_oeis_a184878
import Mathlib

/-!
`Q(n + 2) = Q(n) * (X - (n + 2)^2)`, so with `c = (n + 2)^2` the coefficients satisfy
`T(n + 2, k + 1) = T(n, k + 1) - c * T(n, k)` and `T(n, 0) = 1` (the product is monic of degree
`floor((n + 1)/2)`). Hence `-T(n,1)`, `T(n,2)`, `-T(n,3)` are the elementary symmetric functions
of the squares `(n - 2i)^2`, and a two-step induction checks the closed forms
`n(n+1)(n+2)/6`, `(n-2)(n-1)n(n+1)(n+2)(5n+12)/360` and the stated degree-9 polynomial.
-/

namespace R184878
open OMA.S_oeis_a184878 Polynomial

theorem Q_succ2 (n : ℕ) : Q (n + 2) = Q n * (X - C (((n : ℤ) + 2) ^ 2)) := by
  unfold Q
  rw [show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega, Finset.prod_range_succ']
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp only [show n + 2 - 2 * (i + 1) = n - 2 * i by omega]
  all_goals simp

theorem Q_monic (n : ℕ) : (Q n).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem Q_natDegree (n : ℕ) : (Q n).natDegree = (n + 1) / 2 := by
  unfold Q
  rw [natDegree_prod_of_monic (h := fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem T_zero (n : ℕ) : T n 0 = 1 := by
  unfold T
  rw [if_pos (Nat.zero_le _), Nat.sub_zero, ← Q_natDegree n]
  exact (Q_monic n).coeff_natDegree

theorem T_succ2 (n k : ℕ) :
    T (n + 2) (k + 1) = T n (k + 1) - ((n : ℤ) + 2) ^ 2 * T n k := by
  unfold T
  rw [show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega, Q_succ2]
  generalize (n + 1) / 2 = d
  rcases lt_trichotomy k d with h | h | h
  · have h1 : k + 1 ≤ d + 1 := by omega
    have h2 : k + 1 ≤ d := by omega
    have h3 : k ≤ d := by omega
    rw [if_pos h1, if_pos h2, if_pos h3,
      show d + 1 - (k + 1) = (d - (k + 1)) + 1 by omega, coeff_mul_X_sub_C,
      show d - (k + 1) + 1 = d - k by omega]
    ring
  · have h1 : k + 1 ≤ d + 1 := by omega
    have h2 : ¬ k + 1 ≤ d := by omega
    have h3 : k ≤ d := by omega
    rw [if_pos h1, if_neg h2, if_pos h3,
      show d + 1 - (k + 1) = 0 by omega, show d - k = 0 by omega, mul_coeff_zero]
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero]
    ring
  · have h1 : ¬ k + 1 ≤ d + 1 := by omega
    have h2 : ¬ k + 1 ≤ d := by omega
    have h3 : ¬ k ≤ d := by omega
    rw [if_neg h1, if_neg h2, if_neg h3]
    ring

def g1 (n : ℕ) : ℚ := (n : ℚ) * (n + 1) * (n + 2) / 6

def g2 (n : ℕ) : ℚ := (n : ℚ) * (n - 1) * (n - 2) * (n + 1) * (n + 2) * (5 * n + 12) / 360

def g3 (n : ℕ) : ℚ := (n : ℚ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n + 2) * (n + 1) *
  (35 * n ^ 2 + 182 * n + 240) / 45360

theorem key : ∀ n : ℕ, (T n 1 : ℚ) = -g1 n ∧ (T n 2 : ℚ) = g2 n ∧ (T n 3 : ℚ) = -g3 n
  | 0 => by
    have e1 : T 0 1 = 0 := by simp [T]
    have e2 : T 0 2 = 0 := by simp [T]
    have e3 : T 0 3 = 0 := by simp [T]
    simp [e1, e2, e3, g1, g2, g3]
  | 1 => by
    have e1 : T 1 1 = -1 := by simp [T, Q]
    have e2 : T 1 2 = 0 := by simp [T]
    have e3 : T 1 3 = 0 := by simp [T]
    norm_num [e1, e2, e3, g1, g2, g3]
  | n + 2 => by
    obtain ⟨h1, h2, h3⟩ := key n
    have e1 : T (n + 2) 1 = T n 1 - ((n : ℤ) + 2) ^ 2 * T n 0 := T_succ2 n 0
    have e2 : T (n + 2) 2 = T n 2 - ((n : ℤ) + 2) ^ 2 * T n 1 := T_succ2 n 1
    have e3 : T (n + 2) 3 = T n 3 - ((n : ℤ) + 2) ^ 2 * T n 2 := T_succ2 n 2
    rw [T_zero] at e1
    have q1 : (T (n + 2) 1 : ℚ) = T n 1 - ((n : ℚ) + 2) ^ 2 := by
      rw [e1]; push_cast; ring
    have q2 : (T (n + 2) 2 : ℚ) = T n 2 - ((n : ℚ) + 2) ^ 2 * T n 1 := by
      rw [e2]; push_cast; ring
    have q3 : (T (n + 2) 3 : ℚ) = T n 3 - ((n : ℚ) + 2) ^ 2 * T n 2 := by
      rw [e3]; push_cast; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [q1, h1]; simp only [g1]; push_cast; ring
    · rw [q2, h2, h1]; simp only [g1, g2]; push_cast; ring
    · rw [q3, h3, h2]; simp only [g2, g3]; push_cast; ring

end R184878

theorem OMA.solution : type_of% @OMA.S_oeis_a184878.main := by
  intro n _
  have h := (R184878.key n).2.2
  have ha : (OMA.S_oeis_a184878.a n : ℚ) = -(OMA.S_oeis_a184878.T n 3 : ℚ) := by
    unfold OMA.S_oeis_a184878.a; push_cast; ring
  rw [ha, h]
  simp only [R184878.g3]
  ring
