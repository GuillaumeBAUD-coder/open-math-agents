import OMAStatements.S_oeis_a134357
import Mathlib

namespace OMA.P_oeis_a134357

open OMA.S_oeis_a134357

private lemma a005156_ne_zero (n : ℕ) : a005156 n ≠ 0 := by
  unfold a005156
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  have h1 : ((3 * k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : ((6 * k + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((2 * k + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : ((4 * k + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h5 : ((4 * k + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  positivity

private lemma choose_eq_fact_div (a b : ℕ) (h : b ≤ a) :
    (Nat.choose a b : ℚ) = (a.factorial : ℚ) / ((b.factorial : ℚ) * ((a - b).factorial : ℚ)) := by
  have hnat : Nat.choose a b * b.factorial * (a - b).factorial = a.factorial :=
    Nat.choose_mul_factorial_mul_factorial h
  have hq : (Nat.choose a b : ℚ) * ((b.factorial : ℚ) * ((a - b).factorial : ℚ)) = (a.factorial : ℚ) := by
    have : (Nat.choose a b : ℚ) * (b.factorial : ℚ) * ((a - b).factorial : ℚ) = (a.factorial : ℚ) := by
      exact_mod_cast hnat
    linarith
  have hne : (b.factorial : ℚ) * ((a - b).factorial : ℚ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  exact (eq_div_iff hne).mpr hq

private theorem main_proved :
    ∀ n : ℕ, 1 ≤ n →
      (Nat.choose (6 * n - 2) (2 * n) : ℚ) / (2 * (Nat.choose (4 * n - 1) (2 * n) : ℚ)) =
        a005156 (n + 1) / a005156 n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hratio : a005156 (m + 1 + 1) / a005156 (m + 1) =
      (((3 * m + 2 : ℕ) : ℚ) * ((6 * m + 3).factorial : ℚ) * ((2 * m + 1).factorial : ℚ)) /
        (((4 * m + 2).factorial : ℚ) * ((4 * m + 3).factorial : ℚ)) := by
    have hne := a005156_ne_zero (m + 1)
    rw [div_eq_iff hne]
    simp only [a005156, Nat.add_sub_cancel, Finset.prod_range_succ]
    ring
  rw [hratio]
  have h1 : 6 * (m + 1) - 2 = 6 * m + 4 := by omega
  have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
  have h3 : 4 * (m + 1) - 1 = 4 * m + 3 := by omega
  rw [h1, h2, h3]
  rw [choose_eq_fact_div (6 * m + 4) (2 * m + 2) (by omega),
      choose_eq_fact_div (4 * m + 3) (2 * m + 2) (by omega)]
  have hsub1 : 6 * m + 4 - (2 * m + 2) = 4 * m + 2 := by omega
  have hsub2 : 4 * m + 3 - (2 * m + 2) = 2 * m + 1 := by omega
  rw [hsub1, hsub2]
  have h64 : ((6 * m + 4).factorial : ℚ) = ((6 * m + 4 : ℕ) : ℚ) * ((6 * m + 3).factorial : ℚ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  rw [h64]
  have hne1 : ((2 * m + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne2 : ((4 * m + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne3 : ((4 * m + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne4 : ((2 * m + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hne1, hne2, hne3, hne4]
  push_cast
  ring

end OMA.P_oeis_a134357

theorem OMA.solution : type_of% @OMA.S_oeis_a134357.main :=
  OMA.P_oeis_a134357.main_proved
