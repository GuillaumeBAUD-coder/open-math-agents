import OMAStatements.S_oeis_a014484
import Mathlib

open OMA.S_oeis_a014484 in
lemma OMA.ha (k : ℕ) : (a k : ℤ) * 6 = ((k + 2).factorial * (2 * k + 3) * 2 ^ k : ℕ) := by
  have h : 6 ∣ (k + 2).factorial * (2 * k + 3) * 2 ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Nat.factorial_dvd_factorial (show 3 ≤ k + 2 by omega)) _) _
  simp only [a]
  exact_mod_cast Nat.div_mul_cancel h

theorem OMA.solution : type_of% @OMA.S_oeis_a014484.main := by
  rintro (_ | _ | m) hn
  iterate 2 omega
  have h0 := OMA.ha m
  have h1 := OMA.ha (m + 1)
  have h2 := OMA.ha (m + 2)
  simp only [Nat.factorial_succ, add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] at *
  push_cast at *
  refine (mul_eq_zero.1 (?_ : _ * (6 : ℤ) = 0)).resolve_right (by norm_num)
  linear_combination h2 + (-2 * (m + 2 : ℤ) - 9) * h1 + 6 * (m + 3 : ℤ) * h0
