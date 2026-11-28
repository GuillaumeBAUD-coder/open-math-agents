import OMAStatements.S_oeis_a166588
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: (n+1)(a(n)-a(n-1)) = 4(n-2)(a(n-2)-a(n-3)) reduces to (n+1)b(n) = 4(n-2)b(n-2): trivial for even n, and for odd n it is (j+2)C(j+1) = 2(2j+1)C(j), from succ_mul_catalan_eq_centralBinom and succ_mul_centralBinom_succ.

namespace OMA.P_oeis_a166588

open OMA.S_oeis_a166588

lemma cat_rec (j : ℕ) : ((j : ℤ) + 2) * (catalan (j + 1) : ℤ) = 2 * (2 * (j : ℤ) + 1) * catalan j := by
  have h1 : (((j + 1 + 1) * catalan (j + 1) : ℕ) : ℤ) = ((j + 1).centralBinom : ℤ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (j + 1)
  have h2 : (((j + 1) * catalan j : ℕ) : ℤ) = (j.centralBinom : ℤ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom j
  have h3 : (((j + 1) * (j + 1).centralBinom : ℕ) : ℤ) = ((2 * (2 * j + 1) * j.centralBinom : ℕ) : ℤ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ j
  push_cast at h1 h2 h3
  apply mul_left_cancel₀ (show ((j : ℤ) + 1) ≠ 0 by positivity)
  linear_combination (↑j + 1) * h1 + h3 - 2 * (2 * (j : ℤ) + 1) * h2

lemma key (k : ℕ) : ((k : ℤ) + 4) * b (k + 3) = 4 * ((k : ℤ) + 1) * b (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have e3 : b (2 * j + 3) = catalan (j + 1) := by
      simp only [b]
      rw [if_neg (by omega), if_pos (by omega), show (2 * j + 3 - 1) / 2 = j + 1 by omega]
    have e1 : b (2 * j + 1) = catalan j := by
      simp only [b]
      rw [if_neg (by omega), if_pos (by omega), show (2 * j + 1 - 1) / 2 = j by omega]
    rw [e3, e1]
    push_cast
    linear_combination 2 * cat_rec j
  · have e3 : b (2 * j + 1 + 3) = 0 := by
      simp only [b]
      rw [if_neg (by omega), if_neg (by omega)]
    have e1 : b (2 * j + 1 + 1) = 0 := by
      simp only [b]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e3, e1]; ring

end OMA.P_oeis_a166588

theorem OMA.solution : type_of% @OMA.S_oeis_a166588.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have e1 : OMA.S_oeis_a166588.a (k + 3) = OMA.S_oeis_a166588.a (k + 2) + OMA.S_oeis_a166588.b (k + 3) := by
    simp only [OMA.S_oeis_a166588.a, Finset.sum_range_succ]
  have e2 : OMA.S_oeis_a166588.a (k + 1) = OMA.S_oeis_a166588.a k + OMA.S_oeis_a166588.b (k + 1) := by
    simp only [OMA.S_oeis_a166588.a, Finset.sum_range_succ]
  have hk := OMA.P_oeis_a166588.key k
  push_cast
  linear_combination (-((k : ℤ) + 3 + 1)) * e1 + 4 * ((k : ℤ) + 3 - 2) * e2 - hk
