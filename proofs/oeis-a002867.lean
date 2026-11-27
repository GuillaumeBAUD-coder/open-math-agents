import OMAStatements.S_oeis_a002867
import Mathlib

-- Problem: oeis-a002867
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P002867
open OMA.S_oeis_a002867

theorem sol : type_of% @OMA.S_oeis_a002867.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    subst hj
    unfold a
    rw [show k + 1 + (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 + (k + 1) - 2 = 2 * k by omega,
      show (k + 1 + (k + 1)) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k / 2 = k by omega, show k + 1 + (k + 1) + 1 = (2 * k + 2) + 1 by omega,
      show k + 1 + (k + 1) = 2 * k + 2 by omega,
      Nat.factorial_succ (2 * k + 2), Nat.factorial_succ (2 * k + 1)]
    have e1 : (2 * k + 1 + 1) * (2 * k + 1).choose k = (2 * k + 1 + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq _ _
    have e2 : (2 * k + 1) * (2 * k).choose k = (2 * k + 1).choose (k + 1) * (k + 1) := by
      have := Nat.add_one_mul_choose_eq (2 * k) k
      simpa using this
    have e3 : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := by
      rw [Nat.choose_symm_of_eq_add]; omega
    rw [e3] at e2
    have e1' : (2 * k + 2).choose (k + 1) = 2 * (2 * k + 1).choose k := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < k + 1 by omega)
      rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, ← e1]; ring
    rw [e1']
    have e2z : ((2 * k + 1 : ℕ) : ℤ) * ((2 * k).choose k : ℤ) = ((2 * k + 1).choose k : ℤ) * ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast e2
    push_cast at e2z ⊢
    linear_combination (-4 : ℤ) * (2 * (k : ℤ) + 2) * ((2 * k + 1).factorial : ℤ) * e2z
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    subst hj
    unfold a
    rw [show 2 * (k + 1) + 1 - 1 = 2 * k + 2 by omega, show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega,
      show (2 * (k + 1) + 1) / 2 = k + 1 by omega, show (2 * k + 2) / 2 = k + 1 by omega,
      show (2 * k + 1) / 2 = k by omega, show 2 * (k + 1) + 1 + 1 = (2 * k + 3) + 1 by omega,
      show 2 * k + 2 + 1 = 2 * k + 3 by omega, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
      show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
      Nat.factorial_succ (2 * k + 3), Nat.factorial_succ (2 * k + 2)]
    have e1 : (2 * k + 2 + 1) * (2 * k + 2).choose k = (2 * k + 2 + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq _ _
    have e2 : (2 * k + 2).choose (k + 1) * (k + 1) = (2 * k + 2).choose k * (2 * k + 2 - k) :=
      Nat.choose_succ_right_eq _ _
    have e3a : (2 * k + 1 + 1) * (2 * k + 1).choose k = (2 * k + 1 + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq _ _
    have e3 : (2 * k + 2).choose (k + 1) = 2 * (2 * k + 1).choose k := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < k + 1 by omega)
      rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, ← e3a]; ring
    rw [show 2 * k + 2 - k = k + 2 by omega] at e2
    have z1 : ((2 * k + 3 : ℕ) : ℤ) * ((2 * k + 2).choose k : ℤ) = ((2 * k + 3).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast e1
    have z2 : ((2 * k + 2).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) = ((2 * k + 2).choose k : ℤ) * ((k + 2 : ℕ) : ℤ) := by
      exact_mod_cast e2
    have z3 : ((2 * k + 2).choose (k + 1) : ℤ) = 2 * ((2 * k + 1).choose k : ℤ) := by
      exact_mod_cast e3
    push_cast at z1 z2 z3 ⊢
    set W : ℤ := ((2 * k + 3).choose (k + 1) : ℤ)
    set Z : ℤ := ((2 * k + 2).choose (k + 1) : ℤ)
    set Y : ℤ := ((2 * k + 1).choose k : ℤ)
    set V : ℤ := ((2 * k + 2).choose k : ℤ)
    set F : ℤ := ((2 * k + 2).factorial : ℤ)
    have hk : (k : ℤ) + 1 ≠ 0 := by positivity
    have key : ((k : ℤ) + 1) * (W * ((2 * k + 3 + 1) * ((2 * k + 3) * F)) - 2 * (Z * ((2 * k + 3) * F)) -
        4 * (2 * (k : ℤ) + 3) * (2 * k + 3 - 1) * (Y * F)) = 0 := by
      linear_combination (2 * (k : ℤ) + 3) * F * (-(2 * (k : ℤ) + 4) * z1 - (4 * (k : ℤ) + 6) * z2 + 4 * ((k : ℤ) + 1) ^ 2 * z3)
    have := (mul_eq_zero.mp key).resolve_left hk
    linear_combination this

end OMA.P002867

theorem OMA.solution : type_of% @OMA.S_oeis_a002867.main := OMA.P002867.sol
