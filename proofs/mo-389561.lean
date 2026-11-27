import OMAStatements.S_mo_389561
import Mathlib

-- Problem: mo-389561, two quadrics over the field with 3^(2n+1) elements.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- In characteristic 3, y^2 + y + 1 = (y - 1)^2 and y^2 + y z + z^2 = (y - z)^2, so both
-- equations have the shape a^2 + b^2 = 0. Since 3^(2n+1) = 3 (mod 4), -1 is not a square in
-- the field, hence a^2 + b^2 = 0 forces a = b = 0.

theorem OMA.solution : type_of% @OMA.S_mo_389561.main := by
  intro n F _ _ _ hcard
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hmod : 3 ^ (2 * n + 1) % 4 = 3 := by
    have e : 3 ^ (2 * n + 1) = 9 ^ n * 3 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [e, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hcard]
    exact fun hne => hne hmod
  have key : ∀ a b : F, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      have ha : a ^ 2 = 0 := by linear_combination hab
      exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp ha, rfl⟩
    · exfalso
      apply hns
      refine ⟨a / b, ?_⟩
      field_simp
      linear_combination -hab
  constructor
  · intro x y
    constructor
    · intro h
      have h' : x ^ 2 + (y - 1) ^ 2 = 0 := by linear_combination h - y * h3
      obtain ⟨hx, hy⟩ := key x (y - 1) h'
      exact ⟨hx, sub_eq_zero.mp hy⟩
    · rintro ⟨rfl, rfl⟩
      linear_combination h3
  · intro x y z hne
    constructor
    · intro h
      have h' : x ^ 2 + (y - z) ^ 2 = 0 := by linear_combination h - y * z * h3
      obtain ⟨hx, hyz⟩ := key x (y - z) h'
      have hyz' : y = z := sub_eq_zero.mp hyz
      refine ⟨hx, hyz', ?_⟩
      intro hz
      rcases hne with h1 | h1 | h1
      · exact h1 hx
      · exact h1 (hyz'.trans hz)
      · exact h1 hz
    · rintro ⟨rfl, rfl, _⟩
      linear_combination y ^ 2 * h3
