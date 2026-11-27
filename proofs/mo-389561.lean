import OMAStatements.S_mo_389561
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_389561.main := by
  intro n F _ _ _ hcard
  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    exact_mod_cast this
  have h34 : ∀ m : ℕ, 3 ^ (2 * m + 1) % 4 = 3 := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
      have : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
      rw [this]; omega
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hcard]
    exact not_not.mpr (h34 n)
  have key : ∀ a b : F, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      have ha : a = 0 := by simpa using hab
      exact ⟨ha, rfl⟩
    · exfalso
      apply hns
      refine ⟨a / b, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
      linear_combination -hab
  constructor
  · intro x y
    constructor
    · intro h
      have h' : x ^ 2 + (y - 1) ^ 2 = 0 := by linear_combination h - y * h3
      obtain ⟨hx, hy⟩ := key x (y - 1) h'
      exact ⟨hx, sub_eq_zero.mp hy⟩
    · rintro ⟨hx, hy⟩
      rw [hx, hy]
      linear_combination h3
  · intro x y z hne
    constructor
    · intro h
      have h' : x ^ 2 + (y - z) ^ 2 = 0 := by linear_combination h - y * z * h3
      obtain ⟨hx, hy⟩ := key x (y - z) h'
      have hyz : y = z := sub_eq_zero.mp hy
      refine ⟨hx, hyz, ?_⟩
      intro hz
      rcases hne with h | h | h
      · exact h hx
      · exact h (hyz.trans hz)
      · exact h hz
    · rintro ⟨hx, hy, -⟩
      rw [hx, hy]
      linear_combination z ^ 2 * h3
