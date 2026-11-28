import OMAStatements.S_mo_389561
import Mathlib

namespace OMA.P_mo_389561

theorem key {F : Type} [Field F] [Fintype F] (hns : ¬ IsSquare (-1 : F)) (a b : F)
    (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨?_, rfl⟩
    have : a ^ 2 = 0 := by simpa using h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · exfalso
    apply hns
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination -h

end OMA.P_mo_389561

theorem OMA.solution : type_of% @OMA.S_mo_389561.main := by
  intro n F _ _ _ hcard
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hcard, pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  refine ⟨fun x y => ⟨fun h => ?_, ?_⟩, fun x y z hne => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨hx, hy⟩ := OMA.P_mo_389561.key hns x (y - 1) (by linear_combination h - y * h3)
    exact ⟨hx, sub_eq_zero.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    linear_combination h3
  · obtain ⟨hx, hyz⟩ := OMA.P_mo_389561.key hns x (y - z) (by linear_combination h - y * z * h3)
    have hyz' : y = z := sub_eq_zero.mp hyz
    refine ⟨hx, hyz', ?_⟩
    intro hz
    subst hz
    subst hyz'
    rcases hne with h' | h' | h' <;> simp_all
  · rintro ⟨rfl, rfl, -⟩
    linear_combination y ^ 2 * h3
