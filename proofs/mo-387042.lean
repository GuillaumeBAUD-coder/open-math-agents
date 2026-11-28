import OMAStatements.S_mo_387042
import Mathlib

/-!
MathOverflow 387042: (x, y, z) = (1875, 1125, 375) = (3·5⁴, 3²·5³, 3·5³) is a solution with x ≠ z that is not in the list.
-/

namespace OMA.P387042

/-- `(1875, 1125, 375) = (3 · 5⁴, 3² · 5³, 3 · 5³)` solves `x^y y^z = z^x`. -/
theorem sol : (1875 : ℕ) ^ 1125 * 1125 ^ 375 = 375 ^ 1875 := by
  have key : ∀ a b : ℕ, (a * b ^ 4) ^ 1125 * (a ^ 2 * b ^ 3) ^ 375 = (a * b ^ 3) ^ 1875 := by
    intro a b; ring
  have h := key 3 5
  simpa only [show (3 : ℕ) * 5 ^ 4 = 1875 by norm_num, show (3 : ℕ) ^ 2 * 5 ^ 3 = 1125 by norm_num,
    show (3 : ℕ) * 5 ^ 3 = 375 by norm_num] using h

theorem disproof :
    ¬ ∀ x y z : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ z → x ^ y * y ^ z = z ^ x → x ≠ z →
      (x, y, z) ∈ ({(8, 2, 2), (9, 3, 3), (4, 2, 8), (16, 4, 32), (128, 64, 32), (512, 256, 32),
        (686, 392, 98)} : Finset (ℕ × ℕ × ℕ)) := by
  intro h
  have := h 1875 1125 375 (by norm_num) (by norm_num) (by norm_num) sol (by norm_num)
  simp at this

end OMA.P387042

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_387042.main) := OMA.P387042.disproof
