import OMAStatements.S_oeis_a266839
import Mathlib

/-!
# A266839 (Rule 67, decimal representation): the odd-index closed form is not even an integer

For `n = 3` the claimed closed form for odd `n > 2` gives
`2 · 4³ - 61 · 8^⌊3/2⌋ / 16 - 1 = 128 - 61/2 - 1 = 193/2`,
which is not a natural number, so it cannot be the value of `a 3`.
-/

open OMA.S_oeis_a266839 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266839.main) := by
  rintro ⟨-, -, hodd, -⟩
  have h := hodd 3 (by norm_num) (by decide)
  have hfloor : ⌊((3 : ℕ) : ℚ) / 2⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  rw [hfloor] at h
  -- so `2 * a 3 = 193`, which is impossible for a natural number
  have h2 : (2 * (a 3 : ℚ)) = 193 := by
    rw [h]
    norm_num
  have h3 : 2 * a 3 = 193 := by exact_mod_cast h2
  omega
