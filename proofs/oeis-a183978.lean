import OMAStatements.S_oeis_a183978
import Mathlib

/-!
# A183978: the closed form fails at `n = 1`

For `n = 1` there is a single `2 × 2` block, so every one of the `2⁴ = 16` binary arrays is
valid and `a 1 = 16 / 4 = 4`.  The claimed formula gives
`(2^⌈1/2⌉ + 1)(2^⌊1/2⌋ + 1) = 3 · 2 = 6`.
-/

namespace OMA.S_oeis_a183978

/-- Every `2 × 2` array is valid. -/
lemma all_valid (A : Fin (1 + 1) → Fin 2 → Bool) : isValid 1 A :=
  ⟨subblockSum A 0 0, fun i j => by rw [Subsingleton.elim i 0, Subsingleton.elim j 0]⟩

lemma a_one : a 1 = 4 := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv all_valid), Nat.card_eq_fintype_card]
  simp

end OMA.S_oeis_a183978

open OMA.S_oeis_a183978 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a183978.main) := by
  intro h
  have h1 := h 1 (by norm_num)
  have hc : ⌈((1 : ℕ) : ℚ) / 2⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor <;> norm_num
  have hf : ⌊((1 : ℕ) : ℚ) / 2⌋₊ = 0 := by
    rw [Nat.floor_eq_zero]
    norm_num
  rw [a_one, hc, hf] at h1
  norm_num at h1
