import OMAStatements.S_oeis_a229159
import Mathlib

/-!
# OEIS A229159: every odd prime is a side of an integer triangle with integer area

For `p = 2t + 1` (`t ≥ 1`) take the right triangle from the Pythagorean triple

  `p,  (p² - 1)/2 = 2t(t + 1),  (p² + 1)/2 = 2t(t + 1) + 1`.

Its area is `p · t(t + 1)`, an integer, and Heron's identity
`16 A² = (a + b + c)(-a + b + c)(a - b + c)(a + b - c)` is a polynomial identity in `t`.
(Primality is not needed, only that `p > 2` is odd.)
-/

open OMA.S_oeis_a229159

theorem OMA.solution : type_of% @OMA.S_oeis_a229159.main := by
  intro p hp hp2
  -- `p = 2t + 1` with `t ≥ 1`
  obtain ⟨t, rfl⟩ : ∃ t, p = 2 * t + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact ⟨p / 2, by omega⟩
  have ht : 1 ≤ t := by omega
  have htt : 1 ≤ t * (t + 1) := Nat.mul_pos (by omega) (by omega)
  have hle : t ≤ t * (t + 1) := Nat.le_mul_of_pos_right t (by omega)
  refine ⟨2 * t + 1, 2 * (t * (t + 1)), 2 * (t * (t + 1)) + 1, (2 * t + 1) * (t * (t + 1)),
    Or.inl rfl, by omega, by omega, by omega, by omega, by omega, by omega,
    Nat.mul_pos (by omega) (by omega), ?_⟩
  push_cast
  ring
