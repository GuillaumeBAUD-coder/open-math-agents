import OMAStatements.S_oeis_a010905
import Mathlib

/-!
Credit: @ivillar
Proof: the quantity a(n+1)^2 - 4*a(n)*a(n+1) + a(n)^2 = 1 is invariant. With x = a(n) ≥ 4 and
y = a(n+1), it gives y^2/x = (4y - x) + 1/x with 0 < 1/x ≤ 1/4, so the rounding yields
a(n+2) = 4y - x, and the invariant passes to (y, 4y - x).
-/

namespace OMAA010905Helpers
open OMA.S_oeis_a010905

theorem step (x y : ℤ) (hx : 4 ≤ x) (hinv : y ^ 2 - 4 * x * y + x ^ 2 = 1) :
    ⌊((y : ℚ) ^ 2 / (x : ℚ) + 1 / 2)⌋ = 4 * y - x := by
  have hxq : (4 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
  have hx0 : (0 : ℚ) < (x : ℚ) := by linarith
  have hinvq : (y : ℚ) ^ 2 = (x : ℚ) * (4 * y - x) + 1 := by
    have : ((y ^ 2 - 4 * x * y + x ^ 2 : ℤ) : ℚ) = 1 := by exact_mod_cast hinv
    push_cast at this
    linarith
  have hdiv : (y : ℚ) ^ 2 / (x : ℚ) = (4 * y - x) + 1 / (x : ℚ) := by
    rw [hinvq]
    field_simp
  have h1 : 0 < 1 / (x : ℚ) := by positivity
  have h2 : 1 / (x : ℚ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  rw [Int.floor_eq_iff, hdiv]
  push_cast
  constructor <;> linarith

theorem key (n : ℕ) :
    4 ≤ a n ∧ a n ≤ a (n + 1) ∧ a (n + 1) ^ 2 - 4 * a n * a (n + 1) + a n ^ 2 = 1 := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e : a (k + 1 + 1) = 4 * a (k + 1) - a k := step (a k) (a (k + 1)) h1 h3
    refine ⟨by linarith, ?_, ?_⟩
    · rw [e]; linarith
    · rw [e]; linear_combination h3

end OMAA010905Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a010905.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨h1, -, h3⟩ := OMAA010905Helpers.key m
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]
  exact OMAA010905Helpers.step _ _ h1 h3
