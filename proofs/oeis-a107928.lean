import OMAStatements.S_oeis_a107928
import Mathlib

open OMA.S_oeis_a107928 in
theorem OMA.solution : type_of% @OMA.S_oeis_a107928.main := by
  have s : ∀ n k : ℕ, ∀ c D x y : ℤ, a (n + 1) = x → a (n + 2) = y → 0 < D →
      c.natAbs.Coprime D.natAbs → Nat.Coprime 8 D.natAbs → x + y ≠ 0 →
      2 * y * x * D = c * 8 ^ k * (x + y) → a (n + 3) = c * 8 ^ k := by
    intro n k c D x y hx hy hD hc h8 h0 e
    rw [a, hx, hy, show 2 * (y : ℚ) * x / (x + y) = (c * 8 ^ k : ℤ) / (D : ℤ) by
      rw [div_eq_div_iff (by exact_mod_cast h0) (by positivity)]; exact_mod_cast e]
    exact Rat.num_div_eq_of_coprime hD (by simpa [Int.natAbs_mul] using hc.mul_left (h8.pow_left k))
  have t : ∀ k : ℕ, a (3 * k + 3) = 12 * 8 ^ k ∧ a (3 * k + 4) = 24 * 8 ^ k ∧
      a (3 * k + 5) = 16 * 8 ^ k := by
    intro k
    induction k with
    | zero => norm_num [a]
    | succ k ih =>
      obtain ⟨h3, h4, h5⟩ := ih
      have g6 := s _ k 96 5 _ _ h4 h5 (by norm_num) (by norm_num) (by norm_num) (by positivity) (by ring)
      have g7 := s _ k 192 7 _ _ h5 g6 (by norm_num) (by norm_num) (by norm_num) (by positivity) (by ring)
      have g8 := s _ k 128 1 _ _ g6 g7 (by norm_num) (by norm_num) (by norm_num) (by positivity) (by ring)
      exact ⟨g6.trans (by ring), g7.trans (by ring), g8.trans (by ring)⟩
  rintro (_ | k) hn
  · cases hn
  obtain ⟨h3, h4, h5⟩ := t k
  refine ⟨?_, h4.trans (by ring), h5.trans (by ring)⟩
  rw [show 3 * (k + 1) = 3 * k + 3 by ring, h3]
  push_cast
  ring
