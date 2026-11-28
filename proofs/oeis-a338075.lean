import OMAStatements.S_oeis_a338075
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a338075

lemma t_succ (n : ℕ) : t (n + 1) = 3 * (3 * (n : ℚ) + 1) * (3 * n + 2) / ((n : ℚ) + 1) ^ 2 * t n := by
  have h1 : ((3 * (n + 1)).factorial : ℚ) = (3 * n + 3) * (3 * n + 2) * (3 * n + 1) * (3 * n).factorial := by
    have : 3 * (n + 1) = (3 * n + 2) + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ (3 * n)]
    push_cast; ring
  have h2 : ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  unfold t
  rw [h1, h2]
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp

lemma t_pos (n : ℕ) : 0 < t n := by
  unfold t
  have : (0:ℚ) < (n.factorial : ℚ) := by exact_mod_cast n.factorial_pos
  positivity

end OMA.S_oeis_a338075

theorem OMA.solution : type_of% @OMA.S_oeis_a338075.main := by
  open OMA.S_oeis_a338075 in
  refine ⟨?_, ?_⟩
  · ext n
    rw [add_mul, one_mul, map_add, coeff_mk]
    cases n with
    | zero => simp [a]
    | succ k => rw [coeff_succ_X_mul, coeff_mk]; simp [a, add_comm]
  · intro n
    have e1 : a (n + 1) = t n + t (n + 1) := by simp [a]
    have e2 : a (n + 2) = t (n + 1) + t (n + 2) := by simp [a]
    have e3 : a (n + 3) = t (n + 2) + t (n + 3) := by simp [a]
    have e4 : a (n + 4) = t (n + 3) + t (n + 4) := by simp [a]
    have h1 : t (n + 1) = 3 * (3 * (n : ℚ) + 1) * (3 * n + 2) / ((n : ℚ) + 1) ^ 2 * t n := t_succ n
    have h2 : t (n + 2) = 3 * (3 * ((n + 1 : ℕ) : ℚ) + 1) * (3 * ((n + 1 : ℕ) : ℚ) + 2) / (((n + 1 : ℕ) : ℚ) + 1) ^ 2 * t (n + 1) := t_succ (n + 1)
    have h3 : t (n + 3) = 3 * (3 * ((n + 2 : ℕ) : ℚ) + 1) * (3 * ((n + 2 : ℕ) : ℚ) + 2) / (((n + 2 : ℕ) : ℚ) + 1) ^ 2 * t (n + 2) := t_succ (n + 2)
    have h4 : t (n + 4) = 3 * (3 * ((n + 3 : ℕ) : ℚ) + 1) * (3 * ((n + 3 : ℕ) : ℚ) + 2) / (((n + 3 : ℕ) : ℚ) + 1) ^ 2 * t (n + 3) := t_succ (n + 3)
    rw [e1, e2, e3, e4, h4, h3, h2, h1]
    push_cast
    have : ((n : ℚ) + 1) ≠ 0 := by positivity
    have : ((n : ℚ) + 2) ≠ 0 := by positivity
    have : ((n : ℚ) + 3) ≠ 0 := by positivity
    have : ((n : ℚ) + 4) ≠ 0 := by positivity
    field_simp
    ring
