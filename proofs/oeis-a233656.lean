import OMAStatements.S_oeis_a233656
import Mathlib

namespace OMA.P_oeis_a233656

open OMA.S_oeis_a233656

theorem digits (n : ℕ) : a n % 10 = pattern.getD (n % 20) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : (n + 1) % 20 = (n % 20 + 1) % 20 := by omega
    have hr : n % 20 < 20 := Nat.mod_lt _ (by norm_num)
    have hstep : a (n + 1) = 3 * a n - 2 * n := rfl
    rw [e, hstep]
    generalize hk : n % 20 = k at ih hr ⊢
    interval_cases k <;> simp [pattern] at ih ⊢ <;> omega

end OMA.P_oeis_a233656

theorem OMA.solution : type_of% @OMA.S_oeis_a233656.main := by
  refine ⟨OMA.P_oeis_a233656.digits, ?_⟩
  decide
