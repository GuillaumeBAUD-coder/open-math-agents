import OMAStatements.S_oeis_a026008
import Mathlib.Tactic

/-!
Split `t` by parity. `simp` reduces each index `2 * k + j` mod 2 and div 2 (`Nat.mul_add_div`),
unfolds the closed forms and expands the factorials down to `(2 * k)!` and `k!`; then
`field_simp` and `ring`.
-/

open OMA.S_oeis_a026008 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026008.main := by
  intro t
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩ <;>
  simp [a, evenTerm, oddTerm, Nat.mul_add_div, Nat.factorial_succ, mul_add, add_assoc] <;>
  field_simp <;> ring
