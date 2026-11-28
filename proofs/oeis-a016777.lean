import OMAStatements.S_oeis_a016777
import Mathlib

/-!
The set `A = {1, 2}` has two elements and property P holds vacuously (no element is smaller
than both of two distinct elements), but its largest element is `2 < 3 * 2 - 2 = 4`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a016777.main) := by
  intro h
  have hP : OMA.S_oeis_a016777.PropP ({1, 2} : Finset ℕ) := by
    unfold OMA.S_oeis_a016777.PropP
    decide
  obtain ⟨a, ha, hle⟩ := h 2 {1, 2} (by norm_num) (by decide) (by decide) hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> omega
