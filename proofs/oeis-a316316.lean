import OMAStatements.S_oeis_a316316
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a316316

/-- Shift every entry of a window by `40`. -/
def add40 (w : Window) : Window := ⟨w.a + 40, w.b + 40, w.c + 40, w.d + 40, w.e + 40, w.f + 40⟩

theorem step_add40 (w : Window) : step (add40 w) = add40 (step w) := by
  cases w
  simp only [step, add40, Window.mk.injEq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_⟩
  ring

theorem window_twelve : window 12 = add40 (window 0) := by decide

theorem window_add_twelve (k : ℕ) : window (k + 12) = add40 (window k) := by
  induction k with
  | zero => exact window_twelve
  | succ k ih =>
    rw [show k + 1 + 12 = (k + 12) + 1 by omega]
    show step (window (k + 12)) = add40 (step (window k))
    rw [ih, step_add40]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a316316.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 + 12 = (k + 12) + 1 by omega]
  show (OMA.S_oeis_a316316.window (k + 12)).a = (OMA.S_oeis_a316316.window k).a + 40
  rw [OMA.Helpers.window_add_twelve]
  rfl
