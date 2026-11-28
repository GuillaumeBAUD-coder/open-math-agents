import OMAStatements.S_oeis_a377114
import Mathlib

/-!
Disproof of the OEIS A377114 conjecture: the displayed block for p = 2 is wrong.
The argument follows the accepted proof of the template entry OEIS A377118 (the displayed
one-element block for p = 2 contradicted by an early gap).
The terms start 0, 1, 6, 38, so the second and third even terms have indices 2 and 3 and the
gap with index 1 is 1, while the displayed block (2) forces every gap to be 2.
-/

namespace A377114

open OMA.S_oeis_a377114

lemma nth1 : Nat.nth (fun n => 2 ∣ a n) 1 = 2 := by
  have h : (fun n => 2 ∣ a n) 2 := by
    show 2 ∣ a 2
    decide
  have h2 := Nat.nth_count (p := fun n => 2 ∣ a n) h
  have hc : Nat.count (fun n => 2 ∣ a n) 2 = 1 := by decide +kernel
  rw [hc] at h2
  exact h2

lemma nth2 : Nat.nth (fun n => 2 ∣ a n) 2 = 3 := by
  have h : (fun n => 2 ∣ a n) 3 := by
    show 2 ∣ a 3
    decide
  have h2 := Nat.nth_count (p := fun n => 2 ∣ a n) h
  have hc : Nat.count (fun n => 2 ∣ a n) 3 = 2 := by decide +kernel
  rw [hc] at h2
  exact h2

end A377114

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377114.main) := by
  intro h
  have h2 := (h 2 Nat.prime_two).2 [2] (by simp [OMA.S_oeis_a377114.displayed])
  obtain ⟨phase, hph⟩ := h2.1
  have h1 := hph 1
  unfold OMA.S_oeis_a377114.gap at h1
  rw [A377114.nth1, A377114.nth2] at h1
  simp [Nat.mod_one] at h1
