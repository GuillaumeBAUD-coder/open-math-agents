import OMAStatements.S_oeis_a377116
import Mathlib

/-!
Disproof of the OEIS A377116 conjecture: the displayed block for p = 3 is wrong.
The argument follows the accepted proof of the template entry OEIS A377118 (a displayed block
contradicted by an early gap), with the prime 3 in place of 2.
The terms start 0, 0, 2, 18, so the second and third multiples of 3 have indices 1 and 3 and the
gap with index 1 is 2, a value that does not occur in the displayed block (1, 4, 3, 8, 8).
-/

namespace A377116

open OMA.S_oeis_a377116

lemma nth1 : Nat.nth (fun n => 3 ∣ a n) 1 = 1 := by
  have h : (fun n => 3 ∣ a n) 1 := by
    show 3 ∣ a 1
    decide
  have h2 := Nat.nth_count (p := fun n => 3 ∣ a n) h
  have hc : Nat.count (fun n => 3 ∣ a n) 1 = 1 := by decide +kernel
  rw [hc] at h2
  exact h2

lemma nth2 : Nat.nth (fun n => 3 ∣ a n) 2 = 3 := by
  have h : (fun n => 3 ∣ a n) 3 := by
    show 3 ∣ a 3
    decide
  have h2 := Nat.nth_count (p := fun n => 3 ∣ a n) h
  have hc : Nat.count (fun n => 3 ∣ a n) 3 = 2 := by decide +kernel
  rw [hc] at h2
  exact h2

end A377116

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377116.main) := by
  intro h
  have h2 := (h 3 Nat.prime_three).2 [1, 4, 3, 8, 8]
    (by simp [OMA.S_oeis_a377116.displayed])
  obtain ⟨phase, hph⟩ := h2.1
  have h1 := hph 1
  unfold OMA.S_oeis_a377116.gap at h1
  rw [A377116.nth1, A377116.nth2] at h1
  have hl : ([1, 4, 3, 8, 8] : List ℕ).length = 5 := rfl
  rw [hl] at h1
  have hlt : (1 + phase) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize (1 + phase) % 5 = r at h1 hlt
  interval_cases r <;> simp at h1
