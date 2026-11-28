import OMAStatements.S_oeis_a377113
import Mathlib

/-!
Disproof of the OEIS A377113 conjecture: the displayed block for p = 2 is wrong.
The argument follows the accepted proof of the template entry OEIS A377118.
The terms start 1, 3, 14, 72, so the first two even terms have indices 2 and 3 and the
first gap is 1, while the displayed one-element block (2) forces every gap to be 2.
-/

namespace A377113

open OMA.S_oeis_a377113

lemma a0 : a 0 = 1 := by decide
lemma a1 : a 1 = 3 := by decide
lemma a2 : a 2 = 14 := by decide
lemma a3 : a 3 = 72 := by decide

lemma nth0 : Nat.nth (fun n => 2 ∣ a n) 0 = 2 := by
  have h : (fun n => 2 ∣ a n) 2 := by
    show 2 ∣ a 2
    rw [a2]; norm_num
  have h2 := Nat.nth_count (p := fun n => 2 ∣ a n) h
  have hc : Nat.count (fun n => 2 ∣ a n) 2 = 0 := by
    rw [Nat.count_succ, Nat.count_succ, Nat.count_zero]
    simp [a0, a1]
  rw [hc] at h2
  exact h2

lemma nth1 : Nat.nth (fun n => 2 ∣ a n) 1 = 3 := by
  have h : (fun n => 2 ∣ a n) 3 := by
    show 2 ∣ a 3
    rw [a3]; norm_num
  have h2 := Nat.nth_count (p := fun n => 2 ∣ a n) h
  have hc : Nat.count (fun n => 2 ∣ a n) 3 = 1 := by
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ, Nat.count_zero]
    simp [a0, a1, a2]
  rw [hc] at h2
  exact h2

end A377113

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377113.main) := by
  intro h
  have h2 := (h 2 Nat.prime_two).2 [2] (by simp [OMA.S_oeis_a377113.displayed])
  obtain ⟨phase, hph⟩ := h2.1
  have h0 := hph 0
  unfold OMA.S_oeis_a377113.gap at h0
  rw [A377113.nth0, A377113.nth1] at h0
  simp [Nat.mod_one] at h0
