import OMAStatements.S_oeis_a276706
import Mathlib

open OMA.S_oeis_a276706
open PowerSeries

namespace P276706

theorem c2 : Nat.count IsRecord 2 = 1 := by decide
theorem c4 : Nat.count IsRecord 4 = 2 := by decide
theorem c5 : Nat.count IsRecord 5 = 3 := by decide
theorem c6 : Nat.count IsRecord 6 = 4 := by decide

theorem a2 : a 2 = 2 := by
  have := Nat.nth_count (p := IsRecord) (n := 2) (by decide)
  rw [c2] at this; exact this
theorem a3 : a 3 = 4 := by
  have := Nat.nth_count (p := IsRecord) (n := 4) (by decide)
  rw [c4] at this; exact this
theorem a4 : a 4 = 5 := by
  have := Nat.nth_count (p := IsRecord) (n := 5) (by decide)
  rw [c5] at this; exact this
theorem a5 : a 5 = 6 := by
  have := Nat.nth_count (p := IsRecord) (n := 6) (by decide)
  rw [c6] at this; exact this

end P276706

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a276706.main) := by
  rintro ⟨h, -, -⟩
  have h5 := h 5 (by norm_num)
  norm_num [P276706.a5, P276706.a4, P276706.a3, P276706.a2] at h5
