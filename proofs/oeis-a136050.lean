import OMAStatements.S_oeis_a136050
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a136050.main := by
  intro p hp hq _
  have := hp.eq_one_or_self_of_dvd 3
  have := hq.eq_one_or_self_of_dvd 3
  have := hp.two_le
  have := Nat.modEq_nine_digits_sum (p * (p + 2))
  obtain ⟨k, rfl⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
  unfold OMA.S_oeis_a136050.term Nat.ModEq at *
  ring_nf at *
  omega
