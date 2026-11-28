import OMAStatements.S_oeis_a172507
import Mathlib

open OMA.S_oeis_a172507

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a172507.main) := by
  rintro ⟨n, -, hn⟩
  apply hn
  have hs : scale n ≠ 0 := by
    unfold scale
    positivity
  rw [repeatedDecimal, Rat.natCast_add_den, Rat.den_mkRat, if_neg hs, clearingFactor,
    Int.natAbs_natCast, Nat.gcd_comm]
