import OMAStatements.S_oeis_a329725

open OMA.S_oeis_a329725

theorem OMA.solution : type_of% @OMA.S_oeis_a329725.main := by
  rintro (_|m) h
  omega
  simp [a, p, mul_add, Nat.add_mod, Nat.add_div]
  ring
