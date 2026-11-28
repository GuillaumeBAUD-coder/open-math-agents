import OMAStatements.S_oeis_a025755

theorem OMA.solution : type_of% @OMA.S_oeis_a025755.main := by
  rintro (_ | _ | m) hn <;> try omega
  simp only [OMA.S_oeis_a025755.a, ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp
  ring
