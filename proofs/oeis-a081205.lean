import OMAStatements.S_oeis_a081205

open OMA.S_oeis_a081205 Nat in
theorem OMA.solution : type_of% @OMA.S_oeis_a081205.main := by
  rintro (_|_|k) h <;> simp at h
  qify
  obtain ⟨i, rfl | rfl⟩ := k.even_or_odd' <;> simp +arith [a, cast_choose, mul_add_div, show ∀ i c, 3*i+c-2*i = i+c by omega, factorial_succ] <;> field_simp <;> ring
