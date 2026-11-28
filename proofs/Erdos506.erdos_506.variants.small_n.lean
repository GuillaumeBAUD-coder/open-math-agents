import FormalConjectures.ErdosProblems.«506»

noncomputable def OMA.answer (n : ℕ) : ℕ :=
  if n = 6 then 8 else if n = 7 then 11 else if n = 8 then 17
  else (n - 1) * (n - 2) / 2 + 1 - (n - 1) / 2

theorem OMA.solution : Erdos506.erdos_506.variants.small_n.answer = OMA.answer → type_of% @Erdos506.erdos_506.variants.small_n := by
  intro h
  rw [h]
  have he : Erdos506.erdos_506.variants.small_n.answer 6 =
      Erdos506.erdos_506.variants.small_n.answer 7 := rfl
  rw [h] at he
  have hf : (8 : ℕ) = 11 := he
  omega
