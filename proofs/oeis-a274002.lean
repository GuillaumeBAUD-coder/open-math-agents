import OMAStatements.S_oeis_a274002

theorem OMA.solution : type_of% @OMA.S_oeis_a274002.main := by
  intro p
  constructor <;> rintro ⟨hp, q, hq, e, hd⟩ <;> refine ⟨hp, q, hq, e, ?_⟩
  · intro k
    rw [← pow_mul, mul_comm, pow_mul]
    exact hd.trans (Nat.sub_one_dvd_pow_sub_one _ k)
  · simpa using hd 1
