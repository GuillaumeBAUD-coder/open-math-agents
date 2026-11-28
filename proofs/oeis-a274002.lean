import OMAStatements.S_oeis_a274002

open OMA.S_oeis_a274002 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274002.main := fun p =>
  ⟨fun ⟨hp, q, hq, e, hd⟩ => ⟨hp, q, hq, e, fun k => by
    rw [← pow_mul, mul_comm, pow_mul]; exact hd.trans (Nat.sub_one_dvd_pow_sub_one _ k)⟩,
   fun ⟨hp, q, hq, e, hd⟩ => ⟨hp, q, hq, e, by simpa using hd 1⟩⟩
