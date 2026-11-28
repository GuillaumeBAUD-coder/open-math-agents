import OMAStatements.S_oeis_a260407
import Mathlib

namespace OMA.S_oeis_a260407

theorem main_aux : type_of% @OMA.S_oeis_a260407.main := by
  intro n hn
  constructor
  · intro h k hk
    rw [← pow_mul, mul_comm, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow ((2 : ℕ) ^ (n - 1)) 1 k
    simpa using h.trans this
  · intro h
    simpa using h 1 le_rfl

end OMA.S_oeis_a260407

theorem OMA.solution : type_of% @OMA.S_oeis_a260407.main := OMA.S_oeis_a260407.main_aux
