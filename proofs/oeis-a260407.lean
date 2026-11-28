import OMAStatements.S_oeis_a260407
import Mathlib

namespace OMA.P_oeis_a260407

theorem key (m x k : ℕ) (h : m ∣ 2 ^ x - 1) : m ∣ (2 ^ k) ^ x - 1 := by
  have h2 : 2 ^ x - 1 ∣ (2 ^ x) ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow (2 ^ x) 1 k
  rw [one_pow, ← pow_mul, mul_comm, pow_mul] at h2
  exact h.trans h2

end OMA.P_oeis_a260407

theorem OMA.solution : type_of% @OMA.S_oeis_a260407.main := by
  intro n _
  constructor
  · intro h k _
    exact OMA.P_oeis_a260407.key _ _ k h
  · intro h
    simpa using h 1 le_rfl
