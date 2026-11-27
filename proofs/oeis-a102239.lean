import OMAStatements.S_oeis_a102239

namespace OMA.S_oeis_a102239

lemma s_succ (n : ℕ) : s (n + 1) = 5 * s n + 1 := by
  unfold s
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

end OMA.S_oeis_a102239

open OMA.S_oeis_a102239 in
theorem OMA.solution : type_of% @OMA.S_oeis_a102239.main := by
  intro n
  have h1 := s_succ n
  have h2 : s (n + 2) = 5 * s (n + 1) + 1 := s_succ (n + 1)
  have key : a (n + 2) + 2 = 4 * a (n + 1) + 5 * a n := by
    unfold a
    rcases Nat.even_or_odd (s n) with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [h2, h1, hk] <;> omega
  omega
