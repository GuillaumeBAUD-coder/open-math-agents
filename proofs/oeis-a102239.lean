import OMAStatements.S_oeis_a102239

-- Problem: A102239: a(n) = (Sum{i=0..n} 5^i) + 1 - (Sum{i=0..n} 5^i) mod 2.
-- Proof: s(n+1) = 5 s(n) + 1 and s(n) has the parity of n + 1.

namespace OMA.P_oeis_a102239
open OMA.S_oeis_a102239

lemma s_succ (n : ℕ) : s (n + 1) = 5 * s n + 1 := by
  unfold s
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma s_mod (n : ℕ) : s n % 2 = (n + 1) % 2 := by
  induction n with
  | zero => simp [s]
  | succ k ih => rw [s_succ]; omega

lemma a_eq (n : ℕ) : (a n : ℤ) = (s n : ℤ) + 1 - ((n + 1) % 2 : ℕ) := by
  unfold a
  have h := s_mod n
  have : s n % 2 ≤ s n := Nat.mod_le _ _
  rw [← h]; omega

end OMA.P_oeis_a102239

theorem OMA.solution : type_of% @OMA.S_oeis_a102239.main := by
  intro n
  rw [OMA.P_oeis_a102239.a_eq, OMA.P_oeis_a102239.a_eq, OMA.P_oeis_a102239.a_eq,
    OMA.P_oeis_a102239.s_succ, OMA.P_oeis_a102239.s_succ]
  push_cast
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> push_cast <;> omega
