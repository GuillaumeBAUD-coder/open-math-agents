import OMAStatements.S_oeis_a296159

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: for n ≥ 1, a(n+4) = a(n) + d(n) where the two new summands give
-- d(n) = 2 * (n / 4) + 1 + n % 2 (case split on n mod 4). Then a(n) - 2a(n-4) + a(n-8) = 2 for
-- n ≥ 9, which is the claimed order-9 recurrence.

namespace OMA.Sol_oeis_a296159
open OMA.S_oeis_a296159

lemma step (n : ℕ) (hn : 1 ≤ n) :
    a (n + 4) = a n + ((n - 1) / 2 + 1) * ((n + 4 - ((n - 1) / 2 + 1)) % 2)
      + ((n - 1) / 2 + 2) * ((n + 4 - ((n - 1) / 2 + 2)) % 2) := by
  unfold a
  have hk : (n + 4 - 1) / 2 = (n - 1) / 2 + 2 := by omega
  rw [hk, show (n - 1) / 2 + 2 = ((n - 1) / 2 + 1) + 1 by ring,
    Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  have hc : ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), i * ((n + 4 - i) % 2)
      = ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), i * ((n - i) % 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    congr 1
    omega
  rw [hc]

lemma dval (n : ℕ) :
    ((n - 1) / 2 + 1) * ((n + 4 - ((n - 1) / 2 + 1)) % 2)
      + ((n - 1) / 2 + 2) * ((n + 4 - ((n - 1) / 2 + 2)) % 2) = 2 * (n / 4) + 1 + n % 2 ∨ n = 0 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact Or.inr h0
  left
  rcases Nat.mod_two_eq_zero_or_one (n + 4 - ((n - 1) / 2 + 1)) with e1 | e1 <;>
  rcases Nat.mod_two_eq_zero_or_one (n + 4 - ((n - 1) / 2 + 2)) with e2 | e2 <;>
  · rw [e1, e2]; omega

lemma rec4 (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + (2 * (n / 4) + 1 + n % 2) := by
  rw [step n hn]
  rcases dval n with h | h
  · omega
  · omega

end OMA.Sol_oeis_a296159

theorem OMA.solution : type_of% @OMA.S_oeis_a296159.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have r1 := OMA.Sol_oeis_a296159.rec4 (m + 6) (by omega)
  have r2 := OMA.Sol_oeis_a296159.rec4 (m + 2) (by omega)
  have r3 := OMA.Sol_oeis_a296159.rec4 (m + 5) (by omega)
  have r4 := OMA.Sol_oeis_a296159.rec4 (m + 1) (by omega)
  simp only [show m + 10 - 1 = m + 5 + 4 by omega, show m + 10 - 4 = m + 2 + 4 by omega,
    show m + 10 - 5 = m + 1 + 4 by omega, show m + 10 - 8 = m + 2 by omega,
    show m + 10 - 9 = m + 1 by omega, show m + 10 = m + 6 + 4 by omega]
  rw [show m + 6 + 4 = (m + 6) + 4 from rfl] at r1 ⊢
  rw [show m + 2 + 4 = m + 6 by omega] at r2 ⊢
  rw [show m + 1 + 4 = m + 5 by omega] at r4 ⊢
  omega
