import OMAStatements.S_oeis_a008544

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: a(m+1) = (3m+2) a(m). Writing n = m+3, the first two terms cancel
-- since a(m+3) = (3m+8) a(m+2), and the last two cancel since a(m+1) = (3m+2) a(m).

namespace OMA.A008544Proof

open OMA.S_oeis_a008544

lemma succ_eq (m : ℕ) : a (m + 1) = (3 * (m : ℤ) + 2) * a m := by
  unfold a
  rw [Finset.prod_range_succ, mul_comm]

end OMA.A008544Proof

open OMA.S_oeis_a008544 OMA.A008544Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a008544.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  rw [show m + 3 = (m + 2) + 1 by ring, succ_eq (m + 2), succ_eq m]
  push_cast
  ring
