import OMAStatements.S_oeis_a280523

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: prove simultaneously, by induction on m, that b(2m) = F(2m+3) - (m+1) and
-- b(2m+1) = F(2m+4) - (m+2) (A215004 against Fibonacci); then b(2n-2) = F(2n+1) - n.

namespace OMA.A280523Proof

open OMA.S_oeis_a280523

lemma pair (m : ℕ) : b (2 * m) = (Nat.fib (2 * m + 3) : ℤ) - (m + 1) ∧
    b (2 * m + 1) = (Nat.fib (2 * m + 4) : ℤ) - (m + 2) := by
  induction m with
  | zero => simp [b, Nat.fib_add_two]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : b (2 * (k + 1)) = b (2 * k + 1) + b (2 * k) + (k + 1 : ℕ) := by
      have : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [this, b]
      congr 2
      omega
    have e1 : b (2 * (k + 1) + 1) = b (2 * (k + 1)) + b (2 * k + 1) + (k + 1 : ℕ) := by
      have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [this, b]
      have : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [this]
      congr 2
      omega
    have f1 : Nat.fib (2 * (k + 1) + 3) = Nat.fib (2 * k + 4) + Nat.fib (2 * k + 3) := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by ring, Nat.fib_add_two]
      rw [show 2 * k + 3 + 1 = 2 * k + 4 by ring]; ring
    have f2 : Nat.fib (2 * (k + 1) + 4) = Nat.fib (2 * (k + 1) + 3) + Nat.fib (2 * k + 4) := by
      rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 2 by ring, Nat.fib_add_two]
      rw [show 2 * k + 4 + 1 = 2 * (k + 1) + 3 by ring]; ring
    refine ⟨?_, ?_⟩
    · rw [e0, h0, h1, f1]; push_cast; ring
    · rw [e1, e0, h0, h1, f2, f1]; push_cast; ring

end OMA.A280523Proof

open OMA.S_oeis_a280523 OMA.A280523Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a280523.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (pair m).1
  rw [show 2 * (m + 1) - 2 = 2 * m by omega, h]
  unfold a
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
  push_cast
  ring
