import OMAReductions.R_OeisA78680_conjecture_R1

-- Reduction OeisA78680.conjecture.R1.H2.R1 of step OeisA78680.conjecture.R1.H2
-- Credit: @arindale
--
-- H2 is the finite statement that `a n ≠ 0` for every `1 ≤ n < 2^16`.  Since
-- `a n ≠ 0` unfolds to the existence of `m > 0` with `n * 2^m + 1` prime, this is a
-- finite but computationally heavy verification: every `n` needs a prime witness, and the
-- minimal witnesses can be very large (the four odd multipliers 21181, 22699, 24737, 55459
-- are the surviving Sierpiński candidates, whose witnesses run to millions).
--
-- The parity of `n` separates two different verification regimes.  For odd `n` the witness
-- is directly `n * 2^m + 1`; for even `n = 2^k * u` the power of two can be absorbed into the
-- shift, so a witness for the odd part `u` with shift at least `k + 1` settles `n`.  Both
-- halves are finite and independent; each can be discharged by a certificate generator.

namespace OMA.R_OeisA78680_conjecture_R1_H2_R1

/-- Non-vanishing of `a` on the even multipliers below `2^16`. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n ∧ n < 2 ^ 16 → n % 2 = 0 → OeisA78680.a n ≠ 0

/-- Non-vanishing of `a` on the odd multipliers below `2^16`. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n ∧ n < 2 ^ 16 → n % 2 = 1 → OeisA78680.a n ≠ 0

theorem main : H1 → H2 → OMA.R_OeisA78680_conjecture_R1.H2 := by
  intro h1 h2 n hn
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact h1 n hn h
  · exact h2 n hn h

end OMA.R_OeisA78680_conjecture_R1_H2_R1
