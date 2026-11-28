import OMAReductions.R_oeis_a084030_R1
import Mathlib

/-! # Reduction oeis-a084030.R1.H1.R1 - n ≤ 130 vs n ≥ 131

The existence proof for n ≥ 3 splits at the table bound:

* `H1` : 3 ≤ n ≤ 130, discharged by the finite witness table
  `table029` (reduced further in `oeis-a084030.R1.H1.R1.H1.R1`,
  one step per sub-range).
* `H2` : n ≥ 131, the two-block construction `A084029_large`. -/

namespace OMA.R_oeis_a084030_R1_H1_R1

/-- Table range: at least n witnesses for 3 ≤ n ≤ 130. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 ≤ n → n ≤ 130 → ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s, n ∣ N ∧ (Nat.digits 10 N).length = n ∧ (Nat.digits 10 N).sum = n

/-- Large range: at least n witnesses for n ≥ 131. -/
def H2 : Prop :=
  ∀ n : ℕ, 131 ≤ n → ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s, n ∣ N ∧ (Nat.digits 10 N).length = n ∧ (Nat.digits 10 N).sum = n

theorem main : H1 → H2 → OMA.R_oeis_a084030_R1.H1 := by
  intro h1 h2 n hn
  rcases Nat.lt_or_ge n 131 with h | h
  · exact h1 n hn (by omega)
  · exact h2 n h

end OMA.R_oeis_a084030_R1_H1_R1
