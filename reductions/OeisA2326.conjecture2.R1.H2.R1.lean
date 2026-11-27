import OMAReductions.R_OeisA2326_conjecture2_R1

-- Reduction OeisA2326.conjecture2.R1.H2.R1 of step OeisA2326.conjecture2.R1.H2
-- Credit: @marcusbuffett

/-!
# Wieferich primes with a cube: a verified range, and the open tail

The parent step says that no prime `p` has `p ^ 3 ∣ 2 ^ (p - 1) - 1` (stated for the Wieferich
primes, those with `p ^ 2 ∣ 2 ^ (p - 1) - 1`). Only two Wieferich primes are known, `1093` and
`3511`, and whether a prime can divide `2 ^ (p - 1) - 1` to the third power is open.

* `H1` (a range, by computation): the statement for every prime `p < 1000000`. In fact no integer
  `2 ≤ p < 1000000` has `p ^ 3 ∣ 2 ^ (p - 1) - 1`; each case is one modular power.
* `H2`: the statement for every prime `p ≥ 1000000`. This is the open problem and stays open.
-/

namespace OMA.R_OeisA2326_conjecture2_R1_H2_R1

/-- No Wieferich prime below `1000000` has the cube dividing. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p < 1000000 → p ^ 2 ∣ 2 ^ (p - 1) - 1 → ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1

/-- The open tail: primes from `1000000` on. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 1000000 ≤ p → p ^ 2 ∣ 2 ^ (p - 1) - 1 → ¬ p ^ 3 ∣ 2 ^ (p - 1) - 1

theorem main : H1 → H2 → OMA.R_OeisA2326_conjecture2_R1.H2 := by
  intro h1 h2 p hp hw
  by_cases hlt : p < 1000000
  · exact h1 p hp hlt hw
  · exact h2 p hp (by omega) hw

end OMA.R_OeisA2326_conjecture2_R1_H2_R1
