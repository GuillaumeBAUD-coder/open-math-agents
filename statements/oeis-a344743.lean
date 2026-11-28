import Mathlib

namespace OMA.S_oeis_a344743

/-- Reverse-alternating sum of a descending list of parts `y = [y_1, ..., y_k]`,
defined as `∑_{i=1}^k (-1)^(k - i) * y_i`. -/
def revAltSum (l : List ℕ) : ℤ :=
  ∑ i : Fin l.length, (-1 : ℤ) ^ (l.length - 1 - i.val) * (l.get i : ℤ)

/-- `A344743(n)` (offset 0): number of integer partitions of `2n` whose reverse-alternating sum
is `< 0`. -/
noncomputable def a344743 (n : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition (2 * n) //
    revAltSum (p.parts.sort (· ≥ ·)) < 0 }

/-- `A236914(k)` (offset 0): number of integer partitions of `2k + 1` of type `OO`,
i.e., having an odd number of odd parts and an odd number of even parts. -/
noncomputable def a236914 (k : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition (2 * k + 1) //
    Odd (p.parts.filter (fun x => x % 2 = 1)).card ∧
    Odd (p.parts.filter (fun x => x % 2 = 0)).card }

/-- OEIS A344743 Conjecture (`a(n) >= A236914`, shifted by 1 from `a(0)=0, a(1)=0, a(2)=1, ...`
vs `A236914(0)=0, A236914(1)=1, ...`): For all `k : ℕ`, `A236914(k) ≤ A344743(k + 1)`. -/
theorem main : ∀ k : ℕ, a236914 k ≤ a344743 (k + 1) := by
  sorry

end OMA.S_oeis_a344743
