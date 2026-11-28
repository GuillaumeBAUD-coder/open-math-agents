import Mathlib

/-!
# OEIS A346696: p(n) divides a later partition number

Source: https://oeis.org/A346696 (OEIS Foundation, CC BY-SA 4.0).

Entry: a(n) is the least positive k such that A000041(n) divides A000041(n+k),
or 0 if no such k exists (offset 0).

Conjecture (in the entry): a(n) > 0 for all n.

Formalization notes:
* A000041(n) = p(n) is the number of partitions of n,
  `Fintype.card (Nat.Partition n)`.
* a(n) > 0 means some positive k has p(n) ∣ p(n+k); n ranges over all n ≥ 0
  (the offset is 0).
-/

namespace OMA.S_oeis_a346696

/-- The partition function p(n) (A000041). -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- For every n ≥ 0 there is k > 0 with p(n) dividing p(n+k). -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ p n ∣ p (n + k) := by
  sorry

end OMA.S_oeis_a346696
