import OMAStatements.S_oeis_a255401
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Tactic

/-!
A counterexample to the maximum of eight conjectured in OEIS A255401.
Start with the listed eight-divisor term 9399. Multiplication by the prime
2^28 + 255 appends a second block of eight divisors. For every divisor d of
9399, the binary weight of 255*d is eight and 255*d < 2^28, so the binary
weight of (2^28+255)*d is eight more than that of d.
-/

open OMA.S_oeis_a255401
open scoped Pointwise

private def rankedDivisors : Finset ℕ :=
  {1, 3, 13, 39, 241, 723, 3133, 9399, 268435711, 805307133, 3489664243,
   10468992729, 64693006351, 194079019053, 841009082563, 2523027247689}

set_option maxRecDepth 12000 in
private theorem divisors_certificate :
    Nat.divisors 2523027247689 = rankedDivisors := by
  change Nat.divisors (3 * 13 * 241 * 268435711) = _
  rw [Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul,
    (by norm_num : Nat.Prime 3).divisors, (by norm_num : Nat.Prime 13).divisors,
    (by norm_num : Nat.Prime 241).divisors, (by norm_num : Nat.Prime 268435711).divisors]
  decide

private theorem ranks_certificate : HasDivisorDigitProperty 2523027247689 := by
  unfold HasDivisorDigitProperty
  rw [divisors_certificate]
  exact ⟨by decide, by decide⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a255401.main) := by
  intro h
  have hmem : 16 ∈ {k : ℕ | ∃ m : ℕ, HasDivisorDigitProperty m ∧ m.divisors.card = k} :=
    ⟨2523027247689, ranks_certificate, by rw [divisors_certificate]; decide⟩
  exact (by decide : ¬ (16 : ℕ) ≤ 8) (h.2.2 hmem)
