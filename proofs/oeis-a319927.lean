import OMAStatements.S_oeis_a319927
import Mathlib

-- Counterexample n = 9216 = 2^10 * 3^2 (Peter Munn's member of A319927, used by the refutation the statement
-- cites): the odd nonunitary divisors have square sum 9, which divides 41243877 (all nonunitary divisors),
-- but at exponent 1 the sums are 3 and 16361, and 3 does not divide 16361.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a319927.main) := by
  intro h
  have hm : OMA.S_oeis_a319927.member 9216 := by
    unfold OMA.S_oeis_a319927.member
    decide +kernel
  have h1 : ¬ (OMA.S_oeis_a319927.sums 9216 1).1 ∣ (OMA.S_oeis_a319927.sums 9216 1).2 := by
    decide +kernel
  exact h1 (h 9216 hm 1)
