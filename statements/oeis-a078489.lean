import Mathlib

/-!
# The binomial threshold A078489 and the Beatty index A003258

Source: https://oeis.org/A078489 and https://oeis.org/A003258
Credit: @etaubman

The PARI program stops on equality. Its output and the table both give a(2) = 2;
the strict inequality in the title would give 3. We formalize the conjecture about
the tabulated sequence. Negative lower binomial indices are zero in the source;
for positive n neither j = 0 nor j = 1 can be the first qualifying index.

A003258(n) is the unique positive index m with complementaryBeatty m =
hofstadterG (upperBeatty n). The formulas for these three functions are those of
OEIS A249115, A005206 and A003231 respectively. The relation below expresses
m = j + n - 1, avoiding subtraction of a larger natural number.
-/

namespace OMA.S_oeis_a078489

noncomputable def upperBeatty (n : N) : N :=
  ?(n : R) * ((5 + Real.sqrt 5) / 2)??

noncomputable def complementaryBeatty (m : N) : N :=
  ?(m : R) * ((5 - Real.sqrt 5) / 2)??

noncomputable def hofstadterG (k : N) : N :=
  ?((k : R) + 1) / ((1 + Real.sqrt 5) / 2)??

def thresholdIndices (n : N) : Set N :=
  {j | 2 � j ? j � n + 1 ? Nat.choose n j � Nat.choose (n - 1) (j - 2)}

theorem main :
    ? n : N, 0 < n  ? j : N, IsLeast (thresholdIndices n) j ?
      complementaryBeatty (j + n - 1) = hofstadterG (upperBeatty n) := by
  sorry

end OMA.S_oeis_a078489
