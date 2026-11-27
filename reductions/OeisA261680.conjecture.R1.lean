import FormalConjectures.OEIS.«261680»

-- Reduction OeisA261680.conjecture.R1 of Sums of four binary palindromes
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Every natural number is a sum of four binary palindromes, split into a finite check and a tail

The theorem of Rajasekaran, Shallit and Smith is proved by an automaton argument: one shows that
the set of `n` which are sums of four binary palindromes is recognised by a finite automaton whose
state graph has a certain periodic structure, and that every `n` beyond an explicit threshold is
accepted.  Two ingredients are genuinely separate:

* `H1` is the finite part: the small values of `n` up to a fixed bound, each of which is witnessed
  by an explicit quadruple of binary palindromes.  This is a computation and can be discharged
  mechanically.
* `H2` is the structural part: no counterexample can occur beyond the threshold, which is where the
  automaton argument (or any other global argument) has to be used.

Splitting at `30` isolates the computation from the structural argument.  The threshold is
deliberately small so that `H1` is within reach of a direct check, while `H2` still contains the
whole of the mathematical difficulty.
-/

namespace OMA.R_OeisA261680_conjecture_R1

open OeisA261680

/-- The finite part: every `n < 30` is a sum of four binary palindromes, i.e. `a n > 0`. -/
def H1 : Prop :=
  ∀ n ∈ Finset.range 30, 0 < a n

/-- The structural part: every `n ≥ 30` is a sum of four binary palindromes. -/
def H2 : Prop :=
  ∀ n : ℕ, 30 ≤ n → 0 < a n

theorem main : H1 → H2 → type_of% @OeisA261680.conjecture := by
  intro h1 h2 n
  by_cases hn : n < 30
  · exact h1 n (Finset.mem_range.mpr hn)
  · exact h2 n (by omega)

end OMA.R_OeisA261680_conjecture_R1
