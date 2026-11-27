import Mathlib

/-!
# Catalan–Dickson conjecture on aliquot sequences

Source: https://en.wikipedia.org/wiki/Aliquot_sequence#Catalan-Dickson_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the **aliquot sum** `s n` of a natural number `n` is the sum of its proper divisors,
and the **aliquot sequence** of `n` is `n, s n, s (s n), ...`.  The Catalan–Dickson conjecture
states that no aliquot sequence is infinite but non-repeating, that is, every aliquot sequence is
eventually periodic.

So the proposition formalized below is: for every `n` the aliquot sequence of `n` is eventually
periodic, meaning that it returns to some value after a positive number of steps.
-/

namespace OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences

-- definitions the statement needs (no sorry, no axiom)

/-- The **aliquot sum** of `n`: the sum of the proper divisors of `n`. -/
def aliquotSum (n : ℕ) : ℕ :=
  n.properDivisors.sum id

/-- The **aliquot sequence** of `n`, as the `k`-th iterate of the aliquot sum. -/
def aliquotIterate (k n : ℕ) : ℕ :=
  aliquotSum^[k] n

/-- The Catalan–Dickson conjecture: no aliquot sequence is infinite but non-repeating. -/
theorem main : ∀ n : ℕ, ∃ N k : ℕ, 0 < k ∧ aliquotIterate (N + k) n = aliquotIterate N n := by
  sorry

end OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences
