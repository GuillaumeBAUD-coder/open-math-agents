import Mathlib

/-!
# Does every rational number with an odd denominator have an odd greedy expansion?

Source: https://en.wikipedia.org/wiki/rational_number
(the problem is described at https://en.wikipedia.org/wiki/Odd_greedy_expansion)
Credit: @ishaanzee

The odd greedy algorithm, applied to a positive rational `x / y` with `y` odd: let `u` be the
least odd number that is greater than or equal to `y / x`, include the fraction `1 / u` in the
expansion, and continue in the same way with the remaining fraction `x / y - 1 / u`, avoiding
repeated uses of the same unit fraction. Stein, Selfridge, Graham and others asked whether
this algorithm terminates with a finite expansion for every `x / y` with `y` odd.

Formalization choices:
* A state of the algorithm is the remaining fraction `r` together with the finite set of
  denominators already used. One step chooses the least odd `u` with `y / x ≤ u` (that is,
  `r⁻¹ ≤ u`) among the denominators not used yet, and replaces `r` by `r - 1 / u`. Since
  `1 / u ≤ r`, the remainder never becomes negative. The algorithm has terminated once the
  remainder is `0`, and a state with remainder `0` is left unchanged.
* "Rational number with an odd denominator" is read as a positive rational whose reduced
  denominator is odd (it can be written `x / y` with `y` odd iff its reduced denominator is
  odd). Egyptian fractions represent positive rationals, so `x / y > 0`.
-/

namespace OMA.S_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion

/-- The denominator chosen by the odd greedy algorithm when the remaining fraction is `r` and
the denominators in `used` have already been used: the least odd `u` with `r⁻¹ ≤ u` that is
not in `used`. -/
noncomputable def nextDenom (r : ℚ) (used : Finset ℕ) : ℕ :=
  sInf {u : ℕ | Odd u ∧ r⁻¹ ≤ (u : ℚ) ∧ u ∉ used}

/-- One step of the odd greedy algorithm on the state (remaining fraction, used denominators).
A state whose remaining fraction is `0` is final and is left unchanged. -/
noncomputable def step (s : ℚ × Finset ℕ) : ℚ × Finset ℕ :=
  if s.1 = 0 then s else (s.1 - 1 / (nextDenom s.1 s.2 : ℚ), insert (nextDenom s.1 s.2) s.2)

/-- **Odd greedy expansion problem**: for every positive rational `q` with odd denominator, the
odd greedy algorithm started from `q` (with no denominators used yet) terminates, i.e. after
finitely many steps the remaining fraction is `0`. -/
theorem main : ∀ q : ℚ, 0 < q → Odd q.den → ∃ n : ℕ, (step^[n] (q, ∅)).1 = 0 := by
  sorry

end OMA.S_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion
