import Mathlib

/-!
# Is there a covering system with odd distinct moduli?

Source: https://en.wikipedia.org/wiki/Covering_system
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **covering system** is a finite set of congruence classes `a mod m`, with distinct
moduli `m > 1`, whose union is all of the integers.  Erdős asked whether there is a covering system
all of whose moduli are odd; this is open.

So the proposition formalized below is: there are a finite set `S` of odd moduli greater than `1`
and a residue `r a` for each `a` in `S` such that every natural number is congruent to `r a`
modulo some `a` in `S`.
-/

namespace OMA.S_wp_is_there_a_covering_system_with_odd_distinct_moduli

-- definitions the statement needs (no sorry, no axiom)

/-- `S` together with residues `r` is a **covering system with odd distinct moduli**: every modulus
in `S` is odd and greater than `1`, and every natural number lies in one of the chosen classes. -/
def IsOddCoveringSystem (S : Finset ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ a ∈ S, Odd a ∧ 1 < a) ∧ ∀ n : ℕ, ∃ a ∈ S, n % a = r a

/-- Is there a covering system with odd distinct moduli? -/
theorem main : ∃ (S : Finset ℕ) (r : ℕ → ℕ), IsOddCoveringSystem S r := by
  sorry

end OMA.S_wp_is_there_a_covering_system_with_odd_distinct_moduli
