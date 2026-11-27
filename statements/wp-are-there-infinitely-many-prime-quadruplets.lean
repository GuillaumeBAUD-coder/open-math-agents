import Mathlib

/-!
# Are there infinitely many prime quadruplets?

Source: https://en.wikipedia.org/wiki/prime_quadruplet
Credit: @dayahdover

Transcribed from the source:

* a prime quadruplet is a set of four prime numbers of the form `{p, p + 2, p + 6, p + 8}`
  (the first ones are `{5, 7, 11, 13}`, `{11, 13, 17, 19}`, `{101, 103, 107, 109}`);
* it is not known whether there are infinitely many prime quadruplets, and it is conjectured
  that there are.

A quadruplet is determined by its least element `p`, so there are infinitely many prime
quadruplets exactly when infinitely many natural numbers `p` have `p`, `p + 2`, `p + 6` and
`p + 8` all prime. `main` states the conjectured answer (yes).

No proof here: `main` stays `sorry` (this file only states the problem).
-/

namespace OMA.S_wp_are_there_infinitely_many_prime_quadruplets

/-- `p` is the least element of a prime quadruplet `{p, p + 2, p + 6, p + 8}`. -/
def IsPrimeQuadrupletStart (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime

/-- Are there infinitely many prime quadruplets? (Conjectured: yes.) -/
theorem main : {p : ℕ | IsPrimeQuadrupletStart p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_prime_quadruplets
