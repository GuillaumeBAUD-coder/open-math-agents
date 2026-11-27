import Mathlib

/-!
# Are there infinitely many Cullen primes?

Source: https://en.wikipedia.org/wiki/Cullen_number
Credit: @Madelyyn

Statement of the problem, transcribed from the source:

* "a **Cullen number** is a member of the integer sequence `C n = n * 2 ^ n + 1` (where `n` is a
  natural number)";
* a Cullen prime is a Cullen number that is prime: "The only known **Cullen primes**, sixteen in
  all, are those for `n` equal to: ...";
* "Still, it is conjectured that there are infinitely many Cullen primes."

So: infinitely many natural numbers of the form `n * 2 ^ n + 1` are prime. (The page also records
the separate open question whether some prime `p` has `C p` prime; that is not what is stated
here.)

No proof here: `main` stays `sorry` (this file only states the problem).
-/

namespace OMA.S_wp_are_there_infinitely_many_cullen_primes

/-- The `n`-th Cullen number, `C n = n * 2 ^ n + 1` (Wikipedia, "Cullen number"). -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- Are there infinitely many Cullen primes, i.e. prime Cullen numbers `n * 2 ^ n + 1`? -/
theorem main : {m : ℕ | ∃ n : ℕ, m = cullen n ∧ m.Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cullen_primes
