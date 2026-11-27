import Mathlib

/-!
# Are there infinitely many safe and Sophie Germain primes?

Source: https://en.wikipedia.org/wiki/safe_and_Sophie_Germain_primes
Credit: @Madelyyn

Statement of the problem, transcribed literally from the source:

* "a prime number `p` is a Sophie Germain prime if `2 * p + 1` is also prime";
* "a prime number `p = 2 * q + 1` is called a safe prime if `q` is prime";
* "It is conjectured that there are infinitely many Sophie Germain primes, but this remains
  unproven", and the page asks: "Are there infinitely many Sophie Germain primes?".

The page notes: "Thus, `p = 2 * q + 1` is a safe prime if and only if `q` is a Sophie Germain
prime, so finding safe primes and finding Sophie Germain primes are equivalent". Both halves of
the question are therefore stated, exactly as the title asks.

No proof here: `main` stays `sorry` (this file only states the problem).
-/

namespace OMA.S_wp_are_there_infinitely_many_safe_and_sophie_germain_primes

/-- A prime number `p` is a Sophie Germain prime if `2 * p + 1` is also prime
(Wikipedia, "safe and Sophie Germain primes"). -/
def IsSophieGermainPrime (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- A prime number `p = 2 * q + 1` is a safe prime if `q` is prime
(Wikipedia, "safe and Sophie Germain primes"). -/
def IsSafePrime (p : ℕ) : Prop := p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = 2 * q + 1

/-- Are there infinitely many safe and Sophie Germain primes? -/
theorem main :
    {p : ℕ | IsSophieGermainPrime p}.Infinite ∧ {p : ℕ | IsSafePrime p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_safe_and_sophie_germain_primes
