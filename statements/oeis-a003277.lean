import Mathlib

/-!
# A003277: Michon's conjecture on Carmichael multiples of odd cyclic numbers

Source: https://oeis.org/A003277
Credit: @majdi19

A003277 lists the cyclic numbers: positive integers `k` with `gcd(k, φ(k)) = 1`
(equivalently, `k` such that the only group of order `k` is the cyclic one).
The OEIS comment by G. P. Michon (Jan 08 2008) reads:

  Any divisor of a Carmichael number (A002997) must be odd and cyclic. Conversely,
  G. P. Michon conjectured (c. 1980) that any odd cyclic number has at least one
  Carmichael multiple.

Conventions.
* A Carmichael number (A002997) is a composite number `n` such that
  `b ^ (n - 1) ≡ 1 (mod n)` for every integer `b` coprime to `n`. We state this for natural
  `b`, which is equivalent (only the residue of `b` modulo `n` matters).
  Composite means `1 < n` and `n` not prime.
* A cyclic number is a positive `k` with `Nat.Coprime k (Nat.totient k)`.
  Note that `1` is an odd cyclic number (its Carmichael multiples are all Carmichael numbers).
* Michon and Crump verified the conjecture for all odd cyclic numbers below 10000 (OEIS).
-/

namespace OMA.S_oeis_a003277

/-- Carmichael numbers (A002997): composite `n` with `b ^ (n - 1) ≡ 1 [MOD n]`
for every `b` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ b : ℕ, Nat.Coprime b n → b ^ (n - 1) ≡ 1 [MOD n]

/-- Cyclic numbers (A003277): positive `k` coprime to `φ(k)`. -/
def IsCyclicNumber (k : ℕ) : Prop :=
  0 < k ∧ Nat.Coprime k (Nat.totient k)

/-- Michon's conjecture: every odd cyclic number divides some Carmichael number. -/
theorem main : ∀ k : ℕ, Odd k → IsCyclicNumber k → ∃ m : ℕ, k ∣ m ∧ IsCarmichael m := by
  sorry

end OMA.S_oeis_a003277
