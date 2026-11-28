import Mathlib

/-!
# A235987: prime(k) + phi(n-k) a Sophie Germain prime with primitive root 2 (Sun's conjecture)

Source: https://oeis.org/A235987 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A235987 (offset 1): a(n) = |{0 < k < n: p = prime(k) + phi(n-k) is a Sophie prime having 2 as a
primitive root}|; data 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, ...
(a(10) = 1 since prime(3) + phi(7) = 5 + 6 = 11 is a Sophie Germain prime and 2 is a primitive
root modulo 11.)

The entry records (Zhi-Wei Sun):

  Conjecture: (i) a(n) > 0 for all n > 37.
  (ii) For any integer n > 7, there is a positive integer k < n such that
  p = phi(k) + phi(n-k)/2 - 1 is a prime having 2 as a primitive root.

Both parts are stated here.

Reading of the source:
* `prime k` is the `k`-th prime with `prime 1 = 2` (`Nat.nth Nat.Prime (k - 1)`), and `phi` is
  `Nat.totient`.
* A Sophie (Germain) prime is a prime `p` with `2p + 1` also prime. "2 is a primitive root modulo
  p" means that 2 has multiplicative order `p - 1` modulo `p` (`orderOf (2 : ZMod p) = p - 1`).
* Part (ii): `phi(k) + phi(n-k)/2 - 1` is an integer only when `phi(n-k)` is even (it is odd
  only for `n - k ≤ 2`, where it is 1 and the value is not an integer, hence not a prime), so the
  condition is: `phi(n-k)` even and `p = phi(k) + phi(n-k)/2 - 1` prime with 2 a primitive root.
* `a(n) > 0` is stated as the existence of a qualifying `k` with `0 < k < n`.
-/

namespace OMA.S_oeis_a235987

/-- `prime k`: the `k`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- `p` is prime and 2 is a primitive root modulo `p`. -/
def PrimRootTwo (p : ℕ) : Prop := p.Prime ∧ orderOf (2 : ZMod p) = p - 1

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 37 < n → ∃ k, 0 < k ∧ k < n ∧
      PrimRootTwo (prime k + Nat.totient (n - k)) ∧
        (2 * (prime k + Nat.totient (n - k)) + 1).Prime) ∧
    ∀ n : ℕ, 7 < n → ∃ k, 0 < k ∧ k < n ∧ Even (Nat.totient (n - k)) ∧
      PrimRootTwo (Nat.totient k + Nat.totient (n - k) / 2 - 1) := by
  sorry

end OMA.S_oeis_a235987
