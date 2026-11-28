import Mathlib

/-!
# A242266: sums of the first k primes as small primitive roots (Sun's conjecture)

Source: https://oeis.org/A242266 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A242266 (offset 1): a(n) = |{0 < g < prime(n): g is a primitive root mod prime(n) with
g = sum_{j=1..k} prime(j) for some k > 0}|; data 0, 1, 1, 1, 1, 1, 2, 2, 3, ...
(a(4) = 1 since 2 + 3 = 5 is a primitive root modulo 7 with 5 < 7.)

The entry records (Zhi-Wei Sun):

  Conjecture: (i) a(n) > 0 for all n > 1. In other words, for any odd prime p, there is a
  positive integer k such that the sum of the first k primes is not only a primitive root modulo
  p but also smaller than p.
  (ii) For any n > 1, there is a number k among 1, ..., n such that
  sum_{j=1..k}(-1)^(k-j)*prime(j) is a primitive root modulo prime(n).

Both parts are stated here.

Reading of the source:
* `prime j` is the `j`-th prime with `prime 1 = 2` (`Nat.nth Nat.Prime (j - 1)`).
* "g is a primitive root modulo p" for a prime `p`: the residue of `g` has multiplicative order
  `p - 1` in `ZMod p` (so `g` is not divisible by `p`).
* Part (i) is stated in its second form ("in other words"): for every odd prime `p` there is
  `k ≥ 1` with `S_k = prime(1) + ... + prime(k) < p` and `S_k` a primitive root modulo `p`.
* Part (ii): the alternating sum `∑_{j=1}^{k} (-1)^(k-j) prime(j)` is an integer, taken modulo
  `prime(n)`.
-/

namespace OMA.S_oeis_a242266

/-- `prime j`: the `j`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

/-- The sum of the first `k` primes. -/
noncomputable def S (k : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 k, prime j

/-- The alternating sum `∑_{j=1}^{k} (-1)^(k-j) prime(j)`. -/
noncomputable def T (k : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 k, (-1) ^ (k - j) * (prime j : ℤ)

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∃ k, 1 ≤ k ∧ S k < p ∧ orderOf (S k : ZMod p) = p - 1) ∧
    ∀ n : ℕ, 1 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧
      orderOf (T k : ZMod (prime n)) = prime n - 1 := by
  sorry

end OMA.S_oeis_a242266
