import Mathlib

/-!
# A236374: k with phi(k)/2 + phi(n-k)/8 = m and 2^(m-1) phi(m) - 1 prime (Sun's conjecture)

Source: https://oeis.org/A236374 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A236374 (offset 1): a(n) = |{0 < k < n: m = phi(k)/2 + phi(n-k)/8 is an integer with
2^(m-1)*phi(m) - 1 prime}|, where phi(.) is Euler's totient function; data
0, 0, ..., 0, 2, 2, 0, 2, 1, 2, ... (a(24) = 1 since phi(8)/2 + phi(16)/8 = 3 with
2^(3-1)*phi(3) - 1 = 7 prime).

The entry records (Zhi-Wei Sun):

  Conjecture: a(n) > 0 for all n > 31.
  We have verified this for n up to 60000.

Reading of the source:
* `phi` is `Nat.totient`. `phi(k)/2 + phi(n-k)/8` is a rational number; it is an integer exactly
  when `8` divides `4 phi(k) + phi(n-k)`, and then it equals `m = (4 phi(k) + phi(n-k)) / 8`,
  which is positive (totients of positive integers are positive).
* `a(n) > 0` means some `k` with `0 < k < n` qualifies; the conjecture is stated in that form,
  for every `n > 31`.
-/

namespace OMA.S_oeis_a236374

/-- `k` qualifies for `n`: `m = φ(k)/2 + φ(n-k)/8` is an integer and `2^(m-1) φ(m) - 1` is prime. -/
def Good (n k : ℕ) : Prop :=
  8 ∣ 4 * Nat.totient k + Nat.totient (n - k) ∧
    (2 ^ ((4 * Nat.totient k + Nat.totient (n - k)) / 8 - 1) *
        Nat.totient ((4 * Nat.totient k + Nat.totient (n - k)) / 8) - 1).Prime

/-- Sun's conjecture: for every `n > 31` some `0 < k < n` qualifies. -/
theorem main : ∀ n : ℕ, 31 < n → ∃ k, 0 < k ∧ k < n ∧ Good n k := by
  sorry

end OMA.S_oeis_a236374
