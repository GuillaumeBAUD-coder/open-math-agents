import Mathlib

/-!
# Is the ratio of two consecutive superior highly composite numbers a prime?

Source: https://mathoverflow.net/questions/281938
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Wikipedia, OEIS and MathWorld state, citing only Ramanujan (Highly composite numbers, Proc.
London Math. Soc. 1915), that the ratio of two consecutive superior highly composite numbers is a
prime. The question observes that the argument seems to need the same unproven input (a case of
the four exponentials conjecture) as the analogous Alaoglu–Erdős statement for colossally
abundant numbers, and asks whether the statement is really proved. The statement below is the
claim itself; a Lean proof of it would be unconditional.

Conventions:
* `d(n)` is the number of divisors, `n.divisors.card`;
* superior highly composite, following Ramanujan's definition: `n ≥ 1` is superior highly
  composite iff there is `ε > 0` with `d(k)/k^ε ≤ d(n)/n^ε` for all `1 ≤ k < n` and
  `d(k)/k^ε < d(n)/n^ε` for all `k > n` (real powers `Real.rpow`);
* with this definition `1` is superior highly composite (take any `ε > 1`), so the sequence is
  `1, 2, 6, 12, 60, 120, …`; the extra first ratio `2 / 1 = 2` is prime, so this changes nothing;
* the sequence is listed increasingly as `Nat.nth IsSHC j`; it is infinite (Ramanujan), and if it
  were finite `Nat.nth` would return `0` from some index on and the ratio claim at the last term
  would read `0 = p * N` with `N ≥ 1`, which is false, so no junk value makes the statement true.
-/

namespace OMA.S_mo_281938

/-- Ramanujan's superior highly composite numbers. -/
def IsSHC (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, 1 ≤ k →
    (k < n → (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤ (n.divisors.card : ℝ) / (n : ℝ) ^ ε) ∧
    (n < k → (k.divisors.card : ℝ) / (k : ℝ) ^ ε < (n.divisors.card : ℝ) / (n : ℝ) ^ ε)

/-- The ratio of two consecutive superior highly composite numbers is a prime. -/
theorem main : ∀ j : ℕ, ∃ p : ℕ, p.Prime ∧ Nat.nth IsSHC (j + 1) = p * Nat.nth IsSHC j := by
  sorry

end OMA.S_mo_281938
