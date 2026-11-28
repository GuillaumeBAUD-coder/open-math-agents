import Mathlib

/-!
# OEIS A032450: Poulet's Conjecture

Source: https://oeis.org/A032450
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Poulet's Conjecture states that for any positive integer $n$, the alternating sequence
$$f_0(n) = n, \quad f_{2k+1}(n) = \sigma(f_{2k}(n)), \quad f_{2k+2}(n) = \phi(f_{2k+1}(n)),$$
where $\sigma(m) = \sum_{d \mid m} d$ is the sum of divisors and $\phi(m)$ is Euler's totient
function, is eventually periodic.
-/

namespace OMA.S_oeis_a032450

/-- Sum of positive divisors of `m`. -/
def sigma (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, d

/-- The Poulet alternating sequence `f k n` starting from `n`. -/
def pouletSeq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 =>
      if k % 2 = 0 then sigma (pouletSeq n k)
      else Nat.totient (pouletSeq n k)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ (N p : ℕ), 1 ≤ p ∧ ∀ k : ℕ, N ≤ k → pouletSeq n (k + p) = pouletSeq n k := by
  sorry

end OMA.S_oeis_a032450
