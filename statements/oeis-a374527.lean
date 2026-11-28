import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Basic

namespace OMA.S_oeis_a374527

/-- One step of the Collatz map: `n / 2` if `n` is even, `3 * n + 1` if `n` is odd. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- A set `S : Set ℕ` is a Sidon set if all unordered pairwise sums `a + b` (`a, b ∈ S`) are
distinct. -/
def IsSidonSet (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- `n` has a finite Collatz trajectory reaching `1` whose set of visited terms (up to the first
arrival at `1`) is a Sidon set. -/
def HasSidonCollatzTrajectory (n : ℕ) : Prop :=
  ∃ t : ℕ,
    collatzStep^[t] n = 1 ∧
    (∀ j < t, collatzStep^[j] n ≠ 1) ∧
    IsSidonSet { x : ℕ | ∃ j ≤ t, collatzStep^[j] n = x }

/-- Conjecture (OEIS A374527): Every odd number of the form `(4^k - 1) / 3` (`k ≥ 1`, OEIS A002450)
except `5` (i.e., `k ≠ 2`) has a Collatz trajectory that is a Sidon sequence. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → k ≠ 2 →
      Odd ((4 ^ k - 1) / 3) ∧ HasSidonCollatzTrajectory ((4 ^ k - 1) / 3) := by
  sorry

end OMA.S_oeis_a374527
