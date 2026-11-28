import Mathlib

/-!
# A016090: Automorphic numbers ending in digit 6, with repetitions

Source: https://oeis.org/A016090
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n) = 16^(5^n) mod 10^n`. For any positive integer `m` coprime to `10` and any
integer `k`, the natural density of `n` such that `a(n) ≡ k (mod m)` is `1 / m`.
-/

namespace OMA.S_oeis_a016090

/-- A016090: `a(n) = 16^(5^n) mod 10^n`. -/
def a (n : ℕ) : ℕ :=
  16 ^ (5 ^ n) % 10 ^ n

/-- For every `m > 0` coprime to `10` and every `k`, the natural density of
`{n : ℕ | a(n) ≡ k (mod m)}` is `1 / m`. -/
theorem main :
    ∀ m k : ℕ, 0 < m → Nat.Coprime m 10 →
      Filter.Tendsto
        (fun N : ℕ => (((Finset.range N).filter (fun n => a n % m = k % m)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds (1 / (m : ℝ))) := by
  sorry

end OMA.S_oeis_a016090
