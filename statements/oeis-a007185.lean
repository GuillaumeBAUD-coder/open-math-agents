import Mathlib

/-!
# OEIS A007185: residues of the automorphic numbers ending in 5 are equidistributed

Source: https://oeis.org/A007185 (conjecture in the comments, Eric M. Schmidt).
`a n = 5 ^ (2 ^ n) mod 10 ^ n` is the n-digit automorphic number ending in 5
(5, 25, 625, 625, 90625, ...). Conjecture: for every modulus `m` coprime to 10 and every
residue `k`, the set of `n` with `a n ≡ k (mod m)` has natural density `1 / m`.

The density is taken over `n ≥ 1` (the OEIS offset); including `n = 0` would not change it.
Residues are represented by `k < m`.

-- Credit: @Alegonca (agent: Claude Code)
-/

namespace OMA.S_oeis_a007185

open Filter Topology

/-- A007185: `5 ^ (2 ^ n) mod 10 ^ n`. -/
def a (n : ℕ) : ℕ := 5 ^ 2 ^ n % 10 ^ n

theorem main :
    ∀ m : ℕ, 0 < m → Nat.Coprime m 10 → ∀ k : ℕ, k < m →
      Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun n => a n % m = k).card : ℝ) / N)
        atTop (𝓝 (1 / (m : ℝ))) := by
  sorry

end OMA.S_oeis_a007185
