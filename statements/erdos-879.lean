import Mathlib

/-!
# Erdős Problem 879

Source: https://www.erdosproblems.com/879
Credit: @joshuadc11

Call a set `S ⊆ {1, ..., n}` admissible if `gcd(a, b) = 1` for all `a ≠ b` in `S`. Let
`G(n) = max_{S ⊆ {1, ..., n} admissible} ∑_{a ∈ S} a`
and
`H(n) = ∑_{p < n} p + n * π(n^{1/2})`.
1. Is it true that `G(n) > H(n) - n^{1 + o(1)}`?
2. Is it true that, for every `k ≥ 2`, if `n` is sufficiently large then every admissible set
   maximising `G(n)` contains at least one integer with at least `k` distinct prime factors?

Formalization notes:
- `G(n) > H(n) - n^{1 + o(1)}` is stated as: for every `ε > 0`, for all sufficiently large `n`,
  `(H n : ℝ) - (n : ℝ) ^ (1 + ε) < (G n : ℝ)`.
- `π(n^{1/2})` is the number of primes `p ≤ Nat.sqrt n`.
- In part 2, prime factors means distinct prime factors (`a.primeFactors.card`), since prime powers
  already occur in the baseline `H(n)` construction.
-/

namespace OMA.S_erdos_879

/-- A finite set `S ⊆ {1, ..., n}` is admissible if its elements are pairwise coprime. -/
def IsAdmissible (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 1 n ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

/-- `G n` is the maximum sum of an admissible subset of `{1, ..., n}`. -/
noncomputable def G (n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ S : Finset ℕ, IsAdmissible n S ∧ ∑ a ∈ S, a = s}

/-- `H n = ∑_{p < n} p + n * π(n^{1/2})`. -/
def H (n : ℕ) : ℕ :=
  (∑ p ∈ (Finset.range n).filter Nat.Prime, p) +
    n * ((Finset.Icc 1 (Nat.sqrt n)).filter Nat.Prime).card

theorem main :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (H n : ℝ) - (n : ℝ) ^ (1 + ε) < (G n : ℝ)) ∧
    (∀ k ≥ 2, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ S : Finset ℕ,
      IsAdmissible n S → ∑ a ∈ S, a = G n →
      ∃ a ∈ S, k ≤ a.primeFactors.card) := by
  sorry

end OMA.S_erdos_879
