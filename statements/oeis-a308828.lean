import Mathlib

namespace OMA.S_oeis_a308828

/-- The linear congruential sequence `x 0 = 0`, `x (i+1) = (a * x i + c) mod n`. -/
def lcg (n a c : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (a * lcg n a c i + c) % n

/-- A308828(n): number of sequences that include all residues modulo n, starting with
`x 0 = 0` and `x (i+1) = a * x i + c (mod n)`, where `a` and `c` range over `[0..n-1]`.
As in the OEIS PARI program (and the comment "all such sequences will be cyclic with period
length n"), the n terms `x 1, ..., x n` of one cycle must run through all residues. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {f : ℕ → ℕ | ∃ a < n, ∃ c < n, f = lcg n a c ∧
    ∀ r < n, ∃ i ∈ Finset.Icc 1 n, f i = r}

/-- A003557(m) = m / rad(m). -/
def a003557 (m : ℕ) : ℕ := m / ∏ p ∈ m.primeFactors, p

/-- Conjecture (Andrew Howroyd, 2019): a(n) = phi(n) * A003557(n / gcd(n, 2)). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = n.totient * a003557 (n / Nat.gcd n 2) := by
  sorry

end OMA.S_oeis_a308828
