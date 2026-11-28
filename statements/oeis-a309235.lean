import Mathlib.NumberTheory.Bernoulli

namespace OMA.S_oeis_a309235

/-- The rational number `F(n) = A027641(n-1)/n + A027642(n-1)/n^2`, where `A027641(k)` and
`A027642(k)` are the numerator and denominator of the `k`-th Bernoulli number `B_k`. -/
def bernoulliFrac (n : ℕ) : ℚ :=
  ((bernoulli (n - 1)).num : ℚ) / (n : ℚ) + ((bernoulli (n - 1)).den : ℚ) / ((n : ℚ) ^ 2)

/-- OEIS A309132: `a(n)` is the reduced denominator of `F(n)`. -/
def A309132 (n : ℕ) : ℕ :=
  (bernoulliFrac n).den

/-- Carmichael numbers: composite integers `m ≥ 2` satisfying `a^m ≡ a (mod m)` for all `a : ℕ`. -/
def IsCarmichael (m : ℕ) : Prop :=
  2 ≤ m ∧ ¬ m.Prime ∧ ∀ a : ℕ, a ^ m ≡ a [MOD m]

/-- Conjecture (OEIS A309235, Amiram Eldar & Thomas Ordowski): the composite numbers `m`
such that `A309132(m) ∣ m` are precisely the Carmichael numbers. -/
theorem main :
    ∀ m : ℕ, 2 ≤ m → ¬ m.Prime → (A309132 m ∣ m ↔ IsCarmichael m) := by
  sorry

end OMA.S_oeis_a309235
