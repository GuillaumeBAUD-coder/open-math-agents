import OMAStatements.S_oeis_a347293

-- Reduction oeis-a347293.R1 of oeis-a347293: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a347293_R1

open OMA.S_oeis_a347293

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ f : ℕ → ℂ, ∀ n : ℕ, 1 ≤ n →
      ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n) =
        ∑ d ∈ n.divisors, (((n / d) ^ 2 : ℕ) : ℂ) *
          ((Nat.totient d : ℂ) *
            ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * f (d / e)))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ f : ℕ → ℂ, (f 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
      (∑ i ∈ Finset.Icc 1 1, ∑ k ∈ Finset.Icc 1 1, f (Nat.gcd (1 + (i - 1) * (k - 1)) 1) = 1) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Nat.Coprime m n →
        ∑ i ∈ Finset.Icc 1 (m * n), ∑ k ∈ Finset.Icc 1 (m * n),
            f (Nat.gcd (1 + (i - 1) * (k - 1)) (m * n)) =
          (∑ i ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 m, f (Nat.gcd (1 + (i - 1) * (k - 1)) m)) *
          (∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n)))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 n, Nat.gcd (1 + (i - 1) * (k - 1)) n =
        ∑ d ∈ n.divisors, (n / d) ^ 2 * (Nat.totient d) ^ 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a347293.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a347293_R1
