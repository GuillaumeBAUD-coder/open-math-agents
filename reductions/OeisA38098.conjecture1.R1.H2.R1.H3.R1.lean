import OMAReductions.R_OeisA38098_conjecture1_R1_H2_R1

-- Reduction of step OeisA38098.conjecture1.R1.H2.R1.H3 (hypothesis H3 of
-- OeisA38098.conjecture1.R1.H2.R1) into its three conjuncts.
--
-- H3 in the parent reduction is a conjunction of three independent finite checks of explicit
-- constants (Schoenfeld, Math. Comp. 30 (1976) 337-360, the finite ranges verified there by
-- computation); the three parts share no lemma and have wildly different computational size:
--   H1: psi on [1500, 10^10]           (prime powers up to 10^10, ~4.55e8 primes)
--   H2: theta on [599, 30000]          (prime powers up to 30000, 3245 primes)
--   H3: primeCounting vs logIntegral on [2657, 400000]  (33860 primes)
-- Splitting them lets each be attacked on its own; main is the pure conjunction split.
--
-- Note on strength: 1/(8*pi) * sqrt x * log x ^ 2 is Schoenfeld's RH-conditional bound for
-- |psi x - x| and |theta x - x|, and 1/(8*pi) * sqrt x * log x is his RH-conditional bound for
-- |pi x - li x|. The psi clause above (4/5 * sqrt x on [1500,10^10]) is strictly stronger than
-- the RH-conditional psi bound near 10^10, so it cannot be derived from RH: it is a finite
-- computation, not an analytic consequence.

namespace OMA.R_OeisA38098_conjecture1_R1_H2_R1_H3_R1

def H1 : Prop :=
  ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x

def H2 : Prop :=
  ∀ x : ℝ, 599 ≤ x → x ≤ 30000 →
    |Chebyshev.theta x - x| < 1 / (8 * Real.pi) * (Real.sqrt x * Real.log x ^ 2)

def H3 : Prop :=
  ∀ x : ℝ, 2657 ≤ x → x ≤ 400000 →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| <
      1 / (8 * Real.pi) * (Real.sqrt x * Real.log x)

theorem main : H1 → H2 → H3 → OMA.R_OeisA38098_conjecture1_R1_H2_R1.H3 := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_OeisA38098_conjecture1_R1_H2_R1_H3_R1
