import Mathlib

/-!
# A Fundamental Theorem of Algebra type result

Source: https://math.stackexchange.com/questions/3821760
Credit: @JeremyDevs

Question (Math StackExchange 3821760, 2020). Consider a polynomial
`p(t) = ∑_{i=1}^n a_i t^{b_i} + a_0` of degree `b_n`; show that it admits at most `n + 1`
nonnegative roots and at least one complex root. Assume all `b_i` are positive and `a_i` are
real numbers.

The claim is true: by Descartes' rule of signs a real polynomial with at most `n + 1` nonzero
terms has at most `n` positive roots, so together with the possible root `0` it has at most
`n + 1` nonnegative roots; and since the degree `b_n` is positive, the fundamental theorem of
algebra gives a complex root. `main` states exactly this claim.

Conventions:
* The coefficients are `a₀ : ℝ` and `a : Fin n → ℝ`, the exponents are `b : Fin n → ℕ` (the
  0-based index `i : Fin n` stands for the 1-based index `i + 1` of the source), all `b i` are
  positive, and `p = C a₀ + ∑ i, C (a i) * X ^ b i` in `ℝ[X]`.
* "Of degree `b_n`" is the hypothesis `p.natDegree = b ⟨n - 1, _⟩` (the last exponent), which
  needs `0 < n`. No further assumption (such as the `b i` being distinct or increasing, or the
  `a i` being nonzero) is made; none is stated in the source.
* "At most `n + 1` nonnegative roots" counts distinct roots: the set of real `t` with `0 ≤ t`
  and `p.eval t = 0` is finite and has at most `n + 1` elements (`Set.ncard`).
* "At least one complex root" is `∃ z : ℂ, aeval z p = 0`.
-/

namespace OMA.S_mse_3821760

open Polynomial

/-- A real polynomial `a₀ + ∑_{i=1}^n a_i t^{b_i}` of degree `b_n` with positive exponents `b_i`
has at most `n + 1` nonnegative real roots and at least one complex root. -/
theorem main : ∀ (n : ℕ) (hn : 0 < n) (a₀ : ℝ) (a : Fin n → ℝ) (b : Fin n → ℕ)
    (hb : ∀ i, 0 < b i) (p : ℝ[X]) (hp : p = C a₀ + ∑ i, C (a i) * X ^ b i)
    (hdeg : p.natDegree = b ⟨n - 1, by omega⟩),
    ({t : ℝ | 0 ≤ t ∧ p.eval t = 0}.Finite ∧ {t : ℝ | 0 ≤ t ∧ p.eval t = 0}.ncard ≤ n + 1) ∧
      ∃ z : ℂ, aeval z p = 0 := by
  sorry

end OMA.S_mse_3821760
