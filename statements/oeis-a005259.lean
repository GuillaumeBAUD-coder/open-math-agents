import Mathlib

/-!
# A005259: irreducibility of the Apéry polynomials

Source: https://oeis.org/A005259
Credit: @jagraj28

A005259 lists the Apéry numbers `a(n) = Sum_{k=0..n} (binomial(n,k) * binomial(n+k,k))^2`.
The entry records a conjecture of Zhi-Wei Sun (2013): for each `n = 1, 2, 3, ...` the Apéry
polynomial `A_n(x) = Sum_{k=0..n} binomial(n,k)^2 * binomial(n+k,k)^2 * x^k` is irreducible over
the field of rational numbers.

The other conjectures quoted in the entry are recorded there as settled (Lupas's double integral
formula, answered in Math Overflow question 178790; Sun's Conjecture 56 (4.3) and Z.-H. Sun's
Conjecture 2.4, proved by Blanco Gómez), so `main` states only Sun's irreducibility conjecture.

(OEIS A005258, with `binomial(n+k,k)` not squared, has the analogous conjecture, which is stated
upstream in formal-conjectures; this file is about A005259.)
-/

namespace OMA.S_oeis_a005259

open Polynomial

/-- The Apéry polynomial `A_n(x) = Sum_{k=0..n} binomial(n,k)^2 * binomial(n+k,k)^2 * x^k`,
over `ℚ`. -/
noncomputable def aperyPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (((n.choose k) ^ 2 * ((n + k).choose k) ^ 2 : ℕ) : ℚ) * X ^ k

/-- Sun's conjecture in OEIS A005259: `A_n(x)` is irreducible over `ℚ` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Irreducible (aperyPoly n) := by
  sorry

end OMA.S_oeis_a005259
