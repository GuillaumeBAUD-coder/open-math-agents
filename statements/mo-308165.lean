import Mathlib

/-!
# Finite maps and jacobian condition

Source: https://mathoverflow.net/questions/308165
Credit: @JeremyDevs

Question (MathOverflow 308165, 2018). Let `k` be an algebraically closed field and take
`f_1, ..., f_n ∈ k[X_1, ..., X_n]` with the jacobian condition `det J_f = 1`. Let
`A := k[X_1, ..., X_n] / (f_1, ..., f_n)` and consider the induced map
`f^* : Spec(A) → Spec(k)`. In this case `f^*` is a finite map. Assume that `k` is only a domain.
Is `f^*` a finite map? (The asker adds that in the problem this came from, `k` is a discrete
valuation ring of characteristic `0` with finite residue field; the question posed is the one
for a domain.)

The answer at the source is no: take `f = t x^p + x` over `k = F_p[t]` (one variable, and
`f' = p t x^(p-1) + 1 = 1`). Then `A = k[x] / (t x^p + x)` is not a finitely generated
`k`-module, because the class of `x` is not integral over `k`: every nonzero multiple of
`t x^p + x` has leading coefficient divisible by `t`, so none is monic. `main` states this
negative answer: there is a domain `k`, an `n` and `f_1, ..., f_n` with `det J_f = 1` for which
`A` is not finite over `k`.

Conventions:
* `k[X_1, ..., X_n]` is `MvPolynomial (Fin n) k`, and the family is `f : Fin n → _`.
* The jacobian matrix has `(i, j)` entry `∂ f_i / ∂ X_j` (`MvPolynomial.pderiv j (f i)`), and
  the jacobian condition is the polynomial identity `det J_f = 1` in `k[X_1, ..., X_n]` (the
  strongest reading; it implies the condition modulo `(f_1, ..., f_n)`).
* `A` is the quotient by `Ideal.span (Set.range f)`. A morphism of affine schemes
  `Spec A → Spec k` is finite exactly when `A` is a finitely generated `k`-module, so
  "`f^*` is not finite" is `¬ Module.Finite k A`.
-/

namespace OMA.S_mo_308165

/-- Over a domain, the jacobian condition `det J_f = 1` does not force
`k[X_1, ..., X_n] / (f_1, ..., f_n)` to be finite over `k`. -/
theorem main :
    ∃ (k : Type) (_ : CommRing k) (_ : IsDomain k) (n : ℕ) (f : Fin n → MvPolynomial (Fin n) k),
      (Matrix.of fun i j => MvPolynomial.pderiv j (f i)).det = 1 ∧
      ¬ Module.Finite k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) := by
  sorry

end OMA.S_mo_308165
