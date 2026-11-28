import Mathlib

/-!
# Positivity of polynomial sequences via generating series

Source: https://mathoverflow.net/questions/51186
Credit: @JeremyDevs

Question (MathOverflow 51186, 2011). Write `F ≥ 0` for a formal power series (in any number of
variables) all of whose coefficients are nonnegative. For a numerical sequence one has
`A(x) = ∑ a_n x^n ≥ 0` if and only if
`∑_n a_n ∑_{k,m ≥ 0} C(n+k, n) C(n+m, n) x^(n+k) y^(n+m) ≥ 0`. Replace the binomial coefficients
by the Gaussian polynomials `[a, b]_q = (q;q)_a / ((q;q)_b (q;q)_(a-b))`. Is it true, for a
given sequence `a_n(q) ∈ ℝ[q]`, that
`∑_n a_n(q) x^n ≥ 0 ⟺ ∑_n a_n(q) ∑_{k,m ≥ 0} [n+k, n]_q [n+m, n]_q x^(n+k) y^(n+m) ≥ 0`?

The answer is no (as the answer at the source shows): the implication from right to left fails
for `a_0 = q`, `a_1 = 1 - q + q^2`, `a_n = 0` for `n ≥ 2`. The coefficient of `x^i y^j` in the
bivariate series is `T_{i,j} = ∑_{s ≤ min(i,j)} a_s [i, s]_q [j, s]_q`, which here equals `q` if
`min(i, j) = 0` and `q + (1 - q + q^2) [i]_q [j]_q` otherwise, where `[m]_q = 1 + q + ... +
q^(m-1)`. This is `1 + q^2` for `i = j = 1`, and it has nonnegative coefficients in all other
cases because `(1 - q + q^2) [m]_q = 1 + q^2 + ... + q^(m-1) + q^(m+1)` for `m ≥ 2`. But `a_1`
has the negative coefficient `-1`. `main` states that the equivalence does not hold for all
sequences.

Conventions:
* A sequence `a_n(q) ∈ ℝ[q]` is `a : ℕ → ℝ[X]`, the variable `X` playing the role of `q`.
* `gauss n k` is the Gaussian polynomial `[n, k]_q`, defined by `[n, 0]_q = 1`,
  `[0, k+1]_q = 0` and the `q`-Pascal rule `[n+1, k+1]_q = [n, k]_q + q^(k+1) [n, k+1]_q`
  (this is the polynomial `(q;q)_n / ((q;q)_k (q;q)_(n-k))` for `k ≤ n`).
* `CoeffNonneg p` says that all coefficients of the polynomial `p` are nonnegative. The series
  `∑ a_n(q) x^n` is `≥ 0` when every `a_n` is; the bivariate series is `≥ 0` when every
  coefficient `T a i j` of `x^i y^j` (a polynomial in `q`) is.
-/

namespace OMA.S_mo_51186

open Polynomial

/-- The Gaussian polynomial (`q`-binomial coefficient) `[n, k]_q`, with `q = X`. -/
noncomputable def gauss : ℕ → ℕ → ℝ[X]
  | 0, k => if k = 0 then 1 else 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gauss n k + X ^ (k + 1) * gauss n (k + 1)

/-- All coefficients of the polynomial are nonnegative. -/
def CoeffNonneg (p : ℝ[X]) : Prop := ∀ k, 0 ≤ p.coeff k

/-- The coefficient of `x^i y^j` in
`∑_n a_n(q) ∑_{k,m} [n+k, n]_q [n+m, n]_q x^(n+k) y^(n+m)`. -/
noncomputable def T (a : ℕ → ℝ[X]) (i j : ℕ) : ℝ[X] :=
  ∑ s ∈ Finset.range (min i j + 1), a s * gauss i s * gauss j s

/-- The `q`-analogue of the positivity criterion fails: it is not true that for every sequence
of real polynomials `a_n(q)`, all `a_n` have nonnegative coefficients if and only if all
coefficients of the bivariate series do. -/
theorem main :
    ¬ ∀ a : ℕ → ℝ[X], (∀ n, CoeffNonneg (a n)) ↔ (∀ i j, CoeffNonneg (T a i j)) := by
  sorry

end OMA.S_mo_51186
