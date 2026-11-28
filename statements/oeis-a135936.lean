import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace OMA.S_oeis_a135936

/-- Boubaker polynomials `B_n(x)` over `ℤ`:
`B_0(x) = 1`, `B_1(x) = x`, `B_2(x) = x^2 + 2`, `B_{n+3}(x) = x * B_{n+2}(x) - B_{n+1}(x)`. -/
noncomputable def boubaker : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => Polynomial.X
  | 2 => Polynomial.X ^ 2 + 2
  | n + 3 => Polynomial.X * boubaker (n + 2) - boubaker (n + 1)

/-- OEIS A135936: coefficient of `x^(n - 2m)` in the Boubaker polynomial `B_n(x)`. -/
noncomputable def a135936 (n m : ℕ) : ℤ :=
  (boubaker n).coeff (n - 2 * m)

/-- OEIS A115139: `T(n, m) = (-1)^m * C(n - 1 - m, m)` for `n ≥ 1`. -/
def a115139 (n m : ℕ) : ℤ :=
  (-1 : ℤ) ^ m * (Nat.choose (n - 1 - m) m : ℤ)

/-- OEIS A132460: `T(n, m) = (-1)^m * (C(n - m, m) + C(n - m - 1, m - 1))`
(with the second binomial term `0` for `m = 0`). -/
def a132460 (n m : ℕ) : ℤ :=
  (-1 : ℤ) ^ m *
    ((Nat.choose (n - m) m : ℤ) + if m = 0 then 0 else (Nat.choose (n - m - 1) (m - 1) : ℤ))

/-- OEIS A135936 conjectures (Thomas Baruchel, Jun 03 2018):
For all `n : ℕ` and `m ≤ n / 2`,
1. `T(n, m) = (-1)^m * (C(n - m, m) - 3 * C(n - m - 1, m - 1))` (with `C(·, -1) = 0`), and
2. `T(n, m) = 4 * A115139(n + 1, m) - 3 * A132460(n, m)`. -/
theorem main :
    ∀ n m : ℕ, 2 * m ≤ n →
      a135936 n m = (-1 : ℤ) ^ m *
        ((Nat.choose (n - m) m : ℤ) - if m = 0 then 0 else 3 * (Nat.choose (n - m - 1) (m - 1) : ℤ)) ∧
      a135936 n m = 4 * a115139 (n + 1) m - 3 * a132460 n m := by
  sorry

end OMA.S_oeis_a135936
