import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OMA.S_oeis_a268293

/-- The sequence `A266489`: unique integer sequence with `a(0) = 1`, `a(1) = 1`, whose generating
function `A(x) = ∑ a(k) x^k` satisfies `[x^n] A(x / A(x)^n) = 0` for all `n ≥ 2`.
Equivalently, `a(n) = - ∑_{k=1}^{n-1} a(k) * [x^{n-k}] A(x)^{-n*k}` for `n ≥ 2`, where only
coefficients of `A` of degree `< n` enter the `n`-th step. -/
noncomputable def A266489 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    let Atrunc : PowerSeries ℤ :=
      PowerSeries.mk fun j => if _ : j < n + 2 then A266489 j else 0
    let B : PowerSeries ℤ := Ring.inverse Atrunc
    (-(∑ k : Fin (n + 1),
        A266489 (k.1 + 1) * PowerSeries.coeff (n + 1 - k.1) (B ^ ((n + 2) * (k.1 + 1)))))

/-- Conjecture (OEIS A268293): `a(n) = A266489(n) / n` is an integer for every `n ≥ 1`,
i.e., `n ∣ A266489(n)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ A266489 n := by
  sorry

end OMA.S_oeis_a268293
