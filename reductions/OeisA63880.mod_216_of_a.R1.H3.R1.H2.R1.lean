import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H3.R1.H2.R1 of step OeisA63880.mod_216_of_a.R1.H3.R1.H2
-- Credit: @arindale
--
-- The step says that the exponent of `3` in an odd `10/7` ratio instance cannot be `1`.
-- If the exponent is `1`, then `m = 3 * (m/3)` with `m/3` coprime to `3`, and the equation
-- `7 sigma(m) = 10 usigma(m)` passes to `m/3`: both `sigma` and `usigma` are multiplicative
-- and `sigma(3) = usigma(3) = 4`, so dividing by `4` yields the same equation for `m/3`.
-- The residual difficulty is the exponent-`0` case (no odd `m` coprime to `3` at all),
-- which is isolated as `H1`.  `H2` is the purely structural bridge.

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

/-- The exponent-`0` case: no odd `10/7` ratio instance is coprime to `3`. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m → m.factorization 3 ≠ 0

/-- The structural bridge: exponent `1` descends to exponent `0` for `m/3`. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m → m.factorization 3 = 1 →
    Odd (m / 3) ∧ (m / 3).factorization 3 = 0 ∧
      7 * σ 1 (m / 3) = 10 * usigma (m / 3)

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1.H2 := by
  intro h1 h2 m hm heq hfac
  obtain ⟨hodd, hfac0, heq'⟩ := h2 m hm heq hfac
  exact h1 (m / 3) hodd heq' hfac0

end OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1
