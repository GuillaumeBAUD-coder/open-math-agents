import OMAReductions.R_OeisA63880_mod_216_of_a_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H3.R1 of step OeisA63880.mod_216_of_a.R1.H3
-- Credit: @arindale
--
-- H3 is the `n = 4 * m` branch of the reduction: for odd `m` with
-- `7 * sigma(m) = 10 * usigma(m)`, the odd part must be divisible by `27`.
--
-- The exponent of `3` in `m` splits the statement.  If `3^4 | m` the equation is already
-- impossible: writing `m = 81 * t` with `3` coprime to `t`, multiplicativity gives
-- `sigma(m) = 121 * sigma(t)` and `usigma(m) = 82 * usigma(t)`, and `7 * 121 > 10 * 82`
-- together with `sigma(t) >= usigma(t)` contradicts `7 sigma(m) = 10 usigma(m)`.
-- So the hard content is only the opposite direction: given that `3^4` does not divide `m`,
-- force `27 | m` (equivalently, exponents `0, 1, 2` of `3` are impossible).

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

/-- The hard core: if `3^4` does not divide `m`, then `27` must divide `m`. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m → ¬ (3 ^ 4 ∣ m) → 27 ∣ m

/-- The easy bound: `3^4` cannot divide `m` at all. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m → ¬ (3 ^ 4 ∣ m)

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1.H3 := by
  intro h1 h2 m hm heq
  exact h1 m hm heq (h2 m hm heq)

end OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1
