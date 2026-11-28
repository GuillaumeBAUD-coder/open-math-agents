import FormalConjectures.Wikipedia.CarmichaelTotient

-- Reduction CarmichaelTotient.charmichaelTotient.R1 of Carmichael's totient function conjecture
-- Credit: @marcusbuffett

/-!
# Carmichael's totient conjecture: the classical divisibility conditions, and the open rest

The conjecture says that every `n > 0` shares its totient with some `m ≠ n`. Carmichael (Note on
Euler's φ-function, Bull. Amer. Math. Soc. 28 (1922)) showed that a counterexample must be
divisible by `2^2 * 3^2 * 7^2 * 43^2`, by exchanging prime factors with the same totient. The
three provable hypotheses are the steps of that argument, and the fourth is what remains.

* `H1`: if `36 ∤ n` there is a partner. (Odd `n`: `2n`. `n = 2k` with `k` odd: `k`.
  `4 ∣ n`, `3 ∤ n`: `3n/2`. `4 ∣ n`, `3 ∣ n`, `9 ∤ n`: `2n/3`.)
* `H2`: if `36 ∣ n` and `49 ∤ n` there is a partner. (`7 ∤ n`: `7n/6`. `7 ∣ n`: `6n/7`.)
* `H3`: if `36 ∣ n`, `49 ∣ n` and `43^2 ∤ n` there is a partner. (`43 ∤ n`: `43n/42`.
  `43 ∣ n`: `42n/43`.)
* `H4`: the case `2^2 * 3^2 * 7^2 * 43^2 ∣ n`, which is the open conjecture. (Ford 1998 has no
  counterexample below `10^(10^10)`; that is far beyond these three steps.)
-/

namespace OMA.R_CarmichaelTotient_charmichaelTotient_R1

open CarmichaelTotient

/-- A number not divisible by `36` has a totient partner. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → ¬ 36 ∣ n → CarmichaelTotientFor n

/-- A multiple of `36` not divisible by `49` has a totient partner. -/
def H2 : Prop :=
  ∀ n : ℕ, 36 ∣ n → ¬ 49 ∣ n → CarmichaelTotientFor n

/-- A multiple of `36` and `49` not divisible by `43^2` has a totient partner. -/
def H3 : Prop :=
  ∀ n : ℕ, 36 ∣ n → 49 ∣ n → ¬ 1849 ∣ n → CarmichaelTotientFor n

/-- The open part: multiples of `2^2 * 3^2 * 7^2 * 43^2`. -/
def H4 : Prop :=
  ∀ n : ℕ, 0 < n → 36 ∣ n → 49 ∣ n → 1849 ∣ n → CarmichaelTotientFor n

theorem main : H1 → H2 → H3 → H4 → type_of% @CarmichaelTotient.charmichaelTotient := by
  intro h1 h2 h3 h4 n hn
  by_cases c36 : 36 ∣ n
  · by_cases c49 : 49 ∣ n
    · by_cases c43 : 1849 ∣ n
      · exact h4 n hn c36 c49 c43
      · exact h3 n c36 c49 c43
    · exact h2 n c36 c49
  · exact h1 n hn c36

end OMA.R_CarmichaelTotient_charmichaelTotient_R1
