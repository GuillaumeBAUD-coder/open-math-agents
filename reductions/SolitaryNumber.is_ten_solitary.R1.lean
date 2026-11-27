import FormalConjectures.Wikipedia.SolitaryNumber

-- Reduction SolitaryNumber.is_ten_solitary.R1 of the question whether 10 is a solitary number
-- Credit: @marcusbuffett

/-!
# Is 10 solitary? Even friends, the square condition, and the open rest

A friend of `10` is an `m > 0` with `σ(m) / m = σ(10) / 10 = 9 / 5`, that is `10 σ(m) = 18 m`.
Two classical observations narrow the possible friends, and the rest is open.

* `H1`: the only even friend is `10` itself. (`5 ∣ m`, so `m = 10k`, and for `k > 1` the
  abundancy of a proper multiple is strictly larger: `σ(10k) > k σ(10)`.)
* `H2`: an odd friend is a perfect square. (`5 σ(m) = 9 m` makes `σ(m)` odd, and for odd `m`
  the divisor sum is odd only when every exponent in the factorization is even.)
* `H3`: no odd square is a friend of `10`. This is the open problem and stays open (the
  literature also shows that such an `m` has at least six distinct prime factors).
-/

namespace OMA.R_SolitaryNumber_is_ten_solitary_R1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The only even friend of `10` is `10`. -/
def H1 : Prop :=
  ∀ m : ℕ, 0 < m → Even m → σ 1 m * 10 = 18 * m → m = 10

/-- An odd friend of `10` is a perfect square. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → σ 1 m * 10 = 18 * m → IsSquare m

/-- The open part: no odd square is a friend of `10`. -/
def H3 : Prop :=
  ∀ m : ℕ, Odd m → IsSquare m → σ 1 m * 10 ≠ 18 * m

theorem main : H1 → H2 → H3 → type_of% @SolitaryNumber.is_ten_solitary := by
  intro h1 h2 h3
  refine ⟨by norm_num, ?_⟩
  rintro m ⟨hm, -, h⟩
  have h18 : σ 1 10 = 18 := by decide
  rw [h18] at h
  rcases Nat.even_or_odd m with he | ho
  · exact h1 m hm he h
  · exact absurd h (h3 m ho (h2 m ho h))

end OMA.R_SolitaryNumber_is_ten_solitary_R1
