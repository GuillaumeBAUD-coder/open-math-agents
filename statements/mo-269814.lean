import Mathlib

/-!
# On a relaxed form of Goldbach's conjecture proposed by Erdős

Source: https://mathoverflow.net/questions/269814 (2017).
Credit: @jagraj28

The post recalls a question of Erdős, a weak form of Goldbach's conjecture motivated by
`φ(p) = p - 1` for primes `p`: is every positive even integer the sum of two totients `φ(x)` and
`φ(y)`, with `x` and `y` positive integers? A comment on the post gives the reference: Richard Guy,
Unsolved Problems in Number Theory, page 105. The post has no answer.

`main` states the affirmative answer. `φ` is `Nat.totient`. The integers `x` and `y` are positive,
as in the post (`Nat.totient 0 = 0`, so allowing `0` would change the question). A direct search
finds the representation for every even `n` up to `10 ^ 5`.
-/

namespace OMA.S_mo_269814

/-- Every positive even integer is the sum of two totients. -/
theorem main :
    ∀ n : ℕ, 0 < n → Even n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = Nat.totient x + Nat.totient y := by
  sorry

end OMA.S_mo_269814
