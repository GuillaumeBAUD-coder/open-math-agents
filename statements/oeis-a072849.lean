import Mathlib

/-!
# A072849: Prime(a(n)) + ... + prime(a(n)+3) is a square.

Source: https://oeis.org/A072849
Comment (Jianing Song, Nov 13 2022): this sequence and A064397 (numbers k such that
prime(k) + prime(k+1) is a square) are disjoint; i.e. prime(n) + prime(n+1) and
prime(n) + prime(n+1) + prime(n+2) + prime(n+3) cannot be squares at the same time.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We state the conjecture exactly as in the OEIS comment: there are no four consecutive
primes p < q < r < s such that both p + q and p + q + r + s are perfect squares.
The body stays `sorry`; a person reviews the translation before merging.
-/

namespace OMA.S_oeis_a072849

/-- `BetweenPrimes a b` says that no prime lies strictly between the primes `a` and `b`. -/
def BetweenPrimes (a b : ℕ) : Prop := ∀ t : ℕ, a < t → t < b → ¬ t.Prime

/-- Four primes `p < q < r < s` are consecutive. -/
def ConsecutivePrimes (p q r s : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ p < q ∧ q < r ∧ r < s ∧
    BetweenPrimes p q ∧ BetweenPrimes q r ∧ BetweenPrimes r s

theorem main :
    ¬ ∃ p q r s : ℕ,
      ConsecutivePrimes p q r s ∧
      (∃ a : ℕ, p + q = a ^ 2) ∧
      (∃ b : ℕ, p + q + r + s = b ^ 2) := by
  sorry

end OMA.S_oeis_a072849
