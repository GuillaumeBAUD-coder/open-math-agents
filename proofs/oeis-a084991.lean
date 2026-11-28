import OMAStatements.S_oeis_a084991
import Mathlib

/-
A084991: palindromes that are sums of two primes.

For odd k, a sum of two primes equal to k has one even summand, which is 2, so the other one is
k - 2; conversely k = 2 + (k - 2). For even k > 2 the claim is the Goldbach hypothesis itself.
The palindrome condition is carried along unchanged.
-/

namespace OMA.P084991

lemma main' (IsPal : ℕ → Prop) :
    (∀ k : ℕ, IsPal k → Odd k →
      ((IsPal k ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = k) ↔ (k - 2).Prime)) ∧
    ((∀ n : ℕ, Even n → 2 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) →
      ∀ k : ℕ, IsPal k → Even k → 2 < k →
        (IsPal k ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = k)) := by
  refine ⟨fun k hk ho => ⟨?_, fun h => ⟨hk, 2, k - 2, Nat.prime_two, h, ?_⟩⟩,
    fun G k hk he h2 => ⟨hk, G k he h2⟩⟩
  · rintro ⟨-, p, q, hp, hq, rfl⟩
    rcases hp.eq_two_or_odd' with rfl | hp'
    · simpa using hq
    · rcases hq.eq_two_or_odd' with rfl | hq'
      · simpa using hp
      · exact absurd (hp'.add_odd hq') (Nat.not_even_iff_odd.2 ho)
  · have := h.two_le
    omega

end OMA.P084991

theorem OMA.solution : type_of% @OMA.S_oeis_a084991.main :=
  OMA.P084991.main' OMA.S_oeis_a084991.IsPal
