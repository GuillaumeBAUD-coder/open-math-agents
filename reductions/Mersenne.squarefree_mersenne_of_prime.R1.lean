import FormalConjectures.Wikipedia.Mersenne

-- Reduction Mersenne.squarefree_mersenne_of_prime.R1 of Conjectures about Mersenne primes — squarefree mersenne of prime
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
# Squarefree Mersenne numbers: the Wieferich criterion + the multiplicative-order core

If `p² ∣ M_q = 2^q - 1` with `q` prime, then `p` is a Wieferich prime (lifting the
exponent: the order of `2` modulo `p` and modulo `p²` both equal `q`, and that order divides
`p - 1`). Moreover `p ∣ M_q` forces the multiplicative order of `2` modulo `p` to be exactly
`q`, a prime. So the conjecture reduces to a statement about Wieferich primes alone.

* `H1` (known, textbook; the forward direction of `sq_dvd_mersenne_iff_isWieferichPrime`):
  for primes `q, p`, `p² ∣ M_q` implies `p` is a Wieferich prime.
* `H2` (open core): no Wieferich prime `p` has prime multiplicative order of `2` modulo `p`.
  For the two known Wieferich primes the orders are `364` (for `1093`) and `1755` (for `3511`),
  both composite.

`main` proves that `p ∣ M_q` with `q` prime gives `orderOf (2 : ZMod p) = q`.
-/

namespace OMA.R_Mersenne_squarefree_mersenne_of_prime_R1

/-- A square prime factor of a prime-exponent Mersenne number is a Wieferich prime. -/
def H1 : Prop :=
  ∀ q p : ℕ, q.Prime → p.Prime → p ^ 2 ∣ mersenne q → IsWieferichPrime p

/-- Open core: the multiplicative order of `2` modulo a Wieferich prime is never prime. -/
def H2 : Prop :=
  ∀ p : ℕ, IsWieferichPrime p → ¬ (orderOf (2 : ZMod p)).Prime

/-- If a prime `p` divides `M_q` with `q` prime, then `2` has order `q` modulo `p`. -/
lemma orderOf_two_eq {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hdvd : p ∣ mersenne q) :
    orderOf (2 : ZMod p) = q := by
  haveI := Fact.mk hp
  have hpow : (2 : ZMod p) ^ q = 1 := by
    have h0 : ((mersenne q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    unfold mersenne at h0
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] at h0
    exact h0
  have hne : (2 : ZMod p) ≠ 1 := by
    intro h
    have h' : (1 : ZMod p) + 1 = 1 + 0 := by
      rw [add_zero]
      exact one_add_one_eq_two.trans h
    exact one_ne_zero (add_left_cancel h')
  rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem main : H1 → H2 → type_of% @Mersenne.squarefree_mersenne_of_prime := by
  intro h1 h2 q hq
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hsq : p ^ 2 ∣ mersenne q := by rwa [sq]
  have hdvd : p ∣ mersenne q := (dvd_mul_right p p).trans hpp
  apply h2 p (h1 q p hq hp hsq)
  rw [orderOf_two_eq hq hp hdvd]
  exact hq

end OMA.R_Mersenne_squarefree_mersenne_of_prime_R1
