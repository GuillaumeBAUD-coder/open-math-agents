import OMAStatements.S_oeis_a225004
import Mathlib

/-!
# OEIS A225004: the largest multiple of `n` with fewer than `2·d(n)` divisors divides `n²`

Write `d` for the number-of-divisors function. We prove more than the conjecture asks:
*every* multiple `m` of `n` with `d(m) < 2·d(n)` divides `n²`, not only the largest one.

The idea, one prime at a time. Fix a prime `p`, and write `e`, `f` for the exponents of `p`
in `n`, `m`. Split off the `p`-parts: `n = p^e · n'` and `m = p^f · m'`. Since `n ∣ m`, the
`p`-free part `n'` divides `m'`, so `d(n') ≤ d(m')`. If `f ≥ 2e + 1` then

  `d(m) = (f + 1) · d(m') ≥ (2e + 2) · d(n') = 2 · d(n)`,

which is excluded. Hence `f ≤ 2e` for every prime, which says exactly that `m ∣ n²`.
-/

open Nat

namespace OMA.A225004

/-- The number of divisors is monotone along divisibility. -/
lemma card_divisors_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    a.divisors.card ≤ b.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hb h)

/-- Splitting off the `p`-part: `d(a) = (v_p(a) + 1) · d(a / p^{v_p(a)})`. -/
lemma card_divisors_split {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    a.divisors.card = (a.factorization p + 1) * (a / p ^ a.factorization p).divisors.card := by
  have hcop : Nat.Coprime (p ^ a.factorization p) (a / p ^ a.factorization p) :=
    (Nat.coprime_ordCompl hp ha).pow_left _
  have hmul : p ^ a.factorization p * (a / p ^ a.factorization p) = a :=
    Nat.ordProj_mul_ordCompl_eq_self a p
  calc a.divisors.card
      = (p ^ a.factorization p * (a / p ^ a.factorization p)).divisors.card := by rw [hmul]
    _ = (p ^ a.factorization p).divisors.card * (a / p ^ a.factorization p).divisors.card :=
        hcop.card_divisors_mul
    _ = (a.factorization p + 1) * (a / p ^ a.factorization p).divisors.card := by
        rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- The key bound: a multiple `m` of `n` with fewer than `2·d(n)` divisors has every prime
exponent at most twice the corresponding exponent of `n`. -/
lemma factorization_le_two_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ∣ m)
    (hd : m.divisors.card < 2 * n.divisors.card) (p : ℕ) (hp : p.Prime) :
    m.factorization p ≤ 2 * n.factorization p := by
  by_contra hlt
  push_neg at hlt
  -- the `p`-free part of `n` divides the `p`-free part of `m`
  have hdvd : n / p ^ n.factorization p ∣ m / p ^ m.factorization p :=
    Nat.ordCompl_dvd_ordCompl_of_dvd hnm p
  have hm' : m / p ^ m.factorization p ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hle := card_divisors_le_of_dvd hm' hdvd
  rw [card_divisors_split hp hn, card_divisors_split hp hm] at hd
  -- `(f + 1) · d(m') ≥ (2e + 2) · d(n')` contradicts `hd`
  have : 2 * ((n.factorization p + 1) * (n / p ^ n.factorization p).divisors.card)
      ≤ (m.factorization p + 1) * (m / p ^ m.factorization p).divisors.card := by
    calc 2 * ((n.factorization p + 1) * (n / p ^ n.factorization p).divisors.card)
        = (2 * n.factorization p + 2) * (n / p ^ n.factorization p).divisors.card := by ring
      _ ≤ (m.factorization p + 1) * (m / p ^ m.factorization p).divisors.card :=
          Nat.mul_le_mul (by omega) hle
  omega

/-- Every multiple of `n` with fewer than twice as many divisors as `n` divides `n²`. -/
theorem dvd_sq_of_few_divisors {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ∣ m)
    (hd : m.divisors.card < 2 * n.divisors.card) : m ∣ n ^ 2 := by
  rw [← Nat.factorization_le_iff_dvd hm (pow_ne_zero 2 hn), Nat.factorization_pow]
  intro p
  by_cases hp : p.Prime
  · simpa using factorization_le_two_mul hn hm hnm hd p hp
  · simp [Nat.factorization_eq_zero_of_not_prime m hp]

end OMA.A225004

theorem OMA.solution : type_of% @OMA.S_oeis_a225004.main := by
  intro n hn m hm
  obtain ⟨hnm, hmpos, hd⟩ := hm.1
  exact OMA.A225004.dvd_sq_of_few_divisors (by omega) hmpos.ne' hnm hd
