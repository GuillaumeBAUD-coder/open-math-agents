import OMAStatements.S_oeis_a277273
import Mathlib

/-
A277273: if p, p + 2, 3p + 2 and 3p + 8 are prime then k = (p + 2)(3p + 2) satisfies
sigma(k) = sigma(k - d(k)).

k is a product of two distinct primes, so d(k) = 4 and sigma(k) = (p + 3)(3p + 3). Also
k - 4 = p (3p + 8), a product of two distinct primes, with sigma = (p + 1)(3p + 9). The two
values agree. The eight listed terms come from p = 3, 5, 17, 197, 1427, 1667, 2087, 4157.
-/

namespace OMA.P277273

open ArithmeticFunction

lemma sig_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigma 1 (p * q) = (p + 1) * (q + 1) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, sigma_one_apply, sigma_one_apply,
    hp.sum_divisors, hq.sum_divisors]

lemma card_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p * q).divisors.card = 4 := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  rw [hc.card_divisors_mul, hp.divisors, hq.divisors, Finset.card_pair hp.one_lt.ne,
    Finset.card_pair hq.one_lt.ne]

lemma part1 (p : ℕ) (h1 : p.Prime) (h2 : (p + 2).Prime) (h3 : (3 * p + 2).Prime)
    (h4 : (3 * p + 8).Prime) :
    0 < (p + 2) * (3 * p + 2) ∧ sigma 1 ((p + 2) * (3 * p + 2)) =
      sigma 1 ((p + 2) * (3 * p + 2) - ((p + 2) * (3 * p + 2)).divisors.card) := by
  have hp := h1.pos
  refine ⟨by positivity, ?_⟩
  rw [card_pq h2 h3 (by omega), sig_pq h2 h3 (by omega)]
  have e : (p + 2) * (3 * p + 2) - 4 = p * (3 * p + 8) := by
    have : (p + 2) * (3 * p + 2) = p * (3 * p + 8) + 4 := by ring
    omega
  rw [e, sig_pq h1 h4 (by omega)]
  ring

lemma part2 (k p : ℕ) (hk : k = (p + 2) * (3 * p + 2)) (h1 : p.Prime) (h2 : (p + 2).Prime)
    (h3 : (3 * p + 2).Prime) (h4 : (3 * p + 8).Prime) :
    (0 < k ∧ sigma 1 k = sigma 1 (k - k.divisors.card)) ∧ ∃ p : ℕ,
      (p.Prime ∧ (p + 2).Prime ∧ (3 * p + 2).Prime ∧ (3 * p + 8).Prime) ∧
        k = (p + 2) * (3 * p + 2) := by
  subst hk
  exact ⟨part1 p h1 h2 h3 h4, p, ⟨h1, h2, h3, h4⟩, rfl⟩

lemma main' :
    (∀ p : ℕ, (p.Prime ∧ (p + 2).Prime ∧ (3 * p + 2).Prime ∧ (3 * p + 8).Prime) →
      (0 < (p + 2) * (3 * p + 2) ∧ sigma 1 ((p + 2) * (3 * p + 2)) =
        sigma 1 ((p + 2) * (3 * p + 2) - ((p + 2) * (3 * p + 2)).divisors.card))) ∧
    (∀ k ∈ [55, 119, 1007, 118007, 6120407, 8350007, 13083407, 51875207],
      (0 < k ∧ sigma 1 k = sigma 1 (k - k.divisors.card)) ∧ ∃ p : ℕ,
        (p.Prime ∧ (p + 2).Prime ∧ (3 * p + 2).Prime ∧ (3 * p + 8).Prime) ∧
          k = (p + 2) * (3 * p + 2)) := by
  refine ⟨fun p ⟨h1, h2, h3, h4⟩ => part1 p h1 h2 h3 h4, ?_⟩
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part2 55 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact part2 119 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact part2 1007 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact part2 118007 197 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact part2 6120407 1427 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact part2 8350007 1667 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact part2 13083407 2087 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact part2 51875207 4157 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

end OMA.P277273

theorem OMA.solution : type_of% @OMA.S_oeis_a277273.main := OMA.P277273.main'
