import OMAStatements.S_oeis_a277201
import Mathlib

/-
A277201: the numbers k with d(2k) = 4 and d(2k - 1) = 5 are exactly the primes of the form
(p^4 + 1)/2 with p prime.

- split: writing n = p^e t with p not dividing t, d(n) = (e + 1) d(t).
- five: d(n) = 5 forces n = p^4 (take p the least prime factor: e + 1 divides 5, so e = 4 and
  d(t) = 1, that is t = 1).
- two_prime: d(t) = 2 forces t prime.
If d(2k) = 4 and 2k - 1 = p^4, write 2k = 2^e t with t odd: either e = 1 and t is prime, so
k = t is prime, or e = 3 and t = 1, so 2k - 1 = 7, which is not a fourth power. Conversely, for
a prime q = (p^4 + 1)/2 the prime p is odd, 2q - 1 = p^4 has 5 divisors and 2q has 4.
-/

namespace OMA.P277201

lemma card_pow (p e : ℕ) (hp : p.Prime) : (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp]
  simp

lemma card_one {t : ℕ} (ht : t ≠ 0) (h : t.divisors.card = 1) : t = 1 := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h
  have h1 : (1 : ℕ) ∈ t.divisors := Nat.one_mem_divisors.2 ht
  have h2 : t ∈ t.divisors := Nat.mem_divisors_self t ht
  rw [hx, Finset.mem_singleton] at h1 h2
  omega

lemma split (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    ∃ e t, ¬ p ∣ t ∧ t ≠ 0 ∧ n = p ^ e * t ∧ n.divisors.card = (e + 1) * t.divisors.card := by
  obtain ⟨e, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hn
  refine ⟨e, t, ht, ht0, rfl, ?_⟩
  have hc : Nat.Coprime (p ^ e) t :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 ht)
  rw [hc.card_divisors_mul, card_pow p e hp]

lemma five (n : ℕ) (h : n.divisors.card = 5) : ∃ p, p.Prime ∧ n = p ^ 4 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at h
  have hn1 : n ≠ 1 := by
    rintro rfl
    simp at h
  have hp := Nat.minFac_prime hn1
  have hpd := Nat.minFac_dvd n
  generalize n.minFac = p at hp hpd
  obtain ⟨e, t, ht, ht0, rfl, hc⟩ := split n p hn0 hp
  rw [hc] at h
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hpd
    exact ht hpd
  have h5 : e + 1 ∣ 5 := Dvd.intro _ h
  have he4 : e = 4 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 h5 with h1 | h1 <;> omega
  subst he4
  have hd1 : t.divisors.card = 1 := by omega
  rw [card_one ht0 hd1, mul_one]
  exact ⟨p, hp, rfl⟩

lemma two_prime {t : ℕ} (h : t.divisors.card = 2) : t.Prime := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at h
  rw [Nat.prime_def]
  refine ⟨by omega, fun m hm => ?_⟩
  have hsub : ({1, t} : Finset ℕ) ⊆ t.divisors := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Nat.one_mem_divisors.2 ht0
    · rw [Finset.mem_singleton.1 hx]
      exact Nat.mem_divisors_self t ht0
  have heq : ({1, t} : Finset ℕ) = t.divisors :=
    Finset.eq_of_subset_of_card_le hsub (by rw [h, Finset.card_pair (Ne.symm ht1)])
  have hm' : m ∈ t.divisors := Nat.mem_divisors.2 ⟨hm, ht0⟩
  rw [← heq] at hm'
  simpa using hm'

lemma main' :
    {k : ℕ | (2 * k).divisors.card = 4 ∧ (2 * k - 1).divisors.card = 5} =
      {q : ℕ | q.Prime ∧ ∃ p : ℕ, p.Prime ∧ q = (p ^ 4 + 1) / 2} := by
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h4, h5⟩
    obtain ⟨p, hp, hp4⟩ := five _ h5
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at h4
    have hp16 : 16 ≤ p ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ p ^ 4 := Nat.pow_le_pow_left hp.two_le 4
    obtain ⟨e, t, ht, ht0, hkt, hc⟩ := split (2 * k) 2 (by omega) Nat.prime_two
    rw [hc] at h4
    have he : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hkt
      exact ht ⟨k, hkt.symm⟩
    have hdv : e + 1 ∣ 4 := Dvd.intro _ h4
    have hle : e + 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hdv
    have he2 : e ≠ 2 := by
      rintro rfl
      exact absurd hdv (by decide)
    rcases (by omega : e = 1 ∨ e = 3) with rfl | rfl
    · have hd2 : t.divisors.card = 2 := by omega
      have htp := two_prime hd2
      have hkt' : k = t := by omega
      exact ⟨hkt' ▸ htp, p, hp, by omega⟩
    · have hd1 : t.divisors.card = 1 := by omega
      rw [card_one ht0 hd1] at hkt
      omega
  · rintro ⟨hq, p, hp, rfl⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      norm_num at hq
    have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have h4odd : p ^ 4 % 2 = 1 := by simp [Nat.pow_mod, hpodd]
    have hp16 : 16 ≤ p ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ p ^ 4 := Nat.pow_le_pow_left hp.two_le 4
    have h2q : 2 * ((p ^ 4 + 1) / 2) = p ^ 4 + 1 := by omega
    refine ⟨?_, ?_⟩
    · have hq2 : (p ^ 4 + 1) / 2 ≠ 2 := by omega
      have hc : Nat.Coprime 2 ((p ^ 4 + 1) / 2) :=
        (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
      rw [hc.card_divisors_mul, Nat.prime_two.divisors, hq.divisors,
        Finset.card_pair (by norm_num), Finset.card_pair hq.one_lt.ne]
    · rw [h2q, Nat.add_sub_cancel]
      exact card_pow p 4 hp

end OMA.P277201

theorem OMA.solution : type_of% @OMA.S_oeis_a277201.main := OMA.P277201.main'
