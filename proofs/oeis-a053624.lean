import OMAStatements.S_oeis_a053624

-- Problem: A053624, highly composite odd numbers beyond 1, 3, 9 end in 5.
-- Credit: @ShoQo
-- Proof (Lynch): n is odd, so it suffices that 5 ∣ n. If not, either a prime q ≥ 7 divides n,
-- and replacing q^e by 5^e gives a smaller odd number with the same number of divisors, or
-- n = 3^k with k ≥ 3, and 5 * 3^(k-2) < 3^k is odd with 2(k-1) ≥ k+1 divisors.

open OMA.S_oeis_a053624

namespace OMA_A053624_Proof

lemma card_pow_mul {p e r : ℕ} (hp : p.Prime) (hr : ¬ p ∣ r) :
    (p ^ e * r).divisors.card = (e + 1) * r.divisors.card := by
  rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hr)),
    Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

lemma card_prime_pow {p e : ℕ} (hp : p.Prime) : (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

end OMA_A053624_Proof

open OMA_A053624_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a053624.main := by
  intro n ⟨hodd, hrec⟩ h1 h3 h9
  have hn0 : n ≠ 0 := by rintro rfl; simp at hodd
  have hn2 : n % 2 = 1 := Nat.odd_iff.1 hodd
  suffices h5 : 5 ∣ n by omega
  by_contra h5
  by_cases hq : ∃ q, q.Prime ∧ q ∣ n ∧ q ≠ 3
  · -- swap q^e for 5^e
    obtain ⟨q, hq, hqn, hq3⟩ := hq
    have hq2 : q ≠ 2 := by rintro rfl; omega
    have hq5 : q ≠ 5 := by rintro rfl; exact h5 hqn
    have hq7 : 5 < q := by
      have := hq.two_le
      rcases (by omega : q = 4 ∨ 5 < q ∨ q ≤ 3) with h | h | h
      · subst h; exact absurd hq (by norm_num)
      · exact h
      · interval_cases q <;> simp_all
    set e := n.factorization q
    set r := n / q ^ e
    have hnr : q ^ e * r = n := Nat.ordProj_mul_ordCompl_eq_self n q
    have hqr : ¬ q ∣ r := Nat.not_dvd_ordCompl hq hn0
    have hrn : r ∣ n := Nat.ordCompl_dvd n q
    have h5r : ¬ 5 ∣ r := fun h => h5 (h.trans hrn)
    have he : 1 ≤ e := (hq.dvd_iff_one_le_factorization hn0).1 hqn
    have hr0 : 0 < r := Nat.ordCompl_pos q hn0
    have hrodd : r % 2 = 1 := by
      obtain ⟨t, ht⟩ := hrn
      by_contra hc
      have : 2 ∣ r := by omega
      have : 2 ∣ n := this.trans ⟨t, ht⟩
      omega
    have hcard : (5 ^ e * r).divisors.card = n.divisors.card := by
      rw [card_pow_mul Nat.prime_five h5r, ← card_pow_mul hq hqr, hnr]
    have hlt : 5 ^ e * r < n := by
      rw [← hnr]; exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hq7 (by omega)) hr0
    have hmodd : Odd (5 ^ e * r) := Odd.mul (Odd.pow (by decide)) (Nat.odd_iff.2 hrodd)
    have := hrec _ hmodd hlt
    omega
  · -- n = 3^k with k ≥ 3
    push Not at hq
    obtain ⟨k, hpow⟩ : ∃ k, n = 3 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun hd hdn => hq _ hd hdn)⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := by
      refine ⟨k - 3, ?_⟩
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with h | h | h | h <;>
        first | omega | (rw [h] at hpow; norm_num at hpow; omega)
    have h3k : ¬ 5 ∣ 3 ^ (j + 1) := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_three).1
        (Nat.prime_five.dvd_of_dvd_pow h)
      omega
    have hcard : (5 ^ 1 * 3 ^ (j + 1)).divisors.card = 2 * (j + 2) := by
      rw [card_pow_mul Nat.prime_five h3k, card_prime_pow Nat.prime_three]
    have hlt : 5 ^ 1 * 3 ^ (j + 1) < n := by
      have : 0 < 3 ^ (j + 1) := by positivity
      rw [hpow, show (3 : ℕ) ^ (j + 3) = 9 * 3 ^ (j + 1) by ring, pow_one]; omega
    have hmodd : Odd (5 ^ 1 * 3 ^ (j + 1)) := Odd.mul (by decide) (Odd.pow (by decide))
    have := hrec _ hmodd hlt
    rw [hcard, hpow, card_prime_pow Nat.prime_three] at this
    omega
