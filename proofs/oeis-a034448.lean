import OMAStatements.S_oeis_a034448
import Mathlib

namespace A034448Help
open OMA.S_oeis_a034448 ArithmeticFunction UniqueFactorizationMonoid

lemma unitarySum_eq (n : ℕ) :
    unitarySum n = ∑ d ∈ n.divisors, if d.Coprime (n / d) then d else 0 := by
  rw [unitarySum, Finset.sum_filter]

lemma coprime_iff {m n a b : ℕ} (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) :
    (a * b).Coprime (m * n / (a * b)) ↔ a.Coprime (m / a) ∧ b.Coprime (n / b) := by
  rw [Nat.div_mul_div_comm ha hb |>.symm]
  have h1 : a.Coprime (n / b) := hmn.coprime_dvd_left ha |>.coprime_dvd_right (Nat.div_dvd_of_dvd hb)
  have h2 : b.Coprime (m / a) := (hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha) |>.coprime_dvd_right hb).symm
  rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  tauto

lemma unitarySum_mul {m n : ℕ} (hmn : m.Coprime n) :
    unitarySum (m * n) = unitarySum m * unitarySum n := by
  rw [unitarySum_eq, unitarySum_eq, unitarySum_eq, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image (fun x hx y hy h =>
      hmn.mul_injOn_divisors hx hy h), Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  dsimp only
  have hc := coprime_iff hmn (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb)
  by_cases h1 : a.Coprime (m / a)
  · by_cases h2 : b.Coprime (n / b)
    · rw [if_pos (hc.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]
    · rw [if_neg (fun h => h2 (hc.1 h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (hc.1 h).1), if_neg h1, zero_mul]

lemma unitarySum_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    unitarySum (p ^ a) = 1 + p ^ a := by
  have hne : (1 : ℕ) ≠ p ^ a := (Nat.one_lt_pow ha.ne' hp.one_lt).ne
  have : ((p ^ a).divisors.filter fun d => d.Coprime (p ^ a / d)) = {1, p ^ a} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hc⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
      rw [Nat.pow_div hi hp.pos] at hc
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · left; simp
      rcases Nat.eq_zero_or_pos (a - i) with h0 | h0
      · right; congr 1; omega
      · exfalso
        rw [Nat.coprime_pow_left_iff hi0, Nat.coprime_pow_right_iff h0] at hc
        exact hp.one_lt.ne' ((Nat.coprime_self p).1 hc)
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, (pow_pos hp.pos _).ne'⟩, Nat.coprime_one_left _⟩
      · refine ⟨⟨dvd_rfl, (pow_pos hp.pos _).ne'⟩, ?_⟩
        rw [Nat.div_self (pow_pos hp.pos _)]
        exact Nat.coprime_one_right _
  rw [unitarySum, this, Finset.sum_pair hne]

lemma radical_prime_pow {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) : radical (p ^ a) = p := by
  rw [radical_pow_of_prime hp.prime ha]
  simp

lemma key (p a : ℕ) :
    (1 + p ^ a) * ∑ k ∈ Finset.range a, p ^ k = ∑ k ∈ Finset.range (2 * a), p ^ k := by
  rw [two_mul, Finset.sum_range_add, add_mul, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add]

lemma pow_div_self' {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : p ^ k / p = p ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos, Nat.add_sub_cancel]

lemma case_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    unitarySum (p ^ a) * sigma 1 (p ^ a / radical (p ^ a)) =
      sigma 1 ((p ^ a) ^ 2 / radical (p ^ a)) := by
  rw [radical_prime_pow hp ha.ne', unitarySum_prime_pow hp ha, ← pow_mul,
    pow_div_self' hp ha, pow_div_self' hp (by omega),
    sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp,
    show a - 1 + 1 = a by omega, show a * 2 - 1 + 1 = 2 * a by omega]
  exact key p a

lemma case_mul {m n : ℕ} (hmn : m.Coprime n)
    (Hm : unitarySum m * sigma 1 (m / radical m) = sigma 1 (m ^ 2 / radical m))
    (Hn : unitarySum n * sigma 1 (n / radical n) = sigma 1 (n ^ 2 / radical n)) :
    unitarySum (m * n) * sigma 1 (m * n / radical (m * n)) =
      sigma 1 ((m * n) ^ 2 / radical (m * n)) := by
  have hrel : IsRelPrime m n := Nat.coprime_iff_isRelPrime.1 hmn
  have hrm : radical m ∣ m := radical_dvd_self
  have hrn : radical n ∣ n := radical_dvd_self
  rw [radical_mul hrel, unitarySum_mul hmn, mul_pow,
    ← Nat.div_mul_div_comm hrm hrn,
    ← Nat.div_mul_div_comm (hrm.trans (Dvd.intro_left _ (sq m).symm))
      (hrn.trans (Dvd.intro_left _ (sq n).symm))]
  have c1 : (m / radical m).Coprime (n / radical n) :=
    (hmn.coprime_dvd_left (Nat.div_dvd_of_dvd hrm)).coprime_dvd_right (Nat.div_dvd_of_dvd hrn)
  have c2 : (m ^ 2 / radical m).Coprime (n ^ 2 / radical n) :=
    ((Nat.Coprime.pow 2 2 hmn).coprime_dvd_left (Nat.div_dvd_of_dvd
      (hrm.trans (Dvd.intro_left _ (sq m).symm)))).coprime_dvd_right
      (Nat.div_dvd_of_dvd (hrn.trans (Dvd.intro_left _ (sq n).symm)))
  rw [isMultiplicative_sigma.map_mul_of_coprime c1, isMultiplicative_sigma.map_mul_of_coprime c2,
    ← Hm, ← Hn]
  ring

end A034448Help

open A034448Help in
theorem OMA.solution : type_of% @OMA.S_oeis_a034448.main := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha => intro _; exact case_prime_pow hp ha
  | zero => intro h; omega
  | one => intro _; simp [OMA.S_oeis_a034448.unitarySum, UniqueFactorizationMonoid.radical_one,
      Finset.filter_singleton]
  | coprime a b ha hb hab iha ihb =>
    intro _
    exact case_mul hab (iha (by omega)) (ihb (by omega))
