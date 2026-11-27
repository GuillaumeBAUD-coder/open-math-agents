import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2
import Mathlib.Tactic

/-!
# Step Proof for Erdos Problem 470 (`Erdos470.erdos_470.parts.ii.R2.H1`)
-/

namespace Erdos470R2Step

open Finset

lemma sum_divisors_two_pow (k : ℕ) : ∑ d ∈ (2 ^ k).divisors, d + 1 = 2 ^ (k + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (k + 1)]
    omega

lemma coprime_two_pow_of_prime {k r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : Nat.Coprime (2 ^ k) r :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))

lemma sum_divisors_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∑ d ∈ (2 ^ k * r).divisors, d + (r + 1) = 2 ^ (k + 1) * (r + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (coprime_two_pow_of_prime hr hr2), Nat.Prime.sum_divisors hr]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

lemma sum_divisors_two_pow_mul_mul (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d + (p + 1) * (q + 1) = 2 ^ (k + 1) * ((p + 1) * (q + 1)) := by
  have hcop1 : Nat.Coprime (2 ^ k) (p * q) :=
    Nat.Coprime.mul_right (coprime_two_pow_of_prime hp hp2) (coprime_two_pow_of_prime hq hq2)
  have hcop2 : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [mul_assoc, Nat.Coprime.sum_divisors_mul hcop1, Nat.Coprime.sum_divisors_mul hcop2,
    Nat.Prime.sum_divisors hp, Nat.Prime.sum_divisors hq]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

lemma not_abundant_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hbig : 2 ^ (k + 1) ≤ r + 1) : ¬ (2 ^ k * r).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_prime k r hr hr2
  have h2 : 2 * (2 ^ k * r) = 2 ^ (k + 1) * r := by ring
  rw [h2]
  nlinarith

lemma not_abundant_two_pow_mul_mul (j p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (hpbig : 2 ^ (j + 2) ≤ p) (hqbig : 2 ^ (j + 2) ≤ q) :
    ¬ (2 ^ j * p * q).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_mul j p q hp hq hp2 hq2 hpq
  set m := 2 ^ (j + 1) with hm
  have h2 : 2 * (2 ^ j * p * q) = m * (p * q) := by rw [hm]; ring
  have h4 : 2 ^ (j + 2) = 2 * m := by rw [hm]; ring
  rw [h2]
  obtain ⟨u, rfl⟩ : ∃ u, p = 2 * m + u := ⟨p - 2 * m, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, q = 2 * m + v := ⟨q - 2 * m, by omega⟩
  nlinarith [Nat.zero_le (u * v), Nat.zero_le (m * u), Nat.zero_le (m * v), Nat.zero_le m]

lemma dvd_cases (k p q d : ℕ) (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime)
    (hd : d ∈ (2 ^ k * p * q).properDivisors) :
    d ∣ 2 ^ (k - 1) * p * q ∨ d ∣ 2 ^ k * q ∨ d ∣ 2 ^ k * p := by
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨⟨e, he⟩, hlt⟩ := hd
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at he
    omega
  have hen : e ∣ 2 ^ k * p * q := ⟨d, by rw [he]; ring⟩
  have hr := Nat.minFac_prime he1
  have hrn : e.minFac ∣ 2 ^ k * p * q := (Nat.minFac_dvd e).trans hen
  have hre := Nat.minFac_dvd e
  generalize e.minFac = r at hr hrn hre
  obtain ⟨e', rfl⟩ := hre
  rcases (Nat.Prime.dvd_mul hr).mp hrn with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      left
      refine ⟨e', ?_⟩
      have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2, hk'] at he
      have : 2 * (2 ^ (k - 1) * p * q) = 2 * (d * e') := by
        rw [← mul_assoc, ← mul_assoc, he]
        ring
      omega
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      right; left
      refine ⟨e', ?_⟩
      rw [h2] at he
      have : p * (2 ^ k * q) = p * (d * e') := by linarith [he]
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
  · have h2 := (Nat.prime_dvd_prime_iff_eq hr hq).mp h
    right; right
    refine ⟨e', ?_⟩
    rw [h2] at he
    have : q * (2 ^ k * p) = q * (d * e') := by linarith [he]
    exact Nat.eq_of_mul_eq_mul_left hq.pos this

lemma decomp_lt_q (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (t : Finset ℕ)
    (ht : t ⊆ (2 ^ k * p * q).divisors) (hsmall : ∑ d ∈ t, d < q) :
    ∃ A0 B : ℕ, ∑ d ∈ t, d = A0 + p * B ∧ A0 + 1 ≤ 2 ^ (k + 1) := by
  have hnq : ∀ d ∈ t, ¬ q ∣ d := by
    intro d hdt hqd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (ht hdt)
    have h1 : q ≤ d := Nat.le_of_dvd hd0 hqd
    have h2 : d ≤ ∑ x ∈ t, x :=
      Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hdt
    omega
  have e1 : ∑ d ∈ t.filter (fun d => p ∣ d), d = p * ∑ d ∈ t.filter (fun d => p ∣ d), d / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have hsub : t.filter (fun d => ¬ p ∣ d) ⊆ (2 ^ k).divisors := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdt, hnp⟩ := hd
    have hdn := Nat.dvd_of_mem_divisors (ht hdt)
    have hcp : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
    have hcq : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr (hnq d hdt)).symm
    have h1 : d ∣ 2 ^ k * p := Nat.Coprime.dvd_of_dvd_mul_right hcq hdn
    have h2 : d ∣ 2 ^ k := Nat.Coprime.dvd_of_dvd_mul_right hcp h1
    exact Nat.mem_divisors.mpr ⟨h2, by positivity⟩
  refine ⟨∑ d ∈ t.filter (fun d => ¬ p ∣ d), d,
    ∑ d ∈ t.filter (fun d => p ∣ d), d / p, ?_, ?_⟩
  · rw [← Finset.sum_filter_add_sum_filter_not t (fun d => p ∣ d), e1]
    ring
  · calc ∑ d ∈ t.filter (fun d => ¬ p ∣ d), d + 1
        ≤ ∑ d ∈ (2 ^ k).divisors, d + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) 1
      _ = 2 ^ (k + 1) := sum_divisors_two_pow k

end Erdos470R2Step

theorem prove_Erdos470_R2_H1 :
    ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →
      2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →
      (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) < 2 ^ (k + 1) * p * q + q →
      2 ^ (k + 1) ≤ ((2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q) % p →
      Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  intro k p q hp hq hNp hNq hpq hpos hlt hmod
  have hN2 : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · norm_num at hNp hNq hpos
      nlinarith
    · exact hk0
  have hσ := Erdos470R2Step.sum_divisors_two_pow_mul_mul k p q hp hq hp2 hq2 hpq
  have hσ_eq : ∑ d ∈ (2 ^ k * p * q).divisors, d = (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) := by
    have h1 : (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) + (p + 1) * (q + 1) =
        ((2 ^ (k + 1) - 1) + 1) * ((p + 1) * (q + 1)) := by ring
    have h2 : (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1) := by omega
    rw [h2] at h1
    omega
  have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Nat.abundant_iff_sum_divisors, h2n, hσ_eq]
    exact hpos
  · rintro ⟨-, s, hs, hsum⟩
    have hsd := Finset.sum_sdiff hs (f := fun x => x)
    have hpd := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ k * p * q)
    set t := (2 ^ k * p * q).properDivisors \ s
    have ht_sum : ∑ x ∈ t, x = (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q := by
      omega
    have hsmall : ∑ x ∈ t, x < q := by omega
    have htsub : t ⊆ (2 ^ k * p * q).divisors :=
      Finset.sdiff_subset.trans Nat.properDivisors_subset_divisors
    obtain ⟨A0, B, hAB, hA0⟩ := Erdos470R2Step.decomp_lt_q k p q hp hq t htsub hsmall
    have hmod_eq : (∑ x ∈ t, x) % p = A0 := by
      rw [hAB, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [ht_sum] at hmod_eq
    omega
  · intro d hd hw
    have hab := hw.1
    rcases Erdos470R2Step.dvd_cases k p q d hk hp hq hd with h | h | h
    · have hk' : k - 1 + 2 = k + 1 := by omega
      have hnot := Erdos470R2Step.not_abundant_two_pow_mul_mul (k - 1) p q hp hq hp2 hq2 hpq
        (by rw [hk']; omega) (by rw [hk']; omega)
      exact hnot (Nat.Abundant.of_dvd hab h
        (Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) hp.ne_zero) hq.ne_zero))
    · have hnot := Erdos470R2Step.not_abundant_two_pow_mul_prime k q hq hq2 (by omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hq.ne_zero))
    · have hnot := Erdos470R2Step.not_abundant_two_pow_mul_prime k p hp hp2 (by omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hp.ne_zero))

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 :=
  prove_Erdos470_R2_H1
