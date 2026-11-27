import OMAStatements.S_oeis_a336838
import Mathlib

namespace OMA336838
open Finset

def S (Q k : ℕ) : ℕ := ∑ i ∈ range k, Q ^ i

lemma S_mul (Q a b : ℕ) : S Q (a * b) = S Q a * ∑ j ∈ range b, (Q ^ a) ^ j := by
  induction b with
  | zero => simp [S]
  | succ b ih =>
    rw [Nat.mul_succ, S, sum_range_add, ← S, ih, sum_range_succ, mul_add]
    congr 1
    rw [S, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    ring

lemma dvd_T (r Q a : ℕ) (hr : r ∣ Q - 1) (hQ : 1 ≤ Q) : r ∣ ∑ j ∈ range r, (Q ^ a) ^ j := by
  rw [← ZMod.natCast_eq_zero_iff] at hr ⊢
  have h1 : (Q : ZMod r) = 1 := by
    have : Q = (Q - 1) + 1 := by omega
    rw [this]; push_cast [Nat.cast_add, hr]; simp
  push_cast; simp [h1]

lemma key (r Q : ℕ) (hr : r ∣ Q - 1) (hQ : 1 ≤ Q) : ∀ n k, r ^ n ∣ k → r ^ n ∣ S Q k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro k hk
    obtain ⟨c, rfl⟩ := hk
    have : r ^ (n + 1) * c = (r ^ n * c) * r := by ring
    rw [this, S_mul, pow_succ]
    exact mul_dvd_mul (ih _ (dvd_mul_right _ _)) (dvd_T r Q _ hr hQ)

lemma sum_split (q k : ℕ) : ∑ i ∈ range (2 * k), q ^ i = (q + 1) * S (q ^ 2) k := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    simp only [S, sum_range_succ]
    ring

theorem sol : ∀ p q e : ℕ, p.Prime → q.Prime → p < q →
    (∀ r : ℕ, p < r → r < q → ¬ r.Prime) → Odd e →
    (q+1)/2 ∣ (OMA.S_oeis_a336838.divisorMean (q^e)).num.natAbs := by
  intro p q e hp hq hpq _ he
  obtain ⟨k0, rfl⟩ := he
  set k := k0 + 1 with hk
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  obtain ⟨m0, hm0⟩ := hq.eq_two_or_odd'.resolve_left hq2
  set m := m0 + 1 with hm
  have hqm : (q + 1) / 2 = m := by omega
  rw [hqm]
  have hsig : (∑ d ∈ (q ^ (2 * k0 + 1)).divisors, d) = 2 * m * S (q ^ 2) k := by
    rw [Nat.sum_divisors_prime_pow hq, show 2 * k0 + 1 + 1 = 2 * k by omega, sum_split]
    congr 1; omega
  have hcard : (q ^ (2 * k0 + 1)).divisors.card = 2 * k := by
    rw [Nat.divisors_prime_pow hq, card_map, card_range]; omega
  set x := OMA.S_oeis_a336838.divisorMean (q ^ (2 * k0 + 1)) with hxdef
  have hx : x * (2 * k : ℕ) = (2 * m * S (q ^ 2) k : ℕ) := by
    rw [hxdef, OMA.S_oeis_a336838.divisorMean, hsig, hcard]
    have : ((2 * k : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  have hnum : (x.num : ℚ) * (2 * k : ℕ) = (2 * m * S (q ^ 2) k : ℕ) * x.den := by
    rw [← Rat.mul_den_eq_num, ← hx]; ring
  have hnumZ : x.num * (2 * k : ℕ) = (2 * m * S (q ^ 2) k : ℕ) * x.den := by exact_mod_cast hnum
  have hnumN : x.num.natAbs * k = m * S (q ^ 2) k * x.den := by
    have := congrArg Int.natAbs hnumZ
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at this
    nlinarith
  have hcop : Nat.Coprime x.num.natAbs x.den := x.reduced
  have hQ1 : m ∣ q ^ 2 - 1 := by
    have h := Nat.sq_sub_sq q 1
    simp only [one_pow] at h
    rw [h]
    exact Dvd.dvd.mul_right (Dvd.intro_left 2 (by omega)) _
  rw [Nat.dvd_iff_prime_pow_dvd_dvd x.num.natAbs m]
  intro r a hr hra
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hrm : r ∣ m := (dvd_pow_self r ha.ne').trans hra
  obtain ⟨b, k', hk', hkk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show k ≠ 0 by omega) r hr.ne_one
  have hS := key r (q ^ 2) (hrm.trans hQ1) (Nat.one_le_pow _ _ hq.pos) b k (hkk ▸ dvd_mul_right _ _)
  obtain ⟨S', hS'⟩ := hS
  rw [hS'] at hnumN
  rw [hkk] at hnumN
  have hrb : 0 < r ^ b := pow_pos hr.pos b
  have h2 : x.num.natAbs * k' = m * S' * x.den := by
    have : r ^ b * (x.num.natAbs * k') = r ^ b * (m * S' * x.den) := by
      rw [← mul_assoc]; nlinarith [hnumN]
    exact Nat.eq_of_mul_eq_mul_left hrb this
  have hdiv : r ^ a ∣ x.num.natAbs * k' := by
    rw [h2]; exact (hra.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
  have hcop2 : Nat.Coprime (r ^ a) k' := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr).2 hk')
  exact hcop2.dvd_of_dvd_mul_right hdiv

end OMA336838

theorem OMA.solution : type_of% @OMA.S_oeis_a336838.main := by
  exact OMA336838.sol
