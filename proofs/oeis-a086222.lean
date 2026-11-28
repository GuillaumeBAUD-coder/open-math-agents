import OMAStatements.S_oeis_a086222
import Mathlib
open OMA.S_oeis_a086222
theorem sq_case (p : ℕ) (hp : p.Prime) : a (p^2) = 6 := by
  have h1 : 1 < p := hp.one_lt
  have h2 : p < p^2 := by nlinarith
  have hd : (p^2).divisors = {1, p, p^2} := by
    rw [Nat.divisors_prime_pow hp]
    ext d; simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨1, by omega, by simp⟩
      · exact ⟨2, by omega, rfl⟩
  have l1 : Nat.lcm p (p^2) = p^2 := Nat.lcm_eq_right (dvd_pow_self p two_ne_zero)
  have l2 : Nat.lcm (p^2) p = p^2 := Nat.lcm_eq_left (dvd_pow_self p two_ne_zero)
  have n1 : p ≠ p^2 := by omega
  have n3 : (1:ℕ) ≠ p^2 := by omega
  have m1 : (1:ℕ) ∉ ({p, p^2} : Finset ℕ) := by simp; omega
  have m2 : p ∉ ({p^2} : Finset ℕ) := by simp; omega
  unfold a
  rw [hd]
  simp only [Finset.sum_insert m1, Finset.sum_insert m2, Finset.sum_singleton,
    Nat.lcm_self, Nat.lcm_one_left, Nat.lcm_one_right, l1, l2]
  have o1 : 1 ≤ p := h1.le
  have o2 : p ≤ p^2 := h2.le
  have o3 : 1 ≤ p^2 := by omega
  have o4 : ¬ p ≤ 1 := by omega
  have o5 : ¬ p^2 ≤ p := by omega
  have o6 : ¬ p^2 ≤ 1 := by omega
  simp [o1, o2, o3, o4, o5, o6, n1, n3, n1.symm, n3.symm]

theorem pq_case (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) : a (p*q) = 13 := by
  have h1 : 1 < p := hp.one_lt
  have h2 : q < p * q := by nlinarith
  have hd : (p*q).divisors = {1, p, q, p*q} := by
    rw [Nat.divisors_mul, hp.divisors, hq.divisors]
    ext d; simp [Finset.mem_mul]
    tauto
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq.ne
  have l1 : Nat.lcm p q = p * q := hc.lcm_eq_mul
  have l2 : Nat.lcm q p = p * q := by rw [Nat.lcm_comm, l1]
  have l3 : Nat.lcm p (p*q) = p * q := Nat.lcm_eq_right (dvd_mul_right p q)
  have l4 : Nat.lcm q (p*q) = p * q := Nat.lcm_eq_right (dvd_mul_left q p)
  have l5 : Nat.lcm (p*q) p = p * q := Nat.lcm_eq_left (dvd_mul_right p q)
  have l6 : Nat.lcm (p*q) q = p * q := Nat.lcm_eq_left (dvd_mul_left q p)
  have n1 : p ≠ p * q := by nlinarith
  have n2 : q ≠ p * q := by omega
  have n3 : (1:ℕ) ≠ p * q := by nlinarith
  have m1 : (1:ℕ) ∉ ({p, q, p*q} : Finset ℕ) := by simp; omega
  have m2 : p ∉ ({q, p*q} : Finset ℕ) := by simp; omega
  have m3 : q ∉ ({p*q} : Finset ℕ) := by simp; omega
  unfold a
  rw [hd]
  simp only [Finset.sum_insert m1, Finset.sum_insert m2, Finset.sum_insert m3, Finset.sum_singleton,
    Nat.lcm_self, Nat.lcm_one_left, Nat.lcm_one_right, l1, l2, l3, l4, l5, l6]
  have o1 : 1 ≤ p := h1.le
  have o2 : p ≤ q := hpq.le
  have o3 : q ≤ p*q := h2.le
  have o4 : 1 ≤ q := by omega
  have o5 : 1 ≤ p*q := by omega
  have o6 : p ≤ p*q := by omega
  have o7 : ¬ p ≤ 1 := by omega
  have o8 : ¬ q ≤ 1 := by omega
  have o9 : ¬ p*q ≤ 1 := by omega
  have o10 : ¬ q ≤ p := by omega
  have o11 : ¬ p*q ≤ p := by omega
  have o12 : ¬ p*q ≤ q := by omega
  simp [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, n1, n2, n3, n1.symm, n2.symm, n3.symm]

theorem OMA.solution : type_of% @OMA.S_oeis_a086222.main := by
  refine ⟨fun p q hp hq hne => ?_, sq_case⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact pq_case p q hp hq h
  · rw [mul_comm]; exact pq_case q p hq hp h
