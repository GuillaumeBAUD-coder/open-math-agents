import OMAReductions.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1
import Mathlib

/-! A composite n has the proper divisor n / p, where p is its least prime factor, and
n / p >= p, so s(n) ^ 2 >= (n / p) ^ 2 >= n. -/

theorem OMA.solution :
    OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H2 := by
  unfold OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H2
  intro n hn hnp
  have hs : Erdos955.s n = ∑ d ∈ n.properDivisors, d := by
    rw [Erdos955.s, ArithmeticFunction.sigma_one_apply,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
    exact Nat.add_sub_cancel _ _
  have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  have hp2 : 2 ≤ n.minFac := hpp.two_le
  have hpm : n.minFac ≤ m := by
    by_contra hlt
    have hlt : m < n.minFac := Nat.lt_of_not_ge hlt
    have h1 : n.minFac * m < n.minFac * n.minFac := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    have h2 : n.minFac ^ 2 = n.minFac * n.minFac := sq _
    omega
  have hmpos : 0 < m := by omega
  have hmem : m ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    refine ⟨⟨n.minFac, by rw [mul_comm]; exact hm⟩, ?_⟩
    have h1 : 2 * m ≤ n.minFac * m := Nat.mul_le_mul_right m hp2
    omega
  have hle : m ≤ Erdos955.s n := by
    rw [hs]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d) hmem
  calc n = n.minFac * m := hm
    _ ≤ m * m := Nat.mul_le_mul_right m hpm
    _ ≤ Erdos955.s n * Erdos955.s n := Nat.mul_le_mul hle hle
    _ = Erdos955.s n ^ 2 := (sq _).symm
