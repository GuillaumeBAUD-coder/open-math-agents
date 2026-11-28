import OMAStatements.S_oeis_a010055
import Mathlib

/-!
# A010055: Yanev's identity for the prime-power indicator

If n = p^k is a prime power, its proper divisors are p^0, ..., p^(k−1), so their lcm is p^(k−1),
and n − p^(k−1) = p^(k−1)(p − 1) = φ(n), giving 1. Otherwise every prime power dividing n is a
proper divisor of n, so it divides the lcm of the proper divisors; hence that lcm is n itself and
the quotient is 0.
-/

namespace A010055Proof

theorem lcm_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (p ^ k).properDivisors.lcm id = p ^ (k - 1) := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro d hd
    obtain ⟨hdk, hlt⟩ := Nat.mem_properDivisors.mp hd
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdk
    have : i < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    exact pow_dvd_pow p (by omega)
  · apply Finset.dvd_lcm (s := (p ^ k).properDivisors) (f := id)
    rw [Nat.mem_properDivisors]
    exact ⟨pow_dvd_pow p (by omega), Nat.pow_lt_pow_right hp.one_lt (by omega)⟩

theorem lcm_not_prime_pow (n : ℕ) (hn : 1 < n) (hnp : ¬ IsPrimePow n) :
    n.properDivisors.lcm id = n :=
  Nat.dvd_antisymm (Finset.lcm_dvd fun d hd => (Nat.mem_properDivisors.mp hd).1)
    ((Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p k hp h => by
      rcases k with _ | k
      · simp
      · exact Finset.dvd_lcm (Nat.mem_properDivisors.2 ⟨h, (Nat.le_of_dvd (by omega) h).lt_of_ne
          fun e => hnp ⟨p, k + 1, hp.prime, by omega, e⟩⟩))

end A010055Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a010055.main := by
  intro n hn
  unfold OMA.S_oeis_a010055.a OMA.S_oeis_a010055.lcmProper
  by_cases hpp : IsPrimePow n
  · rw [if_pos (Or.inr hpp)]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [A010055Proof.lcm_prime_pow p k hp hk, Nat.totient_prime_pow hp hk]
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    have hpk : (p : ℚ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by linarith)
    have e : (p : ℚ) ^ k = (p : ℚ) ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    push_cast [Nat.cast_sub hp.one_le, e]
    rw [eq_div_iff (mul_ne_zero hpk (by linarith))]
    ring
  · rw [if_neg (by rintro (h | h) <;> [omega; exact hpp h]),
      A010055Proof.lcm_not_prime_pow n hn hpp]
    simp
