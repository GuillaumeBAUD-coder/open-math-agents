import OMAStatements.S_oeis_a111441
import Mathlib

/-!
# A111441: no terms are 3 or 9 modulo 12

The first two primes contribute 2² + 3² = 13 ≡ 1 (mod 3), and every later prime p > 3 has p² ≡ 1
(mod 3). So for k ≥ 2 the sum of the squares of the first k primes is ≡ k − 1 (mod 3). If
k ≡ 3 or 9 (mod 12) then 3 ∣ k, and k dividing the sum would force 3 to divide it, i.e. k ≡ 1
(mod 3), a contradiction.
-/

namespace PA111441
open OMA.S_oeis_a111441

theorem sq_mod (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : p ^ 2 % 3 = 1 := by
  have hnd : p % 3 ≠ 0 := by
    intro h
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 (Nat.dvd_of_mod_eq_zero h)).resolve_left (by norm_num)
    omega
  rw [Nat.pow_mod]
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h <;> rw [h]

theorem S_mod (k : ℕ) : sumSquaresFirstPrimes (k + 2) % 3 = (k + 1) % 3 := by
  induction k with
  | zero =>
    unfold sumSquaresFirstPrimes
    simp [Finset.sum_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  | succ k ih =>
    unfold sumSquaresFirstPrimes at ih ⊢
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_range_succ]
    have hp : (Nat.nth Nat.Prime (k + 2)).Prime := Nat.prime_nth_prime _
    have h3 : 3 < Nat.nth Nat.Prime (k + 2) := by
      have := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 1 < k + 2 by omega)
      rwa [Nat.nth_prime_one_eq_three] at this
    have := sq_mod _ hp h3
    omega

end PA111441

theorem OMA.solution : type_of% @OMA.S_oeis_a111441.main := by
  rintro k ⟨hk, hd⟩
  by_contra h
  have h3 : k % 3 = 0 := by omega
  have hk3 : 3 ≤ k := by omega
  have hmod := PA111441.S_mod (k - 2)
  rw [show k - 2 + 2 = k by omega] at hmod
  have : 3 ∣ OMA.S_oeis_a111441.sumSquaresFirstPrimes k :=
    (Nat.dvd_of_mod_eq_zero h3).trans hd
  omega
