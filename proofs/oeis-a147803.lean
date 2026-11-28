import OMAStatements.S_oeis_a147803
import Mathlib

/-
A147803: rad(m (5^n - m) 5^n) = 5 rad(m (5^n - m)) for m coprime to 5 and m < 5^n.

n is not 0 (otherwise m = 0, which is not coprime to 5). Then 5 divides 5^n, so 5^n - m is
coprime to 5 as well, m (5^n - m) is coprime to 5^n, and the radical is multiplicative on
coprime factors with rad(5^n) = 5.
-/

namespace OMA.P147803

open UniqueFactorizationMonoid

lemma main' : ∀ n m : ℕ, Nat.Coprime m 5 → m < 5 ^ n →
      radical (m * (5 ^ n - m) * 5 ^ n) = 5 * radical (m * (5 ^ n - m)) := by
  intro n m hm hlt
  have hn : n ≠ 0 := by
    rintro rfl
    have : m = 0 := by simpa using hlt
    subst this
    simp at hm
  have h5 : Nat.Coprime (5 ^ n - m) 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro hd
    have h2 : 5 ∣ m := by
      have := Nat.dvd_sub (dvd_pow_self 5 hn) hd
      rwa [Nat.sub_sub_self hlt.le] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hm.symm h2
  have hc : Nat.Coprime (m * (5 ^ n - m)) (5 ^ n) := (hm.mul_left h5).pow_right n
  rw [radical_mul (Nat.coprime_iff_isRelPrime.1 hc), radical_pow 5 hn,
    radical_of_prime Nat.prime_five.prime]
  simp [mul_comm]

end OMA.P147803

theorem OMA.solution : type_of% @OMA.S_oeis_a147803.main := OMA.P147803.main'
