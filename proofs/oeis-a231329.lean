import OMAStatements.S_oeis_a231329
import Mathlib

/-!
Credit: @ivillar
Proof: modulo 23 we have 19 = -4, so for even n = 2m, 19^n + 4^n = 2 * 16^m is not divisible
by 23; hence n is odd. For n = 1 the quotient is 1, not a prime. If n = a b with 1 < a < n,
then a and b are odd, so 23 = 19 + 4 divides Q = 19^a + 4^a and Q divides 19^n + 4^n. Writing
19^n + 4^n = Q R and Q = 23 Q', the quotient (19^n + 4^n)/23 = Q' R is prime, so Q' = 1 or
R = 1; but Q >= 19^2 > 23 and Q < 19^n + 4^n, a contradiction. So n is prime.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a231329.main := by
  intro n hn
  obtain ⟨hdvd, hp⟩ := hn
  have hz : ((19 ^ n + 4 ^ n : ℕ) : ZMod 23) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | h
    · exfalso
      have e1 : (19 : ZMod 23) ^ 2 = 16 := by decide
      have e2 : (4 : ZMod 23) ^ 2 = 16 := by decide
      have hz' : ((2 * 16 ^ m : ℕ) : ZMod 23) = 0 := by
        push_cast at hz ⊢
        rw [← two_mul, pow_mul, pow_mul, e1, e2, ← two_mul] at hz
        exact hz
      have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz'
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 23)).mp hd with h | h
      · norm_num at h
      · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 23) h
        norm_num at this
    · exact h
  by_contra hnp
  have hn1 : n ≠ 1 := by
    rintro rfl
    norm_num at hp
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  obtain ⟨a, ha1, hlt, b, hb⟩ : ∃ a, 1 < a ∧ a < n ∧ ∃ b, n = a * b :=
    ⟨n.minFac, (Nat.minFac_prime hn1).one_lt, (Nat.not_prime_iff_minFac_lt hn2).mp hnp,
      Nat.minFac_dvd n⟩
  have hab : Odd a ∧ Odd b := Nat.odd_mul.mp (hb ▸ hodd)
  have hQN : 19 ^ a + 4 ^ a ∣ 19 ^ n + 4 ^ n := by
    rw [hb, pow_mul, pow_mul]
    exact hab.2.nat_add_dvd_pow_add_pow (19 ^ a) (4 ^ a)
  have h23Q : 23 ∣ 19 ^ a + 4 ^ a := by
    have := hab.1.nat_add_dvd_pow_add_pow 19 4
    norm_num at this
    exact this
  obtain ⟨R, hR⟩ := hQN
  obtain ⟨Q', hQ'⟩ := h23Q
  have hP : (19 ^ n + 4 ^ n) / 23 = Q' * R := by
    rw [hR, hQ', mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hP] at hp
  have h19a : 19 ^ 2 ≤ 19 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  have h19n : 19 ^ a < 19 ^ n := Nat.pow_lt_pow_right (by norm_num) hlt
  have h4n : 4 ^ a < 4 ^ n := Nat.pow_lt_pow_right (by norm_num) hlt
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hR1⟩ | ⟨_, hQ1⟩
  · rw [hR1, mul_one] at hR
    generalize 19 ^ n = x1 at hR h19n
    generalize 4 ^ n = x2 at hR h4n
    generalize 19 ^ a = x3 at hR h19n
    generalize 4 ^ a = x4 at hR h4n
    omega
  · rw [hQ1, mul_one] at hQ'
    have h361 : 361 ≤ 19 ^ a := by simpa using h19a
    generalize 19 ^ a = x3 at hQ' h361
    generalize 4 ^ a = x4 at hQ'
    omega
