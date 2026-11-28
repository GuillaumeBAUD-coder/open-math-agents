import OMAStatements.S_oeis_a147804

-- The argument follows the accepted proof of the template entry OEIS A147803.

open UniqueFactorizationMonoid in
theorem OMA.solution : type_of% @OMA.S_oeis_a147804.main := by
  intro n m hm hlt
  have hn : n ≠ 0 := by
    rintro rfl
    have : m = 0 := by simpa using hlt
    subst this
    norm_num at hm
  have h7 : Nat.Coprime (7 ^ n - m) 7 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro hd
    have h77 : 7 ∣ 7 ^ n := dvd_pow_self 7 hn
    have : 7 ∣ m := by
      have := Nat.dvd_sub h77 hd
      rwa [Nat.sub_sub_self hlt.le] at this
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)] at hm
    exact hm this
  have hcop : Nat.Coprime (m * (7 ^ n - m)) (7 ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.mul_left hm h7)
  rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hcop), radical_pow _ hn,
    radical_of_prime (a := (7 : ℕ)) (Nat.prime_iff.mp (by norm_num)), mul_comm]
  simp
