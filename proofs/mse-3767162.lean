import OMAStatements.S_mse_3767162

theorem OMA.solution : type_of% @OMA.S_mse_3767162.main := by
  intro n ⟨a, b, hab⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, by simp⟩
  have hda : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hdb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  have ha : (a.num : ℚ) = a * a.den := (div_eq_iff hda).mp (Rat.num_div_den a)
  have hb : (b.num : ℚ) = b * b.den := (div_eq_iff hdb).mp (Rat.num_div_den b)
  have keyQ : (n : ℚ) * ((a.den : ℚ) * (b.den : ℚ)) ^ 2 =
      ((a.num : ℚ) * (b.den : ℚ)) ^ 2 + ((b.num : ℚ) * (a.den : ℚ)) ^ 2 := by
    rw [ha, hb, hab]
    ring
  have keyZ : (n : ℤ) * ((a.den : ℤ) * (b.den : ℤ)) ^ 2 =
      (a.num * (b.den : ℤ)) ^ 2 + (b.num * (a.den : ℤ)) ^ 2 := by
    exact_mod_cast keyQ
  have keyN : n * (a.den * b.den) ^ 2 =
      (a.num * (b.den : ℤ)).natAbs ^ 2 + (b.num * (a.den : ℤ)).natAbs ^ 2 := by
    apply Int.natCast_inj.mp
    push_cast [Int.natAbs_pow_two]
    rw [sq_abs, sq_abs]
    exact keyZ
  have hD : a.den * b.den ≠ 0 := Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero
  have hN := (Nat.eq_sq_add_sq_iff (n := n * (a.den * b.den) ^ 2)).mp ⟨_, _, keyN⟩
  obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_iff.mpr (fun q hq hq3 => by
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := Fact.mk hqp
    have hmem : q ∈ (n * (a.den * b.den) ^ 2).primeFactors :=
      hqp.mem_primeFactors (Dvd.dvd.mul_right (Nat.dvd_of_mem_primeFactors hq) _)
        (Nat.mul_ne_zero hn.ne' (pow_ne_zero 2 hD))
    have h := hN q hmem hq3
    rw [padicValNat.mul hn.ne' (pow_ne_zero 2 hD), padicValNat.pow] at h
    exact (Nat.even_add.mp h).mpr (even_two_mul _))
  exact ⟨x, y, by exact_mod_cast hxy⟩
