import OMAStatements.S_oeis_a182515

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a182515.main := by
  rintro C ⟨h, -, hb⟩ h23 h67
  have : NeZero C := ⟨by omega⟩
  have := carmichael_pow_of_prime_ne_two (p := 67) 1 (by norm_num) (by decide) ▸
    (carmichael_dvd h67).trans (carmichael_eq_exponent' C ▸
    Monoid.exponent_dvd_of_forall_pow_eq_one fun v => Units.ext (by
      simpa using (ZMod.natCast_eq_natCast_iff ..).2 (hb _ (ZMod.val_coe_unit_coprime v))))
  norm_num [Nat.totient_prime] at this
  exact ⟨C / 101706, by omega⟩
