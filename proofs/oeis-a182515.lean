import OMAStatements.S_oeis_a182515

open OMA.S_oeis_a182515

lemma two_pow_small : ∀ r < 66, (2 : ZMod 67) ^ r = 1 → r = 0 := by
  decide

lemma two_pow_66 : (2 : ZMod 67) ^ 66 = 1 := by
  decide

lemma dvd66 (k : ℕ) (hk : (2 : ZMod 67) ^ k = 1) : 66 ∣ k := by
  have h : k = 66 * (k / 66) + k % 66 := (Nat.div_add_mod k 66).symm
  rw [h, pow_add, pow_mul, two_pow_66, one_pow, one_mul] at hk
  exact Nat.dvd_of_mod_eq_zero (two_pow_small _ (Nat.mod_lt _ (by norm_num)) hk)

theorem OMA.solution : type_of% @OMA.S_oeis_a182515.main := by
  intro C hC h23 h67
  obtain ⟨hC1, -, hferm⟩ := hC
  have : NeZero C := ⟨by omega⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := 67) h67
    (ZMod.unitOfCoprime 2 (by norm_num))
  have hcop := ZMod.val_coe_unit_coprime u
  have hmod := (hferm _ hcop).of_dvd h67
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  push_cast at hmod
  have hval : (((u : ZMod C).val : ℕ) : ZMod 67) = 2 := by
    rw [ZMod.natCast_val]
    have := congrArg (fun v : (ZMod 67)ˣ => (v : ZMod 67)) hu
    simpa [ZMod.unitsMap] using this
  rw [hval] at hmod
  have h66 := dvd66 _ hmod
  obtain ⟨m, rfl⟩ : 23 * 67 ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h23 h67
  obtain ⟨k, hk⟩ := h66
  refine ⟨m / 66, ?_⟩
  omega
