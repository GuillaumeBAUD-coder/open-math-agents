import OMAStatements.S_oeis_a182532

open OMA.S_oeis_a182532

lemma three_pow_small7 : ∀ r < 6, (3 : ZMod 7) ^ r = 1 → r = 0 := by
  decide

lemma three_pow_6 : (3 : ZMod 7) ^ 6 = 1 := by
  decide

lemma dvd6 (k : ℕ) (hk : (3 : ZMod 7) ^ k = 1) : 6 ∣ k := by
  have h : k = 6 * (k / 6) + k % 6 := (Nat.div_add_mod k 6).symm
  rw [h, pow_add, pow_mul, three_pow_6, one_pow, one_mul] at hk
  exact Nat.dvd_of_mod_eq_zero (three_pow_small7 _ (Nat.mod_lt _ (by norm_num)) hk)

lemma three_pow_small17 : ∀ r < 16, (3 : ZMod 17) ^ r = 1 → r = 0 := by
  decide

lemma three_pow_16 : (3 : ZMod 17) ^ 16 = 1 := by
  decide

lemma dvd16 (k : ℕ) (hk : (3 : ZMod 17) ^ k = 1) : 16 ∣ k := by
  have h : k = 16 * (k / 16) + k % 16 := (Nat.div_add_mod k 16).symm
  rw [h, pow_add, pow_mul, three_pow_16, one_pow, one_mul] at hk
  exact Nat.dvd_of_mod_eq_zero (three_pow_small17 _ (Nat.mod_lt _ (by norm_num)) hk)

/-- From the Fermat property and a prime-modulus base `g` lift a congruence to `ZMod p`. -/
lemma lift_base (C p g : ℕ) [NeZero C] (hp : p ∣ C) (hg : g.Coprime p)
    (hferm : ∀ b : ℕ, b.Coprime C → b ^ (C - 1) ≡ 1 [MOD C]) :
    (g : ZMod p) ^ (C - 1) = 1 := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := p) hp (ZMod.unitOfCoprime g hg)
  have hcop := ZMod.val_coe_unit_coprime u
  have hmod := (hferm _ hcop).of_dvd hp
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  push_cast at hmod
  have hval : (((u : ZMod C).val : ℕ) : ZMod p) = g := by
    rw [ZMod.natCast_val]
    have := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu
    simpa [ZMod.unitsMap] using this
  rw [hval] at hmod
  exact hmod

theorem OMA.solution : type_of% @OMA.S_oeis_a182532.main := by
  intro C hC h7 h17
  obtain ⟨hC1, -, hferm⟩ := hC
  have : NeZero C := ⟨by omega⟩
  have h3a := lift_base C 7 3 h7 (by norm_num) hferm
  have h3b := lift_base C 17 3 h17 (by norm_num) hferm
  push_cast at h3a h3b
  obtain ⟨k1, hk1⟩ := dvd6 _ h3a
  obtain ⟨k2, hk2⟩ := dvd16 _ h3b
  obtain ⟨m, rfl⟩ : 7 * 17 ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h7 h17
  have hm : m % 48 = 23 := by omega
  refine ⟨fun h => ⟨(m - 119) / 120, by omega⟩, fun h => ⟨(m - 95) / 120, by omega⟩,
    fun h => ⟨(m - 47) / 120, by omega⟩, fun h => ⟨(m - 71) / 120, by omega⟩⟩
