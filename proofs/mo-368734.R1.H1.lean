import OMAReductions.R_mo_368734_R1

/-!
# Proof of `mo-368734.R1.H1`

Proves that for every prime `p` with `p % 5 ≠ 1`, the map `x ↦ x ^ 5 + 3` is a bijection on
`ZMod p`.

If `p = 2` or `p = 5`, Fermat's little theorem gives `x ^ 5 = x` on `ZMod p`. Otherwise `p - 1 ≥ 2`
is coprime to `5`, so there exists `d ≥ 1` with `5 * d ≡ 1 [MOD p - 1]`, giving `(z ^ 5) ^ d = z`
for every `z : ZMod p`. Thus `x ↦ x ^ 5 + 3` is injective on the finite type `ZMod p`, hence
bijective.
-/

theorem OMA.solution : OMA.R_mo_368734_R1.H1 := by
  intro p hp hmod
  have : Fact p.Prime := ⟨hp⟩
  refine (Finite.injective_iff_bijective).mp ?_
  intro x y hxy
  have hpow : x ^ 5 = y ^ 5 := add_right_cancel hxy
  by_cases hp5 : p = 5
  · subst hp5
    have hx : x ^ 5 = x := ZMod.pow_card x
    have hy : y ^ 5 = y := ZMod.pow_card y
    rw [hx, hy] at hpow
    exact hpow
  · by_cases hp2 : p = 2
    · subst hp2
      have h5 : ∀ z : ZMod 2, z ^ 5 = z := by
        intro z
        have h2 : z ^ 2 = z := ZMod.pow_card z
        have h4 : z ^ 4 = z := by
          calc z ^ 4 = (z ^ 2) ^ 2 := by ring
            _ = z ^ 2 := congrArg (· ^ 2) h2
            _ = z := h2
        calc z ^ 5 = z ^ 4 * z := by ring
          _ = z * z := congrArg (· * z) h4
          _ = z ^ 2 := by ring
          _ = z := h2
      rw [h5 x, h5 y] at hpow
      exact hpow
    · have hp1_gt1 : 1 < p - 1 := by have := hp.two_le; omega
      have hcop : Nat.Coprime 5 (p - 1) := by
        rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)]
        intro hdvd
        have h1 : (p - 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd
        omega
      have hinv_exists : ∃ d : ℕ, 5 * d ≡ 1 [MOD (p - 1)] := by
        have : NeZero (p - 1) := ⟨by omega⟩
        refine ⟨((5 : ZMod (p - 1))⁻¹).val, ?_⟩
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        rw [ZMod.natCast_zmod_val]
        exact ZMod.mul_inv_of_unit (5 : ZMod (p - 1))
          (by simpa using (ZMod.isUnit_iff_coprime 5 (p - 1)).mpr hcop)
      obtain ⟨d, hd⟩ := hinv_exists
      have hpow_d : ∀ z : ZMod p, (z ^ 5) ^ d = z := by
        intro z
        have hd_pos : 0 < d := by
          by_contra h0
          have hd0 : d = 0 := by omega
          subst hd0
          have : (0 : ℕ) % (p - 1) = 1 % (p - 1) := by simpa [Nat.ModEq] using hd
          rw [Nat.zero_mod, Nat.mod_eq_of_lt hp1_gt1] at this
          omega
        by_cases hz : z = 0
        · subst hz; rw [zero_pow (by decide : 5 ≠ 0), zero_pow hd_pos.ne']
        · rw [← pow_mul]
          have hdvd : (p - 1) ∣ (5 * d - 1) :=
            (Nat.modEq_iff_dvd' (by omega : 1 ≤ 5 * d)).mp hd.symm
          obtain ⟨k, hk⟩ := hdvd
          have heq : 5 * d = 1 + (p - 1) * k := by omega
          rw [heq, pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hz, one_pow, mul_one]
      have h1 : (x ^ 5) ^ d = (y ^ 5) ^ d := congrArg (· ^ d) hpow
      rw [hpow_d x, hpow_d y] at h1
      exact h1
