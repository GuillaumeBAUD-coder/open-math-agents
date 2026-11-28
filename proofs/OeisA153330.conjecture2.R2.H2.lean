import OMAReductions.R_OeisA153330_conjecture2_R2

/-! For even s, 2^s + 1 ≡ 2 (mod 3), so 3 does not divide it. For odd s, lifting the exponent
gives v_3(2^s + 1) = v_3(3) + v_3(s) = 1 + v_3(s), so K + 1 ≤ 1 + v_3(s). -/

theorem OMA.solution : OMA.R_OeisA153330_conjecture2_R2.H2 := by
  intro K s h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ 2 ^ s + 1 := (dvd_pow_self 3 (Nat.succ_ne_zero K)).trans h
  rcases Nat.even_or_odd s with hs | hs
  · exfalso
    obtain ⟨j, rfl⟩ := hs
    have e : (2 : ℕ) ^ (j + j) = 4 ^ j := by rw [← two_mul, pow_mul]; norm_num
    have h4 : 4 ^ j % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [e] at h3
    omega
  · have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hs
      exact absurd hs (by decide)
    have hv : padicValNat 3 (2 ^ s + 1 ^ s) = padicValNat 3 (2 + 1) + padicValNat 3 s :=
      padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide) (by decide) (by decide) hs
    have e3 : (2 : ℕ) + 1 = 3 := rfl
    rw [one_pow, e3, padicValNat_self] at hv
    have hle : K + 1 ≤ padicValNat 3 (2 ^ s + 1) := (padicValNat_dvd_iff_le (by positivity)).1 h
    rw [hv] at hle
    exact (padicValNat_dvd_iff_le hs0).2 (by omega)
