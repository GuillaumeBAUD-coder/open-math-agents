import OMAReductions.R_Erdos967_erdos_967_variants_two_three_five_R1

-- Step Erdos967.erdos_967.variants.two_three_five.R1.H2: hypothesis H2 of reduction Erdos967.erdos_967.variants.two_three_five.R1
-- Credit: @Raimo33

namespace RaimoE967

lemma pv (p n : ℕ) [Fact p.Prime] : padicValRat p (n : ℚ) = (padicValNat p n : ℤ) := by
  simp

lemma key (a b c : ℤ)
    (h : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 + (c : ℝ) * Real.log 5 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set q : ℚ := (2 : ℚ) ^ a * (3 : ℚ) ^ b * (5 : ℚ) ^ c with hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    rw [hq]; push_cast; positivity
  have hlog : Real.log (q : ℝ) = 0 := by
    rw [hq]; push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_zpow, Real.log_zpow, Real.log_zpow]
    exact h
  have hq1 : (q : ℝ) = 1 := Real.eq_one_of_pos_of_log_eq_zero hqpos hlog
  have hq1' : q = 1 := by exact_mod_cast hq1
  have e2 : (2 : ℚ) = ((2 : ℕ) : ℚ) := by norm_num
  have e3 : (3 : ℚ) = ((3 : ℕ) : ℚ) := by norm_num
  have e5 : (5 : ℚ) = ((5 : ℕ) : ℚ) := by norm_num
  have hval : ∀ (p : ℕ) [Fact p.Prime], padicValRat p q =
      a * padicValNat p 2 + b * padicValNat p 3 + c * padicValNat p 5 := by
    intro p _
    rw [hq, padicValRat.mul (by positivity) (by positivity),
      padicValRat.mul (by positivity) (by positivity),
      padicValRat.zpow, padicValRat.zpow, padicValRat.zpow, e2, e3, e5, pv, pv, pv]
  have h2 := hval 2
  have h3 := hval 3
  have h5 := hval 5
  rw [hq1', padicValRat.one] at h2 h3 h5
  have a2 : padicValNat 2 2 = 1 := padicValNat_self
  have a3 : padicValNat 3 3 = 1 := padicValNat_self
  have a5 : padicValNat 5 5 = 1 := padicValNat_self
  have b23 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have b25 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have b32 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have b35 : padicValNat 3 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have b52 : padicValNat 5 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have b53 : padicValNat 5 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [a2, b23, b25] at h2
  rw [b32, a3, b35] at h3
  rw [b52, b53, a5] at h5
  push_cast at h2 h3 h5
  omega

end RaimoE967

theorem OMA.solution : OMA.R_Erdos967_erdos_967_variants_two_three_five_R1.H2 := by
  unfold OMA.R_Erdos967_erdos_967_variants_two_three_five_R1.H2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def] at hg
  set d0 := (g 0).den
  set d1 := (g 1).den
  set d2 := (g 2).den
  have k0 : (g 0) * d0 = (g 0).num := Rat.mul_den_eq_num _
  have k1 : (g 1) * d1 = (g 1).num := Rat.mul_den_eq_num _
  have k2 : (g 2) * d2 = (g 2).num := Rat.mul_den_eq_num _
  have hd0 : (d0 : ℚ) ≠ 0 := by exact_mod_cast (g 0).den_nz
  have hd1 : (d1 : ℚ) ≠ 0 := by exact_mod_cast (g 1).den_nz
  have hd2 : (d2 : ℚ) ≠ 0 := by exact_mod_cast (g 2).den_nz
  obtain ⟨r0, r1, r2⟩ := RaimoE967.key ((g 0).num * (d1 * d2)) ((g 1).num * (d0 * d2))
    ((g 2).num * (d0 * d1)) (by
      have e : ∀ x : ℚ, ((x : ℚ) : ℝ) = x := fun _ => rfl
      have := congrArg (fun t : ℝ => t * ((d0 * d1 * d2 : ℕ) : ℝ)) hg
      simp only [zero_mul] at this
      rw [← this]
      have c0 : ((g 0).num : ℝ) = ((g 0 : ℚ) : ℝ) * (d0 : ℝ) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) k0; push_cast at this; linarith
      have c1 : ((g 1).num : ℝ) = ((g 1 : ℚ) : ℝ) * (d1 : ℝ) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) k1; push_cast at this; linarith
      have c2 : ((g 2).num : ℝ) = ((g 2 : ℚ) : ℝ) * (d2 : ℝ) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) k2; push_cast at this; linarith
      push_cast
      rw [c0, c1, c2]
      ring)
  intro i
  fin_cases i
  · have : ((g 0).num : ℚ) = 0 := by
      have := r0; simp only [mul_eq_zero, Nat.cast_eq_zero] at this
      rcases this with h | h | h
      · exact_mod_cast h
      · exact absurd h (g 1).den_nz
      · exact absurd h (g 2).den_nz
    rw [← k0] at this
    simpa [hd0] using this
  · have : ((g 1).num : ℚ) = 0 := by
      have := r1; simp only [mul_eq_zero, Nat.cast_eq_zero] at this
      rcases this with h | h | h
      · exact_mod_cast h
      · exact absurd h (g 0).den_nz
      · exact absurd h (g 2).den_nz
    rw [← k1] at this
    simpa [hd1] using this
  · have : ((g 2).num : ℚ) = 0 := by
      have := r2; simp only [mul_eq_zero, Nat.cast_eq_zero] at this
      rcases this with h | h | h
      · exact_mod_cast h
      · exact absurd h (g 0).den_nz
      · exact absurd h (g 1).den_nz
    rw [← k2] at this
    simpa [hd2] using this
