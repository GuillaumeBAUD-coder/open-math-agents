import OMAReductions.R_Erdos244_erdos_244_variants_Romanoff_R1

/-! Count pairs with both the prime and the power at most one third of the cutoff. -/
open Finset Filter Real
namespace RomanoffFirstMoment
lemma primes : ∀ᶠ n : ℕ in atTop, (n:ℝ)/4 ≤ n.primeCounting * log n := by
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have he := Real.isLittleO_log_id_atTop.bound (c := (1:ℝ)/8) (by norm_num)
  filter_upwards [hlim.eventually he,eventually_ge_atTop 2] with n h hn
  change ‖log ((n:ℝ)+1)‖ ≤ 1/8 * ‖(n:ℝ)+1‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(n:ℝ)+1)] at h
  have hlog := log_pos (show (1:ℝ)<n by exact_mod_cast (show 1<n by omega))
  have hb := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge n)
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith only [hb,(le_abs_self _).trans h,hn',mul_le_mul_of_nonneg_right log_two_gt_d9.le (show 0 ≤ (n:ℝ) by positivity)]
end RomanoffFirstMoment

theorem OMA.solution : OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1 := by
  intro C hC
  have hlog := log_pos (show (1:ℝ)<C by exact_mod_cast hC)
  obtain ⟨N,hN⟩ := eventually_atTop.1 RomanoffFirstMoment.primes
  refine ⟨1/(16*log C),by positivity,3*(N+3),?_⟩
  intro x hx
  let y := x/3
  have hy : N+3 ≤ y := by dsimp [y]; omega
  let L := Nat.log C y
  let P := (range (y+1)).filter Nat.Prime
  have hP : P.card=y.primeCounting := by simp [P,Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  have hs : P ×ˢ range (L+1) ⊆ (range x ×ˢ range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1+C^q.2<x) := by
    rintro ⟨p,k⟩ h
    obtain ⟨hp,hk⟩ := mem_product.mp h
    obtain ⟨hpy,hpr⟩ := mem_filter.mp hp
    have hpy' := mem_range.mp hpy
    have hk' := mem_range.mp hk
    have hpow : C^k ≤ y := (Nat.pow_le_pow_right (by omega) (show k≤L by omega)).trans (Nat.pow_log_le_self _ (by omega))
    have hklt := Nat.lt_pow_self (n:=k) hC
    dsimp [y] at hpow hpy'
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,hpr,by change p+C^k<x; omega⟩
  have hl : log y ≤ ((L:ℝ)+1)*log C := by
    have he := Real.log_le_log (show 0<(y:ℝ) by exact_mod_cast (by omega : 0<y))
      (show (y:ℝ) ≤ (C:ℝ)^(L+1) by exact_mod_cast (Nat.lt_pow_succ_log_self hC y).le)
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_one] using he
  have hp := hN y (by omega)
  have hxy : (x:ℝ)≤4*y := by exact_mod_cast (show x≤4*y by dsimp [y] at *; omega)
  have hcard := card_le_card hs
  rw [card_product,card_range,hP] at hcard
  apply le_trans _ (show (y.primeCounting:ℝ)*(L+1) ≤ _ by exact_mod_cast hcard)
  rw [one_div,← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hp,hxy,mul_le_mul_of_nonneg_left hl (show 0 ≤ (y.primeCounting:ℝ) by positivity)]
