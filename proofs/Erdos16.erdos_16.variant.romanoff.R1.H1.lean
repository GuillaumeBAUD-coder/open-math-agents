import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1
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

theorem OMA.solution : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1 := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 RomanoffFirstMoment.primes
  refine ⟨1/(64*log 2),by positivity,3*(N+4),?_⟩
  intro x hx
  let y := x/3
  have hy : N+4 ≤ y := by dsimp [y]; omega
  let L := Nat.log 2 y
  let P := (range (y+1)).filter Nat.Prime
  have hP : P.card=y.primeCounting := by simp [P,Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  have hp2 : 2 ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega), by decide⟩
  have two : 2 ≤ P.card := by
    calc 2 = ({2,3} : Finset ℕ).card := by decide
         _ ≤ _ := card_le_card (by intro p hp; simp at hp; rcases hp with rfl | rfl
                                   · exact hp2
                                   · exact mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩)
  have lp : 1 ≤ L := Nat.le_log_of_pow_le (by decide) (by dsimp [y] at *; norm_num; omega)
  let R (n : ℕ) := (range n).filter fun k => 1 ≤ k ∧ 2^k < n ∧ (n-2^k).Prime ∧ n-2^k ≠ 2
  let F (q : ℕ × ℕ) : (Σ _ : ℕ, ℕ) := ⟨q.1+2^q.2,q.2⟩
  have count : ((P.erase 2) ×ˢ Icc 1 L).card ≤ ((range (x+1)).sigma R).card := by
    apply card_le_card_of_injOn F
    · rintro ⟨p,k⟩ h
      obtain ⟨hp,hk⟩ := mem_product.mp h
      obtain ⟨hne,hp⟩ := mem_erase.mp hp
      obtain ⟨hpy,hpr⟩ := mem_filter.mp hp
      have hpy := mem_range.mp hpy
      obtain ⟨hk1,hkL⟩ := mem_Icc.mp hk
      have ha : 2^k ≤ y := (Nat.pow_le_pow_right (by decide) hkL).trans (Nat.pow_log_le_self _ (by omega))
      have hklt := Nat.lt_pow_self (n:=k) (by decide : 1<2)
      have hpp := hpr.pos
      change (⟨p+2^k,k⟩ : Σ _ : ℕ, ℕ) ∈ (range (x+1)).sigma R
      apply mem_sigma.mpr
      change p+2^k ∈ range (x+1) ∧ k ∈ R (p+2^k)
      refine ⟨mem_range.mpr (by dsimp [y] at *; omega),mem_filter.mpr ⟨mem_range.mpr (by omega),hk1,by omega,?_⟩⟩
      simpa using And.intro hpr hne
    · rintro ⟨p,k⟩ _ ⟨q,j⟩ _ h
      have hk := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
      change k=j at hk
      subst j
      have hn := congrArg Sigma.fst h
      change p+2^k=q+2^k at hn
      simp [Nat.add_right_cancel hn]
  have hp := hN y (by omega)
  have hl : log y ≤ ((L:ℝ)+1)*log 2 := by
    have he := Real.log_le_log (show 0<(y:ℝ) by exact_mod_cast (by omega : 0<y))
      (show (y:ℝ) ≤ (2:ℝ)^(L+1) by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) y).le)
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_one] using he
  have hxy : (x:ℝ)≤4*y := by exact_mod_cast (show x≤4*y by dsimp [y] at *; omega)
  rw [card_product,Nat.card_Icc,card_erase_of_mem hp2,card_sigma] at count
  simp only [Nat.add_sub_cancel] at count
  have scaled : y.primeCounting*(L+1) ≤ 4*∑ n ∈ range (x+1), (R n).card := by
    have e := Nat.mul_le_mul (show P.card ≤ 2*(P.card-1) by omega) (show L+1 ≤ 2*L by omega)
    rw [← hP]
    nlinarith only [e,count]
  have hs : (y.primeCounting:ℝ)*((L:ℝ)+1) ≤ 4*∑ n ∈ range (x+1), ((R n).card : ℝ) := by exact_mod_cast scaled
  rw [one_div,← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hp,hxy,mul_le_mul_of_nonneg_left hl (show 0 ≤ (y.primeCounting:ℝ) by positivity),
    mul_le_mul_of_nonneg_right hs (show 0 ≤ log 2 by positivity)]
