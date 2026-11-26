import FormalConjectures.ErdosProblems.«297»

/-! An exponential weight bounds the number of subsets with reciprocal sum at most one. -/

open Filter
open scoped BigOperators

/-- Rational upper bounds on the exponential weight at the right endpoints of the blocks. -/
def OMA.reciprocal_q (j : Fin 32) : ℚ :=
  ((![12, 109, 228, 330, 412, 478, 531, 575, 611, 642, 669, 691, 711, 729, 744, 758,
      771, 782, 792, 802, 810, 818, 825, 832, 838, 844, 849, 854, 859, 863, 867, 871] :
    Fin 32 → ℕ) j : ℚ) / 1000

theorem OMA.reciprocal_q_nonneg (j : Fin 32) : 0 ≤ (OMA.reciprocal_q j : ℝ) := by
  unfold OMA.reciprocal_q
  positivity

set_option maxRecDepth 4096 in
theorem OMA.reciprocal_q_certificate (j : Fin 32) :
    1 ≤ (OMA.reciprocal_q j) ^ (5 * (j.val + 1)) * (2 : ℚ) ^ (32 : ℕ) := by
  fin_cases j <;> norm_num [OMA.reciprocal_q]

set_option maxRecDepth 4096 in
theorem OMA.reciprocal_product_certificate :
    (∏ j : Fin 32, (1 + OMA.reciprocal_q j)) ^ (4 : ℕ) ≤ (2 : ℚ) ^ (93 : ℕ) := by
  norm_num [Fin.prod_univ_succ, OMA.reciprocal_q]

theorem OMA.reciprocal_q_bound (j : Fin 32) :
    (2 : ℝ) ^ (-32 / (5 * ((j.val : ℝ) + 1))) ≤ (OMA.reciprocal_q j : ℝ) := by
  let a : ℕ := 5 * (j.val + 1)
  have ha : (a : ℝ) = 5 * ((j.val : ℝ) + 1) := by simp [a]
  have hap : (0 : ℝ) < a := by rw [ha]; positivity
  have hcert : (1 : ℝ) ≤ (OMA.reciprocal_q j : ℝ) ^ a * (2 : ℝ) ^ (32 : ℕ) := by
    exact_mod_cast OMA.reciprocal_q_certificate j
  apply (Real.rpow_le_rpow_iff (by positivity) (OMA.reciprocal_q_nonneg j) hap).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← ha,
    div_mul_cancel₀ _ hap.ne', Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (32 : ℝ) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  exact hcert

theorem OMA.reciprocal_product_bound :
    (∏ j : Fin 32, (1 + (OMA.reciprocal_q j : ℝ))) ≤ (2 : ℝ) ^ (93 / 4 : ℝ) := by
  have hcert : (∏ j : Fin 32, (1 + (OMA.reciprocal_q j : ℝ))) ^ (4 : ℕ) ≤
      (2 : ℝ) ^ (93 : ℕ) := by
    exact_mod_cast OMA.reciprocal_product_certificate
  apply (Real.rpow_le_rpow_iff (by
    exact Finset.prod_nonneg fun j _ => by linarith [OMA.reciprocal_q_nonneg j]) (by positivity)
    (show (0 : ℝ) < (4 : ℕ) by norm_num)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (93 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((93 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  exact hcert

noncomputable def OMA.reciprocal_weight (m i : ℕ) : ℝ :=
  2 ^ (-(32 * (m : ℝ) / 5) / (i : ℝ))

theorem OMA.reciprocal_weight_nonneg (m i : ℕ) : 0 ≤ OMA.reciprocal_weight m i := by
  unfold OMA.reciprocal_weight
  positivity

theorem OMA.reciprocal_weight_block (m : ℕ) (hm : 0 < m) (j : Fin 32) (k : Fin m) :
    OMA.reciprocal_weight m (k.val + m * j.val + 1) ≤ (OMA.reciprocal_q j : ℝ) := by
  refine le_trans ?_ (OMA.reciprocal_q_bound j)
  unfold OMA.reciprocal_weight
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hk : k.val + m * j.val + 1 ≤ m * (j.val + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := k.isLt
    omega
  have hkR : ((k.val + m * j.val + 1 : ℕ) : ℝ) ≤ (m : ℝ) * ((j.val : ℝ) + 1) := by
    exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (0 : ℝ) < (j.val : ℝ) + 1 := by positivity
  have hdiv := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 32 * m / 5 by positivity)
    (show (0 : ℝ) < ((k.val + m * j.val + 1 : ℕ) : ℝ) by positivity) hkR
  have hcancel : (32 * (m : ℝ) / 5) / ((m : ℝ) * ((j.val : ℝ) + 1)) =
      32 / (5 * ((j.val : ℝ) + 1)) := by
    field_simp
  rw [hcancel] at hdiv
  simpa only [neg_div] using neg_le_neg hdiv

theorem OMA.reciprocal_weight_product (m : ℕ) (hm : 0 < m) :
    (∏ i ∈ Finset.Icc 1 (32 * m), (1 + OMA.reciprocal_weight m i)) ≤
      (2 : ℝ) ^ ((93 / 4 : ℝ) * (m : ℝ)) := by
  have hIcc : Finset.Icc 1 (32 * m) = Finset.Ico 1 (32 * m + 1) := by
    ext i
    simp
  calc
    (∏ i ∈ Finset.Icc 1 (32 * m), (1 + OMA.reciprocal_weight m i)) =
        ∏ i : Fin (32 * m), (1 + OMA.reciprocal_weight m (i.val + 1)) := by
      rw [hIcc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
      simpa only [Nat.add_comm 1] using
        (Fin.prod_univ_eq_prod_range (fun i => 1 + OMA.reciprocal_weight m (i + 1)) (32 * m)).symm
    _ = ∏ u : Fin 32 × Fin m, (1 + OMA.reciprocal_weight m (u.2.val + m * u.1.val + 1)) := by
      symm
      exact Fintype.prod_equiv finProdFinEquiv _ _ (fun _ => rfl)
    _ ≤ ∏ _u : Fin 32 × Fin m, (1 + (OMA.reciprocal_q _u.1 : ℝ)) := by
      apply Finset.prod_le_prod
      · intro u _
        exact add_nonneg zero_le_one (OMA.reciprocal_weight_nonneg _ _)
      · intro u _
        exact add_le_add_right (OMA.reciprocal_weight_block m hm u.1 u.2) 1
    _ = (∏ j : Fin 32, (1 + (OMA.reciprocal_q j : ℝ))) ^ m := by
      simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow]
    _ ≤ ((2 : ℝ) ^ (93 / 4 : ℝ)) ^ m :=
      pow_le_pow_left₀ (Finset.prod_nonneg fun j _ => by linarith [OMA.reciprocal_q_nonneg j])
        OMA.reciprocal_product_bound _
    _ = (2 : ℝ) ^ ((93 / 4 : ℝ) * (m : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem OMA.reciprocal_weight_count (N m : ℕ) (hNm : N ≤ 32 * m) (hm : 0 < m) :
    ({A ∈ (Finset.Icc 1 N).powerset | ∑ i ∈ A, (1 / (i : ℕ) : ℚ) ≤ 1}.card : ℝ) ≤
      (2 : ℝ) ^ ((93 / 4 + 32 / 5 : ℝ) * (m : ℝ)) := by
  classical
  let S := Finset.Icc 1 N
  let B := S.powerset.filter fun A => ∑ i ∈ A, (1 / (i : ℕ) : ℚ) ≤ 1
  let t : ℝ := 32 * (m : ℝ) / 5
  change (B.card : ℝ) ≤ _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hw (A : Finset ℕ) (hA : A ∈ B) :
      (2 : ℝ) ^ (-t) ≤ ∏ i ∈ A, OMA.reciprocal_weight m i := by
    have hsum : (∑ i ∈ A, (1 / (i : ℕ) : ℝ)) ≤ 1 := by
      have hrat : (∑ i ∈ A, (1 / (i : ℕ) : ℚ)) ≤ 1 := (Finset.mem_filter.mp hA).2
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
        (Rat.cast_le (K := ℝ)).mpr hrat
    have hexponent : (∑ i ∈ A, -t / (i : ℝ)) = -t * ∑ i ∈ A, 1 / (i : ℝ) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    simp only [OMA.reciprocal_weight]
    change (2 : ℝ) ^ (-t) ≤ ∏ i ∈ A, (2 : ℝ) ^ (-t / (i : ℝ))
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2), hexponent]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr ht)
  have hB : B ⊆ S.powerset := Finset.filter_subset _ _
  have hS : S ⊆ Finset.Icc 1 (32 * m) := by
    intro i hi
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hi₁, hi₂.trans hNm⟩
  have htotal : (B.card : ℝ) * (2 : ℝ) ^ (-t) ≤ (2 : ℝ) ^ ((93 / 4 : ℝ) * (m : ℝ)) := by
    calc
      (B.card : ℝ) * (2 : ℝ) ^ (-t) = ∑ _A ∈ B, (2 : ℝ) ^ (-t) := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ A ∈ B, ∏ i ∈ A, OMA.reciprocal_weight m i := Finset.sum_le_sum hw
      _ ≤ ∑ A ∈ S.powerset, ∏ i ∈ A, OMA.reciprocal_weight m i :=
        Finset.sum_le_sum_of_subset_of_nonneg hB fun A _ _ =>
          Finset.prod_nonneg fun i _ => OMA.reciprocal_weight_nonneg m i
      _ = ∏ i ∈ S, (1 + OMA.reciprocal_weight m i) := (Finset.prod_one_add S).symm
      _ ≤ ∏ i ∈ Finset.Icc 1 (32 * m), (1 + OMA.reciprocal_weight m i) :=
        Finset.prod_le_prod_of_subset_of_one_le hS
          (fun i _ => add_nonneg zero_le_one (OMA.reciprocal_weight_nonneg m i))
          (fun i _ _ => le_add_of_nonneg_right (OMA.reciprocal_weight_nonneg m i))
      _ ≤ _ := OMA.reciprocal_weight_product m hm
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (-t))).mpr
    at htotal
  have hexp : (93 / 4 : ℝ) * (m : ℝ) - (-t) = (93 / 4 + 32 / 5 : ℝ) * (m : ℝ) := by
    dsimp [t]
    ring
  simpa only [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), hexp] using htotal

theorem OMA.solution : type_of% @Erdos297.erdos_297.variants.steinerberger := by
  apply eventually_atTop.mpr
  refine ⟨10000, fun N hN => ?_⟩
  let m := (N + 31) / 32
  have hm0 : 0 < m := by dsimp [m]; omega
  have hm₁ : N ≤ 32 * m := by dsimp [m]; omega
  have hm₂ : 32 * m ≤ N + 31 := by dsimp [m]; omega
  refine (OMA.reciprocal_weight_count N m hm₁ hm0).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hmR : 32 * (m : ℝ) ≤ (N : ℝ) + 31 := by exact_mod_cast hm₂
  have hNR : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  linarith