import OMAReductions.R_Erdos499_vanDerWaerden_R1

-- Step Erdos499.vanDerWaerden.R1.H3: hypothesis H3 of reduction Erdos499.vanDerWaerden.R1
-- Credit: @marcusbuffett
-- H3 := ∀ (d m : ℕ), 1 ≤ d → m ≤ d → ∀ (a : ℝ) (r : Fin m → ℝ) (L D : ℝ), 0 ≤ a → (∀ i, 0 ≤ r i) →     (∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) →     HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0 →     (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ D  /-- Weighted AM-GM: for doubly stochastic `M` and positive `x`, `prod x ≤ prod (M x)`. -/

open Finset Filter
open scoped Topology

/-- Pad the product with ones before applying the arithmetic-geometric mean inequality. -/
private theorem padded_amgm {d m : ℕ} (hd : 0 < d) (hm : m ≤ d)
    (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∏ i, (1 + x i)) ≤ (1 + (∑ i, x i) / d) ^ d := by
  let z : Fin m ⊕ Fin (d - m) → ℝ := Sum.elim (fun i => 1+x i) (fun _ => 1)
  have hz (i) : 0 ≤ z i := by
    cases i with
    | inl i => exact add_nonneg zero_le_one (hx i)
    | inr i => exact zero_le_one
  have hc : Fintype.card (Fin m ⊕ Fin (d-m)) = d := by simp; omega
  have hs : ∑ _i : Fin m ⊕ Fin (d-m), (1 : ℝ) = d := by simp [hc]
  have h := Real.geom_mean_le_arith_mean univ (fun _ => (1 : ℝ)) z (by simp)
    (by rw [hs]; exact_mod_cast hd) (fun i _ => hz i)
  simp only [Real.rpow_one, hs, one_mul] at h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (prod_nonneg (fun i _ => hz i)) _) h d
  rw [Real.rpow_inv_natCast_pow (prod_nonneg (fun i _ => hz i)) hd.ne'] at hpow
  have prodz : ∏ i, z i = ∏ i, (1+x i) := by simp [z, Fintype.prod_sum_type]
  have sumz : ∑ i, z i = (d : ℝ) + ∑ i, x i := by
    simp [z, Fintype.sum_sum_type, Finset.sum_add_distrib, Nat.cast_sub hm]; ring
  rw [prodz, sumz, add_div, div_self (by positivity : (d : ℝ) ≠ 0)] at hpow
  exact hpow

private theorem linear_slope (L B E : ℝ) (h : ∀ t : ℝ, 0 < t → L * t ≤ B + E*t) : L ≤ E := by
  by_contra! hne
  let t := (|B|+1)/(L-E)
  have ht : 0 < t := div_pos (by positivity) (sub_pos.mpr hne)
  have he : t*(L-E) = |B|+1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hne.ne')
  have := h t ht
  nlinarith [le_abs_self B]

/-- Optimize the resulting one-variable bound by evaluating it at a positive point. -/
private theorem gurvits_bound {d : ℕ} (hd : 0 < d) (P S L : ℝ) (hS : 0 ≤ S)
    (h : ∀ t : ℝ, 0 < t → L * t ≤ P * (1 + t*S/d)^d) :
    (((d : ℝ) - 1) / d) ^ (d-1) * L ≤ P*S := by
  by_cases hd1 : d = 1
  · subst d
    simp only [Nat.cast_one, sub_self, zero_div, Nat.sub_self, pow_zero, one_mul]
    apply linear_slope L P (P*S)
    intro t ht
    simpa [mul_add, mul_left_comm, mul_comm, mul_assoc] using h t ht
  have hdR : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  let q := ((d : ℝ) - 1) / d
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  by_cases hs : S = 0
  · subst S
    have hL : L ≤ 0 := linear_slope L P 0 (by simpa using h)
    exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq.le _) hL).trans_eq (mul_zero _).symm
  have hsp := lt_of_le_of_ne hS (Ne.symm hs)
  let t := 1 / (q*S)
  have ht : 0 < t := by dsimp [t]; positivity
  have hfactor : 1 + t*S/d = q⁻¹ := by
    dsimp [t, q]
    field_simp [hs, show (d:ℝ)-1 ≠ 0 by linarith, show (d:ℝ) ≠ 0 by linarith]
    ring
  have he : t*q*S = 1 := by dsimp [t]; field_simp
  have H := h t ht
  rw [hfactor] at H
  have H' := mul_le_mul_of_nonneg_right H (pow_nonneg hq.le d)
  rw [mul_assoc P, ← mul_pow, inv_mul_cancel₀ hq.ne', one_pow, mul_one] at H'
  have hp : q^d = q^(d-1)*q := by rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hp] at H'
  have HH := mul_le_mul_of_nonneg_right H' hS
  change q^(d-1)*L ≤ _
  calc
    _ = (L*t*(q^(d-1)*q))*S := by linear_combination -(q^(d-1)*L)*he
    _ ≤ _ := HH

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H3 := by
  intro d m hd hm a r L D ha hr bound der
  classical
  have derivProd := (HasDerivAt.fun_finsetProd (u := (univ : Finset (Fin m)))
    (fun i _ => (hasDerivAt_id (0 : ℝ)).add_const (r i))).const_mul a
  have formula : D = a * ∑ i, ∏ j ∈ univ.erase i, r j := by
    simpa using der.unique derivProd
  have hD : 0 ≤ D := by rw [formula]; exact mul_nonneg ha (sum_nonneg fun _ _ => prod_nonneg fun j _ => hr j)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have coeff0 : 0 ≤ ((d : ℝ)-1)/d := by positivity
  by_cases hL : L ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg coeff0 _) hL).trans hD
  let P := a * ∏ i, r i
  by_cases hP : P = 0
  · have lim : Tendsto (fun t : ℝ => (a * ∏ i, (t+r i)) / t) (𝓝[>] 0) (𝓝 D) := by
      simpa [P, show a * ∏ i, r i = 0 from hP, div_eq_inv_mul] using der.tendsto_slope_zero_right
    have slope : L ≤ D := ge_of_tendsto lim (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (le_div_iff₀ ht).mpr (bound t ht))
    have hc : ((d : ℝ)-1)/d ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact (mul_le_of_le_one_left (le_of_not_ge hL) (pow_le_one₀ coeff0 hc)).trans slope
  have rpos (i : Fin m) : 0 < r i := by
    refine (hr i).lt_of_ne' ?_
    intro hi
    exact hP (by simp [P, Finset.prod_eq_zero (mem_univ i) hi])
  let S := ∑ i, (r i)⁻¹
  have hS : 0 ≤ S := sum_nonneg fun i _ => inv_nonneg.mpr (hr i)
  have Dformula : D = P*S := by
    rw [formula]
    dsimp [P,S]
    rw [mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← prod_erase_mul _ _ (mem_univ i), mul_assoc, mul_inv_cancel₀ (rpos i).ne', mul_one]
  rw [Dformula]
  apply gurvits_bound hd P S L hS
  intro t ht
  apply (bound t ht).trans
  have hfac (i : Fin m) : t + r i = r i * (1 + t*(r i)⁻¹) := by
    field_simp [(rpos i).ne']
    ring
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg ha (prod_nonneg fun i _ => hr i))
  simpa [S, Finset.mul_sum] using padded_amgm hd hm (fun i => t*(r i)⁻¹)
    (fun i => mul_nonneg ht.le (inv_nonneg.mpr (hr i)))
