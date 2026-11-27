import OMAReductions.R_Erdos499_vanDerWaerden_R1

-- Step Erdos499.vanDerWaerden.R1.H3: hypothesis H3 of reduction Erdos499.vanDerWaerden.R1
-- Credit: @LordMike
-- H3 := univariate Gurvits inequality: if L * t <= a * prod_{i<m} (t + r i) for all t > 0 (a >= 0,
-- r i >= 0, m <= d, d >= 1) and D is the derivative at 0 of that product, then
-- ((d-1)/d)^(d-1) * L <= D.
-- Proof idea: D = a * sum_i prod_{j != i} r j. If some r i0 = 0 then L <= a * prod_{j != i0} r j <= D
-- by letting t -> 0. Otherwise the weighted AM-GM / optimal-t argument gives the bound with m factors,
-- and ((d-1)/d)^(d-1) is decreasing in d, so the bound with d follows.

open Finset Filter Topology

namespace OMA

/-- AM-GM in power form. -/
lemma h3_prod_le_avg_pow {k : ℕ} (hk : 0 < k) (z : Fin k → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / k) ^ k := by
  have h := Real.geom_mean_le_arith_mean (univ : Finset (Fin k)) (fun _ => (1:ℝ)) z
    (fun _ _ => zero_le_one) (by simp [hk]) (fun i _ => hz i)
  simp only [Real.rpow_one, one_mul, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  have hP : 0 ≤ ∏ i, z i := prod_nonneg fun i _ => hz i
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  calc ∏ i, z i = ((∏ i, z i) ^ ((k:ℝ))⁻¹) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hkr.ne', Real.rpow_one]
    _ ≤ ((∑ i, z i) / k) ^ k :=
        pow_le_pow_left₀ (Real.rpow_nonneg hP _) h k

/-- prod (1 + t / r i) bound. -/
lemma h3_one_add_bound {k : ℕ} (hk : 0 < k) (r : Fin k → ℝ) (hr : ∀ i, 0 < r i) (t : ℝ)
    (ht : 0 ≤ t) :
    ∏ i, (1 + t / r i) ≤ (1 + t * (∑ i, 1 / r i) / k) ^ k := by
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  refine (h3_prod_le_avg_pow hk _ fun i => by have := hr i; positivity).trans_eq ?_
  congr 1
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_sum]
  field_simp

/-- Optimal choice of `t`. -/
lemma h3_opt_t {k : ℕ} (hk : 2 ≤ k) (a0 a1 : ℝ) (h0 : 0 < a0) (h1 : 0 < a1) :
    let t := k * a0 / ((k - 1) * a1)
    0 < t ∧ a0 * (1 + a1 * t / (k * a0)) ^ k / t = a1 * ((k:ℝ) / (k - 1)) ^ (k - 1) := by
  intro t
  have hk1 : (1:ℝ) < k := by exact_mod_cast hk
  have hkm : (0:ℝ) < k - 1 := by linarith
  have hkp : (0:ℝ) < k := by linarith
  refine ⟨by positivity, ?_⟩
  have e : 1 + a1 * t / (k * a0) = (k:ℝ) / (k - 1) := by
    simp only [t]; field_simp; ring
  rw [e]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ, t]
  push_cast at hkm ⊢
  field_simp

/-- Derivative of `a * prod (t + r i)` at `0`. -/
lemma h3_deriv_formula {m : ℕ} (a : ℝ) (r : Fin m → ℝ) (D : ℝ)
    (h : HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0) :
    D = a * ∑ i, ∏ j ∈ univ.erase i, r j := by
  have h1 : HasDerivAt (fun t : ℝ => ∏ i, (t + r i))
      (∑ i, (∏ j ∈ univ.erase i, (0 + r j)) • (1:ℝ)) 0 :=
    HasDerivAt.fun_finsetProd (fun i _ => (hasDerivAt_id' (0:ℝ)).add_const (r i))
  have h2 := h.unique (h1.const_mul a)
  simpa [smul_eq_mul] using h2

lemma h3_D_nonneg {m : ℕ} (a : ℝ) (r : Fin m → ℝ) (ha : 0 ≤ a) (hr : ∀ i, 0 ≤ r i) :
    0 ≤ a * ∑ i, ∏ j ∈ univ.erase i, r j :=
  mul_nonneg ha (sum_nonneg fun i _ => prod_nonneg fun j _ => hr j)

/-- Zero case: if `r i0 = 0`, then `L ≤ a * prod_{j ≠ i0} r j` (limit `t → 0`). -/
lemma h3_zero_case {m : ℕ} (a L : ℝ) (r : Fin m → ℝ) (i0 : Fin m) (hi0 : r i0 = 0)
    (h : ∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) :
    L ≤ a * ∏ j ∈ univ.erase i0, r j := by
  have hq : ∀ t : ℝ, 0 < t → L ≤ a * ∏ j ∈ univ.erase i0, (t + r j) := by
    intro t ht
    have h1 := h t ht
    have hprod : ∏ i, (t + r i) = (t + r i0) * ∏ j ∈ univ.erase i0, (t + r j) :=
      (Finset.mul_prod_erase univ (fun i => t + r i) (mem_univ i0)).symm
    rw [hprod, hi0, add_zero] at h1
    have e : a * (t * ∏ j ∈ univ.erase i0, (t + r j)) =
        (a * ∏ j ∈ univ.erase i0, (t + r j)) * t := by ring
    rw [e] at h1
    exact le_of_mul_le_mul_right h1 ht
  have hcont : Continuous (fun t : ℝ => a * ∏ j ∈ univ.erase i0, (t + r j)) := by
    fun_prop
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), L ≤ a * ∏ j ∈ univ.erase i0, (t + r j) :=
    eventually_nhdsWithin_of_forall fun t ht => hq t ht
  have := ge_of_tendsto hlim hev
  simpa using this

/-- AM-GM with `p+1` terms (one term `1`, `p` terms `(p+1)/p`). -/
lemma h3_amgm_step (p : ℕ) (hp : 1 ≤ p) :
    (((p:ℝ)+1)/p)^p ≤ (((p:ℝ)+2)/((p:ℝ)+1))^(p+1) := by
  have hpr : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp0 : (p:ℝ) ≠ 0 := hpr.ne'
  let z : Fin (p+1) → ℝ := fun i => if (i:ℕ) = 0 then 1 else ((p:ℝ)+1)/p
  have hz : ∀ i, 0 ≤ z i := fun i => by
    simp only [z]
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (by linarith) hpr.le
  have h := h3_prod_le_avg_pow (by omega : 0 < p + 1) z hz
  have hprod : ∏ i, z i = (((p:ℝ)+1)/p)^p := by
    rw [Fin.prod_univ_succ]
    simp [z, Fin.succ_ne_zero, div_pow]
  have hsum : ∑ i, z i = (p:ℝ) + 2 := by
    rw [Fin.sum_univ_succ]
    simp [z, Fin.succ_ne_zero]
    field_simp
    ring
  rw [hprod, hsum] at h
  push_cast at h
  exact h

lemma h3_g_step (n : ℕ) (hn : 1 ≤ n) :
    ((((n+1 : ℕ):ℝ) - 1) / ((n+1 : ℕ):ℝ)) ^ (n+1-1) ≤ (((n:ℝ) - 1) / n) ^ (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hp : 1 ≤ p := by omega
    have hpr : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have A := h3_amgm_step p hp
    rw [show p + 1 + 1 - 1 = p + 1 by omega, show p + 1 - 1 = p by omega]
    push_cast
    have e1 : ((p:ℝ)+1+1-1)/((p:ℝ)+1+1) = (((p:ℝ)+2)/((p:ℝ)+1))⁻¹ := by
      rw [inv_div]; ring
    have e2 : ((p:ℝ)+1-1)/((p:ℝ)+1) = (((p:ℝ)+1)/(p:ℝ))⁻¹ := by
      rw [inv_div]; ring
    rw [e1, e2, inv_pow, inv_pow]
    exact inv_anti₀ (pow_pos (div_pos (by linarith) hpr) _) A

lemma h3_g_anti (m d : ℕ) (hm : 1 ≤ m) (hmd : m ≤ d) :
    (((d:ℝ)-1)/d)^(d-1) ≤ (((m:ℝ)-1)/m)^(m-1) := by
  induction d, hmd using Nat.le_induction with
  | base => exact le_refl _
  | succ n hmn ih => exact le_trans (h3_g_step n (by omega)) ih

/-- Positive core: all `r i > 0`, `a > 0`, `k ≥ 2` factors. -/
lemma h3_core_pos {k : ℕ} (hk : 2 ≤ k) (a L D : ℝ) (r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (ha : 0 < a) (hD : D = a * ∑ i, ∏ j ∈ univ.erase i, r j)
    (h : ∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) :
    (((k:ℝ) - 1) / k) ^ (k - 1) * L ≤ D := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hPpos : 0 < ∏ i, r i := prod_pos fun i _ => hr i
  have hsum : ∑ i, ∏ j ∈ univ.erase i, r j = (∏ i, r i) * ∑ i, 1 / r i := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← prod_erase_mul univ r (mem_univ i)]
    have := (hr i).ne'
    field_simp
  have hDS : D = (a * ∏ i, r i) * ∑ i, 1 / r i := by
    rw [hD, hsum]; ring
  have ha0 : 0 < a * ∏ i, r i := mul_pos ha hPpos
  have hS : 0 < ∑ i, 1 / r i := sum_pos (fun i _ => by have := hr i; positivity) univ_nonempty
  have ha1 : 0 < D := by rw [hDS]; exact mul_pos ha0 hS
  have key : ∀ t : ℝ, 0 < t → L * t ≤ (a * ∏ i, r i) * (1 + D * t / (k * (a * ∏ i, r i))) ^ k := by
    intro t ht
    have h1 := h t ht
    have h2 : ∏ i, (t + r i) = (∏ i, r i) * ∏ i, (1 + t / r i) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      have := (hr i).ne'
      field_simp
      ring
    have h3 := h3_one_add_bound (by omega) r hr t ht.le
    have hk0 : (k:ℝ) ≠ 0 := by
      have : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      exact this.ne'
    have h4 : 1 + t * (∑ i, 1 / r i) / k = 1 + D * t / (k * (a * ∏ i, r i)) := by
      rw [hDS]
      have : a * ∏ i, r i ≠ 0 := ha0.ne'
      field_simp
    calc L * t ≤ a * ∏ i, (t + r i) := h1
      _ = (a * ∏ i, r i) * ∏ i, (1 + t / r i) := by rw [h2]; ring
      _ ≤ (a * ∏ i, r i) * (1 + t * (∑ i, 1 / r i) / k) ^ k :=
          mul_le_mul_of_nonneg_left h3 ha0.le
      _ = (a * ∏ i, r i) * (1 + D * t / (k * (a * ∏ i, r i))) ^ k := by rw [h4]
  obtain ⟨htpos, heq⟩ := h3_opt_t hk (a * ∏ i, r i) D ha0 ha1
  have hL2 : L ≤ D * ((k:ℝ) / ((k:ℝ) - 1)) ^ (k - 1) := by
    rw [← heq]
    exact (le_div_iff₀ htpos).mpr (key _ htpos)
  have hk1 : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hc : (((k:ℝ) - 1) / k) * ((k:ℝ) / ((k:ℝ) - 1)) = 1 := by
    have : (k:ℝ) - 1 ≠ 0 := by linarith
    have : (k:ℝ) ≠ 0 := by linarith
    field_simp
  calc (((k:ℝ) - 1) / k) ^ (k - 1) * L
      ≤ (((k:ℝ) - 1) / k) ^ (k - 1) * (D * ((k:ℝ) / ((k:ℝ) - 1)) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hL2 (pow_nonneg (div_nonneg (by linarith) (by linarith)) _)
    _ = D * ((((k:ℝ) - 1) / k) * ((k:ℝ) / ((k:ℝ) - 1))) ^ (k - 1) := by rw [mul_pow]; ring
    _ = D := by rw [hc, one_pow, mul_one]

/-- The statement of H3. -/
lemma h3_main : ∀ (d m : ℕ), 1 ≤ d → m ≤ d → ∀ (a : ℝ) (r : Fin m → ℝ) (L D : ℝ), 0 ≤ a → (∀ i, 0 ≤ r i) →
    (∀ t : ℝ, 0 < t → L * t ≤ a * ∏ i, (t + r i)) →
    HasDerivAt (fun t : ℝ => a * ∏ i, (t + r i)) D 0 →
    (((d : ℝ) - 1) / d) ^ (d - 1) * L ≤ D := by
  intro d m hd hmd a r L D ha hr hL hder
  have hDf := h3_deriv_formula a r D hder
  have hD0 : 0 ≤ D := hDf ▸ h3_D_nonneg a r ha hr
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hg0 : 0 ≤ (((d:ℝ)-1)/d)^(d-1) :=
    pow_nonneg (div_nonneg (by linarith) hdpos.le) _
  have hg1 : (((d:ℝ)-1)/d)^(d-1) ≤ 1 :=
    pow_le_one₀ (div_nonneg (by linarith) hdpos.le) ((div_le_one hdpos).mpr (by linarith))
  rcases le_or_gt L 0 with hL0 | hLpos
  · have := mul_nonneg hg0 (neg_nonneg.mpr hL0)
    linarith
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exfalso
      subst hm0
      have h1 := hL ((a + 1) / L) (div_pos (by linarith) hLpos)
      have e : L * ((a + 1) / L) = a + 1 := by field_simp
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h1
      rw [e] at h1
      linarith
    · by_cases hz : ∃ i0, r i0 = 0
      · obtain ⟨i0, hi0⟩ := hz
        have hle := h3_zero_case a L r i0 hi0 hL
        have hLD : L ≤ D := by
          rw [hDf]
          refine hle.trans (mul_le_mul_of_nonneg_left ?_ ha)
          exact single_le_sum (f := fun i => ∏ j ∈ univ.erase i, r j)
            (fun i _ => prod_nonneg fun j _ => hr j) (mem_univ i0)
        calc (((d:ℝ)-1)/d)^(d-1) * L ≤ 1 * L := mul_le_mul_of_nonneg_right hg1 hLpos.le
          _ ≤ D := by linarith
      · push_neg at hz
        have hpos : ∀ i, 0 < r i := fun i => lt_of_le_of_ne (hr i) (hz i).symm
        have ha' : 0 < a := by
          rcases lt_or_eq_of_le ha with h | h
          · exact h
          · exfalso
            have := hL 1 one_pos
            rw [← h] at this
            simp at this
            linarith
        by_cases hm1 : m = 1
        · subst hm1
          have hDa : D = a := by rw [hDf]; simp
          have hLa : L ≤ a := by
            by_contra hcon
            push_neg at hcon
            have hLa' : 0 < L - a := by linarith
            have ht : 0 < (a * r 0 + 1) / (L - a) :=
              div_pos (by have := mul_nonneg ha (hr 0); linarith) hLa'
            have hh := hL _ ht
            rw [Fin.prod_univ_one] at hh
            have e : (L - a) * ((a * r 0 + 1) / (L - a)) = a * r 0 + 1 := by
              field_simp
            nlinarith
          have : (((d:ℝ)-1)/d)^(d-1) * L ≤ 1 * L := mul_le_mul_of_nonneg_right hg1 hLpos.le
          linarith
        · have hm2 : 2 ≤ m := by omega
          have hcore := h3_core_pos hm2 a L D r hpos ha' (hDf) hL
          have hmono := h3_g_anti m d hmpos hmd
          calc (((d:ℝ)-1)/d)^(d-1) * L ≤ (((m:ℝ)-1)/m)^(m-1) * L :=
                mul_le_mul_of_nonneg_right hmono hLpos.le
            _ ≤ D := hcore

end OMA

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H3 := OMA.h3_main
