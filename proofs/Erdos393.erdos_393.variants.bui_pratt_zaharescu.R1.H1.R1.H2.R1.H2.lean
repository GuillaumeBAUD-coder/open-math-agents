import OMAReductions.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1_H2_R1

/-!
Proof of `Erdos393.erdos_393.variants.bui_pratt_zaharescu.R1.H1.R1.H2.R1.H2`
(BPZ Lemma 5.4: algebraic nonvanishing of the 3x3 twisted Wronskian).

Using the 2x2 Wronskian reduction identity
`p 0 * det(table p) = W01 * step_v(W02) - W02 * step_u(W01)`,
the 3x3 nonvanishing reduces to three applications of a single 2x2 nonvanishing lemma
proved purely algebraically in `ℚ[X]` by comparing leading coefficients at the simple
poles `a = 1/k` (`k = u - 1` and `k = v - 1`).
-/

namespace OMA.Erdos393BPZNonvanishing

open Finset Polynomial

private noncomputable def Tpoly (r M : ℕ) : ℚ[X] :=
  C (r : ℚ) * ∏ k ∈ Icc 1 M, (1 - C (k : ℚ) * X)

private noncomputable def Apoly (M b : ℕ) : ℚ[X] :=
  ∑ k ∈ Ico 1 b, C (k : ℚ) * ∏ h ∈ (Icc 1 M).erase k, (1 - C (h : ℚ) * X)

private noncomputable def Dstep (r M b : ℕ) (p : ℚ[X]) : ℚ[X] :=
  Tpoly r M * derivative p + Apoly M b * p

private lemma Dstep_zero_eq (r M : ℕ) (p : ℚ[X]) :
    Dstep r M 0 p = Tpoly r M * derivative p := by
  simp [Dstep, Apoly]

private lemma Dstep_wronskian (r M b : ℕ) (p q : ℚ[X]) :
    Dstep r M b (p * Dstep r M b q - q * Dstep r M 0 p) =
      p * Dstep r M b (Dstep r M b q) - q * Dstep r M 0 (Dstep r M 0 p) := by
  simp only [Dstep, Apoly, Ico_eq_empty (by omega : ¬ 1 < 0), Finset.sum_empty, zero_mul, add_zero,
    derivative_sub, derivative_mul]
  ring

private lemma Tpoly_factor (r M k : ℕ) (hk : k ∈ Icc 1 M) :
    let U := ∏ h ∈ (Icc 1 M).erase k, (1 - C (h : ℚ) * X)
    Tpoly r M = C (-((r : ℚ) * (k : ℚ))) * (X - C ((k : ℚ)⁻¹)) * U := by
  intro U
  have hk0 : (k : ℚ) ≠ 0 := by
    have := (mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  have hlin : (1 - C (k : ℚ) * X : ℚ[X]) = C (-(k : ℚ)) * (X - C ((k : ℚ)⁻¹)) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hk0]
    simp only [map_neg, map_one]
    ring
  unfold Tpoly
  rw [← Finset.mul_prod_erase (Icc 1 M) (fun h => 1 - C (h : ℚ) * X) hk, hlin]
  simp only [map_neg, map_mul]
  ring

private lemma U_eval_ne_zero (M k : ℕ) (hk : k ∈ Icc 1 M) :
    (∏ h ∈ (Icc 1 M).erase k, (1 - C (h : ℚ) * X)).eval ((k : ℚ)⁻¹) ≠ 0 := by
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro h hh
  obtain ⟨hne, _⟩ := mem_erase.mp hh
  have hk0 : (k : ℚ) ≠ 0 := by
    have := (mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
  intro hzero
  have h1 : (h : ℚ) * (k : ℚ)⁻¹ = 1 := by linarith
  have h2 : (h : ℚ) = (k : ℚ) := by
    calc (h : ℚ) = (h : ℚ) * (k : ℚ)⁻¹ * (k : ℚ) := by field_simp
      _ = 1 * (k : ℚ) := by rw [h1]
      _ = (k : ℚ) := one_mul _
  exact hne (by exact_mod_cast h2)

private lemma Tpoly_eval_zero (r M k : ℕ) (hk : k ∈ Icc 1 M) :
    (Tpoly r M).eval ((k : ℚ)⁻¹) = 0 := by
  rw [Tpoly_factor r M k hk]
  simp

private lemma Apoly_eval_of_notMem (M b k : ℕ) (hk : k ∈ Icc 1 M) (hnot : k ∉ Ico 1 b) :
    (Apoly M b).eval ((k : ℚ)⁻¹) = 0 := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have := (mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  unfold Apoly
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hlk : k ∈ (Icc 1 M).erase l := mem_erase.mpr ⟨fun h => hnot (h ▸ hl), hk⟩
  rw [eval_mul, eval_C, eval_prod, Finset.prod_eq_zero hlk, mul_zero]
  simp [hk0]

private lemma Apoly_eval_of_mem (M b k : ℕ) (hk : k ∈ Icc 1 M) (hmem : k ∈ Ico 1 b) :
    (Apoly M b).eval ((k : ℚ)⁻¹) =
      (k : ℚ) * (∏ h ∈ (Icc 1 M).erase k, (1 - C (h : ℚ) * X)).eval ((k : ℚ)⁻¹) := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have := (mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  unfold Apoly
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single k]
  · simp
  · intro l hl hne
    have hlk : k ∈ (Icc 1 M).erase l := mem_erase.mpr ⟨hne.symm, hk⟩
    rw [eval_mul, eval_C, eval_prod, Finset.prod_eq_zero hlk, mul_zero]
    simp [hk0]
  · intro h; exact absurd hmem h

private lemma Dstep_mul_pow_linear (r M b k m : ℕ) (hk : k ∈ Icc 1 M) (f : ℚ[X]) :
    let a : ℚ := (k : ℚ)⁻¹
    let U : ℚ[X] := ∏ h ∈ (Icc 1 M).erase k, (1 - C (h : ℚ) * X)
    Dstep r M b ((X - C a) ^ m * f) =
      (X - C a) ^ m *
        ((C (-((r : ℚ) * (k : ℚ) * (m : ℚ))) * U + Apoly M b) * f + Tpoly r M * derivative f) := by
  intro a U
  have hT := Tpoly_factor r M k hk
  dsimp only [Dstep]
  rw [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one]
  rcases m with _ | m
  · simp
    ring
  · have hstep : Tpoly r M * (C ((m + 1 : ℕ) : ℚ) * (X - C a) ^ (m + 1 - 1) * f) =
        (X - C a) ^ (m + 1) * (C (-((r : ℚ) * (k : ℚ) * ((m + 1 : ℕ) : ℚ))) * U * f) := by
      rw [show m + 1 - 1 = m by omega, hT, pow_succ]
      simp only [map_neg, map_mul]
      ring
    rw [mul_add, hstep]
    ring

private lemma wronskian_two_ne_zero (r M b₁ b₂ k : ℕ) (hr : 2 ≤ r) (hk : k ∈ Icc 1 M)
    (h1 : k ∉ Ico 1 b₁) (h2 : k ∈ Ico 1 b₂) {p q : ℚ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * Dstep r M b₂ q - q * Dstep r M b₁ p ≠ 0 := by
  intro hzero
  have heq : p * Dstep r M b₂ q = q * Dstep r M b₁ p := sub_eq_zero.mp hzero
  set a : ℚ := (k : ℚ)⁻¹
  set U : ℚ[X] := ∏ h ∈ (Icc 1 M).erase k, (1 - C (h : ℚ) * X)
  obtain ⟨p₁, hp_eq, hp₁_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  obtain ⟨q₁, hq_eq, hq₁_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq a
  set mp := rootMultiplicity a p
  set mq := rootMultiplicity a q
  have hp₁_ne : p₁.eval a ≠ 0 := fun hz => hp₁_ndvd (Polynomial.dvd_iff_isRoot.mpr hz)
  have hq₁_ne : q₁.eval a ≠ 0 := fun hz => hq₁_ndvd (Polynomial.dvd_iff_isRoot.mpr hz)
  have hlin_ne : (X - C a : ℚ[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero a
  have hpow_ne : (X - C a : ℚ[X]) ^ (mp + mq) ≠ 0 := pow_ne_zero _ hlin_ne
  rw [hp_eq, hq_eq, Dstep_mul_pow_linear r M b₂ k mq hk q₁,
    Dstep_mul_pow_linear r M b₁ k mp hk p₁] at heq
  have hcancel : (X - C a) ^ (mp + mq) *
      (p₁ * ((C (-((r : ℚ) * (k : ℚ) * (mq : ℚ))) * U + Apoly M b₂) * q₁ +
        Tpoly r M * derivative q₁)) =
      (X - C a) ^ (mp + mq) *
      (q₁ * ((C (-((r : ℚ) * (k : ℚ) * (mp : ℚ))) * U + Apoly M b₁) * p₁ +
        Tpoly r M * derivative p₁)) := by
    rw [pow_add]
    calc ((X - C a) ^ mp * (X - C a) ^ mq) * _
        = ((X - C a) ^ mp * p₁) * ((X - C a) ^ mq *
            ((C (-((r : ℚ) * (k : ℚ) * (mq : ℚ))) * U + Apoly M b₂) * q₁ +
              Tpoly r M * derivative q₁)) := by ring
      _ = ((X - C a) ^ mq * q₁) * ((X - C a) ^ mp *
            ((C (-((r : ℚ) * (k : ℚ) * (mp : ℚ))) * U + Apoly M b₁) * p₁ +
              Tpoly r M * derivative p₁)) := heq
      _ = ((X - C a) ^ mp * (X - C a) ^ mq) * _ := by ring
  have hpoly := mul_left_cancel₀ hpow_ne hcancel
  have heval := congrArg (Polynomial.eval a) hpoly
  have hTa : (Tpoly r M).eval a = 0 := Tpoly_eval_zero r M k hk
  have hA1 : (Apoly M b₁).eval a = 0 := Apoly_eval_of_notMem M b₁ k hk h1
  have hA2 : (Apoly M b₂).eval a = (k : ℚ) * U.eval a := Apoly_eval_of_mem M b₂ k hk h2
  simp only [eval_mul, eval_add, eval_C, hTa, hA1, hA2, zero_mul, add_zero] at heval
  have hU_ne : U.eval a ≠ 0 := U_eval_ne_zero M k hk
  have hk_ne : (k : ℚ) ≠ 0 := by
    have := (mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  have hfac_ne : p₁.eval a * q₁.eval a * U.eval a * (k : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hp₁_ne hq₁_ne) hU_ne) hk_ne
  have hlin_q : (p₁.eval a * q₁.eval a * U.eval a * (k : ℚ)) *
      (1 - (r : ℚ) * (mq : ℚ) + (r : ℚ) * (mp : ℚ)) = 0 := by
    linarith
  have hrat : 1 - (r : ℚ) * (mq : ℚ) + (r : ℚ) * (mp : ℚ) = 0 :=
    (mul_eq_zero.mp hlin_q).resolve_left hfac_ne
  have hint : ((r : ℤ) * ((mq : ℤ) - (mp : ℤ)) : ℚ) = 1 := by
    push_cast; linarith
  have hint' : (r : ℤ) * ((mq : ℤ) - (mp : ℤ)) = 1 := by exact_mod_cast hint
  have hdvd : (r : ℤ) ∣ 1 := ⟨(mq : ℤ) - (mp : ℤ), hint'.symm⟩
  have hle : (r : ℤ).natAbs ≤ 1 := Nat.le_of_dvd (by decide) (Int.natAbs_dvd_natAbs.mpr hdvd)
  omega

end OMA.Erdos393BPZNonvanishing

theorem OMA.solution :
    OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1_H2_R1.H2 := by
  intro r M u v hr hu huv hv hru hrv T β step table p hp
  have hu2 : 2 ≤ u := by
    have := Nat.le_of_dvd hu hru
    omega
  have hv_gap : u + 2 ≤ v := by
    have hsub : r ∣ v - u := Nat.dvd_sub hrv hru
    have hpos : 0 < v - u := by omega
    have := Nat.le_of_dvd hpos hsub
    omega
  set W01 : Polynomial ℚ := p 0 * OMA.Erdos393BPZNonvanishing.Dstep r M u (p 1) -
    p 1 * OMA.Erdos393BPZNonvanishing.Dstep r M 0 (p 0)
  set W02 : Polynomial ℚ := p 0 * OMA.Erdos393BPZNonvanishing.Dstep r M v (p 2) -
    p 2 * OMA.Erdos393BPZNonvanishing.Dstep r M 0 (p 0)
  have hW01 : W01 ≠ 0 :=
    OMA.Erdos393BPZNonvanishing.wronskian_two_ne_zero r M 0 u (u - 1) hr
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (by simp) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) (hp 0) (hp 1)
  have hW02 : W02 ≠ 0 :=
    OMA.Erdos393BPZNonvanishing.wronskian_two_ne_zero r M 0 v (v - 1) hr
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (by simp) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) (hp 0) (hp 2)
  have hW3 : W01 * OMA.Erdos393BPZNonvanishing.Dstep r M v W02 -
      W02 * OMA.Erdos393BPZNonvanishing.Dstep r M u W01 ≠ 0 :=
    OMA.Erdos393BPZNonvanishing.wronskian_two_ne_zero r M u v (v - 1) hr
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (by simp only [Finset.mem_Ico]; omega)
      (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hW01 hW02
  have hdet_eq :
      p 0 * (table p).det =
      W01 * OMA.Erdos393BPZNonvanishing.Dstep r M v W02 -
        W02 * OMA.Erdos393BPZNonvanishing.Dstep r M u W01 := by
    have hstep_eq : ∀ j : Fin 3, step j = OMA.Erdos393BPZNonvanishing.Dstep r M (β j) := fun _ => rfl
    have hb0 : β 0 = 0 := rfl
    have hb1 : β 1 = u := rfl
    have hb2 : β 2 = v := rfl
    have hf0 : (0 : Fin 3).val = 0 := rfl
    have hf1 : (1 : Fin 3).val = 1 := rfl
    have hf2 : (2 : Fin 3).val = 2 := rfl
    dsimp only [table]
    rw [OMA.Erdos393BPZNonvanishing.Dstep_wronskian r M u (p 0) (p 1),
      OMA.Erdos393BPZNonvanishing.Dstep_wronskian r M v (p 0) (p 2),
      Matrix.det_fin_three]
    simp only [Matrix.of_apply, hstep_eq, hb0, hb1, hb2, hf0, hf1, hf2,
      Function.iterate_zero, id_eq, Function.iterate_succ, Function.comp_apply, W01, W02]
    ring
  intro hdet
  apply hW3
  rw [← hdet_eq, hdet, mul_zero]
