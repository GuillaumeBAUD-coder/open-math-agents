import OMAStatements.S_oeis_a001936
import Mathlib

namespace OMA.S_oeis_a001936_Proof

open Polynomial PowerSeries PowerSeries.WithPiTopology Finset

/-! ### Part 1: Generating function identity `R ^ 2 = E ^ 6` in `(ZMod 4)⟦X⟧` -/

private lemma one_sub_pow_four_eq_zmod4 (y : (ZMod 4)⟦X⟧) :
    (1 - y) ^ 4 = (1 - y ^ 2) ^ 2 := by
  have h4 : (4 : (ZMod 4)⟦X⟧) = 0 := by
    have hz : (4 : ZMod 4) = 0 := rfl
    rw [← map_ofNat (PowerSeries.C (R := ZMod 4)) 4, hz, map_zero]
  have hsub : (1 - y) ^ 4 - (1 - y ^ 2) ^ 2 = 4 * (-y + 2 * y ^ 2 - y ^ 3) := by ring
  rw [h4, zero_mul] at hsub
  exact sub_eq_zero.mp hsub

private lemma one_sub_X_pow_four_sq_zmod4 (m : ℕ) :
    (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (4 * m)) ^ 2 =
      (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ m) ^ 8 := by
  have h1 : (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (4 * m)) ^ 2 =
      (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (2 * m)) ^ 4 := by
    rw [show 4 * m = 2 * m * 2 by ring, pow_mul]
    exact (one_sub_pow_four_eq_zmod4 (PowerSeries.X ^ (2 * m))).symm
  have h2 : (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (2 * m)) ^ 4 =
      ((1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ m) ^ 4) ^ 2 := by
    rw [show 2 * m = m * 2 by ring, pow_mul]
    rw [show (1 - ((PowerSeries.X : (ZMod 4)⟦X⟧) ^ m) ^ 2) ^ 4 =
        ((1 - ((PowerSeries.X : (ZMod 4)⟦X⟧) ^ m) ^ 2) ^ 2) ^ 2 by ring]
    rw [← one_sub_pow_four_eq_zmod4 (PowerSeries.X ^ m)]
  rw [h1, h2, ← pow_mul]

private noncomputable def R_series : (ZMod 4)⟦X⟧ :=
  PowerSeries.mk fun n => (OMA.S_oeis_a001936.restrictedCount n : ZMod 4)

private lemma R_sq_eq_E_pow_six :
    R_series * R_series = (pentagonalSeries (ZMod 4)) ^ 6 := by
  let _ : TopologicalSpace (ZMod 4) := ⊥
  have _ : DiscreteTopology (ZMod 4) := ⟨rfl⟩
  set E : (ZMod 4)⟦X⟧ := pentagonalSeries (ZMod 4)
  have hE_tprod : E = ∏' i : ℕ, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1)) :=
    (tprod_one_sub_X_pow (ZMod 4)).symm
  have hR_tprod : R_series = ∏' i : ℕ,
      if ¬ 4 ∣ (i + 1) then ∑' j : ℕ, ((PowerSeries.X : (ZMod 4)⟦X⟧) ^ ((i + 1) * j)) else 1 := by
    have := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod (ZMod 4) (fun i => ¬ 4 ∣ i)
    simpa [R_series, OMA.S_oeis_a001936.restrictedCount] using this
  have hmR : Multipliable (fun i : ℕ =>
      if ¬ 4 ∣ (i + 1) then ∑' j : ℕ, ((PowerSeries.X : (ZMod 4)⟦X⟧) ^ ((i + 1) * j)) else 1) := by
    simpa using Nat.Partition.multipliable_powerSeriesMk_card_restricted (ZMod 4) (fun i => ¬ 4 ∣ i)
  have hmE : Multipliable (fun i : ℕ => (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))) :=
    multipliable_one_sub_X_pow (ZMod 4)
  set f : ℕ → (ZMod 4)⟦X⟧ := fun i =>
    if 4 ∣ (i + 1) then (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1)) else 1 with hf_def
  have hfg : ∀ i : ℕ,
      (if ¬ 4 ∣ (i + 1) then ∑' j : ℕ, ((PowerSeries.X : (ZMod 4)⟦X⟧) ^ ((i + 1) * j)) else 1) *
        (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1)) = f i := by
    intro i
    by_cases h4 : 4 ∣ (i + 1)
    · simp [hf_def, h4]
    · simp only [hf_def, h4, not_false_eq_true, ↓reduceIte]
      have hgeom := tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (R := ZMod 4)
        (f := ((PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))) (by simp)
      simpa [pow_mul] using hgeom
  have hRE : R_series * E = ∏' i : ℕ, f i := by
    rw [hR_tprod, hE_tprod, ← hmR.tprod_mul hmE]
    exact tprod_congr hfg
  have hmf : Multipliable f := by
    have hm := hmR.mul hmE
    exact hm.congr hfg
  have hRE_sq : (R_series * E) ^ 2 = ∏' i : ℕ, f i ^ 2 := by
    rw [sq, hRE, ← hmf.tprod_mul hmf]
    exact tprod_congr fun i => (sq (f i)).symm
  have hE2 : E ^ 2 = ∏' k : ℕ, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (k + 1)) ^ 2 := by
    rw [sq, hE_tprod, ← hmE.tprod_mul hmE]
    exact tprod_congr fun k => (sq _).symm
  have hmE2 : Multipliable (fun k : ℕ => (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (k + 1)) ^ 2) :=
    (hmE.mul hmE).congr fun k => (sq _).symm
  have hE4 : E ^ 4 = ∏' k : ℕ, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (k + 1)) ^ 4 := by
    rw [show E ^ 4 = E ^ 2 * E ^ 2 by ring, hE2, ← hmE2.tprod_mul hmE2]
    exact tprod_congr fun k => by rw [← pow_add]
  have hmE4 : Multipliable (fun k : ℕ => (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (k + 1)) ^ 4) :=
    (hmE2.mul hmE2).congr fun k => by rw [← pow_add]
  have hE8 : E ^ 8 = ∏' k : ℕ, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (k + 1)) ^ 8 := by
    rw [show E ^ 8 = E ^ 4 * E ^ 4 by ring, hE4, ← hmE4.tprod_mul hmE4]
    exact tprod_congr fun k => by rw [← pow_add]
  have h4k : E ^ 8 = ∏' k : ℕ, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (4 * (k + 1))) ^ 2 := by
    rw [hE8]
    exact tprod_congr fun k => (one_sub_X_pow_four_sq_zmod4 (k + 1)).symm
  have hreindex : ∏' k : ℕ, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (4 * (k + 1))) ^ 2 =
      ∏' i : ℕ, f i ^ 2 := by
    have hcomp : (fun k : ℕ => (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (4 * (k + 1))) ^ 2) =
        (fun i : ℕ => f i ^ 2) ∘ (fun k : ℕ => 4 * k + 3) := by
      ext k
      simp [hf_def, show 4 * k + 3 + 1 = 4 * (k + 1) by omega]
    rw [hcomp]
    have hinj : Function.Injective (fun k : ℕ => 4 * k + 3) := fun a b h => by
      dsimp only at h; omega
    refine hinj.tprod_eq (f := fun i : ℕ => f i ^ 2) fun i hi => ?_
    rw [Function.mem_mulSupport] at hi
    have h4 : 4 ∣ (i + 1) := by
      by_contra hnd
      apply hi
      simp [hf_def, hnd]
    obtain ⟨m, hm⟩ := h4
    rcases m with _ | m
    · omega
    · exact ⟨m, by dsimp only; omega⟩
  have hsq : (R_series * E) ^ 2 = E ^ 8 := by
    rw [hRE_sq, ← hreindex, ← h4k]
  have hE_unit : IsUnit E := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff]
    have h0 : PowerSeries.coeff 0 (pentagonalSeries (ZMod 4)) = 1 := by
      have hp0 : pentagonal (0 : ℤ) = 0 := by
        have := two_mul_natCast_pentagonal (0 : ℤ)
        omega
      rw [← hp0, PowerSeries.coeff_pentagonalSeries_pentagonal]
      simp
    rw [show E = pentagonalSeries (ZMod 4) from rfl, h0]
    exact isUnit_one
  have hE2_unit : IsUnit (E ^ 2) := hE_unit.pow 2
  have hmul : (R_series * R_series) * E ^ 2 = E ^ 6 * E ^ 2 := by
    calc (R_series * R_series) * E ^ 2 = (R_series * E) ^ 2 := by ring
      _ = E ^ 8 := hsq
      _ = E ^ 6 * E ^ 2 := by ring
  exact hE2_unit.mul_right_cancel hmul

/-! ### Part 2: Finite algebraic proof of Jacobi cubic identity in `Polynomial ℤ` -/

private noncomputable abbrev qP : Polynomial ℤ := Polynomial.X
private noncomputable abbrev ZP : (Polynomial ℤ)[X] := Polynomial.X

private noncomputable def facP (m : ℕ) : (Polynomial ℤ)[X] :=
  (1 + Polynomial.C (qP ^ (2 * m - 1)) * ZP) * (ZP + Polynomial.C (qP ^ (2 * m - 1)))

private noncomputable def P_poly (N : ℕ) : (Polynomial ℤ)[X] :=
  ∏ m ∈ Finset.Icc 1 N, facP m

private noncomputable def Q_poly (N : ℕ) : (Polynomial ℤ)[X] :=
  (1 + Polynomial.C qP * ZP) * ∏ m ∈ Finset.Icc 2 N, facP m

private noncomputable def piPoly (m : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.Icc 1 m, (1 - qP ^ (2 * j))

private lemma P_poly_succ (N : ℕ) : P_poly (N + 1) = P_poly N * facP (N + 1) := by
  unfold P_poly
  rw [show Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.prod_insert (by simp)]
  ring

private lemma facP_expand (m : ℕ) :
    facP m = Polynomial.C (qP ^ (2 * m - 1)) * ZP ^ 2 +
      Polynomial.C (1 + (qP ^ (2 * m - 1)) ^ 2) * ZP +
      Polynomial.C (qP ^ (2 * m - 1)) := by
  unfold facP
  simp only [map_add, map_one, map_pow]
  ring

private lemma coeff_mul_symm_quad (f : (Polynomial ℤ)[X]) (a b : Polynomial ℤ) (N : ℕ)
    (hdeg : ∀ k, 2 * N < k → f.coeff k = 0)
    (hsym : ∀ k ≤ 2 * N, f.coeff (2 * N - k) = f.coeff k) :
    let g := f * (Polynomial.C a * ZP ^ 2 + Polynomial.C b * ZP + Polynomial.C a)
    (∀ k, 2 * (N + 1) < k → g.coeff k = 0) ∧
    (∀ k ≤ 2 * (N + 1), g.coeff (2 * (N + 1) - k) = g.coeff k) ∧
    g.coeff (2 * (N + 1)) = f.coeff (2 * N) * a := by
  intro g
  have hg_coeff : ∀ k : ℕ, g.coeff k =
      (if 2 ≤ k then f.coeff (k - 2) * a else 0) +
      (if 1 ≤ k then f.coeff (k - 1) * b else 0) +
      f.coeff k * a := by
    intro k
    have hexp : g = f * Polynomial.C a * ZP ^ 2 + f * Polynomial.C b * ZP ^ 1 + f * Polynomial.C a := by
      dsimp only [g]; ring
    rw [hexp, coeff_add, coeff_add, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_X_pow',
      Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hg_coeff]
    have h0 : f.coeff k = 0 := hdeg k (by omega)
    have h1 : f.coeff (k - 1) = 0 := hdeg (k - 1) (by omega)
    have h2 : f.coeff (k - 2) = 0 := hdeg (k - 2) (by omega)
    simp [h0, h1, h2]
  · intro k hk
    rw [hg_coeff (2 * (N + 1) - k), hg_coeff k]
    have t1 : (if 2 ≤ 2 * (N + 1) - k then f.coeff (2 * (N + 1) - k - 2) * a else 0) =
        f.coeff k * a := by
      by_cases hle : k ≤ 2 * N
      · rw [if_pos (by omega), show 2 * (N + 1) - k - 2 = 2 * N - k by omega, hsym k hle]
      · rw [if_neg (by omega), hdeg k (by omega), zero_mul]
    have t2 : (if 1 ≤ 2 * (N + 1) - k then f.coeff (2 * (N + 1) - k - 1) * b else 0) =
        (if 1 ≤ k then f.coeff (k - 1) * b else 0) := by
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos (by omega), if_neg (by omega), hdeg (2 * (N + 1) - 0 - 1) (by omega), zero_mul]
      · by_cases hk2 : k = 2 * (N + 1)
        · subst hk2
          rw [if_neg (by omega), if_pos (by omega), hdeg (2 * (N + 1) - 1) (by omega), zero_mul]
        · rw [if_pos (by omega), if_pos (by omega),
            show 2 * (N + 1) - k - 1 = 2 * N - (k - 1) by omega, hsym (k - 1) (by omega)]
    have t3 : f.coeff (2 * (N + 1) - k) * a =
        (if 2 ≤ k then f.coeff (k - 2) * a else 0) := by
      by_cases h2 : 2 ≤ k
      · rw [if_pos h2, show 2 * (N + 1) - k = 2 * N - (k - 2) by omega, hsym (k - 2) (by omega)]
      · rw [if_neg h2, hdeg (2 * (N + 1) - k) (by omega), zero_mul]
    rw [t1, t2, t3]
    ring
  · rw [hg_coeff (2 * (N + 1))]
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show 2 * (N + 1) - 2 = 2 * N by omega]
    rw [hdeg (2 * (N + 1) - 1) (by omega), hdeg (2 * (N + 1)) (by omega)]
    simp

private lemma P_poly_props (N : ℕ) :
    (∀ k, 2 * N < k → (P_poly N).coeff k = 0) ∧
    (∀ k ≤ 2 * N, (P_poly N).coeff (2 * N - k) = (P_poly N).coeff k) ∧
    (P_poly N).coeff (2 * N) = qP ^ (N ^ 2) := by
  induction N with
  | zero =>
    have h0 : P_poly 0 = 1 := by simp [P_poly]
    rw [h0]
    refine ⟨?_, ?_, by simp⟩
    · intro k hk; rw [Polynomial.coeff_one, if_neg (by omega)]
    · intro k hk
      have hk0 : k = 0 := by omega
      rw [hk0]
  | succ N ih =>
    rcases ih with ⟨hdeg, hsym, htop⟩
    rw [P_poly_succ, facP_expand]
    have h := coeff_mul_symm_quad (P_poly N) (qP ^ (2 * (N + 1) - 1))
      (1 + (qP ^ (2 * (N + 1) - 1)) ^ 2) N hdeg hsym
    refine ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2, htop, ← pow_add]
    congr 1
    have : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
    rw [this]; ring

private lemma P_poly_func_eq (N : ℕ) (hN : 1 ≤ N) :
    Polynomial.C qP * (ZP + Polynomial.C (qP ^ (2 * N - 1))) *
      (P_poly N).comp (Polynomial.C (qP ^ 2) * ZP) =
    Polynomial.C (qP ^ (2 * N)) * (1 + Polynomial.C (qP ^ (2 * N + 1)) * ZP) * P_poly N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hP1 : P_poly 1 = facP 1 := by simp [P_poly]
    rw [hP1]
    unfold facP
    simp only [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.one_comp, Polynomial.C_comp,
      Polynomial.X_comp]
    simp only [map_pow]
    ring
  | succ N hN ih =>
    rw [P_poly_succ, Polynomial.mul_comp]
    have hfac_comp : (facP (N + 1)).comp (Polynomial.C (qP ^ 2) * ZP) =
        Polynomial.C (qP ^ 2) * (1 + Polynomial.C (qP ^ (2 * (N + 1) + 1)) * ZP) *
        (ZP + Polynomial.C (qP ^ (2 * N - 1))) := by
      unfold facP
      simp only [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.one_comp, Polynomial.C_comp,
        Polynomial.X_comp]
      have e1 : 2 * (N + 1) - 1 = (2 * N - 1) + 2 := by omega
      have e2 : 2 * (N + 1) + 1 = (2 * N - 1) + 4 := by omega
      rw [e1, e2, pow_add, pow_add]
      simp only [map_mul, map_pow]
      ring
    rw [hfac_comp]
    have hstep : Polynomial.C qP * (ZP + Polynomial.C (qP ^ (2 * (N + 1) - 1))) *
        ((P_poly N).comp (Polynomial.C (qP ^ 2) * ZP) *
          (Polynomial.C (qP ^ 2) * (1 + Polynomial.C (qP ^ (2 * (N + 1) + 1)) * ZP) *
            (ZP + Polynomial.C (qP ^ (2 * N - 1))))) =
        (Polynomial.C qP * (ZP + Polynomial.C (qP ^ (2 * N - 1))) *
          (P_poly N).comp (Polynomial.C (qP ^ 2) * ZP)) *
        Polynomial.C (qP ^ 2) * (ZP + Polynomial.C (qP ^ (2 * (N + 1) - 1))) *
        (1 + Polynomial.C (qP ^ (2 * (N + 1) + 1)) * ZP) := by ring
    rw [hstep, ih]
    unfold facP
    have e4 : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
    have e3 : 2 * (N + 1) = 2 * N + 2 := by omega
    rw [e4, e3, pow_add]
    simp only [Polynomial.C_mul, Polynomial.C_pow]
    ring

private lemma coeff_comp_C_mul_X (f : (Polynomial ℤ)[X]) (a : Polynomial ℤ) (m : ℕ) :
    (f.comp (Polynomial.C a * ZP)).coeff m = a ^ m * f.coeff m := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [Polynomial.add_comp, coeff_add, coeff_add, hp, hr, mul_add]
  | monomial n c =>
    rw [Polynomial.monomial_comp, mul_pow, ← C_pow, ← C_mul_X_pow_eq_monomial,
      ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    by_cases h : m = n
    · subst h; simp [mul_comm]
    · simp [h]

private lemma P_poly_coeff_rec (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ N) :
    (1 - qP ^ (2 * N + 2 * k)) * (P_poly N).coeff (N + k) =
      qP ^ (2 * k - 1) * (1 - qP ^ (2 * N - 2 * k + 2)) * (P_poly N).coeff (N + k - 1) := by
  have hfe := congr_arg (fun p => p.coeff (N + k)) (P_poly_func_eq N hN)
  have hL : (Polynomial.C qP * (ZP + Polynomial.C (qP ^ (2 * N - 1))) *
      (P_poly N).comp (Polynomial.C (qP ^ 2) * ZP)).coeff (N + k) =
      qP ^ (2 * N + 2 * k - 1) * (P_poly N).coeff (N + k - 1) +
      qP ^ (4 * N + 2 * k) * (P_poly N).coeff (N + k) := by
    have hexp : Polynomial.C qP * (ZP + Polynomial.C (qP ^ (2 * N - 1))) *
        (P_poly N).comp (Polynomial.C (qP ^ 2) * ZP) =
        Polynomial.C qP * ((P_poly N).comp (Polynomial.C (qP ^ 2) * ZP) * ZP ^ 1) +
        Polynomial.C (qP ^ (2 * N)) * (P_poly N).comp (Polynomial.C (qP ^ 2) * ZP) := by
      have hC1 : Polynomial.C (qP ^ (2 * N)) = Polynomial.C qP * Polynomial.C (qP ^ (2 * N - 1)) := by
        rw [← map_mul, ← pow_succ', show 2 * N - 1 + 1 = 2 * N by omega]
      rw [hC1]
      ring
    rw [hexp, coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow',
      if_pos (by omega), coeff_comp_C_mul_X, coeff_comp_C_mul_X]
    have e1 : qP * ((qP ^ 2) ^ (N + k - 1) * (P_poly N).coeff (N + k - 1)) =
        qP ^ (2 * N + 2 * k - 1) * (P_poly N).coeff (N + k - 1) := by
      rw [← mul_assoc, ← pow_mul, ← pow_succ']
      congr 2; omega
    have e2 : qP ^ (2 * N) * ((qP ^ 2) ^ (N + k) * (P_poly N).coeff (N + k)) =
        qP ^ (4 * N + 2 * k) * (P_poly N).coeff (N + k) := by
      rw [← mul_assoc, ← pow_mul, ← pow_add]
      congr 2; omega
    rw [e1, e2]
  have hR : (Polynomial.C (qP ^ (2 * N)) * (1 + Polynomial.C (qP ^ (2 * N + 1)) * ZP) *
      P_poly N).coeff (N + k) =
      qP ^ (2 * N) * (P_poly N).coeff (N + k) +
      qP ^ (4 * N + 1) * (P_poly N).coeff (N + k - 1) := by
    have hexp : Polynomial.C (qP ^ (2 * N)) * (1 + Polynomial.C (qP ^ (2 * N + 1)) * ZP) *
        P_poly N =
        Polynomial.C (qP ^ (2 * N)) * P_poly N +
        Polynomial.C (qP ^ (4 * N + 1)) * (P_poly N * ZP ^ 1) := by
      have hC2 : Polynomial.C (qP ^ (4 * N + 1)) =
          Polynomial.C (qP ^ (2 * N)) * Polynomial.C (qP ^ (2 * N + 1)) := by
        rw [← map_mul, ← pow_add]; congr 2; omega
      rw [hC2]
      ring
    rw [hexp, coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow',
      if_pos (by omega)]
  rw [hL, hR] at hfe
  apply mul_left_cancel₀ (a := qP ^ (2 * N)) (pow_ne_zero _ Polynomial.X_ne_zero)
  have e1 : qP ^ (2 * N) * ((1 - qP ^ (2 * N + 2 * k)) * (P_poly N).coeff (N + k)) =
      qP ^ (2 * N) * (P_poly N).coeff (N + k) - qP ^ (4 * N + 2 * k) * (P_poly N).coeff (N + k) := by
    have h4 : 4 * N + 2 * k = 2 * N + (2 * N + 2 * k) := by omega
    rw [h4, pow_add]; ring
  have e2 : qP ^ (2 * N) * (qP ^ (2 * k - 1) * (1 - qP ^ (2 * N - 2 * k + 2)) *
      (P_poly N).coeff (N + k - 1)) =
      qP ^ (2 * N + 2 * k - 1) * (P_poly N).coeff (N + k - 1) -
      qP ^ (4 * N + 1) * (P_poly N).coeff (N + k - 1) := by
    have ha : 2 * N + 2 * k - 1 = 2 * N + (2 * k - 1) := by omega
    have hb : 4 * N + 1 = 2 * N + (2 * k - 1) + (2 * N - 2 * k + 2) := by omega
    rw [ha, hb, pow_add, pow_add]; ring
  rw [e1, e2]
  linear_combination -hfe

private lemma piPoly_succ (m : ℕ) :
    piPoly (m + 1) = piPoly m * (1 - qP ^ (2 * (m + 1))) := by
  unfold piPoly
  rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.prod_insert (by simp)]
  ring

private lemma piPoly_split (a b : ℕ) (hab : a ≤ b) :
    piPoly b = piPoly a * ∏ j ∈ Finset.Icc (a + 1) b, (1 - qP ^ (2 * j)) := by
  unfold piPoly
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    omega
  rw [← Finset.prod_union hdisj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

private lemma piPoly_ne_zero (m : ℕ) : piPoly m ≠ 0 := by
  intro h
  have hev := congr_arg (Polynomial.eval 0) h
  rw [Polynomial.eval_zero] at hev
  have h1 : (piPoly m).eval 0 = 1 := by
    unfold piPoly
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_Icc] at hj
    simp [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, zero_pow (by omega : 2 * j ≠ 0)]
  rw [h1] at hev
  exact one_ne_zero hev

private lemma P_poly_coeff_formula (N : ℕ) (hN : 1 ≤ N) :
    ∀ m ≤ N, (P_poly N).coeff (2 * N - m) * piPoly (2 * N - m) * piPoly m =
      qP ^ ((N - m) ^ 2) * piPoly (2 * N) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    have h0 : piPoly 0 = 1 := by simp [piPoly]
    rw [h0, mul_one, (P_poly_props N).2.2]
  | succ m ih =>
    intro hm
    have hih := ih (by omega)
    set k := N - m with hk_def
    have hk1 : 1 ≤ k := by omega
    have hrec := P_poly_coeff_rec N hN k hk1 (by omega)
    have eNk : N + k = 2 * N - m := by omega
    have eNk1 : 2 * N - m - 1 = 2 * N - (m + 1) := by omega
    have e2Nk : 2 * N + 2 * k = 2 * (2 * N - m) := by omega
    have e2Nm : 2 * N - 2 * k + 2 = 2 * (m + 1) := by omega
    rw [eNk, eNk1, e2Nk, e2Nm] at hrec
    have hpi1 : piPoly (2 * N - m) = piPoly (2 * N - (m + 1)) * (1 - qP ^ (2 * (2 * N - m))) := by
      have e : 2 * N - m = (2 * N - (m + 1)) + 1 := by omega
      conv_lhs => rw [e]
      rw [piPoly_succ, ← e]
    have hpi2 : piPoly (m + 1) = piPoly m * (1 - qP ^ (2 * (m + 1))) := piPoly_succ m
    have hstep : qP ^ (2 * k - 1) * ((P_poly N).coeff (2 * N - (m + 1)) *
        piPoly (2 * N - (m + 1)) * piPoly (m + 1)) =
        qP ^ (2 * k - 1) * (qP ^ ((N - (m + 1)) ^ 2) * piPoly (2 * N)) := by
      calc qP ^ (2 * k - 1) * ((P_poly N).coeff (2 * N - (m + 1)) *
            piPoly (2 * N - (m + 1)) * piPoly (m + 1))
          = (qP ^ (2 * k - 1) * (1 - qP ^ (2 * (m + 1))) * (P_poly N).coeff (2 * N - (m + 1))) *
              piPoly (2 * N - (m + 1)) * piPoly m := by rw [hpi2]; ring
        _ = ((1 - qP ^ (2 * (2 * N - m))) * (P_poly N).coeff (2 * N - m)) *
              piPoly (2 * N - (m + 1)) * piPoly m := by rw [← hrec]
        _ = (P_poly N).coeff (2 * N - m) * piPoly (2 * N - m) * piPoly m := by rw [hpi1]; ring
        _ = qP ^ (k ^ 2) * piPoly (2 * N) := hih
        _ = qP ^ (2 * k - 1) * (qP ^ ((N - (m + 1)) ^ 2) * piPoly (2 * N)) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          have ekm : N - (m + 1) = k - 1 := by omega
          rw [ekm]
          zify [hk1]
          have : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 1 := by omega
          rw [this]; ring
    exact mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) hstep

private lemma P_poly_coeff_mul_piPoly (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    (P_poly N).coeff (N + k) * piPoly N =
      qP ^ (k ^ 2) *
        (∏ j ∈ Finset.Icc (N + k + 1) (2 * N), (1 - qP ^ (2 * j))) *
        (∏ j ∈ Finset.Icc (N - k + 1) N, (1 - qP ^ (2 * j))) := by
  have hform := P_poly_coeff_formula N hN (N - k) (by omega)
  have e1 : 2 * N - (N - k) = N + k := by omega
  have e2 : N - (N - k) = k := by omega
  rw [e1, e2] at hform
  rw [piPoly_split (N + k) (2 * N) (by omega)] at hform
  have hcancel : (P_poly N).coeff (N + k) * piPoly (N - k) =
      qP ^ (k ^ 2) * ∏ j ∈ Finset.Icc (N + k + 1) (2 * N), (1 - qP ^ (2 * j)) := by
    apply mul_left_cancel₀ (a := piPoly (N + k)) (piPoly_ne_zero (N + k))
    linear_combination hform
  calc (P_poly N).coeff (N + k) * piPoly N
      = ((P_poly N).coeff (N + k) * piPoly (N - k)) *
          ∏ j ∈ Finset.Icc (N - k + 1) N, (1 - qP ^ (2 * j)) := by
        rw [piPoly_split (N - k) N (by omega)]; ring
    _ = qP ^ (k ^ 2) *
          (∏ j ∈ Finset.Icc (N + k + 1) (2 * N), (1 - qP ^ (2 * j))) *
          (∏ j ∈ Finset.Icc (N - k + 1) N, (1 - qP ^ (2 * j))) := by
        rw [hcancel]

private lemma P_poly_eq_mul_Q_poly (N : ℕ) (hN : 1 ≤ N) :
    P_poly N = (ZP + Polynomial.C qP) * Q_poly N := by
  unfold P_poly Q_poly
  have h1 : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h1, Finset.prod_insert (by simp)]
  unfold facP
  simp only [mul_one, Nat.reduceSub, pow_one]
  ring

private lemma Q_poly_eval_neg_q (N : ℕ) (hN : 1 ≤ N) :
    (Q_poly N).eval (-qP) =
      (-qP) ^ (N - 1) * (1 - qP ^ (2 * N)) *
        ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    unfold Q_poly
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C,
      Polynomial.eval_X, sq]
    ring
  | succ N hN ih =>
    have hQsucc : Q_poly (N + 1) = Q_poly N * facP (N + 1) := by
      unfold Q_poly
      rw [show Finset.Icc 2 (N + 1) = insert (N + 1) (Finset.Icc 2 N) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.prod_insert (by simp)]
      ring
    rw [hQsucc, Polynomial.eval_mul, ih]
    have hfac : (facP (N + 1)).eval (-qP) =
        (-qP) * (1 - qP ^ (2 * (N + 1))) * (1 - qP ^ (2 * N)) := by
      unfold facP
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C,
        Polynomial.eval_X]
      have e1 : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
      have e2 : 2 * (N + 1) = 2 * N + 2 := by omega
      rw [e1, e2, pow_succ, pow_add]
      ring
    rw [hfac]
    have hIcc : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    simp only [Nat.add_sub_cancel]
    rw [hIcc, Finset.prod_insert (by simp; omega)]
    have hpow : (-qP) ^ (N - 1) * (-qP) = (-qP) ^ N := by
      rw [← pow_succ, show N - 1 + 1 = N by omega]
    calc (-qP) ^ (N - 1) * (1 - qP ^ (2 * N)) *
          (∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) *
          ((-qP) * (1 - qP ^ (2 * (N + 1))) * (1 - qP ^ (2 * N)))
        = ((-qP) ^ (N - 1) * (-qP)) * (1 - qP ^ (2 * (N + 1))) *
          ((1 - qP ^ (2 * N)) ^ 2 * ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) := by ring
      _ = (-qP) ^ N * (1 - qP ^ (2 * (N + 1))) *
          ((1 - qP ^ (2 * N)) ^ 2 * ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) := by
          rw [hpow]

private lemma deriv_eval_eq_sum (f : (Polynomial ℤ)[X]) (N : ℕ) (x : Polynomial ℤ)
    (hdeg : ∀ k, 2 * N < k → f.coeff k = 0)
    (hsym : ∀ k ≤ 2 * N, f.coeff (2 * N - k) = f.coeff k)
    (hroot : f.eval x = 0) :
    x * f.derivative.eval x =
      ∑ k ∈ Finset.Icc 1 N, (k : Polynomial ℤ) * f.coeff (N + k) * (x ^ (N + k) - x ^ (N - k)) := by
  have hnat : f.natDegree ≤ 2 * N := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hdeg
  have hev_f : f.eval x = ∑ i ∈ Finset.range (2 * N + 1), f.coeff i * x ^ i :=
    Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hnat (Nat.lt_succ_self _)) x
  have hev_df : x * f.derivative.eval x =
      ∑ i ∈ Finset.range (2 * N + 1), (i : Polynomial ℤ) * f.coeff i * x ^ i := by
    have hnat_d : f.derivative.natDegree < 2 * N + 1 := by
      have := Polynomial.natDegree_derivative_le f
      omega
    rw [Polynomial.eval_eq_sum_range' hnat_d x, Finset.mul_sum]
    have hstep1 : ∑ i ∈ Finset.range (2 * N + 1), x * (f.derivative.coeff i * x ^ i) =
        ∑ i ∈ Finset.range (2 * N), ((i + 1 : ℕ) : Polynomial ℤ) * f.coeff (i + 1) * x ^ (i + 1) := by
      rw [Finset.sum_range_succ]
      have hlast : x * (f.derivative.coeff (2 * N) * x ^ (2 * N)) = 0 := by
        rw [Polynomial.coeff_derivative, hdeg (2 * N + 1) (by omega), zero_mul, zero_mul, mul_zero]
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.coeff_derivative]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    rw [hstep1, Finset.sum_range_succ']
    simp
  have hsub : x * f.derivative.eval x =
      ∑ i ∈ Finset.range (2 * N + 1), ((i : Polynomial ℤ) - (N : Polynomial ℤ)) * f.coeff i * x ^ i := by
    calc x * f.derivative.eval x
        = x * f.derivative.eval x - (N : Polynomial ℤ) * f.eval x := by rw [hroot, mul_zero, sub_zero]
      _ = ∑ i ∈ Finset.range (2 * N + 1), (i : Polynomial ℤ) * f.coeff i * x ^ i -
            ∑ i ∈ Finset.range (2 * N + 1), (N : Polynomial ℤ) * (f.coeff i * x ^ i) := by
          rw [hev_df, hev_f, Finset.mul_sum]
      _ = ∑ i ∈ Finset.range (2 * N + 1),
            ((i : Polynomial ℤ) - (N : Polynomial ℤ)) * f.coeff i * x ^ i := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsub]
  set F : ℕ → Polynomial ℤ := fun i => ((i : Polynomial ℤ) - (N : Polynomial ℤ)) * f.coeff i * x ^ i
  change ∑ i ∈ Finset.range (2 * N + 1), F i = _
  have hsplit : Finset.range (2 * N + 1) =
      Finset.range N ∪ ({N} ∪ Finset.Icc (N + 1) (2 * N)) := by
    ext i; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_union, Finset.sum_union, Finset.sum_singleton]
  · have hFN : F N = 0 := by simp [F]
    have hlow : ∑ i ∈ Finset.range N, F i =
        ∑ k ∈ Finset.Icc 1 N, (-(k : Polynomial ℤ)) * f.coeff (N + k) * x ^ (N - k) := by
      symm
      refine Finset.sum_bij (fun k _ => N - k) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
      · intro a ha b hb hab
        simp only [Finset.mem_Icc] at ha hb
        omega
      · intro i hi
        simp only [Finset.mem_range] at hi
        exact ⟨N - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        dsimp only [F]
        have hc : f.coeff (N - k) = f.coeff (N + k) := by
          have := hsym (N + k) (by omega)
          rw [show 2 * N - (N + k) = N - k by omega] at this
          exact this
        rw [hc, Nat.cast_sub hk.2]
        ring
    have hhigh : ∑ i ∈ Finset.Icc (N + 1) (2 * N), F i =
        ∑ k ∈ Finset.Icc 1 N, (k : Polynomial ℤ) * f.coeff (N + k) * x ^ (N + k) := by
      symm
      refine Finset.sum_bij (fun k _ => N + k) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      · intro a _ b _ hab; omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        exact ⟨i - N, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        dsimp only [F]
        simp only [Nat.cast_add]
        ring
    rw [hFN, zero_add, hlow, hhigh, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  · rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_singleton] at hi1
    simp only [Finset.mem_Icc] at hi2
    omega
  · rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_range] at hi1
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at hi2
    omega

private lemma finite_jacobi_poly_id (N : ℕ) (hN : 1 ≤ N) :
    qP ^ N * (1 - qP ^ (2 * N)) ^ 2 * (∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m))) ^ 3 =
      ∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * ((P_poly N).coeff (N + k) * piPoly N) *
          (qP ^ (N + k) - qP ^ (N - k)) := by
  have hroot : (P_poly N).eval (-qP) = 0 := by
    rw [P_poly_eq_mul_Q_poly N hN, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, neg_add_cancel, zero_mul]
  have hd : (P_poly N).derivative.eval (-qP) = (Q_poly N).eval (-qP) := by
    rw [P_poly_eq_mul_Q_poly N hN, Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.derivative_X, Polynomial.derivative_C, add_zero, one_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, neg_add_cancel, zero_mul, add_zero]
  have hsum := deriv_eval_eq_sum (P_poly N) N (-qP) (P_poly_props N).1 (P_poly_props N).2.1 hroot
  rw [hd, Q_poly_eval_neg_q N hN] at hsum
  have hlhs_sign : (-qP) * ((-qP) ^ (N - 1) * (1 - qP ^ (2 * N)) *
      ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) =
      (-1 : Polynomial ℤ) ^ N * (qP ^ N * (1 - qP ^ (2 * N)) *
        ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) := by
    have hpow : (-qP) * (-qP) ^ (N - 1) = (-1 : Polynomial ℤ) ^ N * qP ^ N := by
      rw [← pow_succ', show N - 1 + 1 = N by omega, neg_eq_neg_one_mul, mul_pow]
    calc (-qP) * ((-qP) ^ (N - 1) * (1 - qP ^ (2 * N)) *
          ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2)
        = ((-qP) * (-qP) ^ (N - 1)) * (1 - qP ^ (2 * N)) *
            ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2 := by ring
      _ = (-1 : Polynomial ℤ) ^ N * (qP ^ N * (1 - qP ^ (2 * N)) *
            ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) := by rw [hpow]; ring
  have hrhs_sign : ∑ k ∈ Finset.Icc 1 N, (k : Polynomial ℤ) * (P_poly N).coeff (N + k) *
      ((-qP) ^ (N + k) - (-qP) ^ (N - k)) =
      (-1 : Polynomial ℤ) ^ N * ∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * (P_poly N).coeff (N + k) *
          (qP ^ (N + k) - qP ^ (N - k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hp1 : (-qP) ^ (N + k) = (-1 : Polynomial ℤ) ^ N * (-1 : Polynomial ℤ) ^ k * qP ^ (N + k) := by
      rw [neg_eq_neg_one_mul, mul_pow, pow_add]
    have hp2 : (-qP) ^ (N - k) = (-1 : Polynomial ℤ) ^ N * (-1 : Polynomial ℤ) ^ k * qP ^ (N - k) := by
      rw [neg_eq_neg_one_mul, mul_pow]
      have hneg : (-1 : Polynomial ℤ) ^ (N - k) = (-1 : Polynomial ℤ) ^ N * (-1 : Polynomial ℤ) ^ k := by
        have h1 : (-1 : Polynomial ℤ) ^ N = (-1 : Polynomial ℤ) ^ (N - k) * (-1 : Polynomial ℤ) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk.2]
        rw [h1, mul_assoc, ← pow_add, show k + k = 2 * k by ring, pow_mul]
        norm_num
      rw [hneg]
    rw [hp1, hp2]
    ring
  rw [hlhs_sign, hrhs_sign] at hsum
  have hcore : qP ^ N * (1 - qP ^ (2 * N)) *
      ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2 =
      ∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * (P_poly N).coeff (N + k) *
          (qP ^ (N + k) - qP ^ (N - k)) :=
    mul_left_cancel₀ (pow_ne_zero N (by norm_num : (-1 : Polynomial ℤ) ≠ 0)) hsum
  have hmul := congr_arg (· * piPoly N) hcore
  have hpiN : piPoly N = (1 - qP ^ (2 * N)) * ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) := by
    have e : N = (N - 1) + 1 := by omega
    conv_lhs => rw [e]
    rw [piPoly_succ, ← e]
    unfold piPoly
    ring
  rw [Finset.sum_mul] at hmul
  calc qP ^ N * (1 - qP ^ (2 * N)) ^ 2 * (∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m))) ^ 3
      = (qP ^ N * (1 - qP ^ (2 * N)) * ∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m)) ^ 2) *
          piPoly N := by
        rw [hpiN, Finset.prod_pow]; ring
    _ = ∑ k ∈ Finset.Icc 1 N,
          (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * (P_poly N).coeff (N + k) *
            (qP ^ (N + k) - qP ^ (N - k)) * piPoly N := hmul
    _ = ∑ k ∈ Finset.Icc 1 N,
          (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * ((P_poly N).coeff (N + k) * piPoly N) *
            (qP ^ (N + k) - qP ^ (N - k)) := by
        refine Finset.sum_congr rfl fun k _ => by ring

/-! ### Part 3: Coefficient extraction and Jacobi identity in `Polynomial ℤ` -/

private def HasGap (p : Polynomial ℤ) (M : ℕ) : Prop :=
  p.coeff 0 = 1 ∧ ∀ r, 0 < r → r < M → p.coeff r = 0

private lemma hasGap_one (M : ℕ) : HasGap 1 M :=
  ⟨by simp, fun r hr _ => by rw [Polynomial.coeff_one, if_neg (by omega)]⟩

private lemma hasGap_one_sub_X_pow {n M : ℕ} (hn : 0 < n) (hMn : M ≤ n) :
    HasGap (1 - qP ^ n) M := by
  refine ⟨?_, ?_⟩
  · rw [coeff_sub, coeff_one_zero, Polynomial.coeff_X_pow, if_neg (by omega), sub_zero]
  · intro r hr hlt
    rw [coeff_sub, Polynomial.coeff_one, if_neg (by omega), Polynomial.coeff_X_pow,
      if_neg (by omega), sub_zero]

private lemma hasGap_mul {p r : Polynomial ℤ} {M : ℕ} (hp : HasGap p M) (hr : HasGap r M) :
    HasGap (p * r) M := by
  refine ⟨?_, ?_⟩
  · rw [Polynomial.mul_coeff_zero, hp.1, hr.1, mul_one]
  · intro m hm hlt
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_eq_zero]
    intro k hk
    rw [Finset.mem_range] at hk
    rcases eq_or_ne k 0 with rfl | h1
    · rw [Nat.sub_zero, hr.2 m hm hlt, mul_zero]
    · rw [hp.2 k (by omega) (by omega), zero_mul]

private lemma hasGap_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) (M : ℕ)
    (hf : ∀ a ∈ s, HasGap (f a) M) : HasGap (∏ a ∈ s, f a) M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasGap_one M
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hasGap_mul (hf a (Finset.mem_insert_self a s))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

private lemma coeff_mul_of_hasGap {f g : Polynomial ℤ} {M m : ℕ}
    (hg : HasGap g M) (hm : m < M) : (f * g).coeff m = f.coeff m := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_eq_single m]
  · rw [Nat.sub_self, hg.1, mul_one]
  · intro k hk hne
    rw [Finset.mem_range] at hk
    rw [hg.2 (m - k) (by omega) (by omega), mul_zero]
  · intro h
    exfalso; apply h; rw [Finset.mem_range]; omega

private lemma coeff_X_pow_mul_of_hasGap {g : Polynomial ℤ} {a M m : ℕ}
    (hg : HasGap g M) (hm : m < a + M) : (qP ^ a * g).coeff m = (qP ^ a).coeff m := by
  rw [Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow]
  by_cases hle : a ≤ m
  · rw [if_pos hle]
    by_cases heq : m = a
    · subst heq; simp [hg.1]
    · rw [if_neg heq, hg.2 (m - a) (by omega) (by omega)]
  · rw [if_neg hle, if_neg (by omega)]

private lemma telescoping_tri (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) *
        (qP ^ (k * (k + 1)) - qP ^ ((k - 1) * k)) =
      ∑ j ∈ Finset.range N, (-1 : Polynomial ℤ) ^ j * ((2 * j + 1 : ℕ) : Polynomial ℤ) *
        qP ^ (j * (j + 1)) +
      (-1 : Polynomial ℤ) ^ N * (N : Polynomial ℤ) * qP ^ (N * (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.sum_insert (by simp), ih, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    ring

private lemma coeff_comp_X_sq (f : Polynomial ℤ) (d : ℕ) :
    (f.comp (qP ^ 2)).coeff (2 * d) = f.coeff d := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [Polynomial.add_comp, coeff_add, coeff_add, hp, hr]
  | monomial n c =>
    rw [Polynomial.monomial_comp, ← C_mul_X_pow_eq_monomial, ← pow_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : d = n
    · subst h; simp
    · have h2 : 2 * d ≠ 2 * n := by omega
      simp [h, h2]

private lemma jacobi_cubic_poly (d : ℕ) :
    ((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ m)) ^ 3).coeff d =
      ∑ j ∈ Finset.range (d + 1), if j * (j + 1) / 2 = d then (-1 : ℤ) ^ j * (2 * j + 1) else 0 := by
  set N := d + 1 with hN_def
  have hN : 1 ≤ N := by omega
  have hid := congr_arg (fun p => p.coeff (N + 2 * d)) (finite_jacobi_poly_id N hN)
  have hLHS : (qP ^ N * (1 - qP ^ (2 * N)) ^ 2 *
      (∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m))) ^ 3).coeff (N + 2 * d) =
      ((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ m)) ^ 3).coeff d := by
    have hre : qP ^ N * (1 - qP ^ (2 * N)) ^ 2 *
        (∏ m ∈ Finset.Icc 1 (N - 1), (1 - qP ^ (2 * m))) ^ 3 =
        qP ^ N * (((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ (2 * m))) ^ 3) * (1 - qP ^ (2 * N)) ^ 2) := by
      simp only [hN_def, Nat.add_sub_cancel]; ring
    rw [hre, Polynomial.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left]
    have hgap : HasGap ((1 - qP ^ (2 * N)) ^ 2) (2 * N) := by
      rw [sq]
      exact hasGap_mul (hasGap_one_sub_X_pow (by omega) le_rfl) (hasGap_one_sub_X_pow (by omega) le_rfl)
    rw [coeff_mul_of_hasGap hgap (by omega)]
    have hcomp : ((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ m)) ^ 3).comp (qP ^ 2) =
        (∏ m ∈ Finset.Icc 1 d, (1 - qP ^ (2 * m))) ^ 3 := by
      rw [Polynomial.pow_comp, Polynomial.prod_comp]
      congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.pow_comp, Polynomial.X_comp, ← pow_mul]
    rw [← hcomp, coeff_comp_X_sq]
  have hRHS_replace :
      (∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * ((P_poly N).coeff (N + k) * piPoly N) *
          (qP ^ (N + k) - qP ^ (N - k))).coeff (N + 2 * d) =
      (∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * qP ^ (k ^ 2) *
          (qP ^ (N + k) - qP ^ (N - k))).coeff (N + 2 * d) := by
    rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [P_poly_coeff_mul_piPoly N hN k hk.2]
    set G : Polynomial ℤ :=
      (∏ j ∈ Finset.Icc (N + k + 1) (2 * N), (1 - qP ^ (2 * j))) *
      (∏ j ∈ Finset.Icc (N - k + 1) N, (1 - qP ^ (2 * j)))
    have hG : HasGap G (2 * (N - k + 1)) := by
      refine hasGap_mul (hasGap_prod _ _ _ fun j hj => ?_) (hasGap_prod _ _ _ fun j hj => ?_)
      · simp only [Finset.mem_Icc] at hj
        exact hasGap_one_sub_X_pow (by omega) (by omega)
      · simp only [Finset.mem_Icc] at hj
        exact hasGap_one_sub_X_pow (by omega) (by omega)
    have hbound : 2 * d + k < k ^ 2 + 2 * (N - k + 1) := by
      rcases eq_or_ne k 1 with rfl | hk1'
      · omega
      · have hk2 : 2 ≤ k := by omega
        have hk_le : k ≤ N := hk.2
        have hN_eq : (N : ℤ) = (d : ℤ) + 1 := by omega
        zify [hk_le]
        nlinarith
    have hstep : ∀ A : Polynomial ℤ,
        ((-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * A * (qP ^ (N + k) - qP ^ (N - k))).coeff (N + 2 * d) =
        ((-1 : ℤ) ^ k * (k : ℤ)) *
          ((if N + k ≤ N + 2 * d then A.coeff (N + 2 * d - (N + k)) else 0) -
           (if N - k ≤ N + 2 * d then A.coeff (N + 2 * d - (N - k)) else 0)) := by
      intro A
      have hC : (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) = Polynomial.C ((-1 : ℤ) ^ k * (k : ℤ)) := by
        simp [map_mul, map_pow, map_neg, map_one, map_natCast]
      rw [hC, mul_assoc, Polynomial.coeff_C_mul, mul_sub, coeff_sub]
      congr 2
      · rw [mul_comm, Polynomial.coeff_X_pow_mul']
      · rw [mul_comm, Polynomial.coeff_X_pow_mul']
    have hrew : qP ^ (k ^ 2) *
        (∏ j ∈ Finset.Icc (N + k + 1) (2 * N), (1 - qP ^ (2 * j))) *
        (∏ j ∈ Finset.Icc (N - k + 1) N, (1 - qP ^ (2 * j))) = qP ^ (k ^ 2) * G := by
      dsimp only [G]; ring
    rw [hrew, hstep (qP ^ (k ^ 2) * G), hstep (qP ^ (k ^ 2))]
    congr 2
    · by_cases hle : N + k ≤ N + 2 * d
      · rw [if_pos hle, if_pos hle]
        exact coeff_X_pow_mul_of_hasGap hG (by omega)
      · rw [if_neg hle, if_neg hle]
    · rw [if_pos (by omega), if_pos (by omega)]
      exact coeff_X_pow_mul_of_hasGap hG (by omega)
  have hRHS_eval :
      (∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * qP ^ (k ^ 2) *
          (qP ^ (N + k) - qP ^ (N - k))).coeff (N + 2 * d) =
      ∑ j ∈ Finset.range (d + 1), if j * (j + 1) / 2 = d then (-1 : ℤ) ^ j * (2 * j + 1) else 0 := by
    have hfac : ∑ k ∈ Finset.Icc 1 N,
        (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * qP ^ (k ^ 2) *
          (qP ^ (N + k) - qP ^ (N - k)) =
        qP ^ N * ∑ k ∈ Finset.Icc 1 N,
          (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) *
            (qP ^ (k * (k + 1)) - qP ^ ((k - 1) * k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have e1 : k ^ 2 + (N + k) = N + k * (k + 1) := by ring
      have e2 : k ^ 2 + (N - k) = N + (k - 1) * k := by
        zify [hk.1, hk.2]; ring
      calc (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) * qP ^ (k ^ 2) *
            (qP ^ (N + k) - qP ^ (N - k))
          = (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) *
              (qP ^ (k ^ 2 + (N + k)) - qP ^ (k ^ 2 + (N - k))) := by rw [pow_add, pow_add]; ring
        _ = (-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) *
              (qP ^ (N + k * (k + 1)) - qP ^ (N + (k - 1) * k)) := by rw [e1, e2]
        _ = qP ^ N * ((-1 : Polynomial ℤ) ^ k * (k : Polynomial ℤ) *
              (qP ^ (k * (k + 1)) - qP ^ ((k - 1) * k))) := by rw [pow_add, pow_add]; ring
    rw [hfac, telescoping_tri N, Polynomial.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left,
      coeff_add, Polynomial.finsetSum_coeff]
    have htail : ((-1 : Polynomial ℤ) ^ N * (N : Polynomial ℤ) * qP ^ (N * (N + 1))).coeff (2 * d) = 0 := by
      have hC : (-1 : Polynomial ℤ) ^ N * (N : Polynomial ℤ) = Polynomial.C ((-1 : ℤ) ^ N * (N : ℤ)) := by
        simp [map_mul, map_pow, map_neg, map_one, map_natCast]
      rw [hC, Polynomial.coeff_C_mul_X_pow, if_neg]
      have : 2 * d < N * (N + 1) := by nlinarith
      omega
    rw [htail, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hC : (-1 : Polynomial ℤ) ^ j * ((2 * j + 1 : ℕ) : Polynomial ℤ) =
        Polynomial.C ((-1 : ℤ) ^ j * ((2 * j + 1 : ℕ) : ℤ)) := by
      simp [map_mul, map_pow, map_neg, map_one]
    rw [hC, Polynomial.coeff_C_mul_X_pow]
    have heven : 2 ∣ j * (j + 1) := Nat.even_mul_succ_self j |>.two_dvd
    have hiff : 2 * d = j * (j + 1) ↔ j * (j + 1) / 2 = d := by
      obtain ⟨t, ht⟩ := heven
      omega
    simp only [hiff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [← hLHS, hid, hRHS_replace, hRHS_eval]

/-! ### Part 4: Identifying `E ^ 3 = T` in `(ZMod 4)⟦X⟧` and the mod-4 bijection -/

open Classical in
private noncomputable def T_series : (ZMod 4)⟦X⟧ :=
  PowerSeries.mk fun n => if ∃ k : ℕ, k * (k + 1) / 2 = n then (1 : ZMod 4) else 0

private lemma tri_strictMono : StrictMono (fun k : ℕ => k * (k + 1) / 2) := by
  intro a b hab
  dsimp only
  have ha : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
  have hb : 2 ∣ b * (b + 1) := (Nat.even_mul_succ_self b).two_dvd
  obtain ⟨ta, hta⟩ := ha
  obtain ⟨tb, htb⟩ := hb
  have hlt : a * (a + 1) < b * (b + 1) := by nlinarith
  omega

private lemma le_tri (k : ℕ) : k ≤ k * (k + 1) / 2 := by
  have hk : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  obtain ⟨t, ht⟩ := hk
  have : 2 * k ≤ k * (k + 1) := by nlinarith
  omega

private lemma neg_one_pow_mul_odd_zmod4 (j : ℕ) :
    (((-1 : ℤ) ^ j * (2 * (j : ℤ) + 1) : ℤ) : ZMod 4) = 1 := by
  push_cast
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h1 : (-1 : ZMod 4) ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul, show (-1 : ZMod 4) ^ 2 = 1 by decide, one_pow]
    rw [h1, one_mul]
    push_cast
    have h4 : (4 : ZMod 4) = 0 := by decide
    calc (2 * ((m : ZMod 4) + m) + 1 : ZMod 4) = 4 * (m : ZMod 4) + 1 := by ring
      _ = 1 := by rw [h4, zero_mul, zero_add]
  · have h1 : (-1 : ZMod 4) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul, show (-1 : ZMod 4) ^ 2 = 1 by decide, one_pow, one_mul]
    rw [h1]
    push_cast
    have h4 : (4 : ZMod 4) = 0 := by decide
    calc (-1 : ZMod 4) * (2 * (2 * (m : ZMod 4) + 1) + 1)
        = -(4 * (m : ZMod 4)) + (-3 : ZMod 4) := by ring
      _ = 1 := by rw [h4, zero_mul, neg_zero, zero_add]; decide

private lemma coeff_eq_of_le_agree {f g : (ZMod 4)⟦X⟧} {d : ℕ}
    (h : ∀ r ≤ d, PowerSeries.coeff r f = PowerSeries.coeff r g) :
    PowerSeries.coeff d (f ^ 3) = PowerSeries.coeff d (g ^ 3) := by
  have hmul : ∀ {a b c e : (ZMod 4)⟦X⟧},
      (∀ r ≤ d, PowerSeries.coeff r a = PowerSeries.coeff r b) →
      (∀ r ≤ d, PowerSeries.coeff r c = PowerSeries.coeff r e) →
      ∀ r ≤ d, PowerSeries.coeff r (a * c) = PowerSeries.coeff r (b * e) := by
    intro a b c e hab hce r hr
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hab k (by omega), hce (r - k) (by omega)]
  have h2 := hmul h h
  have h3 := hmul h2 h
  simpa [pow_succ, pow_zero, one_mul] using h3 d le_rfl

private lemma coeff_mul_one_sub_X_pow_of_lt {f : (ZMod 4)⟦X⟧} {n r : ℕ} (hr : r < n) :
    PowerSeries.coeff r (f * (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ n)) = PowerSeries.coeff r f := by
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', if_neg (by omega), sub_zero]

private lemma coeff_E_eq_finprod (d r : ℕ) (hr : r ≤ d) :
    PowerSeries.coeff r (pentagonalSeries (ZMod 4)) =
      PowerSeries.coeff r (∏ m ∈ Finset.Icc 1 d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ m)) := by
  let _ : TopologicalSpace (ZMod 4) := ⊥
  have _ : DiscreteTopology (ZMod 4) := ⟨rfl⟩
  have hE : HasProd (fun i : ℕ => (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1)))
      (pentagonalSeries (ZMod 4)) := by
    rw [← tprod_one_sub_X_pow (ZMod 4)]
    exact (multipliable_one_sub_X_pow (ZMod 4)).hasProd
  have htend : Filter.Tendsto
      (fun s : Finset ℕ => PowerSeries.coeff r (∏ i ∈ s, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))))
      Filter.atTop (nhds (PowerSeries.coeff r (pentagonalSeries (ZMod 4)))) :=
    (PowerSeries.WithPiTopology.continuous_coeff (R := ZMod 4) r).continuousAt.tendsto.comp hE
  have hevent : ∀ s : Finset ℕ, Finset.range d ⊆ s →
      PowerSeries.coeff r (∏ i ∈ s, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))) =
        PowerSeries.coeff r (∏ i ∈ Finset.range d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))) := by
    intro s hs
    have hsplit : ∏ i ∈ s, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1)) =
        (∏ i ∈ Finset.range d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))) *
        (∏ i ∈ s \ Finset.range d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))) := by
      rw [← Finset.prod_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hs]
    rw [hsplit]
    have ht : ∀ i ∈ s \ Finset.range d, r < i + 1 := by
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_range] at hi
      omega
    generalize s \ Finset.range d = t at ht ⊢
    clear hsplit hs
    induction t using Finset.induction_on with
    | empty => simp
    | insert a u ha ih =>
      rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm,
        coeff_mul_one_sub_X_pow_of_lt (ht a (Finset.mem_insert_self a u))]
      exact ih fun i hi => ht i (Finset.mem_insert_of_mem hi)
  have hconst : Filter.Tendsto
      (fun s : Finset ℕ => PowerSeries.coeff r (∏ i ∈ s, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))))
      Filter.atTop
      (nhds (PowerSeries.coeff r (∏ i ∈ Finset.range d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ (i + 1))))) :=
    tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨Finset.range d, fun s hs => (hevent s hs).symm⟩)
  have heq := tendsto_nhds_unique htend hconst
  rw [heq]
  congr 1
  refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
  · intro a _ b _ hab; omega
  · intro m hm; simp only [Finset.mem_Icc] at hm
    exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _; rfl

private lemma E_cube_eq_T : (pentagonalSeries (ZMod 4)) ^ 3 = T_series := by
  ext d
  rw [coeff_eq_of_le_agree (g := ∏ m ∈ Finset.Icc 1 d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ m))
    (fun r hr => coeff_E_eq_finprod d r hr)]
  have hmap : PowerSeries.coeff d ((∏ m ∈ Finset.Icc 1 d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ m)) ^ 3) =
      ((((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ m)) ^ 3).coeff d : ℤ) : ZMod 4) := by
    let φ : Polynomial ℤ →+* (ZMod 4)⟦X⟧ :=
      (PowerSeries.map (Int.castRingHom (ZMod 4))).comp Polynomial.coeToPowerSeries.ringHom
    have hφX : φ qP = (PowerSeries.X : (ZMod 4)⟦X⟧) := by
      simp [φ, qP]
    have hφprod : φ ((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ m)) ^ 3) =
        (∏ m ∈ Finset.Icc 1 d, (1 - (PowerSeries.X : (ZMod 4)⟦X⟧) ^ m)) ^ 3 := by
      simp [map_pow, map_prod, map_sub, map_one, hφX]
    rw [← hφprod]
    change PowerSeries.coeff d
      (PowerSeries.map (Int.castRingHom (ZMod 4))
        ((((∏ m ∈ Finset.Icc 1 d, (1 - qP ^ m)) ^ 3) : Polynomial ℤ) : PowerSeries ℤ)) = _
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe]
    rfl
  rw [hmap, jacobi_cubic_poly d, Int.cast_sum]
  have hterm : ∀ j : ℕ,
      ((if j * (j + 1) / 2 = d then (-1 : ℤ) ^ j * (2 * (j : ℤ) + 1) else 0 : ℤ) : ZMod 4) =
        if j * (j + 1) / 2 = d then (1 : ZMod 4) else 0 := by
    intro j
    split_ifs
    · exact neg_one_pow_mul_odd_zmod4 j
    · simp
  simp_rw [hterm]
  simp only [T_series, PowerSeries.coeff_mk]
  by_cases h : ∃ k : ℕ, k * (k + 1) / 2 = d
  · rw [if_pos h]
    obtain ⟨k, hk⟩ := h
    have hk_mem : k ∈ Finset.range (d + 1) := by
      rw [Finset.mem_range]
      have := le_tri k
      omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hjk
      rw [if_neg]
      intro hj
      exact hjk (tri_strictMono.injective (hj.trans hk.symm))
    · intro hmem; exact absurd hk_mem hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    intro hj
    exact h ⟨j, hj⟩

private lemma coeff_T_sq (n : ℕ) :
    PowerSeries.coeff n (T_series * T_series) =
      (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 * (p.1 + 1) / 2 + p.2 * (p.2 + 1) / 2 = n)).card : ZMod 4) := by
  have hT_sum : ∀ k ≤ n, PowerSeries.coeff k T_series =
      ∑ j ∈ Finset.range (n + 1), if j * (j + 1) / 2 = k then (1 : ZMod 4) else 0 := by
    intro k hk
    simp only [T_series, PowerSeries.coeff_mk]
    by_cases h : ∃ j : ℕ, j * (j + 1) / 2 = k
    · rw [if_pos h]
      obtain ⟨j, hj⟩ := h
      have hj_mem : j ∈ Finset.range (n + 1) := by
        rw [Finset.mem_range]; have := le_tri j; omega
      rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro l _ hlj
        rw [if_neg]; intro hl; exact hlj (tri_strictMono.injective (hl.trans hj.symm))
      · intro hm; exact absurd hj_mem hm
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]; intro hj; exact h ⟨j, hj⟩
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k T_series * PowerSeries.coeff (n - k) T_series =
      ∑ k ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1), if j * (j + 1) / 2 = k then (1 : ZMod 4) else 0) *
        (∑ l ∈ Finset.range (n + 1), if l * (l + 1) / 2 = n - k then (1 : ZMod 4) else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hT_sum k (by omega), hT_sum (n - k) (by omega)]
  rw [h1]
  have h2 : ∑ k ∈ Finset.range (n + 1),
      (∑ j ∈ Finset.range (n + 1), if j * (j + 1) / 2 = k then (1 : ZMod 4) else 0) *
      (∑ l ∈ Finset.range (n + 1), if l * (l + 1) / 2 = n - k then (1 : ZMod 4) else 0) =
      ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        if p.1 * (p.1 + 1) / 2 + p.2 * (p.2 + 1) / 2 = n then (1 : ZMod 4) else 0 := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hsum : j * (j + 1) / 2 + l * (l + 1) / 2 = n
    · rw [if_pos hsum]
      have hmem : j * (j + 1) / 2 ∈ Finset.range (n + 1) := by
        rw [Finset.mem_range]; omega
      rw [Finset.sum_eq_single (j * (j + 1) / 2)]
      · simp [show n - j * (j + 1) / 2 = l * (l + 1) / 2 by omega]
      · intro k _ hkne
        rw [if_neg (Ne.symm hkne), zero_mul]
      · intro hm; exact absurd hmem hm
    · rw [if_neg hsum]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      by_cases hj : j * (j + 1) / 2 = k
      · rw [if_pos hj, one_mul, if_neg]
        omega
      · rw [if_neg hj, zero_mul]
  rw [h2, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma tri_three_mul_add_one (j : ℕ) :
    (3 * j + 1) * (3 * j + 2) / 2 = 9 * (j * (j + 1) / 2) + 1 := by
  have hj : 2 ∣ j * (j + 1) := (Nat.even_mul_succ_self j).two_dvd
  obtain ⟨t, ht⟩ := hj
  have h1 : (3 * j + 1) * (3 * j + 2) = 2 * (9 * t + 1) := by nlinarith
  omega

private lemma tri_pairs_card_eq (n : ℕ) :
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 * (p.1 + 1) / 2 + p.2 * (p.2 + 1) / 2 = n)).card =
    ((Finset.range (9 * n + 2 + 1) ×ˢ Finset.range (9 * n + 2 + 1)).filter
      (fun p => p.1 * (p.1 + 1) / 2 + p.2 * (p.2 + 1) / 2 = 9 * n + 2)).card := by
  refine Finset.card_bij (fun p _ => (3 * p.1 + 1, 3 * p.2 + 1)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have e1 := tri_three_mul_add_one p.1
    have e2 := tri_three_mul_add_one p.2
    rw [show 3 * p.1 + 1 + 1 = 3 * p.1 + 2 by omega,
        show 3 * p.2 + 1 + 1 = 3 * p.2 + 2 by omega, e1, e2]
    omega
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    ext <;> omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    have hq1 : 2 ∣ q.1 * (q.1 + 1) := (Nat.even_mul_succ_self q.1).two_dvd
    have hq2 : 2 ∣ q.2 * (q.2 + 1) := (Nat.even_mul_succ_self q.2).two_dvd
    obtain ⟨t1, ht1⟩ := hq1
    obtain ⟨t2, ht2⟩ := hq2
    have hsq : (2 * q.1 + 1) ^ 2 + (2 * q.2 + 1) ^ 2 = 9 * (8 * n + 2) := by
      have : t1 + t2 = 9 * n + 2 := by omega
      nlinarith
    have hmod : q.1 % 3 = 1 ∧ q.2 % 3 = 1 := by
      have h3 : ((2 * q.1 + 1) ^ 2 + (2 * q.2 + 1) ^ 2) % 3 = 0 := by omega
      have h1 : q.1 % 3 = 0 ∨ q.1 % 3 = 1 ∨ q.1 % 3 = 2 := by omega
      have h2 : q.2 % 3 = 0 ∨ q.2 % 3 = 1 ∨ q.2 % 3 = 2 := by omega
      have hsq_mod : ∀ x : ℕ, (2 * x + 1) ^ 2 % 3 = (2 * (x % 3) + 1) ^ 2 % 3 := by
        intro x
        have hx := Nat.div_add_mod x 3
        set r := x % 3
        set d1 := x / 3
        have hrew : (2 * x + 1) ^ 2 = 3 * (12 * d1 ^ 2 + 8 * d1 * r + 4 * d1) + (2 * r + 1) ^ 2 := by
          rw [← hx]; ring
        rw [hrew]; omega
      rw [Nat.add_mod, hsq_mod q.1, hsq_mod q.2] at h3
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp [h1, h2] at h3 ⊢
    refine ⟨(q.1 / 3, q.2 / 3), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      have eq1 : q.1 = 3 * (q.1 / 3) + 1 := by omega
      have eq2 : q.2 = 3 * (q.2 / 3) + 1 := by omega
      have e1 := tri_three_mul_add_one (q.1 / 3)
      have e2 := tri_three_mul_add_one (q.2 / 3)
      rw [← eq1, show 3 * (q.1 / 3) + 2 = q.1 + 1 by omega] at e1
      rw [← eq2, show 3 * (q.2 / 3) + 2 = q.2 + 1 by omega] at e2
      have hsum : (q.1 / 3) * (q.1 / 3 + 1) / 2 + (q.2 / 3) * (q.2 / 3 + 1) / 2 = n := by omega
      have hb1 := le_tri (q.1 / 3)
      have hb2 := le_tri (q.2 / 3)
      exact ⟨⟨by omega, by omega⟩, hsum⟩
    · ext <;> dsimp <;> omega

end OMA.S_oeis_a001936_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001936.main := by
  intro n
  rw [← ZMod.natCast_eq_natCast_iff]
  have hR_sq : OMA.S_oeis_a001936_Proof.R_series * OMA.S_oeis_a001936_Proof.R_series =
      OMA.S_oeis_a001936_Proof.T_series * OMA.S_oeis_a001936_Proof.T_series := by
    calc OMA.S_oeis_a001936_Proof.R_series * OMA.S_oeis_a001936_Proof.R_series
        = (PowerSeries.pentagonalSeries (ZMod 4)) ^ 6 := OMA.S_oeis_a001936_Proof.R_sq_eq_E_pow_six
      _ = (PowerSeries.pentagonalSeries (ZMod 4)) ^ 3 * (PowerSeries.pentagonalSeries (ZMod 4)) ^ 3 := by
        ring
      _ = OMA.S_oeis_a001936_Proof.T_series * OMA.S_oeis_a001936_Proof.T_series := by
        rw [OMA.S_oeis_a001936_Proof.E_cube_eq_T]
  have ha_coeff : ∀ m : ℕ, (OMA.S_oeis_a001936.a m : ZMod 4) =
      PowerSeries.coeff m (OMA.S_oeis_a001936_Proof.R_series * OMA.S_oeis_a001936_Proof.R_series) := by
    intro m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [OMA.S_oeis_a001936.a, OMA.S_oeis_a001936_Proof.R_series]
  rw [ha_coeff n, ha_coeff (9 * n + 2), hR_sq,
    OMA.S_oeis_a001936_Proof.coeff_T_sq n,
    OMA.S_oeis_a001936_Proof.coeff_T_sq (9 * n + 2),
    OMA.S_oeis_a001936_Proof.tri_pairs_card_eq n]
