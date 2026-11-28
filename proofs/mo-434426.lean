import OMAStatements.S_mo_434426
import Mathlib



open OMA.S_mo_434426

private noncomputable def invScale (a : ℝ) (m : ℕ) : ℝ := (scale a m)⁻¹

private theorem scale_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < scale a n := by
  unfold scale
  positivity

private theorem inv_scale_formula (a : ℝ) (n : ℕ) :
    invScale a n = (↑(n+1) : ℝ) * (a⁻¹)^(n+1) := by
  simp [invScale,scale,div_eq_mul_inv,inv_pow]

private theorem inv_scale_sum {a : ℝ} (ha : 1 < a) :
    Summable (invScale a) ∧ ∑' n : ℕ, invScale a n = a/(a-1)^2 := by
  have ha₀ : 0 < a := by linarith
  have hi : a⁻¹ < 1 := by
    simpa only [one_div] using (div_lt_iff₀ ha₀).mpr (show (1 : ℝ) < 1*a by simpa using ha)
  have hn : ‖a⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha₀)]
    exact hi
  have hg := hasSum_coe_mul_geometric_of_norm_lt_one hn
  let g : ℕ → ℝ := fun n => (n : ℝ)*(a⁻¹)^n
  have hg' : HasSum g (a⁻¹/(1-a⁻¹)^2) := hg
  have hShift : (fun n => g (n+1)) = invScale a := by
    funext n
    exact (inv_scale_formula a n).symm
  have hSummable := (summable_nat_add_iff (f := g) 1).mpr hg'.summable
  rw [hShift] at hSummable
  refine ⟨hSummable,?_⟩
  have hSum := hg'.summable.tsum_eq_zero_add
  rw [hShift,show g 0 = 0 by simp [g],zero_add,hg'.tsum_eq] at hSum
  rw [←hSum]
  have hne : a-1 ≠ 0 := by linarith
  have hne' : 1-a⁻¹ ≠ 0 := by linarith
  field_simp [ha₀.ne',hne,hne']

private theorem term_nonneg {a : ℝ} (ha : 0 < a) (m n : ℕ) : 0 ≤ term a m n := by
  have hm := scale_pos ha m
  have hn := scale_pos ha n
  unfold term
  positivity

private theorem symmetrize {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    term a m n + term a n m = invScale a m * invScale a n := by
  have hm := scale_pos ha m
  have hn := scale_pos ha n
  have hmn := (add_pos hm hn).ne'
  have hnm := (add_pos hn hm).ne'
  unfold term invScale
  field_simp [hm.ne',hn.ne',hmn,hnm]
  ring

theorem OMA.solution : type_of% @OMA.S_mo_434426.main := by
  intro a ha
  have ha₀ : 0 < a := by linarith
  obtain ⟨hU,hSum⟩ := inv_scale_sum ha
  let f : ℕ × ℕ → ℝ := fun p => term a p.1 p.2
  let g : ℕ × ℕ → ℝ := fun p => invScale a p.1 * invScale a p.2
  have hG : Summable g := by
    have hg₀ : 0 ≤ g := fun p => mul_nonneg (inv_nonneg.mpr (scale_pos ha₀ p.1).le)
      (inv_nonneg.mpr (scale_pos ha₀ p.2).le)
    apply (summable_prod_of_nonneg hg₀).mpr
    refine ⟨fun m => hU.mul_left (invScale a m),?_⟩
    change Summable (fun m : ℕ => ∑' n : ℕ, invScale a m * invScale a n)
    simp_rw [tsum_mul_left]
    exact hU.mul_right _
  have hF : Summable f := by
    apply Summable.of_nonneg_of_le (fun p => term_nonneg ha₀ p.1 p.2) _ hG
    intro p
    change term a p.1 p.2 ≤ invScale a p.1 * invScale a p.2
    rw [←symmetrize ha₀]
    exact le_add_of_nonneg_right (term_nonneg ha₀ p.2 p.1)
  have hTwo : (∑' p, f p) + (∑' p, f p) = (∑' m, invScale a m) * (∑' m, invScale a m) := by
    calc
      _ = (∑' p, f p) + (∑' p : ℕ × ℕ, f p.swap) := by
        congr 1
        exact ((Equiv.prodComm ℕ ℕ).tsum_eq f).symm
      _ = ∑' p : ℕ × ℕ, (f p + f p.swap) := (hF.tsum_add hF.prod_symm).symm
      _ = ∑' p, g p := tsum_congr (fun p => symmetrize ha₀ p.1 p.2)
      _ = _ := (hU.hasSum.mul hU.hasSum hG).tsum_eq
  rw [←hF.tsum_prod]
  calc
    _ = ((∑' n, invScale a n) * (∑' n, invScale a n))/2 := by linarith
    _ = _ := by
      rw [hSum]
      have hne : a-1 ≠ 0 := by linarith
      field_simp [hne]
