import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1.H3: hypothesis H3 of reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1
-- Credit: @carterleffen

/-!
# Omitted-mass gate-iterate sum bound `sum_n d_n <= 1 + A + D + F`

Proves summability and the explicit upper bound `sum_n d_n <= 1 + A + D + F` for the
continuous omission-loss gate-iterate series from Section 6 of *A quadratic bound for
Jacobsthal's function* (2026), adapted to Lean 4.33.1 from the public `openai/math`
formalization:

* Exact evaluations `d_0 = 1`, `d_1 = A`, and `d_2 = D` via bounded Fubini and
  threshold-window swaps.
* Free-gate scalar majorization of `d_{n+3}` and ordered affine-moment induction.
* Summability and tail comparison against the weighted factorial series `F`.
-/

namespace ErdosOmissionH3

open Set Filter MeasureTheory
open scoped Topology

section CutoffsAndGates

abbrev Profile := Bool → ℝ → ℝ → ℝ

def JointContinuous (H : Profile) : Prop :=
  ∀ i, Continuous (fun p : ℝ × ℝ => H i p.1 p.2)

noncomputable def upperCutoff (i : Bool) (r b : ℝ) : ℝ :=
  if i then max 1 (min (min 2 b) ((r - 2) / 2)) else max 1 (min 2 b)

noncomputable def baseCutoff (b : ℝ) : ℝ := max 1 (min 2 b)

noncomputable def omissionForce (i : Bool) (r b : ℝ) : ℝ :=
  if i then (upperCutoff true r b)⁻¹ - (upperCutoff false r b)⁻¹ else 0

noncomputable def gate (H : Profile) (i : Bool) (r b : ℝ) : ℝ :=
  ∫ x : ℝ in 1..upperCutoff i r b, H (!i) (r - x) x / max 1 x

noncomputable def gateIterate : ℕ → Profile → Profile
  | 0, H => H
  | n + 1, H => gate (gateIterate n H)

theorem gateIterate_eq_iterate (n : ℕ) (H : Profile) :
    gateIterate n H = gate^[n] H := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gateIterate, Function.iterate_succ_apply', ih]

theorem upperCutoff_bounds (i : Bool) (r b : ℝ) :
    1 ≤ upperCutoff i r b ∧ upperCutoff i r b ≤ 2 := by
  cases i
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · exact ⟨le_max_left _ _, max_le (by norm_num) ((min_le_left _ _).trans (min_le_left _ _))⟩

theorem baseCutoff_bounds (b : ℝ) : 1 ≤ baseCutoff b ∧ baseCutoff b ≤ 2 :=
  upperCutoff_bounds false 0 b

theorem baseCutoff_on {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) : baseCutoff b = b := by
  rw [baseCutoff, min_eq_right hb2, max_eq_right hb1]

theorem cutoff_le_base (i : Bool) (r b : ℝ) : upperCutoff i r b ≤ baseCutoff b := by
  cases i
  · exact le_rfl
  · exact max_le_max le_rfl (min_le_left _ _)

theorem upperCutoff_continuous (i : Bool) :
    Continuous (fun p : ℝ × ℝ => upperCutoff i p.1 p.2) := by
  cases i <;> simp only [upperCutoff, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem baseCutoff_continuous : Continuous baseCutoff := by
  unfold baseCutoff
  fun_prop

theorem upperCutoff_odd_small {r b : ℝ} (hr : r ≤ 4) : upperCutoff true r b = 1 := by
  change max 1 (min (min 2 b) ((r - 2) / 2)) = 1
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem le_clipped_upper {x t : ℝ} (hx : 1 < x) : x ≤ max 1 t ↔ x ≤ t := by
  rw [le_max_iff]
  exact or_iff_right (not_le_of_gt hx)

theorem mem_upperCutoff_true (r b x : ℝ) :
    x ∈ Ioc 1 (upperCutoff true r b) ↔ 1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ x ≤ (r - 2) / 2 := by
  constructor
  · intro hx
    have h : x ≤ min (min 2 b) ((r - 2) / 2) := (le_clipped_upper hx.1).mp hx.2
    obtain ⟨hb, hgate⟩ := le_min_iff.mp h
    obtain ⟨hx2, hxb⟩ := le_min_iff.mp hb
    exact ⟨hx.1, hx2, hxb, hgate⟩
  · rintro ⟨hx, hx2, hxb, hgate⟩
    exact ⟨hx, (le_clipped_upper hx).mpr (le_min (le_min hx2 hxb) hgate)⟩

theorem mem_omission_window (r b x : ℝ) :
    x ∈ Ioc (upperCutoff true r b) (baseCutoff b) ↔
      1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ (r - 2) / 2 < x := by
  constructor
  · intro hx
    have hx1 : 1 < x := (upperCutoff_bounds true r b).1.trans_lt hx.1
    have hbase : x ≤ min 2 b := (le_clipped_upper hx1).mp hx.2
    obtain ⟨hx2, hxb⟩ := le_min_iff.mp hbase
    refine ⟨hx1, hx2, hxb, ?_⟩
    by_contra hle
    have hgate : x ≤ (r - 2) / 2 := not_lt.mp hle
    have hm := (mem_upperCutoff_true r b x).mpr ⟨hx1, hx2, hxb, hgate⟩
    exact (not_lt_of_ge hm.2) hx.1
  · rintro ⟨hx1, hx2, hxb, hbad⟩
    refine ⟨?_, (le_clipped_upper hx1).mpr (le_min hx2 hxb)⟩
    change max 1 (min (min 2 b) ((r - 2) / 2)) < x
    exact max_lt hx1 ((min_le_right _ _).trans_lt hbad)

theorem omissionForce_continuous : JointContinuous omissionForce := by
  intro i
  cases i
  · simpa only [omissionForce, Bool.false_eq_true, ↓reduceIte] using continuous_const
  · simp only [omissionForce, ↓reduceIte]
    have h1 := (upperCutoff_continuous true).inv₀ (fun p => ne_of_gt
      ((by norm_num : (0 : ℝ) < 1).trans_le (upperCutoff_bounds true p.1 p.2).1))
    have h2 := (upperCutoff_continuous false).inv₀ (fun p => ne_of_gt
      ((by norm_num : (0 : ℝ) < 1).trans_le (upperCutoff_bounds false p.1 p.2).1))
    exact h1.sub h2

theorem omissionForce_nonnegative (i : Bool) (r b : ℝ) : 0 ≤ omissionForce i r b := by
  cases i
  · simp only [omissionForce, Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [omissionForce, ↓reduceIte]
    apply sub_nonneg.mpr
    have h := one_div_le_one_div_of_le
      ((by norm_num : (0 : ℝ) < 1).trans_le (upperCutoff_bounds true r b).1)
      (cutoff_le_base true r b)
    simpa only [one_div, upperCutoff, baseCutoff, Bool.false_eq_true, ↓reduceIte] using h

theorem omissionForce_le_one (i : Bool) (r b : ℝ) : omissionForce i r b ≤ 1 := by
  cases i
  · simp only [omissionForce, Bool.false_eq_true, ↓reduceIte, zero_le_one]
  · simp only [omissionForce, ↓reduceIte]
    have hc : (upperCutoff true r b)⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ ((by norm_num : (0 : ℝ) < 1).trans_le (upperCutoff_bounds true r b).1)).mpr
        (upperCutoff_bounds true r b).1
    have hb : 0 ≤ (upperCutoff false r b)⁻¹ :=
      inv_nonneg.mpr (zero_le_one.trans (upperCutoff_bounds false r b).1)
    linarith

theorem continuous_variable_upper_integral
    (F : (ℝ × ℝ) → ℝ → ℝ) (hF : Continuous F.uncurry)
    (c : (ℝ × ℝ) → ℝ) (hc : Continuous c) :
    Continuous (fun p => ∫ x in (1 : ℝ)..c p, F p x) := by
  let G : (ℝ × ℝ) → ℝ → ℝ := fun p t => F p ((c p - 1) * t + 1)
  have hG : Continuous G.uncurry := by
    change Continuous (F.uncurry ∘ (fun q : (ℝ × ℝ) × ℝ => (q.1, (c q.1 - 1) * q.2 + 1)))
    apply hF.comp
    exact continuous_fst.prodMk
      (((hc.comp continuous_fst).sub continuous_const).mul continuous_snd |>.add continuous_const)
  have hi : Continuous (fun p => ∫ t in Icc (0 : ℝ) 1, G p t) :=
    continuous_parametric_integral_of_continuous hG isCompact_Icc
  have heq (p : ℝ × ℝ) : (c p - 1) * (∫ t in Icc (0 : ℝ) 1, G p t) = ∫ x in (1 : ℝ)..c p, F p x := by
    have h := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1) (fun x => F p x) (c p - 1) 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc] at h
    simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel, G] using h
  exact ((hc.sub continuous_const).mul hi).congr heq

theorem gate_integrand_continuous {H : Profile} (hH : JointContinuous H) (i : Bool) (r : ℝ) :
    Continuous (fun x : ℝ => H (!i) (r - x) x / max 1 x) := by
  have hc : Continuous (fun x : ℝ => H (!i) (r - x) x) :=
    (hH (!i)).comp ((continuous_const.sub continuous_id).prodMk continuous_id)
  exact hc.div (continuous_const.max continuous_id) (fun x => ne_of_gt
    ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left 1 x)))

theorem gate_continuous {H : Profile} (hH : JointContinuous H) : JointContinuous (gate H) := by
  intro i
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p x => H (!i) (p.1 - x) x / max 1 x
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ => H (!i) (q.1.1 - q.2) q.2) :=
    (hH (!i)).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
  have hd : Continuous (fun q : (ℝ × ℝ) × ℝ => max 1 q.2) := continuous_const.max continuous_snd
  have hF : Continuous F.uncurry := hc.div hd (fun q => ne_of_gt
    ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left 1 q.2)))
  exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem gate_nonnegative {H : Profile} (hH : ∀ i r b, 0 ≤ H i r b) (i : Bool) (r b : ℝ) :
    0 ≤ gate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (upperCutoff_bounds i r b).1
  intro x
  exact div_nonneg (hH (!i) (r - x) x) (zero_le_one.trans (le_max_left 1 x))

theorem gate_zero_of_side (H : Profile) (i : Bool)
    (hH : ∀ r b, H (!i) r b = 0) (r b : ℝ) : gate H i r b = 0 := by
  simp only [gate, hH, zero_div, intervalIntegral.integral_zero]

theorem gateIterate_continuous {H : Profile} (hH : JointContinuous H) (n : ℕ) :
    JointContinuous (gateIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact gate_continuous ih

theorem gateIterate_nonnegative {H : Profile} (hH : ∀ i r b, 0 ≤ H i r b) (n : ℕ) :
    ∀ i r b, 0 ≤ gateIterate n H i r b := by
  induction n with
  | zero => exact hH
  | succ n ih => exact gate_nonnegative ih

theorem omission_wrong_parity_zero (n : ℕ) :
    (∀ r b, gateIterate (2 * n) omissionForce false r b = 0) ∧
      (∀ r b, gateIterate (2 * n + 1) omissionForce true r b = 0) := by
  induction n with
  | zero =>
    constructor
    · intro r b; simp only [gateIterate, omissionForce, Bool.false_eq_true, ↓reduceIte]
    · intro r b
      exact gate_zero_of_side omissionForce true (fun _ _ => by simp [omissionForce]) r b
  | succ n ih =>
    have hE : ∀ r b, gateIterate (2 * (n + 1)) omissionForce false r b = 0 := by
      intro r b
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, gateIterate]
      exact gate_zero_of_side (gateIterate (2 * n + 1) omissionForce) false ih.2 r b
    refine ⟨hE, ?_⟩
    intro r b
    rw [gateIterate]
    exact gate_zero_of_side (gateIterate (2 * (n + 1)) omissionForce) true hE r b

end CutoffsAndGates

section OmissionDensityAndSupport

noncomputable def sourceWeight (i : Bool) (y : ℝ) : ℝ :=
  if i then y ^ 2 else y ^ 2 - 1

def sourceDomain (i : Bool) : Set ℝ :=
  if i then Ioi 0 else Ioi 1

noncomputable def omissionDensity (n : ℕ) (i : Bool) (y : ℝ) : ℝ :=
  2 * sourceWeight i y * gateIterate n omissionForce i (2 * y + 2) 2

noncomputable def omissionLossTerm (n : ℕ) : ℝ :=
  (∫ y in sourceDomain false, omissionDensity n false y) +
    ∫ y in sourceDomain true, omissionDensity n true y

theorem sourceWeight_nonnegative (i : Bool) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ sourceWeight i y := by
  cases i
  · simp only [sourceDomain, Bool.false_eq_true, ↓reduceIte, mem_Ioi] at hy
    simp only [sourceWeight, Bool.false_eq_true, ↓reduceIte]
    nlinarith
  · simp only [sourceWeight, ↓reduceIte]
    exact sq_nonneg y

theorem omissionDensity_continuous (n : ℕ) (i : Bool) : Continuous (omissionDensity n i) := by
  have hw : Continuous (sourceWeight i) := by
    cases i
    · change Continuous (fun y : ℝ => y ^ 2 - 1); fun_prop
    · change Continuous (fun y : ℝ => y ^ 2); fun_prop
  have hc : Continuous (fun y : ℝ => gateIterate n omissionForce i (2 * y + 2) 2) :=
    (gateIterate_continuous omissionForce_continuous n i).comp
      (((continuous_const.mul continuous_id).add continuous_const).prodMk continuous_const)
  exact (continuous_const.mul hw).mul hc

theorem omissionDensity_nonnegative (n : ℕ) (i : Bool) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ omissionDensity n i y :=
  mul_nonneg (mul_nonneg (by norm_num) (sourceWeight_nonnegative i hy))
    (gateIterate_nonnegative omissionForce_nonnegative n i (2 * y + 2) 2)

theorem omissionLossTerm_nonnegative (n : ℕ) : 0 ≤ omissionLossTerm n := by
  unfold omissionLossTerm
  apply add_nonneg
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (sourceDomain false) from measurableSet_Ioi)] with y hy
    exact omissionDensity_nonnegative n false hy
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (sourceDomain true) from measurableSet_Ioi)] with y hy
    exact omissionDensity_nonnegative n true hy

theorem force_high_zero (i : Bool) {r b : ℝ} (hr : 6 ≤ r) : omissionForce i r b = 0 := by
  cases i
  · simp only [omissionForce, Bool.false_eq_true, ↓reduceIte]
  · have hc : upperCutoff true r b = upperCutoff false r b := by
      change max 1 (min (min 2 b) ((r - 2) / 2)) = max 1 (min 2 b)
      rw [min_eq_left ((min_le_left 2 b).trans (by linarith))]
    simp only [omissionForce, ↓reduceIte, hc, sub_self]

theorem iterated_force_high_zero (n : ℕ) (i : Bool) {r b : ℝ}
    (hr : 2 * (n : ℝ) + 6 ≤ r) : gateIterate n omissionForce i r b = 0 := by
  induction n generalizing i r b with
  | zero => exact force_high_zero i (by simpa only [Nat.cast_zero, mul_zero, zero_add] using hr)
  | succ n ih =>
    rw [gateIterate, gate]
    calc
      _ = ∫ _x : ℝ in 1..upperCutoff i r b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hx2 : x ≤ 2 := hx.2.trans (upperCutoff_bounds i r b).2
        rw [ih (!i) (by push_cast at hr; linarith : 2 * (n : ℝ) + 6 ≤ r - x), zero_div]
      _ = 0 := by simp

theorem omissionDensity_high_zero (n : ℕ) (i : Bool) {y : ℝ} (hy : (n : ℝ) + 2 ≤ y) :
    omissionDensity n i y = 0 := by
  rw [omissionDensity, iterated_force_high_zero n i (by linarith : 2 * (n : ℝ) + 6 ≤ 2 * y + 2), mul_zero]

theorem omissionDensity_integrable (n : ℕ) (i : Bool) :
    IntegrableOn (omissionDensity n i) (sourceDomain i) := by
  let a : ℝ := if i then 0 else 1
  let Y : ℝ := (n : ℝ) + 2
  have haY : a ≤ Y := by
    cases i <;> dsimp [a, Y] <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  have hdom : sourceDomain i = Ioi a := by
    cases i <;> simp [sourceDomain, a]
  rw [hdom]
  have hc : IntegrableOn (omissionDensity n i) (Icc a Y) :=
    (omissionDensity_continuous n i).integrableOn_Icc
  have hz : IntegrableOn (omissionDensity n i) (Ioi Y) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi Y) := integrable_zero ℝ ℝ _
    apply hzero.congr_fun _ measurableSet_Ioi
    intro y hy
    exact (omissionDensity_high_zero n i (le_of_lt hy)).symm
  have hu := hc.union hz
  rw [Icc_union_Ioi_eq_Ici haY] at hu
  exact hu.mono_set Ioi_subset_Ici_self

end OmissionDensityAndSupport

section FirstLossTerm

theorem first_odd_density_low {y : ℝ} (hy : y ≤ 1) : omissionDensity 0 true y = y ^ 2 := by
  have hc : upperCutoff true (2 * y + 2) 2 = 1 := upperCutoff_odd_small (by linarith)
  have hf : upperCutoff false (2 * y + 2) 2 = 2 := by norm_num [upperCutoff]
  simp only [omissionDensity, sourceWeight, gateIterate, omissionForce, ↓reduceIte, hc, hf]
  ring

theorem first_odd_density_middle {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2) :
    omissionDensity 0 true y = 2 * y - y ^ 2 := by
  have hc : upperCutoff true (2 * y + 2) 2 = y := by
    change max 1 (min (min 2 2) ((2 * y + 2 - 2) / 2)) = y
    have he : (2 * y + 2 - 2) / 2 = y := by ring
    rw [he, min_self, min_eq_right hy2, max_eq_right hy1]
  have hf : upperCutoff false (2 * y + 2) 2 = 2 := by norm_num [upperCutoff]
  have hn : y ≠ 0 := by linarith
  simp only [omissionDensity, sourceWeight, gateIterate, omissionForce, ↓reduceIte, hc, hf]
  field_simp

theorem first_odd_density_high {y : ℝ} (hy : 2 ≤ y) : omissionDensity 0 true y = 0 := by
  have hc : upperCutoff true (2 * y + 2) 2 = 2 := by
    change max 1 (min (min 2 2) ((2 * y + 2 - 2) / 2)) = 2
    have he : (2 * y + 2 - 2) / 2 = y := by ring
    rw [he, min_self, min_eq_left hy, max_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
  have hf : upperCutoff false (2 * y + 2) 2 = 2 := by norm_num [upperCutoff]
  simp only [omissionDensity, sourceWeight, gateIterate, omissionForce, ↓reduceIte, hc, hf, sub_self, mul_zero]

theorem actual_first_loss_eq_one : omissionLossTerm 0 = 1 := by
  have he : (∫ y in sourceDomain false, omissionDensity 0 false y) = 0 := by
    simp [omissionDensity, sourceWeight, gateIterate, omissionForce]
  have hz : (∫ y in Ioi (2 : ℝ), omissionDensity 0 true y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact first_odd_density_high (le_of_lt hy)
  have hlow : (∫ y : ℝ in 0..1, omissionDensity 0 true y) = (1 : ℝ) / 3 := by
    calc
      _ = ∫ y : ℝ in 0..1, y ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
        exact first_odd_density_low hy.2
      _ = _ := by norm_num
  have hmid : (∫ y : ℝ in 1..2, omissionDensity 0 true y) = (2 : ℝ) / 3 := by
    calc
      _ = ∫ y : ℝ in 1..2, 2 * y - y ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hy
        exact first_odd_density_middle hy.1 hy.2
      _ = _ := by
        have hl : IntervalIntegrable (fun y : ℝ => 2 * y) volume 1 2 :=
          (continuous_const.mul continuous_id).intervalIntegrable 1 2
        have hq : IntervalIntegrable (fun y : ℝ => y ^ 2) volume 1 2 :=
          (continuous_id.pow 2).intervalIntegrable 1 2
        rw [intervalIntegral.integral_sub hl hq, intervalIntegral.integral_const_mul]
        norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((omissionDensity_continuous 0 true).intervalIntegrable (μ := volume) 0 1)
    ((omissionDensity_continuous 0 true).intervalIntegrable (μ := volume) 1 2)
  rw [hlow, hmid] at hsplit
  have hall := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 0 true) (by norm_num : (0 : ℝ) ≤ 2)
  rw [hz, sub_zero] at hall
  unfold omissionLossTerm
  rw [he, zero_add]
  change (∫ y in Ioi 0, omissionDensity 0 true y) = 1
  linarith

end FirstLossTerm

section FubiniAndThreshold

theorem bounded_rectangle_integrable {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (a b c d C : ℝ)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |f (x, y)| ≤ C) :
    Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc c d)
  let : IsFiniteMeasure μ := ⟨by
    dsimp [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmem : ∀ᵐ p : ℝ × ℝ ∂μ.prod ν, p.1 ∈ Icc a b ∧ p.2 ∈ Icc c d := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact ⟨hx, hy⟩
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hmem] with p hp
  simpa only [Real.norm_eq_abs] using hbound p.1 hp.1 p.2 hp.2

theorem bounded_rectangle_swap {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (a b c d C : ℝ)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |f (x, y)| ≤ C) :
    (∫ x in Icc a b, ∫ y in Icc c d, f (x, y)) =
      ∫ y in Icc c d, ∫ x in Icc a b, f (x, y) :=
  integral_integral_swap (bounded_rectangle_integrable hf a b c d C hbound)

theorem ordered_triangle_swap {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc (1 : ℝ) 2, ∀ t ∈ Icc (1 : ℝ) 2, |f (x, t)| ≤ C) :
    (∫ x : ℝ in 1..2, ∫ t : ℝ in 1..x, f (x, t)) =
      ∫ t : ℝ in 1..2, ∫ x : ℝ in t..2, f (x, t) := by
  classical
  let g : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then f p else 0
  have hg : Measurable g :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) hf measurable_const
  have hb : ∀ x ∈ Icc (1 : ℝ) 2, ∀ t ∈ Icc (1 : ℝ) 2, |g (x, t)| ≤ C := by
    intro x hx t ht
    dsimp only [g]
    split_ifs
    · exact hbound x hx t ht
    · simpa only [abs_zero] using hC
  have hs := bounded_rectangle_swap hg 1 2 1 2 C hb
  have hleft (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) :
      (∫ t in Icc (1 : ℝ) 2, g (x, t)) = ∫ t : ℝ in 1..x, f (x, t) := by
    have hset : Icc (1 : ℝ) 2 ∩ Iic x = Icc 1 x := by
      ext t
      constructor
      · rintro ⟨ht, hx'⟩; exact ⟨ht.1, hx'⟩
      · intro ht; exact ⟨⟨ht.1, ht.2.trans hx.2⟩, ht.2⟩
    change (∫ t in Icc (1 : ℝ) 2, (Iic x).indicator (fun t => f (x, t)) t) = _
    rw [setIntegral_indicator measurableSet_Iic, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx.1]
  have hright (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) :
      (∫ x in Icc (1 : ℝ) 2, g (x, t)) = ∫ x : ℝ in t..2, f (x, t) := by
    have hset : Icc (1 : ℝ) 2 ∩ Ici t = Icc t 2 := by
      ext x
      constructor
      · rintro ⟨hx, ht'⟩; exact ⟨ht', hx.2⟩
      · intro hx; exact ⟨⟨ht.1.trans hx.1, hx.2⟩, hx.1⟩
    change (∫ x in Icc (1 : ℝ) 2, (Ici t).indicator (fun x => f (x, t)) x) = _
    rw [setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.2]
  have he : (∫ x in Icc (1 : ℝ) 2, ∫ t in Icc (1 : ℝ) 2, g (x, t)) =
      ∫ x in Icc (1 : ℝ) 2, ∫ t : ℝ in 1..x, f (x, t) :=
    setIntegral_congr_fun measurableSet_Icc hleft
  have ho : (∫ t in Icc (1 : ℝ) 2, ∫ x in Icc (1 : ℝ) 2, g (x, t)) =
      ∫ t in Icc (1 : ℝ) 2, ∫ x : ℝ in t..2, f (x, t) :=
    setIntegral_congr_fun measurableSet_Icc hright
  rw [he, ho] at hs
  simpa only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hs

theorem weighted_threshold_swap {P W T : ℝ → ℝ}
    (hP : Measurable P) (hW : Measurable W) (hT : Measurable T)
    (a Y b CP CW : ℝ) (hCP : 0 ≤ CP) (hCW : 0 ≤ CW)
    (hPb : ∀ y ∈ Icc a Y, |P y| ≤ CP)
    (hWb : ∀ t ∈ Icc (1 : ℝ) b, |W t| ≤ CW)
    (hTb : ∀ t ∈ Icc (1 : ℝ) b, a ≤ T t ∧ T t ≤ Y) :
    (∫ y in Icc a Y, P y * (∫ t in Icc (1 : ℝ) b, if y < T t then W t else 0)) =
      ∫ t in Icc (1 : ℝ) b, W t * (∫ y : ℝ in a..T t, P y) := by
  classical
  let G : ℝ × ℝ → ℝ := fun p => if p.1 < T p.2 then P p.1 * W p.2 else 0
  have hG : Measurable G := Measurable.ite
    (measurableSet_lt measurable_fst (hT.comp measurable_snd))
    ((hP.comp measurable_fst).mul (hW.comp measurable_snd)) measurable_const
  have hb : ∀ y ∈ Icc a Y, ∀ t ∈ Icc (1 : ℝ) b, |G (y, t)| ≤ CP * CW := by
    intro y hy t ht
    dsimp only [G]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hPb y hy) (hWb t ht) (abs_nonneg _) hCP
    · simpa only [abs_zero] using mul_nonneg hCP hCW
  have hs := bounded_rectangle_swap hG a Y 1 b (CP * CW) hb
  have hleft (y : ℝ) : (∫ t in Icc (1 : ℝ) b, G (y, t)) =
      P y * (∫ t in Icc (1 : ℝ) b, if y < T t then W t else 0) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [G]
    split_ifs <;> simp
  have hright (t : ℝ) (ht : t ∈ Icc (1 : ℝ) b) :
      (∫ y in Icc a Y, G (y, t)) = W t * (∫ y : ℝ in a..T t, P y) := by
    have hset : Icc a Y ∩ Iio (T t) = Ico a (T t) := by
      ext y
      constructor
      · rintro ⟨hy, hyT⟩; exact ⟨hy.1, hyT⟩
      · intro hy; exact ⟨⟨hy.1, hy.2.le.trans (hTb t ht).2⟩, hy.2⟩
    have he : (fun y : ℝ => G (y, t)) = (Iio (T t)).indicator (fun y => W t * P y) := by
      funext y
      dsimp only [G]
      by_cases hh : y < T t
      · rw [if_pos hh, indicator_of_mem (show y ∈ Iio (T t) from hh)]
        ring
      · rw [if_neg hh, indicator_of_notMem (show y ∉ Iio (T t) from hh)]
    rw [he, setIntegral_indicator measurableSet_Iio, hset, integral_const_mul,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hTb t ht).1]
  simp_rw [hleft] at hs
  rw [hs]
  exact setIntegral_congr_fun measurableSet_Icc hright

theorem reciprocal_square_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, (x ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hn : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (uIcc a b) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hn x hx))
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t : ℝ => -t⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    simpa only [neg_neg] using! (hasDerivAt_inv (hn x hx)).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
  ring

theorem omissionForce_odd_integral (r b : ℝ) :
    omissionForce true r b = ∫ x : ℝ in upperCutoff true r b..baseCutoff b, (x ^ 2)⁻¹ := by
  rw [reciprocal_square_integral (upperCutoff_bounds true r b).1 (cutoff_le_base true r b)]
  rfl

theorem force_as_threshold (a y : ℝ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    omissionForce true (2 * y + 2 - a) b =
      ∫ t : ℝ in 1..b, if y < a / 2 + t then (t ^ 2)⁻¹ else 0 := by
  classical
  let r := 2 * y + 2 - a
  have hb : baseCutoff b = b := baseCutoff_on hb1 hb2
  have hc : upperCutoff true r b ≤ b := by simpa only [hb] using cutoff_le_base true r b
  have hset : Ioc (upperCutoff true r b) b = Ioc (1 : ℝ) b ∩ {t : ℝ | y < a / 2 + t} := by
    ext t
    have he := mem_omission_window r b t
    rw [hb] at he
    constructor
    · intro ht
      obtain ⟨ht1, _ht2, htb, hbad⟩ := he.mp ht
      refine ⟨⟨ht1, htb⟩, ?_⟩
      change y < a / 2 + t
      dsimp [r] at hbad
      linarith
    · rintro ⟨⟨ht1, htb⟩, hy⟩
      apply he.mpr
      refine ⟨ht1, htb.trans hb2, htb, ?_⟩
      change y < a / 2 + t at hy
      dsimp [r]
      linarith
  have hm : MeasurableSet {t : ℝ | y < a / 2 + t} :=
    measurableSet_lt measurable_const (measurable_const.add measurable_id)
  rw [omissionForce_odd_integral, hb, intervalIntegral.integral_of_le hc, intervalIntegral.integral_of_le hb1]
  change (∫ t in Ioc (upperCutoff true r b) b, (t ^ 2)⁻¹) =
    ∫ t in Ioc (1 : ℝ) b, ({t : ℝ | y < a / 2 + t}).indicator (fun t => (t ^ 2)⁻¹) t
  rw [setIntegral_indicator hm, hset]

theorem quadratic_window_integral (l u e : ℝ) :
    (∫ y : ℝ in l..u, y ^ 2 - e) = (u ^ 3 - l ^ 3) / 3 - e * (u - l) := by
  have hp : IntervalIntegrable (fun y : ℝ => y ^ 2) volume l u :=
    (continuous_id.pow 2).intervalIntegrable l u
  have hc : IntervalIntegrable (fun _y : ℝ => e) volume l u := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hp hc, integral_pow, intervalIntegral.integral_const]
  norm_num
  ring

theorem integrated_force_window (a l Y b e : ℝ) (hl : 0 ≤ l) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (hlT : l ≤ a / 2 + 1) (hTY : a / 2 + b ≤ Y) :
    (∫ y : ℝ in l..Y, (y ^ 2 - e) * omissionForce true (2 * y + 2 - a) b) =
      ∫ t : ℝ in 1..b, (((a / 2 + t) ^ 3 - l ^ 3) / 3 - e * (a / 2 + t - l)) / (t ^ 2) := by
  have hlY : l ≤ Y := by linarith
  have hP : Measurable (fun y : ℝ => y ^ 2 - e) := (measurable_id.pow_const 2).sub measurable_const
  have hW : Measurable (fun t : ℝ => (t ^ 2)⁻¹) := (measurable_id.pow_const 2).inv
  have hT : Measurable (fun t : ℝ => a / 2 + t) := measurable_const.add measurable_id
  have hPb : ∀ y ∈ Icc l Y, |y ^ 2 - e| ≤ Y ^ 2 + |e| := by
    intro y hy
    have hy0 : 0 ≤ y := hl.trans hy.1
    have hy2 : y ^ 2 ≤ Y ^ 2 := by nlinarith [hy.2]
    calc
      _ ≤ |y ^ 2| + |e| := abs_sub _ _
      _ = y ^ 2 + |e| := by rw [abs_of_nonneg (sq_nonneg y)]
      _ ≤ _ := add_le_add hy2 le_rfl
  have hWb : ∀ t ∈ Icc (1 : ℝ) b, |(t ^ 2)⁻¹| ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
    apply (inv_le_one₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [ht.1]
  have hTb : ∀ t ∈ Icc (1 : ℝ) b, l ≤ a / 2 + t ∧ a / 2 + t ≤ Y := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := weighted_threshold_swap hP hW hT l Y b (Y ^ 2 + |e|) 1
    (by positivity) (by norm_num) hPb hWb hTb
  have hinner (y : ℝ) :
      (∫ t in Icc (1 : ℝ) b, if y < a / 2 + t then (t ^ 2)⁻¹ else 0) =
        omissionForce true (2 * y + 2 - a) b := by
    rw [force_as_threshold a y hb1 hb2, intervalIntegral.integral_of_le hb1, ← integral_Icc_eq_integral_Ioc]
  simp_rw [hinner, quadratic_window_integral] at h
  rw [intervalIntegral.integral_of_le hlY, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hb1, ← integral_Icc_eq_integral_Ioc]
  rw [h]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  ring

end FubiniAndThreshold

section SecondLossTerm

noncomputable def loss2Kernel (t x : ℝ) : ℝ :=
  ((((x + 2 * t) ^ 3 - 8) / 12) - (x + 2 * t - 2)) / (x * t ^ 2)

noncomputable def L2 : ℝ :=
  ∫ t : ℝ in 1..2, ∫ x : ℝ in t..2, loss2Kernel t x

theorem second_loss_bounded : omissionLossTerm 1 = ∫ y : ℝ in 1..3, omissionDensity 1 false y := by
  have ho : (∫ y in sourceDomain true, omissionDensity 1 true y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _hy
    have h := (omission_wrong_parity_zero 0).2 (2 * y + 2) 2
    norm_num only [Nat.mul_zero, Nat.zero_add] at h
    rw [omissionDensity, h, mul_zero]
  have hz : (∫ y in Ioi (3 : ℝ), omissionDensity 1 false y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact omissionDensity_high_zero 1 false (by norm_num; change 3 < y at hy; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 1 false) (by norm_num : (1 : ℝ) ≤ 3)
  rw [hz, sub_zero] at h
  rw [omissionLossTerm, ho, add_zero]
  exact h

noncomputable def secondKernel (p : ℝ × ℝ) : ℝ :=
  (2 * (p.1 ^ 2 - 1) / max 1 p.2) * omissionForce true (2 * p.1 + 2 - p.2) p.2

theorem secondKernel_continuous : Continuous secondKernel := by
  have hf : Continuous (fun p : ℝ × ℝ => omissionForce true (2 * p.1 + 2 - p.2) p.2) :=
    (omissionForce_continuous true).comp
      (((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_snd).prodMk continuous_snd)
  have hp : Continuous (fun p : ℝ × ℝ => 2 * (p.1 ^ 2 - 1) / max 1 p.2) :=
    (continuous_const.mul ((continuous_fst.pow 2).sub continuous_const)).div
      (continuous_const.max continuous_snd) (fun p => ne_of_gt
        ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left 1 p.2)))
  exact hp.mul hf

theorem secondKernel_bound {y x : ℝ} (hy : y ∈ Icc (1 : ℝ) 3) (hx : x ∈ Icc (1 : ℝ) 2) :
    |secondKernel (y, x)| ≤ 16 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hpoly : 0 ≤ y ^ 2 - 1 := by nlinarith [hy.1]
  have hpoly8 : y ^ 2 - 1 ≤ 8 := by nlinarith [hy.1, hy.2]
  have hp0 : 0 ≤ 2 * (y ^ 2 - 1) / x := div_nonneg (mul_nonneg (by norm_num) hpoly) hx0.le
  have hp16 : 2 * (y ^ 2 - 1) / x ≤ 16 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith [hx.1]
  unfold secondKernel
  dsimp only
  rw [max_eq_right hx.1, abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative true _ _))]
  calc
    _ ≤ (2 * (y ^ 2 - 1) / x) * 1 := mul_le_mul_of_nonneg_left (omissionForce_le_one true _ _) hp0
    _ ≤ 16 := by simpa only [mul_one] using hp16

theorem second_density_kernel (y : ℝ) :
    omissionDensity 1 false y = ∫ x : ℝ in 1..2, secondKernel (y, x) := by
  change 2 * (y ^ 2 - 1) * (∫ x : ℝ in 1..upperCutoff false (2 * y + 2) 2,
    omissionForce true (2 * y + 2 - x) x / max 1 x) = _
  have hc : upperCutoff false (2 * y + 2) 2 = 2 := by norm_num [upperCutoff]
  rw [hc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [secondKernel]
  ring

theorem secondKernel_integral {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    (∫ y in Icc (1 : ℝ) 3, secondKernel (y, x)) = ∫ t : ℝ in 1..x, loss2Kernel t x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have h := integrated_force_window x 1 3 x 1 (by norm_num) hx.1 hx.2
    (by linarith [hx.1]) (by linarith [hx.2])
  have he : (fun y : ℝ => secondKernel (y, x)) =
      (fun y => (2 / x) * ((y ^ 2 - 1) * omissionForce true (2 * y + 2 - x) x)) := by
    funext y
    simp only [secondKernel, max_eq_right hx.1]
    ring
  rw [he, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3), h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx.1] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  dsimp only [loss2Kernel]
  field_simp
  ring

theorem second_loss_ordered_integral :
    omissionLossTerm 1 = ∫ x : ℝ in 1..2, ∫ t : ℝ in 1..x, loss2Kernel t x := by
  rw [second_loss_bounded]
  simp_rw [second_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), ← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap secondKernel_continuous.measurable 1 3 1 2 16
    (fun _ hy _ hx => secondKernel_bound hy hx)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact secondKernel_integral hx

theorem lossTwo_measurable : Measurable (fun p : ℝ × ℝ => loss2Kernel p.2 p.1) := by
  unfold loss2Kernel
  fun_prop

theorem lossTwo_bound {x t : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc (1 : ℝ) 2) :
    |loss2Kernel t x| ≤ 16 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have he : loss2Kernel t x = ((x + 2 * t - 2) ^ 2 * (x + 2 * t + 4)) / (12 * x * t ^ 2) := by
    unfold loss2Kernel
    field_simp
    ring
  have hs : 0 ≤ x + 2 * t - 2 ∧ x + 2 * t - 2 ≤ 4 := by constructor <;> linarith [hx.1, hx.2, ht.1, ht.2]
  have hs2 : (x + 2 * t - 2) ^ 2 ≤ 16 := by nlinarith
  have hs4 : 0 ≤ x + 2 * t + 4 ∧ x + 2 * t + 4 ≤ 10 := by constructor <;> linarith [hx.1, hx.2, ht.1, ht.2]
  have hnum : (x + 2 * t - 2) ^ 2 * (x + 2 * t + 4) ≤ 160 := by
    have h := mul_le_mul hs2 hs4.2 hs4.1 (by norm_num : (0 : ℝ) ≤ 16)
    norm_num at h
    exact h
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [ht.1]
  have hden : 12 ≤ 12 * x * t ^ 2 := by
    have h := mul_le_mul hx.1 ht2 (by norm_num : (0 : ℝ) ≤ 1) hx0.le
    nlinarith
  have hden0 : 0 < 12 * x * t ^ 2 := by positivity
  rw [he, abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hs4.1) hden0.le)]
  apply (div_le_iff₀ hden0).mpr
  nlinarith

theorem actual_second_loss_eq_L2 : omissionLossTerm 1 = L2 := by
  rw [second_loss_ordered_integral]
  exact ordered_triangle_swap lossTwo_measurable (by norm_num : (0 : ℝ) ≤ 16)
    (fun _ hx _ ht => lossTwo_bound hx ht)

end SecondLossTerm

section ThirdLossTerm

noncomputable def loss3Kernel (t u x : ℝ) : ℝ :=
  ((x + u + 2 * t) ^ 3 - 8 * x ^ 3) / (12 * x * u * t ^ 2)

noncomputable def L3 : ℝ :=
  ∫ t : ℝ in 1..2, ∫ u : ℝ in t..2, ∫ x : ℝ in u..2, loss3Kernel t u x

theorem third_loss_bounded : omissionLossTerm 2 = ∫ y : ℝ in 0..4, omissionDensity 2 true y := by
  have he : (∫ y in sourceDomain false, omissionDensity 2 false y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _hy
    have h := (omission_wrong_parity_zero 1).1 (2 * y + 2) 2
    norm_num only [Nat.mul_one] at h
    rw [omissionDensity, h, mul_zero]
  have hz : (∫ y in Ioi (4 : ℝ), omissionDensity 2 true y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact omissionDensity_high_zero 2 true (by norm_num; change 4 < y at hy; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 2 true) (by norm_num : (0 : ℝ) ≤ 4)
  rw [hz, sub_zero] at h
  rw [omissionLossTerm, he, zero_add]
  exact h

theorem odd_gate_indicator (H : Profile) (y : ℝ) :
    gate H true (2 * y + 2) 2 =
      ∫ x : ℝ in 1..2, if x ≤ y then H false (2 * y + 2 - x) x / max 1 x else 0 := by
  classical
  have heq : Ioc (1 : ℝ) (upperCutoff true (2 * y + 2) 2) = Ioc (1 : ℝ) 2 ∩ Iic y := by
    ext x
    have hc := mem_upperCutoff_true (2 * y + 2) 2 x
    constructor
    · intro hx
      obtain ⟨hx1, hx2, _hxb, ha⟩ := hc.mp hx
      refine ⟨⟨hx1, hx2⟩, ?_⟩
      change x ≤ y
      linarith
    · rintro ⟨⟨hx1, hx2⟩, hxy⟩
      apply hc.mpr
      refine ⟨hx1, hx2, hx2, ?_⟩
      change x ≤ y at hxy
      linarith
  rw [gate, intervalIntegral.integral_of_le (upperCutoff_bounds true (2 * y + 2) 2).1,
    intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  change (∫ x in Ioc (1 : ℝ) (upperCutoff true (2 * y + 2) 2), H false (2 * y + 2 - x) x / max 1 x) =
    ∫ x in Ioc (1 : ℝ) 2, (Iic y).indicator (fun x => H false (2 * y + 2 - x) x / max 1 x) x
  rw [setIntegral_indicator measurableSet_Iic, heq]

theorem gate_force_bounds (i : Bool) (r b : ℝ) :
    0 ≤ gate omissionForce i r b ∧ gate omissionForce i r b ≤ 1 := by
  have hnon := gate_nonnegative omissionForce_nonnegative i r b
  refine ⟨hnon, ?_⟩
  have hb (x : ℝ) : |omissionForce (!i) (r - x) x / max 1 x| ≤ 1 := by
    have hd : 0 < max (1 : ℝ) x := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left 1 x)
    rw [abs_div, abs_of_pos hd, abs_of_nonneg (omissionForce_nonnegative _ _ _)]
    exact (div_le_one hd).mpr ((omissionForce_le_one _ _ _).trans (le_max_left 1 x))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := upperCutoff i r b)
    (C := 1) (f := fun x => omissionForce (!i) (r - x) x / max 1 x)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hb x)
  have hc := upperCutoff_bounds i r b
  rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (by linarith : 0 ≤ upperCutoff i r b - 1)] at h
  change |gate omissionForce i r b| ≤ upperCutoff i r b - 1 at h
  rw [abs_of_nonneg hnon] at h
  linarith

noncomputable def thirdKernel (p : ℝ × ℝ) : ℝ :=
  if p.2 ≤ p.1 then (2 * p.1 ^ 2 / max 1 p.2) * gate omissionForce false (2 * p.1 + 2 - p.2) p.2 else 0

theorem thirdKernel_measurable : Measurable thirdKernel := by
  have hg := gate_continuous omissionForce_continuous false
  have hc : Continuous (fun p : ℝ × ℝ => gate omissionForce false (2 * p.1 + 2 - p.2) p.2) :=
    hg.comp (((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_snd).prodMk continuous_snd)
  have hp : Measurable (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / max 1 p.2) := by fun_prop
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (hp.mul hc.measurable) measurable_const

theorem thirdKernel_bound {y x : ℝ} (hy : y ∈ Icc (0 : ℝ) 4) (hx : x ∈ Icc (1 : ℝ) 2) :
    |thirdKernel (y, x)| ≤ 32 := by
  have hx0 : 0 < x := by linarith [hx.1]
  unfold thirdKernel
  dsimp only
  split_ifs
  · rw [max_eq_right hx.1]
    have hp0 : 0 ≤ 2 * y ^ 2 / x := by positivity
    have hp32 : 2 * y ^ 2 / x ≤ 32 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith [hy.1, hy.2, hx.1]
    rw [abs_of_nonneg (mul_nonneg hp0 (gate_force_bounds _ _ _).1)]
    exact (mul_le_mul_of_nonneg_left (gate_force_bounds _ _ _).2 hp0).trans (by simpa only [mul_one] using hp32)
  · norm_num

theorem third_density_kernel (y : ℝ) :
    omissionDensity 2 true y = ∫ x : ℝ in 1..2, thirdKernel (y, x) := by
  change 2 * y ^ 2 * gate (gate omissionForce) true (2 * y + 2) 2 = _
  rw [odd_gate_indicator, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [thirdKernel]
  split_ifs <;> ring

noncomputable def thirdInnerKernel (x : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 / max 1 p.2) * omissionForce true (2 * p.1 + 2 - x - p.2) p.2

theorem thirdInnerKernel_continuous (x : ℝ) : Continuous (thirdInnerKernel x) := by
  have hf : Continuous (fun p : ℝ × ℝ => omissionForce true (2 * p.1 + 2 - x - p.2) p.2) :=
    (omissionForce_continuous true).comp
      ((((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_const).sub continuous_snd).prodMk continuous_snd)
  have hp : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 / max 1 p.2) :=
    (continuous_fst.pow 2).div (continuous_const.max continuous_snd) (fun p => ne_of_gt
      ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left 1 p.2)))
  exact hp.mul hf

theorem thirdInnerKernel_bound {x y u : ℝ} (hx : x ∈ Icc (1 : ℝ) 2)
    (hy : y ∈ Icc x 4) (hu : u ∈ Icc (1 : ℝ) x) : |thirdInnerKernel x (y, u)| ≤ 16 := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hy0 : 0 ≤ y := by linarith [hx.1, hy.1]
  have hp0 : 0 ≤ y ^ 2 / u := div_nonneg (sq_nonneg _) hu0.le
  have hp16 : y ^ 2 / u ≤ 16 := by
    apply (div_le_iff₀ hu0).mpr
    nlinarith [hy.2, hu.1]
  unfold thirdInnerKernel
  dsimp only
  rw [max_eq_right hu.1, abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative _ _ _))]
  exact (mul_le_mul_of_nonneg_left (omissionForce_le_one _ _ _) hp0).trans (by simpa only [mul_one] using hp16)

theorem third_even_gate (y : ℝ) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    y ^ 2 * gate omissionForce false (2 * y + 2 - x) x =
      ∫ u : ℝ in 1..x, thirdInnerKernel x (y, u) := by
  have hc : upperCutoff false (2 * y + 2 - x) x = x := baseCutoff_on hx.1 hx.2
  rw [gate, hc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  simp only [thirdInnerKernel, Bool.not_false]
  ring

theorem thirdInner_integral {x u : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) (hu : u ∈ Icc (1 : ℝ) x) :
    (2 / x) * (∫ y in Icc x 4, thirdInnerKernel x (y, u)) =
      ∫ t : ℝ in 1..u, loss3Kernel t u x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hu2 : u ≤ 2 := hu.2.trans hx.2
  have h := integrated_force_window (x + u) x 4 u 0 (by linarith [hx.1]) hu.1 hu2
    (by linarith [hx.2, hu.1]) (by linarith [hx.2])
  have he : (fun y : ℝ => thirdInnerKernel x (y, u)) =
      (fun y => u⁻¹ * (y ^ 2 * omissionForce true (2 * y + 2 - (x + u)) u)) := by
    funext y
    have hh : 2 * y + 2 - x - u = 2 * y + 2 - (x + u) := by ring
    simp only [thirdInnerKernel, max_eq_right hu.1, hh]
    ring
  rw [he, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx.2] : x ≤ 4)]
  simp only [sub_zero, zero_mul, sub_zero] at h
  rw [h, ← mul_assoc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  dsimp only [loss3Kernel]
  field_simp
  ring

theorem thirdKernel_integral {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    (∫ y in Icc (0 : ℝ) 4, thirdKernel (y, x)) =
      ∫ u : ℝ in 1..x, ∫ t : ℝ in 1..u, loss3Kernel t u x := by
  classical
  have he : (fun y : ℝ => thirdKernel (y, x)) =
      (Ici x).indicator (fun y => (2 / x) * (y ^ 2 * gate omissionForce false (2 * y + 2 - x) x)) := by
    funext y
    dsimp only [thirdKernel]
    by_cases hh : x ≤ y
    · rw [if_pos hh, indicator_of_mem (show y ∈ Ici x from hh), max_eq_right hx.1]
      ring
    · rw [if_neg hh, indicator_of_notMem (show y ∉ Ici x from hh)]
  have hset : Icc (0 : ℝ) 4 ∩ Ici x = Icc x 4 := by
    ext y
    constructor
    · rintro ⟨hy, hxy⟩; exact ⟨hxy, hy.2⟩
    · intro hy; exact ⟨⟨by linarith [hx.1, hy.1], hy.2⟩, hy.1⟩
  rw [he, setIntegral_indicator measurableSet_Ici, hset, integral_const_mul]
  simp_rw [third_even_gate _ hx, intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap (thirdInnerKernel_continuous x).measurable x 4 1 x 16
    (fun _ hy _ hu => thirdInnerKernel_bound hx hy hu), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  exact thirdInner_integral hx hu

theorem third_loss_ordered_integral :
    omissionLossTerm 2 = ∫ x : ℝ in 1..2, ∫ u : ℝ in 1..x, ∫ t : ℝ in 1..u, loss3Kernel t u x := by
  rw [third_loss_bounded]
  simp_rw [third_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), ← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap thirdKernel_measurable 0 4 1 2 32
    (fun _ hy _ hx => thirdKernel_bound hy hx)]
  exact setIntegral_congr_fun measurableSet_Icc (fun _ hx => thirdKernel_integral hx)

theorem lossThree_bound {x u t : ℝ} (hx : x ∈ Icc (1 : ℝ) 2)
    (hu : u ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc (1 : ℝ) 2) : |loss3Kernel t u x| ≤ 64 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hu0 : 0 < u := by linarith [hu.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hs0 : 0 ≤ x + u + 2 * t := by positivity
  have hs8 : x + u + 2 * t ≤ 8 := by linarith [hx.2, hu.2, ht.2]
  have hsx : 2 * x ≤ x + u + 2 * t := by linarith [hx.2, hu.1, ht.1]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * x) hsx 3
  have hnum0 : 0 ≤ (x + u + 2 * t) ^ 3 - 8 * x ^ 3 := by nlinarith
  have hp8 := pow_le_pow_left₀ hs0 hs8 3
  have hnum : (x + u + 2 * t) ^ 3 - 8 * x ^ 3 ≤ 512 := by nlinarith [pow_nonneg hx0.le 3]
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [ht.1]
  have hxu : (1 : ℝ) ≤ x * u := by
    simpa only [one_mul] using mul_le_mul hx.1 hu.1 (by norm_num : (0 : ℝ) ≤ 1) hx0.le
  have hprod : (1 : ℝ) ≤ x * u * t ^ 2 := by
    simpa only [one_mul] using mul_le_mul hxu ht2 (by norm_num : (0 : ℝ) ≤ 1) (mul_pos hx0 hu0).le
  have hden : 12 ≤ 12 * x * u * t ^ 2 := by nlinarith
  have hden0 : 0 < 12 * x * u * t ^ 2 := by positivity
  rw [loss3Kernel, abs_of_nonneg (div_nonneg hnum0 hden0.le)]
  apply (div_le_iff₀ hden0).mpr
  nlinarith

noncomputable def clampedThird (x u t : ℝ) : ℝ :=
  loss3Kernel (baseCutoff t) (baseCutoff u) (baseCutoff x)

theorem clampedThird_eq {x u t : ℝ} (hx : x ∈ Icc (1 : ℝ) 2)
    (hu : u ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc (1 : ℝ) 2) :
    clampedThird x u t = loss3Kernel t u x := by
  simp only [clampedThird, baseCutoff_on hx.1 hx.2, baseCutoff_on hu.1 hu.2, baseCutoff_on ht.1 ht.2]

theorem clampedThird_bound (x u t : ℝ) : |clampedThird x u t| ≤ 64 :=
  lossThree_bound (baseCutoff_bounds x) (baseCutoff_bounds u) (baseCutoff_bounds t)

theorem clampedThird_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ => clampedThird p.1 p.2.1 p.2.2) := by
  have hn : Continuous (fun p : ℝ × ℝ × ℝ =>
      (baseCutoff p.1 + baseCutoff p.2.1 + 2 * baseCutoff p.2.2) ^ 3 - 8 * (baseCutoff p.1) ^ 3) := by
    unfold baseCutoff
    fun_prop
  have hd : Continuous (fun p : ℝ × ℝ × ℝ =>
      12 * baseCutoff p.1 * baseCutoff p.2.1 * (baseCutoff p.2.2) ^ 2) := by
    unfold baseCutoff
    fun_prop
  have hp (a : ℝ) : 0 < baseCutoff a := zero_lt_one.trans_le (baseCutoff_bounds a).1
  exact hn.div hd (fun p => ne_of_gt
    (mul_pos (mul_pos (mul_pos (by norm_num) (hp p.1)) (hp p.2.1)) (sq_pos_of_pos (hp p.2.2))))

noncomputable def thirdLowerIntegral (p : ℝ × ℝ) : ℝ :=
  ∫ t : ℝ in 1..baseCutoff p.2, clampedThird p.1 p.2 t

noncomputable def thirdUpperIntegral (p : ℝ × ℝ) : ℝ :=
  ∫ x : ℝ in baseCutoff p.1..2, clampedThird x p.1 p.2

theorem thirdLowerIntegral_continuous : Continuous thirdLowerIntegral := by
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p t => clampedThird p.1 p.2 t
  have hF : Continuous F.uncurry := by
    change Continuous ((fun q : ℝ × ℝ × ℝ => clampedThird q.1 q.2.1 q.2.2) ∘
      (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2)))
    exact clampedThird_continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  exact continuous_variable_upper_integral F hF (fun p => baseCutoff p.2)
    (baseCutoff_continuous.comp continuous_snd)

theorem thirdUpperIntegral_continuous : Continuous thirdUpperIntegral := by
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p x => clampedThird x p.1 p.2
  have hF : Continuous F.uncurry := by
    change Continuous ((fun q : ℝ × ℝ × ℝ => clampedThird q.1 q.2.1 q.2.2) ∘
      (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.1, p.1.2)))
    exact clampedThird_continuous.comp
      (continuous_snd.prodMk (continuous_fst.fst.prodMk continuous_fst.snd))
  have h2 := continuous_variable_upper_integral F hF (fun _ => (2 : ℝ)) continuous_const
  have hc := continuous_variable_upper_integral F hF (fun p => baseCutoff p.1)
    (baseCutoff_continuous.comp continuous_fst)
  have he (p : ℝ × ℝ) : (∫ x : ℝ in 1..2, F p x) - (∫ x : ℝ in 1..baseCutoff p.1, F p x) = thirdUpperIntegral p := by
    have hf : Continuous (F p) := by
      change Continuous (F.uncurry ∘ (fun x : ℝ => (p, x)))
      exact hF.comp (continuous_const.prodMk continuous_id)
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 1 (baseCutoff p.1))
      (hf.intervalIntegrable (μ := volume) (baseCutoff p.1) 2)
    change (∫ x in 1..2, F p x) - (∫ x in 1..baseCutoff p.1, F p x) = ∫ x in baseCutoff p.1..2, F p x
    linarith
  exact (h2.sub hc).congr he

theorem thirdLowerIntegral_bound (p : ℝ × ℝ) : |thirdLowerIntegral p| ≤ 64 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := baseCutoff p.2)
    (C := 64) (f := fun t => clampedThird p.1 p.2 t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using clampedThird_bound p.1 p.2 t)
  have hc := baseCutoff_bounds p.2
  change |thirdLowerIntegral p| ≤ 64
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ baseCutoff p.2 - 1)] at h
  exact h.trans (by nlinarith)

theorem thirdUpperIntegral_bound (p : ℝ × ℝ) : |thirdUpperIntegral p| ≤ 64 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := baseCutoff p.1) (b := 2)
    (C := 64) (f := fun x => clampedThird x p.1 p.2)
    (fun x _ => by simpa only [Real.norm_eq_abs] using clampedThird_bound x p.1 p.2)
  have hc := baseCutoff_bounds p.1
  change |thirdUpperIntegral p| ≤ 64
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 2 - baseCutoff p.1)] at h
  exact h.trans (by nlinarith)

theorem thirdLowerIntegral_eq {x u : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) (hu : u ∈ Icc (1 : ℝ) 2) :
    thirdLowerIntegral (x, u) = ∫ t : ℝ in 1..u, loss3Kernel t u x := by
  rw [thirdLowerIntegral, baseCutoff_on hu.1 hu.2]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  exact clampedThird_eq hx hu ⟨ht.1, ht.2.trans hu.2⟩

theorem thirdUpperIntegral_eq {u t : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc (1 : ℝ) 2) :
    thirdUpperIntegral (u, t) = ∫ x : ℝ in u..2, loss3Kernel t u x := by
  rw [thirdUpperIntegral, baseCutoff_on hu.1 hu.2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hu.2] at hx
  exact clampedThird_eq ⟨hu.1.trans hx.1, hx.2⟩ hu ht

theorem third_inner_rectangle_swap {u : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) :
    (∫ x : ℝ in u..2, ∫ t : ℝ in 1..u, loss3Kernel t u x) =
      ∫ t : ℝ in 1..u, ∫ x : ℝ in u..2, loss3Kernel t u x := by
  have hm : Measurable (fun p : ℝ × ℝ => loss3Kernel p.2 u p.1) := by unfold loss3Kernel; fun_prop
  have hb : ∀ x ∈ Icc u 2, ∀ t ∈ Icc (1 : ℝ) u, |loss3Kernel t u x| ≤ 64 := by
    intro x hx t ht
    exact lossThree_bound ⟨hu.1.trans hx.1, hx.2⟩ hu ⟨ht.1, ht.2.trans hu.2⟩
  have h := bounded_rectangle_swap hm u 2 1 u 64 hb
  simpa only [intervalIntegral.integral_of_le hu.1, intervalIntegral.integral_of_le hu.2,
    ← integral_Icc_eq_integral_Ioc] using h

theorem third_ordered_reversal :
    (∫ x : ℝ in 1..2, ∫ u : ℝ in 1..x, ∫ t : ℝ in 1..u, loss3Kernel t u x) = L3 := by
  calc
    _ = ∫ x : ℝ in 1..2, ∫ u : ℝ in 1..x, thirdLowerIntegral (x, u) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hx.1] at hu
      exact (thirdLowerIntegral_eq hx ⟨hu.1, hu.2.trans hx.2⟩).symm
    _ = ∫ u : ℝ in 1..2, ∫ x : ℝ in u..2, thirdLowerIntegral (x, u) :=
      ordered_triangle_swap thirdLowerIntegral_continuous.measurable (by norm_num : (0 : ℝ) ≤ 64)
        (fun _ _ _ _ => thirdLowerIntegral_bound _)
    _ = ∫ u : ℝ in 1..2, ∫ t : ℝ in 1..u, ∫ x : ℝ in u..2, loss3Kernel t u x := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
      have he : (∫ x : ℝ in u..2, thirdLowerIntegral (x, u)) =
          ∫ x : ℝ in u..2, ∫ t : ℝ in 1..u, loss3Kernel t u x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hu.2] at hx
        exact thirdLowerIntegral_eq ⟨hu.1.trans hx.1, hx.2⟩ hu
      exact he.trans (third_inner_rectangle_swap hu)
    _ = ∫ u : ℝ in 1..2, ∫ t : ℝ in 1..u, thirdUpperIntegral (u, t) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu.1] at ht
      exact (thirdUpperIntegral_eq hu ⟨ht.1, ht.2.trans hu.2⟩).symm
    _ = ∫ t : ℝ in 1..2, ∫ u : ℝ in t..2, thirdUpperIntegral (u, t) :=
      ordered_triangle_swap thirdUpperIntegral_continuous.measurable (by norm_num : (0 : ℝ) ≤ 64)
        (fun _ _ _ _ => thirdUpperIntegral_bound _)
    _ = L3 := by
      unfold L3
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.2] at hu
      exact thirdUpperIntegral_eq ⟨ht.1.trans hu.1, hu.2⟩ ht

theorem actual_third_loss_eq_L3 : omissionLossTerm 2 = L3 :=
  third_loss_ordered_integral.trans third_ordered_reversal

end ThirdLossTerm

section ScalarFreeGateAndTailMass

noncomputable def freeGate (H : Profile) (i : Bool) (r b : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..baseCutoff b, H (!i) (r - x) x / max 1 x

theorem freeGate_continuous {H : Profile} (hH : JointContinuous H) : JointContinuous (freeGate H) := by
  intro i
  let F : (ℝ × ℝ) → ℝ → ℝ := fun p x => H (!i) (p.1 - x) x / max 1 x
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ => H (!i) (q.1.1 - q.2) q.2) :=
    (hH (!i)).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
  have hd : Continuous (fun q : (ℝ × ℝ) × ℝ => max 1 q.2) := continuous_const.max continuous_snd
  have hF : Continuous F.uncurry := hc.div hd (fun q => ne_of_gt
    ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left 1 q.2)))
  have hb : Continuous (fun p : ℝ × ℝ => baseCutoff p.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  exact continuous_variable_upper_integral F hF (fun p => baseCutoff p.2) hb

theorem freeGate_nonnegative {H : Profile} (hH : ∀ i r b, 0 ≤ H i r b) (i : Bool) (r b : ℝ) :
    0 ≤ freeGate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
  intro x
  exact div_nonneg (hH (!i) (r - x) x) (zero_le_one.trans (le_max_left 1 x))

theorem gate_le_freeGate {H : Profile} (hH : JointContinuous H)
    (hpos : ∀ i r b, 0 ≤ H i r b) (i : Bool) (r b : ℝ) : gate H i r b ≤ freeGate H i r b := by
  have hc := gate_integrand_continuous hH i r
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 1 (upperCutoff i r b))
    (hc.intervalIntegrable (μ := volume) (upperCutoff i r b) (baseCutoff b))
  have hp : 0 ≤ ∫ x in upperCutoff i r b..baseCutoff b, H (!i) (r - x) x / max 1 x := by
    apply intervalIntegral.integral_nonneg_of_forall (cutoff_le_base i r b)
    intro x
    exact div_nonneg (hpos (!i) (r - x) x) (zero_le_one.trans (le_max_left 1 x))
  unfold gate freeGate
  linarith

theorem gate_mono {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (h : ∀ i r b, H i r b ≤ G i r b) (i : Bool) (r b : ℝ) : gate H i r b ≤ gate G i r b := by
  apply intervalIntegral.integral_mono_on (upperCutoff_bounds i r b).1
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _)
    ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)
  intro x _
  exact div_le_div_of_nonneg_right (h (!i) (r - x) x) (zero_le_one.trans (le_max_left 1 x))

noncomputable def freeGateIterate : ℕ → Profile → Profile
  | 0, H => H
  | n + 1, H => freeGate (freeGateIterate n H)

theorem freeGateIterate_continuous {H : Profile} (hH : JointContinuous H) (n : ℕ) :
    JointContinuous (freeGateIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact freeGate_continuous ih

theorem freeGateIterate_nonnegative {H : Profile} (hH : ∀ i r b, 0 ≤ H i r b) (n : ℕ) :
    ∀ i r b, 0 ≤ freeGateIterate n H i r b := by
  induction n with
  | zero => exact hH
  | succ n ih => exact freeGate_nonnegative ih

theorem gateIterate_prefix_le {H : Profile} (hH : JointContinuous H)
    (hpos : ∀ i r b, 0 ≤ H i r b) (k n : ℕ) :
    ∀ i r b, gateIterate (k + n) H i r b ≤ freeGateIterate k (gateIterate n H) i r b := by
  induction k with
  | zero => intro i r b; simp only [zero_add, freeGateIterate, le_refl]
  | succ k ih =>
    intro i r b
    rw [show k + 1 + n = (k + n) + 1 by omega, gateIterate, freeGateIterate]
    calc
      _ ≤ gate (freeGateIterate k (gateIterate n H)) i r b :=
        gate_mono (gateIterate_continuous hH _) (freeGateIterate_continuous (gateIterate_continuous hH n) k) ih i r b
      _ ≤ _ := gate_le_freeGate (freeGateIterate_continuous (gateIterate_continuous hH n) k)
        (freeGateIterate_nonnegative (gateIterate_nonnegative hpos n) k) i r b

theorem actual_omission_prefix_le (k : ℕ) (i : Bool) (r b : ℝ) :
    gateIterate (k + 2) omissionForce i r b ≤
      freeGateIterate k (gateIterate 2 omissionForce) i r b :=
  gateIterate_prefix_le omissionForce_continuous omissionForce_nonnegative k 2 i r b

abbrev ScalarProfile := ℝ → ℝ → ℝ

def ScalarContinuous (H : ScalarProfile) : Prop :=
  Continuous (fun p : ℝ × ℝ => H p.1 p.2)

noncomputable def scalarFreeGate (H : ScalarProfile) (r b : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..baseCutoff b, H (r - x) x / max 1 x

noncomputable def scalarFreeIterate : ℕ → ScalarProfile → ScalarProfile
  | 0, H => H
  | n + 1, H => scalarFreeGate (scalarFreeIterate n H)

theorem scalarFreeGate_continuous {H : ScalarProfile} (hH : ScalarContinuous H) :
    ScalarContinuous (scalarFreeGate H) :=
  freeGate_continuous (H := fun _ => H) (fun _ => hH) false

theorem scalarFreeIterate_continuous {H : ScalarProfile} (hH : ScalarContinuous H) (n : ℕ) :
    ScalarContinuous (scalarFreeIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact scalarFreeGate_continuous ih

theorem scalarFreeIterate_nonnegative {H : ScalarProfile} (hH : ∀ r b, 0 ≤ H r b) (n : ℕ) :
    ∀ r b, 0 ≤ scalarFreeIterate n H r b := by
  induction n with
  | zero => exact hH
  | succ n ih =>
    intro r b
    apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
    intro x
    exact div_nonneg (ih (r - x) x) (zero_le_one.trans (le_max_left _ _))

theorem freeGate_total {H : Profile} (hH : JointContinuous H) (r b : ℝ) :
    freeGate H false r b + freeGate H true r b =
      scalarFreeGate (fun r b => H false r b + H true r b) r b := by
  have he := (gate_integrand_continuous hH false r).intervalIntegrable (μ := volume) 1 (baseCutoff b)
  have ho := (gate_integrand_continuous hH true r).intervalIntegrable (μ := volume) 1 (baseCutoff b)
  unfold freeGate scalarFreeGate
  rw [← intervalIntegral.integral_add he ho]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Bool.not_false, Bool.not_true]
  ring

theorem freeGateIterate_total {H : Profile} (hH : JointContinuous H) (n : ℕ) (r b : ℝ) :
    freeGateIterate n H false r b + freeGateIterate n H true r b =
      scalarFreeIterate n (fun r b => H false r b + H true r b) r b := by
  induction n generalizing r b with
  | zero => rfl
  | succ n ih =>
    rw [freeGateIterate, freeGate_total (freeGateIterate_continuous hH n)]
    have he : (fun r b => freeGateIterate n H false r b + freeGateIterate n H true r b) =
        scalarFreeIterate n (fun r b => H false r b + H true r b) := by
      funext r b; exact ih r b
    rw [he]
    rfl

noncomputable def terminalBlock (r b : ℝ) : ℝ := gateIterate 2 omissionForce true r b

theorem terminalBlock_continuous : ScalarContinuous terminalBlock :=
  gateIterate_continuous omissionForce_continuous 2 true

theorem terminalBlock_nonnegative (r b : ℝ) : 0 ≤ terminalBlock r b :=
  gateIterate_nonnegative omissionForce_nonnegative 2 true r b

theorem actual_free_total (k : ℕ) (r b : ℝ) :
    freeGateIterate k (gateIterate 2 omissionForce) false r b +
      freeGateIterate k (gateIterate 2 omissionForce) true r b =
        scalarFreeIterate k terminalBlock r b := by
  rw [freeGateIterate_total (gateIterate_continuous omissionForce_continuous 2)]
  have he : (fun r b => gateIterate 2 omissionForce false r b + gateIterate 2 omissionForce true r b) = terminalBlock := by
    funext r b
    have hh := (omission_wrong_parity_zero 1).1 r b
    norm_num only [Nat.reduceMul] at hh
    rw [hh, zero_add]
    rfl
  rw [he]

noncomputable def combinedDensity (n : ℕ) (y : ℝ) : ℝ :=
  (if 1 < y then omissionDensity n false y else 0) + omissionDensity n true y

theorem actual_combined_density_le (k : ℕ) (y : ℝ) :
    combinedDensity (k + 2) y ≤ 2 * y ^ 2 * scalarFreeIterate k terminalBlock (2 * y + 2) 2 := by
  have he := actual_omission_prefix_le k false (2 * y + 2) 2
  have ho := actual_omission_prefix_le k true (2 * y + 2) 2
  have hpe := gateIterate_nonnegative omissionForce_nonnegative (k + 2) false (2 * y + 2) 2
  have hfE := freeGateIterate_nonnegative (gateIterate_nonnegative omissionForce_nonnegative 2) k false (2 * y + 2) 2
  have hbE : (if 1 < y then omissionDensity (k + 2) false y else 0) ≤
      2 * y ^ 2 * freeGateIterate k (gateIterate 2 omissionForce) false (2 * y + 2) 2 := by
    by_cases h : 1 < y
    · rw [if_pos h]
      have hh := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg y))
      simp only [omissionDensity, sourceWeight, Bool.false_eq_true, ↓reduceIte]
      nlinarith
    · rw [if_neg h]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg y)) hfE
  have hbO : omissionDensity (k + 2) true y ≤
      2 * y ^ 2 * freeGateIterate k (gateIterate 2 omissionForce) true (2 * y + 2) 2 := by
    simp only [omissionDensity, sourceWeight, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left ho (mul_nonneg (by norm_num) (sq_nonneg y))
  have hh := actual_free_total k (2 * y + 2) 2
  unfold combinedDensity
  nlinarith

theorem freeGate_le_one {H : Profile} (hH : JointContinuous H)
    (hupper : ∀ i r b, H i r b ≤ 1) (i : Bool) (r b : ℝ) : freeGate H i r b ≤ 1 := by
  have hc := gate_integrand_continuous hH i r
  have hi := intervalIntegral.integral_mono_on (baseCutoff_bounds b).1
    (hc.intervalIntegrable (μ := volume) 1 (baseCutoff b))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 (baseCutoff b))
    (fun x _ => (div_le_one (by linarith [le_max_left (1 : ℝ) x] : 0 < max 1 x)).mpr
      ((hupper (!i) (r - x) x).trans (le_max_left _ _)))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hi
  exact hi.trans (by linarith [(baseCutoff_bounds b).2])

theorem gateIterate_force_le_one (n : ℕ) (i : Bool) (r b : ℝ) : gateIterate n omissionForce i r b ≤ 1 := by
  induction n generalizing i r b with
  | zero => exact omissionForce_le_one i r b
  | succ n ih =>
    exact (gate_le_freeGate (gateIterate_continuous omissionForce_continuous n)
      (gateIterate_nonnegative omissionForce_nonnegative n) i r b).trans
      (freeGate_le_one (gateIterate_continuous omissionForce_continuous n) ih i r b)

theorem terminalBlock_le_one (r b : ℝ) : terminalBlock r b ≤ 1 := gateIterate_force_le_one 2 true r b

theorem scalarFreeIterate_le_one (n : ℕ) (r b : ℝ) : scalarFreeIterate n terminalBlock r b ≤ 1 := by
  induction n generalizing r b with
  | zero => exact terminalBlock_le_one r b
  | succ n ih =>
    exact freeGate_le_one (H := fun _ => scalarFreeIterate n terminalBlock)
      (fun _ => scalarFreeIterate_continuous terminalBlock_continuous n) (fun _ => ih) false r b

theorem terminalBlock_high {r b : ℝ} (hr : 10 ≤ r) : terminalBlock r b = 0 :=
  iterated_force_high_zero 2 true (by norm_num; exact hr)

theorem scalarFreeIterate_high (n : ℕ) {r b : ℝ} (hr : 2 * (n : ℝ) + 10 ≤ r) :
    scalarFreeIterate n terminalBlock r b = 0 := by
  induction n generalizing r b with
  | zero => exact terminalBlock_high (by simpa only [Nat.cast_zero, mul_zero, zero_add] using hr)
  | succ n ih =>
    rw [scalarFreeIterate, scalarFreeGate]
    calc
      _ = ∫ _x : ℝ in 1..baseCutoff b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (baseCutoff_bounds b).1] at hx
        have hx2 : x ≤ 2 := hx.2.trans (baseCutoff_bounds b).2
        dsimp only
        rw [ih (by push_cast at hr; linarith : 2 * (n : ℝ) + 10 ≤ r - x), zero_div]
      _ = 0 := by simp

noncomputable def scalarTailIntegrand (n : ℕ) (S b y : ℝ) : ℝ :=
  2 * y ^ 2 * scalarFreeIterate n terminalBlock (2 * y + 2 - S) b

noncomputable def scalarTailMass (n : ℕ) (S b : ℝ) : ℝ :=
  ∫ y in Ioi 0, scalarTailIntegrand n S b y

theorem scalarTailIntegrand_continuous (n : ℕ) (S b : ℝ) : Continuous (scalarTailIntegrand n S b) := by
  have hb : Continuous (fun p : ℝ × ℝ => scalarFreeIterate n terminalBlock p.1 p.2) :=
    scalarFreeIterate_continuous terminalBlock_continuous n
  have hp : Continuous (fun y : ℝ => (2 * y + 2 - S, b)) := by fun_prop
  have hc : Continuous (fun y : ℝ => scalarFreeIterate n terminalBlock (2 * y + 2 - S) b) := hb.comp hp
  exact (continuous_const.mul (continuous_id.pow 2)).mul hc

theorem scalarTailIntegrand_integrable (n : ℕ) (S b : ℝ) :
    IntegrableOn (scalarTailIntegrand n S b) (Ioi 0) := by
  let Y : ℝ := |S| + (n : ℝ) + 5
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hc := (scalarTailIntegrand_continuous n S b).integrableOn_Icc (μ := volume) (a := 0) (b := Y)
  have hz : IntegrableOn (scalarTailIntegrand n S b) (Ioi Y) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi Y) := integrable_zero ℝ ℝ _
    apply hzero.congr_fun _ measurableSet_Ioi
    intro y hy
    have hyY : Y < y := hy
    have hS := le_abs_self S
    have hS0 := abs_nonneg S
    have hh : 2 * (n : ℝ) + 10 ≤ 2 * y + 2 - S := by dsimp [Y] at hyY; linarith
    simp only [scalarTailIntegrand, scalarFreeIterate_high n hh, mul_zero]
  have hu := hc.union hz
  rw [Icc_union_Ioi_eq_Ici hY] at hu
  exact hu.mono_set Ioi_subset_Ici_self

theorem evenDensity_indicator_integrable (n : ℕ) :
    IntegrableOn (fun y : ℝ => if 1 < y then omissionDensity n false y else 0) (Ioi 0) := by
  change Integrable ((Ioi (1 : ℝ)).indicator (omissionDensity n false)) (volume.restrict (Ioi 0))
  rw [integrable_indicator_iff measurableSet_Ioi]
  change Integrable (omissionDensity n false) ((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi 1))
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  exact omissionDensity_integrable n false

theorem combinedDensity_integrable (n : ℕ) : IntegrableOn (combinedDensity n) (Ioi 0) :=
  (evenDensity_indicator_integrable n).add (omissionDensity_integrable n true)

theorem combinedDensity_integral (n : ℕ) :
    (∫ y in Ioi 0, combinedDensity n y) = omissionLossTerm n := by
  have he : (∫ y in Ioi (0 : ℝ), if 1 < y then omissionDensity n false y else 0) =
      ∫ y in Ioi 1, omissionDensity n false y := by
    change (∫ y in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (omissionDensity n false) y) = _
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  unfold combinedDensity
  rw [integral_add (evenDensity_indicator_integrable n) (omissionDensity_integrable n true), he]
  rfl

theorem actual_loss_le_scalarTailMass (k : ℕ) : omissionLossTerm (k + 2) ≤ scalarTailMass k 0 2 := by
  rw [← combinedDensity_integral]
  apply integral_mono_ae (combinedDensity_integrable (k + 2)) (scalarTailIntegrand_integrable k 0 2)
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [scalarTailIntegrand, sub_zero] using actual_combined_density_le k y)

theorem scalarTailMass_bounded (n : ℕ) (S b Y : ℝ) (hY : 0 ≤ Y)
    (hhigh : S / 2 + (n : ℝ) + 4 ≤ Y) :
    scalarTailMass n S b = ∫ y : ℝ in 0..Y, scalarTailIntegrand n S b y := by
  have hz : (∫ y in Ioi Y, scalarTailIntegrand n S b y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    change Y < y at hy
    have hh : 2 * (n : ℝ) + 10 ≤ 2 * y + 2 - S := by linarith
    simp only [scalarTailIntegrand, scalarFreeIterate_high n hh, mul_zero]
  have hh := intervalIntegral.integral_Ioi_sub_Ioi (scalarTailIntegrand_integrable n S b) hY
  rw [hz, sub_zero] at hh
  exact hh

theorem scalarTailMass_continuous (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => scalarTailMass n p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Y : ℝ := |p.1| + (n : ℝ) + 5
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  let F : (ℝ × ℝ) → ℝ → ℝ := fun q y => scalarTailIntegrand n q.1 q.2 y
  have hpmap : Continuous (fun q : (ℝ × ℝ) × ℝ => (2 * q.2 + 2 - q.1.1, q.1.2)) := by fun_prop
  have hh : Continuous (fun q : (ℝ × ℝ) × ℝ => scalarFreeIterate n terminalBlock (2 * q.2 + 2 - q.1.1) q.1.2) :=
    (scalarFreeIterate_continuous terminalBlock_continuous n).comp hpmap
  have hF : Continuous F.uncurry := (continuous_const.mul (continuous_snd.pow 2)).mul hh
  have hI : Continuous (fun q : ℝ × ℝ => ∫ y in Icc (0 : ℝ) Y, F q y) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  apply hI.continuousAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < p.1 + 1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith : p.1 < p.1 + 1))
  filter_upwards [hnear] with q hq
  have hp := le_abs_self p.1
  have hp0 := abs_nonneg p.1
  have hhigh : q.1 / 2 + (n : ℝ) + 4 ≤ Y := by dsimp [Y]; linarith
  rw [scalarTailMass_bounded n q.1 q.2 Y hY hhigh,
    intervalIntegral.integral_of_le hY, ← integral_Icc_eq_integral_Ioc]

theorem scalarTailMass_succ (n : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass (n + 1) S b = ∫ x : ℝ in 1..b, scalarTailMass n (S + x) x / x := by
  let Y : ℝ := S / 2 + (n : ℝ) + 5
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  let G : ℝ × ℝ → ℝ := fun p =>
    2 * p.1 ^ 2 * scalarFreeIterate n terminalBlock (2 * p.1 + 2 - S - p.2) p.2 / max 1 p.2
  have hpmap : Continuous (fun p : ℝ × ℝ => (2 * p.1 + 2 - S - p.2, p.2)) := by fun_prop
  have hphi : Continuous (fun p : ℝ × ℝ => scalarFreeIterate n terminalBlock (2 * p.1 + 2 - S - p.2) p.2) :=
    (scalarFreeIterate_continuous terminalBlock_continuous n).comp hpmap
  have hG : Continuous G := by
    apply ((continuous_const.mul (continuous_fst.pow 2)).mul hphi).div
      (continuous_const.max continuous_snd)
    intro p
    exact ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _))
  have hbnd : ∀ y ∈ Icc (0 : ℝ) Y, ∀ x ∈ Icc (1 : ℝ) b, |G (y, x)| ≤ 2 * Y ^ 2 := by
    intro y hy x _hx
    have hp := scalarFreeIterate_nonnegative terminalBlock_nonnegative n (2 * y + 2 - S - x) x
    have hu := scalarFreeIterate_le_one n (2 * y + 2 - S - x) x
    have hn : 0 ≤ 2 * y ^ 2 * scalarFreeIterate n terminalBlock (2 * y + 2 - S - x) x := by positivity
    have hh := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg y))
    dsimp only [G]
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1 : ℝ) x)).trans
    nlinarith [hy.1, hy.2]
  have hswap := bounded_rectangle_swap hG.measurable 0 Y 1 b (2 * Y ^ 2) hbnd
  have hswap' : (∫ y : ℝ in 0..Y, ∫ x : ℝ in 1..b, G (y, x)) =
      ∫ x : ℝ in 1..b, ∫ y : ℝ in 0..Y, G (y, x) := by
    simpa only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY,
      ← intervalIntegral.integral_of_le hb1] using hswap
  rw [scalarTailMass_bounded (n + 1) S b Y hY (by dsimp [Y]; push_cast; linarith)]
  have hleft : (∫ y : ℝ in 0..Y, scalarTailIntegrand (n + 1) S b y) =
      ∫ y : ℝ in 0..Y, ∫ x : ℝ in 1..b, G (y, x) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    simp only [scalarTailIntegrand, scalarFreeIterate, scalarFreeGate, baseCutoff_on hb1 hb2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [G]
    ring
  rw [hleft, hswap']
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hb1] at hx
  have hx2 : x ≤ 2 := hx.2.trans hb2
  dsimp only
  rw [scalarTailMass_bounded n (S + x) x Y hY (by dsimp [Y]; linarith), ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [G, scalarTailIntegrand]
  rw [max_eq_right hx.1]
  have he : 2 * y + 2 - S - x = 2 * y + 2 - (S + x) := by ring
  rw [he]

end ScalarFreeGateAndTailMass

section OrderedWindowAndAffineBound

noncomputable def lastWindowCoefficient (S a b c : ℝ) : ℝ :=
  ((S + a + b + 2 * c) ^ 3 - (S + 2 * a) ^ 3) / (12 * c)

theorem last_window_width {S a b c : ℝ} (ha : a ≤ 2) (hb : 1 ≤ b) (hc : 1 ≤ c) (hab : b ≤ a) :
    1 ≤ (S + a + b + 2 * c) - (S + 2 * a) ∧ (S + a + b + 2 * c) - (S + 2 * a) ≤ 2 * c := by
  constructor <;> linarith

theorem last_window_square_bound {S a b c : ℝ} (hS : 0 ≤ S)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hab : b ≤ a) :
    lastWindowCoefficient S a b c ≤ (S + a + b + 2 * c) ^ 2 / 2 := by
  have hw := last_window_width (S := S) ha2 hb1 hc1 hab
  have hU : 0 ≤ S + a + b + 2 * c := by linarith
  have hV : 0 ≤ S + 2 * a := by linarith
  have hcube : (S + a + b + 2 * c) ^ 3 - (S + 2 * a) ^ 3 ≤
      3 * (S + a + b + 2 * c) ^ 2 * ((S + a + b + 2 * c) - (S + 2 * a)) := by
    have hp := mul_nonneg (sq_nonneg ((S + a + b + 2 * c) - (S + 2 * a)))
      (show 0 ≤ 2 * (S + a + b + 2 * c) + (S + 2 * a) by linarith)
    nlinarith
  have hwidth := mul_le_mul_of_nonneg_left hw.2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (S + a + b + 2 * c)))
  unfold lastWindowCoefficient
  apply (div_le_iff₀ (by linarith : 0 < 12 * c)).mpr
  nlinarith

theorem last_window_mean_bound (k : ℕ) {S a b c : ℝ}
    (hSlo : (k : ℝ) ≤ S) (hShi : S ≤ 2 * (k : ℝ)) (hSc : (k : ℝ) * c ≤ S)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hb1 : 1 ≤ b) (hba : b ≤ a)
    (hc1 : 1 ≤ c) (hcb : c ≤ b) :
    lastWindowCoefficient S a b c ≤
      (((k : ℝ) + 4) ^ 2 / 2) * (3 * (S + a + b + c) / ((k : ℝ) + 3) - 2) := by
  let m : ℝ := (k : ℝ) + 3
  let T : ℝ := S + a + b + c
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hm : 0 < m := by dsimp [m]; linarith
  have hTlo : m ≤ T := by dsimp [m, T]; linarith
  have hThi : T ≤ 2 * m := by dsimp [m, T]; linarith
  have hTc : m * c ≤ T := by dsimp [m, T]; nlinarith
  have hmean1 : 1 ≤ T / m := (one_le_div hm).mpr hTlo
  have hmean2 : T / m ≤ 2 := (div_le_iff₀ hm).mpr hThi
  have hmean : (T / m) ^ 2 ≤ 3 * (T / m) - 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hmean1) (sub_nonneg.mpr hmean2)
    nlinarith
  have hA : S + a + b + 2 * c ≤ (m + 1) * (T / m) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hm).mpr
    change (S + a + b + 2 * c) * m ≤ (m + 1) * T
    dsimp [T] at hTc ⊢
    nlinarith
  have hA0 : 0 ≤ S + a + b + 2 * c := by linarith
  have hsq := mul_self_le_mul_self hA0 hA
  have hlin := mul_le_mul_of_nonneg_left hmean (sq_nonneg (m + 1))
  have hw := last_window_square_bound (hSlo.trans' hk) ha1 ha2 hb1 hc1 hba
  have hme : (k : ℝ) + 4 = m + 1 := by dsimp [m]; ring
  rw [hme]
  change lastWindowCoefficient S a b c ≤ ((m + 1) ^ 2 / 2) * (3 * T / m - 2)
  have hsq2 : (S + a + b + 2 * c) ^ 2 ≤ (m + 1) ^ 2 * (T / m) ^ 2 := by nlinarith [hsq]
  calc
    _ ≤ (S + a + b + 2 * c) ^ 2 / 2 := hw
    _ ≤ ((m + 1) ^ 2 * (T / m) ^ 2) / 2 := div_le_div_of_nonneg_right hsq2 (by norm_num)
    _ ≤ ((m + 1) ^ 2 * (3 * (T / m) - 2)) / 2 := div_le_div_of_nonneg_right hlin (by norm_num)
    _ = _ := by ring

theorem terminalBlock_mask (S y : ℝ) {b : ℝ} (_hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    terminalBlock (2 * y + 2 - S) b =
      ∫ a in Icc (1 : ℝ) b, if S / 2 + a ≤ y then
        gate omissionForce false (2 * y + 2 - S - a) a / max 1 a else 0 := by
  have hset : Ioc (1 : ℝ) (upperCutoff true (2 * y + 2 - S) b) =
      Ioc (1 : ℝ) b ∩ {a : ℝ | S / 2 + a ≤ y} := by
    ext a
    constructor
    · intro ha
      obtain ⟨ha1, _ha2, hab, hgate⟩ := (mem_upperCutoff_true (2 * y + 2 - S) b a).mp ha
      exact ⟨⟨ha1, hab⟩, by change S / 2 + a ≤ y; linarith⟩
    · rintro ⟨⟨ha1, hab⟩, hy⟩
      apply (mem_upperCutoff_true (2 * y + 2 - S) b a).mpr
      refine ⟨ha1, hab.trans hb2, hab, ?_⟩
      change S / 2 + a ≤ y at hy
      linarith
  have hm : MeasurableSet {a : ℝ | S / 2 + a ≤ y} :=
    measurableSet_le (measurable_const.add measurable_id) measurable_const
  change (∫ a : ℝ in 1..upperCutoff true (2 * y + 2 - S) b,
    gate omissionForce false (2 * y + 2 - S - a) a / max 1 a) = _
  rw [intervalIntegral.integral_of_le (upperCutoff_bounds true (2 * y + 2 - S) b).1,
    hset, ← setIntegral_indicator hm, ← integral_Icc_eq_integral_Ioc]
  rfl

noncomputable def terminalOuterIntegrand (S : ℝ) (p : ℝ × ℝ) : ℝ :=
  if S / 2 + p.2 ≤ p.1 then
    2 * p.1 ^ 2 * gate omissionForce false (2 * p.1 + 2 - S - p.2) p.2 / max 1 p.2 else 0

theorem terminalOuterIntegrand_measurable (S : ℝ) : Measurable (terminalOuterIntegrand S) := by
  have hc0 : Continuous (fun p : ℝ × ℝ => gate omissionForce false p.1 p.2) :=
    gate_continuous omissionForce_continuous false
  have hp : Continuous (fun p : ℝ × ℝ => (2 * p.1 + 2 - S - p.2, p.2)) := by fun_prop
  have hc : Continuous (fun p : ℝ × ℝ => gate omissionForce false (2 * p.1 + 2 - S - p.2) p.2) := hc0.comp hp
  exact Measurable.ite (measurableSet_le (measurable_const.add measurable_snd) measurable_fst)
    (((measurable_const.mul (measurable_fst.pow_const 2)).mul hc.measurable).div
      (measurable_const.max measurable_snd)) measurable_const

theorem terminalOuterIntegrand_bound (S a : ℝ) {y Y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) :
    |terminalOuterIntegrand S (y, a)| ≤ 2 * Y ^ 2 := by
  unfold terminalOuterIntegrand
  split_ifs
  · have hp := gate_nonnegative omissionForce_nonnegative false (2 * y + 2 - S - a) a
    have hu := gateIterate_force_le_one 1 false (2 * y + 2 - S - a) a
    change gate omissionForce false (2 * y + 2 - S - a) a ≤ 1 at hu
    have hn : 0 ≤ 2 * y ^ 2 * gate omissionForce false (2 * y + 2 - S - a) a := by positivity
    have hm := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg y))
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1 : ℝ) a)).trans
    nlinarith
  · simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg Y)

theorem scalarTailMass_zero_outer {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b =
      ∫ a : ℝ in 1..b, (2 / a) * (∫ y : ℝ in S / 2 + a..S / 2 + 4,
        y ^ 2 * gate omissionForce false (2 * y + 2 - S - a) a) := by
  let Y : ℝ := S / 2 + 4
  have hY : 0 ≤ Y := by dsimp [Y]; linarith
  have hl (y : ℝ) : scalarTailIntegrand 0 S b y = ∫ a in Icc (1 : ℝ) b, terminalOuterIntegrand S (y, a) := by
    change 2 * y ^ 2 * terminalBlock (2 * y + 2 - S) b = _
    rw [terminalBlock_mask S y hb1 hb2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with a
    dsimp only [terminalOuterIntegrand]
    split_ifs <;> ring
  have hs := bounded_rectangle_swap (terminalOuterIntegrand_measurable S) 0 Y 1 b (2 * Y ^ 2)
    (fun y hy a _ha => terminalOuterIntegrand_bound S a hy.1 hy.2)
  have hr (a : ℝ) (ha : a ∈ Icc (1 : ℝ) b) :
      (∫ y in Icc (0 : ℝ) Y, terminalOuterIntegrand S (y, a)) =
        (2 / a) * (∫ y : ℝ in S / 2 + a..Y, y ^ 2 * gate omissionForce false (2 * y + 2 - S - a) a) := by
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hlo : 0 ≤ S / 2 + a := by linarith [ha.1]
    have hhi : S / 2 + a ≤ Y := by dsimp [Y]; linarith
    have hset : Icc (0 : ℝ) Y ∩ Ici (S / 2 + a) = Icc (S / 2 + a) Y := by
      ext y
      constructor
      · rintro ⟨hy, hylo⟩; exact ⟨hylo, hy.2⟩
      · intro hy; exact ⟨⟨hlo.trans hy.1, hy.2⟩, hy.1⟩
    have he : (fun y : ℝ => terminalOuterIntegrand S (y, a)) =
        (Ici (S / 2 + a)).indicator (fun y => (2 / a) * (y ^ 2 * gate omissionForce false (2 * y + 2 - S - a) a)) := by
      funext y
      unfold terminalOuterIntegrand
      by_cases h : S / 2 + a ≤ y
      · rw [if_pos h, indicator_of_mem (show y ∈ Ici (S / 2 + a) from h), max_eq_right ha.1]
        ring
      · rw [if_neg h, indicator_of_notMem (show y ∉ Ici (S / 2 + a) from h)]
    rw [he, setIntegral_indicator measurableSet_Ici, hset, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hhi]
  rw [scalarTailMass_bounded 0 S b Y hY (by dsimp [Y]; norm_num),
    intervalIntegral.integral_of_le hY, ← integral_Icc_eq_integral_Ioc]
  simp_rw [hl]
  rw [hs, intervalIntegral.integral_of_le hb1, ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc hr

theorem evenGate_weighted_swap (S a l Y : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hl : 0 ≤ l) (hlY : l ≤ Y) :
    (∫ y : ℝ in l..Y, y ^ 2 * gate omissionForce false (2 * y + 2 - S - a) a) =
      ∫ u : ℝ in 1..a, (∫ y : ℝ in l..Y, y ^ 2 * omissionForce true (2 * y + 2 - S - a - u) u) / u := by
  let G : ℝ × ℝ → ℝ := fun p => p.1 ^ 2 * omissionForce true (2 * p.1 + 2 - S - a - p.2) p.2 / max 1 p.2
  have hpmap : Continuous (fun p : ℝ × ℝ => (2 * p.1 + 2 - S - a - p.2, p.2)) := by fun_prop
  have hc : Continuous (fun p : ℝ × ℝ => omissionForce true (2 * p.1 + 2 - S - a - p.2) p.2) :=
    (omissionForce_continuous true).comp hpmap
  have hG : Continuous G := by
    apply ((continuous_fst.pow 2).mul hc).div (continuous_const.max continuous_snd)
    intro p
    exact ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _))
  have hbnd : ∀ y ∈ Icc l Y, ∀ u ∈ Icc (1 : ℝ) a, |G (y, u)| ≤ Y ^ 2 := by
    intro y hy u _hu
    have hy0 : 0 ≤ y := hl.trans hy.1
    have hp := omissionForce_nonnegative true (2 * y + 2 - S - a - u) u
    have hu := omissionForce_le_one true (2 * y + 2 - S - a - u) u
    have hn : 0 ≤ y ^ 2 * omissionForce true (2 * y + 2 - S - a - u) u := by positivity
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg y)
    dsimp only [G]
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1 : ℝ) u)).trans
    nlinarith [hy.2]
  have hs := bounded_rectangle_swap hG.measurable l Y 1 a (Y ^ 2) hbnd
  have hs' : (∫ y : ℝ in l..Y, ∫ u : ℝ in 1..a, G (y, u)) =
      ∫ u : ℝ in 1..a, ∫ y : ℝ in l..Y, G (y, u) := by
    simpa only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlY,
      ← intervalIntegral.integral_of_le ha1] using hs
  have hl' : (∫ y : ℝ in l..Y, y ^ 2 * gate omissionForce false (2 * y + 2 - S - a) a) =
      ∫ y : ℝ in l..Y, ∫ u : ℝ in 1..a, G (y, u) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only
    rw [gate, show upperCutoff false (2 * y + 2 - S - a) a = a from baseCutoff_on ha1 ha2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [G, Bool.not_false]
    ring
  rw [hl', hs']
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha1] at hu
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [G]
  rw [max_eq_right hu.1]

theorem scalarTailMass_zero_triple {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b =
      ∫ a : ℝ in 1..b, ∫ u : ℝ in 1..a, ∫ c : ℝ in 1..u,
        lastWindowCoefficient S a u c / (a * u * c) := by
  rw [scalarTailMass_zero_outer hS hb1 hb2]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hb1] at ha
  have ha2 : a ≤ 2 := ha.2.trans hb2
  have hl : 0 ≤ S / 2 + a := by linarith [ha.1]
  have hlY : S / 2 + a ≤ S / 2 + 4 := by linarith
  dsimp only
  rw [evenGate_weighted_swap S a (S / 2 + a) (S / 2 + 4) ha.1 ha2 hl hlY,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  have hu2 : u ≤ 2 := hu.2.trans ha2
  have hw := integrated_force_window (S + a + u) (S / 2 + a) (S / 2 + 4) u 0 hl hu.1 hu2
    (by linarith [hu.1]) (by linarith)
  simp only [sub_zero, zero_mul] at hw
  have hgap (y : ℝ) : 2 * y + 2 - S - a - u = 2 * y + 2 - (S + a + u) := by ring
  dsimp only
  simp_rw [hgap]
  rw [hw, ← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hu.1] at hc
  have ha0 : a ≠ 0 := by linarith [ha.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hc0 : c ≠ 0 := by linarith [hc.1]
  dsimp only [lastWindowCoefficient]
  field_simp
  ring

noncomputable def windowKernel (S a u c : ℝ) : ℝ :=
  ((S + a + u + 2 * c) ^ 3 - (S + 2 * a) ^ 3) / (12 * max 1 a * max 1 u * (max 1 c) ^ 2)

noncomputable def windowMiddle (S a u : ℝ) : ℝ :=
  ∫ c : ℝ in 1..baseCutoff u, windowKernel S a u c

noncomputable def windowOuter (S a : ℝ) : ℝ :=
  ∫ u : ℝ in 1..baseCutoff a, windowMiddle S a u

noncomputable def windowMass (S b : ℝ) : ℝ :=
  ∫ a : ℝ in 1..baseCutoff b, windowOuter S a

theorem windowKernel_continuous (S : ℝ) :
    Continuous (fun q : (ℝ × ℝ) × ℝ => windowKernel S q.1.1 q.1.2 q.2) := by
  have hn : Continuous (fun q : (ℝ × ℝ) × ℝ => (S + q.1.1 + q.1.2 + 2 * q.2) ^ 3 - (S + 2 * q.1.1) ^ 3) := by fun_prop
  have hd : Continuous (fun q : (ℝ × ℝ) × ℝ => 12 * max 1 q.1.1 * max 1 q.1.2 * (max 1 q.2) ^ 2) := by fun_prop
  apply hn.div hd
  intro q
  have h1 : 0 < max (1 : ℝ) q.1.1 := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have h2 : 0 < max (1 : ℝ) q.1.2 := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have h3 : 0 < max (1 : ℝ) q.2 := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  positivity

theorem windowMiddle_continuous (S : ℝ) : Continuous (fun p : ℝ × ℝ => windowMiddle S p.1 p.2) :=
  continuous_variable_upper_integral (fun p c => windowKernel S p.1 p.2 c)
    (windowKernel_continuous S) (fun p => baseCutoff p.2)
    (continuous_const.max (continuous_const.min continuous_snd))

theorem windowOuter_continuous (S : ℝ) : Continuous (windowOuter S) := by
  have hp : Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) := by fun_prop
  have hF : Continuous (fun q : (ℝ × ℝ) × ℝ => windowMiddle S q.1.1 q.2) :=
    (windowMiddle_continuous S).comp hp
  have hcap : Continuous (fun p : ℝ × ℝ => baseCutoff p.1) :=
    continuous_const.max (continuous_const.min continuous_fst)
  have hh : Continuous (fun p : ℝ × ℝ => ∫ u : ℝ in 1..baseCutoff p.1, windowMiddle S p.1 u) :=
    continuous_variable_upper_integral (fun p u => windowMiddle S p.1 u) hF (fun p => baseCutoff p.1) hcap
  have hmap : Continuous (fun a : ℝ => (a, (0 : ℝ))) := by fun_prop
  change Continuous (fun a : ℝ => ∫ u : ℝ in 1..baseCutoff a, windowMiddle S a u)
  simpa only [Function.comp_def] using! hh.comp hmap

theorem windowKernel_literal {S a u c : ℝ} (ha : 1 ≤ a) (hu : 1 ≤ u) (hc : 1 ≤ c) :
    windowKernel S a u c = lastWindowCoefficient S a u c / (a * u * c) := by
  rw [windowKernel, max_eq_right ha, max_eq_right hu, max_eq_right hc, lastWindowCoefficient]
  ring

theorem scalarTailMass_zero_eq_windowMass {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b = windowMass S b := by
  rw [scalarTailMass_zero_triple hS hb1 hb2, windowMass, baseCutoff_on hb1 hb2]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hb1] at ha
  dsimp only
  rw [windowOuter, baseCutoff_on ha.1 (ha.2.trans hb2)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  dsimp only
  rw [windowMiddle, baseCutoff_on hu.1 (hu.2.trans (ha.2.trans hb2))]
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hu.1] at hc
  exact (windowKernel_literal ha.1 hu.1 hc.1).symm

noncomputable def orderedMass : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, b => ∫ x in (1 : ℝ)..baseCutoff b, orderedMass n x / max 1 x

theorem orderedMass_continuous (n : ℕ) : Continuous (orderedMass n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun x : ℝ => orderedMass n x / max 1 x) :=
      ih.div (continuous_const.max continuous_id)
        (fun x => ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)))
    exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
      (continuous_const.max (continuous_const.min continuous_id))

theorem log_power_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ))
      ((Real.log x) ^ n / ((n.factorial : ℝ) * x)) x := by
  have hh := ((Real.hasDerivAt_log hx.ne').pow (n + 1)).div_const ((n + 1).factorial : ℝ)
  convert! hh using 1
  simp only [Nat.add_sub_cancel_right, Nat.factorial_succ, Nat.cast_mul]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem orderedMass_eq (n : ℕ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    orderedMass n b = (Real.log b) ^ n / (n.factorial : ℝ) := by
  induction n generalizing b with
  | zero => norm_num [orderedMass]
  | succ n ih =>
    rw [orderedMass, baseCutoff_on hb1 hb2]
    have he : (∫ x in (1 : ℝ)..b, orderedMass n x / max 1 x) =
        ∫ x in (1 : ℝ)..b, (Real.log x) ^ n / ((n.factorial : ℝ) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      dsimp only
      rw [ih hx.1 (hx.2.trans hb2), max_eq_right hx.1]
      ring
    rw [he]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hc : ContinuousOn (fun x : ℝ => (Real.log x) ^ n / ((n.factorial : ℝ) * x)) (uIcc 1 b) := by
      rw [uIcc_of_le hb1]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := simp_all)
    have hd : ∀ x ∈ uIcc (1 : ℝ) b, HasDerivAt
        (fun x : ℝ => (Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ))
        ((Real.log x) ^ n / ((n.factorial : ℝ) * x)) x := by
      intro x hx
      rw [uIcc_of_le hb1] at hx
      exact log_power_primitive n (by linarith [hx.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
    simp

noncomputable def orderedFirstMoment : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, b => ∫ x in (1 : ℝ)..baseCutoff b,
      (x * orderedMass n x + orderedFirstMoment n x) / max 1 x

theorem orderedFirstMoment_continuous (n : ℕ) : Continuous (orderedFirstMoment n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun x : ℝ => (x * orderedMass n x + orderedFirstMoment n x) / max 1 x) :=
      ((continuous_id.mul (orderedMass_continuous n)).add ih).div
        (continuous_const.max continuous_id)
        (fun x => ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)))
    exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
      (continuous_const.max (continuous_const.min continuous_id))

theorem first_moment_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x - 1) * ((Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ)))
      ((Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ) + (x - 1) * ((Real.log x) ^ n / (n.factorial : ℝ)) / x) x := by
  have hh := ((hasDerivAt_id x).sub_const 1).mul (log_power_primitive n hx)
  convert! hh using 1
  simp only [id_eq, one_mul]
  ring

theorem orderedFirstMoment_eq (n : ℕ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    orderedFirstMoment (n + 1) b = (b - 1) * ((Real.log b) ^ n / (n.factorial : ℝ)) := by
  induction n generalizing b with
  | zero =>
    rw [orderedFirstMoment, baseCutoff_on hb1 hb2]
    have he : (∫ x in (1 : ℝ)..b, (x * orderedMass 0 x + orderedFirstMoment 0 x) / max 1 x) =
        ∫ _x in (1 : ℝ)..b, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      simp [orderedMass, orderedFirstMoment, max_eq_right hx.1, hx0]
    rw [he]
    simp
  | succ n ih =>
    rw [orderedFirstMoment, baseCutoff_on hb1 hb2]
    have he : (∫ x in (1 : ℝ)..b, (x * orderedMass (n + 1) x + orderedFirstMoment (n + 1) x) / max 1 x) =
        ∫ x in (1 : ℝ)..b, ((Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ) +
          (x - 1) * ((Real.log x) ^ n / (n.factorial : ℝ)) / x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      dsimp only
      rw [orderedMass_eq (n + 1) hx.1 (hx.2.trans hb2), ih hx.1 (hx.2.trans hb2), max_eq_right hx.1]
      field_simp
    rw [he]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn1 : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 1)
    have hc : ContinuousOn (fun x : ℝ => (Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ) +
        (x - 1) * ((Real.log x) ^ n / (n.factorial : ℝ)) / x) (uIcc 1 b) := by
      rw [uIcc_of_le hb1]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := simp_all)
    have hd : ∀ x ∈ uIcc (1 : ℝ) b, HasDerivAt
        (fun x : ℝ => (x - 1) * ((Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ)))
        ((Real.log x) ^ (n + 1) / ((n + 1).factorial : ℝ) +
          (x - 1) * ((Real.log x) ^ n / (n.factorial : ℝ)) / x) x := by
      intro x hx
      rw [uIcc_of_le hb1] at hx
      exact first_moment_primitive n (by linarith [hx.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
    simp

noncomputable def orderedAffine (m : ℝ) (n : ℕ) (S b : ℝ) : ℝ :=
  (3 * S / m - 2) * orderedMass n b + (3 / m) * orderedFirstMoment n b

theorem orderedAffine_continuous (m : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => orderedAffine m n p.1 p.2) := by
  have hM : Continuous (fun p : ℝ × ℝ => orderedMass n p.2) := (orderedMass_continuous n).comp continuous_snd
  have hF : Continuous (fun p : ℝ × ℝ => orderedFirstMoment n p.2) :=
    (orderedFirstMoment_continuous n).comp continuous_snd
  exact (((continuous_const.mul continuous_fst).div_const m).sub continuous_const |>.mul hM).add
    (continuous_const.mul hF)

theorem orderedAffine_shift_continuous (m : ℝ) (n : ℕ) (S : ℝ) :
    Continuous (fun x : ℝ => orderedAffine m n (S + x) x) := by
  have hp : Continuous (fun x : ℝ => (S + x, x)) := by fun_prop
  exact (orderedAffine_continuous m n).comp hp

theorem orderedAffine_shift_div_continuous (m : ℝ) (n : ℕ) (S : ℝ) :
    Continuous (fun x : ℝ => orderedAffine m n (S + x) x / max 1 x) :=
  (orderedAffine_shift_continuous m n S).div (continuous_const.max continuous_id)
    (fun x => ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)))

theorem orderedAffine_zero (m S b : ℝ) : orderedAffine m 0 S b = 3 * S / m - 2 := by
  simp [orderedAffine, orderedMass, orderedFirstMoment]

theorem orderedAffine_succ (m : ℝ) (n : ℕ) (S b : ℝ) :
    orderedAffine m (n + 1) S b =
      ∫ x : ℝ in 1..baseCutoff b, orderedAffine m n (S + x) x / max 1 x := by
  have hd : ∀ x : ℝ, max 1 x ≠ 0 := fun x => ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _))
  have hM : Continuous (fun x : ℝ => orderedMass n x / max 1 x) :=
    (orderedMass_continuous n).div (continuous_const.max continuous_id) hd
  have hF : Continuous (fun x : ℝ => (x * orderedMass n x + orderedFirstMoment n x) / max 1 x) :=
    ((continuous_id.mul (orderedMass_continuous n)).add (orderedFirstMoment_continuous n)).div
      (continuous_const.max continuous_id) hd
  change (3 * S / m - 2) * (∫ x : ℝ in 1..baseCutoff b, orderedMass n x / max 1 x) +
    (3 / m) * (∫ x : ℝ in 1..baseCutoff b, (x * orderedMass n x + orderedFirstMoment n x) / max 1 x) = _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      ((hM.const_mul (3 * S / m - 2)).intervalIntegrable (μ := volume) 1 _)
      ((hF.const_mul (3 / m)).intervalIntegrable (μ := volume) 1 _)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [orderedAffine]
  ring

theorem orderedAffine_at_two (n : ℕ) :
    orderedAffine ((n + 1 : ℕ) : ℝ) (n + 1) 0 2 =
      (3 / Real.log 2 - 2) * (Real.log 2) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [orderedAffine, orderedMass_eq (n + 1) (by norm_num) le_rfl,
    orderedFirstMoment_eq n (by norm_num) le_rfl]
  norm_num only [mul_zero, zero_div, zero_sub, sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
  rw [Nat.factorial_succ, pow_succ, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp
  ring

theorem terminal_mass_affine_bound (k : ℕ) {S b : ℝ}
    (hSlo : (k : ℝ) ≤ S) (hShi : S ≤ 2 * (k : ℝ)) (hSb : (k : ℝ) * b ≤ S)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b ≤ (((k : ℝ) + 4) ^ 2 / 2) * orderedAffine ((k : ℝ) + 3) 3 S b := by
  let m : ℝ := (k : ℝ) + 3
  let C : ℝ := ((k : ℝ) + 4) ^ 2 / 2
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hS : 0 ≤ S := hk.trans hSlo
  have hmiddle : ∀ a ∈ Icc (1 : ℝ) b, ∀ u ∈ Icc (1 : ℝ) a,
      windowMiddle S a u ≤ C / (a * u) * orderedAffine m 1 (S + a + u) u := by
    intro a ha u hu
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hu2 : u ≤ 2 := hu.2.trans ha2
    have ha0 : 0 < a := by linarith [ha.1]
    have hu0 : 0 < u := by linarith [hu.1]
    have hpmap : Continuous (fun c : ℝ => ((a, u), c)) := by fun_prop
    have hlower : Continuous (windowKernel S a u) := by
      simpa only [Function.comp_def] using! (windowKernel_continuous S).comp hpmap
    have hupper := (orderedAffine_shift_div_continuous m 0 (S + a + u)).const_mul (C / (a * u))
    have hh := intervalIntegral.integral_mono_on hu.1
      (hlower.intervalIntegrable (μ := volume) 1 u) (hupper.intervalIntegrable (μ := volume) 1 u) (fun c hc => by
        have hc0 : 0 < c := by linarith [hc.1]
        have hcb : c ≤ b := hc.2.trans (hu.2.trans ha.2)
        have hSc : (k : ℝ) * c ≤ S := (mul_le_mul_of_nonneg_left hcb hk).trans hSb
        have hw := last_window_mean_bound k hSlo hShi hSc ha.1 ha2 hu.1 hu.2 hc.1 hc.2
        rw [windowKernel_literal ha.1 hu.1 hc.1]
        change lastWindowCoefficient S a u c / (a * u * c) ≤ C / (a * u) * (orderedAffine m 0 (S + a + u + c) c / max 1 c)
        rw [orderedAffine_zero, max_eq_right hc.1]
        have hd := div_le_div_of_nonneg_right hw (show 0 ≤ a * u * c by positivity)
        convert! hd using 1; dsimp [C, m]; ring)
    unfold windowMiddle
    rw [baseCutoff_on hu.1 hu2]
    apply hh.trans_eq
    rw [intervalIntegral.integral_const_mul, orderedAffine_succ m 0 (S + a + u) u, baseCutoff_on hu.1 hu2]
  have houter : ∀ a ∈ Icc (1 : ℝ) b, windowOuter S a ≤ C / a * orderedAffine m 2 (S + a) a := by
    intro a ha
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hpmap : Continuous (fun u : ℝ => (a, u)) := by fun_prop
    have hlower : Continuous (windowMiddle S a) := by
      simpa only [Function.comp_def] using! (windowMiddle_continuous S).comp hpmap
    have hupper := (orderedAffine_shift_div_continuous m 1 (S + a)).const_mul (C / a)
    have hh := intervalIntegral.integral_mono_on ha.1
      (hlower.intervalIntegrable (μ := volume) 1 a) (hupper.intervalIntegrable (μ := volume) 1 a) (fun u hu => by
        have hw := hmiddle a ha u hu
        change windowMiddle S a u ≤ C / a * (orderedAffine m 1 (S + a + u) u / max 1 u)
        rw [max_eq_right hu.1]
        convert! hw using 1; ring)
    unfold windowOuter
    rw [baseCutoff_on ha.1 ha2]
    apply hh.trans_eq
    rw [intervalIntegral.integral_const_mul, orderedAffine_succ m 1 (S + a) a, baseCutoff_on ha.1 ha2]
  rw [scalarTailMass_zero_eq_windowMass hS hb1 hb2, windowMass, baseCutoff_on hb1 hb2]
  have hupper := (orderedAffine_shift_div_continuous m 2 S).const_mul C
  have hh := intervalIntegral.integral_mono_on hb1
    ((windowOuter_continuous S).intervalIntegrable (μ := volume) 1 b)
    (hupper.intervalIntegrable (μ := volume) 1 b) (fun a ha => by
      have hw := houter a ha
      change windowOuter S a ≤ C * (orderedAffine m 2 (S + a) a / max 1 a)
      rw [max_eq_right ha.1]
      convert! hw using 1; ring)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul, orderedAffine_succ m 2 S b, baseCutoff_on hb1 hb2]

theorem scalarTailMass_affine_bound (n k : ℕ) {S b : ℝ}
    (hSlo : (k : ℝ) ≤ S) (hShi : S ≤ 2 * (k : ℝ)) (hSb : (k : ℝ) * b ≤ S)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass n S b ≤ (((k : ℝ) + (n : ℝ) + 4) ^ 2 / 2) *
      orderedAffine ((k : ℝ) + (n : ℝ) + 3) (n + 3) S b := by
  induction n generalizing k S b with
  | zero =>
    simpa only [Nat.cast_zero, add_zero, Nat.zero_add] using terminal_mass_affine_bound k hSlo hShi hSb hb1 hb2
  | succ n ih =>
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hS : 0 ≤ S := hk.trans hSlo
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + ((n : ℝ) + 1) + 4 = (k : ℝ) + (n : ℝ) + 5 by ring,
      show (k : ℝ) + ((n : ℝ) + 1) + 3 = (k : ℝ) + (n : ℝ) + 4 by ring,
      show (n + 1) + 3 = (n + 3) + 1 by omega]
    let m : ℝ := (k : ℝ) + (n : ℝ) + 4
    let C : ℝ := ((k : ℝ) + (n : ℝ) + 5) ^ 2 / 2
    change scalarTailMass (n + 1) S b ≤ C * orderedAffine m ((n + 3) + 1) S b
    rw [scalarTailMass_succ n hS hb1 hb2, orderedAffine_succ, baseCutoff_on hb1 hb2,
      ← intervalIntegral.integral_const_mul]
    have hpmap : Continuous (fun x : ℝ => (S + x, x)) := by fun_prop
    have hc : Continuous (fun x : ℝ => scalarTailMass n (S + x) x / max 1 x) :=
      ((scalarTailMass_continuous n).comp hpmap).div (continuous_const.max continuous_id)
        (fun x => ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)))
    have hlow : IntervalIntegrable (fun x : ℝ => scalarTailMass n (S + x) x / x) volume 1 b := by
      apply (hc.intervalIntegrable (μ := volume) 1 b).congr_uIoo
      intro x hx
      rw [uIoo_of_le hb1] at hx
      simp only [max_eq_right hx.1.le]
    have hupper := (orderedAffine_shift_div_continuous m (n + 3) S).const_mul C
    apply intervalIntegral.integral_mono_on hb1 hlow (hupper.intervalIntegrable (μ := volume) 1 b)
    intro x hx
    have hx2 : x ≤ 2 := hx.2.trans hb2
    have hlo : ((k + 1 : ℕ) : ℝ) ≤ S + x := by push_cast; linarith [hx.1]
    have hhi : S + x ≤ 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have horder : ((k + 1 : ℕ) : ℝ) * x ≤ S + x := by
      have hh := mul_le_mul_of_nonneg_left hx.2 hk
      push_cast
      nlinarith
    have hh := ih (k + 1) hlo hhi horder hx.1 hx2
    have hm : ((k + 1 : ℕ) : ℝ) + (n : ℝ) + 3 = m := by dsimp [m]; push_cast; ring
    have hC : (((k + 1 : ℕ) : ℝ) + (n : ℝ) + 4) ^ 2 / 2 = C := by dsimp [C]; push_cast; ring
    rw [hm, hC] at hh
    rw [max_eq_right hx.1]
    have hd := div_le_div_of_nonneg_right hh (show 0 ≤ x by linarith [hx.1])
    convert! hd using 1; ring

end OrderedWindowAndAffineBound

section ExponentialTailAndAssembly

noncomputable def expTerm (x : ℝ) (n : ℕ) : ℝ := x ^ n / (n.factorial : ℝ)
noncomputable def firstExpTerm (x : ℝ) (n : ℕ) : ℝ := (n : ℝ) * expTerm x n
noncomputable def secondExpTerm (x : ℝ) (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) * expTerm x n
noncomputable def weightedExpTerm (x : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2 * expTerm x n

theorem expTerm_hasSum (x : ℝ) : HasSum (expTerm x) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using! NormedSpace.expSeries_div_hasSum_exp x

theorem firstExpTerm_succ (x : ℝ) (n : ℕ) : firstExpTerm x (n + 1) = x * expTerm x n := by
  unfold firstExpTerm expTerm
  rw [Nat.factorial_succ, pow_succ, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem secondExpTerm_add_two (x : ℝ) (n : ℕ) : secondExpTerm x (n + 2) = x ^ 2 * expTerm x n := by
  unfold secondExpTerm expTerm
  rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ]
  push_cast
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem firstExpTerm_hasSum (x : ℝ) : HasSum (firstExpTerm x) (x * Real.exp x) := by
  apply (hasSum_nat_add_iff' 1).mp
  have hh := (expTerm_hasSum x).mul_left x
  simp_rw [firstExpTerm_succ]
  simpa only [Finset.sum_range_one, firstExpTerm, Nat.cast_zero, zero_mul, sub_zero] using! hh

theorem secondExpTerm_hasSum (x : ℝ) : HasSum (secondExpTerm x) (x ^ 2 * Real.exp x) := by
  apply (hasSum_nat_add_iff' 2).mp
  have hh := (expTerm_hasSum x).mul_left (x ^ 2)
  simp_rw [secondExpTerm_add_two]
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    secondExpTerm, Nat.cast_zero, Nat.cast_one, zero_mul, sub_self, mul_zero, add_zero, sub_zero] using! hh

theorem weightedExpTerm_hasSum (x : ℝ) :
    HasSum (weightedExpTerm x) ((x ^ 2 + 3 * x + 1) * Real.exp x) := by
  have hh := ((secondExpTerm_hasSum x).add ((firstExpTerm_hasSum x).mul_left 3)).add (expTerm_hasSum x)
  convert! hh using 1
  · funext n
    unfold weightedExpTerm secondExpTerm firstExpTerm
    ring
  · ring

theorem weighted_log_two_tail_summable :
    Summable (fun n : ℕ => weightedExpTerm (Real.log 2) (n + 4)) :=
  ((hasSum_nat_add_iff' 4).mpr (weightedExpTerm_hasSum (Real.log 2))).summable

theorem actual_omission_factorial_bound (n : ℕ) :
    omissionLossTerm (n + 3) ≤
      (1 : ℝ) / 2 * (3 / Real.log 2 - 2) * weightedExpTerm (Real.log 2) (n + 4) := by
  have hh := scalarTailMass_affine_bound (n + 1) 0 (S := 0) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
  norm_num only [Nat.cast_zero, zero_add] at hh
  have hm : ((n + 1 : ℕ) : ℝ) + 3 = ((n + 4 : ℕ) : ℝ) := by push_cast; ring
  rw [hm, show (n + 1) + 3 = n + 4 by omega, show n + 4 = (n + 3) + 1 by omega, orderedAffine_at_two] at hh
  have hc := (actual_loss_le_scalarTailMass (n + 1)).trans hh
  have he : (n + 1) + 2 = n + 3 := by omega
  rw [he] at hc
  convert! hc using 1
  unfold weightedExpTerm expTerm
  push_cast
  ring

theorem omissionLossTerm_summable_and_bound :
    Summable omissionLossTerm ∧
      (∑' n, omissionLossTerm n) ≤
        1 + L2 + L3 + (1 / 2 : ℝ) * (3 / Real.log 2 - 2) *
          (∑' n, weightedExpTerm (Real.log 2) (n + 4)) := by
  have hmaj : Summable (fun n : ℕ =>
      (1 : ℝ) / 2 * (3 / Real.log 2 - 2) * weightedExpTerm (Real.log 2) (n + 4)) :=
    weighted_log_two_tail_summable.mul_left _
  have htail : Summable (fun n : ℕ => omissionLossTerm (n + 3)) :=
    Summable.of_nonneg_of_le (fun n => omissionLossTerm_nonnegative (n + 3))
      actual_omission_factorial_bound hmaj
  have hsum : Summable omissionLossTerm := (summable_nat_add_iff 3).mp htail
  refine ⟨hsum, ?_⟩
  have hsplit : (∑ n ∈ Finset.range 3, omissionLossTerm n) + (∑' n, omissionLossTerm (n + 3)) =
      ∑' n, omissionLossTerm n := hsum.sum_add_tsum_nat_add 3
  have hfirst3 : (∑ n ∈ Finset.range 3, omissionLossTerm n) = 1 + L2 + L3 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      actual_first_loss_eq_one, actual_second_loss_eq_L2, actual_third_loss_eq_L3]
  have htail_le : (∑' n, omissionLossTerm (n + 3)) ≤
      (1 / 2 : ℝ) * (3 / Real.log 2 - 2) * (∑' n, weightedExpTerm (Real.log 2) (n + 4)) := by
    have h := htail.tsum_le_tsum actual_omission_factorial_bound hmaj
    simpa only [tsum_mul_left] using h
  linarith

end ExponentialTailAndAssembly

end ErdosOmissionH3

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1.H3 := by
  dsimp only [OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1.H3]
  have hd : ErdosOmissionH3.omissionLossTerm = fun n : ℕ =>
      (∫ y in Set.Ioi (1 : ℝ), 2 * (y ^ 2 - 1) * (ErdosOmissionH3.gate^[n] ErdosOmissionH3.omissionForce) false (2 * y + 2) 2) +
       ∫ y in Set.Ioi (0 : ℝ), 2 * y ^ 2 * (ErdosOmissionH3.gate^[n] ErdosOmissionH3.omissionForce) true (2 * y + 2) 2 := by
    funext n
    simp only [ErdosOmissionH3.omissionLossTerm, ErdosOmissionH3.omissionDensity,
      ErdosOmissionH3.sourceWeight, ErdosOmissionH3.sourceDomain,
      ErdosOmissionH3.gateIterate_eq_iterate, Bool.false_eq_true, ↓reduceIte]
  have hf : (fun n : ℕ => ErdosOmissionH3.weightedExpTerm (Real.log 2) (n + 4)) =
      fun n : ℕ => ((n : ℝ) + 5) ^ 2 * ((Real.log 2) ^ (n + 4) / ((n + 4).factorial : ℝ)) := by
    funext n
    unfold ErdosOmissionH3.weightedExpTerm ErdosOmissionH3.expTerm
    push_cast
    ring
  have hmain := ErdosOmissionH3.omissionLossTerm_summable_and_bound
  rw [hd, hf] at hmain
  exact hmain
