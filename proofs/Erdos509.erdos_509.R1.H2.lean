import OMAReductions.R_Erdos509_erdos_509_R1
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
Proof of `Erdos509.erdos_509.R1.H2`: if every root of a monic nonconstant complex polynomial `f`
lies within distance `√3` of the root centroid `c`, then `{z : ℂ | ‖f.eval z‖ ≤ 1}` is contained in
the single closed disc `Metric.closedBall c 2` of radius `2`.

The inclusion follows directly from concavity of `Real.log` on `(0, ∞)` applied to `2 - x` on
`[-√3, √3]`, using `(2 + √3)(2 - √3) = 1` and the zero-sum property of the rotated real parts of
`a - c` over the roots `a` of `f`.
-/

-- Step Erdos509.erdos_509.R1.H2: hypothesis H2 of reduction Erdos509.erdos_509.R1
-- Credit: @yhay81

namespace OMA.Erdos509_R1_H2

open Polynomial

private lemma log_multiset_prod {s : Multiset ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    Real.log s.prod = (s.map Real.log).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (by simp)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx => hs x (by simp [hx])
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs' 0 h0 rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, Real.log_mul ha hprod, ih hs']

private lemma multiset_sum_lt_sum {α : Type*} {s : Multiset α} (hne : s ≠ 0)
    (f g : α → ℝ) (h : ∀ a ∈ s, f a < g a) :
    (s.map f).sum < (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    have ha : f a < g a := h a (by simp)
    by_cases hs0 : s = 0
    · subst hs0; simp [ha]
    · exact add_lt_add ha (ih hs0 fun b hb => h b (by simp [hb]))

private lemma log_two_sub_ge {x : ℝ} (hx : |x| ≤ Real.sqrt 3) :
    -(Real.log (2 + Real.sqrt 3) / Real.sqrt 3) * x ≤ Real.log (2 - x) := by
  set s := Real.sqrt 3
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs_sq : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs_lt2 : s < 2 := by nlinarith
  have hx_lo : -s ≤ x := (abs_le.mp hx).1
  have hx_hi : x ≤ s := (abs_le.mp hx).2
  set t := (x + s) / (2 * s)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
  have ht1 : 0 ≤ 1 - t := by
    have : t ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hcomb : (1 - t) * (2 + s) + t * (2 - s) = 2 - x := by
    dsimp [t]
    field_simp [hs_pos.ne']
    ring
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (Set.mem_Ioi.mpr (show 0 < 2 + s by linarith))
    (Set.mem_Ioi.mpr (show 0 < 2 - s by linarith)) ht1 ht0 (by ring)
  simp only [smul_eq_mul] at hconc
  rw [hcomb] at hconc
  have hinv : 2 - s = (2 + s)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    nlinarith [hs_sq]
  rw [hinv, Real.log_inv] at hconc
  have hlin : (1 - t) * Real.log (2 + s) + t * -Real.log (2 + s) =
      -(Real.log (2 + s) / s) * x := by
    dsimp [t]
    field_simp [hs_pos.ne']
    ring
  linarith

private lemma subset_closedBall_two (f : ℂ[X]) (hf : f.Monic) (hdeg : f.natDegree ≠ 0)
    (hroots : ∀ a ∈ f.roots, ‖a - f.roots.sum / (f.natDegree : ℂ)‖ ≤ Real.sqrt 3) :
    {z : ℂ | ‖f.eval z‖ ≤ 1} ⊆ Metric.closedBall (f.roots.sum / (f.natDegree : ℂ)) 2 := by
  set n := f.natDegree
  set c := f.roots.sum / (n : ℂ)
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hdeg
  have hcard : f.roots.card = n := (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
  have hroots_ne : f.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  have hf_eq : f = (f.roots.map fun a => X - C a).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf hcard).symm
  intro z hz
  change ‖f.eval z‖ ≤ 1 at hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hgt
  push Not at hgt
  set R := ‖z - c‖
  have hR_pos : 0 < R := by linarith
  have hR_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  set u : ℂ := (z - c) / (R : ℂ)
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR_pos.le, div_self hR_pos.ne']
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu_norm
    norm_num at hu_norm
  have hzc : z - c = (R : ℂ) * u := by
    dsimp [u]
    exact (mul_div_cancel₀ (z - c) hR_ne).symm
  let x : ℂ → ℝ := fun a => ((a - c) / u).re
  set k : ℝ := Real.log (2 + Real.sqrt 3) / Real.sqrt 3
  have hs_lt2 : Real.sqrt 3 < 2 := by
    have : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3]
  have hterm : ∀ a ∈ f.roots, 0 < ‖z - a‖ ∧ -k * x a < Real.log ‖z - a‖ := by
    intro a ha
    have hxa_abs : |x a| ≤ Real.sqrt 3 := by
      calc
        |x a| ≤ ‖(a - c) / u‖ := Complex.abs_re_le_norm _
        _ = ‖a - c‖ / ‖u‖ := norm_div _ _
        _ = ‖a - c‖ := by rw [hu_norm, div_one]
        _ ≤ Real.sqrt 3 := hroots a ha
    have h2x_pos : 0 < 2 - x a := by
      have := (abs_le.mp hxa_abs).2
      linarith
    have hza_eq : z - a = u * ((R : ℂ) - (a - c) / u) := by
      rw [mul_sub, mul_comm u (R : ℂ), ← hzc, mul_div_cancel₀ _ hu_ne]
      ring
    have hza_ge : R - x a ≤ ‖z - a‖ := by
      rw [hza_eq, norm_mul, hu_norm, one_mul]
      have hre : ((R : ℂ) - (a - c) / u).re = R - x a := by
        simp [x]
      rw [← hre]
      exact Complex.re_le_norm _
    have hza_gt : 2 - x a < ‖z - a‖ := by linarith
    refine ⟨by linarith, ?_⟩
    exact (log_two_sub_ge hxa_abs).trans_lt (Real.log_lt_log h2x_pos hza_gt)
  have hsum_lt : (f.roots.map fun a => -k * x a).sum <
      (f.roots.map fun a => Real.log ‖z - a‖).sum :=
    multiset_sum_lt_sum hroots_ne _ _ fun a ha => (hterm a ha).2
  have hsum_x : (f.roots.map x).sum = 0 := by
    have h1 : (f.roots.map fun a => (a - c) / u).sum = 0 := by
      have hdiv : (f.roots.map fun a => (a - c) / u).sum =
          (f.roots.map fun a => a - c).sum / u := by
        simp [div_eq_mul_inv, Multiset.sum_map_mul_right]
      rw [hdiv]
      have hsub : (f.roots.map fun a => a - c).sum = f.roots.sum - (f.roots.card : ℂ) * c := by
        induction f.roots using Multiset.induction_on with
        | empty => simp
        | cons a s ih =>
          simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
            Nat.cast_one]
          rw [ih]
          ring
      rw [hsub, hcard]
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdeg
      dsimp [c]
      rw [mul_div_cancel₀ _ hn_ne, sub_self, zero_div]
    have hre := congrArg Complex.re h1
    rw [Complex.zero_re] at hre
    have hmap : ((f.roots.map fun a => (a - c) / u).sum).re = (f.roots.map x).sum := by
      simpa [x, Multiset.map_map] using
        (AddMonoidHom.map_multiset_sum Complex.reAddGroupHom (f.roots.map fun a => (a - c) / u))
    linarith
  have hlhs : (f.roots.map fun a => -k * x a).sum = 0 := by
    have hmul : (f.roots.map fun a => -k * x a).sum = -k * (f.roots.map x).sum := by
      simp [Multiset.sum_map_mul_left]
    rw [hmul, hsum_x, mul_zero]
  have hnorm_mprod : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map norm).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]
  have hnorm_eval : ‖f.eval z‖ = (f.roots.map fun a => ‖z - a‖).prod := by
    conv_lhs => rw [hf_eq]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    have hev : (f.roots.map (Polynomial.eval z ∘ fun a => X - C a)) =
        f.roots.map fun a => z - a := by
      congr 1; ext a; simp
    rw [hev, hnorm_mprod, Multiset.map_map]
    rfl
  have hpos_eval : 0 < ‖f.eval z‖ := by
    rw [hnorm_eval]
    exact Multiset.prod_pos fun r hr => by
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hr
      exact (hterm a ha).1
  have hrhs : Real.log ‖f.eval z‖ = (f.roots.map fun a => Real.log ‖z - a‖).sum := by
    rw [hnorm_eval, log_multiset_prod]
    · rw [Multiset.map_map]; rfl
    · intro r hr
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hr
      exact (hterm a ha).1.ne'
  have hlog_pos : 0 < Real.log ‖f.eval z‖ := by linarith
  have hlog_le : Real.log ‖f.eval z‖ ≤ 0 := by
    simpa [Real.log_one] using Real.log_le_log hpos_eval hz
  linarith

private theorem main_H2 : OMA.R_Erdos509_erdos_509_R1.H2 := by
  intro f hf hdeg hroots
  refine ⟨PUnit, ⟨{
    C := fun _ => f.roots.sum / (f.natDegree : ℂ)
    R := fun _ => 2
    h_cover := fun z hz => by
      simp only [Set.iUnion_const]
      exact subset_closedBall_two f hf hdeg hroots hz
    h_summable := (hasSum_fintype _).summable
    h_bdd := by simp
    h_pos := fun _ => by norm_num
  }⟩⟩

end OMA.Erdos509_R1_H2

theorem OMA.solution : OMA.R_Erdos509_erdos_509_R1.H2 :=
  OMA.Erdos509_R1_H2.main_H2
