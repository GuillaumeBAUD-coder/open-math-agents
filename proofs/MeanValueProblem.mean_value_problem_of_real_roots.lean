import FormalConjectures.Wikipedia.MeanValueProblem
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Choose the nearest critical point on the side selected by the sum of the
reciprocal critical displacements. On the resulting segment the derivative is
a product of nonnegative linear factors. AM–GM and the binomial theorem give
the pointwise bound needed for integration.
-/

open Finset Polynomial Set
open scoped BigOperators Polynomial

namespace OMA.SmaleReal

private theorem choose_direction {n : ℕ} (hn : 0 < n) (u : Fin n → ℝ)
    (hu : ∀ i, u i ≠ 0) :
    ∃ i, (∀ j, u j / u i ≤ 1) ∧ 0 ≤ (∑ j, u j) / u i := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_cases hs : 0 ≤ ∑ j, u j
  · obtain ⟨i, _, hi⟩ := univ.exists_max_image u univ_nonempty
    have hp : 0 < u i := by
      by_contra! h
      have hneg : u i < 0 := lt_of_le_of_ne h (hu i)
      have : ∑ j, u j < 0 := sum_neg (fun j _ => (hi j (mem_univ _)).trans_lt hneg)
        univ_nonempty
      linarith
    exact ⟨i, fun j => (div_le_one hp).2 (hi j (mem_univ _)), div_nonneg hs hp.le⟩
  · obtain ⟨i, _, hi⟩ := univ.exists_min_image u univ_nonempty
    have hneg : u i < 0 := by
      by_contra! h
      exact hs (sum_nonneg fun j _ => h.trans (hi j (mem_univ _)))
    exact ⟨i, fun j => (div_le_one_of_neg hneg).2 (hi j (mem_univ _)),
      div_nonneg_of_nonpos (le_of_not_ge hs) hneg.le⟩

private theorem binomial_bound (k : ℕ) (hk : k ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t / k) ^ k ≤ ∑ j ∈ range (k + 1), t ^ j := by
  rw [add_comm, add_pow]
  apply Finset.sum_le_sum
  intro j _
  simp only [one_pow, mul_one, div_pow]
  have hpos : 0 < (k : ℝ) ^ j := by positivity
  have hchoose : (k.choose j : ℝ) ≤ (k : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow k j
  calc
    t ^ j / (k : ℝ) ^ j * (k.choose j : ℝ) ≤ t ^ j / (k : ℝ) ^ j * (k : ℝ) ^ j := by gcongr
    _ = t ^ j := div_mul_cancel₀ _ hpos.ne'

private theorem product_estimate {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (hi : a i = 1)
    (ha : ∀ j, a j ≤ 1) (hsum : 0 ≤ ∑ j, a j) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∏ j, (1 - t * a j)) ≤ 1 - t ^ n := by
  classical
  let s := (univ : Finset (Fin n)).erase i
  have hcard : s.card + 1 = n := by
    simp [s, card_erase_of_mem (mem_univ i), Nat.sub_add_cancel i.pos]
  have hpos (j : Fin n) : 0 ≤ 1 - t * a j := by
    linarith [mul_le_mul_of_nonneg_left (ha j) ht.1, ht.2]
  rw [← mul_prod_erase univ (fun j => 1 - t * a j) (mem_univ i), hi, mul_one]
  change (1 - t) * (∏ j ∈ s, (1 - t * a j)) ≤ _
  have hgeom : (1 - t) * (∑ j ∈ range (s.card + 1), t ^ j) = 1 - t ^ n := by
    have H := geom_sum_mul t (s.card + 1)
    rw [hcard] at H ⊢
    linarith
  rw [← hgeom]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht.2)
  by_cases hzero : s.card = 0
  · have he : s = ∅ := card_eq_zero.mp hzero
    simp [he]
  have hp : 0 < (s.card : ℝ) := by positivity
  have ham := Real.geom_mean_le_arith_mean s (fun _ => 1) (fun j => 1 - t * a j)
    (by intros; norm_num) (by simpa using hp) (fun j _ => hpos j)
  simp only [Real.rpow_one, one_mul, sum_const, nsmul_eq_mul, mul_one] at ham
  have hp' : 0 ≤ ∏ j ∈ s, (1 - t * a j) := prod_nonneg fun j _ => hpos j
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hp' _) ham s.card
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp', inv_mul_cancel₀ hp.ne', Real.rpow_one] at hpow
  have hsum' : -1 ≤ ∑ j ∈ s, a j := by
    have H := sum_erase_add univ a (mem_univ i)
    rw [hi] at H
    change (∑ j ∈ s, a j) + 1 = _ at H
    linarith
  have havg : (∑ j ∈ s, (1 - t * a j)) / s.card ≤ 1 + t / s.card := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← mul_sum, div_le_iff₀ hp]
    field_simp
    linarith [mul_le_mul_of_nonneg_left hsum' ht.1]
  exact hpow.trans ((pow_le_pow_left₀ (div_nonneg (sum_nonneg fun j _ => hpos j) hp.le) havg
    s.card).trans (binomial_bound _ hzero ht.1))

private theorem critical_im_eq {p : Polynomial ℂ} {z c : ℂ} (hp : 2 ≤ p.natDegree)
    (hr : ∀ x : ℂ, p.eval x = p.eval z → x.im = z.im)
    (hc : p.derivative.eval c = 0) : c.im = z.im := by
  let q := p - C (p.eval z)
  have hqn : 0 < q.natDegree := by
    rw [show q = p - C (p.eval z) by rfl, natDegree_sub_C]
    omega
  have hder : q.derivative = p.derivative := by simp [q]
  have hcrit : c ∈ q.derivative.rootSet ℂ := by
    rw [hder, mem_rootSet, coe_aeval_eq_eval]
    exact ⟨derivative_ne_zero.mpr (by omega), hc⟩
  have hroots : q.rootSet ℂ ⊆ {x : ℂ | x.im = z.im} := by
    intro x hx
    apply hr x
    have hxq := (mem_rootSet.mp hx).2
    simpa [q, sub_eq_zero] using hxq
  exact convexHull_min hroots (convex_hyperplane Complex.imLm.isLinear z.im)
    (rootSet_derivative_subset_convexHull_rootSet (natDegree_pos_iff_degree_pos.mp hqn) hcrit)

private theorem factor_eval (q : ℂ[X]) :
    ∃ (n : ℕ) (w : Fin n → ℂ), n = q.natDegree ∧
      (∀ j, q.eval (w j) = 0) ∧ (∀ x, q.eval x = q.leadingCoeff * ∏ j, (x - w j)) := by
  let L := q.roots.toList
  let w : Fin L.length → ℂ := L.get
  refine ⟨L.length, w, ?_, ?_, ?_⟩
  · simp [L, IsAlgClosed.card_roots_eq_natDegree]
  · intro j
    have hm := Multiset.mem_toList.mp (List.get_mem L j)
    exact (mem_roots'.mp hm).2
  · intro x
    have H := (IsAlgClosed.splits q).eval_eq_prod_roots (x := x)
    rw [← q.roots.coe_toList] at H
    simp only [Multiset.map_coe, Multiset.prod_coe] at H
    change q.eval x = q.leadingCoeff * (L.map (fun r => x-r)).prod at H
    rw [H]
    congr 1
    calc
      _ = ((List.ofFn w).map fun r => x-r).prod := by rw [show List.ofFn w = L from List.ofFn_get L]
      _ = _ := by rw [List.map_ofFn, List.prod_ofFn]; rfl

private theorem segment_bound (p : ℂ[X]) (z D : ℂ) (hD : D ≠ 0) (n : ℕ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖p.derivative.eval (z + (t : ℂ) * D)‖ ≤ ‖p.derivative.eval z‖ * (1 - t ^ n)) :
    ‖p.eval z - p.eval (z + D)‖ / ‖z - (z + D)‖ ≤
      (n : ℝ) / (n + 1) * ‖p.derivative.eval z‖ := by
  let g := fun t : ℝ => p.derivative.eval (z + (t : ℂ) * D) * D
  have hg : Continuous g := by dsimp [g]; fun_prop
  have dpath (t : ℝ) : HasDerivAt (fun t : ℝ => p.eval (z + (t : ℂ) * D)) (g t) t := by
    apply HasDerivAt.comp_ofReal (e := fun x : ℂ => p.eval (z + x * D))
    simpa [g, Function.comp_def] using! (p.hasDerivAt (z + (t : ℂ) * D)).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const D).const_add z)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => dpath t) (hg.intervalIntegrable ..)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero] at hFTC
  have hmajor (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖g t‖ ≤ (‖p.derivative.eval z‖ * ‖D‖) * (1 - t ^ n) := by
    simp only [g, norm_mul]
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg D)
  have hi := (intervalIntegral.norm_integral_le_integral_norm
    (f := g) (μ := MeasureTheory.volume) (zero_le_one : (0 : ℝ) ≤ 1)).trans
    (intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1) (hg.norm.intervalIntegrable ..)
      ((continuous_const.mul (continuous_const.sub (continuous_id.pow n))).intervalIntegrable ..)
      hmajor)
  rw [hFTC] at hi
  change _ ≤ ∫ t : ℝ in 0..1, (‖p.derivative.eval z‖ * ‖D‖) * (1 - t ^ n) at hi
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t ^ n)
    (continuous_const.intervalIntegrable ..) ((continuous_id.pow n).intervalIntegrable ..),
    integral_one, integral_pow] at hi
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero] at hi
  rw [norm_sub_rev, show z - (z + D) = -D by ring, norm_neg, div_le_iff₀ (norm_pos_iff.mpr hD)]
  calc
    _ ≤ (‖p.derivative.eval z‖ * ‖D‖) * (1 - 1 / ((n : ℝ) + 1)) := hi
    _ = _ := by field_simp; ring

end OMA.SmaleReal
open OMA.SmaleReal in
theorem OMA.solution : type_of% @MeanValueProblem.mean_value_problem_of_real_roots := by
  classical
  intro p hp z hz _K
  by_cases h0 : p.derivative.eval z = 0
  · exact ⟨z, h0, by simp [h0]⟩
  obtain ⟨n, w, hn, hw, hfactor⟩ := factor_eval p.derivative
  rw [natDegree_derivative] at hn
  have hpos : 0 < n := by omega
  let v := fun j => (w j - z).re
  have hreal (j : Fin n) : (v j : ℂ) = w j - z := by
    apply Complex.ext
    · simp [v]
    · simp [critical_im_eq hp hz (hw j)]
  have hv (j : Fin n) : v j ≠ 0 := by
    intro H
    have h : w j - z = 0 := by rw [← hreal, H, Complex.ofReal_zero]
    exact h0 (sub_eq_zero.mp h ▸ hw j)
  let u := fun j => (v j)⁻¹
  have hu (j : Fin n) : u j ≠ 0 := inv_ne_zero (hv j)
  obtain ⟨i, hle, hsum⟩ := choose_direction hpos u hu
  let a := fun j => u j / u i
  have hai : a i = 1 := div_self (hu i)
  have hasum : 0 ≤ ∑ j, a j := by simpa [a, sum_div] using hsum
  have hav (j : Fin n) : v j * a j = v i := by
    dsimp [a, u]
    field_simp [hv j, hv i]
  let D := w i - z
  have hD : D ≠ 0 := by
    rw [show D = (v i : ℂ) from (hreal i).symm]
    exact_mod_cast hv i
  have hfac (t : ℝ) (j : Fin n) :
      z + (t : ℂ) * D - w j = (z - w j) * (↑(1 - t * a j) : ℂ) := by
    calc
      _ = ((t * v i - v j : ℝ) : ℂ) := by push_cast; rw [hreal i, hreal j]; dsimp [D]; ring
      _ = (((-v j) * (1 - t * a j) : ℝ) : ℂ) := by
        congr 1
        linear_combination -t * hav j
      _ = _ := by push_cast; rw [hreal j]; ring
  have he (t : ℝ) : p.derivative.eval (z + (t : ℂ) * D) =
      p.derivative.eval z * ↑(∏ j, (1 - t * a j)) := by
    rw [hfactor (z + (t : ℂ) * D), hfactor z]
    simp_rw [hfac]
    rw [prod_mul_distrib, Complex.ofReal_prod]
    ring
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖p.derivative.eval (z + (t : ℂ) * D)‖ ≤ ‖p.derivative.eval z‖ * (1 - t ^ n) := by
    have hnonneg : 0 ≤ ∏ j, (1 - t * a j) := by
      apply prod_nonneg
      intro j _
      linarith [mul_le_mul_of_nonneg_left (hle j) ht.1, ht.2]
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_left (product_estimate a i hai hle hasum ht) (norm_nonneg _)
  refine ⟨w i, hw i, ?_⟩
  have H := segment_bound p z D hD n hbound
  have hdeg : p.natDegree = n + 1 := by omega
  simpa [D, hdeg] using H
