import OMAReductions.R_Erdos1133_erdos_1133_variants_weaker_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
A polynomial bounded on a fine uniform grid is bounded on the interval.
The derivative estimate uses Chebyshev extremality at an endpoint, applied
to the longer of the two intervals that meet at the evaluation point.
-/

open Filter Polynomial Set

namespace OMA.E1133

noncomputable def grid (n k : ℕ) : ℝ := 2 * (k : ℝ) / (n : ℝ)^3 - 1

lemma grid_near {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∃ k ≤ n^3, grid n k ∈ Icc (-1 : ℝ) 1 ∧ |x - grid n k| ≤ 2 / (n : ℝ)^3 := by
  let B : ℝ := (n : ℝ)^3
  have hB : 0 < B := by dsimp [B]; positivity
  let t := (x + 1) * B / 2
  let k := ⌊t⌋₊
  have ht : 0 ≤ t := by
    unfold t
    exact div_nonneg (mul_nonneg (by linarith [hx.1]) hB.le) (by norm_num)
  have hfloor : (k : ℝ) ≤ t := Nat.floor_le ht
  have hnext : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have hkb : (k : ℝ) ≤ B := hfloor.trans (by
    dsimp [t]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hB.le])
  have hk : k ≤ n^3 := by
    dsimp [B] at hkb
    exact_mod_cast hkb
  have hleft : grid n k ≤ x := by
    change 2 * (k : ℝ) / B - 1 ≤ x
    rw [sub_le_iff_le_add, div_le_iff₀ hB]
    dsimp [t] at hfloor
    linarith
  have hright : x < grid n k + 2 / B := by
    change x < 2 * (k : ℝ) / B - 1 + 2 / B
    rw [show 2 * (k : ℝ) / B - 1 + 2 / B = 2 * ((k : ℝ) + 1) / B - 1 by ring,
      lt_sub_iff_add_lt, lt_div_iff₀ hB]
    dsimp [t] at hnext
    linarith
  refine ⟨k, hk, ⟨?_, hleft.trans hx.2⟩, ?_⟩
  · change -1 ≤ 2 * (k : ℝ) / B - 1
    linarith [show 0 ≤ 2 * (k : ℝ) / B by positivity]
  · change |x - grid n k| ≤ 2 / B
    rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
    linarith

lemma derivative_bound {P : ℝ[X]} {n : ℕ} {M : ℝ} (hM : 0 < M)
    (hdeg : P.natDegree ≤ n) (hP : ∀ t ∈ Icc (-1 : ℝ) 1, |P.eval t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |P.derivative.eval x| ≤ 2 * (n : ℝ)^2 * M := by
  let y : ℝ := if 0 ≤ x then -1 else 1
  let s := (x - y) / 2
  have hy : y ∈ Icc (-1 : ℝ) 1 := by
    dsimp [y]
    split <;> norm_num
  have hs : 1 ≤ 2 * |s| := by
    dsimp [s, y]
    by_cases h : 0 ≤ x
    · rw [if_pos h, abs_of_nonneg (by linarith)]
      linarith
    · rw [if_neg h, abs_of_nonpos (by linarith [le_of_not_ge h])]
      linarith [le_of_not_ge h]
  let L : ℝ[X] := C s * X + C (x - s)
  let Q := C M⁻¹ * P.comp L
  have hL (t : ℝ) : L.eval t = s*t + (x-s) := by simp [L]
  have hLone : L.eval 1 = x := by rw [hL]; ring
  have hLdeg : L.natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  have hQdeg : Q.degree ≤ n := natDegree_le_iff_degree_le.mp (by
    apply (natDegree_C_mul_le _ _).trans
    exact natDegree_comp_le.trans ((Nat.mul_le_mul hdeg hLdeg).trans (by simp)))
  have hLmap (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : L.eval t ∈ Icc (-1 : ℝ) 1 := by
    have hA : 0 ≤ (t+1)/2 := by linarith [ht.1]
    have hB : 0 ≤ (1-t)/2 := by linarith [ht.2]
    rw [hL, show s*t + (x-s) = ((t+1)/2)*x + ((1-t)/2)*y by dsimp [s]; ring]
    exact ⟨by linarith [mul_le_mul_of_nonneg_left hx.1 hA, mul_le_mul_of_nonneg_left hy.1 hB],
      by linarith [mul_le_mul_of_nonneg_left hx.2 hA, mul_le_mul_of_nonneg_left hy.2 hB]⟩
  have hQbound : ∀ t ∈ Icc (-1 : ℝ) 1, |Q.eval t| ≤ 1 := by
    intro t ht
    simp only [Q, eval_mul, eval_C, eval_comp, abs_mul, abs_inv, abs_of_pos hM]
    exact (inv_mul_le_iff₀ hM).mpr (by simpa using hP _ (hLmap _ ht))
  have upper := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := 1) le_rfl hQdeg hQbound
  have lower := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := 1) (P := -Q) le_rfl (by simpa using hQdeg)
    (by intro t ht; simpa only [eval_neg, abs_neg] using hQbound t ht)
  simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one, Int.cast_natCast,
    derivative_neg, eval_neg] at upper lower
  have hq : |Q.derivative.eval 1| ≤ (n : ℝ)^2 := abs_le.mpr ⟨by linarith, upper⟩
  have hLder : L.derivative = C s := by simp [L]
  have hqEval : Q.derivative.eval 1 = M⁻¹ * s * P.derivative.eval x := by
    simp only [Q, derivative_C_mul, derivative_comp, hLder, eval_mul, eval_C, eval_comp, hLone]
    ring
  rw [hqEval, abs_mul, abs_mul, abs_inv, abs_of_pos hM] at hq
  have hp : |s| * |P.derivative.eval x| ≤ (n : ℝ)^2 * M := by
    have h := mul_le_mul_of_nonneg_right hq hM.le
    have he : (M⁻¹ * |s| * |P.derivative.eval x|) * M = |s| * |P.derivative.eval x| := by
      field_simp
    rwa [he] at h
  calc
    |P.derivative.eval x| ≤ (2 * |s|) * |P.derivative.eval x| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (abs_nonneg (P.derivative.eval x))
    _ = 2 * (|s| * |P.derivative.eval x|) := by ring
    _ ≤ 2 * ((n : ℝ)^2 * M) := by gcongr
    _ = _ := by ring

lemma eval_near {P : ℝ[X]} {n : ℕ} {M : ℝ} (hn : 0 < n) (hM : 0 < M)
    (hdeg : P.natDegree ≤ n) (hP : ∀ t ∈ Icc (-1 : ℝ) 1, |P.eval t| ≤ M)
    {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huv : |u-v| ≤ 2 / (n : ℝ)^3) : |P.eval u - P.eval v| ≤ 4 * M / n := by
  have hd (t : ℝ) (_ : t ∈ Icc (-1 : ℝ) 1) :
      ‖deriv (fun x => P.eval x) t‖ ≤ 2 * (n : ℝ)^2 * M := by
    rw [(P.hasDerivAt t).deriv, Real.norm_eq_abs]
    exact derivative_bound hM hdeg hP ‹t ∈ Icc (-1 : ℝ) 1›
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (P.hasDerivAt t).differentiableAt) hd (convex_Icc (-1 : ℝ) 1) hv hu
  simp only [Real.norm_eq_abs] at h
  refine h.trans ((mul_le_mul_of_nonneg_left huv (by positivity)).trans_eq ?_)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

end OMA.E1133

theorem OMA.solution : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H1 := by
  intro K hK
  obtain ⟨N, hN⟩ := exists_nat_gt (max (8 : ℝ) (16*K))
  filter_upwards [eventually_ge_atTop N] with n hnN
  have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hnN
  have h8 : (8 : ℝ) ≤ n := (le_max_left _ _).trans (hN.le.trans hNn)
  have h16 : 16*K ≤ (n : ℝ) := (le_max_right _ _).trans (hN.le.trans hNn)
  have hn : 0 < n := by
    by_contra! h
    rw [show n = 0 by omega] at h8
    norm_num at h8
  have hnR : (0 : ℝ) < n := by positivity
  dsimp only
  intro x hx
  obtain ⟨k, hk, hgk, hnear⟩ := OMA.E1133.grid_near hn hx
  refine ⟨k, hk, ?_⟩
  intro P hdeg hsample
  change ∀ j ≤ n^3, |P.eval (OMA.E1133.grid n j)| ≤ K at hsample
  change |P.eval x - P.eval (OMA.E1133.grid n k)| ≤ 1
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
    (f := fun t => |P.eval t|) (continuous_abs.comp P.continuous).continuousOn
  let M := |P.eval y| + K
  have hM : 0 < M := by dsimp [M]; linarith [abs_nonneg (P.eval y)]
  have hbound t ht : |P.eval t| ≤ M :=
    ((isMaxOn_iff.mp hmax) t ht).trans (by dsimp [M]; linarith)
  obtain ⟨j, hj, hgj, hjnear⟩ := OMA.E1133.grid_near hn hy
  have hynear := OMA.E1133.eval_near hn hM hdeg hbound hy hgj hjnear
  have htri := norm_add_le (P.eval y - P.eval (OMA.E1133.grid n j)) (P.eval (OMA.E1133.grid n j))
  simp only [sub_add_cancel, Real.norm_eq_abs] at htri
  have hyb := htri.trans (add_le_add hynear (hsample j hj))
  have hhalf : 4*M/(n:ℝ) ≤ M/2 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr h8) hM.le]
  have hsmall : M ≤ 4*K := by
    linarith only [hyb, hhalf, show M = |P.eval y| + K from rfl]
  refine (OMA.E1133.eval_near hn hM hdeg hbound hx hgk hnear).trans ?_
  apply (div_le_iff₀ hnR).mpr
  linarith
