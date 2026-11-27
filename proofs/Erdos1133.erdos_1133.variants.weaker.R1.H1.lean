import OMAReductions.R_Erdos1133_erdos_1133_variants_weaker_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Order.Floor.Ring

/-! Uniform approximation on the mesh from a Chebyshev endpoint derivative estimate. -/

namespace OMA.Mesh1133

open Polynomial

lemma interval_derivative_bound (P : Polynomial ℝ) (n : ℕ) (hP : P.natDegree ≤ n)
    (M : ℝ) (hM : 0 < M) (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |P.eval u| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |P.derivative.eval x| ≤ 2 * (n : ℝ)^2 * M := by
  let a : ℝ := if 0 ≤ x then 1/2 else -(1/2)
  have ha : |a| = 1/2 := by dsimp [a]; split <;> norm_num
  let L : Polynomial ℝ := C a * X + C (x - a)
  have hL1 : L.eval 1 = x := by simp [L]
  have hL (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : L.eval u ∈ Set.Icc (-1 : ℝ) 1 := by
    have hxlo := hx.1
    have hxhi := hx.2
    have hulo := hu.1
    have huhi := hu.2
    simp only [L, eval_add, eval_mul, eval_C, eval_X, Set.mem_Icc]
    dsimp [a]
    split <;> constructor <;> linarith
  let Q : Polynomial ℝ := C M⁻¹ * P.comp L
  have hbQ (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) : |Q.eval u| ≤ 1 := by
    simp only [Q, eval_mul, eval_C, eval_comp, abs_mul, abs_inv, abs_of_pos hM]
    calc
      _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hb _ (hL u hu)) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hLd : L.natDegree ≤ 1 := by
    rw [show L = C a * X + C (x-a) from rfl, natDegree_add_C]
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hQd : Q.degree ≤ n := by
    apply degree_le_of_natDegree_le
    exact (natDegree_C_mul_le _ _).trans
      (natDegree_comp_le.trans ((Nat.mul_le_mul hP hLd).trans_eq (Nat.mul_one n)))
  have upper (F : Polynomial ℝ) (hd : F.degree ≤ n)
      (hF : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |F.eval u| ≤ 1) :
      F.derivative.eval 1 ≤ (n : ℝ)^2 := by
    simpa [Polynomial.Chebyshev.derivative_T_eval_one] using
      (Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1) le_rfl hd hF)
  have hplus := upper Q hQd hbQ
  have hminus := upper (-Q) (by simpa using hQd) (fun u hu => by simpa using hbQ u hu)
  have habs : |Q.derivative.eval 1| ≤ (n : ℝ)^2 := by
    apply abs_le.mpr
    exact ⟨by simpa using (neg_le_neg hminus), hplus⟩
  have he : Q.derivative.eval 1 = M⁻¹ * (a * P.derivative.eval x) := by
    simp [Q, derivative_C_mul, derivative_comp, eval_comp, hL1,
      show L.derivative = C a by simp [L, derivative_C_mul_X]]
  rw [he, abs_mul, abs_mul, abs_inv, abs_of_pos hM, ha, ← div_eq_inv_mul] at habs
  have h := (div_le_iff₀ hM).mp habs
  linarith

open Set Polynomial Filter

lemma mesh_round {n : ℕ} (hn : 0 < n) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∃ k ≤ n^3, g k ∈ Icc (-1 : ℝ) 1 ∧ |u - g k| ≤ 2 / (n : ℝ)^3 := by
  dsimp only
  let d := (n : ℝ)^3
  have hd : 0 < d := by dsimp [d]; positivity
  let w := (u + 1) * d / 2
  have hw : 0 ≤ w := by dsimp [w]; exact div_nonneg (mul_nonneg (by linarith [hu.1]) hd.le) (by norm_num)
  let k := ⌊w⌋₊
  have hlo : (k : ℝ) ≤ w := Nat.floor_le hw
  have hhi : w < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hw' : w ≤ d := by dsimp [w]; nlinarith [mul_le_mul_of_nonneg_right hu.2 hd.le]
  have hk' : (k : ℝ) ≤ d := hlo.trans hw'
  have hk : k ≤ n^3 := by dsimp [d] at hk'; exact_mod_cast hk'
  refine ⟨k,hk,?_,?_⟩
  · constructor
    · change -1 ≤ 2 * (k : ℝ) / d - 1
      linarith [div_nonneg (by positivity : (0 : ℝ) ≤ 2 * k) hd.le]
    · change 2 * (k : ℝ) / d - 1 ≤ 1
      linarith [(div_le_iff₀ hd).mpr (show 2 * (k : ℝ) ≤ 2 * d by linarith)]
  · change |u - (2 * (k : ℝ) / d - 1)| ≤ 2 / d
    have hpos : 2 * (k : ℝ) / d ≤ u+1 := (div_le_iff₀ hd).mpr (by dsimp [w] at hlo; linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ u - (2 * (k : ℝ) / d - 1))]
    apply (le_div_iff₀ hd).mpr
    have hc := div_mul_cancel₀ (2 * (k : ℝ)) hd.ne'
    dsimp [w] at hhi
    nlinarith

lemma mesh_estimate
    (hMarkov : ∀ (P : Polynomial ℝ) (n : ℕ), P.natDegree ≤ n →
      ∀ M > (0 : ℝ), (∀ u ∈ Icc (-1 : ℝ) 1, |P.eval u| ≤ M) →
        ∀ u ∈ Icc (-1 : ℝ) 1, |P.derivative.eval u| ≤ 2 * (n : ℝ)^2 * M) :
  ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop,
    let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
    ∀ x ∈ Icc (-1 : ℝ) 1, ∃ k ≤ n^3, ∀ P : Polynomial ℝ,
      P.natDegree ≤ n → (∀ j ≤ n^3, |P.eval (g j)| ≤ K) →
      |P.eval x - P.eval (g k)| ≤ 1 := by
  intro K hK
  filter_upwards [Filter.eventually_ge_atTop ⌈8*(K+1)⌉₊] with n hn
  have hn' : 8*(K+1) ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn8 : (8 : ℝ) ≤ n := by linarith
  have hnr : (0 : ℝ) < n := by linarith
  have hnpos : 0 < n := by exact_mod_cast hnr
  dsimp only
  intro x hx
  let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
  obtain ⟨k,hk,hg,hxnear⟩ := mesh_round hnpos x hx
  refine ⟨k, hk, ?_⟩
  intro P hP hgrid
  obtain ⟨s,hs,hmax⟩ : ∃ s : ℝ, s ∈ Icc (-1 : ℝ) 1 ∧
      IsMaxOn (fun t => |P.eval t|) (Icc (-1 : ℝ) 1) s :=
    isCompact_Icc.exists_isMaxOn ⟨0, by constructor <;> norm_num⟩
      (continuous_abs.comp P.continuous).continuousOn
  let M := |P.eval s| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : |P.eval u| ≤ M := by
    dsimp [M]; linarith [show |P.eval u| ≤ |P.eval s| from hmax hu]
  have hlocal (u v : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
      (hd : |u-v| ≤ 2/(n:ℝ)^3) : |P.eval u - P.eval v| ≤ 4*M/(n:ℝ) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z (_ : z ∈ Icc (-1 : ℝ) 1) => P.differentiableAt)
      (fun z hz => by rw [P.deriv, Real.norm_eq_abs]; exact hMarkov P n hP M hM hbound z hz)
      (convex_Icc _ _) hv hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    apply h.trans
    calc
      _ ≤ (2*(n:ℝ)^2*M) * (2/(n:ℝ)^3) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by field_simp; ring
  obtain ⟨j,hj,hgj,hclose⟩ := mesh_round hnpos s hs
  have h1 := hlocal s (g j) hs hgj hclose
  have h2 : |P.eval s| ≤ |P.eval s - P.eval (g j)| + |P.eval (g j)| := by
    simpa only [sub_add_cancel] using abs_add_le (P.eval s - P.eval (g j)) (P.eval (g j))
  have h3 : 4*M/(n:ℝ) ≤ M/2 := (div_le_iff₀ hnr).mpr (by nlinarith [mul_le_mul_of_nonneg_left hn8 hM.le])
  have h4 : M ≤ 2*(K+1) := by
    have hnob := hgrid j hj
    change |P.eval (g j)| ≤ K at hnob
    change |P.eval s| + 1 ≤ 2*(K+1)
    change 4*M/(n:ℝ) ≤ (|P.eval s| + 1)/2 at h3
    linarith
  apply (hlocal x (g k) hx hg hxnear).trans
  exact (div_le_iff₀ hnr).mpr (by linarith)

end OMA.Mesh1133

theorem OMA.solution : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H1 :=
  OMA.Mesh1133.mesh_estimate OMA.Mesh1133.interval_derivative_bound
