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



open Filter Set Polynomial
namespace OMA.MeshPeak1133

lemma grid_obstruction_of_continuous
    (hmesh : OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H1)
    (hw : type_of% @Erdos1133.erdos_1133.variants.weaker) :
    OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H2 := by
  intro A hA
  let K := 3 * (A + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨ε, hε, hweak⟩ := hw K hK
  refine ⟨ε,hε,?_⟩
  filter_upwards [hweak, hmesh K hK, Filter.eventually_ge_atTop 1] with n hweak hnear hpos
  let m := ⌊(1 + ε) * (n : ℝ)⌋₊
  let g := fun k : ℕ => 2 * (k : ℝ) / (n : ℝ)^3 - 1
  have hgridmem (j : ℕ) (hj : j ≤ n^3) : g j ∈ Icc (-1 : ℝ) 1 := by
    have hjreal : (j : ℝ) ≤ (n : ℝ)^3 := by exact_mod_cast hj
    have hden : (0 : ℝ) < (n : ℝ)^3 := by positivity
    constructor
    · dsimp [g]; linarith [div_nonneg (by positivity : 0 ≤ 2 * (j : ℝ)) hden.le]
    · dsimp [g]
      have : 2 * (j : ℝ) / (n : ℝ)^3 ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
      linarith
  dsimp only
  intro a ha
  let x : Fin m → Icc (-1 : ℝ) 1 := fun i => ⟨g (a i), hgridmem _ (ha i)⟩
  obtain ⟨P,hd,hnodes,z,hz,hpz⟩ := hweak x
  obtain ⟨s,hs,hmax⟩ : ∃ s : ℝ, s ∈ Icc (-1 : ℝ) 1 ∧
      IsMaxOn (fun t => |P.eval t|) (Icc (-1 : ℝ) 1) s :=
    isCompact_Icc.exists_isMaxOn ⟨0, by constructor <;> norm_num⟩
      (continuous_abs.comp P.continuous).continuousOn
  let M := |P.eval s|
  have hKM : K < M := hpz.trans_le (hmax hz)
  have hM : 0 < M := hK.trans hKM
  let t := K/M
  have ht : 0 < t := div_pos hK hM
  have ht1 : t ≤ 1 := (div_le_one hM).mpr hKM.le
  let R := Polynomial.C t * P
  have hRdeg : R.natDegree ≤ n := (natDegree_C_mul_le _ _).trans hd.le
  have he (u : ℝ) : |R.eval u| = t * |P.eval u| := by simp [R, abs_mul, abs_of_nonneg ht.le]
  have hRgrid (j : ℕ) (hj : j ≤ n^3) : |R.eval (g j)| ≤ K := by
    rw [he]
    calc
      _ ≤ t * M := mul_le_mul_of_nonneg_left (hmax (hgridmem j hj)) ht.le
      _ = K := div_mul_cancel₀ _ hM.ne'
  have hRs : |R.eval s| = K := by rw [he]; exact div_mul_cancel₀ _ hM.ne'
  refine ⟨R,hRdeg,?_,?_,?_⟩
  · intro i
    rw [he]
    exact (mul_le_of_le_one_right ht.le (hnodes i)).trans ht1
  · intro j hj
    exact (hRgrid j hj).trans (by dsimp [K]; linarith)
  · obtain ⟨j,hj,hg⟩ := hnear s hs
    refine ⟨j,hj,?_⟩
    have hdif := hg R hRdeg hRgrid
    have hab : |R.eval s| ≤ |R.eval s - R.eval (g j)| + |R.eval (g j)| := by
      simpa only [sub_add_cancel] using abs_add_le (R.eval s - R.eval (g j)) (R.eval (g j))
    change |R.eval s - R.eval (g j)| ≤ 1 at hdif
    change 2*A < |R.eval (g j)|
    dsimp [K] at hRs
    linarith
end OMA.MeshPeak1133

namespace OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1

open Filter Polynomial Real Set
open Polynomial.Chebyshev

def H1 : Prop :=
  ∀ K > (0 : ℝ), ∃ η > (0 : ℝ), ∃ D : ℕ, ∀ d ≥ D,
    ∀ Y : Finset ℝ, (Y.card : ℝ) ≤ (1+η)*d →
      ∃ A B : Polynomial ℝ, A.natDegree ≤ d ∧ B.natDegree < d ∧
        let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
        (∀ s ∈ Y, |q s| ≤ 1 ∧ |q (-s)| ≤ 1) ∧
          ∃ t ∈ Icc (0 : ℝ) π, K < |q t| ∧ ∀ s, |q s| ≤ |q t|

def H2 : Prop :=
  ∀ (d : ℕ) (A B : Polynomial ℝ), A.natDegree ≤ d → B.natDegree < d →
    let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
    ∀ M : ℝ, (∀ s, |q s| ≤ M) →
      ∀ s u : ℝ, |q s - q u| ≤ d*M*|s-u|

lemma interior_multiplier {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (hta : t ≤ π - a) :
    ∃ r : ℕ, 0 < r ∧ r ≤ 1 + ⌈(π/6) / a⌉₊ ∧
      1/2 ≤ |sin ((r : ℝ) * t)| := by
  let u := min t (π-t)
  have hmin : a ≤ u := le_min hat (by linarith)
  have hu : 0 < u := ha.trans_le hmin
  have hu' : u ≤ π/2 := by dsimp [u]; rcases le_total t (π-t) with h | h <;> simp [h] <;> linarith
  have he (j : ℕ) : |sin ((j : ℝ) * u)| = |sin ((j : ℝ) * t)| := by
    dsimp [u]
    rcases le_total t (π-t) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, mul_sub, sin_nat_mul_pi_sub, abs_neg, abs_mul, abs_pow]
      simp
  by_cases h : π/6 ≤ u
  · refine ⟨1, by decide, by omega, ?_⟩
    rw [← he]
    calc (1 / 2 : ℝ) = sin (π/6) := sin_pi_div_six.symm
      _ ≤ sin u := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hu' h
      _ ≤ _ := by simpa using (le_abs_self (sin u))
  · let r := ⌈(π/6)/u⌉₊
    have hd : 0 < (π/6)/u := by positivity
    have hr : 0 < r := Nat.ceil_pos.mpr hd
    have hlow : π/6 ≤ (r:ℝ)*u := (div_le_iff₀ hu).mp (Nat.le_ceil _)
    have hh : (r:ℝ) < (π/6)/u + 1 := Nat.ceil_lt_add_one hd.le
    have hupp : (r:ℝ)*u ≤ π/2 := by
      have hh' := mul_lt_mul_of_pos_right hh hu
      rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul] at hh'
      linarith [pi_pos]
    have hr' : r ≤ ⌈(π/6) / a⌉₊ := Nat.ceil_le_ceil (div_le_div_of_nonneg_left
      (by positivity) ha hmin)
    refine ⟨r, hr, by omega, ?_⟩
    rw [← he]
    calc (1 / 2 : ℝ) = sin (π/6) := sin_pi_div_six.symm
      _ ≤ sin ((r:ℝ)*u) := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hupp hlow
      _ ≤ _ := le_abs_self _

lemma transfer_peak {m d n : ℕ} {x : Fin m → Icc (-1 : ℝ) 1} {C a t : ℝ}
    (hC : 0 < C) (ha : 0 < a) (hat : a ≤ t) (hta : t ≤ π-a)
    (hdeg : d + (1 + ⌈(π/6)/a⌉₊) ≤ n)
    (A B : Polynomial ℝ) (hA : A.natDegree ≤ d) (hB : B.natDegree < d)
    (hplus : ∀ i, |A.eval (x i : ℝ) + sin (arccos (x i)) * B.eval (x i : ℝ)| ≤ 1)
    (hminus : ∀ i, |A.eval (x i : ℝ) - sin (arccos (x i)) * B.eval (x i : ℝ)| ≤ 1)
    (hpeak : 4*C < |A.eval (cos t) + sin t * B.eval (cos t)|) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧ (∀ i, |P.eval (x i : ℝ)| ≤ 1) ∧
      ∃ z ∈ Icc (-1 : ℝ) 1, C < |P.eval z| := by
  have hsample (i : Fin m) : |A.eval (x i : ℝ)| ≤ 1 ∧ |sin (arccos (x i)) * B.eval (x i : ℝ)| ≤ 1 := by
    have hp := abs_le.mp (hplus i)
    have hm := abs_le.mp (hminus i)
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  by_cases hv : C < |A.eval (cos t)|
  · exact ⟨A, by omega, fun i => (hsample i).1, cos t, ⟨neg_one_le_cos _,cos_le_one _⟩, hv⟩
  have hb : 2*C < |sin t * B.eval (cos t)| := by
    linarith [abs_add_le (A.eval (cos t)) (sin t * B.eval (cos t))]
  obtain ⟨r, hr, hr', hs⟩ := interior_multiplier ha hat hta
  cases r with
  | zero => omega
  | succ k =>
    let P : Polynomial ℝ := (1 - X^2) * U ℝ (k:ℤ) * B
    have ev (s : ℝ) : P.eval (cos s) =
        sin (((k:ℝ)+1)*s) * (sin s * B.eval (cos s)) := by
      simp only [P, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
      have hh := U_real_cos s (k : ℤ)
      push_cast at hh
      rw [← hh]
      nlinarith only [congrArg (fun v : ℝ => v * (U ℝ (k:ℤ)).eval (cos s) * B.eval (cos s)) (sin_sq_add_cos_sq s)]
    have d₀ : (1 - (X:Polynomial ℝ)^2).natDegree ≤ 2 := by
      apply (natDegree_sub_le ..).trans
      simp
    have d₁ := natDegree_mul_le (p := 1 - (X:Polynomial ℝ)^2) (q := U ℝ (k:ℤ))
    rw [natDegree_U_natCast] at d₁
    have d₂ := natDegree_mul_le (p := (1 - (X:Polynomial ℝ)^2) * U ℝ (k:ℤ)) (q := B)
    refine ⟨P, by dsimp [P]; omega, ?_, cos t, ⟨neg_one_le_cos _,cos_le_one _⟩, ?_⟩
    · intro i
      have e := ev (arccos (x i))
      rw [cos_arccos (x i).2.1 (x i).2.2] at e
      rw [e, abs_mul]
      exact mul_le_one₀ (abs_sin_le_one _) (abs_nonneg _) (hsample i).2
    · rw [ev, abs_mul]
      push_cast at hs
      have les := mul_le_mul_of_nonneg_right hs (abs_nonneg (sin t * B.eval (cos t)))
      linarith

lemma guard_mesh {a s L : ℝ} (hL : 0 < L) (hs : 0 ≤ s) (hsa : s ≤ a) :
    ∃ j : ℕ, j ≤ ⌈L*a⌉₊ ∧ |s - (j:ℝ)/L| ≤ 1/L := by
  let j := ⌊L*s⌋₊
  have hj : (j : ℝ) ≤ L*s := Nat.floor_le (mul_nonneg hL.le hs)
  have hj' : L*s < (j:ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · exact_mod_cast (hj.trans ((mul_le_mul_of_nonneg_left hsa hL.le).trans (Nat.le_ceil _)))
  · rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hL).mpr (by linarith)))]
    apply (le_div_iff₀ hL).mpr
    rw [sub_mul, div_mul_cancel₀ _ hL.ne']
    linarith

lemma guard_peak {n : ℕ} {a t M : ℝ} (hn : 0 < n)
    (ht : t ∈ Icc 0 π) (hM : 2 < M) (q : ℝ → ℝ)
    (hq : |q t| = M)
    (hLip : ∀ x y : ℝ, |q x - q y| ≤ (n:ℝ)*M*|x-y|)
    (hG : ∀ j : ℕ, j ≤ ⌈8*(n:ℝ)*a⌉₊ →
        |q ((j:ℝ)/(8*n))| ≤ 1 ∧ |q (π-(j:ℝ)/(8*n))| ≤ 1) :
    a ≤ t ∧ t ≤ π-a := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hL : (0:ℝ) < 8*n := by positivity
  have far (y : ℝ) (hy : |q y| ≤ 1) : 1/(8*(n:ℝ)) < |t-y| := by
    by_contra! h
    have hb : (n:ℝ)*M*|t-y| ≤ (n:ℝ)*M*(1/(8*(n:ℝ))) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg hn'.le (by linarith))
    have he : (n:ℝ)*M*(1/(8*(n:ℝ))) = M/8 := by field_simp
    rw [he] at hb
    have ht' : |q t| ≤ |q t-q y|+|q y| := by simpa using abs_add_le (q t-q y) (q y)
    have hxy := hLip t y
    linarith
  constructor
  · by_contra! ht'
    obtain ⟨j,hj,h⟩ := guard_mesh hL ht.1 ht'.le
    exact (far _ (hG j hj).1).not_ge h
  · by_contra! ht'
    have hsa : π-t ≤ a := by linarith
    obtain ⟨j,hj,h⟩ := guard_mesh hL (sub_nonneg.mpr ht.2) hsa
    have f := far _ (hG j hj).2
    rw [show t-(π-(j:ℝ)/(8*n)) = -(π-t-(j:ℝ)/(8*n)) by ring, abs_neg] at f
    exact f.not_ge h

lemma exact_degree_of_peaking {n m : ℕ} {C : ℝ} (hC : 0 < C)
    (x : Fin m → Icc (-1 : ℝ) 1) (P : Polynomial ℝ) (hd : P.natDegree ≤ n)
    (hnodes : ∀ i, |P.eval (x i : ℝ)| ≤ 1) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hpeak : C < |P.eval z|) :
    ∃ Q : Polynomial ℝ, Q.natDegree = n ∧ (∀ i, |Q.eval (x i : ℝ)| ≤ 1) ∧
      C < |Q.eval z| := by
  rcases hd.eq_or_lt with heq | hlt
  · exact ⟨P, heq, hnodes, hpeak⟩
  let A := |P.eval z|
  have hA : 0 < A := hC.trans hpeak
  have hdpos : 0 < 2 * (A + 1) := by positivity
  let t := (A - C) / (2 * (A + 1))
  have ht : 0 < t := div_pos (sub_pos.mpr hpeak) hdpos
  have ht1 : t < 1 := by
    apply (div_lt_iff₀ hdpos).mpr
    linarith
  have hgap : t * (2 * (A + 1)) = A - C := div_mul_cancel₀ _ hdpos.ne'
  let Q := Polynomial.C (1-t) * P + Polynomial.C t * (X : Polynomial ℝ)^n
  have hmon : (Polynomial.C t * (X : Polynomial ℝ)^n).natDegree = n :=
    natDegree_C_mul_X_pow n t ht.ne'
  have hQ : Q.natDegree = n := by
    apply (natDegree_add_eq_right_of_natDegree_lt _).trans hmon
    rw [hmon]
    exact (natDegree_C_mul_le _ _).trans_lt hlt
  have heval (v : ℝ) : Q.eval v = (1-t) * P.eval v + t * v^n := by simp [Q]
  have hpow {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |v^n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hv)
  have hbound {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : |t * v^n| ≤ t := by
    rw [abs_mul, abs_of_pos ht]
    exact mul_le_of_le_one_right ht.le (hpow hv)
  refine ⟨Q,hQ,?_,?_⟩
  · intro i
    rw [heval]
    calc
      _ ≤ |(1-t) * P.eval (x i : ℝ)| + |t * (x i : ℝ)^n| := abs_add_le _ _
      _ ≤ (1-t) + t := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)]
        exact add_le_add (mul_le_of_le_one_right (sub_nonneg.mpr ht1.le) (hnodes i)) (hbound (x i).property)
      _ = 1 := by ring
  · have he : |(1-t) * P.eval z| ≤ |Q.eval z| + |t * z^n| := by
      simpa only [heval, add_sub_cancel_right] using
        (abs_sub ((1-t) * P.eval z + t * z^n) (t * z^n))
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1.le)] at he
    change (1-t) * A ≤ |Q.eval z| + |t * z^n| at he
    nlinarith [hbound hz]


lemma continuous_peak : H1 → H2 → type_of% @Erdos1133.erdos_1133.variants.weaker := by
  classical
  intro sample bern C hC
  obtain ⟨η, hη, D, hsamp⟩ := sample (4*C+2) (by positivity)
  let a := η/128
  have ha : 0 < a := by dsimp [a]; positivity
  let R := 1+⌈(π/6)/a⌉₊
  let N := ⌈(4+(1+η)*(R:ℝ))/(η/2)⌉₊
  refine ⟨η/4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (D+R+N+1)] with n hn
  let m := ⌊(1+η/4)*(n:ℝ)⌋₊
  change ∀ x : Fin m → Icc (-1 : ℝ) 1, _
  intro x
  let d := n-R
  have hdN : D ≤ d := by dsimp [d]; omega
  have hdR : d+R = n := by dsimp [d]; omega
  have hdR' : (d:ℝ)+(R:ℝ)=(n:ℝ) := by exact_mod_cast hdR
  have hn' : 0 < n := by omega
  let J := ⌈8*(n:ℝ)*a⌉₊
  let I := Finset.range (J+1)
  let L := fun j : ℕ => (j:ℝ)/(8*(n:ℝ))
  let Y := ((Finset.univ : Finset (Fin m)).image fun i => arccos (x i)) ∪
      (I.image L ∪ I.image (fun j => π-L j))
  have cardY : Y.card ≤ m + 2*(J+1) := by
    have h₀ := Finset.card_image_le (f := fun i : Fin m => arccos (x i)) (s := Finset.univ)
    have h₁ := Finset.card_image_le (f := L) (s := I)
    have h₂ := Finset.card_image_le (f := fun j => π-L j) (s := I)
    have h₃ := Finset.card_union_le (I.image L) (I.image (fun j => π-L j))
    have h₄ := Finset.card_union_le ((Finset.univ : Finset (Fin m)).image fun i => arccos (x i))
      (I.image L ∪ I.image (fun j => π-L j))
    have hI : I.card = J+1 := Finset.card_range _
    simp only [Finset.card_univ, Fintype.card_fin] at h₀
    dsimp only [Y]
    omega
  have hY : (Y.card : ℝ) ≤ (1+η)*d := by
    have hJ : (J:ℝ) < 8*(n:ℝ)*a+1 := Nat.ceil_lt_add_one (by positivity)
    have hm : (m:ℝ) ≤ (1+η/4)*(n:ℝ) := Nat.floor_le (by positivity)
    have hN : (4+(1+η)*(R:ℝ))/(η/2) ≤ (n:ℝ) := by
      apply (Nat.le_ceil _).trans
      exact_mod_cast (show N ≤ n by omega)
    have hnR := (div_le_iff₀ (show 0 < η/2 by positivity)).mp hN
    have hc : (Y.card:ℝ) ≤ (m:ℝ)+2*((J:ℝ)+1) := by exact_mod_cast cardY
    dsimp only [a] at hJ
    rw [← hdR'] at hnR hJ hm
    nlinarith [mul_nonneg hη.le (Nat.cast_nonneg d),
      mul_nonneg hη.le (Nat.cast_nonneg R)]
  obtain ⟨A,B,hA,hB,hS,t,ht,hM,hglobal⟩ := hsamp d hdN Y hY
  let q := fun s : ℝ => A.eval (cos s) + sin s * B.eval (cos s)
  have hLip := bern d A B hA hB |q t| hglobal
  have hM' : 2 < |q t| := by change 4*C+2 < |q t| at hM; linarith
  have hinterior := guard_peak (a := a) hn' ht hM' q rfl (fun s u => (hLip s u).trans (by
    have hd : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show d ≤ n by omega)
    gcongr)) (fun j hj => by
      have hI : j ∈ I := Finset.mem_range.mpr (by omega)
      exact ⟨(hS _ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem L hI)))).1,
        (hS _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hI)))).1⟩)
  have hinput (i : Fin m) : arccos (x i) ∈ Y := Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hsplus (i : Fin m) := (hS _ (hinput i)).1
  have hsminus (i : Fin m) := (hS _ (hinput i)).2
  obtain ⟨P,hP,hPx,z,hz,hPz⟩ := transfer_peak (x := x) hC ha hinterior.1 hinterior.2
    (le_of_eq hdR) A B hA hB (fun i => by
      simpa [Real.cos_arccos (x i).2.1 (x i).2.2] using hsplus i) (fun i => by
      simpa [Real.cos_neg,Real.sin_neg,Real.cos_arccos (x i).2.1 (x i).2.2,sub_eq_add_neg] using hsminus i)
    (by change 4*C+2 < |q t| at hM; change 4*C < |q t|; linarith)
  obtain ⟨Q,hQ,hQx,hQz⟩ := exact_degree_of_peaking hC x P hP hPx hz hPz
  exact ⟨Q,hQ,hQx,z,hz,hQz⟩


theorem main : H1 → H2 → OMA.R_Erdos1133_erdos_1133_variants_weaker_R1.H2 := by
  intro hc hb
  exact OMA.MeshPeak1133.grid_obstruction_of_continuous
    (OMA.Mesh1133.mesh_estimate OMA.Mesh1133.interval_derivative_bound) (continuous_peak hc hb)

end OMA.R_Erdos1133_erdos_1133_variants_weaker_R1_H2_R1
