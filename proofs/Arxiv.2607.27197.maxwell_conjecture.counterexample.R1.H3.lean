import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1

/-!
# Three edge equilibria in the Maxwell counterexample

On the negative x-axis the gradient has just one possibly nonzero component.
For every axial separation parameter between 0 and 1/100 this component changes
sign on the interval from -1/3 to -1/4. Throughout the interval the Hessian is
diagonal with entries of signs -, +, -. Two symmetries of the five charges
carry the resulting equilibrium to distinct points at the same radius.

The distance derivative uses the squared-norm calculation from the project's
proof for the two-charge case.
-/

namespace OMA.Edge
open Arxiv.«2607.27197» InnerProductSpace Filter
open scoped RealInnerProductSpace Gradient Topology

abbrev E := EuclideanSpace ℝ (Fin 3)

lemma dist_derivative (a x : E) (h : x ≠ a) :
    HasFDerivAt (fun y => dist y a) ((dist x a)⁻¹ • innerSL ℝ (x-a)) x := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hs : HasFDerivAt (fun y : E => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y
    simp [dist_eq_norm, Real.sqrt_sq (norm_nonneg _)]
  · simp only [dist_eq_norm, Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    <;> norm_num

noncomputable def dCharge (q : ℝ) (a x : E) : E →L[ℝ] ℝ :=
  (-q / dist x a ^ 3) • innerSL ℝ (x-a)

lemma charge_derivative (q : ℝ) (a x : E) (h : x ≠ a) :
    HasFDerivAt (fun y => q / dist y a) (dCharge q a x) x := by
  have hn : dist x a ≠ 0 := dist_ne_zero.mpr h
  have hd := dist_derivative a x h
  convert! ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q using 1
  dsimp [dCharge]
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

lemma coef_derivative (q : ℝ) (a x : E) (h : x ≠ a) :
    HasFDerivAt (fun y => -q / dist y a ^ 3)
      ((3*q / dist x a ^ 5) • innerSL ℝ (x-a)) x := by
  have hn : dist x a ≠ 0 := dist_ne_zero.mpr h
  have hd := dist_derivative a x h
  have hc := (hasDerivAt_const (dist x a) (-q)).div ((hasDerivAt_id (dist x a)).pow 3) (pow_ne_zero 3 hn)
  convert! hc.comp_hasFDerivAt x hd using 1
  dsimp
  rw [smul_smul]
  congr 1
  field_simp
  <;> ring

lemma potential_derivative {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (x : E)
    (hx : ∀ j, x ≠ a j) :
    fderiv ℝ (potential q a) x = ∑ j, dCharge (q j) (a j) x := by
  exact (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => charge_derivative (q j) (a j) x (hx j))).fderiv

noncomputable def ddCharge (q : ℝ) (a x v w : E) : ℝ :=
  (3*q / dist x a ^ 5) * ⟪x-a,v⟫_ℝ * ⟪x-a,w⟫_ℝ - (q / dist x a ^ 3) * ⟪v,w⟫_ℝ

lemma potential_hessian {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (x v w : E)
    (hx : ∀ j, x ≠ a j) :
    iteratedFDeriv ℝ 2 (potential q a) x ![v,w] = ∑ j, ddCharge (q j) (a j) x v w := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ j, y ≠ a j :=
    eventually_all.mpr fun j => isOpen_compl_singleton.mem_nhds (hx j)
  have heq : fderiv ℝ (potential q a) =ᶠ[𝓝 x] (fun y => ∑ j, dCharge (q j) (a j) y) :=
    hnear.mono fun y hy => potential_derivative q a y hy
  have hi (j : Fin n) := ((innerSL ℝ (E := E)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (a j)))
  have hd (j : Fin n) := (coef_derivative (q j) (a j) x (hx j)).smul (hi j)
  rw [iteratedFDeriv_two_apply, heq.fderiv_eq]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)).fderiv
  change fderiv ℝ (fun y => ∑ j, dCharge (q j) (a j) y) x = _ at hsum
  rw [hsum]
  simp [ddCharge, smul_eq_mul, innerSL_apply_apply, inner_sub_left, -Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change -q j / _ * ⟪v,w⟫_ℝ + _ * (⟪x,w⟫_ℝ - ⟪a j,w⟫_ℝ) = _
  ring

/-! ### Radial force and uniform bounds on the three diagonal entries -/

noncomputable def weight (e : ℝ) := 3 / 4 * e ^ 3 - 5 / 32 * e ^ 5
noncomputable def baseDist (t : ℝ) := Real.sqrt ((t + 1/2)^2 + 3/4)
noncomputable def poleDist (e t : ℝ) := Real.sqrt (t^2 + e^2)
noncomputable def force (e t : ℝ) :=
  1 / (1-t)^2 - 2 * (t+1/2) / (baseDist t)^3 - 2 * weight e * t / (poleDist e t)^3

lemma weight_bounds {e : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ)) :
    0 < weight e ∧ weight e < 1/1000000 := by
  have h := he.1
  have h' := he.2
  have he2 : e ^ 2 < (1/100 : ℝ)^2 := by gcongr
  have he3 : e ^ 3 < (1/100 : ℝ)^3 := by gcongr
  dsimp [weight]
  constructor
  · have hh : 0 < 3/4 - 5/32 * e^2 := by linarith
    nlinarith only [mul_pos (pow_pos h 3) hh]
  · nlinarith only [he3, pow_pos h 5]

lemma base_bounds {t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) :
    7/8 < baseDist t ∧ baseDist t < 91/100 := by
  have hl : (1/6 : ℝ) ≤ t+1/2 := by linarith [ht.1]
  have hu : t+1/2 ≤ 1/4 := by linarith [ht.2]
  have hl2 : (1/6 : ℝ)^2 ≤ (t+1/2)^2 := by gcongr
  have hu2 : (t+1/2)^2 ≤ (1/4 : ℝ)^2 := by gcongr
  have h := Real.sq_sqrt (show 0 ≤ (t+1/2)^2+3/4 by positivity)
  dsimp [baseDist]
  constructor <;> nlinarith only [h, hl2, hu2, Real.sqrt_nonneg ((t+1/2)^2+3/4),
    sq_nonneg (Real.sqrt ((t+1/2)^2+3/4) - 7/8),
    sq_nonneg (Real.sqrt ((t+1/2)^2+3/4) - 91/100)]

lemma pole_lower {t e : ℝ} (ht : t ≤ -1/4) : 1/4 ≤ poleDist e t := by
  apply Real.le_sqrt_of_sq_le
  have h : (1/4 : ℝ)^2 ≤ (-t)^2 := by gcongr; linarith
  nlinarith only [h, sq_nonneg e]

lemma force_root {e : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ)) :
    ∃ t ∈ Set.Icc (-1/3 : ℝ) (-1/4), force e t = 0 := by
  have hw := weight_bounds he
  have hd (t : ℝ) (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) : 0 < baseDist t :=
    lt_trans (by norm_num) (base_bounds ht).1
  have hp (t : ℝ) (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) : 0 < poleDist e t :=
    lt_of_lt_of_le (by norm_num) (pole_lower ht.2)
  have hc : ContinuousOn (force e) (Set.Icc (-1/3 : ℝ) (-1/4)) := by
    intro t ht
    have ha : 1-t ≠ 0 := by linarith [ht.2]
    have hb := (hd t ht).ne'
    have hz := (hp t ht).ne'
    apply ContinuousAt.continuousWithinAt
    unfold force baseDist poleDist at *
    fun_prop (disch := first | positivity | assumption | apply pow_ne_zero; assumption | unfold baseDist poleDist at *; positivity)
  have hI : (-1/3 : ℝ) ≤ -1/4 := by norm_num
  have hL := (base_bounds (Set.left_mem_Icc.mpr hI)).1
  have hR := (base_bounds (Set.right_mem_Icc.mpr hI)).2
  have hbL : (7/8 : ℝ)^3 < (baseDist (-1/3))^3 := by gcongr
  have hbR : (baseDist (-1/4))^3 < (91/100 : ℝ)^3 := by gcongr; exact (hd _ (Set.right_mem_Icc.mpr hI)).le
  have hcR : (1/4 : ℝ)^3 ≤ (poleDist e (-1/4))^3 := by gcongr; exact pole_lower le_rfl
  apply intermediate_value_Icc' hI hc
  constructor
  · have h1 : (66/100 : ℝ) < (1/2) / (baseDist (-1/4))^3 := by
      apply (lt_div_iff₀ (pow_pos (hd _ (Set.right_mem_Icc.mpr hI)) 3)).2
      linarith
    have h2 : weight e / 2 / (poleDist e (-1/4))^3 < 1/100 := by
      apply (div_lt_iff₀ (pow_pos (hp _ (Set.right_mem_Icc.mpr hI)) 3)).2
      linarith [hw.2]
    unfold force
    norm_num at h1 h2 ⊢
    ring_nf at h1 h2 ⊢
    linarith
  · have h1 : (1/3 : ℝ) / (baseDist (-1/3))^3 < 9/16 := by
      apply (div_lt_iff₀ (pow_pos (hd _ (Set.left_mem_Icc.mpr hI)) 3)).2
      linarith
    have h2 : 0 ≤ weight e / (poleDist e (-1/3))^3 := div_nonneg hw.1.le (pow_pos (hp _ (Set.left_mem_Icc.mpr hI)) 3).le
    unfold force
    norm_num at h1 h2 ⊢
    ring_nf at h1 h2 ⊢
    linarith
noncomputable def diagX (e t : ℝ) :=
  2 / (1-t)^3 + (4*(t+1/2)^2-3/2) / (baseDist t)^5 +
    (4*t^2-2*e^2)*weight e / (poleDist e t)^5

noncomputable def diagY (e t : ℝ) :=
  -1 / (1-t)^3 + (3-2*(t+1/2)^2) / (baseDist t)^5 - 2*weight e / (poleDist e t)^3

noncomputable def diagZ (e t : ℝ) :=
  -1 / (1-t)^3 - 2 / (baseDist t)^3 + (4*e^2-2*t^2)*weight e / (poleDist e t)^5

lemma diagonal_signs {e t : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ))
    (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) :
    diagX e t < 0 ∧ 0 < diagY e t ∧ diagZ e t < 0 := by
  obtain ⟨hw, hw'⟩ := weight_bounds he
  obtain ⟨hb, hb'⟩ := base_bounds ht
  have hz := pole_lower (e := e) ht.2
  have A : (5/4 : ℝ) ≤ 1-t := by linarith [ht.2]
  have A3 : (5/4 : ℝ)^3 ≤ (1-t)^3 := by gcongr
  have ha3 : 0 < (1-t)^3 := by linarith
  have B : 0 < baseDist t := by linarith
  have B5 : baseDist t ^5 < 1 := by simpa using (pow_lt_pow_left₀ (by linarith : baseDist t < 1) B.le (by decide : 5 ≠ 0))
  have Z : 0 < poleDist e t := by linarith
  have Z3 : (1/4 : ℝ)^3 ≤ (poleDist e t)^3 := by gcongr
  have Z5 : (1/4 : ℝ)^5 ≤ (poleDist e t)^5 := by gcongr
  have t2 : t^2 ≤ (1/3 : ℝ)^2 := by
    have : (-t)^2 ≤ (1/3 : ℝ)^2 := by gcongr <;> linarith [ht.1, ht.2]
    simpa using this
  have t2' : (1/4 : ℝ)^2 ≤ t^2 := by
    have : (1/4 : ℝ)^2 ≤ (-t)^2 := by gcongr <;> linarith [ht.2]
    simpa using this
  have u : 0 ≤ t+1/2 := by linarith [ht.1]
  have u2 : (t+1/2)^2 ≤ (1/4 : ℝ)^2 := by gcongr <;> linarith [ht.2]
  have e2 : e^2 ≤ (1/100 : ℝ)^2 := by gcongr <;> first | exact he.1.le | exact he.2.le
  have hA : 2 / (1-t)^3 < 6/5 := (div_lt_iff₀ ha3).2 (by linarith)
  have hXb : (4*(t+1/2)^2-3/2) / (baseDist t)^5 < -5/4 :=
    (div_lt_iff₀ (pow_pos B _)).2 (by linarith)
  have hXc : (4*t^2-2*e^2)*weight e / (poleDist e t)^5 < 1/100 :=
    (div_lt_iff₀ (pow_pos Z _)).2 (by
      have : (4*t^2-2*e^2)*weight e ≤ 1*weight e :=
        mul_le_mul_of_nonneg_right (by nlinarith only [t2, sq_nonneg e]) hw.le
      linarith)
  have hYa : -1 / (1-t)^3 > -1 := (lt_div_iff₀ ha3).2 (by linarith)
  have hYb : 2 < (3-2*(t+1/2)^2) / (baseDist t)^5 :=
    (lt_div_iff₀ (pow_pos B _)).2 (by linarith)
  have hYc : 2*weight e / (poleDist e t)^3 < 1/100 :=
    (div_lt_iff₀ (pow_pos Z _)).2 (by linarith)
  have hZc : (4*e^2-2*t^2)*weight e / (poleDist e t)^5 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hw) (pow_pos Z _)
  exact ⟨by unfold diagX; linarith, by unfold diagY; linarith, by
    unfold diagZ
    have h1 : -1 / (1-t)^3 < 0 := div_neg_of_neg_of_pos (by norm_num) ha3
    have h2 : 0 < 2 / baseDist t ^ 3 := by positivity
    linarith only [h1, h2, hZc]⟩

/-! ### Evaluation of both derivatives on the negative x-axis -/

noncomputable def axis (t : ℝ) : E := !₂[t,0,0]

lemma distances {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (j : Fin 5) :
    dist (axis t) (counterexamplePositions e j) =
    ![1-t, baseDist t, baseDist t, poleDist e t, poleDist e t] j := by
  have h : t - 1 < 0 := by linarith [ht.2]
  fin_cases j <;> norm_num [axis, counterexamplePositions, EuclideanSpace.dist_eq, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Real.dist_eq, baseDist, poleDist, div_pow, Real.sq_sqrt, abs_of_neg h] <;>
    first | congr 1 <;> ring | linarith
  rw [show 1 - t * 2 + t ^ 2 = (1-t)^2 by ring, Real.sqrt_sq (by linarith)]

lemma axis_away {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (j : Fin 5) :
    axis t ≠ counterexamplePositions e j := by
  apply dist_pos.mp
  rw [distances ht]
  have ha : 0 < 1-t := by linarith [ht.2]
  have hb : 0 < baseDist t := lt_trans (by norm_num) (base_bounds ht).1
  have hc : 0 < poleDist e t := lt_of_lt_of_le (by norm_num) (pole_lower ht.2)
  fin_cases j <;> assumption

lemma scalar_gradient {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (v : E) :
    fderiv ℝ (potential (counterexampleCharges e) (counterexamplePositions e)) (axis t) v =
      force e t * v.ofLp 0 := by
  rw [potential_derivative _ _ _ (axis_away ht)]
  simp only [_root_.sum_apply, dCharge, _root_.smul_apply, smul_eq_mul, innerSL_apply_apply,
    distances ht]
  have ha : 1-t ≠ 0 := by linarith [ht.2]
  have h : 1 / (1-t)^2 = (1-t)/(1-t)^3 := by field_simp
  unfold force
  rw [h]
  simp [axis, counterexampleCharges, counterexamplePositions, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.head_cons, Matrix.tail_cons, dotProduct, Fin.sum_univ_succ, weight]
  <;> ring

lemma div_cube (c d : ℝ) (hd : d ≠ 0) : c/d^3 = (c*d^2)/d^5 := by
  field_simp

lemma scalar_hessian {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (v w : E) :
    iteratedFDeriv ℝ 2 (potential (counterexampleCharges e) (counterexamplePositions e))
      (axis t) ![v,w] =
        diagX e t * v.ofLp 0 * w.ofLp 0 + diagY e t * v.ofLp 1 * w.ofLp 1 +
        diagZ e t * v.ofLp 2 * w.ofLp 2 := by
  rw [potential_hessian _ _ _ _ _ (axis_away ht)]
  simp only [ddCharge, distances ht]
  have ha : 1-t ≠ 0 := by linarith [ht.2]
  have hb : baseDist t ≠ 0 := ne_of_gt (lt_trans (by norm_num) (base_bounds ht).1)
  have hc : poleDist e t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (pole_lower ht.2))
  have hb2 : baseDist t ^ 2 = (t+1/2)^2 + 3/4 := Real.sq_sqrt (by positivity)
  have hc2 : poleDist e t ^ 2 = t^2 + e^2 := Real.sq_sqrt (by positivity)
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    Fin.succ_zero_eq_one, add_zero]
  simp [axis, counterexampleCharges, counterexamplePositions, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    dotProduct, Fin.sum_univ_three, diagX, diagY, diagZ, weight, div_cube _ _ ha, div_cube _ _ hb,
    div_cube _ _ hc, hb2, hc2, -one_div]
  ring_nf
  norm_num [Real.sq_sqrt]
  <;> ring

/-! ### The triangle symmetries preserve nondegenerate equilibria -/

lemma grad_zero_iff {V : EuclideanSpace ℝ (Fin 3) → ℝ} {x} :
    ∇ V x = 0 ↔ fderiv ℝ V x = 0 := by
  rw [← toDual_gradient]
  exact (toDual ℝ _).map_eq_zero_iff.symm

lemma map_equilibrium {n : ℕ} {q : Fin n → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin 3)}
    (g : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Equiv.Perm (Fin n)) (ha : ∀ j, a (σ j) = g (a j)) (hq : ∀ j, q (σ j) = q j)
    {x} (hx : x ∈ nondegenerateEquilibria q a) : g x ∈ nondegenerateEquilibria q a := by
  let V := potential q a
  have hV : V ∘ g.toContinuousLinearEquiv = V := by
    funext y
    change (∑ j, q j / dist (g y) (a j)) = _
    rw [← Equiv.sum_comp σ (fun j => q j / dist (g y) (a j))]
    simp only [ha, hq, g.dist_map]
    rfl
  refine ⟨⟨?_, grad_zero_iff.mpr ?_⟩, ?_⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, rfl⟩ := σ.surjective j
    exact hx.1.1 ⟨k, g.injective ((ha k).symm.trans hj)⟩
  · have hd := g.toContinuousLinearEquiv.comp_right_fderiv (f := V) (x := x)
    rw [hV, show fderiv ℝ V x = 0 from grad_zero_iff.mp hx.1.2] at hd
    ext v
    obtain ⟨w, rfl⟩ := g.surjective v
    exact (congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L w) hd).symm
  · intro v hv
    obtain ⟨u, rfl⟩ := g.surjective v
    obtain ⟨w, hw⟩ := hx.2 u (fun h => hv (by simp [h]))
    refine ⟨g w, ?_⟩
    have hd := g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right V
      uniqueDiffOn_univ (Set.mem_univ (g x)) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ, hV] at hd
    rw [hd] at hw
    change iteratedFDeriv ℝ 2 V (g x) (fun i => g (![u,w] i)) ≠ 0 at hw
    have hvec : (fun i => g (![u,w] i)) = ![g u, g w] := by
      funext i
      fin_cases i <;> rfl
    exact hvec ▸ hw

noncomputable def edgeMirror (e : ℝ) (k : Fin 5) :=
  (Submodule.span ℝ {counterexamplePositions e k}).reflection

def edgeSwaps (k : Fin 5) := (Equiv.swap (0 : Fin 5) k).trans (Equiv.swap 3 4)

lemma edgeMirror_charges (e : ℝ) (k : Fin 5) (hk : k = 1 ∨ k = 2) (j : Fin 5) :
    counterexampleCharges e (edgeSwaps k j) = counterexampleCharges e j := by
  rcases hk with rfl | rfl <;> fin_cases j <;> rfl

lemma edgeMirror_positions (e : ℝ) {k l : Fin 5}
    (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) (j : Fin 5) :
    counterexamplePositions e (edgeSwaps k j) = edgeMirror e l (counterexamplePositions e j) := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have swap1 (i : Fin 5) : edgeSwaps 1 i = ![1,0,2,4,3] i := by fin_cases i <;> rfl
  have swap2 (i : Fin 5) : edgeSwaps 2 i = ![2,1,0,4,3] i := by fin_cases i <;> rfl
  rw [edgeMirror, Submodule.reflection_singleton_apply]
  rcases hkl with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> fin_cases j <;>
    ext i <;> fin_cases i <;>
    norm_num [swap1, swap2, counterexamplePositions, EuclideanSpace.real_norm_sq_eq,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, div_pow, h3] <;>
    ring_nf <;> norm_num [pow_succ, ← mul_assoc, h3] <;> nlinarith only [congrArg (fun x : ℝ => x * Real.sqrt 3) h3]

/-! ### Three distinct equilibria outside the open ball of radius 1/4 -/

lemma axis_equilibrium {e t : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ))
    (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (hf : force e t = 0) :
    axis t ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) := by
  refine ⟨⟨?_, grad_zero_iff.mpr ?_⟩, ?_⟩
  · rintro ⟨j,h⟩
    exact axis_away ht j h.symm
  · ext v
    rw [scalar_gradient ht, hf]
    simp
  · obtain ⟨hx, hy, hz⟩ := diagonal_signs he ht
    intro v hv
    by_contra! h
    apply hv
    have hh (w : E) := (scalar_hessian (e := e) ht v w).symm.trans (h w)
    have h0 : v.ofLp 0 = 0 := by
      simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hx.ne, hy.ne', hz.ne] using hh (!₂[1,0,0])
    have h1 : v.ofLp 1 = 0 := by
      simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hx.ne, hy.ne', hz.ne] using hh (!₂[0,1,0])
    have h2 : v.ofLp 2 = 0 := by
      simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hx.ne, hy.ne', hz.ne] using hh (!₂[0,0,1])
    ext i
    fin_cases i <;> assumption

lemma axis_eq_vertex (e t : ℝ) : axis t = t • counterexamplePositions e 0 := by
  ext i
  fin_cases i <;> simp [axis, counterexamplePositions]

lemma three_points {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4))
    (hx : axis t ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e)) :
    3 ≤ ((nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e)) \
      Metric.ball 0 (1/4 : ℝ)).encard := by
  let p (i : Fin 5) := t • counterexamplePositions e i
  let S := nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) \
    Metric.ball 0 (1/4 : ℝ)
  have p0 : axis t = p 0 := axis_eq_vertex e t
  have far : axis t ∉ Metric.ball 0 (1/4 : ℝ) := by
    simp [Metric.mem_ball, dist_zero_right, axis, EuclideanSpace.norm_eq, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
    <;> linarith [ht.2]
  have m0 : p 0 ∈ S := p0 ▸ And.intro hx far
  have mir {k l : Fin 5} (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) :
      p k ∈ S := by
    let g := edgeMirror e l
    have hk : k = 1 ∨ k = 2 := hkl.imp And.left And.left
    have hpos := edgeMirror_positions e hkl
    have h0 : edgeSwaps k 0 = k := by rcases hk with rfl | rfl <;> rfl
    have hmap : g (axis t) = p k := by
      rw [p0]
      dsimp [p]
      rw [map_smul, ← hpos, h0]
    rw [← hmap]
    exact ⟨map_equilibrium g (edgeSwaps k) hpos (edgeMirror_charges e k hk) hx, by
      simpa only [Metric.mem_ball, dist_zero_right, g.norm_map] using far⟩
  have m1 : p 1 ∈ S := mir (Or.inl ⟨rfl,rfl⟩ : (1 = (1:Fin 5) ∧ 2 = (2:Fin 5)) ∨ _)
  have m2 : p 2 ∈ S := mir (Or.inr ⟨rfl,rfl⟩ : _ ∨ (2 = (2:Fin 5) ∧ 1 = (1:Fin 5)))
  obtain ⟨d01,d12,d02⟩ := counterexamplePositions_dist_vertices e
  have split {i j : Fin 5} (h : dist (counterexamplePositions e i) (counterexamplePositions e j) = Real.sqrt 3) : p i ≠ p j :=
    (smul_right_injective E (by linarith [ht.2] : t ≠ 0)).ne (dist_pos.mp (h.symm ▸ Real.sqrt_pos.2 (by norm_num)))
  have hcard : ({p 0, p 1, p 2} : Set E).encard = 3 :=
    Set.encard_eq_three.mpr ⟨_, _, _, split d01, split d02, split d12, rfl⟩
  rw [← hcard]
  apply Set.encard_mono
  exact Set.insert_subset m0 (Set.insert_subset m1 (Set.singleton_subset_iff.mpr m2))

end OMA.Edge

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1.H3 := by
  refine ⟨1/4, by norm_num, 1/100, by norm_num, ?_⟩
  intro e he
  obtain ⟨t, ht, hf⟩ := OMA.Edge.force_root he
  exact OMA.Edge.three_points ht (OMA.Edge.axis_equilibrium he ht hf)
