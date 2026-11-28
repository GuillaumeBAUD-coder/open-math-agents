import OMAStatements.S_arxiv_2405_03472

/-!
# Disproof of Conjecture 1 of Katona, Wang, Wibisono (arXiv 2405.03472) as stated

Credit: @tatashbar

The statement asks for a bounded function Phi such that the truncated modified Hamiltonian of
symplectic Euler is conserved up to k Phi(N) L^(N+3) eta^(N+2) along every orbit that stays in the
domain. It fails for d = 1, P = Q = (-inf, 0], F = G = exp of the coordinate, L = 1, eta = 23/25.

Plan of the proof.
* In the variables x = eta e^p, y = eta e^q the method is the map T (x, y) = (x e^-y, y e^(x e^-y)).
* Every correction H_n with n >= 1 is a combination of monomials e^(A p + B q) with A, B >= 1, with an
  explicit bound on the coefficients, so the truncation differs from F + G by at most MM N e^(p + q).
* Along the two-sided orbit through (17/20, 1/10) the quantity y_K - x_(-K) - y_(-K) stays above 10^-8
  for all K >= 28. This is certified by 49 interval steps with rational end points.
* Summing the conjectured bound over 2K steps and choosing K as a quadratic polynomial in N gives a
  contradiction for large N.
-/


namespace AMD

open Real OMA.S_arxiv_2405_03472

/-- `R^1` as a Euclidean space. -/
abbrev E1 : Type := E 1

/-- The coordinate functional. -/
noncomputable def co : E1 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1)

/-- The unit vector. -/
noncomputable def e1 : E1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

/-- The half-line `(-∞, 0]`. -/
def Hs : Set E1 := {x | x 0 ≤ 0}

/-- `exp` of the coordinate. -/
noncomputable def fexp : E1 → ℝ := fun x => exp (x 0)

theorem co_apply (x : E1) : co x = x 0 := rfl

theorem e1_apply : e1 0 = 1 := by simp [e1]

theorem inner_e1 : inner ℝ e1 e1 = 1 := by simp [e1]

theorem inner_e1_left (v : E1) : inner ℝ e1 v = v 0 := by
  rw [e1, EuclideanSpace.inner_single_left]
  simp

theorem Hs_closed : IsClosed Hs :=
  isClosed_le co.continuous (continuous_const (y := (0 : ℝ)))

theorem Hs_convex : Convex ℝ Hs := by
  have h : IsLinearMap ℝ (fun x : E1 => x 0) := co.toLinearMap.isLinear
  exact convex_halfSpace_le h 0

theorem Hs_interior : (interior Hs).Nonempty := by
  have ho : IsOpen {x : E1 | x 0 < 0} := isOpen_lt co.continuous (continuous_const (y := (0 : ℝ)))
  have hsub : {x : E1 | x 0 < 0} ⊆ Hs := fun x (hx : x 0 < 0) => show x 0 ≤ 0 from le_of_lt hx
  refine ⟨-e1, interior_maximal hsub ho ?_⟩
  show (-e1 : E1) 0 < 0
  simp [e1]

theorem Hs_uniqueDiff : UniqueDiffOn ℝ Hs := uniqueDiffOn_convex Hs_convex Hs_interior

theorem fexp_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n fexp :=
  Real.contDiff_exp.comp co.contDiff

theorem norm_co_le : ‖co‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact PiLp.norm_apply_le x 0

theorem norm_iteratedFDeriv_fexp (k : ℕ) (x : E1) : ‖iteratedFDeriv ℝ k fexp x‖ ≤ exp (x 0) := by
  have h1 : iteratedFDeriv ℝ k (Real.exp ∘ co) x =
      (iteratedFDeriv ℝ k Real.exp (co x)).compContinuousLinearMap fun _ => co :=
    co.iteratedFDeriv_comp_right (Real.contDiff_exp (n := ⊤)) x le_top
  have h2 : ‖iteratedFDeriv ℝ k Real.exp (co x)‖ = exp (x 0) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (exp_pos _), co_apply]
  have h3 : ∏ _i : Fin k, ‖co‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_co_le)
  calc ‖iteratedFDeriv ℝ k fexp x‖
      = ‖(iteratedFDeriv ℝ k Real.exp (co x)).compContinuousLinearMap fun _ => co‖ := by
        have h0 : fexp = Real.exp ∘ co := rfl
        rw [h0, h1]
    _ ≤ ‖iteratedFDeriv ℝ k Real.exp (co x)‖ * ∏ _i : Fin k, ‖co‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k Real.exp (co x)‖ * 1 :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = exp (x 0) := by rw [mul_one, h2]

/-- `exp` of the coordinate is `1`-smooth of every order on the half-line. -/
theorem fexp_smooth (m : ℕ) : LSmoothUpTo fexp Hs 1 m := by
  refine ⟨fexp_contDiff.contDiffOn, fun k _ _ x hx => ?_⟩
  rw [iteratedFDerivWithin_eq_iteratedFDeriv Hs_uniqueDiff fexp_contDiff.contDiffAt hx]
  exact (norm_iteratedFDeriv_fexp k x).trans (Real.exp_le_one_iff.mpr hx)

/-- The gradient within the half-line of a function that depends on the coordinate only. -/
theorem gradW {f : E1 → ℝ} {g : ℝ → ℝ} {g' : ℝ} {x : E1} (hx : x ∈ Hs)
    (hg : HasDerivAt g g' (x 0)) (hfg : ∀ y ∈ Hs, f y = g (y 0)) :
    gradientWithin f Hs x = g' • e1 := by
  have h1 : HasFDerivAt (g ∘ co) (g' • (co : E1 →L[ℝ] ℝ)) x :=
    HasDerivAt.comp_hasFDerivAt x hg co.hasFDerivAt
  have h2 : HasFDerivWithinAt f (g' • (co : E1 →L[ℝ] ℝ)) Hs x :=
    h1.hasFDerivWithinAt.congr (fun y hy => hfg y hy) (hfg x hx)
  have h3 : (InnerProductSpace.toDual ℝ E1) (g' • e1) = g' • (co : E1 →L[ℝ] ℝ) := by
    ext v
    simp [co, inner_e1_left]
  have hfd : fderivWithin ℝ f Hs x = g' • (co : E1 →L[ℝ] ℝ) :=
    h2.fderivWithin (Hs_uniqueDiff x hx)
  rw [gradientWithin, hfd, ← h3, LinearIsometryEquiv.symm_apply_apply]

theorem hasDerivAt_mono (c a β t0 : ℝ) :
    HasDerivAt (fun t => c * exp (a * t + β)) (c * a * exp (a * t0 + β)) t0 := by
  have h := (((hasDerivAt_id' t0).const_mul a).add_const β).exp.const_mul c
  refine h.congr_deriv ?_
  ring

/-- The monomial `c e^{a p + b q}`. -/
noncomputable def mono (c a b : ℝ) : E1 × E1 → ℝ := fun z => c * exp (a * z.1 0 + b * z.2 0)

/-- The Poisson bracket of two monomials on the quadrant `Hs × Hs`. -/
theorem pb_mono {c a b c' a' b' : ℝ} {φ ψ : E1 × E1 → ℝ} {z : E1 × E1}
    (hz1 : z.1 ∈ Hs) (hz2 : z.2 ∈ Hs)
    (hφ : ∀ w : E1 × E1, w.1 ∈ Hs → w.2 ∈ Hs → φ w = mono c a b w)
    (hψ : ∀ w : E1 × E1, w.1 ∈ Hs → w.2 ∈ Hs → ψ w = mono c' a' b' w) :
    pb Hs Hs φ ψ z = mono (c * c' * (b * a' - a * b')) (a + a') (b + b') z := by
  have g1 : gradientWithin (fun p => φ (p, z.2)) Hs z.1
      = (c * a * exp (a * z.1 0 + b * z.2 0)) • e1 :=
    gradW hz1 (hasDerivAt_mono c a (b * z.2 0) (z.1 0)) fun y hy => hφ (y, z.2) hy hz2
  have g2 : gradientWithin (fun q => ψ (z.1, q)) Hs z.2
      = (c' * b' * exp (b' * z.2 0 + a' * z.1 0)) • e1 :=
    gradW hz2 (hasDerivAt_mono c' b' (a' * z.1 0) (z.2 0)) fun y hy => by
      rw [hψ (z.1, y) hz1 hy]
      show c' * exp (a' * z.1 0 + b' * y 0) = c' * exp (b' * y 0 + a' * z.1 0)
      rw [add_comm]
  have g3 : gradientWithin (fun q => φ (z.1, q)) Hs z.2
      = (c * b * exp (b * z.2 0 + a * z.1 0)) • e1 :=
    gradW hz2 (hasDerivAt_mono c b (a * z.1 0) (z.2 0)) fun y hy => by
      rw [hφ (z.1, y) hz1 hy]
      show c * exp (a * z.1 0 + b * y 0) = c * exp (b * y 0 + a * z.1 0)
      rw [add_comm]
  have g4 : gradientWithin (fun p => ψ (p, z.2)) Hs z.1
      = (c' * a' * exp (a' * z.1 0 + b' * z.2 0)) • e1 :=
    gradW hz1 (hasDerivAt_mono c' a' (b' * z.2 0) (z.1 0)) fun y hy => hψ (y, z.2) hy hz2
  unfold pb
  rw [g1, g2, g3, g4]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_e1, mono, mul_one]
  have hE : exp ((a + a') * z.1 0 + (b + b') * z.2 0)
      = exp (a * z.1 0 + b * z.2 0) * exp (a' * z.1 0 + b' * z.2 0) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hE, add_comm (b' * z.2 0) (a' * z.1 0), add_comm (b * z.2 0) (a * z.1 0)]
  ring

/-- The gradient of `fexp` within the half-line. -/
theorem grad_fexp {x : E1} (hx : x ∈ Hs) : gradientWithin fexp Hs x = exp (x 0) • e1 :=
  gradW hx (Real.hasDerivAt_exp (x 0)) fun _ _ => rfl

/-- One step of symplectic Euler for `F = G = fexp` on the half-line, in coordinates. -/
theorem step_coords {η : ℝ} (hη : 0 ≤ η) {p q : E1} (hp : p ∈ Hs) (hq : q ∈ Hs) :
    (step Hs Hs fexp fexp η (p, q)).1 0 = p 0 - η * exp (q 0) ∧
    (step Hs Hs fexp fexp η (p, q)).2 0 = q 0 + η * exp (p 0 - η * exp (q 0)) := by
  have hp0 : (p - η • (exp (q 0) • e1)) 0 = p 0 - η * exp (q 0) := by
    simp [e1]
  have hp' : p - η • (exp (q 0) • e1) ∈ Hs := by
    show (p - η • (exp (q 0) • e1)) 0 ≤ 0
    rw [hp0]
    have h1 : 0 ≤ η * exp (q 0) := mul_nonneg hη (exp_pos _).le
    have h2 : p 0 ≤ 0 := hp
    linarith
  have hs : step Hs Hs fexp fexp η (p, q)
      = (p - η • (exp (q 0) • e1),
         q + η • (exp ((p - η • (exp (q 0) • e1)) 0) • e1)) := by
    show (p - η • gradientWithin fexp Hs q,
        q + η • gradientWithin fexp Hs (p - η • gradientWithin fexp Hs q)) = _
    rw [grad_fexp hq, grad_fexp hp']
  rw [hs]
  refine ⟨hp0, ?_⟩
  show (q + η • (exp ((p - η • (exp (q 0) • e1)) 0) • e1)) 0 = _
  rw [hp0]
  simp [e1]

/-- One step of symplectic Euler for `F = exp`, `G = exp` in the variables `x = η e^p`, `y = η e^q`. -/
noncomputable def T (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * exp (-z.2), z.2 * exp (z.1 * exp (-z.2)))

/-- The inverse of `T`. -/
noncomputable def Tinv (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * exp (z.2 * exp (-z.1)), z.2 * exp (-z.1))

/-- Taylor polynomial of `exp` (a lower bound on `[0, ∞)`). -/
noncomputable def EL (t : ℝ) : ℝ := ∑ i ∈ Finset.range 14, t ^ i / (i.factorial : ℝ)

/-- Taylor polynomial plus remainder (an upper bound on `[0, 1]`). -/
noncomputable def EU (t : ℝ) : ℝ :=
  EL t + t ^ 14 * (((14 : ℕ) : ℝ) + 1) / (((Nat.factorial 14 : ℕ) : ℝ) * ((14 : ℕ) : ℝ))

theorem EL_le {t : ℝ} (ht : 0 ≤ t) : EL t ≤ exp t := Real.sum_le_exp_of_nonneg ht 14

theorem le_EU {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : exp t ≤ EU t := by
  unfold EU EL
  exact Real.exp_bound' h0 h1 (by norm_num)

/-- `z` lies in the box `[a, b] × [c, d]`. -/
def Box (z : ℝ × ℝ) (a b c d : ℝ) : Prop := a ≤ z.1 ∧ z.1 ≤ b ∧ c ≤ z.2 ∧ z.2 ≤ d

theorem stepF {z : ℝ × ℝ} {a b c d a' b' c' d' : ℝ} (h : Box z a b c d)
    (ha' : 0 ≤ a') (hb0 : 0 ≤ b') (hc : 0 ≤ c) (hd1 : d ≤ 1) (hb1 : b' ≤ 1)
    (h1 : a' * EU d ≤ a) (h2 : b ≤ b' * EL c) (h3 : c' ≤ c * EL a') (h4 : d * EU b' ≤ d') :
    Box (T z) a' b' c' d' := by
  obtain ⟨hxa, hxb, hyc, hyd⟩ := h
  have hy0 : 0 ≤ z.2 := hc.trans hyc
  have hd0 : 0 ≤ d := hy0.trans hyd
  have e1 : exp z.2 ≤ EU d := (exp_le_exp.mpr hyd).trans (le_EU hd0 hd1)
  have e2 : EL c ≤ exp z.2 := (EL_le hc).trans (exp_le_exp.mpr hyc)
  have hcancel : ∀ r : ℝ, r * exp z.2 * exp (-z.2) = r := by
    intro r
    rw [mul_assoc, ← exp_add]
    simp
  have hlo : a' ≤ z.1 * exp (-z.2) := by
    have h5 : a' * exp z.2 ≤ z.1 := (mul_le_mul_of_nonneg_left e1 ha').trans (h1.trans hxa)
    calc a' = a' * exp z.2 * exp (-z.2) := (hcancel a').symm
      _ ≤ z.1 * exp (-z.2) := mul_le_mul_of_nonneg_right h5 (exp_pos _).le
  have hhi : z.1 * exp (-z.2) ≤ b' := by
    have h5 : z.1 ≤ b' * exp z.2 := hxb.trans (h2.trans (mul_le_mul_of_nonneg_left e2 hb0))
    calc z.1 * exp (-z.2) ≤ b' * exp z.2 * exp (-z.2) :=
          mul_le_mul_of_nonneg_right h5 (exp_pos _).le
      _ = b' := hcancel b'
  refine ⟨hlo, hhi, ?_, ?_⟩
  · show c' ≤ z.2 * exp (z.1 * exp (-z.2))
    have e3 : EL a' ≤ exp (z.1 * exp (-z.2)) := (EL_le ha').trans (exp_le_exp.mpr hlo)
    calc c' ≤ c * EL a' := h3
      _ ≤ c * exp (z.1 * exp (-z.2)) := mul_le_mul_of_nonneg_left e3 hc
      _ ≤ z.2 * exp (z.1 * exp (-z.2)) := mul_le_mul_of_nonneg_right hyc (exp_pos _).le
  · show z.2 * exp (z.1 * exp (-z.2)) ≤ d'
    have e4 : exp (z.1 * exp (-z.2)) ≤ EU b' := (exp_le_exp.mpr hhi).trans (le_EU hb0 hb1)
    calc z.2 * exp (z.1 * exp (-z.2)) ≤ d * exp (z.1 * exp (-z.2)) :=
          mul_le_mul_of_nonneg_right hyd (exp_pos _).le
      _ ≤ d * EU b' := mul_le_mul_of_nonneg_left e4 hd0
      _ ≤ d' := h4

theorem stepB {z : ℝ × ℝ} {a b c d a' b' c' d' : ℝ} (h : Box z a b c d)
    (hc' : 0 ≤ c') (hd0 : 0 ≤ d') (ha : 0 ≤ a) (hb1 : b ≤ 1) (hd1 : d' ≤ 1)
    (h1 : c' * EU b ≤ c) (h2 : d ≤ d' * EL a) (h3 : a' ≤ a * EL c') (h4 : b * EU d' ≤ b') :
    Box (Tinv z) a' b' c' d' := by
  obtain ⟨hxa, hxb, hyc, hyd⟩ := h
  have hx0 : 0 ≤ z.1 := ha.trans hxa
  have hb0 : 0 ≤ b := hx0.trans hxb
  have e1 : exp z.1 ≤ EU b := (exp_le_exp.mpr hxb).trans (le_EU hb0 hb1)
  have e2 : EL a ≤ exp z.1 := (EL_le ha).trans (exp_le_exp.mpr hxa)
  have hcancel : ∀ r : ℝ, r * exp z.1 * exp (-z.1) = r := by
    intro r
    rw [mul_assoc, ← exp_add]
    simp
  have hlo : c' ≤ z.2 * exp (-z.1) := by
    have h5 : c' * exp z.1 ≤ z.2 := (mul_le_mul_of_nonneg_left e1 hc').trans (h1.trans hyc)
    calc c' = c' * exp z.1 * exp (-z.1) := (hcancel c').symm
      _ ≤ z.2 * exp (-z.1) := mul_le_mul_of_nonneg_right h5 (exp_pos _).le
  have hhi : z.2 * exp (-z.1) ≤ d' := by
    have h5 : z.2 ≤ d' * exp z.1 := hyd.trans (h2.trans (mul_le_mul_of_nonneg_left e2 hd0))
    calc z.2 * exp (-z.1) ≤ d' * exp z.1 * exp (-z.1) :=
          mul_le_mul_of_nonneg_right h5 (exp_pos _).le
      _ = d' := hcancel d'
  refine ⟨?_, ?_, hlo, hhi⟩
  · show a' ≤ z.1 * exp (z.2 * exp (-z.1))
    have e3 : EL c' ≤ exp (z.2 * exp (-z.1)) := (EL_le hc').trans (exp_le_exp.mpr hlo)
    calc a' ≤ a * EL c' := h3
      _ ≤ a * exp (z.2 * exp (-z.1)) := mul_le_mul_of_nonneg_left e3 ha
      _ ≤ z.1 * exp (z.2 * exp (-z.1)) := mul_le_mul_of_nonneg_right hxa (exp_pos _).le
  · show z.1 * exp (z.2 * exp (-z.1)) ≤ b'
    have e4 : exp (z.2 * exp (-z.1)) ≤ EU d' := (exp_le_exp.mpr hhi).trans (le_EU hd0 hd1)
    calc z.1 * exp (z.2 * exp (-z.1)) ≤ b * exp (z.2 * exp (-z.1)) :=
          mul_le_mul_of_nonneg_right hxb (exp_pos _).le
      _ ≤ b * EU d' := mul_le_mul_of_nonneg_left e4 hb0
      _ ≤ b' := h4

/-- The base point of the certified orbit. -/
noncomputable def z0 : ℝ × ℝ := (17 / 20, 1 / 10)

theorem fw0 : Box (T^[0] z0) (17 / 20) (17 / 20) (1 / 10) (1 / 10) :=
  ⟨le_refl _, le_refl _, le_refl _, le_refl _⟩

theorem bw0 : Box (Tinv^[0] z0) (17 / 20) (17 / 20) (1 / 10) (1 / 10) :=
  ⟨le_refl _, le_refl _, le_refl _, le_refl _⟩


theorem fw1 : Box (T^[0 + 1] z0) (769111805330 / 1000000000000 : ℝ) (769111805331 / 1000000000000 : ℝ) (215784881256 / 1000000000000 : ℝ) (215784881257 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw2 : Box (T^[1 + 1] z0) (619833856181 / 1000000000000 : ℝ) (619833856183 / 1000000000000 : ℝ) (401061927277 / 1000000000000 : ℝ) (401061927280 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw3 : Box (T^[2 + 1] z0) (415046076154 / 1000000000000 : ℝ) (415046076158 / 1000000000000 : ℝ) (607384433167 / 1000000000000 : ℝ) (607384433175 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw4 : Box (T^[3 + 1] z0) (226106269497 / 1000000000000 : ℝ) (226106269502 / 1000000000000 : ℝ) (761483263030 / 1000000000000 : ℝ) (761483263045 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw5 : Box (T^[4 + 1] z0) (105585583780 / 1000000000000 : ℝ) (105585583785 / 1000000000000 : ℝ) (846282964362 / 1000000000000 : ℝ) (846282964384 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw6 : Box (T^[5 + 1] z0) (45296912812 / 1000000000000 : ℝ) (45296912816 / 1000000000000 : ℝ) (885498434891 / 1000000000000 : ℝ) (885498434918 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw7 : Box (T^[6 + 1] z0) (18685362164 / 1000000000000 : ℝ) (18685362168 / 1000000000000 : ℝ) (902199843851 / 1000000000000 : ℝ) (902199843883 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw8 : Box (T^[7 + 1] z0) (7580207708 / 1000000000000 : ℝ) (7580207711 / 1000000000000 : ℝ) (909064691676 / 1000000000000 : ℝ) (909064691712 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw9 : Box (T^[8 + 1] z0) (3054072389 / 1000000000000 : ℝ) (3054072391 / 1000000000000 : ℝ) (911845284955 / 1000000000000 : ℝ) (911845284994 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw10 : Box (T^[9 + 1] z0) (1227071731 / 1000000000000 : ℝ) (1227071732 / 1000000000000 : ℝ) (912964871293 / 1000000000000 : ℝ) (912964871334 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw11 : Box (T^[10 + 1] z0) (492463837 / 1000000000000 : ℝ) (492463839 / 1000000000000 : ℝ) (913414584201 / 1000000000000 : ℝ) (913414584244 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw12 : Box (T^[11 + 1] z0) (197552909 / 1000000000000 : ℝ) (197552911 / 1000000000000 : ℝ) (913595049734 / 1000000000000 : ℝ) (913595049780 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw13 : Box (T^[12 + 1] z0) (79234466 / 1000000000000 : ℝ) (79234468 / 1000000000000 : ℝ) (913667440817 / 1000000000000 : ℝ) (913667440866 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw14 : Box (T^[13 + 1] z0) (31777037 / 1000000000000 : ℝ) (31777039 / 1000000000000 : ℝ) (913696474922 / 1000000000000 : ℝ) (913696474974 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw15 : Box (T^[14 + 1] z0) (12743832 / 1000000000000 : ℝ) (12743834 / 1000000000000 : ℝ) (913708118990 / 1000000000000 : ℝ) (913708119045 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw16 : Box (T^[15 + 1] z0) (5110714 / 1000000000000 : ℝ) (5110716 / 1000000000000 : ℝ) (913712788702 / 1000000000000 : ℝ) (913712788760 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw17 : Box (T^[16 + 1] z0) (2049562 / 1000000000000 : ℝ) (2049564 / 1000000000000 : ℝ) (913714661414 / 1000000000000 : ℝ) (913714661475 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw18 : Box (T^[17 + 1] z0) (821939 / 1000000000000 : ℝ) (821941 / 1000000000000 : ℝ) (913715412432 / 1000000000000 : ℝ) (913715412495 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw19 : Box (T^[18 + 1] z0) (329623 / 1000000000000 : ℝ) (329625 / 1000000000000 : ℝ) (913715713613 / 1000000000000 : ℝ) (913715713679 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw20 : Box (T^[19 + 1] z0) (132189 / 1000000000000 : ℝ) (132190 / 1000000000000 : ℝ) (913715834396 / 1000000000000 : ℝ) (913715834464 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw21 : Box (T^[20 + 1] z0) (53011 / 1000000000000 : ℝ) (53013 / 1000000000000 : ℝ) (913715882832 / 1000000000000 : ℝ) (913715882903 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw22 : Box (T^[21 + 1] z0) (21259 / 1000000000000 : ℝ) (21260 / 1000000000000 : ℝ) (913715902256 / 1000000000000 : ℝ) (913715902329 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw23 : Box (T^[22 + 1] z0) (8525 / 1000000000000 : ℝ) (8526 / 1000000000000 : ℝ) (913715910045 / 1000000000000 : ℝ) (913715910120 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw24 : Box (T^[23 + 1] z0) (3418 / 1000000000000 : ℝ) (3420 / 1000000000000 : ℝ) (913715913168 / 1000000000000 : ℝ) (913715913245 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw25 : Box (T^[24 + 1] z0) (1370 / 1000000000000 : ℝ) (1372 / 1000000000000 : ℝ) (913715914419 / 1000000000000 : ℝ) (913715914499 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw26 : Box (T^[25 + 1] z0) (549 / 1000000000000 : ℝ) (551 / 1000000000000 : ℝ) (913715914920 / 1000000000000 : ℝ) (913715915003 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw27 : Box (T^[26 + 1] z0) (220 / 1000000000000 : ℝ) (221 / 1000000000000 : ℝ) (913715915121 / 1000000000000 : ℝ) (913715915205 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem fw28 : Box (T^[27 + 1] z0) (88 / 1000000000000 : ℝ) (89 / 1000000000000 : ℝ) (913715915201 / 1000000000000 : ℝ) (913715915287 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepF fw27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw1 : Box (Tinv^[0 + 1] z0) (887117854976 / 1000000000000 : ℝ) (887117854977 / 1000000000000 : ℝ) (42741493194 / 1000000000000 : ℝ) (42741493195 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw2 : Box (Tinv^[1 + 1] z0) (902871773909 / 1000000000000 : ℝ) (902871773913 / 1000000000000 : ℝ) (17602700556 / 1000000000000 : ℝ) (17602700558 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw3 : Box (Tinv^[2 + 1] z0) (909337892653 / 1000000000000 : ℝ) (909337892660 / 1000000000000 : ℝ) (7136200965 / 1000000000000 : ℝ) (7136200967 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw4 : Box (Tinv^[3 + 1] z0) (911955450259 / 1000000000000 : ℝ) (911955450269 / 1000000000000 : ℝ) (2874396284 / 1000000000000 : ℝ) (2874396286 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw5 : Box (Tinv^[4 + 1] z0) (913009142595 / 1000000000000 : ℝ) (913009142608 / 1000000000000 : ℝ) (1154753860 / 1000000000000 : ℝ) (1154753862 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw6 : Box (Tinv^[5 + 1] z0) (913432347166 / 1000000000000 : ℝ) (913432347181 / 1000000000000 : ℝ) (463419804 / 1000000000000 : ℝ) (463419806 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw7 : Box (Tinv^[6 + 1] z0) (913602168682 / 1000000000000 : ℝ) (913602168700 / 1000000000000 : ℝ) (185898532 / 1000000000000 : ℝ) (185898534 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw8 : Box (Tinv^[7 + 1] z0) (913670289034 / 1000000000000 : ℝ) (913670289055 / 1000000000000 : ℝ) (74559601 / 1000000000000 : ℝ) (74559603 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw9 : Box (Tinv^[8 + 1] z0) (913697610097 / 1000000000000 : ℝ) (913697610121 / 1000000000000 : ℝ) (29902094 / 1000000000000 : ℝ) (29902096 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw10 : Box (Tinv^[9 + 1] z0) (913708567126 / 1000000000000 : ℝ) (913708567153 / 1000000000000 : ℝ) (11991893 / 1000000000000 : ℝ) (11991895 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw11 : Box (Tinv^[10 + 1] z0) (913712961306 / 1000000000000 : ℝ) (913712961336 / 1000000000000 : ℝ) (4809159 / 1000000000000 : ℝ) (4809161 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw12 : Box (Tinv^[11 + 1] z0) (913714723520 / 1000000000000 : ℝ) (913714723552 / 1000000000000 : ℝ) (1928628 / 1000000000000 : ℝ) (1928630 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw13 : Box (Tinv^[12 + 1] z0) (913715430224 / 1000000000000 : ℝ) (913715430258 / 1000000000000 : ℝ) (773441 / 1000000000000 : ℝ) (773442 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw14 : Box (Tinv^[13 + 1] z0) (913715713634 / 1000000000000 : ℝ) (913715713670 / 1000000000000 : ℝ) (310174 / 1000000000000 : ℝ) (310175 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw15 : Box (Tinv^[14 + 1] z0) (913715827290 / 1000000000000 : ℝ) (913715827328 / 1000000000000 : ℝ) (124389 / 1000000000000 : ℝ) (124390 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw16 : Box (Tinv^[15 + 1] z0) (913715872868 / 1000000000000 : ℝ) (913715872909 / 1000000000000 : ℝ) (49883 / 1000000000000 : ℝ) (49885 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw17 : Box (Tinv^[16 + 1] z0) (913715891145 / 1000000000000 : ℝ) (913715891189 / 1000000000000 : ℝ) (20004 / 1000000000000 : ℝ) (20006 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw18 : Box (Tinv^[17 + 1] z0) (913715898474 / 1000000000000 : ℝ) (913715898521 / 1000000000000 : ℝ) (8022 / 1000000000000 : ℝ) (8024 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw19 : Box (Tinv^[18 + 1] z0) (913715901413 / 1000000000000 : ℝ) (913715901462 / 1000000000000 : ℝ) (3217 / 1000000000000 : ℝ) (3218 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw20 : Box (Tinv^[19 + 1] z0) (913715902591 / 1000000000000 : ℝ) (913715902642 / 1000000000000 : ℝ) (1290 / 1000000000000 : ℝ) (1291 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

theorem bw21 : Box (Tinv^[20 + 1] z0) (913715903063 / 1000000000000 : ℝ) (913715903116 / 1000000000000 : ℝ) (517 / 1000000000000 : ℝ) (518 / 1000000000000 : ℝ) := by
  rw [Function.iterate_succ_apply']
  exact stepB bw20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]) (by norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial])

/-- The certified inequalities used by the refutation: the gap, the two suprema, and the
thresholds for the monotone bounds. -/
theorem cert :
    (Tinv^[21] z0).1 * exp (Tinv^[21] z0).2 + (Tinv^[21] z0).2 + 1 / 10 ^ 8 ≤ (T^[28] z0).2 ∧
    (T^[28] z0).2 * exp (T^[28] z0).1 ≤ 23 / 25 ∧
    (Tinv^[21] z0).1 * exp (Tinv^[21] z0).2 ≤ 23 / 25 ∧
    4 / 5 ≤ (T^[28] z0).2 ∧ 4 / 5 ≤ (Tinv^[21] z0).1 ∧
    0 < (T^[28] z0).1 ∧ 0 < (Tinv^[21] z0).2 := by
  obtain ⟨f1, f2, f3, f4⟩ := fw28
  obtain ⟨b1, b2, b3, b4⟩ := bw21
  have hf1 : (0 : ℝ) < (T^[28] z0).1 := lt_of_lt_of_le (by norm_num) f1
  have hb3 : (0 : ℝ) < (Tinv^[21] z0).2 := lt_of_lt_of_le (by norm_num) b3
  have hb1 : (0 : ℝ) ≤ (Tinv^[21] z0).1 := le_trans (by norm_num) b1
  have hf3 : (0 : ℝ) ≤ (T^[28] z0).2 := le_trans (by norm_num) f3
  have eb : exp (Tinv^[21] z0).2 ≤ EU (518 / 1000000000000 : ℝ) :=
    (exp_le_exp.mpr b4).trans (le_EU (by norm_num) (by norm_num))
  have ef : exp (T^[28] z0).1 ≤ EU (89 / 1000000000000 : ℝ) :=
    (exp_le_exp.mpr f2).trans (le_EU (by norm_num) (by norm_num))
  have pb : (Tinv^[21] z0).1 * exp (Tinv^[21] z0).2 ≤ (913715903116 / 1000000000000 : ℝ) * EU (518 / 1000000000000 : ℝ) :=
    mul_le_mul b2 eb (exp_pos _).le (by norm_num)
  have pf : (T^[28] z0).2 * exp (T^[28] z0).1 ≤ (913715915287 / 1000000000000 : ℝ) * EU (89 / 1000000000000 : ℝ) :=
    mul_le_mul f4 ef (exp_pos _).le (by norm_num)
  have n1 : (913715903116 / 1000000000000 : ℝ) * EU (518 / 1000000000000 : ℝ) + (518 / 1000000000000 : ℝ) + 1 / 10 ^ 8 ≤ (913715915201 / 1000000000000 : ℝ) := by
    norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]
  have n2 : (913715915287 / 1000000000000 : ℝ) * EU (89 / 1000000000000 : ℝ) ≤ 23 / 25 := by
    norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]
  have n3 : (913715903116 / 1000000000000 : ℝ) * EU (518 / 1000000000000 : ℝ) ≤ 23 / 25 := by
    norm_num [EL, EU, Finset.sum_range_succ, Nat.factorial]
  refine ⟨by linarith, by linarith, by linarith, le_trans (by norm_num) f3, le_trans (by norm_num) b1,
    hf1, hb3⟩

/-! Piece (c): the two-sided orbit through `z0` (appended to the certificate inside `namespace AMD`). -/

theorem T_fst (z : ℝ × ℝ) : (T z).1 = z.1 * exp (-z.2) := rfl

theorem T_snd (z : ℝ × ℝ) : (T z).2 = z.2 * exp (T z).1 := rfl

theorem Tinv_snd (z : ℝ × ℝ) : (Tinv z).2 = z.2 * exp (-z.1) := rfl

theorem Tinv_fst (z : ℝ × ℝ) : (Tinv z).1 = z.1 * exp (Tinv z).2 := rfl

theorem T_Tinv (z : ℝ × ℝ) : T (Tinv z) = z := by
  have h1 : (T (Tinv z)).1 = z.1 := by
    rw [T_fst, Tinv_fst, mul_assoc, ← exp_add]
    simp
  have h2 : (T (Tinv z)).2 = z.2 := by
    rw [T_snd, h1, Tinv_snd, mul_assoc, ← exp_add]
    simp
  exact Prod.ext h1 h2

theorem T_iter_Tinv_iter (K : ℕ) (z : ℝ × ℝ) : T^[K] (Tinv^[K] z) = z :=
  (Function.LeftInverse.iterate T_Tinv K) z

/-- Both coordinates are positive. -/
def Pos (z : ℝ × ℝ) : Prop := 0 < z.1 ∧ 0 < z.2

theorem pos_T {z : ℝ × ℝ} (h : Pos z) : Pos (T z) :=
  ⟨mul_pos h.1 (exp_pos _), mul_pos h.2 (exp_pos _)⟩

theorem pos_Tinv {z : ℝ × ℝ} (h : Pos z) : Pos (Tinv z) :=
  ⟨mul_pos h.1 (exp_pos _), mul_pos h.2 (exp_pos _)⟩

theorem two_le_exp : (2 : ℝ) ≤ exp (4 / 5) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 / 5 by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem exp_neg_le_half {t : ℝ} (ht : 4 / 5 ≤ t) : exp (-t) ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ≤ exp t := two_le_exp.trans (exp_le_exp.mpr ht)
  rw [exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h1

theorem T_fst_le {z : ℝ × ℝ} (hz : Pos z) : (T z).1 ≤ z.1 := by
  rw [T_fst]
  exact mul_le_of_le_one_right hz.1.le (exp_le_one_iff.mpr (by linarith [hz.2]))

theorem T_snd_ge {z : ℝ × ℝ} (hz : Pos z) : z.2 ≤ (T z).2 := by
  rw [T_snd]
  exact le_mul_of_one_le_right hz.2.le (one_le_exp (pos_T hz).1.le)

theorem T_fst_decay {z : ℝ × ℝ} (hz : Pos z) {c : ℝ} (hc : c ≤ z.2) :
    (T z).1 ≤ z.1 * exp (-c) := by
  rw [T_fst]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hz.1.le

/-- Along the forward orbit `y e^x` does not increase once `y ≥ 4/5`. -/
theorem W_T {z : ℝ × ℝ} (hz : Pos z) (h : 4 / 5 ≤ z.2) :
    (T z).2 * exp (T z).1 ≤ z.2 * exp z.1 := by
  have hx : (T z).1 + (T z).1 ≤ z.1 := by
    have h1 : (T z).1 ≤ z.1 * (1 / 2) := by
      rw [T_fst]
      exact mul_le_mul_of_nonneg_left (exp_neg_le_half h) hz.1.le
    linarith
  rw [T_snd, mul_assoc, ← exp_add]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hx) hz.2.le

theorem Tinv_snd_le {z : ℝ × ℝ} (hz : Pos z) : (Tinv z).2 ≤ z.2 := by
  rw [Tinv_snd]
  exact mul_le_of_le_one_right hz.2.le (exp_le_one_iff.mpr (by linarith [hz.1]))

theorem Tinv_fst_ge {z : ℝ × ℝ} (hz : Pos z) : z.1 ≤ (Tinv z).1 := by
  rw [Tinv_fst]
  exact le_mul_of_one_le_right hz.1.le (one_le_exp (pos_Tinv hz).2.le)

theorem Tinv_snd_decay {z : ℝ × ℝ} (hz : Pos z) {c : ℝ} (hc : c ≤ z.1) :
    (Tinv z).2 ≤ z.2 * exp (-c) := by
  rw [Tinv_snd]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hz.2.le

/-- Along the backward orbit `x e^y` does not increase once `x ≥ 4/5`. -/
theorem V_Tinv {z : ℝ × ℝ} (hz : Pos z) (h : 4 / 5 ≤ z.1) :
    (Tinv z).1 * exp (Tinv z).2 ≤ z.1 * exp z.2 := by
  have hy : (Tinv z).2 + (Tinv z).2 ≤ z.2 := by
    have h1 : (Tinv z).2 ≤ z.2 * (1 / 2) := by
      rw [Tinv_snd]
      exact mul_le_mul_of_nonneg_left (exp_neg_le_half h) hz.2.le
    linarith
  rw [Tinv_fst, mul_assoc, ← exp_add]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hy) hz.1.le

/-- The forward orbit of `z0`. -/
noncomputable def Fw (j : ℕ) : ℝ × ℝ := T^[j] z0

/-- The backward orbit of `z0`. -/
noncomputable def Bw (j : ℕ) : ℝ × ℝ := Tinv^[j] z0

theorem Fw_succ (j : ℕ) : Fw (j + 1) = T (Fw j) := Function.iterate_succ_apply' T j z0

theorem Bw_succ (j : ℕ) : Bw (j + 1) = Tinv (Bw j) := Function.iterate_succ_apply' Tinv j z0

theorem Fw_zero_fst : (Fw 0).1 = 17 / 20 := rfl

theorem Fw_zero_snd : (Fw 0).2 = 1 / 10 := rfl

theorem Bw_zero_fst : (Bw 0).1 = 17 / 20 := rfl

theorem Bw_zero_snd : (Bw 0).2 = 1 / 10 := rfl

theorem Fw_pos : ∀ j : ℕ, Pos (Fw j)
  | 0 => ⟨by rw [Fw_zero_fst]; norm_num, by rw [Fw_zero_snd]; norm_num⟩
  | j + 1 => by
    rw [Fw_succ]
    exact pos_T (Fw_pos j)

theorem Bw_pos : ∀ j : ℕ, Pos (Bw j)
  | 0 => ⟨by rw [Bw_zero_fst]; norm_num, by rw [Bw_zero_snd]; norm_num⟩
  | j + 1 => by
    rw [Bw_succ]
    exact pos_Tinv (Bw_pos j)

theorem Fw_snd_mono : Monotone fun j => (Fw j).2 :=
  monotone_nat_of_le_succ fun j => by
    show (Fw j).2 ≤ (Fw (j + 1)).2
    rw [Fw_succ]
    exact T_snd_ge (Fw_pos j)

theorem Fw_fst_anti : Antitone fun j => (Fw j).1 :=
  antitone_nat_of_succ_le fun j => by
    show (Fw (j + 1)).1 ≤ (Fw j).1
    rw [Fw_succ]
    exact T_fst_le (Fw_pos j)

theorem Bw_fst_mono : Monotone fun j => (Bw j).1 :=
  monotone_nat_of_le_succ fun j => by
    show (Bw j).1 ≤ (Bw (j + 1)).1
    rw [Bw_succ]
    exact Tinv_fst_ge (Bw_pos j)

theorem Bw_snd_anti : Antitone fun j => (Bw j).2 :=
  antitone_nat_of_succ_le fun j => by
    show (Bw (j + 1)).2 ≤ (Bw j).2
    rw [Bw_succ]
    exact Tinv_snd_le (Bw_pos j)

theorem Fw_snd_ge (j : ℕ) : 1 / 10 ≤ (Fw j).2 := by
  have h : (Fw 0).2 ≤ (Fw j).2 := Fw_snd_mono (Nat.zero_le j)
  rw [Fw_zero_snd] at h
  exact h

theorem Fw_fst_le (j : ℕ) : (Fw j).1 ≤ 17 / 20 := by
  have h : (Fw j).1 ≤ (Fw 0).1 := Fw_fst_anti (Nat.zero_le j)
  rw [Fw_zero_fst] at h
  exact h

theorem Bw_fst_ge (j : ℕ) : 17 / 20 ≤ (Bw j).1 := by
  have h : (Bw 0).1 ≤ (Bw j).1 := Bw_fst_mono (Nat.zero_le j)
  rw [Bw_zero_fst] at h
  exact h

theorem Bw_snd_le (j : ℕ) : (Bw j).2 ≤ 1 / 10 := by
  have h : (Bw j).2 ≤ (Bw 0).2 := Bw_snd_anti (Nat.zero_le j)
  rw [Bw_zero_snd] at h
  exact h

theorem exp_step (j : ℕ) :
    exp (-(j : ℝ) / 10) * exp (-(1 / 10)) = exp (-((j + 1 : ℕ) : ℝ) / 10) := by
  rw [← exp_add]
  congr 1
  push_cast
  ring

theorem Fw_fst_le_exp : ∀ j : ℕ, (Fw j).1 ≤ exp (-(j : ℝ) / 10)
  | 0 => by
    rw [Fw_zero_fst]
    norm_num
  | j + 1 => by
    have h1 : (T (Fw j)).1 ≤ (Fw j).1 * exp (-(1 / 10)) := T_fst_decay (Fw_pos j) (Fw_snd_ge j)
    rw [← Fw_succ] at h1
    have h2 : (Fw j).1 * exp (-(1 / 10)) ≤ exp (-(j : ℝ) / 10) * exp (-(1 / 10)) :=
      mul_le_mul_of_nonneg_right (Fw_fst_le_exp j) (exp_pos _).le
    rw [exp_step] at h2
    exact h1.trans h2

theorem Bw_snd_le_exp : ∀ j : ℕ, (Bw j).2 ≤ exp (-(j : ℝ) / 10)
  | 0 => by
    rw [Bw_zero_snd]
    norm_num
  | j + 1 => by
    have h0 : (1 / 10 : ℝ) ≤ (Bw j).1 := le_trans (by norm_num) (Bw_fst_ge j)
    have h1 : (Tinv (Bw j)).2 ≤ (Bw j).2 * exp (-(1 / 10)) := Tinv_snd_decay (Bw_pos j) h0
    rw [← Bw_succ] at h1
    have h2 : (Bw j).2 * exp (-(1 / 10)) ≤ exp (-(j : ℝ) / 10) * exp (-(1 / 10)) :=
      mul_le_mul_of_nonneg_right (Bw_snd_le_exp j) (exp_pos _).le
    rw [exp_step] at h2
    exact h1.trans h2

theorem cert_gap : (Bw 21).1 * exp (Bw 21).2 + (Bw 21).2 + 1 / 10 ^ 8 ≤ (Fw 28).2 := cert.1

theorem cert_W : (Fw 28).2 * exp (Fw 28).1 ≤ 23 / 25 := cert.2.1

theorem cert_V : (Bw 21).1 * exp (Bw 21).2 ≤ 23 / 25 := cert.2.2.1

theorem cert_F45 : 4 / 5 ≤ (Fw 28).2 := cert.2.2.2.1

theorem Fw_W (j : ℕ) (hj : 28 ≤ j) : (Fw j).2 * exp (Fw j).1 ≤ (Fw 28).2 * exp (Fw 28).1 := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    refine le_trans ?_ ih
    rw [Fw_succ]
    exact W_T (Fw_pos n) (le_trans cert_F45 (Fw_snd_mono hn))

theorem Bw_V_anti : Antitone fun j => (Bw j).1 * exp (Bw j).2 :=
  antitone_nat_of_succ_le fun j => by
    show (Bw (j + 1)).1 * exp (Bw (j + 1)).2 ≤ (Bw j).1 * exp (Bw j).2
    rw [Bw_succ]
    exact V_Tinv (Bw_pos j) (le_trans (by norm_num) (Bw_fst_ge j))

theorem self_le_mul_exp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ≤ a * exp b :=
  le_mul_of_one_le_right ha (one_le_exp hb)

theorem Fw_snd_le (j : ℕ) : (Fw j).2 ≤ 23 / 25 := by
  rcases le_total j 28 with h | h
  · have h1 : (Fw j).2 ≤ (Fw 28).2 := Fw_snd_mono h
    have h2 := self_le_mul_exp (Fw_pos 28).2.le (Fw_pos 28).1.le
    linarith [cert_W]
  · have h1 := self_le_mul_exp (Fw_pos j).2.le (Fw_pos j).1.le
    linarith [Fw_W j h, cert_W]

theorem Bw_fst_le (j : ℕ) : (Bw j).1 ≤ 23 / 25 := by
  rcases le_total j 21 with h | h
  · have h1 : (Bw j).1 ≤ (Bw 21).1 := Bw_fst_mono h
    have h2 := self_le_mul_exp (Bw_pos 21).1.le (Bw_pos 21).2.le
    linarith [cert_V]
  · have h1 := self_le_mul_exp (Bw_pos j).1.le (Bw_pos j).2.le
    have h2 : (Bw j).1 * exp (Bw j).2 ≤ (Bw 21).1 * exp (Bw 21).2 := Bw_V_anti h
    linarith [cert_V]

/-- The gap between the two ends of the orbit, uniformly in `K ≥ 28`. -/
theorem gap (K : ℕ) (hK : 28 ≤ K) : (Bw K).1 + (Bw K).2 + 1 / 10 ^ 8 ≤ (Fw K).2 := by
  have h1 := self_le_mul_exp (Bw_pos K).1.le (Bw_pos K).2.le
  have h2 : (Bw K).1 * exp (Bw K).2 ≤ (Bw 21).1 * exp (Bw 21).2 := Bw_V_anti (by omega)
  have h3 : (Bw K).2 ≤ (Bw 21).2 := Bw_snd_anti (by omega)
  have h4 : (Fw 28).2 ≤ (Fw K).2 := Fw_snd_mono hK
  linarith [cert_gap]

theorem orb_le (K j : ℕ) (h : j ≤ K) : T^[j] (Bw K) = Bw (K - j) := by
  have e : K = j + (K - j) := by omega
  have hK : Bw K = Tinv^[j] (Bw (K - j)) := by
    show Tinv^[K] z0 = Tinv^[j] (Tinv^[K - j] z0)
    rw [← Function.iterate_add_apply, ← e]
  rw [hK, T_iter_Tinv_iter]

theorem orb_ge (K j : ℕ) (h : K ≤ j) : T^[j] (Bw K) = Fw (j - K) := by
  have e : j = (j - K) + K := by omega
  have h1 : T^[j] (Bw K) = T^[j - K] (T^[K] (Bw K)) := by
    rw [← Function.iterate_add_apply, ← e]
  rw [h1]
  show T^[j - K] (T^[K] (Tinv^[K] z0)) = Fw (j - K)
  rw [T_iter_Tinv_iter]
  rfl

/-- Every point of the two-sided orbit lies in `(0, 23/25]²`. -/
theorem orb_bounds (K j : ℕ) :
    Pos (T^[j] (Bw K)) ∧ (T^[j] (Bw K)).1 ≤ 23 / 25 ∧ (T^[j] (Bw K)).2 ≤ 23 / 25 := by
  rcases le_total j K with h | h
  · rw [orb_le K j h]
    exact ⟨Bw_pos _, Bw_fst_le _, (Bw_snd_le _).trans (by norm_num)⟩
  · rw [orb_ge K j h]
    exact ⟨Fw_pos _, (Fw_fst_le _).trans (by norm_num), Fw_snd_le _⟩

/-! Piece (c), second part: the orbit in the variables of the statement. -/

theorem E1_ext {u v : E1} (h : u 0 = v 0) : u = v := by
  ext i
  fin_cases i
  exact h

/-- The point of `R^1` with coordinate `t`. -/
noncomputable def pt (t : ℝ) : E1 := t • e1

theorem pt_apply (t : ℝ) : pt t 0 = t := by simp [pt, e1]

/-- The point of the phase space with `η e^p = x` and `η e^q = y`. -/
noncomputable def emb (η : ℝ) (z : ℝ × ℝ) : E1 × E1 :=
  (pt (log (z.1 / η)), pt (log (z.2 / η)))

theorem emb_fst (η : ℝ) (z : ℝ × ℝ) : (emb η z).1 0 = log (z.1 / η) := pt_apply _

theorem emb_snd (η : ℝ) (z : ℝ × ℝ) : (emb η z).2 0 = log (z.2 / η) := pt_apply _

theorem emb_mem {η : ℝ} (hη : 0 < η) {z : ℝ × ℝ} (hz : Pos z) (h1 : z.1 ≤ η) (h2 : z.2 ≤ η) :
    (emb η z).1 ∈ Hs ∧ (emb η z).2 ∈ Hs := by
  constructor
  · show (emb η z).1 0 ≤ 0
    rw [emb_fst]
    exact Real.log_nonpos (div_nonneg hz.1.le hη.le) ((div_le_one hη).mpr h1)
  · show (emb η z).2 0 ≤ 0
    rw [emb_snd]
    exact Real.log_nonpos (div_nonneg hz.2.le hη.le) ((div_le_one hη).mpr h2)

theorem exp_emb_fst {η : ℝ} (hη : 0 < η) {z : ℝ × ℝ} (hz : Pos z) :
    exp ((emb η z).1 0) = z.1 / η := by
  rw [emb_fst, Real.exp_log (div_pos hz.1 hη)]

theorem exp_emb_snd {η : ℝ} (hη : 0 < η) {z : ℝ × ℝ} (hz : Pos z) :
    exp ((emb η z).2 0) = z.2 / η := by
  rw [emb_snd, Real.exp_log (div_pos hz.2 hη)]

theorem log_mul_exp {a t η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    log (a * exp t / η) = log (a / η) + t := by
  have h : a * exp t / η = a / η * exp t := by ring
  rw [h, Real.log_mul (div_pos ha hη).ne' (exp_pos t).ne', Real.log_exp]

/-- In the variables `x = η e^p`, `y = η e^q` the symplectic Euler step of the statement is `T`. -/
theorem step_emb {η : ℝ} (hη : 0 < η) {z : ℝ × ℝ} (hz : Pos z) (h1 : z.1 ≤ η) (h2 : z.2 ≤ η) :
    step Hs Hs fexp fexp η (emb η z) = emb η (T z) := by
  obtain ⟨m1, m2⟩ := emb_mem hη hz h1 h2
  obtain ⟨c1, c2⟩ := step_coords hη.le m1 m2
  have hc : η * (z.2 / η) = z.2 := by field_simp
  have k1 : (emb η z).1 0 - η * exp ((emb η z).2 0) = (emb η (T z)).1 0 := by
    rw [exp_emb_snd hη hz, hc, emb_fst, emb_fst, T_fst, log_mul_exp hz.1 hη]
    ring
  have k2 : (emb η z).2 0 + η * exp ((emb η z).1 0 - η * exp ((emb η z).2 0))
      = (emb η (T z)).2 0 := by
    have hT := pos_T hz
    have hc' : η * ((T z).1 / η) = (T z).1 := by field_simp
    rw [k1, exp_emb_fst hη hT, hc', emb_snd, emb_snd, T_snd, log_mul_exp hz.2 hη]
  exact Prod.ext (E1_ext (c1.trans k1)) (E1_ext (c2.trans k2))

/-! Piece (b), first part: the iterated bracket of a word is an integer-like multiple of a monomial. -/

/-- `φ` agrees with the monomial `c e^{A p + B q}` on the quadrant. -/
def IsMono (φ : E1 × E1 → ℝ) (c : ℝ) (A B : ℕ) : Prop :=
  ∀ w : E1 × E1, w.1 ∈ Hs → w.2 ∈ Hs → φ w = mono c A B w

theorem letter_true : IsMono (letter fexp fexp true) 1 0 1 := by
  intro w _ _
  simp [letter, fexp, mono]

theorem letter_false : IsMono (letter fexp fexp false) 1 1 0 := by
  intro w _ _
  simp [letter, fexp, mono]

theorem pb_letter_true {φ : E1 × E1 → ℝ} {c : ℝ} {A B : ℕ} (h : IsMono φ c A B) :
    IsMono (pb Hs Hs φ (letter fexp fexp true)) (-(c * A)) A (B + 1) := by
  intro z hz1 hz2
  rw [pb_mono hz1 hz2 h letter_true]
  simp only [mono, Nat.cast_zero, Nat.cast_one, Nat.cast_add, add_zero, mul_zero, mul_one,
    zero_sub]
  ring

theorem pb_letter_false {φ : E1 × E1 → ℝ} {c : ℝ} {A B : ℕ} (h : IsMono φ c A B) :
    IsMono (pb Hs Hs φ (letter fexp fexp false)) (c * B) (A + 1) B := by
  intro z hz1 hz2
  rw [pb_mono hz1 hz2 h letter_false]
  simp only [mono, Nat.cast_zero, Nat.cast_one, Nat.cast_add, add_zero, mul_zero, mul_one,
    sub_zero]

theorem ipb_cons (a b : Bool) (w : List Bool) :
    ipb Hs Hs fexp fexp (a :: b :: w)
      = pb Hs Hs (ipb Hs Hs fexp fexp (b :: w)) (letter fexp fexp a) := rfl

theorem ipb_step_bound {c : ℝ} {A n : ℕ} (hc : |c| ≤ (n.factorial : ℝ)) (hA : A ≤ n + 1) :
    |c * A| ≤ ((n + 1).factorial : ℝ) := by
  have hA' : (A : ℝ) ≤ n + 1 := by exact_mod_cast hA
  rw [abs_mul, Nat.abs_cast A, Nat.factorial_succ]
  push_cast
  calc |c| * A ≤ n.factorial * (n + 1) :=
        mul_le_mul hc hA' (Nat.cast_nonneg A) (Nat.cast_nonneg _)
    _ = (n + 1) * n.factorial := by ring

/-- The bracket of a word of `n + 1` letters is `c e^{A p + B q}` with `A + B = n + 1`,
`|c| ≤ n!`, and `A, B ≥ 1` when `n ≥ 1` and `c ≠ 0`. -/
theorem ipb_spec : ∀ (n : ℕ) (w : List Bool), w.length = n + 1 →
    ∃ (c : ℝ) (A B : ℕ), A + B = n + 1 ∧ |c| ≤ (n.factorial : ℝ) ∧
      (1 ≤ n → c ≠ 0 → 1 ≤ A ∧ 1 ≤ B) ∧ IsMono (ipb Hs Hs fexp fexp w) c A B := by
  intro n
  induction n with
  | zero =>
    intro w hw
    rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
    · simp at hw
    · cases a
      · exact ⟨1, 1, 0, rfl, by simp, fun h => absurd h (by norm_num), letter_false⟩
      · exact ⟨1, 0, 1, rfl, by simp, fun h => absurd h (by norm_num), letter_true⟩
    · simp at hw
  | succ n ih =>
    intro w hw
    rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
    · simp at hw
    · simp at hw
    · have hw' : (b :: w).length = n + 1 := by
        simp only [List.length_cons] at hw ⊢
        omega
      obtain ⟨c, A, B, hAB, hc, hpos, hm⟩ := ih (b :: w) hw'
      cases a
      · refine ⟨c * B, A + 1, B, by omega, ipb_step_bound hc (by omega), ?_, ?_⟩
        · intro _ hne
          have hB : B ≠ 0 := by
            rintro rfl
            exact hne (by simp)
          exact ⟨by omega, Nat.pos_of_ne_zero hB⟩
        · rw [ipb_cons]
          exact pb_letter_false hm
      · refine ⟨-(c * A), A, B + 1, by omega, ?_, ?_, ?_⟩
        · rw [abs_neg]
          exact ipb_step_bound hc (by omega)
        · intro _ hne
          have hA : A ≠ 0 := by
            rintro rfl
            exact hne (by simp)
          exact ⟨Nat.pos_of_ne_zero hA, by omega⟩
        · rw [ipb_cons]
          exact pb_letter_true hm

/-- Size of the bracket of a word of at least two letters on the quadrant. -/
theorem ipb_bound {n : ℕ} (hn : 1 ≤ n) {w : List Bool} (hw : w.length = n + 1) {z : E1 × E1}
    (hz1 : z.1 ∈ Hs) (hz2 : z.2 ∈ Hs) :
    |ipb Hs Hs fexp fexp w z| ≤ (n.factorial : ℝ) * exp (z.1 0 + z.2 0) := by
  obtain ⟨c, A, B, _, hc, hpos, hm⟩ := ipb_spec n w hw
  rw [hm z hz1 hz2]
  by_cases h0 : c = 0
  · rw [h0]
    simp only [mono, zero_mul, abs_zero]
    positivity
  · obtain ⟨hA, hB⟩ := hpos hn h0
    have hp : z.1 0 ≤ 0 := hz1
    have hq : z.2 0 ≤ 0 := hz2
    have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hexp : (A : ℝ) * z.1 0 + B * z.2 0 ≤ z.1 0 + z.2 0 := by nlinarith
    show |c * exp ((A : ℝ) * z.1 0 + (B : ℝ) * z.2 0)| ≤ _
    rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul hc (exp_le_exp.mpr hexp) (exp_pos _).le (Nat.cast_nonneg _)

/-! Piece (b), second part: size of the corrections `H_n` on the quadrant. -/

theorem word_length {m : ℕ} (rs : Fin m → ℕ × ℕ) :
    (word rs).length = ∑ i, ((rs i).1 + (rs i).2) := by
  simp [word, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem abs_sum_le_card {ι : Type} (S : Finset ι) (t : ι → ℝ) (b : ℝ) (h : ∀ i ∈ S, |t i| ≤ b) :
    |∑ i ∈ S, t i| ≤ (S.card : ℝ) * b := by
  calc |∑ i ∈ S, t i| ≤ ∑ i ∈ S, |t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, b := Finset.sum_le_sum h
    _ = (S.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]

theorem card_filter_pi_le (n m : ℕ) (hm : m ≤ n + 1) (p : (Fin m → ℕ × ℕ) → Prop)
    [DecidablePred p] :
    ((Fintype.piFinset fun _ : Fin m => Finset.range (n + 2) ×ˢ Finset.range (n + 2)).filter p).card
      ≤ ((n + 2) ^ 2) ^ (n + 1) := by
  calc ((Fintype.piFinset fun _ : Fin m =>
          Finset.range (n + 2) ×ˢ Finset.range (n + 2)).filter p).card
      ≤ (Fintype.piFinset fun _ : Fin m => Finset.range (n + 2) ×ˢ Finset.range (n + 2)).card :=
        Finset.card_filter_le _ _
    _ = ((n + 2) ^ 2) ^ m := by simp [Fintype.card_piFinset, pow_two]
    _ ≤ ((n + 2) ^ 2) ^ (n + 1) := Nat.pow_le_pow_right (by positivity) hm

/-- An explicit bound for the coefficient sum of `H_n`. -/
def Cn (n : ℕ) : ℕ := (n + 1) * (((n + 2) ^ 2) ^ (n + 1) * n.factorial)

theorem term_bound {n : ℕ} (hn : 1 ≤ n) {m : ℕ} {rs : Fin m → ℕ × ℕ}
    (hrs : ∑ i, ((rs i).1 + (rs i).2) = n + 1) {z : E1 × E1} (hz1 : z.1 ∈ Hs) (hz2 : z.2 ∈ Hs) :
    |ipb Hs Hs fexp fexp (word rs) z /
        ∏ i, (((rs i).1.factorial : ℝ) * ((rs i).2.factorial : ℝ))|
      ≤ (n.factorial : ℝ) * exp (z.1 0 + z.2 0) := by
  have hlen : (word rs).length = n + 1 := by rw [word_length, hrs]
  have hprod : (1 : ℝ) ≤ ∏ i, (((rs i).1.factorial : ℝ) * ((rs i).2.factorial : ℝ)) := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        (1 : ℝ) ≤ ((rs i).1.factorial : ℝ) * ((rs i).2.factorial : ℝ) := by
      intro i _
      have ha : (1 : ℝ) ≤ ((rs i).1.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hb : (1 : ℝ) ≤ ((rs i).2.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      nlinarith
    calc (1 : ℝ) = ∏ _i : Fin m, (1 : ℝ) := by simp
      _ ≤ ∏ i, (((rs i).1.factorial : ℝ) * ((rs i).2.factorial : ℝ)) :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) h1
  rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos hprod)]
  exact (div_le_self (abs_nonneg _) hprod).trans (ipb_bound hn hlen hz1 hz2)

/-- Size of `H_n`, `n ≥ 1`, on the quadrant. -/
theorem corr_bound {n : ℕ} (hn : 1 ≤ n) {z : E1 × E1} (hz1 : z.1 ∈ Hs) (hz2 : z.2 ∈ Hs) :
    |corr Hs Hs fexp fexp n z| ≤ (Cn n : ℝ) * exp (z.1 0 + z.2 0) := by
  have he0 : 0 ≤ exp (z.1 0 + z.2 0) := (exp_pos _).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h0 : |1 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_le_one (by linarith)).mpr (by linarith)
  unfold corr
  rw [abs_mul]
  refine le_trans (mul_le_mul h0 (abs_sum_le_card _ _
    ((((n + 2) ^ 2) ^ (n + 1) * n.factorial : ℕ) * exp (z.1 0 + z.2 0)) ?_)
    (abs_nonneg _) zero_le_one) ?_
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hc : |(-1 : ℝ) ^ (m - 1) / (m : ℝ)| ≤ 1 := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
      exact (div_le_one (by linarith)).mpr hm'
    rw [abs_mul]
    refine le_trans (mul_le_mul hc (abs_sum_le_card _ _
      ((n.factorial : ℝ) * exp (z.1 0 + z.2 0)) ?_) (abs_nonneg _) zero_le_one) ?_
    · intro rs hrs
      exact term_bound hn (Finset.mem_filter.mp hrs).2.2 hz1 hz2
    · rw [one_mul]
      have hne : 0 ≤ (n.factorial : ℝ) * exp (z.1 0 + z.2 0) :=
        mul_nonneg (Nat.cast_nonneg _) he0
      refine le_trans (mul_le_mul_of_nonneg_right
        ((Nat.cast_le (α := ℝ)).mpr (card_filter_pi_le n m hm2 _)) hne) ?_
      push_cast
      exact le_of_eq (by ring)
  · have hcI : (Finset.Icc 1 (n + 1)).card = n + 1 := by simp
    rw [one_mul, hcI]
    unfold Cn
    push_cast
    exact le_of_eq (by ring)

theorem word_one_zero : word (fun _ : Fin 1 => ((1 : ℕ), (0 : ℕ))) = [true] := by
  simp [word]

theorem word_zero_one : word (fun _ : Fin 1 => ((0 : ℕ), (1 : ℕ))) = [false] := by
  simp [word]

/-- `H_0 = F + G`. -/
theorem corr_zero (z : E1 × E1) : corr Hs Hs fexp fexp 0 z = fexp z.1 + fexp z.2 := by
  have hS : ((Fintype.piFinset fun _ : Fin 1 =>
        Finset.range (0 + 2) ×ˢ Finset.range (0 + 2)).filter
        (fun rs => (∀ i, 0 < (rs i).1 + (rs i).2) ∧ ∑ i, ((rs i).1 + (rs i).2) = 0 + 1))
      = {(fun _ => ((1 : ℕ), (0 : ℕ))), (fun _ => ((0 : ℕ), (1 : ℕ)))} := by
    ext rs
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_range,
      Finset.mem_insert, Finset.mem_singleton, Fin.forall_fin_one, Fin.sum_univ_one]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have h5 : (rs 0).1 = 1 ∧ (rs 0).2 = 0 ∨ (rs 0).1 = 0 ∧ (rs 0).2 = 1 := by omega
      rcases h5 with ⟨a, b⟩ | ⟨a, b⟩
      · left
        funext i
        fin_cases i
        exact Prod.ext a b
      · right
        funext i
        fin_cases i
        exact Prod.ext a b
    · rintro (rfl | rfl) <;> simp
  have hI : Finset.Icc 1 (0 + 1) = ({1} : Finset ℕ) := by simp
  have hne : (fun _ : Fin 1 => ((1 : ℕ), (0 : ℕ))) ≠ (fun _ : Fin 1 => ((0 : ℕ), (1 : ℕ))) := by
    intro h
    have h' := congrFun h 0
    simp at h'
  unfold corr
  rw [hI, Finset.sum_singleton, hS, Finset.sum_pair hne, word_one_zero, word_zero_one]
  simp [ipb, letter]
  ring

/-- The sum of the bounds `Cn 1, ..., Cn N`. -/
def MM (N : ℕ) : ℕ := ∑ j ∈ Finset.range N, Cn (j + 1)

/-- On the quadrant the truncated modified Hamiltonian differs from `F + G` by at most
`MM N e^{p + q}`. -/
theorem truncH_bound (N : ℕ) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {z : E1 × E1}
    (hz1 : z.1 ∈ Hs) (hz2 : z.2 ∈ Hs) :
    |truncH Hs Hs fexp fexp N η z - (fexp z.1 + fexp z.2)|
      ≤ (MM N : ℝ) * exp (z.1 0 + z.2 0) := by
  have hsplit : truncH Hs Hs fexp fexp N η z
      = ∑ j ∈ Finset.range N, η ^ (j + 1) * corr Hs Hs fexp fexp (j + 1) z
        + (fexp z.1 + fexp z.2) := by
    show ∑ j ∈ Finset.range (N + 1), η ^ j * corr Hs Hs fexp fexp j z = _
    rw [Finset.sum_range_succ', pow_zero, one_mul, corr_zero]
  rw [hsplit, add_sub_cancel_right]
  calc |∑ j ∈ Finset.range N, η ^ (j + 1) * corr Hs Hs fexp fexp (j + 1) z|
      ≤ ∑ j ∈ Finset.range N, |η ^ (j + 1) * corr Hs Hs fexp fexp (j + 1) z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, (Cn (j + 1) : ℝ) * exp (z.1 0 + z.2 0) :=
        Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
          calc η ^ (j + 1) * |corr Hs Hs fexp fexp (j + 1) z|
              ≤ 1 * |corr Hs Hs fexp fexp (j + 1) z| :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1) (abs_nonneg _)
            _ = |corr Hs Hs fexp fexp (j + 1) z| := one_mul _
            _ ≤ (Cn (j + 1) : ℝ) * exp (z.1 0 + z.2 0) :=
                corr_bound (Nat.succ_le_succ (Nat.zero_le j)) hz1 hz2
    _ = (MM N : ℝ) * exp (z.1 0 + z.2 0) := by
        rw [← Finset.sum_mul]
        unfold MM
        push_cast
        rfl

/-! Piece (e): the contradiction. -/

open Filter Topology

theorem Cn_le (N j : ℕ) (hj : j < N) : Cn (j + 1) ≤ (N + 3) ^ (3 * N + 3) := by
  unfold Cn
  have h1 : j + 1 + 1 ≤ N + 3 := by omega
  have h2 : ((j + 1 + 2) ^ 2) ^ (j + 1 + 1) ≤ ((N + 3) ^ 2) ^ (N + 1) := by
    calc ((j + 1 + 2) ^ 2) ^ (j + 1 + 1) ≤ ((N + 3) ^ 2) ^ (j + 1 + 1) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left (by omega) 2) _
      _ ≤ ((N + 3) ^ 2) ^ (N + 1) := Nat.pow_le_pow_right (by positivity) (by omega)
  have h3 : (j + 1).factorial ≤ (N + 3) ^ N := by
    calc (j + 1).factorial ≤ (j + 1) ^ (j + 1) := Nat.factorial_le_pow _
      _ ≤ (N + 3) ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (N + 3) ^ N := Nat.pow_le_pow_right (by omega) (by omega)
  calc (j + 1 + 1) * (((j + 1 + 2) ^ 2) ^ (j + 1 + 1) * (j + 1).factorial)
      ≤ (N + 3) * (((N + 3) ^ 2) ^ (N + 1) * (N + 3) ^ N) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    _ = (N + 3) ^ 1 * ((N + 3) ^ (2 * (N + 1)) * (N + 3) ^ N) := by rw [pow_one, ← pow_mul]
    _ = (N + 3) ^ (1 + (2 * (N + 1) + N)) := by rw [← pow_add, ← pow_add]
    _ = (N + 3) ^ (3 * N + 3) := by
        congr 1
        omega

theorem MM_le (N : ℕ) : MM N ≤ (N + 3) ^ (3 * N + 4) := by
  unfold MM
  calc ∑ j ∈ Finset.range N, Cn (j + 1)
      ≤ ∑ _j ∈ Finset.range N, (N + 3) ^ (3 * N + 3) :=
        Finset.sum_le_sum fun j hj => Cn_le N j (Finset.mem_range.mp hj)
    _ = N * (N + 3) ^ (3 * N + 3) := by simp
    _ ≤ (N + 3) * (N + 3) ^ (3 * N + 3) := Nat.mul_le_mul_right _ (by omega)
    _ = (N + 3) ^ (3 * N + 4) := by ring

theorem MM_le_exp (N : ℕ) : (MM N : ℝ) ≤ exp ((3 * (N : ℝ) + 4) * ((N : ℝ) + 3)) := by
  have h1 : (N : ℝ) + 3 ≤ exp ((N : ℝ) + 3) := by
    have h := Real.add_one_le_exp ((N : ℝ) + 3)
    linarith
  have h0 : (0 : ℝ) ≤ (N : ℝ) + 3 := by positivity
  have h2 : (MM N : ℝ) ≤ ((N : ℝ) + 3) ^ (3 * N + 4) := by
    have h := MM_le N
    exact_mod_cast h
  calc (MM N : ℝ) ≤ ((N : ℝ) + 3) ^ (3 * N + 4) := h2
    _ ≤ (exp ((N : ℝ) + 3)) ^ (3 * N + 4) := pow_le_pow_left₀ h0 h1 _
    _ = exp ((3 * (N : ℝ) + 4) * ((N : ℝ) + 3)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- The number of steps used for the truncation order `N`. -/
def Kf (N : ℕ) : ℕ := 10 * ((3 * N + 4) * (N + 3) + N) + 28

theorem MM_exp_Kf (N : ℕ) : (MM N : ℝ) * exp (-((Kf N : ℕ) : ℝ) / 10) ≤ exp (-(N : ℝ)) := by
  have hK : -((Kf N : ℕ) : ℝ) / 10 ≤ -((3 * (N : ℝ) + 4) * ((N : ℝ) + 3)) - (N : ℝ) := by
    unfold Kf
    push_cast
    linarith
  calc (MM N : ℝ) * exp (-((Kf N : ℕ) : ℝ) / 10)
      ≤ exp ((3 * (N : ℝ) + 4) * ((N : ℝ) + 3))
          * exp (-((3 * (N : ℝ) + 4) * ((N : ℝ) + 3)) - (N : ℝ)) :=
        mul_le_mul (MM_le_exp N) (exp_le_exp.mpr hK) (exp_pos _).le (exp_pos _).le
    _ = exp (-(N : ℝ)) := by
        rw [← exp_add]
        congr 1
        ring

theorem final_arith {a b M R η uF vF uB vB xF yF xB yB : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (tF : |a - (uF + vF)| ≤ M * (uF * vF)) (tB : |b - (uB + vB)| ≤ M * (uB * vB))
    (hab : |a - b| ≤ R) (huF : 0 ≤ uF) (hvF : vF ≤ 1) (hvB : 0 ≤ vB) (huB : uB ≤ 1)
    (hxF : η * uF = xF) (hyF : η * vF = yF) (hxB : η * uB = xB) (hyB : η * vB = yB)
    (hgap : xB + yB + 1 / 10 ^ 8 ≤ yF) :
    (1 / 10 ^ 8 : ℝ) ≤ η * R + M * (xF + yB) := by
  have h1 : uF + vF - M * uF ≤ a := by
    have h := (abs_le.mp tF).1
    have h2 : M * (uF * vF) ≤ M * uF :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right huF hvF) hM
    linarith
  have h2 : b ≤ uB + vB + M * vB := by
    have h := (abs_le.mp tB).2
    have h3 : M * (uB * vB) ≤ M * vB :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hvB huB) hM
    linarith
  have h3 : a - b ≤ R := (abs_le.mp hab).2
  have h4 : uF + vF - uB - vB - M * (uF + vB) ≤ R := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hη.le
  have h6 : η * (uF + vF - uB - vB - M * (uF + vB)) = xF + yF - xB - yB - M * (xF + yB) := by
    rw [← hxF, ← hyF, ← hxB, ← hyB]
    ring
  rw [h6] at h5
  have hx0 : 0 ≤ xF := by
    rw [← hxF]
    exact mul_nonneg hη.le huF
  linarith

/-- The statement of Conjecture 1 is false. -/
theorem not_main : ¬ (type_of% @OMA.S_arxiv_2405_03472.main) := by
  rintro ⟨Φ, _, ⟨C, hC⟩, h⟩
  have hη0 : (0 : ℝ) < 23 / 25 := by norm_num
  have hη1 : (23 / 25 : ℝ) ≤ 1 := by norm_num
  have key : ∀ N K : ℕ, 28 ≤ K → (1 / 10 ^ 8 : ℝ)
      ≤ 2 * (K : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (N + 3)
        + 2 * (MM N : ℝ) * exp (-(K : ℝ) / 10) := by
    intro N K hK
    have hmem : ∀ j, (emb (23 / 25) (T^[j] (Bw K))).1 ∈ Hs ∧
        (emb (23 / 25) (T^[j] (Bw K))).2 ∈ Hs := fun j => by
      obtain ⟨hp, hx, hy⟩ := orb_bounds K j
      exact emb_mem hη0 hp hx hy
    have hmain := h 1 Hs Hs fexp fexp 1 N Hs_closed Hs_convex Hs_interior Hs_closed Hs_convex
      Hs_interior one_pos (fexp_smooth _) (fexp_smooth _) (23 / 25) hη0
      (fun j => emb (23 / 25) (T^[j] (Bw K))) (2 * K)
      (fun j _ => ⟨(hmem j).1, (hmem j).2⟩)
      (fun j _ => by
        obtain ⟨hp, hx, hy⟩ := orb_bounds K j
        show emb (23 / 25) (T^[j + 1] (Bw K))
          = step Hs Hs fexp fexp (23 / 25) (emb (23 / 25) (T^[j] (Bw K)))
        rw [step_emb hη0 hp hx hy, Function.iterate_succ_apply'])
    have e2 : T^[2 * K] (Bw K) = Fw K := by
      rw [orb_ge K (2 * K) (by omega)]
      congr 1
      omega
    have hmain' : |truncH Hs Hs fexp fexp N (23 / 25) (emb (23 / 25) (Fw K))
        - truncH Hs Hs fexp fexp N (23 / 25) (emb (23 / 25) (Bw K))|
        ≤ ((2 * K : ℕ) : ℝ) * (Φ N : ℝ) * 1 ^ (N + 3) * (23 / 25) ^ (N + 2) := by
      have h' := hmain
      beta_reduce at h'
      rw [e2] at h'
      exact h'
    obtain ⟨mF1, mF2⟩ := emb_mem hη0 (Fw_pos K) ((Fw_fst_le K).trans (by norm_num)) (Fw_snd_le K)
    obtain ⟨mB1, mB2⟩ := emb_mem hη0 (Bw_pos K) (Bw_fst_le K) ((Bw_snd_le K).trans (by norm_num))
    have tF : |truncH Hs Hs fexp fexp N (23 / 25) (emb (23 / 25) (Fw K))
        - (exp ((emb (23 / 25) (Fw K)).1 0) + exp ((emb (23 / 25) (Fw K)).2 0))|
        ≤ (MM N : ℝ) * (exp ((emb (23 / 25) (Fw K)).1 0) * exp ((emb (23 / 25) (Fw K)).2 0)) := by
      have t := truncH_bound N hη0.le hη1 mF1 mF2
      rw [exp_add] at t
      exact t
    have tB : |truncH Hs Hs fexp fexp N (23 / 25) (emb (23 / 25) (Bw K))
        - (exp ((emb (23 / 25) (Bw K)).1 0) + exp ((emb (23 / 25) (Bw K)).2 0))|
        ≤ (MM N : ℝ) * (exp ((emb (23 / 25) (Bw K)).1 0) * exp ((emb (23 / 25) (Bw K)).2 0)) := by
      have t := truncH_bound N hη0.le hη1 mB1 mB2
      rw [exp_add] at t
      exact t
    have hxF : (23 / 25 : ℝ) * exp ((emb (23 / 25) (Fw K)).1 0) = (Fw K).1 := by
      rw [exp_emb_fst hη0 (Fw_pos K)]
      field_simp
    have hyF : (23 / 25 : ℝ) * exp ((emb (23 / 25) (Fw K)).2 0) = (Fw K).2 := by
      rw [exp_emb_snd hη0 (Fw_pos K)]
      field_simp
    have hxB : (23 / 25 : ℝ) * exp ((emb (23 / 25) (Bw K)).1 0) = (Bw K).1 := by
      rw [exp_emb_fst hη0 (Bw_pos K)]
      field_simp
    have hyB : (23 / 25 : ℝ) * exp ((emb (23 / 25) (Bw K)).2 0) = (Bw K).2 := by
      rw [exp_emb_snd hη0 (Bw_pos K)]
      field_simp
    have vF1 : exp ((emb (23 / 25) (Fw K)).2 0) ≤ 1 := Real.exp_le_one_iff.mpr mF2
    have uB1 : exp ((emb (23 / 25) (Bw K)).1 0) ≤ 1 := Real.exp_le_one_iff.mpr mB1
    have hΦ : (Φ N : ℝ) ≤ max (C : ℝ) 0 :=
      le_trans (by exact_mod_cast hC N) (le_max_left _ _)
    have hab : |truncH Hs Hs fexp fexp N (23 / 25) (emb (23 / 25) (Fw K))
        - truncH Hs Hs fexp fexp N (23 / 25) (emb (23 / 25) (Bw K))|
        ≤ 2 * (K : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (N + 2) := by
      refine hmain'.trans ?_
      have hP : (0 : ℝ) ≤ 2 * (K : ℝ) * (23 / 25 : ℝ) ^ (N + 2) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hΦ hP
      calc ((2 * K : ℕ) : ℝ) * (Φ N : ℝ) * 1 ^ (N + 3) * (23 / 25) ^ (N + 2)
          = 2 * (K : ℝ) * (23 / 25 : ℝ) ^ (N + 2) * (Φ N : ℝ) := by
            push_cast
            ring
        _ ≤ 2 * (K : ℝ) * (23 / 25 : ℝ) ^ (N + 2) * max (C : ℝ) 0 := hmul
        _ = 2 * (K : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (N + 2) := by ring
    have hM0 : (0 : ℝ) ≤ (MM N : ℝ) := Nat.cast_nonneg _
    have hfa := final_arith hη0 hM0 tF tB hab (exp_pos _).le vF1 (exp_pos _).le uB1
      hxF hyF hxB hyB (gap K hK)
    have hx := Fw_fst_le_exp K
    have hy := Bw_snd_le_exp K
    have hsum : (MM N : ℝ) * ((Fw K).1 + (Bw K).2) ≤ (MM N : ℝ) * (2 * exp (-(K : ℝ) / 10)) :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    have e : (23 / 25 : ℝ) * (2 * (K : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (N + 2))
        = 2 * (K : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (N + 3) := by ring
    linarith
  have hr : |(23 / 25 : ℝ)| < 1 := by
    rw [abs_of_pos hη0]
    norm_num
  have t0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hr
  have t1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
  have t2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  have tK : Tendsto (fun n : ℕ => ((Kf n : ℕ) : ℝ) * (23 / 25 : ℝ) ^ n) atTop (𝓝 0) := by
    have h3 := ((t2.const_mul 30).add (t1.const_mul 140)).add (t0.const_mul 148)
    simp only [mul_zero, add_zero] at h3
    refine Tendsto.congr (fun n => ?_) h3
    unfold Kf
    push_cast
    ring
  have tA : Tendsto (fun n : ℕ => 2 * ((Kf n : ℕ) : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (n + 3))
      atTop (𝓝 0) := by
    have h3 := tK.const_mul (2 * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ 3)
    simp only [mul_zero] at h3
    refine Tendsto.congr (fun n => ?_) h3
    ring
  have tB : Tendsto (fun n : ℕ => 2 * exp (-(n : ℝ))) atTop (𝓝 0) := by
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
    simpa using h3
  have tS := tA.add tB
  simp only [add_zero] at tS
  obtain ⟨N, hN⟩ := (tS.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num))).exists
  have hk := key N (Kf N) (by unfold Kf; omega)
  have hM := MM_exp_Kf N
  have hN' : 2 * ((Kf N : ℕ) : ℝ) * max (C : ℝ) 0 * (23 / 25 : ℝ) ^ (N + 3) + 2 * exp (-(N : ℝ))
      < 1 / 10 ^ 8 := hN
  linarith

end AMD

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2405_03472.main) := AMD.not_main
