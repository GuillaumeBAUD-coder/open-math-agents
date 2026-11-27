import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Persistence of the central Maxwell equilibria

Following the rescaling of Arathoon, Ball and Kvalheim (arXiv:2607.27197),
we extend the rescaled potential smoothly across ε = 0. A rationalized
remainder for each inverse distance makes the extension an exact identity.
The implicit function theorem then continues the zeros of the spatial
differential, and finite separation preserves their number.
-/

namespace OMA.Center
open Arxiv.«2607.27197» Filter InnerProductSpace
open scoped Topology Gradient

abbrev E := EuclideanSpace ℝ (Fin 3)

def radicand (t a b : ℝ) := 1 + t * (-2*a + t*b)
noncomputable def c2 (a b : ℝ) := (3*a^2 - b)/2
noncomputable def c3 (a b : ℝ) := (5*a^3 - 3*a*b)/2
noncomputable def c4 (a b : ℝ) := (35*a^4 - 30*a^2*b + 3*b^2)/8

/-- Remainder after degree four in the expansion of the reciprocal square root at one. -/
noncomputable def sqrtRem (s : ℝ) :=
  -(35*s^4 + 175*s^3 + 345*s^2 + 325*s + 128) / (128*s*(s+1)^5)

lemma sqrt_identity {u : ℝ} (hu : 0 < 1+u) :
    1 / Real.sqrt (1+u) =
    1-u/2+3*u^2/8-5*u^3/16+35*u^4/128+u^5*sqrtRem (Real.sqrt (1+u)) := by
  let s := Real.sqrt (1+u)
  have hs : 0 < s := Real.sqrt_pos.2 hu
  have he : u = s^2 - 1 := by linarith [Real.sq_sqrt hu.le]
  change 1/s = 1-u/2+3*u^2/8-5*u^3/16+35*u^4/128+u^5*sqrtRem s
  rw [he]
  unfold sqrtRem
  field_simp [hs.ne', show s+1 ≠ 0 by positivity]
  ring

noncomputable def rem5 (t a b : ℝ) :=
  -5*a*b*(14*a^2-3*b)/8 + t*(5*b^2*(21*a^2-b)/16 +
    t*(-35*a*b^3/16+t*(35*b^4/128))) +
    (-2*a+t*b)^5*sqrtRem (Real.sqrt (radicand t a b))

lemma expand_inv {t a b : ℝ} (h : 0 < radicand t a b) :
    1 / Real.sqrt (radicand t a b) = 1+t*a+t^2*c2 a b+t^3*c3 a b+
      t^4*c4 a b+t^5*rem5 t a b := by
  unfold radicand
  rw [sqrt_identity (u := t*(-2*a+t*b)) h]
  unfold c2 c3 c4 rem5 radicand
  ring

def normSq (x : E) := x.ofLp 0^2 + x.ofLp 1^2 + x.ofLp 2^2
noncomputable def dPlus (x : E) := -x.ofLp 0/2 + Real.sqrt 3*x.ofLp 1/2
noncomputable def dMinus (x : E) := -x.ofLp 0/2 - Real.sqrt 3*x.ofLp 1/2
noncomputable def amp (e : ℝ) := 3/4 - 5/32*e^2
noncomputable def farTail (e a b : ℝ) := c4 a b + e^2*rem5 (e^2) a b

/-- The extension after scaling space by ε² and potential by ε⁶. -/
noncomputable def family (e : ℝ) (x : E) :=
  phiZero x + e^2*(farTail e (x.ofLp 0) (normSq x) +
    farTail e (dPlus x) (normSq x) + farTail e (dMinus x) (normSq x) -
    5/16*c4 (x.ofLp 2) (normSq x)) +
    e*amp e*(rem5 e (x.ofLp 2) (normSq x) + rem5 e (-x.ofLp 2) (normSq x))

lemma family_zero : family 0 = phiZero := by
  funext x
  simp [family]

noncomputable abbrev proj (i : Fin 3) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj i)

lemma rem5_smooth {t a b : ℝ × E → ℝ} {p : ℝ × E}
    (ht : ContDiffAt ℝ ⊤ t p) (ha : ContDiffAt ℝ ⊤ a p) (hb : ContDiffAt ℝ ⊤ b p)
    (hz : t p = 0) : ContDiffAt ℝ ⊤ (fun q => rem5 (t q) (a q) (b q)) p := by
  have hh : radicand (t p) (a p) (b p) = 1 := by simp [radicand, hz]
  have hs : ContDiffAt ℝ ⊤ (fun q => Real.sqrt (radicand (t q) (a q) (b q))) p := by
    apply ContDiffAt.sqrt
    · unfold radicand
      fun_prop
    · rw [hh]; norm_num
  unfold rem5 sqrtRem
  fun_prop (disch := simp [hh])

lemma family_smooth (x : E) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × E => family p.1 p.2) (0,x) := by
  have h (i : Fin 3) : ContDiffAt ℝ ⊤ (fun p : ℝ × E => p.2.ofLp i) (0,x) :=
    (proj i).contDiff.contDiffAt.comp _ contDiffAt_snd
  have hb : ContDiffAt ℝ ⊤ (fun p : ℝ × E => normSq p.2) (0,x) := by
    unfold normSq
    fun_prop
  have hp : ContDiffAt ℝ ⊤ (fun p : ℝ × E => dPlus p.2) (0,x) := by unfold dPlus; fun_prop
  have hm : ContDiffAt ℝ ⊤ (fun p : ℝ × E => dMinus p.2) (0,x) := by unfold dMinus; fun_prop
  have hr0 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1^2) (p.2.ofLp 0) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr1 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1^2) (dPlus p.2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr2 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1^2) (dMinus p.2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr3 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1) (p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr4 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1) (-p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  unfold family phiZero farTail amp c4
  dsimp only
  fun_prop

def regular (e : ℝ) (x : E) : Prop :=
  0 < radicand (e^2) (x.ofLp 0) (normSq x) ∧
  0 < radicand (e^2) (dPlus x) (normSq x) ∧
  0 < radicand (e^2) (dMinus x) (normSq x) ∧
  0 < radicand e (x.ofLp 2) (normSq x) ∧
  0 < radicand e (-x.ofLp 2) (normSq x)

lemma regular_open : IsOpen {p : ℝ × E | regular p.1 p.2} := by
  have h (i : Fin 3) : Continuous (fun p : ℝ × E => p.2.ofLp i) :=
    (proj i).continuous.comp continuous_snd
  have posOpen (t a : ℝ × E → ℝ) (ht : Continuous t) (ha : Continuous a) :
      IsOpen {p : ℝ × E | 0 < radicand (t p) (a p) (normSq p.2)} := by
    apply isOpen_lt (f := fun _ => (0 : ℝ)) continuous_const
    unfold radicand normSq
    fun_prop
  unfold regular
  refine IsOpen.inter (posOpen _ _ ?_ ?_) (IsOpen.inter (posOpen _ _ ?_ ?_)
    (IsOpen.inter (posOpen _ _ ?_ ?_) (IsOpen.inter (posOpen _ _ ?_ ?_) (posOpen _ _ ?_ ?_))))
  all_goals first | fun_prop | unfold dPlus; fun_prop | unfold dMinus; fun_prop

lemma regular_zero (x : E) : regular 0 x := by simp [regular, radicand]

noncomputable def distList (e : ℝ) (x : E) : Fin 5 → ℝ :=
  ![Real.sqrt (radicand (e^2) (x.ofLp 0) (normSq x)),
    Real.sqrt (radicand (e^2) (dPlus x) (normSq x)),
    Real.sqrt (radicand (e^2) (dMinus x) (normSq x)),
    e * Real.sqrt (radicand e (x.ofLp 2) (normSq x)),
    e * Real.sqrt (radicand e (-x.ofLp 2) (normSq x))]

lemma distance_formula {e : ℝ} (he : 0 < e) (x : E) (j : Fin 5) :
    dist (e^2 • x) (counterexamplePositions e j) = distList e x j := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have pull (u : ℝ) : e * Real.sqrt u = Real.sqrt (e^2 * u) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he.le]
  fin_cases j <;>
    simp [distList, counterexamplePositions, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Real.dist_eq, radicand, normSq, dPlus, dMinus, pull] <;>
    congr 1 <;> ring_nf <;> norm_num [hs] <;> ring

lemma away {e : ℝ} {x : E} (he : 0 < e) (h : regular e x) :
    e^2 • x ∉ Set.range (counterexamplePositions e) := by
  rintro ⟨j, hj⟩
  have hpos : 0 < distList e x j := by
    obtain ⟨h0,h1,h2,h3,h4⟩ := h
    fin_cases j <;> simp [distList, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;> positivity
  rw [← distance_formula he, hj, dist_self] at hpos
  exact lt_irrefl _ hpos

noncomputable def base (e : ℝ) := 3 + 2*e^2*amp e

set_option maxHeartbeats 1500000 in
lemma scaling {e : ℝ} {x : E} (he : 0 < e) (h : regular e x) :
    potential (counterexampleCharges e) (counterexamplePositions e) (e^2 • x) =
      base e + e^6 * family e x := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := h
  unfold potential
  simp only [distance_formula he]
  simp [counterexampleCharges, distList, Fin.sum_univ_succ, -one_div]
  have axial (u : ℝ) : (3/4*e^3-5/32*e^5)/(e*u) = (e^2*amp e)*(1/u) := by
    unfold amp
    rw [mul_comm e u, ← div_div, div_eq_mul_inv _ e]
    field_simp [he.ne']
  rw [axial, axial, expand_inv h0, expand_inv h1, expand_inv h2, expand_inv h3, expand_inv h4]
  unfold base family farTail phiZero amp c2 c3 c4
  dsimp only
  unfold dPlus dMinus normSq
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

abbrev Dual := E →L[ℝ] ℝ

lemma grad_zero {V : E → ℝ} {x} :
    ∇ V x = 0 ↔ fderiv ℝ V x = 0 := by
  rw [← toDual_gradient]
  exact (toDual ℝ _).map_eq_zero_iff.symm

lemma hessian_iff (V : E → ℝ) (x : E) :
    HasNondegenerateHessianAt V x ↔ (fderiv ℝ (fderiv ℝ V) x).IsInvertible := by
  let L := fderiv ℝ (fderiv ℝ V) x
  change (∀ v : E, v ≠ 0 → ∃ w, iteratedFDeriv ℝ 2 V x ![v,w] ≠ 0) ↔ L.IsInvertible
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (∀ v : E, v ≠ 0 → ∃ w, L v w ≠ 0) ↔ L.IsInvertible
  constructor
  · intro h
    have hk : L.ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      by_contra hn
      obtain ⟨w, hw⟩ := h v hn
      change L v = 0 at hv
      exact hw (by rw [hv]; rfl)
    have hdim : Module.finrank ℝ E = Module.finrank ℝ Dual :=
      (toDual ℝ E).toLinearEquiv.finrank_eq
    have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (LinearMap.ker_eq_bot.mp hk))
    exact ⟨ContinuousLinearEquiv.ofBijective L hk hr, rfl⟩
  · rintro ⟨A,hA⟩ v hv
    by_contra! h
    apply hv
    apply A.injective
    rw [map_zero]
    change (A : E →L[ℝ] Dual) v = 0
    rw [hA]
    ext w
    exact h w

noncomputable def spatialField (V : ℝ → E → ℝ) (p : ℝ × E) :=
  fderiv ℝ (V p.1) p.2

lemma field_smooth {V : ℝ → E → ℝ} {p : ℝ × E}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry V) p) :
    ContDiffAt ℝ ⊤ (spatialField V) p := by
  rcases p with ⟨e,x⟩
  apply ContDiffAt.fderiv (n := ⊤) (f := fun q : ℝ × E => V q.1) (g := Prod.snd)
  · have hh : ContDiffAt ℝ ⊤ (fun q : (ℝ × E) × E => (q.1.1,q.2)) ((e,x),x) := by fun_prop
    exact h.comp ((e,x),x) hh
  · exact contDiffAt_snd
  · simp

lemma partial_hessian {V : ℝ → E → ℝ} {p : ℝ × E}
    (h : DifferentiableAt ℝ (spatialField V) p) :
    fderiv ℝ (fderiv ℝ (V p.1)) p.2 =
    (fderiv ℝ (spatialField V) p).comp (.inr ℝ ℝ E) := by
  rcases p with ⟨e,x⟩
  have h' := (h.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) e x)).fderiv
  exact h'

/-- The implicit function for the spatial differential preserves nondegeneracy. -/
lemma branch {V : ℝ → E → ℝ} {x : E}
    (hs : ContDiffAt ℝ ⊤ (Function.uncurry V) (0,x))
    (hc : fderiv ℝ (V 0) x = 0) (hn : HasNondegenerateHessianAt (V 0) x) :
    ∃ g : ℝ → E, Tendsto g (𝓝 0) (𝓝 x) ∧
      ∀ᶠ e in 𝓝 0, fderiv ℝ (V e) (g e) = 0 ∧ HasNondegenerateHessianAt (V e) (g e) := by
  let p : ℝ × E := (0,x)
  have h := field_smooth hs
  have h1 : ContDiffAt ℝ 1 (spatialField V) p := h.of_le (by simp)
  have hi := (hessian_iff _ _).mp hn
  change (fderiv ℝ (fderiv ℝ (V p.1)) p.2).IsInvertible at hi
  rw [partial_hessian (h1.differentiableAt (by simp))] at hi
  let g := h1.implicitFunction one_ne_zero hi
  have hg : Tendsto g (𝓝 0) (𝓝 x) :=
    (h1.hasStrictFDerivAt one_ne_zero).tendsto_implicitFunctionOfProdDomain hi
  refine ⟨g, hg, ?_⟩
  have hh : ContinuousAt (fun q : ℝ × E =>
      (fderiv ℝ (spatialField V) q).comp (.inr ℝ ℝ E)) p := by
    have hf := (h.fderiv_right (m := 1) (by simp)).continuousAt
    fun_prop
  have hopen : IsOpen {L : E →L[ℝ] Dual | L.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  have hinv := hh.tendsto (hopen.mem_nhds hi)
  have hd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ (spatialField V) q :=
    (h1.eventually (by norm_num)).mono fun q hq => hq.differentiableAt one_ne_zero
  have hp : Tendsto (fun e => (e,g e)) (𝓝 0) (𝓝 p) :=
    tendsto_id.prodMk_nhds hg
  filter_upwards [h1.eventually_apply_implicitFunction one_ne_zero hi, hp hinv, hp hd] with e he hei hed
  refine ⟨he.trans hc, (hessian_iff _ _).mpr ?_⟩
  rw [partial_hessian hed]
  exact hei

lemma transport {V W : E → ℝ} {x : E} (A : E ≃L[ℝ] E) {b c : ℝ} (hc : c ≠ 0)
    (he : V ∘ A =ᶠ[𝓝 x] fun y => b + c*W y)
    (hs : ContDiffAt ℝ 2 W x) (hg : fderiv ℝ W x = 0) (hn : HasNondegenerateHessianAt W x) :
    fderiv ℝ V (A x) = 0 ∧ HasNondegenerateHessianAt V (A x) := by
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [A.comp_right_fderiv] at hd
  have hdW := hs.differentiableAt (by norm_num)
  have hright : fderiv ℝ (fun y => b + c*W y) x = 0 := by
    have h := (hdW.hasFDerivAt.const_mul c).const_add b
    rw [h.fderiv, hg]
    simp
  rw [hright] at hd
  constructor
  · ext v
    obtain ⟨w, rfl⟩ := A.surjective v
    exact congrArg (fun L : E →L[ℝ] ℝ => L w) hd
  · intro v hv
    obtain ⟨u,rfl⟩ := A.surjective v
    obtain ⟨w,hw⟩ := hn u (fun h => hv (by simp [h]))
    refine ⟨A w, ?_⟩
    have hsrc := (he.iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds
    have ha := A.iteratedFDerivWithin_comp_right V uniqueDiffOn_univ (Set.mem_univ (A x)) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at ha
    have htwo : ContDiffAt ℝ (2 : ℕ) (fun y => c • W y) x := by
      change ContDiffAt ℝ 2 (fun y => c * W y) x
      fun_prop
    change iteratedFDeriv ℝ 2 (V ∘ A) x =
      iteratedFDeriv ℝ 2 (fun y => b + c • W y) x at hsrc
    rw [fun_iteratedFDeriv_add_apply contDiffAt_const htwo,
      iteratedFDeriv_const_of_ne (by decide : (2 : ℕ) ≠ 0), iteratedFDeriv_const_smul_apply' hs] at hsrc
    simp only [Pi.zero_apply, zero_add] at hsrc
    rw [ha] at hsrc
    have hh := congrArg (fun L : E [×2]→L[ℝ] ℝ => L ![u,w]) hsrc
    change iteratedFDeriv ℝ 2 V (A x) (fun i => A (![u,w] i)) =
      c * iteratedFDeriv ℝ 2 W x ![u,w] at hh
    have hvec : (fun i => A (![u,w] i)) = ![A u,A w] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec] at hh
    exact hh.trans_ne (mul_ne_zero hc hw)

lemma original_critical {e : ℝ} {x : E} (he : 0 < e) (hr : regular e x)
    (hs : ContDiffAt ℝ 2 (family e) x) (hg : fderiv ℝ (family e) x = 0)
    (hn : HasNondegenerateHessianAt (family e) x) :
    e^2 • x ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) := by
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (G := ℝˣ) (Units.mk0 (e^2) (pow_ne_zero _ he.ne'))
  let V := potential (counterexampleCharges e) (counterexamplePositions e)
  have heq : V ∘ A =ᶠ[𝓝 x] fun y => base e + e^6 * family e y := by
    have ht : ContinuousAt (fun y : E => (e,y)) x := continuousAt_const.prodMk continuousAt_id
    filter_upwards [ht.tendsto (regular_open.mem_nhds hr)] with y hy
    exact scaling he hy
  obtain ⟨hg',hn'⟩ := transport A (pow_ne_zero 6 he.ne') heq hs hg hn
  exact ⟨⟨away he hr, grad_zero.mpr hg'⟩,hn'⟩

/-- Finitely many branches with distinct limits remain pairwise distinct. -/
lemma eventually_injective {ι : Type*} [Finite ι] {a : ι → E} (ha : Function.Injective a)
    {g : ι → ℝ → E} (hg : ∀ i, Tendsto (g i) (𝓝 0) (𝓝 (a i))) :
    ∀ᶠ e in 𝓝 0, Function.Injective (fun i => g i e) := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases h : i = j
  · exact Eventually.of_forall fun _ _ => h
  · have hn : (a i,a j) ∈ (Set.diagonal E)ᶜ := fun he => h (ha he)
    have hu := (hg i).prodMk_nhds (hg j)
    filter_upwards [hu (isClosed_diagonal.isOpen_compl.mem_nhds hn)] with e he
    exact fun hij => (he hij).elim

lemma center_branch {x : E} (hc : ∇ phiZero x = 0) (hn : HasNondegenerateHessianAt phiZero x)
    {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → E, Tendsto g (𝓝 0) (𝓝 x) ∧ ∀ᶠ e in 𝓝 0, 0 < e →
      e^2 • g e ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) ∩
        Metric.ball 0 r := by
  have hs : ContDiffAt ℝ ⊤ (Function.uncurry family) (0,x) := family_smooth x
  obtain ⟨g,hg,hc'⟩ := branch hs (by rw [family_zero]; exact grad_zero.mp hc) (by rwa [family_zero])
  refine ⟨g,hg,?_⟩
  have hp : Tendsto (fun e => (e,g e)) (𝓝 0) (𝓝 (0,x)) := tendsto_id.prodMk_nhds hg
  have hreg := hp (regular_open.mem_nhds (regular_zero x))
  have h2 : ContDiffAt ℝ 2 (Function.uncurry family) (0,x) := hs.of_le (by simp)
  have hs' := hp (h2.eventually (by norm_num))
  have hball : Tendsto (fun e => e^2 • g e) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (α := ℝ) (x := 𝓝 0)).pow 2 |>.smul hg
  filter_upwards [hc', hreg, hs', hball (Metric.ball_mem_nhds _ hr)] with e h he hdiff hb
  intro hepos
  change ContDiffAt ℝ 2 (Function.uncurry family) (e,g e) at hdiff
  have slice : ContDiffAt ℝ 2 (fun y : E => (e,y)) (g e) := by fun_prop
  exact ⟨original_critical hepos he (hdiff.comp (g e) slice)
    h.1 h.2, hb⟩

end OMA.Center

open Arxiv.«2607.27197» Filter OMA.Center
open scoped Topology Gradient

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1.H2 := by
  classical
  intro s hs r hr
  choose g hg hmem using (fun i : s => center_branch (hs i i.property).1 (hs i i.property).2 hr)
  have hi := eventually_injective (a := fun i : s => (i : E)) Subtype.val_injective hg
  have h := hi.and (eventually_all.mpr hmem)
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨δ,hδ,?_⟩
  intro e he
  obtain ⟨hinj,hinside⟩ := hbound (y := e) (by simpa [Real.dist_eq, abs_of_pos he.1] using he.2)
  have heinj : Function.Injective (fun i : s => e^2 • g i e) := by
    intro i j hij
    apply hinj
    exact (smul_right_injective _ (pow_ne_zero 2 he.1.ne')) hij
  have hle := heinj.encard_range.trans (Set.encard_le_encard (Set.range_subset_iff.mpr
    (fun i => hinside i he.1)))
  simpa using hle
