import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1
import Mathlib

-- Reduction WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1 of step WeierstrassCurve.Affine.Rat.weakBSD.R1.H3
-- Credit: @carterleffen
--
-- H1 gives absolute convergence of the elliptic Dirichlet series on Re(s) > 3/2.
-- H2 supplies a weight-two cusp form for Γ₀(N) with the elliptic Fourier coefficients.
-- H3 asserts that the first nonzero Taylor derivative of the form's Hecke L-function
-- occurs at the eventual growth exponent of the counts #(E(ℚ)/2ⁿE(ℚ)) · #Ш(E)[2ⁿ].
--
-- Cuspidality makes the Hecke L-function entire. The coefficient identity first gives
-- agreement with the elliptic series on Re(s) > 2. Absolute convergence and analytic
-- uniqueness extend the agreement to Re(s) > 3/2. The Taylor criterion then gives the
-- meromorphic order at 1 in the parent hypothesis.

namespace OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1

def H1 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] (s : ℂ), 3 / 2 < s.re →
    LSeriesSummable (fun n : ℕ ↦ (E.LFunction n : ℂ)) s

def H2 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    ∃ N : ℕ, 0 < N ∧
      ∃ f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2,
        ∀ n : ℕ, 1 ≤ n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)

def H3 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] (N : ℕ) [NeZero N]
    (f : CuspForm ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2),
    (∀ n : ℕ, 1 ≤ n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
    let D : ℕ → ℕ := fun n ↦
      Nat.card (E.Point ⧸ (nsmulAddMonoidHom (2 ^ n) : E.Point →+ E.Point).range)
    let s : ℕ → ℕ := fun n ↦ Nat.card {x : E.tateShafarevich // (2 ^ n : ℕ) • x = 0}
    ∃ a : ℕ,
      (∀ j : ℕ, j < a → iteratedDeriv j (ModularForm.L (two_pos : (0 : ℤ) < 2) f) 1 = 0) ∧
      iteratedDeriv a (ModularForm.L (two_pos : (0 : ℤ) < 2) f) 1 ≠ 0 ∧
      ∃ M, ∀ n, M ≤ n → D n * s n ≠ 0 ∧ D (n + 1) * s (n + 1) = 2 ^ a * (D n * s n)

/-- (1) For a group of width one at `∞`, the Hecke L-function of a weight-two cusp form is the
Dirichlet series of any sequence that agrees with its `q`-expansion coefficients for `n ≥ 1`,
on the half-plane `Re s > 2` where the modular series converges. -/
theorem hecke_eq_dirichlet_of_two_lt {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {F : Type*} [FunLike F UpperHalfPlane ℂ] [CuspFormClass F Γ 2]
    (hw : Γ.strictWidthInfty = 1) (f : F) (c : ℕ → ℂ)
    (hc : ∀ n : ℕ, 1 ≤ n → (UpperHalfPlane.qExpansion 1 f).coeff n = c n)
    {s : ℂ} (hs : 2 < s.re) :
    ModularForm.L (two_pos : (0 : ℤ) < 2) f s = LSeries c s := by
  have h := CuspForm.hasSum_L (two_pos : (0 : ℤ) < 2) f (s := s) (by push_cast; linarith)
  rw [hw] at h
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have he : LSeries.term c s =
      fun n : ℕ ↦ (UpperHalfPlane.qExpansion 1 f).coeff n / (n : ℂ) ^ s := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Complex.zero_cpow hs0]
    · rw [LSeries.term_of_ne_zero hn.ne', hc n hn]
  rw [← he] at h
  exact h.tsum_eq.symm

/-- (2) An entire function that equals a Dirichlet series on `Re s > 2` equals it on
`Re s > 3/2` as soon as the series converges absolutely there. -/
theorem eq_LSeries_of_summable {c : ℕ → ℂ}
    (hsum : ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable c s) {M : ℂ → ℂ}
    (hM : Differentiable ℂ M) (h : ∀ s : ℂ, 2 < s.re → M s = LSeries c s)
    {s : ℂ} (hs : 3 / 2 < s.re) : M s = LSeries c s := by
  have habs : LSeries.abscissaOfAbsConv c ≤ ((3 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      hsum y (by simpa using hy)
  have hc : AnalyticOnNhd ℂ (LSeries c) {z : ℂ | 3 / 2 < z.re} :=
    (LSeries_analyticOnNhd c).mono fun z hz ↦
      lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz)
  have hev : M =ᶠ[nhds (3 : ℂ)] LSeries c := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    exact h z hz
  have hMa : AnalyticOnNhd ℂ M {z : ℂ | 3 / 2 < z.re} := fun z _ ↦ hM.analyticAt z
  exact hMa.eqOn_of_preconnected_of_eventuallyEq hc (convex_halfSpace_re_gt _).isPreconnected
    (show (3 / 2 : ℝ) < (3 : ℂ).re by norm_num) hev hs

/-- (4) The Taylor criterion: for an entire function, vanishing of the derivatives of order
`< a` at `1` and a nonzero derivative of order `a` say that the meromorphic order at `1` is `a`. -/
theorem meromorphicOrderAt_of_taylor {M : ℂ → ℂ} (hM : Differentiable ℂ M) {a : ℕ}
    (hlow : ∀ j : ℕ, j < a → iteratedDeriv j M 1 = 0) (hne : iteratedDeriv a M 1 ≠ 0) :
    meromorphicOrderAt M 1 = a := by
  have han : AnalyticAt ℂ M 1 := hM.analyticAt 1
  have ho : analyticOrderAt M 1 = a :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mpr ⟨hlow, hne⟩
  rw [han.meromorphicOrderAt_eq, ho]
  rfl

theorem main : H1 → H2 → H3 → OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1.H3 := by
  intro h1 h2 h3 E hE
  obtain ⟨N, hN, f, hc⟩ := h2 E
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨a, hlow, hne, M, hM⟩ := h3 E N f hc
  have hdiff : Differentiable ℂ (ModularForm.L (two_pos : (0 : ℤ) < 2) f) :=
    CuspForm.differentiable_L _ f
  intro D s
  refine ⟨ModularForm.L (two_pos : (0 : ℤ) < 2) f, a, ⟨?_, ?_⟩,
    meromorphicOrderAt_of_taylor hdiff hlow hne, M, hM⟩
  · exact fun z ↦ (hdiff.analyticAt z).meromorphicAt
  · intro z hz
    exact eq_LSeries_of_summable (h1 E) hdiff
      (fun w hw ↦ hecke_eq_dirichlet_of_two_lt
        (CongruenceSubgroup.strictWidthInfty_Gamma0 N) f _ hc hw) hz

end OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1
