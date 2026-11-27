import OMAReductions.R_ERH_extended_riemann_hypothesis_R1
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-! Zero reflection from the inverse Mellin kernel of the completed Dirichlet series.
The two inputs concern only the Dirichlet series on the right of one and a function
on the positive real axis. The field of rational numbers is treated directly.
-/

namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1

open Complex Filter Set NumberField NumberField.InfinitePlace MeasureTheory Asymptotics
open scoped NumberField Topology

/-- Mellin inversion and decay for the completed Dirichlet series in degree at least two. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], 1 < Module.finrank ℚ K →
    let A : ℂ → ℂ := fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
    let f := mellinInv 2 (fun s => A s * dedekindZeta K s)
    LocallyIntegrableOn f (Ioi 0) ∧ (∀ r : ℝ, f =O[atTop] (fun x : ℝ => x ^ r)) ∧
      ∀ s : ℂ, 1 < s.re → HasMellin f s (A s * dedekindZeta K s)

/-- Poisson inversion up to a constant for the same explicitly specified real-variable kernel. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], 1 < Module.finrank ℚ K →
    let A : ℂ → ℂ := fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
    let f := mellinInv 2 (fun s => A s * dedekindZeta K s)
    ∃ c : ℂ, ∀ x : ℝ, 0 < x → f (1 / x) + c = (x : ℂ) * (f x + c)

theorem zeros_reflect_of_kernel {K : Type*} [Field K] [NumberField K] {Z A : ℂ → ℂ}
    (hZ : ERH.IsDedekindZeta K Z) (hA : ∀ s : ℂ, 0 < s.re → A s ≠ 0)
    (hInv : Differentiable ℂ (fun s => (A s)⁻¹)) {f : ℝ → ℂ}
    (hlocal : LocallyIntegrableOn f (Ioi 0)) (hdecay : ∀ r : ℝ, f =O[atTop] (fun x : ℝ => x ^ r))
    (hm : ∀ s : ℂ, 1 < s.re → HasMellin f s (A s * dedekindZeta K s))
    {c : ℂ} (hinv : ∀ x : ℝ, 0 < x → f (1 / x) + c = (x : ℂ) * (f x + c))
    {z : ℂ} (hpos : 0 < z.re) (hlt : z.re < 1) (hz : Z z = 0) : Z (1 - z) = 0 := by
  let P : WeakFEPair ℂ := {
    f := fun x => f x + c, g := fun x => f x + c, f₀ := c, g₀ := c, k := 1, ε := 1
    hk := zero_lt_one, hε := one_ne_zero
    hf_int := hlocal.add (locallyIntegrableOn_const c), hg_int := hlocal.add (locallyIntegrableOn_const c)
    hf_top := fun r => by simpa using hdecay r, hg_top := fun r => by simpa using hdecay r
    h_feq := fun x hx => by simpa using hinv x hx }
  have hsymm : P.symm = P := by simp [P, WeakFEPair.symm]
  let U : Set ℂ := ({0, 1} : Set ℂ)ᶜ
  have hconn : IsConnected U := Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    ((countable_singleton (1 : ℂ)).insert 0)
  have hZA : AnalyticOnNhd ℂ Z U :=
    (hZ.1.analyticOnNhd isOpen_compl_singleton).mono (by intro w hw; simp_all [U])
  have hPA : AnalyticOnNhd ℂ P.Λ U := by
    have hopen : IsOpen U := (((finite_singleton (1 : ℂ)).insert 0).isClosed).isOpen_compl
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro w hw
    have hw' : w ≠ 0 ∧ w ≠ 1 := by simpa [U] using hw
    exact (P.differentiableAt_Λ (Or.inl hw'.1) (Or.inl (by simpa [P] using hw'.2))).differentiableWithinAt
  have heq : EqOn Z (fun s => (A s)⁻¹ * P.Λ s) U := by
    have hIA : AnalyticOnNhd ℂ (fun s => (A s)⁻¹) U :=
      (hInv.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
    apply hZA.eqOn_of_preconnected_of_eventuallyEq (hIA.mul hPA)
      hconn.isPreconnected (show (2 : ℂ) ∈ U by norm_num [U])
    have hnh : ∀ᶠ w : ℂ in 𝓝 2, 1 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnh] with w hw
    have hM : mellin f w = P.Λ w := by simpa [P] using (P.hasMellin (s := w) (by simpa [P] using hw)).2
    rw [hZ.2 w hw, ← hM, (hm w hw).2, inv_mul_cancel_left₀ (hA w (by linarith))]
  have memU {w : ℂ} (hw : 0 < w.re) (hw' : w.re < 1) : w ∈ U := by
    simp only [U, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => by simp [h] at hw, fun h => by simp [h] at hw'⟩
  have hzw := (heq (memU hpos hlt)).symm.trans hz
  have hΛ : P.Λ z = 0 := (mul_eq_zero.mp hzw).resolve_left (inv_ne_zero (hA z hpos))
  have hreflect : P.Λ (1 - z) = P.Λ z := by
    simpa only [hsymm, show P.k = 1 from rfl, show P.ε = 1 from rfl, ofReal_one, one_smul]
      using P.functional_equation z
  have hw : 0 < (1 - z).re := by rw [sub_re, one_re]; linarith
  have hw' : (1 - z).re < 1 := by rw [sub_re, one_re]; linarith
  exact (heq (memU hw hw')).trans (by dsimp only; rw [hreflect, hΛ, mul_zero])

theorem int_ideal_of_norm (I : Ideal ℤ) : I = Ideal.span {(Ideal.absNorm I : ℤ)} := by
  obtain ⟨a, rfl⟩ := (inferInstance : I.IsPrincipal).principal
  rw [Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply, Int.span_natAbs]

theorem int_ideals_of_norm_card (n : ℕ) :
    Nat.card {I : Ideal ℤ // Ideal.absNorm I = n} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨Ideal.span {(n : ℤ)}, by simp⟩, ?_⟩
  intro J
  apply Subtype.ext
  simpa only [J.property] using int_ideal_of_norm J.val

theorem rational_ideals_of_norm_card (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  let e := Rat.ringOfIntegersEquiv
  let i : Ideal (𝓞 ℚ) ≃ Ideal ℤ := (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.toEquiv
  have hi (J : Ideal (𝓞 ℚ)) : Ideal.absNorm J = Ideal.absNorm (i J) :=
    Nat.card_congr (Ideal.quotientEquiv J (i J) e rfl).toEquiv
  exact (Nat.card_congr (i.subtypeEquiv (p := fun J => Ideal.absNorm J = n)
    (q := fun J => Ideal.absNorm J = n) (fun J => by rw [hi J]))).trans (int_ideals_of_norm_card n)

theorem zeta_eq_in_half_plane {z : ℂ} (hz : 1 < z.re) : dedekindZeta ℚ z = riemannZeta z := by
  calc dedekindZeta ℚ z = LSeries (1 : ℕ → ℂ) z := by
         apply LSeries_congr
         intro n _
         simp [rational_ideals_of_norm_card]
       _ = riemannZeta z := LSeries_one_eq_riemannZeta hz

theorem agrees_off_one {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta ℚ Z) :
    Set.EqOn Z riemannZeta ({1}ᶜ : Set ℂ) := by
  apply (hZ.1.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    analyticOn_riemannZeta
    (isConnected_compl_singleton_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  have hneigh : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hneigh.mono fun z hz => (hZ.2 z hz).trans (zeta_eq_in_half_plane hz)

theorem zeros_reflect {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta ℚ Z) {z : ℂ}
    (hpos : 0 < z.re) (hlt : z.re < 1) (hz : Z z = 0) : Z (1 - z) = 0 := by
  have h1 : z ≠ 1 := by rintro rfl; norm_num at hlt
  have h1' : 1 - z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hnat (n : ℕ) : z ≠ -(n : ℂ) := by
    rintro rfl
    simp at hpos
    exact (not_lt_of_ge (Nat.cast_nonneg n : (0 : ℝ) ≤ n)) hpos
  rw [agrees_off_one hZ h1', riemannZeta_one_sub hnat h1, ← agrees_off_one hZ h1, hz, mul_zero]

/-- A degree-one number field has the same zeta continuations as the rational field. -/
theorem isDedekindZeta_rat_of_finrank_one {K : Type*} [Field K] [NumberField K]
    (hk : Module.finrank ℚ K = 1) {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z) :
    ERH.IsDedekindZeta ℚ Z := by
  have he : Function.Bijective (algebraMap ℚ K) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := ℚ) (E := K)).mp hk
  let e : ℚ ≃+* K := RingEquiv.ofBijective (algebraMap ℚ K) he
  have hzeta := OMA.R_ERH_extended_riemann_hypothesis_R1.dedekindZeta_eq_of_ringEquiv e
  exact ⟨hZ.1, fun z hz => (hZ.2 z hz).trans (congrFun hzeta z).symm⟩

theorem zeros_reflect_of_finrank_one {K : Type*} [Field K] [NumberField K]
    (hk : Module.finrank ℚ K = 1) {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z) {z : ℂ}
    (hpos : 0 < z.re) (hlt : z.re < 1) (hz : Z z = 0) : Z (1 - z) = 0 :=
  zeros_reflect (isDedekindZeta_rat_of_finrank_one hk hZ) hpos hlt hz

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1.H1 := by
  intro hM hP K _ _ Z hZ z hpos hhalf hz
  have hlt : z.re < 1 := by linarith
  by_cases hK : Module.finrank ℚ K = 1
  · exact zeros_reflect_of_finrank_one hK hZ hpos hlt hz
  have hdeg : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  let A : ℂ → ℂ := fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
    Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
  have hA (s : ℂ) (hs : 0 < s.re) : A s ≠ 0 := by
    have hs' : 0 < (s + 1).re := by rw [add_re, one_re]; linarith
    have hC : Gammaℂ s ≠ 0 := by rw [← Gammaℝ_mul_Gammaℝ_add_one]; exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos hs')
    exact mul_ne_zero (mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs))) (pow_ne_zero _ hC)
  have hAinv : Differentiable ℂ (fun s => (A s)⁻¹) := by
    simp only [A, mul_inv, ← inv_pow, ← Complex.exp_neg]
    apply Differentiable.mul _ (differentiable_Gammaℂ_inv.pow _)
    apply Differentiable.mul _ (differentiable_Gammaℝ_inv.pow _)
    fun_prop
  obtain ⟨hlocal, hdecay, hm⟩ := hM K hdeg
  obtain ⟨c, hinv⟩ := hP K hdeg
  exact zeros_reflect_of_kernel hZ hA hAinv hlocal hdecay hm hinv hpos hlt hz

end OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1

