import FormalConjectures.Millennium.RiemannHypothesis

/-! An inverse-series criterion for the Dedekind zeta function.

The open disks of radius `3/2` centered at `2 + t i` reach every point in
the right half of the critical strip. The inverse germ can be computed in
the half-plane of absolute convergence. Its radius bound is the unresolved
estimate. Removing the point `1` preserves the connectedness of each disk.
-/

namespace OMA.R_ERH_extended_riemann_hypothesis_R1

open Complex Filter Set NumberField
open scoped Topology ENNReal NumberField

/-- Zero reflection in the critical strip, as supplied by the functional equation. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Z : ℂ → ℂ), ERH.IsDedekindZeta K Z →
    ∀ z : ℂ, 0 < z.re → z.re < 1 / 2 → Z z = 0 → Z (1 - z) = 0

/-- Radius bound for the power series of the reciprocal of the regularized
Dirichlet series. The germ identity only uses values near real part two. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (t : ℝ),
    let c : ℂ := ⟨2, t⟩
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      ENNReal.ofReal (3 / 2) ≤ p.radius ∧
      ∀ᶠ z in 𝓝 c, ((z - 1) * NumberField.dedekindZeta K z) * p.sum (z - c) = 1

/-- A number-field isomorphism preserves the count of integral ideals of each norm. -/
theorem dedekindZeta_eq_of_ringEquiv {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] (e : K ≃+* L) : dedekindZeta K = dedekindZeta L := by
  let r : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  let i : Ideal (𝓞 K) ≃ Ideal (𝓞 L) := (Ideal.relIsoOfBijective r.toRingHom r.bijective).symm.toEquiv
  have hnorm (I : Ideal (𝓞 K)) : Ideal.absNorm I = Ideal.absNorm (i I) :=
    Nat.card_congr (Ideal.quotientEquiv I (i I) r rfl).toEquiv
  have hcard (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {J : Ideal (𝓞 L) // Ideal.absNorm J = n} :=
    Nat.card_congr (i.subtypeEquiv fun I => by rw [hnorm I])
  funext z
  simp only [dedekindZeta, hcard]

theorem punctured_disk_preconnected (c a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball c r \ {a}) := by
  let e := OpenPartialHomeomorph.univBall c r
  have hi : Function.Injective e := fun _ _ h => e.injOn (by simp [e]) (by simp [e]) h
  have hcount : (e ⁻¹' {a}).Countable := (countable_singleton a).preimage hi
  have hconn := hcount.isConnected_compl_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
  have hrange : Set.range e = Metric.ball c r := by
    simpa only [e, OpenPartialHomeomorph.univBall_source, image_univ,
      OpenPartialHomeomorph.univBall_target c hr] using e.image_source_eq_target
  have himage : e '' (e ⁻¹' {a})ᶜ = Metric.ball c r \ {a} := by
    rw [← preimage_compl, image_preimage_eq_inter_range, hrange, inter_comm]
    rfl
  rw [← himage]
  exact hconn.isPreconnected.image e (OpenPartialHomeomorph.continuous_univBall c r).continuousOn

theorem right_nonzero (K : Type) [Field K] [NumberField K]
    (Z : ℂ → ℂ) (hZ : ERH.IsDedekindZeta K Z) (hseries : H2)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs' : s.re < 1) : Z s ≠ 0 := by
  let c : ℂ := ⟨2, s.im⟩
  obtain ⟨p, hr, hp⟩ := hseries K s.im
  let U := Metric.ball c (3 / 2 : ℝ) \ {(1 : ℂ)}
  have hsub : U ⊆ Metric.eball c p.radius := by
    apply Set.Subset.trans Set.sdiff_subset
    rw [← Metric.eball_ofReal]
    exact Metric.eball_subset_eball hr
  have hg : AnalyticOnNhd ℂ (fun z => p.sum (z - c)) (Metric.eball c p.radius) := by
    simpa using p.analyticOnNhd.comp_sub c
  have hZA : AnalyticOnNhd ℂ Z U :=
    (hZ.1.analyticOnNhd isOpen_compl_singleton).mono fun _ hz => hz.2
  have hprod : AnalyticOnNhd ℂ (fun z => ((z - 1) * Z z) * p.sum (z - c)) U :=
    (((analyticOnNhd_id.sub analyticOnNhd_const).mul hZA).mul (hg.mono hsub))
  have hgerm : (fun z => ((z - 1) * Z z) * p.sum (z - c)) =ᶠ[𝓝 c] (fun _ => (1 : ℂ)) := by
    have hre : ∀ᶠ z in 𝓝 c, 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [c])
    filter_upwards [hre, hp] with z hz hprod
    simpa only [hZ.2 z hz] using hprod
  have hcU : c ∈ U := by
    refine ⟨Metric.mem_ball_self (by norm_num), ?_⟩
    intro hc
    have heq : (2 : ℝ) = 1 := congrArg Complex.re (Set.mem_singleton_iff.mp hc)
    norm_num at heq
  have hall := hprod.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (punctured_disk_preconnected c 1 (by norm_num)) hcU hgerm
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs'
  have hsU : s ∈ U := by
    refine ⟨?_, hs1⟩
    have hdiff : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    change dist s c < 3 / 2
    rw [dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  intro hzero
  have hone : ((s - 1) * Z s) * p.sum (s - c) = 1 := hall hsU
  simp [hzero] at hone

theorem main : H1 → H2 → type_of% @ERH.extended_riemann_hypothesis := by
  intro hreflect hseries K _ _ Z hZ s hpos hlt hz
  let f : K →ₐ[ℚ] ℂ := IsAlgClosed.lift (R := ℚ)
  let L := f.fieldRange
  let e : K ≃+* L := f.equivFieldRange.toRingEquiv
  let _ : NumberField L := NumberField.of_ringEquiv K L e
  have hL : ERH.IsDedekindZeta L Z :=
    ⟨hZ.1, fun z h => (hZ.2 z h).trans (congrFun (dedekindZeta_eq_of_ringEquiv e) z)⟩
  rcases lt_trichotomy s.re (1 / 2) with h | heq | h
  · have hright : 1 / 2 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hstrip : (1 - s).re < 1 := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact ((right_nonzero L Z hL hseries hright hstrip) (hreflect L Z hL s hpos h hz)).elim
  · exact heq
  · exact ((right_nonzero L Z hL hseries h hlt) hz).elim

end OMA.R_ERH_extended_riemann_hypothesis_R1
