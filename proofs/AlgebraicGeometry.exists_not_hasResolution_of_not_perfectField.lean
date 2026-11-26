import FormalConjectures.Wikipedia.ResolutionOfSingularities
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.Polynomial.Taylor

/-! The spectrum of an inseparable simple extension cannot admit a smooth resolution. -/

open AlgebraicGeometry CategoryTheory Polynomial

universe u

private theorem not_formallySmooth_adjoinRoot_of_derivative_zero {k : Type*} [Field k]
    {f : k[X]} (hf : Irreducible f) (hder : derivative f = 0) :
    ¬ Algebra.FormallySmooth k (AdjoinRoot f) := by
  let π := AdjoinRoot.mkₐ f
  let J := RingHom.ker π.toRingHom
  let q : k[X] →ₐ[k] k[X] ⧸ J ^ 2 := Ideal.Quotient.mkₐ k _
  intro hs
  obtain ⟨s, hs⟩ := (Algebra.FormallySmooth.iff_split_surjection π
    AdjoinRoot.mk_surjective).mp hs
  let x := q X
  let e := s (AdjoinRoot.root f) - x
  have he : e ∈ RingHom.ker π.kerSquareLift.toRingHom := by
    change π.kerSquareLift (s (AdjoinRoot.root f) - q X) = 0
    rw [map_sub, sub_eq_zero]
    exact (DFunLike.congr_fun hs (AdjoinRoot.root f)).trans (π.kerSquareLift_mk X).symm
  have he2 : e ^ 2 = 0 := by
    have h := Ideal.pow_mem_pow he 2
    simpa only [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square, Ideal.mem_bot] using h
  have hroot : aeval (x + e) f = 0 := by
    have hx : x + e = s (AdjoinRoot.root f) := by
      rw [add_comm, show e = s (AdjoinRoot.root f) - x from rfl, sub_add_cancel]
    rw [hx]
    exact AdjoinRoot.aeval_algHom_eq_zero f s
  rw [aeval_add_of_sq_eq_zero f x e he2, hder, map_zero, zero_mul, add_zero] at hroot
  have heq : aeval x = q := by apply Polynomial.algHom_ext; simp [x]
  rw [heq] at hroot
  have hm : f ∈ J ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp hroot
  have hJ : J = Ideal.span {f} := by
    ext a
    exact (AdjoinRoot.mk_eq_zero (f := f)).trans Ideal.mem_span_singleton.symm
  rw [hJ, Ideal.span_singleton_pow] at hm
  have hdiv : f ^ 2 ∣ f ^ 1 := by simpa using Ideal.mem_span_singleton.mp hm
  have hle := (pow_dvd_pow_iff hf.ne_zero hf.not_isUnit).mp hdiv
  omega

private theorem smooth_of_resolution_on_subsingleton {S X : Scheme.{u}} [Subsingleton X] [Nonempty X]
    (s : X ⟶ S) (h : Scheme.HasResolution s) : Smooth s := by
  obtain ⟨Y, f, _, _, hs, g, hg⟩ := h
  have ht : g.target = ⊤ := by
    obtain ⟨x, hx⟩ := g.dense_target.nonempty
    apply top_unique
    intro y _
    change y ∈ (g.target : Set X)
    simpa only [Subsingleton.elim y x] using hx
  have hι : IsIso g.target.ι := by
    rw [ht, ← Scheme.topIso_hom]
    infer_instance
  have hcomp : Smooth (g.iso.hom ≫ g.target.ι ≫ s) := by
    have heq : (g.iso.hom ≫ g.target.ι) = (g.source.ι ≫ f) := by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hg
    rw [← Category.assoc, heq, Category.assoc]
    infer_instance
  have hfull : Smooth (inv g.target.ι ≫ g.iso.inv ≫ g.iso.hom ≫ g.target.ι ≫ s) := by
    infer_instance
  simpa only [Iso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc] using hfull

theorem OMA.solution : type_of% @AlgebraicGeometry.exists_not_hasResolution_of_not_perfectField := by
  intro k _ hk
  classical
  have hx : ∃ p : k[X], Irreducible p ∧ p.derivative = 0 := by
    by_contra! h
    exact hk ⟨fun {p} hp ↦ (separable_iff_derivative_ne_zero hp).mpr (h p hp)⟩
  obtain ⟨p, hp, hderiv⟩ := hx
  let : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let X := Spec (CommRingCat.of L)
  let s : X ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hft : LocallyOfFiniteType s :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine ⟨X, s, inferInstance, hft, inferInstance, inferInstance, ?_, ?_⟩
  · change topologicalKrullDim (PrimeSpectrum L) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  · intro h
    have : Subsingleton X := inferInstanceAs (Subsingleton (PrimeSpectrum L))
    have hsm : Smooth s := smooth_of_resolution_on_subsingleton s h
    have hAlg : Algebra.Smooth k L := RingHom.smooth_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
    exact not_formallySmooth_adjoinRoot_of_derivative_zero hp hderiv (inferInstance : Algebra.FormallySmooth k L)