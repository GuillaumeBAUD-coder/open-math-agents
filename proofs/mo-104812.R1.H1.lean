import OMAReductions.R_mo_104812_R1
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Proof of `mo-104812.R1.H1`

Proves that for any compact topological space `X`, if `I` and `J` are intersections of maximal
ideals in `C(X, ℝ)`, then `I ⊔ J` is also an intersection of maximal ideals in `C(X, ℝ)`.

Step 1: Quotient `X` by the equivalence relation `x ~ y ↔ ∀ f : C(X, ℝ), f x = f y`, giving the
quotient `Y` the topology induced by the evaluation map `Y → (C(X, ℝ) → ℝ)`. Then `Y` is compact
(as the continuous image of `X`) and `T2Space` (as it injects continuously into `C(X, ℝ) → ℝ`),
hence `NormalSpace Y`, and `C(Y, ℝ) ≃+* C(X, ℝ)` via pullback.

Step 2: On a compact space `Y`, every maximal ideal of `C(Y, ℝ)` is of the form
`M_y = {g | g y = 0}` (otherwise compactness yields finitely many elements whose sum of squares is
everywhere positive, hence a unit). Thus `I = I(A)` and `J = I(B)` for closed subsets `A, B ⊆ Y`.

Step 3: For any `f ∈ I(A ∩ B)`, the function equal to `0` on `A` and `f` on `B` is continuous on
the closed set `A ∪ B`. By the Tietze extension theorem (`ContinuousMap.exists_restrict_eq`) on the
normal space `Y`, it extends to `g ∈ C(Y, ℝ)` with `g ∈ I(A) = I` and `f - g ∈ I(B) = J`. Hence
`I ⊔ J = I(A ∩ B) = sInf {M_y | y ∈ A ∩ B}` is an intersection of maximal ideals.
-/

namespace Mo104812R1H1Proof

open OMA.S_mo_104812

private def evalHom {Y : Type*} [TopologicalSpace Y] (y : Y) : C(Y, ℝ) →+* ℝ where
  toFun f := f y
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def evalIdeal {Y : Type*} [TopologicalSpace Y] (y : Y) : Ideal C(Y, ℝ) :=
  RingHom.ker (evalHom y)

private lemma mem_evalIdeal {Y : Type*} [TopologicalSpace Y] (y : Y) (f : C(Y, ℝ)) :
    f ∈ evalIdeal y ↔ f y = 0 := Iff.rfl

private lemma evalIdeal_isMaximal {Y : Type*} [TopologicalSpace Y] (y : Y) :
    (evalIdeal y).IsMaximal := by
  have hsurj : Function.Surjective (evalHom (Y := Y) y) := fun r =>
    ⟨ContinuousMap.const Y r, rfl⟩
  exact RingHom.ker_isMaximal_of_surjective _ hsurj

private lemma exists_eq_evalIdeal_of_isMaximal {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {M : Ideal C(Y, ℝ)} (hM : M.IsMaximal) : ∃ y : Y, M = evalIdeal y := by
  have hex : ∃ y : Y, ∀ f ∈ M, f y = 0 := by
    by_contra hno
    push Not at hno
    -- For each y, pick f_y ∈ M with f_y y ≠ 0; open cover by {x | f_y x ≠ 0}
    choose f hfM hfy using hno
    have hopen : ∀ y : Y, IsOpen {x : Y | f y x ≠ 0} := fun y =>
      isOpen_ne_fun (f y).continuous continuous_const
    have hcov : (Set.univ : Set Y) ⊆ ⋃ y : Y, {x : Y | f y x ≠ 0} := fun y _ =>
      Set.mem_iUnion.mpr ⟨y, hfy y⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
    let s : C(Y, ℝ) := ∑ y ∈ t, (f y) ^ 2
    have hsM : s ∈ M := by
      refine M.sum_mem fun y _ => ?_
      rw [sq]
      exact M.mul_mem_left _ (hfM y)
    have hs_pos : ∀ x : Y, 0 < s x := fun x => by
      have hx : x ∈ ⋃ y ∈ t, {z : Y | f y z ≠ 0} := ht (Set.mem_univ x)
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
      obtain ⟨y₀, hy₀, hne⟩ := hx
      have hsum_eval : s x = ∑ y ∈ t, (f y x) ^ 2 := by
        dsimp [s]
        simp
      rw [hsum_eval]
      exact Finset.sum_pos' (fun y _ => sq_nonneg _) ⟨y₀, hy₀, sq_pos_of_ne_zero hne⟩
    let sInv : C(Y, ℝ) :=
      ⟨fun x => (s x)⁻¹, Continuous.inv₀ s.continuous (fun x => (hs_pos x).ne')⟩
    have h1 : sInv * s = 1 := by
      ext x
      exact inv_mul_cancel₀ (hs_pos x).ne'
    have h1M : (1 : C(Y, ℝ)) ∈ M := by
      rw [← h1]
      exact M.mul_mem_left sInv hsM
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M h1M isUnit_one)
  obtain ⟨y, hy⟩ := hex
  have hle : M ≤ evalIdeal y := fun f hf => hy f hf
  exact ⟨y, hM.eq_of_le (evalIdeal_isMaximal y).ne_top hle⟩

private lemma zeroSet_isClosed {Y : Type*} [TopologicalSpace Y] (I : Ideal C(Y, ℝ)) :
    IsClosed {y : Y | ∀ f ∈ I, f y = 0} := by
  have heq : {y : Y | ∀ f ∈ I, f y = 0} = ⋂ f ∈ I, {y : Y | f y = 0} := by
    ext y; simp
  rw [heq]
  exact isClosed_biInter fun f _ => isClosed_eq f.continuous continuous_const

private lemma ideal_eq_zeroIdeal_of_isInfOfMaximal {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] {I : Ideal C(Y, ℝ)} (hI : IsInfOfMaximal I) :
    ∀ f : C(Y, ℝ), f ∈ I ↔ ∀ y ∈ {y : Y | ∀ g ∈ I, g y = 0}, f y = 0 := by
  obtain ⟨S, hSmax, rfl⟩ := hI
  intro f
  constructor
  · intro hf y hy
    exact hy f hf
  · intro hvan
    rw [Ideal.mem_sInf]
    intro M hMS
    obtain ⟨y, rfl⟩ := exists_eq_evalIdeal_of_isMaximal (hSmax M hMS)
    exact hvan y fun g hg => (Ideal.mem_sInf.mp hg) hMS

private lemma compact_normal_case (Y : Type*) [TopologicalSpace Y] [CompactSpace Y]
    [NormalSpace Y] (I J : Ideal C(Y, ℝ)) (hI : IsInfOfMaximal I) (hJ : IsInfOfMaximal J) :
    IsInfOfMaximal (I ⊔ J) := by
  classical
  set A : Set Y := {y : Y | ∀ g ∈ I, g y = 0}
  set B : Set Y := {y : Y | ∀ g ∈ J, g y = 0}
  have hA : IsClosed A := zeroSet_isClosed I
  have hB : IsClosed B := zeroSet_isClosed J
  have hI_iff := ideal_eq_zeroIdeal_of_isInfOfMaximal hI
  have hJ_iff := ideal_eq_zeroIdeal_of_isInfOfMaximal hJ
  refine ⟨(fun y : Y => evalIdeal y) '' (A ∩ B), ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact evalIdeal_isMaximal y
  · apply le_antisymm
    · rw [le_sInf_iff]
      rintro _ ⟨y, ⟨hyA, hyB⟩, rfl⟩
      exact sup_le (fun g hg => hyA g hg) (fun g hg => hyB g hg)
    · intro f hf
      have hfAB : ∀ y ∈ A ∩ B, f y = 0 := fun y hy =>
        (Ideal.mem_sInf.mp hf) ⟨y, hy, rfl⟩
      -- Define continuous function on closed set A ∪ B: 0 on A, f on B
      let uFun : (A ∪ B : Set Y) → ℝ := fun y =>
        if y.1 ∈ A then 0 else f y.1
      have hu_cont : Continuous uFun := by
        rw [← continuousOn_univ]
        -- Express A ∪ B subtype as union of two closed subsets in subtype
        let sA : Set (A ∪ B : Set Y) := Subtype.val ⁻¹' A
        let sB : Set (A ∪ B : Set Y) := Subtype.val ⁻¹' B
        have hsA : IsClosed sA := hA.preimage continuous_subtype_val
        have hsB : IsClosed sB := hB.preimage continuous_subtype_val
        have hunion : (Set.univ : Set (A ∪ B : Set Y)) = sA ∪ sB := by
          ext ⟨y, hy⟩
          simp only [Set.mem_univ, Set.mem_union, Set.mem_preimage, sA, sB, true_iff]
          exact hy
        rw [hunion]
        refine ContinuousOn.union_of_isClosed ?_ ?_ hsA hsB
        · refine (continuousOn_const (c := (0 : ℝ))).congr fun y hy => ?_
          dsimp only [uFun]
          exact if_pos hy
        · refine (f.continuous.comp continuous_subtype_val).continuousOn.congr fun y hy => ?_
          dsimp only [uFun, Function.comp_apply]
          by_cases hyA : y.1 ∈ A
          · rw [if_pos hyA, hfAB y.1 ⟨hyA, hy⟩]
          · rw [if_neg hyA]
      let u : C((A ∪ B : Set Y), ℝ) := ⟨uFun, hu_cont⟩
      obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (hA.union hB) u
      have hgA : ∀ y ∈ A, g y = 0 := fun y hy => by
        have h1 := congrArg (fun k : C((A ∪ B : Set Y), ℝ) => k ⟨y, Or.inl hy⟩) hg
        simpa [u, uFun, hy] using h1
      have hgB : ∀ y ∈ B, (f - g) y = 0 := fun y hy => by
        have h1 := congrArg (fun k : C((A ∪ B : Set Y), ℝ) => k ⟨y, Or.inr hy⟩) hg
        have hgy : g y = f y := by
          by_cases hyA : y ∈ A
          · have h2 : g y = 0 := by simpa [u, uFun, hyA] using h1
            rw [h2, hfAB y ⟨hyA, hy⟩]
          · simpa [u, uFun, hyA] using h1
        change f y - g y = 0
        rw [hgy, sub_self]
      have hgI : g ∈ I := (hI_iff g).mpr hgA
      have hfgJ : f - g ∈ J := (hJ_iff (f - g)).mpr hgB
      have hsum : g + (f - g) = f := by ring
      rw [← hsum]
      exact Submodule.add_mem_sup hgI hfgJ

private lemma isInfOfMaximal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {I : Ideal R} (hI : IsInfOfMaximal I) :
    IsInfOfMaximal (Ideal.map e.toRingHom I) := by
  obtain ⟨T, hT, rfl⟩ := hI
  refine ⟨(fun M : Ideal R => Ideal.map e.toRingHom M) '' T, ?_, ?_⟩
  · rintro _ ⟨M, hMT, rfl⟩
    have : M.IsMaximal := hT M hMT
    exact Ideal.map_isMaximal_of_equiv e
  · apply le_antisymm
    · rw [le_sInf_iff]
      rintro _ ⟨M, hMT, rfl⟩
      exact Ideal.map_mono (sInf_le hMT)
    · intro x hx
      have hpre : e.symm x ∈ sInf T := by
        rw [Ideal.mem_sInf]
        intro M hMT
        have hmem := (Ideal.mem_sInf.mp hx) ⟨M, hMT, rfl⟩
        rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hmem
        obtain ⟨y, hyM, hyx⟩ := hmem
        have : e.symm x = y := e.symm_apply_eq.mpr hyx.symm
        rwa [this]
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
      exact ⟨e.symm x, hpre, e.apply_symm_apply x⟩

end Mo104812R1H1Proof

theorem OMA.solution : OMA.R_mo_104812_R1.H1 := by
  intro X _ _ I J hI hJ
  -- Quotient X by C(X, ℝ)-indistinguishability
  let r : Setoid X :=
    { r := fun x y => ∀ f : C(X, ℝ), f x = f y
      iseqv :=
        ⟨fun _ _ => rfl, fun h f => (h f).symm, fun h1 h2 f => (h1 f).trans (h2 f)⟩ }
  let Y := Quotient r
  let ev : Y → (C(X, ℝ) → ℝ) := fun y f =>
    Quotient.liftOn y (fun x => f x) (fun _ _ h => h f)
  let : TopologicalSpace Y := TopologicalSpace.induced ev inferInstance
  have hev_inj : Function.Injective ev := by
    intro y₁ y₂ h
    induction y₁ using Quotient.ind with
    | _ x₁ =>
      induction y₂ using Quotient.ind with
      | _ x₂ =>
        exact Quotient.sound fun f => congrFun h f
  have hq_cont : Continuous (Quotient.mk r : X → Y) := by
    rw [continuous_induced_rng]
    exact continuous_pi fun f => f.continuous
  have : CompactSpace Y := by
    refine ⟨?_⟩
    have himg : (Set.univ : Set Y) = (Quotient.mk r) '' Set.univ := by
      ext y
      simp only [Set.mem_univ, Set.mem_image, true_and, true_iff]
      exact Quotient.exists_rep y
    rw [himg]
    exact isCompact_univ.image hq_cont
  have : T2Space Y := by
    refine ⟨fun y₁ y₂ hne => ?_⟩
    obtain ⟨u, v, hu, hv, hy₁, hy₂, hdisj⟩ := t2_separation (fun h => hne (hev_inj h))
    exact ⟨ev ⁻¹' u, ev ⁻¹' v, hu.preimage continuous_induced_dom, hv.preimage continuous_induced_dom,
      hy₁, hy₂, hdisj.preimage ev⟩
  have : NormalSpace Y := inferInstance
  let qMap : C(X, Y) := ⟨Quotient.mk r, hq_cont⟩
  let pull : C(Y, ℝ) →+* C(X, ℝ) :=
    { toFun := fun g => g.comp qMap
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hpull_bij : Function.Bijective pull := by
    constructor
    · intro g₁ g₂ h
      ext y
      obtain ⟨x, rfl⟩ := Quotient.exists_rep y
      exact congrArg (fun k : C(X, ℝ) => k x) h
    · intro f
      refine ⟨⟨fun y => ev y f, (continuous_apply f).comp (continuous_induced_dom (f := ev))⟩, ?_⟩
      ext x
      rfl
  let e : C(Y, ℝ) ≃+* C(X, ℝ) := RingEquiv.ofBijective pull hpull_bij
  let I' : Ideal C(Y, ℝ) := Ideal.map e.symm.toRingHom I
  let J' : Ideal C(Y, ℝ) := Ideal.map e.symm.toRingHom J
  have hI' : OMA.S_mo_104812.IsInfOfMaximal I' :=
    Mo104812R1H1Proof.isInfOfMaximal_of_ringEquiv e.symm hI
  have hJ' : OMA.S_mo_104812.IsInfOfMaximal J' :=
    Mo104812R1H1Proof.isInfOfMaximal_of_ringEquiv e.symm hJ
  have hsup' : OMA.S_mo_104812.IsInfOfMaximal (I' ⊔ J') :=
    Mo104812R1H1Proof.compact_normal_case Y I' J' hI' hJ'
  have hmap_sup := Mo104812R1H1Proof.isInfOfMaximal_of_ringEquiv e hsup'
  have heq : Ideal.map e.toRingHom (I' ⊔ J') = I ⊔ J := by
    rw [Ideal.map_sup]
    have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ :=
      RingHom.ext fun x => e.apply_symm_apply x
    have h1 : Ideal.map e.toRingHom I' = I := by
      dsimp only [I']
      rw [Ideal.map_map, hcomp, Ideal.map_id]
    have h2 : Ideal.map e.toRingHom J' = J := by
      dsimp only [J']
      rw [Ideal.map_map, hcomp, Ideal.map_id]
    rw [h1, h2]
  rwa [heq] at hmap_sup
