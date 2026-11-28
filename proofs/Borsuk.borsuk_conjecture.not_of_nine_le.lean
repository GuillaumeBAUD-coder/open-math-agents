import FormalConjectures.Wikipedia.BorsukConjecture
import Mathlib
-- Credit: @marcusbuffett (R1 reduction)
-- Credit: authors of R1.H1.R1 and its leaves, and of R1.H2, are not named in the piece files

section
namespace OMA.R1
open Metric Bornology Borsuk Finset
open scoped EuclideanGeometry
def H1 : Prop :=
  ∃ X : Set (EuclideanSpace ℝ (Fin 9)), X.Nontrivial ∧
    (∀ x ∈ X, ‖x‖^2 = 3/4) ∧ ediam X = ENNReal.ofReal (Real.sqrt 2) ∧
    ¬ HasBorsukCover 10 X
def H2 : Prop :=
  ∀ k : ℕ, ∃ f : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin (9+k)),
    ∃ q : Fin k → EuclideanSpace ℝ (Fin (9+k)), Isometry f ∧
    (∀ i j, i ≠ j → dist (q i) (q j) = Real.sqrt 2) ∧
    (∀ x : EuclideanSpace ℝ (Fin 9), ‖x‖^2 = 3/4 → ∀ i, dist (f x) (q i) = Real.sqrt 2)
theorem main : H1 → H2 → type_of% @Borsuk.borsuk_conjecture.not_of_nine_le := by
  classical
  rintro ⟨X,hX,sphere,diamX,obstruction⟩ extension n hn hB
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨f,q,hf,apart,cross⟩ := extension k
  let D := ENNReal.ofReal (Real.sqrt 2)
  let Y := f '' X ∪ Set.range q
  have cross' (x) (hx : x ∈ X) (i) : edist (f x) (q i) = D := by
    rw [edist_dist, cross x (sphere x hx)]
  have apart' (i j) (h : i ≠ j) : edist (q i) (q j) = D := by
    rw [edist_dist, apart i j h]
  have upper : ediam Y ≤ D := by
    apply ediam_le
    rintro _ (⟨x,hx,rfl⟩ | ⟨i,rfl⟩) _ (⟨y,hy,rfl⟩ | ⟨j,rfl⟩)
    · rw [hf.edist_eq]
      exact (edist_le_ediam_of_mem hx hy).trans diamX.le
    · exact (cross' x hx j).le
    · rw [edist_comm]; exact (cross' y hy i).le
    · by_cases h : i = j
      · simp [h]
      · exact (apart' i j h).le
  have hbdd : IsBounded Y := isBounded_iff_ediam_ne_top.mpr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top upper)
  have hnt : Y.Nontrivial := (hX.image hf.injective).mono Set.subset_union_left
  obtain ⟨U,cover,small⟩ := hB Y hbdd hnt
  have hsmall (j) : ediam (U j) < D := (small j).trans_le upper
  have chosen (i : Fin k) : ∃ j, q i ∈ U j :=
    Set.mem_iUnion.mp (cover (Or.inr ⟨i,rfl⟩))
  choose color memColor using chosen
  have inj : Function.Injective color := by
    intro i j hij
    by_contra h
    have both : q i ∈ U (color j) := hij ▸ memColor i
    exact (hsmall _).not_ge ((apart' i j h) ▸ edist_le_ediam_of_mem both (memColor j))
  let L := (univ : Finset (Fin (9+k+1))) \ univ.image color
  have size : L.card = 10 := by
    dsimp [L]
    rw [card_sdiff_of_subset (subset_univ _), card_image_of_injective _ inj]
    simp; omega
  let e := Fintype.equivFinOfCardEq (show Fintype.card L = 10 by simpa using size)
  apply obstruction
  refine ⟨fun i => f ⁻¹' U (e.symm i).val, ?_, ?_⟩
  · intro x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (cover (Or.inl ⟨x,hx,rfl⟩))
    have hjL : j ∈ L := by
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      rintro hj'
      obtain ⟨i,_,rfl⟩ := mem_image.mp hj'
      exact (hsmall _).not_ge ((cross' x hx i) ▸ edist_le_ediam_of_mem hj (memColor i))
    exact Set.mem_iUnion.mpr ⟨e ⟨j,hjL⟩, by simpa using hj⟩
  · intro i
    rw [diamX, ← hf.ediam_image]
    exact (ediam_mono (Set.image_preimage_subset f _)).trans_lt (hsmall _)
end OMA.R1
end

namespace W4
namespace OMA
theorem dist_sq_append (k : ℕ) (u u' : Fin 9 → ℝ) (v v' : Fin k → ℝ) :
    dist (WithLp.toLp 2 (Fin.append u v) : EuclideanSpace ℝ (Fin (9 + k)))
        (WithLp.toLp 2 (Fin.append u' v')) ^ 2 =
      ∑ a, (u a - u' a) ^ 2 + ∑ l, (v l - v' l) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_add]
  simp only [PiLp.toLp_apply, Fin.append_left, Fin.append_right, Real.dist_eq, sq_abs]
theorem sum_delta_sq (k : ℕ) (i j : Fin k) (hij : i ≠ j) (t : ℝ) :
    ∑ l : Fin k, (((if l = i then (1 : ℝ) else 0) + t) - ((if l = j then (1 : ℝ) else 0) + t)) ^ 2
      = 2 := by
  have h : ∀ l : Fin k,
      (((if l = i then (1 : ℝ) else 0) + t) - ((if l = j then (1 : ℝ) else 0) + t)) ^ 2 =
        (if l = i then (1 : ℝ) else 0) + (if l = j then (1 : ℝ) else 0) := by
    intro l
    by_cases h1 : l = i
    · have h2 : ¬ l = j := fun h => hij (h1.symm.trans h)
      rw [if_pos h1, if_neg h2]
      ring
    · by_cases h2 : l = j
      · rw [if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib]
  simp
  norm_num
theorem sum_delta_t (k : ℕ) (i : Fin k) (t : ℝ) :
    ∑ l : Fin k, ((0 : ℝ) - ((if l = i then (1 : ℝ) else 0) + t)) ^ 2 =
      1 + 2 * t + (k : ℝ) * t ^ 2 := by
  have h : ∀ l : Fin k, ((0 : ℝ) - ((if l = i then (1 : ℝ) else 0) + t)) ^ 2 =
      (if l = i then (1 + 2 * t : ℝ) else 0) + t ^ 2 := by
    intro l
    by_cases h1 : l = i
    · rw [if_pos h1, if_pos h1]
      ring
    · rw [if_neg h1, if_neg h1]
      ring
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib]
  simp
theorem t_eq (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * ((Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ)) ^ 2 +
      2 * ((Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ)) = 1 / 4 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt (1 + (k : ℝ) / 4) ^ 2 = 1 + (k : ℝ) / 4 :=
    Real.sq_sqrt (by positivity)
  generalize Real.sqrt (1 + (k : ℝ) / 4) = s at hs
  have e : (k : ℝ) * ((s - 1) / (k : ℝ)) ^ 2 + 2 * ((s - 1) / (k : ℝ)) =
      (s ^ 2 - 1) / (k : ℝ) := by
    field_simp
    ring
  rw [e, hs]
  field_simp
  ring
end OMA
theorem OMA.L4 : OMA.R1.H2 := by
  unfold OMA.R1.H2
  intro k
  refine ⟨fun x => WithLp.toLp 2 (Fin.append (fun a => x a) (fun _ => (0 : ℝ))),
    fun i => WithLp.toLp 2 (Fin.append (fun _ => (0 : ℝ))
      (fun l => (if l = i then (1 : ℝ) else 0) +
        (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))), ?_, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro x y
    have h : dist (WithLp.toLp 2 (Fin.append (fun a => x a) (fun _ => (0 : ℝ))) :
          EuclideanSpace ℝ (Fin (9 + k)))
        (WithLp.toLp 2 (Fin.append (fun a => y a) (fun _ => (0 : ℝ)))) ^ 2 = dist x y ^ 2 := by
      rw [OMA.dist_sq_append, EuclideanSpace.dist_sq_eq]
      simp only [Real.dist_eq, sq_abs]
      simp
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp h
  · intro i j hij
    have h := OMA.dist_sq_append k (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun l => (if l = i then (1 : ℝ) else 0) + (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))
      (fun l => (if l = j then (1 : ℝ) else 0) + (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))
    rw [OMA.sum_delta_sq k i j hij] at h
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, zero_add] at h
    rw [← Real.sqrt_sq (dist_nonneg (α := EuclideanSpace ℝ (Fin (9 + k)))), h]
  · intro x hx i
    have hk : 0 < k := Fin.pos i
    have h := OMA.dist_sq_append k (fun a => x a) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun l => (if l = i then (1 : ℝ) else 0) + (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))
    rw [OMA.sum_delta_t k i] at h
    have hn : ∑ a : Fin 9, (x a - 0) ^ 2 = 3 / 4 := by
      rw [← hx, EuclideanSpace.real_norm_sq_eq]
      simp
    have ht := OMA.t_eq k hk
    rw [hn] at h
    have h2 : dist (WithLp.toLp 2 (Fin.append (fun a => x a) (fun _ => (0 : ℝ))) :
          EuclideanSpace ℝ (Fin (9 + k)))
        (WithLp.toLp 2 (Fin.append (fun _ => (0 : ℝ))
          (fun l => (if l = i then (1 : ℝ) else 0) +
            (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ)))) ^ 2 = 2 := by
      rw [h]
      linarith
    rw [← Real.sqrt_sq (dist_nonneg (α := EuclideanSpace ℝ (Fin (9 + k)))), h2]
end W4

section
namespace OMA.R11
open Metric Borsuk Finset
open scoped RealInnerProductSpace Classical
def H1 : Prop := ∃ f : (EuclideanSpace ℝ (Fin 4)) → (EuclideanSpace ℝ (Fin 9)),
  (∀ x, ‖x‖ = 1 → ‖f x‖^2 = 3/4) ∧
  ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → dist (f x) (f y)^2 = 2*(1-⟪x,y⟫^2)
def H2 : Prop := ∀ U : Fin 10 → Set (EuclideanSpace ℝ (Fin 4)),
  (∀ x, ‖x‖ = 1 → ∃ i, x ∈ U i) →
  (∀ i, ∃ b : ℝ, b < 2 ∧ ∀ x ∈ U i, ∀ y ∈ U i,
      ‖x‖ = 1 → ‖y‖ = 1 → 2*(1-⟪x,y⟫^2) ≤ b) →
  ∃ T Q : (Finset (Fin 10) → Prop), (
    (∀ S, Q S → S.card = 4) ∧
    (∀ S U, Q S → U ⊆ S → U.card = 3 → T U) ∧
    (∀ U, T U → ∃ S, Q S ∧ U ⊆ S) ∧
    (∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S) ∧
    (∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))) ∧
    (∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2)) ∧ ∃ S, Q S
def H3 : Prop := ∀ T Q : (Finset (Fin 10) → Prop), (
    (∀ S, Q S → S.card = 4) ∧
    (∀ S U, Q S → U ⊆ S → U.card = 3 → T U) ∧
    (∀ U, T U → ∃ S, Q S ∧ U ⊆ S) ∧
    (∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S) ∧
    (∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))) ∧
    (∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2)) → ¬ ∃ S, Q S
theorem main : H1 → H2 → H3 → OMA.R1.H1 := by
  rintro ⟨f,hs,hd⟩ topological finiteObstruction
  let X := f '' {x : (EuclideanSpace ℝ (Fin 4)) | ‖x‖=1}
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hsquare := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hdX : ediam X = ENNReal.ofReal (Real.sqrt 2) := by
    apply le_antisymm
    · apply ediam_le
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hd x y hx hy,sq_nonneg ⟪x,y⟫,dist_nonneg (x:=f x) (y:=f y)]
    · let u : (EuclideanSpace ℝ (Fin 4)) := EuclideanSpace.single 0 1
      let v : (EuclideanSpace ℝ (Fin 4)) := EuclideanSpace.single 1 1
      have hu : ‖u‖=1 := by simp [u]
      have hv : ‖v‖=1 := by simp [v]
      have hi : ⟪u,v⟫=0 := by simp [u,v,EuclideanSpace.inner_single_left]
      have hh := hd u v hu hv
      rw [hi] at hh
      have hdist : dist (f u) (f v) = Real.sqrt 2 := by nlinarith [dist_nonneg (x:=f u) (y:=f v)]
      rw [←hdist,←edist_dist]
      exact edist_le_ediam_of_mem (show f u∈X from ⟨u,hu,rfl⟩) ⟨v,hv,rfl⟩
  refine ⟨X,ediam_pos_iff.mp (hdX ▸ ENNReal.ofReal_pos.mpr hsqrt),?_,hdX,?_⟩
  · rintro _ ⟨x,hx,rfl⟩; exact hs x hx
  rintro ⟨C,hcover,hsmall⟩
  have hU (x : (EuclideanSpace ℝ (Fin 4))) (hx : ‖x‖=1) : ∃ i, x∈ f ⁻¹' C i := by
    change ∃ i, f x∈C i
    exact Set.mem_iUnion.mp (hcover (show f x∈X from ⟨x,hx,rfl⟩))
  apply False.elim
  obtain ⟨T,Q,h,hQ⟩ := topological (fun i => f ⁻¹' C i) hU (by
    intro i
    have hii := hsmall i
    rw [hdX] at hii
    have hne := (hii.trans_le le_top).ne
    have hlt := (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr hii
    rw [ENNReal.toReal_ofReal hsqrt.le] at hlt
    change diam (C i) < Real.sqrt 2 at hlt
    refine ⟨diam (C i)^2,by nlinarith [diam_nonneg (s:=C i)],?_⟩
    intro x hx y hy hxu hyu
    rw [←hd x y hxu hyu]
    exact pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem' hne hx hy) 2)
  exact finiteObstruction T Q h hQ
end OMA.R11
end

namespace W1
open Real Finset
open scoped RealInnerProductSpace
namespace BorsukProjector
private noncomputable def projector (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 9) :=
  !₂[(x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2)/2,
     (x 0 ^ 2 - x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2)/2,
     (x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 + x 3 ^ 2)/2,
     sqrt 2 * (x 0*x 1), sqrt 2 * (x 0*x 2), sqrt 2 * (x 0*x 3),
     sqrt 2 * (x 1*x 2), sqrt 2 * (x 1*x 3), sqrt 2 * (x 2*x 3)]
private lemma projector_inner (x y : EuclideanSpace ℝ (Fin 4)) :
    ⟪projector x,projector y⟫ = ⟪x,y⟫^2 - ‖x‖^2*‖y‖^2/4 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp [projector,PiLp.inner_apply,Fin.sum_univ_succ,Real.inner_apply]
  ring_nf
  norm_num
private lemma sphere_norm {x : EuclideanSpace ℝ (Fin 4)} (hx : ‖x‖=1) :
    ‖projector x‖^2 = 3/4 := by
  have h := projector_inner x x
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hx] at h
  norm_num at h ⊢
  exact h
theorem exists_projector : ∃ f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 9),
    (∀ x, ‖x‖=1 → ‖f x‖^2=3/4) ∧ ∀ x y, ‖x‖=1 → ‖y‖=1 →
    dist (f x) (f y)^2 = 2*(1-⟪x,y⟫^2) := by
  refine ⟨projector,fun _ h => sphere_norm h,?_⟩
  intro x y hx hy
  rw [dist_eq_norm,norm_sub_sq_real,sphere_norm hx,sphere_norm hy,projector_inner,hx,hy]
  ring
end BorsukProjector
theorem OMA.L1 : OMA.R11.H1 :=
  BorsukProjector.exists_projector
end W1

namespace W2
namespace OAI
abbrev Euc (ι : Type*) := EuclideanSpace ℝ ι
abbrev SqMat (ι : Type*) := Matrix ι ι ℝ
abbrev PreComplex (ι : Type*) := PreAbstractSimplicialComplex ι
noncomputable abbrev matrixOp (ι : Type*) [Fintype ι] [DecidableEq ι] := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
end OAI
namespace OAI.BorsukNine
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMeasure
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
abbrev UnitSphere := Metric.sphere (0 : V) 1
noncomputable def sphereProbability : Measure (UnitSphere V) :=
  ((volume : Measure V).toSphere Set.univ)⁻¹ • volume.toSphere
instance sphereMeasure_neZero : NeZero ((volume : Measure V).toSphere) := by
  constructor
  exact (Measure.toSphere_eq_zero_iff_finrank volume).not.mpr
    (ne_of_gt (Module.finrank_pos (R := ℝ) (M := V)))
instance sphereProbability_isProbability : IsProbabilityMeasure (sphereProbability V) := by
  unfold sphereProbability
  infer_instance
instance sphereProbability_openPos : (sphereProbability V).IsOpenPosMeasure := by
  unfold sphereProbability
  exact Measure.isOpenPosMeasure_smul volume.toSphere (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
variable {V}
noncomputable def sphereRotation (e : V ≃ₗᵢ[ℝ] V) : UnitSphere V ≃ₜ UnitSphere V :=
  e.toHomeomorph.subtype (fun x => by simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph, e.norm_map])
omit [Nontrivial V] in
lemma sphereRotation_preserves_toSphere (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) volume.toSphere volume.toSphere := by
  refine ⟨(sphereRotation e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation e).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation e).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, e u, ⟨sphereRotation e u, hu, rfl⟩, by simp⟩
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, he⟩
      refine ⟨r, hr, e.symm u, ⟨(sphereRotation e).symm u, ?_, rfl⟩, ?_⟩
      · simpa using hu
      · apply e.injective
        simpa using he
  rw [hset]
  have he := e.measurePreserving.map_eq
  have hm := e.toMeasurableEquiv.measurableEmbedding.map_apply volume
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at hm
  rw [he] at hm
  exact hm.symm
omit [Nontrivial V] in
lemma sphereRotation_preserves_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) (sphereProbability V) (sphereProbability V) := by
  exact (sphereRotation_preserves_toSphere e).smul_measure _
omit [Nontrivial V] in
lemma integral_sphere_rotation (e : V ≃ₗᵢ[ℝ] V) (g : UnitSphere V → ℝ) :
    (∫ x, g (sphereRotation e x) ∂sphereProbability V) =
      ∫ x, g x ∂sphereProbability V :=
  (sphereRotation_preserves_probability e).integral_comp
    (sphereRotation e).measurableEmbedding g
end SphereMeasure
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMoments
variable {ι : Type*} [Fintype ι] [Nonempty ι]
lemma sphere_coord_integrable (i j : ι) :
    Integrable (fun x : UnitSphere (Euc ι) => (x : (Euc ι)) i * (x : (Euc ι)) j) (sphereProbability (Euc ι)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)
  · exact HasCompactSupport.of_compactSpace _
omit [Nonempty ι] in
lemma sphere_coord_cross {i j : ι} (hij : i ≠ j) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) j ∂sphereProbability (Euc ι)) = 0 := by
  classical
  let e : (Euc ι) ≃ₗᵢ[ℝ] (Euc ι) := LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hi := integral_sphere_rotation e (fun x : UnitSphere (Euc ι) => (x : (Euc ι)) i * (x : (Euc ι)) j)
  have he : (fun x : UnitSphere (Euc ι) => (sphereRotation e x : (Euc ι)) i * (sphereRotation e x : (Euc ι)) j) =
      fun x : UnitSphere (Euc ι) => -((x : (Euc ι)) i * (x : (Euc ι)) j) := by
    funext x
    simp [sphereRotation, e, hij.symm]
  rw [he, integral_neg] at hi
  linarith
omit [Nonempty ι] in
lemma sphere_coord_diag_eq (i j : ι) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) i ∂sphereProbability (Euc ι)) =
      ∫ x : UnitSphere (Euc ι), (x : (Euc ι)) j * (x : (Euc ι)) j ∂sphereProbability (Euc ι) := by
  classical
  let e : (Euc ι) ≃ₗᵢ[ℝ] (Euc ι) := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hi := integral_sphere_rotation e (fun x : UnitSphere (Euc ι) => (x : (Euc ι)) j * (x : (Euc ι)) j)
  convert hi using 1
  congr 1
  ext x
  simp [sphereRotation, e, Equiv.piCongrLeft']
lemma sphere_coord_diag (i : ι) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) i ∂sphereProbability (Euc ι)) =
      (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hs : (∑ j, ∫ x : UnitSphere (Euc ι), (x : (Euc ι)) j * (x : (Euc ι)) j ∂sphereProbability (Euc ι)) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => sphere_coord_integrable j j)]
    have he : (fun x : UnitSphere (Euc ι) => ∑ j, (x : (Euc ι)) j * (x : (Euc ι)) j) = fun _ => (1 : ℝ) := by
      funext x
      have hn : ‖(x : (Euc ι))‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      have hh := EuclideanSpace.real_norm_sq_eq (x : (Euc ι))
      rw [hn] at hh
      simpa only [one_pow, pow_two, one_mul] using hh.symm
    rw [he]
    simp
  have hval : (Fintype.card ι : ℝ) *
      (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) i ∂sphereProbability (Euc ι)) = 1 := by
    rw [← hs]
    rw [Finset.sum_congr rfl (fun j _ => sphere_coord_diag_eq j i)]
    simp
  exact eq_inv_of_mul_eq_one_right hval
lemma sphere_quadratic_integral (A : SqMat ι) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)).ofLp ⬝ᵥ A *ᵥ (x : (Euc ι)).ofLp ∂sphereProbability (Euc ι)) =
      Matrix.trace A * (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hc (i j : ι) : Integrable (fun x : UnitSphere (Euc ι) =>
      A i j * ((x : (Euc ι)) i * (x : (Euc ι)) j)) (sphereProbability (Euc ι)) :=
    (sphere_coord_integrable i j).const_mul _
  have he : (fun x : UnitSphere (Euc ι) => (x : (Euc ι)).ofLp ⬝ᵥ A *ᵥ (x : (Euc ι)).ofLp) =
      fun x : UnitSphere (Euc ι) => ∑ i, ∑ j, A i j * ((x : (Euc ι)) i * (x : (Euc ι)) j) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hc i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hc _ j), integral_const_mul]
  calc
    _ = ∑ i, A i i * (Fintype.card ι : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [sphere_coord_diag]
      · intro j _ hji
        rw [sphere_coord_cross hji.symm, mul_zero]
      · simp
    _ = _ := by rw [← Finset.sum_mul]; rfl
end SphereMoments
end
end
section
section
abbrev Vector4 := Euc (Fin 4)
abbrev Matrix4 := Euc (Fin 4 × Fin 4)
def projector (u : Vector4) : Matrix4 :=
  WithLp.toLp 2 (fun ij => u ij.1 * u ij.2)
def projectorSet : Set Matrix4 :=
  projector '' {u : Vector4 | ‖u‖ = 1}
def HasTenSmallCover : Prop :=
  ∃ C : Fin 10 → Set Matrix4,
    (∀ i, C i ⊆ projectorSet) ∧
    projectorSet ⊆ ⋃ i, C i ∧
    ∀ i, Metric.diam (C i) < Real.sqrt 2
end
end
section
section
open scoped RealInnerProductSpace ContDiff
@[simp] theorem projector_apply (u : Vector4) (i j : Fin 4) :
    projector u (i, j) = u i * u j := rfl
@[simp] theorem projector_neg (u : Vector4) : projector (-u) = projector u := by
  ext ⟨i, j⟩
  simp [projector]
theorem continuous_projector : Continuous projector := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact (PiLp.continuous_apply 2 _ ij.1).mul (PiLp.continuous_apply 2 _ ij.2)
theorem isCompact_projectorSet : IsCompact projectorSet := by
  have h : {u : Vector4 | ‖u‖ = 1} = Metric.sphere 0 1 := by
    ext u
    simp
  rw [projectorSet, h]
  exact (isCompact_sphere (0 : Vector4) 1).image continuous_projector
theorem projector_inner (u v : Vector4) :
    ⟪projector u, projector v⟫ = ⟪u, v⟫ ^ 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, projector]
  change (∑ ij : Fin 4 × Fin 4, (v ij.1 * v ij.2) * (u ij.1 * u ij.2)) =
    (∑ i : Fin 4, v i * u i) ^ 2
  rw [Fintype.sum_prod_type]
  simp only [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem projector_norm_sq (u : Vector4) : ‖projector u‖ ^ 2 = ‖u‖ ^ 4 := by
  rw [← real_inner_self_eq_norm_sq, projector_inner, real_inner_self_eq_norm_sq]
  ring
theorem projector_dist_sq (u v : Vector4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) ^ 2 = 2 - 2 * ⟪u, v⟫ ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real, projector_norm_sq, projector_norm_sq,
    projector_inner, hu, hv]
  ring
theorem projector_dist_eq_sqrt_two_iff (u v : Vector4)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) = Real.sqrt 2 ↔ ⟪u, v⟫ = 0 := by
  have hd := projector_dist_sq u v hu hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · intro h
    rw [h] at hd
    nlinarith [sq_nonneg ⟪u, v⟫]
  · intro h
    rw [h] at hd
    have hn := dist_nonneg (x := projector u) (y := projector v)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
structure Admissible {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] (f : V → ι → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ (fun u => f u i)
  antipodal : ∀ u i, f (-u) i = f u i
  nonneg : ∀ u, ‖u‖ = 1 → ∀ i, 0 ≤ f u i
  sum_one : ∀ u, ‖u‖ = 1 → ∑ i, f u i = 1
  orthogonal : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫ = 0 →
    ∀ i, ¬ (0 < f u i ∧ 0 < f v i)
theorem contDiff_projector : ContDiff ℝ ∞ projector := by
  apply (contDiff_piLp 2).mpr
  intro ij
  exact (contDiff_piLp_apply (p := 2) (i := ij.1)).mul (contDiff_piLp_apply (p := 2) (i := ij.2))
theorem dist_lt_of_mem_thickening_small {C : Set Matrix4}
    (hC : C ⊆ projectorSet) (hd : Metric.diam C < Real.sqrt 2)
    {P Q : Matrix4}
    (hP : P ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C)
    (hQ : Q ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C) :
    dist P Q < Real.sqrt 2 := by
  rcases Metric.mem_thickening_iff.mp hP with ⟨p, hp, hPp⟩
  rcases Metric.mem_thickening_iff.mp hQ with ⟨q, hq, hQq⟩
  have hb := isCompact_projectorSet.isBounded.subset hC
  have hpq := Metric.dist_le_diam_of_mem hb hp hq
  have ht : dist P Q ≤ dist P p + dist p q + dist Q q := by
    calc
      dist P Q ≤ dist P p + dist p Q := dist_triangle P p Q
      _ ≤ dist P p + (dist p q + dist q Q) :=
        add_le_add le_rfl (dist_triangle p q Q)
      _ = dist P p + dist p q + dist Q q := by rw [dist_comm q Q]; ring
  linarith
open scoped Manifold
theorem cover_to_admissible (h : HasTenSmallCover) :
    ∃ f : Vector4 → Fin 10 → ℝ, Admissible f := by
  classical
  rcases h with ⟨C, hCX, hcov, hdiam⟩
  let U : Fin 10 → Set Matrix4 := fun i =>
    Metric.thickening ((Real.sqrt 2 - Metric.diam (C i)) / 4) (C i)
  have hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_thickening
  have hCU : ∀ i, C i ⊆ U i := by
    intro i
    apply Metric.self_subset_thickening
    linarith [hdiam i]
  have hXU : projectorSet ⊆ ⋃ i, U i := by
    intro P hP
    rcases Set.mem_iUnion.mp (hcov hP) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hCU i hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Matrix4)) isCompact_projectorSet.isClosed U hU hXU
  refine ⟨fun u i => ρ i (projector u), ?_⟩
  constructor
  · intro i
    exact (contMDiff_iff_contDiff.mp (ρ i).contMDiff).comp contDiff_projector
  · intro u i
    simp
  · intro u _ i
    exact ρ.nonneg i (projector u)
  · intro u hu
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (show projector u ∈ projectorSet
      from ⟨u, hu, rfl⟩)
  · intro u v hu hv huv i ⟨hui, hvi⟩
    have huU : projector u ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hui))
    have hvU : projector v ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hvi))
    have hd := dist_lt_of_mem_thickening_small (hCX i) (hdiam i) huU hvU
    rw [(projector_dist_eq_sqrt_two_iff u v hu hv).mpr huv] at hd
    exact lt_irrefl _ hd
noncomputable def positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < f u i)
@[simp] theorem mem_positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) (i : ι) :
    i ∈ positiveSupport f u ↔ 0 < f u i := by
  classical
  simp [positiveSupport]
lemma Admissible.support_nonempty {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u : V} (hu : ‖u‖ = 1) :
    (positiveSupport f u).Nonempty := by
  classical
  have hs : 0 < ∑ i, f u i := by rw [hf.sum_one u hu]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hf.nonneg u hu i)).mp hs
  exact ⟨i, (mem_positiveSupport f u i).mpr hi⟩
lemma Admissible.disjoint_supports {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u v : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : ⟪u, v⟫ = 0) :
    Disjoint (positiveSupport f u) (positiveSupport f v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hf.orthogonal u v hu hv horth i
    ⟨(mem_positiveSupport f u i).mp hi, (mem_positiveSupport f v i).mp hj⟩
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
section HomogeneousLift
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*}
noncomputable def homogeneousLift (f : V → ι → ℝ) (v : V) : ι → ℝ :=
  fun i => ‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i
@[simp] lemma homogeneousLift_zero (f : V → ι → ℝ) : homogeneousLift f 0 = 0 := by
  ext i
  simp [homogeneousLift]
lemma homogeneousLift_unit (f : V → ι → ℝ) {v : V} (hv : ‖v‖ = 1) :
    homogeneousLift f v = f v := by
  ext i
  simp [homogeneousLift, hv]
variable [Fintype ι]
lemma Admissible.lift_nonneg {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    0 ≤ homogeneousLift f v i := by
  by_cases hv : v = 0
  · simp [hv]
  · exact mul_nonneg (sq_nonneg _) (hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i)
lemma Admissible.lift_sum {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ∑ i, homogeneousLift f v i = ‖v‖ ^ 2 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  · simp only [homogeneousLift, ← Finset.mul_sum]
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    rw [hf.sum_one _ hn, mul_one]
lemma Admissible.lift_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    homogeneousLift f v i ≤ ‖v‖ ^ 2 := by
  classical
  rw [← hf.lift_sum v]
  exact Finset.single_le_sum (fun j _ => hf.lift_nonneg v j) (Finset.mem_univ i)
lemma Admissible.lift_norm_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ‖homogeneousLift f v‖ ≤ ‖v‖ ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf.lift_nonneg v i)] using hf.lift_le v i
lemma Admissible.lift_even {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    homogeneousLift f (-v) = homogeneousLift f v := by
  ext i
  simp [homogeneousLift, smul_neg, hf.antipodal]
omit [Fintype ι] in
lemma homogeneousLift_smul_pos (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 < t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  ext i
  have he : (‖t • v‖⁻¹ : ℝ) • (t • v) = (‖v‖⁻¹ : ℝ) • v := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
    congr 1
    field_simp
  change ‖t • v‖ ^ 2 * f ((‖t • v‖⁻¹ : ℝ) • (t • v)) i = t ^ 2 * (‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  ring
omit [Fintype ι] in
lemma homogeneousLift_smul_nonneg (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 ≤ t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases ht.eq_or_lt with rfl | hp
  · simp
  · exact homogeneousLift_smul_pos f v hp
lemma Admissible.lift_continuous {f : V → ι → ℝ} (hf : Admissible f) :
    Continuous (homogeneousLift f) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    rw [ContinuousAt, homogeneousLift_zero]
    apply squeeze_zero_norm (fun x => hf.lift_norm_le x)
    have hc : Continuous (fun x : V => ‖x‖ ^ 2) := continuous_norm.pow 2
    simpa using hc.tendsto (0 : V)
  · have hn : ContinuousAt (fun x : V => (‖x‖⁻¹ : ℝ) • x) v :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousAt_id
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_norm.continuousAt.pow 2).mul ((hf.smooth i).continuous.continuousAt.comp hn)
lemma Admissible.lift_orthogonal {f : V → ι → ℝ} (hf : Admissible f)
    {u v : V} (huv : ⟪u, v⟫ = 0) (i : ι) :
    homogeneousLift f u i * homogeneousLift f v i = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hn : ⟪(‖u‖⁻¹ : ℝ) • u, (‖v‖⁻¹ : ℝ) • v⟫ = 0 := by
    simp [inner_smul_left, inner_smul_right, huv]
  have h := hf.orthogonal _ _ (norm_smul_inv_norm (𝕜 := ℝ) hu) (norm_smul_inv_norm (𝕜 := ℝ) hv) hn i
  have hnu := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hu) i
  have hnv := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i
  have hz : f ((‖u‖⁻¹ : ℝ) • u) i = 0 ∨ f ((‖v‖⁻¹ : ℝ) • v) i = 0 := by
    by_contra hh
    push Not at hh
    exact h ⟨lt_of_le_of_ne hnu (Ne.symm hh.1), lt_of_le_of_ne hnv (Ne.symm hh.2)⟩
  rcases hz with hz | hz <;> simp [homogeneousLift, hz]
end HomogeneousLift
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section IntegralLift
variable {ν ι : Type*} [Fintype ν] [Nonempty ν] [Fintype ι]
noncomputable def integralLift (f : (Euc ν) → ι → ℝ) (T : (Euc ν) →L[ℝ] (Euc ν)) : ι → ℝ :=
  fun i => (Fintype.card ν : ℝ) *
    ∫ x : UnitSphere (Euc ν), homogeneousLift f (T x) i ∂sphereProbability (Euc ν)
omit [Nonempty ν] in
lemma Admissible.integrand_continuous {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    Continuous (fun x : UnitSphere (Euc ν) => homogeneousLift f (T x) i) :=
  (continuous_apply i).comp (hf.lift_continuous.comp (T.continuous.comp continuous_subtype_val))
lemma Admissible.integrand_integrable {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    Integrable (fun x : UnitSphere (Euc ν) => homogeneousLift f (T x) i) (sphereProbability (Euc ν)) :=
  (hf.integrand_continuous T i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
omit [Nonempty ν] in
lemma Admissible.integralLift_nonneg {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) : 0 ≤ integralLift f T i :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ => hf.lift_nonneg _ i))
lemma Admissible.integralLift_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) : ∑ i, integralLift f T i =
      (Fintype.card ν : ℝ) * ∫ x : UnitSphere (Euc ν), ‖T x‖ ^ 2 ∂sphereProbability (Euc ν) := by
  classical
  simp only [integralLift, ← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun i _ => hf.integrand_integrable T i)]
  simp only [hf.lift_sum]
lemma Admissible.integralLift_pos_iff_sphere {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : UnitSphere (Euc ν), 0 < homogeneousLift f (T x) i := by
  have hc : (0 : ℝ) < Fintype.card ν := Nat.cast_pos.mpr Fintype.card_pos
  rw [integralLift, mul_pos_iff_of_pos_left hc]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he : (fun x : UnitSphere (Euc ν) => homogeneousLift f (T x) i) = 0 := by
      funext x
      exact le_antisymm (hn x) (hf.lift_nonneg _ i)
    rw [he] at h
    change 0 < ∫ _ : UnitSphere (Euc ν), (0 : ℝ) ∂sphereProbability (Euc ν) at h
    simp only [integral_zero, lt_self_iff_false] at h
  · rintro ⟨x, hx⟩
    exact integral_pos_of_integrable_nonneg_nonzero (hf.integrand_continuous T i)
      (hf.integrand_integrable T i) (fun _ => hf.lift_nonneg _ i) hx.ne'
lemma Admissible.integralLift_continuous {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    Continuous (integralLift f) := by
  apply continuous_pi
  intro i
  apply continuous_const.mul
  have hc : Continuous (fun p : ((Euc ν) →L[ℝ] (Euc ν)) × UnitSphere (Euc ν) =>
      homogeneousLift f (p.1 p.2) i) :=
    (continuous_apply i).comp (hf.lift_continuous.comp
      (continuous_fst.clm_apply (continuous_subtype_val.comp continuous_snd)))
  have hi := continuous_parametric_integral_of_continuous
    (μ := sphereProbability (Euc ν))
    (f := fun (T : (Euc ν) →L[ℝ] (Euc ν)) (x : UnitSphere (Euc ν)) => homogeneousLift f (T x) i)
    hc isCompact_univ
  simpa only [setIntegral_univ] using hi
lemma Admissible.integralLift_pos_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : (Euc ν), 0 < homogeneousLift f (T x) i := by
  rw [hf.integralLift_pos_iff_sphere]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hn : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
    refine ⟨⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx0)⟩, ?_⟩
    simp only [map_smul, homogeneousLift_smul_pos f _ hn, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (sq_pos_of_pos hn) hx
lemma Admissible.integralLift_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    0 < integralLift f T i ↔ ∃ v : (Euc ν),
      v ∈ LinearMap.range T.toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.integralLift_pos_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : T x ≠ 0 := by
      intro hz
      simp only [hz, homogeneousLift_zero, Pi.zero_apply, lt_self_iff_false] at hx
    refine ⟨‖T x‖⁻¹ • T x, ⟨‖T x‖⁻¹ • x, by simp⟩,
      norm_smul_inv_norm (𝕜 := ℝ) hx0, ?_⟩
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mp hx
  · rintro ⟨v, ⟨x, rfl⟩, hv, hx⟩
    refine ⟨x, ?_⟩
    rw [homogeneousLift_unit f (show ‖T x‖ = 1 from hv)]
    exact hx
omit [Nonempty ν] [Fintype ι] in
lemma integralLift_smul_nonneg (f : (Euc ν) → ι → ℝ) (T : (Euc ν) →L[ℝ] (Euc ν))
    {t : ℝ} (ht : 0 ≤ t) : integralLift f (t • T) = t ^ 2 • integralLift f T := by
  ext i
  simp only [integralLift, smul_apply, homogeneousLift_smul_nonneg f _ ht,
    Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring
end IntegralLift
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixNorm
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma matrix_action_norm_sq (A : SqMat ν) (x : (Euc ν)) :
    ‖(matrixOp ν) A x‖ ^ 2 =
      ⟪x, (matrixOp ν) (star A * A) x⟫ := by
  rw [map_mul, map_star]
  change ‖(matrixOp ν) A x‖ ^ 2 =
    ⟪x, (star ((matrixOp ν) A)) ((matrixOp ν) A x)⟫
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
lemma sqrt_action_norm_sq (Q : SqMat ν) (hQ : 0 ≤ Q) (x : (Euc ν)) :
    ‖(matrixOp ν) (CFC.sqrt Q) x‖ ^ 2 = ⟪x, (matrixOp ν) Q x⟫ := by
  rw [matrix_action_norm_sq, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
lemma matrix_sqrt_smul {Q : SqMat ν} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt (t • Q) = Real.sqrt t • CFC.sqrt Q := by
  apply (CFC.sqrt_eq_iff _ _ (smul_nonneg ht hQ)
    (smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _))).mpr
  rw [smul_mul_smul, CFC.sqrt_mul_sqrt_self Q hQ, Real.mul_self_sqrt ht]
end MatrixNorm
section MatrixRange
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma matrix_sqrt_range (Q : SqMat ν) (hQ : 0 ≤ Q) :
    LinearMap.range ((matrixOp ν) (CFC.sqrt Q)).toLinearMap = LinearMap.range ((matrixOp ν) Q).toLinearMap := by
  have hs : star ((matrixOp ν) (CFC.sqrt Q)) = (matrixOp ν) (CFC.sqrt Q) := by
    rw [← map_star, (CFC.sqrt_nonneg Q).star_eq]
  have hh := LinearMap.range_adjoint_comp_self ((matrixOp ν) (CFC.sqrt Q)).toLinearMap
  have ha : ((matrixOp ν) (CFC.sqrt Q)).toLinearMap.adjoint = ((matrixOp ν) (CFC.sqrt Q)).toLinearMap := by
    change (ContinuousLinearMap.adjoint ((matrixOp ν) (CFC.sqrt Q))).toLinearMap = _
    rw [← ContinuousLinearMap.star_eq_adjoint, hs]
  rw [ha] at hh
  have hm : ((matrixOp ν) (CFC.sqrt Q)).toLinearMap.comp ((matrixOp ν) (CFC.sqrt Q)).toLinearMap = ((matrixOp ν) Q).toLinearMap := by
    change ((matrixOp ν) (CFC.sqrt Q) * (matrixOp ν) (CFC.sqrt Q)).toLinearMap = _
    rw [← map_mul, CFC.sqrt_mul_sqrt_self Q hQ]
  rw [hm] at hh
  exact hh.symm
end MatrixRange
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixKernel
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma matrix_abs_action_norm_sq (A : SqMat ν) (x : (Euc ν)) :
    ‖(matrixOp ν) (CFC.abs A) x‖ ^ 2 = ‖(matrixOp ν) A x‖ ^ 2 := by
  rw [matrix_action_norm_sq, (CFC.abs_nonneg A).star_eq, CFC.abs_mul_abs,
    ← matrix_action_norm_sq]
lemma matrix_abs_kernel {A : SqMat ν} {x : (Euc ν)} (hx : (matrixOp ν) A x = 0) :
    (matrixOp ν) (CFC.abs A) x = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [matrix_abs_action_norm_sq, hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
lemma matrix_parts_kernel {A : SqMat ν} (hA : IsSelfAdjoint A)
    {x : (Euc ν)} (hx : (matrixOp ν) A x = 0) : (matrixOp ν) A⁺ x = 0 ∧ (matrixOp ν) A⁻ x = 0 := by
  have habs := matrix_abs_kernel hx
  constructor
  · have h := congrArg (fun B : SqMat ν => (matrixOp ν) B x) (CFC.abs_add_self A hA)
    have hh : (2 : ℝ) • (matrixOp ν) A⁺ x = 0 := by
      simpa only [map_add, add_apply, two_smul, hx, habs, add_zero] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  · have h := congrArg (fun B : SqMat ν => (matrixOp ν) B x) (CFC.abs_sub_self A hA)
    have hh : (2 : ℝ) • (matrixOp ν) A⁻ x = 0 := by
      simpa only [map_sub, sub_apply, two_smul, hx, habs, sub_zero,
        map_add, add_apply] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
lemma matrix_image_orthogonal_kernel {A : SqMat ν} (hA : IsSelfAdjoint A)
    {x : (Euc ν)} (hx : (matrixOp ν) A x = 0) (y : (Euc ν)) : ⟪x, (matrixOp ν) A y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, hA.star_eq, hx, inner_zero_left]
end MatrixKernel
section PositiveExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
noncomputable def positiveExtension (f : (Euc ν) → ι → ℝ) (Q : SqMat ν) : ι → ℝ :=
  integralLift f ((matrixOp ν) (CFC.sqrt Q))
omit [Nonempty ν] in
lemma Admissible.positiveExtension_nonneg {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (Q : SqMat ν) (i : ι) : 0 ≤ positiveExtension f Q i :=
  hf.integralLift_nonneg _ _
lemma Admissible.positiveExtension_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {Q : SqMat ν} (hQ : 0 ≤ Q) : ∑ i, positiveExtension f Q i = Matrix.trace Q := by
  classical
  rw [positiveExtension, hf.integralLift_sum]
  simp_rw [sqrt_action_norm_sq Q hQ, Matrix.inner_toEuclideanCLM]
  rw [sphere_quadratic_integral]
  have hn : (Fintype.card ν : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  field_simp
lemma Admissible.positiveExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (positiveExtension f) {Q : SqMat ν | 0 ≤ Q} := by
  have hc : Continuous (fun Q : SqMat ν => (matrixOp ν) Q) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hf.integralLift_continuous.comp_continuousOn
    (hc.comp_continuousOn CFC.continuousOn_sqrt)
omit [Nonempty ν] [Fintype ι] in
lemma positiveExtension_smul_nonneg (f : (Euc ν) → ι → ℝ)
    {Q : SqMat ν} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    positiveExtension f (t • Q) = t • positiveExtension f Q := by
  unfold positiveExtension
  rw [matrix_sqrt_smul hQ ht, map_smul,
    integralLift_smul_nonneg f _ (Real.sqrt_nonneg t), Real.sq_sqrt ht]
lemma Admissible.positiveExtension_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {Q : SqMat ν} (hQ : 0 ≤ Q) (i : ι) :
    0 < positiveExtension f Q i ↔ ∃ v : (Euc ν),
      v ∈ LinearMap.range ((matrixOp ν) Q).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [positiveExtension, hf.integralLift_support, matrix_sqrt_range Q hQ]
end PositiveExtension
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma matrix_images_orthogonal {P N : SqMat ν} (hP : 0 ≤ P) (hPN : P * N = 0)
    (x y : (Euc ν)) : ⟪(matrixOp ν) P x, (matrixOp ν) N y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have hs : star ((matrixOp ν) P) = (matrixOp ν) P := by rw [← map_star, hP.star_eq]
  rw [hs]
  change ⟪x, ((matrixOp ν) P * (matrixOp ν) N) y⟫ = 0
  rw [← map_mul, hPN, map_zero]
  simp
lemma Admissible.positiveExtension_orthogonal {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {P N : SqMat ν} (hP : 0 ≤ P) (hN : 0 ≤ N) (hPN : P * N = 0) (i : ι) :
    positiveExtension f P i * positiveExtension f N i = 0 := by
  apply mul_eq_zero.mpr
  by_contra hn
  push Not at hn
  have hp := lt_of_le_of_ne (hf.positiveExtension_nonneg P i) (Ne.symm hn.1)
  have hn' := lt_of_le_of_ne (hf.positiveExtension_nonneg N i) (Ne.symm hn.2)
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hP i).mp hp
  obtain ⟨w, ⟨y, rfl⟩, hw, hy⟩ := (hf.positiveExtension_support hN i).mp hn'
  exact hf.orthogonal _ _ hv hw (matrix_images_orthogonal hP hPN x y) i ⟨hx, hy⟩
noncomputable def signedExtension (f : (Euc ν) → ι → ℝ) (A : SqMat ν) : ι → ℝ :=
  positiveExtension f A⁺ - positiveExtension f A⁻
omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_odd (f : (Euc ν) → ι → ℝ) (A : SqMat ν) :
    signedExtension f (-A) = -signedExtension f A := by
  simp [signedExtension, CFC.posPart_neg, CFC.negPart_neg]
lemma Admissible.signedExtension_abs_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) :
    ∑ i, |signedExtension f A i| = Matrix.trace (CFC.abs A) := by
  classical
  have hcoord (i : ι) : |signedExtension f A i| =
      positiveExtension f A⁺ i + positiveExtension f A⁻ i := by
    have hp := hf.positiveExtension_nonneg A⁺ i
    have hn := hf.positiveExtension_nonneg A⁻ i
    have hprod := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    rcases mul_eq_zero.mp hprod with hz | hz
    · simp [signedExtension, hz, abs_of_nonneg hn]
    · simp [signedExtension, hz, abs_of_nonneg hp]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, hf.positiveExtension_sum (CFC.posPart_nonneg A),
    hf.positiveExtension_sum (CFC.negPart_nonneg A), ← Matrix.trace_add,
    CFC.posPart_add_negPart A hA]
omit [Nonempty ν] in
lemma matrix_posPart_continuousOn :
    ContinuousOn (fun A : SqMat ν => A⁺) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : SqMat ν => (1 / 2 : ℝ) • (CFC.abs A + A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.add continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁺ = (1 / 2 : ℝ) • (CFC.abs A + A)
  rw [CFC.abs_add_self A hA, two_smul, smul_add]
  module
omit [Nonempty ν] in
lemma matrix_negPart_continuousOn :
    ContinuousOn (fun A : SqMat ν => A⁻) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : SqMat ν => (1 / 2 : ℝ) • (CFC.abs A - A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.sub continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁻ = (1 / 2 : ℝ) • (CFC.abs A - A)
  rw [CFC.abs_sub_self A hA, two_smul, smul_add]
  module
lemma Admissible.signedExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (signedExtension f) {A : SqMat ν | IsSelfAdjoint A} := by
  apply ContinuousOn.sub
  · exact hf.positiveExtension_continuousOn.comp matrix_posPart_continuousOn
      (fun A _ => CFC.posPart_nonneg A)
  · exact hf.positiveExtension_continuousOn.comp matrix_negPart_continuousOn
      (fun A _ => CFC.negPart_nonneg A)
end SignedExtension
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section FullSupport
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
lemma Admissible.positiveExtension_kernel {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {Q : SqMat ν} (hQ : 0 ≤ Q) {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hk : (matrixOp ν) Q w = 0) {i : ι} (hi : 0 < f w i) : positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hQ i).mp hp
  exact hf.orthogonal _ _ hw hv (matrix_image_orthogonal_kernel hQ.isSelfAdjoint hk x) i
    ⟨hi, hx⟩
lemma Admissible.signedExtension_kernel {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hk : (matrixOp ν) A w = 0) : ∃ i, signedExtension f A i = 0 := by
  obtain ⟨i, hi⟩ := hf.support_nonempty hw
  have hi' := (mem_positiveSupport f w i).mp hi
  obtain ⟨hp, hn⟩ := matrix_parts_kernel hA hk
  refine ⟨i, ?_⟩
  simp only [signedExtension, Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hw hp hi',
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hw hn hi', sub_self]
lemma Admissible.signedExtension_kernel_eq_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0)
    {w : (Euc ν)} (hk : (matrixOp ν) A w = 0) : w = 0 := by
  by_contra hw
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by simp [norm_smul, norm_inv, hw]
  have hk' : (matrixOp ν) A (‖w‖⁻¹ • w) = 0 := by rw [map_smul, hk, smul_zero]
  obtain ⟨i, hi⟩ := hf.signedExtension_kernel hA hunit hk'
  exact hs i hi
lemma Admissible.signedExtension_fullSupport {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0) :
    IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hz : (matrixOp ν) A (WithLp.toLp 2 u - WithLp.toLp 2 v) = 0 := by
    rw [map_sub, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, huv, sub_self]
  have h := sub_eq_zero.mp (hf.signedExtension_kernel_eq_zero hA hs hz)
  exact WithLp.toLp_injective 2 h
omit [Nonempty ν] in
lemma matrix_psd_trace_zero {Q : SqMat ν} (hQ : 0 ≤ Q)
    (htrace : Matrix.trace Q = 0) : Q = 0 := by
  have hprod : (CFC.sqrt Q)ᴴ * CFC.sqrt Q = Q := by
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
  have hz : CFC.sqrt Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (hprod.symm ▸ htrace)
  rw [← hprod, hz]
  simp
end FullSupport
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
lemma Admissible.signedExtension_eq_zero_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) : signedExtension f A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    have ht : Matrix.trace (CFC.abs A) = 0 := by
      rw [← hf.signedExtension_abs_sum hA, hz]
      simp
    have habs : CFC.abs A = 0 := matrix_psd_trace_zero (CFC.abs_nonneg A) ht
    have hsq := CFC.abs_mul_abs A
    rw [habs, zero_mul] at hsq
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.star_eq_conjTranspose] using hsq.symm
  · rintro rfl
    simp [signedExtension]
noncomputable def normalizedSignedExtension (f : (Euc ν) → ι → ℝ) (A : SqMat ν) :
    Euc ι :=
  ‖WithLp.toLp 2 (signedExtension f A)‖⁻¹ • WithLp.toLp 2 (signedExtension f A)
lemma Admissible.normalizedSignedExtension_norm {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) (hneq : A ≠ 0) :
    ‖normalizedSignedExtension f A‖ = 1 := by
  have hn : WithLp.toLp 2 (signedExtension f A) ≠ 0 := by
    intro hz
    have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hz
    exact hneq ((hf.signedExtension_eq_zero_iff hA).mp hs)
  simp [normalizedSignedExtension, norm_smul, norm_inv, hn]
omit [Nonempty ν] in
lemma normalizedSignedExtension_odd (f : (Euc ν) → ι → ℝ) (A : SqMat ν) :
    normalizedSignedExtension f (-A) = -normalizedSignedExtension f A := by
  simp [normalizedSignedExtension, signedExtension_odd, WithLp.toLp_neg]
lemma Admissible.normalizedSignedExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (normalizedSignedExtension f) {A : SqMat ν | IsSelfAdjoint A ∧ A ≠ 0} := by
  have hc : ContinuousOn (fun A : SqMat ν => WithLp.toLp 2 (signedExtension f A))
      {A | IsSelfAdjoint A ∧ A ≠ 0} :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hf.signedExtension_continuousOn.mono (fun _ h => h.1))
  apply ContinuousOn.smul (ContinuousOn.inv₀ hc.norm _) hc
  intro A hA
  rw [norm_ne_zero_iff]
  intro hh
  have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hh
  exact hA.2 ((hf.signedExtension_eq_zero_iff hA.1).mp hs)
end SphereExtension
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]
abbrev UpperTriangle (ν : Type*) [LE ν] := {p : ν × ν // p.1 ≤ p.2}
noncomputable def symmetricCoordinates :
    Euc (UpperTriangle ν) →ₗ[ℝ] SqMat ν where
  toFun x i j := if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩
  map_add' x y := by
    ext i j
    change (if h : i ≤ j then (x+y) ⟨(i,j),h⟩ else (x+y) ⟨(j,i),le_of_not_ge h⟩) =
      (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) +
      (if h : i ≤ j then y ⟨(i,j),h⟩ else y ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl
  map_smul' t x := by
    ext i j
    change (if h : i ≤ j then (t • x) ⟨(i,j),h⟩ else (t • x) ⟨(j,i),le_of_not_ge h⟩) =
      t * (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl
omit [Fintype ν] in
lemma symmetricCoordinates_upper (x : Euc (UpperTriangle ν))
    (i j : ν) (hij : i ≤ j) : symmetricCoordinates x i j = x ⟨(i,j), hij⟩ := by
  change (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) = _
  exact dif_pos hij
omit [Fintype ν] in
lemma symmetricCoordinates_selfAdjoint (x : Euc (UpperTriangle ν)) :
    IsSelfAdjoint (symmetricCoordinates x) := by
  change (symmetricCoordinates x)ᴴ = symmetricCoordinates x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (if h : j ≤ i then x ⟨(j,i),h⟩ else x ⟨(i,j),le_of_not_ge h⟩) =
    (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji]
omit [Fintype ν] in
lemma symmetricCoordinates_injective : Function.Injective (symmetricCoordinates (ν := ν)) := by
  intro x y hxy
  apply PiLp.ext
  intro p
  have h := congrArg (fun A : SqMat ν => A p.val.1 p.val.2) hxy
  simpa only [symmetricCoordinates_upper _ _ _ p.property] using h
end SymmetricCoordinates
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section OddSphereMap
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
noncomputable def sphereExtension (f : (Euc ν) → ι → ℝ)
    (x : Euc (UpperTriangle ν)) : Euc ι :=
  normalizedSignedExtension f (symmetricCoordinates x)
lemma Admissible.sphereExtension_norm {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {x : Euc (UpperTriangle ν)} (hx : ‖x‖ = 1) : ‖sphereExtension f x‖ = 1 := by
  apply hf.normalizedSignedExtension_norm (symmetricCoordinates_selfAdjoint x)
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx
omit [Nonempty ν] in
lemma sphereExtension_odd (f : (Euc ν) → ι → ℝ) (x : Euc (UpperTriangle ν)) :
    sphereExtension f (-x) = -sphereExtension f x := by
  simp only [sphereExtension, map_neg, normalizedSignedExtension_odd]
lemma Admissible.sphereExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (sphereExtension f) {x : Euc (UpperTriangle ν) | ‖x‖ = 1} := by
  apply hf.normalizedSignedExtension_continuousOn.comp
    (symmetricCoordinates.continuous_of_finiteDimensional.continuousOn) (fun x hx => ?_)
  refine ⟨symmetricCoordinates_selfAdjoint x, ?_⟩
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx
end OddSphereMap
end
namespace SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
lemma exists_factor_of_ker_le (N : P →ₗ[K] P) (φ : P →ₗ[K] Q)
    (h : LinearMap.ker N ≤ LinearMap.ker φ) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  let ψ₀ : LinearMap.range N →ₗ[K] Q :=
    (N.ker.liftQ φ h).comp N.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := ψ₀.exists_extend
  refine ⟨ψ, ?_⟩
  ext x
  have he := LinearMap.congr_fun hψ ⟨N x, LinearMap.mem_range_self N x⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, ψ₀,
    LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] using he
lemma exists_factor_of_vanish_norm (N : P →ₗ[K] P)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : P →ₗ[K] Q)
    (hφ : φ.comp N = 0) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  apply exists_factor_of_ker_le N φ
  intro x hx
  obtain ⟨y, rfl⟩ := hexact hx
  exact LinearMap.congr_fun hφ y
lemma tower_augmentation_zero (d N : P →ₗ[K] P)
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (n : ℕ) (φ : P →ₗ[K] Q) (hφN : φ.comp N = 0) (hφd : φ.comp d = 0)
    (c : ℕ → P) (htower : ∀ i < n, d (c (i + 1)) = N (c i))
    (htop : N (c n) = 0) : φ (c 0) = 0 := by
  induction n generalizing φ c with
  | zero =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    rw [← hψ, LinearMap.comp_apply, htop, map_zero]
  | succ n ih =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    have hN : (ψ.comp d).comp N = 0 := by
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, hψ, hφd]
    have hd' : (ψ.comp d).comp d = 0 := by
      rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]
    have hh := ih (ψ.comp d) hN hd' (fun i => c (i + 1))
      (fun i hi => htower (i + 1) (Nat.add_lt_add_right hi 1)) htop
    rw [← hψ, LinearMap.comp_apply, ← htower 0 (Nat.zero_lt_succ n)]
    exact hh
end SmithTheory
end
section
namespace SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}
noncomputable def involutionNorm (τ : ι ≃ ι) :
    (ι →₀ ZMod 2) →ₗ[ZMod 2] (ι →₀ ZMod 2) :=
  LinearMap.id + (Finsupp.domLCongr τ).toLinearMap
lemma involutionNorm_apply (τ : ι ≃ ι) (c : ι →₀ ZMod 2) (a : ι) :
    involutionNorm τ c a = c a + c (τ.symm a) := by
  simp [involutionNorm, Finsupp.domCongr, Finsupp.equivMapDomain_apply]
lemma involutionNorm_exact (τ : ι ≃ ι) (hτ : Function.Involutive τ)
    (hfree : ∀ a, τ a ≠ a) :
    LinearMap.ker (involutionNorm τ) ≤ LinearMap.range (involutionNorm τ) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  intro c hc
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  have heq (a : ι) : c (τ a) = c a := by
    have h := congrArg (fun b : ι →₀ ZMod 2 => b a) hc
    simp only [involutionNorm_apply, Finsupp.zero_apply, hsymm] at h
    have hh := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at hh
  refine ⟨c.filter (fun a => a < τ a), ?_⟩
  ext a
  rw [involutionNorm_apply, hsymm]
  simp only [Finsupp.filter_apply, ht]
  by_cases ha : a < τ a
  · simp [ha, not_lt_of_gt ha]
  · have hb : τ a < a := lt_of_le_of_ne (le_of_not_gt ha) (hfree a)
    simp [ha, hb, heq]
lemma involutionNorm_sq (τ : ι ≃ ι) (hτ : Function.Involutive τ) :
    (involutionNorm τ).comp (involutionNorm τ) = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro a
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  simp only [LinearMap.comp_apply, involutionNorm_apply, hsymm, ht,
    LinearMap.zero_apply, Finsupp.zero_apply]
  simp [add_comm, CharTwo.add_self_eq_zero]
end Involution
end SmithTheory
end
section
namespace SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
abbrev F₂ := ZMod 2
abbrev Chain (K : PreComplex V) := {s : Finset V // s ∈ K} →₀ F₂
noncomputable def simplex (K : PreComplex V) (s : Finset V) : Chain K := by
  classical
  exact if h : s ∈ K then Finsupp.single ⟨s, h⟩ 1 else 0
omit [DecidableEq V] in
lemma simplex_of_mem (K : PreComplex V) {s : Finset V} (hs : s ∈ K) :
    simplex K s = Finsupp.single ⟨s, hs⟩ 1 := by simp [simplex, hs]
omit [DecidableEq V] in
@[simp] lemma simplex_empty (K : PreComplex V) : simplex K ∅ = 0 := by
  have h : (∅ : Finset V) ∉ K := fun h => (K.isRelLowerSet_faces h).1.ne_empty rfl
  simp [simplex, h]
noncomputable def boundary (K : PreComplex V) : Chain K →ₗ[F₂] Chain K := by
  classical
  exact Finsupp.linearCombination F₂ (fun s => ∑ a ∈ s.val, simplex K (s.val.erase a))
lemma boundary_simplex (K : PreComplex V) {s : Finset V} (hs : s ∈ K) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  simp [simplex_of_mem K hs, boundary, Finsupp.linearCombination_single]
lemma boundary_simplex_subset (K : PreComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact boundary_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)
omit [DecidableEq V] in
lemma chain_add_self (K : PreComplex V) (c : Chain K) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _
lemma double_erase_sum (K : PreComplex V) (s : Finset V) :
    (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain K := if p.1 = p.2 then 0 else simplex K ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p hp
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self K _
  · intro p hp hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p hp
    exact Prod.swap_swap p
  · intro p hp
    exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))
lemma boundary_twice_simplex (K : PreComplex V)
    {s : Finset V} (hs : s ∈ K) : boundary K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have h (a : V) : boundary K (simplex K (s.erase a)) =
      ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b) :=
    boundary_simplex_subset K hs (Finset.erase_subset a s)
  simp_rw [h]
  exact double_erase_sum K s
lemma boundary_sq (K : PreComplex V) :
    (boundary K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := boundary_twice_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]
noncomputable def augmentation (K : PreComplex V) : Chain K →ₗ[F₂] F₂ :=
  Finsupp.linearCombination F₂ (fun s => if s.val.card = 1 then 1 else 0)
omit [DecidableEq V] in
lemma augmentation_simplex (K : PreComplex V) {s : Finset V} (hs : s ∈ K) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  simp [simplex_of_mem K hs, augmentation, Finsupp.linearCombination_single]
omit [DecidableEq V] in
lemma augmentation_simplex_subset (K : PreComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact augmentation_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)
lemma augmentation_boundary_simplex (K : PreComplex V)
    {s : Finset V} (hs : s ∈ K) : augmentation K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have hh (a : V) (ha : a ∈ s) : augmentation K (simplex K (s.erase a)) =
      if s.card = 2 then 1 else 0 := by
    rw [augmentation_simplex_subset K hs (Finset.erase_subset a s), Finset.card_erase_of_mem ha]
    have hc : s.card - 1 = 1 ↔ s.card = 2 := by omega
    simp only [hc]
  rw [Finset.sum_congr rfl hh]
  by_cases hc : s.card = 2
  · simpa [hc] using (show (2 : F₂) = 0 by decide)
  · simp [hc]
lemma augmentation_boundary (K : PreComplex V) :
    (augmentation K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := augmentation_boundary_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Maps
variable {W : Type*} [DecidableEq W]
noncomputable def mapSimplex (L : PreComplex W) (f : V → W)
    (s : Finset V) : Chain L :=
  if (s.image f).card = s.card then simplex L (s.image f) else 0
omit [DecidableEq V] in
@[simp] lemma mapSimplex_empty (L : PreComplex W) (f : V → W) :
    mapSimplex L f ∅ = 0 := by simp [mapSimplex]
noncomputable def mapChains (K : PreComplex V)
    (L : PreComplex W) (f : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => mapSimplex L f s.val)
omit [DecidableEq V] in
lemma mapChains_simplex (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) : mapChains K L f (simplex K s) = mapSimplex L f s := by
  simp [simplex_of_mem K hs, mapChains, Finsupp.linearCombination_single]
omit [DecidableEq V] in
lemma mapChains_simplex_subset (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    mapChains K L f (simplex K s) = mapSimplex L f s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact mapChains_simplex K L f ((K.isRelLowerSet_faces ht).2 hs hn)
lemma image_erase_of_injOn (f : V → W) (s : Finset V) (h : Set.InjOn f s)
    {a : V} (ha : a ∈ s) : (s.erase a).image f = (s.image f).erase (f a) := by
  ext b
  constructor
  · intro hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact (Finset.mem_erase.mp hx).1 (h (Finset.mem_of_mem_erase hx) ha he)
    · exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨fun he => hne (congrArg f he), hx⟩, rfl⟩
lemma image_erase_collision (f : V → W) (s : Finset V) {a b : V}
    (hb : b ∈ s) (hne : a ≠ b) (he : f a = f b) : (s.erase a).image f = s.image f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases ha : x = a
    · subst x
      exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩, he.symm⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨ha, hx⟩, rfl⟩
lemma mapSimplex_boundary_degenerate (L : PreComplex W)
    (f : V → W) (s : Finset V) (h : ¬ Set.InjOn f s) :
    (∑ a ∈ s, mapSimplex L f (s.erase a)) = 0 := by
  classical
  change ¬ ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b at h
  push Not at h
  obtain ⟨a, ha, b, hb, he, hne⟩ := h
  rw [Finset.sum_eq_add a b hne]
  · have hima := image_erase_collision f s hb hne he
    have himb := image_erase_collision f s ha hne.symm he.symm
    have hc : mapSimplex L f (s.erase a) = mapSimplex L f (s.erase b) := by
      simp only [mapSimplex, hima, himb, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]
    rw [hc]
    exact chain_add_self L _
  · intro c hc hca
    have hn : ¬ Set.InjOn f (s.erase c) := by
      intro hinj
      exact hne (hinj (Finset.mem_erase.mpr ⟨Ne.symm hca.1, ha⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm hca.2, hb⟩) he)
    simp only [mapSimplex, Finset.card_image_iff, if_neg hn]
  · exact fun hn => (hn ha).elim
  · exact fun hn => (hn hb).elim
lemma mapChains_boundary_simplex (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hinj), boundary_simplex L (hf s hs)]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, if_neg (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]
lemma mapChains_boundary (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (boundary L).comp (mapChains K L f) = (mapChains K L f).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_boundary_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]
omit [DecidableEq V] in
lemma mapChains_augmentation_simplex (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, if_pos hcard, augmentation_simplex L (hf s hs), hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]
omit [DecidableEq V] in
lemma mapChains_augmentation (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (augmentation L).comp (mapChains K L f) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_augmentation_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]
end Maps
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Equivariance
variable (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K)
noncomputable def faceEquiv : {s : Finset V // s ∈ K} ≃ {s : Finset V // s ∈ K} where
  toFun s := ⟨s.val.image e, (he s.val).mp s.property⟩
  invFun s := ⟨s.val.image e.symm, (he _).mpr (by simp [Finset.image_image, s.property])⟩
  left_inv s := Subtype.ext (by simp [Finset.image_image])
  right_inv s := Subtype.ext (by simp [Finset.image_image])
lemma faceEquiv_involutive (hi : Function.Involutive e) :
    Function.Involutive (faceEquiv K e he) := by
  intro s
  apply Subtype.ext
  change (s.val.image e).image e = s.val
  rw [Finset.image_image]
  have h : e ∘ e = id := funext hi
  rw [h, Finset.image_id]
lemma faceEquiv_free (hf : ∀ s ∈ K, s.image e ≠ s) :
    ∀ s, faceEquiv K e he s ≠ s := by
  intro s hh
  exact hf s.val s.property (congrArg Subtype.val hh)
lemma mapChains_equiv :
    mapChains K K e = (Finsupp.domLCongr (faceEquiv K e he)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro s r
  have hc : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  simp only [mapChains, Finsupp.linearCombination_single, mapSimplex, if_pos hc,
    simplex_of_mem K ((he s.val).mp s.property), LinearEquiv.coe_toLinearMap,
    Finsupp.domLCongr_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl
end Equivariance
section Cone
noncomputable def cone (K : PreComplex V) (a : V) : Chain K →ₗ[F₂] Chain K :=
  Finsupp.linearCombination F₂ (fun s => if a ∈ s.val then 0 else simplex K (insert a s.val))
lemma cone_simplex (K : PreComplex V) (a : V) {s : Finset V} (hs : s ∈ K) :
    cone K a (simplex K s) = if a ∈ s then 0 else simplex K (insert a s) := by
  simp [simplex_of_mem K hs, cone, Finsupp.linearCombination_single]
lemma cone_boundary_simplex (K : PreComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) (ha : a ∉ s) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases hc : s.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    have hab : a ≠ b := by simpa using ha
    have hs' : ({a} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hinsert).2 (by simp) (Finset.singleton_nonempty a)
    rw [cone_simplex K a hs, if_neg ha, boundary_simplex K hinsert,
      boundary_simplex K hs, augmentation_simplex K hs]
    simp [ha, Finset.erase_insert_of_ne hab]
  · have hn : s.Nonempty := (K.isRelLowerSet_faces hs).1
    have hc' : 2 ≤ s.card := by have := hn.card_pos; omega
    have he (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    have heK (b : V) (hb : b ∈ s) : s.erase b ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (he b hb)
    rw [cone_simplex K a hs, if_neg ha, boundary_simplex K hinsert,
      augmentation_simplex K hs, if_neg hc, zero_smul, add_zero,
      boundary_simplex K hs, map_sum, Finset.sum_insert ha, Finset.erase_insert ha]
    apply congrArg (fun z => simplex K s + z)
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro hh; subst b; exact ha hb
    have hn : a ∉ s.erase b := fun hh => ha (Finset.mem_of_mem_erase hh)
    rw [cone_simplex K a (heK b hb), if_neg hn, Finset.erase_insert_of_ne hab]
lemma cone_boundary_simplex_all (K : PreComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases ha : a ∈ s
  · by_cases hc : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
      have hab : a = b := Finset.mem_singleton.mp ha
      subst b
      rw [cone_simplex K a hs, if_pos ha, map_zero, boundary_simplex K hs,
        augmentation_simplex K hs]
      simp [chain_add_self]
    · have hcn (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
        have hn := (K.isRelLowerSet_faces hs).1.card_pos
        rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
        omega
      have hcon : cone K a (boundary K (simplex K s)) = simplex K s := by
        rw [boundary_simplex K hs, map_sum]
        rw [Finset.sum_eq_single a]
        · rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) (hcn a ha))]
          simp [Finset.insert_erase ha]
        · intro b hb hba
          rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (hcn b hb))]
          simp [Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩]
        · exact fun hn => False.elim (hn ha)
      rw [cone_simplex K a hs, if_pos ha, map_zero, hcon,
        augmentation_simplex K hs, if_neg hc, zero_smul, add_zero, chain_add_self]
  · exact cone_boundary_simplex K a hs hinsert ha
omit [DecidableEq V] in
lemma chain_eq_sum (K : PreComplex V) (c : Chain K) :
    c = ∑ s ∈ c.support, c s • simplex K s.val := by
  conv_lhs => rw [← c.sum_single]
  simp [Finsupp.sum, simplex_of_mem K, Finsupp.smul_single]
lemma cone_boundary (K : PreComplex V) (a : V) (c : Chain K)
    (hc : ∀ s ∈ c.support, insert a s.val ∈ K) :
    boundary K (cone K a c) = c + cone K a (boundary K c) +
      augmentation K c • simplex K {a} := by
  classical
  conv_lhs => rw [chain_eq_sum K c]
  rw [map_sum, map_sum]
  have he (s : { s : Finset V // s ∈ K }) (hs : s ∈ c.support) :
      boundary K (cone K a (c s • simplex K s.val)) =
        c s • simplex K s.val + cone K a (boundary K (c s • simplex K s.val)) +
        augmentation K (c s • simplex K s.val) • simplex K {a} := by
    rw [map_smul, map_smul, cone_boundary_simplex_all K a s.property (hc s hs)]
    simp only [smul_add, map_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← map_sum, ← map_sum, ← Finset.sum_smul, ← map_sum, ← chain_eq_sum K c]
end Cone
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
noncomputable def normMap (K : PreComplex V) (e : V ≃ V) :
    Chain K →ₗ[F₂] Chain K := LinearMap.id + mapChains K K e
lemma normMap_eq (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) :
    normMap K e = SmithTheory.involutionNorm (faceEquiv K e he) := by
  unfold normMap SmithTheory.involutionNorm
  rw [mapChains_equiv K e he]
lemma boundary_normMap (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (boundary K).comp (normMap K e) = (normMap K e).comp (boundary K) := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_id, LinearMap.id_comp,
    mapChains_boundary K K e he]
lemma augmentation_normMap (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (augmentation K).comp (normMap K e) = 0 := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.comp_id, mapChains_augmentation K K e he]
  ext c
  exact CharTwo.add_self_eq_zero _
lemma antipodal_tower_augmentation_zero (K : PreComplex V)
    (e : V ≃ V) (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (n : ℕ) (c : ℕ → Chain K)
    (htower : ∀ i < n, boundary K (c (i+1)) = normMap K e (c i))
    (htop : normMap K e (c n) = 0) : augmentation K (c 0) = 0 := by
  apply SmithTheory.tower_augmentation_zero (boundary K) (normMap K e)
    (boundary_sq K) (boundary_normMap K e (fun s hs => (he s).mp hs))
    _ n (augmentation K) (augmentation_normMap K e (fun s hs => (he s).mp hs))
    (augmentation_boundary K) c htower htop
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)
noncomputable def degreeChains (K : PreComplex V) (d : ℕ) :
    Submodule F₂ (Chain K) := Finsupp.supported F₂ F₂ {s | s.val.card = d}
omit [DecidableEq V] in
lemma simplex_mem_degree (K : PreComplex V) {s : Finset V}
    (hs : s ∈ K) : simplex K s ∈ degreeChains K s.card := by
  rw [simplex_of_mem K hs]
  exact Finsupp.single_mem_supported _ _ rfl
omit [DecidableEq V] [DecidableEq W] in
lemma grade_map (K : PreComplex V) (L : PreComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (d e : ℕ)
    (hT : ∀ s ∈ K, s.card = d → T (simplex K s) ∈ degreeChains L e) :
    degreeChains K d ≤ (degreeChains L e).comap T := by
  rw [degreeChains, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  change T (Finsupp.single s 1) ∈ degreeChains L e
  rw [← simplex_of_mem K s.property]
  exact hT s.val s.property hs
omit [DecidableEq V] in
lemma mapChains_degree (K : PreComplex V) (L : PreComplex W)
    (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree L (hf s hs)
  · exact Submodule.zero_mem _
omit [DecidableEq V] in
lemma degreeChains_eq_bot_of_card_bound (K : PreComplex V) (d : ℕ)
    (hK : ∀ s ∈ K, s.card < d) : degreeChains K d = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply Finsupp.ext
  intro s
  have hne : s.val.card ≠ d := ne_of_lt (hK s.val s.property)
  exact (Finsupp.mem_supported' F₂ c).mp hc s hne
omit [DecidableEq V] in
lemma augmentation_eq_zero_of_degree (K : PreComplex V) (d : ℕ)
    (hd : d ≠ 1) {c : Chain K} (hc : c ∈ degreeChains K d) : augmentation K c = 0 := by
  have hle : degreeChains K d ≤ LinearMap.ker (augmentation K) := by
    rw [degreeChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change augmentation K (Finsupp.single s 1) = 0
    rw [← simplex_of_mem K s.property, augmentation_simplex K s.property]
    simp [show s.val.card ≠ 1 by simpa only [Set.mem_ofPred_eq] using hs ▸ hd]
  exact hle hc
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma mem_support_simplex (K : PreComplex V) (s : Finset V)
    (t : {s : Finset V // s ∈ K}) :
    t ∈ (simplex K s).support ↔ t.val = s := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs, Finsupp.support_single _ one_ne_zero]
    simp only [Finset.mem_singleton, Subtype.ext_iff]
  · simp only [simplex, dif_neg hs, Finsupp.support_zero, Finset.notMem_empty, false_iff]
    intro he
    exact hs (he ▸ t.property)
omit [DecidableEq V] [DecidableEq W] in
lemma support_linearMap (K : PreComplex V) (L : PreComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (c : Chain K)
    {t : {s : Finset W // s ∈ L}} (ht : t ∈ (T c).support) :
    ∃ s ∈ c.support, t ∈ (T (simplex K s.val)).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (T c) t = 0 := by
    conv_lhs => rw [chain_eq_sum K c]
    rw [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    rw [map_smul, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp (hn s hs), smul_zero]
  exact (Finsupp.mem_support_iff.mp ht) hh
lemma support_cone (K : PreComplex V) (a : V) (c : Chain K)
    {t : {s : Finset V // s ∈ K}} (ht : t ∈ (cone K a c).support) :
    ∃ s ∈ c.support, a ∉ s.val ∧ t.val = insert a s.val := by
  obtain ⟨s, hs, ht⟩ := support_linearMap K K (cone K a) c ht
  rw [cone_simplex K a s.property] at ht
  split_ifs at ht with ha
  · simp at ht
  · exact ⟨s, hs, ha, (mem_support_simplex K _ t).mp ht⟩
lemma cone_degree (K : PreComplex V) (a : V) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K (d+1)).comap (cone K a) := by
  intro c hc t ht
  obtain ⟨s, hs, ha, he⟩ := support_cone K a c ht
  change t.val.card = d+1
  rw [he, Finset.card_insert_of_notMem ha, hc hs]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
noncomputable def subdivSimplex (L : PreComplex W) (b : Finset V → W)
    (s : Finset V) : Chain L :=
  if _hs : s.Nonempty then
    if s.card = 1 then simplex L {b s}
    else cone L (b s) (∑ a ∈ s.attach, subdivSimplex L b (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property
@[simp] lemma subdivSimplex_empty (L : PreComplex W) (b : Finset V → W) :
    subdivSimplex L b ∅ = 0 := by rw [subdivSimplex]; simp
lemma subdivSimplex_one (L : PreComplex W) (b : Finset V → W)
    {s : Finset V} (hc : s.card = 1) : subdivSimplex L b s = simplex L {b s} := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [subdivSimplex, dif_pos hn, if_pos hc]
lemma subdivSimplex_many (L : PreComplex W) (b : Finset V → W)
    {s : Finset V} (hn : s.Nonempty) (hc : s.card ≠ 1) :
    subdivSimplex L b s = cone L (b s) (∑ a ∈ s, subdivSimplex L b (s.erase a)) := by
  rw [subdivSimplex, dif_pos hn, if_neg hc]
  exact congrArg (cone L (b s)) (Finset.sum_attach s (fun a : V => subdivSimplex L b (s.erase a)))
def vertexCarrier (b : Finset V → W) (s : Finset V) : Set W :=
  {w | ∃ t : Finset V, t.Nonempty ∧ t ⊆ s ∧ b t = w}
omit [DecidableEq V] [DecidableEq W] in
lemma vertexCarrier_mono (b : Finset V → W) {s t : Finset V} (hst : s ⊆ t) :
    vertexCarrier b s ⊆ vertexCarrier b t := by
  rintro w ⟨u, hu, hus, hb⟩
  exact ⟨u, hu, hus.trans hst, hb⟩
omit [DecidableEq V] [DecidableEq W] in
lemma center_mem_carrier (b : Finset V → W) {s : Finset V} (hs : s.Nonempty) :
    b s ∈ vertexCarrier b s := ⟨s, hs, Finset.Subset.refl _, rfl⟩
lemma support_sum_chains (L : PreComplex W) {α : Type*}
    (s : Finset α) (c : α → Chain L) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (∑ a ∈ s, c a).support) : ∃ a ∈ s, t ∈ (c a).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (∑ a ∈ s, c a) t = 0 := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero (fun a ha => Finsupp.notMem_support_iff.mp (hn a ha))
  exact Finsupp.mem_support_iff.mp ht hh
lemma subdivSimplex_carrier (L : PreComplex W) (b : Finset V → W)
    (s : Finset V) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (subdivSimplex L b s).support) : ↑t.val ⊆ vertexCarrier b s := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, mem_support_simplex] at ht
      rw [ht]
      exact Finset.singleton_subset_set_iff.mpr (center_mem_carrier b hn)
    · rw [subdivSimplex_many L b hn hc] at ht
      obtain ⟨u, hu, _, htu⟩ := support_cone L (b s) _ ht
      obtain ⟨a, ha, hua⟩ := support_sum_chains L s _ hu
      have hu' := ih (s.erase a) (Finset.erase_ssubset ha) hua
      rw [htu, Finset.coe_insert]
      exact Set.insert_subset (center_mem_carrier b hn)
        (hu'.trans (vertexCarrier_mono b (Finset.erase_subset a s)))
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma simplex_mem_degree_all (K : PreComplex V) (s : Finset V) :
    simplex K s ∈ degreeChains K s.card := by
  classical
  by_cases hs : s ∈ K
  · exact simplex_mem_degree K hs
  · simp only [simplex, dif_neg hs]
    exact Submodule.zero_mem _
lemma subdivSimplex_degree (L : PreComplex W) (b : Finset V → W)
    (s : Finset V) : subdivSimplex L b s ∈ degreeChains L s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · rw [subdivSimplex_empty]
      exact Submodule.zero_mem _
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, hc]
      exact simplex_mem_degree_all L {b s}
    · rw [subdivSimplex_many L b hn hc]
      have hsum : (∑ a ∈ s, subdivSimplex L b (s.erase a)) ∈ degreeChains L (s.card-1) := by
        apply Submodule.sum_mem
        intro a ha
        have hh := ih (s.erase a) (Finset.erase_ssubset ha)
        simpa only [Finset.card_erase_of_mem ha] using hh
      have hpos := hn.card_pos
      simpa only [Submodule.mem_comap, Nat.sub_add_cancel hpos] using
        cone_degree L (b s) (s.card-1) hsum
def SubdivisionCarrier (K : PreComplex V) (L : PreComplex W)
    (b : Finset V → W) : Prop :=
  ∀ s ∈ K, ∀ t : Finset W, t.Nonempty → ↑t ⊆ vertexCarrier b s → t ∈ L
omit [DecidableEq V] [DecidableEq W] in
lemma SubdivisionCarrier.center (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) : {b s} ∈ L :=
  hb s hs {b s} (Finset.singleton_nonempty _) (Finset.singleton_subset_set_iff.mpr
    (center_mem_carrier b (K.isRelLowerSet_faces hs).1))
lemma subdivSimplex_augmentation (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    augmentation L (subdivSimplex L b s) = augmentation K (simplex K s) := by
  rw [augmentation_simplex K hs]
  by_cases hc : s.card = 1
  · rw [subdivSimplex_one L b hc, augmentation_simplex L (hb.center K L b hs)]
    simp [hc]
  · rw [if_neg hc]
    exact augmentation_eq_zero_of_degree L _ hc (subdivSimplex_degree L b s)
noncomputable def subdivMap (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => subdivSimplex L b s.val)
lemma subdivMap_simplex (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  simp [simplex_of_mem K hs, subdivMap, Finsupp.linearCombination_single]
lemma subdivMap_simplex_subset (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) : subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact subdivMap_simplex K L b ((K.isRelLowerSet_faces ht).2 hs hn)
lemma subdivMap_augmentation (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (augmentation L).comp (subdivMap K L b) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_augmentation K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]
lemma subdivMap_boundary_simplex (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (boundary K (simplex K s)) =
      ∑ a ∈ s, subdivSimplex L b (s.erase a) := by
  rw [boundary_simplex K hs, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact subdivMap_simplex_subset K L b hs (Finset.erase_subset a s)
lemma subdivSimplex_boundary (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    boundary L (subdivSimplex L b s) = subdivMap K L b (boundary K (simplex K s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn := (K.isRelLowerSet_faces hs).1
    by_cases hc : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [subdivSimplex_one L b hc, boundary_simplex L (hb.center K L b hs),
        boundary_simplex K hs]
      simp
    · have hd : boundary L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have he : boundary L (subdivMap K L b (boundary K (simplex K s))) =
            subdivMap K L b (boundary K (boundary K (simplex K s))) := by
          rw [boundary_simplex K hs]
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rcases (s.erase a).eq_empty_or_nonempty with heq | hne
          · simp [heq]
          · have hK : s.erase a ∈ K := (K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) hne
            rw [subdivMap_simplex K L b hK]
            exact ih (s.erase a) (Finset.erase_ssubset ha) hK
        rw [he, boundary_twice_simplex K hs, map_zero]
      have hε : augmentation L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have hh := LinearMap.congr_fun (subdivMap_augmentation K L b hb)
          (boundary K (simplex K s))
        rw [LinearMap.comp_apply, augmentation_boundary_simplex K hs] at hh
        exact hh
      have hcone : ∀ t ∈ (subdivMap K L b (boundary K (simplex K s))).support,
          insert (b s) t.val ∈ L := by
        rw [subdivMap_boundary_simplex K L b hs]
        intro t ht
        obtain ⟨a, ha, hta⟩ := support_sum_chains L s _ ht
        have ht' := (subdivSimplex_carrier L b _ hta).trans
          (vertexCarrier_mono b (Finset.erase_subset a s))
        apply hb s hs _ (Finset.insert_nonempty _ _)
        rw [Finset.coe_insert]
        exact Set.insert_subset (center_mem_carrier b hn) ht'
      rw [subdivSimplex_many L b hn hc, ← subdivMap_boundary_simplex K L b hs,
        cone_boundary L (b s) _ hcone, hd, hε, map_zero, zero_smul, add_zero, add_zero]
lemma subdivMap_boundary (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (boundary L).comp (subdivMap K L b) = (subdivMap K L b).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_boundary K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W U : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U]
omit [DecidableEq W] [DecidableEq U] in
lemma mapChains_equiv_simplex_all (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (s : Finset V) :
    mapChains K K e (simplex K s) = simplex K (s.image e) := by
  classical
  by_cases hs : s ∈ K
  · rw [mapChains_simplex K K e hs, mapSimplex,
      if_pos (Finset.card_image_iff.mpr e.injective.injOn)]
  · have ht : s.image e ∉ K := (he s).not.mp hs
    simp [simplex, hs, ht]
omit [DecidableEq W] [DecidableEq U] in
lemma cone_equivariant (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (a : V) :
    (mapChains K K e).comp (cone K a) = (cone K (e a)).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hm := mapChains_equiv_simplex_all K e he s.val
  have hc := cone_simplex K a s.property
  have hsc := cone_simplex K (e a) ((he s.val).mp s.property)
  have hh : mapChains K K e (cone K a (simplex K s.val)) =
      cone K (e a) (mapChains K K e (simplex K s.val)) := by
    rw [hc, hm, hsc]
    by_cases ha : a ∈ s.val
    · rw [if_pos ha, if_pos (Finset.mem_image_of_mem e ha), map_zero]
    · have hna : e a ∉ s.val.image e := by
        intro h
        obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
        exact ha (e.injective heq ▸ hb)
      rw [if_neg ha, if_neg hna, mapChains_equiv_simplex_all K e he,
        Finset.image_insert]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]
omit [DecidableEq U] in
lemma subdivSimplex_equivariant (L : PreComplex W)
    (e : V ≃ V) (d : W ≃ W) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) (s : Finset V) :
    mapChains L L d (subdivSimplex L b s) = subdivSimplex L b (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    have hc : (s.image e).card = s.card := Finset.card_image_iff.mpr e.injective.injOn
    by_cases hs : s.card = 1
    · rw [subdivSimplex_one L b hs, subdivSimplex_one L b (hc.trans hs),
        mapChains_equiv_simplex_all L d hd, Finset.image_singleton, hb]
    · rw [subdivSimplex_many L b hn hs,
        subdivSimplex_many L b (hn.image e) (by omega)]
      have hcone := LinearMap.congr_fun (cone_equivariant L d hd (b s))
        (∑ a ∈ s, subdivSimplex L b (s.erase a))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
      rw [hcone, map_sum, hb, Finset.sum_image (fun a _ b _ he => e.injective he)]
      apply congrArg (cone L (d (b s)))
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih (s.erase a) (Finset.erase_ssubset ha), image_erase_of_injOn e s e.injective.injOn ha]
omit [DecidableEq U] in
lemma subdivMap_equivariant (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (mapChains L L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hh : mapChains L L d (subdivMap K L b (simplex K s.val)) =
      subdivMap K L b (mapChains K K e (simplex K s.val)) := by
    rw [subdivMap_simplex K L b s.property, subdivSimplex_equivariant L e d hd b hb,
      mapChains_equiv_simplex_all K e he, subdivMap_simplex K L b ((he s.val).mp s.property)]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]
omit [DecidableEq U] in
lemma subdivMap_norm (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (normMap L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, subdivMap_equivariant K L e d he hd b hb]
omit [DecidableEq U] in
lemma subdivMap_degree (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (subdivMap K L b) := by
  apply grade_map K L _ d d
  intro s hs hsd
  rw [subdivMap_simplex K L b hs, ← hsd]
  exact subdivSimplex_degree L b s
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma linearMap_eq_of_support {K : PreComplex V}
    {M : Type*} [AddCommMonoid M] [Module F₂ M]
    (T U : Chain K →ₗ[F₂] M) (c : Chain K)
    (hc : ∀ s ∈ c.support, T (simplex K s.val) = U (simplex K s.val)) : T c = U c := by
  rw [chain_eq_sum K c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul, hc s hs]
lemma mapChains_boundary_simplex_of_image (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hinj), boundary_simplex L ht]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, if_neg (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]
lemma mapChains_boundary_of_support (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    boundary L (mapChains K L f c) = mapChains K L f (boundary K c) := by
  apply linearMap_eq_of_support ((boundary L).comp (mapChains K L f))
    ((mapChains K L f).comp (boundary K)) c
  intro s hs
  exact mapChains_boundary_simplex_of_image K L f s.property (hc s hs)
omit [DecidableEq V] in
lemma mapChains_augmentation_simplex_of_image (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, if_pos hcard, augmentation_simplex L ht, hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]
omit [DecidableEq V] in
lemma mapChains_augmentation_of_support (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    augmentation L (mapChains K L f c) = augmentation K c := by
  apply linearMap_eq_of_support ((augmentation L).comp (mapChains K L f)) (augmentation K) c
  intro s hs
  exact mapChains_augmentation_simplex_of_image K L f s.property (hc s hs)
omit [DecidableEq V] in
lemma mapChains_degree_all (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _
lemma mapChains_equivariant (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (mapChains L L d).comp (mapChains K L f) =
      (mapChains K L f).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have him : (s.val.image e).image f = (s.val.image f).image d := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf s.val s.property x hx)
  have hcard : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  have hcard' : ((s.val.image f).image d).card = (s.val.image f).card :=
    Finset.card_image_iff.mpr d.injective.injOn
  have hh : mapChains L L d (mapChains K L f (simplex K s.val)) =
      mapChains K L f (mapChains K K e (simplex K s.val)) := by
    rw [mapChains_simplex K L f s.property, mapChains_equiv_simplex_all K e he,
      mapChains_simplex K L f ((he s.val).mp s.property)]
    simp only [mapSimplex, him, hcard, hcard']
    split_ifs
    · exact mapChains_equiv_simplex_all L d hd _
    · exact map_zero _
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]
lemma mapChains_norm (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (normMap L d).comp (mapChains K L f) =
      (mapChains K L f).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, mapChains_equivariant K L e d he hd f hf]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
abbrev SignedVertex := ℕ × Bool
def flip : SignedVertex ≃ SignedVertex :=
  Equiv.prodCongr (Equiv.refl ℕ) Equiv.boolNot
@[simp] lemma flip_apply (v : SignedVertex) : flip v = (v.1, !v.2) := rfl
lemma flip_involutive : Function.Involutive flip := by
  intro v
  simp
lemma flip_ne (v : SignedVertex) : flip v ≠ v := by
  intro equality
  exact Bool.not_ne_self v.2 (congrArg Prod.snd equality)
def cross (n : ℕ) : PreComplex SignedVertex where
  faces := {s | s.Nonempty ∧ (∀ v ∈ s, v.1 < n) ∧ Set.InjOn Prod.fst (s : Set SignedVertex)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, fun v hv => hs.2.1 v (hts hv), hs.2.2.mono hts⟩
lemma cross_flip_forward (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image flip ∈ cross n := by
  refine ⟨hs.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact hs.2.1 w hw
  · intro v hv w hw he
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg flip (hs.2.2 hv' hw' he)
lemma cross_flip (n : ℕ) (s : Finset SignedVertex) :
    s ∈ cross n ↔ s.image flip ∈ cross n := by
  refine ⟨cross_flip_forward n s, ?_⟩
  intro hs
  have h := cross_flip_forward n _ hs
  rw [Finset.image_image] at h
  have hh : flip ∘ flip = id := funext flip_involutive
  simpa only [hh, Finset.image_id] using h
lemma cross_free (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image flip ≠ s := by
  intro he
  obtain ⟨v, hv⟩ := hs.1
  have hv' : flip v ∈ s := he ▸ Finset.mem_image_of_mem flip hv
  exact flip_ne v (hs.2.2 hv' hv rfl)
lemma cross_card (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) : s.card ≤ n := by
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hs.2.2).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv))
    _ = n := Finset.card_range n
lemma cross_singleton (n i : ℕ) (hi : i < n) (b : Bool) :
    ({(i,b)} : Finset SignedVertex) ∈ cross n := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · simpa using hi
  · simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (i,b)
lemma cross_insert (n i : ℕ) (hi : i < n) (s : Finset SignedVertex)
    (hs : s ∈ cross n) (hsi : ∀ v ∈ s, v.1 < i) (b : Bool) :
    insert (i,b) s ∈ cross n := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hi
    · exact hs.2.1 v hv
  · intro v hv w hw he
    rcases Finset.mem_insert.mp hv with rfl | hv <;>
      rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · exact False.elim ((ne_of_lt (hsi w hw)) he.symm)
    · exact False.elim ((ne_of_lt (hsi v hv)) he)
    · exact hs.2.2 hv hw he
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma support_mapChains_injective (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (hf : Function.Injective f)
    (c : Chain K) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (mapChains K L f c).support) :
    ∃ s ∈ c.support, t.val = s.val.image f := by
  obtain ⟨s, hs, hst⟩ := support_linearMap K L (mapChains K L f) c ht
  rw [mapChains_simplex K L f s.property, mapSimplex,
    if_pos (Finset.card_image_iff.mpr hf.injOn), mem_support_simplex] at hst
  exact ⟨s, hs, hst⟩
lemma normMap_sq (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e) :
    (normMap K e).comp (normMap K e) = 0 := by
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_sq _ (faceEquiv_involutive K e he hi)
lemma normMap_degree (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K d).comap (normMap K e) := by
  intro c hc
  exact (degreeChains K d).add_mem hc (mapChains_degree K K e he d hc)
noncomputable def crossTower (n : ℕ) : ℕ → Chain (cross n)
  | 0 => simplex (cross n) {(0,false)}
  | i+1 => cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i))
lemma crossTower_support (n i : ℕ) {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (crossTower n i).support) : ∀ v ∈ s.val, v.1 ≤ i := by
  induction i generalizing s with
  | zero =>
    have he := (mem_support_simplex (cross n) {(0,false)} s).mp hs
    rw [he]
    intro v hv
    have he' := Finset.mem_singleton.mp hv
    exact he' ▸ Nat.le_refl 0
  | succ i ih =>
    obtain ⟨t, ht, _, he⟩ := support_cone (cross n) (i+1,false) _ hs
    rw [he]
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact le_rfl
    · have hu : t ∈ (crossTower n i).support ∪
          (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
        Finsupp.support_add ht
      rcases Finset.mem_union.mp hu with ht | ht
      · exact (ih ht v hv).trans (Nat.le_succ i)
      · obtain ⟨u, hu, he⟩ := support_mapChains_injective (cross n) (cross n) flip
          flip.injective _ ht
        rw [he] at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (ih hu w hw).trans (Nat.le_succ i)
lemma crossTower_degree (n i : ℕ) : crossTower n i ∈ degreeChains (cross n) (i+1) := by
  induction i with
  | zero => exact simplex_mem_degree_all (cross n) {(0,false)}
  | succ i ih =>
    exact cone_degree (cross n) (i+1,false) (i+1)
      (normMap_degree (cross n) flip (cross_flip_forward n) (i+1) ih)
lemma crossTower_cone_faces (n i : ℕ) (hi : i+1 < n)
    {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (normMap (cross n) flip (crossTower n i)).support) :
    insert (i+1,false) s.val ∈ cross n := by
  apply cross_insert n (i+1) hi s.val s.property
  intro v hv
  have hu : s ∈ (crossTower n i).support ∪
      (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
    Finsupp.support_add hs
  rcases Finset.mem_union.mp hu with hs | hs
  · exact Nat.lt_succ_of_le (crossTower_support n i hs v hv)
  · obtain ⟨t, ht, he⟩ := support_mapChains_injective (cross n) (cross n) flip
      flip.injective _ hs
    rw [he] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.lt_succ_of_le (crossTower_support n i ht w hw)
lemma crossTower_norm_boundary (n i : ℕ) (hi : i < n) :
    boundary (cross n) (normMap (cross n) flip (crossTower n i)) = 0 := by
  induction i with
  | zero =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n 0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n) (simplex (cross n) {(0,false)})) = 0
    rw [boundary_simplex (cross n) (cross_singleton n 0 hi false)]
    simp
  | succ i ih =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n (i+1))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n)
      (cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i)))) = 0
    rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
      ih (by omega)]
    have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n i)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
    rw [ha, map_zero, zero_smul, add_zero, add_zero]
    exact LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _
lemma crossTower_boundary (n i : ℕ) (hi : i+1 < n) :
    boundary (cross n) (crossTower n (i+1)) = normMap (cross n) flip (crossTower n i) := by
  change boundary (cross n) (cone (cross n) (i+1,false)
    (normMap (cross n) flip (crossTower n i))) = _
  rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
    crossTower_norm_boundary n i (by omega)]
  have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
    (crossTower n i)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
  rw [ha, map_zero, zero_smul, add_zero, add_zero]
lemma crossTower_augmentation (n : ℕ) (hn : 0 < n) :
    augmentation (cross n) (crossTower n 0) = 1 := by
  rw [crossTower, augmentation_simplex (cross n) (cross_singleton n 0 hn false)]
  simp
end SimplicialChains
end
section
namespace SimplicialChains
lemma cross_chain_dimension_bound (n m : ℕ)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross m))
    (hd : (boundary (cross m)).comp T = T.comp (boundary (cross n)))
    (hN : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip))
    (ha : (augmentation (cross m)).comp T = augmentation (cross n))
    (hgrade : ∀ d, degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap T) :
    n ≤ m := by
  by_contra hnm
  have hmn : m < n := Nat.lt_of_not_ge hnm
  let c : ℕ → Chain (cross m) := fun i => T (crossTower n i)
  have hstep : ∀ i < m, boundary (cross m) (c (i+1)) =
      normMap (cross m) flip (c i) := by
    intro i hi
    change boundary (cross m) (T (crossTower n (i+1))) =
      normMap (cross m) flip (T (crossTower n i))
    rw [← LinearMap.comp_apply, hd, LinearMap.comp_apply,
      crossTower_boundary n i (by omega), ← LinearMap.comp_apply, ← hN,
      LinearMap.comp_apply]
  have htop : c m = 0 := by
    have hg := hgrade (m+1) (crossTower_degree n m)
    change c m ∈ degreeChains (cross m) (m+1) at hg
    rw [degreeChains_eq_bot_of_card_bound (cross m) (m+1)
      (fun s hs => Nat.lt_succ_of_le (cross_card m s hs)), Submodule.mem_bot] at hg
    exact hg
  have hh := antipodal_tower_augmentation_zero (cross m) flip (cross_flip m)
    flip_involutive (cross_free m) m c hstep (by rw [htop, map_zero])
  change augmentation (cross m) (T (crossTower n 0)) = 0 at hh
  rw [← LinearMap.comp_apply, ha, crossTower_augmentation n (by omega)] at hh
  exact one_ne_zero hh
end SimplicialChains
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def barycenter (s : Finset E) : E := (s.card : ℝ)⁻¹ • ∑ x ∈ s, x
lemma barycenter_eq_centerMass (s : Finset E) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) id := by
  simp [barycenter, Finset.centerMass]
lemma barycenter_mem_convex {A : Set E} (hA : Convex ℝ A) {s : Finset E}
    (hs : s.Nonempty) (hsA : (s : Set E) ⊆ A) : barycenter s ∈ A := by
  rw [barycenter_eq_centerMass]
  apply hA.centerMass_mem
  · intro x hx; exact zero_le_one
  · simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card)
  · intro x hx; exact hsA hx
lemma barycenter_norm_le {s : Finset E} (hs : s.Nonempty) {D : ℝ}
    (hD : ∀ x ∈ s, ‖x‖ ≤ D) : ‖barycenter s‖ ≤ D := by
  have h := barycenter_mem_convex (convex_closedBall (0 : E) D) hs (A := Metric.closedBall 0 D)
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hD x hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h
lemma barycenter_inner {s : Finset E} (hs : s.Nonempty) (w : E)
    (hw : ∀ x ∈ s, ⟪w,x⟫ = 1) : ⟪w,barycenter s⟫ = 1 := by
  rw [barycenter, real_inner_smul_right, inner_sum]
  simp only [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero)
def hemisphereComplex (R : ℝ) : PreComplex E where
  faces := {s | s.Nonempty ∧ ∃ w : E, ‖w‖ ≤ R ∧ ∀ x ∈ s, ‖x‖ ≤ 1 ∧ ⟪w,x⟫ = 1}
  isRelLowerSet_faces := by
    rintro s ⟨hs, w, hw, hs'⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, w, hw, fun x hx => hs' x (hts hx)⟩
lemma barycenter_sub_eq {s : Finset E} (hs : s.Nonempty) (x : E) :
    barycenter s - x = (s.card : ℝ)⁻¹ • ∑ y ∈ s, (y-x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]
  rfl
lemma barycenter_dist_vertex [DecidableEq E] {s : Finset E} {x : E} (hx : x ∈ s)
    {D : ℝ} (hD : ∀ y ∈ s, ∀ z ∈ s, dist y z ≤ D) :
    dist (barycenter s) x ≤ ((s.card : ℝ)-1) / s.card * D := by
  have hs : s.Nonempty := ⟨x,hx⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [dist_eq_norm, barycenter_sub_eq hs x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  have hh : (∑ y ∈ s, (y-x)) = ∑ y ∈ s.erase x, (y-x) := by
    rw [← Finset.sum_erase_add _ _ hx]
    simp
  rw [hh]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ y ∈ s.erase x, (y-x)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, ‖y-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hc))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hc))
      apply Finset.sum_le_sum
      intro y hy
      simpa only [dist_eq_norm] using hD y (Finset.mem_of_mem_erase hy) x hx
    _ = ((s.card : ℝ)-1) / s.card * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub hs.card_pos, Nat.cast_one]
      ring
lemma barycenter_dist_carrier [DecidableEq E] {s t : Finset E} (ht : t.Nonempty)
    (hts : t ⊆ s) {D : ℝ} (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    dist (barycenter s) (barycenter t) ≤ ((s.card : ℝ)-1) / s.card * D := by
  have h := barycenter_mem_convex
    (convex_closedBall (barycenter s) (((s.card : ℝ)-1) / s.card * D)) ht
    (fun x hx => (Metric.mem_closedBall').mpr (barycenter_dist_vertex (hts hx) hD))
  exact (Metric.mem_closedBall').mp h
lemma barycenter_mesh_factor {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    ((a : ℝ)-1) / a ≤ ((n : ℝ)-1) / n := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ha han
  apply (div_le_div_iff₀ ha' hn').mpr
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  nlinarith
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]
lemma barycenter_neg (s : Finset E) : barycenter (s.image Neg.neg) = -barycenter s := by
  rw [barycenter, Finset.card_image_iff.mpr neg_injective.injOn,
    Finset.sum_image neg_injective.injOn, Finset.sum_neg_distrib,
    smul_neg, barycenter]
lemma hemisphere_neg (R : ℝ) (s : Finset E) :
    s ∈ hemisphereComplex R ↔ s.image Neg.neg ∈ hemisphereComplex R := by
  constructor
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨hn.image _, -w, by simpa using hw, ?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa using hh y hy
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨Finset.image_nonempty.mp hn, -w, by simpa using hw, ?_⟩
    intro x hx
    have h := hh (-x) (Finset.mem_image_of_mem Neg.neg hx)
    simpa using h
omit [DecidableEq E] in
lemma hemisphere_subdivision_carrier (R : ℝ) :
    SubdivisionCarrier (hemisphereComplex R : PreComplex E)
      (hemisphereComplex R) barycenter := by
  rintro s ⟨hn,w,hw,hh⟩ t ht hts
  refine ⟨ht,w,hw,?_⟩
  intro x hx
  obtain ⟨u,hu,hus,rfl⟩ := hts hx
  exact ⟨barycenter_norm_le hu (fun y hy => (hh y (hus hy)).1),
    barycenter_inner hu w (fun y hy => (hh y (hus hy)).2)⟩
lemma subdivSimplex_mesh (R : ℝ) (s : Finset E) (n : ℕ) (hsn : s.card ≤ n)
    (D : ℝ) (hD : 0 ≤ D) (hsD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (subdivSimplex (hemisphereComplex R) barycenter s).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ ((n : ℝ)-1) / n * D := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    have hfac : 0 ≤ ((n : ℝ)-1) / n := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hn.card_pos hsn
      exact div_nonneg (by linarith) (by positivity)
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one _ _ hc, mem_support_simplex] at ht
      intro x hx y hy
      rw [ht, Finset.mem_singleton] at hx hy
      subst x; subst y
      simpa only [dist_self] using mul_nonneg hfac hD
    · rw [subdivSimplex_many _ _ hn hc] at ht
      obtain ⟨u,hu,_,htu⟩ := support_cone _ (barycenter s) _ ht
      obtain ⟨a,ha,hua⟩ := support_sum_chains _ s _ hu
      have hsmall := ih (s.erase a) (Finset.erase_ssubset ha)
        (le_trans (Finset.card_le_card (Finset.erase_subset a s)) hsn)
        (fun x hx y hy => hsD x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) hua
      have hcarrier := (subdivSimplex_carrier _ barycenter _ hua).trans
        (vertexCarrier_mono barycenter (Finset.erase_subset a s))
      have hcenter (x : E) (hx : x ∈ u.val) :
          dist (barycenter s) x ≤ ((n : ℝ)-1) / n * D := by
        obtain ⟨v,hv,hvs,rfl⟩ := hcarrier hx
        exact (barycenter_dist_carrier hv hvs hsD).trans
          (mul_le_mul_of_nonneg_right (barycenter_mesh_factor hn.card_pos hsn) hD)
      intro x hx y hy
      rw [htu, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simpa only [dist_self] using mul_nonneg hfac hD
      · exact hcenter y hy
      · rw [dist_comm]; exact hcenter x hx
      · exact hsmall x hx y hy
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
noncomputable def crossEmbedding (n : ℕ) (v : SignedVertex) : Euc (Fin n) :=
  if h : v.1 < n then (if v.2 then (-1:ℝ) else 1) • EuclideanSpace.single ⟨v.1,h⟩ 1 else 0
lemma crossEmbedding_norm (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ‖crossEmbedding n v‖ = 1 := by
  simp only [crossEmbedding, dif_pos hv, norm_smul, PiLp.norm_single]
  cases v.2 <;> norm_num
lemma crossEmbedding_flip (n : ℕ) (v : SignedVertex) :
    crossEmbedding n (flip v) = -crossEmbedding n v := by
  rcases v with ⟨i,b⟩
  cases b <;> simp only [crossEmbedding, flip_apply] <;> split_ifs <;> simp_all
lemma crossEmbedding_inner_ne (n : ℕ) {v w : SignedVertex}
    (hvw : v.1 ≠ w.1) : ⟪crossEmbedding n v, crossEmbedding n w⟫ = 0 := by
  unfold crossEmbedding
  split_ifs <;> simp_all [EuclideanSpace.inner_single_left]
lemma crossEmbedding_inner_self (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ⟪crossEmbedding n v, crossEmbedding n v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, crossEmbedding_norm n v hv]
  norm_num
lemma crossEmbedding_face (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image (crossEmbedding n) ∈ hemisphereComplex (n:ℝ) := by
  refine ⟨hs.1.image _, ∑ v ∈ s, crossEmbedding n v, ?_, ?_⟩
  · calc
      ‖∑ v ∈ s, crossEmbedding n v‖ ≤ ∑ v ∈ s, ‖crossEmbedding n v‖ := norm_sum_le _ _
      _ = s.card := by simp only [Finset.sum_congr rfl (fun v hv => crossEmbedding_norm n v (hs.2.1 v hv)), Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (n:ℝ) := by exact_mod_cast cross_card n s hs
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨le_of_eq (crossEmbedding_norm n v (hs.2.1 v hv)), ?_⟩
    rw [sum_inner, Finset.sum_eq_single v]
    · exact crossEmbedding_inner_self n v (hs.2.1 v hv)
    · intro w hw hwv
      exact crossEmbedding_inner_ne n (fun he => hwv (hs.2.2 hw hv he))
    · exact fun hn => False.elim (hn hv)
noncomputable def crossGeometricMap (n : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreComplex (Euc (Fin n))) :=
  mapChains (cross n) (hemisphereComplex (n:ℝ)) (crossEmbedding n)
lemma crossGeometricMap_boundary (n : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (boundary (cross n)) :=
  mapChains_boundary _ _ _ (crossEmbedding_face n)
lemma crossGeometricMap_augmentation (n : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      augmentation (cross n) := mapChains_augmentation _ _ _ (crossEmbedding_face n)
lemma crossGeometricMap_degree (n d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (crossGeometricMap n) := mapChains_degree _ _ _ (crossEmbedding_face n) d
lemma crossGeometricMap_norm (n : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (normMap (cross n) flip) := by
  apply mapChains_norm _ _ flip (Equiv.neg _) (cross_flip n) (hemisphere_neg (n:ℝ))
  intro s hs x hx
  exact crossEmbedding_flip n x
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]
noncomputable def refinement (R : ℝ) : ℕ →
    Chain (hemisphereComplex R : PreComplex E) →ₗ[F₂]
      Chain (hemisphereComplex R : PreComplex E)
  | 0 => LinearMap.id
  | r+1 => (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter).comp
      (refinement R r)
lemma refinement_boundary (R : ℝ) (r : ℕ) :
    (boundary (hemisphereComplex R : PreComplex E)).comp (refinement R r) =
      (refinement R r).comp (boundary (hemisphereComplex R)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc, subdivMap_boundary _ _ _ (hemisphere_subdivision_carrier R),
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]
lemma refinement_augmentation (R : ℝ) (r : ℕ) :
    (augmentation (hemisphereComplex R : PreComplex E)).comp
      (refinement R r) = augmentation (hemisphereComplex R) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_augmentation _ _ _ (hemisphere_subdivision_carrier R), ih]
lemma refinement_norm (R : ℝ) (r : ℕ) :
    (normMap (hemisphereComplex R : PreComplex E) (Equiv.neg E)).comp
      (refinement R r) = (refinement R r).comp (normMap (hemisphereComplex R) (Equiv.neg E)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_norm _ _ (Equiv.neg E) (Equiv.neg E) (hemisphere_neg R) (hemisphere_neg R)
        barycenter (barycenter_neg), LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]
lemma refinement_degree (R : ℝ) (r d : ℕ) :
    degreeChains (hemisphereComplex R : PreComplex E) d ≤
      (degreeChains (hemisphereComplex R) d).comap (refinement R r) := by
  induction r with
  | zero => intro c hc; exact hc
  | succ r ih =>
    intro c hc
    change subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c) ∈ degreeChains (hemisphereComplex R) d
    exact subdivMap_degree (hemisphereComplex R : PreComplex E)
      (hemisphereComplex R) barycenter d (ih hc)
lemma refinement_mesh (R : ℝ) (r n : ℕ) {c : Chain (hemisphereComplex R : PreComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) n) {D : ℝ} (hD : 0 ≤ D)
    (hmesh : ∀ s ∈ c.support, ∀ x ∈ s.val, ∀ y ∈ s.val, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * D := by
  induction r generalizing t with
  | zero => simpa only [refinement, LinearMap.id_apply, pow_zero, one_mul] using hmesh t ht
  | succ r ih =>
    change t ∈ (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c)).support at ht
    obtain ⟨s,hs,hts⟩ := support_linearMap _ _ _ _ ht
    rw [subdivMap_simplex _ _ _ s.property] at hts
    have hdeg := refinement_degree R r n hc hs
    change s.val.card = n at hdeg
    have hn : 0 < n := hdeg ▸ s.property.1.card_pos
    have hfac : 0 ≤ ((n:ℝ)-1)/n := by
      have hh : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (by linarith) (by positivity)
    have hh := subdivSimplex_mesh R s.val n (le_of_eq hdeg)
      ((((n:ℝ)-1)/n)^r * D) (mul_nonneg (pow_nonneg hfac _) hD) (ih hs) hts
    simpa only [pow_succ', mul_assoc] using hh
omit [DecidableEq E] in
lemma hemisphere_mesh_two (R : ℝ) {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ 2 := by
  obtain ⟨_, _, _, unit_norm⟩ := hs
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 := by linarith [(unit_norm x hx).1, (unit_norm y hy).1]
lemma refinement_mesh_uniform (R : ℝ) (r n d : ℕ) (hd : d ≤ n)
    {c : Chain (hemisphereComplex R : PreComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) d)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  have hdeg := refinement_degree R r d hc ht
  have htpos := t.property.1.card_pos
  change t.val.card = d at hdeg
  have hdpos : 0 < d := hdeg ▸ htpos
  have hfac : 0 ≤ ((d:ℝ)-1)/d := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast hdpos
    exact div_nonneg (by linarith) (by positivity)
  have hm := refinement_mesh R r d hc (D := 2) (by norm_num)
    (fun simplex _ _ first_mem _ second_mem =>
      hemisphere_mesh_two R simplex.property first_mem second_mem) ht
  intro x hx y hy
  exact (hm x hx y hy).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hfac (barycenter_mesh_factor hdpos hd) r) (by norm_num))
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
noncomputable def maxIndex {m : ℕ} [NeZero m] (g : Fin m → ℝ) : Fin m :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose
lemma maxIndex_le {m : ℕ} [NeZero m] (g : Fin m → ℝ) (i : Fin m) :
    g i ≤ g (maxIndex g) :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ _)
noncomputable def peakIndex {m : ℕ} [NeZero m] (y : Euc (Fin m)) : Fin m :=
  maxIndex (fun i => |y i|)
lemma peakIndex_neg {m : ℕ} [NeZero m] (y : Euc (Fin m)) :
    peakIndex (-y) = peakIndex y := by
  unfold peakIndex
  congr 1
  ext i
  simp
lemma euclidean_norm_le_sum_abs {m : ℕ} (y : Euc (Fin m)) :
    ‖y‖ ≤ ∑ i, |y i| := by
  have hy : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext i
    simp
  calc
    ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := congrArg norm hy
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| := by simp
lemma peak_large {m : ℕ} [NeZero m] (y : Euc (Fin m)) (hy : ‖y‖ = 1) :
    (1:ℝ) / m ≤ |y (peakIndex y)| := by
  have h := euclidean_norm_le_sum_abs y
  rw [hy] at h
  have hsum : ∑ i : Fin m, |y i| ≤ (m:ℝ) * |y (peakIndex y)| := by
    calc
      ∑ i : Fin m, |y i| ≤ ∑ _ : Fin m, |y (peakIndex y)| :=
        Finset.sum_le_sum (fun i _ => maxIndex_le (fun j => |y j|) i)
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)
noncomputable def sphereLabel {m : ℕ} [NeZero m] (y : Euc (Fin m)) : SignedVertex :=
  ((peakIndex y).val, decide (y (peakIndex y) < 0))
lemma sphereLabel_bound {m : ℕ} [NeZero m] (y : Euc (Fin m)) :
    (sphereLabel y).1 < m := (peakIndex y).isLt
lemma sphereLabel_neg {m : ℕ} [NeZero m] (y : Euc (Fin m)) (hy : ‖y‖ = 1) :
    sphereLabel (-y) = flip (sphereLabel y) := by
  have hpeak : y (peakIndex y) ≠ 0 := by
    have h := peak_large y hy
    have hm : (0:ℝ) < (1:ℝ)/m := div_pos zero_lt_one (by exact_mod_cast NeZero.pos m)
    intro he
    rw [he, abs_zero] at h
    linarith
  apply Prod.ext
  · simp only [sphereLabel, peakIndex_neg, flip_apply]
  · simp only [sphereLabel, peakIndex_neg, flip_apply, PiLp.neg_apply]
    by_cases h : y (peakIndex y) < 0
    · have h' : ¬ -y (peakIndex y) < 0 := by linarith
      simp [h,h']
    · have h' : -y (peakIndex y) < 0 := by rcases lt_or_gt_of_ne hpeak with hn | hp <;> linarith
      simp [h,h']
lemma sphereLabel_compatible {m : ℕ} [NeZero m]
    (y z : Euc (Fin m)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hd : dist y z < (1:ℝ)/m) (hi : (sphereLabel y).1 = (sphereLabel z).1) :
    sphereLabel y = sphereLabel z := by
  have he : peakIndex y = peakIndex z := Fin.ext hi
  have hcoord : |y (peakIndex y) - z (peakIndex y)| ≤ dist y z := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y z (peakIndex y)
  have hym := peak_large y hy
  have hzm := peak_large z hz
  rw [← he] at hzm
  apply Prod.ext hi
  change decide (y (peakIndex y) < 0) = decide (z (peakIndex z) < 0)
  rw [← he]
  congr 1
  apply propext
  constructor
  · intro hyneg
    by_contra hzneg
    have hzpos := le_of_not_gt hzneg
    rw [abs_of_neg hyneg] at hym
    rw [abs_of_nonpos (by linarith)] at hcoord
    linarith
  · intro hzneg
    by_contra hyneg
    have hypos := le_of_not_gt hyneg
    rw [abs_of_neg hzneg] at hzm
    rw [abs_of_nonneg (by linarith)] at hcoord
    linarith
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
noncomputable def fineCrossMap (n r : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreComplex (Euc (Fin n))) :=
  (refinement (n:ℝ) r).comp (crossGeometricMap n)
lemma fineCrossMap_boundary (n r : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (boundary (cross n)) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_boundary,
    LinearMap.comp_assoc, crossGeometricMap_boundary, ← LinearMap.comp_assoc]
lemma fineCrossMap_augmentation (n r : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) = augmentation (cross n) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_augmentation,
    crossGeometricMap_augmentation]
lemma fineCrossMap_norm (n r : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (normMap (cross n) flip) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_norm,
    LinearMap.comp_assoc, crossGeometricMap_norm, ← LinearMap.comp_assoc]
lemma fineCrossMap_degree (n r d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (fineCrossMap n r) := by
  intro c hc
  change refinement (n:ℝ) r (crossGeometricMap n c) ∈ degreeChains (hemisphereComplex (n:ℝ)) d
  exact refinement_degree (E := Euc (Fin n)) (n:ℝ) r d
    (crossGeometricMap_degree n d hc)
lemma fineCrossMap_simplex_mesh (n r : ℕ) {s : Finset SignedVertex} (hs : s ∈ cross n)
    {t : {s : Finset (Euc (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  apply refinement_mesh_uniform (n:ℝ) r n s.card (cross_card n s hs)
    (crossGeometricMap_degree n s.card (simplex_mem_degree _ hs)) ht
def annulus (n : ℕ) : Set (Euc (Fin n)) :=
  {x | (1:ℝ)/n ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
lemma annulus_compact (n : ℕ) : IsCompact (annulus n) := by
  apply (isCompact_closedBall (0 : Euc (Fin n)) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
lemma hemisphere_vertex_annulus (n : ℕ) (hn : 0 < n)
    {s : Finset (Euc (Fin n))} (hs : s ∈ hemisphereComplex (n:ℝ))
    {x : Euc (Fin n)} (hx : x ∈ s) : x ∈ annulus n := by
  obtain ⟨_,w,hw,hh⟩ := hs
  refine ⟨?_,(hh x hx).1⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := real_inner_le_norm w x
  rw [(hh x hx).2] at h
  calc
    1 ≤ ‖w‖ * ‖x‖ := h
    _ ≤ (n:ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)
    _ = ‖x‖ * (n:ℝ) := mul_comm _ _
lemma annular_odd_dimension_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : Euc (Fin n) → Euc (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) : n ≤ m := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast hm))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  let K : PreComplex (Euc (Fin n)) := hemisphereComplex (n:ℝ)
  let f : Euc (Fin n) → SignedVertex := fun x => sphereLabel (g x)
  let U : Chain K →ₗ[F₂] Chain (cross m) := mapChains K (cross m) f
  let T : Chain (cross n) →ₗ[F₂] Chain (cross m) := U.comp (fineCrossMap n r)
  have hfine (s : Finset SignedVertex) (hs : s ∈ cross n)
      (t : {s : Finset (Euc (Fin n)) // s ∈ K})
      (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) : t.val.image f ∈ cross m := by
    refine ⟨t.property.1.image _, ?_, ?_⟩
    · intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact sphereLabel_bound (g x)
    · intro v hv w hw he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have hxa := hemisphere_vertex_annulus n hn t.property hx
      have hya := hemisphere_vertex_annulus n hn t.property hy
      apply sphereLabel_compatible (g x) (g y) (hgn x hxa) (hgn y hya) _ he
      exact hclose x hxa y hya ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hmeshδ)
  have hdb : (boundary (cross m)).comp T = T.comp (boundary (cross n)) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : boundary (cross m) (T (simplex (cross n) s.val)) =
        T (boundary (cross n) (simplex (cross n) s.val)) := by
      change boundary (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_boundary_of_support K (cross m) f _ (hfine s.val s.property)]
      have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
      rw [hb]
      rfl
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have haug : (augmentation (cross m)).comp T = augmentation (cross n) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : augmentation (cross m) (T (simplex (cross n) s.val)) =
        augmentation (cross n) (simplex (cross n) s.val) := by
      change augmentation (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_augmentation_of_support K (cross m) f _ (hfine s.val s.property)]
      exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have hnorm : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip) := by
    have hu : (normMap (cross m) flip).comp U = U.comp (normMap K (Equiv.neg _)) := by
      apply mapChains_norm K (cross m) (Equiv.neg _) flip
        (hemisphere_neg (n:ℝ)) (cross_flip m) f
      intro s hs x hx
      have hxa := hemisphere_vertex_annulus n hn hs hx
      change sphereLabel (g (-x)) = flip (sphereLabel (g x))
      rw [hgo x hxa, sphereLabel_neg _ (hgn x hxa)]
    change (normMap (cross m) flip).comp (U.comp (fineCrossMap n r)) =
      (U.comp (fineCrossMap n r)).comp (normMap (cross n) flip)
    rw [← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
      fineCrossMap_norm, ← LinearMap.comp_assoc]
  apply cross_chain_dimension_bound n m T hdb hnorm haug
  intro d c hc
  change mapChains K (cross m) f (fineCrossMap n r c) ∈ degreeChains (cross m) d
  exact mapChains_degree_all K (cross m) f d (fineCrossMap_degree n r d hc)
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
noncomputable def unitRadial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) : E :=
  ‖x‖⁻¹ • x
lemma unitRadial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖unitRadial x‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
lemma unitRadial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    unitRadial (-x) = -unitRadial x := by simp [unitRadial]
lemma unitRadial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : ∀ x ∈ S, x ≠ 0) : ContinuousOn unitRadial S := by
  exact (continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (hS x hx))).smul
    continuous_id.continuousOn
lemma odd_sphere_dimension_bound (n m : ℕ) (hn : 0 < n)
    (f : Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : n ≤ m := by
  by_cases hm : 0 < m
  · have ha : ∀ x ∈ annulus n, x ≠ 0 := by
      intro x hx hzero
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one hn'
      simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
      linarith [hx.1]
    apply annular_odd_dimension_bound n m hn hm (fun x => f (unitRadial x))
    · exact hf.comp (unitRadial_continuousOn ha) (fun x hx => unitRadial_norm (ha x hx))
    · intro x hx
      exact hfn _ (unitRadial_norm (ha x hx))
    · intro x hx
      rw [unitRadial_neg, hfo _ (unitRadial_norm (ha x hx))]
  · have hm0 : m = 0 := by omega
    subst m
    let x : Euc (Fin n) := EuclideanSpace.single ⟨0,hn⟩ 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hzero : f x = 0 := Subsingleton.elim _ _
    have hh := hfn x hx
    rw [hzero, norm_zero] at hh
    exact False.elim (zero_ne_one hh)
noncomputable def dropLast (n : ℕ) :
    Euc (Fin (n+1)) →ₗ[ℝ] Euc (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x i.castSucc)
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl
lemma dropLast_zero_iff (n : ℕ) (x : Euc (Fin (n+1))) :
    dropLast n x = 0 ↔ x = x (Fin.last n) • EuclideanSpace.single (Fin.last n) 1 := by
  constructor
  · intro hx
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have hj := congrArg (fun y : Euc (Fin n) => y j) hx
      simpa [dropLast] using hj
  · intro hx
    rw [hx]
    ext i
    simp [dropLast]
lemma dropLast_nonzero (n : ℕ) (x : Euc (Fin (n+1))) (hx : ‖x‖ = 1)
    (hxp : x ≠ EuclideanSpace.single (Fin.last n) 1)
    (hxm : x ≠ -EuclideanSpace.single (Fin.last n) 1) : dropLast n x ≠ 0 := by
  intro hz
  have he := (dropLast_zero_iff n x).mp hz
  have ha : |x (Fin.last n)| = 1 := by
    conv_rhs => rw [← hx, he]
    simp [norm_smul]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp ha with hp | hm
  · apply hxp
    simpa [hp] using he
  · apply hxm
    simpa [hm] using he
lemma odd_sphere_surjective (n : ℕ)
    (f : Euc (Fin (n+1)) → Euc (Fin (n+1)))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  intro y hy
  by_contra hmiss
  push Not at hmiss
  let e : Euc (Fin (n+1)) := EuclideanSpace.single (Fin.last n) 1
  have he : ‖e‖ = 1 := by simp [e]
  let R : Euc (Fin (n+1)) ≃ₗᵢ[ℝ] Euc (Fin (n+1)) :=
    Submodule.reflection (ℝ ∙ (y-e))ᗮ
  have hRy : R y = e := Submodule.reflection_sub (hy.trans he.symm)
  have hnzero (x : Euc (Fin (n+1))) (hx : ‖x‖ = 1) :
      dropLast n (R (f x)) ≠ 0 := by
    apply dropLast_nonzero n (R (f x)) (by rw [R.norm_map, hfn x hx])
    · intro hp
      exact hmiss x hx (R.injective (hp.trans hRy.symm))
    · intro hm
      have hneg : R (f (-x)) = e := by rw [hfo x hx, map_neg, hm, neg_neg]
      exact hmiss (-x) (by simpa using hx) (R.injective (hneg.trans hRy.symm))
  let g : Euc (Fin (n+1)) → Euc (Fin n) :=
    fun x => unitRadial (dropLast n (R (f x)))
  have hicont : ContinuousOn (fun x => dropLast n (R (f x))) {x | ‖x‖ = 1} :=
    (dropLast n).continuous_of_finiteDimensional.comp_continuousOn (R.continuous.comp_continuousOn hf)
  have hgc : ContinuousOn g {x | ‖x‖ = 1} := by
    apply (unitRadial_continuousOn (S := {z : Euc (Fin n) | z ≠ 0})
      (fun _ h => h)).comp hicont
    exact fun x hx => hnzero x hx
  have hgn (x) (hx : ‖x‖ = 1) : ‖g x‖ = 1 := unitRadial_norm (hnzero x hx)
  have hgo (x) (hx : ‖x‖ = 1) : g (-x) = -g x := by
    dsimp [g]
    rw [hfo x hx, map_neg, map_neg, unitRadial_neg]
  have hd := odd_sphere_dimension_bound (n+1) n (by omega) g hgc hgn hgo
  omega
end SimplicialChains
end
section
namespace SimplicialChains
lemma odd_sphere_dimension_bound_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : Euc α → Euc β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : Fintype.card α ≤ Fintype.card β := by
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin β)
  apply odd_sphere_dimension_bound (Fintype.card α) (Fintype.card β)
    Fintype.card_pos (fun x => B (f (A.symm x)))
  · exact B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx))
  · intro x hx
    rw [B.norm_map, hfn _ (by simpa using hx)]
  · intro x hx
    rw [map_neg, hfo _ (by simpa using hx), map_neg]
lemma odd_sphere_surjective_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (hc : Fintype.card α = Fintype.card β)
    (f : Euc α → Euc β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := α)))
  let ea : α ≃ Fin (n+1) := (Fintype.equivFin α).trans (finCongr hn)
  let eb : β ≃ Fin (n+1) := (Fintype.equivFin β).trans (finCongr (hc.symm.trans hn))
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eb
  have hg := odd_sphere_surjective n (fun x => B (f (A.symm x)))
    (B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx)))
    (fun x hx => by rw [B.norm_map, hfn _ (by simpa using hx)])
    (fun x hx => by rw [map_neg, hfo _ (by simpa using hx), map_neg])
  intro y hy
  obtain ⟨x,hx,he⟩ := hg (B y) (by simpa using hy)
  exact ⟨A.symm x, by simpa using hx, B.injective he⟩
end SimplicialChains
section
open scoped RealInnerProductSpace
section LabelBound
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
lemma Admissible.label_bound {f : Euc ν → ι → ℝ} (hf : Admissible f) :
    Fintype.card (UpperTriangle ν) ≤ Fintype.card ι := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_dimension_bound_fintype (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)
lemma Admissible.sphereExtension_surjective {f : Euc ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ sphereExtension f x = y := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_surjective_fintype hc (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)
lemma Admissible.signedExtension_ray {f : Euc ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι)
    {y : ι → ℝ} (hy : y ≠ 0) :
    ∃ A : SqMat ν, IsSelfAdjoint A ∧ ∃ t : ℝ, 0 < t ∧ signedExtension f A = t • y := by
  let Y : Euc ι := WithLp.toLp 2 y
  have hY : Y ≠ 0 := fun hh => hy (WithLp.toLp_injective 2 hh)
  obtain ⟨x,hx,he⟩ := hf.sphereExtension_surjective hc (SimplicialChains.unitRadial Y)
    (SimplicialChains.unitRadial_norm hY)
  let A := symmetricCoordinates x
  have hA : A ≠ 0 := by
    intro hzero
    have hh : x = 0 := symmetricCoordinates_injective (hzero.trans (map_zero _).symm)
    simp [hh] at hx
  have hs : signedExtension f A ≠ 0 := fun hh => hA
    ((hf.signedExtension_eq_zero_iff (symmetricCoordinates_selfAdjoint x)).mp hh)
  let Z : Euc ι := WithLp.toLp 2 (signedExtension f A)
  have hZ : Z ≠ 0 := fun hh => hs (WithLp.toLp_injective 2 hh)
  refine ⟨A, symmetricCoordinates_selfAdjoint x, ‖Z‖ / ‖Y‖,
    div_pos (norm_pos_iff.mpr hZ) (norm_pos_iff.mpr hY), ?_⟩
  change ‖Z‖⁻¹ • Z = ‖Y‖⁻¹ • Y at he
  have he' := congrArg (fun z => ‖Z‖ • z) he
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hZ), one_smul, smul_smul,
    ← div_eq_mul_inv] at he'
  exact WithLp.toLp_injective 2 he'
end LabelBound
end
end
section
section
open scoped RealInnerProductSpace
section Restrict
variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
lemma Admissible.comp_isometry {f : V → ι → ℝ} (hf : Admissible f) (e : W →ₗᵢ[ℝ] V) :
    Admissible (fun x => f (e x)) := by
  refine ⟨fun i => (hf.smooth i).comp e.contDiff,?_,?_,?_,?_⟩
  · intro x i
    rw [map_neg,hf.antipodal]
  · intro x hx i
    exact hf.nonneg _ ((e.norm_map x).trans hx) i
  · intro x hx
    exact hf.sum_one _ ((e.norm_map x).trans hx)
  · intro x y hx hy hxy i
    exact hf.orthogonal _ _ ((e.norm_map x).trans hx) ((e.norm_map y).trans hy)
      ((e.inner_map_map x y).trans hxy) i
lemma Admissible.restrict_labels {f : V → ι → ℝ} (hf : Admissible f)
    (s : Finset ι) (hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f x i = 0) :
    Admissible (fun x (i : s) => f x i.val) := by
  classical
  refine ⟨fun i => hf.smooth i.val,fun x i => hf.antipodal x i.val,
    fun x hx i => hf.nonneg x hx i.val,?_,fun x y hx hy hxy i => hf.orthogonal x y hx hy hxy i.val⟩
  intro x hx
  rw [← hf.sum_one x hx]
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hzero x hx i hi)
end Restrict
lemma orthogonal_isometry (k : ℕ) {u : Euc (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : Euc (Fin k) →ₗᵢ[ℝ] Euc (Fin (k+1)),
      ∀ x, ⟪u,e x⟫ = 0 := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (Euc (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_⟩
  intro x
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)
lemma Admissible.support_card_four_le {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {u : Vector4} (hu : ‖u‖ = 1) : (positiveSupport f u).card ≤ 4 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 3)) = 6 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl] at hb
  rw [Fintype.card_fin] at hb
  omega
end
end
section
section
open scoped RealInnerProductSpace
section Chambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def safeNormals (Z : Set E) : Set E := {x | ∀ z ∈ Z, ⟪x,z⟫ ≠ 0}
def signChamber (Z : Set E) (c : E) : Set E := {x | ∀ z ∈ Z, 0 < ⟪c,z⟫ * ⟪x,z⟫}
lemma mem_signChamber_self {Z : Set E} {c : E} (hc : c ∈ safeNormals Z) :
    c ∈ signChamber Z c := by
  intro z hz
  exact mul_self_pos.mpr (hc z hz)
lemma signChamber_subset_safeNormals (Z : Set E) (c : E) :
    signChamber Z c ⊆ safeNormals Z := by
  intro x hx z hz h
  simpa [h] using hx z hz
lemma signChamber_convex (Z : Set E) (c : E) : Convex ℝ (signChamber Z c) := by
  intro x hx y hy a b ha hb hab z hz
  simp only [inner_add_left,real_inner_smul_left,mul_add]
  have h1 := hx z hz
  have h2 := hy z hz
  have hn1 := mul_nonneg ha h1.le
  have hn2 := mul_nonneg hb h2.le
  have he : ⟪c,z⟫ * (a * ⟪x,z⟫) + ⟪c,z⟫ * (b * ⟪y,z⟫) =
      a * (⟪c,z⟫ * ⟪x,z⟫) + b * (⟪c,z⟫ * ⟪y,z⟫) := by ring
  rw [he]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' h1) hn2
  · have hb' : b = 1 := by linarith
    simp [← ha',hb',h2]
lemma signChamber_eq_of_mem {Z : Set E} {c d x : E}
    (hc : x ∈ signChamber Z c) (hd : x ∈ signChamber Z d) :
    signChamber Z c = signChamber Z d := by
  ext y
  constructor <;> intro hy z hz
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h2.1 h3.2 | exact mul_pos_of_neg_of_neg h2.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h1.1 h3.2 | exact mul_pos_of_neg_of_neg h1.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
lemma signChamber_eq_or_disjoint (Z : Set E) (c d : E) :
    signChamber Z c = signChamber Z d ∨ Disjoint (signChamber Z c) (signChamber Z d) := by
  by_cases h : Disjoint (signChamber Z c) (signChamber Z d)
  · exact Or.inr h
  · rw [Set.disjoint_left] at h
    push Not at h
    obtain ⟨x,hc,hd⟩ := h
    exact Or.inl (signChamber_eq_of_mem hc hd)
lemma interior_safe_mem_chamber {Z : Set E} {c x : E}
    (hx : x ∈ interior (safeNormals Z)) (hxc : x ∈ signChamber Z c) :
    x ∈ interior (signChamber Z c) := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hε)
  intro y hy z hz
  have hc := hxc z hz
  have hn : ∀ w ∈ Metric.ball x ε, ⟪w,z⟫ ≠ 0 := fun w hw => hball hw z hz
  have hf : ContinuousOn (fun w : E => ⟪w,z⟫) (Metric.ball x ε) :=
    (continuous_id.inner continuous_const).continuousOn
  have hxball : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  rcases mul_pos_iff.mp hc with hc | hc
  · exact mul_pos hc.1 ((convex_ball x ε).isPreconnected.lt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)
  · exact mul_pos_of_neg_of_neg hc.1 ((convex_ball x ε).isPreconnected.gt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)
lemma interior_safe_mem_own_chamber {Z : Set E} {c : E}
    (hc : c ∈ interior (safeNormals Z)) : c ∈ interior (signChamber Z c) :=
  interior_safe_mem_chamber hc (mem_signChamber_self (interior_subset hc))
lemma compact_finite_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧ K ⊆ ⋃ c ∈ (↑C : Set E), interior (signChamber Z c) := by
  classical
  obtain ⟨C,hCK,hCf,hcover⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun c : E => interior (signChamber Z c)) (fun _ _ => isOpen_interior)
    (fun c hc => Set.mem_iUnion₂.mpr ⟨c,hc,interior_safe_mem_own_chamber (hsub hc)⟩)
  exact ⟨hCf.toFinset,by simpa using hCK,by simpa using hcover⟩
end Chambers
end
end
section
section
open scoped RealInnerProductSpace
section ActiveChambers
variable {E W ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
def activeVectors (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∃ i ∈ I, 0 < homogeneousLift f z i}
def commonPositiveCone (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∀ i ∈ I, 0 < homogeneousLift f z i}
lemma Admissible.commonPositiveCone_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : IsOpen (commonPositiveCone f I) := by
  have he : commonPositiveCone f I =
      ⋂ i ∈ (I : Set ι), {x | 0 < homogeneousLift f x i} := by ext x; simp [commonPositiveCone]
  rw [he]
  exact isOpen_biInter_finset (fun i _ => isOpen_lt continuous_const
    ((continuous_apply i).comp hf.lift_continuous))
lemma Admissible.commonPositiveCone_safe {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : commonPositiveCone f I ⊆ safeNormals (activeVectors f I) := by
  intro x hx z hz horth
  obtain ⟨i,hi,hzi⟩ := hz
  have hxz := mul_pos (hx i hi) hzi
  rw [hf.lift_orthogonal horth i] at hxz
  exact (lt_irrefl 0) hxz
lemma Admissible.commonPositiveCone_interior_safe {f : E → ι → ℝ}
    (hf : Admissible f) (I : Finset ι) :
    commonPositiveCone f I ⊆ interior (safeNormals (activeVectors f I)) :=
  interior_maximal (hf.commonPositiveCone_safe I) (hf.commonPositiveCone_isOpen I)
omit [Fintype ι] in
lemma commonPositiveCone_active {f : E → ι → ℝ} {I : Finset ι} (hI : I.Nonempty)
    {c : E} (hc : c ∈ commonPositiveCone f I) : c ∈ activeVectors f I := by
  obtain ⟨i,hi⟩ := hI
  exact ⟨i,hi,hc i hi⟩
end ActiveChambers
end
end
section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section RankOne
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
omit [DecidableEq ν] [Nonempty ν] in
lemma Admissible.lift_smul {f : (Euc ν) → ι → ℝ} (hf : Admissible f) (v : (Euc ν)) (t : ℝ) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases le_total 0 t with ht | ht
  · exact homogeneousLift_smul_nonneg f v ht
  · have h := homogeneousLift_smul_nonneg f v (neg_nonneg.mpr ht)
    rw [neg_smul, hf.lift_even, neg_sq] at h
    exact h
noncomputable def rankOne (u : (Euc ν)) : SqMat ν := fun i j => u i * u j
omit [Nonempty ν] in
lemma rankOne_action (u x : (Euc ν)) : (matrixOp ν) (rankOne u) x = ⟪u, x⟫ • u := by
  ext i
  change ∑ j, (u i * u j) * x j = ⟪u, x⟫ * u i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp only [mul_comm]
omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_nonneg (u : (Euc ν)) : 0 ≤ rankOne u := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [rankOne, Matrix.conjTranspose_apply, mul_comm]
  · intro x
    have he : star x ⬝ᵥ (rankOne u) *ᵥ x = (∑ i, u i * x i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, rankOne, Pi.star_apply, star_trivial]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp_rw [← mul_assoc, mul_comm (x _) (u _)]
      rw [← Finset.sum_mul, pow_two]
    rw [he]
    exact sq_nonneg _
omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_trace (u : (Euc ν)) : Matrix.trace (rankOne u) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Matrix.trace, Matrix.diag, rankOne, pow_two]
omit [Nonempty ν] in
lemma rankOne_mul_self (u : (Euc ν)) (hu : ‖u‖ = 1) : rankOne u * rankOne u = rankOne u := by
  apply ((matrixOp ν)).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change (matrixOp ν) (rankOne u) ((matrixOp ν) (rankOne u) x) = (matrixOp ν) (rankOne u) x
  simp only [rankOne_action, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
omit [Nonempty ν] in
lemma rankOne_sqrt (u : (Euc ν)) (hu : ‖u‖ = 1) : CFC.sqrt (rankOne u) = rankOne u :=
  (CFC.sqrt_eq_iff _ _ (rankOne_nonneg u) (rankOne_nonneg u)).mpr
    (rankOne_mul_self u hu)
lemma Admissible.positiveExtension_rankOne {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (u : (Euc ν)) (hu : ‖u‖ = 1) : positiveExtension f (rankOne u) = f u := by
  have hcoord (x : UnitSphere (Euc ν)) (i : ι) :
      homogeneousLift f ((matrixOp ν) (rankOne u) x) i = ⟪u, (x : (Euc ν))⟫ ^ 2 * f u i := by
    rw [rankOne_action, hf.lift_smul, homogeneousLift_unit f hu]
    rfl
  have hm : (Fintype.card ν : ℝ) *
      ∫ x : UnitSphere (Euc ν), ⟪u, (x : (Euc ν))⟫ ^ 2 ∂sphereProbability (Euc ν) = 1 := by
    have hs := hf.positiveExtension_sum (rankOne_nonneg u)
    rw [rankOne_trace, hu, one_pow] at hs
    simp only [positiveExtension, rankOne_sqrt u hu, integralLift] at hs
    simp_rw [hcoord] at hs
    simp only [integral_mul_const, ← Finset.mul_sum] at hs
    rw [hf.sum_one u hu, mul_one] at hs
    exact hs
  ext i
  simp only [positiveExtension, rankOne_sqrt u hu, integralLift]
  simp_rw [hcoord]
  rw [integral_mul_const, ← mul_assoc, hm, one_mul]
end RankOne
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SpectralSupport
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
lemma Admissible.signedExtension_pos_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (A : SqMat ν) (i : ι) :
    0 < signedExtension f A i ↔ 0 < positiveExtension f A⁺ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change 0 < positiveExtension f A⁺ i - positiveExtension f A⁻ i ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_left (ne_of_gt h)
    rwa [hz,sub_zero]
lemma Admissible.signedExtension_neg_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (A : SqMat ν) (i : ι) :
    signedExtension f A i < 0 ↔ 0 < positiveExtension f A⁻ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change positiveExtension f A⁺ i - positiveExtension f A⁻ i < 0 ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_right (ne_of_gt h)
    rw [hz,zero_sub]
    exact neg_neg_of_pos h
lemma Admissible.signedExtension_positive_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (A : SqMat ν) (i : ι) :
    0 < signedExtension f A i ↔ ∃ v : (Euc ν),
      v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.signedExtension_pos_iff,hf.positiveExtension_support (CFC.posPart_nonneg A)]
lemma Admissible.signedExtension_range_labels {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {I : Finset ι}
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap) (hvn : ‖v‖ = 1)
    {i : ι} (hi : i ∉ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hvn i)
  by_contra hn
  have hp : 0 < f v i := lt_of_not_ge hn
  exact (not_lt_of_ge (hI i hi)) ((hf.signedExtension_positive_support A i).mpr ⟨v,hv,hvn,hp⟩)
omit [DecidableEq ν] [Nonempty ν] in
lemma subspace_eq_span_of_inner_separates (W : Submodule ℝ (Euc ν)) (w u : (Euc ν))
    (hu : u ∈ W) (huw : ⟪w,u⟫ ≠ 0)
    (hsep : ∀ v ∈ W, ⟪w,v⟫ = 0 → v = 0) : W = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    have hz : v - (⟪w,v⟫ / ⟪w,u⟫) • u = 0 := hsep _
      (W.sub_mem hv (W.smul_mem _ hu)) (by rw [inner_sub_right,inner_smul_right]; field_simp; ring)
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · exact Submodule.span_le.mpr (by simpa using hu)
lemma Admissible.positive_range_separated {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {I : Finset ι} {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap) (hwv : ⟪w,v⟫ = 0) : v = 0 := by
  by_contra hn
  let u : (Euc ν) := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hn]
  have hur : u ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap := Submodule.smul_mem _ _ hv
  obtain ⟨i,hi⟩ := hf.support_nonempty hu
  have hip : 0 < f u i := by simpa [positiveSupport] using hi
  by_cases hiI : i ∈ I
  · exact hf.orthogonal w u hw hu (by simp [u,inner_smul_right,hwv]) i ⟨hwi i hiI,hip⟩
  · have hz := hf.signedExtension_range_labels hI hur hu hiI
    rw [hz] at hip
    exact (lt_irrefl 0) hip
end SpectralSupport
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section RankOnePreimage
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma symmetric_inner_action {A : SqMat ν} (hA : IsSelfAdjoint A) (u v : (Euc ν)) :
    ⟪u,(matrixOp ν) A v⟫ = ⟪(matrixOp ν) A u,v⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,
    ← map_star,hA.star_eq]
omit [Nonempty ν] in
lemma symmetric_eq_rankOne_of_range {A : SqMat ν} (hA : IsSelfAdjoint A)
    {u : (Euc ν)} (hu : ‖u‖ = 1)
    (hR : LinearMap.range ((matrixOp ν) A).toLinearMap ≤ Submodule.span ℝ {u}) :
    A = ⟪u,(matrixOp ν) A u⟫ • rankOne u := by
  have he (v : (Euc ν)) : (matrixOp ν) A v = ⟪u,(matrixOp ν) A v⟫ • u := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hR (LinearMap.mem_range_self _ v))
    change t • u = ((matrixOp ν) A) v at ht
    rw [← ht,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  have hscalar (v : (Euc ν)) : ⟪u,(matrixOp ν) A v⟫ = ⟪u,(matrixOp ν) A u⟫ * ⟪u,v⟫ := by
    calc
      ⟪u,(matrixOp ν) A v⟫ = ⟪(matrixOp ν) A u,v⟫ := symmetric_inner_action hA u v
      _ = ⟪u,(matrixOp ν) A u⟫ * ⟪u,v⟫ := by
        conv_lhs => rw [he u]
        simp only [inner_smul_left,conj_trivial]
  apply (matrixOp ν).injective
  change (matrixOp ν) A = (matrixOp ν) (⟪u,(matrixOp ν) A u⟫ • rankOne u)
  rw [map_smul]
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply,rankOne_action,smul_smul,← hscalar,← he]
lemma Admissible.signedExtension_positive_rankOne {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {I : Finset ι} {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    (hpos : ∃ i, 0 < signedExtension f A i) :
    ∃ u : (Euc ν), ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  obtain ⟨i,hi⟩ := hpos
  obtain ⟨u,hur,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hi
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro he
    have hz := hf.positive_range_separated hw hwi hI hur he
    simp [hz] at hu
  have hr : LinearMap.range ((matrixOp ν) A⁺).toLinearMap = Submodule.span ℝ {u} :=
    subspace_eq_span_of_inner_separates _ w u hur hwu
      (fun v hv horth => hf.positive_range_separated hw hwi hI hv horth)
  have hP := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  let lam : ℝ := ⟪u,(matrixOp ν) A⁺ u⟫
  have hlam : 0 ≤ lam := by
    change 0 ≤ ⟪u,(matrixOp ν) A⁺ u⟫
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hlam0 : lam ≠ 0 := by
    intro hz
    have hp0 : A⁺ = 0 := by simpa only [lam,hz,zero_smul] using hP
    obtain ⟨v,hv⟩ := hur
    rw [hp0,map_zero] at hv
    have hu0 : u = 0 := by simpa using hv.symm
    simp [hu0] at hu
  exact ⟨u,hu,lam,lt_of_le_of_ne hlam (Ne.symm hlam0),hP⟩
lemma Admissible.signedExtension_splitting {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) {u : (Euc ν)} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) :
    A = lam • rankOne u - A⁻ ∧
      positiveExtension f A⁺ = lam • f u ∧
      signedExtension f A = lam • f u - positiveExtension f A⁻ := by
  have hp : positiveExtension f A⁺ = lam • f u := by
    rw [he,positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
      hf.positiveExtension_rankOne u hu]
  refine ⟨?_,hp,?_⟩
  · rw [← he]
    exact (CFC.posPart_sub_negPart A hA).symm
  · exact congrArg (fun v => v - positiveExtension f A⁻) hp
lemma Admissible.signedExtension_line_labels {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {u : (Euc ν)} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) (i : ι) :
    0 < signedExtension f A i ↔ 0 < f u i := by
  rw [hf.signedExtension_pos_iff,he,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]
  exact mul_pos_iff_of_pos_left hlam
end RankOnePreimage
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section SpectralChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
noncomputable def positiveProjection (A : (SqMat ν)) : (SqMat ν) := Ring.inverse A * A⁺
omit [Nonempty ν] in
lemma positiveProjection_action {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap) :
    (matrixOp ν) (positiveProjection A) v = v := by
  obtain ⟨x,rfl⟩ := hv
  have hAP : A * A⁺ = A⁺ * A⁺ := by
    calc
      A * A⁺ = (A⁺ - A⁻) * A⁺ := by rw [CFC.posPart_sub_negPart A hA]
      _ = A⁺ * A⁺ := by rw [sub_mul,CFC.negPart_mul_posPart,sub_zero]
  have he : positiveProjection A * A⁺ = A⁺ := by
    dsimp [positiveProjection]
    rw [mul_assoc,← hAP,← mul_assoc,Ring.inverse_mul_cancel A hU,one_mul]
  have hh := congrArg (fun B : (SqMat ν) => (matrixOp ν) B x) he
  simpa only [map_mul,mul_apply_eq_comp,ContinuousLinearMap.coe_coe] using hh
omit [Nonempty ν] in
lemma positiveProjection_kills {A : (SqMat ν)} {u v : (Euc ν)} {lam : ℝ}
    (hP : A⁺ = lam • rankOne u) (hv : ⟪u,v⟫ = 0) :
    (matrixOp ν) (positiveProjection A) v = 0 := by
  simp only [positiveProjection,map_mul,mul_apply_eq_comp,hP,map_smul,
    smul_apply,rankOne_action,hv,zero_smul,map_zero,smul_zero]
omit [Nonempty ν] in
lemma positiveRange_separated_of_close {A B : (SqMat ν)} (hB : IsSelfAdjoint B)
    (hBU : IsUnit B) {u : (Euc ν)} {lam : ℝ} (hP : A⁺ = lam • rankOne u)
    (hclose : ‖(matrixOp ν) (positiveProjection B) - (matrixOp ν) (positiveProjection A)‖ < 1)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) B⁺).toLinearMap) (horth : ⟪u,v⟫ = 0) : v = 0 := by
  have he : ((matrixOp ν) (positiveProjection B) - (matrixOp ν) (positiveProjection A)) v = v := by
    rw [sub_apply,positiveProjection_action hB hBU hv,
      positiveProjection_kills hP horth,sub_zero]
  have hn := ContinuousLinearMap.le_opNorm ((matrixOp ν) (positiveProjection B) - (matrixOp ν) (positiveProjection A)) v
  rw [he] at hn
  apply norm_eq_zero.mp
  have hp := norm_nonneg v
  nlinarith
omit [Nonempty ν] in
lemma positive_eq_rankOne_of_separated {A : (SqMat ν)} {w : (Euc ν)}
    (hAw : (matrixOp ν) A⁺ w ≠ 0)
    (hsep : ∀ v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap, ⟪w,v⟫ = 0 → v = 0) :
    ∃ u : (Euc ν), ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  let v : (Euc ν) := (matrixOp ν) A⁺ w
  let u : (Euc ν) := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hAw,v]
  have hur : u ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self _ w)
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro hz
    have hu0 := hsep u hur hz
    simp [hu0] at hu
  have hr := subspace_eq_span_of_inner_separates
    (LinearMap.range ((matrixOp ν) A⁺).toLinearMap) w u hur hwu hsep
  have he := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  have hl : 0 ≤ ⟪u,(matrixOp ν) A⁺ u⟫ := by
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hl0 : ⟪u,(matrixOp ν) A⁺ u⟫ ≠ 0 := by
    intro hz
    have hP0 : A⁺ = 0 := by simpa only [hz,zero_smul] using he
    apply hAw
    simp [hP0]
  exact ⟨u,hu,_,lt_of_le_of_ne hl (Ne.symm hl0),he⟩
omit [Nonempty ν] in
lemma positiveProjection_continuousAt {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) : ContinuousAt (positiveProjection ∘ A) x := by
  have hP : Continuous (fun x => (A x)⁺) :=
    (matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y))
  have hInv : ContinuousAt (fun y => Ring.inverse (A y)) x := by
    obtain ⟨a,ha⟩ := hU
    have hi := NormedRing.inverse_continuousAt a
    rw [ha] at hi
    exact hi.comp hA.continuousAt
  exact hInv.mul hP.continuousAt
omit [Nonempty ν] in
lemma positive_line_eventually {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) {w : (Euc ν)} (hw : ‖w‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (hP : (A x)⁺ = lam • rankOne w) :
    ∀ᶠ y in 𝓝 x, IsUnit (A y) ∧ ∃ u : (Euc ν), ‖u‖ = 1 ∧
      ∃ t : ℝ, 0 < t ∧ (A y)⁺ = t • rankOne u := by
  have hop : Continuous (fun B : (SqMat ν) => (matrixOp ν) B) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hQ := hop.continuousAt.comp (positiveProjection_continuousAt A hA hSA hU)
  have hclose : ∀ᶠ y in 𝓝 x, ‖(matrixOp ν) (positiveProjection (A y)) - (matrixOp ν) (positiveProjection (A x))‖ < 1 := by
    have ht := (hQ.sub (continuousAt_const (y := (matrixOp ν) (positiveProjection (A x))))).norm
    exact ht.eventually_lt continuousAt_const (by simp)
  have hPcont : Continuous (fun y => (A y)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y)
  have hvcont : Continuous (fun y => (matrixOp ν) (A y)⁺ w) := (hop.comp hPcont).clm_apply continuous_const
  have hw0 : (matrixOp ν) (A x)⁺ w ≠ 0 := by
    rw [hP,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,hw]
    have hwne : w ≠ 0 := by intro he; simp only [he,norm_zero] at hw; norm_num at hw
    simpa only [one_pow,one_smul] using smul_ne_zero (ne_of_gt hlam) hwne
  have hv : ∀ᶠ y in 𝓝 x, (matrixOp ν) (A y)⁺ w ≠ 0 := hvcont.continuousAt.eventually_ne hw0
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hA.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hU)
  filter_upwards [hclose,hv,hunit] with y hy hyv hyU
  refine ⟨hyU,positive_eq_rankOne_of_separated hyv ?_⟩
  exact fun v hv he => positiveRange_separated_of_close (hSA y) hyU hP hy hv he
end SpectralChart
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section LineRepresentative
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
omit [Fintype ν] [DecidableEq ν] [Nonempty ν] in
lemma rankOne_smul (t : ℝ) (u : (Euc ν)) : rankOne (t • u) = t^2 • rankOne u := by
  ext i j
  simp only [rankOne,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring
omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_unit_span {u v : (Euc ν)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hsp : v ∈ Submodule.span ℝ {u}) : rankOne v = rankOne u := by
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hsp
  change t • u = v at ht
  have hn : |t| = 1 := by simpa only [← ht,norm_smul,Real.norm_eq_abs,hu,mul_one] using hv
  have hs : t^2 = 1 := by nlinarith [sq_abs t]
  rw [← ht,rankOne_smul,hs,one_smul]
noncomputable def lineRepresentative (w : (Euc ν)) (A : (SqMat ν)) : (Euc ν) :=
  ‖(matrixOp ν) A⁺ w‖⁻¹ • (matrixOp ν) A⁺ w
def HasPositiveLine (A : (SqMat ν)) : Prop :=
  ∃ u : (Euc ν), ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u
omit [Nonempty ν] in
lemma lineRepresentative_norm {w : (Euc ν)} {A : (SqMat ν)} (hAw : (matrixOp ν) A⁺ w ≠ 0) :
    ‖lineRepresentative w A‖ = 1 := by
  simp [lineRepresentative,norm_smul,norm_inv,hAw]
omit [Nonempty ν] in
lemma hasPositiveLine_trace_pos {A : (SqMat ν)} (hA : HasPositiveLine A) :
    0 < Matrix.trace A⁺ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  rwa [he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]
omit [Nonempty ν] in
lemma positive_line_representative {w : (Euc ν)} {A : (SqMat ν)} (hA : HasPositiveLine A)
    (hAw : (matrixOp ν) A⁺ w ≠ 0) : A⁺ = Matrix.trace A⁺ • rankOne (lineRepresentative w A) := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hsp : lineRepresentative w A ∈ Submodule.span ℝ {u} := by
    rw [lineRepresentative,he,map_smul,smul_apply,rankOne_action]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))))
  have hp := rankOne_unit_span hu (lineRepresentative_norm hAw) hsp
  rw [hp,he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]
omit [Nonempty ν] in
lemma lineRepresentative_inner_pos {w : (Euc ν)} {A : (SqMat ν)} (hA : HasPositiveLine A)
    (hAw : (matrixOp ν) A⁺ w ≠ 0) : 0 < ⟪w,lineRepresentative w A⟫ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hi : ⟪u,w⟫ ≠ 0 := by
    intro hz
    apply hAw
    rw [he,map_smul,smul_apply,rankOne_action,hz,zero_smul,smul_zero]
  have hp : 0 < ⟪w,(matrixOp ν) A⁺ w⟫ := by
    rw [he,map_smul,smul_apply,rankOne_action,inner_smul_right,
      inner_smul_right,real_inner_comm w u]
    exact mul_pos hl (mul_self_pos.mpr (by simpa only [real_inner_comm] using hi))
  rw [lineRepresentative,inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hAw)) hp
omit [Nonempty ν] in
lemma lineRepresentative_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) (w : (Euc ν)) :
    ContinuousOn (fun x => lineRepresentative w (A x)) {x | (matrixOp ν) (A x)⁺ w ≠ 0} := by
  have hop : Continuous (fun B : (SqMat ν) => (matrixOp ν) B) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hP : Continuous (fun x => (A x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA hSA
  have hv : Continuous (fun x => (matrixOp ν) (A x)⁺ w) := (hop.comp hP).clm_apply continuous_const
  exact (hv.norm.continuousOn.inv₀ (fun _ hx => norm_ne_zero_iff.mpr hx)).smul hv.continuousOn
omit [Nonempty ν] in
lemma positive_line_isOpen {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen {x | IsUnit (A x) ∧ HasPositiveLine (A x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨u,hu,lam,hl,he⟩ := hx.2
  exact positive_line_eventually A hA hSA hx.1 hu hl he
lemma unit_rankOne_inner_nonzero {A : (SqMat ν)} (_hA : HasPositiveLine A) {w u : (Euc ν)}
    (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u)
    (hwu : ⟪w,u⟫ ≠ 0) : (matrixOp ν) A⁺ w ≠ 0 := by
  rw [he,map_smul,smul_apply,rankOne_action]
  apply smul_ne_zero (ne_of_gt hl)
  apply smul_ne_zero (by simpa only [real_inner_comm] using hwu)
  intro hz
  simp [hz] at hu
end LineRepresentative
end
end
section
section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section PositiveSlice
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
noncomputable def unflattenMatrix : Euc (ν × ν) →ₗ[ℝ] (SqMat ν) where
  toFun x i j := x (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def flatGram (x : Euc (ν × ν)) : (SqMat ν) :=
  unflattenMatrix x * (unflattenMatrix x)ᴴ
omit [DecidableEq ν] in
lemma flatGram_nonneg (x : Euc (ν × ν)) : 0 ≤ flatGram x :=
  (Matrix.posSemidef_self_mul_conjTranspose _).nonneg
omit [DecidableEq ν] in
lemma flatGram_trace (x : Euc (ν × ν)) : Matrix.trace (flatGram x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [flatGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,Fintype.sum_prod_type]
  simp only [pow_two]
  rfl
omit [DecidableEq ν] in
lemma flatGram_continuous : Continuous (flatGram (ν := ν)) := by
  have h := (unflattenMatrix (ν := ν)).continuous_of_finiteDimensional
  exact h.mul h.star
lemma positive_slice_image : {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q = 1} =
    flatGram '' Metric.sphere (0 : Euc (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : Euc (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 = 1 := by rw [← flatGram_trace,hxQ,htr]
    have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hnorm,hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hnorm : ‖x‖ = 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace,hnorm,one_pow]
lemma positive_slice_compact : IsCompact {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q = 1} := by
  rw [positive_slice_image]
  exact (isCompact_sphere (0 : Euc (ν × ν)) 1).image flatGram_continuous
end PositiveSlice
end
end
section
section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section TraceSphere
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
omit [DecidableEq ν] in
lemma matrix_trace_continuous : Continuous (Matrix.trace : (SqMat ν) → ℝ) :=
  (Matrix.traceLinearMap ν ℝ ℝ).continuous_of_finiteDimensional
omit [DecidableEq ν] in
lemma matrix_trace_nonneg {A : (SqMat ν)} (hA : 0 ≤ A) : 0 ≤ Matrix.trace A :=
  (Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg
lemma positive_ball_image : {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} =
    flatGram '' Metric.closedBall (0 : Euc (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : Euc (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 ≤ 1 := by rw [← flatGram_trace,hxQ]; exact htr
    have hn' : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hn',hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hn : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace]
    nlinarith [norm_nonneg x]
lemma positive_ball_compact : IsCompact {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} := by
  rw [positive_ball_image]
  exact (isCompact_closedBall (0 : Euc (ν × ν)) 1).image flatGram_continuous
noncomputable def traceSphere (ν : Type*) [Fintype ν] [DecidableEq ν] : Set (SqMat ν) :=
  {A | IsSelfAdjoint A ∧ Matrix.trace (CFC.abs A) = 1}
lemma traceSphere_closed : IsClosed (traceSphere ν) :=
  (isClosed_eq continuous_star continuous_id).inter
    (isClosed_eq (matrix_trace_continuous.comp CFC.continuous_abs) continuous_const)
lemma traceSphere_compact : IsCompact (traceSphere ν) := by
  have hK : IsCompact ((fun p : (SqMat ν) × (SqMat ν) => p.1 - p.2) ''
      ({Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} ×ˢ {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1})) :=
    (positive_ball_compact.prod positive_ball_compact).image (continuous_fst.sub continuous_snd)
  apply hK.of_isClosed_subset traceSphere_closed
  intro A hA
  have htr : Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
    rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]
    exact hA.2
  refine ⟨(A⁺,A⁻),⟨⟨CFC.posPart_nonneg A,?_⟩,⟨CFC.negPart_nonneg A,?_⟩⟩,
    CFC.posPart_sub_negPart A hA.1⟩
  · linarith [matrix_trace_nonneg (CFC.negPart_nonneg A)]
  · linarith [matrix_trace_nonneg (CFC.posPart_nonneg A)]
lemma traceSphere_ne_zero {A : (SqMat ν)} (hA : A ∈ traceSphere ν) : A ≠ 0 := by
  intro h
  simpa [h] using hA.2
lemma traceAbs_pos {A : (SqMat ν)} (hA : A ≠ 0) : 0 < Matrix.trace (CFC.abs A) := by
  have hp := matrix_trace_nonneg (CFC.abs_nonneg A)
  apply lt_of_le_of_ne hp
  intro hz
  have habs := (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)).trace_eq_zero_iff.mp hz.symm
  have he := CFC.abs_mul_abs A
  rw [habs,zero_mul] at he
  exact hA (Matrix.conjTranspose_mul_self_eq_zero.mp he.symm)
noncomputable def traceRadial (A : (SqMat ν)) : (SqMat ν) := (Matrix.trace (CFC.abs A))⁻¹ • A
lemma traceRadial_mem {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    traceRadial A ∈ traceSphere ν := by
  have hp := traceAbs_pos hAz
  refine ⟨(IsSelfAdjoint.all (_ : ℝ)).smul hA,?_⟩
  change Matrix.trace (CFC.abs ((Matrix.trace (CFC.abs A))⁻¹ • A)) = 1
  rw [CFC.abs_smul,Matrix.trace_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ (ne_of_gt hp)
lemma traceRadial_continuousOn : ContinuousOn (traceRadial (ν := ν)) {A | A ≠ 0} :=
  ((matrix_trace_continuous.comp CFC.continuous_abs).continuousOn.inv₀
    (fun _A hA => ne_of_gt (traceAbs_pos hA))).smul continuous_id.continuousOn
lemma traceRadial_neg (A : (SqMat ν)) : traceRadial (-A) = -traceRadial A := by
  simp only [traceRadial,CFC.abs_neg,smul_neg]
end TraceSphere
end
end
section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section MatrixFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma psd_inner_nonneg {Q : (SqMat ν)} (hQ : 0 ≤ Q) (v : (Euc ν)) : 0 ≤ ⟪v,(matrixOp ν) Q v⟫ := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hQ).re_dotProduct_nonneg v.ofLp
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 ≤ ∑ i, (Q *ᵥ v.ofLp) i * v i
  simpa only [RCLike.re_to_real,dotProduct,Pi.star_apply,star_trivial,mul_comm] using h
lemma rankOne_mul_of_kernel {Q : (SqMat ν)} (hQ : IsSelfAdjoint Q) {u : (Euc ν)}
    (hu : (matrixOp ν) Q u = 0) : rankOne u * Q = 0 := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (rankOne u * Q) = (matrixOp ν) 0
  rw [map_mul,map_zero]
  apply ContinuousLinearMap.ext
  intro v
  change (matrixOp ν) (rankOne u) ((matrixOp ν) Q v) = 0
  rw [rankOne_action]
  have hi : ⟪u,(matrixOp ν) Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint,← map_star,hQ.star_eq,hu,inner_zero_left]
  rw [hi,zero_smul]
lemma rankOne_split_parts {Q : (SqMat ν)} (hQ : 0 ≤ Q) {u : (Euc ν)} (hu : (matrixOp ν) Q u = 0)
    {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) :
    (lam • rankOne u - mu • Q)⁺ = lam • rankOne u ∧
    (lam • rankOne u - mu • Q)⁻ = mu • Q := by
  apply CFC.posPart_negPart_unique rfl _ (smul_nonneg hl (rankOne_nonneg u)) (smul_nonneg hm hQ)
  rw [Matrix.smul_mul,Matrix.mul_smul,rankOne_mul_of_kernel hQ.isSelfAdjoint hu,smul_zero,smul_zero]
lemma nonunit_has_kernel (A : (SqMat ν)) (hA : ¬ IsUnit A) :
    ∃ v : (Euc ν), v ≠ 0 ∧ (matrixOp ν) A v = 0 := by
  have hdet : A.det = 0 := by
    by_contra h
    exact hA ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))
  obtain ⟨v,hv,hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨WithLp.toLp 2 v,fun h => hv (WithLp.toLp_injective 2 h),?_⟩
  rw [Matrix.toEuclideanCLM_toLp,hAv,WithLp.toLp_zero]
lemma fibre_boundary_kernel {Q : (SqMat ν)} (hQ : 0 ≤ Q) (u : (Euc ν))
    (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ v : (Euc ν), ‖v‖ = 1 ∧ ⟪u,v⟫ = 0 ∧ (matrixOp ν) Q v = 0 := by
  obtain ⟨v,hv,hAv⟩ := nonunit_has_kernel _ hnot
  have hsum : ⟪v,(matrixOp ν) (rankOne u + Q) v⟫ = 0 := by rw [hAv,inner_zero_right]
  rw [map_add,add_apply,inner_add_right,rankOne_action,
    inner_smul_right,real_inner_comm u v] at hsum
  have hi : ⟪u,v⟫ = 0 := by
    nlinarith [psd_inner_nonneg hQ v,sq_nonneg ⟪u,v⟫]
  have hQv : (matrixOp ν) Q v = 0 := by
    simpa only [map_add,add_apply,rankOne_action,hi,zero_smul,zero_add] using hAv
  refine ⟨‖v‖⁻¹ • v,by simp [norm_smul,norm_inv,hv],?_,?_⟩
  · simp only [inner_smul_right,hi,mul_zero]
  · rw [map_smul,hQv,smul_zero]
noncomputable def matrixFibre (u : (Euc ν)) : Set (SqMat ν) :=
  {Q | 0 ≤ Q ∧ Matrix.trace Q = 1 ∧ (matrixOp ν) Q u = 0}
end MatrixFibre
end
end
section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section NegativeFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
lemma negPart_kernel_of_positiveLine {A : (SqMat ν)} {u : (Euc ν)} (hu : ‖u‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u) : (matrixOp ν) A⁻ u = 0 := by
  have hz : (matrixOp ν) A⁻ ((matrixOp ν) A⁺ u) = 0 := by
    have h := congrArg (fun B : (SqMat ν) => (matrixOp ν) B u) (CFC.negPart_mul_posPart A)
    simpa only [map_mul,map_zero,mul_apply_eq_comp,zero_apply] using h
  rw [he,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,
    hu,one_pow,one_smul,map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt hl)
noncomputable def negativeFibre (A : (SqMat ν)) : (SqMat ν) := (Matrix.trace A⁻)⁻¹ • A⁻
lemma negativeFibre_mem {A : (SqMat ν)} (hA : HasPositiveLine A) {w : (Euc ν)}
    (hAw : (matrixOp ν) A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    negativeFibre A ∈ matrixFibre (lineRepresentative w A) := by
  have hu := lineRepresentative_norm hAw
  have hl := hasPositiveLine_trace_pos hA
  have he := positive_line_representative hA hAw
  refine ⟨smul_nonneg (inv_nonneg.mpr hm.le) (CFC.negPart_nonneg A),?_,?_⟩
  · rw [negativeFibre,Matrix.trace_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt hm)]
  · rw [negativeFibre,map_smul,smul_apply,
      negPart_kernel_of_positiveLine hu hl he,smul_zero]
omit [Nonempty ν] in
lemma negativeFibre_smul {A : (SqMat ν)} (hm : Matrix.trace A⁻ ≠ 0) :
    Matrix.trace A⁻ • negativeFibre A = A⁻ := by
  rw [negativeFibre,smul_smul,mul_inv_cancel₀ hm,one_smul]
omit [Nonempty ν] in
lemma negativeFibre_splitting {A : (SqMat ν)} (hSA : IsSelfAdjoint A) (hA : HasPositiveLine A)
    {w : (Euc ν)} (hAw : (matrixOp ν) A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    A = Matrix.trace A⁺ • rankOne (lineRepresentative w A) - Matrix.trace A⁻ • negativeFibre A := by
  rw [negativeFibre_smul (ne_of_gt hm),← positive_line_representative hA hAw,
    CFC.posPart_sub_negPart A hSA]
omit [Nonempty ν] in
lemma negativeFibre_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    ContinuousOn (fun x => negativeFibre (A x)) {x | Matrix.trace (A x)⁻ ≠ 0} := by
  have hP : Continuous (fun x => (A x)⁻) :=
    matrix_negPart_continuousOn.comp_continuous hA hSA
  exact ((matrix_trace_continuous.comp hP).continuousOn.inv₀ (fun _ hx => hx)).smul hP.continuousOn
end NegativeFibre
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
open Set
section PurityChart
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
noncomputable def purityChart (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w c : (Euc ν)) : Set (SqMat ν) :=
  {A | IsUnit A ∧ HasPositiveLine A ∧ (matrixOp ν) A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
    lineRepresentative w A ∈ commonPositiveCone f I ∧
    lineRepresentative w A ∈ interior (signChamber (activeVectors f I) c)}
omit [Nonempty ν] in
lemma Admissible.purityChart_isOpen {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : (Euc ν)) {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen (A ⁻¹' purityChart f I w c) := by
  have hop : Continuous (fun x => (matrixOp ν) (A x)⁺ w) :=
    ((((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
      (matrix_posPart_continuousOn.comp_continuous hA hSA)).clm_apply continuous_const
  have hopen : IsOpen {x | (matrixOp ν) (A x)⁺ w ≠ 0} := (isClosed_eq hop continuous_const).isOpen_compl
  have hrep := lineRepresentative_continuousOn A hA hSA w
  have hpre : IsOpen ({x | (matrixOp ν) (A x)⁺ w ≠ 0} ∩
      (fun x => lineRepresentative w (A x)) ⁻¹'
      (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) :=
    hrep.isOpen_inter_preimage hopen ((hf.commonPositiveCone_isOpen I).inter isOpen_interior)
  have hn : IsOpen {x | 0 < Matrix.trace (A x)⁻} := isOpen_lt continuous_const
    (matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA))
  have he : A ⁻¹' purityChart f I w c =
      ({x | IsUnit (A x) ∧ HasPositiveLine (A x)} ∩ {x | 0 < Matrix.trace (A x)⁻}) ∩
        ({x | (matrixOp ν) (A x)⁺ w ≠ 0} ∩ (fun x => lineRepresentative w (A x)) ⁻¹'
          (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) := by
    ext x
    simp only [purityChart,mem_preimage,mem_ofPred_eq,mem_inter_iff]
    tauto
  rw [he]
  exact ((positive_line_isOpen A hA hSA).inter hn).inter hpre
omit [Fintype ι] in
omit [Nonempty ν] in
lemma purityChart_unit {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w c : (Euc ν)} {A : (SqMat ν)}
    (hA : A ∈ purityChart f I w c) : ‖lineRepresentative w A‖ = 1 :=
  lineRepresentative_norm hA.2.2.1
omit [Fintype ι] in
lemma purityChart_fibre {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w c : (Euc ν)} {A : (SqMat ν)}
    (hA : A ∈ purityChart f I w c) : negativeFibre A ∈ matrixFibre (lineRepresentative w A) :=
  negativeFibre_mem hA.2.1 hA.2.2.1 hA.2.2.2.1
end PurityChart
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section BalancedChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
lemma split_unit_of_fibre_unit {u : (Euc ν)} (hu : ‖u‖ = 1) {Q : (SqMat ν)} (hQ : 0 ≤ Q)
    (hQu : (matrixOp ν) Q u = 0) {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu)
    (hunit : IsUnit (rankOne u + Q)) : IsUnit (lam • rankOne u - mu • Q) := by
  apply (isUnit_map_iff ((matrixOp ν)) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective ((matrixOp ν) (lam • rankOne u - mu • Q)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : (matrixOp ν) (lam • rankOne u - mu • Q) v = 0 := hv
    have hi := congrArg (fun b : (Euc ν) => ⟪u,b⟫) hv0
    have hQv : ⟪u,(matrixOp ν) Q v⟫ = 0 := matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu v
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      rankOne_action,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,
      mul_one,hQv,mul_zero,sub_zero,inner_zero_right] at hi
    have huv : ⟪u,v⟫ = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hl)
    have hzero : (matrixOp ν) Q v = 0 := by
      simp only [map_sub,map_smul,sub_apply,smul_apply,
        rankOne_action,huv,zero_smul,smul_zero,zero_sub,neg_eq_zero] at hv0
      exact (smul_eq_zero.mp hv0).resolve_left (ne_of_gt hm)
    have huop := ContinuousLinearMap.isUnit_iff_bijective.mp (hunit.map ((matrixOp ν)).toMonoidHom)
    apply huop.1
    change (matrixOp ν) (rankOne u + Q) v = (matrixOp ν) (rankOne u + Q) 0
    simp only [map_add,add_apply,rankOne_action,huv,zero_smul,hzero,add_zero,map_zero]
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩
omit [Nonempty ν] in
lemma lineRepresentative_split {u w : (Euc ν)} (hu : ‖u‖ = 1) {A : (SqMat ν)} {lam : ℝ}
    (hl : 0 < lam) (he : A⁺ = lam • rankOne u) (hwu : 0 < ⟪w,u⟫) :
    lineRepresentative w A = u := by
  have hp : 0 < lam * ⟪u,w⟫ := mul_pos hl (by simpa only [real_inner_comm] using hwu)
  have hop : (matrixOp ν) A⁺ w = (lam * ⟪u,w⟫) • u := by
    rw [he,map_smul,smul_apply,rankOne_action,smul_smul]
  rw [lineRepresentative,hop,norm_smul,Real.norm_eq_abs,abs_of_pos hp,hu,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt hp),one_smul]
lemma balancedFibre_chart {ι : Type*} [Fintype ι] {f : (Euc ν) → ι → ℝ} {I : Finset ι}
    {w c u : (Euc ν)} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫)
    (huc : u ∈ commonPositiveCone f I)
    (hch : u ∈ interior (signChamber (activeVectors f I) c)) {Q : (SqMat ν)}
    (hQ : Q ∈ matrixFibre u) (hunit : IsUnit (rankOne u + Q)) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ purityChart f I w c := by
  have hp : (0:ℝ) < 1/2 := by norm_num
  obtain ⟨he,hn⟩ := rankOne_split_parts hQ.1 hQ.2.2 hp.le hp.le
  have hline : HasPositiveLine ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) := ⟨u,hu,1/2,hp,he⟩
  have hrep := lineRepresentative_split hu hp he hwu
  refine ⟨split_unit_of_fibre_unit hu hQ.1 hQ.2.2 hp hp hunit,hline,
    unit_rankOne_inner_nonzero hline hu hp he (ne_of_gt hwu),?_,?_,?_⟩
  · rw [hn,Matrix.trace_smul,hQ.2.1,smul_eq_mul,mul_one]; exact hp
  · rwa [hrep]
  · rwa [hrep]
end BalancedChart
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
noncomputable def matrixConjugate (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) : (SqMat ν) ≃⋆ₐ[ℝ] (SqMat ν) :=
  ((matrixOp ν)).trans (e.conjStarAlgEquiv.trans ((matrixOp ν)).symm)
lemma matrixConjugate_action (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) (v : (Euc ν)) :
    (matrixOp ν) (matrixConjugate e A) v = e ((matrixOp ν) A (e.symm v)) := by
  simp only [matrixConjugate,StarAlgEquiv.trans_apply,StarAlgEquiv.apply_symm_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
lemma matrixConjugate_nonneg (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : 0 ≤ A) :
    0 ≤ matrixConjugate e A := map_nonneg _ hA
lemma matrixConjugate_rankOne (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) (u : (Euc ν)) :
    matrixConjugate e (rankOne u) = rankOne (e u) := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate e (rankOne u)) = (matrixOp ν) (rankOne (e u))
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action,rankOne_action,rankOne_action,map_smul]
  congr 1
  simpa using (e.inner_map_map u (e.symm v)).symm
lemma matrix_operator_trace (A : (SqMat ν)) : LinearMap.trace ℝ (Euc ν) ((matrixOp ν) A).toLinearMap = Matrix.trace A := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A _
lemma matrixConjugate_trace (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) :
    Matrix.trace (matrixConjugate e A) = Matrix.trace A := by
  rw [← matrix_operator_trace,← matrix_operator_trace]
  have he : ((matrixOp ν) (matrixConjugate e A)).toLinearMap = e.toLinearEquiv.conj ((matrixOp ν) A).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact matrixConjugate_action e A v
  rw [he,LinearMap.trace_conj']
lemma matrixConjugate_kernel (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} {v : (Euc ν)} (hv : (matrixOp ν) A v = 0) :
    (matrixOp ν) (matrixConjugate e A) (e v) = 0 := by
  rw [matrixConjugate_action,e.symm_apply_apply,hv,map_zero]
lemma matrixConjugate_selfAdjoint (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixConjugate e A) := by
  rw [IsSelfAdjoint,← map_star,hA.star_eq]
lemma matrixConjugate_involutive {e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)}
    (he : ∀ v, e (e v) = v) (A : (SqMat ν)) : matrixConjugate e (matrixConjugate e A) = A := by
  have hes : ∀ v, e.symm v = e v := by intro v; apply e.injective; simp [he]
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate e (matrixConjugate e A)) = (matrixOp ν) A
  apply ContinuousLinearMap.ext
  intro v
  simp only [matrixConjugate_action,hes,he]
end MatrixTransport
end
end
section
section
open scoped RealInnerProductSpace
section ReflectionTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def householder (c x : E) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {c+x}).reflection
lemma householder_apply (c x v : E) :
    householder c x v = (2 * (⟪c+x,v⟫ / ‖c+x‖ ^ 2)) • (c+x) - v := by
  rw [householder,Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, two_smul, two_mul, add_smul]
lemma householder_send {c x : E} (h : ‖c‖ = ‖x‖) : householder c x c = x := by
  have hh := Submodule.reflection_sub (v := c) (w := -x) (by simpa using h)
  rw [sub_neg_eq_add,Submodule.reflection_orthogonal_apply] at hh
  exact neg_injective hh
lemma householder_at_self {c v : E} (hv : ⟪c,v⟫ = 0) :
    householder c c v = -v := by
  rw [householder_apply]
  simp [inner_add_left,hv]
end ReflectionTransport
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixReflection
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
omit [Fintype ν] [DecidableEq ν] in
lemma rankOne_continuous : Continuous (rankOne (ν := ν)) := by
  apply continuous_matrix
  intro i j
  exact (PiLp.continuous_apply 2 (fun _ : ν => ℝ) i).mul
    (PiLp.continuous_apply 2 (fun _ : ν => ℝ) j)
noncomputable def reflectionMatrix (c u : (Euc ν)) : (SqMat ν) :=
  (2 / ‖c+u‖^2) • rankOne (c+u) - 1
lemma reflectionMatrix_action (c u v : (Euc ν)) :
    (matrixOp ν) (reflectionMatrix c u) v = householder c u v := by
  rw [reflectionMatrix,map_sub,map_smul,map_one,sub_apply,
    smul_apply,one_apply_eq_self,rankOne_action,householder_apply,
    smul_smul]
  congr 2
  ring
omit [DecidableEq ν] in
lemma householder_involutive (c u : (Euc ν)) : Function.Involutive (householder c u) :=
  (Submodule.span ℝ {c+u}).reflection_involutive
lemma reflectionMatrix_conjugate (c u : (Euc ν)) (B : (SqMat ν)) :
    matrixConjugate (householder c u) B = reflectionMatrix c u * B * reflectionMatrix c u := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate (householder c u) B) = (matrixOp ν) (reflectionMatrix c u * B * reflectionMatrix c u)
  rw [map_mul,map_mul]
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  change _ = (matrixOp ν) (reflectionMatrix c u) ((matrixOp ν) B ((matrixOp ν) (reflectionMatrix c u) v))
  rw [reflectionMatrix_action,reflectionMatrix_action]
  congr 2
lemma reflectionMatrix_continuousOn (c : (Euc ν)) :
    ContinuousOn (reflectionMatrix c) {u | c+u ≠ 0} := by
  have hn : Continuous (fun u : (Euc ν) => ‖c+u‖^2) := (continuous_const.add continuous_id).norm.pow 2
  have hd : ContinuousOn (fun u : (Euc ν) => 2 / ‖c+u‖^2) {u | c+u ≠ 0} :=
    continuous_const.continuousOn.div hn.continuousOn
      (fun u hu => pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))
  exact (hd.smul (rankOne_continuous.comp (continuous_const.add continuous_id)).continuousOn).sub
    continuous_const.continuousOn
lemma householder_matrix_joint_continuousOn (c : (Euc ν)) :
    ContinuousOn (fun p : (Euc ν) × (SqMat ν) => matrixConjugate (householder c p.1) p.2)
      {p | c+p.1 ≠ 0} := by
  simp_rw [reflectionMatrix_conjugate]
  have hR : ContinuousOn (fun p : (Euc ν) × (SqMat ν) => reflectionMatrix c p.1) {p | c+p.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h)
  exact (hR.mul continuous_snd.continuousOn).mul hR
end MatrixReflection
end
end
section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section FibreTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
omit [DecidableEq ν] in
lemma householder_swap {c u : (Euc ν)} (h : ‖c‖ = ‖u‖) : householder c u u = c := by
  calc
    householder c u u = householder c u (householder c u c) := congrArg (householder c u) (householder_send h).symm
    _ = c := householder_involutive c u c
lemma matrixConjugate_householder_self {c : (Euc ν)} {Q : (SqMat ν)} (hQ : IsSelfAdjoint Q)
    (hc : (matrixOp ν) Q c = 0) : matrixConjugate (householder c c) Q = Q := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate (householder c c) Q) = (matrixOp ν) Q
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  have hs : (householder c c).symm v = householder c c v := by
    apply (householder c c).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (householder_involutive c c v).symm
  have hcz : (matrixOp ν) Q (c+c) = 0 := by rw [map_add,hc,add_zero]
  have hact : (matrixOp ν) Q (householder c c v) = -((matrixOp ν) Q v) := by
    rw [householder_apply,map_sub,map_smul,hcz,smul_zero,zero_sub]
  rw [hs,hact,map_neg]
  have ho : ⟪c,(matrixOp ν) Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,hQ.star_eq,hc,inner_zero_left]
  rw [householder_at_self ho,neg_neg]
noncomputable def fibreTransport (c u v : (Euc ν)) (Q : (SqMat ν)) : (SqMat ν) :=
  matrixConjugate (householder c v) (matrixConjugate (householder c u) Q)
lemma fibreTransport_nonneg (c u v : (Euc ν)) {Q : (SqMat ν)} (hQ : 0 ≤ Q) :
    0 ≤ fibreTransport c u v Q :=
  matrixConjugate_nonneg _ (matrixConjugate_nonneg _ hQ)
lemma fibreTransport_trace (c u v : (Euc ν)) (Q : (SqMat ν)) :
    Matrix.trace (fibreTransport c u v Q) = Matrix.trace Q := by
  simp only [fibreTransport,matrixConjugate_trace]
lemma fibreTransport_kernel {c u v : (Euc ν)} {Q : (SqMat ν)} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖)
    (hQ : (matrixOp ν) Q u = 0) : (matrixOp ν) (fibreTransport c u v Q) v = 0 := by
  have hQc : (matrixOp ν) (matrixConjugate (householder c u) Q) c = 0 := by
    simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hQ
  simpa only [fibreTransport,householder_send hv] using matrixConjugate_kernel (householder c v) hQc
lemma fibreTransport_self (c u : (Euc ν)) (Q : (SqMat ν)) : fibreTransport c u u Q = Q :=
  matrixConjugate_involutive (householder_involutive c u) Q
lemma fibreTransport_center {c u : (Euc ν)} {Q : (SqMat ν)} (hQ : IsSelfAdjoint Q) (hu : ‖c‖ = ‖u‖)
    (hz : (matrixOp ν) Q u = 0) : fibreTransport c u c Q = matrixConjugate (householder c u) Q := by
  apply matrixConjugate_householder_self (matrixConjugate_selfAdjoint _ hQ)
  simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hz
lemma fibreTransport_unit_iff {c u v : (Euc ν)} {Q : (SqMat ν)} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖) :
    IsUnit (rankOne v + fibreTransport c u v Q) ↔ IsUnit (rankOne u + Q) := by
  have he : rankOne v + fibreTransport c u v Q =
      matrixConjugate (householder c v) (matrixConjugate (householder c u) (rankOne u + Q)) := by
    rw [map_add,map_add,matrixConjugate_rankOne,householder_swap hu,
      matrixConjugate_rankOne,householder_send hv]; rfl
  rw [he]
  exact (isUnit_map_iff (matrixConjugate (householder c v)) _).trans
    (isUnit_map_iff (matrixConjugate (householder c u)) _)
lemma fibreTransport_continuousOn (c : (Euc ν)) :
    ContinuousOn (fun p : (Euc ν) × (Euc ν) × (SqMat ν) => fibreTransport c p.1 p.2.1 p.2.2)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} := by
  have hR₁ : ContinuousOn (fun p : (Euc ν) × (Euc ν) × (SqMat ν) => reflectionMatrix c p.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hR₂ : ContinuousOn (fun p : (Euc ν) × (Euc ν) × (SqMat ν) => reflectionMatrix c p.2.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_snd.fst.continuousOn (fun _ h => h.2)
  simp only [fibreTransport,reflectionMatrix_conjugate]
  exact (hR₂.mul ((hR₁.mul continuous_snd.snd.continuousOn).mul hR₁)).mul hR₂
end FibreTransport
end
end
section
section
open scoped RealInnerProductSpace
section ChamberPath
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def chamberPath (c u : E) (t : ℝ) : E :=
  ‖(1-t) • u + t • c‖⁻¹ • ((1-t) • u + t • c)
lemma signChamber_smul {Z : Set E} {c u : E} (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : 0 < t) : t • u ∈ signChamber Z c := by
  intro z hz
  rw [real_inner_smul_left,mul_left_comm]
  exact mul_pos ht (hu z hz)
lemma chamber_interpolation_mem {Z : Set E} {c u : E} (hc : c ∈ safeNormals Z)
    (hu : u ∈ signChamber Z c) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • u + t • c ∈ signChamber Z c :=
  signChamber_convex Z c hu (mem_signChamber_self hc) (sub_nonneg.mpr ht.2) ht.1 (by ring)
lemma chamber_interpolation_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (1-t) • u + t • c ≠ 0 := by
  intro he
  have h := chamber_interpolation_mem hc hu ht c hcZ
  simp [he] at h
lemma chamberPath_norm {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ‖chamberPath c u t‖ = 1 := by
  have hn := chamber_interpolation_ne_zero hcZ hc hu ht
  simp only [chamberPath,norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]
lemma chamberPath_mem {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : chamberPath c u t ∈ signChamber Z c :=
  signChamber_smul (chamber_interpolation_mem hc hu ht)
    (inv_pos.mpr (norm_pos_iff.mpr (chamber_interpolation_ne_zero hcZ hc hu ht)))
lemma chamberPath_zero (c u : E) (hu : ‖u‖ = 1) : chamberPath c u 0 = u := by
  simp [chamberPath,hu]
lemma chamberPath_one (c u : E) (hc : ‖c‖ = 1) : chamberPath c u 1 = c := by
  simp [chamberPath,hc]
lemma chamber_add_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c) : c+u ≠ 0 := by
  intro he
  have h := hu c hcZ
  have hn := hc c hcZ
  have hei : ⟪c,c⟫ + ⟪u,c⟫ = 0 := by rw [← inner_add_left,he,inner_zero_left]
  have hei' : ⟪u,c⟫ = -⟪c,c⟫ := by linarith
  rw [hei'] at h
  nlinarith [sq_nonneg ⟪c,c⟫]
lemma chamberPath_continuousOn {Z : Set E} {c : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) : ContinuousOn (fun p : ℝ × E => chamberPath c p.2 p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ signChamber Z c) := by
  have hs : Continuous (fun p : ℝ × E => (1-p.1) • p.2 + p.1 • c) :=
    ((continuous_const.sub continuous_fst).smul continuous_snd).add
      (continuous_fst.smul continuous_const)
  exact (hs.norm.continuousOn.inv₀ (fun p hp => norm_ne_zero_iff.mpr
    (chamber_interpolation_ne_zero hcZ hc hp.2 hp.1))).smul hs.continuousOn
end ChamberPath
end
end
section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section PurityGeometry
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.safe_orthogonal_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u v : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    (hv : ‖v‖ = 1) (horth : ⟪u,v⟫ = 0) {i : ι} (hi : i ∈ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hv i)
  apply le_of_not_gt
  intro hp
  exact hu v ⟨i,hi,by rwa [homogeneousLift_unit f hv]⟩ horth
omit [DecidableEq ι] in
lemma Admissible.positiveExtension_safe_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : (SqMat ν)} (hQ : 0 ≤ Q) (hQu : (matrixOp ν) Q u = 0) {i : ι} (hi : i ∈ I) :
    positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v,⟨x,hx⟩,hv,hvi⟩ := (hf.positiveExtension_support hQ i).mp hp
  have horth : ⟪u,v⟫ = 0 := by rw [← hx]; exact matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu x
  exact (ne_of_gt hvi) (hf.safe_orthogonal_zero hu hv horth hi)
lemma Admissible.fibre_boundary_missing {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : (SqMat ν)} (hQ : 0 ≤ Q) (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ i ∈ Iᶜ, positiveExtension f Q i = 0 := by
  obtain ⟨v,hv,huv,hQv⟩ := fibre_boundary_kernel hQ u hnot
  obtain ⟨i,hi⟩ := hf.support_nonempty hv
  have hip := (mem_positiveSupport f v i).mp hi
  refine ⟨i,?_,hf.positiveExtension_kernel hQ hv hQv hip⟩
  exact Finset.mem_compl.mpr (fun h => (ne_of_gt hip) (hf.safe_orthogonal_zero hu hv huv h))
noncomputable def orientedLevel (f : (Euc ν) → ι → ℝ) (w : (Euc ν)) (r : ι → ℝ) : Set (Euc ν) :=
  {u | ‖u‖ = 1 ∧ f u = r ∧ 0 ≤ ⟪w,u⟫}
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_compact {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (w : (Euc ν)) (r : ι → ℝ) : IsCompact (orientedLevel f w r) := by
  have hc : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  have he : orientedLevel f w r = Metric.sphere (0:(Euc ν)) 1 ∩
      {u | f u = r ∧ 0 ≤ ⟪w,u⟫} := by ext u; simp [orientedLevel]
  rw [he]
  exact (isCompact_sphere (0:(Euc ν)) 1).inter_right ((isClosed_eq hc continuous_const).inter
    (isClosed_le continuous_const (show Continuous (fun u : (Euc ν) => ⟪w,u⟫) from
      (continuous_const.inner continuous_id))))
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_inner_pos {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i)
    {u : (Euc ν)} (hu : u ∈ orientedLevel f w r) : 0 < ⟪w,u⟫ := by
  apply lt_of_le_of_ne hu.2.2
  intro he
  obtain ⟨i,hi⟩ := hI
  exact hf.orthogonal w u hw hu.1 he.symm i ⟨hwi i hi,by rw [hu.2.1]; exact hr i hi⟩
omit [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] in
lemma orientedLevel_cone {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ}
    (hr : ∀ i ∈ I, 0 < r i) {u : (Euc ν)} (hu : u ∈ orientedLevel f w r) :
    u ∈ commonPositiveCone f I := by
  intro i hi
  rw [homogeneousLift_unit f hu.1,hu.2.1]
  exact hr i hi
noncomputable def levelFibre (f : (Euc ν) → ι → ℝ) (w : (Euc ν)) (r : ι → ℝ) : Set ((Euc ν) × (SqMat ν)) :=
  {p | p.1 ∈ orientedLevel f w r ∧ 0 ≤ p.2 ∧ Matrix.trace p.2 = 1 ∧ (matrixOp ν) p.2 p.1 = 0}
omit [Nonempty ν] [DecidableEq ι] in
lemma Admissible.levelFibre_compact {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (w : (Euc ν)) (r : ι → ℝ) : IsCompact (levelFibre f w r) := by
  have hA : Continuous (fun p : (Euc ν) × (SqMat ν) => (matrixOp ν) p.2) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd
  have he : levelFibre f w r = (orientedLevel f w r ×ˢ {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q = 1}) ∩
      {p | (matrixOp ν) p.2 p.1 = 0} := by ext p; simp only [levelFibre,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_prod,and_assoc]
  rw [he]
  exact ((hf.orientedLevel_compact w r).prod positive_slice_compact).inter_right
    (isClosed_eq (hA.clm_apply continuous_fst) continuous_const)
omit [Nonempty ν] in
lemma balancedFibre_mem {u : (Euc ν)} (hu : ‖u‖ = 1) {Q : (SqMat ν)}
    (hQ : 0 ≤ Q) (htr : Matrix.trace Q = 1) (hQu : (matrixOp ν) Q u = 0) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ traceSphere ν := by
  have hSA : IsSelfAdjoint ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) :=
    ((IsSelfAdjoint.all (_:ℝ)).smul (rankOne_nonneg u).isSelfAdjoint).sub
      ((IsSelfAdjoint.all (_:ℝ)).smul hQ.isSelfAdjoint)
  refine ⟨hSA,?_⟩
  obtain ⟨hp,hn⟩ := rankOne_split_parts hQ hQu (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num)
  rw [← CFC.posPart_add_negPart _ hSA,hp,hn,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
    rankOne_trace,hu,one_pow,htr]
  norm_num
end PurityGeometry
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
noncomputable def negativeCoordinates (f : (Euc ν) → ι → ℝ) (I : Finset ι) (Q : (SqMat ν)) :
    Euc ↥(Iᶜ : Finset ι) :=
  WithLp.toLp 2 (fun i => positiveExtension f Q i.val)
lemma Admissible.negativeCoordinates_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u) :
    (∑ i, negativeCoordinates f I Q i) = 1 := by
  have hz : ∀ i ∈ I, positiveExtension f Q i = 0 := fun i hi =>
    hf.positiveExtension_safe_zero hu hQ.1 hQ.2.2 hi
  have hs := hf.positiveExtension_sum hQ.1
  rw [hQ.2.1] at hs
  have he : ∑ i : ↥(Iᶜ : Finset ι), positiveExtension f Q i.val =
      ∑ i : ι, positiveExtension f Q i := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i (by simpa using hi))
  exact he.trans hs
noncomputable def transportedFibre (c : (Euc ν)) (t : ℝ) (u : (Euc ν)) (Q : (SqMat ν)) : (SqMat ν) :=
  fibreTransport c u (chamberPath c u t) Q
noncomputable def centeredFibre (c u : (Euc ν)) (Q : (SqMat ν)) : (SqMat ν) :=
  matrixConjugate (householder c u) Q
omit [Nonempty ν] in
lemma centeredFibre_mem {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1) {Q : (SqMat ν)}
    (hQ : Q ∈ matrixFibre u) : centeredFibre c u Q ∈ matrixFibre c := by
  refine ⟨matrixConjugate_nonneg _ hQ.1,?_,?_⟩
  · rw [centeredFibre,matrixConjugate_trace,hQ.2.1]
  · simpa only [centeredFibre,householder_swap (hc.trans hu.symm)] using
      matrixConjugate_kernel (householder c u) hQ.2.2
omit [Nonempty ν] [DecidableEq ι] in
lemma transportedFibre_mem {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u) :
    transportedFibre c t u Q ∈ matrixFibre (chamberPath c u t) := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  refine ⟨fibreTransport_nonneg _ _ _ hQ.1,?_,?_⟩
  · rw [transportedFibre,fibreTransport_trace,hQ.2.1]
  · exact fibreTransport_kernel (hcn.trans hun.symm) (hcn.trans hvn.symm) hQ.2.2
noncomputable def fibreHomotopy (f : (Euc ν) → ι → ℝ) (I : Finset ι) (c : (Euc ν))
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (t : ℝ) (u : (Euc ν)) (Q : (SqMat ν)) :=
  negativeCoordinates f I (transportedFibre c t u Q) +
    t • (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q))
omit [Nonempty ν] in
lemma fibreHomotopy_zero (f : (Euc ν) → ι → ℝ) (I : Finset ι) (c : (Euc ν))
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {u : (Euc ν)} (hu : ‖u‖ = 1) (Q : (SqMat ν)) :
    fibreHomotopy f I c g 0 u Q = negativeCoordinates f I Q := by
  simp only [fibreHomotopy,zero_smul,add_zero,transportedFibre,chamberPath_zero c u hu,
    fibreTransport_self]
omit [Nonempty ν] in
lemma fibreHomotopy_one (f : (Euc ν) → ι → ℝ) (I : Finset ι) {c u : (Euc ν)} (hc : ‖c‖ = 1)
    (hu : ‖u‖ = 1) (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {Q : (SqMat ν)}
    (hQ : Q ∈ matrixFibre u) : fibreHomotopy f I c g 1 u Q = g (centeredFibre c u Q) := by
  simp only [fibreHomotopy,one_smul,transportedFibre,chamberPath_one c u hc,
    fibreTransport_center hQ.1.isSelfAdjoint (hc.trans hu.symm) hQ.2.2]
  simp only [centeredFibre]
  abel
lemma Admissible.fibreHomotopy_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι))
    (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u) :
    (∑ i, fibreHomotopy f I c g t u Q i) = 1 := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvs := signChamber_subset_safeNormals _ _ (chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht)
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have hC := centeredFibre_mem hcn hun hQ
  simp only [fibreHomotopy,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
    Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hf.negativeCoordinates_sum hvs hT,hg _ hC,hf.negativeCoordinates_sum hcs hC]
  ring
lemma Admissible.fibreHomotopy_boundary_misses {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {c u : (Euc ν)} (hc : c ∈ commonPositiveCone f I)
    (hcn : ‖c‖ = 1) (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ Q ∈ matrixFibre c, ‖g Q - negativeCoordinates f I Q‖ < ε)
    (z : Euc ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u)
    (hn : ¬ IsUnit (rankOne u + Q)) : fibreHomotopy f I c g t u Q ≠ z := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvmem := chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have htn : ¬ IsUnit (rankOne (chamberPath c u t) + transportedFibre c t u Q) := by
    intro h
    exact hn ((fibreTransport_unit_iff (hcn.trans hun.symm) (hcn.trans hvn.symm)).mp h)
  obtain ⟨i,hi,hzi⟩ := hf.fibre_boundary_missing (signChamber_subset_safeNormals _ _ hvmem) hT.1 htn
  let j : ↥(Iᶜ : Finset ι) := ⟨i,hi⟩
  have hC := centeredFibre_mem hcn hun hQ
  have hb : |(g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j| < ε :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j)) (hg _ hC)
  intro he
  have hj := congrArg (fun v : Euc ↥(Iᶜ : Finset ι) => v j) he
  change positiveExtension f (transportedFibre c t u Q) i +
    t * ((g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j) = z j at hj
  rw [hzi,zero_add] at hj
  have hjb := hz j
  have hab := abs_lt.mp hb
  have hle := mul_le_mul_of_nonneg_left hab.2.le ht.1
  have hh : t * ε ≤ ε := by nlinarith [ht.2]
  linarith
end FibreHomotopy
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreContinuity
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.negativeCoordinates_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : ContinuousOn (negativeCoordinates f I) {Q : (SqMat ν) | 0 ≤ Q} := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i.val).comp_continuousOn hf.positiveExtension_continuousOn
omit [Nonempty ν] in
lemma centeredFibre_continuousOn (c : (Euc ν)) :
    ContinuousOn (fun p : (Euc ν) × (SqMat ν) => centeredFibre c p.1 p.2) {p | c+p.1 ≠ 0} :=
  householder_matrix_joint_continuousOn c
omit [Nonempty ν] in
lemma fibreTransport_continuousOn_comp {X : Type*} [TopologicalSpace X]
    {S : Set X} (c : (Euc ν)) {u v : X → (Euc ν)} {Q : X → (SqMat ν)}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (hQ : ContinuousOn Q S)
    (hc : ∀ x ∈ S, c+u x ≠ 0 ∧ c+v x ≠ 0) :
    ContinuousOn (fun x => fibreTransport c (u x) (v x) (Q x)) S := by
  exact ContinuousOn.comp' (g := fun p : (Euc ν) × (Euc ν) × (SqMat ν) => fibreTransport c p.1 p.2.1 p.2.2)
    (f := fun x : X => (u x,v x,Q x)) (s := S)
    (fibreTransport_continuousOn c) (hu.prodMk (hv.prodMk hQ)) hc
omit [DecidableEq ν] [Nonempty ν] in
lemma chamberPath_matrix_continuousOn {Z : Set (Euc ν)} {c : (Euc ν)} (hcz : c ∈ Z)
    (hcs : c ∈ safeNormals Z) :
    ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => chamberPath c p.2.1 p.1)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber Z c} := by
  have hp : Continuous (fun p : ℝ × (Euc ν) × (SqMat ν) => (p.1,p.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  exact ContinuousOn.comp' (g := fun p : ℝ × (Euc ν) => chamberPath c p.2 p.1)
    (f := fun p : ℝ × (Euc ν) × (SqMat ν) => (p.1,p.2.1))
    (chamberPath_continuousOn hcz hcs) hp.continuousOn (fun _ h => h)
omit [DecidableEq ι] in
omit [Nonempty ν] in
lemma transportedFibre_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) :
    ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => transportedFibre c p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber (activeVectors f I) c} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  apply fibreTransport_continuousOn_comp c continuous_snd.fst.continuousOn
    (chamberPath_matrix_continuousOn hcz hcs) continuous_snd.snd.continuousOn
  intro p hp
  exact ⟨chamber_add_ne_zero hcz hcs hp.2,
    chamber_add_ne_zero hcz hcs (chamberPath_mem hcz hcs hp.2 hp.1)⟩
lemma Admissible.fibreHomotopy_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  let S : Set (ℝ × (Euc ν) × (SqMat ν)) := {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1}
  have hT : ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => transportedFibre c p.1 p.2.1 p.2.2) S :=
    (transportedFibre_continuousOn hf hI hc).mono (fun _ hp => ⟨hp.1,hp.2.2.1⟩)
  have hC : ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => centeredFibre c p.2.1 p.2.2) S :=
    (centeredFibre_continuousOn c).comp continuous_snd.continuousOn
      (fun _ hp => chamber_add_ne_zero hcz hcs hp.2.2.1)
  have hET := (hf.negativeCoordinates_continuousOn I).comp hT
    (fun _ hp => (transportedFibre_mem hf hI hc hcn hp.2.1 hp.2.2.1 hp.1 hp.2.2.2).1)
  have hEC := (hf.negativeCoordinates_continuousOn I).comp hC
    (fun _ hp => (centeredFibre_mem hcn hp.2.1 hp.2.2.2).1)
  exact hET.add (continuous_fst.continuousOn.smul ((hg.comp_continuousOn hC).sub hEC))
end FibreContinuity
end
end
section
section
open scoped BigOperators
section BlockVector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def blockVector (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : Euc ↥(Iᶜ : Finset ι)) : Euc ι :=
  WithLp.toLp 2 (fun i => if hi : i ∈ I then lam * r i else -mu * z ⟨i,Finset.mem_compl.mpr hi⟩)
lemma blockVector_in (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : Euc ↥(Iᶜ : Finset ι)) {i : ι} (hi : i ∈ I) :
    blockVector I lam r mu z i = lam * r i := by simp [blockVector,hi]
lemma blockVector_out (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : Euc ↥(Iᶜ : Finset ι)) (i : ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z i.val = -mu * z i := by simp [blockVector,Finset.mem_compl.mp i.property]
lemma blockVector_continuous {X : Type*} [TopologicalSpace X] (I : Finset ι)
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → Euc ↥(Iᶜ : Finset ι)}
    (hl : Continuous lam) (hr : Continuous r) (hm : Continuous mu) (hz : Continuous z) :
    Continuous (fun x => blockVector I (lam x) (r x) (mu x) (z x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ I
  · simp only [dif_pos hi]
    exact hl.mul ((continuous_apply i).comp hr)
  · simp only [dif_neg hi]
    let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj : Continuous (fun x => z x j) := (PiLp.continuous_apply 2 _ j).comp hz
    exact hm.neg.mul hj
lemma blockVector_continuousOn {X : Type*} [TopologicalSpace X] (I : Finset ι) {S : Set X}
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → Euc ↥(Iᶜ : Finset ι)}
    (hl : ContinuousOn lam S) (hr : ContinuousOn r S) (hm : ContinuousOn mu S) (hz : ContinuousOn z S) :
    ContinuousOn (fun x => blockVector I (lam x) (r x) (mu x) (z x)) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact blockVector_continuous I (continuousOn_iff_continuous_domRestrict.mp hl)
    (continuousOn_iff_continuous_domRestrict.mp hr) (continuousOn_iff_continuous_domRestrict.mp hm)
    (continuousOn_iff_continuous_domRestrict.mp hz)
lemma blockVector_nonzero {I : Finset ι} (hI : I.Nonempty) {lam mu : ℝ} (hl : 0 < lam)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (z : Euc ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z ≠ 0 := by
  obtain ⟨i,hi⟩ := hI
  intro h
  have he := congrArg (fun v : Euc ι => v i) h
  rw [blockVector_in _ _ _ _ _ hi] at he
  exact (ne_of_gt (mul_pos hl (hr i hi))) he
lemma blockVector_ray {I : Finset ι} {lam mu t : ℝ} (_hl : 0 < lam) (_hm : 0 < mu)
    (hlm : lam + mu = 1) (_ht : 0 < t) {a r : ι → ℝ}
    (hao : ∀ i ∉ I, a i = 0) (hro : ∀ i ∉ I, r i = 0)
    (has : ∑ i, a i = 1) (hrs : ∑ i, r i = 1)
    {b z : Euc ↥(Iᶜ : Finset ι)} (hbs : ∑ i, b i = 1) (hzs : ∑ i, z i = 1)
    (he : blockVector I lam a mu b = t • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    t = 1 ∧ lam = 1/2 ∧ mu = 1/2 ∧ a = r ∧ b = z := by
  have hei (i : ι) (hi : i ∈ I) : lam * a i = t * ((1/2:ℝ) * r i) := by
    have h := congrArg (fun v : Euc ι => v i) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_in _ _ _ _ _ hi] using h
  have heo (i : ↥(Iᶜ : Finset ι)) : -mu * b i = t * (-(1/2:ℝ) * z i) := by
    have h := congrArg (fun v : Euc ι => v i.val) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_out] using h
  have hia : ∑ i ∈ I, a i = 1 := by
    rw [← has]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hao i hi)
  have hir : ∑ i ∈ I, r i = 1 := by
    rw [← hrs]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hro i hi)
  have hl' : lam = t*(1/2:ℝ) := by
    have hs := Finset.sum_congr (s₁ := I) (rfl) hei
    simpa only [← Finset.mul_sum,hia,hir,mul_one] using hs
  have hm' : -mu = t*(-(1/2:ℝ)) := by
    have hs := congrArg (fun v : ↥(Iᶜ : Finset ι) → ℝ => ∑ i, v i) (funext heo)
    simpa only [← Finset.mul_sum,hbs,hzs,mul_one] using hs
  have ht1 : t = 1 := by linarith
  have hl2 : lam = 1/2 := by linarith
  have hm2 : mu = 1/2 := by linarith
  refine ⟨ht1,hl2,hm2,?_,?_⟩
  · funext i
    by_cases hi : i ∈ I
    · have h := hei i hi; rw [ht1,hl2] at h; linarith
    · rw [hao i hi,hro i hi]
  · apply PiLp.ext
    intro i
    have h := heo i; rw [ht1,hm2] at h; linarith
end BlockVector
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.cone_unit_positive {f : (Euc ν) → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∈ I, 0 < f u i := by
  intro i hi
  simpa only [homogeneousLift_unit f hu] using hc i hi
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.maximal_cone_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {u : (Euc ν)} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∉ I, f u i = 0 := by
  have he : positiveSupport f u = I := hmax u hu (fun i hi =>
    (mem_positiveSupport f u i).mpr (hf.cone_unit_positive hu hc i hi))
  intro i hi
  apply le_antisymm _ (hf.nonneg u hu i)
  by_contra hp
  have hh := (mem_positiveSupport f u i).mpr (lt_of_not_ge hp)
  rw [he] at hh
  exact hi hh
omit [Nonempty ν] in
lemma traceSphere_weights {A : (SqMat ν)} (hA : A ∈ traceSphere ν) :
    Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
  rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]; exact hA.2
noncomputable def mixedHomotopy (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w c : (Euc ν))
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (t : ℝ) (A : (SqMat ν)) : (Euc ι) :=
  blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A))
lemma Admissible.mixedHomotopy_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : (Euc ν)} (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {A : (SqMat ν)}
    (hSA : IsSelfAdjoint A) (hA : A ∈ purityChart f I w c) :
    mixedHomotopy f I w c g 0 A = WithLp.toLp 2 (signedExtension f A) := by
  have hu := purityChart_unit hA
  have hQ := purityChart_fibre hA
  have hl := hasPositiveLine_trace_pos hA.2.1
  have hm := hA.2.2.2.1
  have hs := (hf.signedExtension_splitting hSA hu hl (positive_line_representative hA.2.1 hA.2.2.1)).2.2
  have hneg : positiveExtension f A⁻ = Matrix.trace A⁻ • positiveExtension f (negativeFibre A) := by
    calc
      positiveExtension f A⁻ = positiveExtension f (Matrix.trace A⁻ • negativeFibre A) :=
        congrArg (positiveExtension f) (negativeFibre_smul (ne_of_gt hm)).symm
      _ = _ := positiveExtension_smul_nonneg f hQ.1 hm.le
  have hpos := hf.cone_unit_positive hu hA.2.2.2.2.1
  have hzero := hf.maximal_cone_zero hmax hu hA.2.2.2.2.1
  have hsafe := hf.commonPositiveCone_safe I hA.2.2.2.2.1
  apply PiLp.ext
  intro i
  change blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g 0 (lineRepresentative w A) (negativeFibre A)) i = signedExtension f A i
  rw [fibreHomotopy_zero f I c g hu,hs,hneg]
  by_cases hi : i ∈ I
  · rw [blockVector_in _ _ _ _ _ hi]
    have hz := hf.positiveExtension_safe_zero hsafe hQ.1 hQ.2.2 hi
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hz,mul_zero,sub_zero]
  · let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj := blockVector_out I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) j
    rw [hj]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hzero i hi,mul_zero,zero_sub]
    exact neg_mul _ _
omit [Nonempty ν] in
lemma Admissible.mixedHomotopy_nonzero {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {w c : (Euc ν)} (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι))
    (t : ℝ) {A : (SqMat ν)} (hA : A ∈ purityChart f I w c) : mixedHomotopy f I w c g t A ≠ 0 :=
  blockVector_nonzero hI (hasPositiveLine_trace_pos hA.2.1)
    (hf.cone_unit_positive (purityChart_unit hA) hA.2.2.2.2.1) _
lemma Admissible.mixedHomotopy_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × traceSphere ν => mixedHomotopy f I w c g p.1 p.2.val)
      (Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}) := by
  let S : Set (ℝ × traceSphere ν) := Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}
  have hA : Continuous (fun p : ℝ × traceSphere ν => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hSA : ∀ p : ℝ × traceSphere ν, IsSelfAdjoint p.2.val := fun p => p.2.property.1
  have hu : ContinuousOn (fun p : ℝ × traceSphere ν => lineRepresentative w p.2.val) S :=
    (lineRepresentative_continuousOn _ hA hSA w).mono (fun p hp => hp.2.2.2.1)
  have hQ : ContinuousOn (fun p : ℝ × traceSphere ν => negativeFibre p.2.val) S :=
    (negativeFibre_continuousOn _ hA hSA).mono (fun p hp => ne_of_gt hp.2.2.2.2.1)
  have htuple : ContinuousOn (fun p : ℝ × traceSphere ν =>
      (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val)) S :=
    continuous_fst.continuousOn.prodMk (hu.prodMk hQ)
  have hF : ContinuousOn (fun p : ℝ × traceSphere ν =>
      fibreHomotopy f I c g p.1 (lineRepresentative w p.2.val) (negativeFibre p.2.val)) S :=
    ContinuousOn.comp' (g := fun p : ℝ × (Euc ν) × (SqMat ν) => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      (f := fun p : ℝ × traceSphere ν => (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val))
      (hf.fibreHomotopy_continuousOn hI hc hcn g hg) htuple
      (fun p hp => ⟨hp.1,purityChart_unit hp.2,interior_subset hp.2.2.2.2.2.2,purityChart_fibre hp.2⟩)
  have hl : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁺) :=
    matrix_trace_continuous.comp (matrix_posPart_continuousOn.comp_continuous hA hSA)
  have hm : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁻) :=
    matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA)
  have hfC : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  exact blockVector_continuousOn I hl.continuousOn (hfC.comp_continuousOn hu) hm.continuousOn hF
end MixedHomotopy
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHits
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.mixedHomotopy_hit {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty)
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {r : ι → ℝ} (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : Euc ↥(Iᶜ : Finset ι)} (hzs : ∑ i, z i = 1)
    {t d : ℝ} (ht : t ∈ Icc 0 1) (hd : 0 < d) {A : (SqMat ν)}
    (hSA : A ∈ traceSphere ν) (hA : A ∈ purityChart f I w c)
    (he : mixedHomotopy f I w c g t A = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    lineRepresentative w A ∈ orientedLevel f w r ∧
      fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A) = z ∧
      A = (1/2:ℝ) • rankOne (lineRepresentative w A) - (1/2:ℝ) • negativeFibre A := by
  have hu := purityChart_unit hA
  have hQ := purityChart_fibre hA
  have hl := hasPositiveLine_trace_pos hA.2.1
  have hm := hA.2.2.2.1
  have hzero := hf.maximal_cone_zero hmax hu hA.2.2.2.2.1
  have hsum := hf.fibreHomotopy_sum hI hc hcn hu (interior_subset hA.2.2.2.2.2) g hg ht hQ
  obtain ⟨-,hl2,hm2,ha,hb⟩ := blockVector_ray hl hm (traceSphere_weights hSA) hd hzero hro
    (hf.sum_one _ hu) hrs hsum hzs he
  refine ⟨⟨hu,ha,(lineRepresentative_inner_pos hA.2.1 hA.2.2.1).le⟩,hb,?_⟩
  calc
    A = Matrix.trace A⁺ • rankOne (lineRepresentative w A) - Matrix.trace A⁻ • negativeFibre A :=
      negativeFibre_splitting hSA.1 hA.2.1 hA.2.2.1 hm
    _ = _ := by rw [hl2,hm2]
omit [DecidableEq ι] in
lemma Admissible.negative_trace_pos {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {A : (SqMat ν)} {i : ι}
    (hi : signedExtension f A i < 0) : 0 < Matrix.trace A⁻ := by
  have hp := (hf.signedExtension_neg_iff A i).mp hi
  have hle : positiveExtension f A⁻ i ≤ Matrix.trace A⁻ := by
    rw [← hf.positiveExtension_sum (CFC.negPart_nonneg A)]
    exact Finset.single_le_sum (fun j _ => hf.positiveExtension_nonneg A⁻ j) (Finset.mem_univ i)
  exact hp.trans_le hle
lemma Admissible.original_ray_level {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc ν)} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : Euc ↥(Iᶜ : Finset ι)} (hz : ∀ i, 0 < z i) (hzs : ∑ i, z i = 1)
    {A : (SqMat ν)} (hA : A ∈ traceSphere ν) {d : ℝ} (hd : 0 < d)
    (he : WithLp.toLp 2 (signedExtension f A) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    IsUnit A ∧ HasPositiveLine A ∧ (matrixOp ν) A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
      lineRepresentative w A ∈ orientedLevel f w r := by
  have hpos (i : ι) (hi : i ∈ I) : 0 < signedExtension f A i := by
    have hh := congrArg (fun v : (Euc ι) => v i) he
    change signedExtension f A i = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i at hh
    rw [hh,blockVector_in _ _ _ _ _ hi]
    exact mul_pos hd (mul_pos (by norm_num) (hr i hi))
  have hneg (i : ↥(Iᶜ : Finset ι)) : signedExtension f A i.val < 0 := by
    have hh := congrArg (fun v : (Euc ι) => v i.val) he
    change signedExtension f A i.val = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i.val at hh
    rw [hh,blockVector_out]
    exact mul_neg_of_pos_of_neg hd (mul_neg_of_neg_of_pos (by norm_num) (hz i))
  have hunit : IsUnit A := hf.signedExtension_fullSupport hA.1 (fun i => by
    by_cases hi : i ∈ I
    · exact ne_of_gt (hpos i hi)
    · exact ne_of_lt (hneg ⟨i,Finset.mem_compl.mpr hi⟩))
  obtain ⟨i,hi⟩ := hI
  have hline : HasPositiveLine A := hf.signedExtension_positive_rankOne hw hwi
    (fun j hj => (hneg ⟨j,Finset.mem_compl.mpr hj⟩).le) ⟨i,hpos i hi⟩
  have hAw : (matrixOp ν) A⁺ w ≠ 0 := by
    obtain ⟨u,hu,lam,hl,hP⟩ := hline
    have hui : 0 < f u i := (hf.signedExtension_line_labels hu hl hP i).mp (hpos i hi)
    have hwu : ⟪w,u⟫ ≠ 0 := fun heq => hf.orthogonal w u hw hu heq i ⟨hwi i hi,hui⟩
    exact unit_rankOne_inner_nonzero ⟨u,hu,lam,hl,hP⟩ hu hl hP hwu
  have hu := lineRepresentative_norm hAw
  have hc : lineRepresentative w A ∈ commonPositiveCone f I := by
    intro j hj
    rw [homogeneousLift_unit f hu]
    exact (hf.signedExtension_line_labels hu (hasPositiveLine_trace_pos hline)
      (positive_line_representative hline hAw) j).mp (hpos j hj)
  have hm := hf.negative_trace_pos (hneg (Classical.arbitrary ↥(Iᶜ : Finset ι)))
  have hchart : A ∈ purityChart f I w (lineRepresentative w A) :=
    ⟨hunit,hline,hAw,hm,hc,interior_safe_mem_own_chamber (hf.commonPositiveCone_interior_safe I hc)⟩
  have hg := hf.mixedHomotopy_zero hmax (fun _ => (0 : Euc ↥(Iᶜ : Finset ι))) hA.1 hchart
  have hb : blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z := by
    rw [← he,← hg]
    exact congrArg (blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻))
      (fibreHomotopy_zero f I (lineRepresentative w A) (fun _ => 0) hu (negativeFibre A)).symm
  have hQ := purityChart_fibre hchart
  obtain ⟨-,-,-,ha,-⟩ := blockVector_ray (hasPositiveLine_trace_pos hline) hm (traceSphere_weights hA) hd
    (hf.maximal_cone_zero hmax hu hc) hro (hf.sum_one _ hu) hrs
    (hf.negativeCoordinates_sum (hf.commonPositiveCone_safe I hc) hQ) hzs hb
  exact ⟨hunit,hline,hAw,hm,hu,ha,(lineRepresentative_inner_pos hline hAw).le⟩
end MixedHits
end
end
section
section
open scoped BigOperators Topology
noncomputable def finiteOpenGlue {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    (S : κ → Set X) (f : κ → X → Y) : X → Y :=
  by classical exact fun x => ∑ i, if x ∈ S i then f i x else 0
lemma finiteOpenGlue_eq {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    {S : κ → Set X} (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (f : κ → X → Y)
    {i : κ} {x : X} (hx : x ∈ S i) : finiteOpenGlue S f x = f i x := by
  classical
  rw [finiteOpenGlue,Finset.sum_eq_single i]
  · simp [hx]
  · intro j hj hji
    have hjx : x ∉ S j := fun hp => Set.disjoint_left.mp (hS hji) hp hx
    simp [hjx]
  · simp
lemma finiteOpenGlue_continuousOn_prod {κ X Y : Type*} [Fintype κ]
    [TopologicalSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    {S : κ → Set X} (hSo : ∀ i, IsOpen (S i)) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : κ → ℝ × X → Y) (hf : ∀ i, ContinuousOn (f i) (Set.Icc (0:ℝ) 1 ×ˢ S i)) :
    ContinuousOn (finiteOpenGlue (fun i => {p : ℝ × X | p.2 ∈ S i}) f)
      (Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i) := by
  intro p hp
  obtain ⟨i,hpi⟩ := Set.mem_iUnion.mp hp.2
  have hn : ∀ᶠ q in 𝓝 p, q.2 ∈ S i :=
    continuous_snd.continuousAt.preimage_mem_nhds ((hSo i).mem_nhds hpi)
  have hs : Set.Icc (0:ℝ) 1 ×ˢ S i ∈ 𝓝[Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i] p := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with q hq hqi
    exact ⟨hqi.1,hq⟩
  have hSp : Pairwise (fun i j => Disjoint {p : ℝ × X | p.2 ∈ S i} {p : ℝ × X | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hi hj => Set.disjoint_left.mp (hS hij) hi hj)
  apply ((hf i p ⟨hp.1,hpi⟩).mono_of_mem_nhdsWithin hs).congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq
    exact finiteOpenGlue_eq hSp f hq
  · exact finiteOpenGlue_eq hSp f hpi
end
end
section
section
open Set
lemma compact_target_hits {P X Y : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (φ : P → X) (hφ : Continuous φ) (K : ℝ × P → Y)
    (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ univ)) (y : Y) :
    IsCompact {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} := by
  have hC : IsCompact ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) :=
    ((isCompact_Icc.prod isCompact_univ) : IsCompact (Icc (0:ℝ) 1 ×ˢ (univ : Set P))).of_isClosed_subset
      (hK.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_univ) isClosed_singleton) inter_subset_left
  have he : {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} =
      (fun q : ℝ × P => φ q.2) '' ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) := by
    ext x
    constructor
    · rintro ⟨p,hp,t,ht,hk⟩
      exact ⟨(t,p),⟨⟨ht,mem_univ _⟩,hk⟩,hp⟩
    · rintro ⟨⟨t,p⟩,⟨⟨ht,-⟩,hk⟩,hp⟩
      exact ⟨p,hp,t,ht,hk⟩
  rw [he]
  exact hC.image (hφ.comp continuous_snd)
end
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section LevelModel
variable {ν ι κ : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
noncomputable def balancedModel {f : (Euc ν) → ι → ℝ} {w : (Euc ν)} {r : ι → ℝ}
    (p : levelFibre f w r) : traceSphere ν :=
  ⟨(1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2,
    balancedFibre_mem p.property.1.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2⟩
omit [Fintype ι] [DecidableEq ι] in
omit [Nonempty ν] in
lemma balancedModel_continuous (f : (Euc ν) → ι → ℝ) (w : (Euc ν)) (r : ι → ℝ) :
    Continuous (balancedModel (f := f) (w := w) (r := r)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : levelFibre f w r => (1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2)
  exact ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul
    (rankOne_continuous.comp continuous_subtype_val.fst)).sub
    ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul continuous_subtype_val.snd)
noncomputable def modelChambers (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w : (Euc ν)) (r : ι → ℝ)
    (c : κ → (Euc ν)) (j : κ) : Set (levelFibre f w r) :=
  {p | p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))}
omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_open (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w : (Euc ν)) (r : ι → ℝ) (c : κ → (Euc ν)) (j : κ) :
    IsOpen (modelChambers f I w r c j) :=
  isOpen_interior.preimage continuous_subtype_val.fst
omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_disjoint {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ} {c : κ → (Euc ν)}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j))))) :
    Pairwise (fun i j => Disjoint (modelChambers f I w r c i) (modelChambers f I w r c j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun p hp hq => Set.disjoint_left.mp (hd hij) hp hq)
omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_cover {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ} {c : κ → (Euc ν)}
    (hc : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j))) :
    (⋃ j, modelChambers f I w r c j) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hc p.property.1)
  exact mem_iUnion.mpr ⟨j,hj⟩
noncomputable def levelHomotopy (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w : (Euc ν)) (r : ι → ℝ)
    (c : κ → (Euc ν)) (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) :
    ℝ × levelFibre f w r → Euc ↥(Iᶜ : Finset ι) :=
  finiteOpenGlue (fun j => {p | p.2 ∈ modelChambers f I w r c j})
    (fun j p => fibreHomotopy f I (c j) (g j) p.1 p.2.val.1 p.2.val.2)
omit [Nonempty ν] in
lemma levelHomotopy_eq {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ} {c : κ → (Euc ν)}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {p : levelFibre f w r} {j : κ}
    (hp : p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))) (t : ℝ) :
    levelHomotopy f I w r c g (t,p) = fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 := by
  apply finiteOpenGlue_eq
  · intro a b hab
    exact Set.disjoint_left.mpr (fun q ha hb => Set.disjoint_left.mp (hd hab) ha hb)
  · exact hp
lemma Admissible.levelHomotopy_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : (Euc ν)} {r : ι → ℝ} (c : κ → (Euc ν))
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j)) :
    ContinuousOn (levelHomotopy f I w r c g) (Icc (0:ℝ) 1 ×ˢ univ) := by
  rw [← modelChambers_cover hcover]
  apply finiteOpenGlue_continuousOn_prod (modelChambers_open f I w r c) (modelChambers_disjoint hd)
  intro j
  have hpar : Continuous (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2)) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).fst.prodMk
      (continuous_subtype_val.comp continuous_snd).snd)
  have hmap : MapsTo (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
      (Icc (0:ℝ) 1 ×ˢ modelChambers f I w r c j)
      {p : ℝ × (Euc ν) × (SqMat ν) | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) (c j) ∧ p.2.2 ∈ matrixFibre p.2.1} :=
    fun p hp => ⟨hp.1,p.2.property.1.1,interior_subset hp.2,p.2.property.2⟩
  exact ContinuousOn.comp' (g := fun p : ℝ × (Euc ν) × (SqMat ν) => fibreHomotopy f I (c j) (g j) p.1 p.2.1 p.2.2)
    (f := fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
    (hf.fibreHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j)) hpar.continuousOn hmap
lemma Admissible.level_hits_compact {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : (Euc ν)} {r : ι → ℝ} (c : κ → (Euc ν))
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j))
    (z : Euc ↥(Iᶜ : Finset ι)) :
    IsCompact {A : traceSphere ν | ∃ p : levelFibre f w r, balancedModel p = A ∧
      ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z} := by
  let : CompactSpace (levelFibre f w r) := isCompact_iff_compactSpace.mp (hf.levelFibre_compact w r)
  exact compact_target_hits balancedModel (balancedModel_continuous f w r)
    (levelHomotopy f I w r c g) (hf.levelHomotopy_continuousOn hI c hc hcn hd hcover g hg) z
end LevelModel
end
end
section
namespace SmithTheory
section CharacteristicCochains
variable {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
variable (d N : P →ₗ[ZMod 2] P)
def SmithCocycle : Submodule (ZMod 2) (P →ₗ[ZMod 2] ZMod 2) where
  carrier := {φ | φ.comp N = 0 ∧ φ.comp d = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ; simp [LinearMap.add_comp, hφ.1, hφ.2, hψ.1, hψ.2]
  smul_mem' := by intro a φ hφ; simp [LinearMap.smul_comp, hφ.1, hφ.2]
noncomputable def smithLift (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : P →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)
lemma smithLift_comp_norm (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : (smithLift d N hexact φ).comp N = φ.val :=
  Classical.choose_spec (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)
noncomputable def smithNext (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    SmithCocycle d N :=
  ⟨(smithLift d N hexact φ).comp d, by
    constructor
    · rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc,
        smithLift_comp_norm, φ.property.2]
    · rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]⟩
noncomputable def smithCochain (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    ℕ → SmithCocycle d N
  | 0 => φ
  | n+1 => smithNext d N hd hcomm hexact (smithCochain hd hcomm hexact φ n)
noncomputable def smithDegree (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) :
    P →ₗ[ZMod 2] ZMod 2 :=
  smithLift d N hexact (smithCochain d N hd hcomm hexact φ n)
lemma smithDegree_norm (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    smithDegree d N hd hcomm hexact φ n (N c) =
      (smithCochain d N hd hcomm hexact φ n).val c :=
  LinearMap.congr_fun (smithLift_comp_norm d N hexact _) c
lemma smithCochain_succ (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    (smithCochain d N hd hcomm hexact φ (n+1)).val c =
      smithDegree d N hd hcomm hexact φ n (d c) := rfl
variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
lemma smithDegree_natural
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N)
    (d' N' : Q →ₗ[ZMod 2] Q) (hd' : d'.comp d' = 0) (hcomm' : d'.comp N' = N'.comp d')
    (hexact' : LinearMap.ker N' ≤ LinearMap.range N') (φ' : SmithCocycle d' N')
    (T : P →ₗ[ZMod 2] Q) (hTd : d'.comp T = T.comp d) (hTN : N'.comp T = T.comp N)
    (hTφ : φ'.val.comp T = φ.val) (n : ℕ) (c : P) (hNc : N c = 0) (hdc : d c = 0) :
    smithDegree d' N' hd' hcomm' hexact' φ' n (T c) =
      smithDegree d N hd hcomm hexact φ n c := by
  induction n generalizing c with
  | zero =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm]
    exact LinearMap.congr_fun hTφ x
  | succ n ih =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm, smithCochain_succ, smithCochain_succ,
      ← LinearMap.comp_apply d' T, hTd, LinearMap.comp_apply]
    apply ih
    · rw [← LinearMap.comp_apply N d, ← hcomm, LinearMap.comp_apply, hx, hdc]
    · exact LinearMap.congr_fun hd x
end CharacteristicCochains
end SmithTheory
end
section
namespace SimplicialChains
open Finset
open BorsukNine.SmithTheory
section CharacteristicDegree
variable {V : Type*} [DecidableEq V]
variable (K : PreComplex V) (e : V ≃ V)
variable (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
variable (hfree : ∀ s ∈ K, s.image e ≠ s)
noncomputable def characteristicAugmentation : SmithCocycle (boundary K) (normMap K e) :=
  ⟨augmentation K, augmentation_normMap K e (fun s hs => (he s).mp hs),
    augmentation_boundary K⟩
include he hi hfree in
lemma normMap_exact : LinearMap.ker (normMap K e) ≤ LinearMap.range (normMap K e) := by
  rw [normMap_eq K e he]
  exact involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)
noncomputable def characteristicDegree (n : ℕ) : Chain K →ₗ[F₂] F₂ :=
  smithDegree (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) n
end CharacteristicDegree
end SimplicialChains
namespace SimplicialChains
open Finset BorsukNine.SmithTheory
section NaturalDegree
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
lemma characteristicDegree_natural
    (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (L : PreComplex W) (d : W ≃ W)
    (hd : ∀ s, s ∈ L ↔ s.image d ∈ L) (hdi : Function.Involutive d)
    (hdfree : ∀ s ∈ L, s.image d ≠ s)
    (T : Chain K →ₗ[F₂] Chain L)
    (hTbd : (boundary L).comp T = T.comp (boundary K))
    (hTN : (normMap L d).comp T = T.comp (normMap K e))
    (hTa : (augmentation L).comp T = augmentation K)
    (n : ℕ) (c : Chain K) (hcN : normMap K e c = 0) (hcb : boundary K c = 0) :
    characteristicDegree L d hd hdi hdfree n (T c) =
      characteristicDegree K e he hi hfree n c := by
  exact smithDegree_natural (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) (boundary L) (normMap L d) (boundary_sq L)
    (boundary_normMap L d (fun s hs => (hd s).mp hs)) (normMap_exact L d hd hdi hdfree)
    (characteristicAugmentation L d hd) T hTbd hTN hTa n c hcN hcb
end NaturalDegree
noncomputable def crossFundamental (n : ℕ) : Chain (cross n) :=
  normMap (cross n) flip (crossTower n (n-1))
lemma crossFundamental_norm (n : ℕ) : normMap (cross n) flip (crossFundamental n) = 0 :=
  LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _
lemma crossFundamental_boundary (n : ℕ) (hn : 0 < n) :
    boundary (cross n) (crossFundamental n) = 0 :=
  crossTower_norm_boundary n (n-1) (by omega)
lemma crossFundamental_degree (n : ℕ) (hn : 0 < n) :
    crossFundamental n ∈ degreeChains (cross n) n := by
  have h := normMap_degree (cross n) flip (cross_flip_forward n) (n-1+1)
    (crossTower_degree n (n-1))
  change normMap (cross n) flip (crossTower n (n-1)) ∈
    degreeChains (cross n) (n-1+1) at h
  simpa only [crossFundamental, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
lemma characteristicCochain_crossTower (n i : ℕ) (hi : i < n) :
    (smithCochain (boundary (cross n)) (normMap (cross n) flip) (boundary_sq (cross n))
      (boundary_normMap (cross n) flip (cross_flip_forward n))
      (normMap_exact (cross n) flip (cross_flip n) flip_involutive (cross_free n))
      (characteristicAugmentation (cross n) flip (cross_flip n)) i).val
        (crossTower n i) = 1 := by
  induction i with
  | zero => exact crossTower_augmentation n (by omega)
  | succ i ih =>
    rw [smithCochain_succ, crossTower_boundary n i hi, smithDegree_norm]
    exact ih (by omega)
lemma characteristicDegree_crossFundamental (n : ℕ) (hn : 0 < n) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (crossFundamental n) = 1 := by
  unfold characteristicDegree crossFundamental
  rw [smithDegree_norm]
  exact characteristicCochain_crossTower n (n-1) (by omega)
lemma cross_equivariant_degree_one (n : ℕ) (hn : 0 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n)) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (T (crossFundamental n)) = 1 := by
  rw [characteristicDegree_natural (cross n) flip (cross_flip n) flip_involutive
    (cross_free n) (cross n) flip (cross_flip n) flip_involutive (cross_free n)
    T hTbd hTN hTa (n-1) (crossFundamental n) (crossFundamental_norm n)
    (crossFundamental_boundary n hn), characteristicDegree_crossFundamental n hn]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
section Coefficients
variable {V : Type*} [DecidableEq V] (K : PreComplex V)
omit [DecidableEq V] in
lemma degreeChains_card_of_ne_zero (n : ℕ) {c : Chain K}
    (hc : c ∈ degreeChains K n) (s : {s : Finset V // s ∈ K}) (hs : c s ≠ 0) :
    s.val.card = n := by
  by_contra h
  exact hs ((Finsupp.mem_supported' F₂ c).mp hc s h)
lemma simplex_coeff (s : Finset V) (t : {t : Finset V // t ∈ K}) :
    simplex K s t = if s = t.val then 1 else 0 := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs]
    simp only [Finsupp.single_apply]
    congr 1
    exact propext Subtype.ext_iff
  · have hst : s ≠ t.val := fun h => hs (h ▸ t.property)
    simp [simplex, hs, hst]
lemma boundary_simplex_coeff {s : Finset V} (hs : s ∈ K)
    (t : {t : Finset V // t ∈ K}) (hcard : t.val.card + 1 = s.card) :
    boundary K (simplex K s) t = if t.val ⊆ s then 1 else 0 := by
  classical
  rw [boundary_simplex K hs, Finsupp.finsetSum_apply]
  simp_rw [simplex_coeff]
  by_cases hts : t.val ⊆ s
  · rw [if_pos hts]
    obtain ⟨a,ha,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts,hcard⟩
    rw [Finset.sum_insert ha, Finset.erase_insert ha, if_pos rfl]
    have hz : ∀ b ∈ t.val, (if (insert a t.val).erase b = t.val then (1:F₂) else 0) = 0 := by
      intro b hb
      rw [if_neg]
      intro he
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have hh : a ∈ (insert a t.val).erase b := Finset.mem_erase.mpr
        ⟨hab, Finset.mem_insert_self _ _⟩
      exact ha (he ▸ hh)
    rw [Finset.sum_eq_zero hz, add_zero]
  · rw [if_neg hts]
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro he
    exact hts (he ▸ Finset.erase_subset a s)
end Coefficients
noncomputable def crossFacet (n : ℕ) (b : Fin n → Bool) : Finset SignedVertex :=
  Finset.univ.image (fun i : Fin n => (i.val,b i))
lemma mem_crossFacet (n : ℕ) (b : Fin n → Bool) (v : SignedVertex) :
    v ∈ crossFacet n b ↔ ∃ i : Fin n, v = (i.val,b i) := by
  classical
  simp only [crossFacet, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)
lemma crossFacet_card (n : ℕ) (b : Fin n → Bool) : (crossFacet n b).card = n := by
  classical
  rw [crossFacet, Finset.card_image_iff.mpr, Finset.card_univ, Fintype.card_fin]
  intro i _ j _ hij
  exact Fin.ext (congrArg Prod.fst hij)
lemma crossFacet_mem (n : ℕ) (hn : 0 < n) (b : Fin n → Bool) : crossFacet n b ∈ cross n := by
  classical
  refine ⟨?_,?_,?_⟩
  · exact Finset.card_pos.mp (by rw [crossFacet_card]; exact hn)
  · intro v hv
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    exact i.isLt
  · intro v hv w hw he
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    obtain ⟨j,rfl⟩ := (mem_crossFacet n b w).mp hw
    have hij : i = j := Fin.ext he
    rw [hij]
lemma cross_top_exists_signs (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n)
    (hcard : s.card = n) : ∃ b : Fin n → Bool, s = crossFacet n b := by
  classical
  have hproj : s.image Prod.fst = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv)
    · rw [Finset.card_image_iff.mpr hs.2.2, Finset.card_range, hcard]
  have hex (i : Fin n) : ∃ v ∈ s, v.1 = i.val := by
    apply Finset.mem_image.mp
    rw [hproj]
    exact Finset.mem_range.mpr i.isLt
  choose v hv hvi using hex
  refine ⟨fun i => (v i).2, ?_⟩
  ext w
  constructor
  · intro hw
    let i : Fin n := ⟨w.1,hs.2.1 w hw⟩
    have he : w = v i := hs.2.2 hw (hv i) (hvi i).symm
    apply (mem_crossFacet n _ w).mpr
    refine ⟨i, ?_⟩
    apply Prod.ext
    · rfl
    · change w.2 = (v i).2
      exact congrArg Prod.snd he
  · intro hw
    obtain ⟨i,rfl⟩ := (mem_crossFacet n _ w).mp hw
    have he : (i.val,(v i).2) = v i := Prod.ext (hvi i).symm rfl
    rw [he]
    exact hv i
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
noncomputable def flipAt {n : ℕ} (b : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update b i (! b i)
lemma flipAt_ne {n : ℕ} (b : Fin n → Bool) (i : Fin n) : flipAt b i ≠ b := by
  intro he
  have hi := congrFun he i
  simp [flipAt] at hi
lemma crossFacet_injective (n : ℕ) : Function.Injective (crossFacet n) := by
  intro b c he
  funext i
  have hi : (i.val,b i) ∈ crossFacet n c := he ▸ (mem_crossFacet n b _).mpr ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := (mem_crossFacet n c _).mp hi
  have hij : i = j := Fin.ext (congrArg Prod.fst hj)
  simpa only [← hij] using congrArg Prod.snd hj
noncomputable def crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) : Finset SignedVertex :=
  (crossFacet n b).erase (i.val,b i)
lemma crossRidge_card (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    (crossRidge n b i).card = n-1 := by
  rw [crossRidge, Finset.card_erase_of_mem ((mem_crossFacet n b _).mpr ⟨i,rfl⟩),
    crossFacet_card]
lemma crossRidge_mem (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ∈ cross n := by
  apply ((cross n).isRelLowerSet_faces (crossFacet_mem n (by omega) b)).2
    (Finset.erase_subset _ _)
  apply Finset.card_pos.mp
  change 0 < (crossRidge n b i).card
  rw [crossRidge_card]
  omega
lemma mem_crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) (v : SignedVertex) :
    v ∈ crossRidge n b i ↔ ∃ j : Fin n, j ≠ i ∧ v = (j.val,b j) := by
  classical
  simp only [crossRidge, Finset.mem_erase, mem_crossFacet]
  constructor
  · rintro ⟨hne,j,rfl⟩
    exact ⟨j, fun h => hne (h ▸ rfl), rfl⟩
  · rintro ⟨j,hji,rfl⟩
    refine ⟨?_,j,rfl⟩
    exact fun h => hji (Fin.ext (congrArg Prod.fst h))
lemma crossRidge_subset_iff (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ ∀ j : Fin n, j ≠ i → c j = b j := by
  constructor
  · intro h j hji
    have hj := h ((mem_crossRidge n b i _).mpr ⟨j,hji,rfl⟩)
    obtain ⟨k,hk⟩ := (mem_crossFacet n c _).mp hj
    have hjk : j = k := Fin.ext (congrArg Prod.fst hk)
    simpa only [← hjk] using (congrArg Prod.snd hk).symm
  · intro h v hv
    obtain ⟨j,hji,rfl⟩ := (mem_crossRidge n b i v).mp hv
    exact (mem_crossFacet n c _).mpr ⟨j, by rw [h j hji]⟩
lemma crossRidge_parents (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ c = b ∨ c = flipAt b i := by
  rw [crossRidge_subset_iff]
  constructor
  · intro h
    by_cases hi : c i = b i
    · left
      funext j
      by_cases hj : j = i
      · subst j; exact hi
      · exact h j hj
    · right
      have hb : c i = !b i := by cases hci : c i <;> cases hbi : b i <;> simp_all
      funext j
      by_cases hj : j = i
      · subst j; simpa [flipAt] using hb
      · simpa [flipAt, hj] using h j hj
  · rintro (rfl | rfl) j hj
    · rfl
    · simp [flipAt, hj]
lemma boundary_ridge_coefficient (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) :
    boundary (cross n) c ⟨crossRidge n b i,crossRidge_mem n hn b i⟩ =
      c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ +
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  classical
  let r : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossRidge n b i,crossRidge_mem n hn b i⟩
  let s : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩
  let t : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩
  let α : Chain (cross n) →ₗ[F₂] F₂ := Finsupp.lapply s + Finsupp.lapply t
  change ((Finsupp.lapply r).comp (boundary (cross n))) c = α c
  apply linearMap_eq_of_support
  intro a ha
  have hcard : a.val.card = n := degreeChains_card_of_ne_zero (cross n) n hc a (Finsupp.mem_support_iff.mp ha)
  obtain ⟨d,hd⟩ := cross_top_exists_signs n a.val a.property hcard
  have hcoeff := boundary_simplex_coeff (cross n) a.property r (by
    change (crossRidge n b i).card + 1 = a.val.card
    rw [crossRidge_card, hcard]
    omega)
  simp only [α, LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.add_apply]
  rw [hcoeff, simplex_coeff, simplex_coeff]
  change (if crossRidge n b i ⊆ a.val then (1:F₂) else 0) =
    (if a.val = crossFacet n b then 1 else 0) +
    (if a.val = crossFacet n (flipAt b i) then 1 else 0)
  rw [hd]
  simp only [crossRidge_parents, crossFacet_injective n |>.eq_iff]
  have hne : flipAt b i ≠ b := flipAt_ne b i
  by_cases hb : d = b <;> by_cases ht : d = flipAt b i <;> simp_all
lemma cross_cycle_adjacent_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) (hd : boundary (cross n) c = 0) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  have h := boundary_ridge_coefficient n hn b i c hc
  rw [hd, Finsupp.zero_apply] at h
  have he := eq_neg_of_add_eq_zero_left h.symm
  simpa only [CharTwo.neg_eq] using he
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
lemma bool_cube_constant {n : ℕ} {A : Type*} (p : (Fin n → Bool) → A)
    (hp : ∀ b i, p b = p (flipAt b i)) (b c : Fin n → Bool) : p b = p c := by
  classical
  suffices hs : ∀ (s : Finset (Fin n)) (b c : Fin n → Bool),
      (∀ i ∉ s, b i = c i) → p b = p c by
    exact hs Finset.univ b c (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro b c h
    have he : b = c := funext (fun i => h i (by simp))
    rw [he]
  | @insert i s _ ih =>
    intro b c h
    let d := Function.update b i (c i)
    have hd : ∀ j ∉ s, d j = c j := by
      intro j hj
      by_cases he : j = i
      · subst j; simp [d]
      · simpa [d, he] using h j (by simp [hj, he])
    have he : p b = p d := by
      by_cases hb : b i = c i
      · have hbd : b = d := by
          funext j
          by_cases hji : j = i
          · subst j; simpa [d] using hb
          · simp [d, hji]
        rw [hbd]
      · have hflip : c i = !b i := by
          cases hbi : b i <;> cases hci : c i <;> simp_all
        have hdflip : d = flipAt b i := by simp only [d, flipAt, hflip]
        rw [hdflip]
        exact hp b i
    exact he.trans (ih d c hd)
lemma cross_cycle_coeff_constant (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b d : Fin n → Bool) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ :=
  bool_cube_constant _ (fun b i => cross_cycle_adjacent_coeff n hn b i c hc hd) b d
lemma crossFundamental_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) :
    crossFundamental n ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ = 1 := by
  have hnonzero : crossFundamental n ≠ 0 := by
    intro h
    have hd := characteristicDegree_crossFundamental n (by omega)
    rw [h, map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨s,hs⟩ : ∃ s, crossFundamental n s ≠ 0 := by
    by_contra h
    push Not at h
    exact hnonzero (Finsupp.ext h)
  have hcard : s.val.card = n := degreeChains_card_of_ne_zero (cross n) n
    (crossFundamental_degree n (by omega)) s hs
  obtain ⟨d,hd⟩ := cross_top_exists_signs n s.val s.property hcard
  have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd
  rw [hsd] at hs
  have hconst := cross_cycle_coeff_constant n hn (crossFundamental n)
    (crossFundamental_degree n (by omega)) (crossFundamental_boundary n (by omega)) b d
  rw [hconst]
  have h₂ : ∀ x : F₂, x = 0 ∨ x = 1 := by decide
  exact (h₂ _).resolve_left hs
lemma cross_top_cycle_eq (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ • crossFundamental n := by
  classical
  ext s
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hcard : s.val.card = n
  · obtain ⟨d,hd'⟩ := cross_top_exists_signs n s.val s.property hcard
    have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd'
    rw [hsd, crossFundamental_coeff n hn d, mul_one]
    exact cross_cycle_coeff_constant n hn c hc hd d b
  · have hz : c s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n hc s hs)
    have hz' : crossFundamental n s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n
        (crossFundamental_degree n (by omega)) s hs)
    rw [hz, hz', mul_zero]
lemma cross_characteristicDegree_eq_coeff (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ := by
  conv_lhs => rw [cross_top_cycle_eq n hn c hc hd b]
  rw [map_smul, characteristicDegree_crossFundamental n (by omega), smul_eq_mul, mul_one]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq W] in
lemma double_erase_sum_fun (L : PreComplex W) (H : Finset V → Chain L)
    (s : Finset V) : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain L := if p.1 = p.2 then 0 else H ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p _
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self L _
  · intro p _ hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p _; exact Prod.swap_swap p
  · intro p hp; exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))
omit [DecidableEq V] in
lemma support_mapSimplex (L : PreComplex W) (f : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (mapSimplex L f s).support) : t.val = s.image f := by
  unfold mapSimplex at ht
  split_ifs at ht
  · exact (mem_support_simplex L _ t).mp ht
  · simp at ht
omit [DecidableEq V] in
lemma mapSimplex_degree (L : PreComplex W) (f : V → W) (s : Finset V) :
    mapSimplex L f s ∈ degreeChains L s.card := by
  unfold mapSimplex
  split_ifs with h
  · rw [← h]; exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _
lemma mapSimplex_boundary (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    boundary L (mapSimplex L f s) = ∑ a ∈ s, mapSimplex L f (s.erase a) := by
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hinj), boundary_simplex L hs,
      Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [mapSimplex, if_pos (Finset.card_image_iff.mpr (hinj.mono (Finset.erase_subset a s))),
        image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, if_neg (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]
omit [DecidableEq V] in
lemma mapSimplex_augmentation (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    augmentation L (mapSimplex L f s) = if s.card = 1 then 1 else 0 := by
  by_cases hinj : (s.image f).card = s.card
  · rw [mapSimplex, if_pos hinj, augmentation_simplex L hs, hinj]
  · have hc : s.card ≠ 1 := by
      intro h
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
      simp at hinj
    simp [mapSimplex, hinj, hc]
noncomputable def contigSimplex (L : PreComplex W) (f g : V → W)
    (s : Finset V) : Chain L :=
  if hs : s.Nonempty then
    cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s +
      ∑ a ∈ s.attach, contigSimplex L f g (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property
@[simp] lemma contigSimplex_empty (L : PreComplex W) (f g : V → W) :
    contigSimplex L f g ∅ = 0 := by rw [contigSimplex]; simp
lemma contigSimplex_nonempty (L : PreComplex W) (f g : V → W)
    {s : Finset V} (hs : s.Nonempty) :
    contigSimplex L f g s = cone L (f hs.choose)
      (mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)) := by
  rw [contigSimplex, dif_pos hs]
  exact congrArg (fun z => cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s + z))
    (Finset.sum_attach s (fun a : V => contigSimplex L f g (s.erase a)))
lemma contigSimplex_carrier (L : PreComplex W) (f g : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (contigSimplex L f g s).support) : t.val ⊆ s.image f ∪ s.image g := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp at ht
    rw [contigSimplex_nonempty L f g hs] at ht
    obtain ⟨u,hu,_,htu⟩ := support_cone L _ _ ht
    rw [htu]
    apply Finset.insert_subset
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f hs.choose_spec)
    have hsub : ∀ a ∈ s, (s.erase a).image f ∪ (s.erase a).image g ⊆ s.image f ∪ s.image g := by
      intro a _
      exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
        (Finset.image_subset_image (Finset.erase_subset a s))
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · rcases Finset.mem_union.mp (Finsupp.support_add hu) with hf | hg
      · rw [support_mapSimplex L f s hf]; exact Finset.subset_union_left
      · rw [support_mapSimplex L g s hg]; exact Finset.subset_union_right
    · obtain ⟨a,ha,hua⟩ := support_sum_chains L s _ hu
      exact (ih (s.erase a) (Finset.erase_ssubset ha) hua).trans (hsub a ha)
lemma contigSimplex_degree (L : PreComplex W) (f g : V → W)
    (s : Finset V) : contigSimplex L f g s ∈ degreeChains L (s.card+1) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [contigSimplex_empty]; exact Submodule.zero_mem _
    rw [contigSimplex_nonempty L f g hs]
    apply cone_degree L _ s.card
    apply Submodule.add_mem _
    · exact Submodule.add_mem _ (mapSimplex_degree L f s) (mapSimplex_degree L g s)
    · apply Submodule.sum_mem
      intro a ha
      have h := ih (s.erase a) (Finset.erase_ssubset ha)
      simpa only [Finset.card_erase_of_mem ha, Nat.sub_add_cancel hs.card_pos] using h
lemma contigSimplex_augmentation (L : PreComplex W) (f g : V → W)
    (s : Finset V) : augmentation L (contigSimplex L f g s) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  exact augmentation_eq_zero_of_degree L (s.card+1) (by have := hs.card_pos; omega)
    (contigSimplex_degree L f g s)
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
lemma contigSimplex_boundary (L : PreComplex W) (f g : V → W)
    {s : Finset V} (hs : s.image f ∪ s.image g ∈ L) :
    boundary L (contigSimplex L f g s) =
      mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn : s.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hs' : (∅ : Finset W) ∈ L := by simpa [he] using hs
      simpa using (L.isRelLowerSet_faces hs').1
    have hf : s.image f ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_left (hn.image f)
    have hg : s.image g ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_right (hn.image g)
    have hb : f hn.choose ∈ s.image f ∪ s.image g :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem f hn.choose_spec)
    let z := mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)
    have hi (a : V) (ha : a ∈ s) : boundary L (contigSimplex L f g (s.erase a)) =
        mapSimplex L f (s.erase a) + mapSimplex L g (s.erase a) +
          ∑ b ∈ s.erase a, contigSimplex L f g ((s.erase a).erase b) := by
      rcases (s.erase a).eq_empty_or_nonempty with he | hne
      · simp [he, mapSimplex]
      · apply ih (s.erase a) (Finset.erase_ssubset ha)
        apply (L.isRelLowerSet_faces hs).2
        · exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s))
        · exact (hne.image f).mono Finset.subset_union_left
    have hzbd : boundary L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_boundary L f hf, mapSimplex_boundary L g hg]
      rw [Finset.sum_congr rfl hi]
      simp only [Finset.sum_add_distrib]
      rw [double_erase_sum_fun, add_zero]
      exact chain_add_self L _
    have hzaug : augmentation L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_augmentation L f hf,
        mapSimplex_augmentation L g hg, contigSimplex_augmentation, Finset.sum_const_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
    have hzcone : ∀ t ∈ z.support, insert (f hn.choose) t.val ∈ L := by
      intro t ht
      apply (L.isRelLowerSet_faces hs).2 _ (Finset.insert_nonempty _ _)
      apply Finset.insert_subset hb
      rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
      · rcases Finset.mem_union.mp (Finsupp.support_add ht) with htf | htg
        · rw [support_mapSimplex L f s htf]; exact Finset.subset_union_left
        · rw [support_mapSimplex L g s htg]; exact Finset.subset_union_right
      · obtain ⟨a,ha,hta⟩ := support_sum_chains L s _ ht
        exact (contigSimplex_carrier L f g (s.erase a) hta).trans
          (Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s)))
    rw [contigSimplex_nonempty L f g hn]
    change boundary L (cone L (f hn.choose) z) = z
    rw [cone_boundary L _ z hzcone, hzbd, hzaug, map_zero, zero_smul, add_zero, add_zero]
noncomputable def contigMap (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => contigSimplex L f g s.val)
lemma contigMap_simplex (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) {s : Finset V} (hs : s ∈ K) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  simp [simplex_of_mem K hs, contigMap, Finsupp.linearCombination_single]
lemma contigMap_simplex_subset (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact contigMap_simplex K L f g ((K.isRelLowerSet_faces ht).2 hs hn)
lemma contigMap_degree (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L (d+1)).comap (contigMap K L f g) := by
  apply grade_map K L _ d (d+1)
  intro s hs hd
  rw [contigMap_simplex K L f g hs, ← hd]
  exact contigSimplex_degree L f g s
lemma contigMap_boundary_of_support (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L) :
    boundary L (contigMap K L f g c) = mapChains K L f c + mapChains K L g c +
      contigMap K L f g (boundary K c) := by
  let A : Chain K →ₗ[F₂] Chain L :=
    mapChains K L f + mapChains K L g + (contigMap K L f g).comp (boundary K)
  change ((boundary L).comp (contigMap K L f g)) c = A c
  apply linearMap_eq_of_support
  intro s hs
  simp only [LinearMap.comp_apply, A, LinearMap.add_apply]
  rw [contigMap_simplex K L f g s.property, contigSimplex_boundary L f g (hc s hs),
    mapChains_simplex K L f s.property, mapChains_simplex K L g s.property,
    boundary_simplex K s.property, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (contigMap_simplex_subset K L f g s.property (Finset.erase_subset a s.val)).symm
lemma contig_maps_agree_top (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) (d : ℕ) (c : Chain K)
    (hc : c ∈ degreeChains K d) (hbd : boundary K c = 0)
    (hfg : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L)
    (hL : ∀ s ∈ L, s.card ≤ d) : mapChains K L f c = mapChains K L g c := by
  have hh : contigMap K L f g c = 0 := by
    have ht := contigMap_degree K L f g d hc
    rw [degreeChains_eq_bot_of_card_bound L (d+1) (fun s hs => by have := hL s hs; omega)] at ht
    exact ht
  have he := contigMap_boundary_of_support K L f g c hfg
  rw [hh, map_zero, hbd, map_zero, add_zero] at he
  have h := eq_neg_of_add_eq_zero_left he.symm
  have hn : -(mapChains K L g c) = mapChains K L g c := by
    ext s
    exact CharTwo.neg_eq _
  exact h.trans hn
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
noncomputable def approximation (n m r : ℕ)
    (f : Euc (Fin n) → SignedVertex) : Chain (cross n) →ₗ[F₂] Chain (cross m) :=
  (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp (fineCrossMap n r)
def IsFineLabel (n m r : ℕ) (f : Euc (Fin n) → SignedVertex) : Prop :=
  ∀ (s : Finset SignedVertex), s ∈ cross n →
    ∀ (t : {s : Finset (Euc (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}),
      t ∈ (fineCrossMap n r (simplex (cross n) s)).support → t.val.image f ∈ cross m
lemma approximation_boundary (n m r : ℕ) (f : Euc (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (boundary (cross m)).comp (approximation n m r f) =
      (approximation n m r f).comp (boundary (cross n)) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : boundary (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      approximation n m r f (boundary (cross n) (simplex (cross n) s.val)) := by
    change boundary (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_boundary_of_support _ (cross m) f _ (hf s.val s.property)]
    have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
    rw [hb]
    rfl
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]
lemma approximation_augmentation (n m r : ℕ) (f : Euc (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (augmentation (cross m)).comp (approximation n m r f) = augmentation (cross n) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : augmentation (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      augmentation (cross n) (simplex (cross n) s.val) := by
    change augmentation (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_augmentation_of_support _ (cross m) f _ (hf s.val s.property)]
    exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]
lemma approximation_norm (n m r : ℕ) (hn : 0 < n)
    (f : Euc (Fin n) → SignedVertex)
    (hf : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    (normMap (cross m) flip).comp (approximation n m r f) =
      (approximation n m r f).comp (normMap (cross n) flip) := by
  have hu : (normMap (cross m) flip).comp (mapChains (hemisphereComplex (n:ℝ)) (cross m) f) =
      (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp
        (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)) := by
    apply mapChains_norm _ (cross m) (Equiv.neg _) flip (hemisphere_neg (n:ℝ)) (cross_flip m) f
    intro s hs x hx
    exact hf x (hemisphere_vertex_annulus n hn hs hx)
  rw [approximation, ← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
    fineCrossMap_norm, ← LinearMap.comp_assoc]
lemma approximation_degree (n m r d : ℕ) (f : Euc (Fin n) → SignedVertex) :
    degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap (approximation n m r f) := by
  intro c hc
  exact mapChains_degree_all _ (cross m) f d (fineCrossMap_degree n r d hc)
lemma cross_equivariant_fundamental (n : ℕ) (hn : 1 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n))
    (hTd : ∀ c ∈ degreeChains (cross n) n, T c ∈ degreeChains (cross n) n) :
    T (crossFundamental n) = crossFundamental n := by
  have hc := hTd _ (crossFundamental_degree n (by omega))
  have hb : boundary (cross n) (T (crossFundamental n)) = 0 := by
    rw [← LinearMap.comp_apply, hTbd, LinearMap.comp_apply,
      crossFundamental_boundary n (by omega), map_zero]
  have hd : T (crossFundamental n) ⟨crossFacet n (fun _ => false),
      crossFacet_mem n (by omega) (fun _ => false)⟩ = 1 := by
    rw [← cross_characteristicDegree_eq_coeff n hn _ hc hb]
    exact cross_equivariant_degree_one n (by omega) T hTbd hTN hTa
  rw [cross_top_cycle_eq n hn _ hc hb (fun _ => false), hd, one_smul]
lemma approximation_odd_fundamental (n r : ℕ) (hn : 1 < n)
    (f : Euc (Fin n) → SignedVertex) (hf : IsFineLabel n n r f)
    (ho : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    approximation n n r f (crossFundamental n) = crossFundamental n := by
  apply cross_equivariant_fundamental n hn _ (approximation_boundary n n r f hf)
    (approximation_norm n n r (by omega) f ho) (approximation_augmentation n n r f hf)
  intro c hc
  exact approximation_degree n n r n f hc
lemma approximation_agree_top (n m r : ℕ) (hn : 0 < n)
    (f g : Euc (Fin n) → SignedVertex)
    (hcard : m ≤ n)
    (hfg : ∀ s ∈ (fineCrossMap n r (crossFundamental n)).support,
      s.val.image f ∪ s.val.image g ∈ cross m) :
    approximation n m r f (crossFundamental n) = approximation n m r g (crossFundamental n) := by
  apply contig_maps_agree_top _ (cross m) f g n _
    (fineCrossMap_degree n r n (crossFundamental_degree n hn)) _ hfg
    (fun s hs => (cross_card m s hs).trans hcard)
  rw [← LinearMap.comp_apply, fineCrossMap_boundary, LinearMap.comp_apply,
    crossFundamental_boundary n hn, map_zero]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped Topology
lemma fineCrossMap_mesh (n r : ℕ) (c : Chain (cross n))
    {t : {s : Finset (Euc (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  obtain ⟨s,_,ht⟩ := support_linearMap (cross n) (hemisphereComplex (n:ℝ)) _ c ht
  exact fineCrossMap_simplex_mesh n r s.property ht
lemma cross_union_labels_mem {m : ℕ} [NeZero m] {V : Type*} [DecidableEq V]
    (s : Finset V) (hs : s.Nonempty) (f g : V → Euc (Fin m))
    (hn : ∀ x ∈ s, ‖f x‖ = 1 ∧ ‖g x‖ = 1)
    (hclose : ∀ x ∈ s, ∀ y ∈ s,
      dist (f x) (f y) < (1:ℝ)/m ∧ dist (f x) (g y) < (1:ℝ)/m ∧
      dist (g x) (f y) < (1:ℝ)/m ∧ dist (g x) (g y) < (1:ℝ)/m) :
    s.image (fun x => sphereLabel (f x)) ∪ s.image (fun x => sphereLabel (g x)) ∈ cross m := by
  refine ⟨(hs.image _).mono Finset.subset_union_left, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;> exact sphereLabel_bound _
  · intro v hv w hw he
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;>
      rcases Finset.mem_union.mp hw with hff | hgg <;>
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ‹_›
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).1 (hclose x hx y hy).1 he
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).2 (hclose x hx y hy).2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).1 (hclose x hx y hy).2.2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).2 (hclose x hx y hy).2.2.2 he
lemma sphere_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × Euc (Fin n) → Euc (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHn : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, ‖H p‖ = 1) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ u ∈ Set.Icc (0:ℝ) 1,
      approximation n m r (fun x => sphereLabel (H (t,x))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (H (u,x))) (crossFundamental n) := by
  classical
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := isCompact_Icc.prod (annulus_compact n)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hH) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let C : Set.Icc (0:ℝ) 1 → Chain (cross m) :=
    fun t => approximation n m r (fun x => sphereLabel (H (t.val,x))) (crossFundamental n)
  have hClocal : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_eventually_eq C).mpr
    intro t
    filter_upwards [Metric.ball_mem_nhds t hδ] with u hu
    apply approximation_agree_top n m r hn _ _ hmn
    intro s hs
    have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
    have ha : ∀ x ∈ s.val, x ∈ annulus n :=
      fun x hx => hemisphere_vertex_annulus n hn s.property hx
    have hh (v w : Set.Icc (0:ℝ) 1) (hv : dist v.val w.val < δ)
        (x : Euc (Fin n)) (hx : x ∈ s.val)
        (y : Euc (Fin n)) (hy : y ∈ s.val) :
        dist (H (v.val,x)) (H (w.val,y)) < (1:ℝ)/m := by
      apply hclose (v.val,x) ⟨v.property,ha x hx⟩ (w.val,y) ⟨w.property,ha y hy⟩
      rw [Prod.dist_eq]
      exact max_lt hv ((hmesh x hx y hy).trans_lt hr)
    have hut : dist u.val t.val < δ := hu
    have htu : dist t.val u.val < δ := by simpa only [dist_comm] using hut
    apply cross_union_labels_mem s.val s.property.1 _ _
    · intro x hx
      exact ⟨hHn (u.val,x) ⟨u.property,ha x hx⟩,hHn (t.val,x) ⟨t.property,ha x hx⟩⟩
    · intro x hx y hy
      exact ⟨hh u u (by simpa using hδ) x hx y hy,hh u t hut x hx y hy,
        hh t u htu x hx y hy,hh t t (by simpa using hδ) x hx y hy⟩
  let : PreconnectedSpace (Set.Icc (0:ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  intro t ht u hu
  exact hClocal.apply_eq_of_preconnectedSpace ⟨t,ht⟩ ⟨u,hu⟩
lemma exists_small_cross_mesh (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  exact ⟨r,by linarith⟩
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
noncomputable def labelRegion {m : ℕ} (i : Fin m) (b : Bool) :
    Set (Euc (Fin m)) :=
  {y | (∀ j, |y j| ≤ |y i|) ∧ if b then y i ≤ 0 else 0 ≤ y i}
lemma labelRegion_closed {m : ℕ} (i : Fin m) (b : Bool) : IsClosed (labelRegion i b) := by
  have hc (j : Fin m) : Continuous (fun y : Euc (Fin m) => y j) :=
    PiLp.continuous_apply 2 _ j
  apply IsClosed.inter
  · change IsClosed {y : Euc (Fin m) | ∀ j, |y j| ≤ |y i|}
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (hc j).abs (hc i).abs)
  · cases b
    · exact isClosed_le continuous_const (hc i)
    · exact isClosed_le (hc i) continuous_const
lemma sphereLabel_mem_region {m : ℕ} [NeZero m] (y : Euc (Fin m))
    (i : Fin m) (b : Bool) (hy : sphereLabel y = (i.val,b)) : y ∈ labelRegion i b := by
  have hi : peakIndex y = i := Fin.ext (congrArg Prod.fst hy)
  have hb : decide (y (peakIndex y) < 0) = b := congrArg Prod.snd hy
  refine ⟨?_,?_⟩
  · intro j
    rw [← hi]
    exact maxIndex_le (fun j => |y j|) j
  · rw [← hb, hi]
    by_cases h : y i < 0
    · simp only [h, decide_true, ↓reduceIte]
      exact h.le
    · simp only [h, decide_false]
      exact le_of_not_gt h
lemma compact_label_locality {X : Type*} [MetricSpace X] [CompactSpace X]
    {m : ℕ} [NeZero m] (b : Fin m → Bool)
    (f g : X → Euc (Fin m)) (hf : Continuous f) (hg : Continuous g)
    (U : Set X) (hU : IsOpen U)
    (heq : ∀ x ∈ U, f x = g x)
    (hfull : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) ∨
      (∀ i, g x ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ x : X,
      (∀ y, dist y x < δ → f y = g y) ∨
      ∃ i j : Fin m,
        (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        (∀ y, dist y x < δ → sphereLabel (g y) ≠ (j.val,b j)) := by
  let c : Option (Fin m × Fin m) → Set X := fun o => match o with
    | none => U
    | some (i,j) => (f ⁻¹' labelRegion i (b i))ᶜ ∩ (g ⁻¹' labelRegion j (b j))ᶜ
  have hc : ∀ i, IsOpen (c i) := by
    intro o
    cases o with
    | none => exact hU
    | some p =>
      exact ((labelRegion_closed p.1 (b p.1)).preimage hf).isOpen_compl.inter
        ((labelRegion_closed p.2 (b p.2)).preimage hg).isOpen_compl
  have hcover : (Set.univ : Set X) ⊆ ⋃ o, c o := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨none,hx⟩
    · have hnf : ¬ ∀ i, f x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inl hh))
      have hng : ¬ ∀ i, g x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inr hh))
      obtain ⟨i,hi⟩ := not_forall.mp hnf
      obtain ⟨j,hj⟩ := not_forall.mp hng
      exact Set.mem_iUnion.mpr ⟨some (i,j),hi,hj⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨o,ho⟩ := hball x (Set.mem_univ _)
  cases o with
  | none => exact Or.inl (fun y hy => heq y (ho hy))
  | some p =>
    refine Or.inr ⟨p.1,p.2,?_,?_⟩
    · intro y hy he
      exact (ho hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro y hy he
      exact (ho hy).2 (sphereLabel_mem_region _ _ _ he)
lemma mapSimplex_coeff_zero_of_ne {V W : Type*} [DecidableEq V] [DecidableEq W]
    (L : PreComplex W) (f : V → W) (s : Finset V)
    (t : {s : Finset W // s ∈ L}) (hne : s.image f ≠ t.val) :
    mapSimplex L f s t = 0 := by
  rw [mapSimplex]
  split_ifs <;> simp_all [simplex_coeff]
lemma image_ne_crossFacet_of_missing {V : Type*} [DecidableEq V] {m : ℕ}
    (s : Finset V) (f : V → SignedVertex) (b : Fin m → Bool)
    (i : Fin m) (hi : ∀ x ∈ s, f x ≠ (i.val,b i)) : s.image f ≠ crossFacet m b := by
  intro h
  have hm : (i.val,b i) ∈ s.image f := by
    rw [h]
    exact (mem_crossFacet m b _).mpr ⟨i,rfl⟩
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
  exact hi x hx he
lemma localized_approximation_coeff (n m : ℕ) (hn : 0 < n) [NeZero m]
    (b : Fin m → Bool)
    (f g : Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ContinuousOn g (annulus n))
    (U : Set (annulus n)) (hU : IsOpen U)
    (heq : ∀ x : annulus n, x ∈ U → f x.val = g x.val)
    (hfull : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) ∨
      (∀ i, g x.val ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      approximation n m r (fun x => sphereLabel (g x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_label_locality b (fun x : annulus n => f x.val)
    (fun x : annulus n => g x.val) hf.domRestrict hg.domRestrict U hU heq hfull
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := Euc (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g x)))
  change T (fineCrossMap n r (crossFundamental n)) = R (fineCrossMap n r (crossFundamental n))
  apply linearMap_eq_of_support T R _
  intro s hs
  change mapChains K (cross m) (fun x => sphereLabel (f x)) (simplex K s.val) t =
    mapChains K (cross m) (fun x => sphereLabel (g x)) (simplex K s.val) t
  rw [mapChains_simplex K (cross m) _ s.property,mapChains_simplex K (cross m) _ s.property]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  rcases hlocal ⟨x,ha x hx⟩ with he | ⟨i,j,hi,hj⟩
  · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g y)) := by
      apply Finset.image_congr
      intro y hy
      exact congrArg sphereLabel (he ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr))
    simp only [mapSimplex,himg]
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t, mapSimplex_coeff_zero_of_ne (cross m) _ s.val t]
    · apply image_ne_crossFacet_of_missing s.val _ b j
      intro y hy
      exact hj ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)
    · apply image_ne_crossFacet_of_missing s.val _ b i
      intro y hy
      exact hi ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
noncomputable def signVector (m : ℕ) (b : Fin m → Bool) : Euc (Fin m) :=
  WithLp.toLp 2 (fun i => if b i then (-1:ℝ) else 1)
@[simp] lemma signVector_apply (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    signVector m b i = if b i then (-1:ℝ) else 1 := rfl
lemma signVector_norm (m : ℕ) (b : Fin m → Bool) : ‖signVector m b‖ = Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have h (i : Fin m) : ‖signVector m b i‖ ^ 2 = (1:ℝ) := by
    simp only [signVector_apply]
    cases b i <;> norm_num
  simp only [h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one]
noncomputable def facetCenter (m : ℕ) (b : Fin m → Bool) : Euc (Fin m) :=
  (Real.sqrt m)⁻¹ • signVector m b
lemma facetCenter_norm (m : ℕ) [NeZero m] (b : Fin m → Bool) : ‖facetCenter m b‖ = 1 := by
  rw [facetCenter, norm_smul, signVector_norm, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast NeZero.pos m)))
lemma facetCenter_region (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    facetCenter m b ∈ labelRegion i (b i) := by
  have ha (j : Fin m) : |facetCenter m b j| = (Real.sqrt m)⁻¹ := by
    simp only [facetCenter, PiLp.smul_apply, smul_eq_mul, signVector_apply, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    cases b j <;> norm_num
  refine ⟨fun j => by rw [ha j,ha i],?_⟩
  change (if b i then (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1) ≤ 0
    else 0 ≤ (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1))
  have h := inv_nonneg.mpr (Real.sqrt_nonneg (m:ℝ))
  cases b i <;> simp_all
lemma all_labelRegions_iff_center (m : ℕ) [NeZero m] (b : Fin m → Bool)
    (y : Euc (Fin m)) (hy : ‖y‖ = 1) :
    (∀ i, y ∈ labelRegion i (b i)) ↔ y = facetCenter m b := by
  refine ⟨?_,fun he i => he ▸ facetCenter_region m b i⟩
  intro hyc
  let i₀ : Fin m := ⟨0,NeZero.pos m⟩
  let d : ℝ := |y i₀|
  have hd : 0 ≤ d := abs_nonneg _
  have hcoord (i : Fin m) : |y i| = d :=
    le_antisymm ((hyc i₀).1 i) ((hyc i).1 i₀)
  have hv : y = d • signVector m b := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, signVector_apply]
    have hsign := (hyc i).2
    change (if b i then y i ≤ 0 else 0 ≤ y i) at hsign
    cases hb : b i
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      simpa only [abs_of_nonneg hsign, mul_one] using hcoord i
    · simp only [hb, ↓reduceIte] at hsign ⊢
      have he := hcoord i
      rw [abs_of_nonpos hsign] at he
      linarith
  have hdval : d = (Real.sqrt m)⁻¹ := by
    have he := hy
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,signVector_norm] at he
    exact eq_inv_of_mul_eq_one_left he
  rw [hv,hdval]
  rfl
lemma constant_approximation_facet_zero (n m r : ℕ) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (y : Euc (Fin m)) :
    approximation n m r (fun _ => sphereLabel y) (crossFundamental n)
      ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  classical
  let K := hemisphereComplex (n:ℝ) (E := Euc (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} := ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun _ => sphereLabel y))
  change T (fineCrossMap n r (crossFundamental n)) = 0
  have ht : T = 0 := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : T (simplex K s.val) = 0 := by
      change mapChains K (cross m) (fun _ => sphereLabel y) (simplex K s.val) t = 0
      rw [mapChains_simplex K (cross m) _ s.property]
      apply mapSimplex_coeff_zero_of_ne
      intro he
      have hc : (s.val.image (fun _ => sphereLabel y)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha c hc
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp hc
        rfl
      rw [he,crossFacet_card] at hc
      omega
    rw [simplex_of_mem K s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [ha,map_smul,hh,smul_zero,LinearMap.zero_apply]
  rw [ht,LinearMap.zero_apply]
lemma continuous_missed_facet_zero (n m : ℕ) (hn : 0 < n) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (f : Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f (annulus n)) (hfn : ∀ x ∈ annulus n, ‖f x‖ = 1)
    (hmiss : ∀ x ∈ annulus n, f x ≠ facetCenter m b) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  have hfneg : -(facetCenter m b) ≠ facetCenter m b := by
    intro he
    have hz : facetCenter m b = 0 := by
      ext i
      have hi := congrArg (fun z : Euc (Fin m) => z i) he
      simp only [PiLp.neg_apply] at hi
      change facetCenter m b i = 0
      linarith
    have hn := facetCenter_norm m b
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨δ,hδ,hh⟩ := localized_approximation_coeff n m hn b f (fun _ => -(facetCenter m b))
    hf continuousOn_const ∅ isOpen_empty (by simp) (by
      intro x hx
      rcases hx with h | h
      · exact False.elim (hmiss x.val x.property ((all_labelRegions_iff_center m b _ (hfn _ x.property)).mp h))
      · exact False.elim (hfneg ((all_labelRegions_iff_center m b _ (by simp [facetCenter_norm])).mp h)))
  refine ⟨δ,hδ,fun r hr => ?_⟩
  rw [hh r hr,constant_approximation_facet_zero n m r hm b]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
lemma eventually_fine_sphereLabel (n m : ℕ) (hn : 0 < n) [NeZero m]
    (g : Euc (Fin n) → Euc (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ → IsFineLabel n m r (fun x => sphereLabel (g x)) := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((annulus_compact n).uniformContinuousOn_of_continuous hg) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr s hs t ht
  refine ⟨t.property.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact sphereLabel_bound _
  · intro v hv w hw he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    have hx' := hemisphere_vertex_annulus n hn t.property hx
    have hy' := hemisphere_vertex_annulus n hn t.property hy
    exact sphereLabel_compatible _ _ (hgn x hx') (hgn y hy')
      (hclose x hx' y hy' ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hr)) he
lemma eventually_odd_sphere_degree (n : ℕ) (hn : 1 < n) [NeZero n]
    (g : Euc (Fin n) → Euc (Fin n))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) = crossFundamental n := by
  obtain ⟨δ,hδ,hr⟩ := eventually_fine_sphereLabel n n (by omega) g hg hgn
  refine ⟨δ,hδ,fun r hh => approximation_odd_fundamental n r hn _ (hr r hh) ?_⟩
  intro x hx
  rw [hgo x hx,sphereLabel_neg _ (hgn x hx)]
lemma normalized_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × Euc (Fin n) → Euc (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (unitRadial (H (0,x)))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (unitRadial (H (1,x)))) (crossFundamental n) := by
  obtain ⟨δ,hδ,hh⟩ := sphere_homotopy_chains n m hn hmn (fun p => unitRadial (H p))
    ((unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp hH hHz)
    (fun p hp => unitRadial_norm (hHz p hp))
  exact ⟨δ,hδ,fun r hr => hh r hr 0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩⟩
end SimplicialChains
end
section
namespace SimplicialChains
open scoped RealInnerProductSpace
lemma odd_homotopy_surjective (n : ℕ) (hn : 1 < n) [NeZero n]
    (H : ℝ × Euc (Fin n) → Euc (Fin n))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    {y : Euc (Fin n)} (hy : ‖y‖ = 1) :
    ∃ x ∈ annulus n, unitRadial (H (1,x)) = y := by
  classical
  by_contra hmiss
  push Not at hmiss
  let b : Fin n → Bool := fun _ => false
  let L := householder y (facetCenter n b)
  have hLy : L y = facetCenter n b := householder_send (hy.trans (facetCenter_norm n b).symm)
  let K : ℝ × Euc (Fin n) → Euc (Fin n) := fun p => L (H p)
  have hK : ContinuousOn K (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := L.continuous.comp_continuousOn hH
  have hKz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, K p ≠ 0 := by
    intro p hp hz
    exact hHz p hp (L.injective (hz.trans (map_zero L).symm))
  let f : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (K (0,x))
  let g : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (K (1,x))
  have hU : ContinuousOn (fun p => unitRadial (K p)) (Set.Icc (0:ℝ) 1 ×ˢ annulus n) :=
    (unitRadial_continuousOn (S := {z | z ≠ 0}) (fun _ h => h)).comp hK hKz
  have hf : ContinuousOn f (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hg : ContinuousOn g (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn : ∀ x ∈ annulus n, ‖f x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hgn : ∀ x ∈ annulus n, ‖g x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfo : ∀ x ∈ annulus n, f (-x) = -f x := by
    intro x hx
    simp only [f,K,hHo x hx,map_neg,unitRadial_neg]
  have hgm : ∀ x ∈ annulus n, g x ≠ facetCenter n b := by
    intro x hx he
    have hnorm : L (unitRadial (H (1,x))) = unitRadial (K (1,x)) := by
      simp [unitRadial,K]
    apply hmiss x hx
    exact L.injective (hnorm.trans (he.trans hLy.symm))
  obtain ⟨δ₀,hδ₀,hdeg⟩ := eventually_odd_sphere_degree n hn f hf hfn hfo
  obtain ⟨δ₁,hδ₁,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl K hK hKz
  obtain ⟨δ₂,hδ₂,hzero⟩ := continuous_missed_facet_zero n n (by omega) hn b g hg hgn hgm
  have hnp : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hq : ((n:ℝ)-1)/n < 1 := by apply (div_lt_one hnp).mpr; linarith
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < min δ₀ (min δ₁ δ₂) / 2 by positivity) hq
  have hr0 : (((n:ℝ)-1)/n)^r * 2 < δ₀ := by
    have hh := min_le_left δ₀ (min δ₁ δ₂); linarith
  have hr1 : (((n:ℝ)-1)/n)^r * 2 < δ₁ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_left δ₁ δ₂); linarith
  have hr2 : (((n:ℝ)-1)/n)^r * 2 < δ₂ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_right δ₁ δ₂); linarith
  have he := hhom r hr1
  change approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) =
    approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) at he
  rw [hdeg r hr0] at he
  have hc := congrArg (fun c : Chain (cross n) => c ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩) he
  rw [crossFundamental_coeff n hn b,hzero r hr2] at hc
  exact one_ne_zero hc
end SimplicialChains
end
section
section
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains
section TraceHomotopy
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma Admissible.traceHomotopy_ray {f : Euc ν → ι → ℝ} (_hf : Admissible f)
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (G : ℝ × traceSphere ν → (Euc ι))
    (hG : ContinuousOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.univ))
    (hG0 : ∀ A : traceSphere ν, G (0,A) = WithLp.toLp 2 (signedExtension f A.val))
    (hGz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A : traceSphere ν, G (t,A) ≠ 0)
    {y : (Euc ι)} (hy : y ≠ 0) :
    ∃ A : traceSphere ν, ∃ t : ℝ, 0 < t ∧ G (1,A) = t • y := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let A : Euc (Fin n) → (SqMat ν) := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x : Euc (Fin n)) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x : Euc (Fin n)) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    have hx0 : x = 0 := eaL.symm.injective (h0.trans (map_zero _).symm)
    have hd := hx.1
    rw [hx0,norm_zero] at hd
    norm_num at hd
    exact hnz hd
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val)
      (fun x => hAz _ x.property)
  let H : ℝ × Euc (Fin n) → Euc (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then ebL (G (p.1,N ⟨p.2,hx⟩)) else 0
  have hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Set.Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hG.comp_continuous (continuous_subtype_val.fst.prodMk hcN)
      (fun p : S => ⟨p.property.1,Set.mem_univ _⟩)
    apply (ebL.continuous.comp hg).congr
    intro p
    change ebL (G (p.val.1,N ⟨p.val.2,p.property.2⟩)) = H p.val
    simp only [H,dif_pos p.property.2]
  have hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0 := by
    intro p hp hz
    have he : G (p.1,N ⟨p.2,hp.2⟩) = 0 := ebL.injective (by simpa only [H,dif_pos hp.2,map_zero] using hz)
    exact hGz _ hp.1 _ he
  have hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H,dif_pos hx,dif_pos hxn,hG0,N]
    have hAn : A (-x) = -A x := by simp only [A,map_neg]
    rw [hAn,traceRadial_neg,signedExtension_odd,WithLp.toLp_neg,map_neg]
  have hY : ‖ebL (unitRadial y)‖ = 1 := by rw [ebL.norm_map,unitRadial_norm hy]
  obtain ⟨x,hx,he⟩ := odd_homotopy_surjective n hn H hH hHz hHo hY
  let z : (Euc ι) := G (1,N ⟨x,hx⟩)
  have hz : z ≠ 0 := hGz _ ⟨zero_le_one,le_rfl⟩ _
  have he' : unitRadial z = unitRadial y := by
    apply ebL.injective
    have heL : ebL (unitRadial z) = unitRadial (ebL z) := by simp only [unitRadial,map_smul,ebL.norm_map]
    rw [heL]
    simpa only [H,dif_pos hx] using he
  refine ⟨N ⟨x,hx⟩,‖z‖ / ‖y‖,div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hy),?_⟩
  have hh := congrArg (fun v : (Euc ι) => ‖z‖ • v) he'
  simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul,
    ← div_eq_mul_inv] using hh
end TraceHomotopy
end
end
section
section
open Set
open scoped Topology
lemma compact_local_homotopy {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TopologicalSpace E] [Zero E]
    {U C : Set X} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (H : X → E) (hH : Continuous H) (hHz : ∀ x, H x ≠ 0)
    (K : ℝ × X → E) (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U))
    (hK0 : ∀ x ∈ U, K (0,x) = H x)
    (hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ≠ 0)
    (B : Set E) (houtside : ∀ x ∉ U, H x ∉ B)
    (hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ∈ B → x ∈ C)
    (hend : ∀ x ∈ U, K (1,x) ∉ B) :
    ∃ G : ℝ × X → E, ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) ∧
      (∀ x, G (0,x) = H x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, G (t,x) ≠ 0) ∧
      (∀ x, G (1,x) ∉ B) := by
  classical
  obtain ⟨q,hq1,-,hqs,hqb⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hC hU hCU
  let G : ℝ × X → E := fun p => if p.2 ∈ U then K (p.1 * q p.2,p.2) else H p.2
  have htm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : X) : t * q x ∈ Icc (0:ℝ) 1 :=
    ⟨mul_nonneg ht.1 (hqb x).1,
      (mul_le_mul_of_nonneg_right ht.2 (hqb x).1).trans (by simpa using (hqb x).2)⟩
  have hG : ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
    intro p hp
    by_cases hx : p.2 ∈ U
    · have hc : ContinuousOn (fun p : ℝ × X => K (p.1 * q p.2,p.2))
          (Icc (0:ℝ) 1 ×ˢ U) := hK.comp
        ((continuous_fst.mul (q.continuous.comp continuous_snd)).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨htm p.1 hp.1 p.2,hp.2⟩)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∈ U :=
        continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      have hset : Icc (0:ℝ) 1 ×ˢ U ∈ 𝓝[Icc (0:ℝ) 1 ×ˢ Set.univ] p := by
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,
          self_mem_nhdsWithin] with p' hu hi
        exact ⟨hi.1,hu⟩
      apply ((hc p ⟨hp.1,hx⟩).mono_of_mem_nhdsWithin hset).congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hu
        simp [G,hu]
      · simp [G,hx]
    · have hxq : p.2 ∉ tsupport q := fun h => hx (hqs h)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∉ tsupport q :=
        continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport q).isOpen_compl.mem_nhds hxq)
      apply (hH.comp continuous_snd).continuousAt.continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hq
        have hz : q p'.2 = 0 := image_eq_zero_of_notMem_tsupport hq
        by_cases hu : p'.2 ∈ U
        · simp [G,hu,hz,hK0 p'.2 hu]
        · simp [G,hu]
      · simp [G,hx]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ U
    · simp [G,hx,hK0 x hx]
    · simp [G,hx]
  · intro t ht x
    by_cases hx : x ∈ U
    · simpa only [G,if_pos hx] using hKz _ (htm t ht x) x hx
    · simpa only [G,if_neg hx] using hHz x
  · intro x hb
    by_cases hx : x ∈ U
    · have hh : K (q x,x) ∈ B := by simpa only [G,if_pos hx,one_mul] using hb
      have hc := hhits _ (hqb x) x hx hh
      rw [hq1 hc] at hh
      exact hend x hx hh
    · exact houtside x hx (by simpa only [G,if_neg hx] using hb)
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section ChartSurgery
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
lemma Admissible.chart_surgery_impossible {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    {I : Finset ι} (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc ν)} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    (c : κ → (Euc ν)) (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    {ε : ℝ} (hε : 0 < ε) (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, ∀ Q ∈ matrixFibre (c j), ∑ i, g j Q i = 1)
    (hge : ∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ < ε)
    (z : Euc ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i) (hzs : ∑ i, z i = 1)
    (hgm : ∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) : False := by
  classical
  let S : κ → Set (traceSphere ν) := fun j => {A | A.val ∈ purityChart f I w (c j)}
  let U : Set (traceSphere ν) := ⋃ j, S j
  let C : Set (traceSphere ν) := {A | ∃ p : levelFibre f w r, balancedModel p = A ∧
    ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z}
  let K : ℝ × traceSphere ν → (Euc ι) := finiteOpenGlue (fun j => {p | p.2 ∈ S j})
    (fun j p => mixedHomotopy f I w (c j) (g j) p.1 p.2.val)
  let H : traceSphere ν → (Euc ι) := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let y : (Euc ι) := blockVector I (1/2:ℝ) r (1/2:ℝ) z
  let B : Set (Euc ι) := {v | ∃ d : ℝ, 0 < d ∧ v = d • y}
  have hSo : ∀ j, IsOpen (S j) := fun j =>
    hf.purityChart_isOpen I w (c j) Subtype.val continuous_subtype_val (fun A => A.property.1)
  have hSd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun A hA hB => Set.disjoint_left.mp (hd hij) hA.2.2.2.2.2 hB.2.2.2.2.2)
  have hKd : Pairwise (fun i j => Disjoint {p : ℝ × traceSphere ν | p.2 ∈ S i}
      {p : ℝ × traceSphere ν | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p ha hb => Set.disjoint_left.mp (hSd hij) ha hb)
  have hKe (j : κ) (A : traceSphere ν) (hA : A ∈ S j) (t : ℝ) :
      K (t,A) = mixedHomotopy f I w (c j) (g j) t A.val :=
    finiteOpenGlue_eq hKd _ hA
  have hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U) :=
    finiteOpenGlue_continuousOn_prod hSo hSd _
      (fun j => hf.mixedHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j))
  have hC : IsCompact C := hf.level_hits_compact hI c hc hcn hd hcover g hg z
  have hCU : C ⊆ U := by
    rintro A ⟨p,rfl,t,ht,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover p.property.1)
    have hF : fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 = z :=
      (levelHomotopy_eq hd g hj t).symm.trans he
    have hunit : IsUnit (rankOne p.val.1 + p.val.2) := by
      by_contra hnu
      exact hf.fibreHomotopy_boundary_misses hI (hc j) (hcn j) p.property.1.1
        (interior_subset hj) (g j) hε (hge j) z hz ht p.property.2 hnu hF
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    exact balancedFibre_chart p.property.1.1 (hf.orientedLevel_inner_pos hI hw hwi hr p.property.1)
      (orientedLevel_cone hr p.property.1) hj p.property.2 hunit
  have hH : Continuous H := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hHz : ∀ A : traceSphere ν, H A ≠ 0 := by
    intro A h
    have hzero : signedExtension f A.val = 0 := WithLp.toLp_injective 2 h
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp hzero)
  have hK0 : ∀ A ∈ U, K (0,A) = H A := by
    intro A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj 0]
    exact hf.mixedHomotopy_zero hmax (g j) A.property.1 hj
  have hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ≠ 0 := by
    intro t ht A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj t]
    exact hf.mixedHomotopy_nonzero hI (g j) t hj
  have houtside : ∀ A ∉ U, H A ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨hunit,hline,hAw,hm,hlevel⟩ := hf.original_ray_level hI hmax hw hwi hr hro hrs
      (fun i => hε.trans (hz i)) hzs A.property hdp he
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hlevel)
    exact hAU (mem_iUnion.mpr ⟨j,hunit,hline,hAw,hm,orientedLevel_cone hr hlevel,hj⟩)
  have hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ∈ B → A ∈ C := by
    rintro t ht A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj t] at he
    obtain ⟨hl,hF,hA⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ht hdp A.property hj he
    let p : levelFibre f w r := ⟨(lineRepresentative w A.val,negativeFibre A.val),hl,purityChart_fibre hj⟩
    refine ⟨p,Subtype.ext hA.symm,t,ht,?_⟩
    exact (levelHomotopy_eq hd g hj.2.2.2.2.2 t).trans hF
  have hend : ∀ A ∈ U, K (1,A) ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj 1] at he
    obtain ⟨-,hF,-⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ⟨zero_le_one,le_rfl⟩ hdp A.property hj he
    rw [fibreHomotopy_one f I (hcn j) (purityChart_unit hj) (g j) (purityChart_fibre hj)] at hF
    exact hgm j _ (centeredFibre_mem (hcn j) (purityChart_unit hj) (purityChart_fibre hj)) hF
  let : CompactSpace (traceSphere ν) := isCompact_iff_compactSpace.mp traceSphere_compact
  obtain ⟨G,hG,hG0,hGz,hGm⟩ := compact_local_homotopy (isOpen_iUnion hSo) hC hCU H hH hHz
    K hK hK0 hKz B houtside hhits hend
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) hr z
  obtain ⟨A,d,hd,he⟩ := hf.traceHomotopy_ray hdim hn G hG hG0 hGz hy
  exact hGm A ⟨d,hd,he⟩
end ChartSurgery
end
end
section
section
open scoped RealInnerProductSpace
section DisjointChambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma compact_disjoint_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧
      (Pairwise (fun c d : ↥C => Disjoint (interior (signChamber Z c.val))
        (interior (signChamber Z d.val)))) ∧
      K ⊆ ⋃ c : ↥C, interior (signChamber Z c.val) := by
  classical
  obtain ⟨C,hCK,hcover⟩ := compact_finite_chambers hK hsub
  let g : E → Set E := fun c => interior (signChamber Z c)
  have hsurj : (↑C : Set E).SurjOn g (↑(C.image g) : Set (Set E)) := by
    intro U hU
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hU
    exact ⟨c,hc,rfl⟩
  obtain ⟨D,hDC,hDinj,hDimage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑C : Set E) (C.image g) hsurj
  refine ⟨D,fun c hc => hCK (hDC hc),?_,?_⟩
  · intro c d hne
    rcases signChamber_eq_or_disjoint Z c.val d.val with he | hdj
    · exfalso
      exact hne (Subtype.ext (hDinj c.property d.property (congrArg interior he)))
    · exact hdj.mono interior_subset interior_subset
  · intro x hx
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hg : g c ∈ D.image g := by rw [hDimage]; exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
    obtain ⟨d,hd,hgd⟩ := Finset.mem_image.mp hg
    exact Set.mem_iUnion.mpr ⟨⟨d,hd⟩,by change x ∈ g d; rw [hgd]; exact hxc⟩
end DisjointChambers
end
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixEmbedding
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
lemma toEuclideanLin_mul {α β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    Matrix.toEuclideanLin (A*B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((A*B)*ᵥ v) i = (A *ᵥ (B *ᵥ v)) i
  rw [Matrix.mulVec_mulVec]
noncomputable def isometryMatrix (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : Matrix ν μ ℝ :=
  Matrix.toEuclideanLin.symm e.toLinearMap
omit [DecidableEq ν] in
lemma isometryMatrix_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (x : (Euc μ)) :
    Matrix.toEuclideanLin (isometryMatrix e) x = e x :=
  LinearMap.congr_fun (Matrix.toEuclideanLin.apply_symm_apply e.toLinearMap) x
lemma isometryMatrix_star_mul (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) :
    (isometryMatrix e)ᴴ * isometryMatrix e = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have he : Matrix.toEuclideanLin (isometryMatrix e) = e.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [he]
  rw [e.adjoint_comp_self']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.id_apply,Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
noncomputable def matrixEmbed (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : SqMat μ →ₗ[ℝ] SqMat ν where
  toFun B := isometryMatrix e * B * (isometryMatrix e)ᴴ
  map_add' B C := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t B := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl
omit [DecidableEq ν] in
lemma matrixEmbed_nonneg (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {B : SqMat μ} (hB : 0 ≤ B) :
    0 ≤ matrixEmbed e B := ((Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same _).nonneg
lemma matrixEmbed_trace (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) :
    Matrix.trace (matrixEmbed e B) = Matrix.trace B := by
  change Matrix.trace (isometryMatrix e * B * (isometryMatrix e)ᴴ) = Matrix.trace B
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,isometryMatrix_star_mul,Matrix.one_mul]
lemma matrixEmbed_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) (x : (Euc μ)) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) (e x) =
      e (Matrix.toEuclideanCLM (n := μ) (𝕜 := ℝ) B x) := by
  change Matrix.toEuclideanLin (matrixEmbed e B) (e x) = e (Matrix.toEuclideanLin B x)
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) (e x) = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)
    (Matrix.toEuclideanLin B (Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x))) = _
  have hh : Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
    rw [← isometryMatrix_action e x]
    change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
      (Matrix.toEuclideanLin (isometryMatrix e))) x = x
    rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
    simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
  rw [hh,isometryMatrix_action]
lemma matrixEmbed_kernel (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) {u : (Euc ν)}
    (hu : ∀ x : (Euc μ), ⟪u,e x⟫ = 0) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) u = 0 := by
  have hz : Matrix.toEuclideanLin (isometryMatrix e)ᴴ u = 0 := by
    apply ext_inner_left ℝ
    intro x
    rw [inner_zero_right,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint u⟫ = 0
    rw [LinearMap.adjoint_inner_right,isometryMatrix_action,real_inner_comm]
    exact hu x
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) u = 0
  rw [toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e * B) (Matrix.toEuclideanLin (isometryMatrix e)ᴴ u) = 0
  rw [hz,map_zero]
end MatrixEmbedding
end
end
section
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixCompression
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
noncomputable def matrixCompress (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : SqMat ν →ₗ[ℝ] SqMat μ where
  toFun Q := (isometryMatrix e)ᴴ * Q * isometryMatrix e
  map_add' Q R := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t Q := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl
omit [DecidableEq ν] in
lemma matrixCompress_nonneg (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {Q : SqMat ν} (hQ : 0 ≤ Q) :
    0 ≤ matrixCompress e Q :=
  ((Matrix.nonneg_iff_posSemidef.mp hQ).conjTranspose_mul_mul_same _).nonneg
lemma isometryMatrix_adjoint_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (x : (Euc μ)) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
  rw [← isometryMatrix_action e x]
  change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
    (Matrix.toEuclideanLin (isometryMatrix e))) x = x
  rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
  simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
lemma matrixEmbed_compress (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {Q : SqMat ν}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    matrixEmbed e (matrixCompress e Q) = Q := by
  let T := isometryMatrix e
  have hleft : (T * Tᴴ) * Q = Q := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx⟩ := hR (LinearMap.mem_range_self (Matrix.toEuclideanLin Q) v)
    change e x = Matrix.toEuclideanLin Q v at hx
    rw [toEuclideanLin_mul,toEuclideanLin_mul]
    change Matrix.toEuclideanLin T (Matrix.toEuclideanLin Tᴴ (Matrix.toEuclideanLin Q v)) = _
    rw [← hx,isometryMatrix_adjoint_action,isometryMatrix_action]
  have hright : Q * (T*Tᴴ) = Q := by
    have he := congrArg Matrix.conjTranspose hleft
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at he
    simpa only [← Matrix.star_eq_conjTranspose,hQ.star_eq] using he
  change T * (Tᴴ * Q * T) * Tᴴ = Q
  calc
    _ = ((T*Tᴴ)*Q)*(T*Tᴴ) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hleft,hright]
lemma matrixCompress_trace (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {Q : SqMat ν}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    Matrix.trace (matrixCompress e Q) = Matrix.trace Q := by
  rw [← matrixEmbed_trace e,matrixEmbed_compress e hQ hR]
end MatrixCompression
end
end
section
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SymmetricEntries
variable {ν : Type*} [Fintype ν] [LinearOrder ν]
noncomputable def symmetricEntries : SqMat ν →ₗ[ℝ] Euc (UpperTriangle ν) where
  toFun Q := WithLp.toLp 2 (fun p => Q p.val.1 p.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [Fintype ν] in
lemma symmetricCoordinates_entries {Q : SqMat ν} (hQ : IsSelfAdjoint Q) :
    symmetricCoordinates (symmetricEntries Q) = Q := by
  ext i j
  change (if h : i ≤ j then Q i j else Q j i) = Q i j
  split_ifs with h
  · rfl
  · have he := congrArg (fun B : SqMat ν => B i j) hQ.star_eq
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial] using he
end SymmetricEntries
end
section
open scoped RealInnerProductSpace
lemma orthogonal_frame (k : ℕ) {u : Euc (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : Euc (Fin k) →ₗᵢ[ℝ] Euc (Fin (k+1)),
      (∀ x, ⟪u,e x⟫ = 0) ∧
      (∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (Euc (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_,?_⟩
  · intro x
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)
  · intro v hv
    have hvW : v ∈ W := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
    refine ⟨b.repr ⟨v,hvW⟩,?_⟩
    change (b.repr.symm (b.repr ⟨v,hvW⟩)).val = v
    rw [LinearIsometryEquiv.symm_apply_apply]
end
end
section
section
open scoped BigOperators
noncomputable def coordinateSum {ι : Type*} [Fintype ι] : Euc ι →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, x i
      map_add' := by intro x y; simp only [PiLp.add_apply,Finset.sum_add_distrib]
      map_smul' := by intro t x; simp only [PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply] }
lemma coordinateSum_apply {ι : Type*} [Fintype ι] (x : Euc ι) :
    coordinateSum x = ∑ i, x i := rfl
noncomputable def uniformVector (ι : Type*) [Fintype ι] : Euc ι :=
  WithLp.toLp 2 (fun _ => (Fintype.card ι : ℝ)⁻¹)
lemma coordinateSum_uniform (ι : Type*) [Fintype ι] [Nonempty ι] :
    coordinateSum (uniformVector ι) = 1 := by
  simp only [coordinateSum_apply,uniformVector,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos)))
noncomputable def zeroSumProjection (ι : Type*) [Fintype ι] :
    Euc ι →L[ℝ] Euc ι :=
  ContinuousLinearMap.id ℝ _ - coordinateSum.smulRight (uniformVector ι)
noncomputable def simplexProjection {ι : Type*} [Fintype ι] (x : Euc ι) :=
  zeroSumProjection ι x + uniformVector ι
lemma simplexProjection_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : Euc ι) :
    coordinateSum (simplexProjection x) = 1 := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,map_add,map_sub,map_smul,coordinateSum_uniform,
    smul_eq_mul,mul_one,sub_self,zero_add]
lemma simplexProjection_fixed {ι : Type*} [Fintype ι] {x : Euc ι}
    (hx : coordinateSum x = 1) : simplexProjection x = x := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,hx,one_smul,sub_add_cancel]
lemma simplexProjection_sub_fixed {ι : Type*} [Fintype ι] {x y : Euc ι}
    (hy : coordinateSum y = 1) : simplexProjection x - y = zeroSumProjection ι (x-y) := by
  rw [map_sub]
  have hy' := simplexProjection_fixed hy
  change zeroSumProjection ι y + uniformVector ι = y at hy'
  change (zeroSumProjection ι x + uniformVector ι) - y = _
  calc
    _ = (zeroSumProjection ι x + uniformVector ι) -
      (zeroSumProjection ι y + uniformVector ι) := by rw [hy']
    _ = _ := by abel
lemma continuous_simplex_approx {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Fintype ι] [Nonempty ι]
    (g : D → Euc ι) (hg : Continuous g)
    {K : Set D} (hK : ∀ x ∈ K, coordinateSum (g x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D → Euc ι, ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, coordinateSum (a x) = 1) ∧ (∀ x ∈ K, ‖a x - g x‖ < ε) := by
  have hp := norm_nonneg (zeroSumProjection ι)
  have hδ : 0 < ε / (‖zeroSumProjection ι‖ + 1) := div_pos hε (by positivity)
  obtain ⟨b,hb,hbg,-⟩ := hg.exists_contDiff_approx (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : D => ε / (‖zeroSumProjection ι‖ + 1))) (fun _ => hδ)
  let a := fun x => simplexProjection (b x)
  refine ⟨a,?_,fun x => simplexProjection_sum (b x),?_⟩
  · exact ((zeroSumProjection ι).contDiff.comp hb).add contDiff_const
  · intro x hx
    change ‖simplexProjection (b x) - g x‖ < ε
    rw [simplexProjection_sub_fixed (hK x hx)]
    have hd : ‖b x - g x‖ < ε / (‖zeroSumProjection ι‖ + 1) := by
      simpa only [dist_eq_norm] using hbg x
    calc
      _ ≤ ‖zeroSumProjection ι‖ * ‖b x - g x‖ := (zeroSumProjection ι).le_opNorm _
      _ ≤ ‖zeroSumProjection ι‖ * (ε / (‖zeroSumProjection ι‖ + 1)) := mul_le_mul_of_nonneg_left hd.le hp
      _ < ε := by
        have he : (‖zeroSumProjection ι‖+1) * (ε / (‖zeroSumProjection ι‖+1)) = ε :=
          mul_div_cancel₀ ε (by positivity)
        nlinarith
end
end
section
section
open Set MeasureTheory
open scoped Topology
section NullImage
variable {D T : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
lemma differentiable_image_null_of_projection (μ : Measure T) [μ.IsAddHaarMeasure]
    (p : T →L[ℝ] D) (hp : Function.Surjective p) (hpn : ¬ Function.Injective p)
    {f : D → T} {S : Set D} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) : μ (f '' S) = 0 := by
  let g : T → T := fun x => f (p x)
  let g' : T → T →L[ℝ] T := fun x => (fderiv ℝ f (p x)).comp p
  have hd : ∀ x ∈ p ⁻¹' S, HasFDerivWithinAt g (g' x) (p ⁻¹' S) x := by
    intro x hx
    exact ((hf (p x) hx).hasFDerivAt.comp x p.hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ x ∈ p ⁻¹' S, (g' x).det = 0 := by
    intro x _
    change ((g' x).toLinearMap).det = 0
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    apply mt LinearMap.ker_eq_bot.mp
    intro hinj
    exact hpn (fun u v huv => hinj (by change fderiv ℝ f (p x) (p u) = fderiv ℝ f (p x) (p v); rw [huv]))
  have he : g '' (p ⁻¹' S) = f '' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨z,rfl⟩ := hp x
      exact ⟨z,hx,rfl⟩
  rw [← he]
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd hdet
end NullImage
noncomputable def initialProjection (n m : ℕ) (h : n ≤ m) :
    Euc (Fin m) →L[ℝ] Euc (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Fin.castLE h i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
lemma initialProjection_surjective (n m : ℕ) (h : n ≤ m) :
    Function.Surjective (initialProjection n m h) := by
  intro x
  refine ⟨WithLp.toLp 2 (fun j : Fin m => if h : j.val < n then x ⟨j.val,h⟩ else 0),?_⟩
  apply PiLp.ext
  intro i
  change (if hj : i.val < n then x ⟨i.val,hj⟩ else 0) = x i
  simp only [dif_pos i.isLt]
lemma initialProjection_not_injective (n m : ℕ) (h : n < m) :
    ¬ Function.Injective (initialProjection n m h.le) := by
  intro hh
  have hl := LinearMap.finrank_le_finrank_of_injective
    (f := (initialProjection n m h.le).toLinearMap) hh
  simp only [finrank_euclideanSpace_fin] at hl
  omega
lemma differentiable_image_null_of_dim_lt (n m : ℕ) (h : n < m)
    {f : Euc (Fin n) → Euc (Fin m)}
    {S : Set (Euc (Fin n))} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    volume (f '' S) = 0 :=
  differentiable_image_null_of_projection volume (initialProjection n m h.le)
    (initialProjection_surjective n m h.le) (initialProjection_not_injective n m h) hf
end
end
section
section
open scoped BigOperators
open MeasureTheory Set
lemma finite_smooth_slice_misses (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → Euc (Fin n) →L[ℝ] ℝ)
    (g : κ → Euc (Fin n) → Euc (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c))
    {V : Set (Euc (Fin m))} (hVo : IsOpen V) (hVn : V.Nonempty)
    (hVp : ∀ y ∈ V, ∀ i, 0 < y i) :
    ∃ z : Euc (Fin m), (∃ y ∈ V, z = (∑ i, y i)⁻¹ • y) ∧
      (∀ i, 0 < z i) ∧ (∑ i, z i) = 1 ∧
      ∀ c x, L c x = 1 → g c x ≠ z := by
  classical
  let C (c : κ) (x : Euc (Fin n)) := L c x • g c ((L c x)⁻¹ • x)
  have hCd (c : κ) : ∀ x ∈ {x | L c x ≠ 0}, DifferentiableAt ℝ (C c) x := by
    intro x hx
    exact (L c).differentiableAt.smul
      (((hg c).differentiable (by simp)).differentiableAt.comp x
        (((L c).differentiableAt.inv hx).smul differentiableAt_id))
  have hnull : volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) = 0 := by
    exact measure_iUnion_null (fun c => differentiable_image_null_of_dim_lt n m hnm (hCd c))
  obtain ⟨y,hy,hym⟩ : ∃ y ∈ V, y ∉ ⋃ c : κ, C c '' {x | L c x ≠ 0} := by
    by_contra hn
    push Not at hn
    have hl : volume V ≤ volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) := measure_mono hn
    rw [hnull] at hl
    exact hVo.measure_ne_zero volume hVn (le_antisymm hl (zero_le))
  let s : ℝ := ∑ i, y i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hVp y hy i)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,by omega⟩⟩)
  let z : Euc (Fin m) := s⁻¹ • y
  refine ⟨z,⟨y,hy,rfl⟩,fun i => ?_,?_,?_⟩
  · change 0 < s⁻¹ * y i
    exact mul_pos (inv_pos.mpr hs) (hVp y hy i)
  · change (∑ i, s⁻¹ * y i) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hs)
  · intro c x hx he
    apply hym
    apply Set.mem_iUnion.mpr
    refine ⟨c,s • x,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,map_smul,hx,smul_eq_mul,mul_one]
      exact ne_of_gt hs
    · simp only [C,map_smul,hx,smul_eq_mul,mul_one,inv_smul_smul₀ (ne_of_gt hs),he,z,
        smul_inv_smul₀ (ne_of_gt hs)]
end
end
section
section
open scoped BigOperators
lemma finite_smooth_slice_misses_bounded (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → Euc (Fin n) →L[ℝ] ℝ)
    (g : κ → Euc (Fin n) → Euc (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : Euc (Fin m), (∀ i, (2*(m:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  have hm : 0 < m := by omega
  let V : Set (Euc (Fin m)) := {y | ∀ i, 1 < y i ∧ y i < 2}
  have hVo : IsOpen V := by
    have he : V = ⋂ i, {y : Euc (Fin m) | 1 < y i ∧ y i < 2} := by
      ext y; simp [V]
    rw [he]
    exact isOpen_iInter_of_finite (fun i => (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i) continuous_const))
  have hVn : V.Nonempty := ⟨WithLp.toLp 2 (fun _ => (3/2:ℝ)),fun _ => by norm_num⟩
  obtain ⟨z,⟨y,hy,hz⟩,hp,hs,hmiss⟩ := finite_smooth_slice_misses n m hnm L g hg
    hVo hVn (fun y hy i => lt_trans zero_lt_one (hy i).1)
  have hmm : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => by linarith [(hy i).1])
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩)
  have hbound : ∑ i, y i < 2*(m:ℝ) := by
    have hh := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩) (fun i _ => (hy i).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  refine ⟨z,?_,hs,hmiss⟩
  intro i
  rw [hz]
  change (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ * y i
  have hinv : (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ := by
    exact (inv_lt_inv₀ (by positivity) hsum).mpr hbound
  exact hinv.trans (by nlinarith [(hy i).1,inv_pos.mpr hsum])
lemma finite_smooth_slice_misses_general {D ι κ : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [Fintype ι] [Fintype κ]
    (hd : Module.finrank ℝ D < Fintype.card ι)
    (L : κ → D →L[ℝ] ℝ) (g : κ → D → Euc ι)
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : Euc ι, (∀ i, (2*(Fintype.card ι:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  let eD := (stdOrthonormalBasis ℝ D).repr
  let eY := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let L' := fun c => (L c).comp eD.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g' := fun c x => eY (g c (eD.symm x))
  have hg' (c : κ) : ContDiff ℝ (⊤ : ℕ∞) (g' c) :=
    eY.toContinuousLinearEquiv.contDiff.comp ((hg c).comp eD.symm.toContinuousLinearEquiv.contDiff)
  obtain ⟨z,hp,hs,hm⟩ := finite_smooth_slice_misses_bounded _ _ hd L' g' hg'
  have heY (q : Euc (Fin (Fintype.card ι))) (i : ι) :
      (eY.symm q) i = q ((Fintype.equivFin ι) i) := by
    simp [eY, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  refine ⟨eY.symm z,?_,?_,?_⟩
  · intro i
    rw [heY]
    exact hp ((Fintype.equivFin ι) i)
  · simp only [heY]
    rw [Equiv.sum_comp]
    exact hs
  · intro c x hx he
    apply hm c (eD x)
    · simpa only [L',ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply] using hx
    · change eY (g c (eD.symm (eD x))) = z
      rw [LinearIsometryEquiv.symm_apply_apply,he,LinearIsometryEquiv.apply_symm_apply]
end
end
section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section CenterApproximation
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma matrixFibre_range {u : (Euc (Fin (k+1)))} (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : (SqMat (Fin (k+1)))} (hQ : Q ∈ matrixFibre u) :
    LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap := by
  rintro v ⟨b,rfl⟩
  obtain ⟨x,hx⟩ := he ((matrixOp (Fin (k+1))) Q b) (matrix_image_orthogonal_kernel hQ.1.isSelfAdjoint hQ.2.2 b)
  exact ⟨x,hx⟩
lemma matrixCompress_mem_slice {u : (Euc (Fin (k+1)))} (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : (SqMat (Fin (k+1)))} (hQ : Q ∈ matrixFibre u) :
    0 ≤ matrixCompress e Q ∧ Matrix.trace (matrixCompress e Q) = 1 :=
  ⟨matrixCompress_nonneg e hQ.1,
    (matrixCompress_trace e hQ.1.isSelfAdjoint (matrixFibre_range e he hQ)).trans hQ.2.1⟩
lemma Admissible.center_approximation {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)] {c : (Euc (Fin (k+1)))}
    (hc : c ∈ safeNormals (activeVectors f I)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    (he : ∀ x, ⟪c,e x⟫ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : (Euc (UpperTriangle (Fin k))) → Euc ↥(Iᶜ : Finset ι), ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, ∑ i, a x i = 1) ∧
      ∀ x, 0 ≤ symmetricCoordinates x → Matrix.trace (symmetricCoordinates x) = 1 →
        ‖a x - negativeCoordinates f I (matrixEmbed e (symmetricCoordinates x))‖ < ε := by
  let g : (Euc (UpperTriangle (Fin k))) → Euc ↥(Iᶜ : Finset ι) :=
    fun x => negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺))
  have hP : Continuous (fun x : (Euc (UpperTriangle (Fin k))) => (symmetricCoordinates x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous symmetricCoordinates.continuous_of_finiteDimensional
      (fun x => symmetricCoordinates_selfAdjoint x)
  have hg : Continuous g :=
    (hf.negativeCoordinates_continuousOn I).comp_continuous
      ((matrixEmbed e).continuous_of_finiteDimensional.comp hP)
      (fun x => matrixEmbed_nonneg e (CFC.posPart_nonneg _))
  let K : Set (Euc (UpperTriangle (Fin k))) := {x | 0 ≤ symmetricCoordinates x ∧ Matrix.trace (symmetricCoordinates x) = 1}
  have hs : ∀ x ∈ K, coordinateSum (g x) = 1 := by
    intro x hx
    change ∑ i, negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺)) i = 1
    rw [(CFC.posPart_eq_self _).mpr hx.1]
    apply hf.negativeCoordinates_sum hc
    exact ⟨matrixEmbed_nonneg _ hx.1,(matrixEmbed_trace _ _).trans hx.2,matrixEmbed_kernel e _ he⟩
  obtain ⟨a,ha,has,hae⟩ := continuous_simplex_approx g hg hs hε
  refine ⟨a,ha,has,?_⟩
  intro x hx ht
  have hh := hae x ⟨hx,ht⟩
  simpa only [g,(CFC.posPart_eq_self _).mpr hx] using hh
lemma Admissible.finite_center_approximations {κ : Type*} [Fintype κ]
    {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hd : Fintype.card (UpperTriangle (Fin k)) < Fintype.card ↥(Iᶜ : Finset ι))
    (c : κ → (Euc (Fin (k+1)))) (hc : ∀ j, c j ∈ safeNormals (activeVectors f I)) (hcn : ∀ j, ‖c j‖ = 1) :
    ∃ z : Euc ↥(Iᶜ : Finset ι), (∀ i, (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧
      ∃ g : κ → (SqMat (Fin (k+1))) → Euc ↥(Iᶜ : Finset ι), (∀ j, Continuous (g j)) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), (∑ i, g j Q i) = 1) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ <
          (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) := by
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  let ε : ℝ := (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose e he hes using (fun j => orthogonal_frame k (hcn j))
  choose a ha has hae using (fun j => hf.center_approximation (hc j) (e j) (he j) hε)
  let L : (Euc (UpperTriangle (Fin k))) →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin k) ℝ ℝ).toContinuousLinearMap.comp
    (symmetricCoordinates (ν := Fin k)).toContinuousLinearMap
  have hendim : Module.finrank ℝ (Euc (UpperTriangle (Fin k))) < Fintype.card ↥(Iᶜ : Finset ι) := by simpa using hd
  obtain ⟨z,hzp,hzs,hzm⟩ := finite_smooth_slice_misses_general hendim (fun _ : κ => L) a ha
  let g : κ → (SqMat (Fin (k+1))) → Euc ↥(Iᶜ : Finset ι) :=
    fun j Q => a j (symmetricEntries (matrixCompress (e j) Q))
  refine ⟨z,hzp,hzs,g,?_,?_,?_,?_⟩
  · intro j
    exact (ha j).continuous.comp (symmetricEntries.continuous_of_finiteDimensional.comp
      (matrixCompress (e j)).continuous_of_finiteDimensional)
  · intro j Q hQ
    exact has j _
  · intro j Q hQ
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    have hSC := symmetricCoordinates_entries hCQ.1.isSelfAdjoint
    have hEQ := matrixEmbed_compress (e j) hQ.1.isSelfAdjoint (matrixFibre_range (e j) (hes j) hQ)
    have hh := hae j (symmetricEntries (matrixCompress (e j) Q))
      (by rw [hSC]; exact hCQ.1) (by rw [hSC]; exact hCQ.2)
    simpa only [hSC,hEQ,g,ε] using hh
  · intro j Q hQ
    apply hzm j _
    change Matrix.trace (symmetricCoordinates (symmetricEntries (matrixCompress (e j) Q))) = 1
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    rw [symmetricCoordinates_entries hCQ.1.isSelfAdjoint]
    exact hCQ.2
end CenterApproximation
end
end
section
section
open scoped RealInnerProductSpace
open Set
section Purity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.maximal_support_complement_bound {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) :
    Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) ≤ Fintype.card (UpperTriangle (Fin k)) := by
  classical
  by_contra hb
  have hd : Fintype.card (UpperTriangle (Fin k)) <
      Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) := lt_of_not_ge hb
  let I := positiveSupport f w
  have hI : I.Nonempty := hf.support_nonempty hw
  have hr : ∀ i ∈ I, 0 < f w i := fun i hi => (mem_positiveSupport f w i).mp hi
  have hro : ∀ i ∉ I, f w i = 0 := by
    intro i hi
    exact le_antisymm (not_lt.mp (fun hp => hi ((mem_positiveSupport f w i).mpr hp))) (hf.nonneg w hw i)
  obtain ⟨C,hCK,hCD,hcover⟩ := compact_disjoint_chambers (hf.orientedLevel_compact w (f w))
    (fun u hu => hf.commonPositiveCone_interior_safe I (orientedLevel_cone hr hu))
  let c : ↥C → (Euc (Fin (k+1))) := Subtype.val
  have hc : ∀ j, c j ∈ commonPositiveCone f I := fun j => orientedLevel_cone hr (hCK j.property)
  have hcn : ∀ j, ‖c j‖ = 1 := fun j => (hCK j.property).1
  obtain ⟨z,hz,hzs,g,hg,hgs,hge,hgm⟩ := hf.finite_center_approximations hd c
    (fun j => hf.commonPositiveCone_safe I (hc j)) hcn
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  have hε : 0 < (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ := by positivity
  exact hf.chart_surgery_impossible hdim hn hI hmax hw hr hr hro (hf.sum_one w hw)
    c hc hcn hCD hcover hε g hg hgs hge z hz hzs hgm
end Purity
end
section
open scoped RealInnerProductSpace
section PureFacets
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
omit [InnerProductSpace ℝ E] [DecidableEq ι] in
lemma exists_maximal_support (f : E → ι → ℝ) {w : E} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧
      ∀ v, ‖v‖ = 1 → positiveSupport f u ⊆ positiveSupport f v →
        positiveSupport f v = positiveSupport f u := by
  classical
  let S : Set (Finset ι) := {s | ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ s ∧ positiveSupport f u = s}
  obtain ⟨s,hs,hm⟩ := (Set.toFinite S).exists_maximal (show S.Nonempty from ⟨_,w,hw,Finset.Subset.rfl,rfl⟩)
  obtain ⟨u,hu,hwu,rfl⟩ := hs
  refine ⟨u,hu,hwu,?_⟩
  intro v hv huv
  exact le_antisymm (hm ⟨v,hv,hwu.trans huv,rfl⟩ huv) huv
end PureFacets
lemma Admissible.maximal_support_card_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {w : Vector4} (hw : ‖w‖ = 1)
    (hm : ∀ u, ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) : (positiveSupport f w).card = 4 := by
  have hl := hf.support_card_four_le hw
  have hb := hf.maximal_support_complement_bound (k := 3) (by decide) (by decide) hw hm
  have hc : Fintype.card (UpperTriangle (Fin 3)) = 6 := by decide
  rw [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hc] at hb
  omega
lemma Admissible.support_extends_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {w : Vector4} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 4 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  exact ⟨u,hu,hwu,hf.maximal_support_card_four hu hm⟩
end
open Set MeasureTheory
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
open SimplicialChains
section HemisphereChart
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (w : E) (e : W →ₗᵢ[ℝ] E)
noncomputable def hemisphereChart (v : W) : E := unitRadial (w + e v)
noncomputable def hemisphereInverse (u : E) : W := ⟪w,u⟫⁻¹ • e.toContinuousLinearMap.adjoint u
lemma adjoint_isometry_apply (v : W) : e.toContinuousLinearMap.adjoint (e v) = v := by
  have hh := congrArg (fun T : W →L[ℝ] W => T v) e.adjoint_comp_self
  exact hh
lemma adjoint_normal (he : ∀ v, ⟪w,e v⟫ = 0) : e.toContinuousLinearMap.adjoint w = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_zero_left,ContinuousLinearMap.adjoint_inner_left]
  exact he v
lemma frame_decomposition (hw : ‖w‖ = 1)
    (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (u : E) :
    e (e.toContinuousLinearMap.adjoint u) = u - ⟪w,u⟫ • w := by
  obtain ⟨v,hv⟩ := hes (u - ⟪w,u⟫ • w) (by simp [inner_sub_right,inner_smul_right,hw])
  have ha := congrArg e.toContinuousLinearMap.adjoint hv
  rw [adjoint_isometry_apply,map_sub,map_smul,adjoint_normal w e he,smul_zero,sub_zero] at ha
  rw [← ha,hv]
omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphere_add_ne_zero (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    w + e v ≠ 0 := by
  intro hz
  have h := congrArg (fun u => ⟪w,u⟫) hz
  simp [inner_add_right,he,hw] at h
omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_contDiff (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (hemisphereChart w e) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun v => w + e v) := contDiff_const.add e.contDiff
  exact (hc.norm ℝ (hemisphere_add_ne_zero w e hw he)).inv
    (fun v => norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)) |>.smul hc
omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_norm (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    ‖hemisphereChart w e v‖ = 1 := unitRadial_norm (hemisphere_add_ne_zero w e hw he v)
lemma hemisphereInverse_chart (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    hemisphereInverse w e (hemisphereChart w e v) = v := by
  have hn : ‖w + e v‖ ≠ 0 := norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)
  simp only [hemisphereInverse,hemisphereChart,unitRadial,inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq,hw,one_pow,he,add_zero,mul_one,inv_inv,map_smul,map_add,
    adjoint_normal w e he,adjoint_isometry_apply,zero_add,smul_smul,mul_inv_cancel₀ hn,one_smul]
lemma hemisphereChart_inverse (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {u : E} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫) :
    hemisphereChart w e (hemisphereInverse w e u) = u := by
  have heq : w + e (hemisphereInverse w e u) = ⟪w,u⟫⁻¹ • u := by
    rw [hemisphereInverse,map_smul,frame_decomposition w e hw he hes,smul_sub,smul_smul,
      inv_mul_cancel₀ (ne_of_gt hwu),one_smul]
    abel
  rw [hemisphereChart,heq,unitRadial,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hwu),hu,mul_one,inv_inv,smul_smul,
    mul_inv_cancel₀ (ne_of_gt hwu),one_smul]
lemma hemisphereInverse_continuousOn :
    ContinuousOn (hemisphereInverse w e) {u | 0 < ⟪w,u⟫} :=
  ((continuous_const.inner continuous_id).continuousOn.inv₀ (fun _ h => ne_of_gt h)).smul
    e.toContinuousLinearMap.adjoint.continuous.continuousOn
end HemisphereChart
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace Topology
open Filter Set
section NegativeQuadratic
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
def NegativeQuadratic (B : E →L[ℝ] E) : Prop := ∀ v, v ≠ 0 → ⟪v,B v⟫ < 0
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_of_unit (B : E →L[ℝ] E)
    (h : ∀ v, ‖v‖ = 1 → ⟪v,B v⟫ < 0) : NegativeQuadratic B := by
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hh := h (‖v‖⁻¹ • v) (by simp [norm_smul,norm_inv,hv])
  rw [map_smul,real_inner_smul_left,real_inner_smul_right] at hh
  by_contra hge
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hn.le)
    (mul_nonneg (inv_nonneg.mpr hn.le) (le_of_not_gt hge))) hh
lemma negativeQuadratic_isOpen (B : X → E →L[ℝ] E) (hB : Continuous B) :
    IsOpen {x | NegativeQuadratic (B x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hcont : Continuous (fun p : X × E => ⟪p.2,B p.1 p.2⟫) :=
    continuous_snd.inner ((hB.comp continuous_fst).clm_apply continuous_snd)
  have hev := (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually
    (P := fun y v => ⟪v,B y v⟫ < 0) (x₀ := x) (fun v hv =>
      hcont.continuousAt.eventually_lt continuousAt_const
        (hx v (fun he => by simp [he] at hv)))
  filter_upwards [hev] with y hy
  exact negativeQuadratic_of_unit (B y) (fun v hv => hy v (by simpa using hv))
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_pos_sub {B : E →L[ℝ] E} (hB : NegativeQuadratic B)
    {v : E} (hv : v ≠ 0) {lam : ℝ} (hl : 0 < lam) : 0 < ⟪v,lam • v - B v⟫ := by
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  exact sub_pos.mpr ((hB v hv).trans_le (mul_nonneg hl.le (sq_nonneg _)))
end NegativeQuadratic
end
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixBlocks
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
omit [DecidableEq ν] in
lemma matrixEmbed_selfAdjoint (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {B : SqMat μ} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (matrixEmbed e B) := by
  change ((isometryMatrix e) * B * (isometryMatrix e)ᴴ)ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Bᴴ = B from hB.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm
omit [DecidableEq ν] in
lemma matrixCompress_selfAdjoint (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixCompress e A) := by
  change ((isometryMatrix e)ᴴ * A * (isometryMatrix e))ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Aᴴ = A from hA.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm
lemma matrixCompress_embed (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) :
    matrixCompress e (matrixEmbed e B) = B := by
  change (isometryMatrix e)ᴴ * (isometryMatrix e * B * (isometryMatrix e)ᴴ) * isometryMatrix e = B
  calc
    _ = ((isometryMatrix e)ᴴ * isometryMatrix e) * B * ((isometryMatrix e)ᴴ * isometryMatrix e) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [isometryMatrix_star_mul,Matrix.one_mul,Matrix.mul_one]
lemma isometryMatrix_star_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (v : (Euc ν)) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ v = e.toContinuousLinearMap.adjoint v := by
  apply ext_inner_left ℝ
  intro x
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint v⟫ = _
  rw [LinearMap.adjoint_inner_right,isometryMatrix_action,ContinuousLinearMap.adjoint_inner_right]
  rfl
lemma matrixCompress_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) (v : (Euc μ)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) v = e.toContinuousLinearMap.adjoint ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A (e v)) := by
  change Matrix.toEuclideanLin ((isometryMatrix e)ᴴ * A * isometryMatrix e) v = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)ᴴ (Matrix.toEuclideanLin A
    (Matrix.toEuclideanLin (isometryMatrix e) v)) = _
  rw [isometryMatrix_action,isometryMatrix_star_action]
  rfl
noncomputable def blockScalar (c : (Euc ν)) (A : (SqMat ν)) : ℝ := ⟪c,(Matrix.toEuclideanCLM (𝕜 := ℝ)) A c⟫
noncomputable def blockOff (c : (Euc ν)) (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) : (Euc μ) := e.toContinuousLinearMap.adjoint ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A c)
noncomputable def blockCorner (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) : (SqMat ν) := matrixEmbed e (matrixCompress e A)
omit [DecidableEq ν] in
lemma blockCorner_selfAdjoint (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (blockCorner e A) := matrixEmbed_selfAdjoint e (matrixCompress_selfAdjoint e hA)
lemma blockCorner_kernel (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {c : (Euc ν)} (he : ∀ v, ⟪c,e v⟫ = 0) (A : (SqMat ν)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ)) (blockCorner e A) c = 0 := matrixEmbed_kernel e _ he
lemma blockCorner_of_kernel (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {c : (Euc ν)}
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hAc : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = 0) :
    blockCorner e A = A := by
  apply matrixEmbed_compress e hA
  rintro _ ⟨x,rfl⟩
  exact hes _ (matrix_image_orthogonal_kernel hA hAc x)
lemma block_data_zero (c : (Euc ν)) (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (ha : blockScalar c A = 0)
    (hb : blockOff c e A = 0) (hC : blockCorner e A = 0) : A = 0 := by
  have hAc : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = 0 := by
    have hd := frame_decomposition c e hc he hes ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A c)
    change e (blockOff c e A) = (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c - blockScalar c A • c at hd
    simpa only [hb,ha,map_zero,zero_smul,sub_zero] using hd.symm
  rw [blockCorner_of_kernel e hes hA hAc] at hC
  exact hC
lemma blockScalar_continuous (c : (Euc ν)) : Continuous (blockScalar c : (SqMat ν) → ℝ) :=
  continuous_const.inner (((matrixOp ν).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq μ] in
lemma blockOff_continuous (c : (Euc ν)) (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : Continuous (blockOff c e : (SqMat ν) → (Euc μ)) :=
  e.toContinuousLinearMap.adjoint.continuous.comp
    (((matrixOp ν).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq ν] in
lemma blockCorner_continuous (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : Continuous (blockCorner e : (SqMat ν) → (SqMat ν)) :=
  (matrixEmbed e).continuous_of_finiteDimensional.comp (matrixCompress e).continuous_of_finiteDimensional
lemma blockOff_eigenvector {c u : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} {lam : ℝ} (_hu : ‖u‖ = 1) (hcu : 0 < ⟪c,u⟫) (hAu : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A u = lam • u) :
    blockOff c e A = lam • hemisphereInverse c e u - (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) (hemisphereInverse c e u) := by
  let v := hemisphereInverse c e u
  have heq : c + e v = ⟪c,u⟫⁻¹ • u := by
    rw [show v = hemisphereInverse c e u from rfl,hemisphereInverse,map_smul,
      frame_decomposition c e hc he hes,smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hcu),one_smul]
    abel
  have hae : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A (c + e v) = lam • (c + e v) := by
    rw [heq,map_smul,hAu,smul_comm]
  have hb := congrArg e.toContinuousLinearMap.adjoint hae
  rw [map_add,map_add,map_smul,map_add,adjoint_normal c e he,zero_add] at hb
  rw [adjoint_isometry_apply,← matrixCompress_action] at hb
  exact eq_sub_iff_add_eq.mpr hb
end MatrixBlocks
end
end
section
open Set MeasureTheory
section
open scoped BigOperators
section FacetTangent
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def facetTangent {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (Euc (Fin k)) →ₗ[ℝ] (ι → ℝ) where
  toFun v i := if hi : i ∈ I then Fin.cases (-∑ j, v j) (fun j => v j) (a.symm ⟨i,hi⟩) else 0
  map_add' x y := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.sum_add_distrib]; ring
      · rfl
    · simp
  map_smul' t x := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.mul_sum]
      · rfl
    · simp
omit [Fintype ι] in
lemma facetTangent_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : (Euc (Fin k))) (j : Fin (k+1)) :
    facetTangent a v (a j).val = Fin.cases (-∑ j, v j) (fun j => v j) j := by
  simp [facetTangent]
omit [Fintype ι] in
lemma facetTangent_zero_outside {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : (Euc (Fin k))) {i : ι} (hi : i ∉ I) :
    facetTangent a v i = 0 := by simp [facetTangent,hi]
omit [Fintype ι] in
lemma facetTangent_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : (Euc (Fin k))) : ∑ i ∈ I, facetTangent a v i = 0 := by
  calc
    _ = ∑ i : ↥I, facetTangent a v i.val := (Finset.sum_coe_sort I _).symm
    _ = ∑ j : Fin (k+1), facetTangent a v (a j).val := (Equiv.sum_comp a _).symm
    _ = 0 := by simp only [facetTangent_apply,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]; ring
omit [Fintype ι] in
lemma facetTangent_injective {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : Function.Injective (facetTangent a) := by
  intro x y h
  ext j
  have hh := congrFun h (a j.succ).val
  simpa only [facetTangent_apply,Fin.cases_succ] using hh
end FacetTangent
end
end
section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalModel
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma Admissible.signedExtension_kernel_coordinate {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1) (hAc : (matrixOp ν) A c = 0)
    {i : ι} (hi : 0 < f c i) : signedExtension f A i = 0 := by
  obtain ⟨hp,hn⟩ := matrix_parts_kernel hA hAc
  simp only [signedExtension,Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hc hp hi,
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hc hn hi,sub_self]
noncomputable def localBlockModel (f : (Euc ν) → ι → ℝ) (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (A : (SqMat ν)) : ι → ℝ :=
  blockScalar c A • f c + facetTangent a (D (blockOff c e A)) + signedExtension f (blockCorner e A)
omit [Nonempty ν] [Fintype ι] in
lemma localBlockModel_odd (f : (Euc ν) → ι → ℝ) (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (A : (SqMat ν)) :
    localBlockModel f c e a D (-A) = -localBlockModel f c e a D A := by
  simp only [localBlockModel,blockScalar,blockOff,blockCorner,map_neg,neg_apply,inner_neg_right,neg_smul,
    signedExtension_odd,neg_add_rev]
  abel
lemma Admissible.localBlockModel_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) :
    ContinuousOn (localBlockModel f c e a D) {A : (SqMat ν) | IsSelfAdjoint A} := by
  apply ContinuousOn.add
  · exact ((blockScalar_continuous c).smul continuous_const).continuousOn.add
      ((facetTangent a).continuous_of_finiteDimensional.comp
        (D.continuous.comp (blockOff_continuous c e))).continuousOn
  · exact hf.signedExtension_continuousOn.comp (blockCorner_continuous e).continuousOn
      (fun A hA => blockCorner_selfAdjoint e hA)
lemma Admissible.localBlockModel_on_facet {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hI : ∀ i ∈ I, 0 < f c i)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A) {i : ι} (hi : i ∈ I) :
    localBlockModel f c e a D A i = blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i := by
  have hz := hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
    (blockCorner_kernel e he A) (hI i hi)
  simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,add_zero]
lemma Admissible.localBlockModel_sum_facet {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    ∑ i ∈ I, localBlockModel f c e a D A i = blockScalar c A := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    apply Finset.sum_subset (Finset.subset_univ I)
    intro i _ hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  calc
    _ = ∑ i ∈ I, (blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i) :=
      Finset.sum_congr rfl (fun i hi => hf.localBlockModel_on_facet hc e he a hp D hA hi)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hs,facetTangent_sum,mul_one,add_zero]
lemma Admissible.localBlockModel_ne_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    localBlockModel f c e a D A ≠ 0 := by
  intro hz
  have ha : blockScalar c A = 0 := by
    rw [← hf.localBlockModel_sum_facet hc e he a hIc D hA,hz]
    simp
  have hb : blockOff c e A = 0 := by
    apply D.injective
    apply (facetTangent_injective a)
    rw [map_zero,map_zero]
    ext i
    by_cases hi : i ∈ I
    · have hp : ∀ j ∈ I, 0 < f c j := fun j hj => (mem_positiveSupport f c j).mp (hIc.symm ▸ hj)
      have hh := hf.localBlockModel_on_facet hc e he a hp D hA hi
      rw [hz,ha] at hh
      simpa using hh.symm
    · exact facetTangent_zero_outside a _ hi
  have hC : blockCorner e A = 0 := by
    apply (hf.signedExtension_eq_zero_iff (blockCorner_selfAdjoint e hA)).mp
    simpa only [localBlockModel,ha,hb,zero_smul,map_zero,zero_add] using hz
  exact hAz (block_data_zero c e hc he hes hA ha hb hC)
end LocalModel
end
end
section
open Set MeasureTheory
section
open scoped MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockParts
variable {μ ν ι : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma matrixCompress_rankOne (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {c : (Euc ν)} (he : ∀ v, ⟪c,e v⟫ = 0) :
    matrixCompress e (rankOne c) = 0 := by
  apply (matrixOp μ).injective
  apply ContinuousLinearMap.ext
  intro v
  change (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e (rankOne c)) v = (Matrix.toEuclideanCLM (𝕜 := ℝ)) (0 : SqMat μ) v
  rw [matrixCompress_action,rankOne_action,he,zero_smul,map_zero,map_zero,
    zero_apply]
omit [Nonempty ν] in
lemma block_decomposition {c : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0) :
    A = blockScalar c A • rankOne c + blockCorner e A := by
  have hAc : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = blockScalar c A • c := by
    have hd := frame_decomposition c e hc he hes ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A c)
    change e (blockOff c e A) = (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c - blockScalar c A • c at hd
    rw [hb,map_zero] at hd
    exact sub_eq_zero.mp hd.symm
  have hP := (rankOne_nonneg c).isSelfAdjoint
  have hB : IsSelfAdjoint (A - blockScalar c A • rankOne c) := hA.sub ((IsSelfAdjoint.all _).smul hP)
  have hk : (Matrix.toEuclideanCLM (𝕜 := ℝ)) (A - blockScalar c A • rankOne c) c = 0 := by
    rw [map_sub,sub_apply,map_smul,smul_apply,
      rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul,hAc,sub_self]
  have hh := blockCorner_of_kernel e hes hB hk
  have hC : blockCorner e (A - blockScalar c A • rankOne c) = blockCorner e A := by
    simp only [blockCorner,map_sub,map_smul,matrixCompress_rankOne e he,smul_zero,sub_zero]
  rw [hC] at hh
  rw [hh]
  abel
lemma Admissible.signedExtension_nonpos {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≤ 0) : A ≤ 0 := by
  have hp (i : ι) : positiveExtension f A⁺ i = 0 := by
    apply le_antisymm _ (hf.positiveExtension_nonneg A⁺ i)
    apply le_of_not_gt
    intro h
    have hd := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    have hn := (mul_eq_zero.mp hd).resolve_left (ne_of_gt h)
    have hh := hs i
    simp only [signedExtension,Pi.sub_apply,hn,sub_zero] at hh
    exact (not_lt_of_ge hh) h
  have hz : A⁺ = 0 := matrix_psd_trace_zero (CFC.posPart_nonneg A) (by
    rw [← hf.positiveExtension_sum (CFC.posPart_nonneg A)]
    simp [hp])
  have he := CFC.posPart_sub_negPart A hA
  rw [hz,zero_sub] at he
  rw [← he]
  exact neg_nonpos.mpr (CFC.negPart_nonneg A)
omit [Nonempty ν] in
lemma block_parts {c : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    A⁺ = blockScalar c A • rankOne c ∧ A⁻ = -blockCorner e A := by
  have hk : (Matrix.toEuclideanCLM (𝕜 := ℝ)) (-blockCorner e A) c = 0 := by
    rw [map_neg,neg_apply,blockCorner_kernel e he,neg_zero]
  have hp := rankOne_split_parts (neg_nonneg.mpr hC) hk ha (show (0:ℝ) ≤ 1 by norm_num)
  have heq : A = blockScalar c A • rankOne c - (1:ℝ) • (-blockCorner e A) := by
    rw [one_smul,sub_neg_eq_add]
    exact block_decomposition e hc he hes hA hb
  rw [← heq] at hp
  simpa only [one_smul] using hp
lemma Admissible.block_extension {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    signedExtension f A = blockScalar c A • f c + signedExtension f (blockCorner e A) := by
  obtain ⟨hp,hn⟩ := block_parts e hc he hes hA hb ha hC
  have hCp : (blockCorner e A)⁺ = 0 := (CFC.posPart_eq_zero_iff _ (blockCorner_selfAdjoint e hA)).mpr hC
  have hCn : (blockCorner e A)⁻ = -blockCorner e A := by
    have h := CFC.posPart_sub_negPart (blockCorner e A) (blockCorner_selfAdjoint e hA)
    rw [hCp,zero_sub] at h
    exact (neg_eq_iff_eq_neg.mp h)
  ext i
  simp only [signedExtension,Pi.sub_apply,hp,hn,hCp,hCn,positiveExtension_smul_nonneg f (rankOne_nonneg c) ha,
    hf.positiveExtension_rankOne c hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hz : positiveExtension f (0:(SqMat ν)) = 0 := by
    simpa only [zero_smul] using positiveExtension_smul_nonneg f (Q := (0:(SqMat ν))) le_rfl (t := 0) le_rfl
  rw [hz]
  simp only [Pi.zero_apply,sub_eq_add_neg,zero_add]
end BlockParts
end
end
section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section ModelRay
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.localBlockModel_ray {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A)
    {y : ι → ℝ} {rho d : ℝ} (hr : 0 < rho) (hd : 0 < d)
    (hyi : ∀ i ∈ I, y i = rho * f c i) (hyo : ∀ i ∉ I, y i ≤ 0)
    (hM : localBlockModel f c e a D A = d • y) :
    blockOff c e A = 0 ∧ 0 < blockScalar c A ∧
    localBlockModel f c e a D A = signedExtension f A ∧
    A⁺ = blockScalar c A • rankOne c := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hfo : ∀ i ∉ I, f c i = 0 := by
    intro i hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hfo i hi)
  have ha : blockScalar c A = d*rho := by
    rw [← hf.localBlockModel_sum_facet hc e he a hIc D hA,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d * (rho * f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by simp only [← Finset.mul_sum,hs,mul_one]
  have ht (i : ι) (hi : i ∈ I) : facetTangent a (D (blockOff c e A)) i = 0 := by
    have hh := hf.localBlockModel_on_facet hc e he a hp D hA hi
    rw [hM,ha] at hh
    simp only [Pi.smul_apply,smul_eq_mul,hyi i hi] at hh
    nlinarith
  have hb : blockOff c e A = 0 := by
    apply D.injective
    apply (facetTangent_injective a)
    rw [map_zero,map_zero]
    ext i
    by_cases hi : i ∈ I
    · exact ht i hi
    · exact facetTangent_zero_outside a _ hi
  have hC : blockCorner e A ≤ 0 := by
    apply hf.signedExtension_nonpos (blockCorner_selfAdjoint e hA)
    intro i
    by_cases hi : i ∈ I
    · exact (hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
        (blockCorner_kernel e he A) (hp i hi)).le
    · have hh := congrFun hM i
      simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hb,map_zero,
        add_zero,hfo i hi,mul_zero,zero_add] at hh
      rw [hh]
      exact mul_nonpos_of_nonneg_of_nonpos hd.le (hyo i hi)
  have hap : 0 < blockScalar c A := ha ▸ mul_pos hd hr
  refine ⟨hb,hap,?_,(block_parts e hc he hes hA hb hap.le hC).1⟩
  rw [hf.block_extension e hc he hes hA hb hap.le hC]
  simp only [localBlockModel,hb,map_zero,add_zero]
end ModelRay
end
end
section
open Set MeasureTheory
section
section Sard
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma exists_regular_value (f : E → E) (hf : Differentiable ℝ f)
    {U : Set E} (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ y ∈ U, ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  let μ := (Module.finBasis ℝ E).addHaar
  let C : Set E := {x | (fderiv ℝ f x).det = 0}
  have hz : μ (f '' C) = 0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have hUp : 0 < μ U := hU.measure_pos μ hUn
  have hns : ¬ U ⊆ f '' C := by
    intro hs
    have hh : μ U ≤ μ (f '' C) := measure_mono hs
    rw [hz] at hh
    exact (not_le_of_gt hUp) hh
  obtain ⟨y,hy,hny⟩ := Set.not_subset.mp hns
  refine ⟨y,hy,?_⟩
  intro x hx hc
  exact hny ⟨x,hc,hx⟩
omit [MeasurableSpace E] [BorelSpace E] in
lemma compact_regular_level_finite (f : E → E) (hf : ContDiff ℝ 1 f) {y : E}
    {K : Set E} (hc : IsCompact K) (hK : ∀ x ∈ K, f x = y) (hr : ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0) :
    K.Finite := by
  apply hc.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hdet := hr x (hK x hx)
  let e : E ≃L[ℝ] E := (LinearMap.equivOfIsUnitDet
    (f := (fderiv ℝ f x).toLinearMap) (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = fderiv ℝ f x := by
    ext z
    exact LinearMap.equivOfIsUnitDet_apply _ z
  have hd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [he]
    exact hf.hasStrictFDerivAt one_ne_zero
  let p := hd.toOpenPartialHomeomorph f
  refine ⟨p.source, p.open_source,?_⟩
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (p.injOn hz.1 hd.mem_toOpenPartialHomeomorph_source
      ((hK z hz.2).trans (hK x hx).symm))
  · rintro rfl
    exact ⟨hd.mem_toOpenPartialHomeomorph_source,hx⟩
end Sard
end
end
section
open Set MeasureTheory
section
open Set
noncomputable def simplexPoint {n : ℕ} (z : Euc (Fin n)) : Fin (n+1) → ℝ :=
  Fin.cases (1 - ∑ i, z i) (fun i => z i)
def simplexInterior (n : ℕ) : Set (Euc (Fin n)) :=
  {z | (∀ i, 0 < z i) ∧ ∑ i, z i < 1}
lemma simplexInterior_isOpen (n : ℕ) : IsOpen (simplexInterior n) := by
  have h₁ : IsOpen {z : Euc (Fin n) | ∀ i, 0 < z i} := by
    rw [show {z : Euc (Fin n) | ∀ i, 0 < z i} =
      ⋂ i, {z : Euc (Fin n) | 0 < z i} from by ext; simp]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  exact h₁.inter (isOpen_lt (continuous_finsetSum Finset.univ
    (fun i _ => (EuclideanSpace.proj i).continuous)) continuous_const)
lemma simplexInterior_nonempty (n : ℕ) : (simplexInterior n).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)/(n+1)),?_,?_⟩
  · intro i
    change 0 < (1:ℝ)/(n+1)
    positivity
  · change ∑ _i : Fin n, (1:ℝ)/(n+1) < 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
lemma simplexPoint_pos {n : ℕ} {z : Euc (Fin n)} (hz : z ∈ simplexInterior n) :
    ∀ i, 0 < simplexPoint z i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact sub_pos.mpr hz.2
  · exact hz.1 j
lemma simplexPoint_sum {n : ℕ} (z : Euc (Fin n)) : ∑ i, simplexPoint z i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [simplexPoint,Fin.cases_zero,Fin.cases_succ]
  ring
lemma simplexPoint_succ {n : ℕ} (z : Euc (Fin n)) (i : Fin n) :
    simplexPoint z i.succ = z i := rfl
end
section
open Set
open scoped RealInnerProductSpace
end
end
section
open Set MeasureTheory
section
open Set
open scoped RealInnerProductSpace
section RegularBase
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def baseCoordinates (f : (Euc (Fin (k+1))) → ι → ℝ) (w : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (Euc (Fin k)) → (Euc (Fin k)) :=
  fun v => WithLp.toLp 2 (fun j => f (hemisphereChart w e v) (a j.succ).val)
omit [DecidableEq ι] in
lemma Admissible.baseCoordinates_contDiff {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : ContDiff ℝ (⊤ : ℕ∞) (baseCoordinates f w e a) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (hf.smooth (a j.succ).val).comp (hemisphereChart_contDiff w e hw he)
noncomputable def facetPoint {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) : ι → ℝ :=
  fun i => if hi : i ∈ I then simplexPoint z (a.symm ⟨i,hi⟩) else 0
omit [Fintype ι] in
lemma facetPoint_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) (j : Fin (k+1)) :
    facetPoint a z (a j).val = simplexPoint z j := by
  simp [facetPoint]
omit [Fintype ι] in
lemma facetPoint_pos {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k) :
    ∀ i ∈ I, 0 < facetPoint a z i := by
  intro i hi
  simp only [facetPoint,dif_pos hi]
  exact simplexPoint_pos hz _
omit [Fintype ι] in
lemma facetPoint_zero {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) {i : ι} (hi : i ∉ I) :
    facetPoint a z i = 0 := by simp [facetPoint,hi]
lemma facetPoint_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) : ∑ i, facetPoint a z i = 1 := by
  have h : ∑ i, facetPoint a z i = ∑ i : ↥I, simplexPoint z (a.symm i) := by
    calc
      _ = ∑ i ∈ I, facetPoint a z i := (Finset.sum_subset (Finset.subset_univ I)
        (fun i _ hi => facetPoint_zero a z hi)).symm
      _ = ∑ i : ↥I, facetPoint a z i.val := (Finset.sum_coe_sort I _).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => by simp [facetPoint])
  rw [h,Equiv.sum_comp a.symm]
  exact simplexPoint_sum z
lemma Admissible.exists_regular_facet_point {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (z : (Euc (Fin k))), (∀ v, ⟪w,e v⟫ = 0) ∧
      (∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) ∧ z ∈ simplexInterior k ∧
      (∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) ∧
      (orientedLevel f w (facetPoint a z)).Finite := by
  obtain ⟨e,he,hes⟩ := orthogonal_frame k hw
  obtain ⟨z,hz,hr⟩ := exists_regular_value (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).differentiable (by simp)) (simplexInterior_isOpen k) (simplexInterior_nonempty k)
  refine ⟨e,z,he,hes,hz,hr,?_⟩
  let K := orientedLevel f w (facetPoint a z)
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hp : K ⊆ {u | 0 < ⟪w,u⟫} := fun u hu =>
    hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) hu
  have hcont : ContinuousOn (hemisphereInverse w e) K := (hemisphereInverse_continuousOn w e).mono hp
  have hc := (hf.orientedLevel_compact w (facetPoint a z)).image_of_continuousOn hcont
  have hK : ∀ v ∈ hemisphereInverse w e '' K, baseCoordinates f w e a v = z := by
    rintro v ⟨u,hu,rfl⟩
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e u)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),hu.2.1,facetPoint_apply,simplexPoint_succ]
  have hfin := compact_regular_level_finite (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).of_le (by simp)) hc hK hr
  apply (Set.finite_image_iff ?_).mp hfin
  intro u hu v hv huv
  have hh := congrArg (hemisphereChart w e) huv
  rwa [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),
    hemisphereChart_inverse w e hw he hes hv.1 (hp hv)] at hh
end RegularBase
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace Topology
open Filter
section ChartRegular
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]
omit [CompleteSpace E] [CompleteSpace W] [FiniteDimensional ℝ W] in
lemma hemisphereChart_zero {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) : hemisphereChart c e 0 = c := by
  simp [hemisphereChart,SimplicialChains.unitRadial,hc]
omit [FiniteDimensional ℝ W] in
lemma hemisphereInverse_contDiffAt (w : E) (e : W →ₗᵢ[ℝ] E) {u : E} (hu : ⟪w,u⟫ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (hemisphereInverse w e) u :=
  ((contDiffAt_const.inner ℝ contDiffAt_id).inv hu).smul e.toContinuousLinearMap.adjoint.contDiff.contDiffAt
omit [FiniteDimensional ℝ W] in
lemma hemisphere_transition_regular {w c : E} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e d : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0) (hd : ∀ v, ⟪c,d v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (_hds : ∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u)
    (hwc : 0 < ⟪w,c⟫) (f : E → W) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr : (fderiv ℝ (fun v => f (hemisphereChart w e v)) (hemisphereInverse w e c)).det ≠ 0) :
    (fderiv ℝ (fun v => f (hemisphereChart c d v)) 0).det ≠ 0 := by
  let T : W → W := fun v => hemisphereInverse w e (hemisphereChart c d v)
  let S : W → W := fun v => hemisphereInverse c d (hemisphereChart w e v)
  let v₀ := hemisphereInverse w e c
  have hTc : T 0 = v₀ := by simp [T,v₀,hemisphereChart_zero hc]
  have hwc' : hemisphereChart w e v₀ = c := hemisphereChart_inverse w e hw he hes hc hwc
  have hT : ContDiffAt ℝ (⊤ : ℕ∞) T 0 :=
    (hemisphereInverse_contDiffAt w e (by simpa only [hemisphereChart_zero hc] using ne_of_gt hwc)).comp 0
      (hemisphereChart_contDiff c d hc hd).contDiffAt
  have hS : ContDiffAt ℝ (⊤ : ℕ∞) S v₀ :=
    (hemisphereInverse_contDiffAt c d (by rw [hwc']; simp [hc])).comp v₀
      (hemisphereChart_contDiff w e hw he).contDiffAt
  have hnear : ∀ᶠ v in 𝓝 (0:W), 0 < ⟪w,hemisphereChart c d v⟫ :=
    (continuous_const.inner (hemisphereChart_contDiff c d hc hd).continuous).continuousAt
      (isOpen_Ioi.mem_nhds (by simpa only [hemisphereChart_zero hc,Set.mem_Ioi] using hwc))
  have hST : (fun v => S (T v)) =ᶠ[𝓝 (0:W)] id := by
    filter_upwards [hnear] with v hv
    dsimp [S,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv,
      hemisphereInverse_chart c d hc hd]
  have hdT := hT.differentiableAt (by simp)
  have hdS := hS.differentiableAt (by simp)
  have hdS' : HasFDerivAt S (fderiv ℝ S v₀) (T 0) := by rw [hTc]; exact hdS.hasFDerivAt
  have hcomp : (fderiv ℝ S v₀).comp (fderiv ℝ T 0) = ContinuousLinearMap.id ℝ W :=
    (hdS'.comp 0 hdT.hasFDerivAt).unique ((hasFDerivAt_id (0:W)).congr_of_eventuallyEq hST)
  have hTdet : (fderiv ℝ T 0).det ≠ 0 := by
    have composition_det := congrArg ContinuousLinearMap.det hcomp
    change LinearMap.det ((fderiv ℝ S v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) =
      LinearMap.det (LinearMap.id : W →ₗ[ℝ] W) at composition_det
    rw [LinearMap.det_comp, LinearMap.det_id] at composition_det
    have nonzero_product : (fderiv ℝ S v₀).det * (fderiv ℝ T 0).det ≠ 0 := by
      rw [composition_det]
      exact one_ne_zero
    exact (mul_ne_zero_iff.mp nonzero_product).2
  let g : W → W := fun v => f (hemisphereChart w e v)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (hemisphereChart_contDiff w e hw he)
  have hfg : (fun v => f (hemisphereChart c d v)) =ᶠ[𝓝 (0:W)] (fun v => g (T v)) := by
    filter_upwards [hnear] with v hv
    dsimp [g,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv]
  have hgT : HasFDerivAt g (fderiv ℝ g v₀) (T 0) := by
    rw [hTc]
    exact (hg.differentiable (by simp) v₀).hasFDerivAt
  have hfinal := (hgT.comp 0 hdT.hasFDerivAt).congr_of_eventuallyEq hfg
  rw [hfinal.fderiv]
  change LinearMap.det ((fderiv ℝ g v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) ≠ 0
  rw [LinearMap.det_comp]
  exact mul_ne_zero hr hTdet
end ChartRegular
end
end
section
open Set MeasureTheory
section
open scoped Matrix MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockLine
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν]
lemma positiveLine_eigenvector {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = lam • c := by
  rw [← CFC.posPart_sub_negPart A hA,map_sub,sub_apply,
    negPart_kernel_of_positiveLine hc hl hP,sub_zero,hP,map_smul,smul_apply,
    rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul]
lemma blockScalar_positiveLine {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockScalar c A = lam := by
  rw [blockScalar,positiveLine_eigenvector hA hc hl hP,inner_smul_right,real_inner_self_eq_norm_sq,hc,one_pow,mul_one]
omit [DecidableEq μ] in
lemma blockOff_positiveLine (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    blockOff c e A = 0 := by
  rw [blockOff,positiveLine_eigenvector hA hc hl hP,map_smul,adjoint_normal c e he,smul_zero]
lemma blockCorner_positiveLine (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockCorner e A = -A⁻ := by
  have hd := block_decomposition e hc he hes hA (blockOff_positiveLine e hA hc he hl hP)
  rw [blockScalar_positiveLine hA hc hl hP] at hd
  have hp := CFC.posPart_sub_negPart A hA
  rw [hP] at hp
  exact (add_left_cancel (show lam • rankOne c + -A⁻ = lam • rankOne c + blockCorner e A by simpa only [sub_eq_add_neg] using hp.trans hd)).symm
omit [Nonempty ν] in
lemma blockCompress_isUnit (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) (hb : blockOff c e A = 0) :
    IsUnit (matrixCompress e A) := by
  have hopU : IsUnit ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A) := IsUnit.map (matrixOp ν) hU
  have hAi : Function.Injective ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A) := (ContinuousLinearMap.isUnit_iff_bijective.mp hopU).1
  apply (isUnit_map_iff ((Matrix.toEuclideanCLM (𝕜 := ℝ))) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) v = 0 := hv
    have hAv : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A (e v) = 0 := by
      conv_lhs => rw [block_decomposition e hc he hes hA hb]
      rw [map_add,add_apply,map_smul,smul_apply,
        rankOne_action,he,zero_smul,smul_zero,zero_add]
      change (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixEmbed e (matrixCompress e A)) (e v) = 0
      rw [show (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixEmbed e (matrixCompress e A)) (e v) = e ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) v) from matrixEmbed_action e _ v,hv0,map_zero]
    apply e.injective
    exact hAi (by simpa only [map_zero] using hAv)
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩
lemma posDef_inner_pos {B : SqMat μ} (hB : B.PosDef) {v : (Euc μ)} (hv : v ≠ 0) :
    0 < ⟪v,(Matrix.toEuclideanCLM (𝕜 := ℝ)) B v⟫ := by
  have hv' : v.ofLp ≠ 0 := fun h => hv (WithLp.ofLp_injective 2 h)
  have h := hB.dotProduct_mulVec_pos hv'
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 < ∑ i, (B *ᵥ v.ofLp) i * v i
  simpa only [dotProduct,Pi.star_apply,star_trivial,mul_comm] using h
lemma blockCompress_negative (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne c) : NegativeQuadratic ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A)) := by
  have hC := blockCorner_positiveLine e hA hc he hes hl hP
  have hcomp : -(matrixCompress e A) = matrixCompress e A⁻ := by
    have hh := congrArg (matrixCompress e) hC
    rw [blockCorner,matrixCompress_embed,map_neg] at hh
    exact neg_eq_iff_eq_neg.mpr hh
  have hn : 0 ≤ -(matrixCompress e A) := by rw [hcomp]; exact matrixCompress_nonneg e (CFC.negPart_nonneg A)
  have hunit := (blockCompress_isUnit e hA hU hc he hes (blockOff_positiveLine e hA hc he hl hP)).neg
  have hpd := (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr hunit
  intro v hv
  have h := posDef_inner_pos hpd hv
  rw [map_neg,neg_apply,inner_neg_right] at h
  exact neg_pos.mp h
end BlockLine
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace Topology
section LocalRegular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma regular_inner_positive (D : E ≃L[ℝ] E) {g : E → E}
    (h0 : g 0 = 0) (hd : HasFDerivAt g D.toContinuousLinearMap 0) :
    ∃ δ > 0, ∀ v, ‖v‖ < δ → v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫ := by
  let H : E → E := fun v => D.symm (g v)
  have hH : HasFDerivAt H (ContinuousLinearMap.id ℝ E) 0 := by
    convert D.symm.hasFDerivAt.comp 0 hd using 1 <;> ext v <;> simp [H]
  have hH0 : H 0 = 0 := by simp [H,h0]
  have herr := hH.isLittleO.def (show (0:ℝ) < 1/2 by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp herr
  refine ⟨δ,hδ,?_⟩
  intro v hv hv0
  have hb := hball (by simpa only [dist_zero_right] using hv)
  simp only [hH0,sub_zero,ContinuousLinearMap.id_apply] at hb
  have hi : |⟪v,H v - v⟫| ≤ ‖v‖ * ((1/2:ℝ)*‖v‖) :=
    (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [inner_sub_right,real_inner_self_eq_norm_sq] at hi
  change 0 < ⟪v,H v⟫
  nlinarith [neg_abs_le ⟪v,H v⟫,neg_abs_le (⟪v,H v⟫-‖v‖^2)]
lemma positive_inner_convex {v x y : E} (hx : 0 < ⟪v,x⟫) (hy : 0 < ⟪v,y⟫)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : 0 < ⟪v,(1-t) • x + t • y⟫ := by
  simp only [inner_add_right,real_inner_smul_right]
  by_cases ht0 : t = 0
  · simpa [ht0] using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hx.le)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hy)
lemma regular_mixed_zero (D : E ≃L[ℝ] E) {g : E → E} {v b : E} {lam t : ℝ}
    (hp : v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫) (hb : v ≠ 0 → 0 < ⟪v,b⟫)
    (hl : 0 < lam) (ht : t ∈ Set.Icc 0 1)
    (hz : (1-t) • (lam • g v) + t • D b = 0) : v = 0 := by
  by_contra hv
  have hh := positive_inner_convex (by simpa only [real_inner_smul_right] using mul_pos hl (hp hv)) (hb hv) ht
    (v := v) (x := lam • D.symm (g v))
  have he := congrArg D.symm hz
  simp only [map_add,map_smul,D.symm_apply_apply,map_zero] at he
  rw [he,inner_zero_right] at hh
  exact (lt_irrefl (0:ℝ)) hh
end LocalRegular
end
end
section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalMix
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.sum_on_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {u : (Euc ν)} (hu : ‖u‖ = 1)
    {I : Finset ι} (hI : positiveSupport f u = I) : ∑ i ∈ I, f u i = 1 := by
  rw [← hf.sum_one u hu]
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  apply le_antisymm _ (hf.nonneg u hu i)
  exact le_of_not_gt (fun h => hi (hI ▸ (mem_positiveSupport f u i).mpr h))
omit [DecidableEq ι] in
lemma Admissible.extension_on_positiveLine {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} {u : (Euc ν)} (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne u) {i : ι} (hi : 0 < f u i) :
    signedExtension f A i = lam * f u i := by
  have hn := hf.positiveExtension_kernel (CFC.negPart_nonneg A) hu
    (negPart_kernel_of_positiveLine hu hl hP) hi
  simp only [signedExtension,Pi.sub_apply,hn,sub_zero,hP,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hl.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]
lemma Admissible.localBlockModel_eq_of_positiveLine {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k)))
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    localBlockModel f c e a D A = signedExtension f A := by
  have hb := blockOff_positiveLine e hA hc he hl hP
  have hC : blockCorner e A ≤ 0 := by rw [blockCorner_positiveLine e hA hc he hes hl hP]; exact neg_nonpos.mpr (CFC.negPart_nonneg A)
  have ha : 0 ≤ blockScalar c A := by rw [blockScalar_positiveLine hA hc hl hP]; exact hl.le
  rw [hf.block_extension e hc he hes hA hb ha hC]
  simp only [localBlockModel,hb,map_zero,add_zero]
noncomputable def localBlockMix (f : (Euc ν) → ι → ℝ) (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (t : ℝ) (A : (SqMat ν)) : ι → ℝ :=
  (1-t) • signedExtension f A + t • localBlockModel f c e a D A
lemma Admissible.localBlockMix_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (t : ℝ) :
    ∑ i ∈ I, localBlockMix f c e a D t A i = (1-t)*lam + t*blockScalar c A := by
  have hF : ∑ i ∈ I, signedExtension f A i = lam := by
    calc
      _ = ∑ i ∈ I, lam * f u i := Finset.sum_congr rfl (fun i hi =>
        hf.extension_on_positiveLine hu hl hP ((mem_positiveSupport f u i).mp (hIu.symm ▸ hi)))
      _ = _ := by rw [← Finset.mul_sum,hf.sum_on_support hu hIu,mul_one]
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,hF,hf.localBlockModel_sum_facet hc e he a hIc D hA]
lemma Admissible.localBlockMix_ne_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u)
    (ha : 0 < blockScalar c A) {t : ℝ} (ht : t ∈ Set.Icc 0 1) : localBlockMix f c e a D t A ≠ 0 := by
  intro hz
  have hh := hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t
  rw [hz] at hh
  simp only [Pi.zero_apply,Finset.sum_const_zero] at hh
  have hp : 0 < (1-t)*lam + t*blockScalar c A := by
    by_cases ht0 : t = 0
    · simpa [ht0] using hl
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hl.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha)
  linarith
noncomputable def facetTail {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (ι → ℝ) →ₗ[ℝ] (Euc (Fin k)) where
  toFun r := WithLp.toLp 2 (fun j => r (a j.succ).val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma Admissible.localBlockMix_tangent_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0) (_hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (_hcu : 0 < ⟪c,u⟫)
    (_hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (_hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (_ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    (1-t) • (lam • facetTail a (f u - f c)) + t • D (blockOff c e A) = 0 := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hpu : ∀ i ∈ I, 0 < f u i := fun i hi => (mem_positiveSupport f u i).mp (hIu.symm ▸ hi)
  have hs : (1-t)*lam+t*blockScalar c A = d*rho := by
    rw [← hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d*(rho*f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum,hf.sum_on_support hc hIc,mul_one]
  apply PiLp.ext
  intro j
  have hi := (a j.succ).property
  have hh := congrFun hM (a j.succ).val
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    hf.extension_on_positiveLine hu hl hP (hpu _ hi),
    hf.localBlockModel_on_facet hc e he a hp D hA hi,facetTangent_apply,Fin.cases_succ,hyi _ hi] at hh
  change (1-t)*(lam*(f u (a j.succ).val - f c (a j.succ).val)) + t*(D (blockOff c e A)) j = 0
  nlinarith [congrArg (fun x : ℝ => x * f c (a j.succ).val) hs]
lemma Admissible.localBlockMix_hit {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (hcu : 0 < ⟪c,u⟫)
    (hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    u = c ∧ localBlockMix f c e a D t A = signedExtension f A := by
  have hz := hf.localBlockMix_tangent_zero hA hc hu e he hes a hIc hIu D hl hP hcu hB hreg hyi ht hM
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,blockOff c e A⟫ := by
    intro hv
    rw [blockOff_eigenvector e hc he hes hu hcu (positiveLine_eigenvector hA hu hl hP)]
    exact negativeQuadratic_pos_sub hB hv hl
  have hv : hemisphereInverse c e u = 0 := regular_mixed_zero D (g := fun _ : (Euc (Fin k)) => facetTail a (f u-f c)) (v := hemisphereInverse c e u) (b := blockOff c e A) hreg hb hl ht hz
  have huc : u = c := by
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv] at hh
    simpa only [hemisphereChart,SimplicialChains.unitRadial,map_zero,add_zero,hc,inv_one,one_smul] using hh.symm
  refine ⟨huc,?_⟩
  have hm := hf.localBlockModel_eq_of_positiveLine hA hc e he hes a D hl (huc ▸ hP)
  rw [localBlockMix,hm,← add_smul,sub_add_cancel,one_smul]
end LocalMix
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section RegularModel
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.regular_model_data {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w c : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u)
    (hwc : 0 < ⟪w,c⟫) {z : (Euc (Fin k))} (hcval : f c = facetPoint a z)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) :
    ∃ (d : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (δ : ℝ),
      (∀ v, ⟪c,d v⟫ = 0) ∧ (∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u) ∧ 0 < δ ∧
      ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → 0 < ⟪c,u⟫ → ‖hemisphereInverse c d u‖ < δ →
        hemisphereInverse c d u ≠ 0 → 0 < ⟪hemisphereInverse c d u,D.symm (facetTail a (f u-f c))⟫ := by
  obtain ⟨d,hd,hds⟩ := orthogonal_frame k hc
  let F : (Euc (Fin (k+1))) → (Euc (Fin k)) := fun u => facetTail a (f u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply (contDiff_piLp 2).mpr
    intro j
    exact hf.smooth (a j.succ).val
  have hz : baseCoordinates f w e a (hemisphereInverse w e c) = z := by
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e c)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hc hwc,hcval,facetPoint_apply,simplexPoint_succ]
  have hdet : (fderiv ℝ (baseCoordinates f c d a) 0).det ≠ 0 :=
    hemisphere_transition_regular hw hc e d he hd hes hds hwc F hF (hr _ hz)
  let D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k)) :=
    (fderiv ℝ (baseCoordinates f c d a) 0).toContinuousLinearEquivOfDetNeZero hdet
  have hD : D.toContinuousLinearMap = fderiv ℝ (baseCoordinates f c d a) 0 := by
    exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet
  let g : (Euc (Fin k)) → (Euc (Fin k)) := fun v => baseCoordinates f c d a v - F c
  have hg0 : g 0 = 0 := by
    change F (hemisphereChart c d 0) - F c = 0
    rw [hemisphereChart_zero hc,sub_self]
  have hgd : HasFDerivAt g D.toContinuousLinearMap 0 := by
    rw [hD]
    exact (((hf.baseCoordinates_contDiff hc d hd a).differentiable (by simp) 0).hasFDerivAt).sub_const (F c)
  obtain ⟨δ,hδ,hpos⟩ := regular_inner_positive D hg0 hgd
  refine ⟨d,D,δ,hd,hds,hδ,?_⟩
  intro u hu hcu hδu hv
  have hg : g (hemisphereInverse c d u) = facetTail a (f u-f c) := by
    change F (hemisphereChart c d (hemisphereInverse c d u)) - F c = _
    rw [hemisphereChart_inverse c d hc hd hds hu hcu]
    exact (map_sub (facetTail a) _ _).symm
  rw [← hg]
  exact hpos _ hδu hv
end RegularModel
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def regularPatch (f : (Euc (Fin (k+1))) → ι → ℝ) (I : Finset ι) (w c : (Euc (Fin (k+1))))
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) : Set (traceSphere (Fin (k+1))) :=
  {A | IsUnit A.val ∧ HasPositiveLine A.val ∧ (matrixOp (Fin (k+1))) A.val⁺ w ≠ 0 ∧
    (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
    0 < ⟪c,lineRepresentative w A.val⟫ ∧
    ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
    0 < blockScalar c A.val ∧
    NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))}
end RegularPatch
section RegularPatchContinuity
variable {domainIndices rangeIndices labels : Type*}
  [Fintype domainIndices] [Fintype rangeIndices] [Fintype labels]
  [DecidableEq domainIndices] [DecidableEq rangeIndices]
private lemma regularPatch_negative_isOpen (frame : (Euc domainIndices) →ₗᵢ[ℝ] (Euc rangeIndices)) :
    IsOpen {point : traceSphere rangeIndices |
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress frame point.val))} := by
  have hoperator : Continuous (fun matrix : Matrix domainIndices domainIndices ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) matrix) :=
    (matrixOp domainIndices).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact negativeQuadratic_isOpen _
    (hoperator.comp ((matrixCompress frame).continuous_of_finiteDimensional.comp continuous_subtype_val))
omit [DecidableEq domainIndices] [DecidableEq rangeIndices] in
private lemma regularPatch_target_isOpen {f : (Euc rangeIndices) → labels → ℝ} (hf : Admissible f)
    (indices : Finset labels) (center : (Euc rangeIndices)) (frame : (Euc domainIndices) →ₗᵢ[ℝ] (Euc rangeIndices)) (radius : ℝ) :
    IsOpen ({vector : (Euc rangeIndices) | ∀ index ∈ indices, 0 < f vector index} ∩
      ({vector : (Euc rangeIndices) | 0 < ⟪center,vector⟫} ∩
        (fun vector => ‖hemisphereInverse center frame vector‖) ⁻¹' Iio radius)) := by
  have hpos : IsOpen {vector : (Euc rangeIndices) | ∀ index ∈ indices, 0 < f vector index} := by
    have he : {vector : (Euc rangeIndices) | ∀ index ∈ indices, 0 < f vector index} =
        ⋂ index ∈ indices, {vector : (Euc rangeIndices) | 0 < f vector index} := by ext vector; simp
    rw [he]
    exact isOpen_biInter_finset (fun index _ => isOpen_lt continuous_const (hf.smooth index).continuous)
  have hinner : IsOpen {vector : (Euc rangeIndices) | 0 < ⟪center,vector⟫} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  exact hpos.inter ((hemisphereInverse_continuousOn center frame).norm.isOpen_inter_preimage
    hinner (isOpen_Iio : IsOpen (Iio radius)))
private lemma regularPatch_representative_isOpen (vector : (Euc rangeIndices)) {target : Set (Euc rangeIndices)}
    (htarget : IsOpen target) :
    IsOpen {point : traceSphere rangeIndices | (matrixOp rangeIndices) point.val⁺ vector ≠ 0 ∧
      lineRepresentative vector point.val ∈ target} := by
  have hval : Continuous (fun point : traceSphere rangeIndices => point.val) :=
    continuous_subtype_val
  have hself : ∀ point : traceSphere rangeIndices, IsSelfAdjoint point.val :=
    fun point => point.property.1
  have hmatrix : Continuous (fun matrix : Matrix rangeIndices rangeIndices ℝ => (matrixOp rangeIndices) matrix) :=
    ((matrixOp rangeIndices)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hpositive : Continuous (fun point : traceSphere rangeIndices => point.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous hval hself
  have hoperator : Continuous (fun point : traceSphere rangeIndices => (matrixOp rangeIndices) point.val⁺ vector) :=
    (hmatrix.comp hpositive).clm_apply continuous_const
  exact (lineRepresentative_continuousOn _ hval hself vector).isOpen_inter_preimage
    (isClosed_eq hoperator continuous_const).isOpen_compl htarget
private lemma regularPatch_isOpen_aux {f : (Euc rangeIndices) → labels → ℝ} (hf : Admissible f)
    (I : Finset labels) (w c : (Euc rangeIndices)) (e : (Euc domainIndices) →ₗᵢ[ℝ] (Euc rangeIndices)) (δ : ℝ) :
    IsOpen {A : traceSphere rangeIndices |
      IsUnit A.val ∧ HasPositiveLine A.val ∧ (matrixOp rangeIndices) A.val⁺ w ≠ 0 ∧
      (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
      0 < ⟪c,lineRepresentative w A.val⟫ ∧
      ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
      0 < blockScalar c A.val ∧
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))} := by
  let T := traceSphere rangeIndices
  have hA : Continuous (fun A : T => A.val) := continuous_subtype_val
  have hSA : ∀ A : T, IsSelfAdjoint A.val := fun A => A.property.1
  have hpre := regularPatch_representative_isOpen w (regularPatch_target_isOpen hf I c e δ)
  have hscalar : IsOpen {A : T | 0 < blockScalar c A.val} :=
    isOpen_lt continuous_const ((blockScalar_continuous c).comp hA)
  have hneg := regularPatch_negative_isOpen e
  apply isOpen_iff_mem_nhds.mpr
  rintro point ⟨hunit,hline,hvector,hlabels,hinner,hnorm,hblock,hquadratic⟩
  filter_upwards [(positive_line_isOpen _ hA hSA).mem_nhds ⟨hunit,hline⟩,
    hpre.mem_nhds ⟨hvector,hlabels,hinner,hnorm⟩,
    hscalar.mem_nhds hblock, hneg.mem_nhds hquadratic]
    with nearby hpositive hrepresentative hscalar hnegative
  exact ⟨hpositive.1,hpositive.2,hrepresentative.1,hrepresentative.2.1,
    hrepresentative.2.2.1,hrepresentative.2.2.2,hscalar,hnegative⟩
end RegularPatchContinuity
section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma Admissible.regularPatch_isOpen {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) : IsOpen (regularPatch f I w c e δ) :=
  regularPatch_isOpen_aux hf I w c e δ
end RegularPatch
end
end
section
open Set MeasureTheory
section
noncomputable def raySet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) : Set E :=
  {v | v = (‖v‖ / ‖y‖) • y}
lemma raySet_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) :
    IsClosed (raySet y) := isClosed_eq continuous_id ((continuous_norm.div_const _).smul continuous_const)
lemma mem_raySet_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v y : E} (hv : v ≠ 0) (hy : y ≠ 0) : v ∈ raySet y ↔ ∃ d : ℝ, 0 < d ∧ v = d • y := by
  constructor
  · intro h
    exact ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),h⟩
  · rintro ⟨d,hd,rfl⟩
    change d • y = (‖d • y‖ / ‖y‖) • y
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd,mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hy)]
end
section
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixFibres
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def matrixRayFibre (F : (traceSphere (Fin (k+1))) → (Euc ι)) (y : (Euc ι)) (c : (Euc (Fin (k+1)))) : Set (traceSphere (Fin (k+1))) :=
  {A | F A ∈ raySet y ∧ A.val⁺ = Matrix.trace A.val⁺ • rankOne c}
omit [DecidableEq ι] in
lemma matrixRayFibre_closed (F : (traceSphere (Fin (k+1))) → (Euc ι)) (hF : Continuous F) (y : (Euc ι)) (c : (Euc (Fin (k+1)))) :
    IsClosed (matrixRayFibre F y c) := by
  have hp : Continuous (fun A : (traceSphere (Fin (k+1))) => A.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1)
  exact ((raySet_isClosed y).preimage hF).inter
    (isClosed_eq hp ((matrix_trace_continuous.comp hp).smul continuous_const))
lemma Admissible.facet_support {f : (Euc (Fin (k+1))) → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k)
    {c : (Euc (Fin (k+1)))} (hc : f c = facetPoint a z) : positiveSupport f c = I := by
  ext i
  rw [mem_positiveSupport,hc]
  by_cases hi : i ∈ I
  · exact iff_of_true (facetPoint_pos a hz i hi) hi
  · rw [facetPoint_zero a z hi]
    simp [hi]
omit [DecidableEq ι] in
lemma matrixRayFibre_representative {F : (traceSphere (Fin (k+1))) → (Euc ι)} {y : (Euc ι)} {w c : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1)
    (hwc : 0 < ⟪w,c⟫) {A : (traceSphere (Fin (k+1)))} (hline : HasPositiveLine A.val)
    (hK : A ∈ matrixRayFibre F y c) : lineRepresentative w A.val = c :=
  lineRepresentative_split hc (hasPositiveLine_trace_pos hline) hK.2 hwc
omit [DecidableEq ι] in
lemma Admissible.matrixRayFibre_subset_patch {f : (Euc (Fin (k+1))) → ι → ℝ} (_hf : Admissible f)
    {F : (traceSphere (Fin (k+1))) → (Euc ι)} {y : (Euc ι)} {w c : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hwc : 0 < ⟪w,c⟫)
    {I : Finset ι} (hp : ∀ i ∈ I, 0 < f c i)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {δ : ℝ} (hδ : 0 < δ)
    {A : (traceSphere (Fin (k+1)))} (hK : A ∈ matrixRayFibre F y c)
    (hU : IsUnit A.val) (hline : HasPositiveLine A.val) (hAw : (matrixOp (Fin (k+1))) A.val⁺ w ≠ 0) :
    A ∈ regularPatch f I w c e δ := by
  have hr := matrixRayFibre_representative hc hwc hline hK
  have ht := hasPositiveLine_trace_pos hline
  refine ⟨hU,hline,hAw,?_,?_,?_,?_,?_⟩
  · simpa only [hr] using hp
  · rw [hr,real_inner_self_eq_norm_sq,hc]; norm_num
  · rw [hr,hemisphereInverse,adjoint_normal c e he,smul_zero,norm_zero]
    exact hδ
  · rw [blockScalar_positiveLine A.property.1 hc ht hK.2]
    exact ht
  · exact blockCompress_negative e A.property.1 hU hc he hes ht hK.2
end MatrixFibres
end
end
section
namespace SimplicialChains
open Finset
section Supports
variable {E ι : Type*} [NormedAddCommGroup E] [DecidableEq ι]
end Supports
lemma annulus_ne_zero (n : ℕ) (hn : 0 < n) {x : Euc (Fin n)}
    (hx : x ∈ annulus n) : x ≠ 0 := by
  intro hzero
  have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one (by exact_mod_cast hn)
  simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
  linarith [hx.1]
end SimplicialChains
end
section
namespace SimplicialChains
open Finset
lemma compact_additive_locality {X A : Type*} [MetricSpace X] [CompactSpace X]
    [Fintype A] [DecidableEq A] {m : ℕ} [NeZero m]
    (b : Fin m → Bool) (f : X → Euc (Fin m))
    (g : A → X → Euc (Fin m)) (hf : Continuous f) (hg : ∀ a, Continuous (g a))
    (U : A → Set X) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a x, x ∈ U a → f x = g a x)
    (hcover : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) → ∃ a, x ∈ U a)
    (hroot : ∀ a x, (∀ i, g a x ∈ labelRegion i (b i)) → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) :
    ∃ δ > 0, ∀ x : X,
      (∃ i : Fin m, (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        ∀ a, ∃ j : Fin m, ∀ y, dist y x < δ → sphereLabel (g a y) ≠ (j.val,b j)) ∨
      ∃ a, (∀ y, dist y x < δ → f y = g a y) ∧
        ∀ a' ≠ a, ∃ j : Fin m, ∀ y, dist y x < δ → sphereLabel (g a' y) ≠ (j.val,b j) := by
  classical
  let c : Option A × (Option A → Fin m) → Set X := fun p => match p.1 with
    | none => (f ⁻¹' labelRegion (p.2 none) (b (p.2 none)))ᶜ ∩
        ⋂ a, (g a ⁻¹' labelRegion (p.2 (some a)) (b (p.2 (some a))))ᶜ
    | some a => U a ∩ ⋂ a' : {a' : A // a' ≠ a},
        (g a'.val ⁻¹' labelRegion (p.2 (some a'.val)) (b (p.2 (some a'.val))))ᶜ
  have hopen : ∀ p, IsOpen (c p) := by
    intro p
    cases ho : p.1 with
    | none =>
      simp only [c,ho]
      exact (((labelRegion_closed _ _).preimage hf).isOpen_compl).inter
        (isOpen_iInter_of_finite (fun a => ((labelRegion_closed _ _).preimage (hg a)).isOpen_compl))
    | some a =>
      simp only [c,ho]
      exact (hU a).inter (isOpen_iInter_of_finite
        (fun a' => ((labelRegion_closed _ _).preimage (hg a'.val)).isOpen_compl))
  have hc : (Set.univ : Set X) ⊆ ⋃ p, c p := by
    intro x _
    by_cases hx : ∃ a, x ∈ U a
    · obtain ⟨a,ha⟩ := hx
      have hm : ∀ a' : {a' : A // a' ≠ a}, ∃ j, g a'.val x ∉ labelRegion j (b j) := by
        intro a'
        apply not_forall.mp
        intro hh
        exact Set.disjoint_left.mp (hdis a'.property) (hroot a'.val x hh) ha
      choose j hj using hm
      let ji : Option A → Fin m := fun o => match o with
        | none => ⟨0,NeZero.pos m⟩
        | some a' => if h : a' ≠ a then j ⟨a',h⟩ else ⟨0,NeZero.pos m⟩
      refine Set.mem_iUnion.mpr ⟨(some a,ji),ha,Set.mem_iInter.mpr ?_⟩
      intro a'
      simpa only [ji,dif_pos a'.property,Set.mem_compl_iff,Set.mem_preimage] using hj a'
    · have hm : ∀ o : Option A, ∃ j, (match o with | none => f x | some a => g a x) ∉ labelRegion j (b j) := by
        intro o
        apply not_forall.mp
        intro hh
        cases o with
        | none => exact hx (hcover x hh)
        | some a => exact hx ⟨a,hroot a x hh⟩
      choose j hj using hm
      exact Set.mem_iUnion.mpr ⟨(none,j),hj none,Set.mem_iInter.mpr (fun a => hj (some a))⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hc
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨⟨o,j⟩,hj⟩ := hball x (Set.mem_univ _)
  cases o with
  | none =>
    refine Or.inl ⟨j none,?_,?_⟩
    · intro y hy he
      exact (hj hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro a
      refine ⟨j (some a),?_⟩
      intro y hy he
      exact Set.mem_iInter.mp (hj hy).2 a (sphereLabel_mem_region _ _ _ he)
  | some a =>
    refine Or.inr ⟨a,fun y hy => heq a y (hj hy).1,?_⟩
    intro a' ha'
    refine ⟨j (some a'),?_⟩
    intro y hy he
    exact Set.mem_iInter.mp (hj hy).2 ⟨a',ha'⟩ (sphereLabel_mem_region _ _ _ he)
lemma additive_approximation_coeff {A : Type*} [Fintype A] [DecidableEq A]
    (n m : ℕ) (hn : 0 < n) [NeZero m] (b : Fin m → Bool)
    (f : Euc (Fin n) → Euc (Fin m))
    (g : A → Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ∀ a, ContinuousOn (g a) (annulus n))
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → f x.val = g a x.val)
    (hcover : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), (∀ i, g a x.val ∈ labelRegion i (b i)) → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      ∑ a, approximation n m r (fun x => sphereLabel (g a x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_additive_locality b (fun x : annulus n => f x.val)
    (fun a (x : annulus n) => g a x.val) hf.domRestrict (fun a => (hg a).domRestrict)
    U hU heq hcover hroot hdis
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := Euc (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : A → Chain K →ₗ[F₂] F₂ := fun a =>
    (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g a x)))
  change T (fineCrossMap n r (crossFundamental n)) = ∑ a, R a (fineCrossMap n r (crossFundamental n))
  rw [← LinearMap.sum_apply]
  apply linearMap_eq_of_support T (∑ a, R a) _
  intro s hs
  rw [LinearMap.sum_apply]
  have heT : T (simplex K s.val) = mapSimplex (cross m) (fun x => sphereLabel (f x)) s.val t := by
    exact congrArg (fun c : Chain (cross m) => c t) (mapChains_simplex K (cross m) _ s.property)
  have heR (a : A) : R a (simplex K s.val) = mapSimplex (cross m) (fun x => sphereLabel (g a x)) s.val t := by
    exact congrArg (fun c : Chain (cross m) => c t) (mapChains_simplex K (cross m) _ s.property)
  simp only [heT,heR]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  have hball (y) (hy : y ∈ s.val) : dist (⟨y,ha y hy⟩ : annulus n) ⟨x,ha x hx⟩ < δ :=
    (hmesh y hy x hx).trans_lt hr
  rcases hlocal ⟨x,ha x hx⟩ with ⟨i,hi,hgmiss⟩ | ⟨a,heq,hgmiss⟩
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
      (image_ne_crossFacet_of_missing s.val _ b i (fun y hy => hi ⟨y,ha y hy⟩ (hball y hy)))]
    symm
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨j,hj⟩ := hgmiss a
    exact mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
      (image_ne_crossFacet_of_missing s.val _ b j (fun y hy => hj ⟨y,ha y hy⟩ (hball y hy)))
  · rw [Finset.sum_eq_single a]
    · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g a y)) := by
        apply Finset.image_congr
        intro y hy
        exact congrArg sphereLabel (heq ⟨y,ha y hy⟩ (hball y hy))
      simp only [mapSimplex,himg]
    · intro a' _ ha'
      obtain ⟨j,hj⟩ := hgmiss a' ha'
      exact mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
        (image_ne_crossFacet_of_missing s.val _ b j (fun y hy => hj ⟨y,ha y hy⟩ (hball y hy)))
    · simp
end SimplicialChains
end
section
open Set MeasureTheory
section
open Finset Set
open scoped Topology
lemma finite_positive_bound {A : Type*} [Fintype A] (d : A → ℝ) (hd : ∀ a, 0 < d a) :
    ∃ ε > 0, ∀ a, ε < d a := by
  classical
  by_cases hne : Nonempty A
  · let r : ℝ := Finset.univ.inf' Finset.univ_nonempty d
    have hr : 0 < r := (Finset.lt_inf'_iff _).mpr (by simpa using hd)
    refine ⟨r/2,by positivity,fun a => ?_⟩
    exact (by linarith : r/2 < r).trans_le (Finset.inf'_le _ (Finset.mem_univ a))
  · exact ⟨1,zero_lt_one,fun a => False.elim (hne ⟨a⟩)⟩
end
namespace SimplicialChains
open Finset Set
lemma odd_homotopy_local_models {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (hn : 1 < n) [NeZero n] (b : Fin n → Bool)
    (H : ℝ × Euc (Fin n) → Euc (Fin n))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    (G : A → Euc (Fin n) → Euc (Fin n))
    (hG : ∀ a, ContinuousOn (G a) (annulus n))
    (hGz : ∀ a x, x ∈ annulus n → G a x ≠ 0)
    (hGo : ∀ a x, x ∈ annulus n → G a (-x) = -G a x)
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → H (1,x.val) = G a x.val)
    (hcover : ∀ x : annulus n, unitRadial (H (1,x.val)) = facetCenter n b → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), unitRadial (G a x.val) = facetCenter n b → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card A : F₂) = 1 := by
  classical
  let f : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (H (1,x))
  let g : A → Euc (Fin n) → Euc (Fin n) := fun a x => unitRadial (G a x)
  have hfc : ContinuousOn f (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩))
      (fun x hx => hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn (x) (hx : x ∈ annulus n) : ‖f x‖ = 1 := unitRadial_norm (hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hgc (a) : ContinuousOn (g a) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp (hG a) (hGz a)
  have hgn (a x) (hx : x ∈ annulus n) : ‖g a x‖ = 1 := unitRadial_norm (hGz a x hx)
  obtain ⟨δa,hδa,hadd⟩ := additive_approximation_coeff n n (by omega) b f g hfc hgc U hU
    (fun a x hx => congrArg unitRadial (heq a x hx))
    (fun x hx => hcover x ((all_labelRegions_iff_center n b _ (hfn _ x.property)).mp hx))
    (fun a x hx => hroot a x ((all_labelRegions_iff_center n b _ (hgn a _ x.property)).mp hx)) hdis
  obtain ⟨δh,hδh,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl H hH hHz
  have hc0 : ContinuousOn (fun x => unitRadial (H (0,x))) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
      (fun x hx => hHz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  obtain ⟨δ0,hδ0,hdeg0⟩ := eventually_odd_sphere_degree n hn _ hc0
    (fun x hx => unitRadial_norm (hHz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
    (fun x hx => by rw [hHo x hx,unitRadial_neg])
  have hgodd : ∀ a, ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n) = crossFundamental n := by
    intro a
    apply eventually_odd_sphere_degree n hn _ (hgc a) (hgn a)
    intro x hx
    change unitRadial (G a (-x)) = -unitRadial (G a x)
    rw [hGo a x hx,unitRadial_neg]
  choose dg hdg hdgprop using hgodd
  obtain ⟨δg,hδg,hδgb⟩ := finite_positive_bound dg hdg
  obtain ⟨r,hr⟩ := exists_small_cross_mesh n (by omega) (lt_min hδ0 (lt_min hδh (lt_min hδa hδg)))
  have hr0 := hr.trans_le (min_le_left _ _)
  have hrh := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hra := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrg := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he0 : approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) = crossFundamental n :=
    (hhom r hrh).symm.trans (hdeg0 r hr0)
  have hadd' := hadd r hra
  rw [he0,crossFundamental_coeff n hn b] at hadd'
  have hm (a : A) : approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 1 := by
    rw [hdgprop a r (hrg.trans (hδgb a)),crossFundamental_coeff n hn b]
  simpa only [hm,Finset.sum_const,Finset.card_univ,nsmul_one] using hadd'.symm
end SimplicialChains
end
section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains Set
section TraceLocalModels
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
  [Fintype κ] [DecidableEq κ]
omit [Nonempty ν] in
lemma trace_odd_local_models
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (H : ℝ × traceSphere ν → (Euc ι))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ univ))
    (hHz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A : traceSphere ν, H (t,A) ≠ 0)
    (hHo : ∀ A B : traceSphere ν, B.val = -A.val → H (0,B) = -H (0,A))
    (G : κ → traceSphere ν → (Euc ι)) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
    (U : κ → Set (traceSphere ν)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a A, A ∈ U a → H (1,A) = G a A)
    {y : (Euc ι)} (hy : y ≠ 0)
    (hcover : ∀ A : traceSphere ν, (∃ d : ℝ, 0 < d ∧ H (1,A) = d • y) → ∃ a, A ∈ U a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card κ : F₂) = 1 := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let b : Fin n → Bool := fun _ => false
  let R := Submodule.reflection (ℝ ∙ (ebL (unitRadial y) - facetCenter n b))ᗮ
  let L : (Euc ι) ≃ₗᵢ[ℝ] Euc (Fin n) := ebL.trans R
  have hRy : L (unitRadial y) = facetCenter n b :=
    Submodule.reflection_sub ((ebL.norm_map _).trans (unitRadial_norm hy) |>.trans (facetCenter_norm n b).symm)
  have hray (v : (Euc ι)) (hv : v ≠ 0) (he : unitRadial (L v) = facetCenter n b) :
      ∃ d : ℝ, 0 < d ∧ v = d • y := by
    have hu : unitRadial v = unitRadial y := by
      apply L.injective
      rw [hRy]
      simpa only [unitRadial,map_smul,L.norm_map] using he
    refine ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),?_⟩
    have hh := congrArg (fun z : (Euc ι) => ‖v‖ • z) hu
    simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul,div_eq_mul_inv] using hh
  let A : Euc (Fin n) → (SqMat ν) := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    exact annulus_ne_zero n (by omega) hx (eaL.symm.injective (h0.trans (map_zero _).symm))
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val) (fun x => hAz _ x.property)
  have hNneg (x) (hx : x ∈ annulus n) (hxn : -x ∈ annulus n) :
      (N ⟨-x,hxn⟩).val = -(N ⟨x,hx⟩).val := by simp only [N,A,map_neg,traceRadial_neg]
  let H' : ℝ × Euc (Fin n) → Euc (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then L (H (p.1,N ⟨p.2,hx⟩)) else 0
  have hH' : ContinuousOn H' (Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hH.comp_continuous (continuous_subtype_val.fst.prodMk hcN) (fun p : S => ⟨p.property.1,mem_univ _⟩)
    apply (L.continuous.comp hg).congr
    intro p
    simp only [Set.domRestrict_apply,Function.comp_apply,H',dif_pos p.property.2]
  have hHz' : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H' p ≠ 0 := by
    intro p hp hz
    exact hHz _ hp.1 _ (L.injective (by simpa only [H',dif_pos hp.2,map_zero] using hz))
  have hHo' : ∀ x ∈ annulus n, H' (0,-x) = -H' (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H',dif_pos hx,dif_pos hxn,hHo _ _ (hNneg x hx hxn),map_neg]
  let G' : κ → Euc (Fin n) → Euc (Fin n) := fun a x =>
    if hx : x ∈ annulus n then L (G a (N ⟨x,hx⟩)) else 0
  have hG' (a) : ContinuousOn (G' a) (annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (L.continuous.comp ((hG a).comp hN)).congr
    intro x
    simp only [Set.domRestrict_apply,Function.comp_apply,G',dif_pos x.property]
  have hGz' (a x) (hx : x ∈ annulus n) : G' a x ≠ 0 := by
    intro hz
    exact hGz a _ (L.injective (by simpa only [G',dif_pos hx,map_zero] using hz))
  have hGo' (a x) (hx : x ∈ annulus n) : G' a (-x) = -G' a x := by
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [G',dif_pos hx,dif_pos hxn,hGo a _ _ (hNneg x hx hxn),map_neg]
  apply odd_homotopy_local_models n hn b H' hH' hHz' hHo' G' hG' hGz' hGo'
    (fun a => N ⁻¹' U a) (fun a => (hU a).preimage hN)
  · intro a x hx
    simp only [H',G',dif_pos x.property,heq a _ hx]
  · intro x hx
    apply hcover (N x)
    apply hray _ (hHz _ ⟨zero_le_one,le_rfl⟩ _)
    simpa only [H',dif_pos x.property] using hx
  · intro a x hx
    apply hroot a (N x)
    apply hray _ (hGz a _)
    simpa only [G',dif_pos x.property] using hx
  · intro a a' haa
    exact (hdis haa).preimage N
end TraceLocalModels
end
end
section
open Set MeasureTheory
section
open Finset
open scoped RealInnerProductSpace
section FinitePatch
variable {X E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype A]
noncomputable def finitePatch (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) : E := f x + ∑ a, (t * q a x) • (g a x - f x)
lemma finitePatch_continuous [TopologicalSpace X] {f : X → E} {g : A → X → E} {q : A → X → ℝ}
    (hf : Continuous f) (hg : ∀ a, Continuous (g a)) (hq : ∀ a, Continuous (q a)) :
    Continuous (fun p : ℝ × X => finitePatch f g q p.1 p.2) := by
  apply (hf.comp continuous_snd).add
  apply continuous_finsetSum
  intro a _
  exact (continuous_fst.mul ((hq a).comp continuous_snd)).smul
    (((hg a).comp continuous_snd).sub (hf.comp continuous_snd))
lemma finitePatch_zero (f : X → E) (g : A → X → E) (q : A → X → ℝ) (x : X) :
    finitePatch f g q 0 x = f x := by simp [finitePatch]
lemma finitePatch_of_all_zero (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) (hq : ∀ a, q a x = 0) : finitePatch f g q t x = f x := by
  simp [finitePatch,hq]
lemma finitePatch_of_disjoint [DecidableEq A]
    (f : X → E) (g : A → X → E) (q : A → X → ℝ) (t : ℝ) (x : X) (a : A)
    (hq : ∀ a' ≠ a, q a' x = 0) :
    finitePatch f g q t x = (1-t*q a x) • f x + (t*q a x) • g a x := by
  unfold finitePatch
  rw [Finset.sum_eq_single a]
  · module
  · intro a' _ ha'
    simp [hq a' ha']
  · simp
lemma finitePatch_one_of_disjoint [DecidableEq A]
    (f : X → E) (g : A → X → E) (q : A → X → ℝ) (x : X) (a : A)
    (h1 : q a x = 1) (hq : ∀ a' ≠ a, q a' x = 0) :
    finitePatch f g q 1 x = g a x := by
  rw [finitePatch_of_disjoint f g q 1 x a hq,h1]
  simp
lemma finitePatch_cases [DecidableEq A] (f : X → E) (g : A → X → E)
    (q : A → X → ℝ) (t : ℝ) (x : X)
    (hq : Pairwise (fun a a' => Disjoint (Function.support (q a)) (Function.support (q a')))) :
    finitePatch f g q t x = f x ∨ ∃ a, q a x ≠ 0 ∧
      finitePatch f g q t x = (1-t*q a x) • f x + (t*q a x) • g a x := by
  by_cases hh : ∃ a, q a x ≠ 0
  · obtain ⟨a,ha⟩ := hh
    refine Or.inr ⟨a,ha,finitePatch_of_disjoint f g q t x a ?_⟩
    intro a' ha'
    by_contra hn
    exact Set.disjoint_left.mp (hq ha') hn ha
  · push Not at hh
    exact Or.inl (finitePatch_of_all_zero f g q t x hh)
lemma finitePatch_ne_zero [DecidableEq A] (f : X → E) (g : A → X → E)
    (q : A → X → ℝ) (t : ℝ) (x : X)
    (hq : Pairwise (fun a a' => Disjoint (Function.support (q a)) (Function.support (q a'))))
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hqb : ∀ a, q a x ∈ Set.Icc (0:ℝ) 1)
    (hf : f x ≠ 0)
    (hseg : ∀ a, q a x ≠ 0 → ∀ s ∈ Set.Icc (0:ℝ) 1,
      (1-s) • f x + s • g a x ≠ 0) : finitePatch f g q t x ≠ 0 := by
  rcases finitePatch_cases f g q t x hq with he | ⟨a,ha,he⟩
  · rwa [he]
  · rw [he]
    exact hseg a ha (t*q a x) ⟨mul_nonneg ht.1 (hqb a).1,
      (mul_le_mul_of_nonneg_left (hqb a).2 ht.1).trans (by simpa using ht.2)⟩
end FinitePatch
end
end
section
open Set MeasureTheory
section
open Set Finset
lemma finite_closed_cutoffs {A X : Type*} [Fintype A] [DecidableEq A]
    [TopologicalSpace X] [NormalSpace X]
    (K S : A → Set X) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hdis : Pairwise (fun a b => Disjoint (K a) (K b))) :
    ∃ U : A → Set X, ∃ q : A → C(X,ℝ), (∀ a, IsOpen (U a)) ∧
      (∀ a, K a ⊆ U a) ∧ (∀ a x, q a x ∈ Icc (0:ℝ) 1) ∧
      (∀ a x, x ∈ U a → q a x = 1) ∧
      (∀ a x, q a x ≠ 0 → x ∈ S a) ∧
      Pairwise (fun a b => Disjoint (Function.support (q a)) (Function.support (q b))) := by
  classical
  let Z : A → Set X := fun a => (S a)ᶜ ∪ ⋃ b ∈ (Finset.univ.erase a : Finset A), K b
  have hZ (a) : IsClosed (Z a) := (hS a).isClosed_compl.union (isClosed_biUnion_finset fun b _ => hK b)
  have hd (a) : Disjoint (Z a) (K a) := by
    apply Set.disjoint_left.mpr
    intro x hx hxa
    rcases hx with hs | hb
    · exact hs (hKS a hxa)
    · obtain ⟨b,hb,hxb⟩ := Set.mem_iUnion₂.mp hb
      exact Set.disjoint_left.mp (hdis (Finset.ne_of_mem_erase hb)) hxb hxa
  have hs (a) := exists_continuous_zero_one_of_isClosed (hZ a) (hK a) (hd a)
  choose p hp0 hp1 hpb using hs
  let score : A → X → ℝ := fun a x => 2*p a x - ∑ b, p b x
  have hscore (a) : Continuous (score a) :=
    ((p a).continuous.const_mul 2).sub (continuous_finsetSum _ (fun b _ => (p b).continuous))
  have hscoreK (a x) (hx : x ∈ K a) : score a x = 1 := by
    have hpothers (b) (hb : b ≠ a) : p b x = 0 := hp0 b (Or.inr (Set.mem_iUnion₂.mpr ⟨a,Finset.mem_erase.mpr ⟨Ne.symm hb,Finset.mem_univ _⟩,hx⟩))
    dsimp [score]
    rw [Finset.sum_eq_single a]
    · rw [hp1 a hx]; norm_num
    · intro b _ hb; exact hpothers b hb
    · simp
  let U : A → Set X := fun a => {x | (3/4:ℝ) < score a x}
  let q : A → C(X,ℝ) := fun a => ⟨fun x => max 0 (min 1 (4*(score a x-1/2))),
    continuous_const.max (continuous_const.min (((hscore a).sub continuous_const).const_mul 4))⟩
  have hpos (a x) (hx : q a x ≠ 0) : (1/2:ℝ) < score a x := by
    change max 0 (min 1 (4*(score a x-1/2))) ≠ 0 at hx
    by_contra hn
    apply hx
    exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
  refine ⟨U,q,fun a => isOpen_lt continuous_const (hscore a),?_,?_,?_,?_,?_⟩
  · intro a x hx
    change (3/4:ℝ) < score a x
    rw [hscoreK a x hx]; norm_num
  · intro a x
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · intro a x hx
    change max 0 (min 1 (4*(score a x-1/2))) = 1
    rw [min_eq_left (by change (3/4:ℝ) < score a x at hx; linarith)]
    norm_num
  · intro a x hx
    by_contra hn
    have hz : p a x = 0 := hp0 a (Or.inl hn)
    have hsum : 0 ≤ ∑ b, p b x := Finset.sum_nonneg (fun b _ => (hpb b x).1)
    have hh := hpos a x hx
    dsimp [score] at hh
    rw [hz] at hh
    linarith
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have ha := hpos a x hxa
    have hb := hpos b x hxb
    have hs : p a x + p b x ≤ ∑ c, p c x := by
      calc
        _ = ∑ c ∈ ({a,b} : Finset A), p c x := by simp [hab]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => (hpb c x).1)
    dsimp [score] at ha hb
    linarith
end
end
section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator
section TracePatchModels
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
  [Fintype κ] [DecidableEq κ]
omit [Nonempty ν] in
lemma trace_patch_models
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (F : traceSphere ν → (Euc ι)) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
    (hFo : ∀ A B : traceSphere ν, B.val = -A.val → F B = -F A)
    (G : κ → traceSphere ν → (Euc ι)) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
    (K S : κ → Set (traceSphere ν)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
    {y : (Euc ι)} (hy : y ≠ 0)
    (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
    (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
    (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
      (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
    (Fintype.card κ : F₂) = 1 := by
  classical
  obtain ⟨U,q,hU,hKU,hqb,hq1,hqS,hqd⟩ := finite_closed_cutoffs K S hK hS hKS hKd
  let H : ℝ × traceSphere ν → (Euc ι) := fun p => finitePatch F G (fun a => q a) p.1 p.2
  have hH : Continuous H := finitePatch_continuous hF hG (fun a => (q a).continuous)
  have hHz (t) (ht : t ∈ Icc (0:ℝ) 1) (A) : H (t,A) ≠ 0 :=
    finitePatch_ne_zero F G (fun a => q a) t A hqd ht (fun a => hqb a A) (hFz A)
      (fun a ha => hseg a A (hqS a A ha))
  refine trace_odd_local_models hc hn H hH.continuousOn hHz
    (fun A B hB => by simpa only [H,finitePatch_zero] using hFo A B hB)
    G hG hGz hGo U hU ?_ hy ?_ ?_ ?_
  · intro a A hA
    apply finitePatch_one_of_disjoint F G (fun a => q a) A a (hq1 a A hA)
    intro b hba
    by_contra hb
    exact Set.disjoint_left.mp (hqd hba) hb (by
      change q a A ≠ 0
      rw [hq1 a A hA]; exact one_ne_zero)
  · intro A hA
    rcases finitePatch_cases F G (fun a => q a) 1 A hqd with he | ⟨a,ha,he⟩
    · have hr : ∃ d : ℝ, 0 < d ∧ F A = d • y := by
        simpa only [H,he] using hA
      obtain ⟨a,ha⟩ := hcover A hr
      exact ⟨a,hKU a ha⟩
    · refine ⟨a,hKU a (hhit a A (hqS a A ha) (q a A) (hqb a A) ?_)⟩
      simpa only [H,he,one_mul] using hA
  · intro a A hA
    exact hKU a (hroot a A hA)
  · intro a b hab
    exact (hqd hab).mono
      (fun A hA => by change q a A ≠ 0; rw [hq1 a A hA]; exact one_ne_zero)
      (fun A hA => by change q b A ≠ 0; rw [hq1 b A hA]; exact one_ne_zero)
end TracePatchModels
end
end
section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.regular_facet_level_odd {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 1 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hcp (c : L) : positiveSupport f c.val = I := hf.facet_support a hz (hcv c)
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let v := uniformVector ↥(Iᶜ : Finset ι)
  have hv (i : ↥(Iᶜ : Finset ι)) : 0 < v i := by
    change 0 < (Fintype.card ↥(Iᶜ : Finset ι) : ℝ)⁻¹
    positivity
  have hvs : ∑ i, v i = 1 := coordinateSum_uniform _
  let y : (Euc ι) := blockVector I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) (facetPoint_pos a hz) _
  let F : (traceSphere (Fin (k+1))) → (Euc ι) := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let G : L → (traceSphere (Fin (k+1))) → (Euc ι) := fun c A => WithLp.toLp 2 (localBlockModel f c.val (d c) a (D c) A.val)
  let K : L → Set (traceSphere (Fin (k+1))) := fun c => matrixRayFibre F y c.val
  let S : L → Set (traceSphere (Fin (k+1))) := fun c => regularPatch f I w c.val (d c) (δ c)
  have hF : Continuous F := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hFz (A : (traceSphere (Fin (k+1)))) : F A ≠ 0 := by
    intro hzA
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp (WithLp.toLp_injective 2 hzA))
  have hFroot (A : (traceSphere (Fin (k+1)))) (hA : F A ∈ raySet y) :
      IsUnit A.val ∧ HasPositiveLine A.val ∧
      (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ) A.val⁺) w ≠ 0 ∧
      0 < Matrix.trace A.val⁻ ∧ lineRepresentative w A.val ∈ L := by
    obtain ⟨t,ht,hAt⟩ := (mem_raySet_iff (hFz A) hy).mp hA
    exact hf.original_ray_level hI hmax hw hwi (facetPoint_pos a hz) (fun i hi => facetPoint_zero a z hi)
      (facetPoint_sum a z) hv hvs A.property ht hAt
  have hG (c : L) : Continuous (G c) := (PiLp.continuous_toLp 2 _).comp
    ((hf.localBlockModel_continuousOn c.val (d c) a (D c)).comp_continuous continuous_subtype_val
      (fun A => A.property.1))
  have hGz (c : L) (A : (traceSphere (Fin (k+1)))) : G c A ≠ 0 := by
    intro hzA
    exact hf.localBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (traceSphere_ne_zero A.property) (WithLp.toLp_injective 2 hzA)
  have hKS (c : L) : K c ⊆ S c := by
    intro A hA
    have hh := hFroot A hA.1
    exact hf.matrixRayFibre_subset_patch (hc c) (hcw c) (by simpa only [hcv c] using facetPoint_pos a hz)
      (d c) (hd c) (hds c) (hδ c) hA hh.1 hh.2.1 hh.2.2.1
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro A hA hA'
    have hh := hFroot A hA.1
    apply hcc
    apply Subtype.ext
    exact (matrixRayFibre_representative (hc c) (hcw c) hh.2.1 hA).symm.trans
      (matrixRayFibre_representative (hc c') (hcw c') hh.2.1 hA')
  have hyi (c : L) (i : ι) (hi : i ∈ I) : y i = (1/2:ℝ)*f c.val i := by
    rw [hcv c]
    exact blockVector_in I _ _ _ _ hi
  have hyo (i : ι) (hi : i ∉ I) : y i ≤ 0 := by
    have hh := blockVector_out I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v ⟨i,Finset.mem_compl.mpr hi⟩
    change y i = _ at hh
    rw [hh]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hv _).le
  have hcover (A : (traceSphere (Fin (k+1)))) (hA : ∃ t : ℝ, 0 < t ∧ F A = t • y) : ∃ c, A ∈ K c := by
    have hray := (mem_raySet_iff (hFz A) hy).mpr hA
    have hh := hFroot A hray
    exact ⟨⟨lineRepresentative w A.val,hh.2.2.2.2⟩,hray,positive_line_representative hh.2.1 hh.2.2.1⟩
  have hroot (c : L) (A : (traceSphere (Fin (k+1)))) (hA : ∃ t : ℝ, 0 < t ∧ G c A = t • y) : A ∈ K c := by
    obtain ⟨t,ht,hAt⟩ := hA
    have hm : localBlockModel f c.val (d c) a (D c) A.val = t • y.ofLp := WithLp.toLp_injective 2 hAt
    obtain ⟨hb,ha,heq,hP⟩ := hf.localBlockModel_ray (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (by norm_num : (0:ℝ) < 1/2) ht (hyi c) hyo hm
    have hFt : F A = t • y := by simpa only [F,G,heq] using hAt
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨t,ht,hFt⟩,?_⟩
    have htr : Matrix.trace A.val⁺ = blockScalar c.val A.val := by
      rw [hP,Matrix.trace_smul,rankOne_trace,hc c,one_pow,smul_eq_mul,mul_one]
    rwa [htr]
  have hseg (c : L) (A : (traceSphere (Fin (k+1)))) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (1-t) • F A + t • G c A ≠ 0 := by
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hh := hf.localBlockMix_ne_zero A.property.1 (hc c) hnU (d c) (hd c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1) hA.2.2.2.2.2.2.1 ht
    intro hzA
    exact hh (WithLp.toLp_injective 2 hzA)
  have hhit (c : L) (A : (traceSphere (Fin (k+1)))) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
      (hAt : ∃ b : ℝ, 0 < b ∧ (1-t) • F A + t • G c A = b • y) : A ∈ K c := by
    obtain ⟨b,hb,heq⟩ := hAt
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hmix : localBlockMix f c.val (d c) a (D c) t A.val = b • y.ofLp := WithLp.toLp_injective 2 heq
    obtain ⟨huc,hme⟩ := hf.localBlockMix_hit A.property.1 (hc c) hnU (d c) (hd c) (hds c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1)
      hA.2.2.2.2.1 hA.2.2.2.2.2.2.2
      (hreg c _ hnU hA.2.2.2.2.1 hA.2.2.2.2.2.1) (hyi c) ht hmix
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨b,hb,?_⟩,?_⟩
    · exact congrArg (WithLp.toLp 2) (hme.symm.trans hmix)
    · rw [← huc]
      exact positive_line_representative hA.2.1 hA.2.2.1
  have hp := trace_patch_models hdim hn F hF hFz (by
      intro A B hB
      simp only [F,hB,signedExtension_odd,WithLp.toLp_neg])
    G hG hGz (by
      intro c A B hB
      simp only [G,hB,localBlockModel_odd,WithLp.toLp_neg])
    K S (fun c => matrixRayFibre_closed F hF y c.val) (fun c => hf.regularPatch_isOpen I w c.val (d c) (δ c))
    hKS hKd hy hcover hroot hseg hhit
  simpa only [Nat.card_eq_fintype_card] using hp
end MatrixParity
end
end
section
open Set MeasureTheory
namespace SimplicialChains
open Finset Set
lemma null_homotopy_local_models {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (hn : 1 < n) [NeZero n] (b : Fin n → Bool)
    (H : ℝ × Euc (Fin n) → Euc (Fin n))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (C : ℝ × Euc (Fin n) → Euc (Fin n))
    (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hCz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, C p ≠ 0)
    (hC1 : ∀ x, C (1,x) = H (0,x))
    (hCmiss : ∀ x ∈ annulus n, unitRadial (C (0,x)) ≠ facetCenter n b)
    (G : A → Euc (Fin n) → Euc (Fin n))
    (hG : ∀ a, ContinuousOn (G a) (annulus n))
    (hGz : ∀ a x, x ∈ annulus n → G a x ≠ 0)
    (hGo : ∀ a x, x ∈ annulus n → G a (-x) = -G a x)
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → H (1,x.val) = G a x.val)
    (hcover : ∀ x : annulus n, unitRadial (H (1,x.val)) = facetCenter n b → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), unitRadial (G a x.val) = facetCenter n b → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card A : F₂) = 0 := by
  classical
  let f : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (H (1,x))
  let g : A → Euc (Fin n) → Euc (Fin n) := fun a x => unitRadial (G a x)
  have hfc : ContinuousOn f (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩))
      (fun x hx => hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn (x) (hx : x ∈ annulus n) : ‖f x‖ = 1 := unitRadial_norm (hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hgc (a) : ContinuousOn (g a) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp (hG a) (hGz a)
  have hgn (a x) (hx : x ∈ annulus n) : ‖g a x‖ = 1 := unitRadial_norm (hGz a x hx)
  obtain ⟨δa,hδa,hadd⟩ := additive_approximation_coeff n n (by omega) b f g hfc hgc U hU
    (fun a x hx => congrArg unitRadial (heq a x hx))
    (fun x hx => hcover x ((all_labelRegions_iff_center n b _ (hfn _ x.property)).mp hx))
    (fun a x hx => hroot a x ((all_labelRegions_iff_center n b _ (hgn a _ x.property)).mp hx)) hdis
  obtain ⟨δh,hδh,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl H hH hHz
  have hc0 : ContinuousOn (fun x => unitRadial (C (0,x))) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hC.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
      (fun x hx => hCz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  obtain ⟨δc,hδc,hhomC⟩ := normalized_homotopy_chains n n (by omega) le_rfl C hC hCz
  obtain ⟨δm,hδm,hmiss⟩ := continuous_missed_facet_zero n n (by omega) hn b _ hc0
    (fun x hx => unitRadial_norm (hCz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)) hCmiss
  have hdeg0 : ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (unitRadial (H (0,x)))) (crossFundamental n)
        ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 0 := by
    refine ⟨min δc δm,lt_min hδc hδm,fun r hr => ?_⟩
    have hh := hhomC r (hr.trans_le (min_le_left _ _))
    simp only [hC1] at hh
    rw [← hh]
    exact hmiss r (hr.trans_le (min_le_right _ _))
  obtain ⟨δ0,hδ0,hdeg0⟩ := hdeg0
  have hgodd : ∀ a, ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n) = crossFundamental n := by
    intro a
    apply eventually_odd_sphere_degree n hn _ (hgc a) (hgn a)
    intro x hx
    change unitRadial (G a (-x)) = -unitRadial (G a x)
    rw [hGo a x hx,unitRadial_neg]
  choose dg hdg hdgprop using hgodd
  obtain ⟨δg,hδg,hδgb⟩ := finite_positive_bound dg hdg
  obtain ⟨r,hr⟩ := exists_small_cross_mesh n (by omega) (lt_min hδ0 (lt_min hδh (lt_min hδa hδg)))
  have hr0 := hr.trans_le (min_le_left _ _)
  have hrh := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hra := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrg := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he0 : approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 0 := by
    dsimp only [f]
    rw [← hhom r hrh]
    exact hdeg0 r hr0
  have hadd' := hadd r hra
  rw [he0] at hadd'
  have hm (a : A) : approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 1 := by
    rw [hdgprop a r (hrg.trans (hδgb a)),crossFundamental_coeff n hn b]
  simpa only [hm,Finset.sum_const,Finset.card_univ,nsmul_one] using hadd'.symm
end SimplicialChains
end
section
open Set MeasureTheory
section
open Set SimplicialChains
noncomputable def normSphere (n : ℕ) : Set (Euc (Fin n)) := {u | ‖u‖ = 1}
section SphereNullModels
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
lemma sphere_null_local_models (hn : 1 < n)
    (H C : ℝ × (normSphere n) → (Euc (Fin n)))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ univ))
    (hHz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : (normSphere n), H (t,u) ≠ 0)
    (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ univ))
    (hCz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : (normSphere n), C (t,u) ≠ 0)
    (hC1 : ∀ u, C (1,u) = H (0,u))
    (G : κ → (normSphere n) → (Euc (Fin n))) (hG : ∀ a, Continuous (G a)) (hGz : ∀ a u, G a u ≠ 0)
    (hGo : ∀ a (u v : (normSphere n)), v.val = -u.val → G a v = -G a u)
    (U : κ → Set (normSphere n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a u, u ∈ U a → H (1,u) = G a u)
    {y : (Euc (Fin n))} (hy : y ≠ 0)
    (hmiss : ∀ u : (normSphere n), ¬ ∃ d : ℝ, 0 < d ∧ C (0,u) = d • y)
    (hcover : ∀ u : (normSphere n), (∃ d : ℝ, 0 < d ∧ H (1,u) = d • y) → ∃ a, u ∈ U a)
    (hroot : ∀ a u, (∃ d : ℝ, 0 < d ∧ G a u = d • y) → u ∈ U a)
    (hdis : Pairwise (fun a b => Disjoint (U a) (U b))) : (Fintype.card κ : F₂) = 0 := by
  classical
  let : NeZero n := ⟨by omega⟩
  let b : Fin n → Bool := fun _ => false
  let L := Submodule.reflection (ℝ ∙ (unitRadial y - facetCenter n b))ᗮ
  have hRy : L (unitRadial y) = facetCenter n b :=
    Submodule.reflection_sub ((unitRadial_norm hy).trans (facetCenter_norm n b).symm)
  have hray (v : (Euc (Fin n))) (hv : v ≠ 0) (he : unitRadial (L v) = facetCenter n b) :
      ∃ d : ℝ, 0 < d ∧ v = d • y := by
    have hu : unitRadial v = unitRadial y := by
      apply L.injective
      rw [hRy]
      simpa only [unitRadial,map_smul,L.norm_map] using he
    refine ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),?_⟩
    have hh := congrArg (fun z : (Euc (Fin n)) => ‖v‖ • z) hu
    simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul,div_eq_mul_inv] using hh
  let N : annulus n → (normSphere n) := fun x => ⟨unitRadial x.val,unitRadial_norm (annulus_ne_zero n (by omega) x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact (unitRadial_continuousOn (fun _ hx => annulus_ne_zero n (by omega) hx)).domRestrict
  have hNneg (x) (hx : x ∈ annulus n) (hxn : -x ∈ annulus n) : (N ⟨-x,hxn⟩).val = -(N ⟨x,hx⟩).val := unitRadial_neg x
  let extH (P : ℝ × (normSphere n) → (Euc (Fin n))) : ℝ × (Euc (Fin n)) → (Euc (Fin n)) := fun p => if hx : p.2 ∈ annulus n then L (P (p.1,N ⟨p.2,hx⟩)) else 0
  have hext (P : ℝ × (normSphere n) → (Euc (Fin n))) (hP : ContinuousOn P (Icc (0:ℝ) 1 ×ˢ univ)) :
      ContinuousOn (extH P) (Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let Q := Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : Q => N ⟨p.val.2,p.property.2⟩) := hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hP.comp_continuous (continuous_subtype_val.fst.prodMk hcN) (fun p : Q => ⟨p.property.1,mem_univ _⟩)
    apply (L.continuous.comp hg).congr
    intro p
    simp only [Set.domRestrict_apply,Function.comp_apply,extH,dif_pos p.property.2]
  have hextz (P : ℝ × (normSphere n) → (Euc (Fin n))) (hPz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, P (t,u) ≠ 0) :
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, extH P p ≠ 0 := by
    intro p hp hz
    exact hPz _ hp.1 _ (L.injective (by simpa only [extH,dif_pos hp.2,map_zero] using hz))
  let G' : κ → (Euc (Fin n)) → (Euc (Fin n)) := fun a x => if hx : x ∈ annulus n then L (G a (N ⟨x,hx⟩)) else 0
  have hG' (a) : ContinuousOn (G' a) (annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (L.continuous.comp ((hG a).comp hN)).congr
    intro x
    simp only [Set.domRestrict_apply,Function.comp_apply,G',dif_pos x.property]
  have hGz' (a x) (hx : x ∈ annulus n) : G' a x ≠ 0 := by
    intro hz
    exact hGz a _ (L.injective (by simpa only [G',dif_pos hx,map_zero] using hz))
  have hGo' (a x) (hx : x ∈ annulus n) : G' a (-x) = -G' a x := by
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [G',dif_pos hx,dif_pos hxn,hGo a _ _ (hNneg x hx hxn),map_neg]
  refine null_homotopy_local_models n hn b (extH H) (hext H hH) (hextz H hHz) (extH C) (hext C hC) (hextz C hCz)
    (fun x => by simp only [extH,hC1]) ?_ G' hG' hGz' hGo'
    (fun a => N ⁻¹' U a) (fun a => (hU a).preimage hN) ?_ ?_ ?_ ?_
  · intro x hx he
    apply hmiss (N ⟨x,hx⟩)
    apply hray _ (hCz _ ⟨le_rfl,zero_le_one⟩ _)
    simpa only [extH,dif_pos hx] using he
  · intro a x hx
    simp only [extH,G',dif_pos x.property,heq a _ hx]
  · intro x hx
    apply hcover (N x)
    apply hray _ (hHz _ ⟨zero_le_one,le_rfl⟩ _)
    simpa only [extH,dif_pos x.property] using hx
  · intro a x hx
    apply hroot a (N x)
    apply hray _ (hGz a _)
    simpa only [G',dif_pos x.property] using hx
  · intro a a' haa
    exact (hdis haa).preimage N
end SphereNullModels
end
end
section
open Set MeasureTheory
section
open Set SimplicialChains
section SphereNullPatch
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
lemma sphere_null_patch_models (hn : 1 < n)
    (F : normSphere n → (Euc (Fin n))) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
    (C : ℝ × normSphere n → (Euc (Fin n))) (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ univ))
    (hCz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, C (t,u) ≠ 0)
    (hC1 : ∀ u, C (1,u) = F u)
    (G : κ → normSphere n → (Euc (Fin n))) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : normSphere n), B.val = -A.val → G a B = -G a A)
    (K S : κ → Set (normSphere n)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
    {y : (Euc (Fin n))} (hy : y ≠ 0)
    (hmiss : ∀ u, ¬ ∃ d : ℝ, 0 < d ∧ C (0,u) = d • y)
    (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
    (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
    (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
      (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
    (Fintype.card κ : F₂) = 0 := by
  classical
  obtain ⟨U,q,hU,hKU,hqb,hq1,hqS,hqd⟩ := finite_closed_cutoffs K S hK hS hKS hKd
  let H : ℝ × normSphere n → (Euc (Fin n)) := fun p => finitePatch F G (fun a => q a) p.1 p.2
  have hH : Continuous H := finitePatch_continuous hF hG (fun a => (q a).continuous)
  have hHz (t) (ht : t ∈ Icc (0:ℝ) 1) (A) : H (t,A) ≠ 0 :=
    finitePatch_ne_zero F G (fun a => q a) t A hqd ht (fun a => hqb a A) (hFz A)
      (fun a ha => hseg a A (hqS a A ha))
  refine sphere_null_local_models hn H C hH.continuousOn hHz hC hCz
    (fun u => by simpa only [H,finitePatch_zero] using hC1 u)
    G hG hGz hGo U hU ?_ hy hmiss ?_ ?_ ?_
  · intro a A hA
    apply finitePatch_one_of_disjoint F G (fun a => q a) A a (hq1 a A hA)
    intro b hba
    by_contra hb
    exact Set.disjoint_left.mp (hqd hba) hb (by
      change q a A ≠ 0
      rw [hq1 a A hA]; exact one_ne_zero)
  · intro A hA
    rcases finitePatch_cases F G (fun a => q a) 1 A hqd with he | ⟨a,ha,he⟩
    · have hr : ∃ d : ℝ, 0 < d ∧ F A = d • y := by
        simpa only [H,he] using hA
      obtain ⟨a,ha⟩ := hcover A hr
      exact ⟨a,hKU a ha⟩
    · refine ⟨a,hKU a (hhit a A (hqS a A ha) (q a A) (hqb a A) ?_)⟩
      simpa only [H,he,one_mul] using hA
  · intro a A hA
    exact hKU a (hroot a A hA)
  · intro a b hab
    exact (hqd hab).mono
      (fun A hA => by change q a A ≠ 0; rw [hq1 a A hA]; exact one_ne_zero)
      (fun A hA => by change q b A ≠ 0; rw [hq1 b A hA]; exact one_ne_zero)
end SphereNullPatch
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section SphereBlock
variable {k : ℕ}
noncomputable def sphereBlock (s : ℝ) (v : (Euc (Fin k))) : (Euc (Fin (k+1))) := WithLp.toLp 2 (Fin.cases s (fun i => v i))
lemma sphereBlock_zero (s : ℝ) (v : (Euc (Fin k))) : sphereBlock s v 0 = s := rfl
lemma sphereBlock_succ (s : ℝ) (v : (Euc (Fin k))) (i : Fin k) : sphereBlock s v i.succ = v i := rfl
lemma sphereBlock_continuous {X : Type*} [TopologicalSpace X] {s : X → ℝ} {v : X → (Euc (Fin k))}
    (hs : Continuous s) (hv : Continuous v) : Continuous (fun x => sphereBlock (s x) (v x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · exact (PiLp.continuous_apply 2 _ j).comp hv
lemma sphereBlock_neg (s : ℝ) (v : (Euc (Fin k))) : sphereBlock (-s) (-v) = -sphereBlock s v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl
lemma sphereBlock_eq_zero {s : ℝ} {v : (Euc (Fin k))} (h : sphereBlock s v = 0) : s = 0 ∧ v = 0 := by
  refine ⟨congrArg (fun u : (Euc (Fin (k+1))) => u 0) h,?_⟩
  ext i
  exact congrArg (fun u : (Euc (Fin (k+1))) => u i.succ) h
noncomputable def sphereBlockModel (c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (u : (Euc (Fin (k+1)))) : (Euc (Fin (k+1))) :=
  sphereBlock ⟪c,u⟫ (D (e.toContinuousLinearMap.adjoint u))
lemma sphereBlockModel_continuous (c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) : Continuous (sphereBlockModel c e D) :=
  sphereBlock_continuous (continuous_const.inner continuous_id) (D.continuous.comp (e.toContinuousLinearMap.adjoint.continuous))
lemma sphereBlockModel_odd (c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (u : (Euc (Fin (k+1)))) :
    sphereBlockModel c e D (-u) = -sphereBlockModel c e D u := by
  simp only [sphereBlockModel,inner_neg_right,map_neg,sphereBlock_neg]
lemma hemisphereInverse_eq_zero_iff {c u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (hcu : 0 < ⟪c,u⟫) : hemisphereInverse c e u = 0 ↔ u = c := by
  constructor
  · intro hv
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv,hemisphereChart_zero hc] at hh
    exact hh.symm
  · intro hh
    subst u
    rw [hemisphereInverse,adjoint_normal c e he,smul_zero]
lemma sphereBlockModel_ne_zero {c u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (hu : u ≠ 0) : sphereBlockModel c e D u ≠ 0 := by
  intro hz
  obtain ⟨h1,h2⟩ := sphereBlock_eq_zero hz
  have he0 : e.toContinuousLinearMap.adjoint u = 0 := D.injective (h2.trans D.map_zero.symm)
  have hd := frame_decomposition c e hc he hes u
  rw [h1,he0,zero_smul,map_zero,sub_zero] at hd
  exact hu hd.symm
lemma sphereBlockModel_ray {c u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {b : ℝ} (hb : 0 < b)
    (h : sphereBlockModel c e D u = b • sphereBlock 1 (0 : (Euc (Fin k)))) : u = c := by
  have hs : ⟪c,u⟫ = b := by
    have hh := congrArg (fun v : (Euc (Fin (k+1))) => v 0) h
    simpa only [sphereBlockModel,sphereBlock_zero,PiLp.smul_apply,mul_one,smul_eq_mul] using hh
  have ht : D (e.toContinuousLinearMap.adjoint u) = 0 := by
    ext i
    have hh := congrArg (fun v : (Euc (Fin (k+1))) => v i.succ) h
    simpa only [sphereBlockModel,sphereBlock_succ,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
  apply (hemisphereInverse_eq_zero_iff hc hu e he hes (hs ▸ hb)).mp
  rw [hemisphereInverse,D.injective (ht.trans D.map_zero.symm),smul_zero]
lemma sphereBlock_mix_nonzero {c w u : (Euc (Fin (k+1)))} (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k)))
    (g : (Euc (Fin k))) (hw : 0 < ⟪w,u⟫) (hc : 0 < ⟪c,u⟫) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • sphereBlock ⟪w,u⟫ g + t • sphereBlockModel c e D u ≠ 0 := by
  intro hz
  have hh := congrArg (fun v : (Euc (Fin (k+1))) => v 0) hz
  simp only [PiLp.add_apply,PiLp.smul_apply,sphereBlockModel,sphereBlock_zero,smul_eq_mul,PiLp.zero_apply] at hh
  rcases lt_or_eq_of_le ht.2 with hl | rfl
  · have hp : 0 < (1-t)*⟪w,u⟫ := mul_pos (sub_pos.mpr hl) hw
    have hn : 0 ≤ t*⟪c,u⟫ := mul_nonneg ht.1 hc.le
    linarith
  · linarith
lemma sphereBlock_mix_ray {c w u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (g : (Euc (Fin k))) (hcu : 0 < ⟪c,u⟫)
    (hr : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,D.symm g⟫)
    {t b : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hm : (1-t) • sphereBlock ⟪w,u⟫ g + t • sphereBlockModel c e D u = b • sphereBlock 1 (0 : (Euc (Fin k)))) :
    u = c := by
  have hz : (1-t) • g + t • D (e.toContinuousLinearMap.adjoint u) = 0 := by
    ext i
    have hh := congrArg (fun v : (Euc (Fin (k+1))) => v i.succ) hm
    simpa only [PiLp.add_apply,PiLp.smul_apply,sphereBlockModel,sphereBlock_succ,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,e.toContinuousLinearMap.adjoint u⟫ := by
    intro hv
    have hvv : e.toContinuousLinearMap.adjoint u = ⟪c,u⟫ • hemisphereInverse c e u := by
      rw [hemisphereInverse,smul_smul,mul_inv_cancel₀ (ne_of_gt hcu),one_smul]
    rw [hvv,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_pos hcu (sq_pos_of_pos (norm_pos_iff.mpr hv))
  have hv := regular_mixed_zero D (g := fun _ : (Euc (Fin k)) => g) (v := hemisphereInverse c e u)
    (b := e.toContinuousLinearMap.adjoint u) hr hb (show (0:ℝ)<1 from zero_lt_one) ht (by simpa only [one_smul] using hz)
  exact (hemisphereInverse_eq_zero_iff hc hu e he hes hcu).mp hv
end SphereBlock
end
end
section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped RealInnerProductSpace
section SphereParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
lemma facetTail_point {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) :
    facetTail a (facetPoint a z) = z := by
  ext j
  exact (facetPoint_apply a z j.succ).trans (simplexPoint_succ z j)
lemma Admissible.eq_facetPoint_of_tail {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {u : (Euc (Fin (k+1)))} (hu : ‖u‖ = 1)
    (hs : positiveSupport f u ⊆ I) {z : (Euc (Fin k))} (hz : facetTail a (f u) = z) :
    f u = facetPoint a z := by
  have he (i : ι) (hi : i ≠ (a 0).val) : f u i = facetPoint a z i := by
    by_cases hI : i ∈ I
    · obtain ⟨j,hj⟩ := a.surjective ⟨i,hI⟩
      have hji : (a j).val = i := congrArg Subtype.val hj
      have hj0 : j ≠ 0 := fun h => hi (by simpa only [h] using hji.symm)
      obtain ⟨l,rfl⟩ := Fin.eq_succ_of_ne_zero hj0
      rw [← hji,facetPoint_apply,simplexPoint_succ]
      exact congrArg (fun v : (Euc (Fin k)) => v l) hz
    · rw [facetPoint_zero a z hI]
      apply le_antisymm _ (hf.nonneg u hu i)
      exact le_of_not_gt (fun h => hI (hs ((mem_positiveSupport f u i).mpr h)))
  have hall : ∑ i, (f u i-facetPoint a z i) = f u (a 0).val-facetPoint a z (a 0).val := by
    apply Finset.sum_eq_single (a 0).val
    · intro i _ hi
      exact sub_eq_zero.mpr (he i hi)
    · simp
  rw [Finset.sum_sub_distrib,hf.sum_one u hu,facetPoint_sum,sub_self] at hall
  funext i
  by_cases hi : i = (a 0).val
  · subst i
    exact sub_eq_zero.mp hall.symm
  · exact he i hi
noncomputable def sphereRegularPatch (w c : (Euc (Fin (k+1)))) (d : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) : Set (normSphere (k+1)) :=
  {u | 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c,u.val⟫ ∧ ‖hemisphereInverse c d u.val‖ < δ}
lemma sphereRegularPatch_isOpen (w c : (Euc (Fin (k+1)))) (d : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) :
    IsOpen (sphereRegularPatch w c d δ) := by
  have hc : IsOpen {u : (Euc (Fin (k+1))) | 0 < ⟪c,u⟫} := isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hp := (hemisphereInverse_continuousOn c d).norm.isOpen_inter_preimage hc (isOpen_Iio : IsOpen (Iio δ))
  exact ((isOpen_lt (f := fun u : (Euc (Fin (k+1))) => (0 : ℝ)) (g := fun u : (Euc (Fin (k+1))) => ⟪w,u⟫) continuous_const (continuous_const.inner continuous_id)).inter hp).preimage continuous_subtype_val
lemma Admissible.regular_facet_level_even {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) {I : Finset ι} (a : Fin (k+1) ≃ ↥I)
    (hfree : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → (∀ j : Fin k, 0 < f u (a j.succ).val) → positiveSupport f u ⊆ I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 0 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let g : (Euc (Fin (k+1))) → (Euc (Fin k)) := fun u => facetTail a (f u)
  have hg : Continuous g := (facetTail a).continuous_of_finiteDimensional.comp (continuous_pi (fun i => (hf.smooth i).continuous))
  let C : ℝ × normSphere (k+1) → (Euc (Fin (k+1))) := fun p => sphereBlock ⟪w,p.2.val⟫ (p.1 • g p.2.val-z)
  have hC : Continuous C := sphereBlock_continuous (continuous_const.inner continuous_snd.subtype_val)
    ((continuous_fst.smul (hg.comp continuous_snd.subtype_val)).sub continuous_const)
  have hCz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (u : normSphere (k+1)) : C (t,u) ≠ 0 := by
    intro hzero
    obtain ⟨hwu,hv⟩ := sphereBlock_eq_zero hzero
    have htail : g u.val = 0 := by
      ext j
      apply le_antisymm _ (hf.nonneg _ u.property _)
      exact le_of_not_gt (fun hp => hf.orthogonal w u.val hw u.property hwu (a j.succ).val ⟨hwi _ (a j.succ).property,hp⟩)
    change t • g u.val-z = 0 at hv
    rw [htail,smul_zero,zero_sub,neg_eq_zero] at hv
    have hpos := hz.1 (⟨0,hk⟩ : Fin k)
    rw [hv] at hpos
    exact lt_irrefl 0 hpos
  let F : normSphere (k+1) → (Euc (Fin (k+1))) := fun u => sphereBlock ⟪w,u.val⟫ (g u.val-z)
  have hF : Continuous F := sphereBlock_continuous (continuous_const.inner continuous_subtype_val)
    ((hg.comp continuous_subtype_val).sub continuous_const)
  have hFz (u) : F u ≠ 0 := by simpa only [C,F,one_smul] using hCz 1 ⟨zero_le_one,le_rfl⟩ u
  let G : L → normSphere (k+1) → (Euc (Fin (k+1))) := fun c u => sphereBlockModel c.val (d c) (D c) u.val
  let K : L → Set (normSphere (k+1)) := fun c => {u | u.val = c.val}
  let S : L → Set (normSphere (k+1)) := fun c => sphereRegularPatch w c.val (d c) (δ c)
  let y : (Euc (Fin (k+1))) := sphereBlock 1 (0 : (Euc (Fin k)))
  have hy : y ≠ 0 := fun h => one_ne_zero (sphereBlock_eq_zero h).1
  have hKS (c : L) : K c ⊆ S c := by
    intro u hu
    change u.val = c.val at hu
    change 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c.val,u.val⟫ ∧ ‖hemisphereInverse c.val (d c) u.val‖ < δ c
    rw [hu,real_inner_self_eq_norm_sq,hc c,one_pow]
    refine ⟨hcw c,zero_lt_one,?_⟩
    rw [hemisphereInverse,adjoint_normal c.val (d c) (hd c),smul_zero,norm_zero]
    exact hδ c
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro u hu hu'
    exact hcc (Subtype.ext (hu.symm.trans hu'))
  have hmiss (u : normSphere (k+1)) : ¬ ∃ b : ℝ, 0 < b ∧ C (0,u) = b • y := by
    rintro ⟨b,hb,hbEq⟩
    have hv := congrArg (fun v : (Euc (Fin (k+1))) => v (Fin.succ ⟨0,hk⟩)) hbEq
    have hpos := hz.1 (⟨0,hk⟩ : Fin k)
    simp only [C,y,zero_smul,zero_sub,sphereBlock_succ,PiLp.neg_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] at hv
    linarith
  have hcover (u : normSphere (k+1)) (hu : ∃ b : ℝ, 0 < b ∧ F u = b • y) : ∃ c, u ∈ K c := by
    obtain ⟨b,hb,hbu⟩ := hu
    have hwu : 0 < ⟪w,u.val⟫ := by
      have hh := congrArg (fun v : (Euc (Fin (k+1))) => v 0) hbu
      have hh' : ⟪w,u.val⟫ = b := by simpa only [F,y,sphereBlock_zero,PiLp.smul_apply,smul_eq_mul,mul_one] using hh
      exact hh' ▸ hb
    have hgz : g u.val = z := by
      ext j
      have hh := congrArg (fun v : (Euc (Fin (k+1))) => v j.succ) hbu
      have hh' : g u.val j-z j = 0 := by simpa only [F,y,sphereBlock_succ,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
      exact sub_eq_zero.mp hh'
    have hup : ∀ j : Fin k, 0 < f u.val (a j.succ).val := by
      intro j
      have hh := congrArg (fun v : (Euc (Fin k)) => v j) hgz
      change f u.val (a j.succ).val = z j at hh
      rw [hh]
      exact hz.1 j
    have huf := hf.eq_facetPoint_of_tail a u.property (hfree u.val u.property hup) hgz
    exact ⟨⟨u.val,u.property,huf,hwu.le⟩,rfl⟩
  have hcount := sphere_null_patch_models (by omega : 1 < k+1) F hF hFz C hC.continuousOn hCz
    (fun u => by simp only [C,F,one_smul]) G
    (fun c => (sphereBlockModel_continuous c.val (d c) (D c)).comp continuous_subtype_val)
    (fun c u => sphereBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) (D c) (norm_ne_zero_iff.mp (by rw [u.property]; exact one_ne_zero)))
    (by intro c u v hv; simp only [G,hv,sphereBlockModel_odd]) K S
    (fun c => isClosed_eq continuous_subtype_val continuous_const)
    (fun c => sphereRegularPatch_isOpen w c.val (d c) (δ c)) hKS hKd hy hmiss hcover
    (by
      intro c u hu
      obtain ⟨b,hb,hbu⟩ := hu
      exact sphereBlockModel_ray (hc c) u.property (d c) (hd c) (hds c) (D c) hb hbu)
    (by
      intro c u hu t ht
      exact sphereBlock_mix_nonzero (d c) (D c) (g u.val-z) hu.1 hu.2.1 ht)
    (by
      intro c u hu t ht htu
      obtain ⟨b,hb,hbu⟩ := htu
      apply sphereBlock_mix_ray (hc c) u.property (d c) (hd c) (hds c) (D c) (g u.val-z) hu.2.1 _ ht hbu
      have hge : g u.val-z = facetTail a (f u.val-f c.val) := by
        rw [map_sub,hcv c,facetTail_point]
      rw [hge]
      exact hreg c u.val u.property hu.2.1 hu.2.2)
  simpa only [Nat.card_eq_fintype_card] using hcount
end SphereParity
end
end
section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped RealInnerProductSpace
section NoFreeRidge
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.no_free_indexed_facet {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : (Euc (Fin (k+1))), ‖u‖ = 1 ∧ (∀ j : Fin k, 0 < f u (a j.succ).val) ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  by_contra hnfree
  push Not at hnfree
  obtain ⟨e,z,he,hes,hz,hr,hfin⟩ := hf.exists_regular_facet_point a hw hwi
  have ho := hf.regular_facet_level_odd hdim hn a hmax hw hwi e he hes hz hr hfin
  have heven := hf.regular_facet_level_even hk a hnfree hw hwi e he hes hz hr hfin
  rw [heven] at ho
  exact zero_ne_one ho
lemma Admissible.no_free_ridge {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I U : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (hI : I.card = k+1) (hUI : U ⊆ I) (hU : U.card = k)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : (Euc (Fin (k+1))), ‖u‖ = 1 ∧ U ⊆ positiveSupport f u ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  have hdiff : (I \ U).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hUI,hI,hU]
    omega
  obtain ⟨i,hi⟩ := hdiff
  have hiI := (Finset.mem_sdiff.mp hi).1
  have hiU := (Finset.mem_sdiff.mp hi).2
  let b : Fin (k+1) ≃ ↥I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let a : Fin (k+1) ≃ ↥I := (Equiv.swap 0 (b.symm ⟨i,hiI⟩)).trans b
  have ha : (a 0).val = i := by simp [a]
  obtain ⟨u,hu,hup,hnot⟩ := hf.no_free_indexed_facet hk hdim hn a hmax hw hwi
  refine ⟨u,hu,?_,hnot⟩
  intro j hj
  obtain ⟨l,hl⟩ := a.surjective ⟨j,hUI hj⟩
  have hlj : (a l).val = j := congrArg Subtype.val hl
  have hl0 : l ≠ 0 := by
    intro hl0
    rw [hl0,ha] at hlj
    exact hiU (hlj ▸ hj)
  obtain ⟨q,rfl⟩ := Fin.eq_succ_of_ne_zero hl0
  rw [← hlj]
  exact (mem_positiveSupport f u _).mpr (hup q)
end NoFreeRidge
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section SupportIncidence
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
def SupportFace (f : V → ι → ℝ) (S : Finset ι) : Prop :=
  ∃ u : V, ‖u‖ = 1 ∧ S ⊆ positiveSupport f u
omit [InnerProductSpace ℝ V] [DecidableEq ι] in
lemma SupportFace.mono {f : V → ι → ℝ} {S U : Finset ι} (h : SupportFace f S) (hUS : U ⊆ S) : SupportFace f U := by
  obtain ⟨u,hu,hSu⟩ := h
  exact ⟨u,hu,hUS.trans hSu⟩
end SupportIncidence
lemma exists_unit_orthogonal_dim {k n : ℕ} (hn : n < k) (v : Fin n → Euc (Fin k)) :
    ∃ w : Euc (Fin k), ‖w‖ = 1 ∧ ∀ i, ⟪v i,w⟫ = 0 := by
  classical
  let W : Submodule ℝ (Euc (Fin k)) := Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro he
    have hh := finrank_le_of_span_eq_top he
    have hd : Module.finrank ℝ (Euc (Fin k)) = k := by simp
    rw [hd,Fintype.card_fin] at hh
    omega
  have hO : Wᗮ ≠ ⊥ := fun he => hW (Submodule.orthogonal_eq_bot_iff.mp he)
  obtain ⟨w,hw,hwne⟩ := (Submodule.ne_bot_iff Wᗮ).mp hO
  refine ⟨(‖w‖⁻¹ : ℝ) • w,norm_smul_inv_norm hwne,?_⟩
  intro i
  rw [inner_smul_right,Submodule.inner_right_of_mem_orthogonal
    (show v i ∈ W from Submodule.subset_span (Set.mem_range_self i)) hw,mul_zero]
lemma Admissible.exists_label_absent_dim {k n : ℕ} {ι : Type*} [Fintype ι]
    {f : Euc (Fin k) → ι → ℝ} (hf : Admissible f) (hn : n < k)
    (v : Fin n → Euc (Fin k)) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ i, ∀ j, i ∉ positiveSupport f (v j) := by
  obtain ⟨w,hw,hvw⟩ := exists_unit_orthogonal_dim hn v
  obtain ⟨i,hi⟩ := hf.support_nonempty hw
  exact ⟨i,fun j hj => Finset.disjoint_left.mp (hf.disjoint_supports (hv j) hw (hvw j)) hj hi⟩
section SixPure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.support_card_three_le_of_card {f : (Euc (Fin 3)) → ι → ℝ}
    (hf : Admissible f) (hcard : Fintype.card ι = 6) {u : (Euc (Fin 3))} (hu : ‖u‖ = 1) :
    (positiveSupport f u).card ≤ 3 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 2 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl,hcard] at hb
  omega
lemma Admissible.support_extends_three_of_card {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {w : (Euc (Fin 3))} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 3 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  have hl := hf.support_card_three_le_of_card hcard hu
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  have hb := hf.maximal_support_complement_bound (k := 2) hdim (by omega) hu hm
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [Fintype.card_coe,Finset.card_compl,hcard,hc] at hb
  exact ⟨u,hu,hwu,by omega⟩
lemma Admissible.face_extends_three {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hU : SupportFace f U) :
    ∃ I : Finset ι, I.card = 3 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_three_of_card hcard hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩
lemma Admissible.triangle_no_free_edge {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {I U : Finset ι} (hIc : I.card = 3)
    (hIf : SupportFace f I) (hUI : U ⊆ I) (hUc : U.card = 2) :
    ∃ I' : Finset ι, I'.card = 3 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : (Euc (Fin 3))) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_three_le_of_card hcard hu)).symm
  have hcomp : (Iᶜ : Finset ι).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,hcard,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset ι) := hcomp.to_subtype
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 2) (by decide) hdim (by omega) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_three hcard (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end SixPure
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section TenPure
lemma Admissible.face_extends_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {U : Finset (Fin 10)} (hU : SupportFace f U) :
    ∃ I : Finset (Fin 10), I.card = 4 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_four hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩
lemma Admissible.tetra_no_free_triangle {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {I U : Finset (Fin 10)} (hIc : I.card = 4) (hIf : SupportFace f I)
    (hUI : U ⊆ I) (hUc : U.card = 3) :
    ∃ I' : Finset (Fin 10), I'.card = 4 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : Vector4) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_four_le hu)).symm
  have hcomp : (Iᶜ : Finset (Fin 10)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,Fintype.card_fin,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset (Fin 10)) := hcomp.to_subtype
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 3) (by decide) (by decide) (by decide) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_four (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end TenPure
end
section
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section TwoLabels
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.sum_two_labels {f : V → ι → ℝ} (hf : Admissible f)
    {u : V} (hu : ‖u‖ = 1) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ l, l ≠ i → l ≠ j → f u l = 0) : f u i + f u j = 1 := by
  have hsum : ∑ l, f u l = ∑ l ∈ ({i,j} : Finset ι), f u l :=
    (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => hzero l (by aesop) (by aesop))).symm
  simpa only [Finset.sum_pair hij] using hsum.symm.trans (hf.sum_one u hu)
lemma Admissible.two_labels_meet {f : V → ι → ℝ} (hf : Admissible f)
    (W : Submodule ℝ V) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ u ∈ W, ‖u‖ = 1 → ∀ l, l ≠ i → l ≠ j → f u l = 0)
    {u v : V} (huW : u ∈ W) (hu : ‖u‖ = 1) (hui : 0 < f u i)
    (hvW : v ∈ W) (hv : ‖v‖ = 1) (hvj : 0 < f v j) :
    ∃ w : V, ‖w‖ = 1 ∧ 0 < f w i ∧ 0 < f w j := by
  classical
  by_contra hn
  have hnot (w : V) (hw : ‖w‖ = 1) : ¬ (0 < f w i ∧ 0 < f w j) := fun hh => hn ⟨w,hw,hh⟩
  have hui' : f u i = 1 := by
    have hj0 : f u j = 0 := le_antisymm (not_lt.mp (fun hp => hnot u hu ⟨hui,hp⟩)) (hf.nonneg u hu j)
    have hh := hf.sum_two_labels hu hij (hzero u huW hu)
    linarith
  have hvi : f v i = 0 := le_antisymm (not_lt.mp (fun hp => hnot v hv ⟨hp,hvj⟩)) (hf.nonneg v hv i)
  obtain ⟨v',hv'W,hv',hv'i,hinner⟩ : ∃ v' : V, v' ∈ W ∧ ‖v'‖ = 1 ∧ f v' i = 0 ∧ 0 ≤ ⟪u,v'⟫ := by
    by_cases hi : 0 ≤ ⟪u,v⟫
    · exact ⟨v,hvW,hv,hvi,hi⟩
    · exact ⟨-v,W.neg_mem hvW,by simpa using hv,by simpa only [hf.antipodal] using hvi,by simp only [inner_neg_right]; linarith⟩
  let p : ℝ → V := fun t => (1-t) • u + t • v'
  have hp : Continuous p := ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have hpW (t : ℝ) : p t ∈ W := W.add_mem (W.smul_mem _ huW) (W.smul_mem _ hv'W)
  have hpz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : p t ≠ 0 := by
    intro hz
    have hi := congrArg (fun x : V => ⟪u,x⟫) hz
    have hi' : (1-t)+t*⟪u,v'⟫ = 0 := by
      simpa only [p,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one,inner_zero_right] using hi
    have ht1 : t = 1 := by nlinarith [ht.2,mul_nonneg ht.1 hinner]
    have hv0 : v' = 0 := by simpa only [p,ht1,sub_self,zero_smul,one_smul,zero_add] using hz
    simp [hv0] at hv'
  let q : ℝ → V := fun t => unitRadial (p t)
  have hq : ContinuousOn q (Icc (0:ℝ) 1) :=
    (unitRadial_continuousOn (S := p '' Icc (0:ℝ) 1) (by rintro x ⟨t,ht,rfl⟩; exact hpz t ht)).comp hp.continuousOn (fun t ht => ⟨t,ht,rfl⟩)
  have hqn (t) (ht : t ∈ Icc (0:ℝ) 1) : ‖q t‖ = 1 := unitRadial_norm (hpz t ht)
  have hqW (t) : q t ∈ W := W.smul_mem _ (hpW t)
  have hq0 : q 0 = u := by simp only [q,p,sub_zero,one_smul,zero_smul,add_zero,unitRadial,hu,inv_one,one_smul]
  have hq1 : q 1 = v' := by simp only [q,p,sub_self,zero_smul,one_smul,zero_add,unitRadial,hv',inv_one,one_smul]
  have hcont : ContinuousOn (fun t => f (q t) i) (Icc (0:ℝ) 1) := (hf.smooth i).continuous.comp_continuousOn hq
  have hhalf : (1/2 : ℝ) ∈ Icc (f (q 1) i) (f (q 0) i) := by rw [hq0,hq1,hui',hv'i]; constructor <;> norm_num
  obtain ⟨t,ht,hth⟩ := intermediate_value_Icc' (zero_le_one : (0:ℝ) ≤ 1) hcont hhalf
  have hsum := hf.sum_two_labels (hqn t ht) hij (hzero (q t) (hqW t) (hqn t ht))
  exact hnot (q t) (hqn t ht) ⟨by linarith,by linarith⟩
end TwoLabels
end
end
section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section AllPairs
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.all_pairs {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    ∃ u : (Euc ν), ‖u‖ = 1 ∧ 0 < f u i ∧ 0 < f u j := by
  classical
  let y : ι → ℝ := fun l => if l = i ∨ l = j then 1 else -1
  have hy : y ≠ 0 := by intro h; have hi := congrFun h i; simp [y] at hi
  obtain ⟨A,hA,t,ht,hAt⟩ := hf.signedExtension_ray hdim hy
  have hai : 0 < signedExtension f A i := by rw [hAt]; simpa [y] using ht
  have haj : 0 < signedExtension f A j := by rw [hAt]; simpa [y] using ht
  obtain ⟨u,huW,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hai
  obtain ⟨v,hvW,hv,hvj⟩ := (hf.signedExtension_positive_support A j).mp haj
  apply hf.two_labels_meet (LinearMap.range ((matrixOp ν) A⁺).toLinearMap) hij ?_ huW hu hui hvW hv hvj
  intro w hw hwn l hli hlj
  apply hf.signedExtension_range_labels (I := {i,j}) ?_ hw hwn (by simp [hli,hlj])
  intro l hl
  have hli : l ≠ i := by aesop
  have hlj : l ≠ j := by aesop
  rw [hAt]
  simp only [Pi.smul_apply,smul_eq_mul,y,if_neg (not_or.mpr ⟨hli,hlj⟩),mul_neg_one]
  linarith
end AllPairs
end
namespace SixCounting
variable {α : Type*} [DecidableEq α]
noncomputable local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
noncomputable def triangles (C : Finset α) (T : Finset α → Prop) : Finset (Finset α) :=
  (C.powersetCard 3).filter T
omit [DecidableEq α] in
@[simp] lemma mem_triangles {C U : Finset α} {T : Finset α → Prop} :
    U ∈ triangles C T ↔ U ⊆ C ∧ U.card = 3 ∧ T U := by
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]
lemma pair_incidence_count (C : Finset α) (T : Finset α → Prop) :
    ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card =
      3 * (triangles C T).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    ∑ U ∈ triangles C T, ∑ P ∈ C.powersetCard 2, (if P ⊆ U then (1 : ℕ) else 0) =
        ∑ U ∈ triangles C T, (U.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [← Finset.card_filter]
      congr 1
      ext P
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨fun h => ⟨h.2, h.1.2⟩,
        fun h => ⟨⟨h.1.trans (mem_triangles.mp hU).1, h.2⟩, h.1⟩⟩
    _ = 3 * (triangles C T).card := by
      have he : ∀ U ∈ triangles C T, (U.powersetCard 2).card = 3 := by
        intro U hU
        rw [Finset.card_powersetCard, (mem_triangles.mp hU).2.1]
        decide
      rw [Finset.sum_congr rfl he]
      simp [mul_comm]
lemma complement_triangle {C U : Finset α} (hC : C.card = 6)
    (hU : U ∈ C.powersetCard 3) : C \ U ∈ C.powersetCard 3 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hU).1,
    hC, (Finset.mem_powersetCard.mp hU).2]
lemma triangle_count_upper {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U)) :
    (triangles C T).card ≤ 10 := by
  classical
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have hc : A.card ≤ B.card := calc
    A.card = (A.image (fun U => C \ U)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ B.card := Finset.card_le_card hi
  have hB : B.card = 20 - A.card := by
    rw [Finset.card_sdiff_of_subset hA, Finset.card_powersetCard, hC]
    norm_num [Nat.choose]
  change A.card ≤ 10
  omega
lemma triangle_count_eq_ten {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card) :
    (triangles C T).card = 10 := by
  have hupper := triangle_count_upper hC hdisj
  have hlower : 30 ≤ ∑ P ∈ C.powersetCard 2,
      ((triangles C T).filter (P ⊆ ·)).card := by
    calc
      30 = ∑ _P ∈ C.powersetCard 2, 2 := by
        norm_num [Finset.card_powersetCard, hC, Nat.choose]
      _ ≤ _ := Finset.sum_le_sum hpairs
  rw [pair_incidence_count] at hlower
  omega
lemma pair_degree_eq_two {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {P : Finset α} (hP : P ∈ C.powersetCard 2) :
    ((triangles C T).filter (P ⊆ ·)).card = 2 := by
  have hsum : (∑ _P ∈ C.powersetCard 2, 2) =
      ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card := by
    rw [pair_incidence_count, triangle_count_eq_ten hC hdisj hpairs]
    norm_num [Finset.card_powersetCard, hC, Nat.choose]
  exact ((Finset.sum_eq_sum_iff_of_le hpairs).mp hsum P hP).symm
lemma complementary_iff {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {U : Finset α} (hU : U ∈ C.powersetCard 3) : T U ↔ ¬T (C \ U) := by
  classical
  refine ⟨hdisj U hU, ?_⟩
  intro hn
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have he : A.image (fun U => C \ U) = B := by
    apply Finset.eq_of_subset_of_card_le hi
    rw [Finset.card_image_of_injOn hinj, Finset.card_sdiff_of_subset hA,
      Finset.card_powersetCard, hC]
    change Nat.choose 6 3 - (triangles C T).card ≤ (triangles C T).card
    rw [triangle_count_eq_ten hC hdisj hpairs]
    decide
  have hcU : C \ U ∈ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC hU, ?_⟩
    intro hh
    exact hn (mem_triangles.mp hh).2.2
  rw [← he] at hcU
  obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hcU
  have hEq : V = U := by
    have hh := congrArg (fun W => C \ W) hVU
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp hU).1] using hh
  exact hEq ▸ (mem_triangles.mp hV).2.2
end SixCounting
end
section
open Set MeasureTheory
section
open scoped Classical
open scoped RealInnerProductSpace
section SixFaces
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.six_complement_exclusion {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    {U : Finset ι} (hU : SupportFace f U) : ¬ SupportFace f Uᶜ := by
  classical
  rintro ⟨v,hv,hUv⟩
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 2) (by decide) ![u,v] (by
    intro j
    fin_cases j <;> simp [hu,hv])
  by_cases h : i ∈ U
  · exact hi 0 (hUu h)
  · exact hi 1 (hUv (Finset.mem_compl.mpr h))
lemma Admissible.six_pair_lower {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
  classical
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hPc
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hui,huj⟩ := hf.all_pairs hdim hij
  have hpair : SupportFace f {i,j} := ⟨u,hu,by
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact (mem_positiveSupport _ _ _).mpr hui
    · exact (mem_positiveSupport _ _ _).mpr huj⟩
  obtain ⟨I,hIc,hIf,hPI⟩ := hf.face_extends_three hcard hpair
  obtain ⟨I',hI'c,hI'f,hPI',hne⟩ := hf.triangle_no_free_edge hcard hIc hIf hPI (by simp [hij])
  have hsub : {I,I'} ⊆ (SixCounting.triangles Finset.univ (SupportFace f)).filter ({i,j} ⊆ ·) := by
    intro J hJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hIc,hIf⟩,hPI⟩
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hI'c,hI'f⟩,hPI'⟩
  have hc := Finset.card_le_card hsub
  simpa [hne.symm] using hc
lemma Admissible.six_complementary {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hUc : U.card = 3) :
    SupportFace f U ↔ ¬ SupportFace f Uᶜ := by
  classical
  have hC : (Finset.univ : Finset ι).card = 6 := by simpa using hcard
  have hd : ∀ U ∈ (Finset.univ : Finset ι).powersetCard 3,
      SupportFace f U → ¬ SupportFace f (Finset.univ \ U) := by
    intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  have hp : ∀ P ∈ (Finset.univ : Finset ι).powersetCard 2,
      2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
    intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
  simpa only [← Finset.compl_eq_univ_sdiff] using SixCounting.complementary_iff hC hd hp
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ U,hUc⟩)
lemma Admissible.six_pair_degree {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card = 2 := by
  classical
  apply SixCounting.pair_degree_eq_two
    (C := Finset.univ) (by simpa using hcard) ?_ ?_ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hPc⟩)
  · intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  · intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
end SixFaces
lemma pair_triangle_card {α : Type*} [DecidableEq α] (C P : Finset α) (T : Finset α → Prop)
    (hPC : P ⊆ C) (hPc : P.card = 2) :
    (SixCounting.triangles C T |>.filter (P ⊆ ·)).card =
      ((C \ P).filter (fun w => T (insert w P))).card := by
  classical
  symm
  apply Finset.card_bij (fun w _ => insert w P)
  · intro w hw
    obtain ⟨hw,hT⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwC,hwP⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr
      ⟨Finset.insert_subset hwC hPC,by rw [Finset.card_insert_of_notMem hwP,hPc],hT⟩,Finset.subset_insert _ _⟩
  · intro w hw v hv he
    have hwP := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    have hm : w ∈ insert v P := he ▸ Finset.mem_insert_self w P
    exact (Finset.mem_insert.mp hm).resolve_right hwP
  · intro U hU
    obtain ⟨hU,hPU⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUC,hUc,hT⟩ := SixCounting.mem_triangles.mp hU
    have hd : (U \ P).card = 1 := by rw [Finset.card_sdiff_of_subset hPU,hUc,hPc]
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hd
    have hwm : w ∈ U \ P := by rw [hw]; simp
    obtain ⟨hwU,hwP⟩ := Finset.mem_sdiff.mp hwm
    have he : insert w P = U := by
      have hh := Finset.sdiff_union_of_subset hPU
      simpa only [hw,Finset.singleton_union] using hh
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hUC hwU,hwP⟩,he ▸ hT⟩,he⟩
lemma Admissible.six_pair_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : Euc (Fin 3) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((Pᶜ : Finset ι).filter (fun w => SupportFace f (insert w P))).card = 2 := by
  classical
  rw [Finset.compl_eq_univ_sdiff,← pair_triangle_card _ _ _ (Finset.subset_univ P) hPc]
  exact hf.six_pair_degree hcard hPc
end
end
section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
open scoped Classical
section Within
variable {α : Type*} [DecidableEq α]
noncomputable def withinLabels (C U : Finset α) : Finset C := U.subtype (· ∈ C)
@[simp] lemma mem_withinLabels {C U : Finset α} {i : C} :
    i ∈ withinLabels C U ↔ i.val ∈ U := Finset.mem_subtype
lemma withinLabels_card {C U : Finset α} (hUC : U ⊆ C) : (withinLabels C U).card = U.card := by
  rw [withinLabels,Finset.card_subtype,Finset.filter_true_of_mem]
  exact fun _ hi => hUC hi
lemma withinLabels_compl (C U : Finset α) :
    withinLabels C (C \ U) = (withinLabels C U)ᶜ := by
  ext i
  simp [i.property]
lemma withinLabels_insert (C U : Finset α) (i : C) :
    withinLabels C (insert i.val U) = insert i (withinLabels C U) := by
  ext j
  simp only [mem_withinLabels,Finset.mem_insert,Subtype.ext_iff]
end Within
section FacetSix
variable {f : Vector4 → Fin 10 → ℝ}
lemma Admissible.facet_complement_exclusion (hf : Admissible f) {S U : Finset (Fin 10)}
    (hS : SupportFace f S) (hU : SupportFace f U) : ¬ SupportFace f (Sᶜ \ U) := by
  classical
  rintro ⟨v,hv,hCv⟩
  obtain ⟨w,hw,hSw⟩ := hS
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 3) (by decide) ![w,u,v] (by
    intro j
    fin_cases j <;> simp [hw,hu,hv])
  by_cases hiS : i ∈ S
  · exact hi 0 (hSw hiS)
  by_cases hiU : i ∈ U
  · exact hi 1 (hUu hiU)
  exact hi 2 (hCv (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hiS,hiU⟩))
lemma restricted_face_image {C U : Finset (Fin 10)} (hUC : U ⊆ C)
    (e : Euc (Fin 3) →ₗᵢ[ℝ] Vector4)
    (hU : SupportFace (fun x (i : C) => f (e x) i.val) (withinLabels C U)) :
    SupportFace f U := by
  obtain ⟨x,hx,hUx⟩ := hU
  refine ⟨e x,by simpa using hx,?_⟩
  intro i hi
  exact (mem_positiveSupport _ _ _).mpr ((mem_positiveSupport _ _ (⟨i,hUC hi⟩ : C)).mp
    (hUx (mem_withinLabels.mpr hi)))
lemma Admissible.facet_six_properties (hf : Admissible f) {S : Finset (Fin 10)}
    (hSc : S.card = 4) (hSf : SupportFace f S) :
    (∀ U ⊆ Sᶜ, U.card = 3 → (SupportFace f U ↔ ¬ SupportFace f (Sᶜ \ U))) ∧
    (∀ P ⊆ Sᶜ, P.card = 2 →
      ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card = 2) := by
  classical
  obtain ⟨w,hw,hSw⟩ := hSf
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hw
  let C : Finset (Fin 10) := Sᶜ
  let g : Euc (Fin 3) → C → ℝ := fun x i => f (e x) i.val
  have hCc : C.card = 6 := by dsimp [C]; rw [Finset.card_compl,Fintype.card_fin,hSc]
  have hcard : Fintype.card C = 6 := by simpa using hCc
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ C, f (e x) i = 0 := by
    intro x hx i hi
    have hiS : i ∈ S := by simpa [C] using hi
    have hwpos : 0 < f w i := (mem_positiveSupport _ _ _).mp (hSw hiS)
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal w (e x) hw
      (by simpa using hx) (he x) i ⟨hwpos,hp⟩)) (hf.nonneg _ (by simpa using hx) i)
  have hg : Admissible g := (hf.comp_isometry e).restrict_labels C hzero
  have hmap {U : Finset (Fin 10)} (hUC : U ⊆ C) :
      SupportFace g (withinLabels C U) → SupportFace f U := restricted_face_image hUC e
  have hfaces {U : Finset (Fin 10)} (hUC : U ⊆ C) (hUc : U.card = 3) :
      SupportFace g (withinLabels C U) ↔ SupportFace f U := by
    refine ⟨hmap hUC,?_⟩
    intro hU
    apply (hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])).mpr
    rw [← withinLabels_compl]
    intro hcomp
    exact hf.facet_complement_exclusion ⟨w,hw,hSw⟩ hU (hmap Finset.sdiff_subset hcomp)
  constructor
  · intro U hUC hUc
    have hcUc : (C \ U).card = 3 := by rw [Finset.card_sdiff_of_subset hUC,hCc,hUc]
    rw [← hfaces hUC hUc,← hfaces Finset.sdiff_subset hcUc,withinLabels_compl]
    exact hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])
  · intro P hPC hPc
    let P' := withinLabels C P
    have hP'c : P'.card = 2 := by rw [withinLabels_card hPC,hPc]
    have hinsert {i : C} (hi : i ∉ P') :
        SupportFace g (insert i P') ↔ SupportFace f (insert i.val P) := by
      have hiP : i.val ∉ P := by simpa only [P',mem_withinLabels] using hi
      have hh := hfaces (Finset.insert_subset i.property hPC)
        (by rw [Finset.card_insert_of_notMem hiP,hPc])
      simpa only [withinLabels_insert] using hh
    have hc := hg.six_pair_count hcard hP'c
    have hcount : ((P'ᶜ).filter (fun i => SupportFace g (insert i P'))).card =
        ((C \ P).filter (fun i => SupportFace f (insert i P))).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        obtain ⟨hiP,hif⟩ := Finset.mem_filter.mp hi
        have hiP' := Finset.mem_compl.mp hiP
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨i.property,by
          simpa only [P',mem_withinLabels] using hiP'⟩,(hinsert hiP').mp hif⟩
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro i hi
        obtain ⟨hiC,hif⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiC,hiP⟩ := Finset.mem_sdiff.mp hiC
        have hiP' : (⟨i,hiC⟩ : C) ∉ P' := by simpa only [P',mem_withinLabels] using hiP
        exact ⟨⟨i,hiC⟩,Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hiP',(hinsert hiP').mpr hif⟩,rfl⟩
    exact hcount.symm.trans hc
end FacetSix
end
end
section
open Set MeasureTheory
namespace FiniteObstruction
abbrev Labels := Fin 10
abbrev Family := Finset Labels → Prop
open scoped Classical
structure TenSystem (T Q : Family) : Prop where
  tetra_card : ∀ S, Q S → S.card = 4
  down : ∀ S U, Q S → U ⊆ S → U.card = 3 → T U
  pure : ∀ U, T U → ∃ S, Q S ∧ U ⊆ S
  no_boundary : ∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S
  complementary : ∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))
  pair_count : ∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2
variable {T Q : Family}
@[simp] lemma map_compl (e : Equiv.Perm Labels) (S : Finset Labels) :
    Sᶜ.map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext x
  simp
@[simp] lemma map_symm_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x
  simp
@[simp] lemma symm_map_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x
  simp
end FiniteObstruction
end
section
open Set MeasureTheory
section
open scoped Classical
theorem Admissible.support_ten_system {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f) :
    FiniteObstruction.TenSystem (fun U => U.card = 3 ∧ SupportFace f U)
      (fun S => S.card = 4 ∧ SupportFace f S) := by
  classical
  constructor
  · intro S hS
    exact hS.1
  · intro S U hS hUS hUc
    exact ⟨hUc,hS.2.mono hUS⟩
  · intro U hU
    obtain ⟨S,hSc,hSf,hUS⟩ := hf.face_extends_four hU.2
    exact ⟨S,⟨hSc,hSf⟩,hUS⟩
  · intro S U hS hUS hUc
    obtain ⟨S',hS'c,hS'f,hUS',hne⟩ := hf.tetra_no_free_triangle hS.1 hS.2 hUS hUc
    exact ⟨S',⟨hS'c,hS'f⟩,hUS',hne⟩
  · intro S U hS hUC hUc
    have hCc : (Sᶜ \ U).card = 3 := by
      rw [Finset.card_sdiff_of_subset hUC,Finset.card_compl,Fintype.card_fin,hS.1,hUc]
    simpa only [hUc,hCc,true_and] using (hf.facet_six_properties hS.1 hS.2).1 U hUC hUc
  · intro S P hS hPC hPc
    trans ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card
    · apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro support_mem
        exact ⟨support_mem.1, support_mem.2.2⟩
      · intro support_mem
        refine ⟨support_mem.1, ⟨?_, support_mem.2⟩⟩
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp support_mem.1).2, hPc]
    · exact (hf.facet_six_properties hS.1 hS.2).2 P hPC hPc
end
end
end OAI.BorsukNine
namespace OAI.BorsukNine
open scoped RealInnerProductSpace
theorem input_projector_cover (U : Fin 10 → Set Vector4)
    (hc : ∀ x, ‖x‖ = 1 → ∃ i, x ∈ U i)
    (hb : ∀ i, ∃ b : ℝ, b < 2 ∧ ∀ x ∈ U i, ∀ y ∈ U i,
      ‖x‖ = 1 → ‖y‖ = 1 → 2*(1-⟪x,y⟫^2) ≤ b) : HasTenSmallCover := by
  let C (i : Fin 10) : Set Matrix4 := projector '' (U i ∩ {x : Vector4 | ‖x‖=1})
  refine ⟨C, ?_, ?_, ?_⟩
  · rintro i _ ⟨x,hx,rfl⟩
    exact ⟨x,hx.2,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := hc x hx
    exact Set.mem_iUnion.mpr ⟨i,x,⟨hi,hx⟩,rfl⟩
  · intro i
    obtain ⟨b,hs,hd⟩ := hb i
    refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg (max b 0)) ?_)
      (Real.sqrt_lt_sqrt (by positivity) (max_lt hs (by norm_num)))
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    have hn := hd x hx.1 y hy.1 hx.2 hy.2
    have hsq := projector_dist_sq x y hx.2 hy.2
    have hroot := Real.sq_sqrt (le_max_right b 0)
    nlinarith [le_max_left b 0,Real.sqrt_nonneg (max b 0), dist_nonneg (x:=projector x) (y:=projector y)]
end OAI.BorsukNine
open OAI.BorsukNine
theorem OMA.L2 : OMA.R11.H2 := by
  classical
  intro U hcov hsmall
  obtain ⟨f,hf⟩ := cover_to_admissible (input_projector_cover U hcov hsmall)
  let T (s : Finset (Fin 10)) := s.card=3 ∧ SupportFace f s
  let Q (s : Finset (Fin 10)) := s.card=4 ∧ SupportFace f s
  have h := hf.support_ten_system
  have hempty : SupportFace f ∅ :=
    ⟨EuclideanSpace.single 0 1,by simp,Finset.empty_subset _⟩
  obtain ⟨s,hs,hface,_⟩ := hf.face_extends_four hempty
  exact ⟨T,Q,⟨h.tetra_card,h.down,h.pure,h.no_boundary,h.complementary,h.pair_count⟩,s,hs,hface⟩
end W2

namespace W3
namespace OAI
open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
abbrev Labels := Fin 10
abbrev Family := Finset Labels → Prop
open scoped Classical
structure TenSystem (T Q : Family) : Prop where
  tetra_card : ∀ S, Q S → S.card = 4
  down : ∀ S U, Q S → U ⊆ S → U.card = 3 → T U
  pure : ∀ U, T U → ∃ S, Q S ∧ U ⊆ S
  no_boundary : ∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S
  complementary : ∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))
  pair_count : ∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2
variable {T Q : Family}
lemma filter_card_eq_two_three_pos {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hs : s.card = 4) (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, p x := by
  by_contra hn
  have hsub : s.filter p ⊆ s \ r := by
    intro x hx
    obtain ⟨hxs, hpx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨hxs, ?_⟩
    intro hxr
    exact hn ⟨x, hxr, hpx⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hrs, hs, hr, hp] at hc
  norm_num at hc
lemma filter_card_eq_two_three_neg {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, ¬ p x := by
  by_contra hn
  have hsub : r ⊆ s.filter p := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨hrs hx, ?_⟩
    by_contra hnp
    exact hn ⟨x, hx, hnp⟩
  have hc := Finset.card_le_card hsub
  rw [hr, hp] at hc
  norm_num at hc
lemma three_pos (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, T (insert w P) := by
  classical
  apply filter_card_eq_two_three_pos (s := Sᶜ \ P) (r := R) ?_ hcR hR
    (h.pair_count S P hS hP hcP)
  rw [Finset.card_sdiff_of_subset hP, Finset.card_compl, h.tetra_card S hS, hcP]
  decide
lemma three_neg (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, ¬ T (insert w P) := by
  classical
  exact filter_card_eq_two_three_neg hcR hR (h.pair_count S P hS hP hcP)
lemma tetra_extension {S U : Finset Labels} (hU : U ⊆ S)
    (hcS : S.card = 4) (hcU : U.card = 3) :
    ∃ v, v ∉ U ∧ S = insert v U := by
  have hcard : (S \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hU, hcS, hcU]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hm : v ∈ S \ U := by rw [hv]; simp
  refine ⟨v, (Finset.mem_sdiff.mp hm).2, ?_⟩
  have he := Finset.sdiff_union_of_subset hU
  rw [hv] at he
  simpa using he.symm
@[simp] lemma map_compl (e : Equiv.Perm Labels) (S : Finset Labels) :
    Sᶜ.map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext x
  simp
@[simp] lemma map_symm_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x
  simp
@[simp] lemma symm_map_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x
  simp
lemma TenSystem.relabel (h : TenSystem T Q) (e : Equiv.Perm Labels) :
    TenSystem (fun U => T (U.map e.toEmbedding))
      (fun S => Q (S.map e.toEmbedding)) := by
  constructor
  · intro S hS
    simpa using h.tetra_card _ hS
  · intro S U hS hUS hcU
    exact h.down _ _ hS (Finset.map_subset_map.mpr hUS) (by simpa using hcU)
  · intro U hU
    obtain ⟨S, hS, hUS⟩ := h.pure _ hU
    refine ⟨S.map e.symm.toEmbedding, ?_, ?_⟩
    · simpa using hS
    · have hh := (Finset.map_subset_map (f := e.symm.toEmbedding)).mpr hUS
      simpa using hh
  · intro S U hS hUS hcU
    obtain ⟨S', hS', hUS', hne⟩ := h.no_boundary _ _ hS
      (Finset.map_subset_map.mpr hUS) (by simpa using hcU)
    refine ⟨S'.map e.symm.toEmbedding, ?_, ?_, ?_⟩
    · simpa using hS'
    · have hh := (Finset.map_subset_map (f := e.symm.toEmbedding)).mpr hUS'
      simpa using hh
    · intro he
      have hh := congrArg (Finset.map e.toEmbedding) he
      exact hne (by simpa using hh)
  · intro S U hS hUS hcU
    have hh := h.complementary _ _ hS
      (show U.map e.toEmbedding ⊆ (S.map e.toEmbedding)ᶜ by
        rw [← map_compl]
        exact Finset.map_subset_map.mpr hUS)
      (by simpa using hcU)
    simpa [Finset.map_sdiff] using hh
  · intro S P hS hPS hcP
    have hh := h.pair_count _ _ hS
      (show P.map e.toEmbedding ⊆ (S.map e.toEmbedding)ᶜ by
        rw [← map_compl]
        exact Finset.map_subset_map.mpr hPS)
      (by simpa using hcP)
    rw [← map_compl, ← Finset.map_sdiff, Finset.filter_map, Finset.card_map] at hh
    simpa only [Function.comp_apply, Finset.map_insert] using hh
end BorsukNine.FiniteObstruction
end OAI
namespace BorsukCert
abbrev Lit := ℕ × Bool
def rawAux : ℕ → ℕ → List Lit
  | 0, _ => []
  | k+1, n => if n=0 then [] else
      let u := n%4096-1
      (u/2,decide (u%2=1)) :: rawAux k (n/4096)
def raw := rawAux 25
def Hits (a : ℕ → Bool) (l : Lit) := a l.1 = l.2
def ValidList (a : ℕ → Bool) (ls : List Lit) := ∃ l ∈ ls, Hits a l
abbrev H (a : ℕ → Bool) (c : ℕ) := ValidList a (raw c)
abbrev Checked (a : ℕ → Bool) := {c : ℕ // H a c}
def pack {a : ℕ → Bool} {c : ℕ} (h : H a c) : Checked a := ⟨c,h⟩
def flip (l : Lit) : Lit := (l.1,!l.2)
def code (l : Lit) := 2*l.1 + l.2.toNat
theorem code_inj {l u : Lit} (h : code l = code u) : l = u := by
  obtain ⟨i,b⟩ := l
  obtain ⟨j,d⟩ := u
  cases b <;> cases d <;> simp_all [code,Bool.toNat] <;> omega
def mark (bad : ℕ) (l : Lit) := bad ||| 2^(code l)
theorem marked {bad : ℕ} {l u : Lit} :
    (mark bad u).testBit (code l) = true ↔ bad.testBit (code l) = true ∨ u=l := by
  simp [mark,Nat.testBit_two_pow,show (code u = code l) ↔ u=l from ⟨code_inj,congrArg code⟩]
def initial (ls : List Lit) := ls.foldr (fun l b => mark b l) 0
theorem initial_mem {ls : List Lit} {l : Lit} :
    (initial ls).testBit (code l) = true → l ∈ ls := by
  induction ls with
  | nil => simp [initial]
  | cons u ls ih =>
    intro h
    rcases marked.mp h with hb | rfl
    · exact List.mem_cons_of_mem _ (ih hb)
    · simp
def propagate (bad : ℕ) : List ℕ → Bool
  | [] => false
  | c :: cs =>
    match (raw c).filter (fun l => !bad.testBit (code l)) with
    | [] => true
    | [l] => propagate (mark bad (flip l)) cs
    | _ => false
theorem propagation {a : ℕ → Bool} (cs : List ℕ) (bad : ℕ)
    (hv : ∀ c ∈ cs, H a c) (hf : ∀ l, bad.testBit (code l) = true → ¬Hits a l)
    (ok : propagate bad cs = true) : False := by
  induction cs generalizing bad with
  | nil => simp [propagate] at ok
  | cons c cs ih =>
    obtain ⟨l,hl,ht⟩ := hv c (by simp)
    have hn : bad.testBit (code l) ≠ true := fun hb => hf l hb ht
    have hm : l ∈ (raw c).filter (fun l => !bad.testBit (code l)) := List.mem_filter.mpr ⟨hl,by simpa using hn⟩
    unfold propagate at ok
    split at ok
    next he => rw [he] at hm; exact List.not_mem_nil hm
    next u he =>
      rw [he] at hm
      have eq : l = u := by simpa using hm
      subst u
      apply ih (mark bad (flip l)) (fun k hk => hv k (by simp [hk])) _ ok
      intro x hx hxv
      rcases (marked.mp hx).symm with rfl | hx
      · simp [Hits,flip] at ht hxv
        simp [ht] at hxv
      · exact hf x hx hxv
    next => contradiction
theorem rup {a : ℕ → Bool} {c : ℕ} (xs : List (Checked a))
    (ok : propagate (initial (raw c)) (xs.map Subtype.val) = true) : H a c := by
  by_contra hn
  apply propagation (a := a) (xs.map Subtype.val) (initial (raw c)) _ _ ok
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact x.property
  · intro l hl h
    exact hn ⟨l,initial_mem hl,h⟩
end BorsukCert
open OAI.BorsukNine.FiniteObstruction
namespace BorsukCert
abbrev Face := Finset Labels
local instance : Std.Commutative Nat.lor := ⟨Nat.or_comm⟩
local instance : Std.Associative Nat.lor := ⟨Nat.or_assoc⟩
def bits (s : Face) := s.fold Nat.lor 0 (fun i => 2^i.val)
def face (n : ℕ) : Face := Finset.univ.filter (fun i => n.testBit i.val)
theorem face_bits (s : Face) : face (bits s) = s := by
  ext i
  simp only [face,Finset.mem_filter,Finset.mem_univ,true_and]
  induction s using Finset.induction_on with
  | empty => simp [bits]
  | insert j s hj ih =>
    rw [bits,Finset.fold_insert hj]
    change ((2^j.val ||| bits s).testBit i.val = true) ↔ _
    simp only [Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih,Finset.mem_insert,Fin.val_inj]
    tauto
def lit (tag : Bool) (s : Face) (sign : Bool) : Lit := (2*bits s+tag.toNat,sign)
def family (T Q : Family) (t : Bool) := if t then Q else T
noncomputable def faceValue (T Q : Family) (t : Bool) (s : Face) : Bool :=
  @decide (family T Q t s) (Classical.propDecidable _)
noncomputable def coloring (T Q : Family) (n : ℕ) : Bool :=
  faceValue T Q (decide (n%2=1)) (face (n/2))
theorem hit {T Q : Family} {tag sign : Bool} {s : Face} :
    Hits (coloring T Q) (lit tag s sign) ↔
      (if sign then family T Q tag s else ¬family T Q tag s) := by
  classical
  have d0 : 2 * bits s / 2 = bits s := by omega
  have d1 : (2 * bits s + 1) / 2 = bits s := by omega
  have m0 : 2 * bits s % 2 = 0 := by omega
  have m1 : (2 * bits s + 1) % 2 = 1 := by omega
  cases tag <;> cases sign <;> simp [Hits,coloring,lit,Bool.toNat,d0,d1,m0,m1,face_bits] <;> simp [faceValue,family]
def tailLits (tag sign : Bool) (u w : Face) : List Lit :=
  ((List.finRange 10).filter (fun i => i ∈ w)).map (fun i => lit tag (insert i u) sign)
theorem tail_ok {T Q : Family} {tag sign : Bool} {u w : Face} {i : Labels}
    (hw : i ∈ w) (hh : if sign then family T Q tag (insert i u) else ¬family T Q tag (insert i u)) :
    ValidList (coloring T Q) (tailLits tag sign u w) := by
  refine ⟨_,List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨List.mem_finRange i,by simpa using hw⟩,rfl⟩,hit.mpr hh⟩
def fixed : Face := {0,1,2,3}
def taut : List Lit := [(0,true),(0,false)]
theorem taut_ok (a : ℕ → Bool) : ValidList a taut := by
  cases hb : a 0 with
  | true => exact ⟨(0,true),by decide,hb⟩
  | false => exact ⟨(0,false),by decide,hb⟩
def rule (kind : ℕ) (s u r : Face) : List Lit :=
  match kind with
  | 0 => [lit true fixed true]
  | 1 => if u⊆s ∧ u.card=3 then [lit true s false,lit false u true] else taut
  | 2 => if u⊆s ∧ u.card=3 then lit true s false :: tailLits true true u
      (uᶜ.filter (fun i => insert i u ≠ s)) else taut
  | 3 => if u.card=3 then lit false u false :: tailLits true true u uᶜ else taut
  | 4 => if u⊆sᶜ ∧ u.card=3 then [lit true s false,lit false u true,lit false (sᶜ \ u) true] else taut
  | 5 => if u⊆sᶜ ∧ u.card=3 then [lit true s false,lit false u false,lit false (sᶜ \ u) false] else taut
  | 6 => if u⊆sᶜ ∧ u.card=2 ∧ r⊆sᶜ \ u ∧ r.card=3 then
      lit true s false :: tailLits false true u r else taut
  | _ => if u⊆sᶜ ∧ u.card=2 ∧ r⊆sᶜ \ u ∧ r.card=3 then
      lit true s false :: tailLits false false u r else taut
def seedLits (z : ℕ) := rule (z%8) (face (z/8%1024)) (face (z/8192%1024)) (face (z/8388608%1024))
class Legal (a : ℕ → Bool) : Prop where
  legal : ∀ z, ValidList a (seedLits z)
theorem seed {a : ℕ → Bool} [v : Legal a] {c : ℕ} (z : ℕ) (eq : raw c = seedLits z) : H a c := by
  unfold H
  rw [eq]
  exact v.legal z
end BorsukCert
open OAI.BorsukNine.FiniteObstruction
namespace BorsukCert
theorem valid_cons {a : ℕ → Bool} {l : Lit} {ls : List Lit} :
    ValidList a (l::ls) ↔ Hits a l ∨ ValidList a ls := by
  simp [ValidList]
theorem valid_nil {a : ℕ → Bool} : ¬ValidList a [] := by simp [ValidList]
theorem rule_sound {T Q : Family} (h : TenSystem T Q) (h0 : Q fixed) (k : ℕ) (s u r : Face) :
    ValidList (coloring T Q) (rule k s u r) := by
  classical
  unfold rule
  split
  · simpa [valid_cons,valid_nil,hit,family] using h0
  all_goals split
  all_goals try exact taut_ok _
  all_goals rename_i hc
  all_goals simp only [valid_cons,valid_nil,or_false,hit,Bool.false_eq_true,if_false,if_true,family]
  · by_cases hs : Q s
    · exact Or.inr (h.down _ _ hs hc.1 hc.2)
    · exact Or.inl hs
  · by_cases hs : Q s
    · obtain ⟨v,hv,hus,hne⟩ := h.no_boundary _ _ hs hc.1 hc.2
      obtain ⟨i,hi,rfl⟩ := tetra_extension hus (h.tetra_card v hv) hc.2
      exact Or.inr (tail_ok (i := i) (by simp [hi,hne]) hv)
    · exact Or.inl hs
  · by_cases hu : T u
    · obtain ⟨v,hv,hus⟩ := h.pure _ hu
      obtain ⟨i,hi,rfl⟩ := tetra_extension hus (h.tetra_card v hv) hc
      exact Or.inr (tail_ok (i := i) (by simpa using hi) hv)
    · exact Or.inl hu
  · by_cases hs : Q s
    · have he := h.complementary _ _ hs hc.1 hc.2
      tauto
    · exact Or.inl hs
  · by_cases hs : Q s
    · have he := h.complementary _ _ hs hc.1 hc.2
      tauto
    · exact Or.inl hs
  · by_cases hs : Q s
    · obtain ⟨i,hi,ht⟩ := three_pos h s u r hs hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      exact Or.inr (tail_ok hi ht)
    · exact Or.inl hs
  · by_cases hs : Q s
    · obtain ⟨i,hi,ht⟩ := three_neg h s u r hs hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      exact Or.inr (tail_ok hi ht)
    · exact Or.inl hs
theorem system_legal {T Q : Family} (h : TenSystem T Q) (h0 : Q fixed) : Legal (coloring T Q) :=
  ⟨fun _ => rule_sound h h0 _ _ _ _⟩
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f1 : H a 64 := seed 120 rfl
lemma f2 : H a 122943 := seed 57465 rfl
lemma f3 : H a 0x8204202201200a006003f := seed 57466 rfl
lemma f4 : H a 188479 := seed 90233 rfl
lemma f5 : H a 0x8304302301300b007003f := seed 90234 rfl
lemma f6 : H a 319583 := seed 155833 rfl
lemma f7 : H a 319599 := seed 155865 rfl
lemma f8 : H a 319823 := seed 156313 rfl
lemma f9 : H a 0x8504502500d007006014f := seed 156314 rfl
lemma f10 : H a 320079 := seed 156825 rfl
lemma f11 : H a 581791 := seed 287033 rfl
lemma f12 : H a 581807 := seed 287065 rfl
lemma f13 : H a 581839 := seed 287129 rfl
lemma f14 : H a 582031 := seed 287513 rfl
lemma f15 : H a 582287 := seed 288025 rfl
lemma f16 : H a 582799 := seed 289049 rfl
lemma f17 : H a 583823 := seed 291097 rfl
lemma f18 : H a 0x91051031019015013012010d := seed 548867 rfl
lemma f19 : H a 1106207 := seed 549433 rfl
lemma f20 : H a 1106223 := seed 549465 rfl
lemma f21 : H a 0x91051031019015012012f := seed 549466 rfl
lemma f22 : H a 1106255 := seed 549529 rfl
lemma f23 : H a 0x91051031019013012014f := seed 549530 rfl
lemma f24 : H a 1106319 := seed 549657 rfl
lemma f25 : H a 1107215 := seed 551449 rfl
lemma f26 : H a 0x51031019015013012090f := seed 553498 rfl
lemma f27 : H a 2155039 := seed 1074233 rfl
lemma f28 : H a 2155055 := seed 1074265 rfl
lemma f29 : H a 0xa1061031029025022022f := seed 1074266 rfl
lemma f30 : H a 2155087 := seed 1074329 rfl
lemma f31 : H a 2155151 := seed 1074457 rfl
lemma f32 : H a 4252719 := seed 2123865 rfl
lemma f33 : H a 4252751 := seed 2123929 rfl
lemma f34 : H a 4252815 := seed 2124057 rfl
lemma f35 : H a 4254735 := seed 2127897 rfl
lemma f36 : H a 0xc10a1091089085083082080d := seed 4218883 rfl
lemma f37 : H a 8448031 := seed 4223033 rfl
lemma f38 : H a 8448047 := seed 4223065 rfl
lemma f39 : H a 0xc10a1091089083082084f := seed 4223130 rfl
lemma f40 : H a 0xc10910890850830820a0f := seed 4224026 rfl
lemma f41 : H a 221247 := seed 106617 rfl
lemma f42 : H a 0x8384382381380b807803f := seed 106618 rfl
lemma f43 : H a 0x8584582581580d8078060055 := seed 172035 rfl
lemma f44 : H a 352351 := seed 172217 rfl
lemma f45 : H a 352375 := seed 172265 rfl
lemma f46 : H a 0x8584582581580d8060077 := seed 172266 rfl
lemma f47 : H a 352471 := seed 172457 rfl
lemma f48 : H a 352599 := seed 172713 rfl
lemma f49 : H a 352855 := seed 173225 rfl
lemma f50 : H a 353367 := seed 174249 rfl
lemma f51 : H a 354391 := seed 176297 rfl
lemma f52 : H a 0x8984982981980d80b80a0095 := seed 303107 rfl
lemma f53 : H a 614583 := seed 303465 rfl
lemma f54 : H a 614615 := seed 303529 rfl
lemma f55 : H a 0x8984982980d80b80a0197 := seed 303914 rfl
lemma f56 : H a 615575 := seed 305449 rfl
lemma f57 : H a 616599 := seed 307497 rfl
lemma f58 : H a 0x4982981980d80b80a0897 := seed 307498 rfl
lemma f59 : H a 1138999 := seed 565865 rfl
lemma f60 : H a 0x918518318198158120137 := seed 565866 rfl
lemma f61 : H a 1139031 := seed 565929 rfl
lemma f62 : H a 1139095 := seed 566057 rfl
lemma f63 : H a 1139479 := seed 566825 rfl
lemma f64 : H a 1139991 := seed 567849 rfl
lemma f65 : H a 1141015 := seed 569897 rfl
lemma f66 : H a 0xa18618318298258238220215 := seed 1089539 rfl
lemma f67 : H a 0xa1861831829825823821f := seed 1090618 rfl
lemma f68 : H a 2187831 := seed 1090665 rfl
lemma f69 : H a 2187863 := seed 1090729 rfl
lemma f70 : H a 0xa18618318298238220257 := seed 1090730 rfl
lemma f71 : H a 2187927 := seed 1090857 rfl
lemma f72 : H a 0xa18618318258238220297 := seed 1090858 rfl
lemma f73 : H a 0xa18618298258238220317 := seed 1091114 rfl
lemma f74 : H a 2188823 := seed 1092649 rfl
lemma f75 : H a 0xc18618518498458438420415 := seed 2138115 rfl
lemma f76 : H a 0xc1861851849845843841f := seed 2140218 rfl
lemma f77 : H a 4285495 := seed 2140265 rfl
lemma f78 : H a 4285527 := seed 2140329 rfl
lemma f79 : H a 0xc18618518498438420457 := seed 2140330 rfl
lemma f80 : H a 4285591 := seed 2140457 rfl
lemma f81 : H a 0xc18618518458438420497 := seed 2140458 rfl
lemma f82 : H a 0xc18618498458438420517 := seed 2140714 rfl
lemma f83 : H a 4285975 := seed 2141225 rfl
lemma f84 : H a 0xc18518498458438420617 := seed 2141226 rfl
lemma f85 : H a 4287511 := seed 2144297 rfl
lemma f86 : H a 0x618518498458438420c17 := seed 2144298 rfl
lemma f87 : H a 0xc18a18918898858838820815 := seed 4235267 rfl
lemma f88 : H a 8480799 := seed 4239417 rfl
lemma f89 : H a 0xc18a1891889885883881f := seed 4239418 rfl
lemma f90 : H a 8480823 := seed 4239465 rfl
lemma f91 : H a 0xc18a18918898858820837 := seed 4239466 rfl
lemma f92 : H a 8480855 := seed 4239529 rfl
lemma f93 : H a 0xc18918898858838820a17 := seed 4240426 rfl
lemma f94 : H a 0xa18918898858838820c17 := seed 4241450 rfl
lemma f95 : H a 0x8684682681680e8078070065 := seed 204803 rfl
lemma f96 : H a 417903 := seed 205017 rfl
lemma f97 : H a 0x8684682681680e8070077 := seed 205034 rfl
lemma f98 : H a 418407 := seed 206025 rfl
lemma f99 : H a 0x4682681680e8078070867 := seed 209098 rfl
lemma f100 : H a 681127 := seed 338249 rfl
lemma f101 : H a 0x8a82a81a80e80b80b04a7 := seed 338250 rfl
lemma f102 : H a 0x9285283281a8168138130125 := seed 598019 rfl
lemma f103 : H a 1204527 := seed 598617 rfl
lemma f104 : H a 0x9285283281a8138130167 := seed 598730 rfl
lemma f105 : H a 1204647 := seed 598857 rfl
lemma f106 : H a 1205031 := seed 599625 rfl
lemma f107 : H a 1205543 := seed 600649 rfl
lemma f108 : H a 0x5283281a8168138130927 := seed 602698 rfl
lemma f109 : H a 0xa286283282a8268238230225 := seed 1122307 rfl
lemma f110 : H a 0xa286283282a8268230237 := seed 1123434 rfl
lemma f111 : H a 2253479 := seed 1123657 rfl
lemma f112 : H a 2253607 := seed 1123913 rfl
lemma f113 : H a 0xa286282a8268238230327 := seed 1123914 rfl
lemma f114 : H a 2254375 := seed 1125449 rfl
lemma f115 : H a 0xa283282a8268238230627 := seed 1125450 rfl
lemma f116 : H a 2255399 := seed 1127497 rfl
lemma f117 : H a 0x6283282a8268238230a27 := seed 1127498 rfl
lemma f118 : H a 0xc286285284a8468438430425 := seed 2170883 rfl
lemma f119 : H a 0xc286285284a8468430437 := seed 2173034 rfl
lemma f120 : H a 4351079 := seed 2173129 rfl
lemma f121 : H a 0xc286285284a8438430467 := seed 2173130 rfl
lemma f122 : H a 4351143 := seed 2173257 rfl
lemma f123 : H a 0xc286285284684384304a7 := seed 2173258 rfl
lemma f124 : H a 4351271 := seed 2173513 rfl
lemma f125 : H a 4351527 := seed 2174025 rfl
lemma f126 : H a 4353063 := seed 2177097 rfl
lemma f127 : H a 0xc28a289288a8868838830825 := seed 4268035 rfl
lemma f128 : H a 8546351 := seed 4272217 rfl
lemma f129 : H a 8546359 := seed 4272233 rfl
lemma f130 : H a 0xc28a289288a8868830837 := seed 4272234 rfl
lemma f131 : H a 8546407 := seed 4272329 rfl
lemma f132 : H a 0xc28a289288a8838830867 := seed 4272330 rfl
lemma f133 : H a 0xc28a288a8868838830927 := seed 4272714 rfl
lemma f134 : H a 8546855 := seed 4273225 rfl
lemma f135 : H a 0xc289288a8868838830a27 := seed 4273226 rfl
lemma f136 : H a 0x8c84c82c81c80e80d80d00c5 := seed 401411 rfl
lemma f137 : H a 811215 := seed 401817 rfl
lemma f138 : H a 811239 := seed 401865 rfl
lemma f139 : H a 811463 := seed 402313 rfl
lemma f140 : H a 811719 := seed 402825 rfl
lemma f141 : H a 0x8c84c81c80e80d80d02c7 := seed 402826 rfl
lemma f142 : H a 812231 := seed 403849 rfl
lemma f143 : H a 0x8c82c81c80e80d80d04c7 := seed 403850 rfl
lemma f144 : H a 0x9485483481c8168158150145 := seed 663555 rfl
lemma f145 : H a 0x9485483481c816815814f := seed 664218 rfl
lemma f146 : H a 0x9485483481c8168150157 := seed 664234 rfl
lemma f147 : H a 0x9485483481c8158150167 := seed 664266 rfl
lemma f148 : H a 1335751 := seed 664457 rfl
lemma f149 : H a 0x9485483481681581501c7 := seed 664458 rfl
lemma f150 : H a 1336135 := seed 665225 rfl
lemma f151 : H a 0x9483481c8168158150547 := seed 666250 rfl
lemma f152 : H a 0xa486483482c8268258250245 := seed 1187843 rfl
lemma f153 : H a 2384463 := seed 1189017 rfl
lemma f154 : H a 2384471 := seed 1189033 rfl
lemma f155 : H a 2384487 := seed 1189065 rfl
lemma f156 : H a 2384711 := seed 1189513 rfl
lemma f157 : H a 0xa486482c8268258250347 := seed 1189514 rfl
lemma f158 : H a 0xa483482c8268258250647 := seed 1191050 rfl
lemma f159 : H a 2386503 := seed 1193097 rfl
lemma f160 : H a 0x6483482c8268258250a47 := seed 1193098 rfl
lemma f161 : H a 0xc486485484c8468458450445 := seed 2236419 rfl
lemma f162 : H a 4482247 := seed 2238857 rfl
lemma f163 : H a 0xc486485484684584504c7 := seed 2238858 rfl
lemma f164 : H a 0xc486484c8468458450547 := seed 2239114 rfl
lemma f165 : H a 0xc485484c8468458450647 := seed 2239626 rfl
lemma f166 : H a 0x6485484c8468458450c47 := seed 2242698 rfl
lemma f167 : H a 8677463 := seed 4337833 rfl
lemma f168 : H a 8677479 := seed 4337865 rfl
lemma f169 : H a 8677959 := seed 4338825 rfl
lemma f170 : H a 0x9885883881c81a8198190185 := seed 794627 rfl
lemma f171 : H a 0x9885881c81a8198190387 := seed 796426 rfl
lemma f172 : H a 1598855 := seed 797449 rfl
lemma f173 : H a 0xa886883882c82a8298290285 := seed 1318915 rfl
lemma f174 : H a 0xa886883882a82982902c7 := seed 1320330 rfl
lemma f175 : H a 0xa886882c82a8298290387 := seed 1320714 rfl
lemma f176 : H a 0x6883882c82a8298290a87 := seed 1324298 rfl
lemma f177 : H a 0xc886885884c84a8498490485 := seed 2367491 rfl
lemma f178 : H a 0xc886885884c84a849848f := seed 2369818 rfl
lemma f179 : H a 0xc886885884c84a8490497 := seed 2369834 rfl
lemma f180 : H a 4744359 := seed 2369865 rfl
lemma f181 : H a 0xc886885884c84984904a7 := seed 2369866 rfl
lemma f182 : H a 4744391 := seed 2369929 rfl
lemma f183 : H a 0xc886885884a84984904c7 := seed 2369930 rfl
lemma f184 : H a 4744583 := seed 2370313 rfl
lemma f185 : H a 0xc886884c84a8498490587 := seed 2370314 rfl
lemma f186 : H a 0xc885884c84a8498490687 := seed 2370826 rfl
lemma f187 : H a 4746375 := seed 2373897 rfl
lemma f188 : H a 0x6885884c84a8498490c87 := seed 2373898 rfl
lemma f189 : H a 0xc88a889888a88988908c7 := seed 4469130 rfl
lemma f190 : H a 8940167 := seed 4470025 rfl
lemma f191 : H a 8940679 := seed 4471049 rfl
lemma f192 : H a 0xa889888c88a8898890c87 := seed 4471050 rfl
lemma f193 : H a 0xb08708388348328318310305 := seed 1581059 rfl
lemma f194 : H a 0xb0870838834832831830f := seed 1582618 rfl
lemma f195 : H a 0xb08708388348328310317 := seed 1582634 rfl
lemma f196 : H a 3171111 := seed 1582665 rfl
lemma f197 : H a 3171143 := seed 1582729 rfl
lemma f198 : H a 0xb08708388328318310347 := seed 1582730 rfl
lemma f199 : H a 0xd08708588548528518510505 := seed 2629635 rfl
lemma f200 : H a 0xd0870858854852851850f := seed 2632218 rfl
lemma f201 : H a 0xd08708588528518510547 := seed 2632330 rfl
lemma f202 : H a 5268871 := seed 2632457 rfl
lemma f203 : H a 0x708588548528518510d07 := seed 2636298 rfl
lemma f204 : H a 0xd08b08988948928918910905 := seed 4726787 rfl
lemma f205 : H a 9464087 := seed 4731433 rfl
lemma f206 : H a 9464199 := seed 4731657 rfl
lemma f207 : H a 0xd08988948928918910b07 := seed 4732426 rfl
lemma f208 : H a 9465095 := seed 4733449 rfl
lemma f209 : H a 0xe08708688648628618610605 := seed 3153923 rfl
lemma f210 : H a 0xe08708688648628610617 := seed 3157034 rfl
lemma f211 : H a 0xe08708688648618610627 := seed 3157066 rfl
lemma f212 : H a 6317703 := seed 3157257 rfl
lemma f213 : H a 0xe08688648628618610707 := seed 3157514 rfl
lemma f214 : H a 10512935 := seed 5256265 rfl
lemma f215 : H a 10512967 := seed 5256329 rfl
lemma f216 : H a 0xe08b08a88a28a18a10a47 := seed 5256330 rfl
lemma f217 : H a 0xe08b08a48a28a18a10a87 := seed 5256458 rfl
lemma f218 : H a 10513159 := seed 5256713 rfl
lemma f219 : H a 10513927 := seed 5258249 rfl
lemma f220 : H a 0xe08d08c88c48c28c18c10c05 := seed 6299651 rfl
lemma f221 : H a 12610599 := seed 6305865 rfl
lemma f222 : H a 12610631 := seed 6305929 rfl
lemma f223 : H a 12610695 := seed 6306057 rfl
lemma f224 : H a 12610823 := seed 6306313 rfl
lemma f225 : H a 0xe08c88c48c28c18c10d07 := seed 6306314 rfl
lemma f226 : H a 12611079 := seed 6306825 rfl
lemma f227 : H a 237631 := seed 114809 rfl
lemma f228 : H a 0x83c43c23c13c0bc07c03f := seed 114810 rfl
lemma f229 : H a 0x85c45c25c15c0dc07c060059 := seed 180227 rfl
lemma f230 : H a 368735 := seed 180409 rfl
lemma f231 : H a 368763 := seed 180465 rfl
lemma f232 : H a 368859 := seed 180657 rfl
lemma f233 : H a 368987 := seed 180913 rfl
lemma f234 : H a 0x85c45c25c0dc07c06015b := seed 180914 rfl
lemma f235 : H a 369243 := seed 181425 rfl
lemma f236 : H a 370779 := seed 184497 rfl
lemma f237 : H a 0x89c49c29c19c0dc0bc0a0099 := seed 311299 rfl
lemma f238 : H a 630943 := seed 311609 rfl
lemma f239 : H a 630971 := seed 311665 rfl
lemma f240 : H a 0x89c49c29c19c0dc0a00bb := seed 311666 rfl
lemma f241 : H a 631195 := seed 312113 rfl
lemma f242 : H a 631451 := seed 312625 rfl
lemma f243 : H a 631963 := seed 313649 rfl
lemma f244 : H a 632987 := seed 315697 rfl
lemma f245 : H a 0x91c51c31c19c15c13c120119 := seed 573443 rfl
lemma f246 : H a 1155359 := seed 574009 rfl
lemma f247 : H a 0x91c51c31c19c15c13c11f := seed 574010 rfl
lemma f248 : H a 1155387 := seed 574065 rfl
lemma f249 : H a 1155419 := seed 574129 rfl
lemma f250 : H a 0x91c51c31c19c13c12015b := seed 574130 rfl
lemma f251 : H a 1155483 := seed 574257 rfl
lemma f252 : H a 0x91c51c31c15c13c12019b := seed 574258 rfl
lemma f253 : H a 1155867 := seed 575025 rfl
lemma f254 : H a 0x91c31c19c15c13c12051b := seed 576050 rfl
lemma f255 : H a 1157403 := seed 578097 rfl
lemma f256 : H a 0x51c31c19c15c13c12091b := seed 578098 rfl
lemma f257 : H a 0xa1c61c31c29c25c23c220219 := seed 1097731 rfl
lemma f258 : H a 2204191 := seed 1098809 rfl
lemma f259 : H a 2204219 := seed 1098865 rfl
lemma f260 : H a 2204251 := seed 1098929 rfl
lemma f261 : H a 2204315 := seed 1099057 rfl
lemma f262 : H a 2204443 := seed 1099313 rfl
lemma f263 : H a 2206235 := seed 1102897 rfl
lemma f264 : H a 0x61c31c29c25c23c220a1b := seed 1102898 rfl
lemma f265 : H a 0xc1c61c51c49c45c43c420419 := seed 2146307 rfl
lemma f266 : H a 4301855 := seed 2148409 rfl
lemma f267 : H a 4301883 := seed 2148465 rfl
lemma f268 : H a 4302107 := seed 2148913 rfl
lemma f269 : H a 4303899 := seed 2152497 rfl
lemma f270 : H a 0xc1ca1c91c89c85c83c820819 := seed 4243459 rfl
lemma f271 : H a 8497183 := seed 4247609 rfl
lemma f272 : H a 0xc1ca1c91c89c85c83c81f := seed 4247610 rfl
lemma f273 : H a 8497211 := seed 4247665 rfl
lemma f274 : H a 0xc1ca1c91c89c85c82083b := seed 4247666 rfl
lemma f275 : H a 8497243 := seed 4247729 rfl
lemma f276 : H a 0xc1ca1c91c89c83c82085b := seed 4247730 rfl
lemma f277 : H a 0xc1ca1c91c85c83c82089b := seed 4247858 rfl
lemma f278 : H a 8497435 := seed 4248113 rfl
lemma f279 : H a 8497691 := seed 4248625 rfl
lemma f280 : H a 0xc1c91c89c85c83c820a1b := seed 4248626 rfl
lemma f281 : H a 0xa1c91c89c85c83c820c1b := seed 4249650 rfl
lemma f282 : H a 0x86c46c26c16c0ec07c070069 := seed 212995 rfl
lemma f283 : H a 434287 := seed 213209 rfl
lemma f284 : H a 434299 := seed 213233 rfl
lemma f285 : H a 0x86c46c26c16c0ec07007b := seed 213234 rfl
lemma f286 : H a 434539 := seed 213713 rfl
lemma f287 : H a 0x86c46c26c0ec07c07016b := seed 213714 rfl
lemma f288 : H a 434795 := seed 214225 rfl
lemma f289 : H a 436331 := seed 217297 rfl
lemma f290 : H a 0x46c26c16c0ec07c07086b := seed 217298 rfl
lemma f291 : H a 0x8ac4ac2ac1ac0ec0bc0b00a9 := seed 344067 rfl
lemma f292 : H a 0x8ac4ac2ac1ac0ec0bc0af := seed 344410 rfl
lemma f293 : H a 696507 := seed 344433 rfl
lemma f294 : H a 696747 := seed 344913 rfl
lemma f295 : H a 697003 := seed 345425 rfl
lemma f296 : H a 697515 := seed 346449 rfl
lemma f297 : H a 0x8ac2ac1ac0ec0bc0b04ab := seed 346450 rfl
lemma f298 : H a 698539 := seed 348497 rfl
lemma f299 : H a 0x92c52c32c1ac16c13c130129 := seed 606211 rfl
lemma f300 : H a 1220911 := seed 606809 rfl
lemma f301 : H a 0x92c52c32c1ac16c13c12f := seed 606810 rfl
lemma f302 : H a 1220923 := seed 606833 rfl
lemma f303 : H a 1220971 := seed 606929 rfl
lemma f304 : H a 1221035 := seed 607057 rfl
lemma f305 : H a 1221419 := seed 607825 rfl
lemma f306 : H a 0x92c52c1ac16c13c13032b := seed 607826 rfl
lemma f307 : H a 1221931 := seed 608849 rfl
lemma f308 : H a 1222955 := seed 610897 rfl
lemma f309 : H a 0xa2c62c32c2ac26c23c230229 := seed 1130499 rfl
lemma f310 : H a 0xa2c62c32c2ac26c23c22f := seed 1131610 rfl
lemma f311 : H a 2269755 := seed 1131633 rfl
lemma f312 : H a 0xa2c62c32c2ac26c23023b := seed 1131634 rfl
lemma f313 : H a 2269995 := seed 1132113 rfl
lemma f314 : H a 2271787 := seed 1135697 rfl
lemma f315 : H a 4367531 := seed 2181457 rfl
lemma f316 : H a 0xc2c62c52c46c43c4304ab := seed 2181458 rfl
lemma f317 : H a 4367659 := seed 2181713 rfl
lemma f318 : H a 4369451 := seed 2185297 rfl
lemma f319 : H a 0xc2ca2c92c8ac86c83c830829 := seed 4276227 rfl
lemma f320 : H a 8562735 := seed 4280409 rfl
lemma f321 : H a 0xc2ca2c92c8ac86c83c82f := seed 4280410 rfl
lemma f322 : H a 8562747 := seed 4280433 rfl
lemma f323 : H a 8562795 := seed 4280529 rfl
lemma f324 : H a 0xc2ca2c92c8ac83c83086b := seed 4280530 rfl
lemma f325 : H a 8562859 := seed 4280657 rfl
lemma f326 : H a 0xc2ca2c92c86c83c8308ab := seed 4280658 rfl
lemma f327 : H a 8562987 := seed 4280913 rfl
lemma f328 : H a 0xc2ca2c8ac86c83c83092b := seed 4280914 rfl
lemma f329 : H a 8563243 := seed 4281425 rfl
lemma f330 : H a 0xc2c92c8ac86c83c830a2b := seed 4281426 rfl
lemma f331 : H a 8563755 := seed 4282449 rfl
lemma f332 : H a 0xa2c92c8ac86c83c830c2b := seed 4282450 rfl
lemma f333 : H a 0x8cc4cc2cc1cc0ec0dc0d00c9 := seed 409603 rfl
lemma f334 : H a 827627 := seed 410065 rfl
lemma f335 : H a 827851 := seed 410513 rfl
lemma f336 : H a 828107 := seed 411025 rfl
lemma f337 : H a 0x8cc4cc1cc0ec0dc0d02cb := seed 411026 rfl
lemma f338 : H a 828619 := seed 412049 rfl
lemma f339 : H a 0x8cc2cc1cc0ec0dc0d04cb := seed 412050 rfl
lemma f340 : H a 0x94c54c34c1cc16c15c150149 := seed 671747 rfl
lemma f341 : H a 1352043 := seed 672465 rfl
lemma f342 : H a 1352139 := seed 672657 rfl
lemma f343 : H a 1352523 := seed 673425 rfl
lemma f344 : H a 1353035 := seed 674449 rfl
lemma f345 : H a 1354059 := seed 676497 rfl
lemma f346 : H a 0x54c34c1cc16c15c15094b := seed 676498 rfl
lemma f347 : H a 2400847 := seed 1197209 rfl
lemma f348 : H a 2400875 := seed 1197265 rfl
lemma f349 : H a 2400971 := seed 1197457 rfl
lemma f350 : H a 0xa4c64c34c26c25c2502cb := seed 1197458 rfl
lemma f351 : H a 2401099 := seed 1197713 rfl
lemma f352 : H a 2402891 := seed 1201297 rfl
lemma f353 : H a 4498635 := seed 2247057 rfl
lemma f354 : H a 0xc4ca4c94c8cc86c85c850849 := seed 4341763 rfl
lemma f355 : H a 8693867 := seed 4346065 rfl
lemma f356 : H a 8694091 := seed 4346513 rfl
lemma f357 : H a 8694347 := seed 4347025 rfl
lemma f358 : H a 8694859 := seed 4348049 rfl
lemma f359 : H a 0x98c58c38c1cc1ac19c190189 := seed 802819 rfl
lemma f360 : H a 0x98c58c38c1cc1ac19c18f := seed 803610 rfl
lemma f361 : H a 1614251 := seed 803665 rfl
lemma f362 : H a 1614283 := seed 803729 rfl
lemma f363 : H a 1615243 := seed 805649 rfl
lemma f364 : H a 0x98c38c1cc1ac19c19058b := seed 805650 rfl
lemma f365 : H a 0x58c38c1cc1ac19c19098b := seed 807698 rfl
lemma f366 : H a 0xa8c68c38c2cc2ac29c290289 := seed 1327107 rfl
lemma f367 : H a 0xa8c68c38c2cc2ac29c28f := seed 1328410 rfl
lemma f368 : H a 0xa8c68c38c2cc2ac29029b := seed 1328434 rfl
lemma f369 : H a 2663083 := seed 1328465 rfl
lemma f370 : H a 0xa8c68c38c2ac29c2902cb := seed 1328530 rfl
lemma f371 : H a 2663307 := seed 1328913 rfl
lemma f372 : H a 2664075 := seed 1330449 rfl
lemma f373 : H a 0xa8c38c2cc2ac29c29068b := seed 1330450 rfl
lemma f374 : H a 0x68c38c2cc2ac29c290a8b := seed 1332498 rfl
lemma f375 : H a 0xc8c68c58c4cc4ac49c490489 := seed 2375683 rfl
lemma f376 : H a 4760719 := seed 2378009 rfl
lemma f377 : H a 0xc8c68c58c4cc4ac49c48f := seed 2378010 rfl
lemma f378 : H a 0xc8c68c58c4cc4ac49049b := seed 2378034 rfl
lemma f379 : H a 4760747 := seed 2378065 rfl
lemma f380 : H a 0xc8c68c58c4ac49c4904cb := seed 2378130 rfl
lemma f381 : H a 4760971 := seed 2378513 rfl
lemma f382 : H a 4761227 := seed 2379025 rfl
lemma f383 : H a 0xc8c58c4cc4ac49c49068b := seed 2379026 rfl
lemma f384 : H a 4762763 := seed 2382097 rfl
lemma f385 : H a 0xc8ca8c98c8cc8ac89c890889 := seed 4472835 rfl
lemma f386 : H a 0xc8ca8c98c8cc8ac89c88f := seed 4477210 rfl
lemma f387 : H a 8956059 := seed 4477233 rfl
lemma f388 : H a 8956075 := seed 4477265 rfl
lemma f389 : H a 0xc8ca8c98c8ac89c8908cb := seed 4477330 rfl
lemma f390 : H a 8956299 := seed 4477713 rfl
lemma f391 : H a 8956555 := seed 4478225 rfl
lemma f392 : H a 8957067 := seed 4479249 rfl
lemma f393 : H a 3187531 := seed 1590929 rfl
lemma f394 : H a 0xb0c70c38c32c31c31034b := seed 1590930 rfl
lemma f395 : H a 3187595 := seed 1591057 rfl
lemma f396 : H a 0xb0c70c34c32c31c31038b := seed 1591058 rfl
lemma f397 : H a 3188491 := seed 1592849 rfl
lemma f398 : H a 3189515 := seed 1594897 rfl
lemma f399 : H a 0x70c38c34c32c31c310b0b := seed 1594898 rfl
lemma f400 : H a 0xd0c70c58c54c52c51c510509 := seed 2637827 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f401 : H a 0xd0c70c58c54c52c51c50f := seed 2640410 rfl
lemma f402 : H a 5285195 := seed 2640529 rfl
lemma f403 : H a 5285259 := seed 2640657 rfl
lemma f404 : H a 0x70c58c54c52c51c510d0b := seed 2644498 rfl
lemma f405 : H a 0xd0cb0c98c94c92c91c910909 := seed 4734979 rfl
lemma f406 : H a 9480463 := seed 4739609 rfl
lemma f407 : H a 9480491 := seed 4739665 rfl
lemma f408 : H a 9480523 := seed 4739729 rfl
lemma f409 : H a 0xd0cb0c98c92c91c91094b := seed 4739730 rfl
lemma f410 : H a 0xd0cb0c94c92c91c91098b := seed 4739858 rfl
lemma f411 : H a 9480971 := seed 4740625 rfl
lemma f412 : H a 0xb0c98c94c92c91c910d0b := seed 4741650 rfl
lemma f413 : H a 0xe0c70c68c64c62c61c610609 := seed 3162115 rfl
lemma f414 : H a 6333995 := seed 3165265 rfl
lemma f415 : H a 6334091 := seed 3165457 rfl
lemma f416 : H a 6334219 := seed 3165713 rfl
lemma f417 : H a 0xe0c68c64c62c61c61070b := seed 3165714 rfl
lemma f418 : H a 0x70c68c64c62c61c610e0b := seed 3169298 rfl
lemma f419 : H a 0xe0cb0ca8ca4ca2ca1ca10a09 := seed 5259267 rfl
lemma f420 : H a 0xe0cb0ca8ca4ca2ca1ca0f := seed 5264410 rfl
lemma f421 : H a 10529323 := seed 5264465 rfl
lemma f422 : H a 10529355 := seed 5264529 rfl
lemma f423 : H a 0xe0cb0ca8ca2ca1ca10a4b := seed 5264530 rfl
lemma f424 : H a 10529419 := seed 5264657 rfl
lemma f425 : H a 10529547 := seed 5264913 rfl
lemma f426 : H a 0xe0ca8ca4ca2ca1ca10b0b := seed 5264914 rfl
lemma f427 : H a 0xb0ca8ca4ca2ca1ca10e0b := seed 5266450 rfl
lemma f428 : H a 0xe0cd0cc8cc4cc2cc1cc10c09 := seed 6307843 rfl
lemma f429 : H a 0xe0cd0cc8cc4cc2cc1cc0f := seed 6314010 rfl
lemma f430 : H a 12626971 := seed 6314033 rfl
lemma f431 : H a 12626987 := seed 6314065 rfl
lemma f432 : H a 12627019 := seed 6314129 rfl
lemma f433 : H a 0xe0cd0cc8cc2cc1cc10c4b := seed 6314130 rfl
lemma f434 : H a 12627083 := seed 6314257 rfl
lemma f435 : H a 12627211 := seed 6314513 rfl
lemma f436 : H a 0x8744742741740f407c078071 := seed 229379 rfl
lemma f437 : H a 467063 := seed 229609 rfl
lemma f438 : H a 0x87447427417407c0780f3 := seed 229858 rfl
lemma f439 : H a 467315 := seed 230113 rfl
lemma f440 : H a 0x8744742740f407c078173 := seed 230114 rfl
lemma f441 : H a 467571 := seed 230625 rfl
lemma f442 : H a 0x8744741740f407c078273 := seed 230626 rfl
lemma f443 : H a 469107 := seed 233697 rfl
lemma f444 : H a 0x8b44b42b41b40f40bc0b80b1 := seed 360451 rfl
lemma f445 : H a 0x8b44b42b41b40bc0b80f3 := seed 360930 rfl
lemma f446 : H a 0x8b44b42b40f40bc0b81b3 := seed 361314 rfl
lemma f447 : H a 730291 := seed 362849 rfl
lemma f448 : H a 731315 := seed 364897 rfl
lemma f449 : H a 0x9345343341b417413c138131 := seed 622595 rfl
lemma f450 : H a 1253687 := seed 623209 rfl
lemma f451 : H a 1253691 := seed 623217 rfl
lemma f452 : H a 0x9345343341b417413813b := seed 623218 rfl
lemma f453 : H a 1253747 := seed 623329 rfl
lemma f454 : H a 1253811 := seed 623457 rfl
lemma f455 : H a 1254195 := seed 624225 rfl
lemma f456 : H a 0x5343341b417413c138933 := seed 627298 rfl
lemma f457 : H a 2302519 := seed 1148009 rfl
lemma f458 : H a 2302523 := seed 1148017 rfl
lemma f459 : H a 2302579 := seed 1148129 rfl
lemma f460 : H a 2302771 := seed 1148513 rfl
lemma f461 : H a 2304563 := seed 1152097 rfl
lemma f462 : H a 0xc346345344b447443c438431 := seed 2195459 rfl
lemma f463 : H a 4400187 := seed 2197617 rfl
lemma f464 : H a 4400307 := seed 2197857 rfl
lemma f465 : H a 0xc3463453447443c4384b3 := seed 2197858 rfl
lemma f466 : H a 4402227 := seed 2201697 rfl
lemma f467 : H a 0xc34a349348b487483c838831 := seed 4292611 rfl
lemma f468 : H a 8595511 := seed 4296809 rfl
lemma f469 : H a 8595515 := seed 4296817 rfl
lemma f470 : H a 8595571 := seed 4296929 rfl
lemma f471 : H a 0xc34a349348b483c838873 := seed 4296930 rfl
lemma f472 : H a 8595635 := seed 4297057 rfl
lemma f473 : H a 0xc34a348b487483c838933 := seed 4297314 rfl
lemma f474 : H a 0xc349348b487483c838a33 := seed 4297826 rfl
lemma f475 : H a 8596531 := seed 4298849 rfl
lemma f476 : H a 860375 := seed 426409 rfl
lemma f477 : H a 860627 := seed 426913 rfl
lemma f478 : H a 861395 := seed 428449 rfl
lemma f479 : H a 0x9545543541d417415c158151 := seed 688131 rfl
lemma f480 : H a 0x9545543541d415c158173 := seed 688866 rfl
lemma f481 : H a 1385299 := seed 689825 rfl
lemma f482 : H a 0x9545541d417415c158353 := seed 689826 rfl
lemma f483 : H a 1385811 := seed 690849 rfl
lemma f484 : H a 0xa546543542d427425c258251 := seed 1212419 rfl
lemma f485 : H a 2433875 := seed 1214113 rfl
lemma f486 : H a 0xa546542d427425c258353 := seed 1214114 rfl
lemma f487 : H a 2435667 := seed 1217697 rfl
lemma f488 : H a 0x6543542d427425c258a53 := seed 1217698 rfl
lemma f489 : H a 0xc546545544d447445c458451 := seed 2260995 rfl
lemma f490 : H a 0x6545544d447445c458c53 := seed 2267298 rfl
lemma f491 : H a 0xc54a549548d487485c858851 := seed 4358147 rfl
lemma f492 : H a 8726615 := seed 4362409 rfl
lemma f493 : H a 8726643 := seed 4362465 rfl
lemma f494 : H a 8726867 := seed 4362913 rfl
lemma f495 : H a 8727123 := seed 4363425 rfl
lemma f496 : H a 0x9945943941d41b419c198191 := seed 819203 rfl
lemma f497 : H a 1646999 := seed 820009 rfl
lemma f498 : H a 1647059 := seed 820129 rfl
lemma f499 : H a 1647507 := seed 821025 rfl
lemma f500 : H a 0x9943941d41b419c198593 := seed 822050 rfl
lemma f501 : H a 0x5943941d41b419c198993 := seed 824098 rfl
lemma f502 : H a 0xc946945944d44b449c498491 := seed 2392067 rfl
lemma f503 : H a 4793495 := seed 2394409 rfl
lemma f504 : H a 4793523 := seed 2394465 rfl
lemma f505 : H a 0xc946945944b449c4984d3 := seed 2394530 rfl
lemma f506 : H a 4793747 := seed 2394913 rfl
lemma f507 : H a 0xc946944d44b449c498593 := seed 2394914 rfl
lemma f508 : H a 4795539 := seed 2398497 rfl
lemma f509 : H a 0x6945944d44b449c498c93 := seed 2398498 rfl
lemma f510 : H a 0xc94a949948d48b489c898891 := seed 4489219 rfl
lemma f511 : H a 0xc94a949948d48b489889b := seed 4493618 rfl
lemma f512 : H a 0xc949948d48b489c898a93 := seed 4494626 rfl
lemma f513 : H a 8989843 := seed 4495649 rfl
lemma f514 : H a 0xa949948d48b489c898c93 := seed 4495650 rfl
lemma f515 : H a 0xb1471439435433431c318311 := seed 1605635 rfl
lemma f516 : H a 3220371 := seed 1607457 rfl
lemma f517 : H a 0x71439435433431c318b13 := seed 1611298 rfl
lemma f518 : H a 0xd1471459455453451c518511 := seed 2654211 rfl
lemma f519 : H a 5317971 := seed 2656929 rfl
lemma f520 : H a 0xd1471459453451c518553 := seed 2656930 rfl
lemma f521 : H a 0x71459455453451c518d13 := seed 2660898 rfl
lemma f522 : H a 0xd14b1499495493491c918911 := seed 4751363 rfl
lemma f523 : H a 9513239 := seed 4756009 rfl
lemma f524 : H a 9513267 := seed 4756065 rfl
lemma f525 : H a 9514259 := seed 4758049 rfl
lemma f526 : H a 0xe14b14a94a54a34a1ca18a11 := seed 5275651 rfl
lemma f527 : H a 10562071 := seed 5280809 rfl
lemma f528 : H a 10562099 := seed 5280865 rfl
lemma f529 : H a 10562131 := seed 5280929 rfl
lemma f530 : H a 10562323 := seed 5281313 rfl
lemma f531 : H a 0xe14d14c94c54c34c1cc18c11 := seed 6324227 rfl
lemma f532 : H a 0xe14d14c94c34c1cc18c53 := seed 6330530 rfl
lemma f533 : H a 12659859 := seed 6330657 rfl
lemma f534 : H a 12659987 := seed 6330913 rfl
lemma f535 : H a 12660243 := seed 6331425 rfl
lemma f536 : H a 0x8e44e42e41e40f40e80eb := seed 459218 rfl
lemma f537 : H a 926179 := seed 459713 rfl
lemma f538 : H a 926435 := seed 460225 rfl
lemma f539 : H a 926947 := seed 461249 rfl
lemma f540 : H a 0x9645643641e417416c168161 := seed 720899 rfl
lemma f541 : H a 0x9645643641e417416816b := seed 721618 rfl
lemma f542 : H a 1450355 := seed 721633 rfl
lemma f543 : H a 0x9645643641e416c168173 := seed 721634 rfl
lemma f544 : H a 1450467 := seed 721857 rfl
lemma f545 : H a 0x96456436417416c1681e3 := seed 721858 rfl
lemma f546 : H a 1450851 := seed 722625 rfl
lemma f547 : H a 0x9645641e417416c168363 := seed 722626 rfl
lemma f548 : H a 0x9643641e417416c168563 := seed 723650 rfl
lemma f549 : H a 1452387 := seed 725697 rfl
lemma f550 : H a 0x5643641e417416c168963 := seed 725698 rfl
lemma f551 : H a 0xa646643642e427426c268261 := seed 1245187 rfl
lemma f552 : H a 0xa646643642e427426c267 := seed 1246410 rfl
lemma f553 : H a 2499299 := seed 1246657 rfl
lemma f554 : H a 2499427 := seed 1246913 rfl
lemma f555 : H a 0xa646642e427426c268363 := seed 1246914 rfl
lemma f556 : H a 0xa643642e427426c268663 := seed 1248450 rfl
lemma f557 : H a 2501219 := seed 1250497 rfl
lemma f558 : H a 0xc646645644e447446c468461 := seed 2293763 rfl
lemma f559 : H a 4596963 := seed 2296257 rfl
lemma f560 : H a 0xc646644e447446c468563 := seed 2296514 rfl
lemma f561 : H a 4598883 := seed 2300097 rfl
lemma f562 : H a 0xc64a649648e487486c868861 := seed 4390915 rfl
lemma f563 : H a 8792171 := seed 4395217 rfl
lemma f564 : H a 0xc64a649648e487486886b := seed 4395218 rfl
lemma f565 : H a 0xc64a649648e486c868873 := seed 4395234 rfl
lemma f566 : H a 8792419 := seed 4395713 rfl
lemma f567 : H a 0xc64a648e487486c868963 := seed 4395714 rfl
lemma f568 : H a 8792675 := seed 4396225 rfl
lemma f569 : H a 0xc649648e487486c868a63 := seed 4396226 rfl
lemma f570 : H a 8793187 := seed 4397249 rfl
lemma f571 : H a 0x9a45a43a41e41b41ac1a81a1 := seed 851971 rfl
lemma f572 : H a 1712555 := seed 852817 rfl
lemma f573 : H a 1712611 := seed 852929 rfl
lemma f574 : H a 1713059 := seed 853825 rfl
lemma f575 : H a 0x9a45a41e41b41ac1a83a3 := seed 853826 rfl
lemma f576 : H a 0x5a43a41e41b41ac1a89a3 := seed 856898 rfl
lemma f577 : H a 0xaa46a43a42e42b42ac2a82a1 := seed 1376259 rfl
lemma f578 : H a 2761635 := seed 1378113 rfl
lemma f579 : H a 0xca46a45a44e44b44ac4a84a1 := seed 2424835 rfl
lemma f580 : H a 4859047 := seed 2427209 rfl
lemma f581 : H a 0xca46a45a44e44b44ac4a7 := seed 2427210 rfl
lemma f582 : H a 0xca46a45a44e44b44a84ab := seed 2427218 rfl
lemma f583 : H a 0xca46a45a44e44ac4a84b3 := seed 2427234 rfl
lemma f584 : H a 4859107 := seed 2427329 rfl
lemma f585 : H a 0xca46a45a44b44ac4a84e3 := seed 2427330 rfl
lemma f586 : H a 4859299 := seed 2427713 rfl
lemma f587 : H a 0xca46a44e44b44ac4a85a3 := seed 2427714 rfl
lemma f588 : H a 4859555 := seed 2428225 rfl
lemma f589 : H a 0xca45a44e44b44ac4a86a3 := seed 2428226 rfl
lemma f590 : H a 4861091 := seed 2431297 rfl
lemma f591 : H a 0x6a45a44e44b44ac4a8ca3 := seed 2431298 rfl
lemma f592 : H a 0xca4aa49a48e48b48ac8a88a1 := seed 4521987 rfl
lemma f593 : H a 0xca4aa49a48e48b48ac8a7 := seed 4526410 rfl
lemma f594 : H a 9054379 := seed 4526417 rfl
lemma f595 : H a 0xca4aa49a48b48ac8a88e3 := seed 4526530 rfl
lemma f596 : H a 9055395 := seed 4528449 rfl
lemma f597 : H a 0xaa49a48e48b48ac8a8ca3 := seed 4528450 rfl
lemma f598 : H a 0xb247243a436433432c328321 := seed 1638403 rfl
lemma f599 : H a 3285799 := seed 1640009 rfl
lemma f600 : H a 3285859 := seed 1640129 rfl
lemma f601 : H a 0xb247243a433432c328363 := seed 1640130 rfl
lemma f602 : H a 0xb2472436433432c3283a3 := seed 1640258 rfl
lemma f603 : H a 0xb243a436433432c328723 := seed 1642050 rfl
lemma f604 : H a 3287843 := seed 1644097 rfl
lemma f605 : H a 0x7243a436433432c328b23 := seed 1644098 rfl
lemma f606 : H a 0xd247245a456453452c528521 := seed 2686979 rfl
lemma f607 : H a 5383463 := seed 2689609 rfl
lemma f608 : H a 5383523 := seed 2689729 rfl
lemma f609 : H a 0xd247245a453452c528563 := seed 2689730 rfl
lemma f610 : H a 0xd2472456453452c5285a3 := seed 2689858 rfl
lemma f611 : H a 5383971 := seed 2690625 rfl
lemma f612 : H a 0xd245a456453452c528723 := seed 2690626 rfl
lemma f613 : H a 5385507 := seed 2693697 rfl
lemma f614 : H a 0x7245a456453452c528d23 := seed 2693698 rfl
lemma f615 : H a 0xd24b249a496493492c928921 := seed 4784131 rfl
lemma f616 : H a 0xd24b249a496493492c927 := seed 4788810 rfl
lemma f617 : H a 9578795 := seed 4788817 rfl
lemma f618 : H a 9578851 := seed 4788929 rfl
lemma f619 : H a 0xd24b249a493492c928963 := seed 4788930 rfl
lemma f620 : H a 0xd24b2496493492c9289a3 := seed 4789058 rfl
lemma f621 : H a 9579299 := seed 4789825 rfl
lemma f622 : H a 0xd249a496493492c928b23 := seed 4789826 rfl
lemma f623 : H a 0xb249a496493492c928d23 := seed 4790850 rfl
lemma f624 : H a 0xe247246a466463462c628621 := seed 3211267 rfl
lemma f625 : H a 0xe2472466463462c6286a3 := seed 3214658 rfl
lemma f626 : H a 6432547 := seed 3214913 rfl
lemma f627 : H a 0xe246a466463462c628723 := seed 3214914 rfl
lemma f628 : H a 0xe24b24aa4a64a34a2ca28a21 := seed 5308419 rfl
lemma f629 : H a 10627627 := seed 5313617 rfl
lemma f630 : H a 0xe24b24aa4a64a2ca28a33 := seed 5313634 rfl
lemma f631 : H a 10627683 := seed 5313729 rfl
lemma f632 : H a 0xe24b24aa4a34a2ca28a63 := seed 5313730 rfl
lemma f633 : H a 10627747 := seed 5313857 rfl
lemma f634 : H a 0xe24b24a64a34a2ca28aa3 := seed 5313858 rfl
lemma f635 : H a 0xe24aa4a64a34a2ca28b23 := seed 5314114 rfl
lemma f636 : H a 10628643 := seed 5315649 rfl
lemma f637 : H a 0xb24aa4a64a34a2ca28e23 := seed 5315650 rfl
lemma f638 : H a 0xe24d24ca4c64c34c2cc28c21 := seed 6356995 rfl
lemma f639 : H a 12725291 := seed 6363217 rfl
lemma f640 : H a 0xe24d24ca4c64c34c28c2b := seed 6363218 rfl
lemma f641 : H a 12725347 := seed 6363329 rfl
lemma f642 : H a 0xe24d24ca4c34c2cc28c63 := seed 6363330 rfl
lemma f643 : H a 12725411 := seed 6363457 rfl
lemma f644 : H a 0xe24d24c64c34c2cc28ca3 := seed 6363458 rfl
lemma f645 : H a 0xe24ca4c64c34c2cc28d23 := seed 6363714 rfl
lemma f646 : H a 12725795 := seed 6364225 rfl
lemma f647 : H a 0xd24ca4c64c34c2cc28e23 := seed 6364226 rfl
lemma f648 : H a 0x9c45c43c41e41d41cc1c81c1 := seed 917507 rfl
lemma f649 : H a 0x9c45c43c41e41d41cc1c7 := seed 918410 rfl
lemma f650 : H a 0x9c45c43c41e41d41c81cb := seed 918418 rfl
lemma f651 : H a 0x9c45c43c41e41cc1c81d3 := seed 918434 rfl
lemma f652 : H a 0x9c45c43c41d41cc1c81e3 := seed 918466 rfl
lemma f653 : H a 0xac46c43c42e42d42cc2c82c1 := seed 1441795 rfl
lemma f654 : H a 2892487 := seed 1443209 rfl
lemma f655 : H a 0xac46c43c42e42d42c82cb := seed 1443218 rfl
lemma f656 : H a 2892499 := seed 1443233 rfl
lemma f657 : H a 2892515 := seed 1443265 rfl
lemma f658 : H a 0xac46c43c42d42cc2c82e3 := seed 1443266 rfl
lemma f659 : H a 0xcc46c45c44e44d44cc4c84c1 := seed 2490371 rfl
lemma f660 : H a 4990151 := seed 2492809 rfl
lemma f661 : H a 0xcc46c45c44e44d44cc4c7 := seed 2492810 rfl
lemma f662 : H a 4990155 := seed 2492817 rfl
lemma f663 : H a 0xcc46c45c44e44d44c84cb := seed 2492818 rfl
lemma f664 : H a 0xcc46c45c44e44cc4c84d3 := seed 2492834 rfl
lemma f665 : H a 4990179 := seed 2492865 rfl
lemma f666 : H a 0xcc46c45c44d44cc4c84e3 := seed 2492866 rfl
lemma f667 : H a 0xcc4ac49c48e48d48cc8c88c1 := seed 4587523 rfl
lemma f668 : H a 0xcc4ac49c48e48d48cc8c7 := seed 4592010 rfl
lemma f669 : H a 0xb447443c436435434c348341 := seed 1703939 rfl
lemma f670 : H a 3416903 := seed 1705609 rfl
lemma f671 : H a 0xb447443c436435434c347 := seed 1705610 rfl
lemma f672 : H a 3416907 := seed 1705617 rfl
lemma f673 : H a 0xb447443c436435434834b := seed 1705618 rfl
lemma f674 : H a 3416915 := seed 1705633 rfl
lemma f675 : H a 0xb447443c436434c348353 := seed 1705634 rfl
lemma f676 : H a 3416931 := seed 1705665 rfl
lemma f677 : H a 0xb447443c435434c348363 := seed 1705666 rfl
lemma f678 : H a 0xd447445c456455454c548541 := seed 2752515 rfl
lemma f679 : H a 5514567 := seed 2755209 rfl
lemma f680 : H a 0xd447445c456455454c547 := seed 2755210 rfl
lemma f681 : H a 5514571 := seed 2755217 rfl
lemma f682 : H a 0xd447445c456455454854b := seed 2755218 rfl
lemma f683 : H a 5514579 := seed 2755233 rfl
lemma f684 : H a 0xd447445c456454c548553 := seed 2755234 rfl
lemma f685 : H a 5514595 := seed 2755265 rfl
lemma f686 : H a 0xd44b449c496495494c948941 := seed 4849667 rfl
lemma f687 : H a 9709895 := seed 4854409 rfl
lemma f688 : H a 0xd44b449c496495494c947 := seed 4854410 rfl
lemma f689 : H a 0xd44b449c496495494894b := seed 4854418 rfl
lemma f690 : H a 9709907 := seed 4854433 rfl
lemma f691 : H a 0xd44b449c496494c948953 := seed 4854434 rfl
lemma f692 : H a 9709923 := seed 4854465 rfl
lemma f693 : H a 0xd44b449c495494c948963 := seed 4854466 rfl
lemma f694 : H a 6563399 := seed 3280009 rfl
lemma f695 : H a 6563411 := seed 3280033 rfl
lemma f696 : H a 6563427 := seed 3280065 rfl
lemma f697 : H a 0xe44b44ac4a64a54a4ca48a41 := seed 5373955 rfl
lemma f698 : H a 10758727 := seed 5379209 rfl
lemma f699 : H a 0xe44b44ac4a64a54a4ca47 := seed 5379210 rfl
lemma f700 : H a 10758731 := seed 5379217 rfl
lemma f701 : H a 0xe44b44ac4a64a54a48a4b := seed 5379218 rfl
lemma f702 : H a 10758739 := seed 5379233 rfl
lemma f703 : H a 0xe44b44ac4a64a4ca48a53 := seed 5379234 rfl
lemma f704 : H a 10758755 := seed 5379265 rfl
lemma f705 : H a 0xe44b44ac4a54a4ca48a63 := seed 5379266 rfl
lemma f706 : H a 0xe44d44cc4c64c54c4cc48c41 := seed 6422531 rfl
lemma f707 : H a 12856391 := seed 6428809 rfl
lemma f708 : H a 0xe44d44cc4c64c54c4cc47 := seed 6428810 rfl
lemma f709 : H a 0xe44d44cc4c64c4cc48c53 := seed 6428834 rfl
lemma f710 : H a 12856419 := seed 6428865 rfl
lemma f711 : H a 0xb847843c43a439438c388381 := seed 1835011 rfl
lemma f712 : H a 3679111 := seed 1836809 rfl
lemma f713 : H a 3679115 := seed 1836817 rfl
lemma f714 : H a 3679123 := seed 1836833 rfl
lemma f715 : H a 3679139 := seed 1836865 rfl
lemma f716 : H a 0xb847843c439438c3883a3 := seed 1836866 rfl
lemma f717 : H a 0xd847845c45a459458c588581 := seed 2883587 rfl
lemma f718 : H a 5776775 := seed 2886409 rfl
lemma f719 : H a 0xd847845c45a459458c587 := seed 2886410 rfl
lemma f720 : H a 5776779 := seed 2886417 rfl
lemma f721 : H a 0xd847845c45a459458858b := seed 2886418 rfl
lemma f722 : H a 5776787 := seed 2886433 rfl
lemma f723 : H a 0xd847845c45a458c588593 := seed 2886434 rfl
lemma f724 : H a 5776803 := seed 2886465 rfl
lemma f725 : H a 0xd847845c459458c5885a3 := seed 2886466 rfl
lemma f726 : H a 0xd84b849c49a499498c988981 := seed 4980739 rfl
lemma f727 : H a 0xd84b849c49a499498c987 := seed 4985610 rfl
lemma f728 : H a 9972131 := seed 4985665 rfl
lemma f729 : H a 0xd84b849c499498c9889a3 := seed 4985666 rfl
lemma f730 : H a 0xe847846c46a469468c688681 := seed 3407875 rfl
lemma f731 : H a 6825607 := seed 3411209 rfl
lemma f732 : H a 0xe847846c46a469468c687 := seed 3411210 rfl
lemma f733 : H a 6825611 := seed 3411217 rfl
lemma f734 : H a 0xe847846c46a469468868b := seed 3411218 rfl
lemma f735 : H a 0xe847846c46a468c688693 := seed 3411234 rfl
lemma f736 : H a 6825635 := seed 3411265 rfl
lemma f737 : H a 0xe847846c469468c6886a3 := seed 3411266 rfl
lemma f738 : H a 0xe84b84ac4aa4a94a8ca88a81 := seed 5505027 rfl
lemma f739 : H a 11020939 := seed 5510417 rfl
lemma f740 : H a 0xe84b84ac4aa4a94a88a8b := seed 5510418 rfl
lemma f741 : H a 11020947 := seed 5510433 rfl
lemma f742 : H a 11020963 := seed 5510465 rfl
lemma f743 : H a 0xe84d84cc4ca4c94c8cc88c81 := seed 6553603 rfl
lemma f744 : H a 13118599 := seed 6560009 rfl
lemma f745 : H a 0xe84d84cc4ca4c94c8cc87 := seed 6560010 rfl
lemma f746 : H a 13118603 := seed 6560017 rfl
lemma f747 : H a 0xe84d84cc4ca4c94c88c8b := seed 6560018 rfl
lemma f748 : H a 13118611 := seed 6560033 rfl
lemma f749 : H a 0xe84d84cc4ca4c8cc88c93 := seed 6560034 rfl
lemma f750 : H a 13118627 := seed 6560065 rfl
lemma f751 : H a 0xe84d84cc4c94c8cc88ca3 := seed 6560066 rfl
lemma f752 : H a 0xf0478474472471470c708701 := seed 3670019 rfl
lemma f753 : H a 7350023 := seed 3673609 rfl
lemma f754 : H a 7350035 := seed 3673633 rfl
lemma f755 : H a 7350051 := seed 3673665 rfl
lemma f756 : H a 0xf0478474471470c708723 := seed 3673666 rfl
lemma f757 : H a 0xf04b84b44b24b14b0cb08b01 := seed 5767171 rfl
lemma f758 : H a 11545351 := seed 5772809 rfl
lemma f759 : H a 0xf04b84b44b24b14b0cb07 := seed 5772810 rfl
lemma f760 : H a 11545355 := seed 5772817 rfl
lemma f761 : H a 0xf04b84b44b24b14b08b0b := seed 5772818 rfl
lemma f762 : H a 0xf04b84b44b24b0cb08b13 := seed 5772834 rfl
lemma f763 : H a 11545379 := seed 5772865 rfl
lemma f764 : H a 0xf04d84d44d24d14d0cd08d01 := seed 6815747 rfl
lemma f765 : H a 0xf04d84d44d24d14d0cd07 := seed 6822410 rfl
lemma f766 : H a 13643019 := seed 6822417 rfl
lemma f767 : H a 0xf04d84d44d24d14d08d0b := seed 6822418 rfl
lemma f768 : H a 0xf04d84d44d24d0cd08d13 := seed 6822434 rfl
lemma f769 : H a 13643043 := seed 6822465 rfl
lemma f770 : H a 0xf04d84d44d14d0cd08d23 := seed 6822466 rfl
lemma f771 : H a 0xf04e84e44e24e14e0ce08e01 := seed 7340035 rfl
lemma f772 : H a 14691847 := seed 7347209 rfl
lemma f773 : H a 14691851 := seed 7347217 rfl
lemma f774 : H a 0xf04e84e44e24e14e08e0b := seed 7347218 rfl
lemma f775 : H a 14691859 := seed 7347233 rfl
lemma f776 : H a 0xf04e84e44e24e0ce08e13 := seed 7347234 rfl
lemma f777 : H a 14691875 := seed 7347265 rfl
lemma f778 : H a 0xf04e84e44e14e0ce08e23 := seed 7347266 rfl
lemma f779 : H a 60164939839 := seed 917628 rfl
lemma f780 : H a 60148158527 := seed 917629 rfl
lemma f781 : H a 55871021119 := seed 1441916 rfl
lemma f782 : H a 55854239807 := seed 1441917 rfl
lemma f783 : H a 47283183679 := seed 2490492 rfl
lemma f784 : H a 47266402367 := seed 2490493 rfl
lemma f785 : H a 30107508799 := seed 4587644 rfl
lemma f786 : H a 30090727487 := seed 4587645 rfl
lemma f787 : H a 53724061759 := seed 1704060 rfl
lemma f788 : H a 53707280447 := seed 1704061 rfl
lemma f789 : H a 45136224319 := seed 2752636 rfl
lemma f790 : H a 45119443007 := seed 2752637 rfl
lemma f791 : H a 27960549439 := seed 4849788 rfl
lemma f792 : H a 27943768127 := seed 4849789 rfl
lemma f793 : H a 40842305599 := seed 3276924 rfl
lemma f794 : H a 40825524287 := seed 3276925 rfl
lemma f795 : H a 23666630719 := seed 5374076 rfl
lemma f796 : H a 23649849407 := seed 5374077 rfl
lemma f797 : H a 15078793279 := seed 6422652 rfl
lemma f798 : H a 15062011967 := seed 6422653 rfl
lemma f799 : H a 83712169222207 := seed 3758489726 rfl
lemma f800 : H a 83643432964159 := seed 3758489727 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f801 : H a 0x8c22c21c203f := seed 5905973374 rfl
lemma f802 : H a 0x8c12c11c103f := seed 5905973375 rfl
lemma f803 : H a 0x8c24c21c203f := seed 6979715198 rfl
lemma f804 : H a 0x8c24c22c203f := seed 7516586110 rfl
lemma f805 : H a 92510409728063 := seed 3490316414 rfl
lemma f806 : H a 92441673470015 := seed 3490316415 rfl
lemma f807 : H a 0x9423421c203f := seed 5637800062 rfl
lemma f808 : H a 0x9413411c103f := seed 5637800063 rfl
lemma f809 : H a 0x9425421c203f := seed 6711541886 rfl
lemma f810 : H a 0x9415411c103f := seed 6711541887 rfl
lemma f811 : H a 0x94254234203f := seed 7516848254 rfl
lemma f812 : H a 0x94154134103f := seed 7516848255 rfl
lemma f813 : H a 0x6423422c203f := seed 2953969790 rfl
lemma f814 : H a 0xa423422c203f := seed 5101453438 rfl
lemma f815 : H a 0xa413412c103f := seed 5101453439 rfl
lemma f816 : H a 0xa426422c203f := seed 6712066174 rfl
lemma f817 : H a 0xa416412c103f := seed 6712066175 rfl
lemma f818 : H a 0xa4264234203f := seed 6980501630 rfl
lemma f819 : H a 0xa4164134103f := seed 6980501631 rfl
lemma f820 : H a 0x6425424c203f := seed 1881276542 rfl
lemma f821 : H a 0x6415414c103f := seed 1881276543 rfl
lemma f822 : H a 0xc425424c203f := seed 5102502014 rfl
lemma f823 : H a 0xc415414c103f := seed 5102502015 rfl
lemma f824 : H a 0xc426424c203f := seed 5639372926 rfl
lemma f825 : H a 0xc416414c103f := seed 5639372927 rfl
lemma f826 : H a 0xc4264254203f := seed 5907808382 rfl
lemma f827 : H a 0xc4164154103f := seed 5907808383 rfl
lemma f828 : H a 0xa429428c203f := seed 1883373694 rfl
lemma f829 : H a 0xa419418c103f := seed 1883373695 rfl
lemma f830 : H a 0xc429428c203f := seed 2957115518 rfl
lemma f831 : H a 0xc419418c103f := seed 2957115519 rfl
lemma f832 : H a 0xc42a428c203f := seed 3493986430 rfl
lemma f833 : H a 0xc42a4294203f := seed 3762421886 rfl
lemma f834 : H a 0xc41a4194103f := seed 3762421887 rfl
lemma f835 : H a 0x9813811c103f := seed 5503713407 rfl
lemma f836 : H a 0x9825821c203f := seed 6577455230 rfl
lemma f837 : H a 0x9815811c103f := seed 6577455231 rfl
lemma f838 : H a 0x98258238203f := seed 7516979326 rfl
lemma f839 : H a 0x98158138103f := seed 7516979327 rfl
lemma f840 : H a 0x6823822c203f := seed 2819883134 rfl
lemma f841 : H a 0xa823822c203f := seed 4967366782 rfl
lemma f842 : H a 0x6825824c203f := seed 1747189886 rfl
lemma f843 : H a 0x6815814c103f := seed 1747189887 rfl
lemma f844 : H a 0xc825824c203f := seed 4968415358 rfl
lemma f845 : H a 0xc815814c103f := seed 4968415359 rfl
lemma f846 : H a 0xc826824c203f := seed 5505286270 rfl
lemma f847 : H a 0xc816814c103f := seed 5505286271 rfl
lemma f848 : H a 0xc8268258203f := seed 5907939454 rfl
lemma f849 : H a 0xc8168158103f := seed 5907939455 rfl
lemma f850 : H a 0xa829828c203f := seed 1749287038 rfl
lemma f851 : H a 0xa819818c103f := seed 1749287039 rfl
lemma f852 : H a 0xc819818c103f := seed 2823028863 rfl
lemma f853 : H a 0xc82a828c203f := seed 3359899774 rfl
lemma f854 : H a 0xc81a8198103f := seed 3762552959 rfl
lemma f855 : H a 0x70238234203f := seed 2551709822 rfl
lemma f856 : H a 0x70138134103f := seed 2551709823 rfl
lemma f857 : H a 0xb0238234203f := seed 4699193470 rfl
lemma f858 : H a 0xb0138134103f := seed 4699193471 rfl
lemma f859 : H a 0xb0270234203f := seed 6578241662 rfl
lemma f860 : H a 0xb0170134103f := seed 6578241663 rfl
lemma f861 : H a 0xb0270238203f := seed 6712459390 rfl
lemma f862 : H a 0xb0170138103f := seed 6712459391 rfl
lemma f863 : H a 0x70258254203f := seed 1479016574 rfl
lemma f864 : H a 0x70158154103f := seed 1479016575 rfl
lemma f865 : H a 0xd0258254203f := seed 4700242046 rfl
lemma f866 : H a 0xd0270254203f := seed 5505548414 rfl
lemma f867 : H a 0xd0170154103f := seed 5505548415 rfl
lemma f868 : H a 0xd0270258203f := seed 5639766142 rfl
lemma f869 : H a 0xb0298294203f := seed 1481113726 rfl
lemma f870 : H a 0xb0198194103f := seed 1481113727 rfl
lemma f871 : H a 0xd0298294203f := seed 2554855550 rfl
lemma f872 : H a 0xd0198194103f := seed 2554855551 rfl
lemma f873 : H a 0xd02b0294203f := seed 3360161918 rfl
lemma f874 : H a 0xd01b0194103f := seed 3360161919 rfl
lemma f875 : H a 0xd02b0298203f := seed 3494379646 rfl
lemma f876 : H a 0xd01b0198103f := seed 3494379647 rfl
lemma f877 : H a 0x70168164103f := seed 942669951 rfl
lemma f878 : H a 0xe0268264203f := seed 4700766334 rfl
lemma f879 : H a 0xe0270264203f := seed 4969201790 rfl
lemma f880 : H a 0xe0170164103f := seed 4969201791 rfl
lemma f881 : H a 0xe0270268203f := seed 5103419518 rfl
lemma f882 : H a 0xe0170168103f := seed 5103419519 rfl
lemma f883 : H a 0xb02a82a4203f := seed 944767102 rfl
lemma f884 : H a 0xb01a81a4103f := seed 944767103 rfl
lemma f885 : H a 0xe02b02a4203f := seed 2823815294 rfl
lemma f886 : H a 0xe01b01a4103f := seed 2823815295 rfl
lemma f887 : H a 0xe02b02a8203f := seed 2958033022 rfl
lemma f888 : H a 0xd02c82c4203f := seed 945815678 rfl
lemma f889 : H a 0xd01c81c4103f := seed 945815679 rfl
lemma f890 : H a 0xe01c81c4103f := seed 1482686591 rfl
lemma f891 : H a 0xe02d02c4203f := seed 1751122046 rfl
lemma f892 : H a 0xe01d01c4103f := seed 1751122047 rfl
lemma f893 : H a 0xe02d02c8203f := seed 1885339774 rfl
lemma f894 : H a 0xe01d01c8103f := seed 1885339775 rfl
lemma f895 : H a 60148027487 := seed 852157 rfl
lemma f896 : H a 47283052639 := seed 2425020 rfl
lemma f897 : H a 47266271327 := seed 2425021 rfl
lemma f898 : H a 30090596447 := seed 4522173 rfl
lemma f899 : H a 53723930719 := seed 1638588 rfl
lemma f900 : H a 53707149407 := seed 1638589 rfl
lemma f901 : H a 45119311967 := seed 2687165 rfl
lemma f902 : H a 27943637087 := seed 4784317 rfl
lemma f903 : H a 0x8a14a11a105f := seed 6979649727 rfl
lemma f904 : H a 90242113212511 := seed 3490250943 rfl
lemma f905 : H a 0xa213212a105f := seed 5101387967 rfl
lemma f906 : H a 0xc21a2192105f := seed 3762356415 rfl
lemma f907 : H a 96909529849951 := seed 3289120958 rfl
lemma f908 : H a 0xc825824a205f := seed 4901306558 rfl
lemma f909 : H a 0x70238232205f := seed 2484601022 rfl
lemma f910 : H a 55870627999 := seed 1245500 rfl
lemma f911 : H a 55853846687 := seed 1245501 rfl
lemma f912 : H a 47266009247 := seed 2294077 rfl
lemma f913 : H a 30090334367 := seed 4391229 rfl
lemma f914 : H a 22592757919 := seed 5308732 rfl
lemma f915 : H a 0x86146116109f := seed 6979518783 rfl
lemma f916 : H a 0x92132116109f := seed 5503516991 rfl
lemma f917 : H a 0xa2262226209f := seed 6577783102 rfl
lemma f918 : H a 0xc2192186109f := seed 2822832447 rfl
lemma f919 : H a 0xa4134126109f := seed 4900127039 rfl
lemma f920 : H a 0xb0234232209f := seed 4497867070 rfl
lemma f921 : H a 0xb01a41a2109f := seed 743440703 rfl
lemma f922 : H a 0xe01d01c4109f := seed 1751122239 rfl
lemma f923 : H a 53723144479 := seed 1245756 rfl
lemma f924 : H a 44061827359 := seed 2425404 rfl
lemma f925 : H a 44045046047 := seed 2425405 rfl
lemma f926 : H a 26869371167 := seed 4522557 rfl
lemma f927 : H a 20428493087 := seed 5308989 rfl
lemma f928 : H a 11840655647 := seed 6357565 rfl
lemma f929 : H a 0x8614610e111f := seed 6711083583 rfl
lemma f930 : H a 0x8a14a10e111f := seed 6576996927 rfl
lemma f931 : H a 0xc2262246211f := seed 5505090110 rfl
lemma f932 : H a 0xc824c24a211f := seed 4498653758 rfl
lemma f933 : H a 55852274207 := seed 459837 rfl
lemma f934 : H a 53705314847 := seed 721981 rfl
lemma f935 : H a 40823558687 := seed 2294845 rfl
lemma f936 : H a 23664665119 := seed 4391996 rfl
lemma f937 : H a 23647883807 := seed 4391997 rfl
lemma f938 : H a 52631835167 := seed 853053 rfl
lemma f939 : H a 39766860319 := seed 2425916 rfl
lemma f940 : H a 39750079007 := seed 2425917 rfl
lemma f941 : H a 20444226079 := seed 4785212 rfl
lemma f942 : H a 0xc414c146121f := seed 4632740927 rfl
lemma f943 : H a 0xc418c186121f := seed 2487354431 rfl
lemma f944 : H a 96846165447199 := seed 740557887 rfl
lemma f945 : H a 45115380767 := seed 723005 rfl
lemma f946 : H a 40838243359 := seed 1247292 rfl
lemma f947 : H a 15057949727 := seed 4393021 rfl
lemma f948 : H a 13984470047 := seed 4524093 rfl
lemma f949 : H a 37601023007 := seed 1640509 rfl
lemma f950 : H a 0x8611610e141f := seed 5100472383 rfl
lemma f951 : H a 0x8a11a10e141f := seed 4966385727 rfl
lemma f952 : H a 0x92132116141f := seed 5503518783 rfl
lemma f953 : H a 0x9218a186141f := seed 943786047 rfl
lemma f954 : H a 48454764991519 := seed 1678116927 rfl
lemma f955 : H a 0xa4134126141f := seed 4900128831 rfl
lemma f956 : H a 0xb0234232241f := seed 4497868862 rfl
lemma f957 : H a 0xb0138132141f := seed 4632086591 rfl
lemma f958 : H a 30082471967 := seed 462909 rfl
lemma f959 : H a 27952293919 := seed 725052 rfl
lemma f960 : H a 27935512607 := seed 725053 rfl
lemma f961 : H a 23658375199 := seed 1249340 rfl
lemma f962 : H a 23641593887 := seed 1249341 rfl
lemma f963 : H a 22568114207 := seed 1380413 rfl
lemma f964 : H a 13997058079 := seed 2428988 rfl
lemma f965 : H a 13980276767 := seed 2428989 rfl
lemma f966 : H a 20437936159 := seed 1642556 rfl
lemma f967 : H a 20421154847 := seed 1642557 rfl
lemma f968 : H a 7539398687 := seed 3215421 rfl
lemma f969 : H a 77040456701983 := seed 2952990783 rfl
lemma f970 : H a 81439576954911 := seed 2818904127 rfl
lemma f971 : H a 55120034670623 := seed 1476988990 rfl
lemma f972 : H a 0x62132126181f := seed 2819690559 rfl
lemma f973 : H a 48454764992543 := seed 1678118975 rfl
lemma f974 : H a 0x6813812a181f := seed 2752778303 rfl
lemma f975 : H a 0x6814c14a181f := seed 1277431871 rfl
lemma f976 : H a 0x6825824a281f := seed 1680085054 rfl
lemma f977 : H a 0x70138132181f := seed 2484604991 rfl
lemma f978 : H a 30090530927 := seed 4489437 rfl
lemma f979 : H a 53723865199 := seed 1605852 rfl
lemma f980 : H a 53707083887 := seed 1605853 rfl
lemma f981 : H a 27943571567 := seed 4751581 rfl
lemma f982 : H a 89142333083759 := seed 3490218207 rfl
lemma f983 : H a 0xc8158149106f := seed 4867752159 rfl
lemma f984 : H a 47265943727 := seed 2261341 rfl
lemma f985 : H a 39768367279 := seed 3178844 rfl
lemma f986 : H a 0xa423422520af := seed 4866572638 rfl
lemma f987 : H a 0xc41a418510af := seed 3259105631 rfl
lemma f988 : H a 0xd01b019110af := seed 3259498847 rfl
lemma f989 : H a 60163957039 := seed 426588 rfl
lemma f990 : H a 60147175727 := seed 426589 rfl
lemma f991 : H a 53723078959 := seed 1213020 rfl
lemma f992 : H a 45135241519 := seed 2261596 rfl
lemma f993 : H a 27959566639 := seed 4358748 rfl
lemma f994 : H a 44061761839 := seed 2392668 rfl
lemma f995 : H a 44044980527 := seed 2392669 rfl
lemma f996 : H a 26869305647 := seed 4489821 rfl
lemma f997 : H a 11840590127 := seed 6324829 rfl
lemma f998 : H a 0xe0264261212f := seed 4465885790 rfl
lemma f999 : H a 55852208687 := seed 427101 rfl
lemma f1000 : H a 53705249327 := seed 689245 rfl
lemma f1001 : H a 39766794799 := seed 2393180 rfl
lemma f1002 : H a 20427379247 := seed 4752477 rfl
lemma f1003 : H a 7545623087 := seed 6325341 rfl
lemma f1004 : H a 80339796824623 := seed 2818868319 rfl
lemma f1005 : H a 96833277334063 := seed 2316043359 rfl
lemma f1006 : H a 0x9811c119122f := seed 4463527007 rfl
lemma f1007 : H a 0xc824c249222f := seed 4465099870 rfl
lemma f1008 : H a 0xc814c149122f := seed 4465099871 rfl
lemma f1009 : H a 0xc8158149122f := seed 4867753055 rfl
lemma f1010 : H a 47262274607 := seed 428125 rfl
lemma f1011 : H a 44041835567 := seed 821341 rfl
lemma f1012 : H a 40756304483375 := seed 1879214175 rfl
lemma f1013 : H a 45155424736303 := seed 1745127519 rfl
lemma f1014 : H a 57250858472495 := seed 1376389215 rfl
lemma f1015 : H a 0xa4234225242f := seed 4866574430 rfl
lemma f1016 : H a 30082406447 := seed 430173 rfl
lemma f1017 : H a 27952228399 := seed 692316 rfl
lemma f1018 : H a 27935447087 := seed 692317 rfl
lemma f1019 : H a 15070472239 := seed 2265180 rfl
lemma f1020 : H a 15053690927 := seed 2265181 rfl
lemma f1021 : H a 26878748719 := seed 823388 rfl
lemma f1022 : H a 26861967407 := seed 823389 rfl
lemma f1023 : H a 22584829999 := seed 1347676 rfl
lemma f1024 : H a 22568048687 := seed 1347677 rfl
lemma f1025 : H a 20437870639 := seed 1609820 rfl
lemma f1026 : H a 20421089327 := seed 1609821 rfl
lemma f1027 : H a 11833251887 := seed 2658397 rfl
lemma f1028 : H a 40756304484399 := seed 1879216223 rfl
lemma f1029 : H a 45155424737327 := seed 1745129567 rfl
lemma f1030 : H a 80339796826159 := seed 2818871391 rfl
lemma f1031 : H a 80344091793455 := seed 3355742303 rfl
lemma f1032 : H a 92448118609967 := seed 841093215 rfl
lemma f1033 : H a 0x6414c145182f := seed 1377964127 rfl
lemma f1034 : H a 60147568847 := seed 623005 rfl
lemma f1035 : H a 0xd01b019110cf := seed 3259498911 rfl
lemma f1036 : H a 53722947919 := seed 1147548 rfl
lemma f1037 : H a 19891556687 := seed 5276317 rfl
lemma f1038 : H a 0xc1189183114f := seed 2487255711 rfl
lemma f1039 : H a 0xa228a283214f := seed 1379992222 rfl
lemma f1040 : H a 0xc22a2283214f := seed 3259040414 rfl
lemma f1041 : H a 0xc814a149114f := seed 4397990559 rfl
lemma f1042 : H a 0xe01c81c2114f := seed 1415578271 rfl
lemma f1043 : H a 55868858959 := seed 361628 rfl
lemma f1044 : H a 53721899599 := seed 623772 rfl
lemma f1045 : H a 23647687247 := seed 4293789 rfl
lemma f1046 : H a 0xc1189183124f := seed 2487256223 rfl
lemma f1047 : H a 0xc225224a224f := seed 5102437534 rfl
lemma f1048 : H a 0xc218a183124f := seed 2453734559 rfl
lemma f1049 : H a 0x9811a119124f := seed 4396418207 rfl
lemma f1050 : H a 0xc824a249224f := seed 4397991070 rfl
lemma f1051 : H a 0xc814a149124f := seed 4397991071 rfl
lemma f1052 : H a 0xc825824a224f := seed 4901307550 rfl
lemma f1053 : H a 0xd0258252224f := seed 4633134238 rfl
lemma f1054 : H a 0xd0158152124f := seed 4633134239 rfl
lemma f1055 : H a 0xd01c81c2124f := seed 878707871 rfl
lemma f1056 : H a 45115184207 := seed 624797 rfl
lemma f1057 : H a 15074534479 := seed 4294812 rfl
lemma f1058 : H a 0x98138119144f := seed 5403052191 rfl
lemma f1059 : H a 0x9813811a144f := seed 5436606623 rfl
lemma f1060 : H a 0xa8138129144f := seed 4866705567 rfl
lemma f1061 : H a 0xb0138131144f := seed 4598532255 rfl
lemma f1062 : H a 0xb0238232244f := seed 4632086686 rfl
lemma f1063 : H a 26325096527 := seed 823453 rfl
lemma f1064 : H a 13443340367 := seed 2396317 rfl
lemma f1065 : H a 80339796695119 := seed 2751762591 rfl
lemma f1066 : H a 44061368719 := seed 2196252 rfl
lemma f1067 : H a 26885693839 := seed 4293404 rfl
lemma f1068 : H a 43507847567 := seed 2261789 rfl
lemma f1069 : H a 0x86146126118f := seed 7516390175 rfl
lemma f1070 : H a 0xc41c21c1118f := seed 241173279 rfl
lemma f1071 : H a 22590726799 := seed 4293916 rfl
lemma f1072 : H a 52094636687 := seed 689437 rfl
lemma f1073 : H a 18816766607 := seed 4752669 rfl
lemma f1074 : H a 5935010447 := seed 6325533 rfl
lemma f1075 : H a 0xc1191185128f := seed 2822800671 rfl
lemma f1076 : H a 0xd0254252228f := seed 4498916638 rfl
lemma f1077 : H a 44058223759 := seed 624924 rfl
lemma f1078 : H a 44041442447 := seed 624925 rfl
lemma f1079 : H a 39747523727 := seed 1149213 rfl
lemma f1080 : H a 13984011407 := seed 4294941 rfl
lemma f1081 : H a 43504702607 := seed 690461 rfl
lemma f1082 : H a 5932913807 := seed 5277981 rfl
lemma f1083 : H a 54019180668047 := seed 1275627806 rfl
lemma f1084 : H a 0xa1185183148f := seed 1279297823 rfl
lemma f1085 : H a 0xa2232223248f := seed 4866509086 rfl
lemma f1086 : H a 0xa2132126148f := seed 4967172383 rfl
lemma f1087 : H a 0xa2186183148f := seed 1245776159 rfl
lemma f1088 : H a 57317984117903 := seed 1175062814 rfl
lemma f1089 : H a 57249247859855 := seed 1175062815 rfl
lemma f1090 : H a 0x94134115148f := seed 5402921247 rfl
lemma f1091 : H a 0x94234216248f := seed 5436475678 rfl
lemma f1092 : H a 0xa4134125148f := seed 4866574623 rfl
lemma f1093 : H a 0xa4234226248f := seed 4900129054 rfl
lemma f1094 : H a 0xa4134126148f := seed 4900129055 rfl
lemma f1095 : H a 0xa4194186148f := seed 1682049311 rfl
lemma f1096 : H a 57256765887631 := seed 236456223 rfl
lemma f1097 : H a 0xb0134132148f := seed 4497869087 rfl
lemma f1098 : H a 0xb0294291248f := seed 1246234910 rfl
lemma f1099 : H a 0xb0194192148f := seed 1279789343 rfl
lemma f1100 : H a 0xb02a22a1248f := seed 642779422 rfl
lemma f1101 : H a 26324834447 := seed 692509 rfl
lemma f1102 : H a 0x70134132188f := seed 2350387487 rfl
lemma f1103 : H a 53721113359 := seed 230940 rfl
lemma f1104 : H a 52094112527 := seed 427549 rfl
lemma f1105 : H a 19889722127 := seed 4359709 rfl
lemma f1106 : H a 0xc1189183130f := seed 2487256607 rfl
lemma f1107 : H a 0x8c24c20d230f := seed 6476400158 rfl
lemma f1108 : H a 0xc814c149130f := seed 4465100319 rfl
lemma f1109 : H a 0xc824c24a230f := seed 4498654750 rfl
lemma f1110 : H a 0xc814c14a130f := seed 4498654751 rfl
lemma f1111 : H a 44057699599 := seed 363036 rfl
lemma f1112 : H a 11853309199 := seed 4295196 rfl
lemma f1113 : H a 43504178447 := seed 428573 rfl
lemma f1114 : H a 0x8612610e150f := seed 5637343775 rfl
lemma f1115 : H a 48451006829839 := seed 1174800927 rfl
lemma f1116 : H a 0xa418c186150f := seed 1413614111 rfl
lemma f1117 : H a 0xa822c229250f := seed 4464052766 rfl
lemma f1118 : H a 26324310287 := seed 430621 rfl
lemma f1119 : H a 19883432207 := seed 1217053 rfl
lemma f1120 : H a 10222115087 := seed 2396701 rfl
lemma f1121 : H a 77044751669519 := seed 3489862175 rfl
lemma f1122 : H a 48451006830863 := seed 1174802975 rfl
lemma f1123 : H a 0x6824c24a290f := seed 1277432350 rfl
lemma f1124 : H a 0x6814c14a190f := seed 1277432351 rfl
lemma f1125 : H a 37615773199 := seed 625692 rfl
lemma f1126 : H a 37062252047 := seed 691229 rfl
lemma f1127 : H a 0x8611610e160f := seed 5100473375 rfl
lemma f1128 : H a 23656344079 := seed 234524 rfl
lemma f1129 : H a 7537367567 := seed 2200605 rfl
lemma f1130 : H a 89148778420751 := seed 941659167 rfl
lemma f1131 : H a 77040456702479 := seed 2952991775 rfl
lemma f1132 : H a 30858820786703 := seed 637932575 rfl
lemma f1133 : H a 96846165383695 := seed 707007519 rfl
lemma f1134 : H a 96917049715215 := seed 472388638 rfl
lemma f1135 : H a 13439409167 := seed 432157 rfl
lemma f1136 : H a 6998531087 := seed 1218589 rfl
lemma f1137 : H a 23161970564111 := seed 872585247 rfl
lemma f1138 : H a 57249247861775 := seed 1175066655 rfl
lemma f1139 : H a 61721937587215 := seed 739514398 rfl
lemma f1140 : H a 60147929207 := seed 803053 rfl
lemma f1141 : H a 47266173047 := seed 2375917 rfl
lemma f1142 : H a 30107279479 := seed 4473068 rfl
lemma f1143 : H a 30090498167 := seed 4473069 rfl
lemma f1144 : H a 53707051127 := seed 1589485 rfl
lemma f1145 : H a 23666401399 := seed 5259500 rfl
lemma f1146 : H a 23649620087 := seed 5259501 rfl
lemma f1147 : H a 0x88a48a18a077 := seed 6979600622 rfl
lemma f1148 : H a 0xc81581489077 := seed 4850974959 rfl
lemma f1149 : H a 0xe02a82a0a077 := seed 2437939438 rfl
lemma f1150 : H a 0xd01c81c09077 := seed 828375279 rfl
lemma f1151 : H a 60147667127 := seed 672109 rfl
lemma f1152 : H a 47265910967 := seed 2244973 rfl
lemma f1153 : H a 44062253239 := seed 2638188 rfl
lemma f1154 : H a 44045471927 := seed 2638189 rfl
lemma f1155 : H a 22592659639 := seed 5259628 rfl
lemma f1156 : H a 13988040887 := seed 6308205 rfl
lemma f1157 : H a 0x94234214a0b7 := seed 5386142062 rfl
lemma f1158 : H a 0x9413411490b7 := seed 5386142063 rfl
lemma f1159 : H a 0xa4234224a0b7 := seed 4849795438 rfl
lemma f1160 : H a 0xa413412490b7 := seed 4849795439 rfl
lemma f1161 : H a 0xb01a41a090b7 := seed 693109103 rfl
lemma f1162 : H a 0xd01c41c090b7 := seed 694157679 rfl
lemma f1163 : H a 60163924279 := seed 410220 rfl
lemma f1164 : H a 60147142967 := seed 410221 rfl
lemma f1165 : H a 53723046199 := seed 1196652 rfl
lemma f1166 : H a 53706264887 := seed 1196653 rfl
lemma f1167 : H a 27942752567 := seed 4342381 rfl
lemma f1168 : H a 44061729079 := seed 2376300 rfl
lemma f1169 : H a 26869272887 := seed 4473453 rfl
lemma f1170 : H a 20428394807 := seed 5259885 rfl
lemma f1171 : H a 11840557367 := seed 6308461 rfl
lemma f1172 : H a 0xa09289249137 := seed 4698686063 rfl
lemma f1173 : H a 0xe02a82a0a137 := seed 2437939822 rfl
lemma f1174 : H a 55852175927 := seed 410733 rfl
lemma f1175 : H a 53721997879 := seed 672876 rfl
lemma f1176 : H a 53705216567 := seed 672877 rfl
lemma f1177 : H a 23647785527 := seed 4342893 rfl
lemma f1178 : H a 52631736887 := seed 803949 rfl
lemma f1179 : H a 39766762039 := seed 2376812 rfl
lemma f1180 : H a 37603021367 := seed 2638957 rfl
lemma f1181 : H a 20444127799 := seed 4736108 rfl
lemma f1182 : H a 20427346487 := seed 4736109 rfl
lemma f1183 : H a 7545590327 := seed 6308973 rfl
lemma f1184 : H a 88598888354359 := seed 941638767 rfl
lemma f1185 : H a 0xc09909889237 := seed 2957001839 rfl
lemma f1186 : H a 0xc418c1849237 := seed 2437022831 rfl
lemma f1187 : H a 0xc81581489237 := seed 4850975855 rfl
lemma f1188 : H a 0xd0254250a237 := seed 4448584814 rfl
lemma f1189 : H a 47262241847 := seed 411757 rfl
lemma f1190 : H a 45132063799 := seed 673900 rfl
lemma f1191 : H a 45115282487 := seed 673901 rfl
lemma f1192 : H a 15074632759 := seed 4343916 rfl
lemma f1193 : H a 39764665399 := seed 1329260 rfl
lemma f1194 : H a 39747884087 := seed 1329261 rfl
lemma f1195 : H a 14001153079 := seed 4474988 rfl
lemma f1196 : H a 13984371767 := seed 4474989 rfl
lemma f1197 : H a 37600924727 := seed 1591405 rfl
lemma f1198 : H a 40206414418999 := seed 1879197807 rfl
lemma f1199 : H a 0xa09289249437 := seed 4698687599 rfl
lemma f1200 : H a 57319594697783 := seed 1359612014 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f1201 : H a 0x941341149437 := seed 5386143855 rfl
lemma f1202 : H a 0xa4234224a437 := seed 4849797230 rfl
lemma f1203 : H a 0xa41341249437 := seed 4849797231 rfl
lemma f1204 : H a 0xb01941909437 := seed 1229457519 rfl
lemma f1205 : H a 0xb01a41a09437 := seed 693110895 rfl
lemma f1206 : H a 30082373687 := seed 413805 rfl
lemma f1207 : H a 27952195639 := seed 675948 rfl
lemma f1208 : H a 23658276919 := seed 1200236 rfl
lemma f1209 : H a 23641495607 := seed 1200237 rfl
lemma f1210 : H a 15070439479 := seed 2248812 rfl
lemma f1211 : H a 26878715959 := seed 807020 rfl
lemma f1212 : H a 26861934647 := seed 807021 rfl
lemma f1213 : H a 13996959799 := seed 2379884 rfl
lemma f1214 : H a 13980178487 := seed 2379885 rfl
lemma f1215 : H a 20437837879 := seed 1593452 rfl
lemma f1216 : H a 11850000439 := seed 2642028 rfl
lemma f1217 : H a 11833219127 := seed 2642029 rfl
lemma f1218 : H a 7539300407 := seed 3166317 rfl
lemma f1219 : H a 40206414420023 := seed 1879199855 rfl
lemma f1220 : H a 0x609309289837 := seed 2953859183 rfl
lemma f1221 : H a 88598888355895 := seed 941641839 rfl
lemma f1222 : H a 57319594698807 := seed 1359614062 rfl
lemma f1223 : H a 57323890714679 := seed 823267438 rfl
lemma f1224 : H a 0x64234224a837 := seed 2702315630 rfl
lemma f1225 : H a 96846165350455 := seed 690229359 rfl
lemma f1226 : H a 0x681581489837 := seed 1629753455 rfl
lemma f1227 : H a 0x70268260a837 := seed 825233518 rfl
lemma f1228 : H a 60147536087 := seed 606637 rfl
lemma f1229 : H a 0x9213211290d7 := seed 5386076591 rfl
lemma f1230 : H a 0x70232230a0d7 := seed 2232943022 rfl
lemma f1231 : H a 0xd017015210d7 := seed 5438439855 rfl
lemma f1232 : H a 0xb019219090d7 := seed 1162346927 rfl
lemma f1233 : H a 0xe017016210d7 := seed 4902093231 rfl
lemma f1234 : H a 27959402839 := seed 4276908 rfl
lemma f1235 : H a 27942621527 := seed 4276909 rfl
lemma f1236 : H a 11303686487 := seed 6308525 rfl
lemma f1237 : H a 0x8294290a9157 := seed 6710969007 rfl
lemma f1238 : H a 0xc09889829157 := seed 2487239343 rfl
lemma f1239 : H a 0xa228a282a157 := seed 1363215022 rfl
lemma f1240 : H a 0xc22a2282a157 := seed 3242263214 rfl
lemma f1241 : H a 0x6824a248a157 := seed 1159987886 rfl
lemma f1242 : H a 0x68262260a157 := seed 355467950 rfl
lemma f1243 : H a 0xc81c21c09157 := seed 358613679 rfl
lemma f1244 : H a 55852044887 := seed 345261 rfl
lemma f1245 : H a 40823329367 := seed 2180269 rfl
lemma f1246 : H a 23664435799 := seed 4277420 rfl
lemma f1247 : H a 23647654487 := seed 4277421 rfl
lemma f1248 : H a 52111647319 := seed 804012 rfl
lemma f1249 : H a 39229891159 := seed 2376876 rfl
lemma f1250 : H a 0x8291290a9257 := seed 5100356783 rfl
lemma f1251 : H a 0xc09889829257 := seed 2487239855 rfl
lemma f1252 : H a 81508312982103 := seed 2701460654 rfl
lemma f1253 : H a 0x8a14a11a1257 := seed 6979650735 rfl
lemma f1254 : H a 0xc218a1829257 := seed 2436957359 rfl
lemma f1255 : H a 96832740430423 := seed 2232157359 rfl
lemma f1256 : H a 96914364736087 := seed 623117486 rfl
lemma f1257 : H a 0xc81581489257 := seed 4850975919 rfl
lemma f1258 : H a 0xc82c22c0a257 := seed 358614190 rfl
lemma f1259 : H a 0xc81c21c09257 := seed 358614191 rfl
lemma f1260 : H a 0xd02c22c0a257 := seed 627049646 rfl
lemma f1261 : H a 0xd02c82c22257 := seed 878707886 rfl
lemma f1262 : H a 45115151447 := seed 608429 rfl
lemma f1263 : H a 15074501719 := seed 4278444 rfl
lemma f1264 : H a 15057720407 := seed 4278445 rfl
lemma f1265 : H a 0x829229129457 := seed 5905664175 rfl
lemma f1266 : H a 61648368342103 := seed 1158416559 rfl
lemma f1267 : H a 0x9813811a1457 := seed 5436606639 rfl
lemma f1268 : H a 61721400616023 := seed 622069934 rfl
lemma f1269 : H a 0xa813812a1457 := seed 4900260015 rfl
lemma f1270 : H a 0x9818a1889457 := seed 625215663 rfl
lemma f1271 : H a 0xa818a1889457 := seed 1162086575 rfl
lemma f1272 : H a 61723548623959 := seed 353896622 rfl
lemma f1273 : H a 0xb01321309457 := seed 4380428463 rfl
lemma f1274 : H a 0xb01921909457 := seed 1162348719 rfl
lemma f1275 : H a 30099023959 := seed 348332 rfl
lemma f1276 : H a 30082242647 := seed 348333 rfl
lemma f1277 : H a 27935283287 := seed 610477 rfl
lemma f1278 : H a 23658145879 := seed 1134764 rfl
lemma f1279 : H a 26325063767 := seed 807085 rfl
lemma f1280 : H a 22047926359 := seed 1331372 rfl
lemma f1281 : H a 44605534541911 := seed 1678004399 rfl
lemma f1282 : H a 79794201598039 := seed 3288617135 rfl
lemma f1283 : H a 90242113214551 := seed 3490255023 rfl
lemma f1284 : H a 61648368343127 := seed 1158418607 rfl
lemma f1285 : H a 96845628479575 := seed 623120559 rfl
lemma f1286 : H a 0x68258248a857 := seed 1629753518 rfl
lemma f1287 : H a 0x6815814a1857 := seed 1680085167 rfl
lemma f1288 : H a 61723548624983 := seed 353898670 rfl
lemma f1289 : H a 0x701321309857 := seed 2232946863 rfl
lemma f1290 : H a 0x70238230a857 := seed 2434273454 rfl
lemma f1291 : H a 0x70252250a857 := seed 1160253614 rfl
lemma f1292 : H a 0x701581509857 := seed 1361580207 rfl
lemma f1293 : H a 44061335959 := seed 2179884 rfl
lemma f1294 : H a 26885661079 := seed 4277036 rfl
lemma f1295 : H a 26868879767 := seed 4277037 rfl
lemma f1296 : H a 0xa41861849197 := seed 1161954095 rfl
lemma f1297 : H a 0xc41c21c09197 := seed 224396079 rfl
lemma f1298 : H a 52094603927 := seed 673069 rfl
lemma f1299 : H a 0x829129069297 := seed 4966139183 rfl
lemma f1300 : H a 0x909149129297 := seed 4496835887 rfl
lemma f1301 : H a 0x861461161297 := seed 6979519791 rfl
lemma f1302 : H a 0xc41861849297 := seed 2235696431 rfl
lemma f1303 : H a 0xc42c22c0a297 := seed 224396590 rfl
lemma f1304 : H a 0xd02c22c0a297 := seed 627049774 rfl
lemma f1305 : H a 14000759959 := seed 4278572 rfl
lemma f1306 : H a 13983978647 := seed 4278573 rfl
lemma f1307 : H a 13447238807 := seed 4344109 rfl
lemma f1308 : H a 35990312087 := seed 1591597 rfl
lemma f1309 : H a 0x829129069497 := seed 4966140207 rfl
lemma f1310 : H a 0x849149069497 := seed 4899096879 rfl
lemma f1311 : H a 53469290603671 := seed 1275611438 rfl
lemma f1312 : H a 0xa0a30a24a497 := seed 4967123246 rfl
lemma f1313 : H a 0xa09849829497 := seed 1279281455 rfl
lemma f1314 : H a 0x921321129497 := seed 5386078511 rfl
lemma f1315 : H a 0xa21261229497 := seed 4447078703 rfl
lemma f1316 : H a 0xa21321261497 := seed 4967172399 rfl
lemma f1317 : H a 57317984085143 := seed 1158285614 rfl
lemma f1318 : H a 57249247827095 := seed 1158285615 rfl
lemma f1319 : H a 0x941341149497 := seed 5386144047 rfl
lemma f1320 : H a 0x942342162497 := seed 5436475694 rfl
lemma f1321 : H a 0xa41341249497 := seed 4849797423 rfl
lemma f1322 : H a 0xa41341261497 := seed 4900129071 rfl
lemma f1323 : H a 30081980567 := seed 217389 rfl
lemma f1324 : H a 26861541527 := seed 610605 rfl
lemma f1325 : H a 13996566679 := seed 2183468 rfl
lemma f1326 : H a 13979785367 := seed 2183469 rfl
lemma f1327 : H a 13443045527 := seed 2249005 rfl
lemma f1328 : H a 53469290604695 := seed 1275613486 rfl
lemma f1329 : H a 57317984086167 := seed 1158287662 rfl
lemma f1330 : H a 57249247828119 := seed 1158287663 rfl
lemma f1331 : H a 57253543843991 := seed 621941039 rfl
lemma f1332 : H a 0x701341321897 := seed 2350387503 rfl
lemma f1333 : H a 53704299287 := seed 214573 rfl
lemma f1334 : H a 20443210519 := seed 4277804 rfl
lemma f1335 : H a 20426429207 := seed 4277805 rfl
lemma f1336 : H a 35991884567 := seed 2377261 rfl
lemma f1337 : H a 3787494167 := seed 6309421 rfl
lemma f1338 : H a 0xc09889829317 := seed 2487240239 rfl
lemma f1339 : H a 0xc228a282a317 := seed 2436957742 rfl
lemma f1340 : H a 0xc41861849317 := seed 2235696687 rfl
lemma f1341 : H a 0xc814c14a1317 := seed 4498654767 rfl
lemma f1342 : H a 0xc42c22c0a317 := seed 224396846 rfl
lemma f1343 : H a 0xc41c21c09317 := seed 224396847 rfl
lemma f1344 : H a 0xc82c22c0a317 := seed 358614574 rfl
lemma f1345 : H a 44057666839 := seed 346668 rfl
lemma f1346 : H a 11853276439 := seed 4278828 rfl
lemma f1347 : H a 11836495127 := seed 4278829 rfl
lemma f1348 : H a 10226275607 := seed 4475437 rfl
lemma f1349 : H a 0x8c10e10c9517 := seed 4379249199 rfl
lemma f1350 : H a 0xa41261249517 := seed 4380035631 rfl
lemma f1351 : H a 0xa41861849517 := seed 1161955887 rfl
lemma f1352 : H a 0xa818a1889517 := seed 1162086959 rfl
lemma f1353 : H a 0xa41a21a09517 := seed 223349295 rfl
lemma f1354 : H a 27934497047 := seed 217645 rfl
lemma f1355 : H a 26324277527 := seed 414253 rfl
lemma f1356 : H a 19883399447 := seed 1200685 rfl
lemma f1357 : H a 10222082327 := seed 2380333 rfl
lemma f1358 : H a 81443871922455 := seed 3355775535 rfl
lemma f1359 : H a 0x641261249917 := seed 2232554031 rfl
lemma f1360 : H a 0x6412c1249917 := seed 2433880623 rfl
lemma f1361 : H a 0x6824a248a917 := seed 1159991854 rfl
lemma f1362 : H a 0x6824c248a917 := seed 1227100718 rfl
lemma f1363 : H a 0x6824c24a2917 := seed 1277432366 rfl
lemma f1364 : H a 0x6814c14a1917 := seed 1277432367 rfl
lemma f1365 : H a 0x68262260a917 := seed 355471918 rfl
lemma f1366 : H a 7558309399 := seed 4279340 rfl
lemma f1367 : H a 0x829129069617 := seed 4966140975 rfl
lemma f1368 : H a 0x849149069617 := seed 4899097647 rfl
lemma f1369 : H a 0x909149129617 := seed 4496837679 rfl
lemma f1370 : H a 30858820752919 := seed 621153327 rfl
lemma f1371 : H a 30929705018903 := seed 352980014 rfl
lemma f1372 : H a 0x941161149617 := seed 4379511855 rfl
lemma f1373 : H a 0x8c1861849617 := seed 356650031 rfl
lemma f1374 : H a 20435872279 := seed 611372 rfl
lemma f1375 : H a 19882351127 := seed 676909 rfl
lemma f1376 : H a 20412520372759 := seed 939611183 rfl
lemma f1377 : H a 30858820753943 := seed 621155375 rfl
lemma f1378 : H a 30929705019927 := seed 352982062 rfl
lemma f1379 : H a 92433619917335 := seed 2232030255 rfl
lemma f1380 : H a 92435230530071 := seed 2433356847 rfl
lemma f1381 : H a 96914364738071 := seed 623121454 rfl
lemma f1382 : H a 96845628480023 := seed 623121455 rfl
lemma f1383 : H a 96846165449239 := seed 740561967 rfl
lemma f1384 : H a 96917049715223 := seed 472388654 rfl
lemma f1385 : H a 11829156887 := seed 612397 rfl
lemma f1386 : H a 7552019479 := seed 1136684 rfl
lemma f1387 : H a 13439376407 := seed 415789 rfl
lemma f1388 : H a 53469290605591 := seed 1275615278 rfl
lemma f1389 : H a 30858820754455 := seed 621156399 rfl
lemma f1390 : H a 57249247829015 := seed 1158289455 rfl
lemma f1391 : H a 57319594699799 := seed 1359616046 rfl
lemma f1392 : H a 57250858441751 := seed 1359616047 rfl
lemma f1393 : H a 57253543844887 := seed 621942831 rfl
lemma f1394 : H a 61721400618007 := seed 622073902 rfl
lemma f1395 : H a 61721937587223 := seed 739514414 rfl
lemma f1396 : H a 60164251879 := seed 573900 rfl
lemma f1397 : H a 55870333159 := seed 1098188 rfl
lemma f1398 : H a 47282495719 := seed 2146764 rfl
lemma f1399 : H a 0xe01a11a090e7 := seed 2203058639 rfl
lemma f1400 : H a 0xe01d01c090e7 := seed 1633681871 rfl
lemma f1401 : H a 53722849639 := seed 1098444 rfl
lemma f1402 : H a 53706068327 := seed 1098445 rfl
lemma f1403 : H a 43239641447 := seed 2376397 rfl
lemma f1404 : H a 0xc09889819167 := seed 2453684943 rfl
lemma f1405 : H a 0xc11891819167 := seed 2436924111 rfl
lemma f1406 : H a 0x681491489167 := seed 1126433487 rfl
lemma f1407 : H a 0xc81491489167 := seed 4347658959 rfl
lemma f1408 : H a 0xc81a81889167 := seed 3242459855 rfl
lemma f1409 : H a 0xe01c81c09167 := seed 1365246671 rfl
lemma f1410 : H a 0xe02c82c12167 := seed 1382023886 rfl
lemma f1411 : H a 55868760679 := seed 312524 rfl
lemma f1412 : H a 53721801319 := seed 574668 rfl
lemma f1413 : H a 53705020007 := seed 574669 rfl
lemma f1414 : H a 23664370279 := seed 4244684 rfl
lemma f1415 : H a 38961455719 := seed 2376908 rfl
lemma f1416 : H a 38944674407 := seed 2376909 rfl
lemma f1417 : H a 0x981191189267 := seed 4346086607 rfl
lemma f1418 : H a 0xc81491489267 := seed 4347659471 rfl
lemma f1419 : H a 0xc81581489267 := seed 4850975951 rfl
lemma f1420 : H a 0xd01981909267 := seed 2437416143 rfl
lemma f1421 : H a 0xd01981911267 := seed 2454193359 rfl
lemma f1422 : H a 0xd01c81c09267 := seed 828376271 rfl
lemma f1423 : H a 47278826599 := seed 313548 rfl
lemma f1424 : H a 45131867239 := seed 575692 rfl
lemma f1425 : H a 40837948519 := seed 1099980 rfl
lemma f1426 : H a 40821167207 := seed 1099981 rfl
lemma f1427 : H a 0x889289099467 := seed 5402544335 rfl
lemma f1428 : H a 53951518053479 := seed 1359513807 rfl
lemma f1429 : H a 0x981381191467 := seed 5403052239 rfl
lemma f1430 : H a 0xa81381291467 := seed 4866705615 rfl
lemma f1431 : H a 0xb01381309467 := seed 4581755087 rfl
lemma f1432 : H a 0xb01381311467 := seed 4598532303 rfl
lemma f1433 : H a 0xa81a11a09467 := seed 324012239 rfl
lemma f1434 : H a 30098958439 := seed 315596 rfl
lemma f1435 : H a 30082177127 := seed 315597 rfl
lemma f1436 : H a 27951999079 := seed 577740 rfl
lemma f1437 : H a 23658080359 := seed 1102028 rfl
lemma f1438 : H a 15070242919 := seed 2150604 rfl
lemma f1439 : H a 13174872167 := seed 2379981 rfl
lemma f1440 : H a 19615750247 := seed 1593549 rfl
lemma f1441 : H a 0x609309289867 := seed 2953859279 rfl
lemma f1442 : H a 53951518054503 := seed 1359515855 rfl
lemma f1443 : H a 96909529753703 := seed 3238793422 rfl
lemma f1444 : H a 96909529786471 := seed 3255570638 rfl
lemma f1445 : H a 96914096302183 := seed 589566158 rfl
lemma f1446 : H a 0x681491489867 := seed 1126437071 rfl
lemma f1447 : H a 0x70238230a867 := seed 2434273486 rfl
lemma f1448 : H a 0x701681611867 := seed 842010831 rfl
lemma f1449 : H a 60163465639 := seed 181068 rfl
lemma f1450 : H a 60146684327 := seed 181069 rfl
lemma f1451 : H a 52649107879 := seed 1098572 rfl
lemma f1452 : H a 52632326567 := seed 1098573 rfl
lemma f1453 : H a 44061270439 := seed 2147148 rfl
lemma f1454 : H a 43239379367 := seed 2245453 rfl
lemma f1455 : H a 18549346727 := seed 5260109 rfl
lemma f1456 : H a 0xc41a418511a7 := seed 3259106127 rfl
lemma f1457 : H a 55851717287 := seed 181581 rfl
lemma f1458 : H a 39766303399 := seed 2147660 rfl
lemma f1459 : H a 22590628519 := seed 4244812 rfl
lemma f1460 : H a 35723973287 := seed 2639181 rfl
lemma f1461 : H a 5666542247 := seed 6309197 rfl
lemma f1462 : H a 0x81a11a05a2a7 := seed 4966106446 rfl
lemma f1463 : H a 0x9111511192a7 := seed 4446520655 rfl
lemma f1464 : H a 0xc419418492a7 := seed 2705458511 rfl
lemma f1465 : H a 47278564519 := seed 182604 rfl
lemma f1466 : H a 44058125479 := seed 575820 rfl
lemma f1467 : H a 44041344167 := seed 575821 rfl
lemma f1468 : H a 39764206759 := seed 1100108 rfl
lemma f1469 : H a 39747425447 := seed 1100109 rfl
lemma f1470 : H a 14000694439 := seed 4245836 rfl
lemma f1471 : H a 13983913127 := seed 4245837 rfl
lemma f1472 : H a 43236234407 := seed 674125 rfl
lemma f1473 : H a 0x8191190594a7 := seed 4966107471 rfl
lemma f1474 : H a 54019180569767 := seed 1225296206 rfl
lemma f1475 : H a 0xa1291281a4a7 := seed 1631619406 rfl
lemma f1476 : H a 57248979391655 := seed 1124731215 rfl
lemma f1477 : H a 0x9413411494a7 := seed 5386144079 rfl
lemma f1478 : H a 0x9413411514a7 := seed 5402921295 rfl
lemma f1479 : H a 57322011665575 := seed 588384590 rfl
lemma f1480 : H a 0xa412512494a7 := seed 4346480975 rfl
lemma f1481 : H a 0xa4234224a4a7 := seed 4849797454 rfl
lemma f1482 : H a 0xa419418494a7 := seed 1631717711 rfl
lemma f1483 : H a 0xb013413094a7 := seed 4447537487 rfl
lemma f1484 : H a 0xb019419114a7 := seed 1246234959 rfl
lemma f1485 : H a 0xb01a41a094a7 := seed 693111119 rfl
lemma f1486 : H a 30098696359 := seed 184652 rfl
lemma f1487 : H a 26878257319 := seed 577868 rfl
lemma f1488 : H a 13996501159 := seed 2150732 rfl
lemma f1489 : H a 21762447527 := seed 1200461 rfl
lemma f1490 : H a 5660252327 := seed 3166541 rfl
lemma f1491 : H a 57248979392679 := seed 1124733263 rfl
lemma f1492 : H a 53721015079 := seed 181836 rfl
lemma f1493 : H a 53704233767 := seed 181837 rfl
lemma f1494 : H a 52647535399 := seed 312908 rfl
lemma f1495 : H a 20443144999 := seed 4245068 rfl
lemma f1496 : H a 20426363687 := seed 4245069 rfl
lemma f1497 : H a 35723449127 := seed 2377293 rfl
lemma f1498 : H a 0xc09889819327 := seed 2453685839 rfl
lemma f1499 : H a 0xc11891819327 := seed 2436925007 rfl
lemma f1500 : H a 0x8c24c20d2327 := seed 6476400206 rfl
lemma f1501 : H a 0xc418c1849327 := seed 2437023311 rfl
lemma f1502 : H a 83651220509479 := seed 186910287 rfl
lemma f1503 : H a 0xc824c248a327 := seed 4448323150 rfl
lemma f1504 : H a 45131080999 := seed 182860 rfl
lemma f1505 : H a 44057601319 := seed 313932 rfl
lemma f1506 : H a 37599941927 := seed 1100365 rfl
lemma f1507 : H a 3516962087 := seed 5261901 rfl
lemma f1508 : H a 48450738361639 := seed 1124469327 rfl
lemma f1509 : H a 0xa41251249527 := seed 4346481231 rfl
lemma f1510 : H a 0xa822c2292527 := seed 4464052814 rfl
lemma f1511 : H a 27951212839 := seed 184908 rfl
lemma f1512 : H a 27934431527 := seed 184909 rfl
lemma f1513 : H a 26877733159 := seed 315980 rfl
lemma f1514 : H a 20436855079 := seed 1102412 rfl
lemma f1515 : H a 20420073767 := seed 1102413 rfl
lemma f1516 : H a 11849017639 := seed 2150988 rfl
lemma f1517 : H a 19614964007 := seed 1200717 rfl
lemma f1518 : H a 9953646887 := seed 2380365 rfl
lemma f1519 : H a 48450738362663 := seed 1124471375 rfl
lemma f1520 : H a 0x6824c248a927 := seed 1227100750 rfl
lemma f1521 : H a 40819332647 := seed 183373 rfl
lemma f1522 : H a 39762634279 := seed 314444 rfl
lemma f1523 : H a 37598893607 := seed 576589 rfl
lemma f1524 : H a 5662873127 := seed 4475981 rfl
lemma f1525 : H a 0x81a11a05a627 := seed 4966108238 rfl
lemma f1526 : H a 27010127205927 := seed 704924751 rfl
lemma f1527 : H a 27560017237543 := seed 688163919 rfl
lemma f1528 : H a 0x911151119627 := seed 4446522447 rfl
lemma f1529 : H a 30858552317479 := seed 587598927 rfl
lemma f1530 : H a 0x9418c1849627 := seed 826412111 rfl
lemma f1531 : H a 23656245799 := seed 185420 rfl
lemma f1532 : H a 22582766119 := seed 316492 rfl
lemma f1533 : H a 22565984807 := seed 316493 rfl
lemma f1534 : H a 20435806759 := seed 578636 rfl
lemma f1535 : H a 19613915687 := seed 676941 rfl
lemma f1536 : H a 5658679847 := seed 2380877 rfl
lemma f1537 : H a 27010127206951 := seed 704926799 rfl
lemma f1538 : H a 30860700326439 := seed 319427663 rfl
lemma f1539 : H a 92433351481895 := seed 2198475855 rfl
lemma f1540 : H a 92435230530087 := seed 2433356879 rfl
lemma f1541 : H a 96914096302631 := seed 589567054 rfl
lemma f1542 : H a 15049530407 := seed 186445 rfl
lemma f1543 : H a 11845872679 := seed 579660 rfl
lemma f1544 : H a 11829091367 := seed 579661 rfl
lemma f1545 : H a 6730062887 := seed 1202253 rfl
lemma f1546 : H a 9967283239 := seed 809036 rfl
lemma f1547 : H a 9950501927 := seed 809037 rfl
lemma f1548 : H a 5673364519 := seed 1333324 rfl
lemma f1549 : H a 27560017239079 := seed 688166991 rfl
lemma f1550 : H a 45152203283495 := seed 1225037903 rfl
lemma f1551 : H a 30858552319015 := seed 587601999 rfl
lemma f1552 : H a 48450738363431 := seed 1124472911 rfl
lemma f1553 : H a 48523501153319 := seed 1627789390 rfl
lemma f1554 : H a 48454764895271 := seed 1627789391 rfl
lemma f1555 : H a 57248979393575 := seed 1124735055 rfl
lemma f1556 : H a 57250858441767 := seed 1359616079 rfl
lemma f1557 : H a 61648905215015 := seed 1225529423 rfl
lemma f1558 : H a 61717641505831 := seed 1242306638 rfl
lemma f1559 : H a 61653201230887 := seed 689182799 rfl
lemma f1560 : H a 60146553287 := seed 115597 rfl
lemma f1561 : H a 18029257159 := seed 5260172 rfl
lemma f1562 : H a 9441419719 := seed 6308748 rfl
lemma f1563 : H a 0x8192190391c7 := seed 5435868047 rfl
lemma f1564 : H a 0x8292290391c7 := seed 5402346383 rfl
lemma f1565 : H a 0x8294290391c7 := seed 6476088207 rfl
lemma f1566 : H a 0xc098298191c7 := seed 2252358543 rfl
lemma f1567 : H a 0x8314310391c7 := seed 6459327375 rfl
lemma f1568 : H a 0xa112312191c7 := seed 4379935631 rfl
lemma f1569 : H a 0xc118318191c7 := seed 2235597711 rfl
lemma f1570 : H a 0xc11a118191c7 := seed 3242230671 rfl
lemma f1571 : H a 0xa2283282a1c7 := seed 1128334222 rfl
lemma f1572 : H a 55851586247 := seed 116109 rfl
lemma f1573 : H a 0x8191190392c7 := seed 4898997647 rfl
lemma f1574 : H a 0x8291290392c7 := seed 4865475983 rfl
lemma f1575 : H a 0x8294290392c7 := seed 6476088719 rfl
lemma f1576 : H a 0x8311310392c7 := seed 4848715151 rfl
lemma f1577 : H a 0xc2283282a2c7 := seed 2202076558 rfl
lemma f1578 : H a 0xc218318292c7 := seed 2202076559 rfl
lemma f1579 : H a 0xd029229122c7 := seed 2252866958 rfl
lemma f1580 : H a 47261652167 := seed 117133 rfl
lemma f1581 : H a 13463823559 := seed 4245900 rfl
lemma f1582 : H a 38958965959 := seed 1132940 rfl
lemma f1583 : H a 13195453639 := seed 4278668 rfl
lemma f1584 : H a 9438274759 := seed 4737420 rfl
lemma f1585 : H a 5127574727 := seed 5261709 rfl
lemma f1586 : H a 0x8191190394c7 := seed 4898998671 rfl
lemma f1587 : H a 0x8192190394c7 := seed 5435869583 rfl
lemma f1588 : H a 0x81a21a11a4c7 := seed 5905631630 rfl
lemma f1589 : H a 0x8291290394c7 := seed 4865477007 rfl
lemma f1590 : H a 0x8292290394c7 := seed 5402347919 rfl
lemma f1591 : H a 0x82a22a12a4c7 := seed 5905664398 rfl
lemma f1592 : H a 53404313425095 := seed 638601615 rfl
lemma f1593 : H a 0xa098298194c7 := seed 1178618255 rfl
lemma f1594 : H a 0x9113111194c7 := seed 5386045839 rfl
lemma f1595 : H a 53954203456711 := seed 621840783 rfl
lemma f1596 : H a 0xa119118314c7 := seed 1681951119 rfl
lemma f1597 : H a 55118155392199 := seed 1124665742 rfl
lemma f1598 : H a 0x92283282a4c7 := seed 591464846 rfl
lemma f1599 : H a 0xa2283282a4c7 := seed 1128335758 rfl
lemma f1600 : H a 0xa218318294c7 := seed 1128335759 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f1601 : H a 0xb0291290a4c7 := seed 1128794510 rfl
lemma f1602 : H a 30081784007 := seed 119181 rfl
lemma f1603 : H a 38006853703879 := seed 1644253583 rfl
lemma f1604 : H a 0x6216116098c7 := seed 120590735 rfl
lemma f1605 : H a 53704102727 := seed 116365 rfl
lemma f1606 : H a 52093883207 := seed 312973 rfl
lemma f1607 : H a 37081948999 := seed 2147980 rfl
lemma f1608 : H a 19906274119 := seed 4245132 rfl
lemma f1609 : H a 19889492807 := seed 4245133 rfl
lemma f1610 : H a 51842294599 := seed 345740 rfl
lemma f1611 : H a 19637904199 := seed 4277900 rfl
lemma f1612 : H a 35203359559 := seed 2377356 rfl
lemma f1613 : H a 35186578247 := seed 2377357 rfl
lemma f1614 : H a 18010903367 := seed 4474509 rfl
lemma f1615 : H a 2982187847 := seed 6309517 rfl
lemma f1616 : H a 0x819099039347 := seed 4630562447 rfl
lemma f1617 : H a 0x819419039347 := seed 6509610639 rfl
lemma f1618 : H a 0x8290a9039347 := seed 4597040783 rfl
lemma f1619 : H a 0x829429039347 := seed 6476088975 rfl
lemma f1620 : H a 0x88a82a81a347 := seed 373311118 rfl
lemma f1621 : H a 0xc0a82a81a347 := seed 2252359310 rfl
lemma f1622 : H a 0xc09889819347 := seed 2453685903 rfl
lemma f1623 : H a 0x8310b1039347 := seed 4580279951 rfl
lemma f1624 : H a 0x831431039347 := seed 6459328143 rfl
lemma f1625 : H a 81504286450503 := seed 2198144654 rfl
lemma f1626 : H a 0x8a283282a347 := seed 323028622 rfl
lemma f1627 : H a 0xc2283282a347 := seed 2202076814 rfl
lemma f1628 : H a 81452197253959 := seed 119801487 rfl
lemma f1629 : H a 0xc824a248a347 := seed 4381214350 rfl
lemma f1630 : H a 45114168647 := seed 117389 rfl
lemma f1631 : H a 43503949127 := seed 313997 rfl
lemma f1632 : H a 9437750599 := seed 4475532 rfl
lemma f1633 : H a 36904926156103 := seed 1409337999 rfl
lemma f1634 : H a 0x819099039547 := seed 4630563471 rfl
lemma f1635 : H a 0x819219039547 := seed 5435869839 rfl
lemma f1636 : H a 0x8290a9039547 := seed 4597041807 rfl
lemma f1637 : H a 0x829229039547 := seed 5402348175 rfl
lemma f1638 : H a 0x8892890a9547 := seed 5436099215 rfl
lemma f1639 : H a 0xa09289229547 := seed 4631579279 rfl
lemma f1640 : H a 0x889829819547 := seed 373312143 rfl
lemma f1641 : H a 0x891831819547 := seed 356551311 rfl
lemma f1642 : H a 0xa11891819547 := seed 1363184271 rfl
lemma f1643 : H a 0xa2283282a547 := seed 1128336014 rfl
lemma f1644 : H a 19899984199 := seed 1102476 rfl
lemma f1645 : H a 19614832967 := seed 1135245 rfl
lemma f1646 : H a 9433557319 := seed 2380428 rfl
lemma f1647 : H a 9416776007 := seed 2380429 rfl
lemma f1648 : H a 81504286452039 := seed 2198147726 rfl
lemma f1649 : H a 0x6822a228a947 := seed 2232685198 rfl
lemma f1650 : H a 81452197255495 := seed 119804559 rfl
lemma f1651 : H a 40819201607 := seed 117901 rfl
lemma f1652 : H a 38940612167 := seed 347277 rfl
lemma f1653 : H a 6753003079 := seed 4279436 rfl
lemma f1654 : H a 6736221767 := seed 4279437 rfl
lemma f1655 : H a 0x819119039647 := seed 4898999439 rfl
lemma f1656 : H a 0x8290a9039647 := seed 4597042319 rfl
lemma f1657 : H a 0x829129039647 := seed 4865477775 rfl
lemma f1658 : H a 0x831131039647 := seed 4848716943 rfl
lemma f1659 : H a 0x8a1831829647 := seed 323030159 rfl
lemma f1660 : H a 0x92283282a647 := seed 591465614 rfl
lemma f1661 : H a 28662751073863 := seed 118230159 rfl
lemma f1662 : H a 0x921911909647 := seed 122162319 rfl
lemma f1663 : H a 0x982922912647 := seed 373820558 rfl
lemma f1664 : H a 23639333447 := seed 119949 rfl
lemma f1665 : H a 19898935879 := seed 578700 rfl
lemma f1666 : H a 21777525319 := seed 349324 rfl
lemma f1667 : H a 19630565959 := seed 611468 rfl
lemma f1668 : H a 19613784647 := seed 611469 rfl
lemma f1669 : H a 6748809799 := seed 2184332 rfl
lemma f1670 : H a 5138590279 := seed 2380940 rfl
lemma f1671 : H a 5121808967 := seed 2380941 rfl
lemma f1672 : H a 19312740112967 := seed 872469647 rfl
lemma f1673 : H a 20412520176199 := seed 838947983 rfl
lemma f1674 : H a 73191225793095 := seed 2717996175 rfl
lemma f1675 : H a 88654736370247 := seed 2450019470 rfl
lemma f1676 : H a 88654736435783 := seed 2483573902 rfl
lemma f1677 : H a 88586000177735 := seed 2483573903 rfl
lemma f1678 : H a 89135890143815 := seed 2433258639 rfl
lemma f1679 : H a 28729876326983 := seed 319362190 rfl
lemma f1680 : H a 90302527482439 := seed 2198410382 rfl
lemma f1681 : H a 81452197255751 := seed 119805071 rfl
lemma f1682 : H a 96914364738119 := seed 623121550 rfl
lemma f1683 : H a 96914364770887 := seed 639898766 rfl
lemma f1684 : H a 15049399367 := seed 120973 rfl
lemma f1685 : H a 11309001799 := seed 579724 rfl
lemma f1686 : H a 13170809927 := seed 350349 rfl
lemma f1687 : H a 11023850567 := seed 612493 rfl
lemma f1688 : H a 6729931847 := seed 1136781 rfl
lemma f1689 : H a 20412520176711 := seed 838949007 rfl
lemma f1690 : H a 38004706221127 := seed 1375819919 rfl
lemma f1691 : H a 38006853704775 := seed 1644255375 rfl
lemma f1692 : H a 45220402670663 := seed 1157929102 rfl
lemma f1693 : H a 53951518055495 := seed 1359517839 rfl
lemma f1694 : H a 54022939716679 := seed 621844622 rfl
lemma f1695 : H a 28662751075399 := seed 118233231 rfl
lemma f1696 : H a 52630360967 := seed 116493 rfl
lemma f1697 : H a 0x819059039387 := seed 4496344847 rfl
lemma f1698 : H a 0x829069039387 := seed 4462823183 rfl
lemma f1699 : H a 0x829429039387 := seed 6476089103 rfl
lemma f1700 : H a 0xc09829819387 := seed 2252359439 rfl
lemma f1701 : H a 0xc11831819387 := seed 2235598607 rfl
lemma f1702 : H a 0x86283282a387 := seed 188811022 rfl
lemma f1703 : H a 44040426887 := seed 117517 rfl
lemma f1704 : H a 43503687047 := seed 183053 rfl
lemma f1705 : H a 36006110599 := seed 1100556 rfl
lemma f1706 : H a 10225816967 := seed 4246285 rfl
lemma f1707 : H a 43252098439 := seed 215820 rfl
lemma f1708 : H a 43235317127 := seed 215821 rfl
lemma f1709 : H a 9974228359 := seed 4279052 rfl
lemma f1710 : H a 35201000839 := seed 1198860 rfl
lemma f1711 : H a 35184219527 := seed 1198861 rfl
lemma f1712 : H a 1906349447 := seed 5262093 rfl
lemma f1713 : H a 0x819219039587 := seed 5435869967 rfl
lemma f1714 : H a 0x81a21a05a587 := seed 5502978830 rfl
lemma f1715 : H a 38003632477575 := seed 1241598735 rfl
lemma f1716 : H a 0x829069039587 := seed 4462824207 rfl
lemma f1717 : H a 0x829229039587 := seed 5402348303 rfl
lemma f1718 : H a 0x82a22a06a587 := seed 5503011598 rfl
lemma f1719 : H a 40271392122247 := seed 1174555406 rfl
lemma f1720 : H a 0x849069059587 := seed 4395780879 rfl
lemma f1721 : H a 0x84a82a81a587 := seed 239094542 rfl
lemma f1722 : H a 0xa0a82a81a587 := seed 1178618638 rfl
lemma f1723 : H a 38553522509191 := seed 1224837903 rfl
lemma f1724 : H a 0x831071039587 := seed 4446063375 rfl
lemma f1725 : H a 0x831231039587 := seed 5385587471 rfl
lemma f1726 : H a 40821282153863 := seed 1157794574 rfl
lemma f1727 : H a 0x85207205a587 := seed 4379020046 rfl
lemma f1728 : H a 0x851251059587 := seed 5385653007 rfl
lemma f1729 : H a 0x851251071587 := seed 5435984655 rfl
lemma f1730 : H a 0xa1223221a587 := seed 4379937550 rfl
lemma f1731 : H a 0xa11231219587 := seed 4379937551 rfl
lemma f1732 : H a 0xa1285281a587 := seed 1228966670 rfl
lemma f1733 : H a 0xa11851831587 := seed 1279298319 rfl
lemma f1734 : H a 0x86207206a587 := seed 4345498382 rfl
lemma f1735 : H a 0x861071069587 := seed 4345498383 rfl
lemma f1736 : H a 0x861261069587 := seed 5385685775 rfl
lemma f1737 : H a 0x86283282a587 := seed 188812046 rfl
lemma f1738 : H a 0xa21831829587 := seed 1128336143 rfl
lemma f1739 : H a 41860112618887 := seed 118622991 rfl
lemma f1740 : H a 0xa4226224a587 := seed 4380035854 rfl
lemma f1741 : H a 0xa42a12a0a587 := seed 189795086 rfl
lemma f1742 : H a 26860558727 := seed 119565 rfl
lemma f1743 : H a 10238404999 := seed 2151180 rfl
lemma f1744 : H a 9416513927 := seed 2249485 rfl
lemma f1745 : H a 38003632478599 := seed 1241600783 rfl
lemma f1746 : H a 40821282154887 := seed 1157796622 rfl
lemma f1747 : H a 41860112619911 := seed 118625039 rfl
lemma f1748 : H a 0x621611609987 := seed 120591119 rfl
lemma f1749 : H a 39745459847 := seed 118029 rfl
lemma f1750 : H a 35988280967 := seed 576781 rfl
lemma f1751 : H a 38940350087 := seed 216333 rfl
lemma f1752 : H a 5679261319 := seed 4279564 rfl
lemma f1753 : H a 35199952519 := seed 675084 rfl
lemma f1754 : H a 35183171207 := seed 675085 rfl
lemma f1755 : H a 0x819059039687 := seed 4496346383 rfl
lemma f1756 : H a 0x819119039687 := seed 4898999567 rfl
lemma f1757 : H a 0x829069039687 := seed 4462824719 rfl
lemma f1758 : H a 0x829129039687 := seed 4865477903 rfl
lemma f1759 : H a 0x82a12a06a687 := seed 4966141198 rfl
lemma f1760 : H a 0x84a82a81a687 := seed 239095054 rfl
lemma f1761 : H a 0x849829819687 := seed 239095055 rfl
lemma f1762 : H a 0x90a82a81a687 := seed 641748238 rfl
lemma f1763 : H a 0x831071039687 := seed 4446063887 rfl
lemma f1764 : H a 0x831131039687 := seed 4848717071 rfl
lemma f1765 : H a 0x851151071687 := seed 4899114255 rfl
lemma f1766 : H a 0x911151119687 := seed 4446522639 rfl
lemma f1767 : H a 24331829814919 := seed 185142542 rfl
lemma f1768 : H a 0x92213212a687 := seed 4345892110 rfl
lemma f1769 : H a 0x86283282a687 := seed 188812558 rfl
lemma f1770 : H a 0x861831829687 := seed 188812559 rfl
lemma f1771 : H a 0x921861829687 := seed 692129039 rfl
lemma f1772 : H a 24263630558855 := seed 118099215 rfl
lemma f1773 : H a 0x861851849687 := seed 121769231 rfl
lemma f1774 : H a 0x94286284a687 := seed 625085710 rfl
lemma f1775 : H a 0x94291290a687 := seed 189271310 rfl
lemma f1776 : H a 22565591687 := seed 120077 rfl
lemma f1777 : H a 18825194119 := seed 578828 rfl
lemma f1778 : H a 5658286727 := seed 2184461 rfl
lemma f1779 : H a 18020084359 := seed 677132 rfl
lemma f1780 : H a 20411446434439 := seed 704730383 rfl
lemma f1781 : H a 13975657607 := seed 121101 rfl
lemma f1782 : H a 13455699079 := seed 186636 rfl
lemma f1783 : H a 10235260039 := seed 579852 rfl
lemma f1784 : H a 10218478727 := seed 579853 rfl
lemma f1785 : H a 5941341319 := seed 1104140 rfl
lemma f1786 : H a 5924560007 := seed 1104141 rfl
lemma f1787 : H a 13170547847 := seed 219405 rfl
lemma f1788 : H a 9966890119 := seed 612620 rfl
lemma f1789 : H a 5672971399 := seed 1136908 rfl
lemma f1790 : H a 5656190087 := seed 1136909 rfl
lemma f1791 : H a 9413368967 := seed 678157 rfl
lemma f1792 : H a 5136231559 := seed 1202444 rfl
lemma f1793 : H a 1899011207 := seed 1595661 rfl
lemma f1794 : H a 19311666371719 := seed 738253071 rfl
lemma f1795 : H a 36903852416135 := seed 1275123983 rfl
lemma f1796 : H a 36907073641607 := seed 1677777167 rfl
lemma f1797 : H a 36975810030727 := seed 1744886030 rfl
lemma f1798 : H a 20411446434951 := seed 704731407 rfl
lemma f1799 : H a 38006853704839 := seed 1644255503 rfl
lemma f1800 : H a 22682428091527 := seed 235428110 rfl
lemma f1801 : H a 53400554282119 := seed 1242061071 rfl
lemma f1802 : H a 40278910151815 := seed 235952398 rfl
lemma f1803 : H a 53404850363527 := seed 739268879 rfl
lemma f1804 : H a 38556743736455 := seed 1627494671 rfl
lemma f1805 : H a 40821282155655 := seed 1157798158 rfl
lemma f1806 : H a 23232318123143 := seed 218667278 rfl
lemma f1807 : H a 23163581865095 := seed 218667279 rfl
lemma f1808 : H a 54022939716743 := seed 621844750 rfl
lemma f1809 : H a 55118155394183 := seed 1124669710 rfl
lemma f1810 : H a 41859575618695 := seed 185669903 rfl
lemma f1811 : H a 55122451410055 := seed 588323086 rfl
lemma f1812 : H a 55054520458375 := seed 688986383 rfl
lemma f1813 : H a 55054520491143 := seed 705763599 rfl
lemma f1814 : H a 57317984087175 := seed 1158289678 rfl
lemma f1815 : H a 57317984119943 := seed 1175066894 rfl
lemma f1816 : H a 57322280103047 := seed 621943054 rfl
lemma f1817 : H a 57322280135815 := seed 638720270 rfl
lemma f1818 : H a 57325502114951 := seed 219683086 rfl
lemma f1819 : H a 57325502147719 := seed 236460302 rfl
lemma f1820 : H a 3514996487 := seed 4279821 rfl
lemma f1821 : H a 0x819059039707 := seed 4496346639 rfl
lemma f1822 : H a 0x819099039707 := seed 4630564367 rfl
lemma f1823 : H a 0x829069039707 := seed 4462824975 rfl
lemma f1824 : H a 0x889829819707 := seed 373313039 rfl
lemma f1825 : H a 0xd1071059707 := seed 352488975 rfl
lemma f1826 : H a 0x891831819707 := seed 356552207 rfl
lemma f1827 : H a 0x86207206a707 := seed 4345499150 rfl
lemma f1828 : H a 19898149639 := seed 185868 rfl
lemma f1829 : H a 19881368327 := seed 185869 rfl
lemma f1830 : H a 3510803207 := seed 2184717 rfl
lemma f1831 : H a 1917364999 := seed 2381324 rfl
lemma f1832 : H a 81452197255943 := seed 119805455 rfl
lemma f1833 : H a 83720225237767 := seed 237245966 rfl
lemma f1834 : H a 11828174087 := seed 121357 rfl
lemma f1835 : H a 11308215559 := seed 186892 rfl
lemma f1836 : H a 10234735879 := seed 317964 rfl
lemma f1837 : H a 2988748039 := seed 1202700 rfl
lemma f1838 : H a 36904926158087 := seed 1409341967 rfl
lemma f1839 : H a 38004706221319 := seed 1375820303 rfl
lemma f1840 : H a 38073442675975 := seed 1476483598 rfl
lemma f1841 : H a 0xd1071059d07 := seed 352492047 rfl
lemma f1842 : H a 41853936639239 := seed 1359157775 rfl
lemma f1843 : H a 0xe10d10c9d07 := seed 117840399 rfl
lemma f1844 : H a 41860112620807 := seed 118626831 rfl
lemma f1845 : H a 7533207047 := seed 121869 rfl
lemma f1846 : H a 6996467207 := seed 187405 rfl
lemma f1847 : H a 2970918407 := seed 678925 rfl
lemma f1848 : H a 20412520177159 := seed 838949903 rfl
lemma f1849 : H a 23161970564615 := seed 872586255 rfl
lemma f1850 : H a 60164694139 := seed 794868 rfl
lemma f1851 : H a 60147912827 := seed 794869 rfl
lemma f1852 : H a 47282937979 := seed 2367732 rfl
lemma f1853 : H a 47266156667 := seed 2367733 rfl
lemma f1854 : H a 53707034747 := seed 1581301 rfl
lemma f1855 : H a 45135978619 := seed 2629876 rfl
lemma f1856 : H a 27960303739 := seed 4727028 rfl
lemma f1857 : H a 27943522427 := seed 4727029 rfl
lemma f1858 : H a 40825278587 := seed 3154165 rfl
lemma f1859 : H a 0x90630618607b := seed 5637677302 rfl
lemma f1860 : H a 0x68138128507b := seed 2694054135 rfl
lemma f1861 : H a 0xc8258248607b := seed 4842586358 rfl
lemma f1862 : H a 0xc8158148507b := seed 4842586359 rfl
lemma f1863 : H a 0xc8198188507b := seed 2697199863 rfl
lemma f1864 : H a 0xe02d02c0607b := seed 1625293046 rfl
lemma f1865 : H a 60164432059 := seed 663924 rfl
lemma f1866 : H a 60147650747 := seed 663925 rfl
lemma f1867 : H a 30090219707 := seed 4333941 rfl
lemma f1868 : H a 22575861947 := seed 5251445 rfl
lemma f1869 : H a 14004805819 := seed 6300020 rfl
lemma f1870 : H a 0xc059058450bb := seed 2822775159 rfl
lemma f1871 : H a 0xa423422460bb := seed 4841406838 rfl
lemma f1872 : H a 0xa413412450bb := seed 4841406839 rfl
lemma f1873 : H a 0xa416412450bb := seed 6452019575 rfl
lemma f1874 : H a 0xa419418450bb := seed 1623327095 rfl
lemma f1875 : H a 0xc41a418450bb := seed 3233939831 rfl
lemma f1876 : H a 0xb01a41a050bb := seed 684720503 rfl
lemma f1877 : H a 60163907899 := seed 402036 rfl
lemma f1878 : H a 60147126587 := seed 402037 rfl
lemma f1879 : H a 53723029819 := seed 1188468 rfl
lemma f1880 : H a 53706248507 := seed 1188469 rfl
lemma f1881 : H a 27942736187 := seed 4334197 rfl
lemma f1882 : H a 52649550139 := seed 1319540 rfl
lemma f1883 : H a 44061712699 := seed 2368116 rfl
lemma f1884 : H a 44044931387 := seed 2368117 rfl
lemma f1885 : H a 26869256507 := seed 4465269 rfl
lemma f1886 : H a 20428378427 := seed 5251701 rfl
lemma f1887 : H a 55868940859 := seed 402548 rfl
lemma f1888 : H a 55852159547 := seed 402549 rfl
lemma f1889 : H a 53705200187 := seed 664693 rfl
lemma f1890 : H a 40823444027 := seed 2237557 rfl
lemma f1891 : H a 39749964347 := seed 2368629 rfl
lemma f1892 : H a 37619786299 := seed 2630772 rfl
lemma f1893 : H a 20444111419 := seed 4727924 rfl
lemma f1894 : H a 7545573947 := seed 6300789 rfl
lemma f1895 : H a 88323943322171 := seed 941630583 rfl
lemma f1896 : H a 0xc0590584523b := seed 2822775927 rfl
lemma f1897 : H a 0x9421c214623b := seed 4572447862 rfl
lemma f1898 : H a 0xc4254244623b := seed 4842456182 rfl
lemma f1899 : H a 0x98258218623b := seed 6451627126 rfl
lemma f1900 : H a 96914901590587 := seed 681837686 rfl
lemma f1901 : H a 96846165332539 := seed 681837687 rfl
lemma f1902 : H a 0xc8258248623b := seed 4842587254 rfl
lemma f1903 : H a 0xc8158148523b := seed 4842587255 rfl
lemma f1904 : H a 0xc8198188523b := seed 2697200759 rfl
lemma f1905 : H a 0x98194190523b := seed 415761527 rfl
lemma f1906 : H a 0xd0194190523b := seed 2294809719 rfl
lemma f1907 : H a 0xd01c81c0523b := seed 819987575 rfl
lemma f1908 : H a 47279006779 := seed 403572 rfl
lemma f1909 : H a 47262225467 := seed 403573 rfl
lemma f1910 : H a 45115266107 := seed 665717 rfl
lemma f1911 : H a 40821347387 := seed 1190005 rfl
lemma f1912 : H a 44058567739 := seed 796788 rfl
lemma f1913 : H a 44041786427 := seed 796789 rfl
lemma f1914 : H a 14001136699 := seed 4466804 rfl
lemma f1915 : H a 11837396027 := seed 4728949 rfl
lemma f1916 : H a 53126683186235 := seed 1476929655 rfl
lemma f1917 : H a 0x8c21c20c643b := seed 4840622198 rfl
lemma f1918 : H a 0x9421c214643b := seed 4572448886 rfl
lemma f1919 : H a 0x94234214643b := seed 5377755254 rfl
lemma f1920 : H a 0xa4234224643b := seed 4841408630 rfl
lemma f1921 : H a 0xa4134124543b := seed 4841408631 rfl
lemma f1922 : H a 0xa4194184543b := seed 1623328887 rfl
lemma f1923 : H a 0xb01a41a0543b := seed 684722295 rfl
lemma f1924 : H a 30099138619 := seed 405620 rfl
lemma f1925 : H a 27952179259 := seed 667764 rfl
lemma f1926 : H a 27935397947 := seed 667765 rfl
lemma f1927 : H a 23658260539 := seed 1192052 rfl
lemma f1928 : H a 23641479227 := seed 1192053 rfl
lemma f1929 : H a 26861918267 := seed 798837 rfl
lemma f1930 : H a 13996943419 := seed 2371700 rfl
lemma f1931 : H a 13980162107 := seed 2371701 rfl
lemma f1932 : H a 20437821499 := seed 1585268 rfl
lemma f1933 : H a 20421040187 := seed 1585269 rfl
lemma f1934 : H a 11833202747 := seed 2633845 rfl
lemma f1935 : H a 7556065339 := seed 3158132 rfl
lemma f1936 : H a 7539284027 := seed 3158133 rfl
lemma f1937 : H a 39931469387835 := seed 1879191671 rfl
lemma f1938 : H a 75120136968251 := seed 3758239863 rfl
lemma f1939 : H a 53126683187259 := seed 1476931703 rfl
lemma f1940 : H a 88323943323707 := seed 941633655 rfl
lemma f1941 : H a 57319594682427 := seed 1351225462 rfl
lemma f1942 : H a 57250858424379 := seed 1351225463 rfl
lemma f1943 : H a 92503966771259 := seed 2424967286 rfl
lemma f1944 : H a 57323890698299 := seed 814878838 rfl
lemma f1945 : H a 57255154440251 := seed 814878839 rfl
lemma f1946 : H a 0x64234224683b := seed 2693927030 rfl
lemma f1947 : H a 0x64134124583b := seed 2693927031 rfl
lemma f1948 : H a 96914901592123 := seed 681840758 rfl
lemma f1949 : H a 0x6814c148583b := seed 1218711671 rfl
lemma f1950 : H a 0x68258248683b := seed 1621364854 rfl
lemma f1951 : H a 55870382299 := seed 1122740 rfl
lemma f1952 : H a 0xb013213050db := seed 4372038071 rfl
lemma f1953 : H a 53722898779 := seed 1122996 rfl
lemma f1954 : H a 27942605147 := seed 4268725 rfl
lemma f1955 : H a 0xc0588582515b := seed 2487231159 rfl
lemma f1956 : H a 0xc814a148515b := seed 4372824759 rfl
lemma f1957 : H a 0xe01c81c2115b := seed 1415578295 rfl
lemma f1958 : H a 53705069147 := seed 599221 rfl
lemma f1959 : H a 23647638107 := seed 4269237 rfl
lemma f1960 : H a 0xc8258248625b := seed 4842587318 rfl
lemma f1961 : H a 0xd0258252225b := seed 4633134262 rfl
lemma f1962 : H a 40837997659 := seed 1124532 rfl
lemma f1963 : H a 15074485339 := seed 4270260 rfl
lemma f1964 : H a 0xa819818a145b := seed 1682180279 rfl
lemma f1965 : H a 0xb0132130545b := seed 4372039863 rfl
lemma f1966 : H a 0xb0138132145b := seed 4632086711 rfl
lemma f1967 : H a 23658129499 := seed 1126580 rfl
lemma f1968 : H a 23641348187 := seed 1126581 rfl
lemma f1969 : H a 13443291227 := seed 2371765 rfl
lemma f1970 : H a 19884169307 := seed 1585333 rfl
lemma f1971 : H a 96845628463195 := seed 614731959 rfl
lemma f1972 : H a 0x6824a248685b := seed 1151602870 rfl
lemma f1973 : H a 0x6815814a185b := seed 1680085175 rfl
lemma f1974 : H a 52649157019 := seed 1123124 rfl
lemma f1975 : H a 18817765787 := seed 5251893 rfl
lemma f1976 : H a 0xa0584582519b := seed 1279271735 rfl
lemma f1977 : H a 0x86146126119b := seed 7516390199 rfl
lemma f1978 : H a 0xa2186182519b := seed 1220608823 rfl
lemma f1979 : H a 0xc41a4184519b := seed 3233940279 rfl
lemma f1980 : H a 0xe01a41a0519b := seed 2295333687 rfl
lemma f1981 : H a 55868547739 := seed 206132 rfl
lemma f1982 : H a 39766352539 := seed 2172212 rfl
lemma f1983 : H a 52111368859 := seed 664884 rfl
lemma f1984 : H a 35992392347 := seed 2630965 rfl
lemma f1985 : H a 5934961307 := seed 6300981 rfl
lemma f1986 : H a 0x84514506529b := seed 4899087671 rfl
lemma f1987 : H a 0x94216214629b := seed 4371121462 rfl
lemma f1988 : H a 0x94116114529b := seed 4371121463 rfl
lemma f1989 : H a 0xd0252250629b := seed 4373087542 rfl
lemma f1990 : H a 0xd0254252229b := seed 4498916662 rfl
lemma f1991 : H a 43504653467 := seed 665909 rfl
lemma f1992 : H a 35990295707 := seed 1583413 rfl
lemma f1993 : H a 0xa0584582549b := seed 1279273271 rfl
lemma f1994 : H a 57253543826587 := seed 613550391 rfl
lemma f1995 : H a 0xa4134126149b := seed 4900129079 rfl
lemma f1996 : H a 0xa4194186149b := seed 1682049335 rfl
lemma f1997 : H a 0xb0134132149b := seed 4497869111 rfl
lemma f1998 : H a 0xb0294290649b := seed 1221069110 rfl
lemma f1999 : H a 0xb01a41a0549b := seed 684722487 rfl
lemma f2000 : H a 0xb01a41a2149b := seed 743442743 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f2001 : H a 13996550299 := seed 2175284 rfl
lemma f2002 : H a 13979768987 := seed 2175285 rfl
lemma f2003 : H a 22047647899 := seed 1192244 rfl
lemma f2004 : H a 22030866587 := seed 1192245 rfl
lemma f2005 : H a 18810427547 := seed 1585461 rfl
lemma f2006 : H a 10239371419 := seed 2634036 rfl
lemma f2007 : H a 53129905330331 := seed 739258679 rfl
lemma f2008 : H a 57317984069787 := seed 1149899062 rfl
lemma f2009 : H a 57322280085659 := seed 613552438 rfl
lemma f2010 : H a 57253543827611 := seed 613552439 rfl
lemma f2011 : H a 57325502097563 := seed 211292470 rfl
lemma f2012 : H a 0x70154150589b := seed 1218974007 rfl
lemma f2013 : H a 53721064219 := seed 206388 rfl
lemma f2014 : H a 20426412827 := seed 4269621 rfl
lemma f2015 : H a 0xc0588582531b := seed 2487232055 rfl
lemma f2016 : H a 81520127795995 := seed 413206070 rfl
lemma f2017 : H a 0x8c24c20c631b := seed 6451234358 rfl
lemma f2018 : H a 0xc424c244631b := seed 4574021174 rfl
lemma f2019 : H a 0xc814a148531b := seed 4372825655 rfl
lemma f2020 : H a 0xc814c148531b := seed 4439934519 rfl
lemma f2021 : H a 43504129307 := seed 404021 rfl
lemma f2022 : H a 0xa0584582551b := seed 1279273527 rfl
lemma f2023 : H a 0x8612610e151b := seed 5637343799 rfl
lemma f2024 : H a 0xa2286282651b := seed 1220610614 rfl
lemma f2025 : H a 0xa418c184551b := seed 1354893879 rfl
lemma f2026 : H a 0xa81a41a0551b := seed 416287287 rfl
lemma f2027 : H a 26861000987 := seed 340533 rfl
lemma f2028 : H a 20436904219 := seed 1126964 rfl
lemma f2029 : H a 20420122907 := seed 1126965 rfl
lemma f2030 : H a 19883383067 := seed 1192501 rfl
lemma f2031 : H a 10222065947 := seed 2372149 rfl
lemma f2032 : H a 44402548566299 := seed 470823478 rfl
lemma f2033 : H a 0x60624622691b := seed 2349871670 rfl
lemma f2034 : H a 77044751669531 := seed 3489862199 rfl
lemma f2035 : H a 81520127797531 := seed 413209142 rfl
lemma f2036 : H a 0x6412c124591b := seed 2425492023 rfl
lemma f2037 : H a 0x6814c148591b := seed 1218712119 rfl
lemma f2038 : H a 39762683419 := seed 338996 rfl
lemma f2039 : H a 35988723227 := seed 797749 rfl
lemma f2040 : H a 0x8611610e161b := seed 5100473399 rfl
lemma f2041 : H a 0x94216214661b := seed 4371123254 rfl
lemma f2042 : H a 0x94116114561b := seed 4371123255 rfl
lemma f2043 : H a 0x98294290661b := seed 415763510 rfl
lemma f2044 : H a 23656294939 := seed 209972 rfl
lemma f2045 : H a 22566033947 := seed 341045 rfl
lemma f2046 : H a 20435855899 := seed 603188 rfl
lemma f2047 : H a 7537318427 := seed 2176053 rfl
lemma f2048 : H a 19882334747 := seed 668725 rfl
lemma f2049 : H a 5927098907 := seed 2372661 rfl
lemma f2050 : H a 88323943324187 := seed 941634615 rfl
lemma f2051 : H a 77040456702491 := seed 2952991799 rfl
lemma f2052 : H a 30929705003547 := seed 344593462 rfl
lemma f2053 : H a 92502356159003 := seed 2223641654 rfl
lemma f2054 : H a 92435230513691 := seed 2424968247 rfl
lemma f2055 : H a 96845628463643 := seed 614732855 rfl
lemma f2056 : H a 96846165334555 := seed 681841719 rfl
lemma f2057 : H a 13976099867 := seed 342069 rfl
lemma f2058 : H a 7552003099 := seed 1128500 rfl
lemma f2059 : H a 7535221787 := seed 1128501 rfl
lemma f2060 : H a 7015263259 := seed 1194036 rfl
lemma f2061 : H a 6998481947 := seed 1194037 rfl
lemma f2062 : H a 10235702299 := seed 800820 rfl
lemma f2063 : H a 37798497643547 := seed 1476474934 rfl
lemma f2064 : H a 37800645389339 := seed 1879128118 rfl
lemma f2065 : H a 53129905331227 := seed 739260471 rfl
lemma f2066 : H a 57317984070683 := seed 1149900854 rfl
lemma f2067 : H a 57249247812635 := seed 1149900855 rfl
lemma f2068 : H a 57250858425371 := seed 1351227447 rfl
lemma f2069 : H a 57322280086555 := seed 613554230 rfl
lemma f2070 : H a 57253543828507 := seed 613554231 rfl
lemma f2071 : H a 61648905198619 := seed 1217140791 rfl
lemma f2072 : H a 57325502098459 := seed 211294262 rfl
lemma f2073 : H a 61655349337115 := seed 471341111 rfl
lemma f2074 : H a 55870316779 := seed 1090004 rfl
lemma f2075 : H a 88386233786603 := seed 3255312854 rfl
lemma f2076 : H a 0xd015115050eb := seed 4339532247 rfl
lemma f2077 : H a 0xd017015050eb := seed 5379719639 rfl
lemma f2078 : H a 0xb019119050eb := seed 1120403927 rfl
lemma f2079 : H a 0xe01d01c050eb := seed 1625293271 rfl
lemma f2080 : H a 53706051947 := seed 1090261 rfl
lemma f2081 : H a 27942539627 := seed 4235989 rfl
lemma f2082 : H a 51827462507 := seed 1319637 rfl
lemma f2083 : H a 0xc8149148516b := seed 4339270359 rfl
lemma f2084 : H a 0xc8268248616b := seed 5379457750 rfl
lemma f2085 : H a 0xc8168149116b := seed 5404623575 rfl
lemma f2086 : H a 0xc81a8188516b := seed 3234071255 rfl
lemma f2087 : H a 0xe01c81c0516b := seed 1356858071 rfl
lemma f2088 : H a 55868744299 := seed 304340 rfl
lemma f2089 : H a 53721784939 := seed 566484 rfl
lemma f2090 : H a 23664353899 := seed 4236500 rfl
lemma f2091 : H a 23647572587 := seed 4236501 rfl
lemma f2092 : H a 36797698667 := seed 2630869 rfl
lemma f2093 : H a 0xc0588581526b := seed 2453677271 rfl
lemma f2094 : H a 96845360026219 := seed 581174487 rfl
lemma f2095 : H a 0xc8149148526b := seed 4339270871 rfl
lemma f2096 : H a 0xc8258248626b := seed 4842587350 rfl
lemma f2097 : H a 0xc8158148526b := seed 4842587351 rfl
lemma f2098 : H a 0xc8158149126b := seed 4867753175 rfl
lemma f2099 : H a 0xd0151150526b := seed 4339533015 rfl
lemma f2100 : H a 0xd01c81c1126b := seed 845153495 rfl
lemma f2101 : H a 47262028907 := seed 305365 rfl
lemma f2102 : H a 45131850859 := seed 567508 rfl
lemma f2103 : H a 40837932139 := seed 1091796 rfl
lemma f2104 : H a 0xb0191190546b := seed 1120405719 rfl
lemma f2105 : H a 30098942059 := seed 307412 rfl
lemma f2106 : H a 30082160747 := seed 307413 rfl
lemma f2107 : H a 27951982699 := seed 569556 rfl
lemma f2108 : H a 27935201387 := seed 569557 rfl
lemma f2109 : H a 23658063979 := seed 1093844 rfl
lemma f2110 : H a 23641282667 := seed 1093845 rfl
lemma f2111 : H a 15070226539 := seed 2142420 rfl
lemma f2112 : H a 13191637099 := seed 2371796 rfl
lemma f2113 : H a 13174855787 := seed 2371797 rfl
lemma f2114 : H a 36700865259627 := seed 1879093462 rfl
lemma f2115 : H a 36632129001579 := seed 1879093463 rfl
lemma f2116 : H a 71885237348459 := seed 2952835286 rfl
lemma f2117 : H a 71816501090411 := seed 2952835287 rfl
lemma f2118 : H a 71889532840043 := seed 3758141654 rfl
lemma f2119 : H a 71820796581995 := seed 3758141655 rfl
lemma f2120 : H a 54020254296171 := seed 1351127254 rfl
lemma f2121 : H a 89211068835947 := seed 3230175446 rfl
lemma f2122 : H a 0x68258248686b := seed 1621364950 rfl
lemma f2123 : H a 0x68258249286b := seed 1646530774 rfl
lemma f2124 : H a 60146667947 := seed 172885 rfl
lemma f2125 : H a 52632310187 := seed 1090389 rfl
lemma f2126 : H a 44044472747 := seed 2138965 rfl
lemma f2127 : H a 51827200427 := seed 1188693 rfl
lemma f2128 : H a 18549330347 := seed 5251925 rfl
lemma f2129 : H a 0xa062462161ab := seed 4463797078 rfl
lemma f2130 : H a 0xa058458151ab := seed 1245717335 rfl
lemma f2131 : H a 0xc058458151ab := seed 2319459159 rfl
lemma f2132 : H a 0xa412512451ab := seed 4338090839 rfl
lemma f2133 : H a 0xa426422461ab := seed 6452020054 rfl
lemma f2134 : H a 0xa416412451ab := seed 6452020055 rfl
lemma f2135 : H a 0xc41a418451ab := seed 3233940311 rfl
lemma f2136 : H a 0xe01a41a051ab := seed 2295333719 rfl
lemma f2137 : H a 55868482219 := seed 173396 rfl
lemma f2138 : H a 55851700907 := seed 173397 rfl
lemma f2139 : H a 52648043179 := seed 566612 rfl
lemma f2140 : H a 39766287019 := seed 2139476 rfl
lemma f2141 : H a 51826152107 := seed 664917 rfl
lemma f2142 : H a 35723956907 := seed 2630997 rfl
lemma f2143 : H a 5666525867 := seed 6301013 rfl
lemma f2144 : H a 0x8151150552ab := seed 4966098263 rfl
lemma f2145 : H a 0x8451450552ab := seed 4865533271 rfl
lemma f2146 : H a 88378717594283 := seed 2315789654 rfl
lemma f2147 : H a 88322869383851 := seed 706749783 rfl
lemma f2148 : H a 0x9128528162ab := seed 683705686 rfl
lemma f2149 : H a 0x9411511452ab := seed 4337567063 rfl
lemma f2150 : H a 47261766827 := seed 174421 rfl
lemma f2151 : H a 44058109099 := seed 567636 rfl
lemma f2152 : H a 44041327787 := seed 567637 rfl
lemma f2153 : H a 39747409067 := seed 1091925 rfl
lemma f2154 : H a 38942299307 := seed 1190229 rfl
lemma f2155 : H a 39931468928171 := seed 1644308823 rfl
lemma f2156 : H a 0x9058458154ab := seed 708847959 rfl
lemma f2157 : H a 0xa058458154ab := seed 1245718871 rfl
lemma f2158 : H a 0x9121521164ab := seed 4438133078 rfl
lemma f2159 : H a 57248979375275 := seed 1116342615 rfl
lemma f2160 : H a 0x9421521464ab := seed 4337568086 rfl
lemma f2161 : H a 0x9411511454ab := seed 4337568087 rfl
lemma f2162 : H a 0x9423421464ab := seed 5377755478 rfl
lemma f2163 : H a 0x9413411454ab := seed 5377755479 rfl
lemma f2164 : H a 0x9413411514ab := seed 5402921303 rfl
lemma f2165 : H a 57253275391147 := seed 579995991 rfl
lemma f2166 : H a 0xa412512454ab := seed 4338092375 rfl
lemma f2167 : H a 0xa423422464ab := seed 4841408854 rfl
lemma f2168 : H a 0xa413412454ab := seed 4841408855 rfl
lemma f2169 : H a 0xa429428464ab := seed 1623329110 rfl
lemma f2170 : H a 0xa429428524ab := seed 1648494934 rfl
lemma f2171 : H a 0xb023423064ab := seed 4439148886 rfl
lemma f2172 : H a 0xb013413054ab := seed 4439148887 rfl
lemma f2173 : H a 0xb019419054ab := seed 1221069143 rfl
lemma f2174 : H a 0xb029429124ab := seed 1246234966 rfl
lemma f2175 : H a 0xb01a41a054ab := seed 684722519 rfl
lemma f2176 : H a 0xb01a41a114ab := seed 709888343 rfl
lemma f2177 : H a 30098679979 := seed 176468 rfl
lemma f2178 : H a 26878240939 := seed 569684 rfl
lemma f2179 : H a 26861459627 := seed 569685 rfl
lemma f2180 : H a 22584322219 := seed 1093972 rfl
lemma f2181 : H a 22567540907 := seed 1093973 rfl
lemma f2182 : H a 13996484779 := seed 2142548 rfl
lemma f2183 : H a 13191375019 := seed 2240852 rfl
lemma f2184 : H a 18558773419 := seed 1585492 rfl
lemma f2185 : H a 71816500828331 := seed 2818617687 rfl
lemma f2186 : H a 39931468929195 := seed 1644310871 rfl
lemma f2187 : H a 88322869385387 := seed 706752855 rfl
lemma f2188 : H a 92514975770795 := seed 581046614 rfl
lemma f2189 : H a 0x6424524468ab := seed 1117917526 rfl
lemma f2190 : H a 0x6415414458ab := seed 1621234007 rfl
lemma f2191 : H a 53720998699 := seed 173652 rfl
lemma f2192 : H a 53704217387 := seed 173653 rfl
lemma f2193 : H a 20443128619 := seed 4236884 rfl
lemma f2194 : H a 20426347307 := seed 4236885 rfl
lemma f2195 : H a 19638018859 := seed 4335188 rfl
lemma f2196 : H a 35723432747 := seed 2369109 rfl
lemma f2197 : H a 18547757867 := seed 4466261 rfl
lemma f2198 : H a 3519042347 := seed 6301269 rfl
lemma f2199 : H a 75182429791019 := seed 2449614422 rfl
lemma f2200 : H a 0xc0584581532b := seed 2319459927 rfl
lemma f2201 : H a 0x8520d205632b := seed 4571956822 rfl
lemma f2202 : H a 0x85245205632b := seed 6451005014 rfl
lemma f2203 : H a 0x8c24c20d232b := seed 6476400214 rfl
lemma f2204 : H a 83651220493099 := seed 178521687 rfl
lemma f2205 : H a 0xc8149148532b := seed 4339271255 rfl
lemma f2206 : H a 0xc814c148532b := seed 4439934551 rfl
lemma f2207 : H a 0xc814c149132b := seed 4465100375 rfl
lemma f2208 : H a 0xc81c41c0532b := seed 417334871 rfl
lemma f2209 : H a 45131064619 := seed 174676 rfl
lemma f2210 : H a 11853194539 := seed 4237908 rfl
lemma f2211 : H a 0xa0584581552b := seed 1245719127 rfl
lemma f2212 : H a 0xa4125124552b := seed 4338092631 rfl
lemma f2213 : H a 0xa412c124552b := seed 4572973655 rfl
lemma f2214 : H a 0xa81a41a0552b := seed 416287319 rfl
lemma f2215 : H a 27951196459 := seed 176724 rfl
lemma f2216 : H a 27934415147 := seed 176725 rfl
lemma f2217 : H a 26877716779 := seed 307796 rfl
lemma f2218 : H a 26860935467 := seed 307797 rfl
lemma f2219 : H a 20436838699 := seed 1094228 rfl
lemma f2220 : H a 20420057387 := seed 1094229 rfl
lemma f2221 : H a 11043891499 := seed 2241108 rfl
lemma f2222 : H a 11027110187 := seed 2241109 rfl
lemma f2223 : H a 18558249259 := seed 1323604 rfl
lemma f2224 : H a 18541467947 := seed 1323605 rfl
lemma f2225 : H a 0x64145144592b := seed 1117917783 rfl
lemma f2226 : H a 48526992632107 := seed 177476182 rfl
lemma f2227 : H a 40836097579 := seed 175188 rfl
lemma f2228 : H a 39762617899 := seed 306260 rfl
lemma f2229 : H a 37615658539 := seed 568404 rfl
lemma f2230 : H a 0x90584581562b := seed 708848727 rfl
lemma f2231 : H a 0x91285281662b := seed 683707478 rfl
lemma f2232 : H a 30858552301099 := seed 579210327 rfl
lemma f2233 : H a 0x94115114562b := seed 4337568855 rfl
lemma f2234 : H a 23656229419 := seed 177236 rfl
lemma f2235 : H a 23639448107 := seed 177237 rfl
lemma f2236 : H a 22582749739 := seed 308308 rfl
lemma f2237 : H a 22565968427 := seed 308309 rfl
lemma f2238 : H a 20435790379 := seed 570452 rfl
lemma f2239 : H a 20419009067 := seed 570453 rfl
lemma f2240 : H a 7554034219 := seed 2143316 rfl
lemma f2241 : H a 7537252907 := seed 2143317 rfl
lemma f2242 : H a 18557200939 := seed 799828 rfl
lemma f2243 : H a 18540419627 := seed 799829 rfl
lemma f2244 : H a 5658663467 := seed 2372693 rfl
lemma f2245 : H a 80339796826667 := seed 2818872407 rfl
lemma f2246 : H a 89135890373163 := seed 2550699095 rfl
lemma f2247 : H a 92435230513707 := seed 2424968279 rfl
lemma f2248 : H a 83718882748971 := seed 312611926 rfl
lemma f2249 : H a 30930510572075 := seed 176952406 rfl
lemma f2250 : H a 96901208238635 := seed 2190218326 rfl
lemma f2251 : H a 96914901592619 := seed 681841750 rfl
lemma f2252 : H a 96914901641771 := seed 707007574 rfl
lemma f2253 : H a 15066295339 := seed 178260 rfl
lemma f2254 : H a 15049514027 := seed 178261 rfl
lemma f2255 : H a 13992815659 := seed 309332 rfl
lemma f2256 : H a 13976034347 := seed 309333 rfl
lemma f2257 : H a 11845856299 := seed 571476 rfl
lemma f2258 : H a 11829074987 := seed 571477 rfl
lemma f2259 : H a 7551937579 := seed 1095764 rfl
lemma f2260 : H a 7535156267 := seed 1095765 rfl
lemma f2261 : H a 13187705899 := seed 407636 rfl
lemma f2262 : H a 13170924587 := seed 407637 rfl
lemma f2263 : H a 11040746539 := seed 669780 rfl
lemma f2264 : H a 6746827819 := seed 1194068 rfl
lemma f2265 : H a 9967266859 := seed 800852 rfl
lemma f2266 : H a 9950485547 := seed 800853 rfl
lemma f2267 : H a 5673348139 := seed 1325140 rfl
lemma f2268 : H a 5656566827 := seed 1325141 rfl
lemma f2269 : H a 3509607467 := seed 1587285 rfl
lemma f2270 : H a 36629981256747 := seed 1476442199 rfl
lemma f2271 : H a 36632128740395 := seed 1744877655 rfl
lemma f2272 : H a 36700865260587 := seed 1879095382 rfl
lemma f2273 : H a 36632129002539 := seed 1879095383 rfl
lemma f2274 : H a 44396104477739 := seed 1241790550 rfl
lemma f2275 : H a 27628753480747 := seed 679778390 rfl
lemma f2276 : H a 27560017222699 := seed 679778391 rfl
lemma f2277 : H a 45152203267115 := seed 1216649303 rfl
lemma f2278 : H a 45155424738347 := seed 1745131607 rfl
lemma f2279 : H a 54019180555307 := seed 1216911446 rfl
lemma f2280 : H a 54023476571179 := seed 680564822 rfl
lemma f2281 : H a 53954740313131 := seed 680564823 rfl
lemma f2282 : H a 53955814054955 := seed 814782551 rfl
lemma f2283 : H a 30927288560683 := seed 579213398 rfl
lemma f2284 : H a 30858552302635 := seed 579213399 rfl
lemma f2285 : H a 48519474605099 := seed 1116084310 rfl
lemma f2286 : H a 48523501136939 := seed 1619400790 rfl
lemma f2287 : H a 48454764878891 := seed 1619400791 rfl
lemma f2288 : H a 48454764928043 := seed 1644566615 rfl
lemma f2289 : H a 57248979377195 := seed 1116346455 rfl
lemma f2290 : H a 57250858425387 := seed 1351227479 rfl
lemma f2291 : H a 57319594732587 := seed 1376393302 rfl
lemma f2292 : H a 61717641505835 := seed 1242306646 rfl
lemma f2293 : H a 60146536907 := seed 107413 rfl
lemma f2294 : H a 52112220619 := seed 1090452 rfl
lemma f2295 : H a 52095439307 := seed 1090453 rfl
lemma f2296 : H a 43256013259 := seed 2171796 rfl
lemma f2297 : H a 26080338379 := seed 4268948 rfl
lemma f2298 : H a 18029240779 := seed 5251988 rfl
lemma f2299 : H a 9424622027 := seed 6300565 rfl
lemma f2300 : H a 72920575726027 := seed 3254854551 rfl
lemma f2301 : H a 0xa058258151cb := seed 1178608535 rfl
lemma f2302 : H a 0x8314310351cb := seed 6450938775 rfl
lemma f2303 : H a 0xc21a218251cb := seed 3233874839 rfl
lemma f2304 : H a 0xa21a11a051cb := seed 114295703 rfl
lemma f2305 : H a 55851569867 := seed 107925 rfl
lemma f2306 : H a 35187086027 := seed 2631061 rfl
lemma f2307 : H a 0x8151150352cb := seed 4898989463 rfl
lemma f2308 : H a 0x8154150352cb := seed 6509602199 rfl
lemma f2309 : H a 0x9218318252cb := seed 583075223 rfl
lemma f2310 : H a 0xd025225062cb := seed 4373087638 rfl
lemma f2311 : H a 0xc21c11c052cb := seed 115344791 rfl
lemma f2312 : H a 13447025867 := seed 4237717 rfl
lemma f2313 : H a 13195437259 := seed 4270484 rfl
lemma f2314 : H a 35201770699 := seed 1583508 rfl
lemma f2315 : H a 36632128607435 := seed 1677765015 rfl
lemma f2316 : H a 0x8251250354cb := seed 4865468823 rfl
lemma f2317 : H a 0x8252250354cb := seed 5402339735 rfl
lemma f2318 : H a 0xa058258154cb := seed 1178610071 rfl
lemma f2319 : H a 38556743718091 := seed 1619102103 rfl
lemma f2320 : H a 0x9123121164cb := seed 5377657238 rfl
lemma f2321 : H a 54022939698379 := seed 613452182 rfl
lemma f2322 : H a 0xa123122164cb := seed 4841310614 rfl
lemma f2323 : H a 0x9128328164cb := seed 616597910 rfl
lemma f2324 : H a 0xa118318154cb := seed 1153468823 rfl
lemma f2325 : H a 0x9218318254cb := seed 583076247 rfl
lemma f2326 : H a 0xa219218254cb := seed 1623263639 rfl
lemma f2327 : H a 0xa219218314cb := seed 1648429463 rfl
lemma f2328 : H a 0xb023123064cb := seed 4338485654 rfl
lemma f2329 : H a 0xb023223064cb := seed 4372040086 rfl
lemma f2330 : H a 0xb023223124cb := seed 4397205910 rfl
lemma f2331 : H a 0xb02a22a064cb := seed 617613718 rfl
lemma f2332 : H a 30081767627 := seed 110997 rfl
lemma f2333 : H a 36632128608459 := seed 1677767063 rfl
lemma f2334 : H a 72920575727819 := seed 3254858135 rfl
lemma f2335 : H a 53949907425483 := seed 1149800855 rfl
lemma f2336 : H a 53954203441355 := seed 613454231 rfl
lemma f2337 : H a 55057474148555 := seed 110629271 rfl
lemma f2338 : H a 53704086347 := seed 108181 rfl
lemma f2339 : H a 52093866827 := seed 304789 rfl
lemma f2340 : H a 37065151307 := seed 2139797 rfl
lemma f2341 : H a 19889476427 := seed 4236949 rfl
lemma f2342 : H a 19621106507 := seed 4269717 rfl
lemma f2343 : H a 35203343179 := seed 2369172 rfl
lemma f2344 : H a 35186561867 := seed 2369173 rfl
lemma f2345 : H a 71814353212235 := seed 2483070615 rfl
lemma f2346 : H a 72914133275467 := seed 2449548951 rfl
lemma f2347 : H a 0x8310b103534b := seed 4571891351 rfl
lemma f2348 : H a 0x83143103534b := seed 6450939543 rfl
lemma f2349 : H a 0x89283281634b := seed 348161686 rfl
lemma f2350 : H a 0xc1283281634b := seed 2227209878 rfl
lemma f2351 : H a 0xc2283282634b := seed 2193688214 rfl
lemma f2352 : H a 81452197237579 := seed 111412887 rfl
lemma f2353 : H a 0xc8249248634b := seed 4339271318 rfl
lemma f2354 : H a 0xc824a248634b := seed 4372825750 rfl
lemma f2355 : H a 45114152267 := seed 109205 rfl
lemma f2356 : H a 11299542347 := seed 4237973 rfl
lemma f2357 : H a 35201246539 := seed 1321620 rfl
lemma f2358 : H a 35184465227 := seed 1321621 rfl
lemma f2359 : H a 2996856139 := seed 5253780 rfl
lemma f2360 : H a 36629981123915 := seed 1409329815 rfl
lemma f2361 : H a 0x81509503554b := seed 4630555287 rfl
lemma f2362 : H a 0xa0582581554b := seed 1178610327 rfl
lemma f2363 : H a 0x8310b103554b := seed 4571892375 rfl
lemma f2364 : H a 0xa2183182554b := seed 1119947415 rfl
lemma f2365 : H a 0xa822a228654b := seed 4371778198 rfl
lemma f2366 : H a 0xa21a11a0554b := seed 114297495 rfl
lemma f2367 : H a 11295349067 := seed 2142869 rfl
lemma f2368 : H a 9416759627 := seed 2372245 rfl
lemma f2369 : H a 36629981124939 := seed 1409331863 rfl
lemma f2370 : H a 72920575727947 := seed 3254858391 rfl
lemma f2371 : H a 81504286435659 := seed 2189759126 rfl
lemma f2372 : H a 40819185227 := seed 109717 rfl
lemma f2373 : H a 39225747019 := seed 306324 rfl
lemma f2374 : H a 35183416907 := seed 797845 rfl
lemma f2375 : H a 23639317067 := seed 111765 rfl
lemma f2376 : H a 22045878859 := seed 308372 rfl
lemma f2377 : H a 22029097547 := seed 308373 rfl
lemma f2378 : H a 19898919499 := seed 570516 rfl
lemma f2379 : H a 19882138187 := seed 570517 rfl
lemma f2380 : H a 7017163339 := seed 2143380 rfl
lemma f2381 : H a 7000382027 := seed 2143381 rfl
lemma f2382 : H a 21760727627 := seed 341141 rfl
lemma f2383 : H a 19630549579 := seed 603284 rfl
lemma f2384 : H a 6732012107 := seed 2176149 rfl
lemma f2385 : H a 5138573899 := seed 2372756 rfl
lemma f2386 : H a 5121792587 := seed 2372757 rfl
lemma f2387 : H a 72914133277259 := seed 2449552535 rfl
lemma f2388 : H a 88311055145547 := seed 2483565719 rfl
lemma f2389 : H a 20962410191435 := seed 813798551 rfl
lemma f2390 : H a 27630364617291 := seed 344495254 rfl
lemma f2391 : H a 89203015772747 := seed 2223543446 rfl
lemma f2392 : H a 96901476674123 := seed 2223772822 rfl
lemma f2393 : H a 81452197239371 := seed 111416471 rfl
lemma f2394 : H a 96914096286283 := seed 581178518 rfl
lemma f2395 : H a 96914364721739 := seed 614732950 rfl
lemma f2396 : H a 2989517899 := seed 1587348 rfl
lemma f2397 : H a 36632128609355 := seed 1677768855 rfl
lemma f2398 : H a 26734645304395 := seed 637810839 rfl
lemma f2399 : H a 53130979007563 := seed 839923863 rfl
lemma f2400 : H a 53949907426379 := seed 1149802647 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f2401 : H a 53951518039115 := seed 1351129239 rfl
lemma f2402 : H a 53954203442251 := seed 613456023 rfl
lemma f2403 : H a 53955814054987 := seed 814782615 rfl
lemma f2404 : H a 61716836150347 := seed 1116477590 rfl
lemma f2405 : H a 61717104585803 := seed 1150032022 rfl
lemma f2406 : H a 55057474149451 := seed 110631063 rfl
lemma f2407 : H a 52630344587 := seed 108309 rfl
lemma f2408 : H a 52110386059 := seed 173844 rfl
lemma f2409 : H a 18832515979 := seed 4237076 rfl
lemma f2410 : H a 51842016139 := seed 206612 rfl
lemma f2411 : H a 35203081099 := seed 2238228 rfl
lemma f2412 : H a 0x81505503538b := seed 4496336663 rfl
lemma f2413 : H a 0x81641605638b := seed 6576711446 rfl
lemma f2414 : H a 0x84582581538b := seed 239085335 rfl
lemma f2415 : H a 0xc2186183138b := seed 2319517463 rfl
lemma f2416 : H a 0x86185184538b := seed 113379095 rfl
lemma f2417 : H a 0xc21c11c0538b := seed 115345175 rfl
lemma f2418 : H a 44040410507 := seed 109333 rfl
lemma f2419 : H a 10225800587 := seed 4238101 rfl
lemma f2420 : H a 43235300747 := seed 207637 rfl
lemma f2421 : H a 9974211979 := seed 4270868 rfl
lemma f2422 : H a 9957430667 := seed 4270869 rfl
lemma f2423 : H a 35200984459 := seed 1190676 rfl
lemma f2424 : H a 35184203147 := seed 1190677 rfl
lemma f2425 : H a 9437472139 := seed 4336404 rfl
lemma f2426 : H a 36628907382155 := seed 1275112215 rfl
lemma f2427 : H a 0x83107103558b := seed 4437674775 rfl
lemma f2428 : H a 0x83123103558b := seed 5377198871 rfl
lemma f2429 : H a 0xa1223221658b := seed 4371548950 rfl
lemma f2430 : H a 0x85283281658b := seed 213945110 rfl
lemma f2431 : H a 0xa1283281658b := seed 1153469206 rfl
lemma f2432 : H a 41920793830795 := seed 1115884310 rfl
lemma f2433 : H a 0x86207206658b := seed 4337109782 rfl
lemma f2434 : H a 0x86183182558b := seed 180423447 rfl
lemma f2435 : H a 0xa2186182558b := seed 1220610839 rfl
lemma f2436 : H a 41860112602507 := seed 110234391 rfl
lemma f2437 : H a 0xa4225224658b := seed 4338092822 rfl
lemma f2438 : H a 0xa4226224658b := seed 4371647254 rfl
lemma f2439 : H a 26860542347 := seed 111381 rfl
lemma f2440 : H a 10238388619 := seed 2142996 rfl
lemma f2441 : H a 9970018699 := seed 2175764 rfl
lemma f2442 : H a 36628907383179 := seed 1275114263 rfl
lemma f2443 : H a 72920575728011 := seed 3254858519 rfl
lemma f2444 : H a 40821282138507 := seed 1149408022 rfl
lemma f2445 : H a 41860112603531 := seed 110236439 rfl
lemma f2446 : H a 39208703627 := seed 175381 rfl
lemma f2447 : H a 35988264587 := seed 568597 rfl
lemma f2448 : H a 38940333707 := seed 208149 rfl
lemma f2449 : H a 5679244939 := seed 4271380 rfl
lemma f2450 : H a 35199936139 := seed 666900 rfl
lemma f2451 : H a 35183154827 := seed 666901 rfl
lemma f2452 : H a 0x81505503568b := seed 4496338199 rfl
lemma f2453 : H a 0x81611605668b := seed 4966100246 rfl
lemma f2454 : H a 20136501401227 := seed 704720151 rfl
lemma f2455 : H a 0x84582581568b := seed 239086871 rfl
lemma f2456 : H a 0x90584581568b := seed 708848919 rfl
lemma f2457 : H a 20961336448651 := seed 679578903 rfl
lemma f2458 : H a 0x91213211668b := seed 4371025174 rfl
lemma f2459 : H a 0x85183181568b := seed 213945623 rfl
lemma f2460 : H a 0x91285281668b := seed 683707670 rfl
lemma f2461 : H a 22565575307 := seed 111893 rfl
lemma f2462 : H a 18808396427 := seed 570645 rfl
lemma f2463 : H a 21760465547 := seed 210197 rfl
lemma f2464 : H a 5658270347 := seed 2176277 rfl
lemma f2465 : H a 1901091467 := seed 2635029 rfl
lemma f2466 : H a 20961336449675 := seed 679580951 rfl
lemma f2467 : H a 23229096094347 := seed 612537622 rfl
lemma f2468 : H a 24263630543499 := seed 109712663 rfl
lemma f2469 : H a 92518466218635 := seed 212342038 rfl
lemma f2470 : H a 92518466267787 := seed 237507862 rfl
lemma f2471 : H a 13975641227 := seed 112917 rfl
lemma f2472 : H a 13455682699 := seed 178452 rfl
lemma f2473 : H a 13438901387 := seed 178453 rfl
lemma f2474 : H a 10218462347 := seed 571669 rfl
lemma f2475 : H a 5924543627 := seed 1095957 rfl
lemma f2476 : H a 9950092427 := seed 604437 rfl
lemma f2477 : H a 9430133899 := seed 669972 rfl
lemma f2478 : H a 9413352587 := seed 669973 rfl
lemma f2479 : H a 5136215179 := seed 1194260 rfl
lemma f2480 : H a 5119433867 := seed 1194261 rfl
lemma f2481 : H a 1915776139 := seed 1587476 rfl
lemma f2482 : H a 1898994827 := seed 1587477 rfl
lemma f2483 : H a 36632128609419 := seed 1677768983 rfl
lemma f2484 : H a 20136501402763 := seed 704723223 rfl
lemma f2485 : H a 37731908672651 := seed 1644247319 rfl
lemma f2486 : H a 39931468930187 := seed 1644312855 rfl
lemma f2487 : H a 53194345573515 := seed 1275607318 rfl
lemma f2488 : H a 20961336450187 := seed 679581975 rfl
lemma f2489 : H a 38556743720075 := seed 1619106071 rfl
lemma f2490 : H a 38625480223883 := seed 1744935190 rfl
lemma f2491 : H a 40821282139275 := seed 1149409558 rfl
lemma f2492 : H a 55118155377803 := seed 1116281110 rfl
lemma f2493 : H a 55118960733323 := seed 1242110230 rfl
lemma f2494 : H a 57322011651211 := seed 580000022 rfl
lemma f2495 : H a 57322280086667 := seed 613554454 rfl
lemma f2496 : H a 57325502098571 := seed 211294486 rfl
lemma f2497 : H a 57325502147723 := seed 236460310 rfl
lemma f2498 : H a 36809631499 := seed 208404 rfl
lemma f2499 : H a 35199411979 := seed 405012 rfl
lemma f2500 : H a 2995021579 := seed 4337172 rfl
lemma f2501 : H a 0x81609605670b := seed 4697665046 rfl
lemma f2502 : H a 0xc606605670b := seed 369241622 rfl
lemma f2503 : H a 0x84582581570b := seed 239087127 rfl
lemma f2504 : H a 0x8a186183170b := seed 440471063 rfl
lemma f2505 : H a 0x86185184570b := seed 113380887 rfl
lemma f2506 : H a 20418091787 := seed 112149 rfl
lemma f2507 : H a 19629763339 := seed 210452 rfl
lemma f2508 : H a 3510786827 := seed 2176533 rfl
lemma f2509 : H a 1917348619 := seed 2373140 rfl
lemma f2510 : H a 1900567307 := seed 2373141 rfl
lemma f2511 : H a 0xc6066056b0b := seed 369243670 rfl
lemma f2512 : H a 75182429793035 := seed 2449618454 rfl
lemma f2513 : H a 79526776363787 := seed 438318615 rfl
lemma f2514 : H a 83703846693643 := seed 2189825558 rfl
lemma f2515 : H a 83704115178251 := seed 2248545814 rfl
lemma f2516 : H a 81452197239563 := seed 111416855 rfl
lemma f2517 : H a 83720225188619 := seed 212080150 rfl
lemma f2518 : H a 83720225237771 := seed 237245974 rfl
lemma f2519 : H a 11828157707 := seed 113173 rfl
lemma f2520 : H a 11308199179 := seed 178708 rfl
lemma f2521 : H a 10234719499 := seed 309780 rfl
lemma f2522 : H a 3793841419 := seed 1096212 rfl
lemma f2523 : H a 9966349579 := seed 342548 rfl
lemma f2524 : H a 9949568267 := seed 342549 rfl
lemma f2525 : H a 2971950347 := seed 1194517 rfl
lemma f2526 : H a 0x95055035d0b := seed 469809687 rfl
lemma f2527 : H a 36628907384075 := seed 1275116055 rfl
lemma f2528 : H a 0xc6066056d0b := seed 369244694 rfl
lemma f2529 : H a 40821282139403 := seed 1149409814 rfl
lemma f2530 : H a 40754156494091 := seed 1350736407 rfl
lemma f2531 : H a 0xe2072066d0b := seed 310581782 rfl
lemma f2532 : H a 41920793832715 := seed 1115888150 rfl
lemma f2533 : H a 0xe20b20a6d0b := seed 176495126 rfl
lemma f2534 : H a 46319914347787 := seed 1116019222 rfl
lemma f2535 : H a 41860112604427 := seed 110238231 rfl
lemma f2536 : H a 7533190667 := seed 113685 rfl
lemma f2537 : H a 3776011787 := seed 572437 rfl
lemma f2538 : H a 0xc60a6096e0b := seed 235158550 rfl
lemma f2539 : H a 26803381562891 := seed 637811734 rfl
lemma f2540 : H a 20962410192395 := seed 813800471 rfl
lemma f2541 : H a 23229096095243 := seed 612539414 rfl
lemma f2542 : H a 23161970564619 := seed 872586263 rfl
lemma f2543 : H a 24263630544395 := seed 109714455 rfl
lemma f2544 : H a 55870284019 := seed 1073636 rfl
lemma f2545 : H a 55853502707 := seed 1073637 rfl
lemma f2546 : H a 30106771699 := seed 4219364 rfl
lemma f2547 : H a 0xe017016050f3 := seed 4843373031 rfl
lemma f2548 : H a 60146897267 := seed 287461 rfl
lemma f2549 : H a 53722800499 := seed 1073892 rfl
lemma f2550 : H a 53706019187 := seed 1073893 rfl
lemma f2551 : H a 51693244787 := seed 1319653 rfl
lemma f2552 : H a 43105407347 := seed 2368229 rfl
lemma f2553 : H a 0xc8248a486173 := seed 4322493158 rfl
lemma f2554 : H a 0xc81489485173 := seed 4322493159 rfl
lemma f2555 : H a 0xc82682486173 := seed 5379457766 rfl
lemma f2556 : H a 0xc81a81889173 := seed 3242459879 rfl
lemma f2557 : H a 0xe01c81c09173 := seed 1365246695 rfl
lemma f2558 : H a 55868711539 := seed 287972 rfl
lemma f2559 : H a 53721752179 := seed 550116 rfl
lemma f2560 : H a 19487806067 := seed 4728037 rfl
lemma f2561 : H a 0xc0588580d273 := seed 2436900071 rfl
lemma f2562 : H a 0xc81489485273 := seed 4322493671 rfl
lemma f2563 : H a 0xc82582486273 := seed 4842587366 rfl
lemma f2564 : H a 0xc81581485273 := seed 4842587367 rfl
lemma f2565 : H a 0xd01c81c09273 := seed 828376295 rfl
lemma f2566 : H a 47278777459 := seed 288996 rfl
lemma f2567 : H a 45131818099 := seed 551140 rfl
lemma f2568 : H a 40821118067 := seed 1075429 rfl
lemma f2569 : H a 15074387059 := seed 4221156 rfl
lemma f2570 : H a 36150975194227 := seed 1879075046 rfl
lemma f2571 : H a 0xa81981889473 := seed 1631848679 rfl
lemma f2572 : H a 0xb01381309473 := seed 4581755111 rfl
lemma f2573 : H a 30098909299 := seed 291044 rfl
lemma f2574 : H a 27951949939 := seed 553188 rfl
lemma f2575 : H a 27935168627 := seed 553189 rfl
lemma f2576 : H a 23641249907 := seed 1077477 rfl
lemma f2577 : H a 13040638067 := seed 2371813 rfl
lemma f2578 : H a 6599759987 := seed 3158245 rfl
lemma f2579 : H a 36150975195251 := seed 1879077094 rfl
lemma f2580 : H a 88317497989235 := seed 3490197735 rfl
lemma f2581 : H a 88661178771571 := seed 3230159078 rfl
lemma f2582 : H a 0x609309289873 := seed 2953859303 rfl
lemma f2583 : H a 0x682582486873 := seed 1621364966 rfl
lemma f2584 : H a 0x681581485873 := seed 1621364967 rfl
lemma f2585 : H a 0x68258248a873 := seed 1629753574 rfl
lemma f2586 : H a 0x701381305873 := seed 2425884903 rfl
lemma f2587 : H a 0x702582506873 := seed 1353191654 rfl
lemma f2588 : H a 60146635187 := seed 156517 rfl
lemma f2589 : H a 52649058739 := seed 1074020 rfl
lemma f2590 : H a 52632277427 := seed 1074021 rfl
lemma f2591 : H a 51692982707 := seed 1188709 rfl
lemma f2592 : H a 0xc09a098491b3 := seed 3359654759 rfl
lemma f2593 : H a 0xa4224a2461b3 := seed 4321313638 rfl
lemma f2594 : H a 0xa412492451b3 := seed 4321313639 rfl
lemma f2595 : H a 0xa426422461b3 := seed 6452020070 rfl
lemma f2596 : H a 0xa416412451b3 := seed 6452020071 rfl
lemma f2597 : H a 0xc41a418451b3 := seed 3233940327 rfl
lemma f2598 : H a 0xe01a41a051b3 := seed 2295333735 rfl
lemma f2599 : H a 55868449459 := seed 157028 rfl
lemma f2600 : H a 52648010419 := seed 550244 rfl
lemma f2601 : H a 0xc419418492b3 := seed 2705458535 rfl
lemma f2602 : H a 47278515379 := seed 158052 rfl
lemma f2603 : H a 47261734067 := seed 158053 rfl
lemma f2604 : H a 44058076339 := seed 551268 rfl
lemma f2605 : H a 39764157619 := seed 1075556 rfl
lemma f2606 : H a 14000645299 := seed 4221284 rfl
lemma f2607 : H a 13983863987 := seed 4221285 rfl
lemma f2608 : H a 38808081587 := seed 1190245 rfl
lemma f2609 : H a 36150974932147 := seed 1744857446 rfl
lemma f2610 : H a 0x90530510d4b3 := seed 5386021223 rfl
lemma f2611 : H a 53400554230963 := seed 1216891239 rfl
lemma f2612 : H a 57248845157555 := seed 1099565415 rfl
lemma f2613 : H a 0x9411491454b3 := seed 4320790887 rfl
lemma f2614 : H a 0x9423421464b3 := seed 5377755494 rfl
lemma f2615 : H a 0x9413411454b3 := seed 5377755495 rfl
lemma f2616 : H a 0x9413411494b3 := seed 5386144103 rfl
lemma f2617 : H a 57253141173427 := seed 563218791 rfl
lemma f2618 : H a 0xa412492454b3 := seed 4321315175 rfl
lemma f2619 : H a 0xa423422464b3 := seed 4841408870 rfl
lemma f2620 : H a 0xa413412454b3 := seed 4841408871 rfl
lemma f2621 : H a 0xa429428464b3 := seed 1623329126 rfl
lemma f2622 : H a 0xa419418494b3 := seed 1631717735 rfl
lemma f2623 : H a 0xb023423064b3 := seed 4439148902 rfl
lemma f2624 : H a 0xb013413054b3 := seed 4439148903 rfl
lemma f2625 : H a 0xb013413094b3 := seed 4447537511 rfl
lemma f2626 : H a 0x94290a9064b3 := seed 164104550 rfl
lemma f2627 : H a 0xb029429064b3 := seed 1221069158 rfl
lemma f2628 : H a 0xb019419054b3 := seed 1221069159 rfl
lemma f2629 : H a 0xb0294290a4b3 := seed 1229457766 rfl
lemma f2630 : H a 0xb01a41a094b3 := seed 693111143 rfl
lemma f2631 : H a 30098647219 := seed 160100 rfl
lemma f2632 : H a 13996452019 := seed 2126180 rfl
lemma f2633 : H a 36150974933171 := seed 1744859494 rfl
lemma f2634 : H a 88317497727155 := seed 3355980135 rfl
lemma f2635 : H a 88592442759347 := seed 3355988327 rfl
lemma f2636 : H a 57248845158579 := seed 1099567463 rfl
lemma f2637 : H a 92510409222323 := seed 3230273894 rfl
lemma f2638 : H a 92441672980659 := seed 3238662503 rfl
lemma f2639 : H a 0x6413412458b3 := seed 2693927271 rfl
lemma f2640 : H a 0x70230a3068b3 := seed 2174226790 rfl
lemma f2641 : H a 0x7023423068b3 := seed 2291667302 rfl
lemma f2642 : H a 0x7015415058b3 := seed 1218974055 rfl
lemma f2643 : H a 53704184627 := seed 157285 rfl
lemma f2644 : H a 52647486259 := seed 288356 rfl
lemma f2645 : H a 52630704947 := seed 288357 rfl
lemma f2646 : H a 20443095859 := seed 4220516 rfl
lemma f2647 : H a 51708191539 := seed 403044 rfl
lemma f2648 : H a 19503801139 := seed 4335204 rfl
lemma f2649 : H a 35589215027 := seed 2369125 rfl
lemma f2650 : H a 18413540147 := seed 4466277 rfl
lemma f2651 : H a 3384824627 := seed 6301285 rfl
lemma f2652 : H a 75182429758259 := seed 2432837222 rfl
lemma f2653 : H a 75388638516019 := seed 2424456807 rfl
lemma f2654 : H a 0x84a0ca04e333 := seed 4571940454 rfl
lemma f2655 : H a 0x8490c904d333 := seed 4571940455 rfl
lemma f2656 : H a 0x84a44a04e333 := seed 6450988646 rfl
lemma f2657 : H a 0xc424c2446333 := seed 4574021222 rfl
lemma f2658 : H a 0xc418c1849333 := seed 2437023335 rfl
lemma f2659 : H a 0xc8248a486333 := seed 4322494054 rfl
lemma f2660 : H a 0xc81489485333 := seed 4322494055 rfl
lemma f2661 : H a 0xc814c1485333 := seed 4439934567 rfl
lemma f2662 : H a 0xc824c248a333 := seed 4448323174 rfl
lemma f2663 : H a 0xc81c41c05333 := seed 417334887 rfl
lemma f2664 : H a 0xc81c41c09333 := seed 425723495 rfl
lemma f2665 : H a 45131031859 := seed 158308 rfl
lemma f2666 : H a 44057552179 := seed 289380 rfl
lemma f2667 : H a 44040770867 := seed 289381 rfl
lemma f2668 : H a 43101476147 := seed 404069 rfl
lemma f2669 : H a 36660598067 := seed 1190501 rfl
lemma f2670 : H a 39929321411891 := seed 1359096423 rfl
lemma f2671 : H a 44396104443187 := seed 1225009766 rfl
lemma f2672 : H a 0x8860c608e533 := seed 4446235238 rfl
lemma f2673 : H a 44333812208947 := seed 420489831 rfl
lemma f2674 : H a 0xa05885845533 := seed 1480600167 rfl
lemma f2675 : H a 40204266427699 := seed 1350716007 rfl
lemma f2676 : H a 44602313200947 := seed 1216629351 rfl
lemma f2677 : H a 0xa4224a246533 := seed 4321315430 rfl
lemma f2678 : H a 0xa41249245533 := seed 4321315431 rfl
lemma f2679 : H a 0xa412c1245533 := seed 4572973671 rfl
lemma f2680 : H a 0xa81a41a05533 := seed 416287335 rfl
lemma f2681 : H a 19480729907 := seed 1192549 rfl
lemma f2682 : H a 9819412787 := seed 2372197 rfl
lemma f2683 : H a 75120136444211 := seed 3489804903 rfl
lemma f2684 : H a 44396104444211 := seed 1225011814 rfl
lemma f2685 : H a 44333812209971 := seed 420491879 rfl
lemma f2686 : H a 40204266428723 := seed 1350718055 rfl
lemma f2687 : H a 44602313201971 := seed 1216631399 rfl
lemma f2688 : H a 83643431934259 := seed 3230012007 rfl
lemma f2689 : H a 0x6412c1245933 := seed 2425492071 rfl
lemma f2690 : H a 0x6414c1445933 := seed 1352798823 rfl
lemma f2691 : H a 0x6814c1485933 := seed 1218712167 rfl
lemma f2692 : H a 27010127156787 := seed 679758951 rfl
lemma f2693 : H a 30858418083379 := seed 562433127 rfl
lemma f2694 : H a 0x9418c1849633 := seed 826412135 rfl
lemma f2695 : H a 0x9828c2886633 := seed 683936870 rfl
lemma f2696 : H a 23656196659 := seed 160868 rfl
lemma f2697 : H a 20435757619 := seed 554084 rfl
lemma f2698 : H a 19479681587 := seed 668773 rfl
lemma f2699 : H a 5524445747 := seed 2372709 rfl
lemma f2700 : H a 88311055276595 := seed 2550674535 rfl
lemma f2701 : H a 27010127157811 := seed 679760999 rfl
lemma f2702 : H a 96846165334579 := seed 681841767 rfl
lemma f2703 : H a 96914901609011 := seed 690230374 rfl
lemma f2704 : H a 11845823539 := seed 555108 rfl
lemma f2705 : H a 7551904819 := seed 1079396 rfl
lemma f2706 : H a 13053488179 := seed 407652 rfl
lemma f2707 : H a 6612610099 := seed 1194084 rfl
lemma f2708 : H a 9816267827 := seed 800869 rfl
lemma f2709 : H a 53126683188275 := seed 1476933735 rfl
lemma f2710 : H a 53401628220467 := seed 1476941927 rfl
lemma f2711 : H a 48454764895283 := seed 1627789415 rfl
lemma f2712 : H a 57248845159475 := seed 1099569255 rfl
lemma f2713 : H a 57319594683443 := seed 1351227494 rfl
lemma f2714 : H a 57250858441779 := seed 1359616103 rfl
lemma f2715 : H a 57255154441267 := seed 814880871 rfl
lemma f2716 : H a 61648905198643 := seed 1217140839 rfl
lemma f2717 : H a 61653201230899 := seed 689182823 rfl
lemma f2718 : H a 61723145956403 := seed 295180390 rfl
lemma f2719 : H a 60146504147 := seed 91045 rfl
lemma f2720 : H a 43121795539 := seed 2171812 rfl
lemma f2721 : H a 25929339347 := seed 4268965 rfl
lemma f2722 : H a 35070697939 := seed 3154852 rfl
lemma f2723 : H a 9290404307 := seed 6300581 rfl
lemma f2724 : H a 72920575693267 := seed 3238077351 rfl
lemma f2725 : H a 0xa0582580d1d3 := seed 1161831335 rfl
lemma f2726 : H a 0xc0682680e1d3 := seed 2235573158 rfl
lemma f2727 : H a 0x82922902d1d3 := seed 5377180583 rfl
lemma f2728 : H a 0x82942902d1d3 := seed 6450922407 rfl
lemma f2729 : H a 0xa2222a2261d3 := seed 4321248166 rfl
lemma f2730 : H a 0xe0260a6061d3 := seed 4323279782 rfl
lemma f2731 : H a 0xe026226061d3 := seed 4373611430 rfl
lemma f2732 : H a 51708584659 := seed 599460 rfl
lemma f2733 : H a 0x82512502d2d3 := seed 4848690599 rfl
lemma f2734 : H a 0x90682680e2d3 := seed 624960934 rfl
lemma f2735 : H a 0x82912902d2d3 := seed 4840310183 rfl
lemma f2736 : H a 0x82942902d2d3 := seed 6450922919 rfl
lemma f2737 : H a 35067552979 := seed 1583524 rfl
lemma f2738 : H a 0x82512502d4d3 := seed 4848691623 rfl
lemma f2739 : H a 0x82522502d4d3 := seed 5385562535 rfl
lemma f2740 : H a 0x90612610e4d3 := seed 4379388326 rfl
lemma f2741 : H a 0x82912902d4d3 := seed 4840311207 rfl
lemma f2742 : H a 0x82922902d4d3 := seed 5377182119 rfl
lemma f2743 : H a 30081734867 := seed 94629 rfl
lemma f2744 : H a 72920575695059 := seed 3238080935 rfl
lemma f2745 : H a 38006853654739 := seed 1619087783 rfl
lemma f2746 : H a 55057339930835 := seed 93852071 rfl
lemma f2747 : H a 53704053587 := seed 91813 rfl
lemma f2748 : H a 52110615379 := seed 288420 rfl
lemma f2749 : H a 19906224979 := seed 4220580 rfl
lemma f2750 : H a 19889443667 := seed 4220581 rfl
lemma f2751 : H a 51708060499 := seed 337572 rfl
lemma f2752 : H a 51691279187 := seed 337573 rfl
lemma f2753 : H a 36679344979 := seed 2172580 rfl
lemma f2754 : H a 36662563667 := seed 2172581 rfl
lemma f2755 : H a 19503670099 := seed 4269732 rfl
lemma f2756 : H a 19486888787 := seed 4269733 rfl
lemma f2757 : H a 35069125459 := seed 2369188 rfl
lemma f2758 : H a 0x80d08d02d353 := seed 4630537895 rfl
lemma f2759 : H a 0x80d40d02d353 := seed 6509586087 rfl
lemma f2760 : H a 72914133242707 := seed 2432771751 rfl
lemma f2761 : H a 0x8250a502d353 := seed 4580255399 rfl
lemma f2762 : H a 0x82542502d353 := seed 6459303591 rfl
lemma f2763 : H a 0x8264260a6353 := seed 6710961830 rfl
lemma f2764 : H a 0x8290a902d353 := seed 4571874983 rfl
lemma f2765 : H a 0x82942902d353 := seed 6450923175 rfl
lemma f2766 : H a 0x88948908d353 := seed 6451119783 rfl
lemma f2767 : H a 0x88a82a80e353 := seed 348145318 rfl
lemma f2768 : H a 0xc0a82a80e353 := seed 2227193510 rfl
lemma f2769 : H a 0xc0988980d353 := seed 2428520103 rfl
lemma f2770 : H a 0xc0a88a82a353 := seed 2487240358 rfl
lemma f2771 : H a 0xc09889829353 := seed 2487240359 rfl
lemma f2772 : H a 81504152216403 := seed 2172978854 rfl
lemma f2773 : H a 0x8a20aa0a6353 := seed 4320462502 rfl
lemma f2774 : H a 0x8a282a826353 := seed 297862822 rfl
lemma f2775 : H a 0xc2282a826353 := seed 2176911014 rfl
lemma f2776 : H a 81452063019859 := seed 94635687 rfl
lemma f2777 : H a 0xc8248a486353 := seed 4322494118 rfl
lemma f2778 : H a 0xc824a2486353 := seed 4372825766 rfl
lemma f2779 : H a 0xc824a248a353 := seed 4381214374 rfl
lemma f2780 : H a 43520681299 := seed 289444 rfl
lemma f2781 : H a 43118126419 := seed 338596 rfl
lemma f2782 : H a 35067028819 := seed 1321636 rfl
lemma f2783 : H a 35050247507 := seed 1321637 rfl
lemma f2784 : H a 9286735187 := seed 4467365 rfl
lemma f2785 : H a 36080091059539 := seed 1409313447 rfl
lemma f2786 : H a 0x8850a508d553 := seed 4379126439 rfl
lemma f2787 : H a 0x8290a902d553 := seed 4571876007 rfl
lemma f2788 : H a 0x82922902d553 := seed 5377182375 rfl
lemma f2789 : H a 0x8892890a9553 := seed 5436099239 rfl
lemma f2790 : H a 0xa09289229553 := seed 4631579303 rfl
lemma f2791 : H a 0xa2222a226553 := seed 4321249958 rfl
lemma f2792 : H a 46259098899795 := seed 93588135 rfl
lemma f2793 : H a 27934251347 := seed 94885 rfl
lemma f2794 : H a 19480598867 := seed 1127077 rfl
lemma f2795 : H a 9299323219 := seed 2372260 rfl
lemma f2796 : H a 9282541907 := seed 2372261 rfl
lemma f2797 : H a 71264463149395 := seed 2483057319 rfl
lemma f2798 : H a 72920575695187 := seed 3238081191 rfl
lemma f2799 : H a 73189078260051 := seed 2424394407 rfl
lemma f2800 : H a 81504152217939 := seed 2172981926 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f2801 : H a 46259098900819 := seed 93590183 rfl
lemma f2802 : H a 0x6822a228a953 := seed 2232685222 rfl
lemma f2803 : H a 0x68248a486953 := seed 1101271718 rfl
lemma f2804 : H a 0x82512502d653 := seed 4848692391 rfl
lemma f2805 : H a 0x90682680e653 := seed 624962726 rfl
lemma f2806 : H a 0x8290a902d653 := seed 4571876519 rfl
lemma f2807 : H a 0x82912902d653 := seed 4840311975 rfl
lemma f2808 : H a 23639284307 := seed 95397 rfl
lemma f2809 : H a 19898886739 := seed 554148 rfl
lemma f2810 : H a 19496331859 := seed 603300 rfl
lemma f2811 : H a 19479550547 := seed 603301 rfl
lemma f2812 : H a 5004356179 := seed 2372772 rfl
lemma f2813 : H a 4987574867 := seed 2372773 rfl
lemma f2814 : H a 18487905016403 := seed 872445095 rfl
lemma f2815 : H a 71266610633299 := seed 2751493287 rfl
lemma f2816 : H a 72914133244499 := seed 2432775335 rfl
lemma f2817 : H a 88586000063059 := seed 2424853671 rfl
lemma f2818 : H a 90302393248339 := seed 2173244582 rfl
lemma f2819 : H a 96901476674131 := seed 2223772838 rfl
lemma f2820 : H a 81452063021651 := seed 94639271 rfl
lemma f2821 : H a 96913962068563 := seed 564401318 rfl
lemma f2822 : H a 96914364721747 := seed 614732966 rfl
lemma f2823 : H a 36080091061331 := seed 1409317031 rfl
lemma f2824 : H a 44330589412435 := seed 1627666599 rfl
lemma f2825 : H a 38006853655635 := seed 1619089575 rfl
lemma f2826 : H a 55057339931731 := seed 93853863 rfl
lemma f2827 : H a 52630311827 := seed 91941 rfl
lemma f2828 : H a 35068863379 := seed 2238244 rfl
lemma f2829 : H a 0x82906902d393 := seed 4437657383 rfl
lemma f2830 : H a 0x82942902d393 := seed 6450923303 rfl
lemma f2831 : H a 44040377747 := seed 92965 rfl
lemma f2832 : H a 43503637907 := seed 158501 rfl
lemma f2833 : H a 10242549139 := seed 4221732 rfl
lemma f2834 : H a 10225767827 := seed 4221733 rfl
lemma f2835 : H a 35066766739 := seed 1190692 rfl
lemma f2836 : H a 35049985427 := seed 1190693 rfl
lemma f2837 : H a 0x82506502d593 := seed 4446038823 rfl
lemma f2838 : H a 0x82522502d593 := seed 5385562919 rfl
lemma f2839 : H a 0xa0582580d593 := seed 1161833255 rfl
lemma f2840 : H a 0x82922902d593 := seed 5377182503 rfl
lemma f2841 : H a 0x84a82a80e593 := seed 213928742 rfl
lemma f2842 : H a 0xa0984980d593 := seed 1220561703 rfl
lemma f2843 : H a 0x86282a826593 := seed 163646246 rfl
lemma f2844 : H a 41859978384787 := seed 93457191 rfl
lemma f2845 : H a 0xa42262246593 := seed 4371647270 rfl
lemma f2846 : H a 26860509587 := seed 95013 rfl
lemma f2847 : H a 10238355859 := seed 2126628 rfl
lemma f2848 : H a 17886898579 := seed 1192740 rfl
lemma f2849 : H a 72920575695251 := seed 3238081319 rfl
lemma f2850 : H a 38003632429459 := seed 1216434983 rfl
lemma f2851 : H a 5930800787 := seed 4222245 rfl
lemma f2852 : H a 5545027219 := seed 4271396 rfl
lemma f2853 : H a 5528245907 := seed 4271397 rfl
lemma f2854 : H a 35065718419 := seed 666916 rfl
lemma f2855 : H a 20136501368467 := seed 687942951 rfl
lemma f2856 : H a 0x82512502d693 := seed 4848692519 rfl
lemma f2857 : H a 0x90612610e693 := seed 4379389222 rfl
lemma f2858 : H a 0x82906902d693 := seed 4437658919 rfl
lemma f2859 : H a 0x82a12a06a693 := seed 4966141222 rfl
lemma f2860 : H a 0x90a82a80e693 := seed 616582438 rfl
lemma f2861 : H a 0x86282a826693 := seed 163646758 rfl
lemma f2862 : H a 5540833939 := seed 2176292 rfl
lemma f2863 : H a 20411446385299 := seed 679564583 rfl
lemma f2864 : H a 24263496325779 := seed 92935463 rfl
lemma f2865 : H a 92515244206739 := seed 614602022 rfl
lemma f2866 : H a 13975608467 := seed 96549 rfl
lemma f2867 : H a 13455649939 := seed 162084 rfl
lemma f2868 : H a 10218429587 := seed 555301 rfl
lemma f2869 : H a 9815874707 := seed 604453 rfl
lemma f2870 : H a 9295916179 := seed 669988 rfl
lemma f2871 : H a 9279134867 := seed 669989 rfl
lemma f2872 : H a 5001997459 := seed 1194276 rfl
lemma f2873 : H a 4985216147 := seed 1194277 rfl
lemma f2874 : H a 1764777107 := seed 1587493 rfl
lemma f2875 : H a 36079017319571 := seed 1275099431 rfl
lemma f2876 : H a 37731908639891 := seed 1627470119 rfl
lemma f2877 : H a 39931468897427 := seed 1627535655 rfl
lemma f2878 : H a 53194345573523 := seed 1275607334 rfl
lemma f2879 : H a 20411446385811 := seed 679565607 rfl
lemma f2880 : H a 38006853655699 := seed 1619089703 rfl
lemma f2881 : H a 38075590159507 := seed 1744918822 rfl
lemma f2882 : H a 24331695582355 := seed 159979814 rfl
lemma f2883 : H a 55118021160083 := seed 1099503910 rfl
lemma f2884 : H a 55118960700563 := seed 1225333030 rfl
lemma f2885 : H a 57321877433491 := seed 563222822 rfl
lemma f2886 : H a 57322280086675 := seed 613554470 rfl
lemma f2887 : H a 55057339931795 := seed 93853991 rfl
lemma f2888 : H a 57325502098579 := seed 211294502 rfl
lemma f2889 : H a 57325502114963 := seed 219683110 rfl
lemma f2890 : H a 35065194259 := seed 405028 rfl
lemma f2891 : H a 0x82906902d713 := seed 4437659175 rfl
lemma f2892 : H a 0x8290a902d713 := seed 4571876903 rfl
lemma f2893 : H a 0xe10c90c5713 := seed 92671527 rfl
lemma f2894 : H a 20418059027 := seed 95781 rfl
lemma f2895 : H a 19881319187 := seed 161317 rfl
lemma f2896 : H a 1783130899 := seed 2373156 rfl
lemma f2897 : H a 83719822535443 := seed 161748518 rfl
lemma f2898 : H a 83720225188627 := seed 212080166 rfl
lemma f2899 : H a 11828124947 := seed 96805 rfl
lemma f2900 : H a 10888830227 := seed 211493 rfl
lemma f2901 : H a 2854513939 := seed 1194532 rfl
lemma f2902 : H a 2837732627 := seed 1194533 rfl
lemma f2903 : H a 36079017319699 := seed 1275099687 rfl
lemma f2904 : H a 36080091061523 := seed 1409317415 rfl
lemma f2905 : H a 38004706172179 := seed 1350654503 rfl
lemma f2906 : H a 44602313202963 := seed 1216633383 rfl
lemma f2907 : H a 41853936639251 := seed 1359157799 rfl
lemma f2908 : H a 0xe10c90c5d13 := seed 92674599 rfl
lemma f2909 : H a 41859978386707 := seed 93461031 rfl
lemma f2910 : H a 3792760339 := seed 556068 rfl
lemma f2911 : H a 5537164819 := seed 343076 rfl
lemma f2912 : H a 3373424147 := seed 605221 rfl
lemma f2913 : H a 20412520128019 := seed 813784103 rfl
lemma f2914 : H a 24261750578707 := seed 813898791 rfl
lemma f2915 : H a 24263496326675 := seed 92937255 rfl
lemma f2916 : H a 60146438627 := seed 58309 rfl
lemma f2917 : H a 51709567459 := seed 1090500 rfl
lemma f2918 : H a 51692786147 := seed 1090501 rfl
lemma f2919 : H a 43121730019 := seed 2139076 rfl
lemma f2920 : H a 34785481187 := seed 3154885 rfl
lemma f2921 : H a 17626587619 := seed 5252036 rfl
lemma f2922 : H a 9038750179 := seed 6300612 rfl
lemma f2923 : H a 71820795564515 := seed 3238044615 rfl
lemma f2924 : H a 72095740580323 := seed 3229664199 rfl
lemma f2925 : H a 0x81921901d1e3 := seed 5377147847 rfl
lemma f2926 : H a 0xa0a60a20e1e3 := seed 6451905478 rfl
lemma f2927 : H a 0xc09a0980d1e3 := seed 3233825735 rfl
lemma f2928 : H a 0xc11a118191e3 := seed 3242230727 rfl
lemma f2929 : H a 51708519139 := seed 566724 rfl
lemma f2930 : H a 71816500597475 := seed 2701174215 rfl
lemma f2931 : H a 0x81511501d2e3 := seed 4848657863 rfl
lemma f2932 : H a 0x90611610e2e3 := seed 4345832902 rfl
lemma f2933 : H a 0xc0581580d2e3 := seed 2202019271 rfl
lemma f2934 : H a 0x81911901d2e3 := seed 4840277447 rfl
lemma f2935 : H a 47261537507 := seed 59845 rfl
lemma f2936 : H a 43235988707 := seed 551365 rfl
lemma f2937 : H a 38942069987 := seed 1075653 rfl
lemma f2938 : H a 13178557667 := seed 4221381 rfl
lemma f2939 : H a 34782336227 := seed 1583557 rfl
lemma f2940 : H a 4741686499 := seed 5253572 rfl
lemma f2941 : H a 0x80d10d01d4e3 := seed 4865419719 rfl
lemma f2942 : H a 36632128509155 := seed 1627433415 rfl
lemma f2943 : H a 36907073524963 := seed 1619052999 rfl
lemma f2944 : H a 0x81911901d4e3 := seed 4840278471 rfl
lemma f2945 : H a 0x81921901d4e3 := seed 5377149383 rfl
lemma f2946 : H a 0x90a81a80e4e3 := seed 583027142 rfl
lemma f2947 : H a 0xa0990980d4e3 := seed 1623214535 rfl
lemma f2948 : H a 54022537045219 := seed 563120582 rfl
lemma f2949 : H a 0xb0231230a4e3 := seed 4346874310 rfl
lemma f2950 : H a 0xa11a09a054e3 := seed 63965639 rfl
lemma f2951 : H a 30081669347 := seed 61893 rfl
lemma f2952 : H a 25921935587 := seed 569797 rfl
lemma f2953 : H a 17619249379 := seed 1585604 rfl
lemma f2954 : H a 36082238478563 := seed 1644196295 rfl
lemma f2955 : H a 36632128510179 := seed 1627435463 rfl
lemma f2956 : H a 71820795566307 := seed 3238048199 rfl
lemma f2957 : H a 36907073525987 := seed 1619055047 rfl
lemma f2958 : H a 72091445614819 := seed 2692796871 rfl
lemma f2959 : H a 72095740582115 := seed 3229667783 rfl
lemma f2960 : H a 53957828303075 := seed 60297671 rfl
lemma f2961 : H a 53703988067 := seed 59077 rfl
lemma f2962 : H a 19621008227 := seed 4220613 rfl
lemma f2963 : H a 51707994979 := seed 304836 rfl
lemma f2964 : H a 51691213667 := seed 304837 rfl
lemma f2965 : H a 19486823267 := seed 4236997 rfl
lemma f2966 : H a 34800690019 := seed 2369220 rfl
lemma f2967 : H a 34783908707 := seed 2369221 rfl
lemma f2968 : H a 71814353113955 := seed 2432739015 rfl
lemma f2969 : H a 0x81509501d363 := seed 4580222663 rfl
lemma f2970 : H a 0x816416096363 := seed 6710929094 rfl
lemma f2971 : H a 79510934967139 := seed 2198087367 rfl
lemma f2972 : H a 0x885485095363 := seed 6476277447 rfl
lemma f2973 : H a 0xc05485415363 := seed 4599064263 rfl
lemma f2974 : H a 0x88681680e363 := seed 322971334 rfl
lemma f2975 : H a 0xc0681680e363 := seed 2202019526 rfl
lemma f2976 : H a 0x81909901d363 := seed 4571842247 rfl
lemma f2977 : H a 0x81941901d363 := seed 6450890439 rfl
lemma f2978 : H a 0xc0a81a80e363 := seed 2193639110 rfl
lemma f2979 : H a 0xc0a88a81a363 := seed 2453685958 rfl
lemma f2980 : H a 80352551392099 := seed 61081287 rfl
lemma f2981 : H a 0xc8248a486363 := seed 4322494150 rfl
lemma f2982 : H a 0xc82492486363 := seed 4339271366 rfl
lemma f2983 : H a 0xc8249248a363 := seed 4347659974 rfl
lemma f2984 : H a 0xc82c0ac06363 := seed 299894470 rfl
lemma f2985 : H a 0xc82c12c0a363 := seed 325060294 rfl
lemma f2986 : H a 36677182819 := seed 1092292 rfl
lemma f2987 : H a 36660401507 := seed 1092293 rfl
lemma f2988 : H a 34781812067 := seed 1321669 rfl
lemma f2989 : H a 2594202979 := seed 5253828 rfl
lemma f2990 : H a 0x80d08d01d563 := seed 4596984519 rfl
lemma f2991 : H a 36629981025635 := seed 1358998215 rfl
lemma f2992 : H a 36904926041443 := seed 1350617799 rfl
lemma f2993 : H a 0x81909901d563 := seed 4571843271 rfl
lemma f2994 : H a 0x81921901d563 := seed 5377149639 rfl
lemma f2995 : H a 45226444023139 := seed 294685382 rfl
lemma f2996 : H a 0xa11891819563 := seed 1363184327 rfl
lemma f2997 : H a 0xa82292286563 := seed 4338223814 rfl
lemma f2998 : H a 0xa11a09a05563 := seed 63965895 rfl
lemma f2999 : H a 27934185827 := seed 62149 rfl
lemma f3000 : H a 25921411427 := seed 307909 rfl
lemma f3001 : H a 19497314659 := seed 1094340 rfl
lemma f3002 : H a 10892695907 := seed 2142917 rfl
lemma f3003 : H a 9030887779 := seed 2372292 rfl
lemma f3004 : H a 9014106467 := seed 2372293 rfl
lemma f3005 : H a 2590009699 := seed 3158724 rfl
lemma f3006 : H a 36629981026659 := seed 1359000263 rfl
lemma f3007 : H a 71820795566435 := seed 3238048455 rfl
lemma f3008 : H a 71889532316003 := seed 3489706694 rfl
lemma f3009 : H a 72089298131299 := seed 2424361671 rfl
lemma f3010 : H a 80352551393635 := seed 61084359 rfl
lemma f3011 : H a 0x68248a486963 := seed 1101271750 rfl
lemma f3012 : H a 36676134499 := seed 568516 rfl
lemma f3013 : H a 2593154659 := seed 4730052 rfl
lemma f3014 : H a 19037794981475 := seed 822127815 rfl
lemma f3015 : H a 0x81511501d663 := seed 4848659655 rfl
lemma f3016 : H a 0x90611610e663 := seed 4345834694 rfl
lemma f3017 : H a 0x88581580d663 := seed 322972871 rfl
lemma f3018 : H a 0x81911901d663 := seed 4840279239 rfl
lemma f3019 : H a 27009321850467 := seed 579095751 rfl
lemma f3020 : H a 23639218787 := seed 62661 rfl
lemma f3021 : H a 21777410659 := seed 292036 rfl
lemma f3022 : H a 19630451299 := seed 554180 rfl
lemma f3023 : H a 19613669987 := seed 554181 rfl
lemma f3024 : H a 6748695139 := seed 2127044 rfl
lemma f3025 : H a 19479485027 := seed 570565 rfl
lemma f3026 : H a 6614510179 := seed 2143428 rfl
lemma f3027 : H a 6597728867 := seed 2143429 rfl
lemma f3028 : H a 17600895587 := seed 799941 rfl
lemma f3029 : H a 4735920739 := seed 2372804 rfl
lemma f3030 : H a 4719139427 := seed 2372805 rfl
lemma f3031 : H a 2588961379 := seed 2634948 rfl
lemma f3032 : H a 2572180067 := seed 2634949 rfl
lemma f3033 : H a 71266610567779 := seed 2717938887 rfl
lemma f3034 : H a 26805261101667 := seed 319304902 rfl
lemma f3035 : H a 88377912257123 := seed 2198353094 rfl
lemma f3036 : H a 88392679352931 := seed 824194246 rfl
lemma f3037 : H a 88323943094883 := seed 824194247 rfl
lemma f3038 : H a 88323943127651 := seed 840971463 rfl
lemma f3039 : H a 19312739998307 := seed 813749447 rfl
lemma f3040 : H a 72091445615203 := seed 2692797639 rfl
lemma f3041 : H a 72160182381155 := seed 2952844486 rfl
lemma f3042 : H a 27009321851491 := seed 579097799 rfl
lemma f3043 : H a 88665745320547 := seed 580932806 rfl
lemma f3044 : H a 96901074020963 := seed 2173441222 rfl
lemma f3045 : H a 96913962068579 := seed 564401350 rfl
lemma f3046 : H a 96914096286307 := seed 581178566 rfl
lemma f3047 : H a 15049284707 := seed 63685 rfl
lemma f3048 : H a 11040517219 := seed 555204 rfl
lemma f3049 : H a 6729817187 := seed 1079493 rfl
lemma f3050 : H a 13036510307 := seed 309445 rfl
lemma f3051 : H a 10906332259 := seed 571588 rfl
lemma f3052 : H a 10889550947 := seed 571589 rfl
lemma f3053 : H a 6595632227 := seed 1095877 rfl
lemma f3054 : H a 4733824099 := seed 1325252 rfl
lemma f3055 : H a 2586864739 := seed 1587396 rfl
lemma f3056 : H a 2570083427 := seed 1587397 rfl
lemma f3057 : H a 36082238479459 := seed 1644198087 rfl
lemma f3058 : H a 36150975196259 := seed 1879079110 rfl
lemma f3059 : H a 36632128511075 := seed 1627437255 rfl
lemma f3060 : H a 53130979007587 := seed 839923911 rfl
lemma f3061 : H a 19312739998819 := seed 813750471 rfl
lemma f3062 : H a 36975810292835 := seed 1879103686 rfl
lemma f3063 : H a 53468485184611 := seed 1116231878 rfl
lemma f3064 : H a 53951518039139 := seed 1351129287 rfl
lemma f3065 : H a 53955814055011 := seed 814782663 rfl
lemma f3066 : H a 61716701932643 := seed 1099700422 rfl
lemma f3067 : H a 61716836150371 := seed 1116477638 rfl
lemma f3068 : H a 53957828303971 := seed 60299463 rfl
lemma f3069 : H a 52630246307 := seed 59205 rfl
lemma f3070 : H a 51841917859 := seed 157508 rfl
lemma f3071 : H a 51707732899 := seed 173892 rfl
lemma f3072 : H a 17624753059 := seed 4335428 rfl
lemma f3073 : H a 1522557859 := seed 6301508 rfl
lemma f3074 : H a 1505776547 := seed 6301509 rfl
lemma f3075 : H a 0x81905901d3a3 := seed 4437624647 rfl
lemma f3076 : H a 0x8518498453a3 := seed 63047495 rfl
lemma f3077 : H a 0xc42c12c063a3 := seed 182454086 rfl
lemma f3078 : H a 44040312227 := seed 60229 rfl
lemma f3079 : H a 9957332387 := seed 4221765 rfl
lemma f3080 : H a 9839928739 := seed 4238148 rfl
lemma f3081 : H a 9823147427 := seed 4238149 rfl
lemma f3082 : H a 34798331299 := seed 1190724 rfl
lemma f3083 : H a 34781549987 := seed 1190725 rfl
lemma f3084 : H a 9034818979 := seed 4336452 rfl
lemma f3085 : H a 9018037667 := seed 4336453 rfl
lemma f3086 : H a 1520461219 := seed 5253956 rfl
lemma f3087 : H a 36079017252259 := seed 1241541447 rfl
lemma f3088 : H a 0x80d04d01d5a3 := seed 4462766919 rfl
lemma f3089 : H a 36628907283875 := seed 1224780615 rfl
lemma f3090 : H a 0x81505501d5a3 := seed 4446006087 rfl
lemma f3091 : H a 0x81521501d5a3 := seed 5385530183 rfl
lemma f3092 : H a 39996178621859 := seed 1124215622 rfl
lemma f3093 : H a 0xa058458155a3 := seed 1245719367 rfl
lemma f3094 : H a 0x81905901d5a3 := seed 4437625671 rfl
lemma f3095 : H a 0x81921901d5a3 := seed 5377149767 rfl
lemma f3096 : H a 0xa0a81a80e5a3 := seed 1119898438 rfl
lemma f3097 : H a 0xa0984980d5a3 := seed 1220561735 rfl
lemma f3098 : H a 0xa112512155a3 := seed 4438657863 rfl
lemma f3099 : H a 0x85281a8165a3 := seed 163613510 rfl
lemma f3100 : H a 0xa1281a8165a3 := seed 1103137606 rfl
lemma f3101 : H a 0xa118518155a3 := seed 1220578119 rfl
lemma f3102 : H a 40760466757027 := seed 59902791 rfl
lemma f3103 : H a 0xa4224a2465a3 := seed 4321315654 rfl
lemma f3104 : H a 0xa4225224a5a3 := seed 4346481478 rfl
lemma f3105 : H a 0x8518498455a3 := seed 63048519 rfl
lemma f3106 : H a 0xa428528465a3 := seed 1120013126 rfl
lemma f3107 : H a 26860444067 := seed 62277 rfl
lemma f3108 : H a 71820795566499 := seed 3238048583 rfl
lemma f3109 : H a 72095740582307 := seed 3229668167 rfl
lemma f3110 : H a 40759661255075 := seed 160469831 rfl
lemma f3111 : H a 40760466758051 := seed 59904839 rfl
lemma f3112 : H a 39745345187 := seed 60741 rfl
lemma f3113 : H a 38957016739 := seed 159044 rfl
lemma f3114 : H a 5679146659 := seed 4222276 rfl
lemma f3115 : H a 5662365347 := seed 4222277 rfl
lemma f3116 : H a 38822831779 := seed 175428 rfl
lemma f3117 : H a 38806050467 := seed 175429 rfl
lemma f3118 : H a 5544961699 := seed 4238660 rfl
lemma f3119 : H a 5528180387 := seed 4238661 rfl
lemma f3120 : H a 34797282979 := seed 666948 rfl
lemma f3121 : H a 34780501667 := seed 666949 rfl
lemma f3122 : H a 1519412899 := seed 4730180 rfl
lemma f3123 : H a 18486831208099 := seed 704671047 rfl
lemma f3124 : H a 0x81505501d6a3 := seed 4446006599 rfl
lemma f3125 : H a 0x8161160566a3 := seed 4966100294 rfl
lemma f3126 : H a 0x90584580d6a3 := seed 692071751 rfl
lemma f3127 : H a 0x9058458156a3 := seed 708848967 rfl
lemma f3128 : H a 19311666255523 := seed 679529799 rfl
lemma f3129 : H a 0x81905901d6a3 := seed 4437626183 rfl
lemma f3130 : H a 0x81911901d6a3 := seed 4840279367 rfl
lemma f3131 : H a 22610201335459 := seed 578964807 rfl
lemma f3132 : H a 0x84914904d6a3 := seed 4840377671 rfl
lemma f3133 : H a 0x8491490596a3 := seed 4865543495 rfl
lemma f3134 : H a 0x90a81a80e6a3 := seed 583028038 rfl
lemma f3135 : H a 0x9098498196a3 := seed 708857159 rfl
lemma f3136 : H a 23163984696995 := seed 59379015 rfl
lemma f3137 : H a 0x94214a1466a3 := seed 4320791878 rfl
lemma f3138 : H a 0x9421521466a3 := seed 4337569094 rfl
lemma f3139 : H a 0x94215214a6a3 := seed 4345957702 rfl
lemma f3140 : H a 22565477027 := seed 62789 rfl
lemma f3141 : H a 5540768419 := seed 2143556 rfl
lemma f3142 : H a 4735658659 := seed 2241860 rfl
lemma f3143 : H a 19036721240739 := seed 687912263 rfl
lemma f3144 : H a 71816500599459 := seed 2701178183 rfl
lemma f3145 : H a 72091445615267 := seed 2692797767 rfl
lemma f3146 : H a 23159957183139 := seed 562206023 rfl
lemma f3147 : H a 23163984698019 := seed 59381063 rfl
lemma f3148 : H a 13975542947 := seed 63813 rfl
lemma f3149 : H a 13187214499 := seed 162116 rfl
lemma f3150 : H a 13170433187 := seed 162117 rfl
lemma f3151 : H a 9949994147 := seed 555333 rfl
lemma f3152 : H a 5672856739 := seed 1079620 rfl
lemma f3153 : H a 13036248227 := seed 178501 rfl
lemma f3154 : H a 9832590499 := seed 571716 rfl
lemma f3155 : H a 9815809187 := seed 571717 rfl
lemma f3156 : H a 5538671779 := seed 1096004 rfl
lemma f3157 : H a 5521890467 := seed 1096005 rfl
lemma f3158 : H a 9027480739 := seed 670020 rfl
lemma f3159 : H a 9010699427 := seed 670021 rfl
lemma f3160 : H a 4733562019 := seed 1194308 rfl
lemma f3161 : H a 4716780707 := seed 1194309 rfl
lemma f3162 : H a 1513122979 := seed 1587524 rfl
lemma f3163 : H a 1496341667 := seed 1587525 rfl
lemma f3164 : H a 18486831209635 := seed 704674119 rfl
lemma f3165 : H a 36079017254051 := seed 1241545031 rfl
lemma f3166 : H a 36150974934179 := seed 1744861510 rfl
lemma f3167 : H a 19036721241251 := seed 687913287 rfl
lemma f3168 : H a 36632128511139 := seed 1627437383 rfl
lemma f3169 : H a 36700864998563 := seed 1744877894 rfl
lemma f3170 : H a 39931468897443 := seed 1627535687 rfl
lemma f3171 : H a 39931468930211 := seed 1644312903 rfl
lemma f3172 : H a 53129905233059 := seed 688929095 rfl
lemma f3173 : H a 53129905265827 := seed 705706311 rfl
lemma f3174 : H a 19311666257059 := seed 679532871 rfl
lemma f3175 : H a 36903852301475 := seed 1216403783 rfl
lemma f3176 : H a 36907073526947 := seed 1619056967 rfl
lemma f3177 : H a 36975810030755 := seed 1744886086 rfl
lemma f3178 : H a 40756303977635 := seed 1619171655 rfl
lemma f3179 : H a 23231915453603 := seed 159947078 rfl
lemma f3180 : H a 54018241031331 := seed 1099471174 rfl
lemma f3181 : H a 40760466758819 := seed 59906375 rfl
lemma f3182 : H a 57321877433507 := seed 563222854 rfl
lemma f3183 : H a 57322011651235 := seed 580000070 rfl
lemma f3184 : H a 53957828304035 := seed 60299591 rfl
lemma f3185 : H a 37597861667 := seed 60997 rfl
lemma f3186 : H a 36809533219 := seed 159300 rfl
lemma f3187 : H a 36675348259 := seed 175684 rfl
lemma f3188 : H a 3380696867 := seed 4238917 rfl
lemma f3189 : H a 2592368419 := seed 4337220 rfl
lemma f3190 : H a 1518888739 := seed 4468292 rfl
lemma f3191 : H a 1502107427 := seed 4468293 rfl
lemma f3192 : H a 0x9905901d723 := seed 411094599 rfl
lemma f3193 : H a 0x81905901d723 := seed 4437626439 rfl
lemma f3194 : H a 0x81909901d723 := seed 4571844167 rfl
lemma f3195 : H a 0xca09a08e723 := seed 176442950 rfl
lemma f3196 : H a 0xc909908d723 := seed 176442951 rfl
lemma f3197 : H a 0x891851815723 := seed 415272519 rfl
lemma f3198 : H a 0x8c20d20c6723 := seed 4337307206 rfl
lemma f3199 : H a 0x8c20d20ca723 := seed 4345695814 rfl
lemma f3200 : H a 0x851849845723 := seed 63049287 rfl
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
lemma f3201 : H a 0x8c2892886723 := seed 180620870 rfl
lemma f3202 : H a 0x8c289288a723 := seed 189009478 rfl
lemma f3203 : H a 20417993507 := seed 63045 rfl
lemma f3204 : H a 19612883747 := seed 161349 rfl
lemma f3205 : H a 18556185379 := seed 292420 rfl
lemma f3206 : H a 3527469859 := seed 2127428 rfl
lemma f3207 : H a 3510688547 := seed 2127429 rfl
lemma f3208 : H a 19495480099 := seed 177732 rfl
lemma f3209 : H a 19478698787 := seed 177733 rfl
lemma f3210 : H a 3393284899 := seed 2143812 rfl
lemma f3211 : H a 3376503587 := seed 2143813 rfl
lemma f3212 : H a 17616890659 := seed 407108 rfl
lemma f3213 : H a 17600109347 := seed 407109 rfl
lemma f3214 : H a 2588175139 := seed 2242116 rfl
lemma f3215 : H a 1514695459 := seed 2373188 rfl
lemma f3216 : H a 1497914147 := seed 2373189 rfl
lemma f3217 : H a 71263389342499 := seed 2315286087 rfl
lemma f3218 : H a 71264463084323 := seed 2449503815 rfl
lemma f3219 : H a 71814353115939 := seed 2432742983 rfl
lemma f3220 : H a 79595512589091 := seed 421541446 rfl
lemma f3221 : H a 0x9905901db23 := seed 411096647 rfl
lemma f3222 : H a 72088224389923 := seed 2290144839 rfl
lemma f3223 : H a 72089298131747 := seed 2424362567 rfl
lemma f3224 : H a 72158034635555 := seed 2550191686 rfl
lemma f3225 : H a 75386759469859 := seed 2189579847 rfl
lemma f3226 : H a 0xc909908db23 := seed 176444999 rfl
lemma f3227 : H a 75471605787427 := seed 178280006 rfl
lemma f3228 : H a 79869652298531 := seed 312497734 rfl
lemma f3229 : H a 76005251574563 := seed 2172819014 rfl
lemma f3230 : H a 75938528598819 := seed 2432865863 rfl
lemma f3231 : H a 0xd10c90c5b23 := seed 59119175 rfl
lemma f3232 : H a 83703712475939 := seed 2173048390 rfl
lemma f3233 : H a 83703846693667 := seed 2189825606 rfl
lemma f3234 : H a 83703846710051 := seed 2198214214 rfl
lemma f3235 : H a 80352551394083 := seed 61085255 rfl
lemma f3236 : H a 83719822535459 := seed 161748550 rfl
lemma f3237 : H a 83719956753187 := seed 178525766 rfl
lemma f3238 : H a 11828059427 := seed 64069 rfl
lemma f3239 : H a 9966251299 := seed 293444 rfl
lemma f3240 : H a 3508591907 := seed 1079877 rfl
lemma f3241 : H a 10905546019 := seed 178756 rfl
lemma f3242 : H a 9026956579 := seed 408132 rfl
lemma f3243 : H a 9010175267 := seed 408133 rfl
lemma f3244 : H a 2586078499 := seed 1194564 rfl
lemma f3245 : H a 1512598819 := seed 1325636 rfl
lemma f3246 : H a 1495817507 := seed 1325637 rfl
lemma f3247 : H a 36079017254179 := seed 1241545287 rfl
lemma f3248 : H a 36628907285795 := seed 1224784455 rfl
lemma f3249 : H a 36629981027619 := seed 1359002183 rfl
lemma f3250 : H a 36904926043427 := seed 1350621767 rfl
lemma f3251 : H a 0xc905904dd23 := seed 310532679 rfl
lemma f3252 : H a 45220000001315 := seed 1099209286 rfl
lemma f3253 : H a 40759661255971 := seed 160471623 rfl
lemma f3254 : H a 40760466758947 := seed 59906631 rfl
lemma f3255 : H a 7533092387 := seed 64581 rfl
lemma f3256 : H a 6744763939 := seed 162884 rfl
lemma f3257 : H a 6727982627 := seed 162885 rfl
lemma f3258 : H a 5671284259 := seed 293956 rfl
lemma f3259 : H a 3524324899 := seed 556100 rfl
lemma f3260 : H a 3507543587 := seed 556101 rfl
lemma f3261 : H a 6593797667 := seed 179269 rfl
lemma f3262 : H a 5537099299 := seed 310340 rfl
lemma f3263 : H a 3373358627 := seed 572485 rfl
lemma f3264 : H a 4731989539 := seed 408644 rfl
lemma f3265 : H a 2585030179 := seed 670788 rfl
lemma f3266 : H a 1511550499 := seed 801860 rfl
lemma f3267 : H a 1494769187 := seed 801861 rfl
lemma f3268 : H a 9690738187811 := seed 436239431 rfl
lemma f3269 : H a 18486831210019 := seed 704674887 rfl
lemma f3270 : H a 18556641406499 := seed 939555910 rfl
lemma f3271 : H a 19037794983459 := seed 822131783 rfl
lemma f3272 : H a 0xc605604ee23 := seed 318913606 rfl
lemma f3273 : H a 22335256321571 := seed 587349063 rfl
lemma f3274 : H a 22405871627811 := seed 822230086 rfl
lemma f3275 : H a 22405871660579 := seed 839007302 rfl
lemma f3276 : H a 19311666257443 := seed 679533639 rfl
lemma f3277 : H a 19312739999267 := seed 813751367 rfl
lemma f3278 : H a 22678937595427 := seed 578968646 rfl
lemma f3279 : H a 22612080385571 := seed 813849671 rfl
lemma f3280 : H a 23159957184035 := seed 562207815 rfl
lemma f3281 : H a 27627813957155 := seed 562338886 rfl
lemma f3282 : H a 27560017223203 := seed 679779399 rfl
lemma f3283 : H a 23163179195939 := seed 159947847 rfl
lemma f3284 : H a 27630901489187 := seed 411606086 rfl
lemma f3285 : H a 27562165247523 := seed 419994695 rfl
lemma f3286 : H a 30927154343459 := seed 562437190 rfl
lemma f3287 : H a 30927288561187 := seed 579214406 rfl
lemma f3288 : H a 23163984698915 := seed 59382855 rfl
lemma f3289 : H a 27563105213987 := seed 59513927 rfl
lemma f3290 : H a 30930510573091 := seed 176954438 rfl
lemma f3291 : H a 30930510589475 := seed 185343046 rfl
lemma f3292 : H a 71262852469699 := seed 2248173447 rfl
lemma f3293 : H a 71812742501315 := seed 2231412615 rfl
lemma f3294 : H a 72912254194627 := seed 2197890951 rfl
lemma f3295 : H a 72997637514179 := seed 119547782 rfl
lemma f3296 : H a 36078480381379 := seed 1174432647 rfl
lemma f3297 : H a 36628370412995 := seed 1157671815 rfl
lemma f3298 : H a 37727882106307 := seed 1124150151 rfl
lemma f3299 : H a 37804673394115 := seed 118500230 rfl
lemma f3300 : H a 36078480382403 := seed 1174434695 rfl
lemma f3301 : H a 36628370414019 := seed 1157673863 rfl
lemma f3302 : H a 37727882107331 := seed 1124152199 rfl
lemma f3303 : H a 37804673395139 := seed 118502278 rfl
lemma f3304 : H a 18486294337219 := seed 637562247 rfl
lemma f3305 : H a 19036184368835 := seed 620801415 rfl
lemma f3306 : H a 20135696062147 := seed 587279751 rfl
lemma f3307 : H a 20208191334083 := seed 117976454 rfl
lemma f3308 : H a 18486294338243 := seed 637564295 rfl
lemma f3309 : H a 19036184369859 := seed 620803463 rfl
lemma f3310 : H a 20135696063171 := seed 587281799 rfl
lemma f3311 : H a 20208191335107 := seed 117978502 rfl
lemma f3312 : H a 18486294338755 := seed 637565319 rfl
lemma f3313 : H a 19036184370371 := seed 620804487 rfl
lemma f3314 : H a 20135696063683 := seed 587282823 rfl
lemma f3315 : H a 20208191335619 := seed 117979526 rfl
lemma f3316 : H a 9690201315139 := seed 369127047 rfl
lemma f3317 : H a 0x9503501d743 := seed 352366215 rfl
lemma f3318 : H a 0xa503502d743 := seed 318844551 rfl
lemma f3319 : H a 0xa609608e743 := seed 117714566 rfl
lemma f3320 : H a 9690201316163 := seed 369129095 rfl
lemma f3321 : H a 0x9503501db43 := seed 352368263 rfl
lemma f3322 : H a 0xa503502db43 := seed 318846599 rfl
lemma f3323 : H a 0xa609608eb43 := seed 117716614 rfl
lemma f3324 : H a 9690201316675 := seed 369130119 rfl
lemma f3325 : H a 0x9503501dd43 := seed 352369287 rfl
lemma f3326 : H a 0xa503502dd43 := seed 318847623 rfl
lemma f3327 : H a 0xa609608ed43 := seed 117717638 rfl
lemma f3328 : H a 9690201316931 := seed 369130631 rfl
lemma f3329 : H a 0x9503501de43 := seed 352369799 rfl
lemma f3330 : H a 0xa503502de43 := seed 318848135 rfl
lemma f3331 : H a 0xa609608ee43 := seed 117718150 rfl
lemma f3332 : H a 5292154804099 := seed 234909447 rfl
lemma f3333 : H a 5842044835715 := seed 218148615 rfl
lemma f3334 : H a 6941556529027 := seed 184626951 rfl
lemma f3335 : H a 7010829789059 := seed 117583622 rfl
lemma f3336 : H a 5292154805123 := seed 234911495 rfl
lemma f3337 : H a 5842044836739 := seed 218150663 rfl
lemma f3338 : H a 6941556530051 := seed 184628999 rfl
lemma f3339 : H a 7010829790083 := seed 117585670 rfl
lemma f3340 : H a 5292154805635 := seed 234912519 rfl
lemma f3341 : H a 5842044837251 := seed 218151687 rfl
lemma f3342 : H a 6941556530563 := seed 184630023 rfl
lemma f3343 : H a 7010829790595 := seed 117586694 rfl
lemma f3344 : H a 5292154805891 := seed 234913031 rfl
lemma f3345 : H a 5842044837507 := seed 218152199 rfl
lemma f3346 : H a 6941556530819 := seed 184630535 rfl
lemma f3347 : H a 7010829790851 := seed 117587206 rfl
lemma f3348 : H a 5292154806019 := seed 234913287 rfl
lemma f3349 : H a 5842044837635 := seed 218152455 rfl
lemma f3350 : H a 6941556530947 := seed 184630791 rfl
lemma f3351 : H a 7010829790979 := seed 117587462 rfl
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3352 : H a 30 := rup [pack f1,pack f2] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3353 : H a 46 := rup [pack f1,pack f4] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3354 : H a 54 := rup [pack f1,pack f41] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3355 : H a 58 := rup [pack f1,pack f227] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3356 : H a 3843 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3348,pack f3349,pack f3350,pack f3351] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3357 : H a 3715 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3344,pack f3345,pack f3346,pack f3347] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3358 : H a 3459 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3340,pack f3341,pack f3342,pack f3343] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3359 : H a 2947 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3336,pack f3337,pack f3338,pack f3339] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3360 : H a 1923 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3332,pack f3333,pack f3334,pack f3335] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3361 : H a 3651 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3328,pack f3329,pack f3330,pack f3331] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3362 : H a 3395 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3324,pack f3325,pack f3326,pack f3327] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3363 : H a 2883 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3320,pack f3321,pack f3322,pack f3323] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3364 : H a 1859 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3316,pack f3317,pack f3318,pack f3319] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3365 : H a 3267 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3312,pack f3313,pack f3314,pack f3315] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3366 : H a 2755 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3308,pack f3309,pack f3310,pack f3311] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3367 : H a 1731 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3304,pack f3305,pack f3306,pack f3307] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3368 : H a 2499 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3300,pack f3301,pack f3302,pack f3303] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3369 : H a 1475 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3296,pack f3297,pack f3298,pack f3299] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3370 : H a 963 := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3292,pack f3293,pack f3294,pack f3295] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3371 : H a 0x17415c1d4151158954554 := rup [pack f1,pack f479,pack f482] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3372 : H a 0x1d415115c1582852891742a1 := rup [pack f1,pack f2792,pack f2801,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3373 : H a 1306672419 := rup [pack f1,pack f3353,pack f3352,pack f3356,pack f3358,pack f3362,pack f3255,pack f3257,pack f3291,pack f3261,pack f48,pack f3290,pack f3267,pack f233,pack f3269,pack f3259,pack f20,pack f3268,pack f3258,pack f12,pack f777,pack f2719,pack f769,pack f3247,pack f3239,pack f3245,pack f3241,pack f894,pack f999,pack f2549,pack f1012,pack f1028,pack f5,pack f96,pack f2900,pack f3372,pack f2520,pack f1835,pack f770] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3374 : H a 0xe23192d24c34c64ca4382 := rup [pack f1,pack f3352,pack f3255,pack f1558,pack f2292,pack f647] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3375 : H a 0xc92cc1cc0dc0d08cc0ec := rup [pack f1,pack f333,pack f339] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3376 : H a 0xe011c21890d08901510560dcc8c341072d018acc27 := rup [pack f1,pack f3354,pack f2305,pack f782,pack f2293,pack f126,pack f221,pack f1547,pack f1553,pack f2002,pack f2464,pack f2079,pack f2444,pack f389,pack f3375] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3377 : H a 0xc52c81c80d80d08c80e8 := rup [pack f1,pack f136,pack f143] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3378 : H a 0xe2319210e0d0890151d2420e474874c64c82 := rup [pack f1,pack f3352,pack f3355,pack f3255,pack f2705,pack f3291,pack f3261,pack f47,pack f3290,pack f3267,pack f232,pack f777,pack f1140,pack f1851,pack f1560,pack f744,pack f746,pack f750,pack f787,pack f2559,pack f2549,pack f3374,pack f438,pack f798,pack f856,pack f436,pack f888,pack f1486,pack f2177,pack f1572,pack f3376,pack f647,pack f318,pack f431,pack f2256,pack f2266,pack f2268,pack f2274,pack f1326,pack f1778,pack f1400,pack f1746,pack f189,pack f3377] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3379 : H a 0x4de2320e0c6ca4 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f777,pack f3257,pack f3269,pack f3268,pack f13,pack f17,pack f3258,pack f3373,pack f2570,pack f2579,pack f3058,pack f3378,pack f894,pack f781,pack f3264,pack f1544,pack f3255,pack f3291,pack f3261,pack f3275,pack f2558,pack f2544,pack f3290,pack f1851,pack f1140,pack f440,pack f436,pack f2705,pack f3267,pack f647,pack f2264,pack f2266,pack f2877,pack f2491,pack f1805,pack f743] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3380 : H a 5352118608070 := rup [pack f1,pack f3352,pack f3269,pack f3268,pack f2579,pack f2570,pack f777,pack f3257,pack f13,pack f17,pack f3258,pack f3373,pack f3058,pack f3378,pack f894,pack f2558,pack f3255,pack f3291,pack f1140,pack f3290,pack f1851,pack f2544,pack f440,pack f2643,pack f3261,pack f3267,pack f2588,pack f3264,pack f3286,pack f1887,pack f3275,pack f3283,pack f1164,pack f1866,pack f3379,pack f3154,pack f3162,pack f2675,pack f2686,pack f1916,pack f1939,pack f452,pack f228] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3381 : H a 0xc605a1c21190c90d114504d18509a10e116ca45a40952c113c43b := rup [pack f1,pack f3352,pack f1508,pack f1544,pack f19,pack f241,pack f233,pack f1908,pack f1910,pack f1913,pack f1915,pack f1916,pack f1917,pack f2935,pack f2603,pack f1010,pack f1189,pack f2101,pack f2567,pack f2151,pack f3013,pack f3122,pack f3055,pack f1523,pack f581,pack f121,pack f118,pack f560,pack f579,pack f558,pack f2016,pack f2035,pack f254,pack f245] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3382 : H a 0xd00780c605aa21e011c20c914520d18515159410e1165a42c127417483b := rup [pack f1,pack f3354,pack f3358,pack f3360,pack f3369,pack f1081,pack f1991,pack f2293,pack f232,pack f231,pack f322,pack f469,pack f1924,pack f1926,pack f1929,pack f1934,pack f1935,pack f1939,pack f1738,pack f2451,pack f2332,pack f791,pack f2574,pack f793,pack f2075,pack f2547,pack f721,pack f3375,pack f2161,pack f2568,pack f436,pack f337,pack f2481,pack f380] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3383 : H a 0x780c60c904d14a13808e333 := rup [pack f1,pack f2643,pack f2644,pack f2647,pack f2653,pack f2655,pack f787,pack f1175,pack f798,pack f1156,pack f1210,pack f1192,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3384 : H a 0xc620d08e245533 := rup [pack f1,pack f2671,pack f2673] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3385 : H a 0xc611920d1b413808eca4c9415133417413b := rup [pack f1,pack f3357,pack f3358,pack f3365,pack f451,pack f1807,pack f747,pack f743,pack f1879,pack f3384,pack f452,pack f2684,pack f2685] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3386 : H a 0xd00c6e2304d1742c1 := rup [pack f1,pack f3353,pack f3352,pack f3264,pack f3380,pack f777,pack f2588,pack f3255,pack f3286,pack f1164,pack f3268,pack f3165,pack f2875,pack f3263,pack f3257,pack f3284,pack f3279,pack f3277,pack f3265,pack f3273,pack f45,pack f3383,pack f3385,pack f3087,pack f3281,pack f636,pack f2832,pack f239,pack f3276,pack f3266,pack f231,pack f3287,pack f3260,pack f782,pack f3381,pack f2558,pack f1887,pack f228,pack f3382] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3387 : H a 0xd00c6e2304d174 := rup [pack f1,pack f3352,pack f3264,pack f3277,pack f3265,pack f3273,pack f45,pack f3380,pack f3165,pack f3268,pack f17,pack f3255,pack f3286,pack f3263,pack f3257,pack f3284,pack f3291,pack f3373,pack f3276,pack f232,pack f231,pack f3287,pack f3260,pack f777,pack f3386,pack f781,pack f799,pack f801,pack f2704,pack f2286,pack f892,pack f894,pack f2545,pack f784,pack f786,pack f710,pack f746,pack f787,pack f2559,pack f2566,pack f2573,pack f2177,pack f647,pack f436,pack f3376] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3388 : H a 0xd02c80c6e2304d := rup [pack f1,pack f3352,pack f3353,pack f3354,pack f3357,pack f3361,pack f3356,pack f3358,pack f3362,pack f3366,pack f3367,pack f3370,pack f3264,pack f3277,pack f3265,pack f242,pack f3276,pack f3266,pack f3255,pack f3287,pack f3260,pack f646,pack f1104,pack f3286,pack f3263,pack f3257,pack f3268,pack f3373,pack f3380,pack f3279,pack f3273,pack f3281,pack f3284,pack f15,pack f2903,pack f343,pack f3387,pack f439,pack f453,pack f542,pack f2550,pack f1137,pack f1849,pack f2542,pack f2457,pack f2466,pack f2488,pack f787,pack f2191,pack f778,pack f2289,pack f2067,pack f535,pack f2910,pack f2914,pack f2912,pack f2911,pack f2141,pack f1843,pack f2013,pack f2502,pack f2511,pack f2528,pack f2398,pack f396,pack f764,pack f428,pack f370,pack f781,pack f2929,pack f2732,pack f653] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3389 : H a 0xe231190d111619114920dc54d02c282b4c82 := rup [pack f1,pack f3352,pack f3361,pack f3362,pack f3365,pack f3240,pack f3049,pack f777,pack f1151,pack f3285,pack f3277,pack f3265,pack f239,pack f750,pack f787,pack f888,pack f2612,pack f2636,pack f2712,pack f2590,pack f647,pack f445,pack f2269,pack f2279,pack f444,pack f2396,pack f1693,pack f706] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3390 : H a 0xc6e2305514918ac64d24c28c81c2cca4 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f3264,pack f3277,pack f3265,pack f647,pack f2706,pack f2707,pack f1801,pack f2486,pack f749,pack f743] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3391 : H a 0xe80c6e2304e20d2c1 := rup [pack f1,pack f3353,pack f3352,pack f3255,pack f3287,pack f3260,pack f3270,pack f2823,pack f3240,pack f3256,pack f3049,pack f777,pack f3264,pack f3276,pack f3278,pack f1151,pack f3285,pack f3266,pack f3289,pack f3272,pack f7,pack f3277,pack f3265,pack f990,pack f3286,pack f3263,pack f1164,pack f782,pack f1544,pack f1508,pack f1519,pack f2599,pack f1411,pack f3389,pack f788,pack f890,pack f1176,pack f2291,pack f1494,pack f3390,pack f3149,pack f3154,pack f3159,pack f1428,pack f1442,pack f1198,pack f1219,pack f1451,pack f42,pack f104,pack f97] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3392 : H a 0xe80c6e2304e20d := rup [pack f1,pack f3352,pack f3353,pack f3356,pack f3358,pack f3362,pack f777,pack f3264,pack f3276,pack f3278,pack f1151,pack f3266,pack f3256,pack f3289,pack f3255,pack f3287,pack f3260,pack f3270,pack f3272,pack f3277,pack f239,pack f3049,pack f3240,pack f2904,pack f3391,pack f781,pack f799,pack f801,pack f2704,pack f2286,pack f892,pack f894,pack f2545,pack f784,pack f786,pack f2600,pack f750,pack f2602,pack f2631,pack f647,pack f446,pack f1545,pack f1546,pack f444,pack f1837,pack f2530,pack f764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3393 : H a 0xe230c90d119105508d18a152c34ca4d01c2c0b2d24 := rup [pack f1,pack f3356,pack f3358,pack f3362,pack f777,pack f892,pack f710,pack f647,pack f1545,pack f1546,pack f1548,pack f1837,pack f2530,pack f2906,pack f764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3394 : H a 3336712898 := rup [pack f1,pack f3352,pack f3255,pack f3287,pack f3260,pack f137,pack f140,pack f3388,pack f138,pack f3392,pack f3166,pack f2633,pack f2609,pack f2705,pack f28,pack f777,pack f3264,pack f3276,pack f3278,pack f1151,pack f3272,pack f2124,pack f3256,pack f3282,pack f3285,pack f3266,pack f3289,pack f3277,pack f239,pack f3270,pack f3274,pack f7,pack f990,pack f2916,pack f3286,pack f657,pack f781,pack f2286,pack f892,pack f2138,pack f2600,pack f2589,pack f445,pack f444,pack f3393,pack f3242,pack f3244,pack f3252,pack f2957,pack f2943,pack f2155,pack f2186,pack f1029,pack f1013,pack f536,pack f292,pack f5] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3395 : H a 0xc909a13811614508d07c18517423c1b4c63 := rup [pack f1,pack f239,pack f710,pack f3051,pack f3055,pack f2645,pack f2676,pack f2687,pack f1916,pack f1939,pack f452,pack f228] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3396 : H a 814627 := rup [pack f1,pack f3352,pack f3361,pack f3362,pack f3365,pack f140,pack f138,pack f137,pack f777,pack f3255,pack f3264,pack f3286,pack f3287,pack f3388,pack f3276,pack f3277,pack f1164,pack f3263,pack f3260,pack f3256,pack f3272,pack f3274,pack f3278,pack f3270,pack f3392,pack f231,pack f3266,pack f239,pack f3285,pack f1151,pack f2548,pack f2705,pack f2609,pack f2633,pack f3166,pack f3394,pack f782,pack f3238,pack f1544,pack f2599,pack f2544,pack f1887,pack f446,pack f444,pack f3395,pack f647,pack f2254,pack f2267,pack f2269,pack f2278,pack f797,pack f2824,pack f2396,pack f1692,pack f706] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3397 : H a 48940098339532 := rup [pack f1,pack f3366,pack f3367,pack f3370,pack f658,pack f653] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3398 : H a 0x51031091013012019010d := rup [pack f1,pack f18,pack f23] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3399 : H a 0x120261292130310510910c63 := rup [pack f1,pack f561,pack f570,pack f3048,pack f1069,pack f3398] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3400 : H a 0xc6d02c2bca41c2 := rup [pack f1,pack f3353,pack f3370,pack f3367,pack f3366,pack f331,pack f318,pack f2736,pack f140,pack f781,pack f3397,pack f655,pack f553,pack f538,pack f349,pack f336,pack f639,pack f928,pack f2261,pack f769,pack f3396,pack f779,pack f2259,pack f2283,pack f2281,pack f2282,pack f990,pack f1104,pack f2265,pack f1552,pack f1115,pack f1122,pack f3399,pack f2708,pack f640] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3401 : H a 0xc6d02c2bca4 := rup [pack f1,pack f3353,pack f3370,pack f3367,pack f3366,pack f331,pack f318,pack f2736,pack f140,pack f781,pack f3397,pack f655,pack f553,pack f538,pack f336,pack f639,pack f928,pack f2258,pack f769,pack f3396,pack f3400,pack f1554,pack f2711,pack f780,pack f800,pack f802,pack f2260,pack f2288,pack f640,pack f1877,pack f2017,pack f2272,pack f989,pack f1107,pack f561,pack f570,pack f3050,pack f1121,pack f1069,pack f1977,pack f2034,pack f1114,pack f2023,pack f3398,pack f250,pack f245,pack f3063] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3402 : H a 48507395058731 := rup [pack f1,pack f3352,pack f779,pack f802,pack f800,pack f2203,pack f1500,pack f476,pack f783,pack f782,pack f893,pack f2961,pack f891,pack f3069,pack f798,pack f431,pack f639,pack f2287,pack f3401,pack f2253,pack f2664,pack f1259,pack f1243,pack f3198,pack f3233,pack f590,pack f3153,pack f598,pack f897,pack f1272,pack f1288,pack f46,pack f43] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3403 : H a 32168249967048 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f648,pack f652] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3404 : H a 7534890035 := rup [pack f1,pack f3355,pack f3354,pack f466,pack f475,pack f1567,pack f2302,pack f3403] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3405 : H a 0xe24c340e1d24c2cc28420820b01220ca3 := rup [pack f1,pack f590,pack f596,pack f644,pack f897,pack f930,pack f561,pack f3,pack f912] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3406 : H a 0xe020d21c82c1 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f3352,pack f779,pack f477,pack f3403,pack f335,pack f650,pack f537,pack f1377,pack f1370,pack f573,pack f362,pack f3404,pack f777,pack f782,pack f3238,pack f800,pack f3402,pack f1554,pack f954,pack f973,pack f891,pack f783,pack f1178,pack f938,pack f3405,pack f642,pack f638,pack f2294,pack f2918,pack f1260,pack f1304,pack f73,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3407 : H a 0xe02c341cb1e3238220ca4c64c2cc82 := rup [pack f1,pack f779,pack f335,pack f537,pack f1377,pack f1370,pack f342,pack f777,pack f787,pack f1556,pack f645,pack f638,pack f2294,pack f2918,pack f1258,pack f1344,pack f72,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3408 : H a 0xe02c341cb1e3d01ca4c64c2c := rup [pack f1,pack f537,pack f933,pack f335,pack f1174,pack f779,pack f1377,pack f1370,pack f362,pack f777,pack f3407,pack f889,pack f797,pack f1557,pack f645,pack f638,pack f2294,pack f2918,pack f1303,pack f1342,pack f70,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3409 : H a 0xe020d21c8ca4c64 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f3406,pack f781,pack f779,pack f477,pack f3403,pack f335,pack f650,pack f537,pack f1389,pack f573,pack f362,pack f3404,pack f777,pack f772,pack f3408,pack f2285,pack f2262,pack f2260,pack f2280,pack f1547,pack f1136,pack f640,pack f3243,pack f2922,pack f2299,pack f1808,pack f1694,pack f225,pack f220] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3410 : H a 0xe020d21c8ca4 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f3352,pack f477,pack f779,pack f3403,pack f650,pack f537,pack f3406,pack f781,pack f933,pack f544,pack f362,pack f342,pack f335,pack f3404,pack f476,pack f777,pack f773,pack f3409,pack f561,pack f570,pack f641,pack f710,pack f3047,pack f3053,pack f1301,pack f1131,pack f969,pack f2051,pack f1127,pack f950,pack f2040,pack f929,pack f915,pack f889,pack f841,pack f840,pack f2917,pack f3,pack f787,pack f790,pack f792,pack f1297,pack f1162,pack f6,pack f230,pack f901,pack f902,pack f1556,pack f1318,pack f1330,pack f3251,pack f52,pack f642,pack f2272,pack f2275,pack f2236,pack f2228,pack f2376,pack f2373,pack f2462,pack f2447,pack f3049,pack f426,pack f417,pack f413,pack f419,pack f2926] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3411 : H a 60163957192 := rup [pack f1,pack f3368,pack f3369,pack f3370,pack f3352,pack f477,pack f476,pack f779,pack f777,pack f3403,pack f335,pack f342,pack f362,pack f650,pack f537,pack f573,pack f3406,pack f781,pack f933,pack f3410,pack f590,pack f596,pack f643,pack f750,pack f3148,pack f3157,pack f1253,pack f970,pack f951,pack f930,pack f903,pack f889,pack f813,pack f814,pack f2917,pack f3,pack f797,pack f794,pack f796,pack f1243,pack f1150,pack f11,pack f238,pack f911,pack f1266,pack f1284,pack f2692,pack f2701,pack f3196,pack f3226,pack f1526,pack f1537,pack f3019,pack f3042,pack f43,pack f2227,pack f2234,pack f625,pack f624,pack f634,pack f628,pack f917] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3412 : H a 0xd01d24d14d08 := rup [pack f1,pack f3356,pack f3358,pack f3362,pack f767,pack f764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3413 : H a 57738339337044 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f669,pack f677] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3414 : H a 0xa2ca21b24a34e24a28aa4 := rup [pack f1,pack f628,pack f632] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3415 : H a 0xd8060158055858458258 := rup [pack f1,pack f43,pack f46] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3416 : H a 0xd0256485728954c077702 := rup [pack f1,pack f3362,pack f3364,pack f3369,pack f866,pack f1275,pack f1142,pack f1638,pack f2789,pack f678] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3417 : H a 0x56485728954c077701541 := rup [pack f1,pack f3362,pack f3364,pack f3369,pack f864,pack f1278,pack f1145,pack f1639,pack f2790,pack f678] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3418 : H a 0x29028938c2ac68ca8c29c := rup [pack f1,pack f366,pack f370] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3419 : H a 0xd0252285754c077 := rup [pack f1,pack f3354,pack f51,pack f92,pack f2452,pack f2412,pack f1280,pack f608,pack f3416,pack f1276,pack f1143,pack f295,pack f391,pack f3417,pack f1990,pack f1076,pack f3418] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3420 : H a 8745643 := rup [pack f1,pack f492,pack f167,pack f92,pack f51,pack f2142,pack f2144,pack f2145,pack f2146] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3421 : H a 90333214524048 := rup [pack f1,pack f3354,pack f3420,pack f51,pack f92,pack f2452,pack f2412,pack f1280,pack f3418,pack f374,pack f424,pack f739,pack f2461,pack f336,pack f349,pack f2305,pack f1199,pack f1172,pack f2355,pack f865,pack f866,pack f1206,pack f3419,pack f796,pack f1292,pack f1153,pack f1188,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3422 : H a 90333214472843 := rup [pack f1,pack f3353,pack f3356,pack f3358,pack f3362,pack f3354,pack f15,pack f31,pack f2904,pack f3420,pack f167,pack f92,pack f51,pack f613,pack f2461,pack f2469,pack f2470,pack f1076,pack f2465,pack f2076,pack f2099,pack f2463,pack f3412,pack f208,pack f224,pack f765,pack f1870,pack f1896,pack f2156,pack f2230,pack f2131,pack f2200,pack f2526,pack f2527,pack f2531,pack f2532,pack f2236,pack f2180,pack f1842,pack f310,pack f292,pack f291,pack f1840,pack f309] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3423 : H a 0x5222cb541096701 := rup [pack f1,pack f3354,pack f2376,pack f2305,pack f2088,pack f790,pack f786,pack f864,pack f853,pack f850,pack f1961,pack f1053,pack f2338,pack f2372,pack f350] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3424 : H a 90333214523542 := rup [pack f1,pack f3353,pack f3354,pack f3362,pack f3364,pack f3369,pack f3421,pack f51,pack f92,pack f2452,pack f2412,pack f3420,pack f3422,pack f367,pack f2305,pack f2310,pack f2306,pack f468,pack f2308,pack f77,pack f2307,pack f59,pack f1076,pack f15,pack f31,pack f2785,pack f1280,pack f608,pack f53,pack f3423,pack f785,pack f1275,pack f1291,pack f1180,pack f1282,pack f1281,pack f42,pack f1147,pack f3416,pack f1638,pack f682] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3425 : H a 22054007452 := rup [pack f1,pack f3353,pack f3354,pack f3362,pack f3364,pack f3369,pack f3420,pack f51,pack f92,pack f2452,pack f2412,pack f608,pack f3421,pack f15,pack f31,pack f2785,pack f3422,pack f367,pack f2305,pack f1076,pack f3424,pack f2361,pack f680,pack f678] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3426 : H a 92931890615628 := rup [pack f1,pack f3369,pack f3364,pack f3362,pack f678,pack f684] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3427 : H a 22054010114 := rup [pack f1,pack f3355,pack f3362,pack f3364,pack f3369,pack f3425,pack f261,pack f242,pack f1633,pack f492,pack f167,pack f92,pack f608,pack f1981,pack f1989,pack f1990,pack f1986,pack f1984,pack f790,pack f1776,pack f1983,pack f3426,pack f344,pack f402,pack f682,pack f2356,pack f1298,pack f1460,pack f483,pack f2365,pack f1072,pack f2358,pack f2783,pack f1702,pack f1769,pack f174,pack f173] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3428 : H a 0x505528548708518d08588 := rup [pack f1,pack f199,pack f200] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3429 : H a 5384279 := rup [pack f1,pack f3355,pack f3356,pack f3358,pack f3362,pack f3354,pack f613,pack f607,pack f51,pack f92,pack f492,pack f2412,pack f2452,pack f3420,pack f3425,pack f242,pack f261,pack f1633,pack f1838,pack f3427,pack f2305,pack f3412,pack f525,pack f534,pack f768,pack f1075,pack f2526,pack f2527,pack f368,pack f2521,pack f2522,pack f391,pack f2461,pack f2469,pack f2465,pack f1348,pack f2907,pack f1984,pack f1734,pack f1827,pack f3428] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3430 : H a 0x23c32c2ac26ca2c22962c := rup [pack f1,pack f309,pack f310] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3431 : H a 0xec4ac0bc0a98ac2ac1ac := rup [pack f1,pack f291,pack f292] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3432 : H a 0xa64a4ca41a48 := rup [pack f1,pack f3361,pack f3363,pack f3366,pack f703,pack f697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3433 : H a 0x52c5a4534521724528d24 := rup [pack f1,pack f606,pack f609] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3434 : H a 45141488947 := rup [pack f1,pack f698,pack f215,pack f169,pack f159,pack f2665,pack f2667,pack f2670,pack f2672,pack f2674] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3435 : H a 0xa88a94aa4a81 := rup [pack f1,pack f3366,pack f3359,pack f3357,pack f738,pack f740] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3436 : H a 0x8d4891a94898c948b4994 := rup [pack f1,pack f510,pack f511] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3437 : H a 0xc94ca4c88c81 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f743,pack f747] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3438 : H a 0x11915c51c12013c31c91c := rup [pack f1,pack f252,pack f245] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3439 : H a 0x708610e08605648688628 := rup [pack f1,pack f209,pack f210] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3440 : H a 0x610708605648688e08 := rup [pack f1,pack f3368,pack f3359,pack f3358,pack f3363,pack f3362,pack f3366,pack f3365,pack f3370,pack f3369,pack f3352,pack f3354,pack f3353,pack f3439,pack f114,pack f125,pack f211,pack f2334,pack f2724,pack f2744,pack f2798,pack f2849,pack f2370,pack f2443,pack f2300,pack f74,pack f83,pack f2956,pack f2923,pack f3007,pack f3108,pack f668,pack f649,pack f688,pack f727,pack f667,pack f3403,pack f686,pack f726,pack f785,pack f871,pack f809,pack f867] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3441 : H a 0x99498c981988 := rup [pack f1,pack f3358,pack f3359,pack f3368,pack f729,pack f726] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3442 : H a 0xe0119c99498c98183b190588198581 := rup [pack f1,pack f3353,pack f3354,pack f3358,pack f3360,pack f3369,pack f794,pack f2293,pack f2719,pack f796,pack f839,pack f1928,pack f2595,pack f2133,pack f713,pack f714,pack f364,pack f500,pack f725,pack f717] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3443 : H a 62137644356500 := rup [pack f1,pack f3370,pack f3360,pack f3359,pack f711,pack f716] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3444 : H a 0x89c83c85ca1cc1c81991c := rup [pack f1,pack f270,pack f272] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3445 : H a 0xa2cc2c8298ac86c83c92c := rup [pack f1,pack f319,pack f321] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3446 : H a 0x8aba2b981e01 := rup [pack f1,pack f794,pack f2178,pack f2239,pack f783,pack f870,pack f791,pack f780,pack f882,pack f2240,pack f2177,pack f2185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3447 : H a 37239306625 := rup [pack f1,pack f794,pack f2178,pack f2239,pack f820,pack f3446,pack f779,pack f806,pack f2241,pack f2182] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3448 : H a 9091627 := rup [pack f1,pack f3355,pack f3353,pack f3352,pack f298,pack f314,pack f1839,pack f2905,pack f3447,pack f793,pack f2179,pack f2238,pack f784,pack f821,pack f875,pack f2236,pack f2180,pack f3412,pack f3249] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3449 : H a 0x8ab54864882f6415424c1 := rup [pack f1,pack f388,pack f594,pack f789,pack f1271,pack f1023,pack f825,pack f1033,pack f707,pack f797,pack f2188,pack f1060,pack f1430,pack f163,pack f161] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3450 : H a 0x8ab54864882f641542 := rup [pack f1,pack f3361,pack f3362,pack f3365,pack f298,pack f2180,pack f1023,pack f3449,pack f822,pack f1025,pack f1686,pack f2403,pack f3065,pack f709,pack f706] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3451 : H a 0x8ab54835471464882f641 := rup [pack f1,pack f2179,pack f1022,pack f63,pack f499,pack f3450,pack f821,pack f827,pack f2190,pack f1025,pack f2018,pack f2657,pack f517,pack f515] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3452 : H a 0xc48c64c41c4c := rup [pack f1,pack f3365,pack f3362,pack f3361,pack f706,pack f709] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3453 : H a 0xa982f6421154c2 := rup [pack f1,pack f1021,pack f824,pack f1025,pack f3064,pack f2401,pack f1686,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3454 : H a 0x8ab54864882f642541 := rup [pack f1,pack f298,pack f2178,pack f3453,pack f388,pack f594,pack f793,pack f1270,pack f1021,pack f823,pack f1032,pack f707,pack f797,pack f2189,pack f1058,pack f1429,pack f163,pack f161] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3455 : H a 0x83c829c2c86c92c8ab := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f3354,pack f3361,pack f3362,pack f3365,pack f298,pack f388,pack f594,pack f1636,pack f2764,pack f2787,pack f2892,pack f2806,pack f1656,pack f3448,pack f326,pack f3451,pack f793,pack f2178,pack f1021,pack f1270,pack f3454,pack f789,pack f826,pack f2180,pack f1023,pack f2571,pack f1964,pack f3059,pack f2397,pack f1029,pack f3452,pack f478,pack f708,pack f490] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3456 : H a 0x83ca2b186c47 := rup [pack f1,pack f3355,pack f314,pack f222,pack f1690,pack f1691,pack f1688,pack f293,pack f302,pack f2249,pack f2250,pack f780,pack f1894,pack f796,pack f1850,pack f228,pack f1912] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3457 : H a 0xc41186c48192 := rup [pack f1,pack f798,pack f3067,pack f2404,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3458 : H a 0xa2182538238c1861901acc63 := rup [pack f1,pack f570,pack f641,pack f3066,pack f1978,pack f2435,pack f2303,pack f365,pack f359] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3459 : H a 0xa09a2180d825c411861a8190c481ac := rup [pack f1,pack f3352,pack f3354,pack f2407,pack f3069,pack f798,pack f3458,pack f3452,pack f358,pack f432,pack f2405,pack f2592,pack f3097,pack f2927,pack f576,pack f571] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3460 : H a 0x83c829a2b82fc41 := rup [pack f1,pack f3355,pack f128,pack f38,pack f629,pack f421,pack f798,pack f1019,pack f2243,pack f1455,pack f1068,pack f3456,pack f3457,pack f1654,pack f1022,pack f793,pack f3459,pack f294,pack f304,pack f361,pack f572,pack f2125,pack f2128,pack f2129,pack f1618,pack f1574,pack f1673,pack f1250,pack f1417,pack f1049,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3461 : H a 0x82f5881c81851901a8192 := rup [pack f1,pack f3355,pack f497,pack f1021,pack f1742,pack f171,pack f170] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3462 : H a 0x5484d44c855480dc4218f := rup [pack f1,pack f3352,pack f3362,pack f3364,pack f3365,pack f3367,pack f3369,pack f14,pack f24,pack f2990,pack f2941,pack f682,pack f663,pack f3426,pack f659,pack f822] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3463 : H a 0xa2b82f5484c8c483814584c2 := rup [pack f1,pack f1020,pack f783,pack f1025,pack f2248,pack f1432,pack f1061,pack f165,pack f161] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3464 : H a 84957813544140 := rup [pack f1,pack f3365,pack f3367,pack f3369,pack f666,pack f659] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3465 : H a 0xc2c82983c86c92c8ac := rup [pack f1,pack f3354,pack f3369,pack f3367,pack f3365,pack f3353,pack f3355,pack f3445,pack f314,pack f330,pack f1637,pack f1717,pack f2742,pack f1590,pack f2788,pack f2840,pack f1564,pack f2727,pack f38,pack f128,pack f3460,pack f707,pack f797,pack f1264,pack f1020,pack f2242,pack f3462,pack f3463,pack f2239,pack f1026,pack f62,pack f516,pack f3464,pack f2317,pack f2320,pack f663,pack f2316,pack f1974,pack f2937,pack f105,pack f2589,pack f3461,pack f501,pack f496] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3466 : H a 0x829c2c83c86c92c := rup [pack f1,pack f3455,pack f3465] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3467 : H a 39386789058 := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f3354,pack f3365,pack f3366,pack f3368,pack f308,pack f314,pack f1691,pack f1603,pack f2745,pack f783,pack f2238,pack f2219,pack f3059,pack f2397,pack f2955,pack f2333,pack f3452,pack f667,pack f797,pack f785,pack f862] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3468 : H a 39386787990 := rup [pack f1,pack f3467,pack f2217,pack f2236,pack f821] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3469 : H a 35057220139 := rup [pack f1,pack f3353,pack f3365,pack f3367,pack f3369,pack f3355,pack f308,pack f1758,pack f2807,pack f2741,pack f1589,pack f1574,pack f617,pack f314,pack f629,pack f2788,pack f1265,pack f2825,pack f3467,pack f2220,pack f3464,pack f71,pack f2326,pack f2327,pack f2313,pack f663,pack f2314,pack f2938,pack f2939,pack f3468,pack f2218,pack f2237,pack f826,pack f1071,pack f1459,pack f798,pack f1696,pack f176,pack f173,pack f1963,pack f2569,pack f2223,pack f489] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3470 : H a 0x2c8688298394a229881a88984980d88b4a0a89c2a81b41901d459419c2905881c88d4c94542 := rup [pack f1,pack f633,pack f789,pack f914,pack f1155,pack f55,pack f501,pack f171,pack f512,pack f176,pack f3435] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3471 : H a 0x92b2c84c84d468882f4c1 := rup [pack f1,pack f3365,pack f3367,pack f3369,pack f3354,pack f3355,pack f128,pack f38,pack f617,pack f407,pack f308,pack f784,pack f2220,pack f1026,pack f3464,pack f71,pack f516,pack f2321,pack f2322,pack f2330,pack f353,pack f2326,pack f2325,pack f663,pack f2328,pack f2317,pack f2319,pack f1744,pack f1454,pack f2936,pack f1327,pack f1314,pack f1229,pack f2312,pack f2331,pack f472,pack f2323,pack f559,pack f2947,pack f2948,pack f2949,pack f2005,pack f111,pack f454,pack f24,pack f2725,pack f2839,pack f1975,pack f1073,pack f1731,pack f1568,pack f2746,pack f2887,pack f3470,pack f1776,pack f1032,pack f175,pack f173,pack f2223] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3472 : H a 0x92b82f541832286 := rup [pack f1,pack f3362,pack f3364,pack f3369,pack f1024,pack f790,pack f2357,pack f2997,pack f2226,pack f3426,pack f1027,pack f680,pack f519] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3473 : H a 0x458445648c484c8450468 := rup [pack f1,pack f161,pack f164] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3474 : H a 0x4c8648b01311458445381 := rup [pack f1,pack f3355,pack f1684,pack f1061,pack f1432,pack f3473] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3475 : H a 0x92b2d42c84c864882fb01311541 := rup [pack f1,pack f407,pack f617,pack f1274,pack f128,pack f790,pack f1024,pack f2221,pack f3474,pack f1019,pack f841,pack f2224,pack f3397,pack f3472,pack f2309] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3476 : H a 0x92b2d42c84c84d468864882f := rup [pack f1,pack f308,pack f3471,pack f783,pack f2219,pack f1025,pack f3475,pack f1023,pack f822,pack f1687,pack f3065,pack f2403,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3477 : H a 0x92b8ab2914c2 := rup [pack f1,pack f3355,pack f2222,pack f2183,pack f308,pack f298,pack f1689,pack f2219,pack f2181,pack f3065,pack f2403,pack f822,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3478 : H a 0x92b4c84d48ab4c1 := rup [pack f1,pack f3355,pack f3353,pack f3365,pack f3367,pack f3369,pack f3356,pack f3357,pack f3361,pack f308,pack f298,pack f2913,pack f1848,pack f784,pack f2220,pack f3464,pack f2180,pack f338,pack f663,pack f790,pack f821,pack f539,pack f887,pack f2178,pack f2537,pack f3263,pack f771] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3479 : H a 0x82983cc2c86c := rup [pack f1,pack f3355,pack f3353,pack f3466,pack f308,pack f2735,pack f1574,pack f1589,pack f2741,pack f1758,pack f1657,pack f3469,pack f3476,pack f328,pack f298,pack f1689,pack f3478,pack f2219,pack f3477,pack f2181,pack f2221,pack f820,pack f822,pack f2225,pack f2223,pack f2184,pack f3060,pack f2399,pack f3452] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3480 : H a 0x86b92b2984986184c2 := rup [pack f1,pack f3353,pack f3355,pack f289,pack f308,pack f1798,pack f2879,pack f617,pack f407,pack f563,pack f355,pack f783,pack f2219,pack f1274,pack f1232,pack f2110,pack f795,pack f842,pack f844,pack f884,pack f1351,pack f1296,pack f792,pack f2108,pack f788,pack f3437,pack f596,pack f643,pack f3157,pack f953,pack f918,pack f1190,pack f1157,pack f86,pack f58,pack f52,pack f75,pack f2116] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3481 : H a 35056433451 := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f289,pack f308,pack f2863,pack f1780,pack f1299,pack f1309,pack f1367,pack f3480,pack f784,pack f2220,pack f2109,pack f796,pack f843,pack f883,pack f2215,pack f2107,pack f3435,pack f3143] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3482 : H a 0x83cc2c86b58868892c4c1498581 := rup [pack f1,pack f784,pack f796,pack f2110,pack f845,pack f843,pack f883,pack f744,pack f787,pack f791,pack f2107,pack f790,pack f2239,pack f2180,pack f324,pack f1026,pack f1017,pack f2112,pack f1478,pack f1090,pack f183,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3483 : H a 0x86b3943884c1582682 := rup [pack f1,pack f3354,pack f3352,pack f2109,pack f795,pack f724,pack f720,pack f2506,pack f784,pack f563,pack f355,pack f733,pack f736,pack f791,pack f848,pack f2107,pack f2122,pack f2123,pack f834,pack f2153,pack f1482,pack f2622,pack f1095,pack f1996,pack f788,pack f2338,pack f2119,pack f2315,pack f2942,pack f2483,pack f3168,pack f2115,pack f2206,pack f2020,pack f1108,pack f797,pack f78,pack f85,pack f375,pack f579,pack f54,pack f57,pack f3443,pack f1213,pack f1241,pack f1286,pack f1361,pack f1381,pack f896,pack f964,pack f1256,pack f396,pack f87,pack f3415,pack f2501] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3484 : H a 0x588688498c884854904a8 := rup [pack f1,pack f183,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3485 : H a 0x83cc2c86b92c6818ac312151 := rup [pack f1,pack f2108,pack f2121,pack f2120,pack f2246,pack f1018,pack f324] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3486 : H a 0xa413121524a7 := rup [pack f1,pack f1467,pack f1474] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3487 : H a 0x83cc2c86b58868892c498a41681c888ac485 := rup [pack f1,pack f2113,pack f3485,pack f3486,pack f3484,pack f1078,pack f1083] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3488 : H a 0x83cc2c86b58839438868892c4c1498 := rup [pack f1,pack f3353,pack f3355,pack f3354,pack f784,pack f289,pack f3482,pack f795,pack f2109,pack f3483,pack f792,pack f847,pack f2108,pack f869,pack f744,pack f794,pack f2178,pack f3487,pack f2112,pack f1026,pack f324,pack f314,pack f2234,pack f2850,pack f1745,pack f2442,pack f3441] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3489 : H a 35056432279 := rup [pack f1,pack f563,pack f355,pack f289,pack f1308,pack f1309,pack f1310,pack f1311] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3490 : H a 0x86b3946947143887086884c212a14a30a := rup [pack f1,pack f3359,pack f3370,pack f3356,pack f3364,pack f3352,pack f3357,pack f3360,pack f3367,pack f1374,pack f305,pack f563,pack f355,pack f395,pack f397,pack f1215,pack f1328,pack f1388,pack f716,pack f3443,pack f756,pack f797,pack f2111,pack f752,pack f1302,pack f1340,pack f785,pack f2105,pack f1290,pack f1501,pack f1373,pack f831,pack f2658,pack f1186,pack f943,pack f3219,pack f2117,pack f2968,pack f598,pack f70,pack f791,pack f61,pack f65,pack f1272,pack f966,pack f909,pack f1230,pack f87,pack f3415,pack f2453,pack f3125,pack f730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3491 : H a 0x6946886816a4 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f734,pack f730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3492 : H a 0xa18918815838858820898 := rup [pack f1,pack f94,pack f87] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3493 : H a 0x86ba189186a38158388ab056 := rup [pack f1,pack f355,pack f289,pack f51,pack f3116,pack f3135,pack f271,pack f3492,pack f2177,pack f1323] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3494 : H a 0xa189186a381586b8388ab := rup [pack f1,pack f3352,pack f3493,pack f3124] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3495 : H a 0x83cc2c86b69468892c4c2a1814a309681 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f289,pack f792,pack f2108,pack f1354,pack f2238,pack f3491,pack f737,pack f3118,pack f3139,pack f372,pack f415,pack f1018,pack f1220,pack f324,pack f3494] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3496 : H a 0x86b309115a64216609289 := rup [pack f1,pack f2952,pack f3052,pack f1441,pack f2582,pack f564,pack f3002,pack f3000,pack f3008] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3497 : H a 0xc2c86b394714388708309115342a64216d242c1ca4815289 := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f3352,pack f3354,pack f3052,pack f3496,pack f416,pack f756,pack f752,pack f2105,pack f855,pack f3271,pack f3443,pack f1559,pack f2717,pack f2412,pack f2408,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3498 : H a 83728286763287 := rup [pack f1,pack f791,pack f736,pack f783,pack f665,pack f205,pack f523,pack f1363,pack f2173,pack f2628,pack f1484,pack f587,pack f579] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3499 : H a 0x94194c948954 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f686,pack f693] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3500 : H a 0x86b39438894c68228a := rup [pack f1,pack f3359,pack f3360,pack f3370,pack f3352,pack f2107,pack f791,pack f736,pack f355,pack f369,pack f371,pack f716,pack f3443,pack f797,pack f2111,pack f2601,pack f1464,pack f3144,pack f2930,pack f577,pack f2802,pack f1649,pack f3499] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3501 : H a 0x83cc2c86b39469471438870868892c4c212a14a := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f3352,pack f1374,pack f783,pack f665,pack f345,pack f3490,pack f3495,pack f791,pack f846,pack f842,pack f2107,pack f870,pack f874,pack f788,pack f3020,pack f2110,pack f2103,pack f769,pack f781,pack f3156,pack f3500,pack f3052,pack f3496,pack f3497,pack f416,pack f756,pack f752,pack f2105,pack f855,pack f3014,pack f3443,pack f2572,pack f1431,pack f560,pack f2409,pack f558] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3502 : H a 0xc2c86b7147084e4b01149682c81a64216198518289309 := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f3352,pack f791,pack f1194,pack f2107,pack f3052,pack f874,pack f781,pack f769,pack f870,pack f2103,pack f1176,pack f289,pack f1333,pack f788,pack f736,pack f355,pack f1144,pack f3496,pack f414,pack f416,pack f756,pack f752,pack f785,pack f2105,pack f881,pack f855,pack f1227,pack f1530,pack f2694,pack f3271,pack f3014,pack f1151,pack f2572,pack f1431,pack f1559,pack f2717,pack f624,pack f644,pack f560,pack f42,pack f558,pack f638,pack f931,pack f1242,pack f1365,pack f60] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3503 : H a 0x39471438870834230a := rup [pack f1,pack f3356,pack f3360,pack f3364,pack f395,pack f397,pack f3443,pack f756,pack f855,pack f752] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3504 : H a 0x498518438618415c18458 := rup [pack f1,pack f75,pack f76] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3505 : H a 0x829c2c86b4c2149682 := rup [pack f1,pack f3353,pack f3355,pack f3352,pack f355,pack f289,pack f1368,pack f783,pack f665,pack f3489,pack f1823,pack f1698,pack f2891,pack f2829,pack f791,pack f846,pack f842,pack f870,pack f874,pack f788,pack f3020,pack f2110,pack f793,pack f781,pack f1295,pack f1347,pack f3503,pack f3502,pack f371,pack f3500,pack f3443,pack f408,pack f2111,pack f1204,pack f2367,pack f1394,pack f1268,pack f3504] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3506 : H a 0x83c829c2c12a := rup [pack f1,pack f3353,pack f3355,pack f3479,pack f289,pack f1716,pack f2829,pack f1698,pack f1757,pack f3481,pack f3489,pack f3488,pack f783,pack f1823,pack f2891,pack f2858,pack f355,pack f303,pack f3501,pack f3505,pack f2108,pack f3491,pack f3119,pack f3132,pack f3133,pack f7,pack f3113,pack f231,pack f3122,pack f2078,pack f2104,pack f290,pack f2089,pack f2090,pack f849] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3507 : H a 0x829c2c86b4c22d42c8654648298618149 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f3353,pack f3355,pack f3354,pack f289,pack f1757,pack f2858,pack f355,pack f3505,pack f2108,pack f3491,pack f63,pack f588,pack f737,pack f3119,pack f3132,pack f3133,pack f1375,pack f382,pack f2453,pack f10,pack f3113,pack f235,pack f3122,pack f3117,pack f2446,pack f1416,pack f2560,pack f1181,pack f941,pack f70,pack f66,pack f2109,pack f2114,pack f2118,pack f2808,pack f1664,pack f849,pack f2345,pack f486,pack f157,pack f787,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3508 : H a 0x83cc2c86b69468892c4c212914a681 := rup [pack f1,pack f3357,pack f3360,pack f3367,pack f289,pack f792,pack f2108,pack f1354,pack f3491,pack f2238,pack f737,pack f3118,pack f3137,pack f3139,pack f2451,pack f1018,pack f468,pack f324,pack f298,pack f3494,pack f1376] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3509 : H a 35374930988 := rup [pack f1,pack f3355,pack f3353,pack f3479,pack f289,pack f1716,pack f2829,pack f2858,pack f1698,pack f1757,pack f3481,pack f3489,pack f3488,pack f3506,pack f2735,pack f1574,pack f2807,pack f1657,pack f1299,pack f2879,pack f1798,pack f1367,pack f3507,pack f3508,pack f846,pack f842,pack f3437,pack f2110,pack f3156] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3510 : H a 0xc2b3943883543481d41c814a := rup [pack f1,pack f3368,pack f3369,pack f3363,pack f3364,pack f3370,pack f3352,pack f431,pack f341,pack f342,pack f343,pack f3403,pack f652,pack f3413,pack f677,pack f779,pack f1391,pack f1222,pack f1200,pack f2259,pack f787,pack f2255,pack f807,pack f890,pack f2557,pack f1409,pack f2991,pack f2273,pack f3006,pack f2270,pack f792,pack f797,pack f540,pack f64,pack f65,pack f50,pack f51,pack f3443,pack f959,pack f1371,pack f1329,pack f1378,pack f1317,pack f3504,pack f2413,pack f3492] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3511 : H a 0xc2b149c81215 := rup [pack f1,pack f3354,pack f788,pack f2255,pack f2338,pack f639,pack f2260,pack f2295,pack f2080,pack f2360,pack f2369,pack f779,pack f1957,pack f1042,pack f340] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3512 : H a 0x83c829682c81 := rup [pack f1,pack f3355,pack f3353,pack f791,pack f3509,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f788,pack f2255,pack f3511,pack f2259,pack f780,pack f810,pack f878,pack f881,pack f3411,pack f2180,pack f2218,pack f786,pack f2106,pack f2288,pack f1016,pack f2257,pack f804,pack f332,pack f2239] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3513 : H a 0x815c18838820898858918 := rup [pack f1,pack f87,pack f93] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3514 : H a 0xc2b394388438898a42215249838261420c18820498618115 := rup [pack f1,pack f2271,pack f2258,pack f50,pack f51,pack f2253,pack f816,pack f82,pack f3443,pack f1359,pack f3504,pack f2413,pack f3513] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3515 : H a 0xc2b394388542438096898a42215249309363838c18820498618 := rup [pack f1,pack f789,pack f546,pack f945,pack f600,pack f554,pack f3514,pack f64,pack f65,pack f2257,pack f79,pack f3504,pack f782,pack f2970,pack f866,pack f3513,pack f1289] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3516 : H a 35374929538 := rup [pack f1,pack f3355,pack f3353,pack f3363,pack f3364,pack f3370,pack f3509,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f791,pack f3512,pack f787,pack f848,pack f812,pack f808,pack f3413,pack f1201,pack f2256,pack f1326,pack f796,pack f2259,pack f351,pack f393,pack f673,pack f1209,pack f546,pack f554,pack f1390,pack f962,pack f1372,pack f1306,pack f3515] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3517 : H a 0xc2b149942ca4c8c498161c182584cc4e43184384204904b44a849c4580554ac215 := rup [pack f1,pack f3352,pack f3354,pack f639,pack f1298,pack f2260,pack f3089,pack f2426,pack f2271,pack f809,pack f589,pack f579,pack f383,pack f375,pack f64,pack f1379,pack f939,pack f1179,pack f84,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3518 : H a 0x83c829341581 := rup [pack f1,pack f3352,pack f3354,pack f3370,pack f3364,pack f3363,pack f3355,pack f3353,pack f3509,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f3413,pack f673,pack f546,pack f1390,pack f600,pack f393,pack f2256,pack f1306,pack f2471,pack f3148,pack f788,pack f3516,pack f792,pack f639,pack f431,pack f796,pack f1247,pack f843,pack f833,pack f828,pack f662,pack f665,pack f783,pack f798,pack f1343,pack f786,pack f1197,pack f949,pack f1097,pack f2625,pack f1483,pack f1997,pack f1273,pack f2253,pack f2105,pack f2235,pack f2150,pack f2216,pack f3517,pack f74,pack f2259,pack f82,pack f3504,pack f780,pack f806,pack f2290,pack f2970,pack f3411,pack f2180,pack f2263,pack f2965,pack f332,pack f1031,pack f2983] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3519 : H a 0x83c829341216 := rup [pack f1,pack f3355,pack f3516,pack f3509,pack f3518,pack f795,pack f815,pack f2257,pack f2108,pack f788,pack f844,pack f2239,pack f2256,pack f819,pack f2217,pack f318,pack f1565,pack f2259,pack f780,pack f806,pack f879,pack f3411,pack f2180,pack f1016,pack f332] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3520 : H a 35374928705 := rup [pack f1,pack f3355,pack f3353,pack f3363,pack f3364,pack f3370,pack f3354,pack f3516,pack f792,pack f3509,pack f639,pack f318,pack f2830,pack f1699,pack f2765,pack f1619,pack f2728,pack f1565,pack f3510,pack f1298,pack f788,pack f2471,pack f1306,pack f3413,pack f351,pack f673,pack f546,pack f554,pack f1390,pack f3518,pack f720,pack f795,pack f844,pack f819,pack f815,pack f1203,pack f1995,pack f955,pack f1094,pack f1350,pack f1335,pack f793,pack f2257,pack f1245,pack f2152,pack f3519,pack f2260,pack f2271,pack f2315,pack f809,pack f50,pack f383,pack f375,pack f1379,pack f84,pack f1179,pack f67,pack f66] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3521 : H a 8636457 := rup [pack f1,pack f3355,pack f3370,pack f3369,pack f3368,pack f3353,pack f3509,pack f318,pack f431,pack f639,pack f2830,pack f1699,pack f2765,pack f1575,pack f1619,pack f2728,pack f1565,pack f3510,pack f3516,pack f792,pack f3520,pack f787,pack f811,pack f2255,pack f807,pack f1259,pack f847,pack f849,pack f790,pack f1776,pack f1540,pack f1380,pack f780,pack f1845,pack f3403,pack f660,pack f783,pack f718,pack f3411,pack f335,pack f362,pack f650,pack f2276,pack f2284,pack f2288,pack f2277,pack f1820,pack f1830,pack f537,pack f573,pack f2264,pack f2261,pack f781,pack f804,pack f841,pack f1117,pack f1510,pack f1132,pack f1349,pack f1843,pack f1266,pack f1061,pack f1432,pack f1422,pack f1055,pack f1684,pack f201,pack f216,pack f165,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3522 : H a 0x868838830c28a288258a8 := rup [pack f1,pack f127,pack f133] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3523 : H a 0x9481451581503481c8168 := rup [pack f1,pack f144,pack f151] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3524 : H a 0xb08b01b24b0c := rup [pack f1,pack f3363,pack f3359,pack f3356,pack f757,pack f762] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3525 : H a 0xa63b23b0b0d1486 := rup [pack f1,pack f3355,pack f631,pack f1113,pack f3207,pack f425,pack f1507,pack f704,pack f1353,pack f1703,pack f3215,pack f2509,pack f3036,pack f1841,pack f1825,pack f3428,pack f201] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3526 : H a 0x4c8a2ca8ca630a049ce0c942342b23b0b4580d1 := rup [pack f1,pack f3352,pack f3020,pack f2508,pack f3207,pack f120,pack f2001,pack f1982,pack f33,pack f3024,pack f3525,pack f3216,pack f3030,pack f2510,pack f232,pack f251,pack f1128,pack f240,pack f237,pack f3214,pack f3031,pack f2050,pack f2513,pack f426,pack f3026,pack f2380,pack f1661,pack f1695,pack f3473] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3527 : H a 0xb01a2ca8ca63b23b0b := rup [pack f1,pack f3355,pack f3353,pack f3352,pack f604,pack f784,pack f3020,pack f844,pack f788,pack f842,pack f792,pack f704,pack f886,pack f773,pack f2831,pack f631,pack f2000,pack f921,pack f1580,pack f398,pack f425,pack f1273,pack f1353,pack f3526,pack f3206,pack f3234,pack f2514,pack f2515,pack f3218,pack f2021,pack f2668,pack f2908,pack f2893,pack f3021,pack f520,pack f518] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3528 : H a 0xa63b23b0c0d2 := rup [pack f1,pack f3352,pack f704,pack f763,pack f884,pack f789,pack f739,pack f886,pack f779,pack f773,pack f3203,pack f477,pack f3206,pack f3234,pack f3233,pack f3411,pack f3404,pack f3033,pack f3218,pack f3217,pack f1189,pack f2693,pack f1909,pack f148,pack f2567,pack f3022,pack f3021,pack f3205,pack f2665,pack f2247,pack f2054,pack f465,pack f1130,pack f462,pack f423,pack f1561,pack f419] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3529 : H a 0xa63b230d1a090c5 := rup [pack f1,pack f763,pack f704,pack f1161,pack f1205,pack f3207,pack f886,pack f3213,pack f3231,pack f3227,pack f3228,pack f3043,pack f1163,pack f1141,pack f1184,pack f1221,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3530 : H a 0xa63b23b0ca2ca09 := rup [pack f1,pack f3352,pack f3528,pack f704,pack f763,pack f884,pack f739,pack f886,pack f779,pack f773,pack f3529,pack f1877,pack f3212,pack f3028,pack f3222,pack f3223,pack f1850,pack f3215,pack f239,pack f3214,pack f3031,pack f1940,pack f2050,pack f1895,pack f228,pack f463,pack f1129,pack f423,pack f419] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3531 : H a 0xa63b230d1a0a0c6 := rup [pack f1,pack f3352,pack f3368,pack f3369,pack f3370,pack f763,pack f1010,pack f704,pack f886,pack f779,pack f884,pack f3203,pack f139,pack f3212,pack f3232,pack f3222,pack f3040,pack f1189,pack f1529,pack f1551,pack f3211,pack f1504,pack f1424,pack f2919,pack f123,pack f118,pack f2720,pack f3403,pack f650] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3532 : H a 0xa63b230d1a0a05a := rup [pack f1,pack f3352,pack f3020,pack f3203,pack f844,pack f788,pack f704,pack f763,pack f886,pack f884,pack f1173,pack f1149,pack f3207,pack f3531,pack f3213,pack f3228,pack f3227,pack f3043,pack f1184,pack f1152,pack f1221,pack f42,pack f1195,pack f842,pack f792,pack f1193,pack f3209,pack f1488,pack f1458,pack f3024,pack f1010,pack f1504,pack f1449,pack f3215,pack f3224,pack f3229,pack f3030,pack f1427,pack f1527,pack f1549,pack f984,pack f1396,pack f119,pack f101] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3533 : H a 0xa63b230d1a0a := rup [pack f1,pack f3352,pack f3207,pack f3024,pack f763,pack f1010,pack f704,pack f886,pack f779,pack f884,pack f3203,pack f3531,pack f1909,pack f2284,pack f2232,pack f3213,pack f3231,pack f3227,pack f3228,pack f334,pack f3210,pack f3209,pack f3025,pack f2126,pack f2209,pack f2102,pack f316,pack f3532,pack f3216,pack f3230,pack f3221,pack f3225,pack f3237,pack f3036,pack f3220,pack f992,pack f239,pack f7,pack f1030,pack f1004,pack f2147,pack f2187,pack f5,pack f292] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3534 : H a 44622297868 := rup [pack f1,pack f3352,pack f3203,pack f3020,pack f3528,pack f3207,pack f3024,pack f3533,pack f3530,pack f2252,pack f2245] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3535 : H a 10894115 := rup [pack f1,pack f3352,pack f3355,pack f704,pack f1703,pack f3020,pack f631,pack f568,pack f557,pack f604,pack f621,pack f763,pack f3203,pack f1316,pack f1086,pack f1580,pack f884,pack f739,pack f3534,pack f425,pack f3527,pack f1485,pack f314,pack f329,pack f2251,pack f1812,pack f1771,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3536 : H a 0xa21b0be02a2b := rup [pack f1,pack f3353,pack f3355,pack f3354,pack f779,pack f314,pack f329,pack f2727,pack f3521,pack f1564,pack f469,pack f3411,pack f3403,pack f2508,pack f2302,pack f2296,pack f2298,pack f2304] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3537 : H a 44622199347 := rup [pack f1,pack f3354,pack f3352,pack f760,pack f2935,pack f704,pack f425,pack f2630,pack f1485,pack f2506,pack f3078,pack f3020,pack f528,pack f2696,pack f2697,pack f2176,pack f3164,pack f3023,pack f3123,pack f579,pack f2518] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3538 : H a 10894091 := rup [pack f1,pack f3354,pack f3352,pack f3535,pack f704,pack f3078,pack f3020,pack f631,pack f425,pack f760,pack f2506,pack f1485,pack f2630,pack f2935,pack f886,pack f884,pack f777,pack f742,pack f3536,pack f3537,pack f3414,pack f214,pack f1531,pack f1534,pack f2175,pack f3174,pack f3030,pack f3128,pack f579,pack f2517] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3539 : H a 44622158375 := rup [pack f1,pack f3352,pack f3363,pack f3359,pack f3356,pack f3535,pack f3538,pack f3524,pack f759,pack f784,pack f3020,pack f1531,pack f1534,pack f1829,pack f3030,pack f2898] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3540 : H a 44622158387 := rup [pack f1,pack f3352,pack f3363,pack f3359,pack f3356,pack f3535,pack f3538,pack f3524,pack f759,pack f784,pack f3020,pack f2696,pack f2697,pack f2895,pack f3023,pack f1833] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3541 : H a 10894081 := rup [pack f1,pack f3356,pack f3359,pack f3363,pack f3355,pack f3538,pack f3535,pack f704,pack f631,pack f886,pack f884,pack f3524,pack f777,pack f742,pack f789,pack f218,pack f759,pack f530,pack f2366,pack f3539,pack f3540,pack f3414,pack f314,pack f329,pack f421,pack f1637,pack f2998,pack f3426] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3542 : H a 10893867 := rup [pack f1,pack f3353,pack f3355,pack f3365,pack f3367,pack f3369,pack f3352,pack f3541,pack f783,pack f704,pack f1703,pack f631,pack f568,pack f557,pack f314,pack f329,pack f2742,pack f1590,pack f1315,pack f3521,pack f3464,pack f273,pack f469,pack f1933,pack f663,pack f2329,pack f2944,pack f1087,pack f1770,pack f1812,pack f3029,pack f181,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3543 : H a 0xa63a2883b485 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f3020,pack f1927,pack f3542,pack f3541,pack f783,pack f3535,pack f3030,pack f1949,pack f1925,pack f848,pack f1938,pack f1937,pack f3142,pack f3396,pack f632,pack f461,pack f2696,pack f2478,pack f2877,pack f3170,pack f3437,pack f745] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3544 : H a 44621269051 := rup [pack f1,pack f3352,pack f3541,pack f783,pack f704,pack f3078,pack f3020,pack f273,pack f1927,pack f1933,pack f197,pack f3543,pack f180,pack f1930,pack f3029,pack f788,pack f3148,pack f2620,pack f2168,pack f2944,pack f3130,pack f579,pack f2778,pack f2354,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3545 : H a 0xa6382a486c82 := rup [pack f1,pack f3352,pack f3361,pack f3363,pack f3366,pack f3354,pack f3356,pack f3358,pack f3362,pack f3020,pack f3046,pack f3023,pack f25,pack f3029,pack f3039,pack f239,pack f3040,pack f268,pack f267,pack f3045,pack f3025,pack f3035,pack f3034,pack f557,pack f1357,pack f2757,pack f3541,pack f1852,pack f1246,pack f322,pack f783,pack f704,pack f2418,pack f3078,pack f787,pack f848,pack f1960,pack f2563,pack f1902,pack f819,pack f815,pack f1214,pack f228,pack f695,pack f656,pack f781,pack f302,pack f451,pack f1886,pack f1881,pack f1879,pack f488,pack f1277,pack f1668,pack f2989,pack f3189,pack f705,pack f352,pack f2388,pack f2389,pack f2395,pack f2678,pack f1331,pack f1393,pack f2909,pack f107,pack f2359,pack f2500,pack f975,pack f3513,pack f2210,pack f614,pack f404,pack f3412,pack f765] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3546 : H a 0xa6382a486ca4 := rup [pack f1,pack f3352,pack f3357,pack f3358,pack f3365,pack f3020,pack f3045,pack f3025,pack f3541,pack f3545,pack f788,pack f859,pack f786,pack f2229,pack f857,pack f798,pack f2139,pack f2951,pack f3047,pack f783,pack f847,pack f2583,pack f3046,pack f1407,pack f2207,pack f1008,pack f3029,pack f1413,pack f2961,pack f3039,pack f1423,pack f239,pack f3040,pack f1398,pack f267,pack f3023,pack f3035,pack f1852,pack f187,pack f323,pack f322,pack f3542,pack f3437,pack f513,pack f533,pack f749,pack f978,pack f2092,pack f392,pack f434,pack f312,pack f1143,pack f228,pack f99,pack f1886,pack f1882,pack f569,pack f2989,pack f2921,pack f2551,pack f2082,pack f550] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3547 : H a 44619179142 := rup [pack f1,pack f3352,pack f323,pack f3541,pack f783,pack f3020,pack f3029,pack f3545,pack f788,pack f847,pack f857,pack f859,pack f2583,pack f3047,pack f2951,pack f3546,pack f3176,pack f1437,pack f3003,pack f569] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3548 : H a 0xb0282a3224e4306 := rup [pack f1,pack f3365,pack f3367,pack f3369,pack f783,pack f2737,pack f2329,pack f661,pack f3464] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3549 : H a 0xa6382ac81ca3 := rup [pack f1,pack f3352,pack f568,pack f3541,pack f788,pack f859,pack f913,pack f2951,pack f857,pack f947,pack f3047,pack f3547,pack f3030,pack f783,pack f847,pack f1436,pack f791,pack f323,pack f631,pack f927,pack f590,pack f596,pack f940,pack f898,pack f3,pack f958,pack f977,pack f539,pack f3548,pack f2586,pack f3163,pack f569,pack f3177,pack f3004] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3550 : H a 0xa6348549868849032205a := rup [pack f1,pack f3355,pack f3541,pack f704,pack f1703,pack f1465,pack f1782,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3551 : H a 0xa6382ac8181f := rup [pack f1,pack f3352,pack f3355,pack f704,pack f568,pack f3541,pack f783,pack f847,pack f791,pack f1095,pack f731,pack f788,pack f1305,pack f859,pack f857,pack f1605,pack f3547,pack f758,pack f3020,pack f271,pack f958,pack f977,pack f976,pack f1496,pack f539,pack f1341,pack f1110,pack f3548,pack f3550,pack f1697,pack f1821,pack f193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3552 : H a 0x4200a0820120220060 := rup [pack f1,pack f3] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3553 : H a 0x1302308300704300b0 := rup [pack f1,pack f5] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3554 : H a 0x1382388380780b8438 := rup [pack f1,pack f42] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3555 : H a 0x7c23c13c83c43c0bc := rup [pack f1,pack f228] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3556 : H a 31344203481547 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f650] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3557 : H a 31619081339347 := rup [pack f1,pack f3370,pack f3369,pack f3368,pack f651] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3558 : H a 86057325216979 := rup [pack f1,pack f3369,pack f3367,pack f3365,pack f664] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3559 : H a 58013536109383 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f671] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3560 : H a 57738658202443 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f673] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3561 : H a 59662602126163 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f675] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3562 : H a 58563090498403 := rup [pack f1,pack f3370,pack f3364,pack f3363,pack f677] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3563 : H a 94855767557451 := rup [pack f1,pack f3369,pack f3364,pack f3362,pack f682] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3564 : H a 0x96494c954947 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f688] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3565 : H a 0x94895494b964 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f689] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3566 : H a 0x94896494c953 := rup [pack f1,pack f3368,pack f3363,pack f3362,pack f691] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3567 : H a 0xa54a64a41a48a4c := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3568 : H a 0xa64a4ca54a47 := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f699] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3569 : H a 0xa64a48a54a4b := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f701] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3570 : H a 0xa48a63a54a4c := rup [pack f1,pack f3366,pack f3363,pack f3361,pack f705] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3571 : H a 0x5815a458c594588 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f717] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3572 : H a 99254753904007 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f719] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3573 : H a 98155175232907 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f721] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3574 : H a 99254753854867 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f723] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3575 : H a 98155175134627 := rup [pack f1,pack f3369,pack f3360,pack f3358,pack f725] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3576 : H a 0x99498898c9a3 := rup [pack f1,pack f3368,pack f3359,pack f3358,pack f729] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3577 : H a 0x6816886a469468c := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3578 : H a 0x6a468c694687 := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f732] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3579 : H a 0x6886946a468b := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f734] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3580 : H a 0x6a468868c693 := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f735] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3581 : H a 0x68869468c6a3 := rup [pack f1,pack f3367,pack f3360,pack f3357,pack f737] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3582 : H a 0xa88a94aa4a8b := rup [pack f1,pack f3366,pack f3359,pack f3357,pack f740] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3583 : H a 0xca4c8cc94c87 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f745] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3584 : H a 0xca4c88c8cc93 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f749] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3585 : H a 0xca3c8cc88c94 := rup [pack f1,pack f3365,pack f3358,pack f3357,pack f751] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3586 : H a 0xb0bb24b08b14 := rup [pack f1,pack f3363,pack f3359,pack f3356,pack f761] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3587 : H a 0xd14d08d0cd23 := rup [pack f1,pack f3362,pack f3358,pack f3356,pack f770] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3588 : H a 0xe14e24e08e01e0c := rup [pack f1,pack f3361,pack f3357,pack f3356,pack f771] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3589 : H a 0xe24e08e14e0b := rup [pack f1,pack f3361,pack f3357,pack f3356,pack f774] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3590 : H a 0xe0ce08e24e13 := rup [pack f1,pack f3361,pack f3357,pack f3356,pack f776] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3591 : H a 14688706 := rup [pack f1,pack f779] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3592 : H a 14684609 := rup [pack f1,pack f780] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3593 : H a 13640386 := rup [pack f1,pack f781] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3594 : H a 13636289 := rup [pack f1,pack f782] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3595 : H a 11543746 := rup [pack f1,pack f783] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3596 : H a 11539649 := rup [pack f1,pack f784] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3597 : H a 7350466 := rup [pack f1,pack f785] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3598 : H a 7346369 := rup [pack f1,pack f786] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3599 : H a 13116226 := rup [pack f1,pack f787] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3600 : H a 13112129 := rup [pack f1,pack f788] (by dsimp only [pack,List.map]; decide +kernel)
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3601 : H a 11019586 := rup [pack f1,pack f789] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3602 : H a 6826306 := rup [pack f1,pack f791] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3603 : H a 6822209 := rup [pack f1,pack f792] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3604 : H a 9971266 := rup [pack f1,pack f793] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3605 : H a 9967169 := rup [pack f1,pack f794] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3606 : H a 5777986 := rup [pack f1,pack f795] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3607 : H a 5773889 := rup [pack f1,pack f796] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3608 : H a 3681346 := rup [pack f1,pack f797] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3609 : H a 3677249 := rup [pack f1,pack f798] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3610 : H a 20436492994 := rup [pack f1,pack f799] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3611 : H a 37617410498 := rup [pack f1,pack f801] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3612 : H a 20436494530 := rup [pack f1,pack f803] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3613 : H a 20443833026 := rup [pack f1,pack f804] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3614 : H a 13997711810 := rup [pack f1,pack f805] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3615 : H a 14001906114 := rup [pack f1,pack f807] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3616 : H a 13985124801 := rup [pack f1,pack f808] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3617 : H a 39763846466 := rup [pack f1,pack f809] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3618 : H a 39750734273 := rup [pack f1,pack f810] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3619 : H a 13980932417 := rup [pack f1,pack f812] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3620 : H a 13998760642 := rup [pack f1,pack f813] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3621 : H a 14002954946 := rup [pack f1,pack f814] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3622 : H a 44043604673 := rup [pack f1,pack f815] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3623 : H a 44063531714 := rup [pack f1,pack f816] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3624 : H a 44046750401 := rup [pack f1,pack f817] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3625 : H a 14002955842 := rup [pack f1,pack f818] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3626 : H a 44043605569 := rup [pack f1,pack f819] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3627 : H a 20441212226 := rup [pack f1,pack f820] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3628 : H a 20423382593 := rup [pack f1,pack f821] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3629 : H a 20440165442 := rup [pack f1,pack f822] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3630 : H a 20447503938 := rup [pack f1,pack f824] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3631 : H a 52653466946 := rup [pack f1,pack f826] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3632 : H a 22578206273 := rup [pack f1,pack f827] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3633 : H a 44049897665 := rup [pack f1,pack f829] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3634 : H a 39774857410 := rup [pack f1,pack f830] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3635 : H a 44066155586 := rup [pack f1,pack f832] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3636 : H a 39772761154 := rup [pack f1,pack f833] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3637 : H a 15059128769 := rup [pack f1,pack f835] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3638 : H a 23657720194 := rup [pack f1,pack f836] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3639 : H a 7538743681 := rup [pack f1,pack f837] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3640 : H a 23665845122 := rup [pack f1,pack f838] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3641 : H a 23660865154 := rup [pack f1,pack f842] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3642 : H a 27939050881 := rup [pack f1,pack f843] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3643 : H a 23660866690 := rup [pack f1,pack f844] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3644 : H a 53708854657 := rup [pack f1,pack f845] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3645 : H a 20441476226 := rup [pack f1,pack f846] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3646 : H a 20430984833 := rup [pack f1,pack f847] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3647 : H a 23662701698 := rup [pack f1,pack f848] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3648 : H a 53710689665 := rup [pack f1,pack f849] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3649 : H a 37625538946 := rup [pack f1,pack f850] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3650 : H a 40828148353 := rup [pack f1,pack f851] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3651 : H a 53713049985 := rup [pack f1,pack f852] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3652 : H a 53731666114 := rup [pack f1,pack f853] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3653 : H a 53714884993 := rup [pack f1,pack f854] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3654 : H a 13979096833 := rup [pack f1,pack f856] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3655 : H a 47281611650 := rup [pack f1,pack f857] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3656 : H a 47264830337 := rup [pack f1,pack f858] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3657 : H a 47281612546 := rup [pack f1,pack f859] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3658 : H a 47264831233 := rup [pack f1,pack f860] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3659 : H a 47281874690 := rup [pack f1,pack f861] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3660 : H a 47268762497 := rup [pack f1,pack f862] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3661 : H a 23663224130 := rup [pack f1,pack f863] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3662 : H a 30103842050 := rup [pack f1,pack f866] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3663 : H a 30095185217 := rup [pack f1,pack f867] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3664 : H a 23669516034 := rup [pack f1,pack f868] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3665 : H a 47287904642 := rup [pack f1,pack f869] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3666 : H a 39771974914 := rup [pack f1,pack f871] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3667 : H a 39755193601 := rup [pack f1,pack f872] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3668 : H a 47287905538 := rup [pack f1,pack f873] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3669 : H a 47288167682 := rup [pack f1,pack f875] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3670 : H a 47271386369 := rup [pack f1,pack f876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3671 : H a 27940624129 := rup [pack f1,pack f877] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3672 : H a 27965531714 := rup [pack f1,pack f878] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3673 : H a 26891790082 := rup [pack f1,pack f879] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3674 : H a 30096234049 := rup [pack f1,pack f880] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3675 : H a 27948750593 := rup [pack f1,pack f882] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3676 : H a 44067990274 := rup [pack f1,pack f883] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3677 : H a 44051733121 := rup [pack f1,pack f884] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3678 : H a 60173855490 := rup [pack f1,pack f885] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3679 : H a 44051734017 := rup [pack f1,pack f886] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3680 : H a 47292885634 := rup [pack f1,pack f887] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3681 : H a 55864204801 := rup [pack f1,pack f892] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3682 : H a 53735337218 := rup [pack f1,pack f893] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3683 : H a 14684615 := rup [pack f1,pack f3355,pack f1560] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3684 : H a 34781032985 := rup [pack f1,pack f3355,pack f1563] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3685 : H a 13636295 := rup [pack f1,pack f3355,pack f1572] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3686 : H a 4722889415 := rup [pack f1,pack f3355,pack f1573] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3687 : H a 35183071943 := rup [pack f1,pack f3355,pack f1576] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3688 : H a 11539655 := rup [pack f1,pack f3355,pack f1580] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3689 : H a 34780320967 := rup [pack f1,pack f3355,pack f1586] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3690 : H a 34781369543 := rup [pack f1,pack f3355,pack f1587] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3691 : H a 7346375 := rup [pack f1,pack f3355,pack f1602] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3692 : H a 13112135 := rup [pack f1,pack f3355,pack f1605] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3693 : H a 34779796295 := rup [pack f1,pack f3355,pack f1616] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3694 : H a 34783466311 := rup [pack f1,pack f3355,pack f1617] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3695 : H a 35182547783 := rup [pack f1,pack f3355,pack f1623] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3696 : H a 35186217799 := rup [pack f1,pack f3355,pack f1624] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3697 : H a 11015495 := rup [pack f1,pack f3355,pack f1630] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3698 : H a 34784702617 := rup [pack f1,pack f3355,pack f1634] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3699 : H a 34784703001 := rup [pack f1,pack f3355,pack f1635] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3700 : H a 9967175 := rup [pack f1,pack f3355,pack f1651] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3701 : H a 4722890311 := rup [pack f1,pack f3355,pack f1655] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3702 : H a 35183072839 := rup [pack f1,pack f3355,pack f1658] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3703 : H a 5773895 := rup [pack f1,pack f3355,pack f1664] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3704 : H a 4725174425 := rup [pack f1,pack f3355,pack f1672] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3705 : H a 4983528007 := rup [pack f1,pack f3355,pack f1673] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3706 : H a 4987198023 := rup [pack f1,pack f3355,pack f1674] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3707 : H a 3677255 := rup [pack f1,pack f3355,pack f1684] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3708 : H a 34779534215 := rup [pack f1,pack f3355,pack f1697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3709 : H a 10753415 := rup [pack f1,pack f3355,pack f1703] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3710 : H a 23748252185 := rup [pack f1,pack f3355,pack f1713] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3711 : H a 23742025833 := rup [pack f1,pack f3355,pack f1715] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3712 : H a 9417814129 := rup [pack f1,pack f3355,pack f1723] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3713 : H a 23748350065 := rup [pack f1,pack f3355,pack f1724] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3714 : H a 23748350513 := rup [pack f1,pack f3355,pack f1725] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3715 : H a 6560135 := rup [pack f1,pack f3355,pack f1742] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3716 : H a 9705095 := rup [pack f1,pack f3355,pack f1749] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3717 : H a 34779534983 := rup [pack f1,pack f3355,pack f1755] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3718 : H a 34780321415 := rup [pack f1,pack f3355,pack f1756] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3719 : H a 35182286471 := rup [pack f1,pack f3355,pack f1763] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3720 : H a 35183072903 := rup [pack f1,pack f3355,pack f1764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3721 : H a 3415175 := rup [pack f1,pack f3355,pack f1781] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3722 : H a 1494326407 := rup [pack f1,pack f3355,pack f1794] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3723 : H a 1495374983 := rup [pack f1,pack f3355,pack f1795] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3724 : H a 9010519175 := rup [pack f1,pack f3355,pack f1796] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3725 : H a 9279020167 := rup [pack f1,pack f3355,pack f1799] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3726 : H a 9413270663 := rup [pack f1,pack f3355,pack f1804] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3727 : H a 34779535111 := rup [pack f1,pack f3355,pack f1821] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3728 : H a 34779797255 := rup [pack f1,pack f3355,pack f1822] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3729 : H a 2891015 := rup [pack f1,pack f3355,pack f1834] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3730 : H a 1842695 := rup [pack f1,pack f3355,pack f1845] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3731 : H a 14684619 := rup [pack f1,pack f3354,pack f2293] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3732 : H a 35186217419 := rup [pack f1,pack f3354,pack f2302] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3733 : H a 20594184741 := rup [pack f1,pack f3354,pack f2317] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3734 : H a 14143869989 := rup [pack f1,pack f3354,pack f2346] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3735 : H a 35185275057 := rup [pack f1,pack f3354,pack f2347] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3736 : H a 35185275953 := rup [pack f1,pack f3354,pack f2348] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3737 : H a 35182548299 := rup [pack f1,pack f3354,pack f2363] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3738 : H a 39915246629 := rup [pack f1,pack f3354,pack f2370] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3739 : H a 5773899 := rup [pack f1,pack f3354,pack f2375] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3740 : H a 44212310181 := rup [pack f1,pack f3354,pack f2387] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3741 : H a 35182286219 := rup [pack f1,pack f3354,pack f2427] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3742 : H a 9420608907 := rup [pack f1,pack f3354,pack f2428] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3743 : H a 6560139 := rup [pack f1,pack f3354,pack f2439] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3744 : H a 4922585189 := rup [pack f1,pack f3354,pack f2454] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3745 : H a 3415179 := rup [pack f1,pack f3354,pack f2471] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3746 : H a 53872840805 := rup [pack f1,pack f3354,pack f2484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3747 : H a 53872841253 := rup [pack f1,pack f3354,pack f2485] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3748 : H a 53873938737 := rup [pack f1,pack f3354,pack f2489] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3749 : H a 4987659 := rup [pack f1,pack f3354,pack f2506] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3750 : H a 2891019 := rup [pack f1,pack f3354,pack f2519] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3751 : H a 1426677003 := rup [pack f1,pack f3354,pack f2526] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3752 : H a 1842699 := rup [pack f1,pack f3354,pack f2536] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3753 : H a 5131776177 := rup [pack f1,pack f3354,pack f2540] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3754 : H a 14684627 := rup [pack f1,pack f3353,pack f2719] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3755 : H a 35051966931 := rup [pack f1,pack f3353,pack f2728] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3756 : H a 34981696211 := rup [pack f1,pack f3353,pack f2733] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3757 : H a 34981696723 := rup [pack f1,pack f3353,pack f2738] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3758 : H a 34982745299 := rup [pack f1,pack f3353,pack f2739] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3759 : H a 7346387 := rup [pack f1,pack f3353,pack f2743] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3760 : H a 13112147 := rup [pack f1,pack f3353,pack f2747] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3761 : H a 34578420563 := rup [pack f1,pack f3353,pack f2758] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3762 : H a 34582090579 := rup [pack f1,pack f3353,pack f2759] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3763 : H a 2772587347 := rup [pack f1,pack f3353,pack f2760] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3764 : H a 34981172051 := rup [pack f1,pack f3353,pack f2761] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3765 : H a 34984842067 := rup [pack f1,pack f3353,pack f2762] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3766 : H a 35051090089 := rup [pack f1,pack f3353,pack f2764] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3767 : H a 35051967315 := rup [pack f1,pack f3353,pack f2765] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3768 : H a 35048297811 := rup [pack f1,pack f3353,pack f2787] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3769 : H a 6822227 := rup [pack f1,pack f3353,pack f2793] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3770 : H a 2369837395 := rup [pack f1,pack f3353,pack f2797] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3771 : H a 17868429651 := rup [pack f1,pack f3353,pack f2799] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3772 : H a 34981697107 := rup [pack f1,pack f3353,pack f2804] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3773 : H a 5773907 := rup [pack f1,pack f3353,pack f2808] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3774 : H a 4523896973 := rup [pack f1,pack f3353,pack f2814] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3775 : H a 4523897869 := rup [pack f1,pack f3353,pack f2815] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3776 : H a 17801304659 := rup [pack f1,pack f3353,pack f2816] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3777 : H a 12850067 := rup [pack f1,pack f3353,pack f2827] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3778 : H a 10753427 := rup [pack f1,pack f3353,pack f2831] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3779 : H a 34980910483 := rup [pack f1,pack f3353,pack f2837] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3780 : H a 34982745491 := rup [pack f1,pack f3353,pack f2838] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3781 : H a 6560147 := rup [pack f1,pack f3353,pack f2846] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3782 : H a 28237254757 := rup [pack f1,pack f3353,pack f2855] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3783 : H a 28244594981 := rup [pack f1,pack f3353,pack f2856] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3784 : H a 3415187 := rup [pack f1,pack f3353,pack f2866] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3785 : H a 54007058981 := rup [pack f1,pack f3353,pack f2876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3786 : H a 54006288681 := rup [pack f1,pack f3353,pack f2879] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3787 : H a 54008123689 := rup [pack f1,pack f3353,pack f2880] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3788 : H a 4987667 := rup [pack f1,pack f3353,pack f2894] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3789 : H a 2891027 := rup [pack f1,pack f3353,pack f2899] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3790 : H a 14684643 := rup [pack f1,pack f3352,pack f2916] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3791 : H a 17601278489 := rup [pack f1,pack f3352,pack f2924] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3792 : H a 34781147673 := rup [pack f1,pack f3352,pack f2925] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3793 : H a 34713195235 := rup [pack f1,pack f3352,pack f2931] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3794 : H a 4722889443 := rup [pack f1,pack f3352,pack f2934] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3795 : H a 11539683 := rup [pack f1,pack f3352,pack f2935] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3796 : H a 4722889955 := rup [pack f1,pack f3352,pack f2944] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3797 : H a 34784293401 := rup [pack f1,pack f3352,pack f2945] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3798 : H a 7346403 := rup [pack f1,pack f3352,pack f2951] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3799 : H a 4515223779 := rup [pack f1,pack f3352,pack f2954] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3800 : H a 17600452835 := rup [pack f1,pack f3352,pack f2958] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3801 : H a 17601501411 := rup [pack f1,pack f3352,pack f2959] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3802 : H a 13112163 := rup [pack f1,pack f3352,pack f2961] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3803 : H a 14546457621 := rup [pack f1,pack f3352,pack f2968] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3804 : H a 2508280675 := rup [pack f1,pack f3352,pack f2969] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3805 : H a 34782720153 := rup [pack f1,pack f3352,pack f2976] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3806 : H a 34782721049 := rup [pack f1,pack f3352,pack f2977] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3807 : H a 9009993059 := rup [pack f1,pack f3352,pack f2992] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3808 : H a 34779796835 := rup [pack f1,pack f3352,pack f2993] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3809 : H a 34781369699 := rup [pack f1,pack f3352,pack f2994] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3810 : H a 6822243 := rup [pack f1,pack f3352,pack f2999] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3811 : H a 40319946905 := rup [pack f1,pack f3352,pack f3009] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3812 : H a 34713196131 := rup [pack f1,pack f3352,pack f3015] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3813 : H a 4722890339 := rup [pack f1,pack f3352,pack f3018] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3814 : H a 5773923 := rup [pack f1,pack f3352,pack f3020] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3815 : H a 3677283 := rup [pack f1,pack f3352,pack f3047] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3816 : H a 4515224675 := rup [pack f1,pack f3352,pack f3057] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3817 : H a 4727386265 := rup [pack f1,pack f3352,pack f3061] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3818 : H a 12850083 := rup [pack f1,pack f3352,pack f3069] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3819 : H a 34779534243 := rup [pack f1,pack f3352,pack f3075] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3820 : H a 10753443 := rup [pack f1,pack f3352,pack f3078] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3821 : H a 34578159011 := rup [pack f1,pack f3352,pack f3088] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3822 : H a 1434539427 := rup [pack f1,pack f3352,pack f3090] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3823 : H a 8950732195 := rup [pack f1,pack f3352,pack f3091] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3824 : H a 34779534755 := rup [pack f1,pack f3352,pack f3094] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3825 : H a 9017857443 := rup [pack f1,pack f3352,pack f3095] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3826 : H a 6560163 := rup [pack f1,pack f3352,pack f3107] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3827 : H a 17601501603 := rup [pack f1,pack f3352,pack f3109] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3828 : H a 9705123 := rup [pack f1,pack f3352,pack f3112] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3829 : H a 34779535011 := rup [pack f1,pack f3352,pack f3129] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3830 : H a 4722890403 := rup [pack f1,pack f3352,pack f3130] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3831 : H a 5511843 := rup [pack f1,pack f3352,pack f3140] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3832 : H a 4718697123 := rup [pack f1,pack f3352,pack f3145] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3833 : H a 3415203 := rup [pack f1,pack f3352,pack f3148] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3834 : H a 54275395661 := rup [pack f1,pack f3352,pack f3164] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3835 : H a 54275428437 := rup [pack f1,pack f3352,pack f3167] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3836 : H a 54275428885 := rup [pack f1,pack f3352,pack f3168] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3837 : H a 4714765475 := rup [pack f1,pack f3352,pack f3174] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3838 : H a 54274658841 := rup [pack f1,pack f3352,pack f3175] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3839 : H a 4727648793 := rup [pack f1,pack f3352,pack f3176] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3840 : H a 9180963 := rup [pack f1,pack f3352,pack f3185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3841 : H a 1493800739 := rup [pack f1,pack f3352,pack f3192] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3842 : H a 34779535139 := rup [pack f1,pack f3352,pack f3193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3843 : H a 34779797283 := rup [pack f1,pack f3352,pack f3194] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3844 : H a 4987683 := rup [pack f1,pack f3352,pack f3203] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3845 : H a 47836139673 := rup [pack f1,pack f3352,pack f3223] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3846 : H a 2891043 := rup [pack f1,pack f3352,pack f3238] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3847 : H a 1293999395 := rup [pack f1,pack f3352,pack f3247] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3848 : H a 1428249891 := rup [pack f1,pack f3352,pack f3248] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3849 : H a 2569116963 := rup [pack f1,pack f3352,pack f3250] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3850 : H a 1842723 := rup [pack f1,pack f3352,pack f3255] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3851 : H a 4729221273 := rup [pack f1,pack f3352,pack f3277] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3852 : H a 0xb08348328059305318310819 := rup [pack f1,pack f3708,pack f3727,pack f193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3853 : H a 0x58848534249868849032281a := rup [pack f1,pack f1470,pack f1581,pack f3484,pack f188] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3854 : H a 0xa6382ac81322305 := rup [pack f1,pack f704,pack f3709,pack f3547,pack f3600,pack f1305,pack f3541,pack f3595,pack f3646,pack f731,pack f568,pack f3602,pack f1095,pack f3853,pack f3550,pack f599,pack f3551,pack f3657,pack f913,pack f3798,pack f3655,pack f947,pack f3815,pack f3030,pack f1436,pack f3692,pack f323,pack f631,pack f927,pack f758,pack f2586,pack f569,pack f549,pack f618,pack f934,pack f3552,pack f906,pack f898,pack f896,pack f1339,pack f1110,pack f3852] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3855 : H a 0xa6382ac81322 := rup [pack f1,pack f3549,pack f3600,pack f3854,pack f2888,pack f2496,pack f3437,pack f3583] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3856 : H a 44619181185 := rup [pack f1,pack f3547,pack f3030,pack f3814,pack f1246,pack f323,pack f631,pack f3541,pack f3595,pack f927,pack f704,pack f3709,pack f568,pack f557,pack f3600,pack f3646,pack f3655,pack f3657,pack f1305,pack f731,pack f3602,pack f1436,pack f3815,pack f947,pack f3798,pack f913,pack f1095,pack f3551,pack f3855,pack f900,pack f3552,pack f258,pack f934,pack f1469,pack f3004,pack f3484,pack f569,pack f188,pack f1812,pack f1813,pack f1814,pack f470,pack f2585,pack f1582,pack f1584,pack f1596,pack f1591,pack f457,pack f1336,pack f1369,pack f1300,pack f527,pack f67] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3857 : H a 0xa41485c886814904988a8c410e8873 := rup [pack f1,pack f3709,pack f443,pack f470,pack f493,pack f2575,pack f2577,pack f2581,pack f3719,pack f987,pack f1456,pack f1460,pack f1154,pack f3484,pack f101] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3858 : H a 0xa6382a321701868 := rup [pack f1,pack f704,pack f3547,pack f3856,pack f744,pack f3814,pack f3647,pack f557,pack f3599,pack f1094,pack f1322,pack f3030,pack f3626,pack f1487,pack f3603,pack f3598,pack f3634,pack f3675,pack f1396,pack f3857,pack f777,pack f772,pack f3622,pack f3611,pack f1332,pack f1102,pack f3593,pack f3663,pack f3654,pack f3798,pack f3541,pack f3595,pack f967,pack f1543,pack f3604,pack f3810,pack f955,pack f919,pack f750,pack f331,pack f323,pack f320,pack f631,pack f927,pack f569,pack f561,pack f3054,pack f935,pack f3552,pack f230,pack f908,pack f907,pack f904,pack f905,pack f1512,pack f3246,pack f1364,pack f1124,pack f3429,pack f1134,pack f1384,pack f1685,pack f1395,pack f1139,pack f642,pack f91,pack f225,pack f39,pack f220,pack f36,pack f3404,pack f135,pack f3522,pack f2726] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3859 : H a 0xa6382a321701 := rup [pack f1,pack f704,pack f3856,pack f3599,pack f3622,pack f3593,pack f3626,pack f3604,pack f3814,pack f3647,pack f3603,pack f325,pack f320,pack f3820,pack f3598,pack f3654,pack f3675,pack f3634,pack f3611,pack f715,pack f3858,pack f168,pack f1435,pack f1437,pack f1438,pack f1443,pack f1444,pack f1448,pack f2597,pack f2135,pack f1875,pack f3031,pack f1452,pack f3028,pack f3791,pack f3827,pack f3027,pack f1011,pack f1006,pack f985,pack f998,pack f2077,pack f571,pack f2140,pack f297,pack f3553,pack f3431,pack f2392,pack f2819,pack f979,pack f982,pack f1666,pack f3570] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3860 : H a 0xa6382a702867 := rup [pack f1,pack f3814,pack f3661,pack f3547,pack f3030,pack f704,pack f3856,pack f3599,pack f3622,pack f1543,pack f3626,pack f1487,pack f320,pack f3541,pack f3595,pack f631,pack f131,pack f1434,pack f1437,pack f1631,pack f1533,pack f3807,pack f1515,pack f3426,pack f132,pack f2364,pack f468] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3861 : H a 0xa6382a702219099 := rup [pack f1,pack f3541,pack f3595,pack f1515,pack f3860,pack f3814,pack f3661,pack f3831,pack f3659,pack f3815,pack f3547,pack f3030,pack f704,pack f3856,pack f3599,pack f3626,pack f1487,pack f3647,pack f2691,pack f3810,pack f750,pack f327,pack f325,pack f323,pack f3535,pack f631,pack f1631,pack f3032,pack f3807,pack f3849,pack f3426,pack f2587,pack f620,pack f344,pack f569,pack f2638,pack f595] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3862 : H a 0xa6382a702219 := rup [pack f1,pack f3860,pack f3547,pack f3030,pack f704,pack f3856,pack f3599,pack f3626,pack f3604,pack f3597,pack f3650,pack f1424,pack f3541,pack f3659,pack f3815,pack f3622,pack f1543,pack f3814,pack f3647,pack f3810,pack f3603,pack f557,pack f1322,pack f1094,pack f744,pack f323,pack f3709,pack f1506,pack f3861,pack f3041,pack f3031,pack f1522,pack f3028,pack f3801,pack f3038,pack f3037,pack f3044,pack f569,pack f77,pack f32,pack f2578,pack f123,pack f212,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3863 : H a 44619178785 := rup [pack f1,pack f3814,pack f3856,pack f3647,pack f3603,pack f704,pack f557,pack f3599,pack f1322,pack f1094,pack f744,pack f3547,pack f3030,pack f2031,pack f322,pack f3541,pack f3595,pack f3709,pack f967,pack f1969,pack f3859,pack f3659,pack f2073,pack f3862,pack f263,pack f1468,pack f277,pack f3444,pack f3484,pack f1588,pack f186] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3864 : H a 44619179778 := rup [pack f1,pack f3856,pack f3863,pack f899,pack f704,pack f3599,pack f3622,pack f1346,pack f3626,pack f3604,pack f694,pack f3814,pack f3647,pack f3603,pack f557,pack f1322,pack f1094,pack f955,pack f919,pack f744,pack f3547,pack f3030,pack f631,pack f3541,pack f3595,pack f927,pack f3709,pack f568,pack f753,pack f3597,pack f3659,pack f3862,pack f3650,pack f1116,pack f3707,pack f258,pack f1468,pack f1424,pack f3552,pack f3484,pack f271,pack f974,pack f960,pack f971,pack f186,pack f3717,pack f1835,pack f1059,pack f1267,pack f163,pack f1504,pack f201] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3865 : H a 44619178522 := rup [pack f1,pack f704,pack f3547,pack f3856,pack f744,pack f3814,pack f3647,pack f557,pack f3599,pack f1094,pack f1322,pack f3030,pack f3626,pack f1487,pack f3603,pack f3864,pack f3598,pack f3634,pack f3675,pack f1396,pack f3857,pack f3798,pack f3863,pack f899,pack f3810,pack f955,pack f919,pack f323,pack f631,pack f3541,pack f3595,pack f927,pack f258,pack f1437,pack f3552,pack f569,pack f958,pack f3062,pack f539,pack f3056,pack f3548] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3866 : H a 0x588485c88341490498219819 := rup [pack f1,pack f3690,pack f1471,pack f186,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3867 : H a 10893354 := rup [pack f1,pack f631,pack f3541,pack f3595,pack f927,pack f704,pack f3709,pack f3814,pack f557,pack f3547,pack f3030,pack f3856,pack f744,pack f3599,pack f3647,pack f919,pack f955,pack f1094,pack f3626,pack f3622,pack f1322,pack f3603,pack f694,pack f3604,pack f3593,pack f3863,pack f899,pack f3864,pack f3598,pack f3654,pack f3663,pack f3634,pack f3652,pack f1263,pack f1062,pack f679,pack f3865,pack f1426,pack f3866,pack f271,pack f1581,pack f3552,pack f166,pack f942,pack f3473,pack f1777,pack f3142,pack f2865,pack f3435] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3868 : H a 2659 := rup [pack f1,pack f631,pack f3541,pack f3595,pack f3867,pack f3521,pack f469,pack f3544,pack f1600,pack f116,pack f134,pack f3758,pack f3733,pack f3464] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3869 : H a 0xc88342322306 := rup [pack f1,pack f3599,pack f2888,pack f2496,pack f3437,pack f3585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3870 : H a 0x5884c8c88485490498688 := rup [pack f1,pack f181,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3871 : H a 8558215 := rup [pack f1,pack f3521,pack f469,pack f273,pack f3716,pack f1761,pack f1770,pack f1774] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3872 : H a 0x6882195884c81e4564c88485342364490 := rup [pack f1,pack f3599,pack f1402,pack f3004,pack f3870,pack f503,pack f179,pack f2083,pack f1469,pack f543,pack f540,pack f1320] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3873 : H a 0x829219c88485 := rup [pack f1,pack f3521,pack f273,pack f3809,pack f3792,pack f3690,pack f3710,pack f3871,pack f1931,pack f2967,pack f3004,pack f3599,pack f1402,pack f3872,pack f16,pack f34,pack f376,pack f3770,pack f2554,pack f541,pack f540,pack f1088,pack f1091,pack f1081,pack f1469,pack f1079,pack f1085,pack f178,pack f1307,pack f356,pack f3499,pack f3564] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3874 : H a 0x83b219486941 := rup [pack f1,pack f1930,pack f3833,pack f3600,pack f180,pack f273,pack f3825,pack f3797,pack f3603,pack f3828,pack f1925,pack f1950,pack f2615,pack f2163,pack f1928,pack f579,pack f156,pack f2778,pack f2354,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3875 : H a 79591132923042 := rup [pack f1,pack f3600,pack f2778,pack f2354,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3876 : H a 0x4e45a44a8ca44a14ac4b4 := rup [pack f1,pack f589,pack f579] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3877 : H a 0x83b2191464b3 := rup [pack f1,pack f273,pack f3809,pack f3792,pack f3684,pack f3699,pack f469,pack f447,pack f464,pack f3737,pack f3732,pack f3426,pack f3557,pack f1943,pack f3403] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3878 : H a 35049804934 := rup [pack f1,pack f3521,pack f273,pack f3825,pack f3797,pack f180,pack f1930,pack f3833,pack f3874,pack f690,pack f3602,pack f1235,pack f1926,pack f150,pack f3875,pack f3877,pack f3876,pack f296,pack f315,pack f582,pack f2160,pack f3766,pack f3768,pack f3755,pack f3829,pack f233,pack f480,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3879 : H a 35049804971 := rup [pack f1,pack f3878,pack f3873,pack f3723,pack f233,pack f1786,pack f542,pack f3521,pack f1931,pack f1815,pack f296,pack f315,pack f3768,pack f1237,pack f3771,pack f3755,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3880 : H a 0x8292194a8ca41c2 := rup [pack f1,pack f3868,pack f3879,pack f3878,pack f3521,pack f1931,pack f3873,pack f1786,pack f1815,pack f2244,pack f1814,pack f2699,pack f191,pack f273,pack f3825,pack f3809,pack f3797,pack f3699,pack f469,pack f3614,pack f3615,pack f1941,pack f3831,pack f3426,pack f1539,pack f2613,pack f3288,pack f635,pack f3563,pack f3737,pack f3876,pack f3414,pack f3768,pack f2780,pack f2786,pack f1648,pack f2371,pack f2800,pack f3499] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3881 : H a 31344203403732 := rup [pack f1,pack f3556,pack f3403] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3882 : H a 0x8292198204a8ca4 := rup [pack f1,pack f3879,pack f3878,pack f3873,pack f3723,pack f1782,pack f3521,pack f1931,pack f1786,pack f1815,pack f1814,pack f3724,pack f273,pack f3825,pack f3792,pack f3797,pack f3684,pack f469,pack f3880,pack f3592,pack f3730,pack f1936,pack f1538,pack f3411,pack f1135,pack f3881,pack f498,pack f3557,pack f2730,pack f3755,pack f2721,pack f2731,pack f1063,pack f335,pack f362,pack f3732,pack f2297,pack f1490,pack f1218,pack f1604,pack f1325,pack f128,pack f1101,pack f1118,pack f1387,pack f1355,pack f1279,pack f464,pack f1748,pack f93,pack f40,pack f3876,pack f192,pack f1665,pack f1828,pack f217] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3883 : H a 0x83b21934216205a11a23c820ca3 := rup [pack f1,pack f255,pack f253,pack f236,pack f235,pack f3160,pack f3162,pack f3159,pack f3172,pack f1925,pack f2066,pack f2008,pack f27,pack f3603,pack f274,pack f2041,pack f1987,pack f264] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3884 : H a 1156263 := rup [pack f1,pack f3868,pack f100,pack f122,pack f1466,pack f3776,pack f3740,pack f3568,pack f3567] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3885 : H a 35049807012 := rup [pack f1,pack f3878,pack f3873,pack f3724,pack f3884,pack f1783,pack f3723,pack f1782,pack f3521,pack f273,pack f3792,pack f3684,pack f3882,pack f3880,pack f972,pack f3592,pack f1936,pack f3881,pack f2731] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3886 : H a 8557081 := rup [pack f1,pack f3521,pack f273,pack f3797,pack f3825,pack f3878,pack f1931,pack f3873,pack f1786,pack f3723,pack f3724,pack f1814,pack f1815,pack f1791,pack f458,pack f3879,pack f3884,pack f3885,pack f3159,pack f3883,pack f3877,pack f37,pack f591,pack f3115] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3887 : H a 0x8194a8ca36482c82502586a481fc87 := rup [pack f1,pack f3868,pack f88,pack f37,pack f750,pack f3802,pack f590,pack f1609,pack f3833,pack f191,pack f223,pack f3017,pack f2561,pack f2093,pack f2933,pack f552,pack f551,pack f160,pack f961,pack f1783,pack f1816,pack f152,pack f3607,pack f3796,pack f3081,pack f2619,pack f2167,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3888 : H a 0x83b4a8ca36a480d119 := rup [pack f1,pack f3833,pack f273,pack f3796,pack f3161,pack f1927,pack f3183,pack f3607,pack f3079,pack f2167,pack f2619,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3889 : H a 0x8294a8ca381f := rup [pack f1,pack f3521,pack f273,pack f3886,pack f3158,pack f3121,pack f3833,pack f1930,pack f750,pack f3802,pack f596,pack f643,pack f1254,pack f469,pack f1048,pack f1578,pack f1659,pack f37,pack f3887,pack f3888,pack f3160,pack f3177,pack f1938,pack f1937,pack f3171,pack f3170,pack f3216,pack f1493,pack f3163,pack f3819,pack f3842,pack f2652,pack f2199,pack f598,pack f3869] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3890 : H a 0x829ca382011a := rup [pack f1,pack f3521,pack f3833,pack f1930,pack f750,pack f3802,pack f3886,pack f3158,pack f590,pack f258,pack f273,pack f246,pack f3160,pack f3177,pack f1938,pack f1937,pack f3171,pack f3170,pack f3216,pack f1493,pack f1829,pack f3819,pack f3842,pack f2652,pack f44,pack f2199,pack f2512,pack f598,pack f3524,pack f956,pack f920,pack f3552] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3891 : H a 35052489891 := rup [pack f1,pack f3868,pack f3886,pack f258,pack f3521,pack f273,pack f596,pack f750,pack f3833,pack f3802,pack f1930,pack f3889,pack f3890,pack f3813,pack f3794,pack f3161,pack f1413,pack f3837,pack f1927,pack f1946,pack f1944,pack f230,pack f2564,pack f2097,pack f3605,pack f926,pack f3594,pack f551,pack f946,pack f910,pack f3552] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3892 : H a 0x83bca4119342246 := rup [pack f1,pack f3868,pack f3599,pack f1413,pack f1930,pack f676,pack f273,pack f3794,pack f3813,pack f1927,pack f2564,pack f2097,pack f551,pack f2495,pack f2886,pack f3437,pack f3583] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3893 : H a 0x83b348249948b08c93 := rup [pack f1,pack f469,pack f273,pack f513,pack f533,pack f2869,pack f1826,pack f1641,pack f1038,pack f1405,pack f1569,pack f1701,pack f1499,pack f1106,pack f146,pack f195,pack f3523,pack f193,pack f2878] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3894 : H a 0x8294a8119342262c87 := rup [pack f1,pack f3521,pack f3891,pack f3892,pack f1928,pack f3606,pack f273,pack f3083,pack f670,pack f3796,pack f3886,pack f3722,pack f1816,pack f1817,pack f2618,pack f2166,pack f3876,pack f1644,pack f1828,pack f3893,pack f3583,pack f392,pack f434,pack f2476,pack f1338,pack f1238,pack f1498,pack f1824,pack f1640,pack f1700,pack f1404,pack f1566,pack f145,pack f3523,pack f194,pack f2487,pack f193] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3895 : H a 0x829ca4119342c88 := rup [pack f1,pack f3521,pack f3892,pack f3599,pack f1413,pack f670,pack f273,pack f3701,pack f3686,pack f469,pack f3437,pack f513,pack f533,pack f3584,pack f1046,pack f392,pack f434,pack f1251,pack f160,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3896 : H a 0x8294a8119342 := rup [pack f1,pack f3891,pack f3895,pack f1784,pack f3894] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3897 : H a 0x83b4a8ca44e46a43414a1245 := rup [pack f1,pack f273,pack f1928,pack f3083,pack f3606,pack f2620,pack f2168,pack f579] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3898 : H a 0x83b4a8ca44e46a4341245 := rup [pack f1,pack f3868,pack f1931,pack f1928,pack f3897,pack f3606,pack f2822,pack f2395,pack f3568,pack f3567] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3899 : H a 57257420538708 := rup [pack f1,pack f3413,pack f3560] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3900 : H a 0x8294a8119364 := rup [pack f1,pack f3521,pack f3896,pack f1931,pack f3891,pack f273,pack f3796,pack f3830,pack f3898,pack f156,pack f3875,pack f469,pack f3899,pack f3561,pack f3767,pack f3736,pack f315,pack f464,pack f587,pack f3876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3901 : H a 0x829820119c8258113c51cc1c19c89c91c := rup [pack f1,pack f3886,pack f263,pack f262,pack f3521,pack f274,pack f1968,pack f1953,pack f3438,pack f247] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3902 : H a 0x819c8248616896424658136391b226 := rup [pack f1,pack f2028,pack f2033,pack f2032,pack f3642,pack f2920,pack f2988,pack f2084,pack f2555,pack f547] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3903 : H a 0x8294a8820119 := rup [pack f1,pack f3891,pack f3886,pack f3521,pack f273,pack f3796,pack f3830,pack f3896,pack f3600,pack f1931,pack f1401,pack f3003,pack f3898,pack f156,pack f1927,pack f1879,pack f3875,pack f3900,pack f3806,pack f3805,pack f268,pack f269,pack f241,pack f244,pack f3901,pack f3902,pack f2029,pack f3595,pack f1932,pack f2172,pack f2624,pack f587,pack f3876] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3904 : H a 0x82982012019c341246225c1b := rup [pack f1,pack f3521,pack f1927,pack f3607,pack f1931,pack f156,pack f3875,pack f184,pack f3600,pack f3886,pack f258,pack f469,pack f273,pack f269,pack f430,pack f2057,pack f2059,pack f2060,pack f3806,pack f3591,pack f895,pack f3899,pack f3561,pack f3767,pack f3766,pack f2777,pack f2756,pack f2771,pack f2773,pack f2763,pack f3736,pack f2353,pack f2848,pack f1293,pack f2794,pack f390,pack f948,pack f3738,pack f1066,pack f1650,pack f3499,pack f3442,pack f3552,pack f3636,pack f3666,pack f922] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3905 : H a 0x82934124689b := rup [pack f1,pack f3521,pack f1927,pack f3607,pack f156,pack f1931,pack f184,pack f3600,pack f469,pack f273,pack f244,pack f387,pack f2003,pack f2002,pack f3698,pack f3843,pack f3728,pack f3808,pack f3805,pack f124,pack f3899,pack f3561,pack f3767,pack f3766,pack f2777,pack f2771,pack f2766,pack f3735,pack f317,pack f1345,pack f2901,pack f435,pack f2666,pack f1111,pack f203,pack f3587,pack f3433,pack f610] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3906 : H a 0x83b4a8ca434124685b := rup [pack f1,pack f1931,pack f156,pack f3875,pack f1927,pack f273,pack f236,pack f1973,pack f3824,pack f3829,pack f3602,pack f1925,pack f2615,pack f2163,pack f3876,pack f585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3907 : H a 0x8294a8820341246 := rup [pack f1,pack f3903,pack f255,pack f251,pack f246,pack f3891,pack f3886,pack f263,pack f3871,pack f3521,pack f3905,pack f3906,pack f274,pack f2057,pack f3904,pack f2058,pack f2063,pack f2064,pack f1942,pack f3782,pack f3744,pack f1925,pack f3581,pack f3577] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3908 : H a 0x8294a8820341 := rup [pack f1,pack f3868,pack f3903,pack f3891,pack f3521,pack f273,pack f3600,pack f1931,pack f1412,pack f3907,pack f1928,pack f3083,pack f1947,pack f1945,pack f3606,pack f1948,pack f2563,pack f2096,pack f696,pack f657,pack f2620,pack f2168,pack f1933,pack f555,pack f197,pack f3899,pack f3875,pack f3561,pack f2777,pack f3876,pack f2353,pack f1681,pack f2940,pack f3432,pack f422,pack f3569,pack f2950,pack f529] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3909 : H a 0x83b4a8ca43425a44e3 := rup [pack f1,pack f1930,pack f273,pack f665,pack f3795,pack f2939,pack f1949,pack f2171,pack f2623,pack f736,pack f585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3910 : H a 0x8194a8ca43425a44e44a14ac := rup [pack f1,pack f3876,pack f583,pack f2606,pack f3828,pack f3121,pack f3138,pack f3115] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3911 : H a 0x82915cc814852454ab := rup [pack f1,pack f3521,pack f1928,pack f3606,pack f296,pack f315,pack f379,pack f2154,pack f2152,pack f3768,pack f1237,pack f3771,pack f3755,pack f2554,pack f2158,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3912 : H a 0x8294a8820245 := rup [pack f1,pack f3868,pack f3521,pack f3908,pack f1930,pack f3599,pack f3903,pack f249,pack f3891,pack f3871,pack f469,pack f273,pack f2836,pack f1928,pack f3083,pack f2424,pack f3572,pack f3606,pack f3909,pack f3911,pack f3910,pack f1665,pack f3432,pack f357,pack f422,pack f3569,pack f1313,pack f1593,pack f495,pack f529,pack f1084,pack f3870,pack f188] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3913 : H a 96849505174924 := rup [pack f1,pack f3574,pack f3571] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3914 : H a 0x829354258a5427490658b593251066 := rup [pack f1,pack f3521,pack f469,pack f3741,pack f3886,pack f260,pack f2432,pack f2433,pack f2434,pack f2834,pack f2805,pack f484,pack f2734] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3915 : H a 35052488736 := rup [pack f1,pack f3891,pack f3886,pack f3521,pack f3903,pack f3908,pack f674,pack f3599,pack f1930,pack f3912,pack f154,pack f155,pack f1927,pack f1946,pack f1944,pack f3607,pack f3773,pack f3644,pack f3648,pack f2564,pack f3605,pack f3715,pack f1929,pack f3594,pack f3729,pack f2167,pack f2619,pack f665,pack f3498,pack f1514,pack f736,pack f1436,pack f1425,pack f172,pack f1397,pack f587,pack f579,pack f1644,pack f1123,pack f207,pack f204,pack f3913,pack f381,pack f3573,pack f2437,pack f1148,pack f506,pack f3914,pack f983,pack f1407,pack f95] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3916 : H a 96849706403236 := rup [pack f1,pack f3913,pack f3572] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3917 : H a 35358110278 := rup [pack f1,pack f88,pack f37,pack f1927,pack f3607,pack f962,pack f2845,pack f2438,pack f3916,pack f3821,pack f3822,pack f3092] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3918 : H a 35052487490 := rup [pack f1,pack f3521,pack f273,pack f3915,pack f3917,pack f3083,pack f3891,pack f3599,pack f1930,pack f3896,pack f964,pack f3909,pack f249,pack f3910,pack f3911] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3919 : H a 8557736 := rup [pack f1,pack f3521,pack f3891,pack f3915,pack f3917,pack f3918,pack f965,pack f584,pack f588,pack f3898] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3920 : H a 2089 := rup [pack f1,pack f3868,pack f3521,pack f273,pack f3886,pack f263,pack f3919,pack f100,pack f180,pack f1471,pack f3884,pack f2967,pack f3599,pack f1467,pack f1473,pack f3813,pack f3794,pack f1413,pack f3606,pack f3625,pack f3621,pack f236,pack f1928,pack f2564,pack f2097,pack f1929,pack f2027,pack f1934,pack f3917,pack f551,pack f2062,pack f2006,pack f274] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3921 : H a 2095 := rup [pack f1,pack f3920,pack f320] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3922 : H a 2107 := rup [pack f1,pack f3920,pack f322] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3923 : H a 2155 := rup [pack f1,pack f3920,pack f323] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3924 : H a 2219 := rup [pack f1,pack f3920,pack f325] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3925 : H a 2347 := rup [pack f1,pack f3920,pack f327] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3926 : H a 2603 := rup [pack f1,pack f3920,pack f329] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3927 : H a 3115 := rup [pack f1,pack f3920,pack f331] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3928 : H a 2385063 := rup [pack f1,pack f3868,pack f3922,pack f156,pack f155,pack f100,pack f122,pack f180,pack f580,pack f3884,pack f3763,pack f3734,pack f1467,pack f3413,pack f3562,pack f3606,pack f3625,pack f3599,pack f1470,pack f2055,pack f2564,pack f2097,pack f1971,pack f2027,pack f3813,pack f3794,pack f551,pack f2069,pack f2009,pack f3444] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3929 : H a 0x2463424854c86886642e4581 := rup [pack f1,pack f3920,pack f3922,pack f3868,pack f1305,pack f3599,pack f676,pack f3928,pack f155,pack f3607,pack f1903,pack f1862,pack f2564,pack f2097,pack f3625,pack f1871,pack f1920,pack f3555,pack f551,pack f1885,pack f1093,pack f191,pack f185,pack f177] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3930 : H a 0x4984a84856885884c8490 := rup [pack f1,pack f177,pack f188] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3931 : H a 0x2463424a1485119819 := rup [pack f1,pack f3920,pack f3868,pack f1305,pack f3928,pack f159,pack f3689,pack f3718,pack f3813,pack f3794,pack f3929,pack f718,pack f3606,pack f3432,pack f3569,pack f2820,pack f376,pack f3930] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3932 : H a 0xa483424a148511991c582 := rup [pack f1,pack f3921,pack f3923,pack f3868,pack f3926,pack f3599,pack f2019,pack f1956,pack f3606,pack f1884,pack f925,pack f3432,pack f3438,pack f352,pack f3569,pack f2386,pack f2393,pack f2379,pack f2391,pack f268,pack f254,pack f2820,pack f2390,pack f1489,pack f3832,pack f3800,pack f241,pack f1213,pack f1445,pack f1541,pack f1545,pack f3817,pack f3851,pack f3811,pack f3845,pack f3522,pack f565,pack f562,pack f630,pack f2024,pack f3414] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3933 : H a 0x2463424a1485119 := rup [pack f1,pack f3599,pack f3928,pack f159,pack f3931,pack f278,pack f3082,pack f3932,pack f3607,pack f3644,pack f3648,pack f2167,pack f2619,pack f665,pack f736,pack f3876,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3934 : H a 0x24634248513c581 := rup [pack f1,pack f3922,pack f3599,pack f3607,pack f1903,pack f1862,pack f1871,pack f1920,pack f3555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3935 : H a 40008732513413 := rup [pack f1,pack f3868,pack f3599,pack f159,pack f3933,pack f248,pack f3160,pack f3934,pack f3606,pack f3432,pack f2386,pack f2393,pack f2479,pack f508,pack f3437,pack f3583] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3936 : H a 40008732515492 := rup [pack f1,pack f3868,pack f3935,pack f187,pack f3599,pack f676,pack f155,pack f3437,pack f508,pack f3584,pack f2886,pack f2868,pack f2872,pack f2885,pack f1517,pack f1120,pack f384,pack f2474,pack f2479,pack f2494,pack f1747,pack f1844,pack f3786,pack f1356,pack f1832,pack f1650,pack f3748,pack f204,pack f288,pack f459,pack f3016,pack f2932,pack f551] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3937 : H a 0x348c814a1486b24305145150158491c8b := rup [pack f1,pack f384,pack f2482,pack f1832,pack f1650,pack f1407,pack f2509,pack f3523,pack f3524,pack f3683,pack f149,pack f3680,pack f3697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3938 : H a 0x5944984a191010e918b24964491928c93126988d08b14954489 := rup [pack f1,pack f1832,pack f1650,pack f204,pack f3586,pack f3565,pack f3499,pack f2740,pack f2857,pack f3524,pack f1998,pack f2627,pack f509] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3939 : H a 40008732513425 := rup [pack f1,pack f3920,pack f3868,pack f3936,pack f3182,pack f3155,pack f61,pack f3183,pack f3151,pack f22,pack f3160,pack f3839,pack f3158,pack f3935,pack f3003,pack f3837,pack f3162,pack f3215,pack f1356,pack f1119,pack f187,pack f184,pack f1305,pack f3599,pack f2835,pack f159,pack f156,pack f1517,pack f3937,pack f3585,pack f2886,pack f2869,pack f2874,pack f2871,pack f1747,pack f1844,pack f2896,pack f2795,pack f3938,pack f381,pack f2810,pack f3575,pack f3569,pack f3916,pack f3567,pack f3606] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3940 : H a 9767756961 := rup [pack f1,pack f3868,pack f3922,pack f159,pack f3935,pack f187,pack f3936,pack f3160,pack f3183,pack f3837,pack f3839,pack f231,pack f259,pack f3939,pack f508,pack f3585,pack f2476,pack f2383,pack f3432,pack f1871,pack f1920,pack f1883,pack f3555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3941 : H a 9767758996 := rup [pack f1,pack f3868,pack f3940,pack f590,pack f3599,pack f159,pack f3437,pack f187,pack f3583,pack f2495,pack f2479,pack f1784,pack f2386,pack f248,pack f3432,pack f3934,pack f3606] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3942 : H a 2384706 := rup [pack f1,pack f3868,pack f3920,pack f2835,pack f159,pack f3940,pack f586,pack f3941,pack f2886,pack f2868,pack f2872,pack f2809,pack f3786,pack f3787,pack f3569,pack f3567,pack f1718,pack f3606,pack f3573,pack f3916] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3943 : H a 0x246a4258b587816a1cc218a16102904924300b006a := rup [pack f1,pack f3921,pack f3926,pack f994,pack f2423,pack f202,pack f2306,pack f172,pack f2374,pack f3942,pack f3600,pack f3741,pack f1103,pack f1711,pack f2437,pack f3606,pack f700,pack f153,pack f283,pack f1719,pack f1707,pack f1734,pack f3553,pack f1728,pack f2420,pack f937,pack f2504,pack f2415,pack f2039,pack f1984,pack f29,pack f1007,pack f1002,pack f2460,pack f2231,pack f2148,pack f2507,pack f418,pack f374,pack f420] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3944 : H a 40038794925218 := rup [pack f1,pack f3920,pack f3925,pack f3606,pack f3942,pack f3600,pack f1879,pack f2835,pack f156,pack f586,pack f3875,pack f3916,pack f381,pack f3573,pack f2423,pack f3741,pack f3742,pack f2437,pack f2422,pack f2419,pack f2425,pack f1518,pack f1706,pack f1721,pack f1711,pack f2344,pack f439,pack f460,pack f279,pack f1165,pack f2677,pack f2593,pack f3413,pack f456,pack f481,pack f3561,pack f2775,pack f2749,pack f3762,pack f3761,pack f2774,pack f1126,pack f1072,pack f2980,pack f32,pack f12,pack f3943,pack f1708,pack f3711,pack f1736,pack f1720,pack f1730,pack f1732,pack f2429,pack f313,pack f566,pack f1492,pack f3110,pack f3253,pack f3076,pack f3200,pack f622,pack f601] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3945 : H a 40018379412900 := rup [pack f1,pack f3920,pack f3942,pack f2835,pack f156,pack f3916,pack f381,pack f3573,pack f2423,pack f184,pack f2344,pack f2776,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3946 : H a 0x2464a1489831485 := rup [pack f1,pack f3942,pack f156,pack f2776,pack f2344,pack f3413] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3947 : H a 0xc34874a348388318b4 := rup [pack f1,pack f3922,pack f467,pack f473] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3948 : H a 9775096417 := rup [pack f1,pack f3920,pack f3606,pack f3942,pack f2835,pack f156,pack f3944,pack f3945,pack f3082,pack f3103,pack f1706,pack f1209,pack f3575,pack f363,pack f381,pack f403,pack f2423,pack f3741,pack f3742,pack f443,pack f461,pack f3946,pack f2757,pack f3413,pack f343,pack f393,pack f2710,pack f2635,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3949 : H a 0xc8234b48505a58731c861845838889c091384380b8072 := rup [pack f1,pack f437,pack f1103,pack f1727,pack f3554,pack f2196,pack f2416,pack f2505,pack f1185,pack f394,pack f411] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3950 : H a 2386498 := rup [pack f1,pack f3920,pack f3942,pack f3600,pack f2835,pack f156,pack f3606,pack f3948,pack f554,pack f2438,pack f3899,pack f3916,pack f485,pack f3561,pack f2757,pack f586,pack f3082,pack f3824,pack f3825,pack f3103,pack f3575,pack f3079,pack f2341,pack f2776,pack f2344,pack f233,pack f262,pack f1401,pack f1705,pack f3084,pack f1209,pack f2767,pack f2768,pack f1168,pack f2349,pack f2350,pack f2754,pack f1196,pack f1156,pack f2752,pack f3949,pack f1712,pack f3712,pack f1735,pack f1729,pack f1741,pack f2781,pack f2720,pack f1036,pack f1646,pack f286,pack f494,pack f3098,pack f2996,pack f1642,pack f2928,pack f1570,pack f146,pack f482,pack f3001,pack f543] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3951 : H a 9772958853 := rup [pack f1,pack f3868,pack f3920,pack f3950,pack f3942,pack f159,pack f3432,pack f3569,pack f487,pack f1092,pack f495,pack f352,pack f1203,pack f1160,pack f1321,pack f3600,pack f3607,pack f3643,pack f3596,pack f357,pack f3647,pack f1167,pack f3709,pack f3721,pack f3928,pack f2813,pack f3484,pack f186,pack f1752,pack f1759,pack f1751,pack f1765,pack f1601,pack f437,pack f1182,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3952 : H a 2385030 := rup [pack f1,pack f3868,pack f3920,pack f3942,pack f3950,pack f3622,pack f656,pack f3626,pack f695,pack f159,pack f3432,pack f3569,pack f3607,pack f3600,pack f154,pack f2757,pack f1960,pack f2563,pack f488] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3953 : H a 582 := rup [pack f1,pack f3868,pack f159,pack f3928,pack f3942,pack f3600,pack f3721,pack f3950,pack f3607,pack f3709,pack f3432,pack f3626,pack f3622,pack f3647,pack f352,pack f357,pack f3569,pack f1321,pack f487,pack f495,pack f1092,pack f3952,pack f2386,pack f2813,pack f3484,pack f3951,pack f186,pack f1773,pack f1768,pack f1767,pack f1216,pack f1211,pack f1597,pack f936,pack f902,pack f952,pack f916,pack f960,pack f2817,pack f3552,pack f19] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3954 : H a 0x831485a4158212a4905882494a89a4d24353 := rup [pack f1,pack f3925,pack f2682,pack f674,pack f3760,pack f3721,pack f1321,pack f3647,pack f3643,pack f3484,pack f3810,pack f3844,pack f3720,pack f1768,pack f616,pack f615] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3955 : H a 0x83734ca53354c82 := rup [pack f1,pack f3953,pack f3920,pack f702,pack f3773,pack f1208,pack f2618,pack f3778,pack f90,pack f468,pack f529,pack f2324,pack f495,pack f2459,pack f1084,pack f487,pack f2166,pack f2424,pack f129,pack f746,pack f748,pack f3599,pack f378,pack f1214,pack f3413,pack f1321,pack f2810,pack f1611,pack f3783,pack f3757,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3956 : H a 35287226963 := rup [pack f1,pack f3953,pack f3924,pack f3921,pack f468,pack f2344,pack f90,pack f487,pack f495,pack f529,pack f702,pack f3773,pack f2813,pack f2212,pack f3101,pack f1084,pack f1733,pack f1208,pack f1480,pack f2678,pack f3181,pack f3111,pack f3254,pack f1509,pack f3954,pack f3955,pack f3600,pack f1213,pack f2820,pack f1518,pack f2811,pack f2809,pack f2818,pack f3774,pack f3775,pack f3433,pack f2632,pack f755,pack f3840,pack f612,pack f3188,pack f3195,pack f3197,pack f3798,pack f1435,pack f3202,pack f685,pack f2987,pack f3807,pack f2995,pack f3199,pack f1533,pack f3831,pack f1550,pack f593,pack f130] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3957 : H a 44369713736 := rup [pack f1,pack f3868,pack f3432,pack f3569] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3958 : H a 0x837485a47c8113212a := rup [pack f1,pack f3953,pack f3868,pack f3600,pack f1213,pack f2562,pack f3802,pack f169,pack f129,pack f215,pack f2022,pack f1976,pack f90,pack f2362,pack f2301,pack f2414,pack f2503,pack f3956,pack f3568,pack f468,pack f2424,pack f304,pack f307,pack f1667,pack f1679,pack f1681,pack f1680,pack f2378,pack f2377,pack f2381,pack f1418,pack f2095,pack f3793,pack f3812,pack f551,pack f2521,pack f2440,pack f401,pack f360,pack f400,pack f359,pack f1676] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3959 : H a 0x837485354582c81 := rup [pack f1,pack f3920,pack f3953,pack f3868,pack f3956,pack f3606,pack f3957,pack f215,pack f90,pack f169,pack f2211,pack f2130,pack f129,pack f2022,pack f1976,pack f2362,pack f2301,pack f2414,pack f2503,pack f3568,pack f1208,pack f2682,pack f2594,pack f2678,pack f1884,pack f1246,pack f468,pack f2424,pack f3600,pack f1166,pack f1213,pack f2554,pack f2562,pack f2660,pack f449,pack f3958,pack f3706,pack f3705,pack f1668,pack f1669,pack f1666,pack f2383,pack f2384,pack f1678,pack f2382,pack f1958,pack f3756,pack f3772,pack f484,pack f2441,pack f2523,pack f360,pack f401,pack f359,pack f400,pack f1675] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3960 : H a 0x49c4ac58c4cc48968cc8c := rup [pack f1,pack f375,pack f377] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3961 : H a 0x837485354582 := rup [pack f1,pack f3953,pack f3868,pack f3956,pack f468,pack f2424,pack f129,pack f90,pack f3606,pack f3957,pack f169,pack f215,pack f3568,pack f2455,pack f2318,pack f2157,pack f1993,pack f3959,pack f2386,pack f746,pack f1670,pack f3960] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3962 : H a 0x485a4224a4984a86884c8132 := rup [pack f1,pack f1077,pack f1792,pack f3930,pack f185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3963 : H a 0x837485581489 := rup [pack f1,pack f3920,pack f3953,pack f1209,pack f468,pack f1045,pack f3703,pack f3607,pack f1214,pack f1613,pack f1226,pack f1225,pack f3599,pack f1305,pack f1481,pack f731,pack f660,pack f1257,pack f1419,pack f3962,pack f3687,pack f3702,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3964 : H a 0x8374853544c2 := rup [pack f1,pack f468,pack f2344,pack f3961,pack f3963,pack f1213,pack f3413,pack f3695,pack f447,pack f3559,pack f600,pack f3600,pack f1629,pack f197,pack f1970,pack f3833,pack f379,pack f129,pack f1959,pack f3607,pack f3956,pack f90,pack f665,pack f3595,pack f3645,pack f1215,pack f1853,pack f897,pack f1965,pack f1952,pack f3769,pack f2584,pack f1287,pack f1954,pack f1483,pack f2826,pack f2746,pack f229,pack f491,pack f3876,pack f3106,pack f3086,pack f3093] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3965 : H a 35287225172 := rup [pack f1,pack f3956,pack f468,pack f2344,pack f129,pack f90,pack f3961,pack f1959,pack f3963,pack f376,pack f1213,pack f3600,pack f3721,pack f3413,pack f150,pack f3559,pack f1629,pack f2048,pack f546,pack f3804,pack f56,pack f3964,pack f3788,pack f3642,pack f2702,pack f1383,pack f1901,pack f2014,pack f944,pack f731,pack f3602,pack f1207,pack f1477,pack f2042,pack f1988,pack f2864,pack f2915,pack f3484,pack f257,pack f526,pack f3714,pack f1730] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3966 : H a 0x8374855814c1 := rup [pack f1,pack f3953,pack f3925,pack f1209,pack f3607,pack f3965,pack f485,pack f3760,pack f129,pack f2756,pack f2779,pack f1119,pack f2030,pack f3764,pack f100,pack f468,pack f674,pack f1080,pack f3721,pack f3749,pack f3642,pack f731,pack f3602,pack f1207,pack f1319,pack f3484,pack f3714,pack f1740,pack f185,pack f2445,pack f2535,pack f1584,pack f409,pack f405] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3967 : H a 35287225729 := rup [pack f1,pack f3920,pack f3953,pack f3965,pack f129,pack f3765,pack f2753,pack f3764,pack f2751,pack f2769,pack f3760,pack f2756,pack f2779,pack f100,pack f674,pack f3833,pack f485,pack f2165,pack f468,pack f2344,pack f90,pack f3966,pack f665,pack f3595,pack f3645,pack f1334,pack f1503,pack f2662,pack f1215,pack f1853,pack f3656,pack f3658,pack f2584,pack f2625,pack f712,pack f715,pack f2569,pack f753,pack f755,pack f2546,pack f3876,pack f3083,pack f3822,pack f3096,pack f45,pack f3208,pack f2191,pack f2552,pack f442,pack f436,pack f601,pack f1103,pack f1831,pack f3561,pack f198] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3968 : H a 8615045 := rup [pack f1,pack f3953,pack f3925,pack f468,pack f129,pack f90,pack f3965,pack f485,pack f674,pack f3760,pack f3764,pack f1080,pack f100,pack f3967,pack f718,pack f3606,pack f1208,pack f3647,pack f3643,pack f1884,pack f2132,pack f2212,pack f3111,pack f3254,pack f2081,pack f2194,pack f301,pack f3954,pack f299] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3969 : H a 35288261441 := rup [pack f1,pack f3953,pack f3922,pack f3606,pack f3968,pack f3600,pack f1214,pack f3626,pack f3622,pack f1872,pack f1921,pack f1902,pack f1861,pack f2821,pack f1211,pack f1216,pack f3555,pack f3957,pack f1677,pack f302] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3970 : H a 79621199010388 := rup [pack f1,pack f3868,pack f3957,pack f3568,pack f1671,pack f2385] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3971 : H a 8615298 := rup [pack f1,pack f3953,pack f3968,pack f187,pack f3606,pack f1208,pack f3969,pack f3599,pack f1213,pack f3970,pack f487,pack f2812,pack f3181,pack f2873,pack f3437] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3972 : H a 2103 := rup [pack f1,pack f3920,pack f3953,pack f3923,pack f90,pack f129,pack f468,pack f2424,pack f3968,pack f184,pack f2757,pack f3971,pack f3607,pack f1209,pack f2091,pack f1959,pack f3913,pack f351,pack f586,pack f3083,pack f3104,pack f3822,pack f3823,pack f3079,pack f3575,pack f1119,pack f275,pack f2966,pack f44,pack f506,pack f2833,pack f3780,pack f3779,pack f3559,pack f96,pack f3413,pack f3599,pack f1213,pack f1224,pack f1223,pack f3648,pack f1041,pack f1518,pack f1832,pack f1650,pack f1357,pack f3605,pack f3715,pack f1212,pack f3594,pack f3729,pack f1217,pack f1207,pack f204,pack f2103,pack f1962,pack f362,pack f2074,pack f1951,pack f402,pack f1856,pack f287,pack f234,pack f346,pack f340] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3973 : H a 0xc88c81c8cca4 := rup [pack f1,pack f3437,pack f3584] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3974 : H a 0xc8858134212a48924a := rup [pack f1,pack f3972,pack f3953,pack f3923,pack f3926,pack f3599,pack f1187,pack f1148,pack f305,pack f303,pack f3607,pack f3621,pack f3594,pack f3625,pack f3605,pack f348,pack f1159,pack f1202,pack f3554,pack f59,pack f450,pack f2480,pack f3973,pack f3585,pack f3835,pack f3836,pack f508,pack f2227,pack f2137,pack f2103,pack f2074,pack f1009,pack f983,pack f285,pack f282,pack f312,pack f2881,pack f3430] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3975 : H a 0xa42342130249ca3 := rup [pack f1,pack f3953,pack f3921,pack f3599,pack f3161,pack f3181,pack f3155,pack f3179,pack f3180,pack f986,pack f1015,pack f1000,pack f980,pack f3553] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3976 : H a 0xc8858134212a249 := rup [pack f1,pack f3953,pack f3923,pack f3926,pack f305,pack f303,pack f300,pack f3607,pack f3621,pack f3594,pack f3625,pack f3605,pack f3599,pack f3975,pack f3437,pack f3973,pack f508,pack f2869,pack f2882,pack f2480,pack f2492,pack f2098,pack f1009,pack f983,pack f2475,pack f2473,pack f2103,pack f2074,pack f2227,pack f2137,pack f285,pack f282,pack f312,pack f2881,pack f3430] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3977 : H a 79600796573994 := rup [pack f1,pack f3925,pack f3953,pack f3607,pack f3621,pack f3789,pack f3846,pack f3594,pack f3625,pack f2689,pack f2036,pack f3781,pack f3826,pack f3605,pack f3599,pack f3648,pack f3644,pack f670,pack f3703,pack f187,pack f3976,pack f347,pack f3974,pack f2897,pack f3236,pack f3011,pack f2803,pack f1520,pack f1362,pack f522,pack f615,pack f1415,pack f1249,pack f1579,pack f1663,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3978 : H a 0xa4234207823813824a := rup [pack f1,pack f3972,pack f1159,pack f1202,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3979 : H a 19433788226 := rup [pack f1,pack f3953,pack f3972,pack f3607,pack f187,pack f672,pack f676,pack f3599,pack f3625,pack f3621,pack f3644,pack f3648,pack f3595,pack f3977,pack f2873,pack f1324,pack f1385,pack f3437,pack f590,pack f3161,pack f3585,pack f253,pack f384,pack f392,pack f2480,pack f1285,pack f1382,pack f1148,pack f1187,pack f1169,pack f455,pack f3978,pack f1360,pack f3975,pack f89,pack f3513,pack f20,pack f103,pack f993,pack f994,pack f996,pack f997,pack f2193,pack f3834,pack f3746,pack f1497,pack f1105,pack f1832,pack f2498,pack f3070,pack f2410,pack f3186,pack f399,pack f605,pack f3524] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3980 : H a 79591134237540 := rup [pack f1,pack f3920,pack f2757,pack f3899,pack f3559,pack f1613,pack f2343] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3981 : H a 0x81982089cc1c91ca1c := rup [pack f1,pack f3922,pack f276,pack f3444] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3982 : H a 19433788553 := rup [pack f1,pack f3920,pack f3953,pack f3922,pack f3979,pack f3600,pack f3607,pack f1883,pack f2757,pack f184,pack f3980,pack f554,pack f2982,pack f2966,pack f2965,pack f962,pack f2962,pack f3083,pack f3806,pack f3805,pack f2974,pack f2975,pack f3913,pack f3573,pack f2010,pack f2070,pack f268,pack f1453,pack f241,pack f1505,pack f2424,pack f2436,pack f2421,pack f2431,pack f2430,pack f2844,pack f2343,pack f991,pack f2015,pack f1955,pack f1403,pack f1497,pack f1165,pack f3413,pack f108,pack f102,pack f1628,pack f924,pack f256,pack f3981,pack f280,pack f2046,pack f1972,pack f3642] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3983 : H a 0x831c348b4934874 := rup [pack f1,pack f3922,pack f3972,pack f474,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3984 : H a 4744577 := rup [pack f1,pack f3920,pack f3953,pack f3922,pack f3972,pack f2757,pack f184,pack f3607,pack f1883,pack f3979,pack f3600,pack f3982,pack f381,pack f2981,pack f2659,pack f2553,pack f1168,pack f3913,pack f3899,pack f586,pack f3083,pack f3575,pack f150,pack f3559,pack f1612,pack f1621,pack f1620,pack f343,pack f351,pack f2341,pack f3736,pack f3735,pack f2591,pack f2669,pack f2712,pack f2636,pack f2844,pack f3102,pack f3100,pack f3099,pack f1066,pack f1111,pack f456,pack f923,pack f991,pack f1037,pack f1105,pack f26,pack f3398,pack f3983,pack f2574,pack f471,pack f3642,pack f2697] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3985 : H a 4744001 := rup [pack f1,pack f3920,pack f3953,pack f3922,pack f3984,pack f1246,pack f3606,pack f2757,pack f3600,pack f3626,pack f3622,pack f1872,pack f1921,pack f3643,pack f1960,pack f1902,pack f2563,pack f1861,pack f695,pack f656,pack f3555,pack f488,pack f1886,pack f3957,pack f215] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3986 : H a 79597578496583 := rup [pack f1,pack f3953,pack f3922,pack f3920,pack f3985,pack f3599,pack f3646,pack f3672,pack f3731,pack f3754,pack f3596,pack f3655,pack f3604,pack f3637,pack f3602,pack f3667,pack f1911,pack f3609,pack f3631,pack f1294,pack f3620,pack f3657,pack f3598,pack f3984,pack f2583,pack f1852,pack f1880,pack f3606,pack f722,pack f720,pack f169,pack f215,pack f1874,pack f1980,pack f2136,pack f2598,pack f3555,pack f1892,pack f1905,pack f1889,pack f1890,pack f1887,pack f2642,pack f206,pack f2713,pack f2828,pack f2688,pack f501,pack f3983,pack f3441,pack f1067,pack f2411,pack f365] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3987 : H a 19433002562 := rup [pack f1,pack f3920,pack f3868,pack f3953,pack f3985,pack f3596,pack f3657,pack f3691,pack f3599,pack f3646,pack f670,pack f3984,pack f1246,pack f3606,pack f182,pack f694,pack f3672,pack f3683,pack f3986,pack f3432,pack f3957,pack f422,pack f2395,pack f2394,pack f2385,pack f529,pack f2812,pack f2821,pack f1399,pack f1051,pack f1418,pack f1034,pack f1228,pack f141,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3988 : H a 19433003592 := rup [pack f1,pack f3920,pack f3868,pack f3953,pack f3987,pack f3628,pack f679,pack f3984,pack f3606,pack f3624,pack f654,pack f3985,pack f3596,pack f3657,pack f3598,pack f3605,pack f3649,pack f3655,pack f3707,pack f3599,pack f670,pack f1246,pack f182,pack f3432,pack f3957,pack f422,pack f2395,pack f2394,pack f2385,pack f529,pack f2812,pack f2821,pack f1433,pack f1051,pack f1418,pack f1056,pack f1262,pack f165,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3989 : H a 4744385 := rup [pack f1,pack f3953,pack f3922,pack f3920,pack f3985,pack f3599,pack f1880,pack f3984,pack f3606,pack f722,pack f720,pack f3596,pack f3646,pack f3655,pack f3657,pack f1852,pack f3602,pack f2583,pack f3609,pack f3598,pack f3987,pack f3605,pack f3624,pack f1873,pack f3628,pack f3638,pack f3669,pack f3649,pack f1346,pack f681,pack f683,pack f3988,pack f169,pack f215,pack f1922,pack f2026,pack f2214,pack f2680,pack f3555,pack f1906,pack f1889,pack f1898,pack f1888,pack f1899,pack f208,pack f2637,pack f2690,pack f2890,pack f2716,pack f521,pack f3983,pack f3412,pack f1112,pack f2499,pack f3587,pack f404] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3990 : H a 19438794305 := rup [pack f1,pack f3922,pack f3953,pack f3920,pack f3924,pack f3927,pack f3984,pack f3989,pack f3641,pack f3985,pack f3599,pack f1880,pack f1900,pack f3595,pack f3606,pack f215,pack f1923,pack f1876,pack f3555,pack f1857,pack f208,pack f187,pack f1854,pack f3869,pack f1859,pack f231,pack f1999,pack f3677,pack f3434,pack f169,pack f3679,pack f3591,pack f777,pack f3601,pack f742,pack f3603,pack f722,pack f3605,pack f3826,pack f3624,pack f3632,pack f3671,pack f3640,pack f3666,pack f3649,pack f2043,pack f1346,pack f710,pack f754,pack f2641,pack f1860,pack f1966,pack f1542,pack f2071,pack f2716,pack f957,pack f2025,pack f2782,pack f265,pack f521,pack f1488,pack f2953,pack f3412,pack f597,pack f645] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3991 : H a 0x3283643a432133472432c := rup [pack f1,pack f598,pack f605] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3992 : H a 4745799 := rup [pack f1,pack f3953,pack f3922,pack f3920,pack f3984,pack f3606,pack f3989,pack f3595,pack f3677,pack f3601,pack f741,pack f3679,pack f1900,pack f3985,pack f3599,pack f1880,pack f676,pack f722,pack f187,pack f169,pack f215,pack f1923,pack f1876,pack f3555,pack f231,pack f284,pack f1854,pack f1855,pack f1493,pack f3869,pack f3990,pack f3604,pack f1294,pack f3630,pack f3673,pack f3651,pack f3670,pack f1863,pack f1858,pack f3818,pack f3777,pack f2597,pack f1979,pack f3759,pack f1323,pack f2642,pack f2012,pack f1864,pack f2722,pack f501,pack f514,pack f3436,pack f2663,pack f2208,pack f3201,pack f3991] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3993 : H a 1158 := rup [pack f1,pack f3868,pack f3953,pack f3925,pack f3984,pack f3606,pack f3985,pack f3599,pack f1880,pack f3989,pack f3641,pack f3992,pack f3432,pack f3957,pack f2394,pack f487,pack f2812,pack f995,pack f2085,pack f2132,pack f2212,pack f306,pack f299] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3994 : H a 0x342b23702641c05aa4a41 := rup [pack f1,pack f3993,pack f3953,pack f3868,pack f3926,pack f3922,pack f3597,pack f763,pack f1853,pack f3216,pack f3844,pack f3599,pack f1880,pack f3607,pack f3679,pack f1873,pack f3633,pack f1531,pack f3664,pack f777,pack f1907,pack f635,pack f3555,pack f2703,pack f2698,pack f1919] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3995 : H a 0x34232133432832c724 := rup [pack f1,pack f3920,pack f3953,pack f3925,pack f3922,pack f3993,pack f1969,pack f1305,pack f3599,pack f676,pack f3991,pack f574,pack f578,pack f715,pack f3818,pack f602,pack f2061,pack f621,pack f763,pack f3844,pack f3216,pack f3688,pack f3660,pack f3629,pack f3630,pack f3073,pack f3831,pack f963,pack f3826,pack f3994,pack f3606,pack f3621,pack f3636,pack f3648,pack f3846,pack f2036,pack f2689,pack f3716,pack f1099,pack f1511,pack f622,pack f549,pack f3004,pack f2049,pack f277,pack f3981,pack f1470,pack f1714,pack f3930] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3996 : H a 0x3427233a39a4e021ac1b40bca8156417416805a := rup [pack f1,pack f3953,pack f3993,pack f3922,pack f3840,pack f3818,pack f3634,pack f1891,pack f3635,pack f3820,pack f3599,pack f1880,pack f676,pack f231,pack f3190,pack f1449,pack f3555,pack f2086,pack f575,pack f267,pack f1922,pack f545,pack f3811,pack f3189] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3997 : H a 0x3420603287233a3858641 := rup [pack f1,pack f3920,pack f3953,pack f3868,pack f3840,pack f3818,pack f3634,pack f3603,pack f1234,pack f3635,pack f3607,pack f1246,pack f3828,pack f755,pack f715,pack f3660,pack f3595,pack f578,pack f611,pack f3599,pack f676,pack f3605,pack f3826,pack f3628,pack f3674,pack f3624,pack f2134,pack f2596,pack f1873,pack f3669,pack f3649,pack f3638,pack f685,pack f777,pack f657,pack f1231,pack f1269,pack f3415,pack f2227,pack f3071,pack f3187,pack f1422,pack f2565,pack f1183,pack f2556,pack f1408,pack f3996,pack f3074,pack f3841,pack f3191,pack f1457,pack f3077,pack f1532,pack f2695,pack f2100,pack f1003,pack f115,pack f627,pack f556] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3998 : H a 0x7233a3642d241b4934610059 := rup [pack f1,pack f3920,pack f3953,pack f3925,pack f715,pack f3604,pack f3637,pack f1366,pack f3840,pack f3818,pack f3634,pack f3603,pack f3672,pack f3790,pack f694,pack f3716,pack f3635,pack f3820,pack f755,pack f3660,pack f763,pack f574,pack f1846,pack f1450,pack f3074,pack f3841,pack f1521,pack f3077,pack f1513,pack f213,pack f2127,pack f3440,pack f575,pack f3005,pack f620] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f3999 : H a 0x3423213343287233a3 := rup [pack f1,pack f3993,pack f3920,pack f3953,pack f3922,pack f3840,pack f755,pack f626,pack f611,pack f3599,pack f900,pack f1880,pack f676,pack f574,pack f715,pack f3818,pack f1283,pack f3635,pack f3634,pack f3607,pack f3820,pack f3603,pack f1891,pack f1246,pack f1234,pack f3997,pack f3604,pack f3620,pack f3672,pack f3653,pack f1911,pack f1267,pack f3846,pack f2679,pack f2213,pack f3790,pack f1233,pack f3415,pack f3071,pack f2591,pack f1171,pack f2557,pack f1409,pack f456,pack f449,pack f1125,pack f3998,pack f231,pack f3073,pack f1504,pack f3555,pack f2087,pack f612,pack f239,pack f1867,pack f548,pack f3811,pack f3072] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4000 : H a 0xc81b231c1885642 := rup [pack f1,pack f3993,pack f3953,pack f3922,pack f3868,pack f3926,pack f3850,pack f3592,pack f763,pack f1853,pack f3216,pack f3844,pack f1880,pack f3604,pack f3627,pack f3639,pack f1911,pack f1904,pack f3831,pack f1531,pack f3555,pack f635,pack f1865,pack f2703,pack f2698] (by dsimp only [pack,List.map]; decide +kernel)
end BorsukCert
namespace BorsukCert
variable {a : ℕ → Bool} [Legal a]
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4001 : H a 0x34232133432832c := rup [pack f1,pack f3920,pack f3953,pack f3925,pack f3922,pack f3993,pack f1969,pack f1305,pack f3599,pack f676,pack f3995,pack f611,pack f626,pack f755,pack f3840,pack f2004,pack f3999,pack f603,pack f621,pack f763,pack f3844,pack f3216,pack f3688,pack f3612,pack f3613,pack f3190,pack f968,pack f3594,pack f3846,pack f4000,pack f3605,pack f3826,pack f3671,pack f2036,pack f2689,pack f3666,pack f731,pack f1511,pack f622,pack f1099,pack f549,pack f3004,pack f2049,pack f281,pack f3444,pack f1470,pack f1714,pack f3930] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4002 : H a 3416875 := rup [pack f1,pack f3953,pack f3922,pack f3993,pack f3599,pack f1880,pack f305,pack f313,pack f2192,pack f2196,pack f2205,pack f2206,pack f2873,pack f3725,pack f2201,pack f2202,pack f504,pack f2195,pack f665,pack f3595,pack f2193,pack f3437,pack f2198,pack f2197,pack f1853,pack f3161,pack f1869,pack f1914,pack f3884,pack f3555,pack f259,pack f1889,pack f1891,pack f1893,pack f3085,pack f2162,pack f3127,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4003 : H a 53707177096 := rup [pack f1,pack f106,pack f112,pack f3747,pack f3785,pack f3437,pack f3585] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4004 : H a 0x25c31c22014616223ca1b := rup [pack f1,pack f2052,pack f2053,pack f2045,pack f2047,pack f3618,pack f2038,pack f1982,pack f264] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4005 : H a 53707150119 := rup [pack f1,pack f3953,pack f3993,pack f3922,pack f1969,pack f106,pack f112,pack f196,pack f1493,pack f1958,pack f3785,pack f3747,pack f2065,pack f2007,pack f4003,pack f3583,pack f590,pack f3161,pack f3172,pack f3173,pack f2030,pack f2019,pack f1797,pack f1783,pack f27,pack f28,pack f68,pack f3159,pack f1786,pack f1812,pack f311,pack f4004,pack f3444,pack f1495,pack f1462,pack f1525,pack f3644,pack f1531,pack f1414,pack f113] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4006 : H a 3416883 := rup [pack f1,pack f3953,pack f3922,pack f3993,pack f3599,pack f1880,pack f455,pack f460,pack f2643,pack f2649,pack f2660,pack f2661,pack f2480,pack f3726,pack f2654,pack f2656,pack f379,pack f2648,pack f665,pack f3595,pack f2646,pack f3973,pack f2651,pack f2650,pack f1853,pack f3161,pack f1869,pack f1914,pack f3884,pack f3555,pack f259,pack f1889,pack f1891,pack f1893,pack f3085,pack f2614,pack f3126,pack f591] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4007 : H a 57365878160523 := rup [pack f1,pack f3920,pack f3953,pack f3993,pack f3161,pack f4006,pack f4002,pack f3599,pack f4003,pack f4001,pack f3869,pack f3163,pack f3177,pack f3159,pack f3173,pack f3156,pack f3172,pack f3152,pack f3884,pack f1305,pack f2480,pack f2493,pack f2472,pack f2497,pack f2482,pack f2477,pack f1772,pack f3178,pack f1595,pack f1726,pack f3870,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4008 : H a 14005341347 := rup [pack f1,pack f3920,pack f3953,pack f3993,pack f4006,pack f4002,pack f3599,pack f4003,pack f4001,pack f3869,pack f1305,pack f3161,pack f3163,pack f3172,pack f3173,pack f3884,pack f3177,pack f3152,pack f3156,pack f3159,pack f4007,pack f3585,pack f2873,pack f2884,pack f2889,pack f2883,pack f2874,pack f2870,pack f2869,pack f1772,pack f1592,pack f1719,pack f3870,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4009 : H a 3419272 := rup [pack f1,pack f3953,pack f3920,pack f3993,pack f4006,pack f4002,pack f1305,pack f3599,pack f4003,pack f4001,pack f3869,pack f4008,pack f3437,pack f3973,pack f2873,pack f2883,pack f2874,pack f2869,pack f2480,pack f2476,pack f1759,pack f1597,pack f1709,pack f1479,pack f3870,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4010 : H a 13995486347 := rup [pack f1,pack f3953,pack f3993,pack f3923,pack f3868,pack f3926,pack f4009,pack f1818,pack f1793,pack f439,pack f1782,pack f3722,pack f1783,pack f249,pack f2577,pack f1819,pack f604,pack f384,pack f2480,pack f2472,pack f2492,pack f2496,pack f2490,pack f2474,pack f1439,pack f1806,pack f3146,pack f3280,pack f3747,pack f3068,pack f2960,pack f2368,pack f1647,pack f1810,pack f61,pack f567,pack f1536,pack f630,pack f3414,pack f3566,pack f2791,pack f2729,pack f3371] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4011 : H a 14005453602 := rup [pack f1,pack f3953,pack f3920,pack f3993,pack f3923,pack f3868,pack f4009,pack f1782,pack f1818,pack f1819,pack f3722,pack f2577,pack f1787,pack f4010,pack f3583,pack f508,pack f2873,pack f2867,pack f2888,pack f2881,pack f1440,pack f1800,pack f2859,pack f1759,pack f3131,pack f3068,pack f2960,pack f2796,pack f1645,pack f567,pack f3491,pack f3565,pack f3499,pack f3602] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4012 : H a 3416865 := rup [pack f1,pack f4006,pack f4002,pack f3599,pack f4005,pack f4001] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4013 : H a 3416617 := rup [pack f1,pack f3953,pack f3927,pack f3924,pack f4012,pack f4009,pack f1818,pack f4011,pack f1819,pack f3184,pack f2011,pack f2072,pack f1787,pack f286,pack f3150,pack f8,pack f1782,pack f3722,pack f1783,pack f249,pack f1793,pack f3153,pack f4010,pack f223,pack f191,pack f672,pack f3725,pack f1803,pack f1810,pack f1790,pack f2784,pack f2723,pack f1800,pack f1788,pack f1809,pack f3154,pack f2467,pack f2541,pack f3157,pack f2445,pack f2535,pack f2335,pack f2400,pack f386,pack f429,pack f428,pack f385,pack f2917,pack f1562,pack f2986,pack f1632,pack f3556,pack f3563,pack f346,pack f340] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4014 : H a 834 := rup [pack f1,pack f3953,pack f3927,pack f3924,pack f3868,pack f676,pack f4009,pack f4012,pack f1782,pack f1818,pack f1819,pack f4010,pack f4011,pack f3722,pack f3838,pack f3153,pack f1793,pack f1787,pack f3184,pack f1783,pack f3158,pack f1785,pack f441,pack f288,pack f2072,pack f2011,pack f4013,pack f1802,pack f1789,pack f1811,pack f3155,pack f3181,pack f2543,pack f2468,pack f3169,pack f2444,pack f2529,pack f2402,pack f2336,pack f386,pack f429,pack f428,pack f385,pack f2929,pack f3012,pack f552,pack f551] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4015 : H a 3201 := rup [pack f1,pack f4014,pack f3600] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4016 : H a 3235 := rup [pack f1,pack f4014,pack f3833] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4017 : H a 3219 := rup [pack f1,pack f4014,pack f3784] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4018 : H a 3211 := rup [pack f1,pack f4014,pack f3745] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4019 : H a 3207 := rup [pack f1,pack f4014,pack f3721] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4020 : H a 0x4c84a8490588688 := rup [pack f1,pack f3993,pack f4019,pack f179,pack f3870] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4021 : H a 14566081364 := rup [pack f1,pack f4014,pack f3899,pack f3559] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4022 : H a 58562165642084 := rup [pack f1,pack f4014,pack f3993,pack f3923,pack f3868,pack f3920,pack f4017,pack f3899,pack f4021,pack f150,pack f197,pack f1611,pack f393,pack f2342,pack f2344,pack f2351,pack f2612,pack f3068,pack f2960,pack f1440,pack f2577,pack f1606,pack f2339,pack f567,pack f562,pack f243,pack f56,pack f2861,pack f2843,pack f505,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4023 : H a 23250942890313 := rup [pack f1,pack f3920,pack f4014,pack f4019,pack f3993,pack f1752,pack f481,pack f4022,pack f546,pack f600,pack f2967,pack f1318,pack f1096,pack f3484,pack f3870,pack f3884,pack f1472,pack f1475,pack f1594] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4024 : H a 5676499729 := rup [pack f1,pack f4014,pack f3953,pack f3993,pack f3923,pack f3920,pack f4017,pack f1752,pack f481,pack f4023,pack f343,pack f345,pack f4021,pack f3413,pack f554,pack f600,pack f2967,pack f197,pack f1611,pack f1608,pack f1621,pack f1628,pack f1994,pack f1969,pack f2406,pack f2337,pack f2962,pack f1064,pack f2393,pack f1615,pack f2964,pack f382,pack f3114,pack f354,pack f447,pack f56,pack f3580,pack f2841,pack f505,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4025 : H a 5676499788 := rup [pack f1,pack f4014,pack f3920,pack f4019,pack f3993,pack f4024,pack f1583,pack f1752,pack f481,pack f4021,pack f3413,pack f2967,pack f1611,pack f1608,pack f1621,pack f1628,pack f2964,pack f376,pack f56,pack f3870] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4026 : H a 0x6885884c8149363 := rup [pack f1,pack f4019,pack f3993,pack f4014,pack f546,pack f554,pack f600,pack f1318,pack f3870,pack f1097,pack f1086,pack f1100,pack f1082] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4027 : H a 1385864 := rup [pack f1,pack f4014,pack f3920,pack f3993,pack f4019,pack f1752,pack f481,pack f4024,pack f1583,pack f4025,pack f343,pack f2344,pack f4026,pack f3899,pack f1611,pack f1626,pack f2352,pack f2340,pack f580,pack f80,pack f3484,pack f178] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4028 : H a 5672047460 := rup [pack f1,pack f4014,pack f3993,pack f3920,pack f4017,pack f4027,pack f1752,pack f481,pack f3899,pack f4021,pack f4022,pack f150,pack f197,pack f1611,pack f393,pack f2344,pack f1583,pack f2612,pack f2352,pack f2342,pack f1737,pack f584,pack f588,pack f2449,pack f2313,pack f1308,pack f1992,pack f3558,pack f3580,pack f507,pack f502] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4029 : H a 1384777 := rup [pack f1,pack f3993,pack f3920,pack f4014,pack f3972,pack f4027,pack f1709,pack f481,pack f2699,pack f4028,pack f554,pack f2967,pack f1739,pack f1722,pack f351,pack f1710,pack f1712,pack f3413,pack f3696,pack f3695,pack f443,pack f466,pack f448,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4030 : H a 338 := rup [pack f1,pack f3920,pack f4014,pack f3972,pack f481,pack f4027,pack f172,pack f202,pack f1709,pack f4029,pack f343,pack f4021,pack f3413,pack f554,pack f150,pack f197,pack f1739,pack f2700,pack f2709,pack f2580,pack f2634,pack f1710,pack f3947] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4031 : H a 0xc10c1cd0cc09e0c := rup [pack f1,pack f3927,pack f4018,pack f428,pack f433] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4032 : H a 14559527751 := rup [pack f1,pack f3993,pack f3953,pack f4014,pack f3920,pack f4030,pack f554,pack f2070,pack f546,pack f1138,pack f2967,pack f150,pack f1621,pack f2543,pack f4031] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4033 : H a 22691978968073 := rup [pack f1,pack f4030,pack f4015,pack f3920,pack f3953,pack f4014,pack f3972,pack f3993,pack f343,pack f554,pack f1709,pack f2535,pack f4032,pack f3413,pack f718,pack f2967,pack f1722,pack f1146,pack f1739,pack f1165,pack f2070,pack f546,pack f1138,pack f1175,pack f1156,pack f2752,pack f2964,pack f4031,pack f3554,pack f2911,pack f3262,pack f77,pack f3589,pack f2973,pack f226] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4034 : H a 5540033927 := rup [pack f1,pack f3993,pack f3953,pack f4014,pack f3920,pack f2967,pack f554,pack f343,pack f1709,pack f1721,pack f1722,pack f2436,pack f2535,pack f4032,pack f3413,pack f4033,pack f2768,pack f2842,pack f3079,pack f3572] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4035 : H a 5540035594 := rup [pack f1,pack f3920,pack f4015,pack f4014,pack f4030,pack f3993,pack f4019,pack f4034,pack f546,pack f1089,pack f2967,pack f343,pack f2963,pack f1621,pack f2979,pack f2984,pack f2985,pack f2978,pack f2972,pack f3803,pack f2971,pack f3413,pack f2754,pack f1985,pack f2143,pack f1074,pack f3115,pack f2851,pack f190,pack f80,pack f3141,pack f2748,pack f122,pack f2862,pack f2311,pack f2417,pack f3484,pack f3582,pack f373,pack f3578] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4036 : H a 5540033363 := rup [pack f1,pack f4014,pack f3953,pack f3993,pack f4019,pack f4030,pack f3922,pack f4035,pack f2964,pack f3262,pack f56,pack f4034,pack f554,pack f2070,pack f546,pack f1138,pack f1089,pack f485,pack f2752,pack f2535,pack f100,pack f2911,pack f4031,pack f3484,pack f3589,pack f773,pack f3752,pack f2539,pack f2543,pack f2538,pack f3716,pack f219,pack f1878,pack f1851,pack f3617,pack f1897,pack f1918,pack f1868,pack f3555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4037 : H a 1352547 := rup [pack f1,pack f4014,pack f3920,pack f3993,pack f3925,pack f3953,pack f3868,pack f345,pack f343,pack f554,pack f2967,pack f2031,pack f4036,pack f3413,pack f1611,pack f1608,pack f4032,pack f2393,pack f1120,pack f2516,pack f3750,pack f412,pack f2535,pack f3743,pack f487,pack f3623,pack f3568,pack f3957] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4038 : H a 5550159898 := rup [pack f1,pack f4015,pack f3953,pack f3993,pack f4014,pack f3925,pack f3972,pack f3920,pack f343,pack f4037,pack f4021,pack f485,pack f2535,pack f2521,pack f3751,pack f45,pack f435,pack f2525,pack f2524,pack f2533,pack f1337,pack f2534,pack f1236,pack f923,pack f3750,pack f1346,pack f1156,pack f3561,pack f1611,pack f1175,pack f345,pack f278,pack f1608,pack f1620,pack f2516,pack f1119,pack f1358,pack f1196,pack f412,pack f3554,pack f3743,pack f60,pack f1294] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4039 : H a 1355019 := rup [pack f1,pack f3920,pack f4015,pack f3993,pack f3953,pack f3925,pack f343,pack f4037,pack f4021,pack f3561,pack f1611,pack f485,pack f435,pack f766,pack f3750,pack f2535,pack f2524,pack f4038,pack f1609,pack f3693,pack f3694,pack f1622,pack f2749,pack f2779,pack f2772,pack f1836,pack f1516,pack f1743,pack f390,pack f3762,pack f2681,pack f3235,pack f3010,pack f2902,pack f2847,pack f3412,pack f3576,pack f623] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4040 : H a 5544974474 := rup [pack f1,pack f3993,pack f4015,pack f3920,pack f3926,pack f343,pack f4037,pack f4021,pack f3561,pack f150,pack f3121,pack f1609,pack f2779,pack f2756,pack f2852,pack f1613,pack f1753,pack f3579,pack f3577,pack f3647,pack f3739,pack f1611,pack f3645,pack f1133,pack f2056,pack f3749,pack f2749,pack f3762,pack f35,pack f3694,pack f269,pack f4039,pack f391,pack f2770,pack f427,pack f4031] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4041 : H a 1353753 := rup [pack f1,pack f4015,pack f4030,pack f3993,pack f3920,pack f3926,pack f4014,pack f343,pack f4037,pack f4021,pack f3561,pack f1611,pack f150,pack f1609,pack f3694,pack f3121,pack f2779,pack f266,pack f1607,pack f2756,pack f1613,pack f2852,pack f1753,pack f3579,pack f3577,pack f3602,pack f3645,pack f3647,pack f3619,pack f3616,pack f1891,pack f2233,pack f2149,pack f2204,pack f2094,pack f3601,pack f1366,pack f3430,pack f1386,pack f4040,pack f2754,pack f1196,pack f1614,pack f1271,pack f1352,pack f2862,pack f81,pack f3504,pack f1779,pack f3435,pack f3141] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4042 : H a 0x6a44a14ac4a84b44e4 := rup [pack f1,pack f4016,pack f579,pack f587] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4043 : H a 330 := rup [pack f1,pack f4014,pack f3953,pack f3920,pack f3993,pack f3925,pack f343,pack f345,pack f4037,pack f4021,pack f485,pack f3561,pack f2165,pack f1611,pack f4039,pack f4041,pack f278,pack f1608,pack f1621,pack f2750,pack f2516,pack f1119,pack f2752,pack f1615,pack f410,pack f100,pack f447,pack f405,pack f3134,pack f2946,pack f4042] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4044 : H a 2611 := rup [pack f1,pack f4043,pack f3993,pack f2699] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4045 : H a 1191 := rup [pack f1,pack f4043,pack f4030,pack f4014,pack f1476] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4046 : H a 3111 := rup [pack f1,pack f4043,pack f4030,pack f4014,pack f1555] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4047 : H a 2215 := rup [pack f1,pack f4043,pack f4014,pack f4030,pack f1491] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4048 : H a 28527178923 := rup [pack f1,pack f3953,pack f4014,pack f4030,pack f3920,pack f3083,pack f3820,pack f2159,pack f2164,pack f2169,pack f2170,pack f2854,pack f3602,pack f3105,pack f3491,pack f1760] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4049 : H a 5911779 := rup [pack f1,pack f3953,pack f4043,pack f4030,pack f4014,pack f3993,pack f4019,pack f4045,pack f3920,pack f3972,pack f3083,pack f3820,pack f724,pack f665,pack f3795,pack f3642,pack f3676,pack f3678,pack f731,pack f3602,pack f1191,pack f1151,pack f1319,pack f1090,pack f3484,pack f1721,pack f1722,pack f1177,pack f1170,pack f1146,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4050 : H a 19887965603 := rup [pack f1,pack f4045,pack f3953,pack f4014,pack f4043,pack f3920,pack f3820,pack f3083,pack f4048,pack f4049,pack f4042,pack f2607,pack f2617,pack f2608,pack f2616,pack f2626,pack f3080,pack f2860,pack f1762,pack f3602,pack f2621,pack f2456,pack f3577] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4051 : H a 6964403 := rup [pack f1,pack f3953,pack f4043,pack f4014,pack f3923,pack f3868,pack f4044,pack f3972,pack f3920,pack f2607,pack f2608,pack f2620,pack f2604,pack f2616,pack f2626,pack f2629,pack f2605,pack f2860,pack f3606,pack f2611,pack f692,pack f3602,pack f2610,pack f3656,pack f3658,pack f2576,pack f3799,pack f3816,pack f2718,pack f2640,pack f1447,pack f3491,pack f562,pack f3947,pack f1769] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4052 : H a 19887965356 := rup [pack f1,pack f4016,pack f4045,pack f4051,pack f4050,pack f585,pack f4042] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4053 : H a 4855460 := rup [pack f1,pack f4045,pack f4016,pack f3953,pack f4030,pack f4014,pack f4050,pack f4051,pack f4052,pack f2164,pack f2154,pack f582,pack f2174,pack f3795] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4054 : H a 1185 := rup [pack f1,pack f4043,pack f4015,pack f3920,pack f3993,pack f4030,pack f4014,pack f3953,pack f4045,pack f4016,pack f4046,pack f3921,pack f4047,pack f3972,pack f4053,pack f3828,pack f3136,pack f3115,pack f150,pack f3120,pack f2967,pack f3083,pack f3829,pack f3830,pack f3899,pack f1492,pack f1412,pack f485,pack f3561,pack f2776,pack f2767,pack f2768,pack f2165,pack f351,pack f2352,pack f381,pack f2755,pack f1179,pack f1524,pack f1461,pack f2617,pack f506,pack f1001,pack f589,pack f3572,pack f3571,pack f117,pack f3797,pack f1437,pack f3522] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4055 : H a 1699 := rup [pack f1,pack f4054,pack f588] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4056 : H a 0x2582c8648250a48268 := rup [pack f1,pack f3953,pack f157,pack f152] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4057 : H a 0x942b02912687 := rup [pack f1,pack f4015,pack f4043,pack f3920,pack f4054,pack f3602,pack f3595,pack f3642,pack f1052,pack f1246,pack f3665,pack f3700,pack f3668,pack f3685,pack f1754,pack f1769,pack f1775,pack f1750,pack f1420,pack f1665,pack f4056] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4058 : H a 39773546770 := rup [pack f1,pack f3993,pack f4019,pack f4045,pack f4055,pack f4043,pack f3920,pack f4014,pack f3602,pack f3595,pack f3642,pack f3606,pack f718,pack f1098,pack f4057,pack f3491,pack f3484,pack f4020,pack f3580,pack f2853,pack f2861,pack f1321,pack f1308,pack f1312,pack f1585,pack f2458,pack f2447] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4059 : H a 9710338 := rup [pack f1,pack f3993,pack f3920,pack f4015,pack f4054,pack f4043,pack f4030,pack f3922,pack f3602,pack f3595,pack f3668,pack f3665,pack f3642,pack f2037,pack f3685,pack f3700,pack f1246,pack f1052,pack f4058,pack f1421,pack f1002,pack f981,pack f4056,pack f160,pack f1683,pack f1682,pack f1665,pack f3704,pack f1608,pack f3694,pack f1535,pack f1406,pack f1502,pack f1446,pack f1528,pack f1463,pack f244,pack f1423,pack f269,pack f1398,pack f110,pack f109,pack f97,pack f95,pack f1967,pack f2044,pack f3444] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4060 : H a 0x942911d01250268258 := rup [pack f1,pack f4030,pack f3953,pack f3972,pack f4044,pack f4015,pack f3993,pack f4043,pack f4014,pack f3920,pack f4054,pack f3921,pack f4059,pack f3656,pack f3596,pack f3594,pack f3610,pack f2714,pack f3602,pack f3643,pack f2584,pack f3607,pack f3623,pack f2639,pack f3947,pack f1057,pack f1112,pack f1014,pack f1035,pack f988,pack f3685,pack f981,pack f3703,pack f3608,pack f932,pack f1109,pack f4056,pack f158,pack f1652,pack f1653,pack f1660,pack f1662,pack f1611,pack f1627,pack f1625,pack f1610,pack f1005,pack f1065,pack f902,pack f406,pack f1070,pack f3553,pack f9,pack f21] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4061 : H a 0x581d01e24c34257 := rup [pack f1,pack f4054,pack f4046,pack f4016,pack f3927,pack f49,pack f69,pack f1244,pack f1252,pack f1255,pack f3848,pack f1248,pack f642,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4062 : H a 27943572071 := rup [pack f1,pack f4015,pack f4030,pack f4055,pack f98,pack f1412,pack f2448,pack f1766,pack f3580,pack f3577] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4063 : H a 39771512065 := rup [pack f1,pack f4015,pack f4014,pack f4043,pack f4054,pack f4046,pack f4016,pack f3927,pack f3602,pack f4062,pack f4059,pack f3656,pack f3608,pack f3596,pack f3643,pack f3594,pack f3681,pack f3610,pack f777,pack f2714,pack f4061,pack f4060,pack f10,pack f30,pack f1054,pack f1047,pack f3847,pack f642,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4064 : H a 0xe08e01e24e0c := rup [pack f1,pack f3588,pack f3590] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4065 : H a 0xd02aa4a2824f := rup [pack f1,pack f4015,pack f4054,pack f4043,pack f3868,pack f3926,pack f4044,pack f3682,pack f10,pack f1043,pack f1044,pack f1050,pack f3204,pack f1847,pack f3753,pack f637,pack f4064] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4066 : H a 0xa48268d02648832250c22 := rup [pack f1,pack f4015,pack f3920,pack f1261,pack f1577,pack f4056] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4067 : H a 0xd24c34c21e24 := rup [pack f1,pack f4046,pack f4016,pack f3927,pack f642,pack f638] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4068 : H a 9709841 := rup [pack f1,pack f4015,pack f3993,pack f3953,pack f4014,pack f4044,pack f3972,pack f4043,pack f4030,pack f3920,pack f4055,pack f3602,pack f4059,pack f3596,pack f3643,pack f2584,pack f3703,pack f3658,pack f4062,pack f4063,pack f769,pack f3593,pack f3662,pack f3666,pack f2715,pack f3831,pack f2638,pack f1539,pack f3700,pack f3947,pack f4065,pack f4066,pack f4067,pack f3288,pack f2854,pack f2450,pack f3491,pack f3578] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4069 : H a 27942658374 := rup [pack f1,pack f3920,pack f4055,pack f2854,pack f2450,pack f3491,pack f3578] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4070 : H a 9710850 := rup [pack f1,pack f3993,pack f4015,pack f3953,pack f4014,pack f4043,pack f4030,pack f3868,pack f4044,pack f3926,pack f3920,pack f4068,pack f524,pack f3602,pack f4059,pack f3596,pack f3643,pack f2584,pack f3658,pack f687,pack f769,pack f3593,pack f3682,pack f3662,pack f2715,pack f3683,pack f3831,pack f2638,pack f1539,pack f3983,pack f4069,pack f3288,pack f635,pack f3414,pack f4067,pack f1643,pack f1040,pack f1240,pack f1627,pack f147,pack f3523] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4071 : H a 2370 := rup [pack f1,pack f3993,pack f3953,pack f3972,pack f4030,pack f4043,pack f4014,pack f3868,pack f4016,pack f4047,pack f3924,pack f4044,pack f3926,pack f4017,pack f3920,pack f4015,pack f687,pack f3602,pack f4059,pack f3596,pack f3656,pack f3643,pack f3608,pack f3607,pack f2584,pack f4068,pack f525,pack f4070,pack f3594,pack f3670,pack f3681,pack f3623,pack f3610,pack f728,pack f775,pack f777,pack f2639,pack f1538,pack f2714,pack f1392,pack f3947,pack f4069,pack f3147,pack f2068,pack f595,pack f635,pack f532,pack f592,pack f3414,pack f531,pack f1239,pack f1626,pack f1039,pack f1571,pack f1410,pack f3523] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4072 : H a 1665 := rup [pack f1,pack f4071,pack f3603] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4073 : H a 1671 := rup [pack f1,pack f4071,pack f3716] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4074 : H a 1175 := rup [pack f1,pack f4071,pack f4043,pack f4014,pack f1319] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4075 : H a 1167 := rup [pack f1,pack f4071,pack f4014,pack f4030,pack f1090] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4076 : H a 1079 := rup [pack f1,pack f4071,pack f4043,pack f4014,pack f1201] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4077 : H a 183 := rup [pack f1,pack f4071,pack f4043,pack f4014,pack f1158] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4078 : H a 1218 := rup [pack f1,pack f4072,pack f4015,pack f3645] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4079 : H a 1416 := rup [pack f1,pack f4074,pack f4075,pack f4045,pack f4073,pack f4019,pack f3993,pack f3484] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4080 : H a 2851 := rup [pack f1,pack f4078,pack f3844] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4081 : H a 594 := rup [pack f1,pack f4079,pack f3920,pack f1709] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4082 : H a 1224 := rup [pack f1,pack f4079,pack f4073,pack f4075,pack f4019,pack f4045,pack f4074,pack f185] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4083 : H a 198 := rup [pack f1,pack f4082,pack f142] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4084 : H a 1094 := rup [pack f1,pack f4082,pack f162] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4085 : H a 2355 := rup [pack f1,pack f4084,pack f3953,pack f4083,pack f2683] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4086 : H a 2098 := rup [pack f1,pack f3920,pack f4082,pack f4079,pack f4081,pack f3953,pack f4072,pack f4085,pack f3925,pack f4080,pack f1599,pack f1710,pack f1598,pack f1704,pack f3111,pack f3254,pack f1511,pack f619,pack f615] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4087 : H a 561 := rup [pack f1,pack f4086,pack f4079,pack f3714] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4088 : H a 113 := rup [pack f1,pack f4086,pack f4079,pack f3713] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4089 : H a 585 := rup [pack f1,pack f4086,pack f4079,pack f1711] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4090 : H a 567 := rup [pack f1,pack f4087,pack f457] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4091 : H a 119 := rup [pack f1,pack f4088,pack f437] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4092 : H a 311 := rup [pack f1,pack f4089,pack f4015,pack f1165] (by dsimp only [pack,List.map]; decide +kernel)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 8000000 in
lemma f4093 : H a 0 := rup [pack f1,pack f4091,pack f4090,pack f4076,pack f4092,pack f3972,pack f4077,pack f3554] (by dsimp only [pack,List.map]; decide +kernel)
end BorsukCert
namespace OAI.BorsukNine.FiniteObstruction
open BorsukCert
theorem no_fixed_ten_system {T Q : Family} (h : TenSystem T Q) (h0 : Q fixed) : False := by
  letI := system_legal h h0
  have hh := f4093 (a := coloring T Q)
  exact valid_nil hh
theorem no_ten_system {T Q : Family} (h : TenSystem T Q) (hQ : ∃ S, Q S) : False := by
  obtain ⟨S,hS⟩ := hQ
  obtain ⟨e,he⟩ := Equiv.Perm.exists_map_finset_eq fixed S (by rw [h.tetra_card S hS]; decide)
  exact no_fixed_ten_system (h.relabel e) (by simpa only [he] using hS)
end OAI.BorsukNine.FiniteObstruction
theorem OMA.L3 : OMA.R11.H3 := by
  rintro T Q ⟨hc,hd,hp,hb,hm,hn⟩
  exact OAI.BorsukNine.FiniteObstruction.no_ten_system ⟨hc,hd,hp,hb,hm,hn⟩
end W3

theorem OMA.solution : type_of% @Borsuk.borsuk_conjecture.not_of_nine_le :=
  OMA.R1.main (OMA.R11.main W1.OMA.L1 W2.OMA.L2 W3.OMA.L3) W4.OMA.L4
