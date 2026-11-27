import FormalConjectures.Wikipedia.Kaplansky
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Finsupp.Encodable

-- Problem: Kaplansky's Conjectures — char zero
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Kaplansky.lean:185 (declaration Kaplansky.direct_finiteness_conjecture.variants.char_zero)
-- Credit: @Jakeybakeypants (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! # Kaplansky's Direct Finiteness Theorem in Characteristic Zero -/

namespace OMA.KaplanskyCharZero

open scoped InnerProductSpace

/- Part 1: Direct finiteness of `MonoidAlgebra ℂ G` via `ℓ²(G)` -/

noncomputable abbrev L2 (G : Type*) := lp (fun _ : G => ℂ) 2

noncomputable def delta {G : Type*} [DecidableEq G] (g : G) : L2 G :=
  lp.single 2 g (1 : ℂ)

lemma memℓp_comp_equiv {G : Type*} (u : L2 G) (σ : G ≃ G) :
    Memℓp (fun h => u (σ h)) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  exact (Equiv.summable_iff σ).mpr ((memℓp_gen_iff hp).mp u.2)

noncomputable def reindex {G : Type*} (σ : G ≃ G) : L2 G ≃ₗᵢ[ℂ] L2 G where
  toFun u := ⟨fun h => u (σ h), memℓp_comp_equiv u σ⟩
  invFun u := ⟨fun h => u (σ.symm h), memℓp_comp_equiv u σ.symm⟩
  left_inv u := by ext h; simp
  right_inv u := by ext h; simp
  map_add' u v := by ext h; rfl
  map_smul' c u := by ext h; rfl
  norm_map' u := by
    have hp : 0 < (2 : ENNReal).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    exact Equiv.tsum_eq σ (fun h => ‖u h‖ ^ (2 : ENNReal).toReal)

lemma reindex_apply {G : Type*} (σ : G ≃ G) (u : L2 G) (h : G) :
    reindex σ u h = u (σ h) := rfl

lemma inner_reindex_right {G : Type*} (σ : G ≃ G) (u v : L2 G) :
    ⟪u, reindex σ v⟫_ℂ = ⟪reindex σ.symm u, v⟫_ℂ := by
  calc ⟪u, reindex σ v⟫_ℂ
      = ⟪reindex σ (reindex σ.symm u), reindex σ v⟫_ℂ := by
          congr 1
          ext h
          simp [reindex_apply]
    _ = ⟪reindex σ.symm u, v⟫_ℂ := (reindex σ).inner_map_map _ _

noncomputable def leftTrans {G : Type*} [Group G] (g : G) : L2 G ≃ₗᵢ[ℂ] L2 G :=
  reindex (Equiv.mulLeft g⁻¹)

noncomputable def rightTrans {G : Type*} [Group G] (g : G) : L2 G ≃ₗᵢ[ℂ] L2 G :=
  reindex (Equiv.mulRight g⁻¹)

lemma leftTrans_apply {G : Type*} [Group G] (g : G) (u : L2 G) (h : G) :
    leftTrans g u h = u (g⁻¹ * h) := rfl

lemma rightTrans_apply {G : Type*} [Group G] (g : G) (u : L2 G) (h : G) :
    rightTrans g u h = u (h * g⁻¹) := rfl

lemma leftTrans_one {G : Type*} [Group G] (u : L2 G) :
    leftTrans (1 : G) u = u := by
  ext h
  simp [leftTrans_apply]

lemma leftTrans_mul {G : Type*} [Group G] (g k : G) (u : L2 G) :
    leftTrans (g * k) u = leftTrans g (leftTrans k u) := by
  ext h
  simp [leftTrans_apply, mul_assoc]

lemma leftTrans_rightTrans_comm {G : Type*} [Group G] (g k : G) (u : L2 G) :
    leftTrans g (rightTrans k u) = rightTrans k (leftTrans g u) := by
  ext h
  simp [leftTrans_apply, rightTrans_apply, mul_assoc]

lemma inner_leftTrans_right {G : Type*} [Group G] (g : G) (u v : L2 G) :
    ⟪u, leftTrans g v⟫_ℂ = ⟪leftTrans g⁻¹ u, v⟫_ℂ := by
  simpa [leftTrans, Equiv.mulLeft_symm] using inner_reindex_right (Equiv.mulLeft g⁻¹) u v

lemma inner_rightTrans_right {G : Type*} [Group G] (g : G) (u v : L2 G) :
    ⟪u, rightTrans g v⟫_ℂ = ⟪rightTrans g⁻¹ u, v⟫_ℂ := by
  simpa [rightTrans, Equiv.mulRight_symm] using inner_reindex_right (Equiv.mulRight g⁻¹) u v

lemma leftTrans_delta_one {G : Type*} [Group G] [DecidableEq G] (g : G) :
    leftTrans g (delta (1 : G)) = delta g := by
  ext h
  simp only [leftTrans_apply, delta, lp.single_apply, Pi.single_apply]
  congr 1
  simp [inv_mul_eq_one, eq_comm]

lemma rightTrans_delta_one {G : Type*} [Group G] [DecidableEq G] (g : G) :
    rightTrans g (delta (1 : G)) = delta g := by
  ext h
  simp only [rightTrans_apply, delta, lp.single_apply, Pi.single_apply]
  congr 1
  simp [mul_inv_eq_one, eq_comm]

noncomputable def leftTransHom (G : Type*) [Group G] : G →* (L2 G →L[ℂ] L2 G) where
  toFun g := (leftTrans g).toLinearIsometry.toContinuousLinearMap
  map_one' := by ext u h; exact congrArg (fun v : L2 G => v h) (leftTrans_one u)
  map_mul' g k := by ext u h; exact congrArg (fun v : L2 G => v h) (leftTrans_mul g k u)

noncomputable def leftReg {G : Type*} [Group G] :
    MonoidAlgebra ℂ G →ₐ[ℂ] (L2 G →L[ℂ] L2 G) :=
  MonoidAlgebra.lift ℂ (L2 G →L[ℂ] L2 G) G (leftTransHom G)

lemma leftReg_single {G : Type*} [Group G] (g : G) (c : ℂ) :
    leftReg (MonoidAlgebra.single g c) = c • (leftTrans g).toLinearIsometry.toContinuousLinearMap := by
  simp [leftReg, MonoidAlgebra.lift_single, leftTransHom]

lemma leftReg_comm_rightTrans {G : Type*} [Group G] (x : MonoidAlgebra ℂ G)
    (k : G) (u : L2 G) :
    leftReg x (rightTrans k u) = rightTrans k (leftReg x u) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y ihx ihy => simp [map_add, ihx, ihy]
  | single g c =>
    rw [leftReg_single]
    change c • leftTrans g (rightTrans k u) = rightTrans k (c • leftTrans g u)
    rw [leftTrans_rightTrans_comm, map_smul]

lemma leftReg_delta_one_apply {G : Type*} [Group G] [DecidableEq G]
    (x : MonoidAlgebra ℂ G) (h : G) :
    (leftReg x (delta (1 : G))) h = x.coeff h := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y ihx ihy =>
    rw [map_add]
    change (leftReg x (delta 1) + leftReg y (delta 1)) h = x.coeff h + y.coeff h
    rw [← ihx, ← ihy]
    rfl
  | single g c =>
    rw [leftReg_single]
    change (c • leftTrans g (delta (1 : G))) h = (MonoidAlgebra.single g c).coeff h
    rw [leftTrans_delta_one]
    simp only [delta, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply,
      smul_eq_mul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hgh : g = h
    · subst hgh; simp
    · simp [hgh, Ne.symm]

lemma inner_delta_one_comm {G : Type*} [Group G] [DecidableEq G]
    (A : L2 G →L[ℂ] L2 G) (hA : ∀ k u, A (rightTrans k u) = rightTrans k (A u))
    (x : MonoidAlgebra ℂ G) :
    ⟪delta (1 : G), A (leftReg x (delta 1))⟫_ℂ = ⟪delta (1 : G), leftReg x (A (delta 1))⟫_ℂ := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y ihx ihy =>
    rw [map_add]
    change ⟪delta (1 : G), A (leftReg x (delta 1) + leftReg y (delta 1))⟫_ℂ =
        ⟪delta (1 : G), leftReg x (A (delta 1)) + leftReg y (A (delta 1))⟫_ℂ
    rw [map_add, inner_add_right, inner_add_right, ihx, ihy]
  | single g c =>
    rw [leftReg_single]
    change ⟪delta (1 : G), A (c • leftTrans g (delta 1))⟫_ℂ =
        ⟪delta (1 : G), c • leftTrans g (A (delta 1))⟫_ℂ
    rw [map_smul, inner_smul_right, inner_smul_right]
    congr 1
    calc ⟪delta (1 : G), A (leftTrans g (delta 1))⟫_ℂ
        = ⟪delta 1, A (rightTrans g (delta 1))⟫_ℂ := by rw [leftTrans_delta_one, rightTrans_delta_one]
      _ = ⟪delta 1, rightTrans g (A (delta 1))⟫_ℂ := by rw [hA]
      _ = ⟪rightTrans g⁻¹ (delta 1), A (delta 1)⟫_ℂ := inner_rightTrans_right g _ _
      _ = ⟪delta g⁻¹, A (delta 1)⟫_ℂ := by rw [rightTrans_delta_one]
      _ = ⟪leftTrans g⁻¹ (delta 1), A (delta 1)⟫_ℂ := by rw [leftTrans_delta_one]
      _ = ⟪delta 1, leftTrans g (A (delta 1))⟫_ℂ := (inner_leftTrans_right g _ _).symm

lemma eq_zero_of_idempotent_of_apply_one_eq_zero {G : Type*} [Group G]
    (p : MonoidAlgebra ℂ G) (hp : p * p = p) (hp1 : p.coeff 1 = 0) : p = 0 := by
  classical
  let T : L2 G →L[ℂ] L2 G := leftReg p
  have hT : ∀ u, T (T u) = T u := by
    intro u
    have hmul : leftReg (p * p) = leftReg p := congrArg leftReg hp
    rw [map_mul] at hmul
    exact congrArg (fun f : L2 G →L[ℂ] L2 G => f u) hmul
  let Ksub : Submodule ℂ (L2 G) :=
    LinearMap.ker (ContinuousLinearMap.id ℂ (L2 G) - T).toLinearMap
  have hKmem : ∀ u, u ∈ Ksub ↔ T u = u := by
    intro u
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, sub_eq_zero, eq_comm]
  have hKclosed : IsClosed (Ksub : Set (L2 G)) :=
    isClosed_singleton.preimage (ContinuousLinearMap.id ℂ (L2 G) - T).continuous
  have : CompleteSpace Ksub := hKclosed.completeSpace_coe
  let P : L2 G →L[ℂ] L2 G := Ksub.starProjection
  have hP_comm : ∀ k u, P (rightTrans k u) = rightTrans k (P u) := by
    intro k u
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hKmem]
      calc T (rightTrans k (P u))
          = rightTrans k (T (P u)) := leftReg_comm_rightTrans p k (P u)
        _ = rightTrans k (P u) := by rw [(hKmem (P u)).mp (Submodule.coe_mem _)]
    · intro w hw
      have hsub : rightTrans k u - rightTrans k (P u) = rightTrans k (u - P u) :=
        (rightTrans k).map_sub u (P u) |>.symm
      rw [hsub]
      have hre : ⟪rightTrans k (u - P u), w⟫_ℂ = ⟪u - P u, rightTrans k⁻¹ w⟫_ℂ := by
        calc ⟪rightTrans k (u - P u), w⟫_ℂ
            = ⟪rightTrans k (u - P u), rightTrans k (rightTrans k⁻¹ w)⟫_ℂ := by
                congr 1
                ext h
                simp [rightTrans_apply]
          _ = ⟪u - P u, rightTrans k⁻¹ w⟫_ℂ := (rightTrans k).inner_map_map _ _
      rw [hre]
      apply Submodule.starProjection_inner_eq_zero
      rw [hKmem]
      calc T (rightTrans k⁻¹ w)
          = rightTrans k⁻¹ (T w) := leftReg_comm_rightTrans p k⁻¹ w
        _ = rightTrans k⁻¹ w := by rw [(hKmem w).mp hw]
  have hPT : ∀ u, P (T u) = T u := by
    intro u
    exact Submodule.starProjection_eq_self_iff.mpr ((hKmem (T u)).mpr (hT u))
  have hTP : ∀ u, T (P u) = P u := by
    intro u
    exact (hKmem (P u)).mp (Submodule.coe_mem _)
  have hinner0 : ⟪delta (1 : G), P (delta 1)⟫_ℂ = 0 := by
    calc ⟪delta (1 : G), P (delta 1)⟫_ℂ
        = ⟪delta 1, T (P (delta 1))⟫_ℂ := by rw [hTP]
      _ = ⟪delta 1, P (T (delta 1))⟫_ℂ := (inner_delta_one_comm P hP_comm p).symm
      _ = ⟪delta 1, T (delta 1)⟫_ℂ := by rw [hPT]
      _ = (T (delta 1)) 1 := by
          rw [delta, lp.inner_single_left]
          simp
      _ = p.coeff 1 := leftReg_delta_one_apply p 1
      _ = 0 := hp1
  have hPsq : ⟪P (delta 1), P (delta 1)⟫_ℂ = 0 := by
    rw [Submodule.inner_starProjection_left_eq_right]
    change ⟪delta 1, P (P (delta 1))⟫_ℂ = 0
    have hPP : P (P (delta 1)) = P (delta 1) :=
      congrArg (fun f : L2 G →L[ℂ] L2 G => f (delta 1))
        (Submodule.isIdempotentElem_starProjection Ksub)
    rw [hPP]
    exact hinner0
  have hP1 : P (delta 1) = 0 := inner_self_eq_zero.mp hPsq
  have hPg : ∀ g : G, P (delta g) = 0 := by
    intro g
    rw [← rightTrans_delta_one g, hP_comm, hP1, map_zero]
  have hPT_zero : ∀ x : MonoidAlgebra ℂ G, P (leftReg x (delta 1)) = 0 := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y ihx ihy => simp [map_add, ihx, ihy]
    | single g c =>
      rw [leftReg_single]
      change P (c • leftTrans g (delta (1 : G))) = 0
      rw [leftTrans_delta_one, map_smul, hPg g, smul_zero]
  have hT_zero : T (delta 1) = 0 := by
    rw [← hPT (delta 1)]
    exact hPT_zero p
  ext h
  rw [← leftReg_delta_one_apply p h]
  change (T (delta 1)) h = 0
  rw [hT_zero]
  rfl

lemma coeff_mul_one_comm {G : Type*} [Group G] (x y : MonoidAlgebra ℂ G) :
    (x * y).coeff 1 = (y * x).coeff 1 := by
  classical
  rw [MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun b _ => ?_
  refine Finsupp.sum_congr fun a _ => ?_
  have hiff : a * b = (1 : G) ↔ b * a = 1 := by
    constructor <;> intro h
    · rw [mul_eq_one_iff_eq_inv.mp h, mul_inv_cancel]
    · rw [mul_eq_one_iff_eq_inv.mp h, mul_inv_cancel]
  simp [hiff, mul_comm]

lemma isDedekindFiniteMonoid_complex (G : Type*) [Group G] :
    IsDedekindFiniteMonoid (MonoidAlgebra ℂ G) := by
  rw [isDedekindFiniteMonoid_iff]
  intro a b hab
  let p : MonoidAlgebra ℂ G := 1 - b * a
  have hp : p * p = p := by
    dsimp [p]
    calc (1 - b * a) * (1 - b * a)
        = 1 - b * a - b * a + b * (a * b) * a := by noncomm_ring
      _ = 1 - b * a := by rw [hab]; noncomm_ring
  have hp1 : p.coeff 1 = 0 := by
    dsimp [p]
    change (1 : MonoidAlgebra ℂ G).coeff 1 - (b * a).coeff 1 = 0
    rw [MonoidAlgebra.coeff_one_one, coeff_mul_one_comm b a, hab,
      MonoidAlgebra.coeff_one_one, sub_self]
  have hp0 : p = 0 := eq_zero_of_idempotent_of_apply_one_eq_zero p hp hp1
  exact (sub_eq_zero.mp hp0).symm

/- Part 2: Embedding finitely generated subfields of `K` into `ℂ` -/

lemma countable_polynomial {F : Type*} [Semiring F] [Countable F] :
    Countable (Polynomial F) :=
  Function.Injective.countable (f := fun p : Polynomial F => p.toFinsupp.coeff)
    (fun p q h => by ext n; exact congrArg (fun f : ℕ →₀ F => f n) h)

lemma exists_transcendental_complex {F : Type*} [Field F] [Countable F] (φ : F →+* ℂ) :
    ∃ z : ℂ, ¬ @IsAlgebraic F ℂ _ _ φ.toAlgebra z := by
  letI : Algebra F ℂ := φ.toAlgebra
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set ℂ) ⊆
      ⋃ p : {p : Polynomial F // p ≠ 0}, ((p.1.map φ).roots.toFinset : Set ℂ) := by
    intro z _
    obtain ⟨p, hp0, hpz⟩ := h z
    refine Set.mem_iUnion.mpr ⟨⟨p, hp0⟩, ?_⟩
    have hmap : p.map φ ≠ 0 :=
      fun hz => hp0 (Polynomial.map_injective φ φ.injective (by simpa using hz))
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hmap]
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hpz
  have : Countable (Polynomial F) := countable_polynomial
  have hcount_univ : (Set.univ : Set ℂ).Countable :=
    (Set.countable_iUnion fun p : {p : Polynomial F // p ≠ 0} =>
      (p.1.map φ).roots.toFinset.countable_toSet).mono hsub
  have hC : Countable ℂ := Set.countable_univ_iff.mp hcount_univ
  have hUC : Uncountable ℂ := Function.Injective.uncountable Complex.ofReal_injective
  exact hUC.not_countable hC

lemma extend_simple_to_complex {K : Type*} [Field K] [CharZero K]
    (F : IntermediateField ℚ K) [Countable F] (φ : F →+* ℂ) (x : K) :
    Countable (IntermediateField.adjoin F ({x} : Set K)) ∧
      Nonempty ((IntermediateField.adjoin F ({x} : Set K)) →+* ℂ) := by
  have : Countable (Polynomial F) := countable_polynomial
  have hcount : Countable (IntermediateField.adjoin F ({x} : Set K)) := by
    let f : Polynomial F × Polynomial F → K :=
      fun pq => Polynomial.aeval x pq.1 / Polynomial.aeval x pq.2
    have hsub : (IntermediateField.adjoin F ({x} : Set K) : Set K) ⊆ Set.range f := by
      intro y hy
      rw [SetLike.mem_coe, IntermediateField.mem_adjoin_simple_iff] at hy
      obtain ⟨r, s, hrs⟩ := hy
      exact ⟨(r, s), hrs.symm⟩
    have hset : (IntermediateField.adjoin F ({x} : Set K) : Set K).Countable :=
      (Set.countable_range f).mono hsub
    exact hset.to_subtype
  refine ⟨hcount, ?_⟩
  letI : Algebra F ℂ := φ.toAlgebra
  by_cases halg : IsAlgebraic F x
  · obtain ⟨ψ⟩ := IntermediateField.nonempty_algHom_adjoin_of_splits (F := F) (E := K) (K := ℂ)
      (S := ({x} : Set K)) (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨halg.isIntegral, IsAlgClosed.splits _⟩)
    exact ⟨ψ.toRingHom⟩
  · obtain ⟨z, hz⟩ := exists_transcendental_complex φ
    have hx_ne : ∀ s : Polynomial F, s ≠ 0 → Polynomial.aeval x s ≠ 0 :=
      fun s hs h0 => halg ⟨s, hs, h0⟩
    have hz_ne : ∀ s : Polynomial F, s ≠ 0 → Polynomial.aeval z s ≠ 0 :=
      fun s hs h0 => hz ⟨s, hs, h0⟩
    have hx_inj : Function.Injective (Polynomial.aeval (R := F) x) := by
      intro p q hpq
      by_contra hne
      exact hx_ne (p - q) (sub_ne_zero.mpr hne) (by rw [map_sub, hpq, sub_self])
    have hrep : ∀ y : IntermediateField.adjoin F ({x} : Set K),
        ∃ pq : Polynomial F × Polynomial F,
          pq.2 ≠ 0 ∧ (y : K) = Polynomial.aeval x pq.1 / Polynomial.aeval x pq.2 := by
      intro y
      have hy := IntermediateField.mem_adjoin_simple_iff (F := F) (α := x) (y : K) |>.mp y.2
      obtain ⟨r, s, hrs⟩ := hy
      by_cases hs : s = 0
      · refine ⟨(0, 1), one_ne_zero, ?_⟩
        simp [hrs, hs]
      · exact ⟨(r, s), hs, hrs⟩
    have hwd : ∀ r₁ s₁ r₂ s₂ : Polynomial F, s₁ ≠ 0 → s₂ ≠ 0 →
        Polynomial.aeval x r₁ / Polynomial.aeval x s₁ =
          Polynomial.aeval x r₂ / Polynomial.aeval x s₂ →
        Polynomial.aeval z r₁ / Polynomial.aeval z s₁ =
          Polynomial.aeval z r₂ / Polynomial.aeval z s₂ := by
      intro r₁ s₁ r₂ s₂ hs₁ hs₂ heq
      have hxs₁ : Polynomial.aeval x s₁ ≠ 0 := hx_ne s₁ hs₁
      have hxs₂ : Polynomial.aeval x s₂ ≠ 0 := hx_ne s₂ hs₂
      have hzs₁ : Polynomial.aeval z s₁ ≠ 0 := hz_ne s₁ hs₁
      have hzs₂ : Polynomial.aeval z s₂ ≠ 0 := hz_ne s₂ hs₂
      have hmul : Polynomial.aeval x (r₁ * s₂) = Polynomial.aeval x (r₂ * s₁) := by
        simp only [map_mul]
        exact (div_eq_div_iff hxs₁ hxs₂).mp heq
      have hpoly : r₁ * s₂ = r₂ * s₁ := hx_inj hmul
      have hmulz : Polynomial.aeval z r₁ * Polynomial.aeval z s₂ =
          Polynomial.aeval z r₂ * Polynomial.aeval z s₁ := by
        simpa only [map_mul] using congrArg (Polynomial.aeval (R := F) z) hpoly
      exact (div_eq_div_iff hzs₁ hzs₂).mpr hmulz
    let num := fun y : IntermediateField.adjoin F ({x} : Set K) => (hrep y).choose.1
    let den := fun y : IntermediateField.adjoin F ({x} : Set K) => (hrep y).choose.2
    have hden_ne : ∀ y, den y ≠ 0 := fun y => (hrep y).choose_spec.1
    have hy_eq : ∀ y : IntermediateField.adjoin F ({x} : Set K),
        (y : K) = Polynomial.aeval x (num y) / Polynomial.aeval x (den y) :=
      fun y => (hrep y).choose_spec.2
    let ψ : IntermediateField.adjoin F ({x} : Set K) →+* ℂ :=
      { toFun := fun y => Polynomial.aeval z (num y) / Polynomial.aeval z (den y)
        map_one' := by
          have h := hwd (num 1) (den 1) 1 1 (hden_ne 1) one_ne_zero
          rw [← hy_eq 1] at h
          simpa using h (by simp)
        map_mul' := fun y₁ y₂ => by
          have h := hwd (num (y₁ * y₂)) (den (y₁ * y₂)) (num y₁ * num y₂) (den y₁ * den y₂)
            (hden_ne (y₁ * y₂)) (mul_ne_zero (hden_ne y₁) (hden_ne y₂))
          have hmul_x : ((y₁ * y₂ : IntermediateField.adjoin F ({x} : Set K)) : K) =
              Polynomial.aeval x (num y₁ * num y₂) / Polynomial.aeval x (den y₁ * den y₂) := by
            rw [MulMemClass.coe_mul, hy_eq y₁, hy_eq y₂, map_mul, map_mul, div_mul_div_comm]
          rw [← hy_eq (y₁ * y₂)] at h
          have hres := h hmul_x
          simpa [map_mul, div_mul_div_comm] using hres
        map_zero' := by
          have h := hwd (num 0) (den 0) 0 1 (hden_ne 0) one_ne_zero
          rw [← hy_eq 0] at h
          simpa using h (by simp)
        map_add' := fun y₁ y₂ => by
          have h := hwd (num (y₁ + y₂)) (den (y₁ + y₂))
            (num y₁ * den y₂ + num y₂ * den y₁) (den y₁ * den y₂)
            (hden_ne (y₁ + y₂)) (mul_ne_zero (hden_ne y₁) (hden_ne y₂))
          have hxs₁ : Polynomial.aeval x (den y₁) ≠ 0 := hx_ne (den y₁) (hden_ne y₁)
          have hxs₂ : Polynomial.aeval x (den y₂) ≠ 0 := hx_ne (den y₂) (hden_ne y₂)
          have hzs₁ : Polynomial.aeval z (den y₁) ≠ 0 := hz_ne (den y₁) (hden_ne y₁)
          have hzs₂ : Polynomial.aeval z (den y₂) ≠ 0 := hz_ne (den y₂) (hden_ne y₂)
          have hadd_x : ((y₁ + y₂ : IntermediateField.adjoin F ({x} : Set K)) : K) =
              Polynomial.aeval x (num y₁ * den y₂ + num y₂ * den y₁) /
                Polynomial.aeval x (den y₁ * den y₂) := by
            rw [AddMemClass.coe_add, hy_eq y₁, hy_eq y₂, div_add_div _ _ hxs₁ hxs₂]
            simp only [map_add, map_mul]
            ring
          rw [← hy_eq (y₁ + y₂)] at h
          have hres := h hadd_x
          rw [hres, map_add, map_mul, map_mul, map_mul, div_add_div _ _ hzs₁ hzs₂]
          ring }
    exact ⟨ψ⟩

lemma exists_ringHom_adjoin_complex {K : Type*} [Field K] [CharZero K] (S : Finset K) :
    Countable (IntermediateField.adjoin ℚ (S : Set K)) ∧
      Nonempty ((IntermediateField.adjoin ℚ (S : Set K)) →+* ℂ) := by
  classical
  induction S using Finset.induction with
  | empty =>
    let e₀ : IntermediateField.adjoin ℚ ((∅ : Finset K) : Set K) ≃ₐ[ℚ] ℚ :=
      (IntermediateField.equivOfEq
        (by simp [IntermediateField.adjoin_empty])).trans
        (IntermediateField.botEquiv ℚ K)
    exact ⟨Function.Injective.countable e₀.injective, ⟨(Rat.castHom ℂ).comp e₀.toRingHom⟩⟩
  | @insert x S hxS ih =>
    rcases ih with ⟨hcount_F, ⟨φ⟩⟩
    let F := IntermediateField.adjoin ℚ (S : Set K)
    have : Countable F := hcount_F
    obtain ⟨hcount_E, ⟨ψ⟩⟩ := extend_simple_to_complex F φ x
    let E := IntermediateField.adjoin F ({x} : Set K)
    let E_Q : IntermediateField ℚ K :=
      { carrier := (E : Set K)
        mul_mem' := E.mul_mem
        one_mem' := E.one_mem
        add_mem' := E.add_mem
        zero_mem' := E.zero_mem
        inv_mem' := fun _ hx => E.inv_mem hx
        algebraMap_mem' := fun q => by
          have hqF : algebraMap ℚ K q ∈ F := F.algebraMap_mem q
          exact IntermediateField.algebraMap_mem E ⟨algebraMap ℚ K q, hqF⟩ }
    have hset : (IntermediateField.adjoin ℚ ((insert x S : Finset K) : Set K) : Set K) =
        (E : Set K) := by
      ext y
      constructor
      · intro hy
        have hle : IntermediateField.adjoin ℚ ((insert x S : Finset K) : Set K) ≤ E_Q := by
          rw [IntermediateField.adjoin_le_iff]
          intro z hz
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hz
          rcases hz with hzx | hzS
          · rw [hzx]
            exact IntermediateField.mem_adjoin_simple_self F x
          · have hzF : z ∈ F := IntermediateField.subset_adjoin ℚ (S : Set K) hzS
            exact IntermediateField.algebraMap_mem E ⟨z, hzF⟩
        exact hle hy
      · intro hy
        rw [SetLike.mem_coe, IntermediateField.mem_adjoin_simple_iff] at hy
        obtain ⟨r, s, hrs⟩ := hy
        rw [SetLike.mem_coe, hrs]
        have hFT : ∀ z ∈ F, z ∈ IntermediateField.adjoin ℚ ((insert x S : Finset K) : Set K) :=
          fun z hz => IntermediateField.adjoin_le_iff.mpr
            (fun w hw => IntermediateField.subset_adjoin ℚ _ (by simp [hw])) hz
        have hx_in : x ∈ IntermediateField.adjoin ℚ ((insert x S : Finset K) : Set K) :=
          IntermediateField.subset_adjoin ℚ _ (by simp)
        have haeval : ∀ p : Polynomial F,
            Polynomial.aeval x p ∈ IntermediateField.adjoin ℚ ((insert x S : Finset K) : Set K) := by
          intro p
          rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum]
          refine sum_mem fun i _ => mul_mem (hFT _ (p.coeff i).2) (pow_mem hx_in i)
        exact div_mem (haeval r) (haeval s)
    let e : IntermediateField.adjoin ℚ ((insert x S : Finset K) : Set K) ≃+* E :=
      { toFun := fun y => ⟨y.1, (Set.ext_iff.mp hset y.1).mp y.2⟩
        invFun := fun y => ⟨y.1, (Set.ext_iff.mp hset y.1).mpr y.2⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl
        map_add' := fun _ _ => Subtype.ext rfl }
    exact ⟨Function.Injective.countable e.injective, ⟨ψ.comp e.toRingHom⟩⟩

end OMA.KaplanskyCharZero

theorem OMA.solution :
    type_of% @Kaplansky.direct_finiteness_conjecture.variants.char_zero := by
  intro K _ _ G _
  rw [isDedekindFiniteMonoid_iff]
  intro a b hab
  classical
  let S : Finset K := a.coeff.support.image a.coeff ∪ b.coeff.support.image b.coeff
  let F := IntermediateField.adjoin ℚ (S : Set K)
  obtain ⟨_, ⟨φ⟩⟩ := OMA.KaplanskyCharZero.exists_ringHom_adjoin_complex S
  have ha_mem : ∀ g : G, a.coeff g ∈ F := by
    intro g
    by_cases hg : a.coeff g = 0
    · rw [hg]; exact zero_mem F
    · refine IntermediateField.subset_adjoin ℚ (S : Set K) ?_
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hg))
  have hb_mem : ∀ g : G, b.coeff g ∈ F := by
    intro g
    by_cases hg : b.coeff g = 0
    · rw [hg]; exact zero_mem F
    · refine IntermediateField.subset_adjoin ℚ (S : Set K) ?_
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hg))
  let a' : MonoidAlgebra F G := MonoidAlgebra.ofCoeff
    (Finsupp.onFinset a.coeff.support (fun g => ⟨a.coeff g, ha_mem g⟩) (by
      intro g hg
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hg (Subtype.ext h0)))
  let b' : MonoidAlgebra F G := MonoidAlgebra.ofCoeff
    (Finsupp.onFinset b.coeff.support (fun g => ⟨b.coeff g, hb_mem g⟩) (by
      intro g hg
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hg (Subtype.ext h0)))
  have hincl : Function.Injective (MonoidAlgebra.mapRingHom G F.val.toRingHom) := by
    intro x y hxy
    ext g
    have hg := congrArg (fun z : MonoidAlgebra K G => z.coeff g) hxy
    rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom] at hg
    exact hg
  have ha_eq : MonoidAlgebra.mapRingHom G F.val.toRingHom a' = a := by
    ext g
    rw [MonoidAlgebra.coeff_mapRingHom]
    rfl
  have hb_eq : MonoidAlgebra.mapRingHom G F.val.toRingHom b' = b := by
    ext g
    rw [MonoidAlgebra.coeff_mapRingHom]
    rfl
  have hab' : a' * b' = 1 := by
    apply hincl
    rw [map_mul, map_one, ha_eq, hb_eq, hab]
  have hab_C : MonoidAlgebra.mapRingHom G φ a' * MonoidAlgebra.mapRingHom G φ b' = 1 := by
    rw [← map_mul, hab', map_one]
  have hba_C : MonoidAlgebra.mapRingHom G φ b' * MonoidAlgebra.mapRingHom G φ a' = 1 :=
    (isDedekindFiniteMonoid_iff _).mp
      (OMA.KaplanskyCharZero.isDedekindFiniteMonoid_complex G) hab_C
  have hphi_inj : Function.Injective (MonoidAlgebra.mapRingHom G φ) := by
    intro x y hxy
    ext g
    have hg := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g) hxy
    rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom] at hg
    exact congrArg Subtype.val (φ.injective hg)
  have hba' : b' * a' = 1 := by
    apply hphi_inj
    rw [map_mul, map_one, hba_C]
  calc b * a
      = MonoidAlgebra.mapRingHom G F.val.toRingHom b' *
          MonoidAlgebra.mapRingHom G F.val.toRingHom a' := by
          rw [ha_eq, hb_eq]
    _ = MonoidAlgebra.mapRingHom G F.val.toRingHom (b' * a') := (map_mul _ _ _).symm
    _ = 1 := by rw [hba', map_one]
