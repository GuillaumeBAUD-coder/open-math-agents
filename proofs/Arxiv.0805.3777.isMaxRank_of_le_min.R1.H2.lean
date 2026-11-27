import OMAReductions.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1
import Mathlib

/-!
# Lower bound for maximal rank of `m × n × (mn - u)` tensors

Step `Arxiv.0805.3777.isMaxRank_of_le_min.R1.H2`: for `3 ≤ m ≤ n` and `u ≤ min 4 m`, there exist
`m * n - u` complex `m × n` matrices not contained in the span of fewer than `m * n - ⌈u / 2⌉`
rank-one matrices.
-/

namespace MaxRankLeMinH2

open Matrix

private def JMap (u : ℕ) : (Fin u → ℂ) →ₗ[ℂ] (Fin u → ℂ) where
  toFun v j := if h : j.1 % 2 = 0 ∧ j.1 + 1 < u then v ⟨j.1 + 1, h.2⟩ else 0
  map_add' v w := by
    ext j
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

private lemma JMap_comp (u : ℕ) (v : Fin u → ℂ) : JMap u (JMap u v) = 0 := by
  ext j
  simp only [JMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

private lemma finrank_range_JMap (u : ℕ) :
    u / 2 ≤ Module.finrank ℂ (LinearMap.range (JMap u)) := by
  let f : Fin (u / 2) → LinearMap.range (JMap u) := fun i =>
    ⟨JMap u (Pi.single ⟨2 * i.1 + 1, by omega⟩ (1 : ℂ)), ⟨_, rfl⟩⟩
  have hli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hval := congrFun (congrArg Subtype.val hc) ⟨2 * i.1, by omega⟩
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at hval
    have hterm : ∀ j : Fin (u / 2),
        (f j).1 ⟨2 * i.1, by omega⟩ = if j = i then 1 else 0 := by
      intro j
      simp only [f, JMap, LinearMap.coe_mk, AddHom.coe_mk]
      have hcond : (2 * i.1) % 2 = 0 ∧ 2 * i.1 + 1 < u := by omega
      rw [dif_pos hcond]
      by_cases hji : j = i
      · subst hji
        simp [Pi.single_eq_same]
      · rw [if_neg hji]
        have hne : (⟨2 * i.1 + 1, hcond.2⟩ : Fin u) ≠ ⟨2 * j.1 + 1, by omega⟩ := by
          intro h
          apply hji
          apply Fin.ext
          have := congrArg Fin.val h
          dsimp at this
          omega
        exact Pi.single_eq_of_ne (M := fun _ : Fin u => ℂ) hne (1 : ℂ)
    simp_rw [hterm] at hval
    simpa using hval
  simpa using hli.fintype_card_le_finrank

private def pMap {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] (Fin u → ℂ) where
  toFun X j := X ⟨0, by omega⟩ ⟨j.1, by have := j.2; omega⟩
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

private def qMap {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] (Fin u → ℂ) where
  toFun X j := X ⟨1, by omega⟩ ⟨j.1, by have := j.2; omega⟩
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

private def deltaMap {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] (Fin u → ℂ) :=
  qMap hm hmn hu - (JMap u).comp (pMap hm hmn hu)

private lemma deltaMap_surjective {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    Function.Surjective (deltaMap hm hmn hu) := by
  intro w
  let X : Matrix (Fin m) (Fin n) ℂ := fun i j =>
    if i.1 = 1 then (if hj : j.1 < u then w ⟨j.1, hj⟩ else 0) else 0
  refine ⟨X, ?_⟩
  have hp : pMap hm hmn hu X = 0 := by
    ext j
    simp [pMap, X]
  have hq : qMap hm hmn hu X = w := by
    ext j
    simp [qMap, X, j.2]
  simp [deltaMap, hp, hq]

private lemma finrank_ker_deltaMap {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ min 4 m) :
    Module.finrank ℂ (LinearMap.ker (deltaMap hm hmn hu)) = m * n - u := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (deltaMap hm hmn hu)
  have hrange : LinearMap.range (deltaMap hm hmn hu) = ⊤ :=
    LinearMap.range_eq_top.mpr (deltaMap_surjective hm hmn hu)
  rw [hrange, finrank_top] at hrn
  have hdom : Module.finrank ℂ (Matrix (Fin m) (Fin n) ℂ) = m * n := by
    simp [Module.finrank_matrix]
  have hcod : Module.finrank ℂ (Fin u → ℂ) = u := by
    simp
  rw [hdom, hcod] at hrn
  omega

private lemma ceilDiv_two_add_div_two {u : ℕ} (hu : u ≤ 4) : u ⌈/⌉ 2 + u / 2 = u := by
  interval_cases u <;> decide

private lemma finrank_map_add_finrank_inf_ker {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (D : Submodule ℂ V) :
    Module.finrank ℂ (D.map f) + Module.finrank ℂ (D ⊓ LinearMap.ker f : Submodule ℂ V) =
      Module.finrank ℂ D := by
  let g := f.domRestrict D
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hrange : LinearMap.range g = D.map f := by
    ext w
    simp [g, Submodule.mem_map]
  have hker : (LinearMap.ker g).map D.subtype = D ⊓ LinearMap.ker f := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, Submodule.mem_inf]
    constructor
    · rintro ⟨⟨x, hx⟩, hgx, rfl⟩
      exact ⟨hx, hgx⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨v, hx⟩, hfx, rfl⟩
  have hker_dim : Module.finrank ℂ (LinearMap.ker g) =
      Module.finrank ℂ (D ⊓ LinearMap.ker f : Submodule ℂ V) := by
    rw [← hker, Submodule.finrank_map_subtype_eq]
  rw [hrange, hker_dim] at hrn
  exact hrn

theorem lower_bound : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H2 := by
  intro m n u hm hmn hu
  let δ := deltaMap hm hmn hu
  let S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ) := LinearMap.ker δ
  have hS_dim : Module.finrank ℂ S = m * n - u := finrank_ker_deltaMap hm hmn hu
  let b := Module.finBasisOfFinrankEq ℂ S hS_dim
  refine ⟨fun c => (b c).1, ?_⟩
  intro R x y hM
  let T : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ) :=
    Submodule.span ℂ (Set.range fun r : Fin R => Matrix.vecMulVec (x r) (y r))
  have hST : S ≤ T := by
    intro X hX
    have hrep := b.sum_repr ⟨X, hX⟩
    have hval : X = ∑ c : Fin (m * n - u), b.repr ⟨X, hX⟩ c • (b c).1 := by
      have h1 := congrArg Subtype.val hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1
      exact h1.symm
    rw [hval]
    exact Submodule.sum_mem T fun c _ => Submodule.smul_mem T _ (hM c)
  have hTR : Module.finrank ℂ T ≤ R := by
    classical
    have h1 := finrank_span_le_card (R := ℂ)
      (Set.range fun r : Fin R => Matrix.vecMulVec (x r) (y r))
    have h2 : (Set.range fun r : Fin R => Matrix.vecMulVec (x r) (y r)).toFinset.card ≤ R := by
      calc (Set.range fun r : Fin R => Matrix.vecMulVec (x r) (y r)).toFinset.card
          = (Finset.univ.image fun r : Fin R => Matrix.vecMulVec (x r) (y r)).card := by
            congr 1
            ext M
            simp
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = R := by simp
    exact h1.trans h2
  let D : Submodule ℂ (Fin u → ℂ) := T.map δ
  let U : Submodule ℂ (Fin u → ℂ) := D.map (JMap u) ⊔ (D ⊓ LinearMap.ker (JMap u))
  have hJp : ∀ X ∈ T, JMap u (pMap hm hmn hu X) ∈ U := by
    intro X hX
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
    · rintro _ ⟨r, rfl⟩
      let a : ℂ := x r ⟨0, by omega⟩
      let b0 : ℂ := x r ⟨1, by omega⟩
      let v : Fin u → ℂ := fun j => y r ⟨j.1, by have := j.2; omega⟩
      have hp : pMap hm hmn hu (Matrix.vecMulVec (x r) (y r)) = a • v := by
        ext j
        simp [pMap, Matrix.vecMulVec_apply, a, v]
      have hq : qMap hm hmn hu (Matrix.vecMulVec (x r) (y r)) = b0 • v := by
        ext j
        simp [qMap, Matrix.vecMulVec_apply, b0, v]
      have hwD : δ (Matrix.vecMulVec (x r) (y r)) ∈ D :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨r, rfl⟩)
      have hw : δ (Matrix.vecMulVec (x r) (y r)) = b0 • v - a • JMap u v := by
        simp [δ, deltaMap, hp, hq, map_smul]
      by_cases hb0 : b0 = 0
      · have hmemD : JMap u (pMap hm hmn hu (Matrix.vecMulVec (x r) (y r))) ∈ D := by
          have hneg : JMap u (pMap hm hmn hu (Matrix.vecMulVec (x r) (y r))) =
              -δ (Matrix.vecMulVec (x r) (y r)) := by
            rw [hw, hp, hb0]
            simp [map_smul]
          rw [hneg]
          exact D.neg_mem hwD
        have hmemK : JMap u (pMap hm hmn hu (Matrix.vecMulVec (x r) (y r))) ∈
            LinearMap.ker (JMap u) := by
          rw [LinearMap.mem_ker]
          exact JMap_comp u _
        exact Submodule.mem_sup_right ⟨hmemD, hmemK⟩
      · have hJw : JMap u (δ (Matrix.vecMulVec (x r) (y r))) = b0 • JMap u v := by
          rw [hw, map_sub, map_smul, map_smul, JMap_comp, smul_zero, sub_zero]
        have heq : JMap u (pMap hm hmn hu (Matrix.vecMulVec (x r) (y r))) =
            (a / b0) • JMap u (δ (Matrix.vecMulVec (x r) (y r))) := by
          rw [hp, map_smul, hJw, smul_smul, div_mul_cancel₀ a hb0]
        rw [heq]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hwD))
    · simp
    · intro X Y _ _ hX' hY'
      rw [map_add, map_add]
      exact U.add_mem hX' hY'
    · intro c X _ hX'
      rw [map_smul, map_smul]
      exact U.smul_mem c hX'
  have hrange_le : LinearMap.range (JMap u) ≤ U := by
    rintro _ ⟨v, rfl⟩
    let X : Matrix (Fin m) (Fin n) ℂ := fun i j =>
      if hj : j.1 < u then
        if i.1 = 0 then v ⟨j.1, hj⟩
        else if i.1 = 1 then JMap u v ⟨j.1, hj⟩
        else 0
      else 0
    have hpX : pMap hm hmn hu X = v := by
      ext j
      simp [pMap, X, j.2]
    have hqX : qMap hm hmn hu X = JMap u v := by
      ext j
      simp [qMap, X, j.2]
    have hXS : X ∈ S := by
      show δ X = 0
      simp [δ, deltaMap, hpX, hqX]
    simpa [hpX] using hJp X (hST hXS)
  have hD_dim : u / 2 ≤ Module.finrank ℂ D := by
    have h1 := finrank_range_JMap u
    have h2 : Module.finrank ℂ (LinearMap.range (JMap u)) ≤ Module.finrank ℂ U :=
      Submodule.finrank_mono hrange_le
    have h3 : Module.finrank ℂ U ≤
        Module.finrank ℂ (D.map (JMap u)) +
          Module.finrank ℂ (D ⊓ LinearMap.ker (JMap u) : Submodule ℂ (Fin u → ℂ)) := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq (D.map (JMap u))
        (D ⊓ LinearMap.ker (JMap u))
      change Module.finrank ℂ U + _ = _ at hsup
      omega
    have h4 := finrank_map_add_finrank_inf_ker (JMap u) D
    omega
  have hT_dim : Module.finrank ℂ D + Module.finrank ℂ S ≤ Module.finrank ℂ T := by
    have h1 := finrank_map_add_finrank_inf_ker δ T
    have h2 : S ≤ T ⊓ LinearMap.ker δ := le_inf hST le_rfl
    have h3 : Module.finrank ℂ S ≤ Module.finrank ℂ (T ⊓ LinearMap.ker δ : Submodule ℂ _) :=
      Submodule.finrank_mono h2
    change Module.finrank ℂ D + Module.finrank ℂ (T ⊓ LinearMap.ker δ : Submodule ℂ _) =
      Module.finrank ℂ T at h1
    omega
  have hu4 : u ≤ 4 := le_trans hu (min_le_left _ _)
  have hceil : u ⌈/⌉ 2 + u / 2 = u := ceilDiv_two_add_div_two hu4
  have humn : u ≤ m * n := by
    have : u ≤ m := le_trans hu (min_le_right _ _)
    nlinarith
  omega

end MaxRankLeMinH2

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1.H2 :=
  MaxRankLeMinH2.lower_bound
