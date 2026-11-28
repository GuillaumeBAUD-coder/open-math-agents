import OMAReductions.R_erdos_634_R1_H2_R1_H1_R1_H3_R1_H1_R1
import Mathlib.Topology.MetricSpace.Congruence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace OMA.E634Transfer

open scoped RealInnerProductSpace

noncomputable def triangleBasis (S : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨S.points, S.independent, S.span_eq_top (by simp)⟩

lemma triangleBasis_apply (S : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (i : Fin 3) : triangleBasis S i = S.points i := rfl

lemma basis_inner_preserved {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (h : ∀ i j, ⟪f (b i), f (b j)⟫ = ⟪b i, b j⟫) :
    ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫ := by
  classical
  intro x y
  calc
    ⟪f x, f y⟫ =
        ⟪f (∑ i, b.repr x i • b i), f (∑ j, b.repr y j • b j)⟫ := by
          rw [b.sum_repr, b.sum_repr]
    _ = ∑ j, ∑ i, b.repr y j * b.repr x i * ⟪f (b i), f (b j)⟫ := by
          simp only [map_sum, map_smul, sum_inner, inner_sum,
            real_inner_smul_left, real_inner_smul_right, mul_assoc]
    _ = ∑ j, ∑ i, b.repr y j * b.repr x i * ⟪b i, b j⟫ := by simp_rw [h]
    _ = ⟪∑ i, b.repr x i • b i, ∑ j, b.repr y j • b j⟫ := by
          simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    _ = ⟪x, y⟫ := by rw [b.sum_repr, b.sum_repr]

lemma congruent_isometry
    (S M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (hc : Congruent S.points M.points) :
    ∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
      ∀ i, f (S.points i) = M.points i := by
  classical
  let bs := triangleBasis S
  let bm := triangleBasis M
  let b := bs.basisOf 0
  let c := bm.basisOf 0
  let f := b.equiv c (Equiv.refl _)
  have hgram (i j : {i : Fin 3 // i ≠ 0}) :
      ⟪f (b i), f (b j)⟫ = ⟪b i, b j⟫ := by
    simp only [f, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp only [b, c, AffineBasis.basisOf_apply, bs, bm, triangleBasis]
    change ⟪M.points i -ᵥ M.points 0, M.points j -ᵥ M.points 0⟫ =
      ⟪S.points i -ᵥ S.points 0, S.points j -ᵥ S.points 0⟫
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    simp only [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2))]
    rw [hc.dist_eq i 0, hc.dist_eq j 0, hc.dist_eq i j]
  let L := f.isometryOfInner (basis_inner_preserved b f hgram)
  let F := ((IsometryEquiv.vaddConst (S.points 0)).symm.trans L.toIsometryEquiv).trans
    (IsometryEquiv.vaddConst (M.points 0))
  refine ⟨F, fun i => ?_⟩
  change f (S.points i -ᵥ S.points 0) +ᵥ M.points 0 = M.points i
  by_cases hi : i = 0
  · simp [hi]
  · have he := Module.Basis.equiv_apply b (⟨i, hi⟩ : {j : Fin 3 // j ≠ 0}) c (Equiv.refl _)
    have he' : f (S.points i -ᵥ S.points 0) = M.points i -ᵥ M.points 0 := by
      simpa only [f, b, c, AffineBasis.basisOf_apply, bs, bm, triangleBasis_apply,
        Equiv.refl_apply] using he
    rw [he', vsub_vadd]

lemma interior_closed_subset
    (S : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    interior S.closedInterior ⊆ S.interior := by
  let b := triangleBasis S
  intro x hx
  have hx' : ∀ i, 0 < b.coord i x := by
    change x ∈ {x | ∀ i, 0 < b.coord i x}
    rw [← b.interior_convexHull]
    change x ∈ interior (convexHull ℝ (Set.range S.points))
    rw [Affine.Simplex.convexHull_eq_closedInterior]
    exact hx
  have hs := b.sum_coord_apply_eq_one x
  refine ⟨fun i => b.coord i x, hs, ?_, ?_⟩
  · intro i
    refine ⟨hx' i, ?_⟩
    have h0 := hx' 0
    have h1 := hx' 1
    have h2 := hx' 2
    rw [Fin.sum_univ_three] at hs
    fin_cases i <;> dsimp <;> linarith
  · exact b.affineCombination_coord_eq_self x

lemma commensurable_third {a b c : ℝ}
    (hab : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b)
    (hac : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * b = n * c := by
  obtain ⟨m, n, hm, hn, hab⟩ := hab
  obtain ⟨r, s, hr, hs, hac⟩ := hac
  refine ⟨n * r, m * s, Nat.mul_pos hn hr, Nat.mul_pos hm hs, ?_⟩
  push_cast
  linear_combination -(r : ℝ) * hab + (m : ℝ) * hac


def ModelHyp : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)

def Conclusion : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, L k = dist ((Ts t).points (k + 1)) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → (∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * b = n * c))

lemma transfer : ModelHyp → Conclusion := by
  intro h p hp hp3 T Ts hc hd hu t A B L hA hB hL hEq α a b c hα hBL
  have hi : ∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))
      (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = (Ts t).points (σ k) := by
    intro i
    obtain ⟨f, hf⟩ := congruent_isometry (Ts i) (Ts t) (hc i t)
    exact ⟨f, Equiv.refl _, hf⟩
  have hd' : Pairwise (fun i j =>
      Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) := by
    intro i j hij
    exact (hd hij).mono (interior_closed_subset (Ts i)) (interior_closed_subset (Ts j))
  have hnot : ¬ ∃ τ : Equiv.Perm (Fin 3), A = B ∘ τ := by
    rintro ⟨τ, hτ⟩
    obtain ⟨σ, hBσ, _⟩ := hBL
    have h120 : B (σ 2) = 2 * Real.pi / 3 := by
      simpa using congrFun hBσ (2 : Fin 3)
    have he := congrFun hτ (τ.symm (σ 2))
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at he
    rw [hEq] at he
    linarith [Real.pi_pos]
  obtain ⟨hab, hac⟩ :=
    h p T (Ts t) Ts hi hd' hu A B L hA hB hL α a b c hα hBL hnot
  exact ⟨hac, commensurable_third hab hac⟩

end OMA.E634Transfer

theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1_H1_R1.H2 := OMA.E634Transfer.transfer
