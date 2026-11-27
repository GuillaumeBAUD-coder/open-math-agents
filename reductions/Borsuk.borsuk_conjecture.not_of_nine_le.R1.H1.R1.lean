import OMAReductions.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1

/-!
The rank-one projector construction of OpenAI, A nine-dimensional counterexample
to Borsuk's covering assertion, separates into three assertions. Coordinate
geometry realizes projective three-space on a sphere in nine dimensions.
A putative ten-set cover then gives a family of triples and tetrahedra on ten
labels. A finite obstruction rules out that incidence system.

The incidence axioms below come from openai/math, Lean module
OAI.Geometry.Borsuk.TenLabels.Labels, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
used under Apache-2.0. The squared-distance formulation and reduction are adapted
to the extended-diameter definition of a Borsuk cover.
-/
namespace OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1
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

theorem main : H1 → H2 → H3 → OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1.H1 := by
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
end OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1
