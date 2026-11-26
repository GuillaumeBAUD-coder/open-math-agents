import FormalConjectures.GreensOpenProblems.«100»

-- Problem: Ben Green's Open Problem 100 — residuallyFinite isSofic
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/100.lean (declaration Green100.green_100.variants.residuallyFinite_isSofic)
-- Credit: @niclorusso (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Residually finite groups are sofic.

Given a finite set `F`, residual finiteness gives, for every pair of distinct elements of `F`,
a finite index normal subgroup separating them. The product of the corresponding finite
quotients is a finite group `Q` with a homomorphism `π : G →* Q` that is injective on `F`.
Letting `G` act on `Q` by left multiplication through `π` gives an exact homomorphism into a
symmetric group, so the approximate-homomorphism conditions hold with error `0`, and distinct
elements of `F` act as permutations that differ at every point, at normalised distance `1`.
-/

namespace OMA.Sofic

open Green100

/-- A homomorphism to a finite group that is injective on `F` gives a sofic approximation of `F`
with any error. -/
lemma sofic_of_hom {G Q : Type*} [Group G] [Group Q] [Fintype Q] (F : Finset G) (π : G →* Q)
    (hπ : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → π x ≠ π y) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (θ : G → Equiv.Perm (Fin n)),
      (∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → hammingDistNorm (θ g * θ h) (θ (g * h)) < ε) ∧
      (1 ∈ F → hammingDistNorm (θ 1) 1 < ε) ∧
      ∀ x ∈ F, ∀ y ∈ F, x ≠ y → (1 / 4 : ℝ) ≤ hammingDistNorm (θ x) (θ y) := by
  let e := Fintype.equivFin Q
  let θ : G → Equiv.Perm (Fin (Fintype.card Q)) := fun g => e.permCongr (Equiv.mulLeft (π g))
  have hθ : ∀ g h, θ g * θ h = θ (g * h) := by
    intro g h
    ext i
    simp [θ, Equiv.permCongr_apply]
  have h1 : θ 1 = 1 := by
    ext i
    simp [θ, Equiv.permCongr_apply]
  refine ⟨Fintype.card Q, θ, ?_, ?_, ?_⟩
  · intro g _ h _ _
    rw [hθ]
    simp [hammingDistNorm, hε]
  · intro _
    rw [h1]
    simp [hammingDistNorm, hε]
  · intro x hx y hy hxy
    have hne := hπ x hx y hy hxy
    have hcard : 0 < Fintype.card Q := Fintype.card_pos
    have hd : hammingDist (⇑(θ x)) (⇑(θ y)) = Fintype.card Q := by
      unfold hammingDist
      rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
      intro i _
      simp [θ, Equiv.permCongr_apply, hne]
    unfold hammingDistNorm
    rw [hd, div_self (by exact_mod_cast hcard.ne')]
    norm_num

end OMA.Sofic

open Green100 OMA.Sofic in
theorem OMA.solution : type_of% @Green100.green_100.variants.residuallyFinite_isSofic := by
  intro G _ _
  classical
  unfold IsSofic
  intro F ε hε
  have hsep : ∀ p : F.offDiag, ∃ H : FiniteIndexNormalSubgroup G,
      (p.1.1 : G ⧸ H.toSubgroup) ≠ ↑p.1.2 := fun p =>
    Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite _ _ (Finset.mem_offDiag.1 p.2).2.2
  choose H hH using hsep
  have hN : ∀ p, (H p).toSubgroup.Normal := fun p => (H p).isNormal'
  have hI : ∀ p, (H p).toSubgroup.FiniteIndex := fun p => (H p).isFiniteIndex'
  have : Finite (∀ p : F.offDiag, G ⧸ (H p).toSubgroup) := Pi.finite
  let _ : Fintype (∀ p : F.offDiag, G ⧸ (H p).toSubgroup) := Fintype.ofFinite _
  let π : G →* ∀ p : F.offDiag, G ⧸ (H p).toSubgroup :=
    MonoidHom.pi fun p => QuotientGroup.mk' (H p).toSubgroup
  refine sofic_of_hom F π ?_ ε hε
  intro x hx y hy hxy h
  have := congrFun h ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩⟩
  exact hH ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩⟩ this
