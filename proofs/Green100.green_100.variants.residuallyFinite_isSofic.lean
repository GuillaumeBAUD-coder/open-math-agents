import FormalConjectures.GreensOpenProblems.«100»

-- Problem: Ben Green's Open Problem 100 — residuallyFinite isSofic
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/100.lean:195 (declaration Green100.green_100.variants.residuallyFinite_isSofic)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Green100

namespace OMA

theorem hamming_self {n : ℕ} (σ : Equiv.Perm (Fin n)) : hammingDistNorm σ σ = 0 := by
  simp [hammingDistNorm]

theorem hamming_all {n : ℕ} (hn : 0 < n) (σ τ : Equiv.Perm (Fin n)) (h : ∀ i, σ i ≠ τ i) :
    hammingDistNorm σ τ = 1 := by
  unfold hammingDistNorm hammingDist
  rw [Finset.filter_true_of_mem (fun i _ => h i), Finset.card_univ, Fintype.card_fin]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end OMA

theorem OMA.solution : type_of% @Green100.green_100.variants.residuallyFinite_isSofic := by
  intro G _ _ F ε hε
  classical
  have hK : ∀ p : F × F, ∃ K : FiniteIndexNormalSubgroup G,
      p.1.1 ≠ p.2.1 → (p.1.1 : G ⧸ K.toSubgroup) ≠ ↑p.2.1 := by
    intro p
    by_cases h : p.1.1 = p.2.1
    · exact ⟨.ofSubgroup ⊤, fun h' => (h' h).elim⟩
    · obtain ⟨K, hK⟩ := Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite _ _ h
      exact ⟨K, fun _ => hK⟩
  choose K hK using hK
  let Q := ∀ p : F × F, G ⧸ (K p).toSubgroup
  let φ : G →* Q := MonoidHom.pi fun p => QuotientGroup.mk' (K p).toSubgroup
  have : Finite Q := inferInstance
  let n := Nat.card Q
  let e : Q ≃ Fin n := Finite.equivFin Q
  have hn : 0 < n := Nat.card_pos
  let θ : G → Equiv.Perm (Fin n) := fun g => (e.symm.trans (Equiv.mulLeft (φ g))).trans e
  have hmul : ∀ g h, θ g * θ h = θ (g * h) := by
    intro g h
    ext i
    simp [θ]
  refine ⟨n, θ, ?_, ?_, ?_⟩
  · intro g _ h _ _
    rw [hmul, OMA.hamming_self]; exact hε
  · intro _
    have : θ 1 = 1 := by ext i; simp [θ]
    rw [this, OMA.hamming_self]; exact hε
  · intro x hx y hy hxy
    have hφ : φ x ≠ φ y := by
      intro h
      have := congrFun h (⟨x, hx⟩, ⟨y, hy⟩)
      exact hK (⟨x, hx⟩, ⟨y, hy⟩) hxy this
    rw [OMA.hamming_all hn]
    · norm_num
    · intro i hi
      apply hφ
      have := e.injective hi
      simpa [θ] using this
