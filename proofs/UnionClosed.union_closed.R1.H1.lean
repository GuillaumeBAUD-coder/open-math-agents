import OMAReductions.R_UnionClosed_union_closed_R1

-- A union-closed family containing a singleton {x} has x in at least half of its members.
-- Original Lean proof of a classical fact (Sarvate and Renaud 1989): X to X with x added maps the members
-- without x injectively into the members with x.
-- A classical special case, not progress on the union-closed sets conjecture.

namespace OMA.UnionClosed1

universe u

theorem singleton_case {n : Type u} [DecidableEq n] (A : Finset (Finset n)) (x : n)
    (huc : UnionClosed.IsUnionClosed A) (hx : {x} ∈ A) :
    (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => x ∈ X)).card := by
  have hsplit : (A.filter (fun X => x ∈ X)).card + (A.filter (fun X => ¬ x ∈ X)).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hmap : ∀ X ∈ A.filter (fun X => ¬ x ∈ X), X ∪ {x} ∈ A.filter (fun X => x ∈ X) := by
    intro X hX
    rw [Finset.mem_filter] at hX ⊢
    exact ⟨huc X hX.1 {x} hx, by simp⟩
  have hinj : Set.InjOn (fun X : Finset n => X ∪ {x})
      (A.filter (fun X => ¬ x ∈ X) : Set (Finset n)) := by
    intro X hX Y hY hXY
    rw [Finset.mem_coe, Finset.mem_filter] at hX hY
    ext a
    have h := Finset.ext_iff.mp hXY a
    simp only [Finset.mem_union, Finset.mem_singleton] at h
    by_cases hax : a = x
    · subst hax
      exact ⟨fun h1 => absurd h1 hX.2, fun h1 => absurd h1 hY.2⟩
    · constructor
      · intro ha
        rcases h.mp (Or.inl ha) with h2 | h2
        · exact h2
        · exact absurd h2 hax
      · intro ha
        rcases h.mpr (Or.inl ha) with h2 | h2
        · exact h2
        · exact absurd h2 hax
  have hle := Finset.card_le_card_of_injOn _ hmap hinj
  have hnat : A.card ≤ 2 * (A.filter (fun X => x ∈ X)).card := by omega
  have hq : (A.card : ℚ) ≤ 2 * ((A.filter (fun X => x ∈ X)).card : ℚ) := by exact_mod_cast hnat
  linarith

end OMA.UnionClosed1

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H1 := by
  intro m A x huc hx
  exact OMA.UnionClosed1.singleton_case A x huc hx
