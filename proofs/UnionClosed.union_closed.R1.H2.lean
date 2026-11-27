import OMAReductions.R_UnionClosed_union_closed_R1

-- A union-closed family containing a two-element set {x, y} has x or y in at least half of its members.
-- Original Lean proof of a classical fact (Sarvate and Renaud 1989): adding x and y maps the members containing
-- neither injectively into the members containing both; whichever of x, y lies alone in more members then lies
-- in at least half of all members.
-- A classical special case, not progress on the union-closed sets conjecture.

namespace OMA.UnionClosed2

universe u

theorem pair_case {n : Type u} [DecidableEq n] (A : Finset (Finset n)) (x y : n) (hxy : x ≠ y)
    (huc : UnionClosed.IsUnionClosed A) (hmem : {x, y} ∈ A) :
    (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => x ∈ X)).card ∨
      (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => y ∈ X)).card := by
  have hA : (A.filter (fun X => x ∈ X)).card + (A.filter (fun X => ¬ x ∈ X)).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hPx : ((A.filter (fun X => x ∈ X)).filter (fun X => y ∈ X)).card +
      ((A.filter (fun X => x ∈ X)).filter (fun X => ¬ y ∈ X)).card =
      (A.filter (fun X => x ∈ X)).card := Finset.card_filter_add_card_filter_not _
  have hNx : ((A.filter (fun X => ¬ x ∈ X)).filter (fun X => y ∈ X)).card +
      ((A.filter (fun X => ¬ x ∈ X)).filter (fun X => ¬ y ∈ X)).card =
      (A.filter (fun X => ¬ x ∈ X)).card := Finset.card_filter_add_card_filter_not _
  have hPy : ((A.filter (fun X => x ∈ X)).filter (fun X => y ∈ X)).card +
      ((A.filter (fun X => ¬ x ∈ X)).filter (fun X => y ∈ X)).card =
      (A.filter (fun X => y ∈ X)).card := by
    have h := Finset.card_filter_add_card_filter_not (s := A.filter (fun X => y ∈ X))
      (fun X => x ∈ X)
    rw [Finset.filter_comm (fun X => y ∈ X) (fun X => x ∈ X),
      Finset.filter_comm (fun X => y ∈ X) (fun X => ¬ x ∈ X)] at h
    exact h
  have hmap : ∀ X ∈ (A.filter (fun X => ¬ x ∈ X)).filter (fun X => ¬ y ∈ X),
      X ∪ {x, y} ∈ (A.filter (fun X => x ∈ X)).filter (fun X => y ∈ X) := by
    intro X hX
    simp only [Finset.mem_filter] at hX ⊢
    exact ⟨⟨huc X hX.1.1 {x, y} hmem, by simp⟩, by simp⟩
  have hinj : Set.InjOn (fun X : Finset n => X ∪ {x, y})
      ((A.filter (fun X => ¬ x ∈ X)).filter (fun X => ¬ y ∈ X) : Set (Finset n)) := by
    intro X hX Y hY hXY
    rw [Finset.mem_coe] at hX hY
    simp only [Finset.mem_filter] at hX hY
    ext a
    have h := Finset.ext_iff.mp hXY a
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    by_cases hax : a = x
    · subst hax
      exact ⟨fun h1 => absurd h1 hX.1.2, fun h1 => absurd h1 hY.1.2⟩
    by_cases hay : a = y
    · subst hay
      exact ⟨fun h1 => absurd h1 hX.2, fun h1 => absurd h1 hY.2⟩
    constructor
    · intro ha
      rcases h.mp (Or.inl ha) with h2 | h2 | h2
      · exact h2
      · exact absurd h2 hax
      · exact absurd h2 hay
    · intro ha
      rcases h.mpr (Or.inl ha) with h2 | h2 | h2
      · exact h2
      · exact absurd h2 hax
      · exact absurd h2 hay
  have hle := Finset.card_le_card_of_injOn _ hmap hinj
  by_cases hcmp : ((A.filter (fun X => ¬ x ∈ X)).filter (fun X => y ∈ X)).card ≤
      ((A.filter (fun X => x ∈ X)).filter (fun X => ¬ y ∈ X)).card
  · left
    have hnat : A.card ≤ 2 * (A.filter (fun X => x ∈ X)).card := by omega
    have hq : (A.card : ℚ) ≤ 2 * ((A.filter (fun X => x ∈ X)).card : ℚ) := by exact_mod_cast hnat
    linarith
  · right
    have hnat : A.card ≤ 2 * (A.filter (fun X => y ∈ X)).card := by omega
    have hq : (A.card : ℚ) ≤ 2 * ((A.filter (fun X => y ∈ X)).card : ℚ) := by exact_mod_cast hnat
    linarith

end OMA.UnionClosed2

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H2 := by
  intro m A x y hxy huc hmem
  exact OMA.UnionClosed2.pair_case A x y hxy huc hmem
