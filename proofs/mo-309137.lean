import OMAStatements.S_mo_309137

-- Problem: The existence of a specific kind of independent set in a connected graph satisfying the following property
-- Upstream: formal-conjectures statements/mo-309137.lean:0 (declaration OMA.S_mo_309137.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)


open Finset

namespace OMA.Aux309137

/-- Two cliques of size `n + 3` joined by a single edge between their `0` vertices. -/
def G (n : ℕ) : SimpleGraph (Fin 2 × Fin (n + 3)) where
  Adj p q := (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.1 ≠ q.1 ∧ p.2 = 0 ∧ q.2 = 0)
  symm := by
    constructor
    intro p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inr ⟨Ne.symm h1, h3, h2⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2 rfl
    · exact h1 rfl⟩

lemma reach (n : ℕ) (v : Fin 2 × Fin (n + 3)) : (G n).Reachable v (0, 0) := by
  obtain ⟨i, a⟩ := v
  have h1 : (G n).Reachable (i, a) (i, 0) := by
    by_cases h : a = 0
    · subst h; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, h⟩)
  have h2 : (G n).Reachable (i, 0) (0, 0) := by
    by_cases h : i = 0
    · subst h; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (Or.inr ⟨h, rfl, rfl⟩)
  exact h1.trans h2

def e1 (n : ℕ) : Fin (n + 3) := ⟨1, by omega⟩

lemma e1_ne (n : ℕ) : e1 n ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [e1] at this

lemma indep_pair (n : ℕ) :
    OMA.S_mo_309137.Independent (G n) {((0 : Fin 2), e1 n), ((1 : Fin 2), e1 n)} := by
  intro x hx y hy hadj
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact h2 rfl
  · exact h1 rfl
  · exact absurd (show (0 : Fin 2) = 1 from h1) (by decide)
  · exact e1_ne n h2
  · exact absurd (show (1 : Fin 2) = 0 from h1) (by decide)
  · exact e1_ne n h2
  · exact h2 rfl
  · exact h1 rfl

lemma priv (n : ℕ) (S : Finset (Fin 2 × Fin (n + 3))) (hS : 2 ≤ S.card)
    (hind : OMA.S_mo_309137.Independent (G n) S) :
    ∃ a ∈ S, n < (OMA.S_mo_309137.privateNeighbors (G n) S a).card := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨i, x⟩, ha⟩ := hne
  refine ⟨(i, x), ha, ?_⟩
  set T : Finset (Fin 2 × Fin (n + 3)) :=
    (((univ : Finset (Fin (n + 3))).erase x).erase 0).image (fun z => (i, z)) with hT
  have hcardT : n + 1 ≤ T.card := by
    rw [hT, Finset.card_image_of_injective _ (fun z w h => (Prod.ext_iff.mp h).2)]
    have c1 := Finset.pred_card_le_card_erase (s := (univ : Finset (Fin (n + 3))).erase x) (a := 0)
    have c2 := Finset.pred_card_le_card_erase (s := (univ : Finset (Fin (n + 3)))) (a := x)
    rw [Finset.card_univ, Fintype.card_fin] at c2
    omega
  have hsub : T ⊆ OMA.S_mo_309137.privateNeighbors (G n) S (i, x) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_erase, Finset.mem_erase] at hz
    obtain ⟨hz0, hzx, _⟩ := hz
    simp only [OMA.S_mo_309137.privateNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, Or.inl ⟨rfl, hzx⟩, ?_⟩
    · intro hz'
      exact hind (i, z) hz' (i, x) ha (Or.inl ⟨rfl, hzx⟩)
    · rintro ⟨j, w⟩ hy hadj
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · have hij : i = j := h1
        subst hij
        by_contra hne
        have hwx : w ≠ x := fun h => hne (by rw [h])
        exact hind (i, w) hy (i, x) ha (Or.inl ⟨rfl, hwx⟩)
      · exact absurd h2 hz0
  calc n < n + 1 := Nat.lt_succ_self n
    _ ≤ T.card := hcardT
    _ ≤ _ := Finset.card_le_card hsub

end OMA.Aux309137

open OMA.Aux309137 in
theorem OMA.solution : type_of% @OMA.S_mo_309137.main := by
  intro n hn
  refine ⟨Fin 2 × Fin (n + 3), inferInstance, G n, ?_, ?_, ?_, ?_⟩
  · exact (SimpleGraph.connected_iff _).mpr
      ⟨fun u v => (reach n u).trans (reach n v).symm, ⟨(0, 0)⟩⟩
  · intro x y h
    exact ⟨y, Or.inl ⟨h, fun h' => (G n).ne_of_adj h' rfl⟩⟩
  · refine ⟨{((0 : Fin 2), e1 n), ((1 : Fin 2), e1 n)}, ?_, indep_pair n⟩
    rw [Finset.card_pair]
    intro h
    exact absurd (show (0 : Fin 2) = 1 from congrArg Prod.fst h) (by decide)
  · intro S hS hind
    exact priv n S hS hind
