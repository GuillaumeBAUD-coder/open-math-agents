import OMAReductions.R_Erdos161_erdos_161_parts_ii_R1_H2_R1

/-!
# Proof of `Erdos161.erdos_161.parts.ii.R1.H2.R1.H1` (Hypergraph Ramsey's Theorem)

We prove Ramsey's Theorem (1930) for 2-colorings of `t`-uniform hypergraphs via the classical
double induction on uniformity `t` and target clique sum `a + b`, using link colorings on
`U.erase v`.
-/

-- Credit: @skhakim

private lemma hypergraph_ramsey :
    ∀ (t a b : ℕ), ∃ R : ℕ,
      ∀ (V : Type) [DecidableEq V] (U : Finset V), R ≤ U.card →
        ∀ col : Finset V → Bool,
          (∃ S ⊆ U, S.card = a ∧ ∀ e ⊆ S, e.card = t → col e = true) ∨
          (∃ S ⊆ U, S.card = b ∧ ∀ e ⊆ S, e.card = t → col e = false) := by
  intro t
  induction t with
  | zero =>
    intro a b
    refine ⟨max a b, fun V _ U hU col ↦ ?_⟩
    cases hcol : col ∅
    · right
      obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq ((le_max_right a b).trans hU)
      refine ⟨S, hSU, hScard, fun e _ he0 ↦ ?_⟩
      rw [Finset.card_eq_zero.mp he0, hcol]
    · left
      obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq ((le_max_left a b).trans hU)
      refine ⟨S, hSU, hScard, fun e _ he0 ↦ ?_⟩
      rw [Finset.card_eq_zero.mp he0, hcol]
  | succ t iht =>
    have hsum : ∀ (s a b : ℕ), a + b = s → ∃ R : ℕ,
        ∀ (V : Type) [DecidableEq V] (U : Finset V), R ≤ U.card →
          ∀ col : Finset V → Bool,
            (∃ S ⊆ U, S.card = a ∧ ∀ e ⊆ S, e.card = t + 1 → col e = true) ∨
            (∃ S ⊆ U, S.card = b ∧ ∀ e ⊆ S, e.card = t + 1 → col e = false) := by
      intro s
      induction s with
      | zero =>
        intro a b hab
        have ha : a = 0 := by omega
        subst ha
        refine ⟨0, fun V _ U _ _ ↦ Or.inl ⟨∅, Finset.empty_subset U, rfl, fun e heS hecard ↦ ?_⟩⟩
        have hle := Finset.card_le_card heS
        rw [hecard, Finset.card_empty] at hle
        omega
      | succ s ihs =>
        intro a b hab
        by_cases hat : a ≤ t
        · refine ⟨a, fun V _ U hU _ ↦ ?_⟩
          left
          obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq hU
          refine ⟨S, hSU, hScard, fun e heS hecard ↦ ?_⟩
          have hle := Finset.card_le_card heS
          omega
        · by_cases hbt : b ≤ t
          · refine ⟨b, fun V _ U hU _ ↦ ?_⟩
            right
            obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq hU
            refine ⟨S, hSU, hScard, fun e heS hecard ↦ ?_⟩
            have hle := Finset.card_le_card heS
            omega
          · obtain ⟨p, hp⟩ := ihs (a - 1) b (by omega)
            obtain ⟨q, hq⟩ := ihs a (b - 1) (by omega)
            obtain ⟨R₀, hR₀⟩ := iht p q
            refine ⟨R₀ + 1, fun V _ U hU col ↦ ?_⟩
            have hUpos : 0 < U.card := by omega
            obtain ⟨v, hvU⟩ := Finset.card_pos.mp hUpos
            let U' := U.erase v
            have hU'card : R₀ ≤ U'.card := by
              dsimp [U']
              rw [Finset.card_erase_of_mem hvU]
              omega
            let col' : Finset V → Bool := fun e ↦ col (insert v e)
            rcases hR₀ V U' hU'card col' with ⟨T, hTU', hTcard, hTmono⟩ | ⟨T, hTU', hTcard, hTmono⟩
            · rcases hp V T (by omega) col with ⟨S, hST, hScard, hSmono⟩ | ⟨S, hST, hScard, hSmono⟩
              · left
                have hvS : v ∉ S := fun hv ↦ (Finset.mem_erase.mp (hTU' (hST hv))).1 rfl
                refine ⟨insert v S, ?_, ?_, ?_⟩
                · exact Finset.insert_subset hvU (hST.trans (hTU'.trans (Finset.erase_subset v U)))
                · rw [Finset.card_insert_of_notMem hvS, hScard]
                  omega
                · intro e heS hecard
                  by_cases hve : v ∈ e
                  · let e' := e.erase v
                    have he'_sub : e' ⊆ S := by
                      intro x hx
                      rw [Finset.mem_erase] at hx
                      have := Finset.mem_insert.mp (heS hx.2)
                      rcases this with rfl | hxS
                      · exact absurd rfl hx.1
                      · exact hxS
                    have he'_card : e'.card = t := by
                      dsimp [e']
                      rw [Finset.card_erase_of_mem hve]
                      omega
                    have hins : insert v e' = e := Finset.insert_erase hve
                    rw [← hins]
                    exact hTmono e' (he'_sub.trans hST) he'_card
                  · have he_sub : e ⊆ S := by
                      intro x hx
                      rcases Finset.mem_insert.mp (heS hx) with rfl | hxS
                      · exact absurd hx hve
                      · exact hxS
                    exact hSmono e he_sub hecard
              · right
                exact ⟨S, hST.trans (hTU'.trans (Finset.erase_subset v U)), hScard, hSmono⟩
            · rcases hq V T (by omega) col with ⟨S, hST, hScard, hSmono⟩ | ⟨S, hST, hScard, hSmono⟩
              · left
                exact ⟨S, hST.trans (hTU'.trans (Finset.erase_subset v U)), hScard, hSmono⟩
              · right
                have hvS : v ∉ S := fun hv ↦ (Finset.mem_erase.mp (hTU' (hST hv))).1 rfl
                refine ⟨insert v S, ?_, ?_, ?_⟩
                · exact Finset.insert_subset hvU (hST.trans (hTU'.trans (Finset.erase_subset v U)))
                · rw [Finset.card_insert_of_notMem hvS, hScard]
                  omega
                · intro e heS hecard
                  by_cases hve : v ∈ e
                  · let e' := e.erase v
                    have he'_sub : e' ⊆ S := by
                      intro x hx
                      rw [Finset.mem_erase] at hx
                      have := Finset.mem_insert.mp (heS hx.2)
                      rcases this with rfl | hxS
                      · exact absurd rfl hx.1
                      · exact hxS
                    have he'_card : e'.card = t := by
                      dsimp [e']
                      rw [Finset.card_erase_of_mem hve]
                      omega
                    have hins : insert v e' = e := Finset.insert_erase hve
                    rw [← hins]
                    exact hTmono e' (he'_sub.trans hST) he'_card
                  · have he_sub : e ⊆ S := by
                      intro x hx
                      rcases Finset.mem_insert.mp (heS hx) with rfl | hxS
                      · exact absurd hx hve
                      · exact hxS
                    exact hSmono e he_sub hecard
    intro a b
    exact hsum (a + b) a b rfl

theorem OMA.solution : OMA.R_Erdos161_erdos_161_parts_ii_R1_H2_R1.H1 := by
  intro t d _ _
  obtain ⟨R₀, hR₀⟩ := hypergraph_ramsey t d d
  refine ⟨max d R₀, le_max_left d R₀, fun col ↦ ?_⟩
  have hcard : R₀ ≤ (Finset.univ : Finset (Fin (max d R₀))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact le_max_right d R₀
  rcases hR₀ (Fin (max d R₀)) Finset.univ hcard col with
    ⟨S, _, hScard, hSmono⟩ | ⟨S, _, hScard, hSmono⟩
  · exact ⟨true, S, hScard, hSmono⟩
  · exact ⟨false, S, hScard, hSmono⟩
