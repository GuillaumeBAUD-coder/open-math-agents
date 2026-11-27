import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

/-!
Reduction `ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1` of the central
(even diameter) non-path tree case of Kelly's theorem (`H3` of `tree.R1`). Proves the radius-1
star case in-file and splits the remainder into four modular subgoals:
1. `H1`: Diameter equality and unique center existence (`G.diam = H.diam = 2 * r`, `r >= 1`).
2. `H2`: Center degree equality and singleton-limb elimination (for `r >= 2`).
3. `H3`: Isomorphism when every center component has cardinality at most `r`.
4. `H4`: Isomorphism when some center component has cardinality strictly greater than `r`.
-/

-- Reduction ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H3.R1
-- Credit: @green-notes

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1

open SimpleGraph

def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Even G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      ∃ (r : ℕ) (cG : V) (cH : W),
        1 ≤ r ∧ G.diam = 2 * r ∧ H.diam = 2 * r ∧
        G.eccent cG = r ∧ H.eccent cH = r ∧
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) ∧
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)

def H2 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ (r : ℕ) (cG : V) (cH : W),
        2 ≤ r → G.diam = 2 * r → H.diam = 2 * r →
        G.eccent cG = r → H.eccent cH = r →
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) →
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w) →
        (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
        Nonempty (G ≃g H) ∨
          ((G.neighborSet cG).ncard = (H.neighborSet cH).ncard ∧
            (∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard) ∧
            (∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard))

def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ (r : ℕ) (cG : V) (cH : W),
        2 ≤ r → G.diam = 2 * r → H.diam = 2 * r →
        G.eccent cG = r → H.eccent cH = r →
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) →
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w) →
        (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
        (G.neighborSet cG).ncard = (H.neighborSet cH).ncard →
        (∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard) →
        (∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard) →
        (∀ C : (G.induce {cG}ᶜ).ConnectedComponent, C.supp.ncard ≤ r) →
        (∀ D : (H.induce {cH}ᶜ).ConnectedComponent, D.supp.ncard ≤ r) →
        Nonempty (G ≃g H)

def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ (r : ℕ) (cG : V) (cH : W),
        2 ≤ r → G.diam = 2 * r → H.diam = 2 * r →
        G.eccent cG = r → H.eccent cH = r →
        (∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v) →
        (∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w) →
        (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
          Fintype.card U < Fintype.card V →
          {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
            {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
        (G.neighborSet cG).ncard = (H.neighborSet cH).ncard →
        (∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard) →
        (∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard) →
        ((∃ C : (G.induce {cG}ᶜ).ConnectedComponent, r < C.supp.ncard) ∨
          (∃ D : (H.induce {cH}ᶜ).ConnectedComponent, r < D.supp.ncard)) →
        Nonempty (G ≃g H)

section StarRadiusOne

open Classical

private lemma adj_iff_center_of_eccent_one {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (hecc : T.eccent c = 1) (a b : U) :
    T.Adj a b ↔ (a = c ∧ b ≠ c) ∨ (b = c ∧ a ≠ c) := by
  have hadj : ∀ x : U, c ≠ x → T.Adj c x := (T.eccent_le_one_iff c).mp hecc.le
  constructor
  · intro hab
    by_cases hac : a = c
    · exact Or.inl ⟨hac, fun hbc => T.ne_of_adj hab (hac.trans hbc.symm)⟩
    · by_cases hbc : b = c
      · exact Or.inr ⟨hbc, hac⟩
      · have h1 : T.dist c a = 1 := dist_eq_one_iff_adj.mpr (hadj a (Ne.symm hac))
        have h2 : T.dist c b = 1 := dist_eq_one_iff_adj.mpr (hadj b (Ne.symm hbc))
        exact False.elim (hT.dist_ne_of_adj c hab (h1.trans h2.symm))
  · rintro (⟨rfl, hbc⟩ | ⟨rfl, hac⟩)
    · exact hadj b (Ne.symm hbc)
    · exact (hadj a (Ne.symm hac)).symm

private lemma iso_of_eccent_one {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (σ : V ≃ W) (hTG : G.IsTree) (hTH : H.IsTree) (cG : V) (cH : W)
    (heccG : G.eccent cG = 1) (heccH : H.eccent cH = 1) :
    Nonempty (G ≃g H) := by
  classical
  let τ : V ≃ W := σ.trans (Equiv.swap (σ cG) cH)
  have hτc : τ cG = cH := by simp [τ]
  refine ⟨⟨τ, ?_⟩⟩
  intro a b
  rw [adj_iff_center_of_eccent_one H hTH cH heccH,
      adj_iff_center_of_eccent_one G hTG cG heccG]
  have ha : τ a = cH ↔ a = cG := by
    rw [← hτc]
    exact τ.apply_eq_iff_eq
  have hb : τ b = cH ↔ b = cG := by
    rw [← hτc]
    exact τ.apply_eq_iff_eq
  simp only [ne_eq, ha, hb]

end StarRadiusOne

theorem main : H1 → H2 → H3 → H4 → OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H3 := by
  intro h1 h2 h3 h4 V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath heven hsub
  obtain ⟨r, cG, cH, hr1, hdiamG, hdiamH, heccG, heccH, huG, huH⟩ :=
    h1 hV G H σ hTG hTH hσ hdeg hnonpath heven hsub
  by_cases hr2 : 2 ≤ r
  · rcases h2 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub with
      hiso | ⟨hdegc, hnoleafG, hnoleafH⟩
    · exact hiso
    · by_cases hG : ∃ C : (G.induce {cG}ᶜ).ConnectedComponent, r < C.supp.ncard
      · exact h4 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub
          hdegc hnoleafG hnoleafH (Or.inl hG)
      · by_cases hH : ∃ D : (H.induce {cH}ᶜ).ConnectedComponent, r < D.supp.ncard
        · exact h4 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub
            hdegc hnoleafG hnoleafH (Or.inr hH)
        · exact h3 hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr2 hdiamG hdiamH heccG heccH huG huH hsub
            hdegc hnoleafG hnoleafH
            (fun C => Nat.le_of_not_lt fun hlt => hG ⟨C, hlt⟩)
            (fun D => Nat.le_of_not_lt fun hlt => hH ⟨D, hlt⟩)
  · have hr_eq : r = 1 := by omega
    subst hr_eq
    simp only [Nat.cast_one] at heccG heccH
    exact iso_of_eccent_one G H σ hTG hTH cG cH heccG heccH

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1
