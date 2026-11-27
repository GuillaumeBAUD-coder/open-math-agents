import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1

-- Reduction ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4.R1 of step ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4
-- Credit: @green-notes

/-!
Splits the bicentral (odd-diameter) non-path tree reconstruction step `tree.R1.H4` into four
independent mathematical subgoals:
1. `H1`: Diameter preservation (`3 ≤ G.diam` and `G.diam = H.diam`) for non-path hypomorphic trees
   via Kelly's subgraph-counting hypothesis on a diametral path.
2. `H2`: Jordan's bicenter decomposition for any finite tree of odd diameter `2 * r + 1 ≥ 3`:
   existence of the central edge `{c₁, c₂} = T.center`, metric partition into two trees of height
   at most `r`, and distance factorization across `{c₁, c₂}`.
3. `H3`: Kelly's non-path-limb reconstruction when all four central limbs have size `≥ r + 2`
   (counting induced subtrees of diameter `2 * r + 1` with one limb a path of length `r`).
4. `H4`: Kelly's path-limb reconstruction when at least one central limb has size `≤ r + 1`
   (i.e. is a path of length `r`).
-/

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1

open SimpleGraph ReconstructionConjecture

def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      Odd G.diam →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      3 ≤ G.diam ∧ G.diam = H.diam

def H2 : Prop :=
  ∀ {U : Type} [Fintype U] (T : SimpleGraph U),
    T.IsTree → 3 ≤ T.diam → Odd T.diam →
    ∃ c₁ c₂ : U, T.Adj c₁ c₂ ∧
      T.center = {c₁, c₂} ∧
      (∀ x : U, T.dist x c₁ ≠ T.dist x c₂) ∧
      (∀ x : U, T.dist x c₁ < T.dist x c₂ → T.dist x c₁ ≤ (T.diam - 1) / 2) ∧
      (∀ x : U, T.dist x c₂ < T.dist x c₁ → T.dist x c₂ ≤ (T.diam - 1) / 2) ∧
      (T.induce {x : U | T.dist x c₁ < T.dist x c₂}).IsTree ∧
      (T.induce {x : U | T.dist x c₂ < T.dist x c₁}).IsTree ∧
      (∀ x y : U, T.dist x c₁ < T.dist x c₂ → T.dist y c₂ < T.dist y c₁ →
        T.dist x y = T.dist x c₁ + 1 + T.dist c₂ y)

def H3 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    G.IsTree → H.IsTree → Fintype.card V = Fintype.card W →
    ∀ r : ℕ, 1 ≤ r → G.diam = 2 * r + 1 → H.diam = 2 * r + 1 →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      ∀ c₁ c₂ : V, G.Adj c₁ c₂ →
        (∀ x : V, G.dist x c₁ ≠ G.dist x c₂) →
        (∀ x : V, G.dist x c₁ < G.dist x c₂ → G.dist x c₁ ≤ r) →
        (∀ x : V, G.dist x c₂ < G.dist x c₁ → G.dist x c₂ ≤ r) →
        (G.induce {x : V | G.dist x c₁ < G.dist x c₂}).IsTree →
        (G.induce {x : V | G.dist x c₂ < G.dist x c₁}).IsTree →
        (∀ x y : V, G.dist x c₁ < G.dist x c₂ → G.dist y c₂ < G.dist y c₁ →
          G.dist x y = G.dist x c₁ + 1 + G.dist c₂ y) →
        r + 2 ≤ {x : V | G.dist x c₁ < G.dist x c₂}.ncard →
        r + 2 ≤ {x : V | G.dist x c₂ < G.dist x c₁}.ncard →
      ∀ d₁ d₂ : W, H.Adj d₁ d₂ →
        (∀ y : W, H.dist y d₁ ≠ H.dist y d₂) →
        (∀ y : W, H.dist y d₁ < H.dist y d₂ → H.dist y d₁ ≤ r) →
        (∀ y : W, H.dist y d₂ < H.dist y d₁ → H.dist y d₂ ≤ r) →
        (H.induce {y : W | H.dist y d₁ < H.dist y d₂}).IsTree →
        (H.induce {y : W | H.dist y d₂ < H.dist y d₁}).IsTree →
        (∀ x y : W, H.dist x d₁ < H.dist x d₂ → H.dist y d₂ < H.dist y d₁ →
          H.dist x y = H.dist x d₁ + 1 + H.dist d₂ y) →
        r + 2 ≤ {y : W | H.dist y d₁ < H.dist y d₂}.ncard →
        r + 2 ≤ {y : W | H.dist y d₂ < H.dist y d₁}.ncard →
      Nonempty (G ≃g H)

def H4 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W),
      G.IsTree → H.IsTree →
      (∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) →
      (∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard) →
      (∃ v : V, 3 ≤ (G.neighborSet v).ncard) →
      ∀ r : ℕ, 1 ≤ r → G.diam = 2 * r + 1 → H.diam = 2 * r + 1 →
      (∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card V →
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
          {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard) →
      ∀ c₁ c₂ : V, G.Adj c₁ c₂ → G.center = {c₁, c₂} →
        (∀ x : V, G.dist x c₁ ≠ G.dist x c₂) →
        (∀ x : V, G.dist x c₁ < G.dist x c₂ → G.dist x c₁ ≤ r) →
        (∀ x : V, G.dist x c₂ < G.dist x c₁ → G.dist x c₂ ≤ r) →
        (G.induce {x : V | G.dist x c₁ < G.dist x c₂}).IsTree →
        (G.induce {x : V | G.dist x c₂ < G.dist x c₁}).IsTree →
        (∀ x y : V, G.dist x c₁ < G.dist x c₂ → G.dist y c₂ < G.dist y c₁ →
          G.dist x y = G.dist x c₁ + 1 + G.dist c₂ y) →
      ∀ d₁ d₂ : W, H.Adj d₁ d₂ → H.center = {d₁, d₂} →
        (∀ y : W, H.dist y d₁ ≠ H.dist y d₂) →
        (∀ y : W, H.dist y d₁ < H.dist y d₂ → H.dist y d₁ ≤ r) →
        (∀ y : W, H.dist y d₂ < H.dist y d₁ → H.dist y d₂ ≤ r) →
        (H.induce {y : W | H.dist y d₁ < H.dist y d₂}).IsTree →
        (H.induce {y : W | H.dist y d₂ < H.dist y d₁}).IsTree →
        (∀ x y : W, H.dist x d₁ < H.dist x d₂ → H.dist y d₂ < H.dist y d₁ →
          H.dist x y = H.dist x d₁ + 1 + H.dist d₂ y) →
      ({x : V | G.dist x c₁ < G.dist x c₂}.ncard ≤ r + 1 ∨
       {x : V | G.dist x c₂ < G.dist x c₁}.ncard ≤ r + 1 ∨
       {y : W | H.dist y d₁ < H.dist y d₂}.ncard ≤ r + 1 ∨
       {y : W | H.dist y d₂ < H.dist y d₁}.ncard ≤ r + 1) →
      Nonempty (G ≃g H)

theorem main : H1 → H2 → H3 → H4 → OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1.H4 := by
  intro h1 h2 h3 h4 V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath hodd hkelly
  obtain ⟨hd3, hd_eq⟩ := h1 hV G H σ hTG hTH hdeg hnonpath hodd hkelly
  have hoddH : Odd H.diam := hd_eq ▸ hodd
  have hd3H : 3 ≤ H.diam := hd_eq ▸ hd3
  obtain ⟨c₁, c₂, hc_adj, hc_ctr, hc_ne, hc_le1, hc_le2, hc_t1, hc_t2, hc_dist⟩ :=
    h2 G hTG hd3 hodd
  obtain ⟨d₁, d₂, hd_adj, hd_ctr, hd_ne, hd_le1, hd_le2, hd_t1, hd_t2, hd_dist⟩ :=
    h2 H hTH hd3H hoddH
  set r := (G.diam - 1) / 2
  have hr1 : 1 ≤ r := by omega
  have hGdiam : G.diam = 2 * r + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hHdiam : H.diam = 2 * r + 1 := by
    rw [← hd_eq]
    exact hGdiam
  have hr_eqH : (H.diam - 1) / 2 = r := by rw [← hd_eq]
  rw [hr_eqH] at hd_le1 hd_le2
  by_cases hsmall :
      {x : V | G.dist x c₁ < G.dist x c₂}.ncard ≤ r + 1 ∨
      {x : V | G.dist x c₂ < G.dist x c₁}.ncard ≤ r + 1 ∨
      {y : W | H.dist y d₁ < H.dist y d₂}.ncard ≤ r + 1 ∨
      {y : W | H.dist y d₂ < H.dist y d₁}.ncard ≤ r + 1
  · exact h4 hV G H σ hTG hTH hσ hdeg hnonpath r hr1 hGdiam hHdiam hkelly
      c₁ c₂ hc_adj hc_ctr hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist
      d₁ d₂ hd_adj hd_ctr hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist hsmall
  · push Not at hsmall
    have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
    exact h3 G H hTG hTH hcard r hr1 hGdiam hHdiam hkelly
      c₁ c₂ hc_adj hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist (by omega) (by omega)
      d₁ d₂ hd_adj hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist (by omega) (by omega)

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
