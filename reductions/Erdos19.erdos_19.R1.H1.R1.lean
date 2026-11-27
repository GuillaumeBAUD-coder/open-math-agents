import OMAReductions.R_Erdos19_erdos_19_R1

/-! Complete the pair-containing branch to linear spaces and separate the bounded cases. -/

namespace OMA.R_Erdos19_erdos_19_R1_H1_R1

open scoped Classical

private theorem intersection_le_one {n : ℕ} {a b : Finset (Fin n)}
    (ha : a.card = 2) (h : ¬ a ⊆ b) : (a ∩ b).card ≤ 1 := by
  by_contra! hv
  have hle : a.card ≤ (a ∩ b).card := by omega
  have heq : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
  exact h (heq ▸ Finset.inter_subset_right)

/-- Preserve the original blocks and cover each unused pair with a two-point block. -/
private theorem complete_family {n : ℕ} (K : Finset (Finset (Fin n)))
    (size : ∀ a ∈ K, 2 ≤ a.card)
    (linear : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → (a ∩ b).card ≤ 1) :
    ∃ L : Finset (Finset (Fin n)), K ⊆ L ∧ (∀ a ∈ L, 2 ≤ a.card) ∧
      (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) ∧
      (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) ∧
      (∀ a ∈ L, 3 ≤ a.card → a ∈ K) := by
  let extra := ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
    (fun p => ∀ e ∈ K, ¬ p ⊆ e)
  let L := K ∪ extra
  have classify : ∀ a ∈ L, a ∈ K ∨ (a.card = 2 ∧ ∀ e ∈ K, ¬ a ⊆ e) := by
    intro a ha
    rcases Finset.mem_union.mp ha with old | fresh
    · exact Or.inl old
    · obtain ⟨pairSize, uncovered⟩ := Finset.mem_filter.mp fresh
      exact Or.inr ⟨(Finset.mem_powersetCard.mp pairSize).2, uncovered⟩
  refine ⟨L, fun _ he => Finset.mem_union_left _ he, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases classify a ha with old | ⟨pairSize, _⟩
    · exact size a old
    · simp [pairSize]
  · intro a ha b hb hab
    rcases classify a ha with oldA | ⟨sizeA, uncoveredA⟩
    · rcases classify b hb with oldB | ⟨sizeB, uncoveredB⟩
      · exact linear a oldA b oldB hab
      · rw [Finset.inter_comm]
        exact intersection_le_one sizeB (uncoveredB a oldA)
    · rcases classify b hb with oldB | ⟨sizeB, _⟩
      · exact intersection_le_one sizeA (uncoveredA b oldB)
      · apply intersection_le_one sizeA
        intro sub
        exact hab (Finset.eq_of_subset_of_card_le sub (by rw [sizeA, sizeB]))
  · intro i j hij
    by_cases covered : ∃ e ∈ K, i ∈ e ∧ j ∈ e
    · obtain ⟨e, he, hi, hj⟩ := covered
      exact ⟨e, Finset.mem_union_left _ he, hi, hj⟩
    · refine ⟨{i, j}, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, ?_⟩),
        by simp, by simp⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hij⟩
      · intro e he sub
        exact covered ⟨e, he, sub (by simp), sub (by simp)⟩
  · intro a ha large
    rcases classify a ha with old | ⟨pairSize, _⟩
    · exact old
    · omega

/-- The published small orders and the checked families on thirteen points. -/
def H1 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    (n ≤ 12 ∨ (n = 13 ∧ (L.card ≤ 32 ∨ 55 ≤ L.card ∨
      ((L.filter fun b => 3 ≤ b.card).biUnion id).card ≤ 11 ∨
      (∃ b ∈ L, 7 ≤ b.card) ∨ 20 ≤ (L.filter fun b => 3 ≤ b.card).card))) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Complete spaces at any order with at most six points outside a block. -/
def H2 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    (∃ b ∈ L, n ≤ b.card + 6) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- The remaining completed spaces with a potential critical subfamily. -/
def H3 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    ¬ (n ≤ 12 ∨ (n = 13 ∧ (L.card ≤ 32 ∨ 55 ≤ L.card ∨
      ((L.filter fun b => 3 ≤ b.card).biUnion id).card ≤ 11 ∨
      (∃ b ∈ L, 7 ≤ b.card) ∨ 20 ≤ (L.filter fun b => 3 ≤ b.card).card))) →
    (¬ ∃ b ∈ L, n ≤ b.card + 6) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

theorem main : H1 → H2 → H3 → OMA.R_Erdos19_erdos_19_R1.H1 := by
  intro h1 h2 h3 n K _ _ size linear degree _ _
  obtain ⟨L, sub, lsize, llinear, covers, oldLarge⟩ := complete_family K size linear
  have core : ∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card := by
    exact ⟨K, sub, oldLarge, degree⟩
  have colorable :
      ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
    by_cases tested : (n ≤ 12 ∨ (n = 13 ∧ (L.card ≤ 32 ∨ 55 ≤ L.card ∨
      ((L.filter fun b => 3 ≤ b.card).biUnion id).card ≤ 11 ∨
      (∃ b ∈ L, 7 ≤ b.card) ∨ 20 ≤ (L.filter fun b => 3 ≤ b.card).card)))
    · exact h1 n L lsize llinear covers core tested
    · by_cases near : ∃ b ∈ L, n ≤ b.card + 6
      · exact h2 n L lsize llinear covers core near
      · exact h3 n L lsize llinear covers core tested near
  obtain ⟨c, proper⟩ := colorable
  let lift : K → L := fun a => ⟨a.val, sub a.property⟩
  refine ⟨c ∘ lift, ?_⟩
  intro a b different meet
  apply proper (lift a) (lift b) ?_ meet
  intro h
  exact different (Subtype.ext (congrArg (fun x : L => x.val) h))

end OMA.R_Erdos19_erdos_19_R1_H1_R1
