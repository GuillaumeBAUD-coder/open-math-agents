import OMAReductions.R_Erdos101_erdos_101_R3

-- Reduction Erdos101.erdos_101.R3.H2.R2 of step Erdos101.erdos_101.R3.H2
-- Credit: @Mapika

/-!
# Clean subfamilies of generating anchors

The finite step bounds rich lines by two counts of unordered pairs. The
remaining geometric question concerns only configurations for which every
clean subfamily of anchors leaves a positive fraction of the points outside
its first-round closure. For unrestricted generic plane anchors the full
first-round closure has no collinear triple outside the anchor joins, so
these are excluded even without assuming the remaining geometric step.
The quantitative deletion idea is also used in @RickyDash's note 192815 for
generic conic anchors, where extra Pascal triples occur.
-/

namespace OMA.R_Erdos101_erdos_101_R3_H2_R2

open EuclideanGeometry
open scoped Classical

/-- If every rich line containing three points outside U is a join of G,
charge each rich line to an unordered pair of G or an unordered pair of U. -/
def H1 : Prop :=
  ∀ T G U : Finset ℝ², (∀ L ∈ linesWithPointsFor 4 (T : Set ℝ²),
      3 ≤ ((T.filter fun p => p ∈ L).filter (fun p => p ∉ U)).card →
      ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ line[ℝ,a,b] = L) →
    (linesWithPointsFor 4 (T : Set ℝ²)).ncard ≤ G.card.choose 2 + U.card.choose 2

/-- Every retained subfamily whose closure has no accidental triple on a
rich line must miss a density-dependent fraction of the configuration. -/
def H2 : Prop :=
  ∀ s C : ℕ, 0 < s → ∃ N : ℕ, ∀ T B : Finset ℝ², N ≤ T.card →
    NonCollinearFor 5 (T : Set ℝ²) → B ⊆ T → B.card ^ 2 ≤ C * T.card →
    (∀ p ∈ T, p ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
        a ≠ b ∧ c ≠ d ∧ line[ℝ,a,b] ≠ line[ℝ,c,d] ∧
        p ∈ line[ℝ,a,b] ∧ p ∈ line[ℝ,c,d]) →
    (∀ G ⊆ B,
      let U := T.filter fun p => ¬ (p ∈ G ∨ ∃ a ∈ G, ∃ b ∈ G, ∃ c ∈ G, ∃ d ∈ G,
        a ≠ b ∧ c ≠ d ∧ line[ℝ,a,b] ≠ line[ℝ,c,d] ∧
        p ∈ line[ℝ,a,b] ∧ p ∈ line[ℝ,c,d])
      (∀ L ∈ linesWithPointsFor 4 (T : Set ℝ²),
      3 ≤ ((T.filter fun p => p ∈ L).filter (fun p => p ∉ U)).card →
      ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ line[ℝ,a,b] = L) →
      T.card ^ 2 ≤ s * U.card ^ 2) →
    s * (linesWithPointsFor 4 (T : Set ℝ²)).ncard < T.card ^ 2

-- The following finiteness and pencil identities are from the merged R1.
lemma four_finite (T : Finset ℝ²) :
    (linesWithPointsFor 4 (T : Set ℝ²)).Finite := by
  apply (T.finite_toSet.image2 (fun p q => line[ℝ, p, q]) T.finite_toSet).subset
  rintro L ⟨⟨p, hp, q, hq, _, he⟩, _⟩
  exact ⟨p, hp, q, hq, he⟩

lemma four_card {T : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (T : Set ℝ²)) :
    (T.filter (fun p => p ∈ L)).card = 4 := by
  have he : ((T.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ T := by
    ext p
    simp [and_comm]
  rw [← Set.ncard_coe_finset, he]
  exact hL.2

lemma joins_card (G : Finset ℝ²) : (((G : Finset ℝ²).powersetCard 2).image (fun A : Finset ℝ² => affineSpan ℝ (A : Set ℝ²))).card ≤ G.card.choose 2 :=
  (Finset.card_image_le).trans (by simp)

lemma join_mem {X : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    {a b : ℝ²} (ha : a ∈ X) (hb : b ∈ X) (hne : a ≠ b)
    (hab : line[ℝ,a,b] = L) : L ∈ ((X : Finset ℝ²).powersetCard 2).image (fun A : Finset ℝ² => affineSpan ℝ (A : Set ℝ²)) := by
  apply Finset.mem_image.mpr
  refine ⟨{a,b}, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · simp [hne]
  · simpa using hab

/-- Unconditional unordered-pair charging, for every finite configuration. -/
theorem clean_bound : H1 := by
  intro T G U clean
  let J := fun X : Finset ℝ² => ((X : Finset ℝ²).powersetCard 2).image (fun A : Finset ℝ² => affineSpan ℝ (A : Set ℝ²))
  let rich := (four_finite T).toFinset
  have cover : rich ⊆ J G ∪ J U := by
    intro L hL
    have mem := (four_finite T).mem_toFinset.mp hL
    by_cases h : L ∈ J G
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      let F := T.filter (fun p => p ∈ L)
      have size : F.card = 4 := four_card mem
      have few : ¬ 3 ≤ (F.filter fun p => p ∉ U).card := by
        intro H
        obtain ⟨a, ha, b, hb, hab, he⟩ := clean L mem H
        exact h (join_mem ha hb hab he)
      have sum := Finset.card_filter_add_card_filter_not (s := F) (p := fun p => p ∉ U)
      have two : 1 < (F.filter fun p => ¬ p ∉ U).card := by omega
      obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp two
      obtain ⟨haF, hag⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbF, hbg⟩ := Finset.mem_filter.mp hb
      obtain ⟨_, haL⟩ := Finset.mem_filter.mp haF
      obtain ⟨_, hbL⟩ := Finset.mem_filter.mp hbF
      apply join_mem (not_not.mp hag) (not_not.mp hbg) hne
      obtain ⟨⟨p, _, q, _, _, rfl⟩, _⟩ := mem
      exact affineSpan_pair_eq_of_mem_of_mem_of_ne haL hbL hne
  rw [Set.ncard_eq_toFinset_card _ (four_finite T)]
  exact (Finset.card_le_card cover).trans
    ((Finset.card_union_le ..).trans (Nat.add_le_add (joins_card _) (joins_card _)))

lemma twice_choose_two_le_square (n : ℕ) : 2 * n.choose 2 ≤ n^2 := by
  rw [Nat.choose_two_right]
  have h := Nat.mul_div_le (n*(n-1)) 2
  have h' := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  simpa only [pow_two] using (show 2 * (n * (n-1) / 2) ≤ n * n by omega)

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R3.H2 := by
  intro bound residual s C hs
  obtain ⟨N, take⟩ := residual s C hs
  refine ⟨max N (s*C+1), ?_⟩
  intro T B large cap sub cheap gen
  by_contra! dense
  apply (fun far => (take T B ((le_max_left ..).trans large) cap sub cheap gen far).not_ge dense)
  intro G hGB
  let U := T.filter fun p => ¬ (p ∈ G ∨ ∃ a ∈ G, ∃ b ∈ G, ∃ c ∈ G, ∃ d ∈ G,
        a ≠ b ∧ c ≠ d ∧ line[ℝ,a,b] ≠ line[ℝ,c,d] ∧
        p ∈ line[ℝ,a,b] ∧ p ∈ line[ℝ,c,d])
  change (∀ L ∈ linesWithPointsFor 4 (T : Set ℝ²),
      3 ≤ ((T.filter fun p => p ∈ L).filter (fun p => p ∉ U)).card →
      ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ line[ℝ,a,b] = L) → T.card ^ 2 ≤ s * U.card ^ 2
  intro clean
  have count := bound T G U clean
  have gprice : G.card ^ 2 ≤ C*T.card :=
    (Nat.pow_le_pow_left (Finset.card_le_card hGB) 2).trans cheap
  have nlarge : s*C < T.card := (le_max_right ..).trans large
  have npos : 0 < T.card := Nat.zero_lt_of_lt nlarge
  have terms := Nat.mul_lt_mul_of_pos_right nlarge npos
  have pairs : 2 * (linesWithPointsFor 4 (T : Set ℝ²)).ncard ≤ C*T.card + U.card^2 := by
    have hg := (twice_choose_two_le_square G.card).trans gprice
    have hu := twice_choose_two_le_square U.card
    omega
  have twice := Nat.mul_le_mul_left s pairs
  nlinarith

end OMA.R_Erdos101_erdos_101_R3_H2_R2
