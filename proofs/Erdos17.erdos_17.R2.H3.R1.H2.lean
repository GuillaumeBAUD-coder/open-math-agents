import OMAReductions.R_Erdos17_erdos_17_R2_H3_R1

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: greedy thinning: repeatedly take the minimum m and discard elements below m + d; each step removes at most d elements, so A.card <= d * S.card with d = 2k^2.

namespace OMA.Erdos17H2

theorem greedy (d : ℕ) (hd : 1 ≤ d) : ∀ n : ℕ, ∀ A : Finset ℕ, A.card ≤ n →
    ∃ S : Finset ℕ, S ⊆ A ∧ (∀ p ∈ S, ∀ q ∈ S, p < q → p + d ≤ q) ∧ A.card ≤ d * S.card := by
  intro n
  induction n with
  | zero =>
    intro A hA
    refine ⟨∅, by simp, by simp, ?_⟩
    simp only [Finset.card_empty, Nat.mul_zero]; omega
  | succ n ih =>
    intro A hA
    rcases A.eq_empty_or_nonempty with h | h
    · subst h; exact ⟨∅, by simp, by simp, by simp⟩
    · have hmA : A.min' h ∈ A := A.min'_mem h
      have hle : ∀ x ∈ A, A.min' h ≤ x := fun x hx => A.min'_le x hx
      have hlt : (A.filter (fun x => A.min' h + d ≤ x)).card < A.card :=
        Finset.card_lt_card (Finset.filter_ssubset.2 ⟨A.min' h, hmA, by omega⟩)
      obtain ⟨S, hSB, hSsep, hScard⟩ := ih (A.filter (fun x => A.min' h + d ≤ x)) (by omega)
      have hmS : A.min' h ∉ S := by
        intro hm
        have := hSB hm
        rw [Finset.mem_filter] at this; omega
      refine ⟨insert (A.min' h) S, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_iff.2 ⟨hmA, hSB.trans (Finset.filter_subset _ _)⟩
      · intro p hp q hq hpq
        rw [Finset.mem_insert] at hp hq
        rcases hp with rfl | hp <;> rcases hq with rfl | hq
        · omega
        · have := hSB hq; rw [Finset.mem_filter] at this; omega
        · have := hSB hp; rw [Finset.mem_filter] at this; omega
        · exact hSsep p hp q hq hpq
      · have hsplit := Finset.card_filter_add_card_filter_not
          (s := A) (fun x => A.min' h + d ≤ x)
        have hsub : A.filter (fun x => ¬ (A.min' h + d ≤ x)) ⊆ Finset.Ico (A.min' h) (A.min' h + d) := by
          intro x hx
          simp only [Finset.mem_filter] at hx
          have := hle x hx.1
          simp only [Finset.mem_Ico]; omega
        have h2 := Finset.card_le_card hsub
        simp only [Nat.card_Ico] at h2
        rw [Finset.card_insert_of_notMem hmS]
        rw [Nat.mul_succ]
        omega

theorem main : ∀ k : ℕ, ∀ A : Finset ℕ,
    (∀ p ∈ A, k ^ 4 ≤ p ∧ p ≤ 2 * k ^ 4) →
      4 * k ^ 3 < A.card →
        ∃ S : Finset ℕ, S ⊆ A ∧ k < S.card ∧
          ∀ p ∈ S, ∀ q ∈ S, p < q → p + 2 * k ^ 2 ≤ q := by
  intro k A _ hA
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hA
    obtain ⟨a, ha⟩ := hA
    refine ⟨{a}, by simpa using ha, by simp, ?_⟩
    intro p hp q hq hpq
    simp at hp hq; omega
  · have hd : 1 ≤ 2 * k ^ 2 := by
      have : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
      omega
    obtain ⟨S, hSA, hsep, hcard⟩ := greedy (2 * k ^ 2) hd A.card A le_rfl
    refine ⟨S, hSA, ?_, hsep⟩
    by_contra hc
    rw [not_lt] at hc
    have h1 := Nat.mul_le_mul_left (2 * k ^ 2) hc
    have h3 : 2 * k ^ 2 * k ≤ 4 * k ^ 3 := by
      have : k ^ 3 = k ^ 2 * k := by ring
      rw [this]; nlinarith
    have h4 : 0 < k ^ 3 := by positivity
    have h5 : 2 * k ^ 2 * k = 2 * k ^ 3 := by ring
    omega

end OMA.Erdos17H2

theorem OMA.solution : OMA.R_Erdos17_erdos_17_R2_H3_R1.H2 := by
  unfold OMA.R_Erdos17_erdos_17_R2_H3_R1.H2
  exact OMA.Erdos17H2.main
