import FormalConjectures.ErdosProblems.«83»

-- Problem: Erdős Problem 83 — extremal
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/83.lean:75 (declaration Erdos83.erdos_83.variants.extremal)
-- Credit: @kenanwienberg (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

private def halfSet (n : ℕ) : Finset (Fin (4 * n)) :=
  univ.map (Fin.castLEEmb (by omega : 2 * n ≤ 4 * n))

private lemma halfSet_card (n : ℕ) : (halfSet n).card = 2 * n := by
  simp [halfSet]

private lemma halfSet_compl_card (n : ℕ) : (halfSet n)ᶜ.card = 2 * n := by
  rw [card_compl, halfSet_card, Fintype.card_fin]
  omega

private lemma card_inter_compl_add (n : ℕ) (A : Finset (Fin (4 * n))) :
    (Aᶜ ∩ halfSet n).card + (A ∩ halfSet n).card = 2 * n := by
  simpa [sdiff_eq_inter_compl, inter_comm, halfSet_card] using card_sdiff_add_card_inter (halfSet n) A

theorem OMA.solution : type_of% @Erdos83.erdos_83.variants.extremal := by
  intro n
  let H := halfSet n
  let U : Finset (Finset (Fin (4 * n))) := univ.powersetCard (2 * n)
  let F := U.filter fun A => n + 1 ≤ (A ∩ H).card
  let E := U.filter fun A => (A ∩ H).card = n
  let G := U.filter fun A => (A ∩ H).card < n
  refine ⟨F, ?_, ?_, ?_⟩
  · intro A hA
    exact (mem_powersetCard.mp (mem_filter.mp hA).1).2
  · intro A hA B hB
    have hAH : n + 1 ≤ (A ∩ H).card := (mem_filter.mp hA).2
    have hBH : n + 1 ≤ (B ∩ H).card := (mem_filter.mp hB).2
    have hcu := card_union_add_card_inter (A ∩ H) (B ∩ H)
    have hunion_le : ((A ∩ H) ∪ (B ∩ H)).card ≤ 2 * n :=
      (card_le_card (union_subset inter_subset_right inter_subset_right)).trans (halfSet_card n).le
    have hinter_le : ((A ∩ H) ∩ (B ∩ H)).card ≤ (A ∩ B).card :=
      card_le_card (inter_subset_inter inter_subset_left inter_subset_left)
    omega
  · have hU_card : U.card = (4 * n).choose (2 * n) := by
      simp [U]
    -- Complementation swaps the families `F` and `G`.
    have hc : ∀ A ∈ U, Aᶜ ∈ U ∧ (Aᶜ ∩ H).card + (A ∩ H).card = 2 * n := fun A hA => by
      rw [mem_powersetCard] at hA ⊢
      exact ⟨⟨subset_univ _, by rw [card_compl, hA.2, Fintype.card_fin]; omega⟩, card_inter_compl_add n A⟩
    have hFG : F.card = G.card := by
      refine card_bij (fun A _ => Aᶜ) (fun A hA => ?_) (fun A _ B _ h => compl_injective h)
        (fun B hB => ⟨Bᶜ, ?_, compl_compl B⟩)
      · simp only [F, G, mem_filter] at hA ⊢
        have := hc A hA.1
        exact ⟨this.1, by omega⟩
      · simp only [F, G, mem_filter] at hB ⊢
        have := hc B hB.1
        exact ⟨this.1, by omega⟩
    have hE_card : E.card = (2 * n).choose n ^ 2 := by
      have hP : (H.powersetCard n ×ˢ Hᶜ.powersetCard n).card = (2 * n).choose n ^ 2 := by
        rw [card_product, card_powersetCard, card_powersetCard, halfSet_card, halfSet_compl_card, sq]
      -- A pair of halves is recovered from its union by intersecting with `H` and `Hᶜ`.
      have key : ∀ p ∈ H.powersetCard n ×ˢ Hᶜ.powersetCard n,
          (p.1 ∪ p.2) ∩ H = p.1 ∧ (p.1 ∪ p.2) ∩ Hᶜ = p.2 ∧ (p.1 ∪ p.2).card = 2 * n := by
        intro p hp
        simp only [mem_product, mem_powersetCard] at hp
        obtain ⟨⟨h1, c1⟩, h2, c2⟩ := hp
        refine ⟨?_, ?_, by rw [card_union_of_disjoint (disjoint_compl_right.mono h1 h2), c1, c2]; omega⟩ <;>
          ext x <;> have := @h1 x <;> have := @h2 x <;> simp only [mem_inter, mem_union, mem_compl] at * <;>
          tauto
      rw [← hP]
      symm
      refine card_bij (fun p _ => p.1 ∪ p.2) (fun p hp => ?_) (fun p hp q hq h => ?_) (fun A hA => ?_)
      · obtain ⟨h1, -, h3⟩ := key p hp
        simp only [E, U, mem_filter, mem_powersetCard]
        exact ⟨⟨subset_univ _, h3⟩, by rw [h1]; exact (mem_powersetCard.1 (mem_product.1 hp).1).2⟩
      · obtain ⟨hp1, hp2, -⟩ := key p hp
        obtain ⟨hq1, hq2, -⟩ := key q hq
        exact Prod.ext (by rw [← hp1, h, hq1]) (by rw [← hp2, h, hq2])
      · simp only [E, U, mem_filter, mem_powersetCard] at hA
        have := card_inter_add_card_sdiff A H
        rw [sdiff_eq_inter_compl] at this
        refine ⟨(A ∩ H, A ∩ Hᶜ), ?_, by rw [← inter_union_distrib_left, union_compl, inter_univ]⟩
        simp only [mem_product, mem_powersetCard]
        exact ⟨⟨inter_subset_right, hA.2⟩, inter_subset_right, by omega⟩
    -- `U` splits into `F`, `E` and `G` by the size of `A ∩ H`.
    have h1 := card_filter_add_card_filter_not (s := U) fun A => n + 1 ≤ (A ∩ H).card
    have h2 := card_filter_add_card_filter_not (s := U.filter fun A => ¬ n + 1 ≤ (A ∩ H).card)
      fun A => (A ∩ H).card = n
    have e1 : (U.filter fun A => ¬ n + 1 ≤ (A ∩ H).card ∧ (A ∩ H).card = n) = E :=
      filter_congr fun A _ => by omega
    have e2 : (U.filter fun A => ¬ n + 1 ≤ (A ∩ H).card ∧ ¬ (A ∩ H).card = n) = G :=
      filter_congr fun A _ => by omega
    rw [filter_filter, filter_filter, e1, e2] at h2
    change F.card + _ = _ at h1
    omega
