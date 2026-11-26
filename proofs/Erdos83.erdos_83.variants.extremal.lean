import FormalConjectures.ErdosProblems.«83»

-- Problem: Erdős Problem 83 — extremal
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/83.lean:75 (declaration Erdos83.erdos_83.variants.extremal)
-- Credit: @kenanwienberg (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

private def halfSet (n : ℕ) : Finset (Fin (4 * n)) :=
  univ.filter fun i : Fin (4 * n) => i.val < 2 * n

private lemma halfSet_card (n : ℕ) : (halfSet n).card = 2 * n := by
  have h : halfSet n = (univ : Finset (Fin (2 * n))).map
      ⟨fun i : Fin (2 * n) => (⟨i.val, by omega⟩ : Fin (4 * n)),
       fun a b hab => Fin.ext (congrArg (Fin.val : Fin (4 * n) → ℕ) hab)⟩ := by
    ext x
    simp only [halfSet, mem_filter, mem_univ, true_and, mem_map]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [h, card_map, card_fin]

private lemma halfSet_compl_card (n : ℕ) : (halfSet n)ᶜ.card = 2 * n := by
  have h := card_compl_add_card (halfSet n)
  rw [halfSet_card, Fintype.card_fin] at h
  omega

private lemma card_inter_compl_add (n : ℕ) (A : Finset (Fin (4 * n))) :
    (Aᶜ ∩ halfSet n).card + (A ∩ halfSet n).card = 2 * n := by
  have hdisj : Disjoint (Aᶜ ∩ halfSet n) (A ∩ halfSet n) := by
    rw [disjoint_left]
    intro x hx1 hx2
    simp only [mem_inter, mem_compl] at hx1 hx2
    exact hx1.1 hx2.1
  have hunion : (Aᶜ ∩ halfSet n) ∪ (A ∩ halfSet n) = halfSet n := by
    ext x
    simp only [mem_union, mem_inter, mem_compl]
    by_cases hx : x ∈ A <;> simp [hx]
  rw [← card_union_of_disjoint hdisj, hunion, halfSet_card]

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
    have hunion_le : ((A ∩ H) ∪ (B ∩ H)).card ≤ 2 * n := by
      rw [← halfSet_card n]
      exact card_le_card (union_subset inter_subset_right inter_subset_right)
    have hinter_le : ((A ∩ H) ∩ (B ∩ H)).card ≤ (A ∩ B).card := by
      apply card_le_card
      intro x hx
      simp only [mem_inter] at hx ⊢
      exact ⟨hx.1.1, hx.2.1⟩
    omega
  · have hU_card : U.card = (4 * n).choose (2 * n) := by
      simp [U]
    have hFG : F.card = G.card := by
      refine card_bij (fun A _ => Aᶜ) ?_ ?_ ?_
      · intro A hA
        have hAU : A ∈ U := (mem_filter.mp hA).1
        have hAcard : A.card = 2 * n := (mem_powersetCard.mp hAU).2
        have hAH : n + 1 ≤ (A ∩ halfSet n).card := (mem_filter.mp hA).2
        have hcompl_card : Aᶜ.card = 2 * n := by
          have hc := card_compl_add_card A
          rw [hAcard, Fintype.card_fin] at hc
          omega
        have hsum := card_inter_compl_add n A
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hcompl_card⟩, ?_⟩
        change (Aᶜ ∩ halfSet n).card < n
        omega
      · intro A _ B _ hAB
        simpa using congrArg Compl.compl hAB
      · intro B hB
        have hBU : B ∈ U := (mem_filter.mp hB).1
        have hBcard : B.card = 2 * n := (mem_powersetCard.mp hBU).2
        have hBH : (B ∩ halfSet n).card < n := (mem_filter.mp hB).2
        have hcompl_card : Bᶜ.card = 2 * n := by
          have hc := card_compl_add_card B
          rw [hBcard, Fintype.card_fin] at hc
          omega
        have hsum := card_inter_compl_add n B
        refine ⟨Bᶜ, ?_, compl_compl B⟩
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hcompl_card⟩, ?_⟩
        change n + 1 ≤ (Bᶜ ∩ halfSet n).card
        omega
    have hE_card : E.card = (2 * n).choose n ^ 2 := by
      have hP : (H.powersetCard n ×ˢ Hᶜ.powersetCard n).card = (2 * n).choose n ^ 2 := by
        rw [card_product, card_powersetCard, card_powersetCard, halfSet_card, halfSet_compl_card, sq]
      rw [← hP]
      symm
      refine card_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hp1, hp2⟩ := mem_product.mp hp
        obtain ⟨h1sub, h1card⟩ := mem_powersetCard.mp hp1
        obtain ⟨h2sub, h2card⟩ := mem_powersetCard.mp hp2
        have hdisj : Disjoint p.1 p.2 := disjoint_compl_right.mono h1sub h2sub
        have hcard : (p.1 ∪ p.2).card = 2 * n := by
          rw [card_union_of_disjoint hdisj, h1card, h2card]
          omega
        have hinter : (p.1 ∪ p.2) ∩ H = p.1 := by
          ext x
          simp only [mem_inter, mem_union]
          constructor
          · rintro ⟨hx1 | hx2, hxH⟩
            · exact hx1
            · exact absurd hxH (mem_compl.mp (h2sub hx2))
          · intro hx1
            exact ⟨Or.inl hx1, h1sub hx1⟩
        exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, by rw [hinter, h1card]⟩
      · intro p hp q hq hpq
        obtain ⟨hp1, hp2⟩ := mem_product.mp hp
        obtain ⟨h1sub, _⟩ := mem_powersetCard.mp hp1
        obtain ⟨h2sub, _⟩ := mem_powersetCard.mp hp2
        obtain ⟨hq1, hq2⟩ := mem_product.mp hq
        obtain ⟨h3sub, _⟩ := mem_powersetCard.mp hq1
        obtain ⟨h4sub, _⟩ := mem_powersetCard.mp hq2
        have hp_H : (p.1 ∪ p.2) ∩ H = p.1 := by
          ext x
          simp only [mem_inter, mem_union]
          exact ⟨fun ⟨h, hxH⟩ => h.resolve_right fun hx2 => mem_compl.mp (h2sub hx2) hxH,
            fun hx1 => ⟨Or.inl hx1, h1sub hx1⟩⟩
        have hq_H : (q.1 ∪ q.2) ∩ H = q.1 := by
          ext x
          simp only [mem_inter, mem_union]
          exact ⟨fun ⟨h, hxH⟩ => h.resolve_right fun hx2 => mem_compl.mp (h4sub hx2) hxH,
            fun hx1 => ⟨Or.inl hx1, h3sub hx1⟩⟩
        have hp_Hc : (p.1 ∪ p.2) ∩ Hᶜ = p.2 := by
          ext x
          simp only [mem_inter, mem_union]
          exact ⟨fun ⟨h, hxHc⟩ => h.resolve_left fun hx1 => mem_compl.mp hxHc (h1sub hx1),
            fun hx2 => ⟨Or.inr hx2, h2sub hx2⟩⟩
        have hq_Hc : (q.1 ∪ q.2) ∩ Hᶜ = q.2 := by
          ext x
          simp only [mem_inter, mem_union]
          exact ⟨fun ⟨h, hxHc⟩ => h.resolve_left fun hx1 => mem_compl.mp hxHc (h3sub hx1),
            fun hx2 => ⟨Or.inr hx2, h4sub hx2⟩⟩
        exact Prod.ext (by rw [← hp_H, hpq, hq_H]) (by rw [← hp_Hc, hpq, hq_Hc])
      · intro A hA
        have hAU : A ∈ U := (mem_filter.mp hA).1
        have hAcard : A.card = 2 * n := (mem_powersetCard.mp hAU).2
        have hAH : (A ∩ H).card = n := (mem_filter.mp hA).2
        have hunion : (A ∩ H) ∪ (A ∩ Hᶜ) = A := by
          ext x
          simp only [mem_union, mem_inter, mem_compl]
          by_cases hx : x ∈ H <;> simp [hx]
        have hdisj : Disjoint (A ∩ H) (A ∩ Hᶜ) := by
          rw [disjoint_left]
          intro x hx1 hx2
          exact (mem_compl.mp (mem_inter.mp hx2).2) (mem_inter.mp hx1).2
        have hAHc : (A ∩ Hᶜ).card = n := by
          have := card_union_of_disjoint hdisj
          rw [hunion, hAcard, hAH] at this
          omega
        refine ⟨(A ∩ H, A ∩ Hᶜ), ?_, hunion⟩
        exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right, hAH⟩,
          mem_powersetCard.mpr ⟨inter_subset_right, hAHc⟩⟩
    have hdisj_FE : Disjoint F E := by
      rw [disjoint_left]
      intro A hAF hAE
      have h1 := (mem_filter.mp hAF).2
      have h2 := (mem_filter.mp hAE).2
      omega
    have hdisj_FE_G : Disjoint (F ∪ E) G := by
      rw [disjoint_left]
      intro A hAFE hAG
      have h3 := (mem_filter.mp hAG).2
      rcases mem_union.mp hAFE with hAF | hAE
      · have h1 := (mem_filter.mp hAF).2; omega
      · have h2 := (mem_filter.mp hAE).2; omega
    have hunion_U : (F ∪ E) ∪ G = U := by
      ext A
      simp only [mem_union, mem_filter, F, E, G]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h1 : n + 1 ≤ (A ∩ H).card
        · exact Or.inl (Or.inl ⟨h, h1⟩)
        · by_cases h2 : (A ∩ H).card = n
          · exact Or.inl (Or.inr ⟨h, h2⟩)
          · exact Or.inr ⟨h, by omega⟩
    have htotal : U.card = F.card + E.card + G.card := by
      rw [← hunion_U, card_union_of_disjoint hdisj_FE_G, card_union_of_disjoint hdisj_FE]
    omega
