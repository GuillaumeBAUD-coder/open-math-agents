import OMAReductions.R_oeis_a004109_R1

/-!
# Proof of `oeis-a004109.R1.H2`

We show that the count `a n` of connected cubic labeled graphs on `Fin (2 * n)` is at most the
total count `g n` of cubic labeled graphs, and for `0 < n` the disconnected cubic graphs satisfy
`g n - a n ≤ ∑ i ∈ Icc 1 (n / 2), (2 * n).choose (2 * i) * g i * g (n - i)`.

For any disconnected cubic graph `G` on `Fin (2 * n)`, the reachable component of vertex `0` or its
complement gives a nonempty proper closed vertex subset `S` with `S.card ≤ n`. Counting directed
edges inside `S` by symmetry shows `3 * S.card` is even, so `S.card = 2 * i` with `1 ≤ i ≤ n / 2`.
Restricting `G` to `S` and `univ \ S` injects closed-`S` cubic graphs into `R i ×ˢ R (n - i)`.
-/

-- Step oeis-a004109.R1.H2: hypothesis H2 of reduction oeis-a004109.R1
-- Credit: @umarsxlim

namespace OeisA004109H2

open Finset SimpleGraph
open scoped Classical BigOperators

noncomputable def cubicGraphs (n : ℕ) : Finset (SimpleGraph (Fin (2 * n))) :=
  univ.filter fun G : SimpleGraph (Fin (2 * n)) => ∀ v, (G.neighborFinset v).card = 3

noncomputable def connCubicGraphs (n : ℕ) : Finset (SimpleGraph (Fin (2 * n))) :=
  univ.filter fun G : SimpleGraph (Fin (2 * n)) =>
    G.Connected ∧ ∀ v, (G.neighborFinset v).card = 3

noncomputable def disconnCubicGraphs (n : ℕ) : Finset (SimpleGraph (Fin (2 * n))) :=
  univ.filter fun G : SimpleGraph (Fin (2 * n)) =>
    ¬ G.Connected ∧ ∀ v, (G.neighborFinset v).card = 3

noncomputable def closedCubicGraphs (n : ℕ) (S : Finset (Fin (2 * n))) :
    Finset (SimpleGraph (Fin (2 * n))) :=
  (cubicGraphs n).filter fun G => ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S

lemma a_eq_card (n : ℕ) : OMA.S_oeis_a004109.a n = (connCubicGraphs n).card := by
  unfold OMA.S_oeis_a004109.a connCubicGraphs
  congr 1

lemma conn_subset_cubic (n : ℕ) : connCubicGraphs n ⊆ cubicGraphs n := by
  intro G hG
  simp only [connCubicGraphs, cubicGraphs, mem_filter, mem_univ, true_and] at hG ⊢
  exact hG.2

lemma cubic_sdiff_conn (n : ℕ) : cubicGraphs n \ connCubicGraphs n = disconnCubicGraphs n := by
  ext G
  simp only [mem_sdiff, cubicGraphs, connCubicGraphs, disconnCubicGraphs, mem_filter, mem_univ,
    true_and]
  tauto

lemma sub_card_eq_disconn (n : ℕ) :
    (cubicGraphs n).card - (connCubicGraphs n).card = (disconnCubicGraphs n).card := by
  rw [← cubic_sdiff_conn n, Finset.card_sdiff_of_subset (conn_subset_cubic n)]

lemma closed_compl {n : ℕ} {G : SimpleGraph (Fin (2 * n))} {S : Finset (Fin (2 * n))}
    (hS : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S) :
    ∀ u ∈ univ \ S, ∀ w, G.Adj u w → w ∈ univ \ S := by
  intro u hu w huw
  simp only [mem_sdiff, mem_univ, true_and] at hu ⊢
  intro hw
  exact hu (hS w hw u huw.symm)

lemma even_card_of_closed_cubic {n : ℕ} {G : SimpleGraph (Fin (2 * n))}
    (hdeg : ∀ v, (G.neighborFinset v).card = 3) {S : Finset (Fin (2 * n))}
    (hS : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S) : Even S.card := by
  let E := (S ×ˢ S).filter (fun p : Fin (2 * n) × Fin (2 * n) => G.Adj p.1 p.2)
  have hE_eq : E.card = 3 * S.card := by
    dsimp only [E]
    rw [Finset.card_filter, Finset.sum_product]
    have hinner : ∀ u ∈ S,
        ∑ w ∈ S, (if G.Adj u w then 1 else 0) = 3 := by
      intro u hu
      rw [← Finset.card_filter]
      have hf : S.filter (fun w => G.Adj u w) = G.neighborFinset u := by
        ext w
        simp only [mem_filter, mem_neighborFinset]
        exact ⟨fun h => h.2, fun h => ⟨hS u hu w h, h⟩⟩
      rw [hf, hdeg u]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  let Elt := E.filter (fun p => p.1 < p.2)
  let Egt := E.filter (fun p => p.2 < p.1)
  have hdisj : Disjoint Elt Egt := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Elt, Egt, mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hunion : Elt ∪ Egt = E := by
    ext p
    simp only [Elt, Egt, mem_union, mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      have hadj : G.Adj p.1 p.2 := (mem_filter.mp hp).2
      rcases lt_or_gt_of_ne hadj.ne with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  have hswap : Elt.card = Egt.card := by
    apply Finset.card_bij (fun (p : Fin (2 * n) × Fin (2 * n)) _ => (p.2, p.1))
    · intro p hp
      simp only [Elt, Egt, E, mem_filter, mem_product] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, hp.2⟩
    · intro p₁ _ p₂ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2 heq.1
    · intro p hp
      simp only [Elt, Egt, E, mem_filter, mem_product] at hp ⊢
      exact ⟨(p.2, p.1), ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, hp.2⟩, rfl⟩
  have htwo : E.card = 2 * Elt.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hswap]
    ring
  refine ⟨S.card / 2, ?_⟩
  omega

lemma exists_closed_even_subset {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin (2 * n))}
    (hdis : ¬ G.Connected) (hdeg : ∀ v, (G.neighborFinset v).card = 3) :
    ∃ i ∈ Icc 1 (n / 2), ∃ S ∈ (univ : Finset (Fin (2 * n))).powersetCard (2 * i),
      ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S := by
  let v₀ : Fin (2 * n) := ⟨0, by omega⟩
  let C := univ.filter (fun u : Fin (2 * n) => G.Reachable v₀ u)
  have hv₀ : v₀ ∈ C := by simp [C]
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨v₀, hv₀⟩
  have hCclosed : ∀ u ∈ C, ∀ w, G.Adj u w → w ∈ C := by
    intro u hu w huw
    simp only [C, mem_filter, mem_univ, true_and] at hu ⊢
    exact hu.trans huw.reachable
  have hCstrict : C.card < 2 * n := by
    by_contra hge
    have hcard : C.card = (univ : Finset (Fin (2 * n))).card := by
      have hle : C.card ≤ (univ : Finset (Fin (2 * n))).card := Finset.card_le_univ C
      simp only [Finset.card_univ, Fintype.card_fin] at hle ⊢
      omega
    have heq : C = univ := Finset.eq_univ_of_card C (by simpa [Fintype.card_fin] using hcard)
    apply hdis
    have : Nonempty (Fin (2 * n)) := ⟨v₀⟩
    refine ⟨fun u w => ?_⟩
    have hu : G.Reachable v₀ u := by
      have : u ∈ C := by rw [heq]; exact mem_univ u
      exact (mem_filter.mp this).2
    have hw : G.Reachable v₀ w := by
      have : w ∈ C := by rw [heq]; exact mem_univ w
      exact (mem_filter.mp this).2
    exact hu.symm.trans hw
  let S := if C.card ≤ n then C else univ \ C
  have hSclosed : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S := by
    dsimp only [S]
    split_ifs
    · exact hCclosed
    · exact closed_compl hCclosed
  have hScard_pos : 0 < S.card := by
    dsimp only [S]
    split_ifs with hle
    · exact hCpos
    · rw [Finset.card_sdiff_of_subset (subset_univ C), Finset.card_univ, Fintype.card_fin]
      omega
  have hScard_le : S.card ≤ n := by
    dsimp only [S]
    split_ifs with hle
    · exact hle
    · rw [Finset.card_sdiff_of_subset (subset_univ C), Finset.card_univ, Fintype.card_fin]
      omega
  obtain ⟨i, hi⟩ := even_card_of_closed_cubic hdeg hSclosed
  refine ⟨i, mem_Icc.mpr ⟨by omega, by omega⟩, S, mem_powersetCard.mpr ⟨subset_univ S, by omega⟩,
    hSclosed⟩

lemma pullGraph_cubic {n m : ℕ} {G : SimpleGraph (Fin (2 * n))}
    (hdeg : ∀ v, (G.neighborFinset v).card = 3)
    {S : Finset (Fin (2 * n))} (hS : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S)
    (e : ↥S ≃ Fin (2 * m)) :
    G.comap (fun a : Fin (2 * m) => (e.symm a).1) ∈ cubicGraphs m := by
  simp only [cubicGraphs, mem_filter, mem_univ, true_and]
  intro a
  let u : Fin (2 * n) := (e.symm a).1
  have hu : u ∈ S := (e.symm a).2
  rw [← hdeg u]
  apply Finset.card_bij (fun (b : Fin (2 * m)) _ => (e.symm b).1)
  · intro b hb
    simpa only [mem_neighborFinset, comap_adj] using hb
  · intro b₁ _ b₂ _ heq
    exact e.symm.injective (Subtype.ext heq)
  · intro w hw
    rw [mem_neighborFinset] at hw
    have hwS : w ∈ S := hS u hu w hw
    refine ⟨e ⟨w, hwS⟩, ?_, by simp⟩
    simpa only [mem_neighborFinset, comap_adj, Equiv.symm_apply_apply] using hw

lemma closedCubicGraphs_card_le {n i : ℕ} (hi : i ≤ n)
    {S : Finset (Fin (2 * n))} (hScard : S.card = 2 * i) :
    (closedCubicGraphs n S).card ≤ (cubicGraphs i).card * (cubicGraphs (n - i)).card := by
  have hcard1 : Fintype.card ↥S = 2 * i := by simpa using hScard
  have hcard2 : Fintype.card ↥(univ \ S) = 2 * (n - i) := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (subset_univ S), Finset.card_univ,
      Fintype.card_fin, hScard]
    omega
  let e₁ : ↥S ≃ Fin (2 * i) := Fintype.equivFinOfCardEq hcard1
  let e₂ : ↥(univ \ S) ≃ Fin (2 * (n - i)) := Fintype.equivFinOfCardEq hcard2
  let Φ : SimpleGraph (Fin (2 * n)) →
      SimpleGraph (Fin (2 * i)) × SimpleGraph (Fin (2 * (n - i))) :=
    fun G => (G.comap (fun a => (e₁.symm a).1), G.comap (fun a => (e₂.symm a).1))
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn Φ
  · intro G hG
    simp only [mem_coe, closedCubicGraphs, cubicGraphs, mem_filter, mem_univ, true_and] at hG
    simp only [mem_coe, mem_product, Φ]
    exact ⟨pullGraph_cubic hG.1 hG.2 e₁, pullGraph_cubic hG.1 (closed_compl hG.2) e₂⟩
  · intro G hG H hH heq
    simp only [mem_coe, closedCubicGraphs, cubicGraphs, mem_filter, mem_univ, true_and] at hG hH
    simp only [Φ, Prod.mk.injEq] at heq
    obtain ⟨heq1, heq2⟩ := heq
    ext u v
    by_cases hu : u ∈ S
    · by_cases hv : v ∈ S
      · have h1 := congrArg (fun K : SimpleGraph (Fin (2 * i)) =>
          K.Adj (e₁ ⟨u, hu⟩) (e₁ ⟨v, hv⟩)) heq1
        exact iff_of_eq (by simpa only [comap_adj, Equiv.symm_apply_apply] using h1)
      · constructor
        · intro hadj; exact absurd (hG.2 u hu v hadj) hv
        · intro hadj; exact absurd (hH.2 u hu v hadj) hv
    · by_cases hv : v ∈ S
      · constructor
        · intro hadj; exact absurd (hG.2 v hv u hadj.symm) hu
        · intro hadj; exact absurd (hH.2 v hv u hadj.symm) hu
      · have hu' : u ∈ univ \ S := mem_sdiff.mpr ⟨mem_univ u, hu⟩
        have hv' : v ∈ univ \ S := mem_sdiff.mpr ⟨mem_univ v, hv⟩
        have h2 := congrArg (fun K : SimpleGraph (Fin (2 * (n - i))) =>
          K.Adj (e₂ ⟨u, hu'⟩) (e₂ ⟨v, hv'⟩)) heq2
        exact iff_of_eq (by simpa only [comap_adj, Equiv.symm_apply_apply] using h2)

lemma h2_proof : OMA.R_oeis_a004109_R1.H2 := by
  dsimp only [OMA.R_oeis_a004109_R1.H2]
  have hg_eq : ∀ n,
      (univ.filter fun G : SimpleGraph (Fin (2 * n)) =>
        ∀ v, (G.neighborFinset v).card = 3).card = (cubicGraphs n).card := by
    intro n
    unfold cubicGraphs
    congr 1
  constructor
  · intro n
    rw [a_eq_card n, hg_eq n]
    exact Finset.card_le_card (conn_subset_cubic n)
  · intro n hn
    rw [a_eq_card n, hg_eq n, sub_card_eq_disconn n]
    have hsub : disconnCubicGraphs n ⊆
        (Icc 1 (n / 2)).biUnion (fun i =>
          ((univ : Finset (Fin (2 * n))).powersetCard (2 * i)).biUnion
            (fun S => closedCubicGraphs n S)) := by
      intro G hG
      simp only [disconnCubicGraphs, mem_filter, mem_univ, true_and] at hG
      obtain ⟨i, hi, S, hS, hclosed⟩ := exists_closed_even_subset hn hG.1 hG.2
      rw [mem_biUnion]
      refine ⟨i, hi, ?_⟩
      rw [mem_biUnion]
      refine ⟨S, hS, ?_⟩
      simp only [closedCubicGraphs, cubicGraphs, mem_filter, mem_univ, true_and]
      exact ⟨hG.2, hclosed⟩
    calc
      (disconnCubicGraphs n).card
          ≤ ((Icc 1 (n / 2)).biUnion (fun i =>
              ((univ : Finset (Fin (2 * n))).powersetCard (2 * i)).biUnion
                (fun S => closedCubicGraphs n S))).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Icc 1 (n / 2),
            (((univ : Finset (Fin (2 * n))).powersetCard (2 * i)).biUnion
              (fun S => closedCubicGraphs n S)).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Icc 1 (n / 2),
            ∑ S ∈ (univ : Finset (Fin (2 * n))).powersetCard (2 * i),
              (closedCubicGraphs n S).card :=
            Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
      _ ≤ ∑ i ∈ Icc 1 (n / 2),
            ∑ _S ∈ (univ : Finset (Fin (2 * n))).powersetCard (2 * i),
              ((cubicGraphs i).card * (cubicGraphs (n - i)).card) := by
            apply Finset.sum_le_sum
            intro i hi
            have hin : i ≤ n := by
              have := (mem_Icc.mp hi).2
              omega
            apply Finset.sum_le_sum
            intro S hS
            exact closedCubicGraphs_card_le hin (mem_powersetCard.mp hS).2
      _ = ∑ i ∈ Icc 1 (n / 2),
            (2 * n).choose (2 * i) * (cubicGraphs i).card * (cubicGraphs (n - i)).card := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
              Fintype.card_fin, mul_assoc]
      _ = ∑ i ∈ Icc 1 (n / 2),
            (2 * n).choose (2 * i) *
              (univ.filter fun G : SimpleGraph (Fin (2 * i)) =>
                ∀ v, (G.neighborFinset v).card = 3).card *
              (univ.filter fun G : SimpleGraph (Fin (2 * (n - i))) =>
                ∀ v, (G.neighborFinset v).card = 3).card := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hg_eq i, hg_eq (n - i)]

end OeisA004109H2

theorem OMA.solution : OMA.R_oeis_a004109_R1.H2 :=
  OeisA004109H2.h2_proof
