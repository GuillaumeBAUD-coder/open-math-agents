import OMAStatements.S_opg_strong_matchings_and_covers

/-!
# Refutation of Aharoni's Strong Matching Conjecture for Bounded-Size Hypergraphs

We construct a hypergraph `H₁` whose edges are nonempty finite sets of size at most `3`
(in fact sizes `2` and `3`), and prove that `H₁` admits no strongly maximal matching.
This refutes `OMA.S_opg_strong_matchings_and_covers.main`.

Construction (Hollom–Randall Shaw, *Counterexamples to conjectures on strong maximality
and minimality*, arXiv:2511.13709, 2025/2026; building on Ahlswede–Khachatrian 1996):
1. `H₁*` is the hypergraph on `ℕ` whose edges are finite subsets `e ⊆ ℕ` with `min(e) ≥ 3`
   and `|e| = min(e)`. Every matching `M*` of `H₁*` admits a matching `N*` with
   `N* \ M*` and `M* \ N*` finite and `|M* \ N*| < |N* \ M*|`.
2. Each edge `e` of `H₁*` of size `k = |e| ≥ 3` is replaced by a path gadget `G_e` using
   `2(k - 1)` private vertices and `2k - 1` edges of size `2` or `3` (`k` outer edges and
   `k - 1` inner edges) whose intersection graph is the path `P_{2k-1}`.
3. Any strongly maximal matching `M` of `H₁` must pick either `k - 1` edges or all `k`
   outer edges in each gadget `G_e`, inducing a matching `M*` of `H₁*`; modifying `M` on
   finitely many gadgets according to `N*` strictly increases the matching cardinality
   relative to `M`, contradicting strong maximality.
-/

namespace OMA.P_opg_strong_matchings_and_covers

open OMA.S_opg_strong_matchings_and_covers

/-! ## Part 1: The unbounded-edge hypergraph `H₁*` (Ahlswede–Khachatrian) -/

/-- Edges of `H₁*`: nonempty finite subsets `e ⊆ ℕ` with `3 ≤ min(e)` and `|e| = min(e)`. -/
private abbrev EdgeStar :=
  { e : Finset ℕ // ∃ h : e.Nonempty, 3 ≤ e.min' h ∧ e.card = e.min' h }

private lemma edgeStar_nonempty (e : EdgeStar) : e.1.Nonempty := e.2.choose

private lemma edgeStar_min_ge (e : EdgeStar) : 3 ≤ e.1.min' (edgeStar_nonempty e) :=
  (e.2.choose_spec).1

private lemma edgeStar_card_eq_min (e : EdgeStar) : e.1.card = e.1.min' (edgeStar_nonempty e) :=
  (e.2.choose_spec).2

private lemma edgeStar_card_ge_three (e : EdgeStar) : 3 ≤ e.1.card := by
  rw [edgeStar_card_eq_min e]; exact edgeStar_min_ge e

/-- Any matching `M*` of `H₁*` can be improved by a finite swap to a matching `N*`. -/
private lemma exists_better_matching_star (M : Set EdgeStar)
    (hM : M.Pairwise fun e₁ e₂ => Disjoint e₁.1 e₂.1) :
    ∃ N : Set EdgeStar,
      (N.Pairwise fun e₁ e₂ => Disjoint e₁.1 e₂.1) ∧
      (M \ N).Finite ∧ (N \ M).Finite ∧
      (M \ N).ncard < (N \ M).ncard := by
  by_cases hfin : M.Finite
  · -- Finite case: pick a fresh interval edge disjoint from all edges in `M`
    let U : Finset ℕ := hfin.toFinset.biUnion (fun e => e.1)
    let m : ℕ := max 3 (U.sup id + 1)
    let e0_set : Finset ℕ := Finset.Ico m (2 * m)
    have he0_ne : e0_set.Nonempty := ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have he0_min : e0_set.min' he0_ne = m := by
      refine le_antisymm (Finset.min'_le _ m (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)) ?_
      rw [Finset.le_min'_iff]
      intro x hx
      exact (Finset.mem_Ico.mp hx).1
    have he0_card : e0_set.card = m := by
      simp only [e0_set, Nat.card_Ico]; omega
    let e0 : EdgeStar := ⟨e0_set, ⟨he0_ne, by rw [he0_min]; omega, by rw [he0_min, he0_card]⟩⟩
    have he0_disj : ∀ e ∈ M, Disjoint e0.1 e.1 := by
      intro e he
      rw [Finset.disjoint_left]
      intro x hx0 hxe
      have hxm : m ≤ x := (Finset.mem_Ico.mp hx0).1
      have hxU : x ∈ U := Finset.mem_biUnion.mpr ⟨e, hfin.mem_toFinset.mpr he, hxe⟩
      have hxle : x ≤ U.sup id := Finset.le_sup (f := id) hxU
      omega
    have he0_nmem : e0 ∉ M := by
      intro hmem
      have hdisj := he0_disj e0 hmem
      exact Finset.disjoint_left.mp hdisj (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
        (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
    refine ⟨insert e0 M, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      rcases Set.mem_insert_iff.mp ha with rfl | haM <;>
        rcases Set.mem_insert_iff.mp hb with rfl | hbM
      · exact absurd rfl hab
      · exact he0_disj b hbM
      · exact (he0_disj a haM).symm
      · exact hM haM hbM hab
    · have : M \ insert e0 M = ∅ := Set.sdiff_eq_empty.mpr (Set.subset_insert _ _)
      rw [this]; exact Set.finite_empty
    · have : insert e0 M \ M = {e0} := by
        ext x; simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | hx, hxn⟩
          · rfl
          · exact absurd hx hxn
        · rintro rfl; exact ⟨Or.inl rfl, he0_nmem⟩
      rw [this]; exact Set.finite_singleton e0
    · have h1 : M \ insert e0 M = ∅ := Set.sdiff_eq_empty.mpr (Set.subset_insert _ _)
      have h2 : insert e0 M \ M = {e0} := by
        ext x; simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | hx, hxn⟩
          · rfl
          · exact absurd hx hxn
        · rintro rfl; exact ⟨Or.inl rfl, he0_nmem⟩
      rw [h1, h2, Set.ncard_empty, Set.ncard_singleton]
      omega
  · -- Infinite case: Ahlswede–Khachatrian 2-for-3 swap
    have hinf : M.Infinite := hfin
    obtain ⟨E₁, hE₁M⟩ := hinf.nonempty
    let k₁ : ℕ := E₁.1.card
    have hk₁ : 3 ≤ k₁ := edgeStar_card_ge_three E₁
    let emb := E₁.1.orderEmbOfFin (rfl : E₁.1.card = k₁)
    let v₁ : ℕ := emb ⟨0, by omega⟩
    let v₂ : ℕ := emb ⟨1, by omega⟩
    let v₃ : ℕ := emb ⟨2, by omega⟩
    have hv₁_mem : v₁ ∈ E₁.1 := Finset.orderEmbOfFin_mem E₁.1 rfl ⟨0, by omega⟩
    have hv₂_mem : v₂ ∈ E₁.1 := Finset.orderEmbOfFin_mem E₁.1 rfl ⟨1, by omega⟩
    have hv₃_mem : v₃ ∈ E₁.1 := Finset.orderEmbOfFin_mem E₁.1 rfl ⟨2, by omega⟩
    have hv12 : v₁ < v₂ := emb.strictMono (show (⟨0, by omega⟩ : Fin k₁) < ⟨1, by omega⟩ from Nat.zero_lt_one)
    have hv23 : v₂ < v₃ := emb.strictMono (show (⟨1, by omega⟩ : Fin k₁) < ⟨2, by omega⟩ from Nat.lt_succ_self 1)
    have hv₁_eq_min : v₁ = E₁.1.min' (edgeStar_nonempty E₁) := by
      refine le_antisymm ?_ (Finset.min'_le _ v₁ hv₁_mem)
      rw [Finset.le_min'_iff]
      intro x hx
      have hx_ran : x ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨idx, rfl⟩ := hx_ran
      exact emb.monotone (show (⟨0, by omega⟩ : Fin k₁) ≤ idx from Nat.zero_le _)
    have hv₁_ge3 : 3 ≤ v₁ := by rw [hv₁_eq_min]; exact edgeStar_min_ge E₁
    have hE₁_card : E₁.1.card = v₁ := by rw [hv₁_eq_min]; exact edgeStar_card_eq_min E₁
    have hE₁_gt_v₃ : ∀ x ∈ E₁.1, x ≠ v₁ → x ≠ v₂ → x ≠ v₃ → v₃ < x := by
      intro x hx hx1 hx2 hx3
      have hx_ran : x ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨idx, rfl⟩ := hx_ran
      have hidx : 2 < idx.val := by
        by_contra hle
        have hcases : idx.val = 0 ∨ idx.val = 1 ∨ idx.val = 2 := by omega
        rcases hcases with h0 | h1 | h2
        · exact hx1 (congrArg emb (Fin.ext h0))
        · exact hx2 (congrArg emb (Fin.ext h1))
        · exact hx3 (congrArg emb (Fin.ext h2))
      exact emb.strictMono (show (⟨2, by omega⟩ : Fin k₁) < idx from hidx)
    -- Find E₂ ∈ M with E₂ ≠ E₁ and v₂ + v₃ ≤ min(E₂)
    have hE₂_ex : ∃ E₂ ∈ M, E₂ ≠ E₁ ∧ v₂ + v₃ ≤ E₂.1.min' (edgeStar_nonempty E₂) := by
      by_contra hall
      push Not at hall
      let f : EdgeStar → ℕ := fun e => e.1.min' (edgeStar_nonempty e)
      have hinj : Set.InjOn f M := by
        intro a ha b hb hab
        by_contra hne
        have hdisj := hM ha hb hne
        have hmem_a : f a ∈ a.1 := Finset.min'_mem _ _
        have hmem_b : f a ∈ b.1 := by rw [hab]; exact Finset.min'_mem _ _
        exact Finset.disjoint_left.mp hdisj hmem_a hmem_b
      have hsub : f '' (M \ {E₁}) ⊆ (Finset.range (v₂ + v₃) : Set ℕ) := by
        rintro _ ⟨e, ⟨heM, hene⟩, rfl⟩
        exact Finset.mem_range.mpr (hall e heM hene)
      have hfin_img : (f '' (M \ {E₁})).Finite := (Finset.finite_toSet _).subset hsub
      have hfin_diff : (M \ {E₁}).Finite := hfin_img.of_finite_image (hinj.mono Set.sdiff_subset)
      exact hinf ((hfin_diff.union (Set.finite_singleton E₁)).subset fun x hx =>
        if h : x = E₁ then Or.inr h else Or.inl ⟨hx, h⟩)
    obtain ⟨E₂, hE₂M, hE₂_ne, hE₂_min⟩ := hE₂_ex
    have hdisj12 : Disjoint E₁.1 E₂.1 := hM hE₁M hE₂M hE₂_ne.symm
    have hE₂_gt_v₃ : ∀ x ∈ E₂.1, v₃ < x := fun x hx => by
      have := Finset.min'_le _ x hx
      omega
    -- Pool R = (E₁ ∪ E₂) \ {v₁, v₂, v₃}
    let R : Finset ℕ := (E₁.1 ∪ E₂.1) \ {v₁, v₂, v₃}
    have hR_gt_v₃ : ∀ x ∈ R, v₃ < x := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx.1 with h1 | h2
      · exact hE₁_gt_v₃ x h1 (by tauto) (by tauto) (by tauto)
      · exact hE₂_gt_v₃ x h2
    have hv_sub : ({v₁, v₂, v₃} : Finset ℕ) ⊆ E₁.1 ∪ E₂.1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_union]
      rcases hx with rfl | rfl | rfl <;> exact Or.inl (by assumption)
    have hv_card : ({v₁, v₂, v₃} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hR_card : (v₁ - 1) + (v₂ - 1) + (v₃ - 1) ≤ R.card := by
      have h1 : R.card = (E₁.1 ∪ E₂.1).card - 3 := by
        rw [Finset.card_sdiff_of_subset hv_sub, hv_card]
      have h2 : (E₁.1 ∪ E₂.1).card = E₁.1.card + E₂.1.card := Finset.card_union_of_disjoint hdisj12
      have h3 : E₂.1.card = E₂.1.min' (edgeStar_nonempty E₂) := edgeStar_card_eq_min E₂
      omega
    -- Extract pairwise disjoint subsets S₁, S₂, S₃ ⊆ R of sizes v₁-1, v₂-1, v₃-1
    obtain ⟨S₁, hS₁R, hS₁c⟩ := Finset.exists_subset_card_eq (by omega : v₁ - 1 ≤ R.card)
    have hR1_card : (v₂ - 1) + (v₃ - 1) ≤ (R \ S₁).card := by
      rw [Finset.card_sdiff_of_subset hS₁R, hS₁c]; omega
    obtain ⟨S₂, hS₂R1, hS₂c⟩ := Finset.exists_subset_card_eq (by omega : v₂ - 1 ≤ (R \ S₁).card)
    have hR2_card : v₃ - 1 ≤ ((R \ S₁) \ S₂).card := by
      rw [Finset.card_sdiff_of_subset hS₂R1, hS₂c]; omega
    obtain ⟨S₃, hS₃R2, hS₃c⟩ := Finset.exists_subset_card_eq hR2_card
    have hS₂R : S₂ ⊆ R := hS₂R1.trans Finset.sdiff_subset
    have hS₃R : S₃ ⊆ R := hS₃R2.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)
    have hS12 : Disjoint S₁ S₂ := Finset.disjoint_of_subset_right hS₂R1 disjoint_sdiff_self_right
    have hS13 : Disjoint S₁ S₃ := Finset.disjoint_of_subset_right
      (hS₃R2.trans Finset.sdiff_subset) disjoint_sdiff_self_right
    have hS23 : Disjoint S₂ S₃ := Finset.disjoint_of_subset_right hS₃R2 disjoint_sdiff_self_right
    -- Build F₁, F₂, F₃ ∈ EdgeStar
    let mkF : ∀ (v : ℕ) (S : Finset ℕ), 3 ≤ v → S.card = v - 1 → (∀ x ∈ S, v < x) → EdgeStar :=
      fun v S hv hSc hgt =>
        let F := insert v S
        have hne : F.Nonempty := ⟨v, Finset.mem_insert_self v S⟩
        have hmin : F.min' hne = v := by
          refine le_antisymm (Finset.min'_le _ v (Finset.mem_insert_self v S)) ?_
          rw [Finset.le_min'_iff]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · exact le_rfl
          · exact (hgt x hxS).le
        have hvn : v ∉ S := fun h => lt_irrefl v (hgt v h)
        have hcard : F.card = v := by
          rw [Finset.card_insert_of_notMem hvn, hSc]; omega
        ⟨F, ⟨hne, by rw [hmin]; exact hv, by rw [hmin, hcard]⟩⟩
    let F₁ : EdgeStar := mkF v₁ S₁ hv₁_ge3 hS₁c (fun x hx => by have := hR_gt_v₃ x (hS₁R hx); omega)
    let F₂ : EdgeStar := mkF v₂ S₂ (by omega) hS₂c (fun x hx => by have := hR_gt_v₃ x (hS₂R hx); omega)
    let F₃ : EdgeStar := mkF v₃ S₃ (by omega) hS₃c (fun x hx => hR_gt_v₃ x (hS₃R hx))
    have hF₁_sub : F₁.1 ⊆ E₁.1 ∪ E₂.1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact Finset.mem_union_left _ hv₁_mem
      · exact (Finset.mem_sdiff.mp (hS₁R hxS)).1
    have hF₂_sub : F₂.1 ⊆ E₁.1 ∪ E₂.1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact Finset.mem_union_left _ hv₂_mem
      · exact (Finset.mem_sdiff.mp (hS₂R hxS)).1
    have hF₃_sub : F₃.1 ⊆ E₁.1 ∪ E₂.1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact Finset.mem_union_left _ hv₃_mem
      · exact (Finset.mem_sdiff.mp (hS₃R hxS)).1
    have hF12 : Disjoint F₁.1 F₂.1 := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      rcases Finset.mem_insert.mp h1 with rfl | h1S <;>
        rcases Finset.mem_insert.mp h2 with h2v | h2S
      · omega
      · have := hR_gt_v₃ v₁ (hS₂R h2S); omega
      · subst h2v; have := hR_gt_v₃ v₂ (hS₁R h1S); omega
      · exact Finset.disjoint_left.mp hS12 h1S h2S
    have hF13 : Disjoint F₁.1 F₃.1 := by
      rw [Finset.disjoint_left]
      intro x h1 h3
      rcases Finset.mem_insert.mp h1 with rfl | h1S <;>
        rcases Finset.mem_insert.mp h3 with h3v | h3S
      · omega
      · have := hR_gt_v₃ v₁ (hS₃R h3S); omega
      · subst h3v; have := hR_gt_v₃ v₃ (hS₁R h1S); omega
      · exact Finset.disjoint_left.mp hS13 h1S h3S
    have hF23 : Disjoint F₂.1 F₃.1 := by
      rw [Finset.disjoint_left]
      intro x h2 h3
      rcases Finset.mem_insert.mp h2 with rfl | h2S <;>
        rcases Finset.mem_insert.mp h3 with h3v | h3S
      · omega
      · have := hR_gt_v₃ v₂ (hS₃R h3S); omega
      · subst h3v; have := hR_gt_v₃ v₃ (hS₂R h2S); omega
      · exact Finset.disjoint_left.mp hS23 h2S h3S
    have hF_ne12 : F₁ ≠ F₂ := fun h =>
      Finset.disjoint_left.mp hF12 (Finset.mem_insert_self v₁ S₁) (by rw [← h]; exact Finset.mem_insert_self v₁ S₁)
    have hF_ne13 : F₁ ≠ F₃ := fun h =>
      Finset.disjoint_left.mp hF13 (Finset.mem_insert_self v₁ S₁) (by rw [← h]; exact Finset.mem_insert_self v₁ S₁)
    have hF_ne23 : F₂ ≠ F₃ := fun h =>
      Finset.disjoint_left.mp hF23 (Finset.mem_insert_self v₂ S₂) (by rw [← h]; exact Finset.mem_insert_self v₂ S₂)
    -- None of F₁, F₂, F₃ is in M
    have hF₁_nM : F₁ ∉ M := by
      intro hmem
      by_cases heq : F₁ = E₁
      · have h2 : v₂ ∈ F₁.1 := by rw [heq]; exact hv₂_mem
        rcases Finset.mem_insert.mp h2 with h21 | h2S
        · omega
        · have := hR_gt_v₃ v₂ (hS₁R h2S); omega
      · exact Finset.disjoint_left.mp (hM hmem hE₁M heq) (Finset.mem_insert_self v₁ S₁) hv₁_mem
    have hF₂_nM : F₂ ∉ M := by
      intro hmem
      by_cases heq : F₂ = E₁
      · have h1 : v₁ ∈ F₂.1 := by rw [heq]; exact hv₁_mem
        rcases Finset.mem_insert.mp h1 with h12 | h1S
        · omega
        · have := hR_gt_v₃ v₁ (hS₂R h1S); omega
      · exact Finset.disjoint_left.mp (hM hmem hE₁M heq) (Finset.mem_insert_self v₂ S₂) hv₂_mem
    have hF₃_nM : F₃ ∉ M := by
      intro hmem
      by_cases heq : F₃ = E₁
      · have h1 : v₁ ∈ F₃.1 := by rw [heq]; exact hv₁_mem
        rcases Finset.mem_insert.mp h1 with h13 | h1S
        · omega
        · have := hR_gt_v₃ v₁ (hS₃R h1S); omega
      · exact Finset.disjoint_left.mp (hM hmem hE₁M heq) (Finset.mem_insert_self v₃ S₃) hv₃_mem
    let N : Set EdgeStar := (M \ {E₁, E₂}) ∪ {F₁, F₂, F₃}
    have hdisj_other : ∀ e ∈ M \ {E₁, E₂}, ∀ F ∈ ({F₁, F₂, F₃} : Set EdgeStar), Disjoint e.1 F.1 := by
      intro e ⟨heM, hene⟩ F hF
      have he1 : e ≠ E₁ := fun h => hene (Or.inl h)
      have he2 : e ≠ E₂ := fun h => hene (Or.inr h)
      have hsub : F.1 ⊆ E₁.1 ∪ E₂.1 := by
        rcases hF with rfl | rfl | rfl
        · exact hF₁_sub
        · exact hF₂_sub
        · exact hF₃_sub
      exact Finset.disjoint_of_subset_right hsub
        (Finset.disjoint_union_right.mpr ⟨hM heM hE₁M he1, hM heM hE₂M he2⟩)
    have hN_match : N.Pairwise fun a b => Disjoint a.1 b.1 := by
      intro a ha b hb hab
      rcases ha with haM | haF <;> rcases hb with hbM | hbF
      · exact hM haM.1 hbM.1 hab
      · exact hdisj_other a haM b hbF
      · exact (hdisj_other b hbM a haF).symm
      · rcases haF with rfl | rfl | rfl <;> rcases hbF with rfl | rfl | rfl
        · exact absurd rfl hab
        · exact hF12
        · exact hF13
        · exact hF12.symm
        · exact absurd rfl hab
        · exact hF23
        · exact hF13.symm
        · exact hF23.symm
        · exact absurd rfl hab
    have hMN : M \ N = {E₁, E₂} := by
      ext e
      simp only [N, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨heM, hnot⟩
        by_contra hne
        exact hnot (Or.inl ⟨heM, hne⟩)
      · rintro (rfl | rfl)
        · refine ⟨hE₁M, ?_⟩
          rintro (⟨_, h⟩ | (h | h | h))
          · exact h (Or.inl rfl)
          · exact hF₁_nM (h ▸ hE₁M)
          · exact hF₂_nM (h ▸ hE₁M)
          · exact hF₃_nM (h ▸ hE₁M)
        · refine ⟨hE₂M, ?_⟩
          rintro (⟨_, h⟩ | (h | h | h))
          · exact h (Or.inr rfl)
          · exact hF₁_nM (h ▸ hE₂M)
          · exact hF₂_nM (h ▸ hE₂M)
          · exact hF₃_nM (h ▸ hE₂M)
    have hNM : N \ M = {F₁, F₂, F₃} := by
      ext e
      simp only [N, Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨heM, _⟩ | (rfl | rfl | rfl), henM⟩
        · exact absurd heM henM
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨Or.inr (Or.inl rfl), hF₁_nM⟩
        · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hF₂_nM⟩
        · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hF₃_nM⟩
    refine ⟨N, hN_match, ?_, ?_, ?_⟩
    · rw [hMN]; exact (Set.finite_singleton E₂).insert E₁
    · rw [hNM]; exact ((Set.finite_singleton F₃).insert F₂).insert F₁
    · rw [hMN, hNM]
      have hc1 : ({E₁, E₂} : Set EdgeStar).ncard = 2 := by
        rw [Set.ncard_pair hE₂_ne.symm]
      have hc2 : ({F₁, F₂, F₃} : Set EdgeStar).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by simp [hF_ne12, hF_ne13]) ((Set.finite_singleton F₃).insert F₂),
          Set.ncard_pair hF_ne23]
      rw [hc1, hc2]; omega

/-! ## Part 2: The gadget hypergraph `H₁` with edge sizes ≤ 3 -/

/-- Vertices of `H₁`: base vertices `ℕ` plus `2(k - 1)` private vertices per edge `e` of `H₁*`. -/
private abbrev Vert := ℕ ⊕ (Σ e : EdgeStar, Fin (e.1.card - 1) × Bool)

/-- Edges of `H₁`: for each `e : EdgeStar` of size `k`, `k` outer edges and `k - 1` inner edges. -/
private abbrev Edge := Σ e : EdgeStar, Fin e.1.card ⊕ Fin (e.1.card - 1)

private def vtxOf (e : EdgeStar) (i : Fin e.1.card) : ℕ :=
  e.1.orderEmbOfFin rfl i

private lemma vtxOf_mem (e : EdgeStar) (i : Fin e.1.card) : vtxOf e i ∈ e.1 :=
  Finset.orderEmbOfFin_mem e.1 rfl i

private lemma vtxOf_inj (e : EdgeStar) : Function.Injective (vtxOf e) :=
  (e.1.orderEmbOfFin rfl).injective

private lemma vtxOf_surj (e : EdgeStar) {x : ℕ} (hx : x ∈ e.1) : ∃ i : Fin e.1.card, vtxOf e i = x := by
  have : x ∈ Set.range (e.1.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hx
  exact this

/-- The finite set of vertices in each edge of `H₁`. -/
private def edgeFinset : Edge → Finset Vert
  | ⟨e, Sum.inr j⟩ =>
      { Sum.inr ⟨e, (j, false)⟩, Sum.inr ⟨e, (j, true)⟩ }
  | ⟨e, Sum.inl i⟩ =>
      let k := e.1.card
      have hk : 3 ≤ k := edgeStar_card_ge_three e
      if h0 : i.val = 0 then
        { Sum.inl (vtxOf e i), Sum.inr ⟨e, (⟨0, by omega⟩, false)⟩ }
      else if hlast : i.val = k - 1 then
        { Sum.inl (vtxOf e i), Sum.inr ⟨e, (⟨k - 2, by omega⟩, true)⟩ }
      else
        { Sum.inl (vtxOf e i),
          Sum.inr ⟨e, (⟨i.val - 1, by omega⟩, true)⟩,
          Sum.inr ⟨e, (⟨i.val, by omega⟩, false)⟩ }

private def edgeSetH (x : Edge) : Set Vert := (edgeFinset x : Set Vert)

private lemma edgeSetH_props (x : Edge) :
    (edgeSetH x).Nonempty ∧ (edgeSetH x).Finite ∧ (edgeSetH x).ncard ≤ 3 := by
  refine ⟨?_, Finset.finite_toSet _, ?_⟩
  · rcases x with ⟨e, i | j⟩
    · dsimp only [edgeSetH, edgeFinset]
      split_ifs
      · exact ⟨Sum.inl (vtxOf e i), by simp⟩
      · exact ⟨Sum.inl (vtxOf e i), by simp⟩
      · exact ⟨Sum.inl (vtxOf e i), by simp⟩
    · exact ⟨Sum.inr ⟨e, (j, false)⟩, by simp [edgeSetH, edgeFinset]⟩
  · rw [edgeSetH, Set.ncard_coe_finset]
    rcases x with ⟨e, i | j⟩
    · dsimp only [edgeFinset]
      split_ifs
      · exact Finset.card_le_two.trans (by decide)
      · exact Finset.card_le_two.trans (by decide)
      · exact Finset.card_le_three
    · exact Finset.card_le_two.trans (by decide)

/-! ## Part 3: Disjointness inside and across gadgets -/

private lemma inner_disj_inner (e : EdgeStar) {j₁ j₂ : Fin (e.1.card - 1)} (hne : j₁ ≠ j₂) :
    Disjoint (edgeSetH ⟨e, Sum.inr j₁⟩) (edgeSetH ⟨e, Sum.inr j₂⟩) := by
  rw [Set.disjoint_left]
  intro v hv1 hv2
  simp only [edgeSetH, edgeFinset, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hv1 hv2
  rcases hv1 with rfl | rfl <;> rcases hv2 with h | h <;>
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at h
  all_goals exact hne h.2.1

private lemma outer_disj_outer (e : EdgeStar) {i₁ i₂ : Fin e.1.card} (hne : i₁ ≠ i₂) :
    Disjoint (edgeSetH ⟨e, Sum.inl i₁⟩) (edgeSetH ⟨e, Sum.inl i₂⟩) := by
  have hk : 3 ≤ e.1.card := edgeStar_card_ge_three e
  rw [Set.disjoint_left]
  intro v hv1 hv2
  have h1 := Finset.mem_coe.mp hv1
  have h2 := Finset.mem_coe.mp hv2
  dsimp only [edgeFinset] at h1 h2
  split_ifs at h1 <;> split_ifs at h2 <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  all_goals
    rcases h1 with rfl | h1' <;> [skip; (try rcases h1' with rfl | rfl)]
  all_goals
    rcases h2 with h2' | h2'' <;> [skip; (try rcases h2'' with h2a | h2b)]
  all_goals
    try (simp only [Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq,
      Fin.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, reduceCtorEq,
      and_false, false_and, true_and, and_true] at *)
  all_goals
    first
    | exact hne (vtxOf_inj e (by assumption))
    | exact hne (Fin.ext (by omega))
    | (try cases ‹_ ∧ _›; omega)
    | omega
    | contradiction

private lemma mem_edgeSetH_inr_eq {e₁ e₂ : EdgeStar} {s : Fin e₂.1.card ⊕ Fin (e₂.1.card - 1)}
    {p : Fin (e₁.1.card - 1) × Bool} (h : (Sum.inr ⟨e₁, p⟩ : Vert) ∈ edgeSetH ⟨e₂, s⟩) :
    e₁ = e₂ := by
  have hm := Finset.mem_coe.mp h
  rcases s with i | j
  · dsimp only [edgeFinset] at hm
    split_ifs at hm <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
        Sum.inr.injEq, Sigma.mk.inj_iff] at hm
    · exact hm.1
    · exact hm.1
    · rcases hm with h1 | h2
      · exact h1.1
      · exact h2.1
  · simp only [edgeFinset, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq,
      Sigma.mk.inj_iff] at hm
    rcases hm with h1 | h2
    · exact h1.1
    · exact h2.1

private lemma mem_outer_inl_eq {e : EdgeStar} {i : Fin e.1.card} {w : ℕ}
    (h : (Sum.inl w : Vert) ∈ edgeSetH ⟨e, Sum.inl i⟩) : w = vtxOf e i := by
  have hm := Finset.mem_coe.mp h
  dsimp only [edgeFinset] at hm
  split_ifs at hm <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_false, Sum.inl.injEq] at hm <;>
    exact hm

private lemma inner_disj_other_gadget {e₁ e₂ : EdgeStar} (hne : e₁ ≠ e₂)
    (j : Fin (e₁.1.card - 1)) (s : Fin e₂.1.card ⊕ Fin (e₂.1.card - 1)) :
    Disjoint (edgeSetH ⟨e₁, Sum.inr j⟩) (edgeSetH ⟨e₂, s⟩) := by
  rw [Set.disjoint_left]
  intro v hv1 hv2
  have h1 := Finset.mem_coe.mp hv1
  simp only [edgeFinset, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl
  · exact hne (mem_edgeSetH_inr_eq hv2)
  · exact hne (mem_edgeSetH_inr_eq hv2)

private lemma outer_disj_other_outer {e₁ e₂ : EdgeStar} (hne : e₁ ≠ e₂)
    (i₁ : Fin e₁.1.card) (i₂ : Fin e₂.1.card) (hv : vtxOf e₁ i₁ ≠ vtxOf e₂ i₂) :
    Disjoint (edgeSetH ⟨e₁, Sum.inl i₁⟩) (edgeSetH ⟨e₂, Sum.inl i₂⟩) := by
  rw [Set.disjoint_left]
  intro v hv1 hv2
  rcases v with w | ⟨e', p⟩
  · exact hv ((mem_outer_inl_eq hv1).symm.trans (mem_outer_inl_eq hv2))
  · exact hne ((mem_edgeSetH_inr_eq hv1).symm.trans (mem_edgeSetH_inr_eq hv2))

/-- Adjacent outer and inner edges in the same gadget share a private vertex. -/
private lemma outer_not_disj_inner_right (e : EdgeStar) (j : Fin (e.1.card - 1)) :
    ¬ Disjoint (edgeSetH ⟨e, Sum.inl ⟨j.val, by omega⟩⟩) (edgeSetH ⟨e, Sum.inr j⟩) := by
  intro hdisj
  have hk : 3 ≤ e.1.card := edgeStar_card_ge_three e
  have h2 : Sum.inr ⟨e, (j, false)⟩ ∈ edgeSetH ⟨e, Sum.inr j⟩ := by
    simp [edgeSetH, edgeFinset]
  have h1 : Sum.inr ⟨e, (j, false)⟩ ∈ edgeSetH ⟨e, Sum.inl ⟨j.val, by omega⟩⟩ := by
    rw [edgeSetH, Finset.mem_coe]
    dsimp only [edgeFinset]
    by_cases h0 : j.val = 0
    · rw [dif_pos h0]
      simp [Fin.ext_iff, h0]
    · rw [dif_neg h0, dif_neg (show j.val ≠ e.1.card - 1 by omega)]
      simp [Fin.ext_iff]
  exact Set.disjoint_left.mp hdisj h1 h2

private lemma outer_not_disj_inner_left (e : EdgeStar) (j : Fin (e.1.card - 1)) :
    ¬ Disjoint (edgeSetH ⟨e, Sum.inl ⟨j.val + 1, by omega⟩⟩) (edgeSetH ⟨e, Sum.inr j⟩) := by
  intro hdisj
  have hk : 3 ≤ e.1.card := edgeStar_card_ge_three e
  have h2 : Sum.inr ⟨e, (j, true)⟩ ∈ edgeSetH ⟨e, Sum.inr j⟩ := by
    simp [edgeSetH, edgeFinset]
  have h1 : Sum.inr ⟨e, (j, true)⟩ ∈ edgeSetH ⟨e, Sum.inl ⟨j.val + 1, by omega⟩⟩ := by
    rw [edgeSetH, Finset.mem_coe]
    dsimp only [edgeFinset]
    rw [dif_neg (show (j.val + 1 : ℕ) ≠ 0 by omega)]
    by_cases hlast : j.val + 1 = e.1.card - 1
    · rw [dif_pos hlast]
      simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, Sigma.mk.inj_iff,
        heq_eq_eq, Prod.mk.injEq, and_true, Fin.ext_iff, reduceCtorEq, false_or]
      exact ⟨trivial, by omega⟩
    · rw [dif_neg hlast]
      simp [Fin.ext_iff]
  exact Set.disjoint_left.mp hdisj h1 h2

/-! ## Part 4: Matching structure inside a single gadget `G_e` -/

private noncomputable def gadgetPart (M : Set Edge) (e : EdgeStar) :
    Finset (Fin e.1.card ⊕ Fin (e.1.card - 1)) := by
  classical
  exact Finset.univ.filter (fun s => (⟨e, s⟩ : Edge) ∈ M)

private def allOuter (e : EdgeStar) : Finset (Fin e.1.card ⊕ Fin (e.1.card - 1)) :=
  Finset.univ.image Sum.inl

private def allInner (e : EdgeStar) : Finset (Fin e.1.card ⊕ Fin (e.1.card - 1)) :=
  Finset.univ.image Sum.inr

private lemma allOuter_card (e : EdgeStar) : (allOuter e).card = e.1.card := by
  rw [allOuter, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, Fintype.card_fin]

private lemma allInner_card (e : EdgeStar) : (allInner e).card = e.1.card - 1 := by
  rw [allInner, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]

/-- In any matching `M` of `H₁`, the gadget `G_e` contains at most `k` edges, and if it
contains `k` edges then they are precisely the `k` outer edges. -/
private lemma gadget_matching_le_and_eq {M : Set Edge} (hM : IsMatching edgeSetH M) (e : EdgeStar) :
    (gadgetPart M e).card ≤ e.1.card ∧
    ((gadgetPart M e).card = e.1.card → gadgetPart M e = allOuter e) := by
  classical
  let k := e.1.card
  have hk : 3 ≤ k := edgeStar_card_ge_three e
  -- Inductively bound the number of matching edges in the prefix `{0..m}` of the path `P_{2k-1}`
  -- Specifically, count outer(0..m) and inner(0..m-1)
  let pref : ℕ → Finset (Fin e.1.card ⊕ Fin (e.1.card - 1)) := fun m =>
    Finset.univ.filter (fun s => match s with
      | Sum.inl i => i.val ≤ m
      | Sum.inr j => j.val < m)
  have hpref_full : pref (k - 1) = Finset.univ := by
    ext s; simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases s with i | j <;> dsimp <;> omega
  have hstep : ∀ m : ℕ, m < k →
      ((gadgetPart M e) ∩ pref m).card ≤ m + 1 ∧
      (((gadgetPart M e) ∩ pref m).card = m + 1 →
        ∀ i : Fin e.1.card, i.val ≤ m → Sum.inl i ∈ gadgetPart M e) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hsub : pref 0 ⊆ {Sum.inl ⟨0, by omega⟩} := by
        intro s hs
        simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        simp only [Finset.mem_singleton]
        rcases s with i | j
        · congr 1; exact Fin.ext (by dsimp at hs ⊢; omega)
        · dsimp at hs; omega
      have hle : ((gadgetPart M e) ∩ pref 0).card ≤ 1 := by
        calc ((gadgetPart M e) ∩ pref 0).card ≤ (pref 0).card := Finset.card_le_card Finset.inter_subset_right
          _ ≤ ({Sum.inl ⟨0, by omega⟩} : Finset _).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton _
      refine ⟨hle, fun heq i hi => ?_⟩
      have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by change i.val = 0; omega)
      subst hi0
      have hne : ((gadgetPart M e) ∩ pref 0).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨s, hs⟩ := hne
      have hs0 := Finset.mem_singleton.mp (hsub (Finset.mem_inter.mp hs).2)
      rw [← hs0]
      exact (Finset.mem_inter.mp hs).1
    | succ m ih =>
      intro hmk
      obtain ⟨ih_le, ih_eq⟩ := ih (by omega)
      let j : Fin (e.1.card - 1) := ⟨m, by omega⟩
      let i₁ : Fin e.1.card := ⟨m + 1, hmk⟩
      let i₀ : Fin e.1.card := ⟨m, by omega⟩
      have hpref_succ : pref (m + 1) = insert (Sum.inl i₁) (insert (Sum.inr j) (pref m)) := by
        ext s
        simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        rcases s with i | j'
        · simp only [Sum.inl.injEq, reduceCtorEq, false_or]
          constructor
          · intro h
            by_cases h1 : i.val = m + 1
            · exact Or.inl (Fin.ext h1)
            · exact Or.inr (by omega)
          · rintro (rfl | h)
            · simp [i₁]
            · omega
        · simp only [Sum.inr.injEq, reduceCtorEq, false_or]
          constructor
          · intro h
            by_cases h1 : j'.val = m
            · exact Or.inl (Fin.ext h1)
            · exact Or.inr (by omega)
          · rintro (rfl | h)
            · simp [j]
            · omega
      -- At most one of `Sum.inl i₁` and `Sum.inr j` is in `gadgetPart M e`
      have hnot_both : ¬ (Sum.inl i₁ ∈ gadgetPart M e ∧ Sum.inr j ∈ gadgetPart M e) := by
        rintro ⟨h1, h2⟩
        simp only [gadgetPart, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        have hdisj := hM h1 h2 (by simp)
        exact outer_not_disj_inner_left e j hdisj
      have hadd_le : ((gadgetPart M e) ∩ pref (m + 1)).card ≤
          ((gadgetPart M e) ∩ pref m).card + 1 := by
        rw [hpref_succ]
        have hsub : (gadgetPart M e) ∩ insert (Sum.inl i₁) (insert (Sum.inr j) (pref m)) ⊆
            ((gadgetPart M e) ∩ pref m) ∪ ((gadgetPart M e) ∩ {Sum.inl i₁, Sum.inr j}) := by
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton] at hx ⊢
          tauto
        have hpair_le : ((gadgetPart M e) ∩ {Sum.inl i₁, Sum.inr j}).card ≤ 1 := by
          by_cases h1 : Sum.inl i₁ ∈ gadgetPart M e
          · have h2 : Sum.inr j ∉ gadgetPart M e := fun h => hnot_both ⟨h1, h⟩
            have hsub2 : (gadgetPart M e) ∩ {Sum.inl i₁, Sum.inr j} ⊆ {Sum.inl i₁} := by
              intro x hx
              simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl
              · rfl
              · exact absurd hx.1 h2
            exact (Finset.card_le_card hsub2).trans (by simp)
          · have hsub2 : (gadgetPart M e) ∩ {Sum.inl i₁, Sum.inr j} ⊆ {Sum.inr j} := by
              intro x hx
              simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl
              · exact absurd hx.1 h1
              · rfl
            exact (Finset.card_le_card hsub2).trans (by simp)
        calc ((gadgetPart M e) ∩ insert (Sum.inl i₁) (insert (Sum.inr j) (pref m))).card
            ≤ (((gadgetPart M e) ∩ pref m) ∪ ((gadgetPart M e) ∩ {Sum.inl i₁, Sum.inr j})).card :=
              Finset.card_le_card hsub
          _ ≤ ((gadgetPart M e) ∩ pref m).card + ((gadgetPart M e) ∩ {Sum.inl i₁, Sum.inr j}).card :=
              Finset.card_union_le _ _
          _ ≤ ((gadgetPart M e) ∩ pref m).card + 1 := Nat.add_le_add_left hpair_le _
      refine ⟨by omega, fun heq => ?_⟩
      -- Equality forces `((gadgetPart M e) ∩ pref m).card = m + 1`, so `Sum.inl i₀ ∈ gadgetPart M e`,
      -- which forces `Sum.inr j ∉ gadgetPart M e`, which forces `Sum.inl i₁ ∈ gadgetPart M e`!
      have hprev_eq : ((gadgetPart M e) ∩ pref m).card = m + 1 := by omega
      have hall_prev := ih_eq hprev_eq
      have hi0_mem : Sum.inl i₀ ∈ gadgetPart M e := hall_prev i₀ le_rfl
      have hj_nmem : Sum.inr j ∉ gadgetPart M e := by
        intro hj_mem
        simp only [gadgetPart, Finset.mem_filter, Finset.mem_univ, true_and] at hi0_mem hj_mem
        exact outer_not_disj_inner_right e j (hM hi0_mem hj_mem (by simp))
      have hi1_mem : Sum.inl i₁ ∈ gadgetPart M e := by
        by_contra hi1_nmem
        have hsame : (gadgetPart M e) ∩ pref (m + 1) = (gadgetPart M e) ∩ pref m := by
          ext s
          rw [hpref_succ]
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hsM, rfl | rfl | hs⟩
            · exact absurd hsM hi1_nmem
            · exact absurd hsM hj_nmem
            · exact ⟨hsM, hs⟩
          · rintro ⟨hsM, hs⟩
            exact ⟨hsM, Or.inr (Or.inr hs)⟩
        rw [hsame] at heq
        omega
      intro i hi
      by_cases hlt : i.val ≤ m
      · exact hall_prev i hlt
      · have hi_eq : i = i₁ := Fin.ext (by change i.val = m + 1; omega)
        rw [hi_eq]; exact hi1_mem
  obtain ⟨hle, heq_fn⟩ := hstep (k - 1) (by omega)
  rw [hpref_full, Finset.inter_univ] at hle heq_fn
  refine ⟨by omega, fun heq => ?_⟩
  have hall_out : allOuter e ⊆ gadgetPart M e := by
    intro s hs
    rw [allOuter, Finset.mem_image] at hs
    obtain ⟨i, _, rfl⟩ := hs
    exact heq_fn (by omega) i (by omega)
  exact (Finset.eq_of_subset_of_card_le hall_out (by rw [allOuter_card, heq])).symm

/-! ## Part 5: Replacing `M` on finitely many gadgets -/

/-- Cardinality of `M \ N` and `N \ M` when `N` differs from `M` only on a finite set `S` of gadgets. -/
private lemma diff_ncard_replaceOn (M N : Set Edge) (S : Finset EdgeStar)
    (hagree : ∀ x : Edge, x.1 ∉ S → (x ∈ N ↔ x ∈ M)) :
    (M \ N).Finite ∧ (N \ M).Finite ∧
    ((N \ M).ncard : ℤ) - ((M \ N).ncard : ℤ) =
      ∑ e ∈ S, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) := by
  classical
  let proj : Finset Edge := S.sigma (fun e => Finset.univ)
  have hMN_sub : M \ N ⊆ (proj.filter (fun x => x ∈ M ∧ x ∉ N) : Set Edge) := by
    intro x ⟨hxM, hxN⟩
    have hxS : x.1 ∈ S := by
      by_contra hnot; exact hxN ((hagree x hnot).mpr hxM)
    simp only [Finset.mem_coe, Finset.mem_filter, proj, Finset.mem_sigma, Finset.mem_univ, and_true]
    exact ⟨hxS, hxM, hxN⟩
  have hMN_eq : M \ N = (proj.filter (fun x => x ∈ M ∧ x ∉ N) : Set Edge) := by
    refine Set.Subset.antisymm hMN_sub ?_
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    exact hx.2
  have hNM_eq : N \ M = (proj.filter (fun x => x ∈ N ∧ x ∉ M) : Set Edge) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x ⟨hxN, hxM⟩
      have hxS : x.1 ∈ S := by
        by_contra hnot; exact hxM ((hagree x hnot).mp hxN)
      simp only [Finset.mem_coe, Finset.mem_filter, proj, Finset.mem_sigma, Finset.mem_univ, and_true]
      exact ⟨hxS, hxN, hxM⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2
  refine ⟨by rw [hMN_eq]; exact Finset.finite_toSet _,
          by rw [hNM_eq]; exact Finset.finite_toSet _, ?_⟩
  rw [hNM_eq, hMN_eq, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hcard_NM : (proj.filter (fun x => x ∈ N ∧ x ∉ M)).card =
      ∑ e ∈ S, (gadgetPart N e \ gadgetPart M e).card := by
    have h1 : proj.filter (fun x => x ∈ N ∧ x ∉ M) =
        S.sigma (fun e => gadgetPart N e \ gadgetPart M e) := by
      ext ⟨e, s⟩
      simp [proj, gadgetPart]
    rw [h1, Finset.card_sigma]
  have hcard_MN : (proj.filter (fun x => x ∈ M ∧ x ∉ N)).card =
      ∑ e ∈ S, (gadgetPart M e \ gadgetPart N e).card := by
    have h1 : proj.filter (fun x => x ∈ M ∧ x ∉ N) =
        S.sigma (fun e => gadgetPart M e \ gadgetPart N e) := by
      ext ⟨e, s⟩
      simp [proj, gadgetPart]
    rw [h1, Finset.card_sigma]
  rw [hcard_NM, hcard_MN, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (gadgetPart N e \ gadgetPart M e).card + (gadgetPart N e ∩ gadgetPart M e).card =
      (gadgetPart N e).card := Finset.card_sdiff_add_card_inter _ _
  have h2 : (gadgetPart M e \ gadgetPart N e).card + (gadgetPart M e ∩ gadgetPart N e).card =
      (gadgetPart M e).card := Finset.card_sdiff_add_card_inter _ _
  rw [Finset.inter_comm] at h2
  omega

/-! ## Part 6: `H₁` has no strongly maximal matching -/

private lemma cardinal_mk_eq_ncard {α : Type} {s : Set α} (hs : s.Finite) :
    Cardinal.mk ↥s = (s.ncard : Cardinal) := by
  rw [← hs.coe_toFinset, Set.ncard_coe_finset, Cardinal.mk_fintype]
  simp

private theorem no_strongly_maximal_matching_H1 :
    ¬ ∃ F : Set Edge, IsMatching edgeSetH F ∧
        ∀ F' : Set Edge, IsMatching edgeSetH F' →
          Cardinal.mk ↥(F' \ F) ≤ Cardinal.mk ↥(F \ F') := by
  classical
  rintro ⟨M, hM_match, hM_strong⟩
  -- Step 1: In every gadget G_e, M must have at least |e| - 1 edges
  have hM_ge : ∀ e : EdgeStar, e.1.card - 1 ≤ (gadgetPart M e).card := by
    intro e
    by_contra hlt
    push Not at hlt
    -- Replace M on gadget e by allInner e
    let N : Set Edge := { x : Edge | if x.1 = e then x.2 ∈ allInner x.1 else x ∈ M }
    have hN_match : IsMatching edgeSetH N := by
      intro x hx y hy hxy
      by_cases hxe : x.1 = e <;> by_cases hye : y.1 = e
      · rcases x with ⟨ex, sx⟩; rcases y with ⟨ey, sy⟩
        dsimp only at hxe hye; subst hxe; subst hye
        simp only [N, Set.mem_ofPred_eq, ↓reduceIte, allInner, Finset.mem_image, Finset.mem_univ,
          true_and] at hx hy
        obtain ⟨jx, rfl⟩ := hx
        obtain ⟨jy, rfl⟩ := hy
        have hne : jx ≠ jy := fun h => hxy (by rw [h])
        exact inner_disj_inner _ hne
      · rcases x with ⟨ex, sx⟩
        dsimp only at hxe; subst hxe
        simp only [N, Set.mem_ofPred_eq, ↓reduceIte, allInner, Finset.mem_image, Finset.mem_univ,
          true_and] at hx
        obtain ⟨jx, rfl⟩ := hx
        exact inner_disj_other_gadget (Ne.symm hye) jx y.2
      · rcases y with ⟨ey, sy⟩
        dsimp only at hye; subst hye
        simp only [N, Set.mem_ofPred_eq, ↓reduceIte, allInner, Finset.mem_image, Finset.mem_univ,
          true_and] at hy
        obtain ⟨jy, rfl⟩ := hy
        exact (inner_disj_other_gadget (Ne.symm hxe) jy x.2).symm
      · simp only [N, Set.mem_ofPred_eq, hxe, hye, ↓reduceIte] at hx hy
        exact hM_match hx hy hxy
    have hagree : ∀ x : Edge, x.1 ∉ ({e} : Finset EdgeStar) → (x ∈ N ↔ x ∈ M) := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      simp [N, hx]
    obtain ⟨hMN_fin, hNM_fin, hdiff⟩ := diff_ncard_replaceOn M N {e} hagree
    have hNe : gadgetPart N e = allInner e := by
      ext s; simp [gadgetPart, N]
    rw [Finset.sum_singleton, hNe, allInner_card] at hdiff
    have hlt_card : (M \ N).ncard < (N \ M).ncard := by omega
    have hle_card := hM_strong N hN_match
    rw [cardinal_mk_eq_ncard hNM_fin, cardinal_mk_eq_ncard hMN_fin, Nat.cast_le] at hle_card
    omega
  -- Step 2: Induced matching M* of H₁* = {e | gadgetPart M e = allOuter e}
  let Mstar : Set EdgeStar := { e : EdgeStar | (gadgetPart M e).card = e.1.card }
  have hMstar_eq : ∀ e ∈ Mstar, gadgetPart M e = allOuter e := fun e he =>
    (gadget_matching_le_and_eq hM_match e).2 he
  have hMstar_not : ∀ e ∉ Mstar, (gadgetPart M e).card = e.1.card - 1 := fun e he => by
    have hle := (gadget_matching_le_and_eq hM_match e).1
    have hge := hM_ge e
    have hne : (gadgetPart M e).card ≠ e.1.card := he
    omega
  have hMstar_match : Mstar.Pairwise fun e₁ e₂ => Disjoint e₁.1 e₂.1 := by
    intro e₁ he₁ e₂ he₂ hne
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨i₁, hi₁⟩ := vtxOf_surj e₁ hv1
    obtain ⟨i₂, hi₂⟩ := vtxOf_surj e₂ hv2
    have hm1 : (⟨e₁, Sum.inl i₁⟩ : Edge) ∈ M := by
      have : Sum.inl i₁ ∈ gadgetPart M e₁ := by rw [hMstar_eq e₁ he₁]; simp [allOuter]
      exact (Finset.mem_filter.mp this).2
    have hm2 : (⟨e₂, Sum.inl i₂⟩ : Edge) ∈ M := by
      have : Sum.inl i₂ ∈ gadgetPart M e₂ := by rw [hMstar_eq e₂ he₂]; simp [allOuter]
      exact (Finset.mem_filter.mp this).2
    have hdisj := hM_match hm1 hm2 (fun h => hne (congrArg Sigma.fst h))
    have hv_mem1 : Sum.inl v ∈ edgeSetH ⟨e₁, Sum.inl i₁⟩ := by
      rw [← hi₁, edgeSetH, Finset.mem_coe]; dsimp only [edgeFinset]; split_ifs <;> simp
    have hv_mem2 : Sum.inl v ∈ edgeSetH ⟨e₂, Sum.inl i₂⟩ := by
      rw [← hi₂, edgeSetH, Finset.mem_coe]; dsimp only [edgeFinset]; split_ifs <;> simp
    exact Set.disjoint_left.mp hdisj hv_mem1 hv_mem2
  -- Step 3: Get better matching N* of H₁*
  obtain ⟨Nstar, hNstar_match, hMN_star_fin, hNM_star_fin, hstar_lt⟩ :=
    exists_better_matching_star Mstar hMstar_match
  let S_rem : Finset EdgeStar := hMN_star_fin.toFinset
  let S_add : Finset EdgeStar := hNM_star_fin.toFinset
  -- Finite set of base vertices in ⋃ (N* \ M*)
  let U_add : Finset ℕ := S_add.biUnion (fun e => e.1)
  -- For each v ∈ ℕ, there is at most one outer edge of M containing `Sum.inl v`
  have h_outer_unique : ∀ v : ℕ, ∃ e_opt : Option EdgeStar,
      (∀ e : EdgeStar, e_opt = some e →
        ∃ i : Fin e.1.card, (⟨e, Sum.inl i⟩ : Edge) ∈ M ∧ vtxOf e i = v) ∧
      (∀ (e : EdgeStar) (i : Fin e.1.card),
        (⟨e, Sum.inl i⟩ : Edge) ∈ M → vtxOf e i = v → e_opt = some e) := by
    intro v
    by_cases hex : ∃ (e : EdgeStar) (i : Fin e.1.card), (⟨e, Sum.inl i⟩ : Edge) ∈ M ∧ vtxOf e i = v
    · obtain ⟨e₀, i₀, hm₀, hv₀⟩ := hex
      refine ⟨some e₀, ?_, ?_⟩
      · intro e he
        injection he with he
        subst he
        exact ⟨i₀, hm₀, hv₀⟩
      · intro e i hm hv
        congr 1
        by_contra hne
        have hdisj := hM_match hm₀ hm (fun h => hne (congrArg Sigma.fst h))
        have h1 : Sum.inl v ∈ edgeSetH ⟨e₀, Sum.inl i₀⟩ := by
          rw [← hv₀, edgeSetH, Finset.mem_coe]; dsimp only [edgeFinset]; split_ifs <;> simp
        have h2 : Sum.inl v ∈ edgeSetH ⟨e, Sum.inl i⟩ := by
          rw [← hv, edgeSetH, Finset.mem_coe]; dsimp only [edgeFinset]; split_ifs <;> simp
        exact Set.disjoint_left.mp hdisj h1 h2
    · refine ⟨none, (fun _ he => by cases he), fun e i hm hv => absurd ⟨e, i, hm, hv⟩ hex⟩
  choose outerOwner h_outerOwner_mem h_outerOwner_eq using h_outer_unique
  let S_hit_raw : Finset EdgeStar := U_add.biUnion (fun v => (outerOwner v).toFinset)
  let S_hit : Finset EdgeStar := S_hit_raw \ (S_rem ∪ S_add)
  let S_all : Finset EdgeStar := S_rem ∪ S_add ∪ S_hit
  have hS_rem_add : Disjoint S_rem S_add := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rw [Set.Finite.mem_toFinset] at h1 h2
    exact h1.2 h2.1
  have hS_hit_disj : Disjoint (S_rem ∪ S_add) S_hit := disjoint_sdiff_self_right
  have hS_add_disj_rem_hit : Disjoint S_add (S_rem ∪ S_hit) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hS_rem_add.symm, Finset.disjoint_of_subset_left Finset.subset_union_right hS_hit_disj⟩
  -- Every e ∈ S_hit is NOT in Mstar (since if e ∈ Mstar and meets e' ∈ N* \ M*, then e ∉ N*, so e ∈ M* \ N* = S_rem!)
  have hS_hit_nMstar : ∀ e ∈ S_hit, e ∉ Mstar := by
    intro e he heMstar
    simp only [S_hit, Finset.mem_sdiff, Finset.mem_union] at he
    have he_raw := he.1
    simp only [S_hit_raw, Finset.mem_biUnion, Option.mem_toFinset] at he_raw
    obtain ⟨v, hvU, hown⟩ := he_raw
    simp only [U_add, Finset.mem_biUnion] at hvU
    obtain ⟨e', he'_add, hve'⟩ := hvU
    obtain ⟨i, _, hv_eq⟩ := h_outerOwner_mem v e hown
    have hve : v ∈ e.1 := hv_eq ▸ vtxOf_mem e i
    have hne : e ≠ e' := fun h => he.2 (Or.inr (h ▸ he'_add))
    have he'_Nstar : e' ∈ Nstar := (hNM_star_fin.mem_toFinset.mp he'_add).1
    have he_Nstar : e ∈ Nstar := by
      by_contra hnot
      exact he.2 (Or.inl (hMN_star_fin.mem_toFinset.mpr ⟨heMstar, hnot⟩))
    exact Finset.disjoint_left.mp (hNstar_match he_Nstar he'_Nstar hne) hve hve'
  -- Define improved matching N on H₁
  let N : Set Edge :=
    { x : Edge |
      if x.1 ∈ S_add then x.2 ∈ allOuter x.1
      else if x.1 ∈ S_rem ∪ S_hit then x.2 ∈ allInner x.1
      else x ∈ M }
  -- Helper: outer edge of S_add is disjoint from any edge of M outside S_all
  have hadd_disj_rest : ∀ {x y : Edge},
      x.1 ∈ S_add → x.2 ∈ allOuter x.1 → y.1 ∉ S_all → y ∈ M →
      Disjoint (edgeSetH x) (edgeSetH y) := by
    rintro ⟨e₁, s₁⟩ ⟨e₂, s₂⟩ he₁_add hs₁ he₂_nAll hyM
    dsimp only at he₁_add hs₁ he₂_nAll
    have hne : e₁ ≠ e₂ := fun h => he₂_nAll (by
      subst h
      simp only [S_all, Finset.mem_union]
      exact Or.inl (Or.inr he₁_add))
    simp only [allOuter, Finset.mem_image, Finset.mem_univ, true_and] at hs₁
    obtain ⟨i₁, rfl⟩ := hs₁
    rcases s₂ with i₂ | j₂
    · apply outer_disj_other_outer hne i₁ i₂
      intro hv_eq
      set v := vtxOf e₁ i₁
      have hvU : v ∈ U_add := by
        simp only [U_add, Finset.mem_biUnion]
        exact ⟨e₁, he₁_add, vtxOf_mem e₁ i₁⟩
      have hown : outerOwner v = some e₂ := h_outerOwner_eq v e₂ i₂ hyM hv_eq.symm
      have he₂_raw : e₂ ∈ S_hit_raw := by
        simp only [S_hit_raw, Finset.mem_biUnion, Option.mem_toFinset]
        exact ⟨v, hvU, hown⟩
      have he₂_nrem_add : e₂ ∉ S_rem ∪ S_add := fun h =>
        he₂_nAll (Finset.mem_union_left S_hit h)
      have he₂_hit : e₂ ∈ S_hit := Finset.mem_sdiff.mpr ⟨he₂_raw, he₂_nrem_add⟩
      exact he₂_nAll (Finset.mem_union_right (S_rem ∪ S_add) he₂_hit)
    · exact (inner_disj_other_gadget hne.symm j₂ (Sum.inl i₁)).symm
  -- Helper: inner edge of S_rem ∪ S_hit is disjoint from any other edge of N
  have hinner_disj_N : ∀ {x y : Edge},
      x.1 ∈ S_rem ∪ S_hit → x.2 ∈ allInner x.1 → y ∈ N → x ≠ y →
      Disjoint (edgeSetH x) (edgeSetH y) := by
    rintro ⟨e₁, s₁⟩ ⟨e₂, s₂⟩ he₁_rh hs₁ hyN hxy
    dsimp only at he₁_rh hs₁
    simp only [allInner, Finset.mem_image, Finset.mem_univ, true_and] at hs₁
    obtain ⟨j₁, rfl⟩ := hs₁
    by_cases heq : e₁ = e₂
    · subst heq
      have he₁_nadd : e₁ ∉ S_add := Finset.disjoint_right.mp hS_add_disj_rem_hit he₁_rh
      simp only [N, Set.mem_ofPred_eq, he₁_nadd, he₁_rh, ↓reduceIte, allInner, Finset.mem_image,
        Finset.mem_univ, true_and] at hyN
      obtain ⟨j₂, rfl⟩ := hyN
      have hjne : j₁ ≠ j₂ := fun h => hxy (by rw [h])
      exact inner_disj_inner e₁ hjne
    · exact inner_disj_other_gadget heq j₁ s₂
  have hN_match : IsMatching edgeSetH N := by
    intro x hx y hy hxy
    by_cases hx_add : x.1 ∈ S_add
    · have hx_out : x.2 ∈ allOuter x.1 := by
        simpa only [N, Set.mem_ofPred_eq, hx_add, ↓reduceIte] using hx
      by_cases hy_add : y.1 ∈ S_add
      · have hy_out : y.2 ∈ allOuter y.1 := by
          simpa only [N, Set.mem_ofPred_eq, hy_add, ↓reduceIte] using hy
        rcases x with ⟨e₁, s₁⟩; rcases y with ⟨e₂, s₂⟩
        dsimp only at hx_add hx_out hy_add hy_out
        simp only [allOuter, Finset.mem_image, Finset.mem_univ, true_and] at hx_out hy_out
        obtain ⟨i₁, rfl⟩ := hx_out
        obtain ⟨i₂, rfl⟩ := hy_out
        by_cases heq : e₁ = e₂
        · subst heq
          have hine : i₁ ≠ i₂ := fun h => hxy (by rw [h])
          exact outer_disj_outer e₁ hine
        · apply outer_disj_other_outer heq i₁ i₂
          intro hv
          have h1 : e₁ ∈ Nstar := (hNM_star_fin.mem_toFinset.mp hx_add).1
          have h2 : e₂ ∈ Nstar := (hNM_star_fin.mem_toFinset.mp hy_add).1
          exact Finset.disjoint_left.mp (hNstar_match h1 h2 heq) (vtxOf_mem e₁ i₁) (hv ▸ vtxOf_mem e₂ i₂)
      · by_cases hy_rh : y.1 ∈ S_rem ∪ S_hit
        · have hy_in : y.2 ∈ allInner y.1 := by
            simpa only [N, Set.mem_ofPred_eq, hy_add, hy_rh, ↓reduceIte] using hy
          exact (hinner_disj_N hy_rh hy_in hx hxy.symm).symm
        · have hy_nAll : y.1 ∉ S_all := by
            intro h
            simp only [S_all, Finset.mem_union] at h
            simp only [Finset.mem_union] at hy_rh
            tauto
          have hyM : y ∈ M := by
            simpa only [N, Set.mem_ofPred_eq, hy_add, hy_rh, ↓reduceIte] using hy
          exact hadd_disj_rest hx_add hx_out hy_nAll hyM
    · by_cases hx_rh : x.1 ∈ S_rem ∪ S_hit
      · have hx_in : x.2 ∈ allInner x.1 := by
          simpa only [N, Set.mem_ofPred_eq, hx_add, hx_rh, ↓reduceIte] using hx
        exact hinner_disj_N hx_rh hx_in hy hxy
      · have hx_nAll : x.1 ∉ S_all := by
          intro h
          simp only [S_all, Finset.mem_union] at h
          simp only [Finset.mem_union] at hx_rh
          tauto
        have hxM : x ∈ M := by
          simpa only [N, Set.mem_ofPred_eq, hx_add, hx_rh, ↓reduceIte] using hx
        by_cases hy_add : y.1 ∈ S_add
        · have hy_out : y.2 ∈ allOuter y.1 := by
            simpa only [N, Set.mem_ofPred_eq, hy_add, ↓reduceIte] using hy
          exact (hadd_disj_rest hy_add hy_out hx_nAll hxM).symm
        · by_cases hy_rh : y.1 ∈ S_rem ∪ S_hit
          · have hy_in : y.2 ∈ allInner y.1 := by
              simpa only [N, Set.mem_ofPred_eq, hy_add, hy_rh, ↓reduceIte] using hy
            exact (hinner_disj_N hy_rh hy_in hx hxy.symm).symm
          · have hyM : y ∈ M := by
              simpa only [N, Set.mem_ofPred_eq, hy_add, hy_rh, ↓reduceIte] using hy
            exact hM_match hxM hyM hxy
  -- Step 4: Compare |N \ M| and |M \ N| using diff_ncard_replaceOn
  have hagree : ∀ x : Edge, x.1 ∉ S_all → (x ∈ N ↔ x ∈ M) := by
    intro x hx
    have h1 : x.1 ∉ S_add := fun h => hx (Finset.mem_union_left S_hit (Finset.mem_union_right S_rem h))
    have h2 : x.1 ∉ S_rem ∪ S_hit := fun h => by
      simp only [Finset.mem_union] at h
      simp only [S_all, Finset.mem_union] at hx
      tauto
    simp only [N, Set.mem_ofPred_eq, h1, h2, ↓reduceIte]
  obtain ⟨hMN_fin, hNM_fin, hdiff⟩ := diff_ncard_replaceOn M N S_all hagree
  -- Compute per-gadget delta on S_rem, S_add, S_hit
  have hsum_split :
      ∑ e ∈ S_all, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) =
        (∑ e ∈ S_rem, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ))) +
        (∑ e ∈ S_add, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ))) +
        (∑ e ∈ S_hit, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ))) := by
    dsimp only [S_all]
    rw [Finset.sum_union hS_hit_disj, Finset.sum_union hS_rem_add]
  have hsum_rem :
      ∑ e ∈ S_rem, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) = -(S_rem.card : ℤ) := by
    have hterm : ∀ e ∈ S_rem, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) = -1 := by
      intro e he
      have he_nadd : e ∉ S_add := Finset.disjoint_left.mp hS_rem_add he
      have he_rh : e ∈ S_rem ∪ S_hit := Finset.mem_union_left S_hit he
      have hNe : gadgetPart N e = allInner e := by
        ext s
        simp only [gadgetPart, Finset.mem_filter, Finset.mem_univ, true_and, N, Set.mem_ofPred_eq,
          he_nadd, he_rh, ↓reduceIte]
      have he_Mstar : e ∈ Mstar := (hMN_star_fin.mem_toFinset.mp he).1
      have hMe : (gadgetPart M e).card = e.1.card := he_Mstar
      have hk := edgeStar_card_ge_three e
      rw [hNe, allInner_card, hMe]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  have hsum_add :
      ∑ e ∈ S_add, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) = (S_add.card : ℤ) := by
    have hterm : ∀ e ∈ S_add, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) = 1 := by
      intro e he
      have hNe : gadgetPart N e = allOuter e := by
        ext s
        simp only [gadgetPart, Finset.mem_filter, Finset.mem_univ, true_and, N, Set.mem_ofPred_eq,
          he, ↓reduceIte]
      have he_nMstar : e ∉ Mstar := (hNM_star_fin.mem_toFinset.mp he).2
      have hMe : (gadgetPart M e).card = e.1.card - 1 := hMstar_not e he_nMstar
      have hk := edgeStar_card_ge_three e
      rw [hNe, allOuter_card, hMe]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  have hsum_hit :
      ∑ e ∈ S_hit, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) = 0 := by
    have hterm : ∀ e ∈ S_hit, (((gadgetPart N e).card : ℤ) - ((gadgetPart M e).card : ℤ)) = 0 := by
      intro e he
      have he_rh : e ∈ S_rem ∪ S_hit := Finset.mem_union_right S_rem he
      have he_nadd : e ∉ S_add := Finset.disjoint_right.mp hS_add_disj_rem_hit he_rh
      have hNe : gadgetPart N e = allInner e := by
        ext s
        simp only [gadgetPart, Finset.mem_filter, Finset.mem_univ, true_and, N, Set.mem_ofPred_eq,
          he_nadd, he_rh, ↓reduceIte]
      have hMe : (gadgetPart M e).card = e.1.card - 1 := hMstar_not e (hS_hit_nMstar e he)
      rw [hNe, allInner_card, hMe]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero]
  rw [hsum_split, hsum_rem, hsum_add, hsum_hit] at hdiff
  have hcard_rem : S_rem.card = (Mstar \ Nstar).ncard :=
    (Set.ncard_eq_toFinset_card (Mstar \ Nstar) hMN_star_fin).symm
  have hcard_add : S_add.card = (Nstar \ Mstar).ncard :=
    (Set.ncard_eq_toFinset_card (Nstar \ Mstar) hNM_star_fin).symm
  have hlt_card : (M \ N).ncard < (N \ M).ncard := by omega
  have hle_card := hM_strong N hN_match
  rw [cardinal_mk_eq_ncard hNM_fin, cardinal_mk_eq_ncard hMN_fin, Nat.cast_le] at hle_card
  omega

theorem prove_main : ¬ type_of% @OMA.S_opg_strong_matchings_and_covers.main := by
  intro h
  have hinst := h Vert Edge edgeSetH 3 edgeSetH_props
  exact no_strongly_maximal_matching_H1 hinst.1

end OMA.P_opg_strong_matchings_and_covers

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_strong_matchings_and_covers.main) :=
  OMA.P_opg_strong_matchings_and_covers.prove_main
