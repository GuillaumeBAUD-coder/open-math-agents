import FormalConjectures.ErdosProblems.«1182»

open SimpleGraph

lemma OMA.emb {V : Type} (H : SimpleGraph V) (x : V) (k : ℕ)
    (hd : ∀ s : Finset V, s.card ≤ k → ∀ v ∈ s, ∃ w ∉ s, H.Adj v w) :
    ∀ (A : Type) [Fintype A] (G : SimpleGraph A), Fintype.card A = k + 1 → G.IsTree → G ⊑ H := by
  classical
  induction k with
  | zero =>
    intro A _ G hA _
    have := Fintype.card_le_one_iff_subsingleton.1 hA.le
    exact ⟨⟨⟨fun _ => x, fun h => (h.ne (Subsingleton.elim _ _)).elim⟩, fun a b _ => Subsingleton.elim a b⟩⟩
  | succ k ih =>
    intro A _ G hA hG
    have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, hu, hU⟩ := degree_eq_one_iff_existsUnique_adj.1 hv
    have hS : Fintype.card ({v}ᶜ : Set A) = k + 1 := by rw [Fintype.card_compl_set]; simp [hA]
    obtain ⟨f⟩ := ih (fun s hs => hd s (by omega)) _ _ hS
      ⟨hG.1.induce_compl_singleton_of_degree_eq_one hv, hG.2.induce _⟩
    obtain ⟨w, hn, hw⟩ := hd (Finset.univ.map f.toEmbedding) (by simp [hS]) (f ⟨u, hu.ne'⟩)
      (Finset.mem_map_of_mem _ (Finset.mem_univ _))
    refine ⟨⟨⟨fun a => if h : a = v then w else f ⟨a, h⟩, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
    · split_ifs <;> first | exact f.toHom.map_adj hab | grind [Adj.symm]
    · dsimp at hab
      split_ifs at hab <;> first | exact Subtype.mk.inj (f.injective hab) | exact (hn (hab ▸ Finset.mem_map_of_mem _ (Finset.mem_univ _))).elim | grind


theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.chvatal := by
  classical
  intro n T hT
  obtain ⟨⟨_, _⟩⟩ := hT.1.2
  refine IsLeast.csInf_eq ⟨fun C => ?_, fun N hN => ?_⟩
  · by_cases h3 : C.CliqueFree 3
    · right
      by_cases hd : ∃ v, n ≤ C.degree v
      · obtain ⟨v, hv⟩ := hd
        obtain ⟨t, ht, hc⟩ := Finset.exists_subset_card_eq (s := C.neighborFinset v) (by simpa using hv)
        exact (IsContained.of_le le_top).trans ((not_cliqueFree_iff_top_isContained n).mp fun h =>
          h t ⟨((isClique_compl C).2 (isIndepSet_neighborSet_of_triangleFree C h3 v)).subset
            (Set.subset_toFinset.1 ht), hc⟩)
      · refine OMA.emb _ ⟨0, by omega⟩ (n - 1) (fun s hs v hv => ?_) _ T (by simp; omega) hT
        obtain ⟨w, h1, h2⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := C.neighborFinset v)
          (t := sᶜ) (by simp [Finset.card_compl]; grind)
        simp at h1 h2
        exact ⟨w, h1, fun h => h1 (h ▸ hv), h2⟩
    · exact .inl ((not_cliqueFree_iff_top_isContained 3).mp h3)
  · by_contra! h
    have e := (Fin.castLEEmb (by omega : N ≤ 2 * (n - 1))).trans finProdFinEquiv.symm.toEmbedding
    rcases hN ((⊤ : SimpleGraph (Fin 2)).comap fun v => (e v).1) with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · have := Fin.le_of_injective (fun i => (e (f i)).1)
        fun i j h => by_contra fun hij => f.toHom.map_adj hij h
      omega
    · have k (i j) : (e (f i)).1 = (e (f j)).1 := by
        obtain ⟨w⟩ := hT.1.1 i j
        induction w with
        | nil => rfl
        | cons h _ ih => exact (not_ne_iff.1 (f.toHom.map_adj h).2).trans ih
      have := Fin.le_of_injective (fun i => (e (f i)).2)
        fun i j h => f.injective (e.injective (Prod.ext (k i j) h))
      omega
