import OMAReductions.R_Erdos917_erdos_917_variants_three_dvd_R1

namespace OMAHajos

open SimpleGraph

section Generic

variable {V : Type*}

lemma colorable_of_lt (G : SimpleGraph V) (h : G.chromaticNumber < 6) : G.Colorable 5 := by
  by_contra hc
  have h6 : (6 : ℕ) ≤ G.chromaticNumber :=
    (le_chromaticNumber_iff_not_colorable (G := G) (n := 6) (by norm_num)).mpr hc
  exact absurd h (not_lt.mpr (by exact_mod_cast h6))

lemma extract {G : SimpleGraph V} (hG : Erdos917.IsKCritical G 6) :
    ¬ G.Colorable 5 ∧
    (∀ a b, G.Adj a b → ∃ col : V → Fin 5,
      ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → col u ≠ col v) ∧
    (∀ w, ∃ col : V → Fin 5, ∀ u v, u ≠ w → v ≠ w → G.Adj u v → col u ≠ col v) := by
  obtain ⟨⟨hχ, hv⟩, he⟩ := hG
  have h5 : ¬ G.Colorable 5 := by
    intro hc
    have := hc.chromaticNumber_le
    rw [hχ] at this
    norm_num at this
  refine ⟨h5, ?_, ?_⟩
  · intro a b hab
    have hcrit := he s(a, b) hab
    unfold SimpleGraph.IsCriticalEdge SimpleGraph.IsCriticalEdges at hcrit
    rw [hχ] at hcrit
    obtain ⟨C⟩ := colorable_of_lt _ (by exact_mod_cast hcrit)
    refine ⟨C, fun u v huv hne => C.valid ?_⟩
    rw [deleteEdges_adj]
    exact ⟨huv, by simpa using hne⟩
  · intro w
    have hcrit := hv w
    unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at hcrit
    have htop : (⊤ : G.Subgraph).coe.chromaticNumber ≤ 6 := by
      have h6 : G.Colorable 6 := by
        rw [← chromaticNumber_le_iff_colorable, hχ]
      obtain ⟨C⟩ := h6
      exact Colorable.chromaticNumber_le ⟨Coloring.mk (fun v => C v.1) (fun h => C.valid h)⟩
    obtain ⟨C⟩ := colorable_of_lt _ (lt_of_lt_of_le hcrit htop)
    classical
    refine ⟨fun u => if h : u = w then 0 else C ⟨u, by simp [h]⟩, ?_⟩
    intro u v hu hv huv
    simp only [hu, hv, dite_false]
    apply C.valid
    simpa [hu, hv] using huv

lemma crit_of {H : SimpleGraph V} (h5 : ¬ H.Colorable 5)
    (hE : ∀ a b, H.Adj a b → ∃ col : V → Fin 5,
      ∀ u v, H.Adj u v → s(u, v) ≠ s(a, b) → col u ≠ col v)
    (hV : ∀ w, ∃ col : V → Fin 5, ∀ u v, u ≠ w → v ≠ w → H.Adj u v → col u ≠ col v) :
    Erdos917.IsKCritical H 6 := by
  classical
  have h6 : H.Colorable 6 := by
    rcases isEmpty_or_nonempty V with hV0 | ⟨⟨w⟩⟩
    · exact ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩
    · obtain ⟨col, hcol⟩ := hV w
      refine ⟨Coloring.mk (fun u => if u = w then Fin.last 5 else (col u).castSucc) ?_⟩
      intro u v huv
      by_cases hu : u = w
      · subst hu
        have hv : v ≠ u := huv.ne.symm
        simp only [if_neg hv]
        exact (Fin.castSucc_lt_last (col v)).ne'
      · by_cases hv : v = w
        · subst hv
          simp only [if_neg hu]
          exact (Fin.castSucc_lt_last (col u)).ne
        · simp only [if_neg hu, if_neg hv]
          exact fun h => hcol u v hu hv huv (Fin.castSucc_injective _ h)
  have h6le : (6 : ℕ∞) ≤ H.chromaticNumber := by
    have := (le_chromaticNumber_iff_not_colorable (G := H) (n := 6) (by norm_num)).mpr h5
    exact_mod_cast this
  have hχ : H.chromaticNumber = ((6 : ℕ) : ℕ∞) := le_antisymm h6.chromaticNumber_le h6le
  refine ⟨⟨hχ, fun w => ?_⟩, fun f hf => ?_⟩
  · unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    have htop : (6 : ℕ∞) ≤ (⊤ : H.Subgraph).coe.chromaticNumber := by
      have : ¬ (⊤ : H.Subgraph).coe.Colorable 5 := by
        rintro ⟨C⟩
        exact h5 ⟨Coloring.mk (fun v => C ⟨v, by simp⟩) (fun h => C.valid h)⟩
      have := (le_chromaticNumber_iff_not_colorable (n := 6) (by norm_num)).mpr this
      exact_mod_cast this
    obtain ⟨col, hcol⟩ := hV w
    have hdel : ((⊤ : H.Subgraph).deleteVerts {w}).coe.Colorable 5 := by
      refine ⟨Coloring.mk (fun v => col v.1) ?_⟩
      rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and] at hu hv
      simp only [Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.top_adj] at huv
      exact hcol u v hu hv huv.2.2.2.2
    have := hdel.chromaticNumber_le
    refine lt_of_le_of_lt this (lt_of_lt_of_le ?_ htop)
    norm_num
  · induction f using Sym2.ind with
    | _ a b =>
    unfold SimpleGraph.IsCriticalEdge SimpleGraph.IsCriticalEdges
    obtain ⟨col, hcol⟩ := hE a b hf
    have hdel : (H.deleteEdges {s(a, b)}).Colorable 5 := by
      refine ⟨Coloring.mk col ?_⟩
      intro u v huv
      rw [deleteEdges_adj] at huv
      exact hcol u v huv.1 (by simpa using huv.2)
    refine lt_of_le_of_lt hdel.chromaticNumber_le ?_
    rw [hχ]
    norm_num

lemma transfer {W : Type*} {H0 : SimpleGraph W} (eq : V ≃ W) (H : SimpleGraph V)
    (hH : ∀ u v, H.Adj u v ↔ H0.Adj (eq u) (eq v)) (h5 : ¬ H0.Colorable 5)
    (hE : ∀ a b, H0.Adj a b → ∃ col : W → Fin 5,
      ∀ u v, H0.Adj u v → s(u, v) ≠ s(a, b) → col u ≠ col v)
    (hV : ∀ w, ∃ col : W → Fin 5, ∀ u v, u ≠ w → v ≠ w → H0.Adj u v → col u ≠ col v) :
    Erdos917.IsKCritical H 6 := by
  apply crit_of
  · rintro ⟨C⟩
    refine h5 ⟨Coloring.mk (fun w => C (eq.symm w)) ?_⟩
    intro p q hpq
    apply C.valid
    rw [hH]
    simpa using hpq
  · intro a b hab
    obtain ⟨col, hcol⟩ := hE _ _ ((hH a b).mp hab)
    refine ⟨col ∘ eq, fun u v huv hne => hcol _ _ ((hH u v).mp huv) ?_⟩
    intro h
    apply hne
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [eq.injective h1, eq.injective h2]
    · rw [eq.injective h1, eq.injective h2, Sym2.eq_swap]
  · intro w
    obtain ⟨col, hcol⟩ := hV (eq w)
    exact ⟨col ∘ eq, fun u v hu hv huv =>
      hcol _ _ (eq.injective.ne hu) (eq.injective.ne hv) ((hH u v).mp huv)⟩

end Generic

section Hajos

variable {n : ℕ}

def g (x : Fin n) : Fin 6 → Fin n ⊕ Fin 5 := Fin.cases (Sum.inl x) Sum.inr

lemma g_zero (x : Fin n) : g x 0 = Sum.inl x := rfl

lemma g_succ (x : Fin n) (i : Fin 5) : g x i.succ = Sum.inr i := rfl

lemma g_one (x : Fin n) : g x 1 = Sum.inr 0 := rfl

lemma g_inj (x : Fin n) : Function.Injective (g x) := by
  intro i j h
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [g_zero, g_succ]

lemma g_eq_inl {x a : Fin n} {i : Fin 6} (h : g x i = Sum.inl a) : i = 0 ∧ x = a := by
  cases i using Fin.cases
  · simp_all [g_zero]
  · simp [g_succ] at h

def gE (x : Fin n) : Fin 6 ↪ Fin n ⊕ Fin 5 := ⟨g x, g_inj x⟩

def K' : SimpleGraph (Fin 6) := (⊤ : SimpleGraph (Fin 6)).deleteEdges {s(0, 1)}

lemma K'_adj {i j : Fin 6} : K'.Adj i j ↔ i ≠ j ∧ s(i, j) ≠ s(0, 1) := by
  simp [K', deleteEdges_adj]

def inlE : Fin n ↪ Fin n ⊕ Fin 5 := ⟨Sum.inl, Sum.inl_injective⟩

def H0 (G : SimpleGraph (Fin n)) (x y : Fin n) : SimpleGraph (Fin n ⊕ Fin 5) :=
  (G.deleteEdges {s(x, y)}).map inlE ⊔ K'.map (gE x) ⊔ SimpleGraph.edge (Sum.inl y) (Sum.inr 0)

lemma K6 (h : Fin 6 → Fin 5) (hh : ∀ i j, K'.Adj i j → h i ≠ h j) : h 0 = h 1 := by
  by_contra hne
  have hinj : Function.Injective h := by
    intro i j hij
    by_contra hij'
    by_cases hk : s(i, j) = s(0, 1)
    · rcases Sym2.eq_iff.mp hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne hij
      · exact hne hij.symm
    · exact hh i j (K'_adj.mpr ⟨hij', hk⟩) hij
  have := Fintype.card_le_of_injective h hinj
  simp at this

def phi (j0 : Fin 6) (k : Fin 6) : Fin 5 :=
  ⟨if k.val < j0.val then k.val else k.val - 1, by split <;> omega⟩

def dE (i0 j0 : Fin 6) (k : Fin 6) : Fin 5 := phi j0 (if k = j0 then i0 else k)

lemma dE_ne_aux : ∀ i0 j0 i j : Fin 6, i0 ≠ j0 → i ≠ j → ¬ (i = i0 ∧ j = j0) →
    ¬ (i = j0 ∧ j = i0) → dE i0 j0 i ≠ dE i0 j0 j := by
  decide

lemma dE_ne {i0 j0 i j : Fin 6} (h0 : i0 ≠ j0) (h : i ≠ j) (hs : s(i, j) ≠ s(i0, j0)) :
    dE i0 j0 i ≠ dE i0 j0 j := by
  apply dE_ne_aux i0 j0 i j h0 h
  · rintro ⟨rfl, rfl⟩; exact hs rfl
  · rintro ⟨rfl, rfl⟩; exact hs Sym2.eq_swap


variable (G : SimpleGraph (Fin n)) (x y : Fin n)

lemma glue (Ok : Fin n ⊕ Fin 5 → Fin n ⊕ Fin 5 → Prop) (c : Fin n → Fin 5) (d : Fin 6 → Fin 5)
    (Hc : ∀ a b, G.Adj a b → s(a, b) ≠ s(x, y) → Ok (Sum.inl a) (Sum.inl b) → c a ≠ c b)
    (Hd : ∀ i j, K'.Adj i j → Ok (g x i) (g x j) → d i ≠ d j)
    (Hyz : Ok (Sum.inl y) (Sum.inr 0) ∨ Ok (Sum.inr 0) (Sum.inl y) →
      (d 1 = d 0 ∧ c y ≠ c x) ∨ (d 1 ≠ d 0 ∧ c y = c x)) :
    ∃ col : Fin n ⊕ Fin 5 → Fin 5, ∀ p q, (H0 G x y).Adj p q → Ok p q → col p ≠ col q := by
  classical
  let σ := Equiv.swap (d 0) (c x)
  let col : Fin n ⊕ Fin 5 → Fin 5 := Sum.elim c (fun j => σ (d j.succ))
  have hg : ∀ i, col (g x i) = σ (d i) := by
    intro i
    cases i using Fin.cases
    · simp [col, σ, g_zero]
    · rfl
  have h1 : col (Sum.inr 0) = σ (d 1) := rfl
  have hcx : σ (d 0) = c x := Equiv.swap_apply_left _ _
  have hyz : (Ok (Sum.inl y) (Sum.inr 0) ∨ Ok (Sum.inr 0) (Sum.inl y)) → c y ≠ σ (d 1) := by
    intro hok
    rcases Hyz hok with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, hcx]; exact h2
    · rw [h2, ← hcx]; exact (σ.injective.ne h1).symm
  refine ⟨col, ?_⟩
  intro p q hpq hok
  rcases hpq with (hA | hB) | hC
  · obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj _ _ _ _).mp hA
    rw [deleteEdges_adj] at hab
    exact Hc a b hab.1 (by simpa using hab.2) hok
  · obtain ⟨i, j, hij, rfl, rfl⟩ := (map_adj _ _ _ _).mp hB
    change col (g x i) ≠ col (g x j)
    rw [hg, hg]
    exact σ.injective.ne (Hd i j hij hok)
  · rw [edge_adj] at hC
    rcases hC.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hyz (Or.inl hok)
    · exact (hyz (Or.inr hok)).symm

lemma adjA {a b : Fin n} (h : G.Adj a b) (hne : s(a, b) ≠ s(x, y)) :
    (H0 G x y).Adj (Sum.inl a) (Sum.inl b) := by
  left; left
  exact (map_adj _ _ _ _).mpr ⟨a, b, by rw [deleteEdges_adj]; exact ⟨h, by simpa using hne⟩, rfl, rfl⟩

lemma adjB {i j : Fin 6} (h : K'.Adj i j) : (H0 G x y).Adj (g x i) (g x j) := by
  left; right
  exact (map_adj _ _ _ _).mpr ⟨i, j, h, rfl, rfl⟩

lemma adjC : (H0 G x y).Adj (Sum.inl y) (Sum.inr 0) := by
  right
  rw [edge_adj]
  simp

lemma not5 (hG5 : ¬ G.Colorable 5) (hxy : G.Adj x y) : ¬ (H0 G x y).Colorable 5 := by
  rintro ⟨C⟩
  have hK : C (g x 0) = C (g x 1) := K6 (fun i => C (g x i)) (fun i j h => C.valid (adjB G x y h))
  rw [g_zero, g_one] at hK
  have hyC : C (Sum.inl y) ≠ C (Sum.inr 0) := C.valid (adjC G x y)
  apply hG5
  refine ⟨Coloring.mk (fun a => C (Sum.inl a)) ?_⟩
  intro a b hab
  by_cases hk : s(a, b) = s(x, y)
  · rcases Sym2.eq_iff.mp hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hK]; exact hyC.symm
    · rw [hK]; exact hyC
  · exact C.valid (adjA G x y hab hk)

lemma sym2_inl {a b a' b' : Fin n} (h : s(a', b') = s(a, b)) :
    s((Sum.inl a' : Fin n ⊕ Fin 5), Sum.inl b') = s(Sum.inl a, Sum.inl b) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

lemma sym2_g {i j i0 j0 : Fin 6} (h : s(g x i, g x j) = s(g x i0, g x j0)) :
    s(i, j) = s(i0, j0) := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [g_inj x h1, g_inj x h2]
  · rw [g_inj x h1, g_inj x h2]; exact Sym2.eq_swap

lemma goodxy (hG5 : ¬ G.Colorable 5) (c : Fin n → Fin 5)
    (hc : ∀ u v, G.Adj u v → s(u, v) ≠ s(x, y) → c u ≠ c v) : c x = c y := by
  by_contra hne
  apply hG5
  refine ⟨Coloring.mk c ?_⟩
  intro u v huv
  by_cases hk : s(u, v) = s(x, y)
  · rcases Sym2.eq_iff.mp hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact fun h => hne h.symm
  · exact hc u v huv hk

lemma d01 : dE 0 1 1 = dE 0 1 0 := by decide

lemma hE0 (hG5 : ¬ G.Colorable 5)
    (hGE : ∀ a b, G.Adj a b → ∃ col : Fin n → Fin 5,
      ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → col u ≠ col v)
    (hxy : G.Adj x y) :
    ∀ p q, (H0 G x y).Adj p q → ∃ col : Fin n ⊕ Fin 5 → Fin 5,
      ∀ u v, (H0 G x y).Adj u v → s(u, v) ≠ s(p, q) → col u ≠ col v := by
  obtain ⟨c0, hc0⟩ := hGE x y hxy
  have hc0xy := goodxy G x y hG5 c0 hc0
  intro p q hpq
  rcases hpq with (hA | hB) | hC
  · obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj _ _ _ _).mp hA
    rw [deleteEdges_adj] at hab
    have hab2 : s(a, b) ≠ s(x, y) := by simpa using hab.2
    obtain ⟨c, hc⟩ := hGE a b hab.1
    apply glue G x y _ c (dE 0 1)
    · intro a' b' h1 _ h3
      exact hc a' b' h1 (fun h => h3 (sym2_inl h))
    · intro i j hij _
      rw [K'_adj] at hij
      exact dE_ne (by decide) hij.1 hij.2
    · intro _
      left
      refine ⟨d01, fun h => hc x y hxy (fun h' => hab2 h'.symm) h.symm⟩
  · obtain ⟨i0, j0, hij0, rfl, rfl⟩ := (map_adj _ _ _ _).mp hB
    change ∃ col : Fin n ⊕ Fin 5 → Fin 5,
      ∀ u v, (H0 G x y).Adj u v → s(u, v) ≠ s(g x i0, g x j0) → col u ≠ col v
    rw [K'_adj] at hij0
    apply glue G x y _ c0 (dE i0 j0)
    · intro a' b' h1 h2 _
      exact hc0 a' b' h1 h2
    · intro i j hij h
      rw [K'_adj] at hij
      refine dE_ne hij0.1 hij.1 (fun h' => h ?_)
      rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    · intro _
      right
      refine ⟨dE_ne hij0.1 (by decide) ?_, hc0xy.symm⟩
      intro h
      exact hij0.2 (h.symm.trans Sym2.eq_swap)
  · rw [edge_adj] at hC
    apply glue G x y _ c0 (dE 0 1)
    · intro a' b' h1 h2 _
      exact hc0 a' b' h1 h2
    · intro i j hij _
      rw [K'_adj] at hij
      exact dE_ne (by decide) hij.1 hij.2
    · rintro (h | h)
      · exfalso
        rcases hC.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h rfl
        · exact h Sym2.eq_swap
      · exfalso
        rcases hC.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h Sym2.eq_swap
        · exact h rfl

lemma hV0 (hG5 : ¬ G.Colorable 5)
    (hGE : ∀ a b, G.Adj a b → ∃ col : Fin n → Fin 5,
      ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → col u ≠ col v)
    (hGV : ∀ w, ∃ col : Fin n → Fin 5, ∀ u v, u ≠ w → v ≠ w → G.Adj u v → col u ≠ col v)
    (hxy : G.Adj x y) :
    ∀ w, ∃ col : Fin n ⊕ Fin 5 → Fin 5,
      ∀ u v, u ≠ w → v ≠ w → (H0 G x y).Adj u v → col u ≠ col v := by
  obtain ⟨c0, hc0⟩ := hGE x y hxy
  have hc0xy := goodxy G x y hG5 c0 hc0
  intro w
  suffices h : ∃ col : Fin n ⊕ Fin 5 → Fin 5,
      ∀ p q, (H0 G x y).Adj p q → (p ≠ w ∧ q ≠ w) → col p ≠ col q by
    obtain ⟨col, hcol⟩ := h
    exact ⟨col, fun u v hu hv huv => hcol u v huv ⟨hu, hv⟩⟩
  have hK01 : ∀ i j, K'.Adj i j → dE 0 1 i ≠ dE 0 1 j := by
    intro i j hij
    rw [K'_adj] at hij
    exact dE_ne (by decide) hij.1 hij.2
  rcases w with a | j
  · obtain ⟨c, hc⟩ := hGV a
    have Hc : ∀ a' b', G.Adj a' b' → s(a', b') ≠ s(x, y) →
        (Sum.inl a' ≠ (Sum.inl a : Fin n ⊕ Fin 5) ∧ Sum.inl b' ≠ (Sum.inl a : Fin n ⊕ Fin 5)) →
        c a' ≠ c b' := by
      intro a' b' h1 _ h3
      exact hc a' b' (fun h => h3.1 (by rw [h])) (fun h => h3.2 (by rw [h])) h1
    by_cases ha : a = x
    · subst ha
      by_cases hcy : c y = c a
      · apply glue G a y _ c (dE 0 2) Hc
        · intro i j hij hok
          rw [K'_adj] at hij
          have hi : i ≠ 0 := by rintro rfl; exact hok.1 rfl
          have hj : j ≠ 0 := by rintro rfl; exact hok.2 rfl
          refine dE_ne (by decide) hij.1 ?_
          intro h
          rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hi h1
          · exact hj h2
        · intro _
          right
          exact ⟨by decide, hcy⟩
      · apply glue G a y _ c (dE 0 1) Hc
        · intro i j hij _
          exact hK01 i j hij
        · intro _
          left
          exact ⟨d01, hcy⟩
    · apply glue G x y _ c (dE 0 1) Hc
      · intro i j hij _
        exact hK01 i j hij
      · intro h
        have hy : y ≠ a := by
          rintro rfl
          rcases h with h | h
          · exact h.1 rfl
          · exact h.2 rfl
        left
        exact ⟨d01, fun h' => hc x y (Ne.symm ha) hy hxy h'.symm⟩
  · apply glue G x y _ c0 (dE j.succ 0)
    · intro a' b' h1 h2 _
      exact hc0 a' b' h1 h2
    · intro i i' hii' hok
      rw [K'_adj] at hii'
      have hi : i ≠ j.succ := by rintro rfl; exact hok.1 rfl
      have hi' : i' ≠ j.succ := by rintro rfl; exact hok.2 rfl
      refine dE_ne (Fin.succ_ne_zero j) hii'.1 ?_
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hi h1
      · exact hi' h2
    · intro h
      have hj : j ≠ 0 := by
        rintro rfl
        rcases h with h | h
        · exact h.2 rfl
        · exact h.1 rfl
      right
      refine ⟨dE_ne (Fin.succ_ne_zero j) (by decide) ?_, hc0xy.symm⟩
      intro h'
      rcases Sym2.eq_iff.mp h' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hj (Fin.succ_injective _ (h1.symm.trans rfl))
      · exact absurd h1 (by decide)

lemma top6 : (⊤ : SimpleGraph (Fin 6)).edgeSet.ncard = 15 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
  decide

lemma countK : K'.edgeSet.ncard = 14 := by
  have hm : s((0 : Fin 6), 1) ∈ (⊤ : SimpleGraph (Fin 6)).edgeSet := by
    rw [mem_edgeSet]; decide
  have := Set.ncard_sdiff_singleton_add_one hm (Set.toFinite _)
  rw [top6] at this
  unfold K'
  rw [edgeSet_deleteEdges]
  omega

lemma count (hxy : G.Adj x y) : (H0 G x y).edgeSet.ncard = G.edgeSet.ncard + 14 := by
  have hdisj1 : Disjoint ((G.deleteEdges {s(x, y)}).map inlE).edgeSet (K'.map (gE x)).edgeSet := by
    rw [Set.disjoint_left]
    intro z
    induction z using Sym2.ind with
    | _ p q =>
    intro h1 h2
    rw [mem_edgeSet] at h1 h2
    obtain ⟨a, b, _, rfl, rfl⟩ := (map_adj _ _ _ _).mp h1
    obtain ⟨i, j, hij, hi, hj⟩ := (map_adj _ _ _ _).mp h2
    have hi' := g_eq_inl (x := x) (i := i) (a := a) hi
    have hj' := g_eq_inl (x := x) (i := j) (a := b) hj
    rw [hi'.1, hj'.1] at hij
    exact hij.ne rfl
  have hne : (Sum.inl y : Fin n ⊕ Fin 5) ≠ Sum.inr 0 := by simp
  have hdisj2 : Disjoint (((G.deleteEdges {s(x, y)}).map inlE).edgeSet ∪ (K'.map (gE x)).edgeSet)
      (SimpleGraph.edge (Sum.inl y) (Sum.inr 0)).edgeSet := by
    rw [edgeSet_edge_of_ne hne, Set.disjoint_singleton_right]
    rintro (h | h)
    · rw [mem_edgeSet] at h
      obtain ⟨a, b, _, _, hb⟩ := (map_adj _ _ _ _).mp h
      simp [inlE] at hb
    · rw [mem_edgeSet] at h
      obtain ⟨i, j, _, hi, _⟩ := (map_adj _ _ _ _).mp h
      have hi' := g_eq_inl (x := x) (i := i) (a := y) hi
      exact hxy.ne hi'.2
  unfold H0
  rw [edgeSet_sup, edgeSet_sup, Set.ncard_union_eq hdisj2, Set.ncard_union_eq hdisj1,
    edgeSet_map, Set.ncard_image_of_injective _ (Function.Embedding.injective _),
    edgeSet_map, Set.ncard_image_of_injective _ (Function.Embedding.injective _),
    edgeSet_deleteEdges, countK, edgeSet_edge_of_ne hne, Set.ncard_singleton]
  have hm : s(x, y) ∈ G.edgeSet := hxy
  have := Set.ncard_sdiff_singleton_add_one hm (Set.toFinite _)
  omega

end Hajos

end OMAHajos

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_three_dvd_R1.H3 := by
  rintro n e ⟨G, hG, hGe⟩
  obtain ⟨hG5, hGE, hGV⟩ := OMAHajos.extract hG
  obtain ⟨x, y, hxy⟩ : ∃ x y, G.Adj x y := by
    by_contra h
    apply hG5
    refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
    intro a b hab
    exact absurd ⟨a, b, hab⟩ h
  let eq : Fin (n + 5) ≃ Fin n ⊕ Fin 5 := finSumFinEquiv.symm
  refine ⟨(OMAHajos.H0 G x y).map eq.symm.toEmbedding, ?_, ?_⟩
  · apply OMAHajos.transfer eq _ _ (OMAHajos.not5 G x y hG5 hxy) (OMAHajos.hE0 G x y hG5 hGE hxy)
      (OMAHajos.hV0 G x y hG5 hGE hGV hxy)
    intro u v
    rw [SimpleGraph.map_symm]
    rfl
  · rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ (Function.Embedding.injective _),
      OMAHajos.count G x y hxy, hGe]
