import FormalConjectures.Wikipedia.GracefulLabeling

/-!
# A reduction of the Graceful Tree Conjecture

Credit goes to @ysanatomic.

Inductively, delete a leaf, reflect the smaller labeling so the leaf's parent has label
at most (m - 1) / 2, and restore the leaf at its parent's label plus m. This realizes
all m lengths. The first step asks to compress the labels to span at most m + 1.

If both endpoints of this interval occur, joining them adds a new edge of length m + 1,
forming a gracefully labeled unicyclic graph. The second step asks whether removing
this longest edge from its cycle always leaves a tree that can be gracefully relabeled.
-/

namespace OMA.R_GracefulLabeling_graceful_tree_conjecture_R1

open SimpleGraph

/-- Compress a labeling with every edge length to a range with one spare position. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree →
    let m := T.edgeFinset.card
    (∃ f : V → ℕ, Function.Injective f ∧ (∀ v, f v ≤ m + (m - 1) / 2) ∧
      ∀ d ∈ Finset.Icc 1 m, ∃ a b, T.Adj a b ∧ Nat.dist (f a) (f b) = d) →
    ∃ g : V → ℕ, Function.Injective g ∧ (∀ v, g v ≤ m + 1) ∧
      ∀ d ∈ Finset.Icc 1 m, ∃ a b, T.Adj a b ∧ Nat.dist (g a) (g b) = d

/-- Delete the longest edge of a gracefully labeled unicyclic graph when that edge lies
on its cycle. The resulting tree may be relabeled. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → ∀ u v : V, u ≠ v → ¬T.Adj u v →
    let q := T.edgeFinset.card + 1
    (∃ f : V → ℕ, Function.Injective f ∧ (∀ x, f x ≤ q) ∧ f u = 0 ∧ f v = q ∧
      ∀ d ∈ Finset.Icc 1 q, ∃ a b, (T ⊔ edge u v).Adj a b ∧ Nat.dist (f a) (f b) = d) →
    ∃ g : V → ℕ, Function.Injective g ∧ (∀ x, g x ≤ q - 1) ∧
      ∀ d ∈ Finset.Icc 1 (q - 1), ∃ a b, T.Adj a b ∧ Nat.dist (g a) (g b) = d

lemma bounds_of_coverage {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (f : V → ℕ)
    (hf : ∀ d ∈ Finset.Icc 1 T.edgeFinset.card, ∃ a b, T.Adj a b ∧ Nat.dist (f a) (f b) = d)
    {u v : V} (huv : T.Adj u v) : Nat.dist (f u) (f v) ≤ T.edgeFinset.card := by
  let length : Sym2 V → ℕ := Sym2.lift ⟨fun a b => Nat.dist (f a) (f b), fun a b => Nat.dist_comm ..⟩
  have heq : Finset.Icc 1 T.edgeFinset.card = T.edgeFinset.image length := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      obtain ⟨a,b,hab,he⟩ := hf d hd
      exact Finset.mem_image.mpr ⟨s(a,b), mem_edgeFinset.mpr hab, he⟩
    · simpa using Finset.card_image_le (s := T.edgeFinset) (f := length)
  have hmem : length s(u,v) ∈ T.edgeFinset.image length :=
    Finset.mem_image_of_mem _ (mem_edgeFinset.mpr huv)
  rw [← heq] at hmem
  exact (Finset.mem_Icc.mp hmem).2

lemma compress_span (h₁ : H1) (h₂ : H2) {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    let m := T.edgeFinset.card
    (∃ f : V → ℕ, Function.Injective f ∧ (∀ v, f v ≤ m + (m - 1) / 2) ∧
      ∀ d ∈ Finset.Icc 1 m, ∃ a b, T.Adj a b ∧ Nat.dist (f a) (f b) = d) →
    ∃ g : V → ℕ, Function.Injective g ∧ (∀ v, g v ≤ m) ∧
      ∀ d ∈ Finset.Icc 1 m, ∃ a b, T.Adj a b ∧ Nat.dist (g a) (g b) = d := by
  intro m hwide
  obtain ⟨f, hi, hb, hc⟩ := h₁ T hT hwide
  by_cases htop : ∃ v, f v = m + 1
  · obtain ⟨v,hv⟩ := htop
    by_cases hzero : ∃ u, f u = 0
    · obtain ⟨u,hu⟩ := hzero
      have hne : u ≠ v := by rintro rfl; omega
      have hnon : ¬T.Adj u v := by
        intro hadj
        have := bounds_of_coverage T f hc hadj
        simp only [hu,hv,Nat.dist] at this
        dsimp [m] at *
        omega
      apply h₂ T hT u v hne hnon
      refine ⟨f, hi, hb, hu, hv, ?_⟩
      intro d hd
      obtain ⟨hd1,hd2⟩ := Finset.mem_Icc.mp hd
      by_cases hdm : d ≤ m
      · obtain ⟨a,b,hab,hlen⟩ := hc d (Finset.mem_Icc.mpr ⟨hd1,hdm⟩)
        exact ⟨a,b,Or.inl hab,hlen⟩
      · have hlast : d = m + 1 := by omega
        exact ⟨u,v,Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩), by simp [hu,hv,hlast,Nat.dist]⟩
    · push Not at hzero
      refine ⟨fun x => f x - 1, ?_, ?_, ?_⟩
      · intro x y h
        apply hi
        have := hzero x
        have := hzero y
        dsimp at h
        omega
      · intro x
        have := hb x
        change f x - 1 ≤ T.edgeFinset.card
        omega
      · intro d hd
        obtain ⟨a,b,hab,he⟩ := hc d hd
        refine ⟨a,b,hab,?_⟩
        have := hzero a
        have := hzero b
        simp only [Nat.dist] at he ⊢
        omega
  · push Not at htop
    refine ⟨f,hi,?_,hc⟩
    intro x
    have hx := htop x
    have hb' : f x ≤ m + 1 := hb x
    omega

/-- Reflect, if necessary, to put a specified vertex in the lower half. -/
lemma orient_labeling {V : Type*} (T : SimpleGraph V) (n : ℕ) (r : V)
    (f : V → ℕ) (hf : Function.Injective f) (hb : ∀ v, f v ≤ n)
    (hd : ∀ d ∈ Finset.Icc 1 n, ∃ x y, T.Adj x y ∧ Nat.dist (f x) (f y) = d) :
    ∃ g : V → ℕ, Function.Injective g ∧ (∀ v, g v ≤ n) ∧ g r ≤ n / 2 ∧
      ∀ d ∈ Finset.Icc 1 n, ∃ x y, T.Adj x y ∧ Nat.dist (g x) (g y) = d := by
  by_cases h : f r ≤ n / 2
  · exact ⟨f, hf, hb, h, hd⟩
  have hr : n - f r ≤ n / 2 := by
    have := hb r
    omega
  refine ⟨fun x => n - f x, ?_, fun _ => Nat.sub_le .., hr, ?_⟩
  · intro x y hxy
    apply hf
    have := hb x
    have := hb y
    dsimp at hxy
    omega
  · intro d hmem
    obtain ⟨x, y, hxy, heq⟩ := hd d hmem
    refine ⟨x, y, hxy, ?_⟩
    have := hb x
    have := hb y
    dsimp [Nat.dist] at heq ⊢
    omega

/-- Extend a labeling on the complement of one leaf, after orienting it
at the neighbor. The removed vertex takes label n + 1 + g(r). -/
lemma extend_one_vertex {V : Type*} [DecidableEq V] (T : SimpleGraph V)
    (v r : V) (hr : T.Adj v r) (n : ℕ)
    (old : ∃ f : ({v}ᶜ : Set V) → ℕ, Function.Injective f ∧ (∀ x, f x ≤ n) ∧
      ∀ d ∈ Finset.Icc 1 n, ∃ x y, (T.induce {v}ᶜ).Adj x y ∧ Nat.dist (f x) (f y) = d) :
    ∃ F : V → ℕ, Function.Injective F ∧ (∀ x, F x ≤ n + 1 + n / 2) ∧
      ∀ d ∈ Finset.Icc 1 (n + 1), ∃ x y, T.Adj x y ∧ Nat.dist (F x) (F y) = d := by
  obtain ⟨f, hf, hb, hd⟩ := old
  let r' : ({v}ᶜ : Set V) := ⟨r, hr.ne.symm⟩
  obtain ⟨g, hg, hgb, hgr, hgd⟩ := orient_labeling (T.induce {v}ᶜ) n r' f hf hb hd
  let F (x : V) := if hx : x = v then n + 1 + g r' else g ⟨x, hx⟩
  have hold (x : ({v}ᶜ : Set V)) : F x = g x := by
    have hne : x.val ≠ v := x.property
    simp [F, hne]
  have hleaf : F v = n + 1 + g r' := by simp [F]
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      by_contra h
      have hy : y ≠ v := Ne.symm h
      have hlt := hgb ⟨y, hy⟩
      rw [hleaf, hold ⟨y,hy⟩] at hxy
      omega
    · by_cases hy : y = v
      · subst y
        have hlt := hgb ⟨x, hx⟩
        rw [hold ⟨x,hx⟩, hleaf] at hxy
        omega
      · rw [hold ⟨x,hx⟩, hold ⟨y,hy⟩] at hxy
        exact congrArg Subtype.val (hg hxy)
  · intro x
    by_cases hx : x = v
    · subst x
      omega
    · rw [hold ⟨x,hx⟩]
      exact (hgb _).trans (by omega)
  · intro d hm
    obtain ⟨hpos, hmax⟩ := Finset.mem_Icc.mp hm
    by_cases hdn : d ≤ n
    · obtain ⟨x, y, hxy, heq⟩ := hgd d (Finset.mem_Icc.mpr ⟨hpos, hdn⟩)
      exact ⟨x, y, hxy, by rwa [hold x, hold y]⟩
    · refine ⟨v, r, hr, ?_⟩
      rw [hleaf, hold r']
      dsimp [Nat.dist]
      omega

lemma bounded_of_compression (h₁ : H1) (h₂ : H2)
    (n : ℕ) : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree → T.edgeFinset.card = n →
      ∃ f : V → ℕ, Function.Injective f ∧ (∀ v, f v ≤ n) ∧
         ∀ d ∈ Finset.Icc 1 n, ∃ x y, T.Adj x y ∧ Nat.dist (f x) (f y) = d := by
  induction n with
  | zero =>
    intro V _ _ T _ hT h0
    have hcard := hT.card_edgeFinset
    have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim .., fun _ => le_rfl, by simp⟩
  | succ n ih =>
    intro V _ _ T _ hT hc
    have hcard := hT.card_edgeFinset
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨r, hvr, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    let S := T.induce {v}ᶜ
    have hS : S.IsTree := ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
      hT.isAcyclic.induce _⟩
    have hsub : Fintype.card ({v}ᶜ : Set V) = Fintype.card V - 1 := by
      rw [Fintype.card_compl_set]
      simp
    have hsmall : S.edgeFinset.card = n := by
      have hs := hS.card_edgeFinset
      omega
    have old := ih S hS hsmall
    have wide := extend_one_vertex T v r hvr n old
    have tighten := compress_span h₁ h₂ T hT
    dsimp only at tighten
    rw [hc] at tighten
    exact tighten (by simpa using wide)

/-- A result for all finite graphs on small types applies in every universe. -/
lemma graceful_of_small_bounded
    (hsmall : ∀ {W : Type} [Fintype W] [DecidableEq W]
      (S : SimpleGraph W) [DecidableRel S.Adj], S.IsTree →
      let m := S.edgeFinset.card
      ∃ f : W → ℕ, Function.Injective f ∧ (∀ v, f v ≤ m) ∧
        ∀ d ∈ Finset.Icc 1 m, ∃ x y, S.Adj x y ∧ Nat.dist (f x) (f y) = d)
    {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) :
    let m := T.edgeFinset.card
    ∃ f : V → ℕ, Function.Injective f ∧ (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  intro m
  classical
  let e := Fintype.equivFin V
  let S := T.comap e.symm
  let i : S ≃g T := SimpleGraph.Iso.comap e.symm T
  have hS := i.isTree_iff.mpr hT
  have hcard : S.edgeFinset.card = m := i.card_edgeFinset_eq
  obtain ⟨f, hf, hb, hd⟩ := hsmall S hS
  refine ⟨f ∘ i.symm, hf.comp i.symm.injective, fun v => (hb _).trans_eq hcard,
    Eq.symm (Finset.eq_of_subset_of_card_le ?_ ?_)⟩
  · intro d hm
    obtain ⟨x, y, hxy, heq⟩ := hd d (by simpa [hcard] using hm)
    refine Finset.mem_image.mpr ⟨s(i x, i y), mem_edgeFinset.mpr (i.map_rel_iff.mpr hxy), ?_⟩
    change ((f (i.symm (i x)) : ℤ) - f (i.symm (i y))).natAbs = d
    simp only [RelIso.symm_apply_apply]
    dsimp [Nat.dist] at heq
    omega
  · simpa [m] using Finset.card_image_le (s := T.edgeFinset) (f := _)

theorem main : H1 → H2 → type_of% @GracefulLabeling.graceful_tree_conjecture := by
  intro h₁ h₂ V _ _ T _ hT
  apply graceful_of_small_bounded _ T hT
  intro W _ _ S _ hS
  exact bounded_of_compression h₁ h₂ S.edgeFinset.card S hS rfl

end OMA.R_GracefulLabeling_graceful_tree_conjecture_R1
