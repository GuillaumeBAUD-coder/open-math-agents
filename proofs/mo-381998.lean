import OMAStatements.S_mo_381998

-- Problem: Increasing the Hadwiger number by making any pair of non-adjacent points adjacent (MathOverflow 381998)
-- Credit: @koolkao
-- The complement of the 9-cycle is connected, non-complete and vertex-critical (chromatic number 5); its Hadwiger
-- number is 6, and adding any missing edge raises it to 7 (a K_7 model for each added edge; the upper bound 6 is the
-- counting bound: singleton branch sets form a clique, so 2t <= 9 + 4).

open SimpleGraph Finset OMA.S_mo_381998


namespace MO381998

variable {V : Type*}

/-! ## Definitions -/

/-- Vertex-critical: deleting any vertex lowers the chromatic number. -/
def VertexCritical (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.induce ({v}ᶜ : Set V)).chromaticNumber < G.chromaticNumber

/-! ## Clique-minor models with Finset branch sets -/

/-- A `K_t`-model with Finset branch sets. -/
structure KModel (G : SimpleGraph V) (t : ℕ) where
  B : Fin t → Finset V
  nonempty : ∀ i, (B i).Nonempty
  disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j)
  connected : ∀ i, (G.induce (B i : Set V)).Connected
  adjacent : ∀ i j, i ≠ j → ∃ a ∈ B i, ∃ b ∈ B j, G.Adj a b

/-- `G` has a `K_t`-model with Finset branch sets. -/
def HasCliqueMinor (G : SimpleGraph V) (t : ℕ) : Prop := Nonempty (KModel G t)

lemma hasCompleteMinor_iff [Fintype V] {G : SimpleGraph V} {t : ℕ} :
    HasCompleteMinor G t ↔ HasCliqueMinor G t := by
  classical
  constructor
  · rintro ⟨B, hc, hd, ha⟩
    have hco : ∀ i, ((univ.filter (· ∈ B i) : Finset V) : Set V) = B i := fun i => by ext; simp
    refine ⟨⟨fun i => univ.filter (· ∈ B i), fun i => ?_, fun i j hij => ?_, fun i => ?_,
      fun i j hij => ?_⟩⟩
    · obtain ⟨⟨x, hx⟩⟩ := (hc i).nonempty
      exact ⟨x, by simpa using hx⟩
    · rw [← Finset.disjoint_coe, hco i, hco j]
      exact hd hij
    · rw [hco i]
      exact hc i
    · obtain ⟨x, hx, y, hy, h⟩ := ha i j hij
      exact ⟨x, by simpa using hx, y, by simpa using hy, h⟩
  · rintro ⟨M⟩
    refine ⟨fun i => (M.B i : Set V), M.connected, fun i j hij => Finset.disjoint_coe.2 (M.disjoint i j hij),
      fun i j hij => ?_⟩
    obtain ⟨a, ha, b, hb, h⟩ := M.adjacent i j hij
    exact ⟨a, Finset.mem_coe.2 ha, b, Finset.mem_coe.2 hb, h⟩

lemma hasCompleteMinor_zero (G : SimpleGraph V) : HasCompleteMinor G 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- Restricting a model to its first `t` blocks. -/
def KModel.restrict {G : SimpleGraph V} {s t : ℕ} (h : t ≤ s) (M : KModel G s) : KModel G t where
  B i := M.B (Fin.castLE h i)
  nonempty _ := M.nonempty _
  disjoint _ _ hij := M.disjoint _ _ (fun e => hij (Fin.castLE_injective h e))
  connected _ := M.connected _
  adjacent _ _ hij := M.adjacent _ _ (fun e => hij (Fin.castLE_injective h e))

/-- A block whose vertices are pairwise adjacent induces a connected subgraph. -/
lemma connected_of_clique {G : SimpleGraph V} (B : Finset V) (hne : B.Nonempty)
    (h : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) : (G.induce (B : Set V)).Connected := by
  have : Nonempty (B : Set V) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine ⟨fun x y => ?_⟩
  by_cases hxy : x = y
  · rw [hxy]
  · exact Adj.reachable (h x.1 x.2 y.1 y.2 (fun e => hxy (Subtype.ext e)))

lemma KModel.le_card [Fintype V] {G : SimpleGraph V} {t : ℕ} (M : KModel G t) :
    t ≤ Fintype.card V := by
  classical
  have hsum : #(univ.biUnion M.B) = ∑ i, #(M.B i) :=
    card_biUnion (fun i _ j _ hij => M.disjoint i j hij)
  have h1 : ∑ _i : Fin t, 1 ≤ ∑ i, #(M.B i) :=
    sum_le_sum fun i _ => (M.nonempty i).card_pos
  have h2 : #(univ.biUnion M.B) ≤ Fintype.card V := card_le_univ _
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  omega

/-- Counting bound (Ivančo's upper bound, Corollary 1 of his 1997 paper): the singleton blocks
form a clique, and every other block has at least two vertices. -/
lemma KModel.two_mul_le [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t c : ℕ}
    (hc : ∀ s : Finset V, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y) → #s ≤ c)
    (M : KModel G t) : 2 * t ≤ Fintype.card V + c := by
  set T := univ.filter (fun i => #(M.B i) = 1) with hT
  have hU : #(T.biUnion M.B) = #T := by
    rw [card_biUnion (fun i _ j _ hij => M.disjoint i j hij),
      sum_congr rfl (fun i hi => (mem_filter.1 hi).2), sum_const, smul_eq_mul, mul_one]
  have hUc : #(T.biUnion M.B) ≤ c := by
    apply hc
    intro x hx y hy hxy
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hx
    obtain ⟨j, hj, hyj⟩ := mem_biUnion.1 hy
    obtain ⟨a, ha⟩ := card_eq_one.1 (mem_filter.1 hi).2
    obtain ⟨b, hb⟩ := card_eq_one.1 (mem_filter.1 hj).2
    rw [ha, mem_singleton] at hxi
    rw [hb, mem_singleton] at hyj
    have hij : i ≠ j := by
      rintro rfl
      rw [ha] at hb
      exact hxy (by rw [hxi, hyj]; exact singleton_injective hb)
    obtain ⟨p, hp, q, hq, hpq⟩ := M.adjacent i j hij
    rw [ha, mem_singleton] at hp
    rw [hb, mem_singleton] at hq
    rw [hxi, hyj, ← hp, ← hq]
    exact hpq
  have hsum : #(univ.biUnion M.B) = ∑ i, #(M.B i) :=
    card_biUnion (fun i _ j _ hij => M.disjoint i j hij)
  have h2 : #(univ.biUnion M.B) ≤ Fintype.card V := card_le_univ _
  have hpt : ∀ i, 2 ≤ #(M.B i) + (if #(M.B i) = 1 then 1 else 0) := by
    intro i
    have := (M.nonempty i).card_pos
    split_ifs with h <;> omega
  have h3 : ∑ _i : Fin t, 2 ≤ ∑ i, (#(M.B i) + (if #(M.B i) = 1 then 1 else 0)) :=
    sum_le_sum fun i _ => hpt i
  rw [sum_add_distrib, ← card_filter] at h3
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h3
  rw [← hT] at h3
  omega

/-- Build a model from a vertex labelling whose label classes are cliques. -/
def KModel.ofLabel [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ} (lab : V → Fin t)
    (hsurj : ∀ i, ∃ v, lab v = i) (hcl : ∀ x y, lab x = lab y → x ≠ y → G.Adj x y)
    (hadj : ∀ i j, i ≠ j → ∃ x y, lab x = i ∧ lab y = j ∧ G.Adj x y) : KModel G t where
  B i := univ.filter (fun v => lab v = i)
  nonempty i := by
    obtain ⟨v, hv⟩ := hsurj i
    exact ⟨v, mem_filter.2 ⟨mem_univ _, hv⟩⟩
  disjoint i j hij := by
    rw [Finset.disjoint_left]
    intro v hvi hvj
    exact hij ((mem_filter.1 hvi).2.symm.trans (mem_filter.1 hvj).2)
  connected i := by
    obtain ⟨v, hv⟩ := hsurj i
    refine connected_of_clique _ ⟨v, mem_filter.2 ⟨mem_univ _, hv⟩⟩ ?_
    intro x hx y hy hxy
    exact hcl x y ((mem_filter.1 hx).2.trans (mem_filter.1 hy).2.symm) hxy
  adjacent i j hij := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hadj i j hij
    exact ⟨x, mem_filter.2 ⟨mem_univ _, hx⟩, y, mem_filter.2 ⟨mem_univ _, hy⟩, hxy⟩

/-! ## The Hadwiger number of a finite graph -/

lemma bddAbove_minor [Fintype V] (G : SimpleGraph V) : BddAbove {t | HasCompleteMinor G t} :=
  ⟨Fintype.card V, fun _ ht => by
    obtain ⟨M⟩ := hasCompleteMinor_iff.1 ht
    exact M.le_card⟩

/-- For a finite graph, `hadwigerNumber G` is the largest `t` with a `K_t`-minor. -/
theorem isGreatest_hadwigerNumber [Fintype V] (G : SimpleGraph V) :
    IsGreatest {t | HasCompleteMinor G t} (hadwigerNumber G) :=
  ⟨Nat.sSup_mem ⟨0, hasCompleteMinor_zero G⟩ (bddAbove_minor G),
    fun _ ht => le_csSup (bddAbove_minor G) ht⟩

lemma hadwigerNumber_eq [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (h1 : HasCliqueMinor G m) (h2 : ¬ HasCliqueMinor G (m + 1)) : hadwigerNumber G = m := by
  have hle : m ≤ hadwigerNumber G := (isGreatest_hadwigerNumber G).2 (hasCompleteMinor_iff.2 h1)
  obtain ⟨M⟩ := hasCompleteMinor_iff.1 (isGreatest_hadwigerNumber G).1
  by_contra hne
  exact h2 ⟨M.restrict (by omega)⟩

lemma le_hadwigerNumber [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (h1 : HasCliqueMinor G m) : m ≤ hadwigerNumber G :=
  (isGreatest_hadwigerNumber G).2 (hasCompleteMinor_iff.2 h1)

/-- Deleting the branch set that contains `a` turns a `K_{t+1}`-model of `G ⊔ edge a b` into a
`K_t`-model of `G`. -/
lemma KModel.dropEdge {G : SimpleGraph V} {a b : V} {t : ℕ} (M : KModel (G ⊔ edge a b) (t + 1)) :
    HasCliqueMinor G t := by
  classical
  obtain ⟨i₀, hout⟩ : ∃ i₀ : Fin (t + 1), ∀ j : Fin t, a ∉ M.B (i₀.succAbove j) := by
    by_cases h : ∃ i, a ∈ M.B i
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, fun j hj => Finset.disjoint_left.1 (M.disjoint _ _ (Fin.succAbove_ne i j)) hj hi⟩
    · exact ⟨Fin.last t, fun j hj => h ⟨_, hj⟩⟩
  have hadj : ∀ x y, x ≠ a → y ≠ a → (G ⊔ edge a b).Adj x y → G.Adj x y := by
    intro x y hx hy h
    rcases (sup_adj _ _ _ _).1 h with h | h
    · exact h
    · rw [edge_adj] at h
      rcases h with ⟨⟨h1, -⟩ | ⟨-, h2⟩, -⟩
      · exact absurd h1 hx
      · exact absurd h2 hy
  have hind : ∀ s : Finset V, a ∉ s → (G ⊔ edge a b).induce (s : Set V) = G.induce (s : Set V) := by
    intro s hs
    refine le_antisymm (fun x y h => ?_) (fun x y h => ?_)
    · exact hadj x.1 y.1 (fun e => hs (Finset.mem_coe.1 (e ▸ x.2)))
        (fun e => hs (Finset.mem_coe.1 (e ▸ y.2))) h
    · exact (le_sup_left : G ≤ G ⊔ edge a b) h
  refine ⟨⟨fun j => M.B (i₀.succAbove j), fun j => M.nonempty _,
    fun i j hij => M.disjoint _ _ (Fin.succAbove_right_injective.ne hij), fun j => ?_,
    fun i j hij => ?_⟩⟩
  · rw [← hind _ (hout j)]
    exact M.connected _
  · obtain ⟨x, hx, y, hy, h⟩ := M.adjacent _ _ (Fin.succAbove_right_injective.ne hij)
    exact ⟨x, hx, y, hy, hadj x y (fun e => hout i (e ▸ hx)) (fun e => hout j (e ▸ hy)) h⟩

/-- Adding one edge raises the Hadwiger number by at most one. -/
theorem hadwigerNumber_sup_edge_le [Fintype V] (G : SimpleGraph V) (a b : V) :
    hadwigerNumber (G ⊔ edge a b) ≤ hadwigerNumber G + 1 := by
  have hmem : HasCompleteMinor (G ⊔ edge a b) (hadwigerNumber (G ⊔ edge a b)) :=
    (isGreatest_hadwigerNumber (G ⊔ edge a b)).1
  rcases Nat.eq_zero_or_pos (hadwigerNumber (G ⊔ edge a b)) with h | h
  · omega
  · obtain ⟨t, ht⟩ : ∃ t, hadwigerNumber (G ⊔ edge a b) = t + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    rw [ht] at hmem
    obtain ⟨M⟩ := hasCompleteMinor_iff.1 hmem
    have := le_hadwigerNumber M.dropEdge
    omega

/-! ## The complement of `C_9` -/

/-- The complement of the 9-cycle. -/
abbrev G9 : SimpleGraph (Fin 9) := (cycleGraph 9)ᶜ

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- No five pairwise adjacent vertices (searched in increasing order, with pruning). -/
lemma G9_no_clique5 : ∀ a b : Fin 9, a < b → G9.Adj a b → ∀ c : Fin 9, b < c → G9.Adj a c → G9.Adj b c →
    ∀ d : Fin 9, c < d → G9.Adj a d → G9.Adj b d → G9.Adj c d →
    ∀ e : Fin 9, d < e → G9.Adj a e → G9.Adj b e → G9.Adj c e → ¬ G9.Adj d e := by
  decide

/-- No three pairwise non-adjacent vertices. -/
lemma G9_no_indep3 : ∀ a b : Fin 9, a < b → ¬ G9.Adj a b → ∀ c : Fin 9, b < c → ¬ G9.Adj a c →
    G9.Adj b c := by
  decide

lemma G9_clique_le : ∀ s : Finset (Fin 9), (∀ x ∈ s, ∀ y ∈ s, x ≠ y → G9.Adj x y) → #s ≤ 4 := by
  intro s hs
  by_contra h
  obtain ⟨u, hus, hu⟩ := exists_subset_card_eq (show 5 ≤ #s by omega)
  set f := u.orderEmbOfFin hu
  have mem : ∀ i, f i ∈ s := fun i => hus (u.orderEmbOfFin_mem hu i)
  have adj : ∀ i j : Fin 5, i < j → G9.Adj (f i) (f j) := fun i j hij =>
    hs _ (mem i) _ (mem j) (f.injective.ne hij.ne)
  have lt : ∀ i j : Fin 5, i < j → f i < f j := fun i j hij => f.strictMono hij
  exact G9_no_clique5 (f 0) (f 1) (lt 0 1 (by decide)) (adj 0 1 (by decide))
    (f 2) (lt 1 2 (by decide)) (adj 0 2 (by decide)) (adj 1 2 (by decide))
    (f 3) (lt 2 3 (by decide)) (adj 0 3 (by decide)) (adj 1 3 (by decide)) (adj 2 3 (by decide))
    (f 4) (lt 3 4 (by decide)) (adj 0 4 (by decide)) (adj 1 4 (by decide)) (adj 2 4 (by decide))
    (adj 3 4 (by decide))

lemma G9_indep_le : ∀ s : Finset (Fin 9), (∀ x ∈ s, ∀ y ∈ s, ¬ G9.Adj x y) → #s ≤ 2 := by
  intro s hs
  by_contra h
  obtain ⟨u, hus, hu⟩ := exists_subset_card_eq (show 3 ≤ #s by omega)
  set f := u.orderEmbOfFin hu
  have mem : ∀ i, f i ∈ s := fun i => hus (u.orderEmbOfFin_mem hu i)
  have lt : ∀ i j : Fin 3, i < j → f i < f j := fun i j hij => f.strictMono hij
  exact hs _ (mem 1) _ (mem 2) (G9_no_indep3 (f 0) (f 1) (lt 0 1 (by decide))
    (hs _ (mem 0) _ (mem 1)) (f 2) (lt 1 2 (by decide)) (hs _ (mem 0) _ (mem 2)))

theorem G9_no_K7 : ¬ HasCliqueMinor G9 7 := by
  rintro ⟨M⟩
  have := M.two_mul_le G9_clique_le
  simp at this

/-- Labels for the blocks `{0},{2},{4,8},{6},{1,5},{3,7}`. -/
def lab6 : Fin 9 → Fin 6 := ![0, 4, 1, 5, 2, 4, 3, 5, 2]

theorem G9_K6 : HasCliqueMinor G9 6 :=
  ⟨KModel.ofLabel lab6 (by decide) (by decide) (by decide)⟩

/-- `η(complement of C_9) = 6`. -/
theorem hadwiger_G9 : hadwigerNumber G9 = 6 := hadwigerNumber_eq G9_K6 G9_no_K7

/-- Labels for `{0},{2},{4},{6},{8},{1,5},{3,7}`, the `K_7` model after adding the edge `{8,0}`. -/
def base7 : Fin 9 → Fin 7 := ![0, 5, 1, 6, 2, 5, 3, 6, 4]

/-- The base model rotated by `r`: a `K_7` model after adding the edge `{r-1, r}`. -/
def lab7 (r : Fin 9) (v : Fin 9) : Fin 7 := base7 (v - r)

/-- Explicit adjacency of `G9 ⊔ edge (r-1) r` (Mathlib's `edge` decidability goes through `rw`). -/
def A7 (r x y : Fin 9) : Prop := G9.Adj x y ∨ ((x = r - 1 ∧ y = r ∨ x = r ∧ y = r - 1) ∧ x ≠ y)

instance (r : Fin 9) : DecidableRel (A7 r) := fun x y =>
  inferInstanceAs (Decidable (G9.Adj x y ∨ ((x = r - 1 ∧ y = r ∨ x = r ∧ y = r - 1) ∧ x ≠ y)))

lemma adj7 (r x y : Fin 9) : (G9 ⊔ edge (r - 1) r).Adj x y ↔ A7 r x y := by
  rw [sup_adj, edge_adj]; rfl

lemma lab7_surj : ∀ r : Fin 9, ∀ i : Fin 7, ∃ v, lab7 r v = i := by decide
lemma lab7_clique' : ∀ r x y : Fin 9, lab7 r x = lab7 r y → x ≠ y → A7 r x y := by
  decide
lemma lab7_adj' : ∀ r : Fin 9, ∀ i j : Fin 7, i ≠ j → ∃ x y, lab7 r x = i ∧ lab7 r y = j ∧ A7 r x y := by
  decide

theorem K7_after_edge (r : Fin 9) : HasCliqueMinor (G9 ⊔ edge (r - 1) r) 7 :=
  ⟨KModel.ofLabel (lab7 r) (lab7_surj r)
    (fun x y h hne => (adj7 r x y).2 (lab7_clique' r x y h hne))
    (fun i j hij => by
      obtain ⟨x, y, hx, hy, h⟩ := lab7_adj' r i j hij
      exact ⟨x, y, hx, hy, (adj7 r x y).2 h⟩)⟩

lemma nonedge_cases : ∀ a b : Fin 9, a ≠ b → ¬ G9.Adj a b → a = b - 1 ∨ b = a - 1 := by decide

/-- Adding any missing edge raises the Hadwiger number. -/
theorem hadwiger_increases (a b : Fin 9) (hab : a ≠ b) (hn : ¬ G9.Adj a b) :
    hadwigerNumber G9 < hadwigerNumber (G9 ⊔ edge a b) := by
  rw [hadwiger_G9]
  rcases nonedge_cases a b hab hn with h | h
  · have := le_hadwigerNumber (K7_after_edge b); rw [← h] at this; omega
  · have := le_hadwigerNumber (K7_after_edge a); rw [← h, edge_comm] at this; omega

/-- After adding any missing edge, the Hadwiger number is exactly 7. -/
theorem hadwiger_sup_edge (a b : Fin 9) (hab : a ≠ b) (hn : ¬ G9.Adj a b) :
    hadwigerNumber (G9 ⊔ edge a b) = 7 := by
  have h1 := hadwiger_increases a b hab hn
  have h2 := hadwigerNumber_sup_edge_le G9 a b
  rw [hadwiger_G9] at h1 h2
  omega

/-! ## Colouring facts -/

lemma G9_not_colorable4 : ¬ G9.Colorable 4 := by
  rintro ⟨C⟩
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (n := 2) C (by simp)
  have hind : ∀ x ∈ univ.filter (fun x => C x = y), ∀ z ∈ univ.filter (fun x => C x = y),
      ¬ G9.Adj x z := by
    intro x hx z hz hxz
    exact C.valid hxz ((mem_filter.1 hx).2.trans (mem_filter.1 hz).2.symm)
  have := G9_indep_le _ hind
  omega

lemma G9_colorable5 : G9.Colorable 5 := by
  have key : ∀ u v : Fin 9, G9.Adj u v → (⟨u.val / 2, by omega⟩ : Fin 5) ≠ ⟨v.val / 2, by omega⟩ := by
    decide
  exact ⟨Coloring.mk (fun u => ⟨u.val / 2, by omega⟩) (fun h => key _ _ h)⟩

/-- `χ(complement of C_9) = 5`. -/
theorem chromatic_G9 : G9.chromaticNumber = 5 :=
  chromaticNumber_eq_iff_colorable_not_colorable.2 ⟨G9_colorable5, G9_not_colorable4⟩

lemma G9_delete_colorable4 (v : Fin 9) : (G9.induce ({v}ᶜ : Set (Fin 9))).Colorable 4 := by
  have hlt : ∀ v u : Fin 9, u ≠ v → (u - v - 1).val / 2 < 4 := by decide
  have key : ∀ v u w : Fin 9, u ≠ v → w ≠ v → G9.Adj u w →
      (u - v - 1).val / 2 ≠ (w - v - 1).val / 2 := by decide
  refine ⟨Coloring.mk (fun u => ⟨(u.1 - v - 1).val / 2, hlt v u.1 u.2⟩) ?_⟩
  intro u w huw heq
  exact key v u.1 w.1 u.2 w.2 huw (congrArg Fin.val heq)

theorem G9_vertexCritical : VertexCritical G9 := by
  intro v
  rw [chromatic_G9]
  calc (G9.induce ({v}ᶜ : Set (Fin 9))).chromaticNumber ≤ 4 :=
        (G9_delete_colorable4 v).chromaticNumber_le
    _ < 5 := by norm_num

theorem G9_connected : G9.Connected := by
  have h : ∀ u : Fin 9, u = 0 ∨ G9.Adj 0 u ∨ (G9.Adj 0 4 ∧ G9.Adj 4 u) := by decide
  have r0 : ∀ u : Fin 9, G9.Reachable 0 u := by
    intro u
    rcases h u with h | h | ⟨h1, h2⟩
    · rw [h]
    · exact h.reachable
    · exact h1.reachable.trans h2.reachable
  exact ⟨fun u v => (r0 u).symm.trans (r0 v)⟩

theorem G9_ne_top : G9 ≠ ⊤ := by
  intro h
  have : (⊤ : SimpleGraph (Fin 9)).Adj 0 1 := by simp
  rw [← h] at this
  revert this
  decide

/-! ## The answer -/

/-- **Answer to MO 381998** (smallest case): the complement of `C_9`. -/
theorem mo381998 :
    G9.Connected ∧ G9 ≠ ⊤ ∧ VertexCritical G9 ∧
      ∀ a b : Fin 9, a ≠ b → ¬ G9.Adj a b → hadwigerNumber G9 < hadwigerNumber (G9 ⊔ edge a b) :=
  ⟨G9_connected, G9_ne_top, G9_vertexCritical, hadwiger_increases⟩

end MO381998

theorem OMA.solution : type_of% @OMA.S_mo_381998.main :=
  ⟨9, MO381998.G9, MO381998.mo381998⟩
