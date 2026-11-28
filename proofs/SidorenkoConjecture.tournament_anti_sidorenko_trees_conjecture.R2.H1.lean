import OMAReductions.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R2
import Mathlib

-- Step SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R2.H1: hypothesis H1 of reduction SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R2
-- Credit: @sebastianbachmaier
-- H1 := ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree →     (∀ a b c : V, a ≠ b → (∀ x, T.Adj a x ↔ x = c) → ¬ (∀ x, T.Adj b x ↔ x = c)) →     (∀ z : V, T.degree z ≤ 2) → ∃ D : Digraph V, D.IsOrientation T ∧       ∀ {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W)         [DecidableRel G.Adj], G.IsTournament → D.homDensity G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card

-- Package A: a finite tree in which every vertex has at most two neighbours is a path.

-- Degree at most two, restated through adjacency: among three neighbours two coincide.
lemma sido_three_nbrs {V : Type} [Fintype V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hdeg : ∀ z : V, T.degree z ≤ 2) (z a b c : V)
    (ha : T.Adj z a) (hb : T.Adj z b) (hc : T.Adj z c) : a = b ∨ a = c ∨ b = c := by
  classical
  by_contra hne
  have h1 : a ≠ b := fun h => hne (Or.inl h)
  have h2 : a ≠ c := fun h => hne (Or.inr (Or.inl h))
  have h3 : b ≠ c := fun h => hne (Or.inr (Or.inr h))
  have hsub : ({a, b, c} : Finset V) ⊆ T.neighborFinset z := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [SimpleGraph.mem_neighborFinset]
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, h1, h2, h3, rfl⟩
  have hle := Finset.card_le_card hsub
  have hz : (T.neighborFinset z).card ≤ 2 := hdeg z
  omega

-- A tree has a vertex with at most one neighbour.
lemma sido_exists_end {V : Type} [Fintype V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (ht : T.IsTree) :
    ∃ v : V, ∀ x y : V, T.Adj v x → T.Adj v y → x = y := by
  have hne : Nonempty V := ht.connected.nonempty
  by_cases h1 : Nontrivial V
  · obtain ⟨v, hv⟩ := ht.exists_vert_degree_one_of_nontrivial
    obtain ⟨w, _, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    exact ⟨v, fun x y hx hy => (hw x hx).trans (hw y hy).symm⟩
  · rw [not_nontrivial_iff_subsingleton] at h1
    obtain ⟨v⟩ := hne
    exact ⟨v, fun x y _ _ => Subsingleton.elim x y⟩

-- Strengthened statement: any end vertex can be sent to the last vertex of the path.
lemma sido_path_aux (n : ℕ) : ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
    Fintype.card V = n + 1 → T.IsTree →
    (∀ z a b c : V, T.Adj z a → T.Adj z b → T.Adj z c → a = b ∨ a = c ∨ b = c) →
    ∀ v : V, (∀ x y : V, T.Adj v x → T.Adj v y → x = y) →
    ∃ e : T ≃g SimpleGraph.pathGraph (n + 1), e v = Fin.last n := by
  classical
  induction n with
  | zero =>
    intro V _ T hcard _ _ v _
    have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    let e0 : V ≃ Fin (0 + 1) := Fintype.equivFinOfCardEq hcard
    refine ⟨⟨e0, ?_⟩, ?_⟩
    swap
    · apply Fin.ext
      have h1 := (e0 v).isLt
      show (e0 v).val = 0
      omega
    intro a b
    constructor
    · intro h
      rw [SimpleGraph.pathGraph_adj] at h
      have h1 := (e0 a).isLt
      have h2 := (e0 b).isLt
      exfalso
      omega
    · intro h
      exact absurd (Subsingleton.elim a b) h.ne
  | succ n ih =>
    intro V _ T hcard ht hdeg v hv
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨u, hvu⟩ := ht.connected.preconnected.exists_adj_of_nontrivial v
    have huv : u ≠ v := hvu.ne.symm
    have dv : T.degree v = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      ⟨u, hvu, fun x hx => hv x u hx hvu⟩
    have hconn : (T.induce ({v}ᶜ : Set V)).Connected :=
      ht.connected.induce_compl_singleton_of_degree_eq_one dv
    have htree : (T.induce ({v}ᶜ : Set V)).IsTree := ⟨hconn, ht.isAcyclic.induce _⟩
    have hcard' : Fintype.card ({v}ᶜ : Set V) = n + 1 := by
      have h1 : Fintype.card ({v}ᶜ : Set V) = Fintype.card V - Fintype.card ({v} : Set V) :=
        Fintype.card_compl_set _
      have h2 : Fintype.card ({v} : Set V) = 1 := by
        first
          | exact Set.card_singleton v
          | exact Fintype.card_unique
          | simp
      omega
    obtain ⟨e', he'⟩ := ih (T.induce ({v}ᶜ : Set V)) hcard' htree
      (fun z a b c hza hzb hzc => by
        rcases hdeg z.val a.val b.val c.val hza hzb hzc with h | h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Subtype.ext h)))
      ⟨u, huv⟩
      (fun x y hx hy => by
        rcases hdeg u v x.val y.val hvu.symm hx hy with h | h | h
        · exact absurd h.symm x.property
        · exact absurd h.symm y.property
        · exact Subtype.ext h)
    let f : V → Fin (n + 1 + 1) := fun x =>
      if h : x = v then Fin.last (n + 1) else (e' ⟨x, h⟩).castSucc
    have hfv : (f v).val = n + 1 := by
      simp [f]
    have hfne : ∀ (x : V) (h : x ≠ v), (f x).val = (e' ⟨x, h⟩).val := by
      intro x h
      first
        | (simp only [f, dif_neg h]; rfl)
        | (simp [f, h]; done)
    have hlt : ∀ (x : V) (h : x ≠ v), (e' ⟨x, h⟩).val < n + 1 := fun x h => (e' ⟨x, h⟩).isLt
    have hfinj : Function.Injective f := by
      intro x y hxy
      have hval : (f x).val = (f y).val := congrArg Fin.val hxy
      by_cases hx : x = v
      · by_cases hy : y = v
        · exact hx.trans hy.symm
        · rw [hx, hfv, hfne y hy] at hval
          have := hlt y hy
          exfalso
          omega
      · by_cases hy : y = v
        · rw [hy, hfv, hfne x hx] at hval
          have := hlt x hx
          exfalso
          omega
        · rw [hfne x hx, hfne y hy] at hval
          have h2 := e'.injective (Fin.ext hval)
          exact congrArg Subtype.val h2
    have hfbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by simp [hcard]⟩
    have hkey : ∀ (b : V) (hb : b ≠ v), T.Adj v b ↔ (e' ⟨b, hb⟩).val = n := by
      intro b hb
      constructor
      · intro h
        have hbu : b = u := hv b u h hvu
        have h2 : (⟨b, hb⟩ : ({v}ᶜ : Set V)) = ⟨u, huv⟩ := Subtype.ext hbu
        have h3 : e' ⟨b, hb⟩ = Fin.last n := (congrArg (fun z => e' z) h2).trans he'
        exact (congrArg Fin.val h3).trans (Fin.val_last n)
      · intro h
        have h2 : e' ⟨b, hb⟩ = e' ⟨u, huv⟩ :=
          (Fin.ext (h.trans (Fin.val_last n).symm)).trans he'.symm
        have h3 : b = u := congrArg Subtype.val (e'.injective h2)
        rw [h3]
        exact hvu
    have hadj : ∀ (a b : V) (ha : a ≠ v) (hb : b ≠ v),
        ((e' ⟨a, ha⟩).val + 1 = (e' ⟨b, hb⟩).val ∨ (e' ⟨b, hb⟩).val + 1 = (e' ⟨a, ha⟩).val) ↔
          T.Adj a b := by
      intro a b ha hb
      have h : (SimpleGraph.pathGraph (n + 1)).Adj (e' ⟨a, ha⟩) (e' ⟨b, hb⟩) ↔ T.Adj a b :=
        e'.map_rel_iff
      rw [SimpleGraph.pathGraph_adj] at h
      exact h
    refine ⟨⟨Equiv.ofBijective f hfbij, ?_⟩, ?_⟩
    · intro a b
      rw [SimpleGraph.pathGraph_adj]
      show ((f a).val + 1 = (f b).val ∨ (f b).val + 1 = (f a).val) ↔ T.Adj a b
      by_cases ha : a = v
      · by_cases hb : b = v
        · have hab : a = b := ha.trans hb.symm
          constructor
          · intro h
            rw [hab] at h
            exfalso
            omega
          · intro h
            exact absurd hab h.ne
        · rw [ha, hfv, hfne b hb, hkey b hb]
          have := hlt b hb
          constructor <;> intro h <;> omega
      · by_cases hb : b = v
        · rw [hb, hfv, hfne a ha, T.adj_comm a v, hkey a ha]
          have := hlt a ha
          constructor <;> intro h <;> omega
        · rw [hfne a ha, hfne b hb]
          exact hadj a b ha hb
    · apply Fin.ext
      show (f v).val = n + 1
      exact hfv

theorem sido_tree_iso_path {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (ht : T.IsTree) (hdeg : ∀ z : V, T.degree z ≤ 2) :
    ∃ n : ℕ, Nonempty (T ≃g SimpleGraph.pathGraph (n + 1)) := by
  have hne : Nonempty V := ht.connected.nonempty
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 1 :=
    ⟨Fintype.card V - 1, by have := Fintype.card_pos (α := V); omega⟩
  obtain ⟨v, hv⟩ := sido_exists_end T ht
  obtain ⟨e, _⟩ := sido_path_aux n T hn ht (sido_three_nbrs T hdeg) v hv
  exact ⟨n, ⟨e⟩⟩

-- Package B1: the two gluing inequalities for digraph homomorphism counts.

theorem sido_hom_ext {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {D : Digraph V} {G : Digraph W} (f g : D →g G) (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  congr

theorem sido_glue_odd {A V W : Type} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (Q : Digraph A) (D : Digraph V) (G : Digraph W)
    [DecidableRel Q.Adj] [DecidableRel D.Adj] [DecidableRel G.Adj] (hG : G.IsTournament)
    (iL iR : A → V) (r : A)
    (hL : ∀ x y, Q.Adj x y → D.Adj (iL x) (iL y)) (hR : ∀ x y, Q.Adj x y → D.Adj (iR x) (iR y))
    (hcov : ∀ v : V, ∃ a, v = iL a ∨ v = iR a) (hmid : D.Adj (iL r) (iR r)) :
    2 * D.homCount G ≤ Q.homCount G ^ 2 := by
  let resL (f : D →g G) : Q →g G :=
    ⟨fun a => f.toFun (iL a), fun {x y} h => f.map_adj' (hL x y h)⟩
  let resR (f : D →g G) : Q →g G :=
    ⟨fun a => f.toFun (iR a), fun {x y} h => f.map_adj' (hR x y h)⟩
  have key : ∀ f g : D →g G, resL f = resL g → resR f = resR g → f = g := by
    intro f g h1 h2
    apply sido_hom_ext
    funext v
    obtain ⟨a, ha | ha⟩ := hcov v
    · subst ha
      exact congrArg (fun k : Q →g G => k.toFun a) h1
    · subst ha
      exact congrArg (fun k : Q →g G => k.toFun a) h2
  -- a hom and its mirror image can never restrict to the same pair
  have clash : ∀ f g : D →g G, resL f = resR g → resR f = resL g → False := by
    intro f g h1 h2
    have e1 : f.toFun (iL r) = g.toFun (iR r) := congrArg (fun k : Q →g G => k.toFun r) h1
    have e2 : f.toFun (iR r) = g.toFun (iL r) := congrArg (fun k : Q →g G => k.toFun r) h2
    have af : G.Adj (f.toFun (iL r)) (f.toFun (iR r)) := f.map_adj' hmid
    have ag : G.Adj (g.toFun (iL r)) (g.toFun (iR r)) := g.map_adj' hmid
    rw [← e1, ← e2] at ag
    by_cases he : f.toFun (iL r) = f.toFun (iR r)
    · rw [he] at af
      exact hG.1 _ af
    · exact ((hG.2 _ _ he).mp af) ag
  let encode : (D →g G) ⊕ (D →g G) → (Q →g G) × (Q →g G) :=
    Sum.elim (fun f => (resL f, resR f)) (fun f => (resR f, resL f))
  have inj : Function.Injective encode := by
    rintro (f | f) (g | g) h
    · have h1 : resL f = resL g := congrArg Prod.fst h
      have h2 : resR f = resR g := congrArg Prod.snd h
      exact congrArg Sum.inl (key f g h1 h2)
    · have h1 : resL f = resR g := congrArg Prod.fst h
      have h2 : resR f = resL g := congrArg Prod.snd h
      exact (clash f g h1 h2).elim
    · have h1 : resR f = resL g := congrArg Prod.fst h
      have h2 : resL f = resR g := congrArg Prod.snd h
      exact (clash f g h2 h1).elim
    · have h1 : resR f = resR g := congrArg Prod.fst h
      have h2 : resL f = resL g := congrArg Prod.snd h
      exact congrArg Sum.inr (key f g h2 h1)
  have hc := Fintype.card_le_of_injective encode inj
  rw [Fintype.card_sum, Fintype.card_prod] at hc
  show 2 * Fintype.card (D →g G) ≤ Fintype.card (Q →g G) ^ 2
  rw [two_mul, sq]
  exact hc

theorem sido_glue_even {A V W : Type} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (Q : Digraph A) (D : Digraph V) (G : Digraph W)
    [DecidableRel Q.Adj] [DecidableRel D.Adj] [DecidableRel G.Adj] (hG : G.IsTournament)
    (iL iR : A → V) (r : A) (c : V)
    (hL : ∀ x y, Q.Adj x y → D.Adj (iL x) (iL y)) (hR : ∀ x y, Q.Adj x y → D.Adj (iR x) (iR y))
    (hcov : ∀ v : V, v = c ∨ ∃ a, v = iL a ∨ v = iR a)
    (hin : D.Adj (iL r) c) (hout : D.Adj c (iR r)) :
    4 * D.homCount G ≤ Fintype.card W * Q.homCount G ^ 2 := by
  classical
  let resL (f : D →g G) : Q →g G :=
    ⟨fun a => f.toFun (iL a), fun {x y} h => f.map_adj' (hL x y h)⟩
  let resR (f : D →g G) : Q →g G :=
    ⟨fun a => f.toFun (iR a), fun {x y} h => f.map_adj' (hR x y h)⟩
  let fiber (w : W) :=
    {g : Q →g G // G.Adj (g.toFun r) w} × {g : Q →g G // G.Adj w (g.toFun r)}
  let encode (f : D →g G) : Σ w : W, fiber w :=
    ⟨f.toFun c, ⟨resL f, f.map_adj' hin⟩, ⟨resR f, f.map_adj' hout⟩⟩
  have inj : Function.Injective encode := by
    intro f g h
    have h0 : f.toFun c = g.toFun c := congrArg Sigma.fst h
    have h1 : resL f = resL g := congrArg (fun z : Σ w : W, fiber w => z.2.1.val) h
    have h2 : resR f = resR g := congrArg (fun z : Σ w : W, fiber w => z.2.2.val) h
    apply sido_hom_ext
    funext v
    rcases hcov v with hv | ⟨a, ha | ha⟩
    · subst hv
      exact h0
    · subst ha
      exact congrArg (fun k : Q →g G => k.toFun a) h1
    · subst ha
      exact congrArg (fun k : Q →g G => k.toFun a) h2
  have bound (w : W) : 4 * Fintype.card (fiber w) ≤ Fintype.card (Q →g G) ^ 2 := by
    let incoming := (Finset.univ : Finset (Q →g G)).filter (fun g => G.Adj (g.toFun r) w)
    let outgoing := (Finset.univ : Finset (Q →g G)).filter (fun g => G.Adj w (g.toFun r))
    have dis : Disjoint incoming outgoing := by
      refine Finset.disjoint_left.mpr ?_
      intro g hi ho
      have hx : G.Adj (g.toFun r) w := (Finset.mem_filter.mp hi).2
      have hy : G.Adj w (g.toFun r) := (Finset.mem_filter.mp ho).2
      by_cases he : g.toFun r = w
      · rw [he] at hx
        exact hG.1 _ hx
      · exact ((hG.2 _ _ he).mp hx) hy
    have sumle : incoming.card + outgoing.card ≤ Fintype.card (Q →g G) := by
      rw [← Finset.card_union_of_disjoint dis]
      exact Finset.card_le_univ _
    have ci : Fintype.card {g : Q →g G // G.Adj (g.toFun r) w} = incoming.card :=
      Fintype.card_of_subtype _ (by simp [incoming])
    have co : Fintype.card {g : Q →g G // G.Adj w (g.toFun r)} = outgoing.card :=
      Fintype.card_of_subtype _ (by simp [outgoing])
    rw [show Fintype.card (fiber w) = _ from Fintype.card_prod _ _, ci, co]
    calc
      4 * (incoming.card * outgoing.card) ≤ (incoming.card + outgoing.card) ^ 2 := by
        zify
        nlinarith [sq_nonneg ((incoming.card : ℤ) - outgoing.card)]
      _ ≤ _ := Nat.pow_le_pow_left sumle _
  calc
    4 * D.homCount G ≤ 4 * Fintype.card (Σ w : W, fiber w) :=
      Nat.mul_le_mul_left _ (Fintype.card_le_of_injective encode inj)
    _ = ∑ w : W, 4 * Fintype.card (fiber w) := by rw [Fintype.card_sigma, Finset.mul_sum]
    _ ≤ ∑ _w : W, Fintype.card (Q →g G) ^ 2 := Finset.sum_le_sum (fun w _ => bound w)
    _ = _ := by simp [Digraph.homCount]

-- Package B2: the oriented path on Fin (m + 1).

-- The vertex of the small path that is mirrored onto position a of the left copy.
theorem sido_fin_sub (j a : ℕ) (h : a ≤ j) : ∃ x : Fin (j + 1), a + x.val = j :=
  ⟨⟨j - a, by omega⟩, by show a + (j - a) = j; omega⟩

-- The vertex of the small path that is shifted onto position a of the right copy.
theorem sido_fin_add (j b a : ℕ) (h1 : b ≤ a) (h2 : a < b + (j + 1)) :
    ∃ x : Fin (j + 1), a = b + x.val :=
  ⟨⟨a - b, by omega⟩, by show a = b + (a - b); omega⟩

-- The two copies of the small path inside the long one: mirrored on the left, shifted on the right.
theorem sido_maps (j e N : ℕ) (hN : N = 2 * j + e + 2) :
    ∃ iL iR : Fin (j + 1) → Fin N,
      (∀ t, (iL t).val + t.val = j) ∧ (∀ t, (iR t).val = j + 1 + e + t.val) :=
  ⟨fun t => ⟨j - t.val, by omega⟩, fun t => ⟨j + 1 + e + t.val, by omega⟩,
    fun t => (by show j - t.val + t.val = j; omega), fun _ => rfl⟩

-- Two copies of an oriented path on j + 1 vertices, the left one mirrored, joined by a
-- forward path with e + 1 arcs from position j to position j + 1 + e.
theorem sido_double (j e N : ℕ) (hN : N = 2 * j + e + 2) (Q : Digraph (Fin (j + 1)))
    (hQ : Q.IsOrientation (SimpleGraph.pathGraph (j + 1))) :
    ∃ D : Digraph (Fin N), D.IsOrientation (SimpleGraph.pathGraph N) ∧
      (∀ u v : Fin N, j ≤ u.val → u.val + 1 = v.val → v.val ≤ j + 1 + e → D.Adj u v) ∧
      (∀ (x y : Fin (j + 1)) (u v : Fin N), Q.Adj x y → u.val + x.val = j → v.val + y.val = j →
        D.Adj u v) ∧
      (∀ (x y : Fin (j + 1)) (u v : Fin N), Q.Adj x y → u.val = j + 1 + e + x.val →
        v.val = j + 1 + e + y.val → D.Adj u v) := by
  obtain ⟨D, hdef⟩ : ∃ D : Digraph (Fin N), ∀ u v : Fin N, D.Adj u v ↔
      ((j ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ j + 1 + e) ∨
        (∃ x y : Fin (j + 1), Q.Adj x y ∧ u.val + x.val = j ∧ v.val + y.val = j) ∨
        (∃ x y : Fin (j + 1), Q.Adj x y ∧ u.val = j + 1 + e + x.val ∧
          v.val = j + 1 + e + y.val)) :=
    ⟨⟨fun u v => (j ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ j + 1 + e) ∨
        (∃ x y : Fin (j + 1), Q.Adj x y ∧ u.val + x.val = j ∧ v.val + y.val = j) ∨
        (∃ x y : Fin (j + 1), Q.Adj x y ∧ u.val = j + 1 + e + x.val ∧
          v.val = j + 1 + e + y.val)⟩, fun _ _ => Iff.rfl⟩
  have hleft : ∀ (u v : Fin N) (x y : Fin (j + 1)), u.val + x.val = j → v.val + y.val = j →
      (D.Adj u v ↔ Q.Adj x y) := by
    intro u v x y hx hy
    constructor
    · intro h
      rcases (hdef u v).mp h with ⟨h1, h2, h3⟩ | ⟨x', y', h', hx', hy'⟩ | ⟨x', y', h', hx', hy'⟩
      · omega
      · have ex : x' = x := Fin.ext (by omega)
        have ey : y' = y := Fin.ext (by omega)
        rw [← ex, ← ey]
        exact h'
      · omega
    · intro h
      exact (hdef u v).mpr (Or.inr (Or.inl ⟨x, y, h, hx, hy⟩))
  have hright : ∀ (u v : Fin N) (x y : Fin (j + 1)), u.val = j + 1 + e + x.val →
      v.val = j + 1 + e + y.val → (D.Adj u v ↔ Q.Adj x y) := by
    intro u v x y hx hy
    constructor
    · intro h
      rcases (hdef u v).mp h with ⟨h1, h2, h3⟩ | ⟨x', y', h', hx', hy'⟩ | ⟨x', y', h', hx', hy'⟩
      · omega
      · omega
      · have ex : x' = x := Fin.ext (by omega)
        have ey : y' = y := Fin.ext (by omega)
        rw [← ex, ← ey]
        exact h'
    · intro h
      exact (hdef u v).mpr (Or.inr (Or.inr ⟨x, y, h, hx, hy⟩))
  have hmid : ∀ u v : Fin N, ¬ (u.val ≤ j ∧ v.val ≤ j) →
      ¬ (j + 1 + e ≤ u.val ∧ j + 1 + e ≤ v.val) →
      (D.Adj u v ↔ (j ≤ u.val ∧ u.val + 1 = v.val ∧ v.val ≤ j + 1 + e)) := by
    intro u v h1 h2
    constructor
    · intro h
      rcases (hdef u v).mp h with h' | ⟨x', y', h', hx', hy'⟩ | ⟨x', y', h', hx', hy'⟩
      · exact h'
      · omega
      · omega
    · intro h
      exact (hdef u v).mpr (Or.inl h)
  refine ⟨D, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro u v h
    rw [SimpleGraph.pathGraph_adj]
    rcases (hdef u v).mp h with ⟨h1, h2, h3⟩ | ⟨x, y, h', hx, hy⟩ | ⟨x, y, h', hx, hy⟩
    · omega
    · have hp := hQ.1 x y h'
      rw [SimpleGraph.pathGraph_adj] at hp
      omega
    · have hp := hQ.1 x y h'
      rw [SimpleGraph.pathGraph_adj] at hp
      omega
  · intro u v huv
    rw [SimpleGraph.pathGraph_adj] at huv
    by_cases hl : u.val ≤ j ∧ v.val ≤ j
    · obtain ⟨x, hx⟩ := sido_fin_sub j u.val hl.1
      obtain ⟨y, hy⟩ := sido_fin_sub j v.val hl.2
      rw [hleft u v x y hx hy, hleft v u y x hy hx]
      refine hQ.2 x y ?_
      rw [SimpleGraph.pathGraph_adj]
      omega
    · by_cases hr : j + 1 + e ≤ u.val ∧ j + 1 + e ≤ v.val
      · obtain ⟨x, hx⟩ := sido_fin_add j (j + 1 + e) u.val hr.1 (by omega)
        obtain ⟨y, hy⟩ := sido_fin_add j (j + 1 + e) v.val hr.2 (by omega)
        rw [hright u v x y hx hy, hright v u y x hy hx]
        refine hQ.2 x y ?_
        rw [SimpleGraph.pathGraph_adj]
        omega
      · have hl' : ¬ (v.val ≤ j ∧ u.val ≤ j) := fun h => hl ⟨h.2, h.1⟩
        have hr' : ¬ (j + 1 + e ≤ v.val ∧ j + 1 + e ≤ u.val) := fun h => hr ⟨h.2, h.1⟩
        rw [hmid u v hl hr, hmid v u hl' hr']
        constructor
        · intro h1 h2
          omega
        · intro h1
          refine ⟨?_, ?_, ?_⟩ <;> omega
  · intro u v h1 h2 h3
    exact (hdef u v).mpr (Or.inl ⟨h1, h2, h3⟩)
  · intro x y u v h hx hy
    exact (hdef u v).mpr (Or.inr (Or.inl ⟨x, y, h, hx, hy⟩))
  · intro x y u v h hx hy
    exact (hdef u v).mpr (Or.inr (Or.inr ⟨x, y, h, hx, hy⟩))

-- Odd number of edges: two copies joined by one arc.
theorem sido_step_odd (j N : ℕ) (hN : N = 2 * j + 2) (Q : Digraph (Fin (j + 1)))
    (hQ : Q.IsOrientation (SimpleGraph.pathGraph (j + 1))) :
    ∃ D : Digraph (Fin N), D.IsOrientation (SimpleGraph.pathGraph N) ∧
      ∀ (instD : DecidableRel D.Adj) (instQ : DecidableRel Q.Adj) {W : Type} [Fintype W]
        [DecidableEq W] (G : Digraph W) [DecidableRel G.Adj], G.IsTournament →
        2 * D.homCount G ≤ Q.homCount G ^ 2 := by
  obtain ⟨D, hD, hm, hl, hr⟩ := sido_double j 0 N (by omega) Q hQ
  obtain ⟨iL, iR, hiL, hiR⟩ := sido_maps j 0 N (by omega)
  obtain ⟨r, hr0⟩ : ∃ r : Fin (j + 1), r.val = 0 := ⟨⟨0, Nat.succ_pos j⟩, rfl⟩
  refine ⟨D, hD, ?_⟩
  intro instD instQ W _ _ G _ hG
  refine sido_glue_odd Q D G hG iL iR r ?_ ?_ ?_ ?_
  · intro x y h
    exact hl x y (iL x) (iL y) h (hiL x) (hiL y)
  · intro x y h
    exact hr x y (iR x) (iR y) h (hiR x) (hiR y)
  · intro v
    by_cases hv : v.val ≤ j
    · obtain ⟨a, ha⟩ := sido_fin_sub j v.val hv
      have := hiL a
      exact ⟨a, Or.inl (Fin.ext (by omega))⟩
    · obtain ⟨a, ha⟩ := sido_fin_add j (j + 1) v.val (by omega) (by omega)
      have := hiR a
      exact ⟨a, Or.inr (Fin.ext (by omega))⟩
  · have h1 := hiL r
    have h2 := hiR r
    exact hm (iL r) (iR r) (by omega) (by omega) (by omega)

-- Even positive number of edges: two copies joined through a new middle vertex.
theorem sido_step_even (j N : ℕ) (hN : N = 2 * j + 3) (Q : Digraph (Fin (j + 1)))
    (hQ : Q.IsOrientation (SimpleGraph.pathGraph (j + 1))) :
    ∃ D : Digraph (Fin N), D.IsOrientation (SimpleGraph.pathGraph N) ∧
      ∀ (instD : DecidableRel D.Adj) (instQ : DecidableRel Q.Adj) {W : Type} [Fintype W]
        [DecidableEq W] (G : Digraph W) [DecidableRel G.Adj], G.IsTournament →
        4 * D.homCount G ≤ Fintype.card W * Q.homCount G ^ 2 := by
  obtain ⟨D, hD, hm, hl, hr⟩ := sido_double j 1 N (by omega) Q hQ
  obtain ⟨iL, iR, hiL, hiR⟩ := sido_maps j 1 N (by omega)
  obtain ⟨r, hr0⟩ : ∃ r : Fin (j + 1), r.val = 0 := ⟨⟨0, Nat.succ_pos j⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin N, c.val = j + 1 := ⟨⟨j + 1, by omega⟩, rfl⟩
  refine ⟨D, hD, ?_⟩
  intro instD instQ W _ _ G _ hG
  refine sido_glue_even Q D G hG iL iR r c ?_ ?_ ?_ ?_ ?_
  · intro x y h
    exact hl x y (iL x) (iL y) h (hiL x) (hiL y)
  · intro x y h
    exact hr x y (iR x) (iR y) h (hiR x) (hiR y)
  · intro v
    by_cases hv : v.val ≤ j
    · obtain ⟨a, ha⟩ := sido_fin_sub j v.val hv
      have := hiL a
      exact Or.inr ⟨a, Or.inl (Fin.ext (by omega))⟩
    · by_cases hv' : v.val = j + 1
      · exact Or.inl (Fin.ext (by omega))
      · obtain ⟨a, ha⟩ := sido_fin_add j (j + 2) v.val (by omega) (by omega)
        have := hiR a
        exact Or.inr ⟨a, Or.inr (Fin.ext (by omega))⟩
  · have h1 := hiL r
    exact hm (iL r) c (by omega) (by omega) (by omega)
  · have h2 := hiR r
    exact hm c (iR r) (by omega) (by omega) (by omega)

-- A single vertex: every hom is determined by the image of that vertex.
theorem sido_path_zero :
    ∃ D : Digraph (Fin (0 + 1)), D.IsOrientation (SimpleGraph.pathGraph (0 + 1)) ∧
      ∀ (inst : DecidableRel D.Adj) {W : Type} [Fintype W] [DecidableEq W] (G : Digraph W)
        [DecidableRel G.Adj], D.homCount G ≤ Fintype.card W := by
  obtain ⟨D, hdef⟩ : ∃ D : Digraph (Fin (0 + 1)), ∀ u v, ¬ D.Adj u v :=
    ⟨⟨fun _ _ => False⟩, fun _ _ h => h⟩
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · intro u v h
    exact (hdef u v h).elim
  · intro u v h
    rw [SimpleGraph.pathGraph_adj] at h
    omega
  · intro inst W _ _ G _
    have hinj : Function.Injective
        (fun f : Digraph.Hom D G => f.toFun ⟨0, Nat.succ_pos 0⟩) := by
      intro f g h
      have eqf : f.toFun = g.toFun := by
        funext x
        have hx : x = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by show x.val = 0; omega)
        rw [hx]
        exact h
      cases f
      cases g
      congr
    exact Fintype.card_le_of_injective
      (fun f : Digraph.Hom D G => f.toFun ⟨0, Nat.succ_pos 0⟩) hinj

theorem sido_path_orientation (m : ℕ) :
    ∃ D : Digraph (Fin (m + 1)), D.IsOrientation (SimpleGraph.pathGraph (m + 1)) ∧
      ∀ (inst : DecidableRel D.Adj) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : Digraph W)
        [DecidableRel G.Adj], G.IsTournament → 2 ^ m * D.homCount G ≤ Fintype.card W ^ (m + 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      obtain ⟨D, hD, hcount⟩ := sido_path_zero
      refine ⟨D, hD, ?_⟩
      intro inst W _ _ _ G _ _
      have hc := hcount inst G
      have e1 : 2 ^ 0 * D.homCount G = D.homCount G := by simp
      have e2 : Fintype.card W ^ (0 + 1) = Fintype.card W := by simp
      rw [e1, e2]
      exact hc
    · obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 ∨ m = 2 * j + 2 := ⟨(m - 1) / 2, by omega⟩
      obtain ⟨Q, hQ, hQb⟩ := ih j (by omega)
      rcases hj with hj | hj
      · obtain ⟨D, hD, hstep⟩ := sido_step_odd j (m + 1) (by omega) Q hQ
        refine ⟨D, hD, ?_⟩
        intro inst W _ _ _ G _ hG
        have instQ : DecidableRel Q.Adj := Classical.decRel _
        have h1 := hstep inst instQ G hG
        have h2 := hQb instQ G hG
        subst hj
        calc 2 ^ (2 * j + 1) * D.homCount G
            = (2 ^ j) ^ 2 * (2 * D.homCount G) := by ring
          _ ≤ (2 ^ j) ^ 2 * Q.homCount G ^ 2 := Nat.mul_le_mul_left _ h1
          _ = (2 ^ j * Q.homCount G) ^ 2 := by ring
          _ ≤ (Fintype.card W ^ (j + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
          _ = Fintype.card W ^ (2 * j + 1 + 1) := by ring
      · obtain ⟨D, hD, hstep⟩ := sido_step_even j (m + 1) (by omega) Q hQ
        refine ⟨D, hD, ?_⟩
        intro inst W _ _ _ G _ hG
        have instQ : DecidableRel Q.Adj := Classical.decRel _
        have h1 := hstep inst instQ G hG
        have h2 := hQb instQ G hG
        subst hj
        calc 2 ^ (2 * j + 2) * D.homCount G
            = (2 ^ j) ^ 2 * (4 * D.homCount G) := by ring
          _ ≤ (2 ^ j) ^ 2 * (Fintype.card W * Q.homCount G ^ 2) := Nat.mul_le_mul_left _ h1
          _ = Fintype.card W * (2 ^ j * Q.homCount G) ^ 2 := by ring
          _ ≤ Fintype.card W * (Fintype.card W ^ (j + 1)) ^ 2 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2)
          _ = Fintype.card W ^ (2 * j + 2 + 1) := by ring

-- Package C: the assembly.

open scoped Classical

-- Homomorphism counts do not grow when the source digraph is pulled back along a bijection.
theorem sido_count_transfer {V U W : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W] (D : Digraph V) (B : Digraph U) (G : Digraph W)
    [DecidableRel D.Adj] [DecidableRel B.Adj] [DecidableRel G.Adj] (e : V ≃ U)
    (h : ∀ i j, B.Adj i j → D.Adj (e.symm i) (e.symm j)) :
    D.homCount G ≤ B.homCount G := by
  let encode (f : D →g G) : B →g G :=
    ⟨fun i => f.toFun (e.symm i), fun {i j} hij => f.map_adj' (h i j hij)⟩
  have inj : Function.Injective encode := by
    intro f g hfg
    have heq : f.toFun = g.toFun := by
      funext x
      have hx : f.toFun (e.symm (e x)) = g.toFun (e.symm (e x)) :=
        congrArg (fun k : B →g G => k.toFun (e x)) hfg
      rwa [Equiv.symm_apply_apply] at hx
    cases f
    cases g
    congr
  exact Fintype.card_le_of_injective encode inj

-- From the counting bound to the density bound.
theorem sido_density_of_count {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Nonempty W] (D : Digraph V) (G : Digraph W) [DecidableRel D.Adj] [DecidableRel G.Adj] (n : ℕ)
    (hV : Fintype.card V = n + 1) (h : 2 ^ n * D.homCount G ≤ Fintype.card W ^ (n + 1)) :
    D.homDensity G ≤ (1 / 2 : ℝ) ^ n := by
  have hpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have h' : (2 : ℝ) ^ n * (D.homCount G : ℝ) ≤ (Fintype.card W : ℝ) ^ (n + 1) := by
    exact_mod_cast h
  unfold Digraph.homDensity
  rw [hV, div_le_iff₀ (pow_pos hpos _)]
  calc
    (D.homCount G : ℝ) = (1 / 2 : ℝ) ^ n * ((2 : ℝ) ^ n * (D.homCount G : ℝ)) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 / 2 : ℝ) ^ n * (Fintype.card W : ℝ) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left h' (by positivity)

theorem OMA.solution : OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R2.H1 := by
  intro V _ _ T _ ht _ hdeg
  obtain ⟨n, ⟨e⟩⟩ := sido_tree_iso_path T ht hdeg
  obtain ⟨B, hB, hcount⟩ := sido_path_orientation n
  have hV : Fintype.card V = n + 1 := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]
  have hedges : T.edgeFinset.card = n := by
    have hp := ht.card_edgeFinset
    omega
  obtain ⟨D, hD⟩ : ∃ D : Digraph V, ∀ x y, D.Adj x y ↔ B.Adj (e x) (e y) :=
    ⟨⟨fun x y => B.Adj (e x) (e y)⟩, fun _ _ => Iff.rfl⟩
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    exact e.map_rel_iff.mp (hB.1 _ _ ((hD x y).mp h))
  · intro x y h
    rw [hD x y, hD y x]
    exact hB.2 _ _ (e.map_rel_iff.mpr h)
  · intro W _ _ _ G _ hG
    rw [hedges]
    have hc := hcount (fun a b => Classical.propDecidable (B.Adj a b)) G hG
    have htr : D.homCount G ≤ B.homCount G := by
      apply sido_count_transfer D B G e.toEquiv
      intro i j hij
      have hi : e (e.toEquiv.symm i) = i := e.toEquiv.apply_symm_apply i
      have hj : e (e.toEquiv.symm j) = j := e.toEquiv.apply_symm_apply j
      rw [hD, hi, hj]
      exact hij
    exact sido_density_of_count D G n hV (le_trans (Nat.mul_le_mul_left _ htr) hc)
