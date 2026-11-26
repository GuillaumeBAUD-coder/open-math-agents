import FormalConjectures.Wikipedia.SidorenkoConjecture

/-!
# Tournament Anti-Sidorenko Property for Trees with One Even-Degree Vertex

We prove that every finite tree `T` having a unique vertex `r` of even degree admits an
orientation `D` such that for every finite nonempty tournament `G`,
`Digraph.homDensity D G ≤ (1 / 2) ^ T.edgeFinset.card`.

By strong induction on `|V|`, we construct an orientation `D` of any rooted tree `(T, r)` whose
root `r` has even degree and whose non-root vertices all have odd degree, satisfying the stronger
pointwise integer bound
`2 ^ (|V| - 1) * |{f : D →g G | f r = x}| ≤ |W| ^ (|V| - 1)`
for every finite tournament `G` on `W` and every `x : W`.
Deleting `r` decomposes `T` into `2k = deg_T(r)` rooted subtrees `(T_c, c)` (`c ∈ N_T(r)`), each
inheriting the exact parity hypothesis. Orienting `k` incident edges outward from `r` and `k` inward
to `r` yields the pointwise bound via AM–GM on the disjoint out- and in-neighborhoods of `x` in
the tournament `G`: `4 * d^+(x) * d^-(x) ≤ (d^+(x) + d^-(x))^2 ≤ |W|^2`.
Summing over `x : W` gives `2 ^ e(T) * homCount D G ≤ |W| ^ |V|`.
-/

-- Problem: TAS Trees Conjecture: Trees with a single even-degree vertex.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SidorenkoConjecture.lean:189 (declaration SidorenkoConjecture.tournament_anti_sidorenko_single_even_degree_tree)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace TASTreesSingleEvenProof

open SimpleGraph Finset
open scoped Classical

/- ### Section 1: Homomorphism counting helpers -/

private noncomputable def allHoms {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (G : Digraph W) : Finset (V → W) :=
  Finset.univ.filter (fun f : V → W => ∀ u v, D.Adj u v → G.Adj (f u) (f v))

private noncomputable def homsAt {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (G : Digraph W) (r : V) (x : W) : Finset (V → W) :=
  Finset.univ.filter (fun f : V → W => (∀ u v, D.Adj u v → G.Adj (f u) (f v)) ∧ f r = x)

private noncomputable def localHoms {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (G : Digraph W) (c : V) (x : W) (isOut : Bool) : Finset (V → W) :=
  Finset.univ.filter (fun f : V → W =>
    (∀ a b, D.Adj a b → G.Adj (f a) (f b)) ∧
    (if isOut then G.Adj x (f c) else G.Adj (f c) x))

private lemma mem_allHoms {V W : Type*} [Fintype V] [Fintype W]
    {D : Digraph V} {G : Digraph W} {f : V → W} :
    f ∈ allHoms D G ↔ ∀ u v, D.Adj u v → G.Adj (f u) (f v) := by
  simp [allHoms]

private lemma mem_homsAt {V W : Type*} [Fintype V] [Fintype W]
    {D : Digraph V} {G : Digraph W} {r : V} {x : W} {f : V → W} :
    f ∈ homsAt D G r x ↔ (∀ u v, D.Adj u v → G.Adj (f u) (f v)) ∧ f r = x := by
  simp [homsAt]

private lemma mem_localHoms {V W : Type*} [Fintype V] [Fintype W]
    {D : Digraph V} {G : Digraph W} {c : V} {x : W} {isOut : Bool} {f : V → W} :
    f ∈ localHoms D G c x isOut ↔
      (∀ a b, D.Adj a b → G.Adj (f a) (f b)) ∧
      (if isOut then G.Adj x (f c) else G.Adj (f c) x) := by
  simp [localHoms]

private lemma homCount_eq_card_allHoms {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (D : Digraph V) (G : Digraph W) [DecidableRel D.Adj] [DecidableRel G.Adj] :
    Digraph.homCount D G = (allHoms D G).card := by
  unfold Digraph.homCount
  let e : (D →g G) ≃ ↥(allHoms D G) :=
    { toFun := fun φ => ⟨φ.toFun, mem_allHoms.mpr (fun u v huv => φ.map_adj' huv)⟩
      invFun := fun f => ⟨f.1, fun {u v} huv => (mem_allHoms.mp f.2) u v huv⟩
      left_inv := fun φ => by cases φ; rfl
      right_inv := fun f => by cases f; rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]

private lemma card_allHoms_eq_sum_homsAt {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (G : Digraph W) (r : V) :
    (allHoms D G).card = ∑ x : W, (homsAt D G r x).card := by
  have hunion : allHoms D G = Finset.univ.biUnion (fun x : W => homsAt D G r x) := by
    ext f
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_allHoms, mem_homsAt]
    exact ⟨fun hf => ⟨f r, hf, rfl⟩, fun ⟨_, hf, _⟩ => hf⟩
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset W) (fun x => homsAt D G r x) := by
    intro x _ y _ hxy
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f hfx hfy
    exact hxy ((mem_homsAt.mp hfx).2.symm.trans (mem_homsAt.mp hfy).2)
  rw [hunion, Finset.card_biUnion hdisj]

private lemma card_localHoms_true {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (G : Digraph W) (c : V) (x : W) :
    (localHoms D G c x true).card =
      ∑ y ∈ Finset.univ.filter (fun y : W => G.Adj x y), (homsAt D G c y).card := by
  let P : Finset W := Finset.univ.filter (fun y : W => G.Adj x y)
  have hunion : localHoms D G c x true = P.biUnion (fun y => homsAt D G c y) := by
    ext f
    simp only [P, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_localHoms, mem_homsAt, ↓reduceIte]
    exact ⟨fun ⟨h1, h2⟩ => ⟨f c, h2, h1, rfl⟩, fun ⟨_, hy, h1, heq⟩ => ⟨h1, heq ▸ hy⟩⟩
  have hdisj : Set.PairwiseDisjoint (P : Set W) (fun y => homsAt D G c y) := by
    intro y₁ _ y₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f h1 h2
    exact hne ((mem_homsAt.mp h1).2.symm.trans (mem_homsAt.mp h2).2)
  rw [hunion, Finset.card_biUnion hdisj]

private lemma card_localHoms_false {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (G : Digraph W) (c : V) (x : W) :
    (localHoms D G c x false).card =
      ∑ y ∈ Finset.univ.filter (fun y : W => G.Adj y x), (homsAt D G c y).card := by
  let M : Finset W := Finset.univ.filter (fun y : W => G.Adj y x)
  have hunion : localHoms D G c x false = M.biUnion (fun y => homsAt D G c y) := by
    ext f
    simp only [M, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_localHoms, mem_homsAt, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun ⟨h1, h2⟩ => ⟨f c, h2, h1, rfl⟩, fun ⟨_, hy, h1, heq⟩ => ⟨h1, heq ▸ hy⟩⟩
  have hdisj : Set.PairwiseDisjoint (M : Set W) (fun y => homsAt D G c y) := by
    intro y₁ _ y₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f h1 h2
    exact hne ((mem_homsAt.mp h1).2.symm.trans (mem_homsAt.mp h2).2)
  rw [hunion, Finset.card_biUnion hdisj]

private lemma tournament_four_mul_out_in_le {W : Type*} [Fintype W]
    (G : Digraph W) (hG : G.IsTournament) (x : W) :
    4 * ((Finset.univ.filter (fun y : W => G.Adj x y)).card *
      (Finset.univ.filter (fun y : W => G.Adj y x)).card) ≤ (Fintype.card W) ^ 2 := by
  let P : Finset W := Finset.univ.filter (fun y : W => G.Adj x y)
  let M : Finset W := Finset.univ.filter (fun y : W => G.Adj y x)
  have hdisj : Disjoint P M := by
    rw [Finset.disjoint_left]
    intro y hyP hyM
    simp only [P, M, Finset.mem_filter, Finset.mem_univ, true_and] at hyP hyM
    by_cases hxy : x = y
    · subst hxy
      exact hG.1 x hyP
    · exact ((hG.2 x y hxy).mp hyP) hyM
  have hsum : P.card + M.card ≤ Fintype.card W := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ (P ∪ M)
  have h4 : 4 * (P.card * M.card) ≤ (P.card + M.card) ^ 2 := by
    zify
    nlinarith [sq_nonneg ((P.card : ℤ) - (M.card : ℤ))]
  exact le_trans h4 (Nat.pow_le_pow_left hsum 2)

/- ### Section 2: Walk and acyclicity helpers for rooted tree decomposition -/

private lemma walk_support_head? {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.head? = some u := by
  cases p <;> rfl

private lemma walk_eq_of_support_eq {V : Type*} {G : SimpleGraph V} {u v : V}
    {p q : G.Walk u v} (h : p.support = q.support) : p = q := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons _ _ => simp at h
  | cons hadj p' ih =>
    cases q with
    | nil => simp at h
    | cons hadj' q' =>
      simp only [SimpleGraph.Walk.support_cons, List.cons.injEq] at h
      have hhead : _ = _ := congrArg List.head? h.2
      rw [walk_support_head?, walk_support_head?, Option.some.injEq] at hhead
      subst hhead
      congr 1
      exact ih h.2

private lemma isAcyclic_induce {V : Type*} (T : SimpleGraph V) (hA : T.IsAcyclic) (S : Set V) :
    (T.induce S).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_subsingleton_path]
  intro u v
  refine ⟨fun p q => ?_⟩
  let emb : T.induce S ↪g T := SimpleGraph.Embedding.induce S
  let p' : T.Walk u.1 v.1 := p.1.map emb.toHom
  let q' : T.Walk u.1 v.1 := q.1.map emb.toHom
  have hp'_supp : p'.support = p.1.support.map Subtype.val :=
    SimpleGraph.Walk.support_map emb.toHom p.1
  have hq'_supp : q'.support = q.1.support.map Subtype.val :=
    SimpleGraph.Walk.support_map emb.toHom q.1
  have hp' : p'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hp'_supp]
    exact p.2.support_nodup.map Subtype.val_injective
  have hq' : q'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hq'_supp]
    exact q.2.support_nodup.map Subtype.val_injective
  have heq : (⟨p', hp'⟩ : T.Path u.1 v.1) = ⟨q', hq'⟩ :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hA u.1 v.1).elim _ _
  have hsupp : p'.support = q'.support := congrArg (fun x => x.1.support) heq
  rw [hp'_supp, hq'_supp] at hsupp
  have hsupp' : p.1.support = q.1.support :=
    (List.map_injective_iff.mpr Subtype.val_injective) hsupp
  exact Subtype.ext (walk_eq_of_support_eq hsupp')

private lemma lift_walk_reachable {V : Type*} (T : SimpleGraph V) (S : Set V) :
    ∀ {a b : V} (w : T.Walk a b), (∀ z ∈ w.support, z ∈ S) →
      ∃ (ha : a ∈ S) (hb : b ∈ S), (T.induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b w
  induction w with
  | @nil u =>
    intro hS
    have hu : u ∈ S := hS u (by simp)
    exact ⟨hu, hu, SimpleGraph.Reachable.refl _⟩
  | @cons u v z huv w' ih =>
    intro hS
    have hu : u ∈ S := hS u (by simp)
    have hS' : ∀ t ∈ w'.support, t ∈ S := fun t ht => hS t (by simp [ht])
    obtain ⟨hv, hz, hreach⟩ := ih hS'
    have hadj : (T.induce S).Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
    exact ⟨hu, hz, hadj.reachable.trans hreach⟩

/- ### Section 3: Gluing subtree orientations around the root -/

private lemma glue_orientations.{u, v} {V : Type u} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (r : V) (N_r : Finset V) (comp : V → Finset V)
    (hNr_eq : ∀ b : V, b ∈ N_r ↔ T.Adj r b)
    (hc_mem : ∀ c ∈ N_r, c ∈ comp c)
    (hr_not_mem : ∀ c : V, r ∉ comp c)
    (hcover : ∀ w : V, w ≠ r → ∃ c ∈ N_r, w ∈ comp c)
    (hcomp_disj : ∀ c₁ ∈ N_r, ∀ c₂ ∈ N_r, c₁ ≠ c₂ → Disjoint (comp c₁) (comp c₂))
    (hno_cross : ∀ c₁ ∈ N_r, ∀ c₂ ∈ N_r, ∀ a ∈ comp c₁, ∀ b ∈ comp c₂, T.Adj a b → c₁ = c₂)
    (Out : Finset V) (hOut_sub : Out ⊆ N_r) (k : ℕ)
    (hNr_card : N_r.card = 2 * k) (hOut_card : Out.card = k)
    (Dc : ∀ c : ↥N_r, Digraph ↥(comp c.1 : Set V))
    (hDc_ori : ∀ c : ↥N_r, (Dc c).IsOrientation (T.induce (comp c.1 : Set V)))
    (hDc_bd : ∀ (c : ↥N_r) {W : Type v} [Fintype W] (G : Digraph W),
      G.IsTournament → ∀ y : W,
        2 ^ ((comp c.1).card - 1) * (homsAt (Dc c) G ⟨c.1, hc_mem c.1 c.2⟩ y).card ≤
          (Fintype.card W) ^ ((comp c.1).card - 1)) :
    ∃ (D : Digraph V),
      D.IsOrientation T ∧
      ∀ {W : Type v} [Fintype W] (G : Digraph W),
        G.IsTournament →
        ∀ x : W,
          2 ^ (Fintype.card V - 1) * (homsAt D G r x).card ≤
            (Fintype.card W) ^ (Fintype.card V - 1) := by
  have hcomp_ne_r : ∀ c : V, ∀ w ∈ comp c, w ≠ r := fun c w hw h => hr_not_mem c (h ▸ hw)
  have hIn_card : (N_r \ Out).card = k := by
    have h := Finset.card_union_of_disjoint (Finset.disjoint_sdiff : Disjoint Out (N_r \ Out))
    rw [Finset.union_sdiff_of_subset hOut_sub] at h
    omega
  let D : Digraph V :=
    { Adj := fun a b =>
        (a = r ∧ b ∈ Out) ∨
        (b = r ∧ a ∈ N_r \ Out) ∨
        (∃ (c : ↥N_r) (ha : a ∈ comp c.1) (hb : b ∈ comp c.1),
          (Dc c).Adj ⟨a, ha⟩ ⟨b, hb⟩) }
  have hD_ori : D.IsOrientation T := by
    constructor
    · intro a b hab
      rcases hab with ⟨har, hb⟩ | ⟨hbr, ha⟩ | ⟨c, ha, hb, h⟩
      · rw [har]; exact (hNr_eq b).mp (hOut_sub hb)
      · rw [hbr]; exact ((hNr_eq a).mp (Finset.mem_sdiff.mp ha).1).symm
      · exact (hDc_ori c).1 ⟨a, ha⟩ ⟨b, hb⟩ h
    · intro a b hab
      by_cases har : a = r
      · rw [har] at hab ⊢
        have hb_ne : b ≠ r := (T.ne_of_adj hab).symm
        have hbNr : b ∈ N_r := (hNr_eq b).mpr hab
        have h1 : D.Adj r b ↔ b ∈ Out := by
          constructor
          · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨c, hr, _⟩)
            · exact h
            · exact absurd h hb_ne
            · exact absurd hr (hr_not_mem c.1)
          · exact fun h => Or.inl ⟨rfl, h⟩
        have h2 : D.Adj b r ↔ b ∈ N_r \ Out := by
          constructor
          · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨c, _, hr, _⟩)
            · exact absurd h hb_ne
            · exact h
            · exact absurd hr (hr_not_mem c.1)
          · exact fun h => Or.inr (Or.inl ⟨rfl, h⟩)
        rw [h1, h2]
        simp [hbNr]
      · by_cases hbr : b = r
        · rw [hbr] at hab ⊢
          have haNr : a ∈ N_r := (hNr_eq a).mpr hab.symm
          have h1 : D.Adj a r ↔ a ∈ N_r \ Out := by
            constructor
            · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨c, _, hr, _⟩)
              · exact absurd h har
              · exact h
              · exact absurd hr (hr_not_mem c.1)
            · exact fun h => Or.inr (Or.inl ⟨rfl, h⟩)
          have h2 : D.Adj r a ↔ a ∈ Out := by
            constructor
            · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨c, hr, _⟩)
              · exact h
              · exact absurd h har
              · exact absurd hr (hr_not_mem c.1)
            · exact fun h => Or.inl ⟨rfl, h⟩
          rw [h1, h2]
          simp [haNr]
        · obtain ⟨c₁, hc₁, ha₁⟩ := hcover a har
          obtain ⟨c₂, hc₂, hb₂⟩ := hcover b hbr
          have hceq : c₁ = c₂ := hno_cross c₁ hc₁ c₂ hc₂ a ha₁ b hb₂ hab
          subst hceq
          let c : ↥N_r := ⟨c₁, hc₁⟩
          have h1 : D.Adj a b ↔ (Dc c).Adj ⟨a, ha₁⟩ ⟨b, hb₂⟩ := by
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨c', ha', hb', h⟩)
              · exact absurd h har
              · exact absurd h hbr
              · have hcc : c' = c := by
                  apply Subtype.ext
                  by_contra hne
                  exact Finset.disjoint_left.mp (hcomp_disj c'.1 c'.2 c.1 c.2 hne) ha' ha₁
                subst hcc
                exact h
            · exact fun h => Or.inr (Or.inr ⟨c, ha₁, hb₂, h⟩)
          have h2 : D.Adj b a ↔ (Dc c).Adj ⟨b, hb₂⟩ ⟨a, ha₁⟩ := by
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨c', hb', ha', h⟩)
              · exact absurd h hbr
              · exact absurd h har
              · have hcc : c' = c := by
                  apply Subtype.ext
                  by_contra hne
                  exact Finset.disjoint_left.mp (hcomp_disj c'.1 c'.2 c.1 c.2 hne) hb' hb₂
                subst hcc
                exact h
            · exact fun h => Or.inr (Or.inr ⟨c, hb₂, ha₁, h⟩)
          rw [h1, h2]
          exact (hDc_ori c).2 ⟨a, ha₁⟩ ⟨b, hb₂⟩ hab
  refine ⟨D, hD_ori, fun {W} _ G hG x => ?_⟩
  let P : Finset W := Finset.univ.filter (fun y : W => G.Adj x y)
  let M : Finset W := Finset.univ.filter (fun y : W => G.Adj y x)
  let L : ∀ c : ↥N_r, Finset (↥(comp c.1 : Set V) → W) :=
    fun c => localHoms (Dc c) G ⟨c.1, hc_mem c.1 c.2⟩ x (decide (c.1 ∈ Out))
  -- Bijection between homsAt D G r x and ∏ c : N_r, L c
  have hcard_prod : (homsAt D G r x).card = ∏ c : ↥N_r, (L c).card := by
    let toF : ↥(homsAt D G r x) → ∀ c : ↥N_r, ↥(L c) := fun f c =>
      ⟨fun a => f.1 a.1, by
        have hf := mem_homsAt.mp f.2
        rw [mem_localHoms]
        refine ⟨fun a b hab => hf.1 a.1 b.1 (Or.inr (Or.inr ⟨c, a.2, b.2, hab⟩)), ?_⟩
        by_cases hOut : c.1 ∈ Out
        · simp only [hOut, decide_true, ↓reduceIte]
          have h1 := hf.1 r c.1 (Or.inl ⟨rfl, hOut⟩)
          rwa [hf.2] at h1
        · simp only [hOut, decide_false, Bool.false_eq_true, ↓reduceIte]
          have h1 := hf.1 c.1 r (Or.inr (Or.inl ⟨rfl, Finset.mem_sdiff.mpr ⟨c.2, hOut⟩⟩))
          rwa [hf.2] at h1⟩
    let mkFun : (∀ c : ↥N_r, ↥(L c)) → (V → W) := fun g w =>
      if hw : w = r then x
      else
        let c0 := Classical.choose (hcover w hw)
        let hc0 := Classical.choose_spec (hcover w hw)
        (g ⟨c0, hc0.1⟩).1 ⟨w, hc0.2⟩
    have hmkFun_comp : ∀ (g : ∀ c : ↥N_r, ↥(L c)) (c : ↥N_r) (a : ↥(comp c.1 : Set V)),
        mkFun g a.1 = (g c).1 a := by
      intro g c a
      have hne : a.1 ≠ r := hcomp_ne_r c.1 a.1 a.2
      simp only [mkFun, dif_neg hne]
      have hc0 := Classical.choose_spec (hcover a.1 hne)
      have hceq : (⟨Classical.choose (hcover a.1 hne), hc0.1⟩ : ↥N_r) = c := by
        apply Subtype.ext
        by_contra hdiff
        exact Finset.disjoint_left.mp
          (hcomp_disj (Classical.choose (hcover a.1 hne)) hc0.1 c.1 c.2 hdiff) hc0.2 a.2
      have hval : ∀ (c₁ c₂ : ↥N_r) (w : V) (h₁ : w ∈ comp c₁.1) (h₂ : w ∈ comp c₂.1),
          c₁ = c₂ → (g c₁).1 ⟨w, h₁⟩ = (g c₂).1 ⟨w, h₂⟩ := by
        rintro c₁ c₂ w h₁ h₂ rfl; rfl
      exact hval _ c a.1 hc0.2 a.2 hceq
    let invF : (∀ c : ↥N_r, ↥(L c)) → ↥(homsAt D G r x) := fun g =>
      ⟨mkFun g, by
        rw [mem_homsAt]
        refine ⟨fun a b hab => ?_, by simp [mkFun]⟩
        rcases hab with ⟨har, hbOut⟩ | ⟨hbr, haIn⟩ | ⟨c, ha, hb, h⟩
        · rw [har]
          have hbNr : b ∈ N_r := hOut_sub hbOut
          let cb : ↥N_r := ⟨b, hbNr⟩
          have hfb : mkFun g b = (g cb).1 ⟨b, hc_mem b hbNr⟩ :=
            hmkFun_comp g cb ⟨b, hc_mem b hbNr⟩
          have hfr : mkFun g r = x := by simp [mkFun]
          rw [hfr, hfb]
          have hg := (mem_localHoms.mp (g cb).2).2
          simpa [cb, hbOut] using hg
        · rw [hbr]
          have haNr : a ∈ N_r := (Finset.mem_sdiff.mp haIn).1
          have haNotOut : a ∉ Out := (Finset.mem_sdiff.mp haIn).2
          let ca : ↥N_r := ⟨a, haNr⟩
          have hfa : mkFun g a = (g ca).1 ⟨a, hc_mem a haNr⟩ :=
            hmkFun_comp g ca ⟨a, hc_mem a haNr⟩
          have hfr : mkFun g r = x := by simp [mkFun]
          rw [hfr, hfa]
          have hg := (mem_localHoms.mp (g ca).2).2
          simpa [ca, haNotOut] using hg
        · rw [hmkFun_comp g c ⟨a, ha⟩, hmkFun_comp g c ⟨b, hb⟩]
          exact (mem_localHoms.mp (g c).2).1 ⟨a, ha⟩ ⟨b, hb⟩ h⟩
    let e : ↥(homsAt D G r x) ≃ ∀ c : ↥N_r, ↥(L c) :=
      { toFun := toF
        invFun := invF
        left_inv := fun f => by
          apply Subtype.ext
          ext w
          by_cases hw : w = r
          · rw [hw]
            simpa [invF, mkFun] using (mem_homsAt.mp f.2).2.symm
          · obtain ⟨c, hc, hwc⟩ := hcover w hw
            exact hmkFun_comp (toF f) ⟨c, hc⟩ ⟨w, hwc⟩
        right_inv := fun g => by
          ext c a
          exact hmkFun_comp g c a }
    rw [← Fintype.card_coe (homsAt D G r x), Fintype.card_congr e, Fintype.card_pi]
    refine Finset.prod_congr rfl fun c _ => Fintype.card_coe (L c)
  -- Bound each factor 2 ^ (|comp c| - 1) * |L c|
  have hfactor : ∀ c : ↥N_r,
      2 ^ ((comp c.1).card - 1) * (L c).card ≤
        (if c.1 ∈ Out then P.card else M.card) * (Fintype.card W) ^ ((comp c.1).card - 1) := by
    intro c
    by_cases hOut : c.1 ∈ Out
    · simp only [L, hOut, decide_true, ↓reduceIte]
      rw [card_localHoms_true, Finset.mul_sum]
      calc ∑ y ∈ P, 2 ^ ((comp c.1).card - 1) *
              (homsAt (Dc c) G ⟨c.1, hc_mem c.1 c.2⟩ y).card
          ≤ ∑ _y ∈ P, (Fintype.card W) ^ ((comp c.1).card - 1) :=
            Finset.sum_le_sum fun y _ => hDc_bd c G hG y
        _ = P.card * (Fintype.card W) ^ ((comp c.1).card - 1) := by
            rw [Finset.sum_const, smul_eq_mul]
    · simp only [L, hOut, decide_false, ↓reduceIte]
      rw [card_localHoms_false, Finset.mul_sum]
      calc ∑ y ∈ M, 2 ^ ((comp c.1).card - 1) *
              (homsAt (Dc c) G ⟨c.1, hc_mem c.1 c.2⟩ y).card
          ≤ ∑ _y ∈ M, (Fintype.card W) ^ ((comp c.1).card - 1) :=
            Finset.sum_le_sum fun y _ => hDc_bd c G hG y
        _ = M.card * (Fintype.card W) ^ ((comp c.1).card - 1) := by
            rw [Finset.sum_const, smul_eq_mul]
  -- Sum of component sizes: |V| - 1 = 2 * k + ∑ c : N_r, (|comp c| - 1)
  let S_rem : ℕ := ∑ c : ↥N_r, ((comp c.1).card - 1)
  have hV_sum : Fintype.card V - 1 = 2 * k + S_rem := by
    have huniv : (Finset.univ : Finset V) = insert r (N_r.biUnion comp) := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_biUnion, true_iff]
      by_cases hw : w = r
      · exact Or.inl hw
      · exact Or.inr (hcover w hw)
    have hr_not_bi : r ∉ N_r.biUnion comp := by
      simp only [Finset.mem_biUnion]
      rintro ⟨c, _, hrc⟩
      exact hr_not_mem c hrc
    have hpw : Set.PairwiseDisjoint (N_r : Set V) comp :=
      fun c₁ hc₁ c₂ hc₂ hne => hcomp_disj c₁ hc₁ c₂ hc₂ hne
    have hcard_V : Fintype.card V = 1 + ∑ c ∈ N_r, (comp c).card := by
      rw [← Finset.card_univ, huniv, Finset.card_insert_of_notMem hr_not_bi,
        Finset.card_biUnion hpw, add_comm]
    have hsum_split : ∑ c ∈ N_r, (comp c).card =
        N_r.card + ∑ c : ↥N_r, ((comp c.1).card - 1) := by
      rw [← Finset.sum_coe_sort N_r (fun c => (comp c).card)]
      have hterm : ∀ c : ↥N_r, (comp c.1).card = 1 + ((comp c.1).card - 1) := by
        intro c
        have hpos : 1 ≤ (comp c.1).card := Finset.card_pos.mpr ⟨c.1, hc_mem c.1 c.2⟩
        omega
      rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_one]
    omega
  -- Multiply all factors together and apply AM-GM (4 * P.card * M.card ≤ |W|^2)
  have hprod_le :
      (∏ c : ↥N_r, 2 ^ ((comp c.1).card - 1)) * (homsAt D G r x).card ≤
        (∏ c : ↥N_r, if c.1 ∈ Out then P.card else M.card) *
          (∏ c : ↥N_r, (Fintype.card W) ^ ((comp c.1).card - 1)) := by
    rw [hcard_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun c _ => hfactor c
  have hprod_PM : (∏ c : ↥N_r, if c.1 ∈ Out then P.card else M.card) =
      P.card ^ k * M.card ^ k := by
    rw [Finset.prod_coe_sort N_r (fun c => if c ∈ Out then P.card else M.card)]
    rw [← Finset.union_sdiff_of_subset hOut_sub,
      Finset.prod_union (Finset.disjoint_sdiff : Disjoint Out (N_r \ Out))]
    have hP : ∏ c ∈ Out, (if c ∈ Out then P.card else M.card) = P.card ^ k := by
      rw [Finset.prod_congr rfl fun c hc => if_pos hc, Finset.prod_const, hOut_card]
    have hM : ∏ c ∈ N_r \ Out, (if c ∈ Out then P.card else M.card) = M.card ^ k := by
      rw [Finset.prod_congr rfl fun c hc => if_neg (Finset.mem_sdiff.mp hc).2,
        Finset.prod_const, hIn_card]
    rw [hP, hM]
  have hprod_2 : (∏ c : ↥N_r, 2 ^ ((comp c.1).card - 1)) = 2 ^ S_rem := by
    rw [Finset.prod_pow_eq_pow_sum]
  have hprod_W : (∏ c : ↥N_r, (Fintype.card W) ^ ((comp c.1).card - 1)) =
      (Fintype.card W) ^ S_rem := by
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hprod_2, hprod_PM, hprod_W] at hprod_le
  have hAMGM : 4 * (P.card * M.card) ≤ (Fintype.card W) ^ 2 :=
    tournament_four_mul_out_in_le G hG x
  have hpow_AMGM : 2 ^ (2 * k) * (P.card ^ k * M.card ^ k) ≤ (Fintype.card W) ^ (2 * k) := by
    calc 2 ^ (2 * k) * (P.card ^ k * M.card ^ k)
        = (2 ^ 2) ^ k * (P.card * M.card) ^ k := by rw [pow_mul, mul_pow]
      _ = (4 * (P.card * M.card)) ^ k := by rw [← mul_pow]; norm_num
      _ ≤ ((Fintype.card W) ^ 2) ^ k := Nat.pow_le_pow_left hAMGM k
      _ = (Fintype.card W) ^ (2 * k) := by rw [← pow_mul]
  rw [hV_sum, pow_add, pow_add, mul_assoc]
  calc 2 ^ (2 * k) * (2 ^ S_rem * (homsAt D G r x).card)
      ≤ 2 ^ (2 * k) * (P.card ^ k * M.card ^ k * (Fintype.card W) ^ S_rem) :=
        Nat.mul_le_mul_left _ hprod_le
    _ = (2 ^ (2 * k) * (P.card ^ k * M.card ^ k)) * (Fintype.card W) ^ S_rem := by ring
    _ ≤ (Fintype.card W) ^ (2 * k) * (Fintype.card W) ^ S_rem :=
        Nat.mul_le_mul_right _ hpow_AMGM

/- ### Section 4: Main strong induction on tree size -/

private lemma exists_good_orientation.{u, v} :
    ∀ (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V]
      (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree →
      ∀ (r : V), Even (T.degree r) → (∀ x, x ≠ r → Odd (T.degree x)) →
      Fintype.card V = n →
      ∃ (D : Digraph V),
        D.IsOrientation T ∧
        ∀ {W : Type v} [Fintype W] (G : Digraph W),
          G.IsTournament →
          ∀ x : W,
            2 ^ (Fintype.card V - 1) * (homsAt D G r x).card ≤
              (Fintype.card W) ^ (Fintype.card V - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ T _ hTree r hr_even h_odd hcard
    let N_r : Finset V := T.neighborFinset r
    let S_del : Set V := { w : V | w ≠ r }
    let T_del : SimpleGraph ↥S_del := T.induce S_del
    let comp : V → Finset V := fun c =>
      Finset.univ.filter (fun w => ∃ (hw : w ≠ r) (hc : c ≠ r), T_del.Reachable ⟨c, hc⟩ ⟨w, hw⟩)
    have hNr_eq : ∀ b : V, b ∈ N_r ↔ T.Adj r b := fun b => mem_neighborFinset T r b
    have hNr_ne : ∀ c ∈ N_r, c ≠ r := fun c hc => (T.ne_of_adj ((hNr_eq c).mp hc)).symm
    have hc_mem : ∀ c ∈ N_r, c ∈ comp c := by
      intro c hc
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hNr_ne c hc, hNr_ne c hc, SimpleGraph.Reachable.refl _⟩
    have hr_not_mem : ∀ c : V, r ∉ comp c := by
      intro c h
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨hneq, _⟩ := h
      exact hneq rfl
    have hcomp_ne_r : ∀ c : V, ∀ w ∈ comp c, w ≠ r := fun c w hw h => hr_not_mem c (h ▸ hw)
    have hcover : ∀ w : V, w ≠ r → ∃ c ∈ N_r, w ∈ comp c := by
      intro w hw
      obtain ⟨p, hp, _⟩ := hTree.existsUnique_path r w
      cases p with
      | nil => exact absurd rfl hw
      | @cons _ c _ hrc p' =>
        have hcNr : c ∈ N_r := (hNr_eq c).mpr hrc
        have hr_not_supp : r ∉ p'.support := by
          have hnodup := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
          exact hnodup.1
        have hS_supp : ∀ z ∈ p'.support, z ∈ S_del := fun z hz hzr =>
          hr_not_supp (hzr ▸ hz)
        obtain ⟨hc', hw', hreach⟩ := lift_walk_reachable T S_del p' hS_supp
        refine ⟨c, hcNr, ?_⟩
        simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hw', hc', hreach⟩
    have hcomp_disj : ∀ c₁ ∈ N_r, ∀ c₂ ∈ N_r, c₁ ≠ c₂ → Disjoint (comp c₁) (comp c₂) := by
      intro c₁ hc₁ c₂ hc₂ hne
      rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
      obtain ⟨hw_ne, hc₁_ne, hr₁⟩ := hw₁
      obtain ⟨_, hc₂_ne, hr₂⟩ := hw₂
      have hreach : T_del.Reachable ⟨c₁, hc₁_ne⟩ ⟨c₂, hc₂_ne⟩ := hr₁.trans hr₂.symm
      obtain ⟨p_del⟩ := hreach
      let q_del := p_del.toPath
      let emb : T_del ↪g T := SimpleGraph.Embedding.induce S_del
      let q : T.Walk c₁ c₂ := q_del.1.map emb.toHom
      have hq_supp : q.support = q_del.1.support.map Subtype.val :=
        SimpleGraph.Walk.support_map emb.toHom q_del.1
      have hq_nodup : q.support.Nodup := by
        rw [hq_supp]
        exact q_del.2.support_nodup.map Subtype.val_injective
      have hr_not_q : r ∉ q.support := by
        rw [hq_supp, List.mem_map]
        rintro ⟨z, _, hz⟩
        exact z.2 hz
      have hrc₁ : T.Adj r c₁ := (hNr_eq c₁).mp hc₁
      have hrc₂ : T.Adj r c₂ := (hNr_eq c₂).mp hc₂
      let path1 : T.Walk r c₂ := SimpleGraph.Walk.cons hrc₂ SimpleGraph.Walk.nil
      let path2 : T.Walk r c₂ := SimpleGraph.Walk.cons hrc₁ q
      have hp1 : path1.IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        simp [path1, hrc₂.ne]
      have hp2 : path2.IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        simp [path2, List.nodup_cons, hr_not_q, hq_nodup]
      have hpeq : path1 = path2 :=
        (hTree.existsUnique_path r c₂).unique hp1 hp2
      have hsupp_eq := congrArg SimpleGraph.Walk.support hpeq
      have htail_head := congrArg (fun l => l.tail.head?) hsupp_eq
      simp only [path1, path2, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.tail_cons, List.head?_cons] at htail_head
      rw [walk_support_head?, Option.some.injEq] at htail_head
      exact hne htail_head.symm
    have hcomp_closed : ∀ c ∈ N_r, ∀ a ∈ comp c, ∀ b : V, b ≠ r → T.Adj a b → b ∈ comp c := by
      intro c _ a ha b hb hab
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨ha_ne, hc_ne, hreach⟩ := ha
      have hadj : T_del.Adj ⟨a, ha_ne⟩ ⟨b, hb⟩ := hab
      exact ⟨hb, hc_ne, hreach.trans hadj.reachable⟩
    have hno_cross : ∀ c₁ ∈ N_r, ∀ c₂ ∈ N_r, ∀ a ∈ comp c₁, ∀ b ∈ comp c₂, T.Adj a b → c₁ = c₂ := by
      intro c₁ hc₁ c₂ hc₂ a ha b hb hab
      by_contra hne
      have hb1 : b ∈ comp c₁ := hcomp_closed c₁ hc₁ a ha b (hcomp_ne_r c₂ b hb) hab
      exact Finset.disjoint_left.mp (hcomp_disj c₁ hc₁ c₂ hc₂ hne) hb1 hb
    have hr_adj_comp : ∀ c ∈ N_r, ∀ a ∈ comp c, T.Adj r a → a = c := by
      intro c hc a ha hra
      have haNr : a ∈ N_r := (hNr_eq a).mpr hra
      by_contra hne
      exact Finset.disjoint_left.mp (hcomp_disj a haNr c hc hne) (hc_mem a haNr) ha
    -- Apply strong IH to each subtree (T_c, c)
    have hsub_exists : ∀ c : ↥N_r,
        ∃ (Dc : Digraph ↥(comp c.1 : Set V)),
          Dc.IsOrientation (T.induce (comp c.1 : Set V)) ∧
          ∀ {W : Type v} [Fintype W] (G : Digraph W),
            G.IsTournament →
            ∀ y : W,
              2 ^ ((comp c.1).card - 1) *
                (homsAt Dc G ⟨c.1, hc_mem c.1 c.2⟩ y).card ≤
                (Fintype.card W) ^ ((comp c.1).card - 1) := by
      intro c
      let Tc : SimpleGraph ↥(comp c.1 : Set V) := T.induce (comp c.1 : Set V)
      have hcard_c : Fintype.card ↥(comp c.1 : Set V) = (comp c.1).card := Fintype.card_coe (comp c.1)
      have hcard_lt : (comp c.1).card < n := by
        rw [← hcard]
        have hss : comp c.1 ⊂ Finset.univ := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.subset_univ _, fun heq => hr_not_mem c.1 (heq ▸ Finset.mem_univ r)⟩
        exact Finset.card_lt_card hss
      have : Nonempty ↥(comp c.1 : Set V) := ⟨⟨c.1, hc_mem c.1 c.2⟩⟩
      have hTc_conn : Tc.Connected :=
        SimpleGraph.Connected.mk fun ⟨a, ha⟩ ⟨b, hb⟩ => by
          have ha' := ha
          have hb' := hb
          simp only [Finset.mem_coe, comp, Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
          obtain ⟨ha_ne, hc_ne, hra⟩ := ha'
          obtain ⟨hb_ne, _, hrb⟩ := hb'
          obtain ⟨w⟩ := hra.symm.trans hrb
          have hw_in : ∀ z ∈ (w.map (SimpleGraph.Embedding.induce S_del).toHom).support,
              z ∈ (comp c.1 : Set V) := by
            intro z hz
            have hws : (w.map (SimpleGraph.Embedding.induce S_del).toHom).support =
                w.support.map Subtype.val := by
              rw [SimpleGraph.Walk.support_map]; rfl
            rw [hws, List.mem_map] at hz
            obtain ⟨z', hz', rfl⟩ := hz
            have hreach_z : T_del.Reachable ⟨a, ha_ne⟩ z' :=
              (w.takeUntil z' hz').reachable
            simp only [Finset.mem_coe, comp, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨z'.2, hc_ne, hra.trans hreach_z⟩
          obtain ⟨_, _, hreach_c⟩ :=
            lift_walk_reachable T (comp c.1 : Set V)
              (w.map (SimpleGraph.Embedding.induce S_del).toHom) hw_in
          exact hreach_c
      have hTc_tree : Tc.IsTree := ⟨hTc_conn, isAcyclic_induce T hTree.isAcyclic _⟩
      have hdeg_nonroot : ∀ u : ↥(comp c.1 : Set V), u ≠ ⟨c.1, hc_mem c.1 c.2⟩ →
          Tc.degree u = T.degree u.1 := by
        intro u hu
        rw [SimpleGraph.degree, SimpleGraph.degree]
        refine Finset.card_bij (fun w _ => w.1)
          (fun w hw => (mem_neighborFinset T u.1 w.1).mpr ((mem_neighborFinset Tc u w).mp hw))
          (fun _ _ _ _ h => Subtype.ext h)
          (fun b hb => ?_)
        have hub : T.Adj u.1 b := (mem_neighborFinset T u.1 b).mp hb
        have hb_ne_r : b ≠ r := by
          intro hbr
          rw [hbr] at hub
          exact hu (Subtype.ext (hr_adj_comp c.1 c.2 u.1 u.2 hub.symm))
        have hb_comp : b ∈ comp c.1 := hcomp_closed c.1 c.2 u.1 u.2 b hb_ne_r hub
        exact ⟨⟨b, hb_comp⟩, (mem_neighborFinset Tc u ⟨b, hb_comp⟩).mpr hub, rfl⟩
      have hdeg_root : Tc.degree ⟨c.1, hc_mem c.1 c.2⟩ + 1 = T.degree c.1 := by
        let c' : ↥(comp c.1 : Set V) := ⟨c.1, hc_mem c.1 c.2⟩
        have hnb_eq : T.neighborFinset c.1 =
            insert r ((Tc.neighborFinset c').image Subtype.val) := by
          ext b
          simp only [Finset.mem_insert, Finset.mem_image, mem_neighborFinset]
          constructor
          · intro hcb
            by_cases hbr : b = r
            · exact Or.inl hbr
            · right
              have hb_comp : b ∈ comp c.1 :=
                hcomp_closed c.1 c.2 c.1 (hc_mem c.1 c.2) b hbr hcb
              exact ⟨⟨b, hb_comp⟩, hcb, rfl⟩
          · rintro (hbr | ⟨w, hw, rfl⟩)
            · rw [hbr]
              exact ((hNr_eq c.1).mp c.2).symm
            · exact hw
        have hr_not_img : r ∉ (Tc.neighborFinset c').image Subtype.val := by
          simp only [Finset.mem_image]
          rintro ⟨w, _, hwr⟩
          exact hr_not_mem c.1 (hwr ▸ w.2)
        change (Tc.neighborFinset c').card + 1 = (T.neighborFinset c.1).card
        rw [hnb_eq, Finset.card_insert_of_notMem hr_not_img,
          Finset.card_image_of_injective _ Subtype.val_injective]
      have hc_even : Even (Tc.degree ⟨c.1, hc_mem c.1 c.2⟩) := by
        have hodd_c : Odd (T.degree c.1) := h_odd c.1 (hNr_ne c.1 c.2)
        rw [← hdeg_root] at hodd_c
        obtain ⟨m, hm⟩ := hodd_c
        exact ⟨m, by omega⟩
      have hc_odd : ∀ u : ↥(comp c.1 : Set V), u ≠ ⟨c.1, hc_mem c.1 c.2⟩ → Odd (Tc.degree u) := by
        intro u hu
        rw [hdeg_nonroot u hu]
        exact h_odd u.1 (hcomp_ne_r c.1 u.1 u.2)
      obtain ⟨Dc, hDc_ori, hDc_bd⟩ :=
        ih (comp c.1).card hcard_lt Tc hTc_tree ⟨c.1, hc_mem c.1 c.2⟩ hc_even hc_odd hcard_c
      refine ⟨Dc, hDc_ori, fun {W} _ G hG y => ?_⟩
      simpa [hcard_c] using hDc_bd G hG y
    choose Dc hDc_ori hDc_bd using hsub_exists
    obtain ⟨k, hk⟩ := hr_even
    have hNr_card : N_r.card = 2 * k := by
      change T.degree r = 2 * k
      omega
    obtain ⟨Out, hOut_sub, hOut_card⟩ :=
      Finset.exists_subset_card_eq (show k ≤ N_r.card by omega)
    exact glue_orientations T r N_r comp hNr_eq hc_mem hr_not_mem hcover hcomp_disj hno_cross
      Out hOut_sub k hNr_card hOut_card Dc hDc_ori hDc_bd

end TASTreesSingleEvenProof

theorem OMA.solution :
    type_of% @SidorenkoConjecture.tournament_anti_sidorenko_single_even_degree_tree := by
  classical
  intro V _ _ T _ hTree hEven
  obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hEven
  have hr_even : Even (T.degree r) := by
    have : r ∈ Finset.univ.filter (fun v => Even (T.degree v)) := by rw [hr_eq]; simp
    exact (Finset.mem_filter.mp this).2
  have h_odd : ∀ u : V, u ≠ r → Odd (T.degree u) := by
    intro u hu
    rw [← Nat.not_even_iff_odd]
    intro hev
    have hmem : u ∈ Finset.univ.filter (fun v => Even (T.degree v)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ u, hev⟩
    rw [hr_eq, Finset.mem_singleton] at hmem
    exact hu hmem
  obtain ⟨D, hD_ori, hD_bd⟩ :=
    TASTreesSingleEvenProof.exists_good_orientation (Fintype.card V) T hTree r hr_even h_odd rfl
  refine ⟨D, hD_ori, fun {W} _ _ _ G _ hG => ?_⟩
  have hV_pos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr hTree.connected.nonempty
  have hedge : T.edgeFinset.card = Fintype.card V - 1 := by
    have h := hTree.card_edgeFinset
    omega
  have hnat : 2 ^ T.edgeFinset.card * Digraph.homCount D G ≤ (Fintype.card W) ^ (Fintype.card V) := by
    rw [hedge, TASTreesSingleEvenProof.homCount_eq_card_allHoms,
      TASTreesSingleEvenProof.card_allHoms_eq_sum_homsAt, Finset.mul_sum]
    calc ∑ x : W, 2 ^ (Fintype.card V - 1) *
            (TASTreesSingleEvenProof.homsAt D G r x).card
        ≤ ∑ _x : W, (Fintype.card W) ^ (Fintype.card V - 1) :=
          Finset.sum_le_sum fun x _ => hD_bd G hG x
      _ = Fintype.card W * (Fintype.card W) ^ (Fintype.card V - 1) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = (Fintype.card W) ^ (Fintype.card V) := by
          rw [← pow_succ', Nat.sub_add_cancel hV_pos]
  unfold Digraph.homDensity
  have hW_card_pos : (0 : ℝ) < (Fintype.card W : ℝ) := by positivity
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) ^ (Fintype.card V) := pow_pos hW_card_pos _
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ T.edgeFinset.card := by positivity
  rw [one_div, inv_pow, div_le_iff₀ hW_pos, inv_mul_eq_div, le_div_iff₀ h2_pos, mul_comm]
  exact_mod_cast hnat
