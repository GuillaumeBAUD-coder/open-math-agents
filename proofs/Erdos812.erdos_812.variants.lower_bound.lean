import FormalConjectures.ErdosProblems.«812»
import Mathlib.Data.Finset.Sum

/-!
# The gap between consecutive diagonal Ramsey numbers

Extend a Ramsey-critical graph by two finite cliques. The first clique attaches
to selected original vertices by a matching. The second copies their
neighborhoods, and its matching edges to the first clique are removed.
The enlarged graph avoids the same clique size and independent sets of one
larger size. Apply the resulting one-sided growth bound twice.

References: Burr, Erdős, Faudree and Schelp, On the Difference between
Consecutive Ramsey Numbers, Theorem 1. The graph is the clique case of
the construction cited by Xu, Shao and Radziszowski, Theorem 1 and Corollary 1.
-/

/- Graph and hypergraph Ramsey numbers for two colors. -/

namespace OMA.ER812

def GraphRamseyOn (v a b : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin v), ¬ (G.CliqueFree a ∧ (Gᶜ).CliqueFree b)

private def Mono {v : ℕ} (c : Finset (Fin v) → Bool) (color : Bool)
    (a : ℕ) (S : Finset (Fin v)) : Prop :=
  S.card = a ∧ ∀ e ⊆ S, e.card = 2 → c e = color

private theorem isNClique_iff_mono {v a : ℕ} {G : SimpleGraph (Fin v)}
    {c : Finset (Fin v) → Bool} {color : Bool} {S : Finset (Fin v)}
    (h : ∀ x y, x ≠ y → (G.Adj x y ↔ c {x, y} = color)) :
    G.IsNClique a S ↔ Mono c color a S := by
  rw [SimpleGraph.isNClique_iff]
  constructor
  · rintro ⟨hc, hcard⟩
    refine ⟨hcard, ?_⟩
    intro e he hecard
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
    apply (h x y hxy).mp
    exact hc (he (by simp)) (he (by simp)) hxy
  · rintro ⟨hcard, hc⟩
    refine ⟨?_, hcard⟩
    intro x hx y hy hxy
    exact (h x y hxy).mpr (hc {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (Finset.card_pair hxy))

private theorem compl_adj_iff_false {v : ℕ} {G : SimpleGraph (Fin v)}
    {c : Finset (Fin v) → Bool}
    (h : ∀ x y, x ≠ y → (G.Adj x y ↔ c {x, y} = true)) :
    ∀ x y, x ≠ y → ((Gᶜ).Adj x y ↔ c {x, y} = false) := by
  intro x y hxy
  simp [h x y hxy, SimpleGraph.compl_adj, hxy]

private theorem graphRamseyOn_iff_mono (v a b : ℕ) :
    GraphRamseyOn v a b ↔ ∀ c : Finset (Fin v) → Bool,
      (∃ S, Mono c true a S) ∨ (∃ S, Mono c false b S) := by
  classical
  constructor
  · intro h c
    let G : SimpleGraph (Fin v) :=
      { Adj := fun x y ↦ x ≠ y ∧ c {x, y} = true
        symm := ⟨by
          intro x y hxy
          exact ⟨hxy.1.symm, by rw [Finset.pair_comm y x]; exact hxy.2⟩⟩
        loopless := ⟨fun _ hxx ↦ hxx.1 rfl⟩ }
    have hG (x y : Fin v) (hxy : x ≠ y) : G.Adj x y ↔ c {x, y} = true := by
      exact and_iff_right hxy
    have hc := h G
    rw [SimpleGraph.CliqueFree, SimpleGraph.CliqueFree, not_and_or] at hc
    push Not at hc
    obtain ⟨S, hS⟩ | ⟨S, hS⟩ := hc
    · exact Or.inl ⟨S, (isNClique_iff_mono hG).mp hS⟩
    · exact Or.inr ⟨S, (isNClique_iff_mono (compl_adj_iff_false hG)).mp hS⟩
  · intro h G ⟨hG, hGc⟩
    let c (e : Finset (Fin v)) : Bool := decide (G.IsClique (e : Set (Fin v)))
    have hc (x y : Fin v) (hxy : x ≠ y) : G.Adj x y ↔ c {x, y} = true := by
      simp [c, hxy]
    obtain ⟨S, hS⟩ | ⟨S, hS⟩ := h c
    · exact hG S ((isNClique_iff_mono hc).mpr hS)
    · exact hGc S ((isNClique_iff_mono (compl_adj_iff_false hc)).mpr hS)

theorem classicalRamsey_eq_sInf (a b : ℕ) :
    SimpleGraph.classicalRamsey a b = sInf {v : ℕ | GraphRamseyOn v a b} := by
  classical
  simp only [SimpleGraph.classicalRamsey, SimpleGraph.graphRamsey,
    GraphRamseyOn, not_and_or, SimpleGraph.not_cliqueFree_iff_top_isContained]

theorem hypergraphRamsey_two (n : ℕ) :
    Combinatorics.hypergraphRamsey 2 n = SimpleGraph.classicalRamsey n n := by
  rw [Combinatorics.hypergraphRamsey, classicalRamsey_eq_sInf]
  congr 1
  ext v
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, graphRamseyOn_iff_mono]
  constructor
  · intro h c
    obtain ⟨S, hcard, color, hS⟩ := h c
    cases color
    · exact Or.inr ⟨S, hcard, hS⟩
    · exact Or.inl ⟨S, hcard, hS⟩
  · intro h c
    obtain ⟨S, hcard, hS⟩ | ⟨S, hcard, hS⟩ := h c
    · exact ⟨S, hcard, true, hS⟩
    · exact ⟨S, hcard, false, hS⟩

theorem graphRamseyOn_nonempty (a b : ℕ) :
    {v : ℕ | GraphRamseyOn v a b}.Nonempty := by
  refine ⟨Nat.choose (b + a) b, (graphRamseyOn_iff_mono _ _ _).mpr ?_⟩
  intro c
  obtain ⟨S, _, hcard, hS⟩ | ⟨S, _, hcard, hS⟩ :=
    Combinatorics.Diagonal.hasRamseyProperty_choose b a c Finset.univ (by simp)
  · exact Or.inr ⟨S, hcard, hS⟩
  · exact Or.inl ⟨S, hcard, hS⟩

theorem GraphRamseyOn.mono {v w a b : ℕ} (hvw : v ≤ w) :
    GraphRamseyOn v a b → GraphRamseyOn w a b := by
  intro h G ⟨hG, hGc⟩
  let e : Fin v ↪ Fin w := Fin.castLEEmb hvw
  let H : SimpleGraph (Fin v) := G.comap e
  let emb : H ↪g G := SimpleGraph.Embedding.comap e G
  let embc : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv emb
  exact h H ⟨hG.comap emb.isContained, hGc.comap embc.isContained⟩

theorem GraphRamseyOn.symm {v a b : ℕ} :
    GraphRamseyOn v a b ↔ GraphRamseyOn v b a := by
  constructor <;> intro h G <;> simpa [and_comm] using h (Gᶜ)

theorem classicalRamsey_symm (a b : ℕ) :
    SimpleGraph.classicalRamsey a b = SimpleGraph.classicalRamsey b a := by
  rw [classicalRamsey_eq_sInf, classicalRamsey_eq_sInf]
  congr 1
  ext v
  exact GraphRamseyOn.symm

theorem classicalRamsey_le_iff {v a b : ℕ} :
    SimpleGraph.classicalRamsey a b ≤ v ↔ GraphRamseyOn v a b := by
  rw [classicalRamsey_eq_sInf]
  exact ⟨fun hv ↦ GraphRamseyOn.mono hv (Nat.sInf_mem (graphRamseyOn_nonempty a b)),
    fun hv ↦ Nat.sInf_le (show v ∈ {v : ℕ | GraphRamseyOn v a b} from hv)⟩

theorem lt_classicalRamsey_iff {v a b : ℕ} :
    v < SimpleGraph.classicalRamsey a b ↔
      ∃ G : SimpleGraph (Fin v), G.CliqueFree a ∧ (Gᶜ).CliqueFree b := by
  rw [← not_le, classicalRamsey_le_iff, GraphRamseyOn]
  push Not
  rfl

end OMA.ER812

namespace OMA.ER812

private def addRedVertex {r : ℕ} (G : SimpleGraph (Fin r)) :
    SimpleGraph (Fin r ⊕ Fin 1) :=
  ((Gᶜ).sum (⊥ : SimpleGraph (Fin 1)))ᶜ

private theorem addRedVertex_cliqueFree {r a : ℕ} {G : SimpleGraph (Fin r)}
    (hG : G.CliqueFree a) : (addRedVertex G).CliqueFree (a + 1) := by
  intro S hS
  apply hG.mono (m := a) (n := S.toLeft.card) ?_ S.toLeft
  · refine ⟨?_, rfl⟩
    intro x hx y hy hxy
    have hAdj := hS.isClique (Finset.mem_toLeft.mp hx) (Finset.mem_toLeft.mp hy)
      (show Sum.inl x ≠ (Sum.inl y : Fin r ⊕ Fin 1) from fun h ↦ hxy (Sum.inl.inj h))
    simpa [addRedVertex, SimpleGraph.compl_adj, hxy] using hAdj
  · have hleft := S.card_toLeft_add_card_toRight
    have hright : S.toRight.card ≤ 1 := by
      simpa using Finset.card_le_univ S.toRight
    have hcard := hS.card_eq
    omega

private theorem addRedVertex_compl_cliqueFree {r t : ℕ} {G : SimpleGraph (Fin r)}
    (ht : 2 ≤ t) (hG : (Gᶜ).CliqueFree t) : ((addRedVertex G)ᶜ).CliqueFree t := by
  intro S hS
  have hright : S.toRight = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxS : Sum.inr x ∈ S := Finset.mem_toRight.mp hx
    have hsub : S ⊆ {Sum.inr x} := by
      intro y hy
      apply Finset.mem_singleton.mpr
      by_contra! hne
      have hAdj := hS.isClique hy hxS hne
      cases y <;> simp [addRedVertex] at hAdj
    have hcard := Finset.card_le_card hsub
    rw [hS.card_eq, Finset.card_singleton] at hcard
    omega
  apply hG S.toLeft
  constructor
  · intro x hx y hy hxy
    have hAdj := hS.isClique (Finset.mem_toLeft.mp hx) (Finset.mem_toLeft.mp hy)
      (show Sum.inl x ≠ (Sum.inl y : Fin r ⊕ Fin 1) from fun h ↦ hxy (Sum.inl.inj h))
    simpa [addRedVertex] using hAdj
  · simpa [hright, hS.card_eq] using S.card_toLeft_add_card_toRight

theorem exists_criticalGraph (k t : ℕ) (ht : 2 ≤ t) :
    ∃ (r : ℕ) (G : SimpleGraph (Fin r)) (i : Fin k ↪ Fin r),
      r + 1 = SimpleGraph.classicalRamsey (k + 2) t ∧
      G.CliqueFree (k + 2) ∧ (Gᶜ).CliqueFree t ∧
      (∀ j z, j ≠ z → G.Adj (i j) (i z)) := by
  have hpos : 0 < SimpleGraph.classicalRamsey (k + 2) t := by
    apply lt_classicalRamsey_iff.mpr
    refine ⟨⊥, SimpleGraph.cliqueFree_of_card_lt ?_, SimpleGraph.cliqueFree_of_card_lt ?_⟩
    · simp
    · simpa using (show 0 < t by omega)
  let r := SimpleGraph.classicalRamsey (k + 2) t - 1
  have hr : r + 1 = SimpleGraph.classicalRamsey (k + 2) t := by dsimp [r]; omega
  obtain ⟨G, hG, hGc⟩ := lt_classicalRamsey_iff.mp (show r <
      SimpleGraph.classicalRamsey (k + 2) t by omega)
  have hRamsey : GraphRamseyOn (r + 1) (k + 2) t :=
    classicalRamsey_le_iff.mp hr.ge
  have hClique : ¬ G.CliqueFree k := by
    intro hNo
    let e : Fin (r + 1) ↪ Fin r ⊕ Fin 1 := finSumFinEquiv.symm.toEmbedding
    let H := (addRedVertex G).comap e
    let emb : H ↪g addRedVertex G := SimpleGraph.Embedding.comap e _
    let embc : Hᶜ ↪g (addRedVertex G)ᶜ := SimpleGraph.Embedding.complEquiv emb
    apply hRamsey H
    exact ⟨(addRedVertex_cliqueFree (hNo.mono (Nat.le_succ k))).comap emb.isContained,
      (addRedVertex_compl_cliqueFree ht hGc).comap embc.isContained⟩
  let emb := SimpleGraph.topEmbeddingOfNotCliqueFree hClique
  refine ⟨r, G, emb.toEmbedding, hr, hG, hGc, ?_⟩
  intro j z hjz
  exact emb.map_adj_iff.mpr hjz

end OMA.ER812

/- Clique expansion for a Ramsey-number bound. -/

namespace OMA.RamseyGap

open SimpleGraph

/-- The clique expansion used for the one-sided Ramsey-number gap. -/
def enlarged {α : Type*} {k : ℕ} (G : SimpleGraph α) (i : Fin k ↪ α) :
    SimpleGraph (α ⊕ (Fin (k + 1) ⊕ Fin k)) where
  Adj a b := match a, b with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr (.inl b) => ∃ z : Fin k, a = i z ∧ b = z.castSucc
    | .inr (.inl b), .inl a => ∃ z : Fin k, a = i z ∧ b = z.castSucc
    | .inl a, .inr (.inr w) => G.Adj a (i w)
    | .inr (.inr w), .inl a => G.Adj a (i w)
    | .inr (.inl b), .inr (.inl c) => b ≠ c
    | .inr (.inr w), .inr (.inr z) => w ≠ z
    | .inr (.inl b), .inr (.inr w) => b ≠ w.castSucc
    | .inr (.inr w), .inr (.inl b) => b ≠ w.castSucc
  symm := ⟨by
    intro a b h
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    all_goals first | exact h | exact G.adj_symm h | exact Ne.symm h⟩
  loopless := ⟨by
    rintro (a | (b | w))
    · exact G.irrefl
    · exact fun h => h rfl
    · exact fun h => h rfl⟩

end OMA.RamseyGap

namespace OMA.RamseyGap

open SimpleGraph

lemma enlarged_cliqueFree {α : Type*} {k : ℕ} (G : SimpleGraph α) (i : Fin k ↪ α)
    (hi : ∀ j z, j ≠ z → G.Adj (i j) (i z)) (hG : G.CliqueFree (k + 2)) :
    (enlarged G i).CliqueFree (k + 2) := by
  classical
  intro s hs
  obtain ⟨hc, hsCard⟩ := hs
  let A := s.toLeft
  let B := s.toRight.toLeft
  let W := s.toRight.toRight
  have hCard : A.card + B.card + W.card = k + 2 := by
    have hA := Finset.card_toLeft_add_card_toRight (u := s)
    have hB := Finset.card_toLeft_add_card_toRight (u := s.toRight)
    dsimp [A, B, W]
    omega
  have memA {a : α} (ha : a ∈ A) : Sum.inl a ∈ s :=
    Finset.mem_toLeft.mp ha
  have memB {b : Fin (k + 1)} (hb : b ∈ B) : Sum.inr (Sum.inl b) ∈ s :=
    Finset.mem_toRight.mp (Finset.mem_toLeft.mp hb)
  have memW {w : Fin k} (hw : w ∈ W) : Sum.inr (Sum.inr w) ∈ s :=
    Finset.mem_toRight.mp (Finset.mem_toRight.mp hw)
  have hAB {a b} (ha : a ∈ A) (hb : b ∈ B) :
      ∃ z : Fin k, a = i z ∧ b = z.castSucc :=
    hc (memA ha) (memB hb) (by simp)
  have hAW {a w} (ha : a ∈ A) (hw : w ∈ W) : G.Adj a (i w) :=
    hc (memA ha) (memW hw) (by simp)
  have hBW {b w} (hb : b ∈ B) (hw : w ∈ W) : b ≠ w.castSucc :=
    hc (memB hb) (memW hw) (by simp)
  by_cases hAn : A.Nonempty
  · by_cases hBn : B.Nonempty
    · obtain ⟨a, ha⟩ := hAn
      obtain ⟨b, hb⟩ := hBn
      obtain ⟨z, haz, hbz⟩ := hAB ha hb
      have hAs : A ⊆ {a} := by
        intro a' ha'
        obtain ⟨j, haj, hbj⟩ := hAB ha' hb
        have hj : j = z := Fin.castSucc_injective _ (hbj.symm.trans hbz)
        exact Finset.mem_singleton.mpr ((haj.trans (congrArg i hj)).trans haz.symm)
      have hBs : B ⊆ {b} := by
        intro b' hb'
        obtain ⟨j, haj, hbj⟩ := hAB ha hb'
        have hj : j = z := i.injective (haj.symm.trans haz)
        exact Finset.mem_singleton.mpr ((hbj.trans (congrArg Fin.castSucc hj)).trans hbz.symm)
      have hAc : A.card ≤ 1 := by simpa using Finset.card_le_card hAs
      have hBc : B.card ≤ 1 := by simpa using Finset.card_le_card hBs
      have hz : z ∉ W := fun hw => hBW hb hw hbz
      have hWc := Finset.card_le_univ (insert z W)
      rw [Finset.card_insert_of_notMem hz, Fintype.card_fin] at hWc
      omega
    · have hBc : B.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hBn)
      have hDisj : Disjoint A (W.map i) := by
        apply Finset.disjoint_left.mpr
        intro a ha haw
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp haw
        exact G.irrefl (hAW ha hw)
      apply hG (A ∪ W.map i)
      refine ⟨?_, ?_⟩
      · intro x hx y hy hne
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hy with hy | hy
          · exact hc (memA hx) (memA hy) (fun h => hne (Sum.inl.inj h))
          · obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
            exact hAW hx hw
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
          rcases Finset.mem_union.mp hy with hy | hy
          · exact G.adj_symm (hAW hy hv)
          · obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hy
            exact hi v w (fun h => hne (congrArg i h))
      · rw [Finset.card_union_of_disjoint hDisj, Finset.card_map]
        omega
  · have hAc : A.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hAn)
    have hDisj : Disjoint B (W.map Fin.castSuccEmb) := by
      apply Finset.disjoint_left.mpr
      intro b hb hbw
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hbw
      exact hBW hb hw rfl
    have hBWc := Finset.card_le_univ (B ∪ W.map Fin.castSuccEmb)
    rw [Finset.card_union_of_disjoint hDisj, Finset.card_map, Fintype.card_fin] at hBWc
    omega

end OMA.RamseyGap

namespace OMA.RamseyGap

/-- Any independent set meeting both new blocks extends its old part by their matched vertex. -/
lemma enlarged_compl_cliqueFree {α : Type*} {k : ℕ} (G : SimpleGraph α)
    (i : Fin k ↪ α) {t : ℕ} (hG : Gᶜ.CliqueFree t) :
    (enlarged G i)ᶜ.CliqueFree (t + 1) := by
  classical
  intro S hS
  let A := S.toLeft
  let B := S.toRight.toLeft
  let W := S.toRight.toRight
  have hcard : A.card + B.card + W.card = t + 1 := by
    have h₁ := Finset.card_toLeft_add_card_toRight (u := S)
    have h₂ := Finset.card_toLeft_add_card_toRight (u := S.toRight)
    have h₃ := hS.card_eq
    dsimp [A, B, W]
    omega
  have memA {a : α} (ha : a ∈ A) : Sum.inl a ∈ S := by
    simpa [A] using ha
  have memB {b : Fin (k + 1)} (hb : b ∈ B) : Sum.inr (Sum.inl b) ∈ S := by
    simpa [B] using hb
  have memW {w : Fin k} (hw : w ∈ W) : Sum.inr (Sum.inr w) ∈ S := by
    simpa [W] using hw
  have hA : Gᶜ.IsClique (A : Set α) := by
    intro a ha a' ha' hne
    have h := hS.isClique (memA ha) (memA ha') (by simpa using hne)
    exact (SimpleGraph.compl_adj G a a').2 ⟨hne, h.2⟩
  have hB : B.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro b b' hb hb'
    by_contra hne
    have h := hS.isClique (memB hb) (memB hb') (by simpa using hne)
    exact h.2 hne
  have hW : W.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro w w' hw hw'
    by_contra hne
    have h := hS.isClique (memW hw) (memW hw') (by simpa using hne)
    exact h.2 hne
  have card_lt {U : Finset α} (hU : Gᶜ.IsClique (U : Set α)) : U.card < t := by
    by_contra! h
    exact hG.mono h U ⟨hU, rfl⟩
  have hAcard := card_lt hA
  have hBpos : 0 < B.card := by omega
  have hWpos : 0 < W.card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hBpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hWpos
  have hbw : b = w.castSucc := by
    have h := hS.isClique (memB hb) (memW hw) (by simp)
    exact not_not.mp h.2
  have hnotmem : i w ∉ A := by
    intro hi
    have h := hS.isClique (memA hi) (memB hb) (by simp)
    exact h.2 ⟨w, rfl, hbw⟩
  have hinsert : Gᶜ.IsClique (↑(insert (i w) A) : Set α) := by
    rw [Finset.coe_insert]
    apply hA.insert
    intro a ha hne
    have h := hS.isClique (memA ha) (memW hw) (by simp)
    exact (SimpleGraph.compl_adj G (i w) a).2 ⟨hne, fun hadj ↦ h.2 (hadj.symm)⟩
  have hlarge := card_lt hinsert
  rw [Finset.card_insert_of_notMem hnotmem] at hlarge
  omega

end OMA.RamseyGap

namespace OMA.ER812

theorem card_lt_classicalRamsey_of_cliqueFree {V : Type*} [Fintype V] {a b : ℕ}
    {G : SimpleGraph V} (hG : G.CliqueFree a) (hGc : (Gᶜ).CliqueFree b) :
    Fintype.card V < SimpleGraph.classicalRamsey a b := by
  let e := (Fintype.equivFin V).symm.toEmbedding
  let H := G.comap e
  let emb : H ↪g G := SimpleGraph.Embedding.comap e G
  let embc : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv emb
  exact lt_classicalRamsey_iff.mpr ⟨H, hG.comap emb.isContained, hGc.comap embc.isContained⟩

/-- Applying the off-diagonal increment twice gives the diagonal gap. -/
theorem diagonal_gap_of_step
    (step : ∀ k t : ℕ, 2 ≤ t →
      SimpleGraph.classicalRamsey (k + 2) t + (2 * k + 1) ≤
        SimpleGraph.classicalRamsey (k + 2) (t + 1)) :
    ∀ n : ℕ, 2 ≤ n →
      (Combinatorics.hypergraphRamsey 2 (n + 1) : ℤ) -
        (Combinatorics.hypergraphRamsey 2 n : ℤ) ≥ 4 * (n : ℤ) - 4 := by
  intro n hn
  have hn2 : n - 2 + 2 = n := by omega
  have hn1 : n - 1 + 2 = n + 1 := by omega
  have h₁ := step (n - 2) n hn
  have h₂ := step (n - 1) n hn
  rw [hn2] at h₁
  rw [hn1] at h₂
  rw [classicalRamsey_symm n (n + 1)] at h₁
  rw [hypergraphRamsey_two, hypergraphRamsey_two]
  omega

end OMA.ER812

namespace OMA.RamseyGap

open SimpleGraph

theorem classicalRamsey_step (k t : ℕ) (ht : 2 ≤ t) :
    classicalRamsey (k + 2) t + (2 * k + 1) ≤ classicalRamsey (k + 2) (t + 1) := by
  obtain ⟨r, G, i, hr, hG, hGc, hi⟩ := OMA.ER812.exists_criticalGraph k t ht
  have hrlt : r + ((k + 1) + k) < classicalRamsey (k + 2) (t + 1) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      OMA.ER812.card_lt_classicalRamsey_of_cliqueFree
        (enlarged_cliqueFree G i hi hG) (enlarged_compl_cliqueFree G i hGc)
  omega

end OMA.RamseyGap

theorem OMA.solution : type_of% @Erdos812.erdos_812.variants.lower_bound := by
  intro n hn
  have h := OMA.ER812.diagonal_gap_of_step OMA.RamseyGap.classicalRamsey_step n hn
  omega
