import FormalConjectures.Wikipedia.SumnerUniversalTournamentConjecture
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Reduction SumnerUniversalTournamentConjecture.sumner_conjecture.R1 of Sumner's universal tournament conjecture (1971).
Credit: @iskamag

Unconditionally proved in this reduction file (zero sorry, zero helper defs):
1. 2-Strong Tournament Reduction (all non-2-strong tournaments on 2n-2 vertices, and n = 2, 3)
2. Local Median Order Existence (both M2-Right and M2-Left inequalities + successor arc)
3. Online Greedy Branching Theorem with Prefix 1-Vertex Refinement
4. Bi-Arborescences and Heart h = 2 Trees (improves Ai-Lian 2026 bound 2n -> 2n-2; subsumes stars and double stars)
5. All Oriented Trees with at most 3 Internal Vertices (n - k <= 3; covers all n <= 5)

Surviving open core split cleanly into three pairwise-disjoint hypotheses:
- H1: Few-leaf / low-leaf-density trees (k <= 4 or 3k <= n, n >= 6; known: Ceroi-Havet 2004, Dross-Havet 2021)
- H2: Near-regular 2-strong tournaments (n >= 9; known: Reid-Wormald 1983)
- H3: Minimal open core (n >= 9, 2-strong non-near-regular, non-heart-2, k >= 5, n - k >= 4, n < 3k)
-/

namespace OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1

open SimpleGraph Digraph SumnerUniversalTournamentConjecture

def H1 : Prop :=
  ∀ (n : ℕ), 6 ≤ n →
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
      Fintype.card W = n → IsOrientedTree D →
      (¬ ∃ u v : W, D.Adj u v ∧ ∃ A : Finset W, u ∉ A ∧ v ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u → y ≠ v → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u → y ≠ v → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      4 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      ((Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ 4 ∨
       3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ n) →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
        Fintype.card V = 2 * n - 2 → G.IsTournament →
        (∀ S : Finset V, S.card ≤ 1 → ∀ V1 : Finset V, Disjoint S V1 → V1.Nonempty →
          (S ∪ V1) ≠ Finset.univ → ∃ u ∈ V1, ∃ v, v ∉ S ∧ v ∉ V1 ∧ G.Adj v u) →
        Embeds D G

def H2 : Prop :=
  ∀ (n : ℕ), 9 ≤ n →
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
      Fintype.card W = n → IsOrientedTree D →
      (¬ ∃ u v : W, D.Adj u v ∧ ∃ A : Finset W, u ∉ A ∧ v ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u → y ≠ v → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u → y ≠ v → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      4 < (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      n < 3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      4 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
        Fintype.card V = 2 * n - 2 → G.IsTournament →
        (∀ S : Finset V, S.card ≤ 1 → ∀ V1 : Finset V, Disjoint S V1 → V1.Nonempty →
          (S ∪ V1) ≠ Finset.univ → ∃ u ∈ V1, ∃ v, v ∉ S ∧ v ∉ V1 ∧ G.Adj v u) →
        (∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 1 ∨
          (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 2) →
        Embeds D G

def H3 : Prop :=
  ∀ (n : ℕ), 9 ≤ n →
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
      Fintype.card W = n → IsOrientedTree D →
      (¬ ∃ u v : W, D.Adj u v ∧ ∃ A : Finset W, u ∉ A ∧ v ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u → y ≠ v → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u → y ≠ v → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      4 < (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      n < 3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      4 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
        Fintype.card V = 2 * n - 2 → G.IsTournament →
        (∀ S : Finset V, S.card ≤ 1 → ∀ V1 : Finset V, Disjoint S V1 → V1.Nonempty →
          (S ∪ V1) ≠ Finset.univ → ∃ u ∈ V1, ∃ v, v ∉ S ∧ v ∉ V1 ∧ G.Adj v u) →
        (∃ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≠ n - 1 ∧
          (Finset.univ.filter (fun u : V => G.Adj v u)).card ≠ n - 2) →
        Embeds D G

section CoreToolkit

-- ============================================================================
-- MODULE 1: Forest completion, Topological cut, n=2, n=3, 2-Strong Reduction
-- ============================================================================

lemma adj_ne_of_isOrientation {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (h : D.Adj u v) : u ≠ v :=
  T.ne_of_adj (hO.1 u v h)

lemma not_adj_rev_of_isOrientation {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (h : D.Adj u v) : ¬ D.Adj v u :=
  (hO.2 u v (hO.1 u v h)).mp h

lemma adj_or_rev_of_isOrientation {W : Type*} {D : Digraph W} {T : SimpleGraph W}
    (hO : D.IsOrientation T) {u v : W} (hT : T.Adj u v) : D.Adj u v ∨ D.Adj v u := by
  by_cases h : D.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hO.2 u v hT).not.mp h))

lemma adj_or_rev_of_isTournament {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (hne : u ≠ v) : G.Adj u v ∨ G.Adj v u := by
  by_cases h : G.Adj u v
  · exact Or.inl h
  · exact Or.inr (not_not.mp ((hG.2 u v hne).not.mp h))

lemma embeds_of_le_subdigraph {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    {D1 D2 : Digraph W} {G : Digraph V} (hle : ∀ u v, D1.Adj u v → D2.Adj u v)
    (hemb : Embeds D2 G) : Embeds D1 G := by
  obtain ⟨f, hf⟩ := hemb
  exact ⟨⟨f.toFun, fun h => f.map_adj' (hle _ _ h)⟩, hf⟩

lemma isTournament_induce {V : Type*} {G : Digraph V} (hG : G.IsTournament) (S : Finset V) :
    (⟨fun u v : S => G.Adj u.1 v.1⟩ : Digraph S).IsTournament :=
  ⟨fun u => hG.1 u.1, fun u v huv => hG.2 u.1 v.1 (fun h => huv (Subtype.ext h))⟩

lemma card_filter_add_card_filter_not_eq {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2; exact hx2.2 hx1.2

lemma exists_orientedTree_of_acyclic {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (D : Digraph W) {H : SimpleGraph W} (hH : H.IsAcyclic) (hO : D.IsOrientation H) :
    ∃ D' : Digraph W, (∀ u v, D.Adj u v → D'.Adj u v) ∧ IsOrientedTree D' := by
  classical
  have htop : (⊤ : SimpleGraph W).Connected := SimpleGraph.connected_top
  obtain ⟨F, hHF, _, hFtree⟩ := htop.exists_isTree_le_of_le_of_isAcyclic le_top hH
  let e := Fintype.equivFin W
  let D' : Digraph W := ⟨fun u v =>
    if H.Adj u v then D.Adj u v
    else F.Adj u v ∧ (e u).val < (e v).val⟩
  refine ⟨D', ?_, F, hFtree, ?_, ?_⟩
  · intro u v huv
    have hHuv : H.Adj u v := hO.1 u v huv
    simp [D', hHuv, huv]
  · intro u v huv
    dsimp [D'] at huv
    split_ifs at huv with hHuv
    · exact hHF hHuv
    · exact huv.1
  · intro u v hFuv
    dsimp [D']
    by_cases hHuv : H.Adj u v
    · have hHvu : H.Adj v u := hHuv.symm
      simp only [hHuv, hHvu, ↓reduceIte]
      exact hO.2 u v hHuv
    · have hHvu : ¬ H.Adj v u := fun h => hHuv h.symm
      have hFvu : F.Adj v u := hFuv.symm
      have hne : u ≠ v := F.ne_of_adj hFuv
      have hne' : (e u).val ≠ (e v).val := fun h => hne (e.injective (Fin.ext h))
      simp only [hHuv, hHvu, ↓reduceIte, hFuv, hFvu, true_and]
      omega

lemma isTree_induce_erase {W : Type*} [Fintype W] [DecidableEq W] {T : SimpleGraph W}
    [DecidableRel T.Adj] (hT : T.IsTree) {v : W} (hdeg : T.degree v = 1) :
    (T.induce ({v}ᶜ : Set W)).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg, hT.isAcyclic.induce _⟩

lemma exists_topological_cut {n : ℕ} :
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W),
      Fintype.card W = n → IsOrientedTree D →
      ∀ a : ℕ, 1 ≤ a → a < n →
        ∃ A : Finset W, A.card = a ∧ ∀ u ∈ A, ∀ v ∉ A, ¬ D.Adj v u := by
  induction n with
  | zero =>
    intro W _ _ D _ _ a ha hlt; omega
  | succ m ih =>
    intro W _ _ D hcard hD a ha hlt
    classical
    obtain ⟨T, hT, hO⟩ := hD
    have hnt : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hdeg⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨u0, hTvu0, hu0_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
    let W' := {w : W // w ∈ ({v}ᶜ : Set W)}
    have hcard' : Fintype.card W' = m := by
      have h1 : Fintype.card W' = Fintype.card W - 1 := by
        simp [W', Fintype.card_subtype_compl]
      omega
    let T' : SimpleGraph W' := T.induce ({v}ᶜ : Set W)
    let D' : Digraph W' := ⟨fun x y => D.Adj x.1 y.1⟩
    have hT' : T'.IsTree := isTree_induce_erase hT hdeg
    have hO' : D'.IsOrientation T' := ⟨fun x y h => hO.1 x.1 y.1 h, fun x y h => hO.2 x.1 y.1 h⟩
    have hD' : IsOrientedTree D' := ⟨T', hT', hO'⟩
    rcases adj_or_rev_of_isOrientation hO hTvu0 with hsrc | hsnk
    · have hnoin : ∀ w : W, ¬ D.Adj w v := by
        intro w hwv
        have hTw : T.Adj v w := (hO.1 w v hwv).symm
        have heq : w = u0 := hu0_uniq w hTw
        subst heq
        exact not_adj_rev_of_isOrientation hO hsrc hwv
      by_cases ha1 : a = 1
      · refine ⟨{v}, by simp [ha1], ?_⟩
        intro x hx y hy hyx
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact hnoin y hyx
      · obtain ⟨A', hA'card, hA'cut⟩ := ih D' hcard' hD' (a - 1) (by omega) (by omega)
        let A : Finset W := insert v (A'.map ⟨Subtype.val, Subtype.val_injective⟩)
        have hv_notin : v ∉ A'.map ⟨Subtype.val, Subtype.val_injective⟩ := by
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
          intro x _ hx
          exact x.2 (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)
        refine ⟨A, ?_, ?_⟩
        · simp [A, Finset.card_insert_of_notMem hv_notin, hA'card]; omega
        · intro x hx y hy hyx
          simp only [A, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk] at hx hy
          push Not at hy
          rcases hx with rfl | ⟨x', hx', rfl⟩
          · exact hnoin y hyx
          · have hyne : y ≠ v := hy.1
            let y' : W' := ⟨y, hyne⟩
            have hy'notin : y' ∉ A' := fun h => hy.2 y' h rfl
            exact hA'cut x' hx' y' hy'notin hyx
    · have hnoout : ∀ w : W, ¬ D.Adj v w := by
        intro w hvw
        have hTw : T.Adj v w := hO.1 v w hvw
        have heq : w = u0 := hu0_uniq w hTw
        subst heq
        exact not_adj_rev_of_isOrientation hO hsnk hvw
      by_cases ham : a = m
      · let A : Finset W := Finset.univ.erase v
        refine ⟨A, ?_, ?_⟩
        · simp [A, Finset.card_erase_of_mem, hcard, ham]
        · intro x hx y hy hyx
          have hyv : y = v := by
            by_contra hne
            exact hy (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ y⟩)
          subst hyv
          exact hnoout x hyx
      · obtain ⟨A', hA'card, hA'cut⟩ := ih D' hcard' hD' a ha (by omega)
        let A : Finset W := A'.map ⟨Subtype.val, Subtype.val_injective⟩
        refine ⟨A, by simp [A, hA'card], ?_⟩
        intro x hx y hy hyx
        simp only [A, Finset.mem_map, Function.Embedding.coeFn_mk] at hx hy
        push Not at hy
        obtain ⟨x', hx', rfl⟩ := hx
        by_cases hyv : y = v
        · subst hyv; exact hnoout x'.1 hyx
        · let y' : W' := ⟨y, hyv⟩
          have hy'notin : y' ∉ A' := fun h => hy y' h rfl
          exact hA'cut x' hx' y' hy'notin hyx

lemma sumner_n_eq_2 {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = 2) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2) (hG : G.IsTournament) : Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  have hWu : (Finset.univ : Finset W).card = 2 := hW
  obtain ⟨w1, w2, hneW, hW_eq⟩ := Finset.card_eq_two.mp hWu
  have hW_all : ∀ z : W, z = w1 ∨ z = w2 := fun z => by
    have : z ∈ ({w1, w2} : Finset W) := hW_eq ▸ Finset.mem_univ z
    simpa using this
  have hVu : (Finset.univ : Finset V).card = 2 := hV
  obtain ⟨v1, v2, hneV, _⟩ := Finset.card_eq_two.mp hVu
  have hT12 : T.Adj w1 w2 := by
    obtain ⟨p⟩ := hT.connected w1 w2
    cases p with
    | nil => exact absurd rfl hneW
    | @cons _ z _ hadj _ =>
      have hz : z = w2 := by
        rcases hW_all z with rfl | rfl
        · exact absurd rfl (T.ne_of_adj hadj)
        · rfl
      subst hz; exact hadj
  have hG12 : G.Adj v1 v2 ∨ G.Adj v2 v1 := adj_or_rev_of_isTournament hG hneV
  have mk_emb : ∀ (a b : W) (x y : V), a ≠ b → (∀ z, z = a ∨ z = b) → D.Adj a b →
      x ≠ y → G.Adj x y → Embeds D G := by
    intro a b x y hab hall hadjD hxy hadjG
    refine ⟨⟨fun z => if z = a then x else y, ?_⟩, ?_⟩
    · intro p q hpq
      have hpq_ne : p ≠ q := adj_ne_of_isOrientation hO hpq
      rcases hall p with rfl | rfl <;> rcases hall q with rfl | rfl
      · exact absurd rfl hpq_ne
      · simp [hab.symm, hadjG]
      · exact absurd hpq (not_adj_rev_of_isOrientation hO hadjD)
      · exact absurd rfl hpq_ne
    · intro p q h
      rcases hall p with rfl | rfl <;> rcases hall q with rfl | rfl
      · rfl
      · simp [hab.symm] at h; exact absurd h hxy
      · simp [hab.symm] at h; exact absurd h.symm hxy
      · rfl
  rcases adj_or_rev_of_isOrientation hO hT12 with hD12 | hD21
  · rcases hG12 with hG12 | hG21
    · exact mk_emb w1 w2 v1 v2 hneW hW_all hD12 hneV hG12
    · exact mk_emb w1 w2 v2 v1 hneW hW_all hD12 hneV.symm hG21
  · rcases hG12 with hG12 | hG21
    · exact mk_emb w2 w1 v1 v2 hneW.symm (fun z => (hW_all z).symm) hD21 hneV hG12
    · exact mk_emb w2 w1 v2 v1 hneW.symm (fun z => (hW_all z).symm) hD21 hneV.symm hG21

lemma embeds_induced_forest_of_ih {n : ℕ}
    (ih : ∀ m, 2 ≤ m → m < n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = m → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * m - 2 → G.IsTournament → Embeds D G)
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} (hD : IsOrientedTree D)
    {A : Finset W} (hA_pos : 1 ≤ A.card) (hA_lt : A.card < n)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} (hG : G.IsTournament)
    {U : Finset V} (hU_pos : 1 ≤ U.card) (hU_ge : 2 * A.card - 2 ≤ U.card) :
    Embeds (⟨fun x y : A => D.Adj x.1 y.1⟩ : Digraph A)
           (⟨fun x y : U => G.Adj x.1 y.1⟩ : Digraph U) := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  by_cases hA1 : A.card = 1
  · obtain ⟨u0, hu0⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
    refine ⟨⟨fun _ => ⟨u0, hu0⟩, ?_⟩, ?_⟩
    · intro x y hxy
      have hne : x.1 ≠ y.1 := adj_ne_of_isOrientation hO hxy
      obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hA1
      have hx : x.1 = w0 := by simpa [hw0] using x.2
      have hy : y.1 = w0 := by simpa [hw0] using y.2
      exact absurd (hx.trans hy.symm) hne
    · intro x y _
      obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hA1
      exact Subtype.ext (by
        have hx : x.1 = w0 := by simpa [hw0] using x.2
        have hy : y.1 = w0 := by simpa [hw0] using y.2
        exact hx.trans hy.symm)
  · have hA2 : 2 ≤ A.card := by omega
    have hAne : Nonempty A := (Finset.card_pos.mp (by omega)).to_subtype
    let DA : Digraph A := ⟨fun x y => D.Adj x.1 y.1⟩
    let TA : SimpleGraph A := T.induce (A : Set W)
    have hTA : TA.IsAcyclic := hT.isAcyclic.induce _
    have hOA : DA.IsOrientation TA := ⟨fun x y h => hO.1 x.1 y.1 h, fun x y h => hO.2 x.1 y.1 h⟩
    obtain ⟨DA', hle, hDA'_tree⟩ := exists_orientedTree_of_acyclic DA hTA hOA
    obtain ⟨U', hU'sub, hU'card⟩ := Finset.exists_subset_card_eq hU_ge
    let GU' : Digraph U' := ⟨fun x y => G.Adj x.1 y.1⟩
    have hGU' : GU'.IsTournament := isTournament_induce hG U'
    have hcardA : Fintype.card A = A.card := Fintype.card_coe A
    have hcardU' : Fintype.card U' = 2 * A.card - 2 := by rw [Fintype.card_coe, hU'card]
    have hemb' : Embeds DA' GU' := ih A.card hA2 hA_lt DA' hcardA hDA'_tree GU' hcardU' hGU'
    have hembA : Embeds DA GU' := embeds_of_le_subdigraph hle hemb'
    obtain ⟨f, hf⟩ := hembA
    refine ⟨⟨fun x => ⟨(f x).1, hU'sub (f x).2⟩, fun h => f.map_adj' h⟩, ?_⟩
    intro x y hxy
    have hval : (f x).1 = (f y).1 := congrArg (fun z : U => z.1) hxy
    exact hf (Subtype.ext hval)

lemma twoStrong_reduction {n : ℕ} (hn : 3 ≤ n)
    (ih : ∀ m, 2 ≤ m → m < n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = m → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * m - 2 → G.IsTournament → Embeds D G)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hnot2 : ∃ S : Finset V, S.card ≤ 1 ∧ ∃ V1 : Finset V, Disjoint S V1 ∧ V1.Nonempty ∧
      (S ∪ V1) ≠ Finset.univ ∧ ∀ u ∈ V1, ∀ v, v ∉ S → v ∉ V1 → ¬ G.Adj v u) :
    Embeds D G := by
  classical
  obtain ⟨S, hScard, V1, hdisjSV1, hV1ne, hne_univ, hno_back⟩ := hnot2
  let V2 : Finset V := (S ∪ V1)ᶜ
  have hdisj12 : Disjoint V1 V2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact Finset.mem_compl.mp hx2 (Finset.mem_union_right S hx1)
  have hV2ne : V2.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hemp
    exact hne_univ hemp
  have hV1pos : 1 ≤ V1.card := Finset.one_le_card.mpr hV1ne
  have hV2pos : 1 ≤ V2.card := Finset.one_le_card.mpr hV2ne
  have hsum : V1.card + V2.card + S.card = 2 * n - 2 := by
    have h1 : (S ∪ V1).card + V2.card = Fintype.card V := Finset.card_add_card_compl (S ∪ V1)
    have h2 : (S ∪ V1).card = S.card + V1.card := Finset.card_union_of_disjoint hdisjSV1
    omega
  have hV12_ge : 2 * n - 3 ≤ V1.card + V2.card := by omega
  let a : ℕ := V1.card / 2 + 1
  have ha_ge : 1 ≤ a := by omega
  have ha_lt : a < n := by omega
  obtain ⟨A, hAcard, hAcut⟩ := exists_topological_cut D hW hD a ha_ge ha_lt
  let B : Finset W := Aᶜ
  have hBcard : B.card = n - a := by
    have h1 : A.card + B.card = Fintype.card W := Finset.card_add_card_compl A
    rw [hW, hAcard] at h1
    omega
  have hBpos : 1 ≤ B.card := by omega
  have hBlt : B.card < n := by omega
  have hV1_ge : 2 * A.card - 2 ≤ V1.card := by omega
  have hV2_ge : 2 * B.card - 2 ≤ V2.card := by omega
  obtain ⟨f1, hf1⟩ := embeds_induced_forest_of_ih ih hD (by omega) (by omega) hG hV1pos hV1_ge
  obtain ⟨f2, hf2⟩ := embeds_induced_forest_of_ih ih hD hBpos hBlt hG hV2pos hV2_ge
  refine ⟨⟨fun w => if h : w ∈ A then (f1 ⟨w, h⟩).1 else (f2 ⟨w, Finset.mem_compl.mpr h⟩).1, ?_⟩, ?_⟩
  · intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · simp only [hx, hy, ↓reduceDIte]
      exact f1.map_adj' hxy
    · simp only [hx, hy, ↓reduceDIte]
      have hu1 : (f1 ⟨x, hx⟩).1 ∈ V1 := (f1 ⟨x, hx⟩).2
      have hv2 : (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 ∈ V2 := (f2 ⟨y, Finset.mem_compl.mpr hy⟩).2
      have hv_notS : (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 ∉ S := fun h =>
        Finset.mem_compl.mp hv2 (Finset.mem_union_left V1 h)
      have hv_notV1 : (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 ∉ V1 := fun h =>
        Finset.mem_compl.mp hv2 (Finset.mem_union_right S h)
      have hnb : ¬ G.Adj (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 (f1 ⟨x, hx⟩).1 :=
        hno_back _ hu1 _ hv_notS hv_notV1
      have hne : (f1 ⟨x, hx⟩).1 ≠ (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 := fun heq =>
        hv_notV1 (heq ▸ hu1)
      exact (hG.2 (f1 ⟨x, hx⟩).1 (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 hne).mpr hnb
    · exact absurd hxy (hAcut y hy x hx)
    · simp only [hx, hy, ↓reduceDIte]
      exact f2.map_adj' hxy
  · intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · simp only [hx, hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (hf1 (Subtype.ext hxy))
    · simp only [hx, hy, ↓reduceDIte] at hxy
      have hu1 : (f1 ⟨x, hx⟩).1 ∈ V1 := (f1 ⟨x, hx⟩).2
      have hv2 : (f2 ⟨y, Finset.mem_compl.mpr hy⟩).1 ∈ V2 := (f2 ⟨y, Finset.mem_compl.mpr hy⟩).2
      exact absurd (hxy ▸ hu1) (Finset.disjoint_right.mp hdisj12 hv2)
    · simp only [hx, hy, ↓reduceDIte] at hxy
      have hu1 : (f1 ⟨y, hy⟩).1 ∈ V1 := (f1 ⟨y, hy⟩).2
      have hv2 : (f2 ⟨x, Finset.mem_compl.mpr hx⟩).1 ∈ V2 := (f2 ⟨x, Finset.mem_compl.mpr hx⟩).2
      exact absurd (hxy.symm ▸ hu1) (Finset.disjoint_right.mp hdisj12 hv2)
    · simp only [hx, hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (hf2 (Subtype.ext hxy))

lemma not_twoStrong_of_card_four {V : Type} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 4) (hG : G.IsTournament) :
    ∃ S : Finset V, S.card ≤ 1 ∧ ∃ V1 : Finset V, Disjoint S V1 ∧ V1.Nonempty ∧
      (S ∪ V1) ≠ Finset.univ ∧ ∀ u ∈ V1, ∀ v, v ∉ S → v ∉ V1 → ¬ G.Adj v u := by
  classical
  obtain ⟨v0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  let inS := Finset.univ.filter (fun u : V => G.Adj u v0)
  let outS := Finset.univ.filter (fun u : V => G.Adj v0 u)
  have hpart : inS.card + outS.card = 3 := by
    have hdisj : Disjoint inS outS := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [inS, outS, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
      have hne : u ≠ v0 := fun h => hG.1 v0 (h ▸ hu1)
      exact (hG.2 u v0 hne).mp hu1 hu2
    have hunion : inS ∪ outS = Finset.univ.erase v0 := by
      ext u
      simp only [inS, outS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · rintro (h | h) <;> intro heq <;> subst heq <;> exact hG.1 u h
      · intro hne
        rcases adj_or_rev_of_isTournament hG hne with h | h
        · exact Or.inl h
        · exact Or.inr h
    have hcard_u := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_univ, hV] at hcard_u
    omega
  by_cases hin : inS.card ≤ 1
  · refine ⟨inS, hin, {v0}, ?_, Finset.singleton_nonempty v0, ?_, ?_⟩
    · rw [Finset.disjoint_singleton_right]
      simp [inS, hG.1 v0]
    · intro h
      have hc := congrArg Finset.card h
      rw [Finset.card_union_of_disjoint (by rw [Finset.disjoint_singleton_right]; simp [inS, hG.1 v0]),
        Finset.card_singleton, Finset.card_univ, hV] at hc
      omega
    · intro u hu v hvS _ hv_adj
      simp only [Finset.mem_singleton] at hu
      subst hu
      exact hvS (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv_adj⟩)
  · have hout : outS.card ≤ 1 := by omega
    let V1 : Finset V := (insert v0 outS)ᶜ
    have hv0_notin_out : v0 ∉ outS := by simp [outS, hG.1 v0]
    have hcard_ins : (insert v0 outS).card = outS.card + 1 :=
      Finset.card_insert_of_notMem hv0_notin_out
    have hV1pos : 0 < V1.card := by
      have h1 : (insert v0 outS).card + V1.card = Fintype.card V :=
        Finset.card_add_card_compl (insert v0 outS)
      rw [hcard_ins, hV] at h1
      omega
    refine ⟨outS, hout, V1, ?_, Finset.card_pos.mp hV1pos, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact Finset.mem_compl.mp hx2 (Finset.mem_insert_of_mem hx1)
    · intro h
      have hv0_mem : v0 ∈ outS ∪ V1 := h ▸ Finset.mem_univ v0
      rcases Finset.mem_union.mp hv0_mem with h1 | h2
      · exact hv0_notin_out h1
      · exact Finset.mem_compl.mp h2 (Finset.mem_insert_self v0 outS)
    · intro u hu v hvS hvV1 hv_adj
      have hvv0 : v = v0 := by
        by_contra hne
        exact hvV1 (Finset.mem_compl.mpr (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hne, hvS⟩))
      subst hvv0
      have hu_out : u ∈ outS := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hv_adj⟩
      exact Finset.mem_compl.mp hu (Finset.mem_insert_of_mem hu_out)

-- ============================================================================
-- MODULE 2: Existence of Median Order & Half-Dominance (M2)
-- ============================================================================

lemma median_right_of_max {V : Type} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hG : G.IsTournament)
    (σ : Fin (Fintype.card V) ≃ V)
    (hmax : ∀ σ' : Fin (Fintype.card V) ≃ V,
      ((Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
        (fun p => p.1 < p.2 ∧ G.Adj (σ' p.1) (σ' p.2))).card ≤
      ((Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V))).filter
        (fun p => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2))).card)
    (i j : Fin (Fintype.card V)) (hij : i < j) :
    j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card := by
  classical
  let m := Fintype.card V
  have hij_val : i.val < j.val := hij
  have hj_lt : j.val < m := j.isLt
  let toF : Fin m → Fin m := fun k =>
    if k.val < i.val then k
    else if hkj : k.val < j.val then ⟨k.val + 1, by omega⟩
    else if k.val = j.val then i
    else k
  let invF : Fin m → Fin m := fun k =>
    if k.val < i.val then k
    else if k.val = i.val then j
    else if k.val ≤ j.val then ⟨k.val - 1, by omega⟩
    else k
  have htoF_val : ∀ k : Fin m, (toF k).val =
      if k.val < i.val then k.val
      else if k.val < j.val then k.val + 1
      else if k.val = j.val then i.val
      else k.val := fun k => by dsimp [toF]; split_ifs <;> rfl
  have hinvF_val : ∀ k : Fin m, (invF k).val =
      if k.val < i.val then k.val
      else if k.val = i.val then j.val
      else if k.val ≤ j.val then k.val - 1
      else k.val := fun k => by dsimp [invF]; split_ifs <;> rfl
  have hleft : Function.LeftInverse invF toF := by
    intro k; apply Fin.ext
    rw [hinvF_val, htoF_val]
    split_ifs <;> omega
  have hright : Function.RightInverse invF toF := by
    intro k; apply Fin.ext
    rw [htoF_val, hinvF_val]
    split_ifs <;> omega
  let τ : Fin m ≃ Fin m := ⟨toF, invF, hleft, hright⟩
  let σ' : Fin m ≃ V := τ.trans σ
  have hle := hmax σ'
  let A := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2))
  let A' := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ G.Adj (σ' p.1) (σ' p.2))
  let F_i := (Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))
  let B_i := (Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j ∧ G.Adj (σ k) (σ i))
  have hFB_sum : F_i.card + B_i.card = j.val - i.val := by
    have hdisj : Disjoint F_i B_i := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [F_i, B_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
      have hne_ik : σ i ≠ σ k := fun h => absurd (σ.injective h) (ne_of_lt hk1.1)
      exact (hG.2 _ _ hne_ik).mp hk1.2.2 hk2.2.2
    have hunion : F_i ∪ B_i = (Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j) := by
      ext k
      simp only [F_i, B_i, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have hne_ik : σ i ≠ σ k := fun h => absurd (σ.injective h) (ne_of_lt h1)
        rcases adj_or_rev_of_isTournament hG hne_ik with h | h
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨h1, h2, h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hbij : ((Finset.univ : Finset (Fin m)).filter (fun k => i < k ∧ k ≤ j)).card =
        (Finset.Ioc i.val j.val).card := by
      refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_Ioc.mpr ⟨hk.1, hk.2⟩
      · intro a _ b _ h; exact Fin.ext h
      · intro n hn
        have ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
        refine ⟨⟨n, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h1, h2⟩
    rw [hbij, Nat.card_Ioc]
  let A_flip := A.filter (fun p => p.1 = i ∧ p.2 ≤ j)
  let A_keep := A.filter (fun p => ¬ (p.1 = i ∧ p.2 ≤ j))
  let A'_flip := A'.filter (fun p => p.2 = j ∧ i ≤ p.1)
  let A'_keep := A'.filter (fun p => ¬ (p.2 = j ∧ i ≤ p.1))
  have hA_split : A.card = A_flip.card + A_keep.card :=
    (card_filter_add_card_filter_not_eq A _).symm
  have hA'_split : A'.card = A'_flip.card + A'_keep.card :=
    (card_filter_add_card_filter_not_eq A' _).symm
  have hflip1 : A_flip.card = F_i.card := by
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [A_flip, A, F_i, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hlt, hadj⟩, rfl, hle_j⟩
      exact ⟨hlt, hle_j, hadj⟩
    · intro p hp q hq h
      simp only [A_flip, Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.1.trans hq.2.1.symm) h
    · intro k hk
      simp only [F_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact ⟨(i, k), by simp [A_flip, A, hk.1, hk.2.1, hk.2.2], rfl⟩
  have hτj : τ j = i := by
    apply Fin.ext; change (toF j).val = i.val; rw [htoF_val]; split_ifs <;> omega
  have hflip2 : A'_flip.card = B_i.card := by
    refine Finset.card_bij (fun p _ => τ p.1) ?_ ?_ ?_
    · intro p hp
      simp only [A'_flip, A', B_i, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hlt, hadj⟩, h2j, hi1⟩
      have h1_lt : p.1.val < j.val := h2j ▸ hlt
      have h1_ge : i.val ≤ p.1.val := hi1
      have hv : (τ p.1).val = (toF p.1).val := rfl
      rw [htoF_val] at hv
      have hτ1 : i < τ p.1 ∧ τ p.1 ≤ j := by
        constructor <;> (simp only [Fin.lt_def, Fin.le_def]; split_ifs at hv <;> omega)
      refine ⟨hτ1.1, hτ1.2, ?_⟩
      simpa [σ', Equiv.trans_apply, h2j, hτj] using hadj
    · intro p hp q hq h
      simp only [A'_flip, Finset.mem_filter] at hp hq
      exact Prod.ext (τ.injective h) (hp.2.1.trans hq.2.1.symm)
    · intro k hk
      simp only [B_i, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨(τ.symm k, j), ?_, τ.apply_symm_apply k⟩
      have h1 : i.val < k.val := hk.1
      have h2 : k.val ≤ j.val := hk.2.1
      have hv : (τ.symm k).val = (invF k).val := rfl
      rw [hinvF_val] at hv
      have hsk1 : i ≤ τ.symm k := by
        change i.val ≤ (τ.symm k).val; split_ifs at hv <;> omega
      have hsk2 : τ.symm k < j := by
        change (τ.symm k).val < j.val; split_ifs at hv <;> omega
      simp only [A'_flip, A', Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨hsk2, ?_⟩, hsk1⟩
      simpa [σ', Equiv.trans_apply, hτj] using hk.2.2
  have hkeep : A_keep.card = A'_keep.card := by
    refine Finset.card_bij (fun p _ => (τ.symm p.1, τ.symm p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [A_keep, A, A'_keep, A', Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hlt, hadj⟩, hnot⟩
      have hlt_val : p.1.val < p.2.val := hlt
      have hnot' : ¬ (p.1.val = i.val ∧ p.2.val ≤ j.val) := fun ⟨h1, h2⟩ =>
        hnot ⟨Fin.ext h1, h2⟩
      have hv1 : (τ.symm p.1).val = (invF p.1).val := rfl
      have hv2 : (τ.symm p.2).val = (invF p.2).val := rfl
      rw [hinvF_val] at hv1 hv2
      have hlt' : τ.symm p.1 < τ.symm p.2 := by
        change (τ.symm p.1).val < (τ.symm p.2).val
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      have hnot2 : ¬ (τ.symm p.2 = j ∧ i ≤ τ.symm p.1) := by
        rintro ⟨h1, h2⟩
        have h1v : (τ.symm p.2).val = j.val := congrArg Fin.val h1
        have h2v : i.val ≤ (τ.symm p.1).val := h2
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      exact ⟨⟨hlt', by simpa [σ', Equiv.trans_apply] using hadj⟩, hnot2⟩
    · intro p _ q _ h
      exact Prod.ext (τ.symm.injective (congrArg Prod.fst h))
        (τ.symm.injective (congrArg Prod.snd h))
    · intro q hq
      simp only [A'_keep, A', Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rcases hq with ⟨⟨hlt, hadj⟩, hnot⟩
      refine ⟨(τ q.1, τ q.2), ?_, by simp⟩
      simp only [A_keep, A, Finset.mem_filter, Finset.mem_univ, true_and]
      have hlt_val : q.1.val < q.2.val := hlt
      have hnot' : ¬ (q.2.val = j.val ∧ i.val ≤ q.1.val) := fun ⟨h1, h2⟩ =>
        hnot ⟨Fin.ext h1, h2⟩
      have hv1 : (τ q.1).val = (toF q.1).val := rfl
      have hv2 : (τ q.2).val = (toF q.2).val := rfl
      rw [htoF_val] at hv1 hv2
      have hlt1 : τ q.1 < τ q.2 := by
        change (τ q.1).val < (τ q.2).val
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      have hnot1 : ¬ (τ q.1 = i ∧ τ q.2 ≤ j) := by
        rintro ⟨h1, h2⟩
        have h1v : (τ q.1).val = i.val := congrArg Fin.val h1
        have h2v : (τ q.2).val ≤ j.val := h2
        split_ifs at hv1 <;> split_ifs at hv2 <;> omega
      exact ⟨⟨hlt1, by simpa [σ', Equiv.trans_apply] using hadj⟩, hnot1⟩
  change A'.card ≤ A.card at hle
  change j.val - i.val ≤ 2 * F_i.card
  omega

lemma exists_median_order {V : Type} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hG : G.IsTournament) :
    ∃ σ : Fin (Fintype.card V) ≃ V,
      (∀ i j : Fin (Fintype.card V), i < j →
        j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card) ∧
      (∀ i j : Fin (Fintype.card V), i < j →
        j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) := by
  classical
  let m := Fintype.card V
  let fwd : (Fin m ≃ V) → ℕ := fun σ =>
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2))).card
  have hne : (Finset.univ : Finset (Fin m ≃ V)).Nonempty :=
    ⟨(Fintype.equivFin V).symm, Finset.mem_univ _⟩
  obtain ⟨σ, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m ≃ V)) fwd hne
  refine ⟨σ, fun i j hij => median_right_of_max G hG σ (fun σ' => hmax σ' (Finset.mem_univ _)) i j hij, ?_⟩
  let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
  have hGrev : Grev.IsTournament := ⟨fun v => hG.1 v, fun u v huv => hG.2 v u huv.symm⟩
  let revFin : Fin m ≃ Fin m := Fin.revPerm
  let σrev : Fin m ≃ V := revFin.trans σ
  have hfwd_eq : ∀ τ : Fin m ≃ V,
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ Grev.Adj (τ p.1) (τ p.2))).card =
      fwd (revFin.trans τ) := by
    intro τ
    refine Finset.card_bij (fun p _ => (revFin p.2, revFin p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨Fin.rev_lt_rev.mpr hp.1, ?_⟩
      simpa [revFin, Grev, Equiv.trans_apply] using hp.2
    · intro p _ q _ h
      exact Prod.ext (revFin.injective (congrArg Prod.snd h))
        (revFin.injective (congrArg Prod.fst h))
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(revFin q.2, revFin q.1), ?_, by simp [revFin]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Fin.rev_lt_rev.mpr hq.1, ?_⟩
      simpa [revFin, Grev, Equiv.trans_apply] using hq.2
  have hmax_rev : ∀ τ : Fin m ≃ V,
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ Grev.Adj (τ p.1) (τ p.2))).card ≤
      ((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun p => p.1 < p.2 ∧ Grev.Adj (σrev p.1) (σrev p.2))).card := by
    intro τ
    rw [hfwd_eq τ, hfwd_eq σrev]
    have hinv : revFin.trans σrev = σ := by
      ext k; simp [σrev, revFin, Equiv.trans_apply]
    rw [hinv]
    exact hmax (revFin.trans τ) (Finset.mem_univ _)
  intro i j hij
  have hij_rev : revFin j < revFin i := Fin.rev_lt_rev.mpr hij
  have hstep := median_right_of_max Grev hGrev σrev hmax_rev (revFin j) (revFin i) hij_rev
  have hdiff : (revFin i).val - (revFin j).val = j.val - i.val := by
    simp only [revFin, Fin.revPerm_apply, Fin.val_rev]
    have := i.isLt; have := j.isLt; have : i.val < j.val := hij; omega
  have hcard_eq : (Finset.univ.filter (fun k : Fin m =>
      revFin j < k ∧ k ≤ revFin i ∧ Grev.Adj (σrev (revFin j)) (σrev k))).card =
    (Finset.univ.filter (fun k : Fin m => i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card := by
    refine Finset.card_bij (fun k _ => revFin k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      refine ⟨Fin.rev_le_rev.mp (by simpa [revFin] using hk.2.1),
        Fin.rev_lt_rev.mp (by simpa [revFin] using hk.1), ?_⟩
      simpa [σrev, revFin, Grev, Equiv.trans_apply] using hk.2.2
    · intro a _ b _ h; exact revFin.injective h
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨revFin k, ?_, by simp [revFin]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Fin.rev_lt_rev.mpr hk.2.1, Fin.rev_le_rev.mpr hk.1, ?_⟩
      simpa [σrev, revFin, Grev, Equiv.trans_apply] using hk.2.2
  rw [hdiff, hcard_eq] at hstep
  exact hstep

lemma median_adj_succ {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (i : Fin (Fintype.card V)) (hi : i.val + 1 < Fintype.card V) :
    G.Adj (σ i) (σ ⟨i.val + 1, hi⟩) := by
  let j : Fin (Fintype.card V) := ⟨i.val + 1, hi⟩
  have hij : i < j := by change i.val < i.val + 1; omega
  have h := hR i j hij
  have hjv : j.val = i.val + 1 := rfl
  have hpos : 0 < (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card := by
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hkj : k = ⟨i.val + 1, hi⟩ := Fin.ext (by
    have h1 : i.val < k.val := hk.1
    have h2 : k.val ≤ j.val := hk.2.1
    omega)
  simpa [hkj] using hk.2.2

-- ============================================================================
-- MODULE 3: Online Greedy Branching Theorem + Prefix Refinement (Theorem 4.1)
-- ============================================================================

lemma branching_ancestors_comparable {W : Type*} {D : Digraph W}
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    {x1 x2 w : W} (h1 : Relation.ReflTransGen D.Adj x1 w)
    (h2 : Relation.ReflTransGen D.Adj x2 w) :
    Relation.ReflTransGen D.Adj x1 x2 ∨ Relation.ReflTransGen D.Adj x2 x1 := by
  induction h1 with
  | refl => exact Or.inr h2
  | @tail b c h1b hbc ih =>
    cases h2 with
    | refl => exact Or.inl (Relation.ReflTransGen.tail h1b hbc)
    | tail h2b' hb'c =>
      rename_i b'
      have hbb' : b = b' := hInDeg c b b' hbc hb'c
      subst hbb'
      exact ih h2b'

lemma greedy_out_branching_embeds
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hRank : ∃ rank : W → ℕ, ∀ u v, D.Adj u v → rank u < rank v)
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    {p : ℕ} (roots : Fin p → W) (hroots_inj : Function.Injective roots)
    (hroots_iff : ∀ w : W, (∀ u, ¬ D.Adj u w) ↔ ∃ j : Fin p, roots j = w)
    (hp_le : p ≤ Fintype.card V)
    (q : ℕ) (hq_le : q ≤ p)
    (hpref : ∀ j : Fin p, j.val < q → ∀ u, ¬ D.Adj (roots j) u)
    (hm : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      Fintype.card V + 1 + q) :
    ∃ f : D →g G, Function.Injective f ∧ ∀ j : Fin p, f (roots j) = σ ⟨j.val, by omega⟩ := by
  classical
  let m := Fintype.card V
  obtain ⟨rank, hrank⟩ := hRank
  -- Step 1: Build greedy assignment g : Fin t → Option W for p ≤ t ≤ m by induction on d = t - p
  have hbuild : ∀ d : ℕ, (hd : p + d ≤ m) →
      ∃ g : Fin (p + d) → Option W,
        (∀ j : Fin p, g ⟨j.val, by omega⟩ = some (roots j)) ∧
        (∀ i1 i2 : Fin (p + d), ∀ x : W, g i1 = some x → g i2 = some x → i1 = i2) ∧
        (∀ i : Fin (p + d), ∀ x : W, g i = some x →
          (i.val < p) ∨
          (∃ s : Fin (p + d), s < i ∧ ∃ u : W, g s = some u ∧ D.Adj u x ∧
            G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨i.val, by omega⟩))) ∧
        (∀ i : Fin (p + d), p ≤ i.val → ∀ x : W, g i = some x →
          ∀ s : Fin (p + d), s < i → ∀ u : W, g s = some u →
          (∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + d), k < i → g k ≠ some c) →
          G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨i.val, by omega⟩) →
          ∃ s' : Fin (p + d), s' ≤ s ∧ ∃ u' : W, g s' = some u' ∧ D.Adj u' x) ∧
        (∀ i : Fin (p + d), p ≤ i.val → g i = none →
          ∀ s : Fin (p + d), s < i → ∀ u : W, g s = some u →
          (∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + d), k < i → g k ≠ some c) →
          ¬ G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨i.val, by omega⟩)) := by
    intro d
    induction d with
    | zero =>
      intro hd
      refine ⟨fun j => some (roots ⟨j.val, by omega⟩), ?_, ?_, ?_, ?_, ?_⟩
      · intro j; rfl
      · intro i1 i2 x h1 h2
        have heq : roots ⟨i1.val, by omega⟩ = roots ⟨i2.val, by omega⟩ :=
          Option.some.inj (h1.trans h2.symm)
        exact Fin.ext (congrArg Fin.val (hroots_inj heq))
      · intro i _ _; exact Or.inl (by omega)
      · intro i hi; omega
      · intro i hi; omega
    | succ d ih =>
      intro hd
      obtain ⟨g, h1, h2, h3, h4, h5⟩ := ih (by omega)
      let t := p + d
      let cand : Finset (Fin t) := Finset.univ.filter (fun s =>
        ∃ u : W, g s = some u ∧ (∃ c : W, D.Adj u c ∧ ∀ k : Fin t, g k ≠ some c) ∧
          G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨t, by omega⟩))
      by_cases hcand : cand.Nonempty
      · let s0 := cand.min' hcand
        have hs0_mem : s0 ∈ cand := Finset.min'_mem cand hcand
        have hs0_spec := (Finset.mem_filter.mp hs0_mem).2
        obtain ⟨u0, hgu0, ⟨c0, hD0, hc0_new⟩, hG0⟩ := hs0_spec
        let g' : Fin (p + (d + 1)) → Option W := fun i =>
          if hi : i.val < t then g ⟨i.val, hi⟩ else some c0
        refine ⟨g', ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          have hlt : j.val < t := by omega
          simp only [g', hlt, ↓reduceDIte]
          exact h1 j
        · intro i1 i2 x hx1 hx2
          by_cases hi1 : i1.val < t <;> by_cases hi2 : i2.val < t
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            exact Fin.ext (congrArg (fun z : Fin t => z.val) (h2 ⟨i1.val, hi1⟩ ⟨i2.val, hi2⟩ x hx1 hx2))
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            have : x = c0 := (Option.some.inj hx2).symm
            subst this; exact absurd hx1 (hc0_new ⟨i1.val, hi1⟩)
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            have : x = c0 := (Option.some.inj hx1).symm
            subst this; exact absurd hx2 (hc0_new ⟨i2.val, hi2⟩)
          · exact Fin.ext (by omega)
        · intro i x hx
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            rcases h3 ⟨i.val, hi⟩ x hx with hlt | ⟨s, hsi, u, hgs, hDu, hGu⟩
            · exact Or.inl hlt
            · refine Or.inr ⟨⟨s.val, by omega⟩, hsi, u, ?_, hDu, hGu⟩
              dsimp only [g']; rw [dif_pos s.isLt]; exact hgs
          · simp only [g', hi, ↓reduceDIte] at hx
            have hxc : x = c0 := (Option.some.inj hx).symm
            subst hxc
            have hit : i.val = t := by omega
            refine Or.inr ⟨⟨s0.val, by omega⟩, by change s0.val < i.val; omega, u0, ?_, hD0, ?_⟩
            · dsimp only [g']; rw [dif_pos s0.isLt]; exact hgu0
            · convert hG0 using 2; exact Fin.ext hit
        · intro i hip x hx s hsi u hgs hact hGs
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              have h := hc ⟨k.val, by omega⟩ hk
              simpa [g', k.isLt] using h
            obtain ⟨s', hs'le, u', hgu', hDu'⟩ :=
              h4 ⟨i.val, hi⟩ hip x hx ⟨s.val, hs_lt⟩ hsi u hgs hact' hGs
            refine ⟨⟨s'.val, by omega⟩, hs'le, u', ?_, hDu'⟩
            dsimp only [g']; rw [dif_pos s'.isLt]; exact hgu'
          · simp only [g', hi, ↓reduceDIte] at hx
            have hxc : x = c0 := (Option.some.inj hx).symm
            subst hxc
            have hit : i.val = t := by omega
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hs_cand : (⟨s.val, hs_lt⟩ : Fin t) ∈ cand := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hgs, ?_, ?_⟩
              · obtain ⟨c, hDc, hc⟩ := hact
                refine ⟨c, hDc, fun k => ?_⟩
                have hk : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by
                  change k.val < i.val; omega
                simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
              · convert hGs using 2; exact Fin.ext hit.symm
            have hle : s0 ≤ ⟨s.val, hs_lt⟩ := Finset.min'_le cand _ hs_cand
            refine ⟨⟨s0.val, by omega⟩, hle, u0, ?_, hD0⟩
            dsimp only [g']; rw [dif_pos s0.isLt]; exact hgu0
        · intro i hip hgi s hsi u hgs hact
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hgi
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
            exact h5 ⟨i.val, hi⟩ hip hgi ⟨s.val, hs_lt⟩ hsi u hgs hact'
          · simp only [g', hi, ↓reduceDIte] at hgi
            exact absurd hgi (Option.some_ne_none c0)
      · let g' : Fin (p + (d + 1)) → Option W := fun i =>
          if hi : i.val < t then g ⟨i.val, hi⟩ else none
        refine ⟨g', ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          have hlt : j.val < t := by omega
          simp only [g', hlt, ↓reduceDIte]; exact h1 j
        · intro i1 i2 x hx1 hx2
          by_cases hi1 : i1.val < t <;> by_cases hi2 : i2.val < t
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            exact Fin.ext (congrArg (fun z : Fin t => z.val) (h2 ⟨i1.val, hi1⟩ ⟨i2.val, hi2⟩ x hx1 hx2))
          · simp only [g', hi2, ↓reduceDIte] at hx2; cases hx2
          · simp only [g', hi1, ↓reduceDIte] at hx1; cases hx1
          · simp only [g', hi1, ↓reduceDIte] at hx1; cases hx1
        · intro i x hx
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            rcases h3 ⟨i.val, hi⟩ x hx with hlt | ⟨s, hsi, u, hgs, hDu, hGu⟩
            · exact Or.inl hlt
            · refine Or.inr ⟨⟨s.val, by omega⟩, hsi, u, ?_, hDu, hGu⟩
              dsimp only [g']; rw [dif_pos s.isLt]; exact hgs
          · simp only [g', hi, ↓reduceDIte] at hx; cases hx
        · intro i hip x hx s hsi u hgs hact hGs
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
            obtain ⟨s', hs'le, u', hgu', hDu'⟩ :=
              h4 ⟨i.val, hi⟩ hip x hx ⟨s.val, hs_lt⟩ hsi u hgs hact' hGs
            refine ⟨⟨s'.val, by omega⟩, hs'le, u', ?_, hDu'⟩
            dsimp only [g']; rw [dif_pos s'.isLt]; exact hgu'
          · simp only [g', hi, ↓reduceDIte] at hx; cases hx
        · intro i hip hgi s hsi u hgs hact hGs
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hgi
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
            exact h5 ⟨i.val, hi⟩ hip hgi ⟨s.val, hs_lt⟩ hsi u hgs hact' hGs
          · have hit : i.val = t := by omega
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hs_cand : (⟨s.val, hs_lt⟩ : Fin t) ∈ cand := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hgs, ?_, ?_⟩
              · obtain ⟨c, hDc, hc⟩ := hact
                refine ⟨c, hDc, fun k => ?_⟩
                have hk : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by
                  change k.val < i.val; omega
                simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
              · convert hGs using 2; exact Fin.ext hit.symm
            exact hcand ⟨_, hs_cand⟩
  -- Instantiate at d = m - p
  obtain ⟨g0, hg1, hg2, hg3, hg4, hg5⟩ := hbuild (m - p) (by omega)
  have hpm : p + (m - p) = m := by omega
  let eFin : Fin m ≃ Fin (p + (m - p)) := finCongr hpm.symm
  let g : Fin m → Option W := fun i => g0 (eFin i)
  have hroots_g : ∀ j : Fin p, g ⟨j.val, by omega⟩ = some (roots j) := by
    intro j; simpa [g, eFin] using hg1 j
  have hinj_g : ∀ i1 i2 : Fin m, ∀ x : W, g i1 = some x → g i2 = some x → i1 = i2 := by
    intro i1 i2 x hx1 hx2
    exact eFin.injective (hg2 (eFin i1) (eFin i2) x hx1 hx2)
  have hpar_g : ∀ i : Fin m, ∀ x : W, g i = some x →
      (i.val < p) ∨ (∃ s : Fin m, s < i ∧ ∃ u : W, g s = some u ∧ D.Adj u x ∧ G.Adj (σ s) (σ i)) := by
    intro i x hx
    rcases hg3 (eFin i) x hx with hlt | ⟨s, hsi, u, hgs, hDu, hGu⟩
    · exact Or.inl (by simpa [eFin] using hlt)
    · refine Or.inr ⟨eFin.symm s, ?_, u, ?_, hDu, ?_⟩
      · change (eFin.symm s).val < i.val
        have : s.val < (eFin i).val := hsi
        simpa [eFin] using this
      · simpa [g] using hgs
      · convert hGu using 2 <;> exact Fin.ext (by simp [eFin])
  have hleft_g : ∀ i : Fin m, p ≤ i.val → ∀ x : W, g i = some x →
      ∀ s : Fin m, s < i → ∀ u : W, g s = some u →
      (∃ c : W, D.Adj u c ∧ ∀ k : Fin m, k < i → g k ≠ some c) →
      G.Adj (σ s) (σ i) →
      ∃ s' : Fin m, s' ≤ s ∧ ∃ u' : W, g s' = some u' ∧ D.Adj u' x := by
    intro i hip x hx s hsi u hgs ⟨c, hDc, hc⟩ hGs
    have hact : ∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + (m - p)), k < eFin i → g0 k ≠ some c := by
      refine ⟨c, hDc, fun k hk => ?_⟩
      have hk' : eFin.symm k < i := by
        change (eFin.symm k).val < i.val
        have : k.val < (eFin i).val := hk
        simpa [eFin] using this
      simpa [g] using hc (eFin.symm k) hk'
    have hGs' : G.Adj (σ ⟨(eFin s).val, by omega⟩) (σ ⟨(eFin i).val, by omega⟩) := by
      convert hGs using 2 <;> exact Fin.ext (by simp [eFin])
    have hsi' : eFin s < eFin i := by
      change (eFin s).val < (eFin i).val
      have : s.val < i.val := hsi
      simpa [eFin] using this
    obtain ⟨s', hs'le, u', hgu', hDu'⟩ :=
      hg4 (eFin i) (by simpa [eFin] using hip) x hx (eFin s) hsi' u hgs hact hGs'
    have hs'le' : eFin.symm s' ≤ s := by
      change (eFin.symm s').val ≤ s.val
      have : s'.val ≤ (eFin s).val := hs'le
      simpa [eFin] using this
    exact ⟨eFin.symm s', hs'le', u', by simpa [g] using hgu', hDu'⟩
  have hfail_g : ∀ i : Fin m, p ≤ i.val → g i = none →
      ∀ s : Fin m, s < i → ∀ u : W, g s = some u →
      (∃ c : W, D.Adj u c ∧ ∀ k : Fin m, k < i → g k ≠ some c) →
      ¬ G.Adj (σ s) (σ i) := by
    intro i hip hgi s hsi u hgs ⟨c, hDc, hc⟩ hGs
    have hact : ∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + (m - p)), k < eFin i → g0 k ≠ some c := by
      refine ⟨c, hDc, fun k hk => ?_⟩
      have hk' : eFin.symm k < i := by
        change (eFin.symm k).val < i.val
        have : k.val < (eFin i).val := hk
        simpa [eFin] using this
      simpa [g] using hc (eFin.symm k) hk'
    have hGs' : G.Adj (σ ⟨(eFin s).val, by omega⟩) (σ ⟨(eFin i).val, by omega⟩) := by
      convert hGs using 2 <;> exact Fin.ext (by simp [eFin])
    have hsi' : eFin s < eFin i := by
      change (eFin s).val < (eFin i).val
      have : s.val < i.val := hsi
      simpa [eFin] using this
    exact hg5 (eFin i) (by simpa [eFin] using hip) hgi (eFin s) hsi' u hgs hact hGs'
  -- Step 2: Prove every w : W is embedded in g (by contradiction!)
  let emb : Finset W := Finset.univ.filter (fun w => ∃ i : Fin m, g i = some w)
  let fail : Finset (Fin m) := Finset.univ.filter (fun i => g i = none)
  have hsum_ef : emb.card + fail.card = m := by
    have h1 : (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card + fail.card = m := by
      have hsplit := card_filter_add_card_filter_not_eq (Finset.univ : Finset (Fin m)) (fun i => g i = none)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      have hcomm : (Finset.univ.filter (fun i : Fin m => ¬ g i = none)) =
          Finset.univ.filter (fun i : Fin m => g i ≠ none) := rfl
      rw [hcomm] at hsplit
      change (Finset.univ.filter (fun i : Fin m => g i = none)).card +
        (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card = m at hsplit
      change (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card +
        (Finset.univ.filter (fun i : Fin m => g i = none)).card = m
      omega
    have hbij : (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card = emb.card := by
      refine Finset.card_bij (fun i hi => (g i).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hi).2)) ?_ ?_ ?_
      · intro i hi
        simp only [emb, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, (Option.some_get _).symm⟩
      · intro i1 hi1 i2 hi2 h
        have h1' : g i1 = some ((g i1).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hi1).2)) :=
          (Option.some_get _).symm
        have h2' : g i2 = some ((g i2).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hi2).2)) :=
          (Option.some_get _).symm
        exact hinj_g i1 i2 _ h1' (h2'.trans (congrArg some h.symm))
      · intro w hw
        simp only [emb, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨i, hgi⟩ := hw
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simp [hgi]⟩, ?_⟩
        simp [hgi]
    omega
  have hall_emb : ∀ w : W, ∃ i : Fin m, g i = some w := by
    by_contra hnot_all
    push Not at hnot_all
    have hunemb_ne : (Finset.univ.filter (fun w : W => ∀ i : Fin m, g i ≠ some w)).Nonempty := by
      obtain ⟨w0, hw0⟩ := hnot_all
      exact ⟨w0, Finset.mem_filter.mpr ⟨Finset.mem_univ w0, hw0⟩⟩
    -- Unembedded leaf z_max maximizing rank among unembedded vertices
    obtain ⟨z_max, hz_mem, hz_max⟩ := Finset.exists_max_image _ rank hunemb_ne
    have hz_unemb : ∀ i : Fin m, g i ≠ some z_max := (Finset.mem_filter.mp hz_mem).2
    have hz_leaf : ∀ c : W, ¬ D.Adj z_max c := by
      intro c hDc
      have hrc : rank z_max < rank c := hrank z_max c hDc
      have hc_emb : ∃ i : Fin m, g i = some c := by
        by_contra hc_not
        push Not at hc_not
        have hc_mem : c ∈ Finset.univ.filter (fun w : W => ∀ i : Fin m, g i ≠ some w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc_not⟩
        have := hz_max c hc_mem
        omega
      obtain ⟨ic, hic⟩ := hc_emb
      rcases hpar_g ic c hic with hlt | ⟨s, _, u, hgs, hDu, _⟩
      · have hrc' : g ⟨ic.val, by omega⟩ = some (roots ⟨ic.val, hlt⟩) := hroots_g ⟨ic.val, hlt⟩
        have hceq : c = roots ⟨ic.val, hlt⟩ := Option.some.inj (hic.symm.trans hrc')
        have hnoroot : ∀ u, ¬ D.Adj u c := (hroots_iff c).mpr ⟨⟨ic.val, hlt⟩, hceq.symm⟩
        exact hnoroot z_max hDc
      · have hu_eq : u = z_max := hInDeg c u z_max hDu hDc
        subst hu_eq
        exact hz_unemb s hgs
    -- For every j ∈ fail, Q_j is nonempty
    let Q : Fin m → Finset (Fin m) := fun j =>
      Finset.univ.filter (fun s : Fin m => s < j ∧ ∃ u : W, g s = some u ∧
        ∃ c : W, D.Adj u c ∧ ∀ k : Fin m, k < j → g k ≠ some c)
    have hQ_ne : ∀ j ∈ fail, (Q j).Nonempty := by
      intro j hj
      have hj_none : g j = none := (Finset.mem_filter.mp hj).2
      have hjp : p ≤ j.val := by
        by_contra hlt
        have h1 := hroots_g ⟨j.val, by omega⟩
        have h2 : (⟨j.val, by omega⟩ : Fin m) = j := Fin.ext rfl
        rw [h2, hj_none] at h1
        cases h1
      have hU_ne : (Finset.univ.filter (fun w : W => ∀ k : Fin m, k < j → g k ≠ some w)).Nonempty :=
        ⟨z_max, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k _ => hz_unemb k⟩⟩
      obtain ⟨z_min, hzmin_mem, hzmin_le⟩ := Finset.exists_min_image _ rank hU_ne
      have hzmin_un : ∀ k : Fin m, k < j → g k ≠ some z_min := (Finset.mem_filter.mp hzmin_mem).2
      have hhas_par : ∃ u : W, D.Adj u z_min := by
        by_contra hno
        push Not at hno
        obtain ⟨jr, hjr⟩ := (hroots_iff z_min).mp hno
        have h1 := hroots_g jr
        have hlt_j : (⟨jr.val, by omega⟩ : Fin m) < j := by
          change jr.val < j.val; omega
        exact hzmin_un ⟨jr.val, by omega⟩ hlt_j (by simpa [hjr] using h1)
      obtain ⟨u, hDu⟩ := hhas_par
      have hu_lt : rank u < rank z_min := hrank u z_min hDu
      have hu_emb : ∃ s : Fin m, s < j ∧ g s = some u := by
        by_contra hno
        push Not at hno
        have hu_mem : u ∈ Finset.univ.filter (fun w : W => ∀ k : Fin m, k < j → g k ≠ some w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno⟩
        have := hzmin_le u hu_mem
        omega
      obtain ⟨s, hsj, hgs⟩ := hu_emb
      exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsj, u, hgs, z_min, hDu, hzmin_un⟩⟩
    -- Define a j = max of Q j for j ∈ fail
    let a : Fin m → Fin m := fun j =>
      if hj : j ∈ fail then (Q j).max' (hQ_ne j hj) else j
    have ha_mem : ∀ j ∈ fail, a j ∈ Q j := fun j hj => by
      simp only [a, hj, ↓reduceDIte]; exact Finset.max'_mem _ _
    have ha_lt : ∀ j ∈ fail, a j < j := fun j hj => (Finset.mem_filter.mp (ha_mem j hj)).2.1
    have ha_max : ∀ j ∈ fail, ∀ s ∈ Q j, s ≤ a j := fun j hj s hs => by
      simp only [a, hj, ↓reduceDIte]; exact Finset.le_max' _ s hs
    -- Key Property 1: Laminarity
    have hlam : ∀ j1 ∈ fail, ∀ j2 ∈ fail, j1 < j2 → ¬ (a j1 < a j2 ∧ a j2 < j1) := by
      intro j1 hj1 j2 hj2 hj12 ⟨h1, h2⟩
      have ha2_Q2 := (Finset.mem_filter.mp (ha_mem j2 hj2)).2
      obtain ⟨_, u, hgu, c, hDc, hc_un⟩ := ha2_Q2
      have ha2_Q1 : a j2 ∈ Q j1 := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h2, u, hgu, c, hDc, fun k hk => hc_un k (lt_trans hk hj12)⟩
      have hle := ha_max j1 hj1 (a j2) ha2_Q1
      exact absurd hle (not_le_of_gt h1)
    -- Key Property 2: Maximal failed intervals
    let MaxFail : Finset (Fin m) := fail.filter (fun j =>
      ∀ j' ∈ fail, a j' ≤ a j → j ≤ j' → j' = j)
    have hcover : ∀ j ∈ fail, ∃ b ∈ MaxFail, a b ≤ a j ∧ j ≤ b := by
      intro j hj
      let S := fail.filter (fun j' => a j' ≤ a j ∧ j ≤ j')
      have hSne : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl, le_rfl⟩⟩
      obtain ⟨b, hbS, hb_max⟩ := Finset.exists_max_image S (fun x => x.val - (a x).val) hSne
      have hb_spec := Finset.mem_filter.mp hbS
      refine ⟨b, Finset.mem_filter.mpr ⟨hb_spec.1, ?_⟩, hb_spec.2.1, hb_spec.2.2⟩
      intro j' hj' ha' hbj'
      have hj'S : j' ∈ S := Finset.mem_filter.mpr
        ⟨hj', le_trans ha' hb_spec.2.1, le_trans hb_spec.2.2 hbj'⟩
      have hle := hb_max j' hj'S
      have ha_lt_b := ha_lt b hb_spec.1
      have ha_lt_j' := ha_lt j' hj'
      have hb_le : b.val ≤ j'.val := hbj'
      have ha_le : (a j').val ≤ (a b).val := ha'
      exact Fin.ext (by omega)
    have hdisj_max : ∀ b1 ∈ MaxFail, ∀ b2 ∈ MaxFail, b1 ≠ b2 →
        Disjoint (Finset.univ.filter (fun k : Fin m => a b1 < k ∧ k ≤ b1))
                 (Finset.univ.filter (fun k : Fin m => a b2 < k ∧ k ≤ b2)) := by
      intro b1 hb1 b2 hb2 hne
      have hb1_f := (Finset.mem_filter.mp hb1).1
      have hb1_m := (Finset.mem_filter.mp hb1).2
      have hb2_f := (Finset.mem_filter.mp hb2).1
      have hb2_m := (Finset.mem_filter.mp hb2).2
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · -- b1 < b2: since k ≤ b1 and a b2 < k, we have a b2 < b1.
        -- By laminarity, ¬(a b1 < a b2 ∧ a b2 < b1), so a b2 ≤ a b1!
        have ha2_lt_b1 : a b2 < b1 := lt_of_lt_of_le hk2.1 hk1.2
        have ha2_le_a1 : a b2 ≤ a b1 := by
          by_contra hgt
          push Not at hgt
          exact hlam b1 hb1_f b2 hb2_f hlt ⟨hgt, ha2_lt_b1⟩
        exact hne (hb1_m b2 hb2_f ha2_le_a1 (le_of_lt hlt)).symm
      · have ha1_lt_b2 : a b1 < b2 := lt_of_lt_of_le hk1.1 hk2.2
        have ha1_le_a2 : a b1 ≤ a b2 := by
          by_contra hgt
          push Not at hgt
          exact hlam b2 hb2_f b1 hb1_f hlt ⟨hgt, ha1_lt_b2⟩
        exact hne (hb2_m b1 hb1_f ha1_le_a2 (le_of_lt hlt))
    -- Key Property 3: Inside each maximal interval I_b = (a b, b], |fail ∩ I_b| ≤ |leaves embedded in I_b|
    let leaves : Finset W := Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)
    let leafPos : Finset (Fin m) := Finset.univ.filter (fun k : Fin m => ∃ w ∈ leaves, g k = some w)
    have hper_int : ∀ b ∈ MaxFail,
        (fail.filter (fun j => a b < j ∧ j ≤ b)).card ≤
        (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card := by
      intro b hb
      have hb_f := (Finset.mem_filter.mp hb).1
      have hab_lt : a b < b := ha_lt b hb_f
      have hab_Q := (Finset.mem_filter.mp (ha_mem b hb_f)).2
      obtain ⟨_, u_ab, hg_ab, c_ab, hDc_ab, hc_ab_un⟩ := hab_Q
      let S_b := Finset.univ.filter (fun i : Fin m => a b < i ∧ i ≤ b ∧ G.Adj (σ (a b)) (σ i))
      -- Every j ∈ fail ∩ (a b, b] satisfies ¬ G.Adj (σ (a b)) (σ j)
      have hfail_not_S : ∀ j ∈ fail.filter (fun j => a b < j ∧ j ≤ b), j ∉ S_b := by
        intro j hj hS
        have hj_f := (Finset.mem_filter.mp hj).1
        have hj_int := (Finset.mem_filter.mp hj).2
        have hj_none : g j = none := (Finset.mem_filter.mp hj_f).2
        have hjp : p ≤ j.val := by
          by_contra hlt
          have h1 := hroots_g ⟨j.val, by omega⟩
          have h2 : (⟨j.val, by omega⟩ : Fin m) = j := Fin.ext rfl
          rw [h2, hj_none] at h1; cases h1
        have hGadj := (Finset.mem_filter.mp hS).2.2.2
        have hact : ∃ c : W, D.Adj u_ab c ∧ ∀ k : Fin m, k < j → g k ≠ some c :=
          ⟨c_ab, hDc_ab, fun k hk => hc_ab_un k (lt_of_lt_of_le hk hj_int.2)⟩
        exact hfail_g j hjp hj_none (a b) hj_int.1 u_ab hg_ab hact hGadj
      -- Hence (fail ∩ (a b, b]).card ≤ S_b.card by M2-Right!
      have hfail_le_S : (fail.filter (fun j => a b < j ∧ j ≤ b)).card ≤ S_b.card := by
        have hR_b := hR (a b) b hab_lt
        let Int_b := Finset.univ.filter (fun i : Fin m => a b < i ∧ i ≤ b)
        have hInt_card : Int_b.card = b.val - (a b).val := by
          have hbij : Int_b.card = (Finset.Ioc (a b).val b.val).card := by
            refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
            · intro k hk
              simp only [Int_b, Finset.mem_filter, Finset.mem_univ, true_and] at hk
              exact Finset.mem_Ioc.mpr ⟨hk.1, hk.2⟩
            · intro x _ y _ h; exact Fin.ext h
            · intro n hn
              have ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
              refine ⟨⟨n, by have := b.isLt; omega⟩, ?_, rfl⟩
              simp only [Int_b, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩
          rw [hbij, Nat.card_Ioc]
        have hsub : fail.filter (fun j => a b < j ∧ j ≤ b) ⊆ Int_b \ S_b := by
          intro j hj
          have hj_int := (Finset.mem_filter.mp hj).2
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_int⟩, hfail_not_S j hj⟩
        have hS_sub : S_b ⊆ Int_b := by
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h.1, h.2.1⟩
        have hcard_le := Finset.card_le_card hsub
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub] at hcard_le
        change b.val - (a b).val ≤ 2 * S_b.card at hR_b
        omega
      -- Now inject S_b into leafPos ∩ (a b, b]!
      -- First: for every i ∈ S_b, g i = some x_i (since i ∉ fail)
      have hS_some : ∀ i ∈ S_b, ∃ x : W, g i = some x := by
        intro i hi
        cases hgi : g i with
        | none =>
          have hi_f : i ∈ fail := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgi⟩
          have hi_int := (Finset.mem_filter.mp hi).2
          exact absurd hi (hfail_not_S i (Finset.mem_filter.mpr ⟨hi_f, hi_int.1, hi_int.2.1⟩))
        | some x => exact ⟨x, rfl⟩
      -- Helper: any descendant of a vertex embedded at i ∈ (a b, b) is embedded in [i, b)!
      have hdesc_emb : ∀ (i : Fin m) (x : W), a b < i → i < b → g i = some x →
          ∀ w : W, Relation.ReflTransGen D.Adj x w →
          ∃ k : Fin m, i ≤ k ∧ k < b ∧ g k = some w := by
        intro i x hi1 hi2 hgi w hreach
        induction hreach with
        | refl => exact ⟨i, le_rfl, hi2, hgi⟩
        | @tail y z hxy hyz ih =>
          obtain ⟨ky, hiky, hkyb, hgky⟩ := ih
          -- z MUST be embedded at some kz < b, else ky ∈ Q b contradicting ky > a b!
          have hz_emb_lt : ∃ kz : Fin m, kz < b ∧ g kz = some z := by
            by_contra hno
            push Not at hno
            have hky_Q : ky ∈ Q b := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hkyb, y, hgky, z, hyz, hno⟩
            have hle := ha_max b hb_f ky hky_Q
            have hlt : a b < ky := lt_of_lt_of_le hi1 hiky
            exact absurd hle (not_le_of_gt hlt)
          obtain ⟨kz, hkzb, hgkz⟩ := hz_emb_lt
          -- By hpar_g + hInDeg, ky < kz!
          have hky_lt_kz : ky < kz := by
            rcases hpar_g kz z hgkz with hltp | ⟨s, hskz, u', hgs', hDu', _⟩
            · have h1 := hroots_g ⟨kz.val, hltp⟩
              have hzeq : z = roots ⟨kz.val, hltp⟩ := Option.some.inj (hgkz.symm.trans h1)
              have hnoroot := (hroots_iff z).mpr ⟨⟨kz.val, hltp⟩, hzeq.symm⟩
              exact absurd hyz (hnoroot y)
            · have hu'eq : u' = y := hInDeg z u' y hDu' hyz
              subst u'
              have hseq : s = ky := hinj_g s ky y hgs' hgky
              exact hseq ▸ hskz
          exact ⟨kz, le_of_lt (lt_of_le_of_lt hiky hky_lt_kz), hkzb, hgkz⟩
      -- For every i ∈ S_b, pick a leaf descendant w_i embedded at k_i ∈ (a b, b]!
      have hex_leaf : ∀ i ∈ S_b, ∃ k ∈ leafPos.filter (fun k => a b < k ∧ k ≤ b),
          ∃ x w : W, g i = some x ∧ g k = some w ∧ Relation.ReflTransGen D.Adj x w := by
        intro i hi
        obtain ⟨x, hgi⟩ := hS_some i hi
        have hi_int := (Finset.mem_filter.mp hi).2
        have hib : i < b := lt_of_le_of_ne hi_int.2.1 (by
          intro heq; subst heq
          have hbn : g i = none := (Finset.mem_filter.mp hb_f).2
          rw [hbn] at hgi; cases hgi)
        let Desc := Finset.univ.filter (fun w : W => Relation.ReflTransGen D.Adj x w)
        have hDne : Desc.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
        obtain ⟨w, hwD, hw_max⟩ := Finset.exists_max_image Desc rank hDne
        have hreach : Relation.ReflTransGen D.Adj x w := (Finset.mem_filter.mp hwD).2
        have hw_leaf : w ∈ leaves := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hDc => ?_⟩
          have hcD : c ∈ Desc := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hreach hDc⟩
          have hle := hw_max c hcD
          have hlt := hrank w c hDc
          omega
        obtain ⟨k, hik, hkb, hgk⟩ := hdesc_emb i x hi_int.1 hib hgi w hreach
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ k, w, hw_leaf, hgk⟩,
          lt_of_lt_of_le hi_int.1 hik, le_of_lt hkb⟩, x, w, hgi, hgk, hreach⟩
      -- Choose function φ : S_b → Fin m via Classical.choose and prove injective!
      choose φ hφ_mem hφ_desc using hex_leaf
      have hS_le_leaf : S_b.card ≤ (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card := by
        refine Finset.card_le_card_of_injOn (fun i => if hi : i ∈ S_b then φ i hi else i) ?_ ?_
        · intro i hi
          have hi' : i ∈ S_b := Finset.mem_coe.mp hi
          dsimp only; rw [dif_pos hi']; exact Finset.mem_coe.mpr (hφ_mem i hi')
        · intro i1 hi1 i2 hi2 hEq
          have hi1' : i1 ∈ S_b := Finset.mem_coe.mp hi1
          have hi2' : i2 ∈ S_b := Finset.mem_coe.mp hi2
          dsimp only at hEq
          rw [dif_pos hi1', dif_pos hi2'] at hEq
          obtain ⟨x1, w1, hgi1, hgk1, hreach1⟩ := hφ_desc i1 hi1'
          obtain ⟨x2, w2, hgi2, hgk2, hreach2⟩ := hφ_desc i2 hi2'
          have hw_eq : w1 = w2 := Option.some.inj (hgk1.symm.trans (hEq ▸ hgk2))
          subst hw_eq
          -- Helper: no distinct i1, i2 ∈ S_b can have x2 a proper descendant of x1!
          have hno_prop : ∀ j1 ∈ S_b, ∀ j2 ∈ S_b, ∀ y1 y2 : W,
              g j1 = some y1 → g j2 = some y2 →
              Relation.ReflTransGen D.Adj y1 y2 → j1 = j2 := by
            intro j1 hj1 j2 hj2 y1 y2 hgj1 hgj2 hr12
            by_cases heqy : y1 = y2
            · subst heqy; exact hinj_g j1 j2 y1 hgj1 hgj2
            · -- y2 is a proper descendant of y1, so ∃ y, ReflTransGen y1 y ∧ D.Adj y y2
              cases hr12 with
              | refl => exact absurd rfl heqy
              | tail h1y hy2 =>
                rename_i y
                have hj1_int := (Finset.mem_filter.mp hj1).2
                have hj1b : j1 < b := lt_of_le_of_ne hj1_int.2.1 (by
                  intro heq; subst heq; rw [(Finset.mem_filter.mp hb_f).2] at hgj1
                  cases hgj1)
                obtain ⟨ky, hj1ky, _, hgky⟩ := hdesc_emb j1 y1 hj1_int.1 hj1b hgj1 y h1y
                have hj2_int := (Finset.mem_filter.mp hj2).2
                have hj2p : p ≤ j2.val := by
                  by_contra hltp
                  have h1 := hroots_g ⟨j2.val, by omega⟩
                  have hy2eq : y2 = roots ⟨j2.val, by omega⟩ := Option.some.inj (hgj2.symm.trans h1)
                  have hnoroot := (hroots_iff y2).mpr ⟨⟨j2.val, by omega⟩, hy2eq.symm⟩
                  exact hnoroot y hy2
                have hact_j2 : ∃ c : W, D.Adj u_ab c ∧ ∀ k : Fin m, k < j2 → g k ≠ some c :=
                  ⟨c_ab, hDc_ab, fun k hk => hc_ab_un k (lt_of_lt_of_le hk hj2_int.2.1)⟩
                obtain ⟨s', hs'le, u', hgs', hDu'⟩ :=
                  hleft_g j2 hj2p y2 hgj2 (a b) hj2_int.1 u_ab hg_ab hact_j2 hj2_int.2.2
                have hu'eq : u' = y := hInDeg y2 u' y hDu' hy2
                subst u'
                have hseq : s' = ky := hinj_g s' ky y hgs' hgky
                have hky_gt : a b < ky := lt_of_lt_of_le hj1_int.1 hj1ky
                exact absurd (hseq ▸ hs'le) (not_le_of_gt hky_gt)
          rcases branching_ancestors_comparable hInDeg hreach1 hreach2 with h12 | h21
          · exact hno_prop i1 hi1 i2 hi2 x1 x2 hgi1 hgi2 h12
          · exact (hno_prop i2 hi2 i1 hi1 x2 x1 hgi2 hgi1 h21).symm
      exact le_trans hfail_le_S hS_le_leaf
    -- Key Property 4: Sum over MaxFail, exclude prefix q and unembedded leaf z_max!
    have hfail_le_sum : fail.card ≤ ∑ b ∈ MaxFail, (fail.filter (fun j => a b < j ∧ j ≤ b)).card := by
      have hsub : fail ⊆ MaxFail.biUnion (fun b => fail.filter (fun j => a b < j ∧ j ≤ b)) := by
        intro j hj
        obtain ⟨b, hb, hab, hjb⟩ := hcover j hj
        refine Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨hj, lt_of_le_of_lt hab (ha_lt j hj), hjb⟩⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hsum_le_leaves : ∑ b ∈ MaxFail, (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card ≤
        (leafPos.filter (fun k => q ≤ k.val)).card := by
      rw [← Finset.card_biUnion]
      · refine Finset.card_le_card ?_
        intro k hk
        obtain ⟨b, hb, hkb⟩ := Finset.mem_biUnion.mp hk
        have hkl := (Finset.mem_filter.mp hkb).1
        have hkint := (Finset.mem_filter.mp hkb).2
        -- a b ≥ q because a b ∈ Q b has an unembedded child!
        have hab_ge_q : q ≤ (a b).val := by
          by_contra hltq
          have hb_f := (Finset.mem_filter.mp hb).1
          obtain ⟨_, u, hgu, c, hDc, _⟩ := (Finset.mem_filter.mp (ha_mem b hb_f)).2
          have h1 := hroots_g ⟨(a b).val, by omega⟩
          have hueq : u = roots ⟨(a b).val, by omega⟩ := Option.some.inj (hgu.symm.trans h1)
          subst hueq
          exact hpref ⟨(a b).val, by omega⟩ (by simpa using hltq) c hDc
        refine Finset.mem_filter.mpr ⟨hkl, ?_⟩
        have : (a b).val < k.val := hkint.1
        omega
      · intro b1 hb1 b2 hb2 hne
        exact (hdisj_max b1 hb1 b2 hb2 hne).mono
          (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2⟩)
          (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2⟩)
    -- Bound (leafPos.filter (q ≤ k.val)).card ≤ leaves.card - 1 - q!
    have hleaf_bound : (leafPos.filter (fun k => q ≤ k.val)).card + q + 1 ≤ leaves.card := by
      -- Map each k ∈ leafPos to its vertex in leaves, plus the q prefix roots, plus z_max!
      let L_used : Finset W := (leafPos.filter (fun k => q ≤ k.val)).image
        (fun k => if h : ∃ w ∈ leaves, g k = some w then Classical.choose h else z_max)
      let L_pref : Finset W := (Finset.univ : Finset (Fin q)).image (fun j => roots ⟨j.val, by omega⟩)
      have hcard_used : L_used.card = (leafPos.filter (fun k => q ≤ k.val)).card := by
        refine Finset.card_image_of_injOn ?_
        intro k1 hk1 k2 hk2 hEq
        have h1 : ∃ w ∈ leaves, g k1 = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk1).1).2
        have h2 : ∃ w ∈ leaves, g k2 = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk2).1).2
        simp only [h1, h2, ↓reduceDIte] at hEq
        have hg1' := (Classical.choose_spec h1).2
        have hg2' := (Classical.choose_spec h2).2
        exact hinj_g k1 k2 _ hg1' (hEq ▸ hg2')
      have hcard_pref : L_pref.card = q := by
        rw [Finset.card_image_of_injective]
        · exact Fintype.card_fin q
        · intro j1 j2 h
          exact Fin.ext (congrArg (fun z : Fin p => z.val) (hroots_inj h))
      have hdisj_up : Disjoint L_used L_pref := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw1
        obtain ⟨j, _, hjw⟩ := Finset.mem_image.mp hw2
        have h1 : ∃ w ∈ leaves, g k = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
        simp only [h1, ↓reduceDIte] at hjw
        have hgk := (Classical.choose_spec h1).2
        have hgj := hroots_g ⟨j.val, by omega⟩
        have hkj := hinj_g k ⟨j.val, by omega⟩ _ hgk (hjw.symm ▸ hgj)
        have hkq : q ≤ k.val := (Finset.mem_filter.mp hk).2
        have hjlt : j.val < q := j.isLt
        have : k.val = j.val := congrArg Fin.val hkj
        omega
      have hz_notin : z_max ∉ L_used ∪ L_pref := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · obtain ⟨k, hk, hkw⟩ := Finset.mem_image.mp h1
          have hex : ∃ w ∈ leaves, g k = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
          simp only [hex, ↓reduceDIte] at hkw
          exact hz_unemb k (hkw ▸ (Classical.choose_spec hex).2)
        · obtain ⟨j, _, hjw⟩ := Finset.mem_image.mp h2
          exact hz_unemb ⟨j.val, by omega⟩ (hjw ▸ hroots_g ⟨j.val, by omega⟩)
      have hsub_L : insert z_max (L_used ∪ L_pref) ⊆ leaves := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz_leaf⟩
        · rcases Finset.mem_union.mp hw' with h1 | h2
          · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h1
            have hex : ∃ w ∈ leaves, g k = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
            simp only [hex, ↓reduceDIte]
            exact (Classical.choose_spec hex).1
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref ⟨j.val, by omega⟩ j.isLt⟩
      have hc := Finset.card_le_card hsub_L
      rw [Finset.card_insert_of_notMem hz_notin, Finset.card_union_of_disjoint hdisj_up,
        hcard_used, hcard_pref] at hc
      omega
    have hfail_bound : fail.card + q + 1 ≤ leaves.card := by
      have hsum_step : ∑ b ∈ MaxFail, (fail.filter (fun j => a b < j ∧ j ≤ b)).card ≤
          ∑ b ∈ MaxFail, (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card :=
        Finset.sum_le_sum hper_int
      omega
    have hemb_lt : emb.card < Fintype.card W := by
      have hsub : emb ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun h => by
        have : z_max ∈ emb := h ▸ Finset.mem_univ z_max
        obtain ⟨i, hi⟩ := (Finset.mem_filter.mp this).2
        exact hz_unemb i hi)
      simpa using Finset.card_lt_card hsub
    change Fintype.card W + leaves.card ≤ m + 1 + q at hm
    omega
  -- Step 3: Extract the injective digraph homomorphism f : D →g G from g!
  choose idx hidx using hall_emb
  refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_, ?_⟩
  · intro u v hDuv
    rcases hpar_g (idx v) v (hidx v) with hltp | ⟨s, _, u', hgs', hDu', hGu'⟩
    · have h1 := hroots_g ⟨(idx v).val, hltp⟩
      have hveq : v = roots ⟨(idx v).val, hltp⟩ := Option.some.inj ((hidx v).symm.trans h1)
      exact absurd hDuv ((hroots_iff v).mpr ⟨⟨(idx v).val, hltp⟩, hveq.symm⟩ u)
    · have hueq : u' = u := hInDeg v u' u hDu' hDuv
      subst u'
      have hseq : s = idx u := hinj_g s (idx u) u hgs' (hidx u)
      exact hseq ▸ hGu'
  · intro w1 w2 h
    have hi := σ.injective h
    have h1 := hidx w1
    rw [hi] at h1
    exact Option.some.inj (h1.symm.trans (hidx w2))
  · intro j
    exact congrArg σ (hinj_g (idx (roots j)) ⟨j.val, by omega⟩ (roots j) (hidx (roots j)) (hroots_g j))

end CoreToolkit

-- ============================================================================
-- MODULE 4A: Interval Branching, Bi-Arborescences, and Heart h = 2 (Thm 4.2)
-- ============================================================================

section Module4A

lemma greedy_right_interval
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hRank : ∃ rank : W → ℕ, ∀ u v, D.Adj u v → rank u < rank v)
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (lo len : ℕ) (hlen : lo + len ≤ Fintype.card V)
    {p : ℕ} (roots : Fin p → W) (hroots_inj : Function.Injective roots)
    (hroots_iff : ∀ w : W, (∀ u, ¬ D.Adj u w) ↔ ∃ j : Fin p, roots j = w)
    (hp_le : p ≤ len) (q : ℕ) (hq_le : q ≤ p)
    (hpref : ∀ j : Fin p, j.val < q → ∀ u, ¬ D.Adj (roots j) u)
    (hm : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      len + 1 + q) :
    ∃ f : W → Fin (Fintype.card V),
      Function.Injective f ∧
      (∀ w : W, lo ≤ (f w).val ∧ (f w).val < lo + len) ∧
      (∀ u v : W, D.Adj u v → G.Adj (σ (f u)) (σ (f v))) ∧
      (∀ j : Fin p, f (roots j) = ⟨lo + j.val, by omega⟩) := by
  classical
  let Gsub : Digraph (Fin len) := ⟨fun a b => G.Adj (σ ⟨lo + a.val, by omega⟩) (σ ⟨lo + b.val, by omega⟩)⟩
  let σsub : Fin (Fintype.card (Fin len)) ≃ Fin len := finCongr (Fintype.card_fin len)
  have hRsub : ∀ i j : Fin (Fintype.card (Fin len)), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i < k ∧ k ≤ j ∧ Gsub.Adj (σsub i) (σsub k))).card := by
    intro i j hij
    let i' : Fin (Fintype.card V) := ⟨lo + i.val, by have := i.isLt; simp only [Fintype.card_fin] at this; omega⟩
    let j' : Fin (Fintype.card V) := ⟨lo + j.val, by have := j.isLt; simp only [Fintype.card_fin] at this; omega⟩
    have hij' : i' < j' := by change lo + i.val < lo + j.val; have : i.val < j.val := hij; omega
    have h := hR i' j' hij'
    have hdiff : j'.val - i'.val = j.val - i.val := by change (lo + j.val) - (lo + i.val) = j.val - i.val; omega
    have hcard : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i' < k ∧ k ≤ j' ∧ G.Adj (σ i') (σ k))).card =
      (Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i < k ∧ k ≤ j ∧ Gsub.Adj (σsub i) (σsub k))).card := by
      refine Finset.card_bij (fun k hk => ⟨k.val - lo, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have h2 : k.val ≤ lo + j.val := hk.2.1
        have hjlt : j.val < len := by simpa using j.isLt
        rw [Fintype.card_fin]; omega⟩) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        have h1 : lo + i.val < k.val := hk.1
        have h2 : k.val ≤ lo + j.val := hk.2.1
        refine ⟨by change i.val < k.val - lo; omega, by change k.val - lo ≤ j.val; omega, ?_⟩
        dsimp only [Gsub, σsub, finCongr_apply, Fin.val_cast]
        have heq1 : (⟨lo + i.val, by omega⟩ : Fin (Fintype.card V)) = i' := rfl
        have heq2 : (⟨lo + (k.val - lo), by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext (by dsimp only; omega)
        simpa [heq1, heq2] using hk.2.2
      · intro k1 hk1 k2 hk2 hEq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
        have h1 : lo + i.val < k1.val := hk1.1
        have h2 : lo + i.val < k2.val := hk2.1
        have hv : k1.val - lo = k2.val - lo := congrArg Fin.val hEq
        exact Fin.ext (by omega)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have hklt : k.val < len := by simpa using k.isLt
        refine ⟨⟨lo + k.val, by omega⟩, ?_, Fin.ext (by simp)⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : i.val < k.val := hk.1
        have h2 : k.val ≤ j.val := hk.2.1
        refine ⟨by change lo + i.val < lo + k.val; omega,
          by change lo + k.val ≤ lo + j.val; omega, ?_⟩
        simpa [Gsub, σsub, i'] using hk.2.2
    rw [hdiff, hcard] at h
    exact h
  have hp_le' : p ≤ Fintype.card (Fin len) := by simpa using hp_le
  have hm' : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      Fintype.card (Fin len) + 1 + q := by simpa using hm
  obtain ⟨f0, hf0_inj, hf0_roots⟩ := greedy_out_branching_embeds D hRank hInDeg Gsub hRsub
    roots hroots_inj hroots_iff hp_le' q hq_le hpref hm'
  refine ⟨fun w => ⟨lo + (f0 w).val, by omega⟩, ?_, ?_, ?_, ?_⟩
  · intro w1 w2 h
    have hv : lo + (f0 w1).val = lo + (f0 w2).val := congrArg Fin.val h
    exact hf0_inj (Fin.ext (by omega))
  · intro w; dsimp only; exact ⟨by omega, by have := (f0 w).isLt; omega⟩
  · intro u v huv; exact f0.map_adj' huv
  · intro j
    have h := hf0_roots j
    apply Fin.ext
    have hv : (f0 (roots j)).val = j.val := by
      have := congrArg Fin.val h
      simpa [σsub] using this
    change lo + (f0 (roots j)).val = lo + j.val
    omega

lemma greedy_left_interval
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hRank : ∃ rank : W → ℕ, ∀ u v, D.Adj u v → rank v < rank u)
    (hOutDeg : ∀ w u1 u2 : W, D.Adj w u1 → D.Adj w u2 → u1 = u2)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {σ : Fin (Fintype.card V) ≃ V}
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (hi len : ℕ) (hlen : len ≤ hi + 1) (hhi : hi < Fintype.card V)
    {p : ℕ} (roots : Fin p → W) (hroots_inj : Function.Injective roots)
    (hroots_iff : ∀ w : W, (∀ u, ¬ D.Adj w u) ↔ ∃ j : Fin p, roots j = w)
    (hp_le : p ≤ len) (q : ℕ) (hq_le : q ≤ p)
    (hpref : ∀ j : Fin p, j.val < q → ∀ u, ¬ D.Adj u (roots j))
    (hm : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj u w)).card ≤
      len + 1 + q) :
    ∃ f : W → Fin (Fintype.card V),
      Function.Injective f ∧
      (∀ w : W, hi + 1 - len ≤ (f w).val ∧ (f w).val ≤ hi) ∧
      (∀ u v : W, D.Adj u v → G.Adj (σ (f u)) (σ (f v))) ∧
      (∀ j : Fin p, f (roots j) = ⟨hi - j.val, by omega⟩) := by
  classical
  let Drev : Digraph W := ⟨fun u v => D.Adj v u⟩
  let Gsub : Digraph (Fin len) := ⟨fun a b =>
    G.Adj (σ ⟨hi - b.val, by omega⟩) (σ ⟨hi - a.val, by omega⟩)⟩
  let σsub : Fin (Fintype.card (Fin len)) ≃ Fin len := finCongr (Fintype.card_fin len)
  have hRsub : ∀ i j : Fin (Fintype.card (Fin len)), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i < k ∧ k ≤ j ∧ Gsub.Adj (σsub i) (σsub k))).card := by
    intro i j hij
    have hjlt : j.val < len := by simpa using j.isLt
    have hij_val : i.val < j.val := hij
    let i' : Fin (Fintype.card V) := ⟨hi - j.val, by omega⟩
    let j' : Fin (Fintype.card V) := ⟨hi - i.val, by omega⟩
    have hij' : i' < j' := by change hi - j.val < hi - i.val; omega
    have h := hL i' j' hij'
    have hdiff : j'.val - i'.val = j.val - i.val := by change (hi - i.val) - (hi - j.val) = j.val - i.val; omega
    have hcard : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i' ≤ k ∧ k < j' ∧ G.Adj (σ k) (σ j'))).card =
      (Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i < k ∧ k ≤ j ∧ Gsub.Adj (σsub i) (σsub k))).card := by
      refine Finset.card_bij (fun k hk => ⟨hi - k.val, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have h1 : hi - j.val ≤ k.val := hk.1
        have h2 : k.val < hi - i.val := hk.2.1
        rw [Fintype.card_fin]; omega⟩) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        have h1 : hi - j.val ≤ k.val := hk.1
        have h2 : k.val < hi - i.val := hk.2.1
        refine ⟨by change i.val < hi - k.val; omega, by change hi - k.val ≤ j.val; omega, ?_⟩
        dsimp only [Gsub, σsub, finCongr_apply, Fin.val_cast]
        have heq1 : (⟨hi - (hi - k.val), by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext (by dsimp only; omega)
        have heq2 : (⟨hi - i.val, by omega⟩ : Fin (Fintype.card V)) = j' := rfl
        simpa [heq1, heq2] using hk.2.2
      · intro k1 hk1 k2 hk2 hEq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
        have h1 : k1.val < hi - i.val := hk1.2.1
        have h2 : k2.val < hi - i.val := hk2.2.1
        have hv : hi - k1.val = hi - k2.val := congrArg Fin.val hEq
        exact Fin.ext (by omega)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have hklt : k.val < len := by simpa using k.isLt
        have h1 : i.val < k.val := hk.1
        have h2 : k.val ≤ j.val := hk.2.1
        refine ⟨⟨hi - k.val, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by change hi - j.val ≤ hi - k.val; omega,
          by change hi - k.val < hi - i.val; omega, ?_⟩
        simpa [Gsub, σsub, j'] using hk.2.2
    rw [hdiff, hcard] at h
    exact h
  have hp_le' : p ≤ Fintype.card (Fin len) := by simpa using hp_le
  have hm' : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ Drev.Adj w u)).card ≤
      Fintype.card (Fin len) + 1 + q := by simpa [Drev] using hm
  obtain ⟨f0, hf0_inj, hf0_roots⟩ := greedy_out_branching_embeds Drev
    (by obtain ⟨rk, hrk⟩ := hRank; exact ⟨rk, fun u v h => hrk v u h⟩) hOutDeg Gsub hRsub
    roots hroots_inj hroots_iff hp_le' q hq_le hpref hm'
  refine ⟨fun w => ⟨hi - (f0 w).val, by have := (f0 w).isLt; omega⟩, ?_, ?_, ?_, ?_⟩
  · intro w1 w2 h
    have h1 := (f0 w1).isLt; have h2 := (f0 w2).isLt
    have hv : hi - (f0 w1).val = hi - (f0 w2).val := congrArg Fin.val h
    exact hf0_inj (Fin.ext (by omega))
  · intro w; dsimp only; have := (f0 w).isLt; exact ⟨by omega, by omega⟩
  · intro u v huv
    exact f0.map_adj' huv
  · intro j
    have h := hf0_roots j
    apply Fin.ext
    have hv : (f0 (roots j)).val = j.val := by
      have := congrArg Fin.val h; simpa [σsub] using this
    change hi - (f0 (roots j)).val = hi - j.val
    omega

-- Subtree connectivity when no edge crosses between S \ {r} and Sᶜ
lemma isTree_induce_of_single_gate {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) {S : Finset W} {r : W} (hr : r ∈ S)
    (hgate : ∀ x ∈ S, x ≠ r → ∀ y ∉ S, ¬ T.Adj x y) :
    (T.induce (S : Set W)).IsTree := by
  refine ⟨?_, hT.isAcyclic.induce _⟩
  have : Nonempty S := ⟨⟨r, hr⟩⟩
  refine SimpleGraph.Connected.mk (fun a b => ?_)
  -- Suffices to show every a ∈ S is reachable from ⟨r, hr⟩ inside T.induce S
  have hreach_r : ∀ x : S, (T.induce (S : Set W)).Reachable ⟨r, hr⟩ x := by
    intro x
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath r x.1
    have hsupp : ∀ w ∈ p.support, w ∈ S := by
      have hback : ∀ (u v : W) (q : T.Walk u v), q.IsPath → v ∈ S →
          (∀ w ∈ q.support, w = r → w = u) → ∀ w ∈ q.support, w ∈ S := by
        intro u v q hq hv hrstart
        induction q with
        | nil =>
          intro w hw; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          exact hw ▸ hv
        | @cons a1 b1 c1 hab q' ih =>
          have hq'path : q'.IsPath := hq.of_cons
          have hb_ne_r : ∀ w ∈ q'.support, w ≠ r := by
            intro w hw hwr
            have hw_mem : w ∈ (SimpleGraph.Walk.cons hab q').support := List.mem_cons_of_mem a1 hw
            have hwa : w = a1 := hrstart w hw_mem hwr
            have ha_notin : a1 ∉ q'.support := by
              have hnd := hq.support_nodup
              simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
              exact hnd.1
            exact ha_notin (hwa ▸ hw)
          have hq'_S : ∀ w ∈ q'.support, w ∈ S := ih hq'path hv (fun w hw hwr => absurd hwr (hb_ne_r w hw))
          intro w hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
          rcases hw with hwa | hw'
          · rw [hwa]
            by_cases har : a1 = r
            · exact har ▸ hr
            · by_contra ha_notS
              have hbS : b1 ∈ S := hq'_S b1 q'.start_mem_support
              have hbne : b1 ≠ r := hb_ne_r b1 q'.start_mem_support
              exact hgate b1 hbS hbne a1 ha_notS hab.symm
          · exact hq'_S w hw'
      exact hback r x.1 p hp x.2 (fun _ _ h => h)
    have hlift : ∀ (u v : W) (q : T.Walk u v), (hu : u ∈ S) → (hv : v ∈ S) →
        (∀ w ∈ q.support, w ∈ S) → (T.induce (S : Set W)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro u v q hu hv hqS
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a1 b1 c1 hab q' ih =>
        have hbS : b1 ∈ S := hqS b1 (List.mem_cons_of_mem a1 q'.start_mem_support)
        have hstep : (T.induce (S : Set W)).Adj ⟨a1, hu⟩ ⟨b1, hbS⟩ := hab
        exact hstep.reachable.trans (ih hbS hv (fun w hw => hqS w (List.mem_cons_of_mem a1 hw)))
    exact hlift r x.1 p hr x.2 hsupp
  exact (hreach_r a).symm.trans (hreach_r b)

-- Subtree connectivity when gate is a single edge u - v (for Heart h = 2!)
lemma isTree_induce_of_edge_gate {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) {S : Finset W} {u v : W}
    (hu : u ∈ S) (hv : v ∈ S) (huv : T.Adj u v)
    (hgate : ∀ x ∈ S, x ≠ u → x ≠ v → ∀ y ∉ S, ¬ T.Adj x y) :
    (T.induce (S : Set W)).IsTree := by
  refine ⟨?_, hT.isAcyclic.induce _⟩
  have : Nonempty S := ⟨⟨u, hu⟩⟩
  refine SimpleGraph.Connected.mk (fun a b => ?_)
  have hreach_u : ∀ x : S, (T.induce (S : Set W)).Reachable ⟨u, hu⟩ x := by
    intro x
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath u x.1
    have hsupp_app : ∀ {x1 y1 z1 : W} (q1 : T.Walk x1 y1) (q2 : T.Walk y1 z1) {w : W},
        w ∈ (q1.append q2).support → w ∈ q1.support ∨ w ∈ q2.support := by
      intro x1 y1 z1 q1 q2 w hw
      induction q1 with
      | nil => exact Or.inr hw
      | @cons a1 b1 c1 hab q1' ih =>
        simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.support_cons, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw'
        · exact Or.inl (Or.inl rfl)
        · rcases ih q2 hw' with h1 | h2
          · exact Or.inl (Or.inr h1)
          · exact Or.inr h2
    have huv_path : (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simpa using T.ne_of_adj huv)
    have hsupp : ∀ w ∈ p.support, w ∈ S := by
      have hv_snd : ∀ (q : T.Walk u x.1), q.IsPath → v ∈ q.support →
          ∀ w ∈ q.support, w = u ∨ w = v ∨ ∀ (q2 : T.Walk v x.1), q2.IsPath → w ∈ q2.support := by
        intro q hq hvq w hw
        let p1 := q.takeUntil v hvq
        let p2 := q.dropUntil v hvq
        have hp1_path : p1.IsPath := hq.takeUntil hvq
        have hp2_path : p2.IsPath := hq.dropUntil hvq
        have hp1_eq : p1 = SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil :=
          congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u v).elim
            ⟨p1, hp1_path⟩ ⟨SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil, huv_path⟩)
        have hcat : p1.append p2 = q := SimpleGraph.Walk.take_spec q hvq
        have hmem : w ∈ p1.support ∨ w ∈ p2.support := by
          rw [← hcat] at hw
          exact hsupp_app p1 p2 hw
        rcases hmem with h1 | h2
        · rw [hp1_eq] at h1
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at h1
          rcases h1 with hwu | hwv
          · exact Or.inl hwu
          · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr fun q2 hq2 => by
            have heq : p2 = q2 := congrArg Subtype.val
              ((hT.isAcyclic.subsingleton_path v x.1).elim ⟨p2, hp2_path⟩ ⟨q2, hq2⟩)
            exact heq ▸ h2)
      have hback : ∀ (a0 c0 : W) (q : T.Walk a0 c0), q.IsPath → c0 ∈ S →
          (∀ w ∈ q.support, (w = u ∨ w = v) → w = a0) →
          ∀ w ∈ q.support, w ∈ S := by
        intro a0 c0 q hq hc hstart
        induction q with
        | nil =>
          intro w hw; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          exact hw ▸ hc
        | @cons a1 b1 c1 hab q' ih =>
          have hq'path : q'.IsPath := hq.of_cons
          have hnd : a1 ∉ q'.support := by
            have h := hq.support_nodup
            simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at h
            exact h.1
          have hq'_no_uv : ∀ w ∈ q'.support, w ≠ u ∧ w ≠ v := by
            intro w hw
            constructor <;> intro heq
            · exact hnd (hstart w (List.mem_cons_of_mem a1 hw) (Or.inl heq) ▸ hw)
            · exact hnd (hstart w (List.mem_cons_of_mem a1 hw) (Or.inr heq) ▸ hw)
          have hq'_S : ∀ w ∈ q'.support, w ∈ S :=
            ih hq'path hc (fun w hw huv' => by
              rcases huv' with h1 | h2
              · exact absurd h1 (hq'_no_uv w hw).1
              · exact absurd h2 (hq'_no_uv w hw).2)
          intro w hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
          rcases hw with hwa | hw'
          · rw [hwa]
            by_cases ha_uv : a1 = u ∨ a1 = v
            · rcases ha_uv with h1 | h2
              · exact h1 ▸ hu
              · exact h2 ▸ hv
            · push Not at ha_uv
              by_contra ha_notS
              have hbS : b1 ∈ S := hq'_S b1 q'.start_mem_support
              have hb_no := hq'_no_uv b1 q'.start_mem_support
              exact hgate b1 hbS hb_no.1 hb_no.2 a1 ha_notS hab.symm
          · exact hq'_S w hw'
      by_cases hv_mem : v ∈ p.support
      · let p2 := p.dropUntil v hv_mem
        have hp2_path : p2.IsPath := hp.dropUntil hv_mem
        have hp2_no_u : u ∉ p2.support := by
          have hp1_eq : p.takeUntil v hv_mem = SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil :=
            congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u v).elim
              ⟨p.takeUntil v hv_mem, hp.takeUntil hv_mem⟩
              ⟨SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil, huv_path⟩)
          have hcat := SimpleGraph.Walk.take_spec p hv_mem
          rw [hp1_eq] at hcat
          have hnd := hp.support_nodup
          rw [← hcat] at hnd
          simp only [SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append,
            SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.1
        have hp2_S : ∀ w ∈ p2.support, w ∈ S :=
          hback v x.1 p2 hp2_path x.2 (fun w hw huv' => by
            rcases huv' with rfl | rfl
            · exact absurd hw hp2_no_u
            · rfl)
        intro w hw
        rcases hv_snd p hp hv_mem w hw with rfl | rfl | hw2
        · exact hu
        · exact hv
        · exact hp2_S w (hw2 p2 hp2_path)
      · exact hback u x.1 p hp x.2 (fun w hw huv' => by
          rcases huv' with rfl | rfl
          · rfl
          · exact absurd hw hv_mem)
    have hlift : ∀ (a1 c1 : W) (q : T.Walk a1 c1), (ha1 : a1 ∈ S) → (hc1 : c1 ∈ S) →
        (∀ w ∈ q.support, w ∈ S) → (T.induce (S : Set W)).Reachable ⟨a1, ha1⟩ ⟨c1, hc1⟩ := by
      intro a1 c1 q ha1 hc1 hqS
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a2 b2 c2 hab q' ih =>
        have hbS : b2 ∈ S := hqS b2 (List.mem_cons_of_mem a2 q'.start_mem_support)
        have hstep : (T.induce (S : Set W)).Adj ⟨a2, ha1⟩ ⟨b2, hbS⟩ := hab
        exact hstep.reachable.trans (ih hbS hc1 (fun w hw => hqS w (List.mem_cons_of_mem a2 hw)))
    exact hlift u x.1 p hu x.2 hsupp
  exact (hreach_u a).symm.trans (hreach_u b)

lemma sum_indeg_eq_card_sub_one {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} [DecidableRel T.Adj] (hT : T.IsTree)
    {D : Digraph W} [DecidableRel D.Adj] (hO : D.IsOrientation T) :
    ∑ w : W, (Finset.univ.filter (fun x : W => D.Adj x w)).card = Fintype.card W - 1 := by
  classical
  let arcs := (Finset.univ : Finset (W × W)).filter (fun p => D.Adj p.1 p.2)
  have harcs_sum : arcs.card = ∑ w : W, (Finset.univ.filter (fun x : W => D.Adj x w)).card := by
    have hpart : arcs = Finset.univ.biUnion (fun w : W =>
        (Finset.univ.filter (fun x : W => D.Adj x w)).image (fun x => (x, w))) := by
      ext ⟨a, b⟩
      simp only [arcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨b, a, h, rfl, rfl⟩
      · rintro ⟨w, x, hx, rfl, rfl⟩; exact hx
    rw [hpart, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Finset.card_image_of_injective]
      intro x1 x2 h; exact congrArg Prod.fst h
    · intro w1 _ w2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hp2
      exact hne (congrArg Prod.snd hEq).symm
  have harcs_edge : arcs.card = T.edgeFinset.card := by
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [arcs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact T.mem_edgeFinset.mpr (hO.1 p.1 p.2 hp)
    · intro p hp q hq hEq
      simp only [arcs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      rw [Sym2.eq_iff] at hEq
      rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        rw [h1, h2] at hp
        exact not_adj_rev_of_isOrientation hO hp hq
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hTab : T.Adj a b := T.mem_edgeFinset.mp he
        rcases adj_or_rev_of_isOrientation hO hTab with hab | hba
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩, Sym2.eq_swap⟩
  have hedge := hT.card_edgeFinset
  omega

-- Out-arborescence characterization: if T is a tree, D orients T, and every w ≠ r has in-degree 1,
-- then r has in-degree 0 and rank w := T.dist r w strictly increases along every arc of D!
lemma out_arborescence_rank_and_root {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} [DecidableRel T.Adj] (hT : T.IsTree)
    {D : Digraph W} [DecidableRel D.Adj] (hO : D.IsOrientation T)
    (r : W) (hin : ∀ w : W, w ≠ r → (Finset.univ.filter (fun x : W => D.Adj x w)).card = 1) :
    (∀ x : W, ¬ D.Adj x r) ∧
    (∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2) ∧
    (∀ u v : W, D.Adj u v → T.dist r u < T.dist r v) := by
  classical
  have hsum_in : ∑ w : W, (Finset.univ.filter (fun x : W => D.Adj x w)).card = Fintype.card W - 1 :=
    sum_indeg_eq_card_sub_one hT hO
  have hsum_split : ∑ w : W, (Finset.univ.filter (fun x : W => D.Adj x w)).card =
      (Finset.univ.filter (fun x : W => D.Adj x r)).card +
      ∑ w ∈ Finset.univ.erase r, (Finset.univ.filter (fun x : W => D.Adj x w)).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ r)).symm
  have herase_sum : ∑ w ∈ Finset.univ.erase r, (Finset.univ.filter (fun x : W => D.Adj x w)).card =
      Fintype.card W - 1 := by
    rw [Finset.sum_congr rfl (fun w hw => hin w (Finset.mem_erase.mp hw).1)]
    simp [Finset.card_erase_of_mem]
  have hr_zero : (Finset.univ.filter (fun x : W => D.Adj x r)).card = 0 := by omega
  have hr_noin : ∀ x : W, ¬ D.Adj x r := fun x hx => by
    have : x ∈ Finset.univ.filter (fun x : W => D.Adj x r) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    rw [Finset.card_eq_zero.mp hr_zero] at this
    exact Finset.notMem_empty x this
  have huniq_in : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2 := by
    intro w u1 u2 h1 h2
    by_cases hwr : w = r
    · subst hwr; exact absurd h1 (hr_noin u1)
    · have hc := hin w hwr
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
      have h1' : u1 ∈ ({z} : Finset W) := hz ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
      have h2' : u2 ∈ ({z} : Finset W) := hz ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
      simp only [Finset.mem_singleton] at h1' h2'
      exact h1'.trans h2'.symm
  -- Step 2: By induction on d = T.dist r v, whenever T.Adj v u and T.dist r u = d + 1, we have D.Adj v u!
  have hdir : ∀ d : ℕ, ∀ v u : W, T.dist r v = d → T.Adj v u → T.dist r u = d + 1 → D.Adj v u := by
    intro d
    induction d with
    | zero =>
      intro v u hv0 hTvu _
      have hvr : v = r := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hv0).resolve_right
        (not_not.mpr (hT.connected r v)) |>.symm
      subst hvr
      rcases adj_or_rev_of_isOrientation hO hTvu with h | h
      · exact h
      · exact absurd h (hr_noin u)
    | succ d' ih =>
      intro v u hvd hTvu hud
      have hex_p : ∃ p : W, T.Adj p v ∧ T.dist r p = d' := by
        obtain ⟨pwalk, _, hp_len⟩ := (hT.connected r v).exists_path_of_dist
        have hrev_len : pwalk.reverse.length = d' + 1 := by simpa [hvd] using hp_len
        generalize hq : pwalk.reverse = q at hrev_len
        cases q with
        | nil => simp at hrev_len
        | @cons _ p _ hTvp q' =>
          have hTpv : T.Adj p v := hTvp.symm
          have hqlen : q'.length = d' := by simp at hrev_len; omega
          have hle : T.dist r p ≤ d' := by
            have := SimpleGraph.dist_le q'.reverse
            simpa [hqlen] using this
          refine ⟨p, hTpv, ?_⟩
          rcases hT.dist_eq_dist_add_one_of_adj r hTpv with h1 | h2 <;> omega
      obtain ⟨p, hTpv, hdist_p⟩ := hex_p
      have hDpv : D.Adj p v := ih p v hdist_p hTpv hvd
      have hpu : p ≠ u := fun h => by subst h; omega
      rcases adj_or_rev_of_isOrientation hO hTvu with h | h
      · exact h
      · exact absurd (huniq_in v p u hDpv h) hpu
  refine ⟨hr_noin, huniq_in, ?_⟩
  intro u v hDuv
  have hTuv : T.Adj u v := hO.1 u v hDuv
  rcases hT.dist_eq_dist_add_one_of_adj r hTuv with h1 | h2
  · exfalso
    have hDvu : D.Adj v u := hdir (T.dist r v) v u rfl hTuv.symm h1
    exact not_adj_rev_of_isOrientation hO hDuv hDvu
  · omega

-- ============================================================================
-- Bi-Arborescence Theorem (All out-/in-arborescences, stars, bi-arborescences!)
-- ============================================================================

lemma embeds_bi_arborescence {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hBi : ∃ r : W, ∃ A : Finset W, r ∉ A ∧
      (∀ u ∈ A, (Finset.univ.filter (fun x : W => D.Adj x u)).card = 1) ∧
      (∀ v : W, v ≠ r → v ∉ A → (Finset.univ.filter (fun x : W => D.Adj v x)).card = 1) ∧
      (∀ u ∈ A, ∀ v : W, v ≠ r → v ∉ A → ¬ D.Adj u v ∧ ¬ D.Adj v u)) :
    Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  obtain ⟨r, A, hrA, hAin, hBout, hnocross⟩ := hBi
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  let Splus : Finset W := insert r A
  let Sminus : Finset W := Aᶜ
  have hr_plus : r ∈ Splus := Finset.mem_insert_self r A
  have hr_minus : r ∈ Sminus := Finset.mem_compl.mpr hrA
  have hT_nocross : ∀ u ∈ A, ∀ v ∉ Splus, ¬ T.Adj u v := by
    intro u hu v hv hTuv
    have hvne : v ≠ r := fun h => hv (h ▸ hr_plus)
    have hvA : v ∉ A := fun h => hv (Finset.mem_insert_of_mem h)
    rcases adj_or_rev_of_isOrientation hO hTuv with h | h
    · exact (hnocross u hu v hvne hvA).1 h
    · exact (hnocross u hu v hvne hvA).2 h
  have hT_plus : (T.induce (Splus : Set W)).IsTree :=
    isTree_induce_of_single_gate hT hr_plus (fun x hx hxr y hy =>
      hT_nocross x ((Finset.mem_insert.mp hx).resolve_left hxr) y hy)
  have hT_minus : (T.induce (Sminus : Set W)).IsTree :=
    isTree_induce_of_single_gate hT hr_minus (fun x hx hxr y hy hTxy => by
      have hyA : y ∈ A := by
        by_contra h; exact hy (Finset.mem_compl.mpr h)
      have hx_notS : x ∉ Splus := fun h => by
        rcases Finset.mem_insert.mp h with rfl | hxA
        · exact hxr rfl
        · exact Finset.mem_compl.mp hx hxA
      exact hT_nocross y hyA x hx_notS hTxy.symm)
  let Dplus : Digraph Splus := ⟨fun x y => D.Adj x.1 y.1⟩
  let Dminus : Digraph Sminus := ⟨fun x y => D.Adj x.1 y.1⟩
  let Dminus_rev : Digraph Sminus := ⟨fun x y => D.Adj y.1 x.1⟩
  have hO_plus : Dplus.IsOrientation (T.induce (Splus : Set W)) :=
    ⟨fun x y h => hO.1 x.1 y.1 h, fun x y h => hO.2 x.1 y.1 h⟩
  have hO_minus_rev : Dminus_rev.IsOrientation (T.induce (Sminus : Set W)) :=
    ⟨fun x y h => (hO.1 y.1 x.1 h).symm, fun x y h => hO.2 y.1 x.1 h.symm⟩
  -- Every x ∈ Splus \ {r} has in-degree 1 inside Dplus
  have hin_plus : ∀ x : Splus, x ≠ ⟨r, hr_plus⟩ →
      (Finset.univ.filter (fun y : Splus => Dplus.Adj y x)).card = 1 := by
    intro x hxr
    have hxA : x.1 ∈ A := (Finset.mem_insert.mp x.2).resolve_left (fun h => hxr (Subtype.ext h))
    have hcard_all := hAin x.1 hxA
    have hbij : (Finset.univ.filter (fun y : Splus => Dplus.Adj y x)).card =
        (Finset.univ.filter (fun y : W => D.Adj y x.1)).card := by
      refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro y1 _ y2 _ h; exact Subtype.ext h
      · intro y hy
        have hDyx : D.Adj y x.1 := (Finset.mem_filter.mp hy).2
        have hyS : y ∈ Splus := by
          by_contra hynot
          exact hT_nocross x.1 hxA y hynot (hO.1 y x.1 hDyx).symm
        exact ⟨⟨y, hyS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDyx⟩, rfl⟩
    rw [hbij, hcard_all]
  -- Every x ∈ Sminus \ {r} has in-degree 1 inside Dminus_rev
  have hin_minus : ∀ x : Sminus, x ≠ ⟨r, hr_minus⟩ →
      (Finset.univ.filter (fun y : Sminus => Dminus_rev.Adj y x)).card = 1 := by
    intro x hxr
    have hxne : x.1 ≠ r := fun h => hxr (Subtype.ext h)
    have hxA : x.1 ∉ A := Finset.mem_compl.mp x.2
    have hcard_all := hBout x.1 hxne hxA
    have hbij : (Finset.univ.filter (fun y : Sminus => Dminus_rev.Adj y x)).card =
        (Finset.univ.filter (fun y : W => D.Adj x.1 y)).card := by
      refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro y1 _ y2 _ h; exact Subtype.ext h
      · intro y hy
        have hDxy : D.Adj x.1 y := (Finset.mem_filter.mp hy).2
        have hyS : y ∈ Sminus := by
          by_contra hynot
          have hyA : y ∈ A := not_not.mp (Finset.mem_compl.not.mp hynot)
          exact (hnocross y hyA x.1 hxne hxA).2 hDxy
        exact ⟨⟨y, hyS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy⟩, rfl⟩
    rw [hbij, hcard_all]
  obtain ⟨hr_noin_p, huniq_p, hrank_p⟩ := out_arborescence_rank_and_root hT_plus hO_plus ⟨r, hr_plus⟩ hin_plus
  obtain ⟨hr_noin_m, huniq_m, hrank_m⟩ := out_arborescence_rank_and_root hT_minus hO_minus_rev ⟨r, hr_minus⟩ hin_minus
  -- Compute lengths len_minus and len_plus!
  let kplus := (Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus.Adj x y)).card
  let kminus := (Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus.Adj y x)).card
  have hkplus_le : kplus ≤ Splus.card := by
    simpa [kplus, Fintype.card_coe] using
      Finset.card_le_univ (Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus.Adj x y))
  have hkminus_le : kminus ≤ Sminus.card := by
    simpa [kminus, Fintype.card_coe] using
      Finset.card_le_univ (Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus.Adj y x))
  have hkplus_strict : 1 < Splus.card → kplus ≤ Splus.card - 1 := by
    intro hgt
    -- r has an out-neighbor in Splus (since T_plus is connected and every edge goes away from r!)
    have hne_r : ∃ x : Splus, x ≠ ⟨r, hr_plus⟩ := by
      have : 1 < Fintype.card Splus := by simpa [Fintype.card_coe] using hgt
      obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp this
      by_cases hx : x = ⟨r, hr_plus⟩
      · exact ⟨y, fun h => hxy (hx.trans h.symm)⟩
      · exact ⟨x, hx⟩
    obtain ⟨x0, hx0⟩ := hne_r
    obtain ⟨p⟩ := hT_plus.connected ⟨r, hr_plus⟩ x0
    have hradj : ∃ y : Splus, Dplus.Adj ⟨r, hr_plus⟩ y := by
      cases p with
      | nil => exact absurd rfl hx0
      | @cons _ y _ hadj _ =>
        rcases adj_or_rev_of_isOrientation hO_plus hadj with h | h
        · exact ⟨y, h⟩
        · exact absurd h (hr_noin_p y)
    obtain ⟨y0, hy0⟩ := hradj
    have hsub : Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus.Adj x y) ⊆
        Finset.univ.erase ⟨r, hr_plus⟩ := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq; subst heq
      exact (Finset.mem_filter.mp hx).2 y0 hy0
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe] at hc
    exact hc
  have hkminus_strict : 1 < Sminus.card → kminus ≤ Sminus.card - 1 := by
    intro hgt
    have hne_r : ∃ x : Sminus, x ≠ ⟨r, hr_minus⟩ := by
      have : 1 < Fintype.card Sminus := by simpa [Fintype.card_coe] using hgt
      obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp this
      by_cases hx : x = ⟨r, hr_minus⟩
      · exact ⟨y, fun h => hxy (hx.trans h.symm)⟩
      · exact ⟨x, hx⟩
    obtain ⟨x0, hx0⟩ := hne_r
    obtain ⟨p⟩ := hT_minus.connected ⟨r, hr_minus⟩ x0
    have hradj : ∃ y : Sminus, Dminus.Adj y ⟨r, hr_minus⟩ := by
      cases p with
      | nil => exact absurd rfl hx0
      | @cons _ y _ hadj _ =>
        rcases adj_or_rev_of_isOrientation hO_minus_rev hadj with h | h
        · exact ⟨y, h⟩
        · exact absurd h (hr_noin_m y)
    obtain ⟨y0, hy0⟩ := hradj
    have hsub : Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus.Adj y x) ⊆
        Finset.univ.erase ⟨r, hr_minus⟩ := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq; subst heq
      exact (Finset.mem_filter.mp hx).2 y0 hy0
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe] at hc
    exact hc
  have hcard_sum : Splus.card + Sminus.card = n + 1 := by
    have h1 : A.card + Sminus.card = n := by
      have := Finset.card_add_card_compl A
      change A.card + Sminus.card = Fintype.card W at this
      rw [hW] at this; exact this
    have h2 : Splus.card = A.card + 1 := Finset.card_insert_of_notMem hrA
    omega
  have hSplus_pos : 1 ≤ Splus.card := Finset.one_le_card.mpr ⟨r, hr_plus⟩
  have hSminus_pos : 1 ≤ Sminus.card := Finset.one_le_card.mpr ⟨r, hr_minus⟩
  have hkplus_pos : 1 ≤ kplus := by
    obtain ⟨w, _, hwmax⟩ := Finset.exists_max_image (Finset.univ : Finset Splus)
      (fun x => (T.induce (Splus : Set W)).dist ⟨r, hr_plus⟩ x) ⟨⟨r, hr_plus⟩, Finset.mem_univ _⟩
    refine Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => ?_⟩⟩
    have := hrank_p w y hy; have := hwmax y (Finset.mem_univ _); omega
  have hkminus_pos : 1 ≤ kminus := by
    obtain ⟨w, _, hwmax⟩ := Finset.exists_max_image (Finset.univ : Finset Sminus)
      (fun x => (T.induce (Sminus : Set W)).dist ⟨r, hr_minus⟩ x) ⟨⟨r, hr_minus⟩, Finset.mem_univ _⟩
    refine Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => ?_⟩⟩
    have := hrank_m w y hy; have := hwmax y (Finset.mem_univ _); omega
  let len_m := Sminus.card + kminus - 1
  let len_p := Splus.card + kplus - 1
  have htot_le : len_m + len_p - 1 ≤ Fintype.card V := by
    have : len_m + len_p - 1 ≤ 2 * n - 2 := by
      by_cases hp1 : Splus.card = 1
      · have hm1 : 1 < Sminus.card := by omega
        have := hkminus_strict hm1; omega
      · by_cases hm1 : Sminus.card = 1
        · have hp2 : 1 < Splus.card := by omega
          have := hkplus_strict hp2; omega
        · have := hkplus_strict (by omega); have := hkminus_strict (by omega); omega
    omega
  let r0 := len_m - 1
  -- Embed Dplus on [r0, r0 + len_p) with r ↦ r0!
  obtain ⟨fp, hfp_inj, hfp_rng, hfp_adj, hfp_root⟩ := greedy_right_interval Dplus
    ⟨fun x => (T.induce (Splus : Set W)).dist ⟨r, hr_plus⟩ x, hrank_p⟩ huniq_p
    G hR r0 len_p (by omega)
    (fun (_ : Fin 1) => ⟨r, hr_plus⟩) (fun a b _ => Subsingleton.elim a b)
    (fun w => by
      constructor
      · intro hno
        refine ⟨0, ?_⟩
        by_contra hne
        have hc := hin_plus w (Ne.symm hne)
        obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun y : Splus => Dplus.Adj y w)).card)
        exact hno y (Finset.mem_filter.mp hy).2
      · rintro ⟨_, rfl⟩; exact hr_noin_p)
    (by omega) 0 (by omega) (fun j hj => by omega)
    (by rw [Fintype.card_coe]; change Splus.card + kplus ≤ len_p + 1 + 0; omega)
  -- Embed Dminus on [0, r0] (hi = r0, len = len_m) with r ↦ r0!
  obtain ⟨fm, hfm_inj, hfm_rng, hfm_adj, hfm_root⟩ := greedy_left_interval Dminus
    ⟨fun x => (T.induce (Sminus : Set W)).dist ⟨r, hr_minus⟩ x, fun u v huv => hrank_m v u huv⟩
    (fun w u1 u2 h1 h2 => huniq_m w u1 u2 h1 h2)
    G hL r0 len_m (by omega) (by omega)
    (fun (_ : Fin 1) => ⟨r, hr_minus⟩) (fun a b _ => Subsingleton.elim a b)
    (fun w => by
      constructor
      · intro hno
        refine ⟨0, ?_⟩
        by_contra hne
        have hc := hin_minus w (Ne.symm hne)
        obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun y : Sminus => Dminus_rev.Adj y w)).card)
        exact hno y (Finset.mem_filter.mp hy).2
      · rintro ⟨_, rfl⟩; exact hr_noin_m)
    (by omega) 0 (by omega) (fun j hj => by omega)
    (by rw [Fintype.card_coe]; change Sminus.card + kminus ≤ len_m + 1 + 0; omega)
  have hfpr : fp ⟨r, hr_plus⟩ = ⟨r0, by omega⟩ := by simpa using hfp_root 0
  have hfmr : fm ⟨r, hr_minus⟩ = ⟨r0, by omega⟩ := by simpa using hfm_root 0
  -- Glue fp and fm!
  let idx : W → Fin (Fintype.card V) := fun w =>
    if h : w ∈ Splus then fp ⟨w, h⟩ else fm ⟨w, Finset.mem_compl.mpr (fun hwA => h (Finset.mem_insert_of_mem hwA))⟩
  have hidx_minus : ∀ w : W, (hw : w ∈ Sminus) → idx w = fm ⟨w, hw⟩ := by
    intro w hw
    by_cases hwp : w ∈ Splus
    · have hwr : w = r := (Finset.mem_insert.mp hwp).resolve_right (Finset.mem_compl.mp hw)
      subst hwr
      simp only [idx, hr_plus, ↓reduceDIte, hfpr, hfmr]
    · simp only [idx, hwp, ↓reduceDIte]
  refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ Splus <;> by_cases hv : v ∈ Splus
    · simp only [idx, hu, hv, ↓reduceDIte]
      exact hfp_adj ⟨u, hu⟩ ⟨v, hv⟩ huv
    · exfalso
      have huA : u ∈ A := by
        rcases Finset.mem_insert.mp hu with rfl | huA
        · have hvm : v ∈ Sminus := Finset.mem_compl.mpr (fun h => hv (Finset.mem_insert_of_mem h))
          exact absurd huv (hr_noin_m ⟨v, hvm⟩)
        · exact huA
      exact hT_nocross u huA v hv (hO.1 u v huv)
    · rcases Finset.mem_insert.mp hv with hvr | hvA
      · have hum : u ∈ Sminus := Finset.mem_compl.mpr (fun h => hu (Finset.mem_insert_of_mem h))
        rw [hvr] at huv ⊢
        rw [hidx_minus u hum, hidx_minus r hr_minus]
        exact hfm_adj ⟨u, hum⟩ ⟨r, hr_minus⟩ huv
      · exact absurd (hO.1 u v huv).symm (hT_nocross v hvA u hu)
    · have hum : u ∈ Sminus := Finset.mem_compl.mpr (fun h => hu (Finset.mem_insert_of_mem h))
      have hvm : v ∈ Sminus := Finset.mem_compl.mpr (fun h => hv (Finset.mem_insert_of_mem h))
      rw [hidx_minus u hum, hidx_minus v hvm]
      exact hfm_adj ⟨u, hum⟩ ⟨v, hvm⟩ huv
  · intro u v hEq
    have hi : idx u = idx v := σ.injective hEq
    by_cases hu : u ∈ Splus <;> by_cases hv : v ∈ Splus
    · simp only [idx, hu, hv, ↓reduceDIte] at hi
      exact congrArg Subtype.val (hfp_inj hi)
    · have hvm : v ∈ Sminus := Finset.mem_compl.mpr (fun h => hv (Finset.mem_insert_of_mem h))
      simp only [idx, hu, hv, ↓reduceDIte] at hi
      have h1 := (hfp_rng ⟨u, hu⟩).1
      have h2 := (hfm_rng ⟨v, hvm⟩).2
      have hfm_r : fm ⟨v, hvm⟩ = fm ⟨r, hr_minus⟩ := by
        rw [hfmr]; exact Fin.ext (by dsimp only; have := congrArg Fin.val hi; omega)
      have hvr : v = r := congrArg Subtype.val (hfm_inj hfm_r)
      exact absurd (hvr ▸ hr_plus) hv
    · have hum : u ∈ Sminus := Finset.mem_compl.mpr (fun h => hu (Finset.mem_insert_of_mem h))
      simp only [idx, hu, hv, ↓reduceDIte] at hi
      have h1 := (hfp_rng ⟨v, hv⟩).1
      have h2 := (hfm_rng ⟨u, hum⟩).2
      have hfm_r : fm ⟨u, hum⟩ = fm ⟨r, hr_minus⟩ := by
        rw [hfmr]; exact Fin.ext (by dsimp only; have := congrArg Fin.val hi; omega)
      have hur : u = r := congrArg Subtype.val (hfm_inj hfm_r)
      exact absurd (hur ▸ hr_plus) hu
    · have hum : u ∈ Sminus := Finset.mem_compl.mpr (fun h => hu (Finset.mem_insert_of_mem h))
      have hvm : v ∈ Sminus := Finset.mem_compl.mpr (fun h => hv (Finset.mem_insert_of_mem h))
      rw [hidx_minus u hum, hidx_minus v hvm] at hi
      exact congrArg Subtype.val (hfm_inj hi)

-- ============================================================================
-- Heart h = 2 Theorem (Theorem 4.2: improves Ai & Lian Aug 2026: 2n -> 2n-2,
-- and simultaneously subsumes all bi-arborescences and all double stars!)
-- ============================================================================

lemma embeds_heart_two {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hH2 : ∃ u v : W, D.Adj u v ∧ ∃ A : Finset W, u ∉ A ∧ v ∉ A ∧
      (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
      (∀ y : W, y ≠ u → y ≠ v → y ∉ A →
        (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
      (∀ x ∈ A, ∀ y : W, y ≠ u → y ≠ v → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) :
    Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  obtain ⟨u, v, hDuv, A, huA, hvA, hAin, hBout, hnocross⟩ := hH2
  have hTuv : T.Adj u v := hO.1 u v hDuv
  have huv_ne : u ≠ v := T.ne_of_adj hTuv
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  let Splus : Finset W := insert u (insert v A)
  let Sminus : Finset W := Aᶜ
  have hu_plus : u ∈ Splus := Finset.mem_insert_self u _
  have hv_plus : v ∈ Splus := Finset.mem_insert_of_mem (Finset.mem_insert_self v A)
  have hu_minus : u ∈ Sminus := Finset.mem_compl.mpr huA
  have hv_minus : v ∈ Sminus := Finset.mem_compl.mpr hvA
  have hT_nocross : ∀ x ∈ A, ∀ y ∉ Splus, ¬ T.Adj x y := by
    intro x hx y hy hTxy
    have hyu : y ≠ u := fun h => hy (h ▸ hu_plus)
    have hyv : y ≠ v := fun h => hy (h ▸ hv_plus)
    have hyA : y ∉ A := fun h => hy (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rcases adj_or_rev_of_isOrientation hO hTxy with h | h
    · exact (hnocross x hx y hyu hyv hyA).1 h
    · exact (hnocross x hx y hyu hyv hyA).2 h
  have hT_plus : (T.induce (Splus : Set W)).IsTree :=
    isTree_induce_of_edge_gate hT hu_plus hv_plus hTuv (fun x hx hxu hxv y hy => by
      have hxA : x ∈ A := by
        rcases Finset.mem_insert.mp hx with rfl | h1
        · exact absurd rfl hxu
        · rcases Finset.mem_insert.mp h1 with rfl | hxA
          · exact absurd rfl hxv
          · exact hxA
      exact hT_nocross x hxA y hy)
  have hT_minus : (T.induce (Sminus : Set W)).IsTree :=
    isTree_induce_of_edge_gate hT hu_minus hv_minus hTuv (fun y hy hyu hyv x hx hTyx => by
      have hxA : x ∈ A := not_not.mp (Finset.mem_compl.not.mp hx)
      have hy_notS : y ∉ Splus := fun h => by
        rcases Finset.mem_insert.mp h with rfl | h1
        · exact hyu rfl
        · rcases Finset.mem_insert.mp h1 with rfl | hyA
          · exact hyv rfl
          · exact Finset.mem_compl.mp hy hyA
      exact hT_nocross x hxA y hy_notS hTyx.symm)
  let Dplus : Digraph Splus := ⟨fun x y => D.Adj x.1 y.1⟩
  let Dminus : Digraph Sminus := ⟨fun x y => D.Adj x.1 y.1⟩
  let Dminus_rev : Digraph Sminus := ⟨fun x y => D.Adj y.1 x.1⟩
  have hO_plus : Dplus.IsOrientation (T.induce (Splus : Set W)) :=
    ⟨fun x y h => hO.1 x.1 y.1 h, fun x y h => hO.2 x.1 y.1 h⟩
  have hO_minus_rev : Dminus_rev.IsOrientation (T.induce (Sminus : Set W)) :=
    ⟨fun x y h => (hO.1 y.1 x.1 h).symm, fun x y h => hO.2 y.1 x.1 h.symm⟩
  -- For x ∈ Splus \ {u, v}, indeg_{Dplus}(x) = 1
  have hin_plus_A : ∀ x : Splus, x ≠ ⟨u, hu_plus⟩ → x ≠ ⟨v, hv_plus⟩ →
      (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card = 1 := by
    intro x hxu hxv
    have hxA : x.1 ∈ A := by
      rcases Finset.mem_insert.mp x.2 with h1 | h2
      · exact absurd (Subtype.ext h1) hxu
      · rcases Finset.mem_insert.mp h2 with h3 | hxA
        · exact absurd (Subtype.ext h3) hxv
        · exact hxA
    have hcard_all := hAin x.1 hxA
    have hbij : (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card =
        (Finset.univ.filter (fun z : W => D.Adj z x.1)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        have hDzx : D.Adj z x.1 := (Finset.mem_filter.mp hz).2
        have hzS : z ∈ Splus := by
          by_contra hznot
          exact hT_nocross x.1 hxA z hznot (hO.1 z x.1 hDzx).symm
        exact ⟨⟨z, hzS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDzx⟩, rfl⟩
    rw [hbij, hcard_all]
  -- Deduce indeg_{Dplus}(v) = 1 (and indeg_{Dplus}(u) = 0) from tree edge count!
  have hin_plus : ∀ x : Splus, x ≠ ⟨u, hu_plus⟩ →
      (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card = 1 := by
    have hsum := sum_indeg_eq_card_sub_one hT_plus hO_plus
    have huv_sub : (⟨u, hu_plus⟩ : Splus) ≠ ⟨v, hv_plus⟩ := fun h => huv_ne (congrArg Subtype.val h)
    have hsplit1 : ∑ x : Splus, (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card =
        (Finset.univ.filter (fun z : Splus => Dplus.Adj z ⟨u, hu_plus⟩)).card +
        ∑ x ∈ Finset.univ.erase ⟨u, hu_plus⟩,
          (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    have hv_mem_er : (⟨v, hv_plus⟩ : Splus) ∈ (Finset.univ : Finset Splus).erase ⟨u, hu_plus⟩ :=
      Finset.mem_erase.mpr ⟨huv_sub.symm, Finset.mem_univ _⟩
    have hsplit2 : ∑ x ∈ (Finset.univ : Finset Splus).erase ⟨u, hu_plus⟩,
          (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card =
        (Finset.univ.filter (fun z : Splus => Dplus.Adj z ⟨v, hv_plus⟩)).card +
        ∑ x ∈ ((Finset.univ : Finset Splus).erase ⟨u, hu_plus⟩).erase ⟨v, hv_plus⟩,
          (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card :=
      (Finset.add_sum_erase _ _ hv_mem_er).symm
    have hrest : ∑ x ∈ ((Finset.univ : Finset Splus).erase ⟨u, hu_plus⟩).erase ⟨v, hv_plus⟩,
          (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card = Fintype.card Splus - 2 := by
      rw [Finset.sum_congr rfl (fun x hx => by
        have h1 := Finset.mem_erase.mp hx
        have h2 := Finset.mem_erase.mp h1.2
        exact hin_plus_A x h2.1 h1.1)]
      simp only [Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hv_mem_er, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      omega
    have hv_ge : 1 ≤ (Finset.univ.filter (fun z : Splus => Dplus.Adj z ⟨v, hv_plus⟩)).card :=
      Finset.one_le_card.mpr ⟨⟨u, hu_plus⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDuv⟩⟩
    have hcard_ge2 : 2 ≤ Fintype.card Splus := by
      have : ({⟨u, hu_plus⟩, ⟨v, hv_plus⟩} : Finset Splus).card ≤ Fintype.card Splus :=
        Finset.card_le_univ _
      rw [Finset.card_pair huv_sub] at this; exact this
    have hsum' : ∑ x : Splus, (Finset.univ.filter (fun z : Splus => Dplus.Adj z x)).card =
        Fintype.card Splus - 1 :=
      sum_indeg_eq_card_sub_one (W := Splus) hT_plus hO_plus
    have hv_eq1 : (Finset.univ.filter (fun z : Splus => Dplus.Adj z ⟨v, hv_plus⟩)).card = 1 := by
      rw [hsplit1, hsplit2, hrest] at hsum'
      omega
    intro x hxu
    by_cases hxv : x = ⟨v, hv_plus⟩
    · exact hxv ▸ hv_eq1
    · exact hin_plus_A x hxu hxv
  -- Symmetrically for Dminus_rev with root v!
  have hin_minus_B : ∀ y : Sminus, y ≠ ⟨v, hv_minus⟩ → y ≠ ⟨u, hu_minus⟩ →
      (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card = 1 := by
    intro y hyv hyu
    have hyu' : y.1 ≠ u := fun h => hyu (Subtype.ext h)
    have hyv' : y.1 ≠ v := fun h => hyv (Subtype.ext h)
    have hyA : y.1 ∉ A := Finset.mem_compl.mp y.2
    have hcard_all := hBout y.1 hyu' hyv' hyA
    have hbij : (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card =
        (Finset.univ.filter (fun z : W => D.Adj y.1 z)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        have hDyz : D.Adj y.1 z := (Finset.mem_filter.mp hz).2
        have hzS : z ∈ Sminus := by
          by_contra hznot
          have hzA : z ∈ A := not_not.mp (Finset.mem_compl.not.mp hznot)
          exact (hnocross z hzA y.1 hyu' hyv' hyA).2 hDyz
        exact ⟨⟨z, hzS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDyz⟩, rfl⟩
    rw [hbij, hcard_all]
  have hin_minus : ∀ y : Sminus, y ≠ ⟨v, hv_minus⟩ →
      (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card = 1 := by
    have hsum := sum_indeg_eq_card_sub_one hT_minus hO_minus_rev
    have hvu_sub : (⟨v, hv_minus⟩ : Sminus) ≠ ⟨u, hu_minus⟩ := fun h => huv_ne (congrArg Subtype.val h).symm
    have hsplit1 : ∑ y : Sminus, (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card =
        (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z ⟨v, hv_minus⟩)).card +
        ∑ y ∈ Finset.univ.erase ⟨v, hv_minus⟩,
          (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    have hu_mem_er : (⟨u, hu_minus⟩ : Sminus) ∈ (Finset.univ : Finset Sminus).erase ⟨v, hv_minus⟩ :=
      Finset.mem_erase.mpr ⟨hvu_sub.symm, Finset.mem_univ _⟩
    have hsplit2 : ∑ y ∈ (Finset.univ : Finset Sminus).erase ⟨v, hv_minus⟩,
          (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card =
        (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z ⟨u, hu_minus⟩)).card +
        ∑ y ∈ ((Finset.univ : Finset Sminus).erase ⟨v, hv_minus⟩).erase ⟨u, hu_minus⟩,
          (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card :=
      (Finset.add_sum_erase _ _ hu_mem_er).symm
    have hrest : ∑ y ∈ ((Finset.univ : Finset Sminus).erase ⟨v, hv_minus⟩).erase ⟨u, hu_minus⟩,
          (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card = Fintype.card Sminus - 2 := by
      rw [Finset.sum_congr rfl (fun y hy => by
        have h1 := Finset.mem_erase.mp hy
        have h2 := Finset.mem_erase.mp h1.2
        exact hin_minus_B y h2.1 h1.1)]
      simp only [Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hu_mem_er, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      omega
    have hu_ge : 1 ≤ (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z ⟨u, hu_minus⟩)).card :=
      Finset.one_le_card.mpr ⟨⟨v, hv_minus⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDuv⟩⟩
    have hcard_ge2 : 2 ≤ Fintype.card Sminus := by
      have : ({⟨v, hv_minus⟩, ⟨u, hu_minus⟩} : Finset Sminus).card ≤ Fintype.card Sminus :=
        Finset.card_le_univ _
      rw [Finset.card_pair hvu_sub] at this; exact this
    have hsum' : ∑ y : Sminus, (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z y)).card =
        Fintype.card Sminus - 1 :=
      sum_indeg_eq_card_sub_one (W := Sminus) hT_minus hO_minus_rev
    have hu_eq1 : (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z ⟨u, hu_minus⟩)).card = 1 := by
      rw [hsplit1, hsplit2, hrest] at hsum'
      omega
    intro y hyv
    by_cases hyu : y = ⟨u, hu_minus⟩
    · exact hyu ▸ hu_eq1
    · exact hin_minus_B y hyv hyu
  obtain ⟨hr_noin_p, huniq_p, hrank_p⟩ := out_arborescence_rank_and_root hT_plus hO_plus ⟨u, hu_plus⟩ hin_plus
  obtain ⟨hr_noin_m, huniq_m, hrank_m⟩ := out_arborescence_rank_and_root hT_minus hO_minus_rev ⟨v, hv_minus⟩ hin_minus
  -- Define 2-root branchings Dplus' and Dminus' by deleting the single arc u -> v!
  let Dplus' : Digraph Splus := ⟨fun x y => Dplus.Adj x y ∧ ¬ (x = ⟨u, hu_plus⟩ ∧ y = ⟨v, hv_plus⟩)⟩
  let Dminus' : Digraph Sminus := ⟨fun x y => Dminus.Adj x y ∧ ¬ (x = ⟨u, hu_minus⟩ ∧ y = ⟨v, hv_minus⟩)⟩
  let kplus := (Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus.Adj x y)).card
  let kminus := (Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus.Adj y x)).card
  let qp : ℕ := if ∀ y : Splus, ¬ Dplus'.Adj ⟨u, hu_plus⟩ y then 1 else 0
  let qm : ℕ := if ∀ y : Sminus, ¬ Dminus'.Adj y ⟨v, hv_minus⟩ then 1 else 0
  have hSplus_card : Splus.card = A.card + 2 := by
    have hu_not : u ∉ insert v A := fun h => by
      rcases Finset.mem_insert.mp h with rfl | hu'
      · exact huv_ne rfl
      · exact huA hu'
    rw [Finset.card_insert_of_notMem hu_not, Finset.card_insert_of_notMem hvA]
  have hSminus_card : A.card + Sminus.card = n := by
    have := Finset.card_add_card_compl A
    change A.card + Sminus.card = Fintype.card W at this
    rw [hW] at this; exact this
  have hSminus_ge2 : 2 ≤ Sminus.card := by
    have hpair : ({u, v} : Finset W) ⊆ Sminus := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hu_minus
      · exact hv_minus
    have := Finset.card_le_card hpair
    rw [Finset.card_pair huv_ne] at this; exact this
  have hkplus_pos : 1 ≤ kplus := by
    obtain ⟨w, _, hwmax⟩ := Finset.exists_max_image (Finset.univ : Finset Splus)
      (fun x => (T.induce (Splus : Set W)).dist ⟨u, hu_plus⟩ x) ⟨⟨u, hu_plus⟩, Finset.mem_univ _⟩
    refine Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => ?_⟩⟩
    have := hrank_p w y hy; have := hwmax y (Finset.mem_univ _); omega
  have hkminus_pos : 1 ≤ kminus := by
    obtain ⟨w, _, hwmax⟩ := Finset.exists_max_image (Finset.univ : Finset Sminus)
      (fun x => (T.induce (Sminus : Set W)).dist ⟨v, hv_minus⟩ x) ⟨⟨v, hv_minus⟩, Finset.mem_univ _⟩
    refine Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => ?_⟩⟩
    have := hrank_m w y hy; have := hwmax y (Finset.mem_univ _); omega
  have hkplus_le : kplus ≤ Splus.card - 1 := by
    have hsub : Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus.Adj x y) ⊆
        Finset.univ.erase ⟨u, hu_plus⟩ := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq; subst heq
      exact (Finset.mem_filter.mp hx).2 ⟨v, hv_plus⟩ hDuv
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe] at hc
    exact hc
  have hkminus_le : kminus ≤ Sminus.card - 1 := by
    have hsub : Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus.Adj y x) ⊆
        Finset.univ.erase ⟨v, hv_minus⟩ := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq; subst heq
      exact (Finset.mem_filter.mp hx).2 ⟨u, hu_minus⟩ hDuv
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe] at hc
    exact hc
  -- Relate sinks of Dplus' to kplus + qp, and sources of Dminus' to kminus + qm!
  have hkp' : (Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus'.Adj x y)).card = kplus + qp := by
    let Sp := Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus.Adj x y)
    let Sp' := Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus'.Adj x y)
    have hu_not_Sp : (⟨u, hu_plus⟩ : Splus) ∉ Sp := fun h =>
      (Finset.mem_filter.mp h).2 ⟨v, hv_plus⟩ hDuv
    by_cases hqu : ∀ y : Splus, ¬ Dplus'.Adj ⟨u, hu_plus⟩ y
    · have hqp1 : qp = 1 := if_pos hqu
      have heq : Sp' = insert ⟨u, hu_plus⟩ Sp := by
        ext x; simp only [Sp', Sp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hxu : x = ⟨u, hu_plus⟩
        · subst hxu; simp [hqu]
        · constructor
          · intro h; right; intro y hy; exact h y ⟨hy, fun h0 => hxu h0.1⟩
          · rintro (rfl | h)
            · exact absurd rfl hxu
            · intro y hy; exact h y hy.1
      rw [show (Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus'.Adj x y)).card = Sp'.card from rfl,
        heq, Finset.card_insert_of_notMem hu_not_Sp, hqp1]
    · have hqp0 : qp = 0 := if_neg hqu
      have heq : Sp' = Sp := by
        ext x; simp only [Sp', Sp, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hxu : x = ⟨u, hu_plus⟩
        · subst hxu
          constructor
          · intro h; exact absurd h hqu
          · intro h; exact absurd h (fun h0 => h0 ⟨v, hv_plus⟩ hDuv)
        · constructor
          · intro h y hy; exact h y ⟨hy, fun h0 => hxu h0.1⟩
          · intro h y hy; exact h y hy.1
      rw [show (Finset.univ.filter (fun x : Splus => ∀ y : Splus, ¬ Dplus'.Adj x y)).card = Sp'.card from rfl,
        heq, hqp0, add_zero]
  have hkm' : (Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus'.Adj y x)).card = kminus + qm := by
    let Sm := Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus.Adj y x)
    let Sm' := Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus'.Adj y x)
    have hv_not_Sm : (⟨v, hv_minus⟩ : Sminus) ∉ Sm := fun h =>
      (Finset.mem_filter.mp h).2 ⟨u, hu_minus⟩ hDuv
    by_cases hqv : ∀ y : Sminus, ¬ Dminus'.Adj y ⟨v, hv_minus⟩
    · have hqm1 : qm = 1 := if_pos hqv
      have heq : Sm' = insert ⟨v, hv_minus⟩ Sm := by
        ext x; simp only [Sm', Sm, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hxv : x = ⟨v, hv_minus⟩
        · subst hxv; simp [hqv]
        · constructor
          · intro h; right; intro y hy; exact h y ⟨hy, fun h0 => hxv h0.2⟩
          · rintro (rfl | h)
            · exact absurd rfl hxv
            · intro y hy; exact h y hy.1
      rw [show (Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus'.Adj y x)).card = Sm'.card from rfl,
        heq, Finset.card_insert_of_notMem hv_not_Sm, hqm1]
    · have hqm0 : qm = 0 := if_neg hqv
      have heq : Sm' = Sm := by
        ext x; simp only [Sm', Sm, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hxv : x = ⟨v, hv_minus⟩
        · subst hxv
          constructor
          · intro h; exact absurd h hqv
          · intro h; exact absurd h (fun h0 => h0 ⟨u, hu_minus⟩ hDuv)
        · constructor
          · intro h y hy; exact h y ⟨hy, fun h0 => hxv h0.2⟩
          · intro h y hy; exact h y hy.1
      rw [show (Finset.univ.filter (fun x : Sminus => ∀ y : Sminus, ¬ Dminus'.Adj y x)).card = Sm'.card from rfl,
        heq, hqm0, add_zero]
  let len_m := Sminus.card + kminus - 1
  let len_p := Splus.card + kplus - 1
  let r0 := len_m - 2
  have hlen_m_ge2 : 2 ≤ len_m := by omega
  have hlen_p_ge2 : 2 ≤ len_p := by omega
  have htot_le : r0 + len_p ≤ Fintype.card V := by omega
  have hqp_le : qp ≤ 2 := by dsimp only [qp]; split_ifs <;> omega
  have hqm_le : qm ≤ 2 := by dsimp only [qm]; split_ifs <;> omega
  -- Embed Dplus' on [r0, r0 + len_p) with roots ![u, v] ↦ r0, r0 + 1!
  let roots_p : Fin 2 → Splus := fun j => if j.val = 0 then ⟨u, hu_plus⟩ else ⟨v, hv_plus⟩
  obtain ⟨fp, hfp_inj, hfp_rng, hfp_adj, hfp_root⟩ := greedy_right_interval Dplus'
    ⟨fun x => (T.induce (Splus : Set W)).dist ⟨u, hu_plus⟩ x, fun x y h => hrank_p x y h.1⟩
    (fun w z1 z2 h1 h2 => huniq_p w z1 z2 h1.1 h2.1)
    G hR r0 len_p htot_le roots_p
    (by
      intro a b h
      fin_cases a <;> fin_cases b
      · rfl
      · exfalso; exact huv_ne (congrArg Subtype.val h)
      · exfalso; exact huv_ne (congrArg Subtype.val h).symm
      · rfl)
    (fun w => by
      constructor
      · intro hno
        by_cases hwu : w = ⟨u, hu_plus⟩
        · exact ⟨⟨0, by omega⟩, by simp [roots_p, hwu]⟩
        · by_cases hwv : w = ⟨v, hv_plus⟩
          · exact ⟨⟨1, by omega⟩, by simp [roots_p, hwv]⟩
          · exfalso
            have hc := hin_plus w hwu
            obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : Splus => Dplus.Adj z w)).card)
            exact hno z ⟨(Finset.mem_filter.mp hz).2, fun h0 => hwv h0.2⟩
      · rintro ⟨j, rfl⟩ z hz
        fin_cases j
        · exact hr_noin_p z hz.1
        · have hz_eq : z = ⟨u, hu_plus⟩ := huniq_p ⟨v, hv_plus⟩ z ⟨u, hu_plus⟩ hz.1 hDuv
          exact hz.2 ⟨hz_eq, rfl⟩)
    hlen_p_ge2 qp hqp_le
    (fun j hj => by
      dsimp only [qp] at hj
      split_ifs at hj with hqu
      · have hj0 : j = 0 := Fin.ext (by omega)
        simpa [roots_p, hj0] using hqu
      · omega)
    (by rw [Fintype.card_coe, hkp']; omega)
  -- Embed Dminus' on [0, r0 + 1] (hi = r0 + 1, len = len_m) with roots ![v, u] ↦ r0 + 1, r0!
  let roots_m : Fin 2 → Sminus := fun j => if j.val = 0 then ⟨v, hv_minus⟩ else ⟨u, hu_minus⟩
  obtain ⟨fm, hfm_inj, hfm_rng, hfm_adj, hfm_root⟩ := greedy_left_interval Dminus'
    ⟨fun x => (T.induce (Sminus : Set W)).dist ⟨v, hv_minus⟩ x, fun x y h => hrank_m y x h.1⟩
    (fun w z1 z2 h1 h2 => huniq_m w z1 z2 h1.1 h2.1)
    G hL (r0 + 1) len_m (by omega) (by omega) roots_m
    (by
      intro a b h
      fin_cases a <;> fin_cases b
      · rfl
      · exfalso; exact huv_ne (congrArg Subtype.val h).symm
      · exfalso; exact huv_ne (congrArg Subtype.val h)
      · rfl)
    (fun w => by
      constructor
      · intro hno
        by_cases hwv : w = ⟨v, hv_minus⟩
        · exact ⟨⟨0, by omega⟩, by simp [roots_m, hwv]⟩
        · by_cases hwu : w = ⟨u, hu_minus⟩
          · exact ⟨⟨1, by omega⟩, by simp [roots_m, hwu]⟩
          · exfalso
            have hc := hin_minus w hwv
            obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : Sminus => Dminus_rev.Adj z w)).card)
            exact hno z ⟨(Finset.mem_filter.mp hz).2, fun h0 => hwu h0.1⟩
      · rintro ⟨j, rfl⟩ z hz
        fin_cases j
        · exact hr_noin_m z hz.1
        · have hz_eq : z = ⟨v, hv_minus⟩ := huniq_m ⟨u, hu_minus⟩ z ⟨v, hv_minus⟩ hz.1 hDuv
          exact hz.2 ⟨rfl, hz_eq⟩)
    hlen_m_ge2 qm hqm_le
    (fun j hj => by
      dsimp only [qm] at hj
      split_ifs at hj with hqv
      · have hj0 : j = 0 := Fin.ext (by omega)
        simpa [roots_m, hj0] using hqv
      · omega)
    (by rw [Fintype.card_coe, hkm']; omega)
  have hfpu : fp ⟨u, hu_plus⟩ = ⟨r0, by omega⟩ := by
    have := hfp_root ⟨0, by omega⟩; simpa [roots_p] using this
  have hfpv : fp ⟨v, hv_plus⟩ = ⟨r0 + 1, by omega⟩ := by
    have := hfp_root ⟨1, by omega⟩; simpa [roots_p] using this
  have hfmv : fm ⟨v, hv_minus⟩ = ⟨r0 + 1, by omega⟩ := by
    have := hfm_root ⟨0, by omega⟩; simpa [roots_m] using this
  have hfmu : fm ⟨u, hu_minus⟩ = ⟨r0, by omega⟩ := by
    have := hfm_root ⟨1, by omega⟩; simpa [roots_m] using this
  -- Glue fp and fm!
  let idx : W → Fin (Fintype.card V) := fun w =>
    if h : w ∈ Splus then fp ⟨w, h⟩
    else fm ⟨w, Finset.mem_compl.mpr (fun hwA => h (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwA)))⟩
  have hidx_minus : ∀ w : W, (hw : w ∈ Sminus) → idx w = fm ⟨w, hw⟩ := by
    intro w hw
    by_cases hwp : w ∈ Splus
    · rcases Finset.mem_insert.mp hwp with rfl | h1
      · simp only [idx, hu_plus, ↓reduceDIte, hfpu, hfmu]
      · rcases Finset.mem_insert.mp h1 with rfl | hwA
        · simp only [idx, hv_plus, ↓reduceDIte, hfpv, hfmv]
        · exact absurd hwA (Finset.mem_compl.mp hw)
    · simp only [idx, hwp, ↓reduceDIte]
  refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_⟩
  · intro x y hDxy
    by_cases hxy : x = u ∧ y = v
    · rcases hxy with ⟨rfl, rfl⟩
      simp only [idx, hu_plus, hv_plus, ↓reduceDIte, hfpu, hfpv]
      exact median_adj_succ hR ⟨r0, by omega⟩ (by dsimp only; omega)
    · by_cases hxA : x ∈ A
      · have hxS : x ∈ Splus := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxA)
        have hyS : y ∈ Splus := by
          by_contra hynot; exact hT_nocross x hxA y hynot (hO.1 x y hDxy)
        simp only [idx, hxS, hyS, ↓reduceDIte]
        exact hfp_adj ⟨x, hxS⟩ ⟨y, hyS⟩ ⟨hDxy, fun h0 =>
          hxy ⟨congrArg Subtype.val h0.1, congrArg Subtype.val h0.2⟩⟩
      · by_cases hyA : y ∈ A
        · have hyS : y ∈ Splus := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hyA)
          have hxS : x ∈ Splus := by
            by_contra hxnot; exact hT_nocross y hyA x hxnot (hO.1 x y hDxy).symm
          simp only [idx, hxS, hyS, ↓reduceDIte]
          exact hfp_adj ⟨x, hxS⟩ ⟨y, hyS⟩ ⟨hDxy, fun h0 =>
            hxy ⟨congrArg Subtype.val h0.1, congrArg Subtype.val h0.2⟩⟩
        · have hxm : x ∈ Sminus := Finset.mem_compl.mpr hxA
          have hym : y ∈ Sminus := Finset.mem_compl.mpr hyA
          rw [hidx_minus x hxm, hidx_minus y hym]
          exact hfm_adj ⟨x, hxm⟩ ⟨y, hym⟩ ⟨hDxy, fun h0 =>
            hxy ⟨congrArg Subtype.val h0.1, congrArg Subtype.val h0.2⟩⟩
  · intro x y hEq
    have hi : idx x = idx y := σ.injective hEq
    by_cases hx : x ∈ Splus <;> by_cases hy : y ∈ Splus
    · simp only [idx, hx, hy, ↓reduceDIte] at hi
      exact congrArg Subtype.val (hfp_inj hi)
    · have hym : y ∈ Sminus := Finset.mem_compl.mpr (fun h => hy (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
      simp only [idx, hx, hy, ↓reduceDIte] at hi
      have h1 := (hfp_rng ⟨x, hx⟩).1
      have h2 := (hfm_rng ⟨y, hym⟩).2
      have hval : (fm ⟨y, hym⟩).val = r0 ∨ (fm ⟨y, hym⟩).val = r0 + 1 := by
        have := congrArg Fin.val hi; omega
      rcases hval with h0 | h1'
      · have hfm_u : fm ⟨y, hym⟩ = fm ⟨u, hu_minus⟩ := by
          rw [hfmu]; exact Fin.ext (by dsimp only; exact h0)
        have hyu : y = u := congrArg Subtype.val (hfm_inj hfm_u)
        exact absurd (hyu ▸ hu_plus) hy
      · have hfm_v : fm ⟨y, hym⟩ = fm ⟨v, hv_minus⟩ := by
          rw [hfmv]; exact Fin.ext (by dsimp only; exact h1')
        have hyv : y = v := congrArg Subtype.val (hfm_inj hfm_v)
        exact absurd (hyv ▸ hv_plus) hy
    · have hxm : x ∈ Sminus := Finset.mem_compl.mpr (fun h => hx (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
      simp only [idx, hx, hy, ↓reduceDIte] at hi
      have h1 := (hfp_rng ⟨y, hy⟩).1
      have h2 := (hfm_rng ⟨x, hxm⟩).2
      have hval : (fm ⟨x, hxm⟩).val = r0 ∨ (fm ⟨x, hxm⟩).val = r0 + 1 := by
        have := congrArg Fin.val hi; omega
      rcases hval with h0 | h1'
      · have hfm_u : fm ⟨x, hxm⟩ = fm ⟨u, hu_minus⟩ := by
          rw [hfmu]; exact Fin.ext (by dsimp only; exact h0)
        have hxu : x = u := congrArg Subtype.val (hfm_inj hfm_u)
        exact absurd (hxu ▸ hu_plus) hx
      · have hfm_v : fm ⟨x, hxm⟩ = fm ⟨v, hv_minus⟩ := by
          rw [hfmv]; exact Fin.ext (by dsimp only; exact h1')
        have hxv : x = v := congrArg Subtype.val (hfm_inj hfm_v)
        exact absurd (hxv ▸ hv_plus) hx
    · have hxm : x ∈ Sminus := Finset.mem_compl.mpr (fun h => hx (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
      have hym : y ∈ Sminus := Finset.mem_compl.mpr (fun h => hy (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
      rw [hidx_minus x hxm, hidx_minus y hym] at hi
      exact congrArg Subtype.val (hfm_inj hi)

end Module4A

-- ============================================================================
-- MODULE 4B: Trees with at most 3 internal vertices (m = n - k <= 3)
-- ============================================================================

section Module4B

lemma alloc_three_buckets {W : Type*} [DecidableEq W] {U : Type*} [DecidableEq U]
    {S0 S1 S2 : Finset W} (hd01 : Disjoint S0 S1) (hd02 : Disjoint S0 S2) (hd12 : Disjoint S1 S2)
    {P0 P1 P2 : Finset U}
    (h0 : S0.card ≤ P0.card)
    (h1 : S0.card + S1.card ≤ P1.card)
    (h2 : S0.card + S1.card + S2.card ≤ P2.card) :
    ∃ g : ↥(S0 ∪ S1 ∪ S2) → U,
      Function.Injective g ∧
      (∀ w : ↥(S0 ∪ S1 ∪ S2), w.1 ∈ S0 → g w ∈ P0) ∧
      (∀ w : ↥(S0 ∪ S1 ∪ S2), w.1 ∈ S1 → g w ∈ P1) ∧
      (∀ w : ↥(S0 ∪ S1 ∪ S2), w.1 ∈ S2 → g w ∈ P2) := by
  classical
  obtain ⟨A0, hA0sub, hA0card⟩ := Finset.exists_subset_card_eq h0
  have h1' : S1.card ≤ (P1 \ A0).card := by
    have := Finset.le_card_sdiff A0 P1; omega
  obtain ⟨A1, hA1sub, hA1card⟩ := Finset.exists_subset_card_eq h1'
  have h2' : S2.card ≤ (P2 \ (A0 ∪ A1)).card := by
    have := Finset.le_card_sdiff (A0 ∪ A1) P2
    have hu := Finset.card_union_le A0 A1
    omega
  obtain ⟨A2, hA2sub, hA2card⟩ := Finset.exists_subset_card_eq h2'
  have hA1P1 : A1 ⊆ P1 := fun u hu => (Finset.mem_sdiff.mp (hA1sub hu)).1
  have hA2P2 : A2 ⊆ P2 := fun u hu => (Finset.mem_sdiff.mp (hA2sub hu)).1
  have hdisj01 : Disjoint A0 A1 := Finset.disjoint_left.mpr (fun u hu0 hu1 =>
    (Finset.mem_sdiff.mp (hA1sub hu1)).2 hu0)
  have hdisj02 : Disjoint A0 A2 := Finset.disjoint_left.mpr (fun u hu0 hu2 =>
    (Finset.mem_sdiff.mp (hA2sub hu2)).2 (Finset.mem_union_left A1 hu0))
  have hdisj12 : Disjoint A1 A2 := Finset.disjoint_left.mpr (fun u hu1 hu2 =>
    (Finset.mem_sdiff.mp (hA2sub hu2)).2 (Finset.mem_union_right A0 hu1))
  let e0 : S0 ≃ A0 := Fintype.equivOfCardEq (by simp [hA0card])
  let e1 : S1 ≃ A1 := Fintype.equivOfCardEq (by simp [hA1card])
  let e2 : S2 ≃ A2 := Fintype.equivOfCardEq (by simp [hA2card])
  have hmem2 : ∀ w : ↥(S0 ∪ S1 ∪ S2), w.1 ∉ S0 → w.1 ∉ S1 → w.1 ∈ S2 := by
    intro w h0n h1n
    rcases Finset.mem_union.mp w.2 with h01 | h2m
    · rcases Finset.mem_union.mp h01 with h0m | h1m
      · exact absurd h0m h0n
      · exact absurd h1m h1n
    · exact h2m
  let g : ↥(S0 ∪ S1 ∪ S2) → U := fun w =>
    if h0m : w.1 ∈ S0 then (e0 ⟨w.1, h0m⟩).1
    else if h1m : w.1 ∈ S1 then (e1 ⟨w.1, h1m⟩).1
    else (e2 ⟨w.1, hmem2 w h0m h1m⟩).1
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx0 : x.1 ∈ S0 <;> by_cases hy0 : y.1 ∈ S0
    · simp only [g, hx0, hy0, ↓reduceDIte] at hxy
      have h := e0.injective (Subtype.ext hxy)
      exact Subtype.ext (congrArg (fun z : S0 => z.1) h)
    · exfalso
      by_cases hy1 : y.1 ∈ S1
      · simp only [g, hx0, hy0, hy1, ↓reduceDIte] at hxy
        exact Finset.disjoint_left.mp hdisj01 (e0 ⟨x.1, hx0⟩).2 (hxy ▸ (e1 ⟨y.1, hy1⟩).2)
      · simp only [g, hx0, hy0, hy1, ↓reduceDIte] at hxy
        exact Finset.disjoint_left.mp hdisj02 (e0 ⟨x.1, hx0⟩).2 (hxy ▸ (e2 ⟨y.1, hmem2 y hy0 hy1⟩).2)
    · exfalso
      by_cases hx1 : x.1 ∈ S1
      · simp only [g, hx0, hy0, hx1, ↓reduceDIte] at hxy
        exact Finset.disjoint_left.mp hdisj01 (e0 ⟨y.1, hy0⟩).2 (hxy.symm ▸ (e1 ⟨x.1, hx1⟩).2)
      · simp only [g, hx0, hy0, hx1, ↓reduceDIte] at hxy
        exact Finset.disjoint_left.mp hdisj02 (e0 ⟨y.1, hy0⟩).2 (hxy.symm ▸ (e2 ⟨x.1, hmem2 x hx0 hx1⟩).2)
    · by_cases hx1 : x.1 ∈ S1 <;> by_cases hy1 : y.1 ∈ S1
      · simp only [g, hx0, hy0, hx1, hy1, ↓reduceDIte] at hxy
        have h := e1.injective (Subtype.ext hxy)
        exact Subtype.ext (congrArg (fun z : S1 => z.1) h)
      · exfalso
        simp only [g, hx0, hy0, hx1, hy1, ↓reduceDIte] at hxy
        exact Finset.disjoint_left.mp hdisj12 (e1 ⟨x.1, hx1⟩).2 (hxy ▸ (e2 ⟨y.1, hmem2 y hy0 hy1⟩).2)
      · exfalso
        simp only [g, hx0, hy0, hx1, hy1, ↓reduceDIte] at hxy
        exact Finset.disjoint_left.mp hdisj12 (e1 ⟨y.1, hy1⟩).2 (hxy.symm ▸ (e2 ⟨x.1, hmem2 x hx0 hx1⟩).2)
      · simp only [g, hx0, hy0, hx1, hy1, ↓reduceDIte] at hxy
        have h := e2.injective (Subtype.ext hxy)
        exact Subtype.ext (congrArg (fun z : S2 => z.1) h)
  · intro w hw0
    simp only [g, hw0, ↓reduceDIte]
    exact hA0sub (e0 ⟨w.1, hw0⟩).2
  · intro w hw1
    have hw0 : w.1 ∉ S0 := Finset.disjoint_right.mp hd01 hw1
    simp only [g, hw0, hw1, ↓reduceDIte]
    exact hA1P1 (e1 ⟨w.1, hw1⟩).2
  · intro w hw2
    have hw0 : w.1 ∉ S0 := Finset.disjoint_right.mp hd02 hw2
    have hw1 : w.1 ∉ S1 := Finset.disjoint_right.mp hd12 hw2
    simp only [g, hw0, hw1, ↓reduceDIte]
    exact hA2P2 (e2 ⟨w.1, hmem2 w hw0 hw1⟩).2

lemma median_card_in_lt_ge {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (t : Fin (Fintype.card V)) :
    t.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      k.val < t.val ∧ G.Adj (σ k) (σ t))).card := by
  classical
  by_cases ht : t.val = 0
  · omega
  · let i0 : Fin (Fintype.card V) := ⟨0, by omega⟩
    have hi0t : i0 < t := by change 0 < t.val; omega
    have h := hL i0 t hi0t
    have heq : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i0 ≤ k ∧ k < t ∧ G.Adj (σ k) (σ t)) =
      Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        k.val < t.val ∧ G.Adj (σ k) (σ t)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h0le : i0 ≤ k := Nat.zero_le k.val
      exact ⟨fun hk => ⟨hk.2.1, hk.2.2⟩, fun hk => ⟨h0le, hk.1, hk.2⟩⟩
    rw [heq] at h
    have hi0v : i0.val = 0 := rfl
    omega

lemma median_card_out_gt_ge {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (t : Fin (Fintype.card V)) :
    Fintype.card V - 1 - t.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      t.val < k.val ∧ G.Adj (σ t) (σ k))).card := by
  classical
  by_cases ht : t.val + 1 = Fintype.card V
  · omega
  · have hpos : 0 < Fintype.card V := by have := t.isLt; omega
    let j0 : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
    have htj0 : t < j0 := by change t.val < Fintype.card V - 1; have := t.isLt; omega
    have h := hR t j0 htj0
    have heq : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        t < k ∧ k ≤ j0 ∧ G.Adj (σ t) (σ k)) =
      Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        t.val < k.val ∧ G.Adj (σ t) (σ k)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hle : k ≤ j0 := by change k.val ≤ Fintype.card V - 1; have := k.isLt; omega
      exact ⟨fun hk => ⟨hk.1, hk.2.2⟩, fun hk => ⟨hk.1, hle, hk.2⟩⟩
    rw [heq] at h
    have hj0v : j0.val = Fintype.card V - 1 := rfl
    omega

lemma embeds_rev {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (h : Embeds (⟨fun u v => D.Adj v u⟩ : Digraph W) (⟨fun u v => G.Adj v u⟩ : Digraph V)) :
    Embeds D G := by
  obtain ⟨f, hfinj⟩ := h
  exact ⟨⟨f, fun huv => f.map_adj' huv⟩, hfinj⟩

-- Shared glue lemma for 3-internal-vertex trees (m = 3):
-- Given distinct core vertices v0, v1, v2 embedded at distinct target vertices t0, t1, t2,
-- and disjoint injections on in-leaves and out-leaves avoiding {t0, t1, t2}, assemble Embeds D G!
lemma glue_three_core {W : Type} [Fintype W] [DecidableEq W]
    {D : Digraph W} [DecidableRel D.Adj]
    {T : SimpleGraph W} (_hO : D.IsOrientation T)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    {v0 v1 v2 : W} (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2)
    {Lplus Lminus : Finset W}
    (hpart : ∀ w : W, w = v0 ∨ w = v1 ∨ w = v2 ∨ w ∈ Lplus ∨ w ∈ Lminus)
    (hdisj_p : v0 ∉ Lplus ∧ v1 ∉ Lplus ∧ v2 ∉ Lplus)
    (hdisj_m : v0 ∉ Lminus ∧ v1 ∉ Lminus ∧ v2 ∉ Lminus)
    (hdisj_pm : Disjoint Lplus Lminus)
    (hno_leaf_leaf : ∀ x y : W, (x ∈ Lplus ∨ x ∈ Lminus) → (y ∈ Lplus ∨ y ∈ Lminus) → ¬ D.Adj x y)
    (hLp_in : ∀ x ∈ Lplus, ∀ y : W, ¬ D.Adj x y)
    (hLm_out : ∀ x ∈ Lminus, ∀ y : W, ¬ D.Adj y x)
    {t0 t1 t2 : V} (ht01 : t0 ≠ t1) (ht02 : t0 ≠ t2) (ht12 : t1 ≠ t2)
    (hcore_adj : ∀ a b : W, (a = v0 ∨ a = v1 ∨ a = v2) → (b = v0 ∨ b = v1 ∨ b = v2) →
      D.Adj a b → G.Adj (if a = v0 then t0 else if a = v1 then t1 else t2)
        (if b = v0 then t0 else if b = v1 then t1 else t2))
    (gR : ↥Lplus → V) (hgR_inj : Function.Injective gR)
    (hgR_avoid : ∀ w : ↥Lplus, gR w ≠ t0 ∧ gR w ≠ t1 ∧ gR w ≠ t2)
    (hgR_adj : ∀ w : ↥Lplus,
      (D.Adj v0 w.1 → G.Adj t0 (gR w)) ∧
      (D.Adj v1 w.1 → G.Adj t1 (gR w)) ∧
      (D.Adj v2 w.1 → G.Adj t2 (gR w)))
    (gL : ↥Lminus → V) (hgL_inj : Function.Injective gL)
    (hgL_avoid : ∀ w : ↥Lminus, gL w ≠ t0 ∧ gL w ≠ t1 ∧ gL w ≠ t2)
    (hgL_adj : ∀ w : ↥Lminus,
      (D.Adj w.1 v0 → G.Adj (gL w) t0) ∧
      (D.Adj w.1 v1 → G.Adj (gL w) t1) ∧
      (D.Adj w.1 v2 → G.Adj (gL w) t2))
    (hgLR_disj : ∀ (x : ↥Lplus) (y : ↥Lminus), gR x ≠ gL y) :
    Embeds D G := by
  classical
  have hmem_m : ∀ w : W, w ≠ v0 → w ≠ v1 → w ≠ v2 → w ∉ Lplus → w ∈ Lminus := by
    intro w h0 h1 h2 hp
    rcases hpart w with rfl | rfl | rfl | hpm | hmm
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd hpm hp
    · exact hmm
  let f : W → V := fun w =>
    if h0 : w = v0 then t0
    else if h1 : w = v1 then t1
    else if h2 : w = v2 then t2
    else if hp : w ∈ Lplus then gR ⟨w, hp⟩
    else gL ⟨w, hmem_m w h0 h1 h2 hp⟩
  have hf_v0 : f v0 = t0 := by simp [f]
  have hf_v1 : f v1 = t1 := by simp [f, h01.symm]
  have hf_v2 : f v2 = t2 := by simp [f, h02.symm, h12.symm]
  have hf_Lp : ∀ w : W, (hp : w ∈ Lplus) → f w = gR ⟨w, hp⟩ := by
    intro w hp
    have h0 : w ≠ v0 := fun h => hdisj_p.1 (h ▸ hp)
    have h1 : w ≠ v1 := fun h => hdisj_p.2.1 (h ▸ hp)
    have h2 : w ≠ v2 := fun h => hdisj_p.2.2 (h ▸ hp)
    simp only [f, h0, h1, h2, hp, ↓reduceDIte]
  have hf_Lm : ∀ w : W, (hm : w ∈ Lminus) → f w = gL ⟨w, hm⟩ := by
    intro w hm
    have h0 : w ≠ v0 := fun h => hdisj_m.1 (h ▸ hm)
    have h1 : w ≠ v1 := fun h => hdisj_m.2.1 (h ▸ hm)
    have h2 : w ≠ v2 := fun h => hdisj_m.2.2 (h ▸ hm)
    have hp : w ∉ Lplus := Finset.disjoint_right.mp hdisj_pm hm
    simp only [f, h0, h1, h2, hp, ↓reduceDIte]
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro a b hab
    have hcore_eq : ∀ x : W, x = v0 ∨ x = v1 ∨ x = v2 →
        f x = (if x = v0 then t0 else if x = v1 then t1 else t2) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · simp [hf_v0]
      · simp [hf_v1, h01.symm]
      · simp [hf_v2, h02.symm, h12.symm]
    rcases hpart a with haM | haM | haM | haP | haM'
    · rcases hpart b with hbM | hbM | hbM | hbP | hbM'
      · rw [hcore_eq a (Or.inl haM), hcore_eq b (Or.inl hbM)]
        exact hcore_adj a b (Or.inl haM) (Or.inl hbM) hab
      · rw [hcore_eq a (Or.inl haM), hcore_eq b (Or.inr (Or.inl hbM))]
        exact hcore_adj a b (Or.inl haM) (Or.inr (Or.inl hbM)) hab
      · rw [hcore_eq a (Or.inl haM), hcore_eq b (Or.inr (Or.inr hbM))]
        exact hcore_adj a b (Or.inl haM) (Or.inr (Or.inr hbM)) hab
      · rw [haM, hf_v0, hf_Lp b hbP]; exact (hgR_adj ⟨b, hbP⟩).1 (haM ▸ hab)
      · exact absurd hab (hLm_out b hbM' a)
    · rcases hpart b with hbM | hbM | hbM | hbP | hbM'
      · rw [hcore_eq a (Or.inr (Or.inl haM)), hcore_eq b (Or.inl hbM)]
        exact hcore_adj a b (Or.inr (Or.inl haM)) (Or.inl hbM) hab
      · rw [hcore_eq a (Or.inr (Or.inl haM)), hcore_eq b (Or.inr (Or.inl hbM))]
        exact hcore_adj a b (Or.inr (Or.inl haM)) (Or.inr (Or.inl hbM)) hab
      · rw [hcore_eq a (Or.inr (Or.inl haM)), hcore_eq b (Or.inr (Or.inr hbM))]
        exact hcore_adj a b (Or.inr (Or.inl haM)) (Or.inr (Or.inr hbM)) hab
      · rw [haM, hf_v1, hf_Lp b hbP]; exact (hgR_adj ⟨b, hbP⟩).2.1 (haM ▸ hab)
      · exact absurd hab (hLm_out b hbM' a)
    · rcases hpart b with hbM | hbM | hbM | hbP | hbM'
      · rw [hcore_eq a (Or.inr (Or.inr haM)), hcore_eq b (Or.inl hbM)]
        exact hcore_adj a b (Or.inr (Or.inr haM)) (Or.inl hbM) hab
      · rw [hcore_eq a (Or.inr (Or.inr haM)), hcore_eq b (Or.inr (Or.inl hbM))]
        exact hcore_adj a b (Or.inr (Or.inr haM)) (Or.inr (Or.inl hbM)) hab
      · rw [hcore_eq a (Or.inr (Or.inr haM)), hcore_eq b (Or.inr (Or.inr hbM))]
        exact hcore_adj a b (Or.inr (Or.inr haM)) (Or.inr (Or.inr hbM)) hab
      · rw [haM, hf_v2, hf_Lp b hbP]; exact (hgR_adj ⟨b, hbP⟩).2.2 (haM ▸ hab)
      · exact absurd hab (hLm_out b hbM' a)
    · exact absurd hab (hLp_in a haP b)
    · rcases hpart b with hbM | hbM | hbM | hbP | hbM'
      · rw [hf_Lm a haM', hbM, hf_v0]; exact (hgL_adj ⟨a, haM'⟩).1 (hbM ▸ hab)
      · rw [hf_Lm a haM', hbM, hf_v1]; exact (hgL_adj ⟨a, haM'⟩).2.1 (hbM ▸ hab)
      · rw [hf_Lm a haM', hbM, hf_v2]; exact (hgL_adj ⟨a, haM'⟩).2.2 (hbM ▸ hab)
      · exact absurd hab (hno_leaf_leaf a b (Or.inr haM') (Or.inl hbP))
      · exact absurd hab (hno_leaf_leaf a b (Or.inr haM') (Or.inr hbM'))
  · intro a b hEq
    change f a = f b at hEq
    rcases hpart a with rfl | rfl | rfl | haP | haM <;>
    rcases hpart b with rfl | rfl | rfl | hbP | hbM
    · rfl
    · rw [hf_v0, hf_v1] at hEq; exact absurd hEq ht01
    · rw [hf_v0, hf_v2] at hEq; exact absurd hEq ht02
    · rw [hf_v0, hf_Lp b hbP] at hEq; exact absurd hEq.symm (hgR_avoid ⟨b, hbP⟩).1
    · rw [hf_v0, hf_Lm b hbM] at hEq; exact absurd hEq.symm (hgL_avoid ⟨b, hbM⟩).1
    · rw [hf_v1, hf_v0] at hEq; exact absurd hEq.symm ht01
    · rfl
    · rw [hf_v1, hf_v2] at hEq; exact absurd hEq ht12
    · rw [hf_v1, hf_Lp b hbP] at hEq; exact absurd hEq.symm (hgR_avoid ⟨b, hbP⟩).2.1
    · rw [hf_v1, hf_Lm b hbM] at hEq; exact absurd hEq.symm (hgL_avoid ⟨b, hbM⟩).2.1
    · rw [hf_v2, hf_v0] at hEq; exact absurd hEq.symm ht02
    · rw [hf_v2, hf_v1] at hEq; exact absurd hEq.symm ht12
    · rfl
    · rw [hf_v2, hf_Lp b hbP] at hEq; exact absurd hEq.symm (hgR_avoid ⟨b, hbP⟩).2.2
    · rw [hf_v2, hf_Lm b hbM] at hEq; exact absurd hEq.symm (hgL_avoid ⟨b, hbM⟩).2.2
    · rw [hf_Lp a haP, hf_v0] at hEq; exact absurd hEq (hgR_avoid ⟨a, haP⟩).1
    · rw [hf_Lp a haP, hf_v1] at hEq; exact absurd hEq (hgR_avoid ⟨a, haP⟩).2.1
    · rw [hf_Lp a haP, hf_v2] at hEq; exact absurd hEq (hgR_avoid ⟨a, haP⟩).2.2
    · rw [hf_Lp a haP, hf_Lp b hbP] at hEq; exact congrArg Subtype.val (hgR_inj hEq)
    · rw [hf_Lp a haP, hf_Lm b hbM] at hEq; exact absurd hEq (hgLR_disj ⟨a, haP⟩ ⟨b, hbM⟩)
    · rw [hf_Lm a haM, hf_v0] at hEq; exact absurd hEq (hgL_avoid ⟨a, haM⟩).1
    · rw [hf_Lm a haM, hf_v1] at hEq; exact absurd hEq (hgL_avoid ⟨a, haM⟩).2.1
    · rw [hf_Lm a haM, hf_v2] at hEq; exact absurd hEq (hgL_avoid ⟨a, haM⟩).2.2
    · rw [hf_Lm a haM, hf_Lp b hbP] at hEq; exact absurd hEq.symm (hgLR_disj ⟨b, hbP⟩ ⟨a, haM⟩)
    · rw [hf_Lm a haM, hf_Lm b hbM] at hEq; exact congrArg Subtype.val (hgL_inj hEq)

-- Helper: S_3^+ core (y -> x, y -> z) with leaves Lplus and Lminus
lemma embeds_three_core_S3plus {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n)
    {T : SimpleGraph W} (hO : D.IsOrientation T)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    {y x z : W} (hyx : y ≠ x) (hyz : y ≠ z) (hxz : x ≠ z)
    (hDyx : D.Adj y x) (hDyz : D.Adj y z) (hno_xz : ¬ D.Adj x z ∧ ¬ D.Adj z x)
    {Lplus Lminus : Finset W}
    (hpart : ∀ w : W, w = y ∨ w = x ∨ w = z ∨ w ∈ Lplus ∨ w ∈ Lminus)
    (hdisj_p : y ∉ Lplus ∧ x ∉ Lplus ∧ z ∉ Lplus)
    (hdisj_m : y ∉ Lminus ∧ x ∉ Lminus ∧ z ∉ Lminus)
    (hdisj_pm : Disjoint Lplus Lminus)
    (hno_leaf_leaf : ∀ a b : W, (a ∈ Lplus ∨ a ∈ Lminus) → (b ∈ Lplus ∨ b ∈ Lminus) → ¬ D.Adj a b)
    (hLp_in : ∀ a ∈ Lplus, ∀ b : W, ¬ D.Adj a b)
    (hLm_out : ∀ a ∈ Lminus, ∀ b : W, ¬ D.Adj b a)
    (hLp_uniq : ∀ w ∈ Lplus, (D.Adj y w ∧ ¬ D.Adj x w ∧ ¬ D.Adj z w) ∨
      (D.Adj x w ∧ ¬ D.Adj y w ∧ ¬ D.Adj z w) ∨ (D.Adj z w ∧ ¬ D.Adj y w ∧ ¬ D.Adj x w))
    (hLm_uniq : ∀ w ∈ Lminus, (D.Adj w y ∧ ¬ D.Adj w x ∧ ¬ D.Adj w z) ∨
      (D.Adj w x ∧ ¬ D.Adj w y ∧ ¬ D.Adj w z) ∨ (D.Adj w z ∧ ¬ D.Adj w y ∧ ¬ D.Adj w x)) :
    Embeds D G := by
  classical
  -- WLOG bz <= bx (if bx < bz, swap x and z!)
  have hmain : ∀ (x' z' : W), y ≠ x' → y ≠ z' → x' ≠ z' →
      D.Adj y x' → D.Adj y z' → (¬ D.Adj x' z' ∧ ¬ D.Adj z' x') →
      (∀ w : W, w = y ∨ w = x' ∨ w = z' ∨ w ∈ Lplus ∨ w ∈ Lminus) →
      (y ∉ Lplus ∧ x' ∉ Lplus ∧ z' ∉ Lplus) →
      (y ∉ Lminus ∧ x' ∉ Lminus ∧ z' ∉ Lminus) →
      (∀ w ∈ Lplus, (D.Adj y w ∧ ¬ D.Adj x' w ∧ ¬ D.Adj z' w) ∨
        (D.Adj x' w ∧ ¬ D.Adj y w ∧ ¬ D.Adj z' w) ∨ (D.Adj z' w ∧ ¬ D.Adj y w ∧ ¬ D.Adj x' w)) →
      (∀ w ∈ Lminus, (D.Adj w y ∧ ¬ D.Adj w x' ∧ ¬ D.Adj w z') ∨
        (D.Adj w x' ∧ ¬ D.Adj w y ∧ ¬ D.Adj w z') ∨ (D.Adj w z' ∧ ¬ D.Adj w y ∧ ¬ D.Adj w x')) →
      (Lminus.filter (fun w => D.Adj w z')).card ≤ (Lminus.filter (fun w => D.Adj w x')).card →
      Embeds D G := by
    intro x' z' hyx' hyz' hxz' hDyx' hDyz' hnoxz' hpart' hdp' hdm' hLpu' hLmu' hbz_le
    let A := Lplus.card
    let B := Lminus.card
    have hn_eq : n = A + B + 3 := by
      let M : Finset W := {y, x', z'}
      have hMcard : M.card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hxz']
        · simp [hyx', hyz']
      have hd1 : Disjoint M Lplus := Finset.disjoint_left.mpr (fun w hw => by
        simp only [M, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hdp'.1
        · exact hdp'.2.1
        · exact hdp'.2.2)
      have hd2 : Disjoint (M ∪ Lplus) Lminus := Finset.disjoint_left.mpr (fun w hw => by
        rcases Finset.mem_union.mp hw with hwM | hwP
        · simp only [M, Finset.mem_insert, Finset.mem_singleton] at hwM
          rcases hwM with rfl | rfl | rfl
          · exact hdm'.1
          · exact hdm'.2.1
          · exact hdm'.2.2
        · exact Finset.disjoint_left.mp hdisj_pm hwP)
      have huniv : M ∪ Lplus ∪ Lminus = Finset.univ := by
        ext w; simp only [Finset.mem_union, Finset.mem_univ, iff_true, M,
          Finset.mem_insert, Finset.mem_singleton]
        rcases hpart' w with rfl | rfl | rfl | h | h <;> tauto
      have hc := congrArg Finset.card huniv
      rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hMcard, Finset.card_univ, hW] at hc
      omega
    obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
    have hV_eq : Fintype.card V = 2 * A + 2 * B + 4 := by omega
    let i0 : Fin (Fintype.card V) := ⟨2 * B, by omega⟩
    let i1 : Fin (Fintype.card V) := ⟨2 * B + 1, by omega⟩
    let i2 : Fin (Fintype.card V) := ⟨2 * B + 2, by omega⟩
    let i3 : Fin (Fintype.card V) := ⟨2 * B + 3, by omega⟩
    have h01_adj : G.Adj (σ i0) (σ i1) := median_adj_succ hR i0 (by dsimp only [i0]; omega)
    -- Partition Lminus into Sz, Sx, Sy and Lplus into Ry, Rx, Rz
    let Sz := Lminus.filter (fun w => D.Adj w z')
    let Sx := Lminus.filter (fun w => D.Adj w x')
    let Sy := Lminus.filter (fun w => D.Adj w y)
    have hS_eq : Sz ∪ Sx ∪ Sy = Lminus := by
      ext w; simp only [Sz, Sx, Sy, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro hw
        rcases hLmu' w hw with h | h | h
        · exact Or.inr ⟨hw, h.1⟩
        · exact Or.inl (Or.inr ⟨hw, h.1⟩)
        · exact Or.inl (Or.inl ⟨hw, h.1⟩)
    have hSzx : Disjoint Sz Sx := Finset.disjoint_left.mpr (fun w h1 h2 => by
      have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
      rcases hLmu' w h1'.1 with h | h | h
      · exact h.2.1 h2'.2
      · exact h.2.2 h1'.2
      · exact h.2.2 h2'.2)
    have hSzy : Disjoint Sz Sy := Finset.disjoint_left.mpr (fun w h1 h2 => by
      have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
      rcases hLmu' w h1'.1 with h | h | h
      · exact h.2.2 h1'.2
      · exact h.2.1 h2'.2
      · exact h.2.1 h2'.2)
    have hSxy : Disjoint Sx Sy := Finset.disjoint_left.mpr (fun w h1 h2 => by
      have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
      rcases hLmu' w h1'.1 with h | h | h
      · exact h.2.1 h1'.2
      · exact h.2.1 h2'.2
      · exact h.2.1 h2'.2)
    have hS_sum : Sz.card + Sx.card + Sy.card = B := by
      have hc := congrArg Finset.card hS_eq
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSzy, hSxy⟩),
        Finset.card_union_of_disjoint hSzx] at hc
      exact hc
    let Ry := Lplus.filter (fun w => D.Adj y w)
    let Rx := Lplus.filter (fun w => D.Adj x' w)
    let Rz := Lplus.filter (fun w => D.Adj z' w)
    have hR_eq : Ry ∪ Rx ∪ Rz = Lplus := by
      ext w; simp only [Ry, Rx, Rz, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro hw
        rcases hLpu' w hw with h | h | h
        · exact Or.inl (Or.inl ⟨hw, h.1⟩)
        · exact Or.inl (Or.inr ⟨hw, h.1⟩)
        · exact Or.inr ⟨hw, h.1⟩
    have hRyx : Disjoint Ry Rx := Finset.disjoint_left.mpr (fun w h1 h2 => by
      have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
      rcases hLpu' w h1'.1 with h | h | h
      · exact h.2.1 h2'.2
      · exact h.2.1 h1'.2
      · exact h.2.1 h1'.2)
    have hRyz : Disjoint Ry Rz := Finset.disjoint_left.mpr (fun w h1 h2 => by
      have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
      rcases hLpu' w h1'.1 with h | h | h
      · exact h.2.2 h2'.2
      · exact h.2.1 h1'.2
      · exact h.2.1 h1'.2)
    have hRxz : Disjoint Rx Rz := Finset.disjoint_left.mpr (fun w h1 h2 => by
      have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
      rcases hLpu' w h1'.1 with h | h | h
      · exact h.2.1 h1'.2
      · exact h.2.2 h2'.2
      · exact h.2.2 h1'.2)
    have hR_sum : Ry.card + Rx.card + Rz.card = A := by
      have hc := congrArg Finset.card hR_eq
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hRyz, hRxz⟩),
        Finset.card_union_of_disjoint hRyx] at hc
      exact hc
    -- Common in-neighbor bounds in PoolL = {k : k.val < 2 * B}
    have hPy_in : B ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        k.val < 2 * B ∧ G.Adj (σ k) (σ i0))).card := by
      have h := median_card_in_lt_ge hL i0
      change 2 * B ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        k.val < 2 * B ∧ G.Adj (σ k) (σ i0))).card at h
      omega
    have hPx_in : B ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        k.val < 2 * B ∧ G.Adj (σ k) (σ i1))).card := by
      have h := median_card_in_lt_ge hL i1
      have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
            k.val < i1.val ∧ G.Adj (σ k) (σ i1))) \ ({i0} : Finset (Fin (Fintype.card V))) ⊆
          Finset.univ.filter (fun k : Fin (Fintype.card V) =>
            k.val < 2 * B ∧ G.Adj (σ k) (σ i1)) := by
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton] at hk ⊢
        refine ⟨?_, hk.1.2⟩
        have hne : k.val ≠ 2 * B := fun hv => hk.2 (Fin.ext hv)
        have hlt : k.val < 2 * B + 1 := hk.1.1
        omega
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.le_card_sdiff ({i0} : Finset (Fin (Fintype.card V)))
        (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < i1.val ∧ G.Adj (σ k) (σ i1)))
      simp only [Finset.card_singleton] at hc2
      have hi1v : i1.val = 2 * B + 1 := rfl
      omega
    -- Case split on G.Adj (σ i0) (σ i3)!
    by_cases h03 : G.Adj (σ i0) (σ i3)
    · -- Case 1: u0 -> u3. Map y ↦ i0, x' ↦ i1, z' ↦ i3!
      have hPz_in : B - 1 ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          k.val < 2 * B ∧ G.Adj (σ k) (σ i3))).card := by
        have h := median_card_in_lt_ge hL i3
        have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              k.val < i3.val ∧ G.Adj (σ k) (σ i3))) \ ({i0, i1, i2} : Finset (Fin (Fintype.card V))) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              k.val < 2 * B ∧ G.Adj (σ k) (σ i3)) := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hk ⊢
          refine ⟨?_, hk.1.2⟩
          push Not at hk
          have hne0 : k.val ≠ 2 * B := fun hv => hk.2.1 (Fin.ext hv)
          have hne1 : k.val ≠ 2 * B + 1 := fun hv => hk.2.2.1 (Fin.ext hv)
          have hne2 : k.val ≠ 2 * B + 2 := fun hv => hk.2.2.2 (Fin.ext hv)
          have hlt : k.val < 2 * B + 3 := hk.1.1
          omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.le_card_sdiff ({i0, i1, i2} : Finset (Fin (Fintype.card V)))
          (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < i3.val ∧ G.Adj (σ k) (σ i3)))
        have hc3 : ({i0, i1, i2} : Finset (Fin (Fintype.card V))).card ≤ 3 := by
          have := Finset.card_insert_le i0 {i1, i2}
          have := Finset.card_insert_le i1 {i2}
          simp only [Finset.card_singleton] at this; omega
        have hi3v : i3.val = 2 * B + 3 := rfl
        omega
      -- Out-neighbor pools inside PoolR = {k : k.val = 2*B+2 ∨ 2*B+4 ≤ k.val}
      have hPy_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i0) (σ k))).card := by
        have h := median_card_out_gt_ge hR i0
        have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              i0.val < k.val ∧ G.Adj (σ i0) (σ k))) \ ({i1, i3} : Finset (Fin (Fintype.card V))) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i0) (σ k)) := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hk ⊢
          refine ⟨?_, hk.1.2⟩
          push Not at hk
          have hgt : 2 * B < k.val := hk.1.1
          have hne1 : k.val ≠ 2 * B + 1 := fun hv => hk.2.1 (Fin.ext hv)
          have hne3 : k.val ≠ 2 * B + 3 := fun hv => hk.2.2 (Fin.ext hv)
          omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.le_card_sdiff ({i1, i3} : Finset (Fin (Fintype.card V)))
          (Finset.univ.filter (fun k : Fin (Fintype.card V) => i0.val < k.val ∧ G.Adj (σ i0) (σ k)))
        have hc3 : ({i1, i3} : Finset (Fin (Fintype.card V))).card ≤ 2 := by
          have := Finset.card_insert_le i1 {i3}; simp only [Finset.card_singleton] at this; omega
        have hi0v : i0.val = 2 * B := rfl
        omega
      have hPx_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i1) (σ k))).card := by
        have h := median_card_out_gt_ge hR i1
        have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              i1.val < k.val ∧ G.Adj (σ i1) (σ k))) \ ({i3} : Finset (Fin (Fintype.card V))) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i1) (σ k)) := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton] at hk ⊢
          refine ⟨?_, hk.1.2⟩
          have hgt : 2 * B + 1 < k.val := hk.1.1
          have hne3 : k.val ≠ 2 * B + 3 := fun hv => hk.2 (Fin.ext hv)
          omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.le_card_sdiff ({i3} : Finset (Fin (Fintype.card V)))
          (Finset.univ.filter (fun k : Fin (Fintype.card V) => i1.val < k.val ∧ G.Adj (σ i1) (σ k)))
        simp only [Finset.card_singleton] at hc2
        have hi1v : i1.val = 2 * B + 1 := rfl
        omega
      have hPz_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i3) (σ k))).card := by
        have h := median_card_out_gt_ge hR i3
        have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              i3.val < k.val ∧ G.Adj (σ i3) (σ k)) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i3) (σ k)) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          have hgt : 2 * B + 3 < k.val := hk.1
          exact ⟨Or.inr (by omega), hk.2⟩
        have hc1 := Finset.card_le_card hsub
        have hi3v : i3.val = 2 * B + 3 := rfl
        omega
      change Sz.card ≤ Sx.card at hbz_le
      obtain ⟨gL0, hgL0_inj, hgL0_z, hgL0_x, hgL0_y⟩ := alloc_three_buckets hSzx hSzy hSxy
        (by omega : Sz.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * B ∧ G.Adj (σ k) (σ i3))).card)
        (by omega : Sz.card + Sx.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * B ∧ G.Adj (σ k) (σ i1))).card)
        (by omega : Sz.card + Sx.card + Sy.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * B ∧ G.Adj (σ k) (σ i0))).card)
      obtain ⟨gR0, hgR0_inj, hgR0_y, hgR0_x, hgR0_z⟩ := alloc_three_buckets hRyx hRyz hRxz
        (by omega : Ry.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i0) (σ k))).card)
        (by omega : Ry.card + Rx.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i1) (σ k))).card)
        (by omega : Ry.card + Rx.card + Rz.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => (k.val = 2 * B + 2 ∨ 2 * B + 4 ≤ k.val) ∧ G.Adj (σ i3) (σ k))).card)
      let gL : ↥Lminus → V := fun w => σ (gL0 ⟨w.1, hS_eq.symm ▸ w.2⟩)
      let gR : ↥Lplus → V := fun w => σ (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩)
      have hgL_lt : ∀ w : ↥Lminus, (gL0 ⟨w.1, hS_eq.symm ▸ w.2⟩).val < 2 * B := by
        intro w
        rcases hLmu' w.1 w.2 with h | h | h
        · exact (Finset.mem_filter.mp (hgL0_y ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgL0_x ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgL0_z ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
      have hgR_gt : ∀ w : ↥Lplus,
          (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩).val = 2 * B + 2 ∨ 2 * B + 4 ≤ (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩).val := by
        intro w
        rcases hLpu' w.1 w.2 with h | h | h
        · exact (Finset.mem_filter.mp (hgR0_y ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgR0_x ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgR0_z ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
      refine glue_three_core (t0 := σ i0) (t1 := σ i1) (t2 := σ i3)
        hO hyx' hyz' hxz' hpart' hdp' hdm' hdisj_pm hno_leaf_leaf hLp_in hLm_out
        (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i0, i1] at this; omega)
        (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i0, i3] at this; omega)
        (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i1, i3] at this; omega)
        ?_ gR (fun a b h => by have h0 := hgR0_inj (σ.injective h); exact Subtype.ext (congrArg (fun z : ↥(Ry ∪ Rx ∪ Rz) => z.1) h0)) ?_ ?_
        gL (fun a b h => by have h0 := hgL0_inj (σ.injective h); exact Subtype.ext (congrArg (fun z : ↥(Sz ∪ Sx ∪ Sy) => z.1) h0)) ?_ ?_ ?_
      · intro a b ha hb hab
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
        · simp only [↓reduceIte, hyx'.symm]; exact h01_adj
        · simp only [↓reduceIte, hyz'.symm, hxz'.symm]; exact h03
        · exact absurd hab (not_adj_rev_of_isOrientation hO hDyx')
        · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
        · exact absurd hab hnoxz'.1
        · exact absurd hab (not_adj_rev_of_isOrientation hO hDyz')
        · exact absurd hab hnoxz'.2
        · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
      · intro w; have h := hgR_gt w
        refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;>
        · have hv := congrArg Fin.val (σ.injective heq); dsimp only [i0, i1, i3] at hv; omega
      · intro w
        refine ⟨fun h => (Finset.mem_filter.mp (hgR0_y ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgR0_x ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgR0_z ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2⟩
      · intro w; have h := hgL_lt w
        refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;>
        · have hv := congrArg Fin.val (σ.injective heq); dsimp only [i0, i1, i3] at hv; omega
      · intro w
        refine ⟨fun h => (Finset.mem_filter.mp (hgL0_y ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgL0_x ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgL0_z ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2⟩
      · intro a b heq
        have hv := congrArg Fin.val (σ.injective heq)
        have h1 := hgR_gt a; have h2 := hgL_lt b; omega
    · -- Case 2: ¬ (u0 -> u3). By M2 on [i0, i3], u0 -> u2! Map y ↦ i0, x' ↦ i1, z' ↦ i2!
      have h02_adj : G.Adj (σ i0) (σ i2) := by
        have h03_lt : i0 < i3 := by change 2 * B < 2 * B + 3; omega
        have h := hR i0 i3 h03_lt
        have hdiff : i3.val - i0.val = 3 := by change (2 * B + 3) - (2 * B) = 3; omega
        have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
            i0 < k ∧ k ≤ i3 ∧ G.Adj (σ i0) (σ k)) ⊆ ({i1, i2} : Finset (Fin (Fintype.card V))) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton] at hk ⊢
          have h1 : 2 * B < k.val := hk.1
          have h2 : k.val ≤ 2 * B + 3 := hk.2.1
          by_cases hk3 : k = i3
          · subst hk3; exact absurd hk.2.2 h03
          · have hne3 : k.val ≠ 2 * B + 3 := fun hv => hk3 (Fin.ext hv)
            have : k.val = 2 * B + 1 ∨ k.val = 2 * B + 2 := by omega
            rcases this with hv | hv
            · exact Or.inl (Fin.ext hv)
            · exact Or.inr (Fin.ext hv)
        by_contra hno02
        have hsub1 : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
            i0 < k ∧ k ≤ i3 ∧ G.Adj (σ i0) (σ k)) ⊆ ({i1} : Finset (Fin (Fintype.card V))) := by
          intro k hk
          have hm := hsub hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
          rcases hm with rfl | rfl
          · rfl
          · exact absurd (Finset.mem_filter.mp hk).2.2.2 hno02
        have hc := Finset.card_le_card hsub1
        simp only [Finset.card_singleton] at hc
        omega
      have hPz_in : B - 1 ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          k.val < 2 * B ∧ G.Adj (σ k) (σ i2))).card := by
        have h := median_card_in_lt_ge hL i2
        have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              k.val < i2.val ∧ G.Adj (σ k) (σ i2))) \ ({i0, i1} : Finset (Fin (Fintype.card V))) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              k.val < 2 * B ∧ G.Adj (σ k) (σ i2)) := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hk ⊢
          refine ⟨?_, hk.1.2⟩
          push Not at hk
          have hne0 : k.val ≠ 2 * B := fun hv => hk.2.1 (Fin.ext hv)
          have hne1 : k.val ≠ 2 * B + 1 := fun hv => hk.2.2 (Fin.ext hv)
          have hlt : k.val < 2 * B + 2 := hk.1.1
          omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.le_card_sdiff ({i0, i1} : Finset (Fin (Fintype.card V)))
          (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < i2.val ∧ G.Adj (σ k) (σ i2)))
        have hc3 : ({i0, i1} : Finset (Fin (Fintype.card V))).card ≤ 2 := by
          have := Finset.card_insert_le i0 {i1}; simp only [Finset.card_singleton] at this; omega
        have hi2v : i2.val = 2 * B + 2 := rfl
        omega
      -- Out-neighbor pools inside PoolR = {k : 2 * B + 3 ≤ k.val}
      have hPy_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          2 * B + 3 ≤ k.val ∧ G.Adj (σ i0) (σ k))).card := by
        have h := median_card_out_gt_ge hR i0
        have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              i0.val < k.val ∧ G.Adj (σ i0) (σ k))) \ ({i1, i2} : Finset (Fin (Fintype.card V))) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              2 * B + 3 ≤ k.val ∧ G.Adj (σ i0) (σ k)) := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton] at hk ⊢
          refine ⟨?_, hk.1.2⟩
          push Not at hk
          have hgt : 2 * B < k.val := hk.1.1
          have hne1 : k.val ≠ 2 * B + 1 := fun hv => hk.2.1 (Fin.ext hv)
          have hne2 : k.val ≠ 2 * B + 2 := fun hv => hk.2.2 (Fin.ext hv)
          omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.le_card_sdiff ({i1, i2} : Finset (Fin (Fintype.card V)))
          (Finset.univ.filter (fun k : Fin (Fintype.card V) => i0.val < k.val ∧ G.Adj (σ i0) (σ k)))
        have hc3 : ({i1, i2} : Finset (Fin (Fintype.card V))).card ≤ 2 := by
          have := Finset.card_insert_le i1 {i2}; simp only [Finset.card_singleton] at this; omega
        have hi0v : i0.val = 2 * B := rfl
        omega
      have hPx_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          2 * B + 3 ≤ k.val ∧ G.Adj (σ i1) (σ k))).card := by
        have h := median_card_out_gt_ge hR i1
        have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              i1.val < k.val ∧ G.Adj (σ i1) (σ k))) \ ({i2} : Finset (Fin (Fintype.card V))) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              2 * B + 3 ≤ k.val ∧ G.Adj (σ i1) (σ k)) := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton] at hk ⊢
          refine ⟨?_, hk.1.2⟩
          have hgt : 2 * B + 1 < k.val := hk.1.1
          have hne2 : k.val ≠ 2 * B + 2 := fun hv => hk.2 (Fin.ext hv)
          omega
        have hc1 := Finset.card_le_card hsub
        have hc2 := Finset.le_card_sdiff ({i2} : Finset (Fin (Fintype.card V)))
          (Finset.univ.filter (fun k : Fin (Fintype.card V) => i1.val < k.val ∧ G.Adj (σ i1) (σ k)))
        simp only [Finset.card_singleton] at hc2
        have hi1v : i1.val = 2 * B + 1 := rfl
        omega
      have hPz_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          2 * B + 3 ≤ k.val ∧ G.Adj (σ i2) (σ k))).card := by
        have h := median_card_out_gt_ge hR i2
        have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              i2.val < k.val ∧ G.Adj (σ i2) (σ k)) ⊆
            Finset.univ.filter (fun k : Fin (Fintype.card V) =>
              2 * B + 3 ≤ k.val ∧ G.Adj (σ i2) (σ k)) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          have hgt : 2 * B + 2 < k.val := hk.1
          exact ⟨by omega, hk.2⟩
        have hc1 := Finset.card_le_card hsub
        have hi2v : i2.val = 2 * B + 2 := rfl
        omega
      change Sz.card ≤ Sx.card at hbz_le
      obtain ⟨gL0, hgL0_inj, hgL0_z, hgL0_x, hgL0_y⟩ := alloc_three_buckets hSzx hSzy hSxy
        (by omega : Sz.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * B ∧ G.Adj (σ k) (σ i2))).card)
        (by omega : Sz.card + Sx.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * B ∧ G.Adj (σ k) (σ i1))).card)
        (by omega : Sz.card + Sx.card + Sy.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * B ∧ G.Adj (σ k) (σ i0))).card)
      obtain ⟨gR0, hgR0_inj, hgR0_y, hgR0_x, hgR0_z⟩ := alloc_three_buckets hRyx hRyz hRxz
        (by omega : Ry.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * B + 3 ≤ k.val ∧ G.Adj (σ i0) (σ k))).card)
        (by omega : Ry.card + Rx.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * B + 3 ≤ k.val ∧ G.Adj (σ i1) (σ k))).card)
        (by omega : Ry.card + Rx.card + Rz.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * B + 3 ≤ k.val ∧ G.Adj (σ i2) (σ k))).card)
      let gL : ↥Lminus → V := fun w => σ (gL0 ⟨w.1, hS_eq.symm ▸ w.2⟩)
      let gR : ↥Lplus → V := fun w => σ (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩)
      have hgL_lt : ∀ w : ↥Lminus, (gL0 ⟨w.1, hS_eq.symm ▸ w.2⟩).val < 2 * B := by
        intro w
        rcases hLmu' w.1 w.2 with h | h | h
        · exact (Finset.mem_filter.mp (hgL0_y ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgL0_x ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgL0_z ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
      have hgR_gt : ∀ w : ↥Lplus, 2 * B + 3 ≤ (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩).val := by
        intro w
        rcases hLpu' w.1 w.2 with h | h | h
        · exact (Finset.mem_filter.mp (hgR0_y ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgR0_x ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
        · exact (Finset.mem_filter.mp (hgR0_z ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
      refine glue_three_core (t0 := σ i0) (t1 := σ i1) (t2 := σ i2)
        hO hyx' hyz' hxz' hpart' hdp' hdm' hdisj_pm hno_leaf_leaf hLp_in hLm_out
        (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i0, i1] at this; omega)
        (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i0, i2] at this; omega)
        (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i1, i2] at this; omega)
        ?_ gR (fun a b h => by have h0 := hgR0_inj (σ.injective h); exact Subtype.ext (congrArg (fun z : ↥(Ry ∪ Rx ∪ Rz) => z.1) h0)) ?_ ?_
        gL (fun a b h => by have h0 := hgL0_inj (σ.injective h); exact Subtype.ext (congrArg (fun z : ↥(Sz ∪ Sx ∪ Sy) => z.1) h0)) ?_ ?_ ?_
      · intro a b ha hb hab
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
        · simp only [↓reduceIte, hyx'.symm]; exact h01_adj
        · simp only [↓reduceIte, hyz'.symm, hxz'.symm]; exact h02_adj
        · exact absurd hab (not_adj_rev_of_isOrientation hO hDyx')
        · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
        · exact absurd hab hnoxz'.1
        · exact absurd hab (not_adj_rev_of_isOrientation hO hDyz')
        · exact absurd hab hnoxz'.2
        · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
      · intro w; have h := hgR_gt w
        refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;>
        · have hv := congrArg Fin.val (σ.injective heq); dsimp only [i0, i1, i2] at hv; omega
      · intro w
        refine ⟨fun h => (Finset.mem_filter.mp (hgR0_y ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgR0_x ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgR0_z ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2⟩
      · intro w; have h := hgL_lt w
        refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;>
        · have hv := congrArg Fin.val (σ.injective heq); dsimp only [i0, i1, i2] at hv; omega
      · intro w
        refine ⟨fun h => (Finset.mem_filter.mp (hgL0_y ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgL0_x ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
          fun h => (Finset.mem_filter.mp (hgL0_z ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2⟩
      · intro a b heq
        have hv := congrArg Fin.val (σ.injective heq)
        have h1 := hgR_gt a; have h2 := hgL_lt b; omega
  by_cases hle : (Lminus.filter (fun w => D.Adj w z)).card ≤ (Lminus.filter (fun w => D.Adj w x)).card
  · exact hmain x z hyx hyz hxz hDyx hDyz hno_xz hpart hdisj_p hdisj_m hLp_uniq hLm_uniq hle
  · exact hmain z x hyz hyx hxz.symm hDyz hDyx ⟨hno_xz.2, hno_xz.1⟩
      (fun w => by rcases hpart w with h | h | h | h | h <;> tauto)
      ⟨hdisj_p.1, hdisj_p.2.2, hdisj_p.2.1⟩ ⟨hdisj_m.1, hdisj_m.2.2, hdisj_m.2.1⟩
      (fun w hw => by rcases hLp_uniq w hw with h | h | h <;> tauto)
      (fun w hw => by rcases hLm_uniq w hw with h | h | h <;> tauto) (by omega)

-- Helper: P_3^+ core (x -> y -> z) when ay + az >= 1!
lemma embeds_three_core_P3plus_shifted {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (hW : Fintype.card W = n)
    {T : SimpleGraph W} (hO : D.IsOrientation T)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    {x y z : W} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hDxy : D.Adj x y) (hDyz : D.Adj y z) (hno_xz : ¬ D.Adj x z ∧ ¬ D.Adj z x)
    {Lplus Lminus : Finset W}
    (hpart : ∀ w : W, w = x ∨ w = y ∨ w = z ∨ w ∈ Lplus ∨ w ∈ Lminus)
    (hdisj_p : x ∉ Lplus ∧ y ∉ Lplus ∧ z ∉ Lplus)
    (hdisj_m : x ∉ Lminus ∧ y ∉ Lminus ∧ z ∉ Lminus)
    (hdisj_pm : Disjoint Lplus Lminus)
    (hno_leaf_leaf : ∀ a b : W, (a ∈ Lplus ∨ a ∈ Lminus) → (b ∈ Lplus ∨ b ∈ Lminus) → ¬ D.Adj a b)
    (hLp_in : ∀ a ∈ Lplus, ∀ b : W, ¬ D.Adj a b)
    (hLm_out : ∀ a ∈ Lminus, ∀ b : W, ¬ D.Adj b a)
    (hLp_uniq : ∀ w ∈ Lplus, (D.Adj x w ∧ ¬ D.Adj y w ∧ ¬ D.Adj z w) ∨
      (D.Adj y w ∧ ¬ D.Adj x w ∧ ¬ D.Adj z w) ∨ (D.Adj z w ∧ ¬ D.Adj x w ∧ ¬ D.Adj y w))
    (hLm_uniq : ∀ w ∈ Lminus, (D.Adj w x ∧ ¬ D.Adj w y ∧ ¬ D.Adj w z) ∨
      (D.Adj w y ∧ ¬ D.Adj w x ∧ ¬ D.Adj w z) ∨ (D.Adj w z ∧ ¬ D.Adj w x ∧ ¬ D.Adj w y))
    (hayz : 1 ≤ (Lplus.filter (fun w => D.Adj y w)).card + (Lplus.filter (fun w => D.Adj z w)).card) :
    Embeds D G := by
  classical
  let A := Lplus.card
  let B := Lminus.card
  have hn_eq : n = A + B + 3 := by
    let M : Finset W := {x, y, z}
    have hMcard : M.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hyz]
      · simp [hxy, hxz]
    have hd1 : Disjoint M Lplus := Finset.disjoint_left.mpr (fun w hw => by
      simp only [M, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hdisj_p.1
      · exact hdisj_p.2.1
      · exact hdisj_p.2.2)
    have hd2 : Disjoint (M ∪ Lplus) Lminus := Finset.disjoint_left.mpr (fun w hw => by
      rcases Finset.mem_union.mp hw with hwM | hwP
      · simp only [M, Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with rfl | rfl | rfl
        · exact hdisj_m.1
        · exact hdisj_m.2.1
        · exact hdisj_m.2.2
      · exact Finset.disjoint_left.mp hdisj_pm hwP)
    have huniv : M ∪ Lplus ∪ Lminus = Finset.univ := by
      ext w; simp only [Finset.mem_union, Finset.mem_univ, iff_true, M,
        Finset.mem_insert, Finset.mem_singleton]
      rcases hpart w with rfl | rfl | rfl | h | h <;> tauto
    have hc := congrArg Finset.card huniv
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hMcard, Finset.card_univ, hW] at hc
    omega
  obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
  have hV_eq : Fintype.card V = 2 * A + 2 * B + 4 := by omega
  let i1 : Fin (Fintype.card V) := ⟨2 * B + 1, by omega⟩
  let i2 : Fin (Fintype.card V) := ⟨2 * B + 2, by omega⟩
  let i3 : Fin (Fintype.card V) := ⟨2 * B + 3, by omega⟩
  have h12_adj : G.Adj (σ i1) (σ i2) := median_adj_succ hR i1 (by dsimp only [i1]; omega)
  have h23_adj : G.Adj (σ i2) (σ i3) := median_adj_succ hR i2 (by dsimp only [i2]; omega)
  let Sx := Lminus.filter (fun w => D.Adj w x)
  let Sy := Lminus.filter (fun w => D.Adj w y)
  let Sz := Lminus.filter (fun w => D.Adj w z)
  have hS_eq : Sx ∪ Sy ∪ Sz = Lminus := by
    ext w; simp only [Sx, Sy, Sz, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hw; rcases hLm_uniq w hw with h | h | h
      · exact Or.inl (Or.inl ⟨hw, h.1⟩)
      · exact Or.inl (Or.inr ⟨hw, h.1⟩)
      · exact Or.inr ⟨hw, h.1⟩
  have hSxy : Disjoint Sx Sy := Finset.disjoint_left.mpr (fun w h1 h2 => by
    have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
    rcases hLm_uniq w h1'.1 with h | h | h
    · exact h.2.1 h2'.2
    · exact h.2.1 h1'.2
    · exact h.2.1 h1'.2)
  have hSxz : Disjoint Sx Sz := Finset.disjoint_left.mpr (fun w h1 h2 => by
    have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
    rcases hLm_uniq w h1'.1 with h | h | h
    · exact h.2.2 h2'.2
    · exact h.2.1 h1'.2
    · exact h.2.1 h1'.2)
  have hSyz : Disjoint Sy Sz := Finset.disjoint_left.mpr (fun w h1 h2 => by
    have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
    rcases hLm_uniq w h1'.1 with h | h | h
    · exact h.2.1 h1'.2
    · exact h.2.2 h2'.2
    · exact h.2.2 h1'.2)
  have hS_sum : Sx.card + Sy.card + Sz.card = B := by
    have hc := congrArg Finset.card hS_eq
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSxz, hSyz⟩),
      Finset.card_union_of_disjoint hSxy] at hc
    exact hc
  let Rx := Lplus.filter (fun w => D.Adj x w)
  let Ry := Lplus.filter (fun w => D.Adj y w)
  let Rz := Lplus.filter (fun w => D.Adj z w)
  have hR_eq : Rx ∪ Ry ∪ Rz = Lplus := by
    ext w; simp only [Rx, Ry, Rz, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hw; rcases hLp_uniq w hw with h | h | h
      · exact Or.inl (Or.inl ⟨hw, h.1⟩)
      · exact Or.inl (Or.inr ⟨hw, h.1⟩)
      · exact Or.inr ⟨hw, h.1⟩
  have hRxy : Disjoint Rx Ry := Finset.disjoint_left.mpr (fun w h1 h2 => by
    have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
    rcases hLp_uniq w h1'.1 with h | h | h
    · exact h.2.1 h2'.2
    · exact h.2.1 h1'.2
    · exact h.2.1 h1'.2)
  have hRxz : Disjoint Rx Rz := Finset.disjoint_left.mpr (fun w h1 h2 => by
    have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
    rcases hLp_uniq w h1'.1 with h | h | h
    · exact h.2.2 h2'.2
    · exact h.2.1 h1'.2
    · exact h.2.1 h1'.2)
  have hRyz : Disjoint Ry Rz := Finset.disjoint_left.mpr (fun w h1 h2 => by
    have h1' := Finset.mem_filter.mp h1; have h2' := Finset.mem_filter.mp h2
    rcases hLp_uniq w h1'.1 with h | h | h
    · exact h.2.1 h1'.2
    · exact h.2.2 h2'.2
    · exact h.2.2 h1'.2)
  have hR_sum : Rx.card + Ry.card + Rz.card = A := by
    have hc := congrArg Finset.card hR_eq
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hRxz, hRyz⟩),
      Finset.card_union_of_disjoint hRxy] at hc
    exact hc
  -- In-neighbor counts in PoolL = {k : k.val <= 2 * B} (size 2*B+1)
  have hPx_in : B ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i1))).card := by
    have h := median_card_in_lt_ge hL i1
    have hi1v : i1.val = 2 * B + 1 := rfl
    have heq : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        k.val < i1.val ∧ G.Adj (σ k) (σ i1)) =
      Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i1)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi1v]
      exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
    rw [heq] at h; omega
  have hPy_in : B ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i2))).card := by
    have h := median_card_in_lt_ge hL i2
    have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          k.val < i2.val ∧ G.Adj (σ k) (σ i2))) \ ({i1} : Finset (Fin (Fintype.card V))) ⊆
        Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i2)) := by
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hk ⊢
      refine ⟨?_, hk.1.2⟩
      have hlt : k.val < 2 * B + 2 := hk.1.1
      have hne1 : k.val ≠ 2 * B + 1 := fun hv => hk.2 (Fin.ext hv)
      omega
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.le_card_sdiff ({i1} : Finset (Fin (Fintype.card V)))
      (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < i2.val ∧ G.Adj (σ k) (σ i2)))
    simp only [Finset.card_singleton] at hc2
    have hi2v : i2.val = 2 * B + 2 := rfl; omega
  have hPz_in : B ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i3))).card := by
    have h := median_card_in_lt_ge hL i3
    have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          k.val < i3.val ∧ G.Adj (σ k) (σ i3))) \ ({i1, i2} : Finset (Fin (Fintype.card V))) ⊆
        Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i3)) := by
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton] at hk ⊢
      refine ⟨?_, hk.1.2⟩
      push Not at hk
      have hlt : k.val < 2 * B + 3 := hk.1.1
      have hne1 : k.val ≠ 2 * B + 1 := fun hv => hk.2.1 (Fin.ext hv)
      have hne2 : k.val ≠ 2 * B + 2 := fun hv => hk.2.2 (Fin.ext hv)
      omega
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.le_card_sdiff ({i1, i2} : Finset (Fin (Fintype.card V)))
      (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < i3.val ∧ G.Adj (σ k) (σ i3)))
    have hc3 : ({i1, i2} : Finset (Fin (Fintype.card V))).card ≤ 2 := by
      have := Finset.card_insert_le i1 {i2}; simp only [Finset.card_singleton] at this; omega
    have hi3v : i3.val = 2 * B + 3 := rfl; omega
  -- Out-neighbor counts in PoolR = {k : 2 * B + 4 <= k.val} (size 2*A)
  have hPx_out : A - 1 ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      2 * B + 4 ≤ k.val ∧ G.Adj (σ i1) (σ k))).card := by
    have h := median_card_out_gt_ge hR i1
    have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i1.val < k.val ∧ G.Adj (σ i1) (σ k))) \ ({i2, i3} : Finset (Fin (Fintype.card V))) ⊆
        Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          2 * B + 4 ≤ k.val ∧ G.Adj (σ i1) (σ k)) := by
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton] at hk ⊢
      refine ⟨?_, hk.1.2⟩
      push Not at hk
      have hgt : 2 * B + 1 < k.val := hk.1.1
      have hne2 : k.val ≠ 2 * B + 2 := fun hv => hk.2.1 (Fin.ext hv)
      have hne3 : k.val ≠ 2 * B + 3 := fun hv => hk.2.2 (Fin.ext hv)
      omega
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.le_card_sdiff ({i2, i3} : Finset (Fin (Fintype.card V)))
      (Finset.univ.filter (fun k : Fin (Fintype.card V) => i1.val < k.val ∧ G.Adj (σ i1) (σ k)))
    have hc3 : ({i2, i3} : Finset (Fin (Fintype.card V))).card ≤ 2 := by
      have := Finset.card_insert_le i2 {i3}; simp only [Finset.card_singleton] at this; omega
    have hi1v : i1.val = 2 * B + 1 := rfl; omega
  have hPy_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      2 * B + 4 ≤ k.val ∧ G.Adj (σ i2) (σ k))).card := by
    have h := median_card_out_gt_ge hR i2
    have hsub : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i2.val < k.val ∧ G.Adj (σ i2) (σ k))) \ ({i3} : Finset (Fin (Fintype.card V))) ⊆
        Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          2 * B + 4 ≤ k.val ∧ G.Adj (σ i2) (σ k)) := by
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hk ⊢
      refine ⟨?_, hk.1.2⟩
      have hgt : 2 * B + 2 < k.val := hk.1.1
      have hne3 : k.val ≠ 2 * B + 3 := fun hv => hk.2 (Fin.ext hv)
      omega
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.le_card_sdiff ({i3} : Finset (Fin (Fintype.card V)))
      (Finset.univ.filter (fun k : Fin (Fintype.card V) => i2.val < k.val ∧ G.Adj (σ i2) (σ k)))
    simp only [Finset.card_singleton] at hc2
    have hi2v : i2.val = 2 * B + 2 := rfl; omega
  have hPz_out : A ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      2 * B + 4 ≤ k.val ∧ G.Adj (σ i3) (σ k))).card := by
    have h := median_card_out_gt_ge hR i3
    have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          i3.val < k.val ∧ G.Adj (σ i3) (σ k)) ⊆
        Finset.univ.filter (fun k : Fin (Fintype.card V) =>
          2 * B + 4 ≤ k.val ∧ G.Adj (σ i3) (σ k)) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      have hgt : 2 * B + 3 < k.val := hk.1
      exact ⟨by omega, hk.2⟩
    have hc1 := Finset.card_le_card hsub
    have hi3v : i3.val = 2 * B + 3 := rfl; omega
  change 1 ≤ Ry.card + Rz.card at hayz
  obtain ⟨gL0, hgL0_inj, hgL0_x, hgL0_y, hgL0_z⟩ := alloc_three_buckets hSxy hSxz hSyz
    (by omega : Sx.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i1))).card)
    (by omega : Sx.card + Sy.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i2))).card)
    (by omega : Sx.card + Sy.card + Sz.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val ≤ 2 * B ∧ G.Adj (σ k) (σ i3))).card)
  obtain ⟨gR0, hgR0_inj, hgR0_x, hgR0_y, hgR0_z⟩ := alloc_three_buckets hRxy hRxz hRyz
    (by omega : Rx.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * B + 4 ≤ k.val ∧ G.Adj (σ i1) (σ k))).card)
    (by omega : Rx.card + Ry.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * B + 4 ≤ k.val ∧ G.Adj (σ i2) (σ k))).card)
    (by omega : Rx.card + Ry.card + Rz.card ≤ (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * B + 4 ≤ k.val ∧ G.Adj (σ i3) (σ k))).card)
  let gL : ↥Lminus → V := fun w => σ (gL0 ⟨w.1, hS_eq.symm ▸ w.2⟩)
  let gR : ↥Lplus → V := fun w => σ (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩)
  have hgL_le : ∀ w : ↥Lminus, (gL0 ⟨w.1, hS_eq.symm ▸ w.2⟩).val ≤ 2 * B := by
    intro w
    rcases hLm_uniq w.1 w.2 with h | h | h
    · exact (Finset.mem_filter.mp (hgL0_x ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
    · exact (Finset.mem_filter.mp (hgL0_y ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
    · exact (Finset.mem_filter.mp (hgL0_z ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
  have hgR_ge : ∀ w : ↥Lplus, 2 * B + 4 ≤ (gR0 ⟨w.1, hR_eq.symm ▸ w.2⟩).val := by
    intro w
    rcases hLp_uniq w.1 w.2 with h | h | h
    · exact (Finset.mem_filter.mp (hgR0_x ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
    · exact (Finset.mem_filter.mp (hgR0_y ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
    · exact (Finset.mem_filter.mp (hgR0_z ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h.1⟩))).2.1
  refine glue_three_core (t0 := σ i1) (t1 := σ i2) (t2 := σ i3)
    hO hxy hxz hyz hpart hdisj_p hdisj_m hdisj_pm hno_leaf_leaf hLp_in hLm_out
    (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i1, i2] at this; omega)
    (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i1, i3] at this; omega)
    (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only [i2, i3] at this; omega)
    ?_ gR (fun a b h => by have h0 := hgR0_inj (σ.injective h); exact Subtype.ext (congrArg (fun z : ↥(Rx ∪ Ry ∪ Rz) => z.1) h0)) ?_ ?_
    gL (fun a b h => by have h0 := hgL0_inj (σ.injective h); exact Subtype.ext (congrArg (fun z : ↥(Sx ∪ Sy ∪ Sz) => z.1) h0)) ?_ ?_ ?_
  · intro a b ha hb hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
    · simp only [↓reduceIte, hxy.symm]; exact h12_adj
    · exact absurd hab hno_xz.1
    · exact absurd hab (not_adj_rev_of_isOrientation hO hDxy)
    · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
    · simp only [↓reduceIte, hxy.symm, hxz.symm, hyz.symm]; exact h23_adj
    · exact absurd hab hno_xz.2
    · exact absurd hab (not_adj_rev_of_isOrientation hO hDyz)
    · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
  · intro w; have h := hgR_ge w
    refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;>
    · have hv := congrArg Fin.val (σ.injective heq); dsimp only [i1, i2, i3] at hv; omega
  · intro w
    refine ⟨fun h => (Finset.mem_filter.mp (hgR0_x ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
      fun h => (Finset.mem_filter.mp (hgR0_y ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
      fun h => (Finset.mem_filter.mp (hgR0_z ⟨w.1, hR_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2⟩
  · intro w; have h := hgL_le w
    refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩ <;>
    · have hv := congrArg Fin.val (σ.injective heq); dsimp only [i1, i2, i3] at hv; omega
  · intro w
    refine ⟨fun h => (Finset.mem_filter.mp (hgL0_x ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
      fun h => (Finset.mem_filter.mp (hgL0_y ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2,
      fun h => (Finset.mem_filter.mp (hgL0_z ⟨w.1, hS_eq.symm ▸ w.2⟩ (Finset.mem_filter.mpr ⟨w.2, h⟩))).2.2⟩
  · intro a b heq
    have hv := congrArg Fin.val (σ.injective heq)
    have h1 := hgR_ge a; have h2 := hgL_le b; omega

lemma ne_of_adj_tournament {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (h : G.Adj u v) : u ≠ v :=
  fun heq => hG.1 u (heq ▸ h)

lemma not_adj_rev_of_tournament {V : Type*} {G : Digraph V} (hG : G.IsTournament)
    {u v : V} (h : G.Adj u v) : ¬ G.Adj v u :=
  (hG.2 u v (ne_of_adj_tournament hG h)).mp h

-- Helper: Tournament subset internal arc identity 2 * e(S, S) = S.card * S.card - S.card
lemma tournament_two_mul_internal_arcs {V : Type*} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] (hG : G.IsTournament) (S : Finset V) :
    2 * ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card = S.card * S.card - S.card := by
  classical
  let P := (S ×ˢ S).filter (fun p => G.Adj p.1 p.2)
  let Q := (S ×ˢ S).filter (fun p => G.Adj p.2 p.1)
  have hPQ : P.card = Q.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp; simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨(p.2, p.1), ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
  have hdisj : Disjoint P Q := Finset.disjoint_left.mpr (fun p hp hq => by
    simp only [P, Q, Finset.mem_filter] at hp hq
    exact not_adj_rev_of_tournament hG hp.2 hq.2)
  have hunion : P ∪ Q = (S ×ˢ S).filter (fun p => p.1 ≠ p.2) := by
    ext ⟨a, b⟩
    simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro (⟨h, hab⟩ | ⟨h, hba⟩)
      · exact ⟨h, ne_of_adj_tournament hG hab⟩
      · exact ⟨h, (ne_of_adj_tournament hG hba).symm⟩
    · rintro ⟨h, hne⟩
      rcases adj_or_rev_of_isTournament hG hne with hab | hba
      · exact Or.inl ⟨h, hab⟩
      · exact Or.inr ⟨h, hba⟩
  let Dg := S.image (fun x => (x, x))
  have hDg_card : Dg.card = S.card :=
    Finset.card_image_of_injective S (fun _ _ h => congrArg Prod.fst h)
  have hDg_sub : Dg ⊆ S ×ˢ S := fun p hp => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨hx, hx⟩
  have hsdiff : (S ×ˢ S) \ Dg = (S ×ˢ S).filter (fun p => p.1 ≠ p.2) := by
    ext ⟨a, b⟩
    simp only [Dg, Finset.mem_sdiff, Finset.mem_product, Finset.mem_image, Prod.mk.injEq,
      Finset.mem_filter]
    constructor
    · rintro ⟨h, hnd⟩; refine ⟨h, fun hab => hnd ⟨a, h.1, rfl, hab⟩⟩
    · rintro ⟨h, hne⟩; refine ⟨h, fun ⟨x, _, h1, h2⟩ => hne (h1.symm.trans h2)⟩
  have h1 := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, ← hPQ, ← hsdiff, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hDg_sub, Finset.card_product, hDg_card] at h1
  change 2 * P.card = S.card * S.card - S.card
  omega

-- Helper: In any strong tournament on 2n - 2 >= 4 vertices, there exist x1 ∈ V+, x2 ∈ V+, y1 ∈ V-
-- with x1 -> x2 -> y1!
lemma exists_two_path_Vplus_to_Vminus {n : ℕ} (hn : 3 ≤ n)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hStrong : ∀ V1 : Finset V, V1.Nonempty → V1 ≠ Finset.univ →
      ∃ u ∈ V1, ∃ v ∉ V1, G.Adj v u) :
    ∃ x1 x2 y1 : V, x1 ≠ x2 ∧ x1 ≠ y1 ∧ x2 ≠ y1 ∧
      G.Adj x1 x2 ∧ G.Adj x2 y1 ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj x1 u)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u y1)).card := by
  classical
  let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
  let Vm := Vpᶜ
  have hdeg_sum : ∀ v : V,
      (Finset.univ.filter (fun u : V => G.Adj v u)).card +
      (Finset.univ.filter (fun u : V => G.Adj u v)).card = 2 * n - 3 := by
    intro v
    have hdisj : Disjoint (Finset.univ.filter (fun u : V => G.Adj v u))
        (Finset.univ.filter (fun u : V => G.Adj u v)) :=
      Finset.disjoint_left.mpr (fun u h1 h2 =>
        not_adj_rev_of_tournament hG (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
    have hunion : Finset.univ.filter (fun u : V => G.Adj v u) ∪
        Finset.univ.filter (fun u : V => G.Adj u v) = Finset.univ.erase v := by
      ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · rintro (h | h)
        · exact (ne_of_adj_tournament hG h).symm
        · exact ne_of_adj_tournament hG h
      · intro hne
        rcases adj_or_rev_of_isTournament hG hne.symm with h | h
        · exact Or.inl h
        · exact Or.inr h
    have hc := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, hV] at hc
    exact hc
  have hVm_deg : ∀ v ∈ Vm, n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card := by
    intro v hv
    have hvnot : ¬ n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card := by
      intro h; exact Finset.mem_compl.mp hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have := hdeg_sum v; omega
  have hVpVm : Vp.card + Vm.card = 2 * n - 2 := by
    have := Finset.card_add_card_compl Vp
    change Vp.card + Vm.card = Fintype.card V at this; omega
  have hsum_out : ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
      ((Vp ×ˢ Vp).filter (fun p => G.Adj p.1 p.2)).card +
      ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    have hall : ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
        ((Vp ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)).card := by
      have hpart : (Vp ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2) =
          Vp.biUnion (fun v => (Finset.univ.filter (fun u : V => G.Adj v u)).image (fun u => (v, u))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, true_and,
          Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨ha, hab⟩; exact ⟨a, ha, b, hab, rfl, rfl⟩
        · rintro ⟨v, hv, u, hvu, rfl, rfl⟩; exact ⟨hv, hvu⟩
      rw [hpart, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
      · intro v1 _ v2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro p h1 h2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2
        exact hne (congrArg Prod.fst hEq).symm
    rw [hall]
    have hdisj : Disjoint ((Vp ×ˢ Vp).filter (fun p => G.Adj p.1 p.2))
        ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)) :=
      Finset.disjoint_left.mpr (fun p h1 h2 =>
        Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp h2).1).2
          (Finset.mem_product.mp (Finset.mem_filter.mp h1).1).2)
    have hunion : (Vp ×ˢ Vp).filter (fun p => G.Adj p.1 p.2) ∪
        (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) =
        (Vp ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, Vm, Finset.mem_compl]
      tauto
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hsum_in : ∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
      ((Vm ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card +
      ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    have hall : ∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
        ((Finset.univ ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      have hpart : (Finset.univ ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) =
          Vm.biUnion (fun v => (Finset.univ.filter (fun u : V => G.Adj u v)).image (fun u => (u, v))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨hb, hab⟩; exact ⟨b, hb, a, hab, rfl, rfl⟩
        · rintro ⟨v, hv, u, huv, rfl, rfl⟩; exact ⟨hv, huv⟩
      rw [hpart, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
      · intro v1 _ v2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro p h1 h2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2
        exact hne (congrArg Prod.snd hEq).symm
    rw [hall]
    have hdisj : Disjoint ((Vm ×ˢ Vm).filter (fun p => G.Adj p.1 p.2))
        ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)) :=
      Finset.disjoint_left.mpr (fun p h1 h2 =>
        Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp h1).1).1
          (Finset.mem_product.mp (Finset.mem_filter.mp h2).1).1)
    have hunion : (Vm ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) ∪
        (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) =
        (Finset.univ ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and, Vm, Finset.mem_compl]
      tauto
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have heVp : 2 * ((Vp ×ˢ Vp).filter (fun p => G.Adj p.1 p.2)).card = Vp.card * (Vp.card - 1) := by
    have h := tournament_two_mul_internal_arcs hG Vp
    rw [Nat.mul_sub_left_distrib, mul_one]; exact h
  have heVm : 2 * ((Vm ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card = Vm.card * (Vm.card - 1) := by
    have h := tournament_two_mul_internal_arcs hG Vm
    rw [Nat.mul_sub_left_distrib, mul_one]; exact h
  have hsum_out_lb : Vp.card * (n - 1) ≤ ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card := by
    calc Vp.card * (n - 1) = ∑ _ ∈ Vp, (n - 1) := by simp
      _ ≤ ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
  have hsum_in_lb : Vm.card * (n - 1) ≤ ∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card := by
    calc Vm.card * (n - 1) = ∑ _ ∈ Vm, (n - 1) := by simp
      _ ≤ ∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card :=
        Finset.sum_le_sum (fun v hv => hVm_deg v hv)
  have hVp_ge2 : 2 ≤ Vp.card := by
    by_contra hlt
    have hcase : Vp.card = 0 ∨ Vp.card = 1 := by omega
    rcases hcase with h0 | h1
    · have hVm_eq : Vm.card = 2 * n - 2 := by omega
      have h0e : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card = 0 := by
        have hVpe : Vp = ∅ := Finset.card_eq_zero.mp h0; simp [hVpe]
      have hle : Vm.card * (2 * (n - 1)) ≤ Vm.card * (Vm.card - 1) := by
        have : Vm.card * (2 * (n - 1)) = 2 * (Vm.card * (n - 1)) := by ring
        omega
      have hcancel := Nat.le_of_mul_le_mul_left hle (by omega : 0 < Vm.card)
      omega
    · obtain ⟨u0, hu0⟩ := Finset.card_eq_one.mp h1
      have hVm_eq : Vm.card = 2 * n - 3 := by omega
      have hle : Vm.card * (2 * (n - 1)) ≤ Vm.card * (Vm.card - 1) +
          2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
        have : Vm.card * (2 * (n - 1)) = 2 * (Vm.card * (n - 1)) := by ring
        omega
      have hsplit : Vm.card * (2 * (n - 1)) = Vm.card * (Vm.card - 1) + 2 * Vm.card := by
        have h2 : 2 * (n - 1) = (Vm.card - 1) + 2 := by omega
        rw [h2, mul_add]; ring
      have he_ge : Vm.card ≤ ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by omega
      have he_le : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card ≤ (Vp ×ˢ Vm).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hprod : (Vp ×ˢ Vm).card = Vm.card := by rw [Finset.card_product, h1, one_mul]
      have hall_cross : (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) = Vp ×ˢ Vm :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hne_univ : Vp ≠ Finset.univ := fun heq => by
        have := congrArg Finset.card heq; rw [Finset.card_univ, hV] at this; omega
      obtain ⟨u, hu, v, hvnot, hGvu⟩ := hStrong Vp (by rw [hu0]; exact Finset.singleton_nonempty u0) hne_univ
      have hvVm : v ∈ Vm := Finset.mem_compl.mpr hvnot
      have hmem : (u, v) ∈ (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) := by
        rw [hall_cross]; exact Finset.mem_product.mpr ⟨hu, hvVm⟩
      exact not_adj_rev_of_tournament hG (Finset.mem_filter.mp hmem).2 hGvu
  -- Key counting inequality: 2 * e(Vp, Vm) >= p * (q + 1) >= 2 * (q + 1) > 2 * q!
  have he_gt_q : Vm.card < ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    have hle : Vp.card * (2 * (n - 1)) ≤ Vp.card * (Vp.card - 1) +
        2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      have : Vp.card * (2 * (n - 1)) = 2 * (Vp.card * (n - 1)) := by ring
      omega
    have hsplit : Vp.card * (2 * (n - 1)) = Vp.card * (Vp.card - 1) + Vp.card * (Vm.card + 1) := by
      have h2 : 2 * (n - 1) = (Vp.card - 1) + (Vm.card + 1) := by omega
      rw [h2, mul_add]
    have hmul : 2 * (Vm.card + 1) ≤ Vp.card * (Vm.card + 1) := Nat.mul_le_mul_right _ hVp_ge2
    omega
  let U := Vp.filter (fun x2 => ∃ y1 ∈ Vm, G.Adj x2 y1)
  have hU_ge2 : 2 ≤ U.card := by
    by_contra hlt
    have hsub : (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) ⊆ U ×ˢ Vm := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, U] at hp ⊢
      exact ⟨⟨hp.1.1, ⟨p.2, hp.1.2, hp.2⟩⟩, hp.1.2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_product] at hc
    have hle1 : U.card * Vm.card ≤ 1 * Vm.card := Nat.mul_le_mul_right Vm.card (by omega)
    rw [one_mul] at hle1
    omega
  obtain ⟨a, ha, b, hb, hab_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
  rcases adj_or_rev_of_isTournament hG hab_ne with hab | hba
  · obtain ⟨y1, hy1, hby1⟩ := (Finset.mem_filter.mp hb).2
    have haVp : a ∈ Vp := (Finset.mem_filter.mp ha).1
    have hbVp : b ∈ Vp := (Finset.mem_filter.mp hb).1
    refine ⟨a, b, y1, hab_ne, fun h => Finset.mem_compl.mp hy1 (h ▸ haVp),
      fun h => Finset.mem_compl.mp hy1 (h ▸ hbVp), hab, hby1,
      (Finset.mem_filter.mp haVp).2, hVm_deg y1 hy1⟩
  · obtain ⟨y1, hy1, hay1⟩ := (Finset.mem_filter.mp ha).2
    have haVp : a ∈ Vp := (Finset.mem_filter.mp ha).1
    have hbVp : b ∈ Vp := (Finset.mem_filter.mp hb).1
    refine ⟨b, a, y1, hab_ne.symm, fun h => Finset.mem_compl.mp hy1 (h ▸ hbVp),
      fun h => Finset.mem_compl.mp hy1 (h ▸ haVp), hba, hay1,
      (Finset.mem_filter.mp hbVp).2, hVm_deg y1 hy1⟩

-- Master Theorem for Module 4B: Every oriented tree with <= 3 internal vertices (n - k <= 3)
-- embeds in every 2-strong tournament on 2n - 2 vertices!
lemma embeds_internal_le_three {n : ℕ} (hn : 3 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (h2S : ∀ S : Finset V, S.card ≤ 1 → ∀ V1 : Finset V, Disjoint S V1 → V1.Nonempty →
      (S ∪ V1) ≠ Finset.univ → ∃ u ∈ V1, ∃ v, v ∉ S ∧ v ∉ V1 ∧ G.Adj v u)
    (hm_le : n - (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ 3) :
    Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  let L := Finset.univ.filter (fun w : W =>
    (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)
  let M := Lᶜ
  have hM_card_le : M.card ≤ 3 := by
    have h1 := Finset.card_add_card_compl L
    change L.card + M.card = Fintype.card W at h1
    change n - L.card ≤ 3 at hm_le
    omega
  have hdeg_eq : ∀ w : W, (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card =
      (Finset.univ.filter (fun z : W => T.Adj w z)).card := by
    intro w; congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => by rcases h with h1 | h2; exact hO.1 w z h1; exact (hO.1 z w h2).symm,
      fun h => adj_or_rev_of_isOrientation hO h⟩
  -- No two leaves are adjacent when n >= 3!
  have hno_leaf_leaf_T : ∀ x ∈ L, ∀ y ∈ L, ¬ T.Adj x y := by
    intro x hx y hy hTxy
    have hxy_ne : x ≠ y := T.ne_of_adj hTxy
    have hdegx : (Finset.univ.filter (fun z : W => T.Adj x z)).card = 1 := by
      rw [← hdeg_eq]; exact (Finset.mem_filter.mp hx).2
    have hdegy : (Finset.univ.filter (fun z : W => T.Adj y z)).card = 1 := by
      rw [← hdeg_eq]; exact (Finset.mem_filter.mp hy).2
    have hx_uniq : ∀ z : W, T.Adj x z → z = y := by
      intro z hxz
      obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hdegx
      have h1 : y ∈ ({w0} : Finset W) := hw0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy⟩
      have h2 : z ∈ ({w0} : Finset W) := hw0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩
      simp only [Finset.mem_singleton] at h1 h2; exact h2.trans h1.symm
    have hy_uniq : ∀ z : W, T.Adj y z → z = x := by
      intro z hyz
      obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hdegy
      have h1 : x ∈ ({w0} : Finset W) := hw0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy.symm⟩
      have h2 : z ∈ ({w0} : Finset W) := hw0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩
      simp only [Finset.mem_singleton] at h1 h2; exact h2.trans h1.symm
    have hex_z : ∃ z : W, z ≠ x ∧ z ≠ y := by
      have hpair : ({x, y} : Finset W).card < (Finset.univ : Finset W).card := by
        rw [Finset.card_pair hxy_ne, Finset.card_univ, hW]; omega
      obtain ⟨z, _, hznot⟩ := Finset.exists_mem_notMem_of_card_lt_card hpair
      simp only [Finset.mem_insert, Finset.mem_singleton] at hznot
      push Not at hznot; exact ⟨z, hznot⟩
    obtain ⟨z, hzx, hzy⟩ := hex_z
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath x z
    cases p with
    | nil => exact hzx rfl
    | @cons _ w _ hxw q' =>
      have hwy : w = y := hx_uniq w hxw
      subst hwy
      have hxnot : x ∉ q'.support := by
        have hnd := hp.support_nodup
        simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd; exact hnd.1
      cases q' with
      | nil => exact hzy rfl
      | @cons _ u _ hyu q'' =>
        have hux : u = x := hy_uniq u hyu
        subst hux
        exact hxnot (List.mem_cons_of_mem w q''.start_mem_support)
  -- Partition L into Lplus (indeg = 1, outdeg = 0) and Lminus (indeg = 0, outdeg = 1)
  let Lplus := L.filter (fun w => ∃ p : W, D.Adj p w)
  let Lminus := L.filter (fun w => ∃ p : W, D.Adj w p)
  have hL_leaf_deg : ∀ w ∈ L, ∃! p : W, T.Adj w p := by
    intro w hw
    have hdeg : (Finset.univ.filter (fun z : W => T.Adj w z)).card = 1 := by
      rw [← hdeg_eq]; exact (Finset.mem_filter.mp hw).2
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hdeg
    refine ⟨p, ?_, fun q hq => ?_⟩
    · have : p ∈ Finset.univ.filter (fun z : W => T.Adj w z) := hp.symm ▸ Finset.mem_singleton_self p
      exact (Finset.mem_filter.mp this).2
    · have : q ∈ ({p} : Finset W) := hp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
      exact Finset.mem_singleton.mp this
  have hLp_indeg : ∀ w ∈ Lplus, (Finset.univ.filter (fun z : W => D.Adj z w)).card = 1 := by
    intro w hw
    obtain ⟨hwL, p, hDpw⟩ := Finset.mem_filter.mp hw
    obtain ⟨p0, hp0, hp0u⟩ := hL_leaf_deg w hwL
    have hp_eq : p = p0 := hp0u p (hO.1 p w hDpw).symm
    subst hp_eq
    have heq : Finset.univ.filter (fun z : W => D.Adj z w) = {p} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hp0u z (hO.1 z w h).symm, fun h => h ▸ hDpw⟩
    rw [heq, Finset.card_singleton]
  have hLp_noout : ∀ w ∈ Lplus, ∀ z : W, ¬ D.Adj w z := by
    intro w hw z hDwz
    obtain ⟨hwL, p, hDpw⟩ := Finset.mem_filter.mp hw
    obtain ⟨p0, _, hp0u⟩ := hL_leaf_deg w hwL
    have h1 : p = p0 := hp0u p (hO.1 p w hDpw).symm
    have h2 : z = p0 := hp0u z (hO.1 w z hDwz)
    subst h1; subst h2
    exact not_adj_rev_of_isOrientation hO hDpw hDwz
  have hLm_outdeg : ∀ w ∈ Lminus, (Finset.univ.filter (fun z : W => D.Adj w z)).card = 1 := by
    intro w hw
    obtain ⟨hwL, p, hDwp⟩ := Finset.mem_filter.mp hw
    obtain ⟨p0, hp0, hp0u⟩ := hL_leaf_deg w hwL
    have hp_eq : p = p0 := hp0u p (hO.1 w p hDwp)
    subst hp_eq
    have heq : Finset.univ.filter (fun z : W => D.Adj w z) = {p} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hp0u z (hO.1 w z h), fun h => h ▸ hDwp⟩
    rw [heq, Finset.card_singleton]
  have hLm_noin : ∀ w ∈ Lminus, ∀ z : W, ¬ D.Adj z w := by
    intro w hw z hDzw
    obtain ⟨hwL, p, hDwp⟩ := Finset.mem_filter.mp hw
    obtain ⟨p0, _, hp0u⟩ := hL_leaf_deg w hwL
    have h1 : p = p0 := hp0u p (hO.1 w p hDwp)
    have h2 : z = p0 := hp0u z (hO.1 z w hDzw).symm
    subst h1; subst h2
    exact not_adj_rev_of_isOrientation hO hDwp hDzw
  have hL_part : ∀ w ∈ L, w ∈ Lplus ∨ w ∈ Lminus := by
    intro w hw
    obtain ⟨p, hp, _⟩ := hL_leaf_deg w hw
    rcases adj_or_rev_of_isOrientation hO hp with h | h
    · exact Or.inr (Finset.mem_filter.mpr ⟨hw, p, h⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hw, p, h⟩)
  have hLpm_disj : Disjoint Lplus Lminus := Finset.disjoint_left.mpr (fun w hp hm => by
    obtain ⟨_, z, hDwz⟩ := Finset.mem_filter.mp hm
    exact hLp_noout w hp z hDwz)
  -- Show M is nonempty and T.induce M is a tree!
  have hM_nonempty : M.Nonempty := by
    by_contra hempty
    have hM0 : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hLuniv : L = Finset.univ := by
      ext w; simp only [Finset.mem_univ, iff_true]
      by_contra hnot; have : w ∈ M := Finset.mem_compl.mpr hnot; rw [hM0] at this; exact Finset.notMem_empty w this
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card W)
    obtain ⟨p⟩ := hT.connected x y
    cases p with
    | nil => exact hxy rfl
    | @cons _ w _ hxw _ =>
      exact hno_leaf_leaf_T x (hLuniv ▸ Finset.mem_univ x) w (hLuniv ▸ Finset.mem_univ w) hxw
  have hT_M : (T.induce (M : Set W)).IsTree := by
    refine ⟨?_, hT.isAcyclic.induce _⟩
    obtain ⟨m0, hm0⟩ := hM_nonempty
    have : Nonempty M := ⟨⟨m0, hm0⟩⟩
    refine SimpleGraph.Connected.mk (fun a b => ?_)
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath a.1 b.1
    have hsupp : ∀ (x0 y0 : W) (q : T.Walk x0 y0), q.IsPath → x0 ∈ M → y0 ∈ M →
        ∀ w ∈ q.support, w ∈ M := by
      intro x0 y0 q hq hx0 hy0
      induction q with
      | nil =>
        intro w hw; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        exact hw ▸ hx0
      | @cons a1 b1 c1 hab q' ih =>
        have hb1M : b1 ∈ M := by
          cases q' with
          | nil => exact hy0
          | @cons _ d1 _ hbd q'' =>
            have hne : a1 ≠ d1 := by
              intro heq; subst heq
              have hnd := hq.support_nodup
              simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
              exact hnd.1 (List.mem_cons_of_mem b1 q''.start_mem_support)
            have hsub : ({a1, d1} : Finset W) ⊆ Finset.univ.filter (fun z : W => T.Adj b1 z) := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              rcases hz with rfl | rfl
              · exact hab.symm
              · exact hbd
            have hge2 : 2 ≤ (Finset.univ.filter (fun z : W => T.Adj b1 z)).card := by
              have := Finset.card_le_card hsub; rw [Finset.card_pair hne] at this; exact this
            refine Finset.mem_compl.mpr (fun hbL => ?_)
            have h1 := (Finset.mem_filter.mp hbL).2
            rw [hdeg_eq] at h1; omega
        intro w hw; simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw'
        · exact hx0
        · exact ih hq.of_cons hb1M hy0 w hw'
    have hlift : ∀ (x0 y0 : W) (q : T.Walk x0 y0), (hx0 : x0 ∈ M) → (hy0 : y0 ∈ M) →
        (∀ w ∈ q.support, w ∈ M) → (T.induce (M : Set W)).Reachable ⟨x0, hx0⟩ ⟨y0, hy0⟩ := by
      intro x0 y0 q hx0 hy0 hqM
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a1 b1 c1 hab q' ih =>
        have hbM : b1 ∈ M := hqM b1 (List.mem_cons_of_mem a1 q'.start_mem_support)
        have hstep : (T.induce (M : Set W)).Adj ⟨a1, hx0⟩ ⟨b1, hbM⟩ := hab
        exact hstep.reachable.trans (ih hbM hy0 (fun w hw => hqM w (List.mem_cons_of_mem a1 hw)))
    exact hlift a.1 b.1 p a.2 b.2 (hsupp a.1 b.1 p hp a.2 b.2)
  -- Case split on M.card ∈ {1, 2, 3}!
  have hM_pos : 1 ≤ M.card := Finset.one_le_card.mpr hM_nonempty
  have hM_cases : M.card = 1 ∨ M.card = 2 ∨ M.card = 3 := by omega
  rcases hM_cases with hM1 | hM2 | hM3
  · -- Case M.card = 1: Star -> embeds_bi_arborescence!
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hM1
    refine embeds_bi_arborescence (by omega) D hW ⟨T, hT, hO⟩ G hV hG ⟨r, Lplus, ?_, hLp_indeg, ?_, ?_⟩
    · intro hrp
      have hrL : r ∈ L := (Finset.mem_filter.mp hrp).1
      have hrM : r ∈ M := hr.symm ▸ Finset.mem_singleton_self r
      exact Finset.mem_compl.mp hrM hrL
    · intro v hvr hvnot
      have hvL : v ∈ L := by
        by_contra hnot
        have hvM : v ∈ M := Finset.mem_compl.mpr hnot
        rw [hr, Finset.mem_singleton] at hvM; exact hvr hvM
      have hvLm : v ∈ Lminus := (hL_part v hvL).resolve_left hvnot
      exact hLm_outdeg v hvLm
    · intro u hu v hvr hvnot
      have huL : u ∈ L := (Finset.mem_filter.mp hu).1
      have hvL : v ∈ L := by
        by_contra hnot
        have hvM : v ∈ M := Finset.mem_compl.mpr hnot
        rw [hr, Finset.mem_singleton] at hvM; exact hvr hvM
      exact ⟨fun h => hno_leaf_leaf_T u huL v hvL (hO.1 u v h),
        fun h => hno_leaf_leaf_T v hvL u huL (hO.1 v u h)⟩
  · -- Case M.card = 2: Double star -> embeds_heart_two!
    obtain ⟨u0, v0, huv_ne, hM_eq⟩ := Finset.card_eq_two.mp hM2
    have hu0M : u0 ∈ M := hM_eq.symm ▸ Finset.mem_insert_self u0 {v0}
    have hv0M : v0 ∈ M := hM_eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v0)
    have hTuv : T.Adj u0 v0 := by
      obtain ⟨p⟩ := hT_M.connected ⟨u0, hu0M⟩ ⟨v0, hv0M⟩
      cases p with
      | nil => exact absurd rfl huv_ne
      | @cons _ w _ hstep _ =>
        have hwM : w.1 ∈ ({u0, v0} : Finset W) := hM_eq ▸ w.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with hwu | hwv
        · exact absurd hwu.symm (T.ne_of_adj hstep)
        · exact hwv ▸ hstep
    have hrun : ∀ a b : W, D.Adj a b → M = {a, b} → Embeds D G := by
      intro a b hDab hMab
      refine embeds_heart_two (by omega) D hW ⟨T, hT, hO⟩ G hV hG ⟨a, b, hDab, Lplus, ?_, ?_, hLp_indeg, ?_, ?_⟩
      · intro hap
        have haM : a ∈ M := hMab.symm ▸ Finset.mem_insert_self a {b}
        exact Finset.mem_compl.mp haM (Finset.mem_filter.mp hap).1
      · intro hbp
        have hbM : b ∈ M := hMab.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
        exact Finset.mem_compl.mp hbM (Finset.mem_filter.mp hbp).1
      · intro y hya hyb hynot
        have hyL : y ∈ L := by
          by_contra hnot
          have hyM : y ∈ M := Finset.mem_compl.mpr hnot
          rw [hMab] at hyM; simp only [Finset.mem_insert, Finset.mem_singleton] at hyM
          rcases hyM with rfl | rfl <;> contradiction
        exact hLm_outdeg y ((hL_part y hyL).resolve_left hynot)
      · intro x hx y hya hyb hynot
        have hxL : x ∈ L := (Finset.mem_filter.mp hx).1
        have hyL : y ∈ L := by
          by_contra hnot
          have hyM : y ∈ M := Finset.mem_compl.mpr hnot
          rw [hMab] at hyM; simp only [Finset.mem_insert, Finset.mem_singleton] at hyM
          rcases hyM with rfl | rfl <;> contradiction
        exact ⟨fun h => hno_leaf_leaf_T x hxL y hyL (hO.1 x y h),
          fun h => hno_leaf_leaf_T y hyL x hxL (hO.1 y x h)⟩
    rcases adj_or_rev_of_isOrientation hO hTuv with h | h
    · exact hrun u0 v0 h hM_eq
    · exact hrun v0 u0 h (by rw [hM_eq, Finset.pair_comm])
  · -- Case M.card = 3: M = {a, b, c}, T[M] is a 3-vertex tree (center y, leaves x and z)!
    obtain ⟨a, b, c, hab, hac, hbc, hM_eq⟩ := Finset.card_eq_three.mp hM3
    -- Extract center y and leaves x, z of T[M] (3-vertex tree has 2 edges, no triangle!)
    have hcenter : ∃ y x z : W, y ≠ x ∧ y ≠ z ∧ x ≠ z ∧ M = {y, x, z} ∧
        T.Adj y x ∧ T.Adj y z ∧ ¬ T.Adj x z := by
      have ha_mem : a ∈ M := hM_eq.symm ▸ Finset.mem_insert_self a _
      have hb_mem : b ∈ M := hM_eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
      have hc_mem : c ∈ M := hM_eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
      -- Helper: any 2 distinct vertices in M that are NOT adjacent must both be adjacent to the 3rd!
      have hnot_tri : ¬ (T.Adj a b ∧ T.Adj b c ∧ T.Adj c a) := by
        rintro ⟨h1, h2, h3⟩
        let p1 : T.Walk a c := SimpleGraph.Walk.cons h3.symm SimpleGraph.Walk.nil
        let p2 : T.Walk a c := SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)
        have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hac])
        have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.cons
          (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hbc]))
          (by simp [hab, hac])
        have heq : p1 = p2 := congrArg Subtype.val
          ((hT.isAcyclic.subsingleton_path a c).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩)
        have hlen := congrArg SimpleGraph.Walk.length heq
        simp [p1, p2] at hlen
      -- Every vertex in M has a neighbor in M (by connectedness of T.induce M)
      have hhas_nbr : ∀ u : M, ∃ v : M, T.Adj u.1 v.1 := by
        intro u
        obtain ⟨v0, hv0⟩ : ∃ v0 : M, v0 ≠ u := by
          by_cases hua : u.1 = a
          · exact ⟨⟨b, hb_mem⟩, fun h => hab (hua.symm.trans (congrArg Subtype.val h).symm)⟩
          · exact ⟨⟨a, ha_mem⟩, fun h => hua (congrArg Subtype.val h).symm⟩
        obtain ⟨p⟩ := hT_M.connected u v0
        cases p with
        | nil => exact absurd rfl hv0
        | @cons _ w _ hadj _ => exact ⟨w, hadj⟩
      -- Case split on the 3 possible edges ab, bc, ac!
      by_cases h1 : T.Adj a b <;> by_cases h2 : T.Adj b c <;> by_cases h3 : T.Adj a c
      · exact absurd ⟨h1, h2, h3.symm⟩ hnot_tri
      · exact ⟨b, a, c, hab.symm, hbc, hac, by
          ext w; simp only [hM_eq, Finset.mem_insert, Finset.mem_singleton]; tauto, h1.symm, h2, h3⟩
      · exact ⟨a, b, c, hab, hac, hbc, hM_eq, h1, h3, h2⟩
      · exfalso
        obtain ⟨w, hw⟩ := hhas_nbr ⟨c, hc_mem⟩
        have hwM : w.1 ∈ ({a, b, c} : Finset W) := hM_eq ▸ w.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with hwa | hwb | hwc
        · exact h3 (hwa ▸ hw).symm
        · exact h2 (hwb ▸ hw).symm
        · exact T.ne_of_adj hw hwc.symm
      · exact ⟨c, a, b, hac.symm, hbc.symm, hab, by
          ext w; simp only [hM_eq, Finset.mem_insert, Finset.mem_singleton]; tauto, h3.symm, h2.symm, h1⟩
      · exfalso
        obtain ⟨w, hw⟩ := hhas_nbr ⟨a, ha_mem⟩
        have hwM : w.1 ∈ ({a, b, c} : Finset W) := hM_eq ▸ w.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with hwa | hwb | hwc
        · exact T.ne_of_adj hw hwa.symm
        · exact h1 (hwb ▸ hw)
        · exact h3 (hwc ▸ hw)
      · exfalso
        obtain ⟨w, hw⟩ := hhas_nbr ⟨b, hb_mem⟩
        have hwM : w.1 ∈ ({a, b, c} : Finset W) := hM_eq ▸ w.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with hwa | hwb | hwc
        · exact h1 (hwa ▸ hw).symm
        · exact T.ne_of_adj hw hwb.symm
        · exact h2 (hwc ▸ hw)
      · exfalso
        obtain ⟨w, hw⟩ := hhas_nbr ⟨a, ha_mem⟩
        have hwM : w.1 ∈ ({a, b, c} : Finset W) := hM_eq ▸ w.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with hwa | hwb | hwc
        · exact T.ne_of_adj hw hwa.symm
        · exact h1 (hwb ▸ hw)
        · exact h3 (hwc ▸ hw)
    obtain ⟨y, x, z, hyx, hyz, hxz, hMyxz, hTyx, hTyz, hnoTxz⟩ := hcenter
    -- Common leaf partition properties for {y, x, z}
    have hpart_yxz : ∀ w : W, w = y ∨ w = x ∨ w = z ∨ w ∈ Lplus ∨ w ∈ Lminus := by
      intro w
      by_cases hwL : w ∈ L
      · rcases hL_part w hwL with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · have hwM : w ∈ M := Finset.mem_compl.mpr hwL
        rw [hMyxz] at hwM; simp only [Finset.mem_insert, Finset.mem_singleton] at hwM
        rcases hwM with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
    have hyM : y ∈ M := hMyxz.symm ▸ Finset.mem_insert_self y _
    have hxM : x ∈ M := hMyxz.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self x _)
    have hzM : z ∈ M := hMyxz.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
    have hdp_yxz : y ∉ Lplus ∧ x ∉ Lplus ∧ z ∉ Lplus :=
      ⟨fun h => Finset.mem_compl.mp hyM (Finset.mem_filter.mp h).1,
       fun h => Finset.mem_compl.mp hxM (Finset.mem_filter.mp h).1,
       fun h => Finset.mem_compl.mp hzM (Finset.mem_filter.mp h).1⟩
    have hdm_yxz : y ∉ Lminus ∧ x ∉ Lminus ∧ z ∉ Lminus :=
      ⟨fun h => Finset.mem_compl.mp hyM (Finset.mem_filter.mp h).1,
       fun h => Finset.mem_compl.mp hxM (Finset.mem_filter.mp h).1,
       fun h => Finset.mem_compl.mp hzM (Finset.mem_filter.mp h).1⟩
    have hno_ll : ∀ a1 b1 : W, (a1 ∈ Lplus ∨ a1 ∈ Lminus) → (b1 ∈ Lplus ∨ b1 ∈ Lminus) → ¬ D.Adj a1 b1 := by
      intro a1 b1 ha1 hb1 hDab
      have haL : a1 ∈ L := by rcases ha1 with h | h <;> exact (Finset.mem_filter.mp h).1
      have hbL : b1 ∈ L := by rcases hb1 with h | h <;> exact (Finset.mem_filter.mp h).1
      exact hno_leaf_leaf_T a1 haL b1 hbL (hO.1 a1 b1 hDab)
    have hLpu_yxz : ∀ w ∈ Lplus, (D.Adj y w ∧ ¬ D.Adj x w ∧ ¬ D.Adj z w) ∨
        (D.Adj x w ∧ ¬ D.Adj y w ∧ ¬ D.Adj z w) ∨ (D.Adj z w ∧ ¬ D.Adj y w ∧ ¬ D.Adj x w) := by
      intro w hw
      obtain ⟨hwL, p, hDpw⟩ := Finset.mem_filter.mp hw
      obtain ⟨p0, _, hp0u⟩ := hL_leaf_deg w hwL
      have hp_eq : p = p0 := hp0u p (hO.1 p w hDpw).symm
      subst hp_eq
      have hpM : p ∈ M := Finset.mem_compl.mpr (fun hpL => hno_leaf_leaf_T p hpL w hwL (hO.1 p w hDpw))
      rw [hMyxz] at hpM; simp only [Finset.mem_insert, Finset.mem_singleton] at hpM
      rcases hpM with rfl | rfl | rfl
      · exact Or.inl ⟨hDpw, fun h => hyx (hp0u x (hO.1 x w h).symm).symm,
          fun h => hyz (hp0u z (hO.1 z w h).symm).symm⟩
      · exact Or.inr (Or.inl ⟨hDpw, fun h => hyx (hp0u y (hO.1 y w h).symm),
          fun h => hxz (hp0u z (hO.1 z w h).symm).symm⟩)
      · exact Or.inr (Or.inr ⟨hDpw, fun h => hyz (hp0u y (hO.1 y w h).symm),
          fun h => hxz (hp0u x (hO.1 x w h).symm)⟩)
    have hLmu_yxz : ∀ w ∈ Lminus, (D.Adj w y ∧ ¬ D.Adj w x ∧ ¬ D.Adj w z) ∨
        (D.Adj w x ∧ ¬ D.Adj w y ∧ ¬ D.Adj w z) ∨ (D.Adj w z ∧ ¬ D.Adj w y ∧ ¬ D.Adj w x) := by
      intro w hw
      obtain ⟨hwL, p, hDwp⟩ := Finset.mem_filter.mp hw
      obtain ⟨p0, _, hp0u⟩ := hL_leaf_deg w hwL
      have hp_eq : p = p0 := hp0u p (hO.1 w p hDwp)
      subst hp_eq
      have hpM : p ∈ M := Finset.mem_compl.mpr (fun hpL => hno_leaf_leaf_T w hwL p hpL (hO.1 w p hDwp))
      rw [hMyxz] at hpM; simp only [Finset.mem_insert, Finset.mem_singleton] at hpM
      rcases hpM with rfl | rfl | rfl
      · exact Or.inl ⟨hDwp, fun h => hyx (hp0u x (hO.1 w x h)).symm,
          fun h => hyz (hp0u z (hO.1 w z h)).symm⟩
      · exact Or.inr (Or.inl ⟨hDwp, fun h => hyx (hp0u y (hO.1 w y h)),
          fun h => hxz (hp0u z (hO.1 w z h)).symm⟩)
      · exact Or.inr (Or.inr ⟨hDwp, fun h => hyz (hp0u y (hO.1 w y h)),
          fun h => hxz (hp0u x (hO.1 w x h))⟩)
    have hnoDxz : ¬ D.Adj x z ∧ ¬ D.Adj z x := ⟨fun h => hnoTxz (hO.1 x z h), fun h => hnoTxz (hO.1 z x h).symm⟩
    -- Helper for P_3^+ (x0 -> y -> z0) covering all 3 subcases!
    have hP3_solve : ∀ x0 z0 : W, x0 ≠ y → x0 ≠ z0 → y ≠ z0 →
        D.Adj x0 y → D.Adj y z0 → (¬ D.Adj x0 z0 ∧ ¬ D.Adj z0 x0) →
        (∀ w : W, w = x0 ∨ w = y ∨ w = z0 ∨ w ∈ Lplus ∨ w ∈ Lminus) →
        (x0 ∉ Lplus ∧ y ∉ Lplus ∧ z0 ∉ Lplus) →
        (x0 ∉ Lminus ∧ y ∉ Lminus ∧ z0 ∉ Lminus) →
        (∀ w ∈ Lplus, (D.Adj x0 w ∧ ¬ D.Adj y w ∧ ¬ D.Adj z0 w) ∨
          (D.Adj y w ∧ ¬ D.Adj x0 w ∧ ¬ D.Adj z0 w) ∨ (D.Adj z0 w ∧ ¬ D.Adj x0 w ∧ ¬ D.Adj y w)) →
        (∀ w ∈ Lminus, (D.Adj w x0 ∧ ¬ D.Adj w y ∧ ¬ D.Adj w z0) ∨
          (D.Adj w y ∧ ¬ D.Adj w x0 ∧ ¬ D.Adj w z0) ∨ (D.Adj w z0 ∧ ¬ D.Adj w x0 ∧ ¬ D.Adj w y)) →
        Embeds D G := by
      intro x0 z0 hx0y hx0z hyz0 hDx0y hDyz0 hnox0z hpart' hdp' hdm' hLpu' hLmu'
      by_cases hayz : 1 ≤ (Lplus.filter (fun w => D.Adj y w)).card + (Lplus.filter (fun w => D.Adj z0 w)).card
      · exact embeds_three_core_P3plus_shifted hW hO hV hG hx0y hx0z hyz0 hDx0y hDyz0 hnox0z
          hpart' hdp' hdm' hLpm_disj hno_ll hLp_noout hLm_noin hLpu' hLmu' hayz
      · by_cases hbxy : 1 ≤ (Lminus.filter (fun w => D.Adj w y)).card + (Lminus.filter (fun w => D.Adj w x0)).card
        · -- Subcase 2: Reverse D and G! Now z0 -> y -> x0 with Lminus becoming Lplus!
          let Drev : Digraph W := ⟨fun u v => D.Adj v u⟩
          let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
          have hOrev : Drev.IsOrientation T :=
            ⟨fun u v h => (hO.1 v u h).symm, fun u v h => hO.2 v u h.symm⟩
          have hGrev : Grev.IsTournament :=
            ⟨fun u => hG.1 u, fun u v hne => hG.2 v u hne.symm⟩
          have hpart_rev : ∀ w : W, w = z0 ∨ w = y ∨ w = x0 ∨ w ∈ Lminus ∨ w ∈ Lplus := fun w => by
            rcases hpart' w with h | h | h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          have hLpu_rev : ∀ w ∈ Lminus,
              (Drev.Adj z0 w ∧ ¬ Drev.Adj y w ∧ ¬ Drev.Adj x0 w) ∨
              (Drev.Adj y w ∧ ¬ Drev.Adj z0 w ∧ ¬ Drev.Adj x0 w) ∨
              (Drev.Adj x0 w ∧ ¬ Drev.Adj z0 w ∧ ¬ Drev.Adj y w) := fun w hw => by
            rcases hLmu' w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
            · exact Or.inr (Or.inr ⟨h1, h3, h2⟩)
            · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
            · exact Or.inl ⟨h1, h3, h2⟩
          have hLmu_rev : ∀ w ∈ Lplus,
              (Drev.Adj w z0 ∧ ¬ Drev.Adj w y ∧ ¬ Drev.Adj w x0) ∨
              (Drev.Adj w y ∧ ¬ Drev.Adj w z0 ∧ ¬ Drev.Adj w x0) ∨
              (Drev.Adj w x0 ∧ ¬ Drev.Adj w z0 ∧ ¬ Drev.Adj w y) := fun w hw => by
            rcases hLpu' w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
            · exact Or.inr (Or.inr ⟨h1, h3, h2⟩)
            · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
            · exact Or.inl ⟨h1, h3, h2⟩
          exact embeds_rev (embeds_three_core_P3plus_shifted (D := Drev) (G := Grev)
            hW hOrev hV hGrev hyz0.symm hx0z.symm hx0y.symm hDyz0 hDx0y ⟨hnox0z.1, hnox0z.2⟩
            hpart_rev ⟨hdm'.2.2, hdm'.2.1, hdm'.1⟩ ⟨hdp'.2.2, hdp'.2.1, hdp'.1⟩ hLpm_disj.symm
            (fun a1 b1 ha1 hb1 h => hno_ll b1 a1 hb1.symm ha1.symm h)
            (fun a1 ha1 b1 => hLm_noin a1 ha1 b1) (fun a1 ha1 b1 => hLp_noout a1 ha1 b1)
            hLpu_rev hLmu_rev hbxy)
        · -- Subcase 3: ay = az = bx = by = 0! All Lplus attach to x0, all Lminus attach to z0!
          have hStrong : ∀ V1 : Finset V, V1.Nonempty → V1 ≠ Finset.univ →
              ∃ u ∈ V1, ∃ v ∉ V1, G.Adj v u := by
            intro V1 hne hnu
            obtain ⟨u, hu, v, _, hv1, hvu⟩ := h2S ∅ (by simp) V1 (Finset.disjoint_empty_left V1) hne
              (by simpa using hnu)
            exact ⟨u, hu, v, hv1, hvu⟩
          obtain ⟨t0, t1, t2, ht01, ht02, ht12, hGt01, hGt12, ht0_out, ht2_in⟩ :=
            exists_two_path_Vplus_to_Vminus hn hV hG hStrong
          have hn_eq : n = Lplus.card + Lminus.card + 3 := by
            let M0 : Finset W := {x0, y, z0}
            have hM0card : M0.card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp [hyz0]
              · simp [hx0y, hx0z]
            have hd1 : Disjoint M0 Lplus := Finset.disjoint_left.mpr (fun w hw => by
              simp only [M0, Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl
              · exact hdp'.1
              · exact hdp'.2.1
              · exact hdp'.2.2)
            have hd2 : Disjoint (M0 ∪ Lplus) Lminus := Finset.disjoint_left.mpr (fun w hw => by
              rcases Finset.mem_union.mp hw with hwM | hwP
              · simp only [M0, Finset.mem_insert, Finset.mem_singleton] at hwM
                rcases hwM with rfl | rfl | rfl
                · exact hdm'.1
                · exact hdm'.2.1
                · exact hdm'.2.2
              · exact Finset.disjoint_left.mp hLpm_disj hwP)
            have huniv : M0 ∪ Lplus ∪ Lminus = Finset.univ := by
              ext w; simp only [Finset.mem_union, Finset.mem_univ, iff_true, M0,
                Finset.mem_insert, Finset.mem_singleton]
              rcases hpart' w with h | h | h | h | h
              · exact Or.inl (Or.inl (Or.inl h))
              · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
              · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
              · exact Or.inl (Or.inr h)
              · exact Or.inr h
            have hc := congrArg Finset.card huniv
            rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hM0card,
              Finset.card_univ, hW] at hc
            omega
          -- Pick SA ⊆ N+(t0) \ {t0, t1, t2} of size Lplus.card
          have hSA_ge : Lplus.card ≤ ((Finset.univ.filter (fun u : V => G.Adj t0 u)) \ {t1, t2}).card := by
            have h1 := Finset.le_card_sdiff ({t1, t2} : Finset V) (Finset.univ.filter (fun u : V => G.Adj t0 u))
            have h2 : ({t1, t2} : Finset V).card = 2 := Finset.card_pair ht12
            omega
          obtain ⟨SA, hSAsub, hSAcard⟩ := Finset.exists_subset_card_eq hSA_ge
          -- Pick SB ⊆ N-(t2) \ ({t0, t1} ∪ SA) of size Lminus.card
          have hSB_ge : Lminus.card ≤ ((Finset.univ.filter (fun u : V => G.Adj u t2)) \ ({t0, t1} ∪ SA)).card := by
            have h1 := Finset.le_card_sdiff ({t0, t1} ∪ SA) (Finset.univ.filter (fun u : V => G.Adj u t2))
            have h2 := Finset.card_union_le ({t0, t1} : Finset V) SA
            have h3 : ({t0, t1} : Finset V).card = 2 := Finset.card_pair ht01
            omega
          obtain ⟨SB, hSBsub, hSBcard⟩ := Finset.exists_subset_card_eq hSB_ge
          let eR : Lplus ≃ SA := Fintype.equivOfCardEq (by simp [hSAcard])
          let eL : Lminus ≃ SB := Fintype.equivOfCardEq (by simp [hSBcard])
          have hLp_all_x0 : ∀ w ∈ Lplus, D.Adj x0 w ∧ ¬ D.Adj y w ∧ ¬ D.Adj z0 w := by
            intro w hw
            rcases hLpu' w hw with h | h | h
            · exact h
            · exfalso
              have : 1 ≤ (Lplus.filter (fun w => D.Adj y w)).card :=
                Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, h.1⟩⟩
              omega
            · exfalso
              have : 1 ≤ (Lplus.filter (fun w => D.Adj z0 w)).card :=
                Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, h.1⟩⟩
              omega
          have hLm_all_z0 : ∀ w ∈ Lminus, D.Adj w z0 ∧ ¬ D.Adj w x0 ∧ ¬ D.Adj w y := by
            intro w hw
            rcases hLmu' w hw with h | h | h
            · exfalso
              have : 1 ≤ (Lminus.filter (fun w => D.Adj w x0)).card :=
                Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, h.1⟩⟩
              omega
            · exfalso
              have : 1 ≤ (Lminus.filter (fun w => D.Adj w y)).card :=
                Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, h.1⟩⟩
              omega
            · exact h
          refine glue_three_core hO hx0y hx0z hyz0 hpart' hdp' hdm' hLpm_disj hno_ll hLp_noout hLm_noin
            ht01 ht02 ht12 ?_ (fun w => (eR w).1) (fun a b h => eR.injective (Subtype.ext h)) ?_ ?_
            (fun w => (eL w).1) (fun a b h => eL.injective (Subtype.ext h)) ?_ ?_ ?_
          · intro a1 b1 ha1 hb1 hab
            rcases ha1 with rfl | rfl | rfl <;> rcases hb1 with rfl | rfl | rfl
            · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
            · simp only [↓reduceIte, hx0y.symm]; exact hGt01
            · exact absurd hab hnox0z.1
            · exact absurd hab (not_adj_rev_of_isOrientation hO hDx0y)
            · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
            · simp only [↓reduceIte, hx0y.symm, hx0z.symm, hyz0.symm]; exact hGt12
            · exact absurd hab hnox0z.2
            · exact absurd hab (not_adj_rev_of_isOrientation hO hDyz0)
            · exact absurd hab (not_adj_rev_of_isOrientation hO hab)
          · intro w
            have hmem := Finset.mem_sdiff.mp (hSAsub (eR w).2)
            have hadj : G.Adj t0 (eR w).1 := (Finset.mem_filter.mp hmem.1).2
            have hnot := hmem.2; simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
            push Not at hnot
            exact ⟨(ne_of_adj_tournament hG hadj).symm, hnot.1, hnot.2⟩
          · intro w
            have hmem := Finset.mem_sdiff.mp (hSAsub (eR w).2)
            have hadj : G.Adj t0 (eR w).1 := (Finset.mem_filter.mp hmem.1).2
            exact ⟨fun _ => hadj, fun h => absurd h (hLp_all_x0 w.1 w.2).2.1,
              fun h => absurd h (hLp_all_x0 w.1 w.2).2.2⟩
          · intro w
            have hmem := Finset.mem_sdiff.mp (hSBsub (eL w).2)
            have hadj : G.Adj (eL w).1 t2 := (Finset.mem_filter.mp hmem.1).2
            have hnot := hmem.2
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hnot
            push Not at hnot
            exact ⟨hnot.1.1, hnot.1.2, ne_of_adj_tournament hG hadj⟩
          · intro w
            have hmem := Finset.mem_sdiff.mp (hSBsub (eL w).2)
            have hadj : G.Adj (eL w).1 t2 := (Finset.mem_filter.mp hmem.1).2
            exact ⟨fun h => absurd h (hLm_all_z0 w.1 w.2).2.1,
              fun h => absurd h (hLm_all_z0 w.1 w.2).2.2, fun _ => hadj⟩
          · intro a1 b1 heq
            have hmem := Finset.mem_sdiff.mp (hSBsub (eL b1).2)
            exact hmem.2 (Finset.mem_union_right _ (heq ▸ (eR a1).2))
    -- Now dispatch on the 4 orientations of (x - y) and (y - z)!
    rcases adj_or_rev_of_isOrientation hO hTyx with hDyx | hDxy <;>
    rcases adj_or_rev_of_isOrientation hO hTyz with hDyz | hDzy
    · -- S_3^+: y -> x, y -> z
      exact embeds_three_core_S3plus hW hO hV hG hyx hyz hxz hDyx hDyz hnoDxz
        hpart_yxz hdp_yxz hdm_yxz hLpm_disj hno_ll hLp_noout hLm_noin hLpu_yxz hLmu_yxz
    · -- P_3^+: z -> y -> x
      exact hP3_solve z x hyz.symm hxz.symm hyx hDzy hDyx ⟨hnoDxz.2, hnoDxz.1⟩
        (fun w => by rcases hpart_yxz w with h | h | h | h | h
                     · exact Or.inr (Or.inl h)
                     · exact Or.inr (Or.inr (Or.inl h))
                     · exact Or.inl h
                     · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
                     · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
        ⟨hdp_yxz.2.2, hdp_yxz.1, hdp_yxz.2.1⟩ ⟨hdm_yxz.2.2, hdm_yxz.1, hdm_yxz.2.1⟩
        (fun w hw => by rcases hLpu_yxz w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
                        · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
                        · exact Or.inr (Or.inr ⟨h1, h3, h2⟩)
                        · exact Or.inl ⟨h1, h2, h3⟩)
        (fun w hw => by rcases hLmu_yxz w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
                        · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
                        · exact Or.inr (Or.inr ⟨h1, h3, h2⟩)
                        · exact Or.inl ⟨h1, h2, h3⟩)
    · -- P_3^+: x -> y -> z
      exact hP3_solve x z hyx.symm hxz hyz hDxy hDyz hnoDxz
        (fun w => by rcases hpart_yxz w with h | h | h | h | h
                     · exact Or.inr (Or.inl h)
                     · exact Or.inl h
                     · exact Or.inr (Or.inr (Or.inl h))
                     · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
                     · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
        ⟨hdp_yxz.2.1, hdp_yxz.1, hdp_yxz.2.2⟩ ⟨hdm_yxz.2.1, hdm_yxz.1, hdm_yxz.2.2⟩
        (fun w hw => by rcases hLpu_yxz w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
                        · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
                        · exact Or.inl ⟨h1, h2, h3⟩
                        · exact Or.inr (Or.inr ⟨h1, h3, h2⟩))
        (fun w hw => by rcases hLmu_yxz w hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
                        · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
                        · exact Or.inl ⟨h1, h2, h3⟩
                        · exact Or.inr (Or.inr ⟨h1, h3, h2⟩))
    · -- S_3^-: x -> y, z -> y (exact arc-reversal of S_3^+!)
      let Drev : Digraph W := ⟨fun u v => D.Adj v u⟩
      let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
      have hOrev : Drev.IsOrientation T :=
        ⟨fun u v h => (hO.1 v u h).symm, fun u v h => hO.2 v u h.symm⟩
      have hGrev : Grev.IsTournament :=
        ⟨fun u => hG.1 u, fun u v hne => hG.2 v u hne.symm⟩
      exact embeds_rev (embeds_three_core_S3plus (D := Drev) (G := Grev)
        hW hOrev hV hGrev hyx hyz hxz hDxy hDzy ⟨hnoDxz.2, hnoDxz.1⟩
        (fun w => by rcases hpart_yxz w with h | h | h | h | h
                     · exact Or.inl h
                     · exact Or.inr (Or.inl h)
                     · exact Or.inr (Or.inr (Or.inl h))
                     · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
                     · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
        hdm_yxz hdp_yxz hLpm_disj.symm
        (fun a1 b1 ha1 hb1 h => hno_ll b1 a1 hb1.symm ha1.symm h)
        (fun a1 ha1 b1 => hLm_noin a1 ha1 b1) (fun a1 ha1 b1 => hLp_noout a1 ha1 b1)
        hLmu_yxz hLpu_yxz)

lemma card_leaves_ge_two {n : ℕ} (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D) :
    2 ≤ (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := by
  classical
  obtain ⟨T, hT, hO⟩ := hD
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v1, v2, hv12, hv1, hv2⟩ := hT.exists_ne_and_degree_eq_one
  have hdeg_eq : ∀ w : W, (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card =
      T.degree w := by
    intro w
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1; ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => by rcases h with h1 | h2; exact hO.1 w z h1; exact (hO.1 z w h2).symm,
      fun h => adj_or_rev_of_isOrientation hO h⟩
  have hsub : ({v1, v2} : Finset W) ⊆ Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1) := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hdeg_eq]; rcases hw with rfl | rfl
    · exact hv1
    · exact hv2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hv12] at hc
  exact hc

end Module4B

theorem main : H1 → H2 → H3 → type_of% @SumnerUniversalTournamentConjecture.sumner_conjecture := by
  intro hH1 hH2 hH3 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn W _ _ D _ hW hD V _ _ G _ hV hG
    by_cases hn2 : n = 2
    · subst hn2
      exact sumner_n_eq_2 D hW hD G hV hG
    have hn3 : 3 ≤ n := by omega
    by_cases hn3eq : n = 3
    · subst hn3eq
      exact twoStrong_reduction (by omega) (fun m hm2 hmn => ih m hmn hm2) D hW hD G hV hG
        (not_twoStrong_of_card_four G (by omega) hG)
    by_cases h2S : ∀ S : Finset V, S.card ≤ 1 → ∀ V1 : Finset V, Disjoint S V1 → V1.Nonempty →
        (S ∪ V1) ≠ Finset.univ → ∃ u ∈ V1, ∃ v, v ∉ S ∧ v ∉ V1 ∧ G.Adj v u
    · by_cases hH2D : ∃ u v : W, D.Adj u v ∧ ∃ A : Finset W, u ∉ A ∧ v ∉ A ∧
          (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u → y ≠ v → y ∉ A →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A, ∀ y : W, y ≠ u → y ≠ v → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
      · exact embeds_heart_two hn D hW hD G hV hG hH2D
      let k := (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card
      by_cases hm3 : n - k ≤ 3
      · exact embeds_internal_le_three hn3 D hW hD G hV hG h2S hm3
      have hk_ge2 : 2 ≤ k := card_leaves_ge_two hn D hW hD
      have hm4 : 4 ≤ n - k := by omega
      have hn6 : 6 ≤ n := by omega
      by_cases hfew : k ≤ 4 ∨ 3 * k ≤ n
      · exact hH1 n hn6 D hW hD hH2D hm4 hfew G hV hG h2S
      have hk_gt4 : 4 < k := by omega
      have hn_lt3k : n < 3 * k := by omega
      have hn9 : 9 ≤ n := by omega
      by_cases hnr : ∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 1 ∨
          (Finset.univ.filter (fun u : V => G.Adj v u)).card = n - 2
      · exact hH2 n hn9 D hW hD hH2D hk_gt4 hn_lt3k hm4 G hV hG h2S hnr
      have hnotnr : ∃ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≠ n - 1 ∧
          (Finset.univ.filter (fun u : V => G.Adj v u)).card ≠ n - 2 := by
        push Not at hnr
        exact hnr
      exact hH3 n hn9 D hW hD hH2D hk_gt4 hn_lt3k hm4 G hV hG h2S hnotnr
    · push Not at h2S
      exact twoStrong_reduction hn3 (fun m hm2 hmn => ih m hmn hm2) D hW hD G hV hG h2S

end OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1
