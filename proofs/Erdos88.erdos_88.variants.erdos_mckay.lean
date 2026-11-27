import FormalConjectures.ErdosProblems.«88»

/-!
# Proof of Erdős Problem 88 (Erdős–McKay variant)

Self-contained proof of `Erdos88.erdos_88.variants.erdos_mckay`:
for every `ε > 0`, there exists `δ > 0` such that every `n`-vertex graph `G` with
`ω(G) < ε log n` and `α(G) < ε log n` contains an induced subgraph with exactly `m` edges
for every natural number `m ≤ δ (log n)^2`.

Proof overview:
1. Any `m ≤ h (h - 1) / 2` is the edge count of a threshold graph on `h` vertices specified by
   a Boolean list `bs` of length `h`.
2. Using amortized peeling of low-degree vertices into an independent set `I` and low-non-degree
   vertices into a clique `K` (whose total size stays `< ω(G) + α(G) < 2 ε log n`), every
   threshold graph on `h = ⌊c(ε) log n⌋` vertices embeds as an induced subgraph of `G` once
   `log n ≥ L₀(ε)`.
3. Choosing `δ ≤ 1 / (2 L₀²)` forces `m = 0` for `log n < L₀`, realized by `S = ∅`.
-/

namespace Erdos88McKayProof

open SimpleGraph Finset

/-- Edge count of the threshold graph specified by a list of bits `bs`, where `true` means
adjacent to all later vertices and `false` means non-adjacent to all later vertices. -/
def targetEdges : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then bs.length else 0) + targetEdges bs

private lemma two_mul_le_mul_pred (h : ℕ) (hh : 1 ≤ h) : 2 * (h - 1) ≤ h * (h - 1) := by
  rcases h with _ | _ | k
  · omega
  · simp
  · nlinarith

private lemma exists_bits_targetEdges :
    ∀ h m : ℕ, m ≤ h * (h - 1) / 2 → ∃ bs : List Bool, bs.length = h ∧ targetEdges bs = m
  | 0, m, hm => by
      have hm0 : m = 0 := by simpa using hm
      exact ⟨[], rfl, by simp [targetEdges, hm0]⟩
  | h + 1, m, hm => by
      have htri : (h + 1) * h / 2 = h + h * (h - 1) / 2 := by
        rcases h with _ | k
        · simp
        · have heven : 2 ∣ (k + 1) * k := by
            rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
            · exact ⟨(t + t + 1) * t, by ring⟩
            · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
          have hmul : (k + 2) * (k + 1) = 2 * (k + 1) + (k + 1) * k := by ring
          rw [show k + 1 + 1 = k + 2 from rfl, hmul, Nat.add_sub_cancel,
            Nat.mul_add_div (by norm_num)]
      rw [Nat.add_sub_cancel, htri] at hm
      by_cases hle : h ≤ m
      · obtain ⟨bs, hlen, hsum⟩ := exists_bits_targetEdges h (m - h) (by omega)
        exact ⟨true :: bs, by simp [hlen], by simp [targetEdges, hlen, hsum]; omega⟩
      · have hle_tri : m ≤ h * (h - 1) / 2 := by
          rcases h with _ | k
          · omega
          · have h2 := two_mul_le_mul_pred (k + 1) (by omega)
            omega
        obtain ⟨bs, hlen, hsum⟩ := exists_bits_targetEdges h m hle_tri
        exact ⟨false :: bs, by simp [hlen], by simp [targetEdges, hsum]⟩

/-- A list of vertices `vs` realizes the threshold graph pattern `bs` in `G`. -/
def IsThresholdEmbed {V : Type*} (G : SimpleGraph V) : List V → List Bool → Prop
  | [], [] => True
  | v :: vs, b :: bs => (∀ u ∈ vs, G.Adj v u ↔ b = true) ∧ IsThresholdEmbed G vs bs
  | _, _ => False

section EdgeCount

open scoped Classical

private noncomputable def inducedEdgeFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S)

private lemma induce_edgeSet_ncard_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).edgeSet.ncard = (inducedEdgeFinset G S).card := by
  classical
  have hfin : (G.induce (S : Set V)).edgeSet.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine Finset.card_bij (fun e _ => e.map Subtype.val) ?_ ?_ ?_
  · intro e he
    rw [Set.Finite.mem_toFinset] at he
    rw [inducedEdgeFinset, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset]
      induction e using Sym2.ind with
      | _ a b =>
        simpa [SimpleGraph.mem_edgeSet] using he
    · intro u hu
      rw [Sym2.mem_map] at hu
      rcases hu with ⟨x, _, rfl⟩
      exact x.property
  · intro e₁ _ e₂ _ hmap
    exact Sym2.map.injective Subtype.val_injective hmap
  · intro e he
    rw [inducedEdgeFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    rcases he with ⟨heG, heS⟩
    induction e using Sym2.ind with
    | _ a b =>
      have ha : a ∈ S := heS a (Sym2.mem_mk_left a b)
      have hb : b ∈ S := heS b (Sym2.mem_mk_right a b)
      refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, by simp⟩
      rw [Set.Finite.mem_toFinset]
      exact heG

private lemma inducedEdgeFinset_empty {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (inducedEdgeFinset G ∅).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [inducedEdgeFinset, Finset.mem_filter] at he
  induction e using Sym2.ind with
  | _ a b => exact Finset.notMem_empty a (he.2 a (Sym2.mem_mk_left a b))

private lemma inducedEdgeFinset_insert {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (S : Finset V) (hv : v ∉ S) :
    (inducedEdgeFinset G (insert v S)).card =
      (inducedEdgeFinset G S).card + (S.filter (G.Adj v)).card := by
  classical
  let star : Finset (Sym2 V) := (S.filter (G.Adj v)).image (fun u => s(v, u))
  have hunion : inducedEdgeFinset G (insert v S) = inducedEdgeFinset G S ∪ star := by
    ext e
    simp only [inducedEdgeFinset, star, Finset.mem_union, Finset.mem_filter, Finset.mem_image,
      SimpleGraph.mem_edgeFinset]
    induction e using Sym2.ind with
    | _ a b =>
      constructor
      · rintro ⟨hadj, hsub⟩
        have ha := hsub a (Sym2.mem_mk_left a b)
        have hb := hsub b (Sym2.mem_mk_right a b)
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | haS
        · rcases hb with rfl | hbS
          · exact False.elim (G.ne_of_adj hadj rfl)
          · right
            exact ⟨b, ⟨hbS, hadj⟩, rfl⟩
        · rcases hb with rfl | hbS
          · right
            exact ⟨a, ⟨haS, (G.adj_comm _ _).mp hadj⟩, Sym2.eq_swap⟩
          · left
            refine ⟨hadj, fun u hu => ?_⟩
            rw [Sym2.mem_iff] at hu
            rcases hu with rfl | rfl <;> assumption
      · rintro (⟨hadj, hsub⟩ | ⟨u, ⟨huS, hadj⟩, heq⟩)
        · exact ⟨hadj, fun u hu => Finset.mem_insert_of_mem (hsub u hu)⟩
        · rw [← heq]
          refine ⟨hadj, fun x hx => ?_⟩
          rw [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_insert_self _ S
          · exact Finset.mem_insert_of_mem huS
  have hdisj : Disjoint (inducedEdgeFinset G S) star := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [inducedEdgeFinset, Finset.mem_filter] at he1
    rw [Finset.mem_image] at he2
    rcases he2 with ⟨u, _, rfl⟩
    exact hv (he1.2 v (Sym2.mem_mk_left v u))
  have hstar_card : star.card = (S.filter (G.Adj v)).card := by
    refine Finset.card_image_of_injOn ?_
    intro u₁ hu₁ u₂ hu₂ heq
    have h1 : u₁ ≠ v := fun h => hv (h ▸ (Finset.mem_filter.mp hu₁).1)
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, rfl⟩ | ⟨_, hu1v⟩
    · rfl
    · exact False.elim (h1 hu1v)
  rw [hunion, Finset.card_union_of_disjoint hdisj, hstar_card]

private lemma card_induce_edges_of_threshold {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∀ (vs : List V) (bs : List Bool),
      vs.length = bs.length → vs.Nodup → IsThresholdEmbed G vs bs →
      (G.induce (vs.toFinset : Set V)).edgeSet.ncard = targetEdges bs
  | [], [], _, _, _ => by
      classical
      rw [induce_edgeSet_ncard_eq]
      simpa [targetEdges] using inducedEdgeFinset_empty G
  | v :: vs, b :: bs, hlen, hnd, ⟨hadj, hrest⟩ => by
      classical
      rw [induce_edgeSet_ncard_eq]
      have hnd' : v ∉ vs ∧ vs.Nodup := List.nodup_cons.mp hnd
      have hv : v ∉ vs.toFinset := by simpa using hnd'.1
      have hlen' : vs.length = bs.length := by simpa using hlen
      rw [List.toFinset_cons, inducedEdgeFinset_insert G v vs.toFinset hv]
      have ih := card_induce_edges_of_threshold G vs bs hlen' hnd'.2 hrest
      rw [induce_edgeSet_ncard_eq] at ih
      rw [ih, targetEdges]
      have hdeg : (vs.toFinset.filter (G.Adj v)).card = if b then bs.length else 0 := by
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_eq_zero,
            Finset.eq_empty_iff_forall_notMem, Finset.mem_filter, List.mem_toFinset]
          intro u ⟨hu, hvu⟩
          exact Bool.false_ne_true ((hadj u hu).mp hvu)
        · have hfilt : vs.toFinset.filter (G.Adj v) = vs.toFinset := by
            ext u
            simp only [Finset.mem_filter, List.mem_toFinset, and_iff_left_iff_imp]
            intro hu
            exact (hadj u hu).mpr rfl
          rw [hfilt, List.toFinset_card_of_nodup hnd'.2, hlen']
          simp
      rw [hdeg, add_comm]
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen

end EdgeCount

section AmortizedPeeling

open scoped Classical

private structure ValidPool {V : Type*} (G : SimpleGraph V) (K I U : Finset V) : Prop where
  clique : G.IsClique (K : Set V)
  indep : G.IsIndepSet (I : Set V)
  disjK : Disjoint K U
  disjI : Disjoint I U
  adjK : ∀ x ∈ K, ∀ u ∈ U, G.Adj x u
  nadjI : ∀ x ∈ I, ∀ u ∈ U, ¬ G.Adj x u

private lemma validPool_subset {V : Type*} {G : SimpleGraph V} {K I U U' : Finset V}
    (hp : ValidPool G K I U) (hsub : U' ⊆ U) : ValidPool G K I U' where
  clique := hp.clique
  indep := hp.indep
  disjK := hp.disjK.mono_right hsub
  disjI := hp.disjI.mono_right hsub
  adjK x hx u hu := hp.adjK x hx u (hsub hu)
  nadjI x hx u hu := hp.nadjI x hx u (hsub hu)

private lemma validPool_peel_indep {V : Type*} {G : SimpleGraph V} {K I U : Finset V}
    (hp : ValidPool G K I U) {w : V} (hw : w ∈ U) :
    ValidPool G K (insert w I) ((U.erase w).filter (fun u => ¬ G.Adj w u)) := by
  have hsub : (U.erase w).filter (fun u => ¬ G.Adj w u) ⊆ U :=
    (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  refine ⟨hp.clique, ?_, hp.disjK.mono_right hsub, ?_,
    fun x hx u hu => hp.adjK x hx u (hsub hu), ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hxI
    · rcases hy with rfl | hyI
      · exact (hxy rfl).elim
      · exact fun h => hp.nadjI y hyI x hw ((G.adj_comm _ _).mp h)
    · rcases hy with rfl | hyI
      · exact hp.nadjI x hxI y hw
      · exact hp.indep hxI hyI hxy
  · rw [Finset.disjoint_insert_left]
    refine ⟨?_, hp.disjI.mono_right hsub⟩
    simp
  · intro x hx u hu
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxI
    · exact (Finset.mem_filter.mp hu).2
    · exact hp.nadjI x hxI u (hsub hu)

private lemma validPool_peel_clique {V : Type*} {G : SimpleGraph V} {K I U : Finset V}
    (hp : ValidPool G K I U) {w : V} (hw : w ∈ U) :
    ValidPool G (insert w K) I (U.filter (G.Adj w)) := by
  have hsub : U.filter (G.Adj w) ⊆ U := Finset.filter_subset _ _
  refine ⟨?_, hp.indep, ?_, hp.disjI.mono_right hsub, ?_,
    fun x hx u hu => hp.nadjI x hx u (hsub hu)⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hxK
    · rcases hy with rfl | hyK
      · exact (hxy rfl).elim
      · exact (G.adj_comm _ _).mp (hp.adjK y hyK x hw)
    · rcases hy with rfl | hyK
      · exact hp.adjK x hxK y hw
      · exact hp.clique hxK hyK hxy
  · rw [Finset.disjoint_insert_left]
    refine ⟨?_, hp.disjK.mono_right hsub⟩
    simp only [Finset.mem_filter, not_and]
    exact fun _ h => G.ne_of_adj h rfl
  · intro x hx u hu
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxK
    · exact (Finset.mem_filter.mp hu).2
    · exact hp.adjK x hxK u (hsub hu)

private lemma card_filter_adj_add_nadj {V : Type*} (G : SimpleGraph V) (U : Finset V)
    {w : V} (hw : w ∈ U) :
    (U.filter (G.Adj w)).card + ((U.erase w).filter (fun u => ¬ G.Adj w u)).card + 1 = U.card := by
  have heq : U.filter (G.Adj w) = (U.erase w).filter (G.Adj w) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, hadj⟩
      exact ⟨⟨fun h => G.ne_of_adj (h ▸ hadj) rfl, hu⟩, hadj⟩
    · rintro ⟨⟨_, hu⟩, hadj⟩
      exact ⟨hu, hadj⟩
  have hunion : (U.erase w).filter (G.Adj w) ∪ (U.erase w).filter (fun u => ¬ G.Adj w u) =
      U.erase w := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint ((U.erase w).filter (G.Adj w))
      ((U.erase w).filter (fun u => ¬ G.Adj w u)) := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hsum : ((U.erase w).filter (G.Adj w)).card +
      ((U.erase w).filter (fun u => ¬ G.Adj w u)).card = (U.erase w).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  rw [heq, hsum, Finset.card_erase_of_mem hw]
  have hpos : 1 ≤ U.card := Finset.one_le_card.mpr ⟨w, hw⟩
  omega

private lemma embed_threshold_aux {V : Type*} [Fintype V]
    (G : SimpleGraph V) (η : ℝ) (hη0 : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ (N : ℕ) (bs : List Bool) (K I U : Finset V),
      ValidPool G K I U →
      bs.length + (G.cliqueNum + G.indepNum - (K.card + I.card)) ≤ N →
      1 / η ≤ (U.card : ℝ) * (1 - 2 * η) ^ (G.cliqueNum + G.indepNum - (K.card + I.card)) *
        η ^ bs.length →
      ∃ vs : List V, vs.length = bs.length ∧ vs.Nodup ∧ (∀ v ∈ vs, v ∈ U) ∧
        IsThresholdEmbed G vs bs
  | 0, [], _, _, _, _, _, _ => ⟨[], rfl, List.nodup_nil, by simp, trivial⟩
  | 0, _ :: _, _, _, _, _, hN, _ => by simp at hN
  | N + 1, [], _, _, _, _, _, _ => ⟨[], rfl, List.nodup_nil, by simp, trivial⟩
  | N + 1, b :: bs', K, I, U, hpool, hN, hsize => by
      have hKle : K.card ≤ G.cliqueNum := hpool.clique.card_le_cliqueNum
      have hIle : I.card ≤ G.indepNum := hpool.indep.card_le_indepNum
      have h12η_pos : 0 < 1 - 2 * η := by linarith
      have h12η_le1 : 1 - 2 * η ≤ 1 := by linarith
      have hη_le1 : η ≤ 1 := by linarith
      set rem := G.cliqueNum + G.indepNum - (K.card + I.card)
      have hpow_le1 : (1 - 2 * η) ^ rem * η ^ (b :: bs').length ≤ 1 := by
        have h1 : (1 - 2 * η) ^ rem ≤ 1 := pow_le_one₀ h12η_pos.le h12η_le1
        have h2 : η ^ (b :: bs').length ≤ 1 := pow_le_one₀ hη0.le hη_le1
        nlinarith [pow_nonneg h12η_pos.le rem, pow_nonneg hη0.le (b :: bs').length]
      have hUge : 1 / η ≤ (U.card : ℝ) := by
        have hU0 : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
        have : (U.card : ℝ) * (1 - 2 * η) ^ rem * η ^ (b :: bs').length ≤ (U.card : ℝ) * 1 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hpow_le1 hU0
        linarith
      have h1le_ηU : 1 ≤ η * (U.card : ℝ) := by
        have := mul_le_mul_of_nonneg_left hUge hη0.le
        rwa [mul_one_div_cancel hη0.ne'] at this
      have hUne : U.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        subst h
        simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at h1le_ηU
        linarith
      cases b
      · -- b = false: either peel a low-non-degree vertex into K, or pick any v ∈ U
        by_cases hpeel : ∃ w ∈ U,
            (((U.erase w).filter (fun u => ¬ G.Adj w u)).card : ℝ) < η * (U.card : ℝ)
        · rcases hpeel with ⟨w, hwU, hwlt⟩
          let K₁ := insert w K
          let U₁ := U.filter (G.Adj w)
          have hpool₁ : ValidPool G K₁ I U₁ := validPool_peel_clique hpool hwU
          have hwK : w ∉ K := Finset.disjoint_right.mp hpool.disjK hwU
          have hK₁card : K₁.card = K.card + 1 := Finset.card_insert_of_notMem hwK
          have hK₁le : K₁.card ≤ G.cliqueNum := hpool₁.clique.card_le_cliqueNum
          have hrem_pos : 1 ≤ rem := by omega
          have hrem₁ : G.cliqueNum + G.indepNum - (K₁.card + I.card) = rem - 1 := by omega
          have hU₁card_nat := card_filter_adj_add_nadj G U hwU
          have hU₁ge : (1 - 2 * η) * (U.card : ℝ) ≤ (U₁.card : ℝ) := by
            have hcast : (U₁.card : ℝ) +
                (((U.erase w).filter (fun u => ¬ G.Adj w u)).card : ℝ) + 1 = (U.card : ℝ) := by
              exact_mod_cast hU₁card_nat
            linarith
          have hsize₁ : 1 / η ≤ (U₁.card : ℝ) *
              (1 - 2 * η) ^ (G.cliqueNum + G.indepNum - (K₁.card + I.card)) *
              η ^ (false :: bs').length := by
            rw [hrem₁]
            have hstep : (U.card : ℝ) * (1 - 2 * η) ^ rem ≤
                (U₁.card : ℝ) * (1 - 2 * η) ^ (rem - 1) := by
              have hpow : (1 - 2 * η) ^ rem = (1 - 2 * η) * (1 - 2 * η) ^ (rem - 1) := by
                conv_lhs => rw [← Nat.sub_add_cancel hrem_pos, pow_succ']
              rw [hpow, ← mul_assoc, mul_comm (U.card : ℝ) (1 - 2 * η)]
              exact mul_le_mul_of_nonneg_right hU₁ge (pow_nonneg h12η_pos.le _)
            exact hsize.trans (mul_le_mul_of_nonneg_right hstep (pow_nonneg hη0.le _))
          obtain ⟨vs, hlen, hnd, hmem, hemb⟩ :=
            embed_threshold_aux G η hη0 hη8 N (false :: bs') K₁ I U₁ hpool₁ (by omega) hsize₁
          exact ⟨vs, hlen, hnd, fun v hv => (Finset.filter_subset _ _) (hmem v hv), hemb⟩
        · push Not at hpeel
          rcases hUne with ⟨v, hvU⟩
          let U₁ := (U.erase v).filter (fun u => ¬ G.Adj v u)
          have hsub : U₁ ⊆ U := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
          have hpool₁ : ValidPool G K I U₁ := validPool_subset hpool hsub
          have hU₁ge : η * (U.card : ℝ) ≤ (U₁.card : ℝ) := hpeel v hvU
          have hsize₁ : 1 / η ≤ (U₁.card : ℝ) *
              (1 - 2 * η) ^ (G.cliqueNum + G.indepNum - (K.card + I.card)) * η ^ bs'.length := by
            have hstep : (U.card : ℝ) * (1 - 2 * η) ^ rem * η ^ (false :: bs').length ≤
                (U₁.card : ℝ) * (1 - 2 * η) ^ rem * η ^ bs'.length := by
              simp only [List.length_cons, pow_succ']
              have hmul := mul_le_mul_of_nonneg_right hU₁ge
                (mul_nonneg (pow_nonneg h12η_pos.le rem) (pow_nonneg hη0.le bs'.length))
              calc
                (U.card : ℝ) * (1 - 2 * η) ^ rem * (η * η ^ bs'.length)
                    = (η * (U.card : ℝ)) * ((1 - 2 * η) ^ rem * η ^ bs'.length) := by ring
                _ ≤ (U₁.card : ℝ) * ((1 - 2 * η) ^ rem * η ^ bs'.length) := hmul
                _ = (U₁.card : ℝ) * (1 - 2 * η) ^ rem * η ^ bs'.length := by ring
            exact hsize.trans hstep
          obtain ⟨vs', hlen', hnd', hmem', hemb'⟩ :=
            embed_threshold_aux G η hη0 hη8 N bs' K I U₁ hpool₁ (by simp at hN; omega) hsize₁
          have hv_not : v ∉ vs' := by
            intro h
            have := hmem' v h
            simp [U₁] at this
          refine ⟨v :: vs', by simp [hlen'], List.nodup_cons.mpr ⟨hv_not, hnd'⟩, ?_, ?_⟩
          · intro u hu
            rw [List.mem_cons] at hu
            rcases hu with rfl | hu'
            · exact hvU
            · exact hsub (hmem' u hu')
          · refine ⟨fun u hu => ?_, hemb'⟩
            have hu1 := Finset.mem_filter.mp (hmem' u hu)
            simp [hu1.2]
      · -- b = true: either peel a low-degree vertex into I, or pick any v ∈ U
        by_cases hpeel : ∃ w ∈ U, ((U.filter (G.Adj w)).card : ℝ) < η * (U.card : ℝ)
        · rcases hpeel with ⟨w, hwU, hwlt⟩
          let I₁ := insert w I
          let U₁ := (U.erase w).filter (fun u => ¬ G.Adj w u)
          have hpool₁ : ValidPool G K I₁ U₁ := validPool_peel_indep hpool hwU
          have hwI : w ∉ I := Finset.disjoint_right.mp hpool.disjI hwU
          have hI₁card : I₁.card = I.card + 1 := Finset.card_insert_of_notMem hwI
          have hI₁le : I₁.card ≤ G.indepNum := hpool₁.indep.card_le_indepNum
          have hrem_pos : 1 ≤ rem := by omega
          have hrem₁ : G.cliqueNum + G.indepNum - (K.card + I₁.card) = rem - 1 := by omega
          have hU₁card_nat := card_filter_adj_add_nadj G U hwU
          have hU₁ge : (1 - 2 * η) * (U.card : ℝ) ≤ (U₁.card : ℝ) := by
            have hcast : ((U.filter (G.Adj w)).card : ℝ) + (U₁.card : ℝ) + 1 = (U.card : ℝ) := by
              exact_mod_cast hU₁card_nat
            linarith
          have hsize₁ : 1 / η ≤ (U₁.card : ℝ) *
              (1 - 2 * η) ^ (G.cliqueNum + G.indepNum - (K.card + I₁.card)) *
              η ^ (true :: bs').length := by
            rw [hrem₁]
            have hstep : (U.card : ℝ) * (1 - 2 * η) ^ rem ≤
                (U₁.card : ℝ) * (1 - 2 * η) ^ (rem - 1) := by
              have hpow : (1 - 2 * η) ^ rem = (1 - 2 * η) * (1 - 2 * η) ^ (rem - 1) := by
                conv_lhs => rw [← Nat.sub_add_cancel hrem_pos, pow_succ']
              rw [hpow, ← mul_assoc, mul_comm (U.card : ℝ) (1 - 2 * η)]
              exact mul_le_mul_of_nonneg_right hU₁ge (pow_nonneg h12η_pos.le _)
            exact hsize.trans (mul_le_mul_of_nonneg_right hstep (pow_nonneg hη0.le _))
          obtain ⟨vs, hlen, hnd, hmem, hemb⟩ :=
            embed_threshold_aux G η hη0 hη8 N (true :: bs') K I₁ U₁ hpool₁ (by omega) hsize₁
          have hsub : U₁ ⊆ U := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
          exact ⟨vs, hlen, hnd, fun v hv => hsub (hmem v hv), hemb⟩
        · push Not at hpeel
          rcases hUne with ⟨v, hvU⟩
          let U₁ := U.filter (G.Adj v)
          have hsub : U₁ ⊆ U := Finset.filter_subset _ _
          have hpool₁ : ValidPool G K I U₁ := validPool_subset hpool hsub
          have hU₁ge : η * (U.card : ℝ) ≤ (U₁.card : ℝ) := hpeel v hvU
          have hsize₁ : 1 / η ≤ (U₁.card : ℝ) *
              (1 - 2 * η) ^ (G.cliqueNum + G.indepNum - (K.card + I.card)) * η ^ bs'.length := by
            have hstep : (U.card : ℝ) * (1 - 2 * η) ^ rem * η ^ (true :: bs').length ≤
                (U₁.card : ℝ) * (1 - 2 * η) ^ rem * η ^ bs'.length := by
              simp only [List.length_cons, pow_succ']
              have hmul := mul_le_mul_of_nonneg_right hU₁ge
                (mul_nonneg (pow_nonneg h12η_pos.le rem) (pow_nonneg hη0.le bs'.length))
              calc
                (U.card : ℝ) * (1 - 2 * η) ^ rem * (η * η ^ bs'.length)
                    = (η * (U.card : ℝ)) * ((1 - 2 * η) ^ rem * η ^ bs'.length) := by ring
                _ ≤ (U₁.card : ℝ) * ((1 - 2 * η) ^ rem * η ^ bs'.length) := hmul
                _ = (U₁.card : ℝ) * (1 - 2 * η) ^ rem * η ^ bs'.length := by ring
            exact hsize.trans hstep
          obtain ⟨vs', hlen', hnd', hmem', hemb'⟩ :=
            embed_threshold_aux G η hη0 hη8 N bs' K I U₁ hpool₁ (by simp at hN; omega) hsize₁
          have hv_not : v ∉ vs' := by
            intro h
            have := Finset.mem_filter.mp (hmem' v h)
            exact G.ne_of_adj this.2 rfl
          refine ⟨v :: vs', by simp [hlen'], List.nodup_cons.mpr ⟨hv_not, hnd'⟩, ?_, ?_⟩
          · intro u hu
            rw [List.mem_cons] at hu
            rcases hu with rfl | hu'
            · exact hvU
            · exact hsub (hmem' u hu')
          · refine ⟨fun u hu => ?_, hemb'⟩
            have hu1 := Finset.mem_filter.mp (hmem' u hu)
            simp [hu1.2]

end AmortizedPeeling

private lemma exp_neg_four_mul_le {η : ℝ} (hη0 : 0 ≤ η) (hη8 : η ≤ 1 / 8) :
    Real.exp (-4 * η) ≤ 1 - 2 * η := by
  have h1 : 1 + 4 * η ≤ Real.exp (4 * η) := by linarith [Real.add_one_le_exp (4 * η)]
  have h2 : (1 : ℝ) ≤ (1 - 2 * η) * Real.exp (4 * η) := by
    have hprod : (1 - 2 * η) * (1 + 4 * η) ≤ (1 - 2 * η) * Real.exp (4 * η) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  have hpos : 0 < Real.exp (4 * η) := Real.exp_pos _
  have hrew : Real.exp (-4 * η) = (Real.exp (4 * η))⁻¹ := by
    rw [show -4 * η = -(4 * η) by ring, Real.exp_neg]
  rw [hrew, inv_le_iff_one_le_mul₀' hpos]
  linarith

theorem erdos_88_erdos_mckay :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < ε * Real.log n → (G.indepNum : ℝ) < ε * Real.log n →
        ∀ m : ℕ, (m : ℝ) ≤ δ * Real.log n ^ 2 →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  intro ε hε
  let η : ℝ := min (1 / 8) (1 / (16 * ε))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hηε : η ≤ 1 / (16 * ε) := min_le_right _ _
  have h8ηε : 8 * η * ε ≤ 1 / 2 := by
    have h1 : η * (16 * ε) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hηε (by positivity : (0 : ℝ) ≤ 16 * ε)
      rwa [one_div_mul_cancel (by positivity)] at this
    linarith
  have hinv_ge8 : (8 : ℝ) ≤ 1 / η := by
    rw [le_div_iff₀ hη0]; linarith
  have hlog_inv_pos : 0 < Real.log (1 / η) := Real.log_pos (by linarith)
  let c : ℝ := 1 / (4 * Real.log (1 / η))
  have hc0 : 0 < c := by positivity
  let L₀ : ℝ := max 1 (16 * Real.log (1 / η))
  have hL₀1 : 1 ≤ L₀ := le_max_left _ _
  have hL₀0 : 0 < L₀ := by linarith
  let δ : ℝ := min (c ^ 2 / 16) (1 / (2 * L₀ ^ 2))
  refine ⟨δ, lt_min (by positivity) (by positivity), ?_⟩
  intro n G hcl hind m hm
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have h0 : (0 : ℝ) < ε * Real.log (n : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) hcl
    exact pos_of_mul_pos_right h0 hε.le
  have hn1 : 1 ≤ n := by
    rcases n with _ | k
    · simp at hlog_pos
    · omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  by_cases hbig : L₀ ≤ Real.log (n : ℝ)
  · -- Large regime: embed a threshold graph of order h = ⌊c * log n⌋
    have hlog_16 : 16 * Real.log (1 / η) ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hbig
    have hc_log_ge4 : 4 ≤ c * Real.log (n : ℝ) := by
      rw [show c * Real.log (n : ℝ) = Real.log (n : ℝ) / (4 * Real.log (1 / η)) by
        simp [c, div_eq_mul_inv, mul_comm]]
      rw [le_div_iff₀ (by positivity)]
      linarith
    let h : ℕ := Nat.floor (c * Real.log (n : ℝ))
    have hh_ge4 : 4 ≤ h := Nat.le_floor hc_log_ge4
    have hh_le : (h : ℝ) ≤ c * Real.log (n : ℝ) := Nat.floor_le (by positivity)
    have hh_gt : c * Real.log (n : ℝ) - 1 < (h : ℝ) := Nat.sub_one_lt_floor _
    have hm_le_tri : m ≤ h * (h - 1) / 2 := by
      have hreal : (m : ℝ) ≤ ((h * (h - 1) / 2 : ℕ) : ℝ) := by
        have h2dvd : 2 ∣ h * (h - 1) := by
          rcases Nat.even_or_odd h with ⟨t, ht⟩ | ⟨t, ht⟩
          · exact ⟨t * (h - 1), by rw [ht]; ring⟩
          · exact ⟨h * t, by
              have hsub : h - 1 = 2 * t := by omega
              rw [hsub]; ring⟩
        have hcast_tri : ((h * (h - 1) / 2 : ℕ) : ℝ) = (h : ℝ) * ((h : ℝ) - 1) / 2 := by
          rw [Nat.cast_div h2dvd (by norm_num), Nat.cast_mul, Nat.cast_sub (by omega),
            Nat.cast_one, Nat.cast_ofNat]
        rw [hcast_tri]
        have hh_real : (3 / 4 : ℝ) * (c * Real.log (n : ℝ)) ≤ (h : ℝ) := by linarith
        have hh_pred : (1 / 2 : ℝ) * (h : ℝ) ≤ (h : ℝ) - 1 := by
          have : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
          linarith
        have hδ_le : δ ≤ c ^ 2 / 16 := min_le_left _ _
        calc
          (m : ℝ) ≤ δ * Real.log (n : ℝ) ^ 2 := hm
          _ ≤ (c ^ 2 / 16) * Real.log (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hδ_le (sq_nonneg _)
          _ ≤ (h : ℝ) * ((h : ℝ) - 1) / 2 := by nlinarith
      exact_mod_cast hreal
    obtain ⟨bs, hbs_len, hbs_sum⟩ := exists_bits_targetEdges h m hm_le_tri
    -- Verify the size invariant for K = ∅, I = ∅, U = univ
    have hpool0 : ValidPool G (∅ : Finset (Fin n)) (∅ : Finset (Fin n)) Finset.univ :=
      ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
    have hsize0 : 1 / η ≤
        ((Finset.univ : Finset (Fin n)).card : ℝ) *
        (1 - 2 * η) ^ (G.cliqueNum + G.indepNum - ((∅ : Finset (Fin n)).card + (∅ : Finset (Fin n)).card)) *
        η ^ bs.length := by
      simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty, add_zero, Nat.sub_zero,
        hbs_len]
      set B : ℕ := G.cliqueNum + G.indepNum
      have hB_lt : (B : ℝ) < 2 * ε * Real.log (n : ℝ) := by
        simp only [B, Nat.cast_add]; linarith
      have hterm1 : Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) ≤ (1 - 2 * η) ^ B := by
        have hbase := exp_neg_four_mul_le hη0.le hη8
        calc
          Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ))
              ≤ Real.exp (-(8 * η * ε) * Real.log (n : ℝ)) :=
            Real.exp_le_exp.mpr (by nlinarith)
          _ ≤ Real.exp (-4 * η * (B : ℝ)) :=
            Real.exp_le_exp.mpr (by nlinarith)
          _ = Real.exp (-4 * η) ^ B := by
            rw [← Real.exp_nat_mul]; congr 1; ring
          _ ≤ (1 - 2 * η) ^ B := pow_le_pow_left₀ (Real.exp_pos _).le hbase B
      have hterm2 : Real.exp (-(1 / 4 : ℝ) * Real.log (n : ℝ)) ≤ η ^ h := by
        have hη_eq : η = Real.exp (-Real.log (1 / η)) := by
          rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
        have hh_bound : (h : ℝ) * Real.log (1 / η) ≤ (1 / 4 : ℝ) * Real.log (n : ℝ) := by
          have := mul_le_mul_of_nonneg_right hh_le hlog_inv_pos.le
          have hsimp : c * Real.log (n : ℝ) * Real.log (1 / η) =
              (1 / 4 : ℝ) * Real.log (n : ℝ) := by
            simp only [c]; field_simp [hlog_inv_pos.ne']
          linarith
        calc
          Real.exp (-(1 / 4 : ℝ) * Real.log (n : ℝ))
              ≤ Real.exp (-((h : ℝ) * Real.log (1 / η))) :=
            Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp (-Real.log (1 / η)) ^ h := by
            rw [← Real.exp_nat_mul]; congr 1; ring
          _ = η ^ h := by rw [← hη_eq]
      calc
        1 / η = Real.exp (Real.log (1 / η)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((1 / 4 : ℝ) * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) *
            Real.exp (-(1 / 4 : ℝ) * Real.log (n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ = (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) *
            Real.exp (-(1 / 4 : ℝ) * Real.log (n : ℝ)) := by
          rw [Real.exp_log hn_pos]
        _ ≤ (n : ℝ) * (1 - 2 * η) ^ B * η ^ h := by
          have h12 : (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) ≤
              (n : ℝ) * (1 - 2 * η) ^ B :=
            mul_le_mul_of_nonneg_left hterm1 hn_pos.le
          have hpos_mid : 0 ≤ (n : ℝ) * (1 - 2 * η) ^ B :=
            mul_nonneg hn_pos.le (pow_nonneg (by linarith) B)
          exact (mul_le_mul_of_nonneg_right h12 (Real.exp_pos _).le).trans
            (mul_le_mul_of_nonneg_left hterm2 hpos_mid)
    obtain ⟨vs, hvs_len, hvs_nd, _, hvs_emb⟩ :=
      embed_threshold_aux G η hη0 hη8 (bs.length + (G.cliqueNum + G.indepNum))
        bs ∅ ∅ Finset.univ hpool0 (by simp) hsize0
    refine ⟨vs.toFinset, ?_⟩
    rw [card_induce_edges_of_threshold G vs bs hvs_len hvs_nd hvs_emb, hbs_sum]
  · -- Small regime: log n < L₀ forces m = 0, witnessed by S = ∅
    push Not at hbig
    have hδ_le : δ ≤ 1 / (2 * L₀ ^ 2) := min_le_right _ _
    have hm_lt1 : (m : ℝ) < 1 := by
      have hsq : Real.log (n : ℝ) ^ 2 < L₀ ^ 2 := by nlinarith
      calc
        (m : ℝ) ≤ δ * Real.log (n : ℝ) ^ 2 := hm
        _ ≤ (1 / (2 * L₀ ^ 2)) * Real.log (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hδ_le (sq_nonneg _)
        _ < (1 / (2 * L₀ ^ 2)) * L₀ ^ 2 :=
          mul_lt_mul_of_pos_left hsq (by positivity)
        _ = 1 / 2 := by field_simp [hL₀0.ne']
        _ < 1 := by norm_num
    have hm0 : m = 0 := by
      have : m < 1 := by exact_mod_cast hm_lt1
      omega
    refine ⟨∅, ?_⟩
    rw [hm0, induce_edgeSet_ncard_eq, inducedEdgeFinset_empty]

end Erdos88McKayProof

theorem OMA.solution : type_of% @Erdos88.erdos_88.variants.erdos_mckay :=
  Erdos88McKayProof.erdos_88_erdos_mckay
