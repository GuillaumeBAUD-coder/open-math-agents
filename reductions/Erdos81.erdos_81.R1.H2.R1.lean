import OMAReductions.R_Erdos81_erdos_81_R1
import Mathlib

/-!
# Reduction of `Erdos81.erdos_81.R1.H2` (Haxell--Rödl / Yuster Bounded-Clique Rounding)

We reduce `OMA.R_Erdos81_erdos_81_R1.H2` (dual-form fractional-to-integral bounded-clique
edge-partition rounding) to two standard standalone regularity-method lemmas:
- `H1`: Bipartite regular edge-splitting (Chernoff / Hoeffding bound for partitioning an
  `ε`-uniform bipartite graph into `r` edge-disjoint `ε₁`-uniform subgraphs of prescribed
  densities `α_s ≥ δ` with `∑ α_s ≤ d`).
- `H2`: Almost-full `K_q`-packing in uniform `ε₁`-regular `q`-partite graphs (Graph Counting
  Lemma + Rödl Nibble / Pippenger--Spencer).

Inside `main`, we prove unconditionally in Lean 4:
1. LP Duality via geometric Hahn--Banach (`geometric_hahn_banach_closed_point`): converts the
   dual weighting hypothesis into a primal fractional clique packing `w` on cliques of size
   `3..L` with `∑_{Q ∋ e} w Q ≤ 1` and `|E(G)| - ∑ (choose |Q| 2 - 1) w Q ≤ M`.
2. Basic Feasible Solution support bound (rank--nullity + compactness): replaces any feasible
   cluster-tuple weighting `α` by an optimal maximizer `α*` with `|supp(α*)| ≤ |E_reg| ≤ k^2/2`,
   making the truncation error for `α* T < δ` independent of `k`.
3. Szemerédi Regularity (`szemeredi_regularity`), equal-size cluster trimming preserving
   uniformity, fractional aggregation onto regular cluster tuples, application of `H1` and `H2`,
   and edge-disjoint clique partition assembly.
-/

-- Credit: @preternatural-tocsin

namespace OMA.R_Erdos81_erdos_81_R1_H2_R1

open SimpleGraph Finset

/-- Bipartite regular edge-splitting (Chernoff / Hoeffding): any `ε`-uniform bipartite graph on
disjoint vertex classes `A, B` of size `m ≥ m₀` can be edge-colored so that for prescribed
densities `α : Fin r → ℝ` with `∀ s, δ ≤ α s` and `∑ s, α s ≤ d_G(A, B)`, each color class
subgraph is `ε₁`-uniform on `(A, B)` with edge density within `ε₁` of `α s`. -/
def H1 : Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ → ∀ δ : ℝ, 0 < δ →
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (n m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A B : Finset (Fin n)), Disjoint A B → A.card = m → B.card = m →
        G.IsUniform ε A B →
        ∀ (r : ℕ) (α : Fin r → ℝ), (∀ s, δ ≤ α s) →
          ∑ s, α s ≤ (G.edgeDensity A B : ℝ) →
          ∃ col : Sym2 (Fin n) → Option (Fin r),
            ∀ s : Fin r, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
              (∀ u v, H.Adj u v ↔ G.Adj u v ∧ col s(u, v) = some s) →
              H.IsUniform ε₁ A B ∧ |(H.edgeDensity A B : ℝ) - α s| ≤ ε₁

/-- Almost-full `K_q`-packing in uniform `ε₁`-regular `q`-partite graphs (Graph Counting Lemma +
Rödl Nibble / Pippenger--Spencer): if `V : Fin q → Finset (Fin n)` are pairwise disjoint parts
of size `m ≥ m₀` (`q ≥ 3`) and every pair `(V i, V j)` (`i ≠ j`) is `ε₁`-uniform with density
within `ε₁` of `p ∈ [δ, 1]`, then `G` contains at least `(p - η) * m^2` pairwise edge-disjoint
transversal `q`-cliques. -/
def H2 : Prop :=
  ∀ (q : ℕ), 3 ≤ q → ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ m₀ : ℕ,
      ∀ (n m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (V : Fin q → Finset (Fin n)),
        (∀ i j, i ≠ j → Disjoint (V i) (V j)) →
        (∀ i, (V i).card = m) →
        ∀ p : ℝ, δ ≤ p → p ≤ 1 →
        (∀ i j, i ≠ j → G.IsUniform ε₁ (V i) (V j) ∧
          |(G.edgeDensity (V i) (V j) : ℝ) - p| ≤ ε₁) →
        ∃ 𝒬 : Finset (Finset (Fin n)),
          (∀ Q ∈ 𝒬, Q.card = q ∧ G.IsClique (Q : Set (Fin n)) ∧
            ∀ i : Fin q, (Q ∩ V i).card = 1) ∧
          (∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
          (p - η) * (m : ℝ) ^ 2 ≤ (𝒬.card : ℝ)

/- ### Section 1: Graph and Clique Edge Counting Helpers -/

lemma clique_edges_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Finset (Fin n)) (hQ : G.IsClique (Q : Set (Fin n))) :
    (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)).card = Q.card.choose 2 := by
  have hcard : (Q.powersetCard 2).card = Q.card.choose 2 := card_powersetCard 2 Q
  rw [← hcard]
  refine Finset.card_bij (fun e _ ↦ e.toFinset) ?_ ?_ ?_
  · intro e he
    rw [mem_filter] at he
    have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp he.1
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Sym2.mem_toFinset] at hx
        exact he.2 x hx
      · rw [Sym2.toFinset_mk_eq, card_pair (G.ne_of_adj hadj)]
  · intro e₁ he₁ e₂ he₂ heq
    have hnd₁ : ¬e₁.IsDiag := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he₁).1)
    have hnd₂ : ¬e₂.IsDiag := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he₂).1)
    induction e₁ using Sym2.ind with
    | h a b =>
      induction e₂ using Sym2.ind with
      | h c d =>
        have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using hnd₁
        have hcd : c ≠ d := by simpa [Sym2.mk_isDiag_iff] using hnd₂
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at heq
        have ha : a ∈ ({c, d} : Finset (Fin n)) := heq ▸ mem_insert_self a {b}
        have hb : b ∈ ({c, d} : Finset (Fin n)) := heq ▸ mem_insert_of_mem (mem_singleton_self b)
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hab
  · intro s hs
    rw [mem_powersetCard] at hs
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
    have haQ : a ∈ Q := hs.1 (mem_insert_self a {b})
    have hbQ : b ∈ Q := hs.1 (mem_insert_of_mem (mem_singleton_self b))
    refine ⟨s(a, b), mem_filter.mpr ⟨mem_edgeFinset.mpr (hQ haQ hbQ hab), ?_⟩, ?_⟩
    · intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
    · rw [Sym2.toFinset_mk_eq]

lemma edgeDensity_congr_on {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] {A B : Finset (Fin n)}
    (h : ∀ u ∈ A, ∀ v ∈ B, G₁.Adj u v ↔ G₂.Adj u v) :
    G₁.edgeDensity A B = G₂.edgeDensity A B := by
  have hint : G₁.interedges A B = G₂.interedges A B := by
    ext ⟨u, v⟩
    simp only [SimpleGraph.mem_interedges_iff]
    exact ⟨fun ⟨hu, hv, hadj⟩ ↦ ⟨hu, hv, (h u hu v hv).mp hadj⟩,
      fun ⟨hu, hv, hadj⟩ ↦ ⟨hu, hv, (h u hu v hv).mpr hadj⟩⟩
  change ((G₁.interedges A B).card : ℚ) / (A.card * B.card) =
    ((G₂.interedges A B).card : ℚ) / (A.card * B.card)
  rw [hint]

lemma isUniform_congr_on {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] {ε : ℝ} {A B : Finset (Fin n)}
    (h : ∀ u ∈ A, ∀ v ∈ B, G₁.Adj u v ↔ G₂.Adj u v) :
    G₁.IsUniform ε A B ↔ G₂.IsUniform ε A B := by
  constructor <;> intro hunif s' hs' t' ht' hs ht
  · rw [← edgeDensity_congr_on G₁ G₂ (fun u hu v hv ↦ h u (hs' hu) v (ht' hv)),
      ← edgeDensity_congr_on G₁ G₂ h]
    exact hunif hs' ht' hs ht
  · rw [edgeDensity_congr_on G₁ G₂ (fun u hu v hv ↦ h u (hs' hu) v (ht' hv)),
      edgeDensity_congr_on G₁ G₂ h]
    exact hunif hs' ht' hs ht

lemma trim_isUniform {n m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {U₁ U₂ V₁ V₂ : Finset (Fin n)}
    (hV₁U : V₁ ⊆ U₁) (hV₂U : V₂ ⊆ U₂)
    (hV₁ : V₁.card = m) (hV₂ : V₂.card = m)
    (hU₁ : U₁.card ≤ m + 1) (hU₂ : U₂.card ≤ m + 1)
    (hunif : G.IsUniform ε U₁ U₂) :
    G.IsUniform (2 * ε) V₁ V₂ := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hε_pos : 0 < ε := hunif.pos
  have hU₁m : (U₁.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hU₁
  have hU₂m : (U₂.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hU₂
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hVU₁ : (U₁.card : ℝ) * ε ≤ (V₁.card : ℝ) := by rw [hV₁]; nlinarith
  have hVU₂ : (U₂.card : ℝ) * ε ≤ (V₂.card : ℝ) := by rw [hV₂]; nlinarith
  have hbase : |(G.edgeDensity V₁ V₂ : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| < ε :=
    hunif hV₁U hV₂U hVU₁ hVU₂
  intro s' hs' t' ht' hs ht
  have hs_U : (U₁.card : ℝ) * ε ≤ (s'.card : ℝ) := by
    rw [hV₁] at hs; nlinarith
  have ht_U : (U₂.card : ℝ) * ε ≤ (t'.card : ℝ) := by
    rw [hV₂] at ht; nlinarith
  have hsub : |(G.edgeDensity s' t' : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| < ε :=
    hunif (hs'.trans hV₁U) (ht'.trans hV₂U) hs_U ht_U
  calc |(G.edgeDensity s' t' : ℝ) - (G.edgeDensity V₁ V₂ : ℝ)|
      = |((G.edgeDensity s' t' : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)) -
          ((G.edgeDensity V₁ V₂ : ℝ) - (G.edgeDensity U₁ U₂ : ℝ))| := by ring_nf
    _ ≤ |(G.edgeDensity s' t' : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| +
        |(G.edgeDensity V₁ V₂ : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| := abs_sub _ _
    _ < ε + ε := add_lt_add hsub hbase
    _ = 2 * ε := by ring

/- ### Section 2: LP Duality for Bounded-Clique Packing (Hahn--Banach) -/

lemma lp_duality_cliques {n L : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : ℝ)
    (hdual : ∀ z : Sym2 (Fin n) → ℝ,
      (∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1) →
      ∑ e ∈ G.edgeFinset, z e ≤ M) :
    ∃ w : Finset (Fin n) → ℝ,
      (∀ Q, 0 ≤ w Q) ∧
      (∀ e ∈ G.edgeFinset,
        ∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun (Q : Finset (Fin n)) ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q),
          w Q ≤ 1) ∧
      (G.edgeFinset.card : ℝ) -
        ∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun (Q : Finset (Fin n)) ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n))),
          ((Q.card.choose 2 : ℝ) - 1) * w Q ≤ M := by
  classical
  have hM_nonneg : 0 ≤ M := by
    have h0 := hdual (fun _ ↦ 0) (fun _ _ _ _ ↦ by simp)
    simpa using h0
  -- Handle `M = 0` separately: then `G.edgeFinset = ∅`.
  rcases eq_or_lt_of_le hM_nonneg with rfl | hM_pos
  · have hE_empty : G.edgeFinset = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro e₀ he₀
      let z : Sym2 (Fin n) → ℝ := fun e ↦ if e = e₀ then 1 else 0
      have hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1 := by
        intro Q _ _ _
        simp only [z, sum_ite_eq']
        split_ifs <;> norm_num
      have h1 := hdual z hz
      simp only [z, sum_ite_eq', if_pos he₀] at h1
      linarith
    refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, fun _ _ ↦ by simp, ?_⟩
    simp [hE_empty]
  -- Now `0 < M`. Set up the finite-dimensional simplex and its image in `(E → ℝ)`.
  let E : Finset (Sym2 (Fin n)) := G.edgeFinset
  let 𝒬 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun Q ↦ 2 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)))
  let S : Set ({ Q // Q ∈ 𝒬 } → ℝ) :=
    { w | (∀ Q, 0 ≤ w Q) ∧ ∑ Q, w Q ≤ M }
  let Φ : ({ Q // Q ∈ 𝒬 } → ℝ) →ₗ[ℝ] ({ e // e ∈ E } → ℝ) :=
    { toFun := fun w e ↦ ∑ Q : { Q // Q ∈ 𝒬 }, if (∀ x ∈ e.1, x ∈ Q.1) then w Q else 0
      map_add' := fun w₁ w₂ ↦ by
        ext e
        simp only [Pi.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun Q _ ↦ ?_
        split_ifs <;> ring
      map_smul' := fun r w ↦ by
        ext e
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun Q _ ↦ ?_
        split_ifs <;> ring }
  have hS_closed : IsClosed S := by
    have h1 : IsClosed { w : { Q // Q ∈ 𝒬 } → ℝ | ∀ Q, 0 ≤ w Q } := by
      have : { w : { Q // Q ∈ 𝒬 } → ℝ | ∀ Q, 0 ≤ w Q } =
          ⋂ Q : { Q // Q ∈ 𝒬 }, { w | 0 ≤ w Q } := by ext; simp
      rw [this]
      exact isClosed_iInter fun Q ↦ isClosed_le continuous_const (continuous_apply Q)
    have h2 : IsClosed { w : { Q // Q ∈ 𝒬 } → ℝ | ∑ Q, w Q ≤ M } :=
      isClosed_le (continuous_finsetSum _ fun Q _ ↦ continuous_apply Q) continuous_const
    exact h1.inter h2
  have hS_sub : S ⊆ Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) M) := by
    intro w hw Q _
    refine ⟨hw.1 Q, ?_⟩
    calc w Q ≤ ∑ Q' : { Q // Q ∈ 𝒬 }, w Q' :=
          single_le_sum (fun Q' _ ↦ hw.1 Q') (mem_univ Q)
      _ ≤ M := hw.2
  have hS_compact : IsCompact S :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hS_closed hS_sub
  have hS_convex : Convex ℝ S := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨fun Q ↦ add_nonneg (mul_nonneg ha (hw₁.1 Q)) (mul_nonneg hb (hw₂.1 Q)), ?_⟩
    calc ∑ Q, (a * w₁ Q + b * w₂ Q)
        = a * ∑ Q, w₁ Q + b * ∑ Q, w₂ Q := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ a * M + b * M := add_le_add (mul_le_mul_of_nonneg_left hw₁.2 ha)
          (mul_le_mul_of_nonneg_left hw₂.2 hb)
      _ = (a + b) * M := by ring
      _ = M := by rw [hab, one_mul]
  have hΦ_cont : Continuous Φ := Φ.continuous_of_finiteDimensional
  let K : Set ({ e // e ∈ E } → ℝ) := Φ '' S
  have hK_closed : IsClosed K := (hS_compact.image hΦ_cont).isClosed
  have hK_convex : Convex ℝ K := hS_convex.linear_image Φ
  have h0_mem : (0 : { e // e ∈ E } → ℝ) ∈ K :=
    ⟨0, ⟨fun _ ↦ le_rfl, by simpa using hM_nonneg⟩, map_zero Φ⟩
  let one_E : { e // e ∈ E } → ℝ := fun _ ↦ 1
  have hone_mem : one_E ∈ K := by
    by_contra hnot
    obtain ⟨f, u, hK_lt, hu_lt⟩ := geometric_hahn_banach_closed_point hK_convex hK_closed hnot
    have hu_pos : 0 < u := by
      have h0 := hK_lt 0 h0_mem
      rwa [map_zero] at h0
    -- Represent `f` on basis vectors `Pi.single e 1`.
    have hf_repr : ∀ v : { e // e ∈ E } → ℝ,
        f v = ∑ e : { e // e ∈ E }, v e * f (Pi.single e 1) := by
      intro v
      have hv : v = ∑ e : { e // e ∈ E }, v e • Pi.single e (1 : ℝ) := by
        ext e
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv]
      rw [map_sum]
      refine sum_congr rfl fun e _ ↦ ?_
      rw [map_smul, smul_eq_mul]
    let z : Sym2 (Fin n) → ℝ := fun e ↦
      if he : e ∈ E then (M / u) * f (Pi.single ⟨e, he⟩ 1) else 0
    have hz_dual : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L →
        G.IsClique (Q : Set (Fin n)) →
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1 := by
      intro Q hQ2 hQL hQcl
      have hQmem : Q ∈ 𝒬 := mem_filter.mpr ⟨mem_univ Q, hQ2, hQL, hQcl⟩
      let wQ : { Q // Q ∈ 𝒬 } → ℝ := Pi.single ⟨Q, hQmem⟩ M
      have hwQ_mem : wQ ∈ S := by
        refine ⟨fun Q' ↦ ?_, ?_⟩
        · by_cases h : Q' = ⟨Q, hQmem⟩
          · subst h; simp [wQ, hM_nonneg]
          · simp [wQ, Pi.single_eq_of_ne h]
        · simp [wQ, Pi.single_apply]
      have hΦwQ : f (Φ wQ) < u := hK_lt (Φ wQ) ⟨wQ, hwQ_mem, rfl⟩
      have hΦ_eval : ∀ e : { e // e ∈ E },
          Φ wQ e = if (∀ x ∈ e.1, x ∈ Q) then M else 0 := by
        intro e
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, wQ, Pi.single_apply]
        rw [Finset.sum_eq_single ⟨Q, hQmem⟩]
        · simp
        · intro Q' _ hne; simp [hne]
        · intro h; exact absurd (mem_univ _) h
      have hfΦ : f (Φ wQ) = M * ∑ e : { e // e ∈ E },
          if (∀ x ∈ e.1, x ∈ Q) then f (Pi.single e 1) else 0 := by
        rw [hf_repr (Φ wQ), mul_sum]
        refine sum_congr rfl fun e _ ↦ ?_
        rw [hΦ_eval e]
        split_ifs <;> ring
      have hsum_eq : ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e =
          f (Φ wQ) / u := by
        rw [hfΦ, mul_div_assoc]
        have hlhs : ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e =
            ∑ e : { e // e ∈ E }, if (∀ x ∈ e.1, x ∈ Q) then z e.1 else 0 := by
          change ∑ e ∈ E.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e = _
          rw [Finset.sum_filter, ← Finset.sum_coe_sort E]
        rw [hlhs, sum_div, mul_sum]
        refine sum_congr rfl fun e _ ↦ ?_
        split_ifs
        · simp only [z, dif_pos e.2]; ring
        · simp
      rw [hsum_eq]
      exact (div_lt_one hu_pos).mpr hΦwQ |>.le
    have hbound := hdual z hz_dual
    have htotal : ∑ e ∈ G.edgeFinset, z e = (M / u) * f one_E := by
      rw [hf_repr one_E, mul_sum]
      have hlhs : ∑ e ∈ G.edgeFinset, z e = ∑ e : { e // e ∈ E }, z e.1 := by
        simpa [E] using (Finset.sum_coe_sort E z).symm
      rw [hlhs]
      refine sum_congr rfl fun e _ ↦ ?_
      simp [z, one_E, dif_pos e.2]
    rw [htotal] at hbound
    have hgt : M < (M / u) * f one_E := by
      have h1 : (M / u) * u < (M / u) * f one_E :=
        mul_lt_mul_of_pos_left hu_lt (div_pos hM_pos hu_pos)
      rwa [div_mul_cancel₀ M hu_pos.ne'] at h1
    linarith
  -- Extract `w ∈ S` with `Φ w = one_E`.
  obtain ⟨w_sub, hw_mem, hw_eq⟩ := hone_mem
  let w : Finset (Fin n) → ℝ := fun Q ↦ if hQ : Q ∈ 𝒬 then w_sub ⟨Q, hQ⟩ else 0
  have hw_nonneg : ∀ Q, 0 ≤ w Q := by
    intro Q; simp only [w]; split_ifs with h
    · exact hw_mem.1 ⟨Q, h⟩
    · exact le_rfl
  have hw_cover : ∀ e ∈ E, ∑ Q ∈ 𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q), w Q = 1 := by
    intro e he
    have h1 := congr_fun hw_eq ⟨e, he⟩
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, one_E] at h1
    rw [← h1, Finset.sum_filter, ← Finset.sum_coe_sort 𝒬]
    refine sum_congr rfl fun Q _ ↦ ?_
    simp [w, dif_pos Q.2]
  -- Double count edges covered by `𝒬`.
  have hdouble : (E.card : ℝ) = ∑ Q ∈ 𝒬, (Q.card.choose 2 : ℝ) * w Q := by
    calc (E.card : ℝ)
        = ∑ e ∈ E, (1 : ℝ) := by simp
      _ = ∑ e ∈ E, ∑ Q ∈ 𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q), w Q :=
          sum_congr rfl fun e he ↦ (hw_cover e he).symm
      _ = ∑ e ∈ E, ∑ Q ∈ 𝒬, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := by
          refine sum_congr rfl fun e _ ↦ Finset.sum_filter _ _
      _ = ∑ Q ∈ 𝒬, ∑ e ∈ E, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := Finset.sum_comm
      _ = ∑ Q ∈ 𝒬, (Q.card.choose 2 : ℝ) * w Q := by
          refine sum_congr rfl fun Q hQ ↦ ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hQcl : G.IsClique (Q : Set (Fin n)) := (mem_filter.mp hQ).2.2.2
          rw [clique_edges_card G Q hQcl]
  have hw_sum_le : ∑ Q ∈ 𝒬, w Q ≤ M := by
    calc ∑ Q ∈ 𝒬, w Q = ∑ Q : { Q // Q ∈ 𝒬 }, w_sub Q := by
          rw [← Finset.sum_coe_sort 𝒬]
          refine sum_congr rfl fun Q _ ↦ by simp [w, dif_pos Q.2]
      _ ≤ M := hw_mem.2
  let 𝒬3 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)))
  have h𝒬3_sub : 𝒬3 ⊆ 𝒬 := by
    intro Q hQ
    simp only [𝒬3, 𝒬, mem_filter, mem_univ, true_and] at hQ ⊢
    exact ⟨by omega, hQ.2.1, hQ.2.2⟩
  refine ⟨w, hw_nonneg, ?_, ?_⟩
  · intro e he
    have hsub : ((Finset.univ : Finset (Finset (Fin n))).filter (fun (Q : Finset (Fin n)) ↦
        3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q)) ⊆
        𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q) := by
      intro Q hQ
      simp only [𝒬, mem_filter, mem_univ, true_and] at hQ ⊢
      exact ⟨⟨by omega, hQ.2.1, hQ.2.2.1⟩, hQ.2.2.2⟩
    calc ∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun (Q : Finset (Fin n)) ↦
            3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q), w Q
        ≤ ∑ Q ∈ 𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q), w Q :=
          sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ ↦ hw_nonneg Q)
      _ = 1 := hw_cover e he
  · have hsplit : ∑ Q ∈ 𝒬, ((Q.card.choose 2 : ℝ) - 1) * w Q =
        ∑ Q ∈ 𝒬3, ((Q.card.choose 2 : ℝ) - 1) * w Q := by
      symm
      refine sum_subset h𝒬3_sub fun Q hQ hQ3 ↦ ?_
      simp only [𝒬, mem_filter, mem_univ, true_and] at hQ
      simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3
      have hnot3 : ¬(3 ≤ Q.card) := fun h3 ↦ hQ3 ⟨h3, hQ.2.1, hQ.2.2⟩
      have hcard2 : Q.card = 2 := by omega
      simp [hcard2]
    have hident : (E.card : ℝ) - ∑ Q ∈ 𝒬, ((Q.card.choose 2 : ℝ) - 1) * w Q =
        ∑ Q ∈ 𝒬, w Q := by
      rw [hdouble]
      have : ∑ Q ∈ 𝒬, ((Q.card.choose 2 : ℝ) - 1) * w Q =
          ∑ Q ∈ 𝒬, (Q.card.choose 2 : ℝ) * w Q - ∑ Q ∈ 𝒬, w Q := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun Q _ ↦ by ring
      linarith
    have : (E.card : ℝ) - ∑ Q ∈ 𝒬3, ((Q.card.choose 2 : ℝ) - 1) * w Q = ∑ Q ∈ 𝒬, w Q := by
      rw [← hsplit, hident]
    linarith

/- ### Section 3: Basic Feasible Solution Support Bound -/

lemma bfs_support_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c : ι → ℝ) (B : ℝ)
    (x₀ : ι → ℝ)
    (hx₀_nonneg : ∀ i, 0 ≤ x₀ i)
    (hx₀_le : ∀ j, ∑ i, A j i * x₀ i ≤ b j)
    (hbounded : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ j, ∑ i, A j i * x i ≤ b j) → ∀ i, x i ≤ B) :
    ∃ x : ι → ℝ,
      (∀ i, 0 ≤ x i) ∧
      (∀ j, ∑ i, A j i * x i ≤ b j) ∧
      ∑ i, c i * x₀ i ≤ ∑ i, c i * x i ∧
      (Finset.univ.filter (fun i ↦ x i ≠ 0)).card ≤ Fintype.card κ := by
  classical
  let P : Set (ι → ℝ) := { x | (∀ i, 0 ≤ x i) ∧ ∀ j, ∑ i, A j i * x i ≤ b j }
  have hx₀P : x₀ ∈ P := ⟨hx₀_nonneg, hx₀_le⟩
  have hP_closed : IsClosed P := by
    have h1 : IsClosed { x : ι → ℝ | ∀ i, 0 ≤ x i } := by
      have : { x : ι → ℝ | ∀ i, 0 ≤ x i } = ⋂ i : ι, { x | 0 ≤ x i } := by ext; simp
      rw [this]
      exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed { x : ι → ℝ | ∀ j, ∑ i, A j i * x i ≤ b j } := by
      have : { x : ι → ℝ | ∀ j, ∑ i, A j i * x i ≤ b j } =
          ⋂ j : κ, { x | ∑ i, A j i * x i ≤ b j } := by ext; simp
      rw [this]
      exact isClosed_iInter fun j ↦
        isClosed_le (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i))
          continuous_const
    exact h1.inter h2
  have hP_sub : P ⊆ Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) B) :=
    fun x hx i _ ↦ ⟨hx.1 i, hbounded x hx.1 hx.2 i⟩
  have hP_compact : IsCompact P :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hP_closed hP_sub
  let obj : (ι → ℝ) → ℝ := fun x ↦ ∑ i, c i * x i
  have hobj_cont : Continuous obj :=
    continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i)
  obtain ⟨x_init, hx_initP, hx_init_max⟩ :=
    hP_compact.exists_isMaxOn ⟨x₀, hx₀P⟩ hobj_cont.continuousOn
  let P_opt : Set (ι → ℝ) := { x ∈ P | ∀ y ∈ P, obj y ≤ obj x }
  have hP_opt_ne : ∃ s : ℕ, ∃ x ∈ P_opt, (Finset.univ.filter (fun i ↦ x i ≠ 0)).card = s :=
    ⟨(Finset.univ.filter (fun i ↦ x_init i ≠ 0)).card, x_init,
      ⟨hx_initP, fun y hy ↦ hx_init_max hy⟩, rfl⟩
  let s_min := Nat.find hP_opt_ne
  obtain ⟨x, hx_opt, hx_card⟩ := Nat.find_spec hP_opt_ne
  refine ⟨x, hx_opt.1.1, hx_opt.1.2, hx_opt.2 x₀ hx₀P, ?_⟩
  rw [hx_card]
  by_contra hlt
  push Not at hlt
  -- `Fintype.card κ < supp.card`
  let supp : Finset ι := Finset.univ.filter (fun i ↦ x i ≠ 0)
  have hsupp_gt : Fintype.card κ < supp.card := by simpa [supp, hx_card] using hlt
  let Lmap : ({ i // i ∈ supp } → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun d j ↦ ∑ i : { i // i ∈ supp }, A j i.1 * d i
      map_add' := fun d₁ d₂ ↦ by
        ext j; simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun r d ↦ by
        ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun i _ ↦ by ring }
  have hrank : Module.finrank ℝ (LinearMap.range Lmap) + Module.finrank ℝ (LinearMap.ker Lmap) =
      Module.finrank ℝ ({ i // i ∈ supp } → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker Lmap
  have hrange_le : Module.finrank ℝ (LinearMap.range Lmap) ≤ Fintype.card κ := by
    calc Module.finrank ℝ (LinearMap.range Lmap)
        ≤ Module.finrank ℝ (κ → ℝ) := Submodule.finrank_le _
      _ = Fintype.card κ := Module.finrank_pi ℝ
  have hdom : Module.finrank ℝ ({ i // i ∈ supp } → ℝ) = supp.card := by
    rw [Module.finrank_pi ℝ, Fintype.card_coe]
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker Lmap) := by omega
  have hker_ne : LinearMap.ker Lmap ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    omega
  obtain ⟨d_sub, hd_ker, hd_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  let d0 : ι → ℝ := fun i ↦ if hi : i ∈ supp then d_sub ⟨i, hi⟩ else 0
  have hd0_ne : ∃ i ∈ supp, d0 i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hd_ne
    ext ⟨i, hi⟩
    have := hall i hi
    simpa [d0, dif_pos hi] using this
  have hd0_out : ∀ i, i ∉ supp → d0 i = 0 := fun i hi ↦ dif_neg hi
  have hd0_ker : ∀ j : κ, ∑ i : ι, A j i * d0 i = 0 := by
    intro j
    have hj : Lmap d_sub j = 0 := congr_fun (LinearMap.mem_ker.mp hd_ker) j
    have hsum : ∑ i : ι, A j i * d0 i = ∑ i ∈ supp, A j i * d0 i := by
      symm
      refine sum_subset (subset_univ supp) fun i _ hi ↦ by simp [hd0_out i hi]
    rw [hsum, ← Finset.sum_coe_sort supp]
    simpa [Lmap, d0] using hj
  -- Prove `obj d0 = 0` by small perturbations `x ± t₀ • d0 ∈ P`.
  have hsupp_pos : ∀ i ∈ supp, 0 < x i := fun i hi ↦
    lt_of_le_of_ne (hx_opt.1.1 i) (Ne.symm (mem_filter.mp hi).2)
  have hsupp_ne : supp.Nonempty := by
    obtain ⟨i, hi, _⟩ := hd0_ne; exact ⟨i, hi⟩
  obtain ⟨i_min, hi_min, hmin_le⟩ :=
    Finset.exists_min_image supp (fun i ↦ x i / (|d0 i| + 1)) hsupp_ne
  let t₀ : ℝ := x i_min / (|d0 i_min| + 1)
  have ht₀_pos : 0 < t₀ := div_pos (hsupp_pos i_min hi_min) (by positivity)
  have hpert : ∀ t : ℝ, |t| ≤ t₀ → (fun i ↦ x i + t * d0 i) ∈ P := by
    intro t ht
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · by_cases hi : i ∈ supp
      · have hle : t₀ ≤ x i / (|d0 i| + 1) := hmin_le i hi
        have h1 : |t| * (|d0 i| + 1) ≤ x i := by
          have hpos : (0 : ℝ) < |d0 i| + 1 := by positivity
          calc |t| * (|d0 i| + 1) ≤ t₀ * (|d0 i| + 1) :=
                mul_le_mul_of_nonneg_right ht hpos.le
            _ ≤ (x i / (|d0 i| + 1)) * (|d0 i| + 1) :=
                mul_le_mul_of_nonneg_right hle hpos.le
            _ = x i := div_mul_cancel₀ _ hpos.ne'
        have h2 : -(t * d0 i) ≤ |t| * |d0 i| := by
          calc -(t * d0 i) ≤ |t * d0 i| := neg_le_abs _
            _ = |t| * |d0 i| := abs_mul _ _
        nlinarith [abs_nonneg t]
      · simp [hd0_out i hi, hx_opt.1.1 i]
    · calc ∑ i, A j i * (x i + t * d0 i)
          = ∑ i, A j i * x i + t * ∑ i, A j i * d0 i := by
            rw [mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ ↦ by ring
        _ = ∑ i, A j i * x i := by rw [hd0_ker j, mul_zero, add_zero]
        _ ≤ b j := hx_opt.1.2 j
  have hobj_d0 : obj d0 = 0 := by
    have hplus := hx_opt.2 (fun i ↦ x i + t₀ * d0 i) (hpert t₀ (by rw [abs_of_pos ht₀_pos]))
    have hminus := hx_opt.2 (fun i ↦ x i + (-t₀) * d0 i)
      (hpert (-t₀) (by rw [abs_neg, abs_of_pos ht₀_pos]))
    have heq1 : obj (fun i ↦ x i + t₀ * d0 i) = obj x + t₀ * obj d0 := by
      simp only [obj, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ ↦ by ring
    have heq2 : obj (fun i ↦ x i + (-t₀) * d0 i) = obj x - t₀ * obj d0 := by
      simp only [obj, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ by ring
    rw [heq1] at hplus
    rw [heq2] at hminus
    nlinarith
  -- Orient `d` so that some coordinate in `supp` is strictly negative.
  obtain ⟨i_nz, hi_nz, hnz⟩ := hd0_ne
  let d : ι → ℝ := if d0 i_nz < 0 then d0 else fun i ↦ -d0 i
  have hd_out : ∀ i, i ∉ supp → d i = 0 := by
    intro i hi; simp only [d]; split_ifs <;> simp [hd0_out i hi]
  have hd_ker_eq : ∀ j : κ, ∑ i : ι, A j i * d i = 0 := by
    intro j; simp only [d]; split_ifs
    · exact hd0_ker j
    · simp only [mul_neg, sum_neg_distrib, hd0_ker j, neg_zero]
  have hd_obj : obj d = 0 := by
    simp only [d]; split_ifs
    · exact hobj_d0
    · simp only [obj, mul_neg, sum_neg_distrib]
      have : ∑ i, c i * d0 i = 0 := hobj_d0
      linarith
  have hd_has_neg : ∃ i ∈ supp, d i < 0 := by
    refine ⟨i_nz, hi_nz, ?_⟩
    simp only [d]; split_ifs with h
    · exact h
    · push Not at h
      have : 0 < d0 i_nz := lt_of_le_of_ne h (Ne.symm hnz)
      linarith
  let S_neg : Finset ι := supp.filter (fun i ↦ d i < 0)
  have hS_neg : S_neg.Nonempty := by
    obtain ⟨i, hi, hdi⟩ := hd_has_neg
    exact ⟨i, mem_filter.mpr ⟨hi, hdi⟩⟩
  obtain ⟨i_hit, hi_hit, hhit_min⟩ :=
    Finset.exists_min_image S_neg (fun i ↦ x i / (-d i)) hS_neg
  have hi_hit_supp : i_hit ∈ supp := (mem_filter.mp hi_hit).1
  have hdi_hit_neg : d i_hit < 0 := (mem_filter.mp hi_hit).2
  let t_star : ℝ := x i_hit / (-d i_hit)
  have ht_star_pos : 0 < t_star :=
    div_pos (hsupp_pos i_hit hi_hit_supp) (by linarith)
  let x_new : ι → ℝ := fun i ↦ x i + t_star * d i
  have hx_newP : x_new ∈ P := by
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · by_cases hi : i ∈ supp
      · by_cases hdi : d i < 0
        · have hi_neg : i ∈ S_neg := mem_filter.mpr ⟨hi, hdi⟩
          have hle : t_star ≤ x i / (-d i) := hhit_min i hi_neg
          have hpos : 0 < -d i := by linarith
          have hmul : t_star * (-d i) ≤ x i := (le_div_iff₀ hpos).mp hle
          simp only [x_new]; linarith
        · push Not at hdi
          simp only [x_new]
          exact add_nonneg (hx_opt.1.1 i) (mul_nonneg ht_star_pos.le hdi)
      · simp [x_new, hd_out i hi, hx_opt.1.1 i]
    · calc ∑ i, A j i * x_new i
          = ∑ i, A j i * x i + t_star * ∑ i, A j i * d i := by
            simp only [x_new, mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ ↦ by ring
        _ = ∑ i, A j i * x i := by rw [hd_ker_eq j, mul_zero, add_zero]
        _ ≤ b j := hx_opt.1.2 j
  have hx_new_obj : obj x_new = obj x := by
    have : obj x_new = obj x + t_star * obj d := by
      simp only [obj, x_new, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ ↦ by ring
    rw [this, hd_obj, mul_zero, add_zero]
  have hx_new_opt : x_new ∈ P_opt :=
    ⟨hx_newP, fun y hy ↦ hx_new_obj.symm ▸ hx_opt.2 y hy⟩
  have hx_hit_zero : x_new i_hit = 0 := by
    have hne : -d i_hit ≠ 0 := by linarith
    have hmul : x i_hit / (-d i_hit) * d i_hit = -x i_hit := by
      rw [div_mul_eq_mul_div, div_eq_iff hne]
      ring
    simp only [x_new, t_star]
    linarith
  have hsub_supp : Finset.univ.filter (fun i ↦ x_new i ≠ 0) ⊆ supp.erase i_hit := by
    intro i hi
    have hne : x_new i ≠ 0 := (mem_filter.mp hi).2
    have hi_ne : i ≠ i_hit := fun heq ↦ hne (heq ▸ hx_hit_zero)
    have hi_supp : i ∈ supp := by
      by_contra hnot
      have hxi : x i = 0 := by
        by_contra hxne
        exact hnot (mem_filter.mpr ⟨mem_univ i, hxne⟩)
      exact hne (by simp [x_new, hxi, hd_out i hnot])
    exact mem_erase.mpr ⟨hi_ne, hi_supp⟩
  have hcard_lt : (Finset.univ.filter (fun i ↦ x_new i ≠ 0)).card < s_min := by
    have h1 := Finset.card_le_card hsub_supp
    have h2 : (supp.erase i_hit).card < supp.card := card_erase_lt_of_mem hi_hit_supp
    have hsupp_eq : supp.card = s_min := hx_card
    omega
  exact Nat.find_min hP_opt_ne hcard_lt ⟨x_new, hx_new_opt, rfl⟩

/- ### Section 4: Simultaneous `H2` Parameters Across `3 ≤ q ≤ L` -/

lemma h2_uniform_params (h2 : H2) (L : ℕ) (hL : 3 ≤ L) (δ : ℝ) (hδ : 0 < δ)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ m₀ : ℕ,
      ∀ q : ℕ, 3 ≤ q → q ≤ L →
        ∀ (n m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
          (V : Fin q → Finset (Fin n)),
          (∀ i j, i ≠ j → Disjoint (V i) (V j)) →
          (∀ i, (V i).card = m) →
          ∀ p : ℝ, δ ≤ p → p ≤ 1 →
          (∀ i j, i ≠ j → G.IsUniform ε₁ (V i) (V j) ∧
            |(G.edgeDensity (V i) (V j) : ℝ) - p| ≤ ε₁) →
          ∃ 𝒬 : Finset (Finset (Fin n)),
            (∀ Q ∈ 𝒬, Q.card = q ∧ G.IsClique (Q : Set (Fin n)) ∧
              ∀ i : Fin q, (Q ∩ V i).card = 1) ∧
            (∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
            (p - η) * (m : ℝ) ^ 2 ≤ (𝒬.card : ℝ) := by
  induction L, hL using Nat.le_induction with
  | base =>
    obtain ⟨ε₁, hε₁, m₀, hspec⟩ := h2 3 le_rfl δ hδ η hη
    refine ⟨ε₁, hε₁, m₀, fun q hq3 hqL ↦ ?_⟩
    have hq : q = 3 := by omega
    subst hq
    exact hspec
  | succ k hk ih =>
    obtain ⟨ε_ih, hε_ih, m_ih, hspec_ih⟩ := ih
    obtain ⟨ε_k, hε_k, m_k, hspec_k⟩ := h2 (k + 1) (by omega) δ hδ η hη
    refine ⟨min ε_ih ε_k, lt_min hε_ih hε_k, max m_ih m_k, ?_⟩
    intro q hq3 hqk n m hm G _ V hdisj hcard p hpδ hp1 hunif
    rcases lt_or_eq_of_le hqk with hlt | rfl
    · exact hspec_ih q hq3 (by omega) n m (le_trans (le_max_left _ _) hm) G V hdisj hcard
        p hpδ hp1 (fun i j hij ↦
          ⟨(hunif i j hij).1.mono (min_le_left _ _),
            (hunif i j hij).2.trans (min_le_left _ _)⟩)
    · exact hspec_k n m (le_trans (le_max_right _ _) hm) G V hdisj hcard
        p hpδ hp1 (fun i j hij ↦
          ⟨(hunif i j hij).1.mono (min_le_right _ _),
            (hunif i j hij).2.trans (min_le_right _ _)⟩)

/- ### Section 5: Main Reduction Theorem -/

set_option maxHeartbeats 1600000 in
theorem main : H1 → H2 → OMA.R_Erdos81_erdos_81_R1.H2 := by
  intro h1 h2 L hL ζ hζ
  classical
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hL2_pos : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hL_pos
  -- Step 1: Choose all constants in non-circular order.
  let δ : ℝ := ζ / (16 * (L : ℝ) ^ 2)
  let η : ℝ := ζ / (16 * (L : ℝ) ^ 2)
  have hδ_pos : 0 < δ := div_pos hζ (by positivity)
  have hη_pos : 0 < η := div_pos hζ (by positivity)
  obtain ⟨ε₁, hε₁_pos, m₀_pack, hpack⟩ := h2_uniform_params h2 L hL δ hδ_pos η hη_pos
  obtain ⟨ε_split, hε_split_pos, m₀_split, hsplit⟩ := h1 ε₁ hε₁_pos δ hδ_pos
  let ε_reg : ℝ := min (min (ε_split / 2) (1 / 2)) (ζ / (16 * (L : ℝ) ^ 2))
  have hε_reg_pos : 0 < ε_reg :=
    lt_min (lt_min (half_pos hε_split_pos) (by norm_num)) (div_pos hζ (by positivity))
  have hε_reg_split : 2 * ε_reg ≤ ε_split := by
    have : ε_reg ≤ ε_split / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hε_reg_half : ε_reg ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε_reg_ζ : ε_reg ≤ ζ / (16 * (L : ℝ) ^ 2) := min_le_right _ _
  let l : ℕ := max 1 (Nat.ceil (16 * (L : ℝ) ^ 2 / ζ))
  have hl_pos : 1 ≤ l := le_max_left _ _
  have hl_bound : 16 * (L : ℝ) ^ 2 / ζ ≤ (l : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  let K_max : ℕ := SzemerediRegularity.bound ε_reg l
  let m_req : ℕ := max 1 (max m₀_split m₀_pack)
  let n₀ : ℕ := max (max l (K_max * m_req))
    (Nat.ceil (16 * (L : ℝ) ^ 2 * (K_max : ℝ) / ζ))
  refine ⟨n₀, fun n hn G _ M hdual ↦ ?_⟩
  -- Handle `n = 0` (cannot happen since `1 ≤ l ≤ n₀ ≤ n`, so `0 < n`).
  have hn_l : l ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by omega) hn_l
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  -- Step 2: LP Duality gives fractional packing `w` on cliques of size `3..L`.
  obtain ⟨w, hw_nonneg, hw_edge, hw_val⟩ := lp_duality_cliques G M hdual
  let 𝒬3 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)))
  -- Step 3: Apply Szemerédi Regularity Lemma to `G`.
  have hl_card : l ≤ Fintype.card (Fin n) := by simpa using hn_l
  obtain ⟨P, hP_eq, hl_k, hk_max, hP_unif⟩ := szemeredi_regularity G hε_reg_pos hl_card
  let k : ℕ := P.parts.card
  have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hl_k
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  -- Enumerate parts of `P` as `U : Fin k → Finset (Fin n)`.
  let eParts : P.parts ≃ Fin k := P.parts.equivFin
  let U : Fin k → Finset (Fin n) := fun i ↦ (eParts.symm i).1
  have hU_mem : ∀ i : Fin k, U i ∈ P.parts := fun i ↦ (eParts.symm i).2
  have hU_inj : Function.Injective U := fun i j hij ↦ by
    apply eParts.symm.injective
    exact Subtype.ext hij
  have hU_disj : ∀ i j : Fin k, i ≠ j → Disjoint (U i) (U j) := fun i j hij ↦
    P.disjoint (hU_mem i) (hU_mem j) (fun h ↦ hij (hU_inj h))
  -- Trim each part `U i` to exact size `m = n / k`.
  let m : ℕ := n / k
  have hU_card_lo : ∀ i : Fin k, m ≤ (U i).card := by
    intro i
    have := hP_eq.average_le_card_part (hU_mem i)
    simpa [m, k] using this
  have hU_card_hi : ∀ i : Fin k, (U i).card ≤ m + 1 := by
    intro i
    have := hP_eq.card_part_le_average_add_one (hU_mem i)
    simpa [m, k] using this
  have hm_req : m_req ≤ m := by
    have hn_Km : K_max * m_req ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hkm : k * m_req ≤ n := le_trans (Nat.mul_le_mul_right m_req hk_max) hn_Km
    exact (Nat.le_div_iff_mul_le hk_pos).mpr (by rwa [mul_comm])
  have hm_one : 1 ≤ m := le_trans (le_max_left _ _) hm_req
  have hm_split : m₀_split ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm_req
  have hm_pack : m₀_pack ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm_req
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hkm_le_n : k * m ≤ n := Nat.mul_div_le n k
  have hkm_le_n_real : (k : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkm_le_n
  -- Choose trimmed clusters `V i ⊆ U i` with `(V i).card = m`.
  have hV_ex : ∀ i : Fin k, ∃ s : Finset (Fin n), s ⊆ U i ∧ s.card = m :=
    fun i ↦ Finset.exists_subset_card_eq (hU_card_lo i)
  let V : Fin k → Finset (Fin n) := fun i ↦ (hV_ex i).choose
  have hV_sub : ∀ i : Fin k, V i ⊆ U i := fun i ↦ (hV_ex i).choose_spec.1
  have hV_card : ∀ i : Fin k, (V i).card = m := fun i ↦ (hV_ex i).choose_spec.2
  have hV_disj : ∀ i j : Fin k, i ≠ j → Disjoint (V i) (V j) := fun i j hij ↦
    (hU_disj i j hij).mono (hV_sub i) (hV_sub j)
  -- Step 4: Regular cluster pairs `E_reg` and good/bad edges of `G`.
  let E_reg : Finset (Sym2 (Fin k)) :=
    Finset.univ.filter (fun e ↦ ¬e.IsDiag ∧ ∀ i j : Fin k, e = s(i, j) →
      G.IsUniform ε_reg (U i) (U j))
  have hE_reg_mem : ∀ i j : Fin k, s(i, j) ∈ E_reg ↔ i ≠ j ∧ G.IsUniform ε_reg (U i) (U j) := by
    intro i j
    simp only [E_reg, mem_filter, mem_univ, true_and, Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨hij, h⟩; exact ⟨hij, h i j rfl⟩
    · rintro ⟨hij, h⟩
      refine ⟨hij, fun a b hab ↦ ?_⟩
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact h.symm
  have hE_reg_unif_split : ∀ i j : Fin k, s(i, j) ∈ E_reg → G.IsUniform ε_split (V i) (V j) := by
    intro i j hij
    have hu := (hE_reg_mem i j).mp hij |>.2
    exact (trim_isUniform hm_one hε_reg_half G (hV_sub i) (hV_sub j)
      (hV_card i) (hV_card j) (hU_card_hi i) (hU_card_hi j) hu).mono hε_reg_split
  -- Bound `E_reg.card ≤ k^2 / 2`.
  have hE_reg_card : (E_reg.card : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h2 : 2 * E_reg.card ≤ k * k := by
      let S_ord : Finset (Fin k × Fin k) :=
        Finset.univ.filter (fun p ↦ s(p.1, p.2) ∈ E_reg)
      have hS_le : S_ord.card ≤ k * k := by
        calc S_ord.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := card_le_card (subset_univ _)
          _ = k * k := by simp
      have hfib : S_ord.card = 2 * E_reg.card := by
        have hmap : S_ord.card = ∑ e ∈ E_reg, (S_ord.filter (fun p ↦ s(p.1, p.2) = e)).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext p; simp [S_ord]
          · intro e₁ _ e₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro p hp₁ hp₂
            exact hne ((mem_filter.mp hp₁).2.symm.trans (mem_filter.mp hp₂).2)
        rw [hmap]
        have h2e : ∀ e ∈ E_reg, (S_ord.filter (fun p ↦ s(p.1, p.2) = e)).card = 2 := by
          intro e he
          induction e using Sym2.ind with
          | h a b =>
            have hab : a ≠ b := ((hE_reg_mem a b).mp he).1
            have hset : S_ord.filter (fun p ↦ s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
              ext ⟨x, y⟩
              simp only [S_ord, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
                Prod.mk.injEq, Sym2.eq_iff]
              constructor
              · rintro ⟨_, h⟩; exact h
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
                · exact ⟨by rwa [Sym2.eq_swap], Or.inr ⟨rfl, rfl⟩⟩
            rw [hset, card_pair]
            intro h; exact hab (Prod.mk.inj h).1
        rw [Finset.sum_congr rfl h2e, Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have h2r : 2 * (E_reg.card : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (2 * E_reg.card : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith
    linarith
  -- Good edges and bad edges of `G`.
  let E_good : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e ↦ ∃ i j : Fin k, s(i, j) ∈ E_reg ∧
      ∃ u ∈ V i, ∃ v ∈ V j, e = s(u, v))
  let E_bad : Finset (Sym2 (Fin n)) := G.edgeFinset \ E_good
  -- Bound `E_bad.card ≤ (3 * ζ / (16 * L^2)) * n^2`.
  let V_union : Finset (Fin n) := Finset.univ.biUnion V
  let D_trim : Finset (Fin n) := Finset.univ \ V_union
  have hV_union_card : V_union.card = k * m := by
    rw [Finset.card_biUnion (fun i _ j _ hij ↦ hV_disj i j hij)]
    simp [hV_card]
  have hD_trim_card : D_trim.card ≤ k := by
    have hsub : V_union ⊆ Finset.univ := subset_univ _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, hV_union_card]
    have hmod : n = k * m + n % k := (Nat.div_add_mod n k).symm
    have hlt : n % k < k := Nat.mod_lt n hk_pos
    omega
  let B_trim : Finset (Sym2 (Fin n)) :=
    D_trim.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y)))
  let B_intra : Finset (Sym2 (Fin n)) :=
    (Finset.univ : Finset (Fin k)).biUnion (fun i ↦
      (V i ×ˢ V i).image (fun p ↦ s(p.1, p.2)))
  let badPairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2 ∧ ¬ G.IsUniform ε_reg (U p.1) (U p.2))
  let B_nonunif : Finset (Sym2 (Fin n)) :=
    badPairs.biUnion (fun p ↦ (V p.1 ×ˢ V p.2).image (fun q ↦ s(q.1, q.2)))
  have hE_bad_sub : E_bad ⊆ B_trim ∪ (B_intra ∪ B_nonunif) := by
    intro e he
    rw [mem_sdiff] at he
    obtain ⟨heG, he_not_good⟩ := he
    induction e using Sym2.ind with
    | h u v =>
      by_cases hu : u ∈ V_union
      · by_cases hv : v ∈ V_union
        · obtain ⟨i, _, hui⟩ := mem_biUnion.mp hu
          obtain ⟨j, _, hvj⟩ := mem_biUnion.mp hv
          by_cases hij : i = j
          · subst hij
            refine mem_union_right _ (mem_union_left _ ?_)
            exact mem_biUnion.mpr ⟨i, mem_univ i,
              mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hui, hvj⟩, rfl⟩⟩
          · have hnotreg : s(i, j) ∉ E_reg := fun hreg ↦
              he_not_good (mem_filter.mpr ⟨heG, i, j, hreg, u, hui, v, hvj, rfl⟩)
            have hnotunif : ¬ G.IsUniform ε_reg (U i) (U j) := fun hunif ↦
              hnotreg ((hE_reg_mem i j).mpr ⟨hij, hunif⟩)
            refine mem_union_right _ (mem_union_right _ ?_)
            exact mem_biUnion.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij, hnotunif⟩,
              mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hui, hvj⟩, rfl⟩⟩
        · refine mem_union_left _ (mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨mem_univ v, hv⟩,
            mem_image.mpr ⟨u, mem_univ u, Sym2.eq_swap⟩⟩)
      · refine mem_union_left _ (mem_biUnion.mpr ⟨u, mem_sdiff.mpr ⟨mem_univ u, hu⟩,
          mem_image.mpr ⟨v, mem_univ v, rfl⟩⟩)
  have hB_trim_card : (B_trim.card : ℝ) ≤ (K_max : ℝ) * (n : ℝ) := by
    have h1 : B_trim.card ≤ D_trim.card * n := by
      calc B_trim.card
          ≤ ∑ x ∈ D_trim, ((Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y))).card :=
            card_biUnion_le
        _ ≤ ∑ _x ∈ D_trim, n := sum_le_sum fun x _ ↦
            card_image_le.trans (by simp)
        _ = D_trim.card * n := by simp
    have h2 : B_trim.card ≤ K_max * n :=
      h1.trans (Nat.mul_le_mul_right n (hD_trim_card.trans hk_max))
    exact_mod_cast h2
  have hB_intra_card : (B_intra.card : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have h1 : B_intra.card ≤ k * (m * m) := by
      calc B_intra.card
          ≤ ∑ i : Fin k, ((V i ×ˢ V i).image (fun p ↦ s(p.1, p.2))).card := card_biUnion_le
        _ ≤ ∑ i : Fin k, (m * m) := sum_le_sum fun i _ ↦
            card_image_le.trans (by rw [card_product, hV_card i])
        _ = k * (m * m) := by simp
    have h1r : (B_intra.card : ℝ) ≤ (k : ℝ) * (m : ℝ) ^ 2 := by
      have : (B_intra.card : ℝ) ≤ ((k * (m * m) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have hl_le_k : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl_k
    have hkm2 : (k : ℝ) * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / (k : ℝ) := by
      rw [le_div_iff₀ hk_real_pos]
      have : ((k : ℝ) * (m : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hkm_le_n_real 2
      nlinarith
    have hdiv : (n : ℝ) ^ 2 / (k : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
      have h16 : (16 * (L : ℝ) ^ 2) / ζ ≤ (k : ℝ) := hl_bound.trans hl_le_k
      have hinv : 1 / (k : ℝ) ≤ ζ / (16 * (L : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hk_real_pos (by positivity)]
        have := (div_le_iff₀ hζ).mp h16
        linarith
      calc (n : ℝ) ^ 2 / (k : ℝ) = (1 / (k : ℝ)) * (n : ℝ) ^ 2 := by ring
        _ ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    exact h1r.trans (hkm2.trans hdiv)
  have hB_nonunif_card : (B_nonunif.card : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have hbad_le : badPairs.card ≤ (P.nonUniforms G ε_reg).card := by
      refine Finset.card_le_card_of_injOn (fun p ↦ (U p.1, U p.2)) ?_ ?_
      · intro p hp
        simp only [mem_coe, badPairs, mem_filter, mem_univ, true_and] at hp
        rw [mem_coe, Finpartition.mk_mem_nonUniforms]
        exact ⟨hU_mem p.1, hU_mem p.2, fun h ↦ hp.1 (hU_inj h), hp.2⟩
      · intro p₁ _ p₂ _ h
        have h1 : U p₁.1 = U p₂.1 := (Prod.mk.inj h).1
        have h2 : U p₁.2 = U p₂.2 := (Prod.mk.inj h).2
        exact Prod.ext (hU_inj h1) (hU_inj h2)
    have h1 : B_nonunif.card ≤ badPairs.card * (m * m) := by
      calc B_nonunif.card
          ≤ ∑ p ∈ badPairs, ((V p.1 ×ˢ V p.2).image (fun q ↦ s(q.1, q.2))).card :=
            card_biUnion_le
        _ ≤ ∑ _p ∈ badPairs, (m * m) := sum_le_sum fun p _ ↦
            card_image_le.trans (by rw [card_product, hV_card p.1, hV_card p.2])
        _ = badPairs.card * (m * m) := by simp
    have h1r : (B_nonunif.card : ℝ) ≤ (badPairs.card : ℝ) * (m : ℝ) ^ 2 := by
      have : (B_nonunif.card : ℝ) ≤ ((badPairs.card * (m * m) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have hbad_r : (badPairs.card : ℝ) ≤ (k : ℝ) ^ 2 * ε_reg := by
      have hnu : ((P.nonUniforms G ε_reg).card : ℝ) ≤ ((k * (k - 1) : ℕ) : ℝ) * ε_reg := hP_unif
      have hkk : ((k * (k - 1) : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
        rw [sq]
        exact_mod_cast this
      calc (badPairs.card : ℝ) ≤ ((P.nonUniforms G ε_reg).card : ℝ) := by exact_mod_cast hbad_le
        _ ≤ ((k * (k - 1) : ℕ) : ℝ) * ε_reg := hnu
        _ ≤ (k : ℝ) ^ 2 * ε_reg := mul_le_mul_of_nonneg_right hkk hε_reg_pos.le
    calc (B_nonunif.card : ℝ)
        ≤ ((k : ℝ) ^ 2 * ε_reg) * (m : ℝ) ^ 2 :=
          h1r.trans (mul_le_mul_of_nonneg_right hbad_r (sq_nonneg _))
      _ = ε_reg * ((k : ℝ) * (m : ℝ)) ^ 2 := by ring
      _ ≤ ε_reg * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkm_le_n_real 2) hε_reg_pos.le
      _ ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hε_reg_ζ (sq_nonneg _)
  have htrim_n : (K_max : ℝ) * (n : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have hn_ceil : 16 * (L : ℝ) ^ 2 * (K_max : ℝ) / ζ ≤ (n : ℝ) := by
      have h1 : Nat.ceil (16 * (L : ℝ) ^ 2 * (K_max : ℝ) / ζ) ≤ n :=
        le_trans (le_max_right _ _) hn
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hmul : 16 * (L : ℝ) ^ 2 * (K_max : ℝ) ≤ (n : ℝ) * ζ := (div_le_iff₀ hζ).mp hn_ceil
    have hdiv : (K_max : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    calc (K_max : ℝ) * (n : ℝ) ≤ ((ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hdiv hn_real_pos.le
      _ = (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by ring
  have hE_bad_card : (E_bad.card : ℝ) ≤ (3 * ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have hcard : E_bad.card ≤ B_trim.card + (B_intra.card + B_nonunif.card) :=
      (card_le_card hE_bad_sub).trans
        ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
    have hcard_r : (E_bad.card : ℝ) ≤ (B_trim.card : ℝ) + (B_intra.card : ℝ) + (B_nonunif.card : ℝ) := by
      have : (E_bad.card : ℝ) ≤ ((B_trim.card + (B_intra.card + B_nonunif.card) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      push_cast at this; linarith
    calc (E_bad.card : ℝ)
        ≤ (B_trim.card : ℝ) + (B_intra.card : ℝ) + (B_nonunif.card : ℝ) := hcard_r
      _ ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 + (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 +
          (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
        add_le_add (add_le_add (hB_trim_card.trans htrim_n) hB_intra_card) hB_nonunif_card
      _ = (3 * ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by ring
  -- Step 5: Restrict `w` to good cliques `𝒬_good` and aggregate onto regular cluster tuples `𝒯`.
  let 𝒬_good : Finset (Finset (Fin n)) :=
    𝒬3.filter (fun Q ↦ ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ Q) → e ∈ E_good)
  -- Helper: cluster index of a vertex `u ∈ V_union`.
  let clSet : Finset (Fin n) → Finset (Fin k) :=
    fun Q ↦ Finset.univ.filter (fun i ↦ (Q ∩ V i).Nonempty)
  let 𝒯 : Finset (Finset (Fin k)) :=
    Finset.univ.filter (fun T ↦ 3 ≤ T.card ∧ T.card ≤ L ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → s(i, j) ∈ E_reg)
  have hQgood_props : ∀ Q ∈ 𝒬_good,
      clSet Q ∈ 𝒯 ∧ (clSet Q).card = Q.card ∧
      (∀ i ∈ clSet Q, (Q ∩ V i).card = 1) ∧
      (∀ u ∈ Q, ∃ i ∈ clSet Q, u ∈ V i) := by
    intro Q hQ
    have hQ3 : Q ∈ 𝒬3 := (mem_filter.mp hQ).1
    have hQedge_good : ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ Q) → e ∈ E_good :=
      (mem_filter.mp hQ).2
    simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3
    obtain ⟨hQ_lo, hQ_hi, hQ_cl⟩ := hQ3
    -- Every vertex of `Q` lies in some `V i`.
    have hv_in_V : ∀ u ∈ Q, ∃ i : Fin k, u ∈ V i := by
      intro u hu
      have hne : (Q.erase u).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have := card_erase_of_mem hu
        rw [hemp, card_empty] at this
        omega
      obtain ⟨v, hv⟩ := hne
      have huv : u ≠ v := (mem_erase.mp hv).1.symm
      have hvQ : v ∈ Q := (mem_erase.mp hv).2
      have hadj : G.Adj u v := hQ_cl hu hvQ huv
      have hgood := hQedge_good s(u, v) (mem_edgeFinset.mpr hadj) (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
      obtain ⟨i, j, _, a, ha, b, hb, heq⟩ := (mem_filter.mp hgood).2
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨i, ha⟩
      · exact ⟨j, hb⟩
    -- No two distinct vertices of `Q` lie in the same `V i`.
    have huniq_in_V : ∀ i : Fin k, ∀ u ∈ Q, ∀ v ∈ Q, u ∈ V i → v ∈ V i → u = v := by
      intro i u hu v hv hui hvi
      by_contra huv
      have hadj : G.Adj u v := hQ_cl hu hv huv
      have hgood := hQedge_good s(u, v) (mem_edgeFinset.mpr hadj) (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
      obtain ⟨a, b, hab_reg, x, hxa, y, hyb, heq⟩ := (mem_filter.mp hgood).2
      have hab_ne : a ≠ b := ((hE_reg_mem a b).mp hab_reg).1
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hia : i = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i a h) hui hxa
        have hib : i = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i b h) hvi hyb
        exact hab_ne (hia.symm.trans hib)
      · have hib : i = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i b h) hui hyb
        have hia : i = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i a h) hvi hxa
        exact hab_ne (hia.symm.trans hib)
    have hcard_one : ∀ i ∈ clSet Q, (Q ∩ V i).card = 1 := by
      intro i hi
      obtain ⟨u, hu⟩ := (mem_filter.mp hi).2
      rw [Finset.card_eq_one]
      refine ⟨u, ?_⟩
      ext v
      simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨hvQ, hvi⟩
        exact huniq_in_V i v hvQ u (mem_inter.mp hu).1 hvi (mem_inter.mp hu).2
      · rintro rfl; exact mem_inter.mp hu
    have hv_cl : ∀ u ∈ Q, ∃ i ∈ clSet Q, u ∈ V i := by
      intro u hu
      obtain ⟨i, hui⟩ := hv_in_V u hu
      exact ⟨i, mem_filter.mpr ⟨mem_univ i, ⟨u, mem_inter.mpr ⟨hu, hui⟩⟩⟩, hui⟩
    have hcard_eq : (clSet Q).card = Q.card := by
      symm
      refine Finset.card_bij (fun u hu ↦ (hv_cl u hu).choose) ?_ ?_ ?_
      · intro u hu; exact (hv_cl u hu).choose_spec.1
      · intro u₁ hu₁ u₂ hu₂ heq
        have h1 : u₁ ∈ V ((hv_cl u₁ hu₁).choose) := (hv_cl u₁ hu₁).choose_spec.2
        have h2 : u₂ ∈ V ((hv_cl u₁ hu₁).choose) := heq ▸ (hv_cl u₂ hu₂).choose_spec.2
        exact huniq_in_V _ u₁ hu₁ u₂ hu₂ h1 h2
      · intro i hi
        obtain ⟨u, hu⟩ := (mem_filter.mp hi).2
        have huQ : u ∈ Q := (mem_inter.mp hu).1
        have hui : u ∈ V i := (mem_inter.mp hu).2
        refine ⟨u, huQ, ?_⟩
        by_contra hne
        exact Finset.disjoint_left.mp (hV_disj _ i hne) (hv_cl u huQ).choose_spec.2 hui
    have hreg_pairs : ∀ i ∈ clSet Q, ∀ j ∈ clSet Q, i ≠ j → s(i, j) ∈ E_reg := by
      intro i hi j hj hij
      obtain ⟨u, hu⟩ := (mem_filter.mp hi).2
      obtain ⟨v, hv⟩ := (mem_filter.mp hj).2
      have huQ : u ∈ Q := (mem_inter.mp hu).1
      have hui : u ∈ V i := (mem_inter.mp hu).2
      have hvQ : v ∈ Q := (mem_inter.mp hv).1
      have hvj : v ∈ V j := (mem_inter.mp hv).2
      have huv : u ≠ v := fun heq ↦ Finset.disjoint_left.mp (hV_disj i j hij) hui (heq ▸ hvj)
      have hgood := hQedge_good s(u, v) (mem_edgeFinset.mpr (hQ_cl huQ hvQ huv)) (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
      obtain ⟨a, b, hab_reg, x, hxa, y, hyb, heq⟩ := (mem_filter.mp hgood).2
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hia : i = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i a h) hui hxa
        have hjb : j = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj j b h) hvj hyb
        rwa [hia, hjb]
      · have hib : i = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i b h) hui hyb
        have hja : j = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj j a h) hvj hxa
        rw [hib, hja, Sym2.eq_swap]; exact hab_reg
    refine ⟨mem_filter.mpr ⟨mem_univ _, hcard_eq ▸ hQ_lo, hcard_eq ▸ hQ_hi, hreg_pairs⟩,
      hcard_eq, hcard_one, hv_cl⟩
  -- Bound weight lost by dropping `𝒬3 \ 𝒬_good`.
  have hdrop_bad :
      ∑ Q ∈ 𝒬3 \ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q ≤
        (L : ℝ) ^ 2 * (E_bad.card : ℝ) := by
    have hstep1 : ∑ Q ∈ 𝒬3 \ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q ≤
        (L : ℝ) ^ 2 * ∑ Q ∈ 𝒬3 \ 𝒬_good, w Q := by
      rw [mul_sum]
      refine sum_le_sum fun Q hQ ↦ ?_
      have hQ3 : Q ∈ 𝒬3 := (mem_sdiff.mp hQ).1
      have hQL : Q.card ≤ L := (mem_filter.mp hQ3).2.2.1
      have hch : (Q.card.choose 2 : ℝ) - 1 ≤ (L : ℝ) ^ 2 := by
        have h1 : Q.card.choose 2 ≤ Q.card * Q.card := by
          rw [Nat.choose_two_right]
          exact Nat.div_le_self _ 2 |>.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ 1))
        have h2 : Q.card * Q.card ≤ L * L := Nat.mul_le_mul hQL hQL
        have h3 : (Q.card.choose 2 : ℝ) ≤ (L : ℝ) ^ 2 := by
          have : (Q.card.choose 2 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
            exact_mod_cast h1.trans h2
          push_cast at this; linarith
        linarith
      exact mul_le_mul_of_nonneg_right hch (hw_nonneg Q)
    have hstep2 : ∑ Q ∈ 𝒬3 \ 𝒬_good, w Q ≤ (E_bad.card : ℝ) := by
      have hhas_bad : ∀ Q ∈ 𝒬3 \ 𝒬_good,
          ∃ e ∈ E_bad, ∀ x ∈ e, x ∈ Q := by
        intro Q hQ
        obtain ⟨hQ3, hnot⟩ := mem_sdiff.mp hQ
        simp only [𝒬_good, mem_filter, hQ3, true_and, not_forall] at hnot
        obtain ⟨e, heG, heQ, hnotg⟩ := hnot
        exact ⟨e, mem_sdiff.mpr ⟨heG, hnotg⟩, heQ⟩
      calc ∑ Q ∈ 𝒬3 \ 𝒬_good, w Q
          ≤ ∑ Q ∈ 𝒬3 \ 𝒬_good, ∑ e ∈ E_bad, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := by
            refine sum_le_sum fun Q hQ ↦ ?_
            obtain ⟨e₀, he₀, he₀Q⟩ := hhas_bad Q hQ
            calc w Q = (if (∀ x ∈ e₀, x ∈ Q) then w Q else 0) := (if_pos he₀Q).symm
              _ ≤ ∑ e ∈ E_bad, if (∀ x ∈ e, x ∈ Q) then w Q else 0 :=
                single_le_sum (f := fun e ↦ if (∀ x ∈ e, x ∈ Q) then w Q else 0)
                  (fun e _ ↦ by split_ifs <;> [exact hw_nonneg Q; exact le_rfl]) he₀
        _ = ∑ e ∈ E_bad, ∑ Q ∈ 𝒬3 \ 𝒬_good, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := Finset.sum_comm
        _ ≤ ∑ e ∈ E_bad, (1 : ℝ) := by
            refine sum_le_sum fun e he ↦ ?_
            rw [← Finset.sum_filter]
            have hsub : (𝒬3 \ 𝒬_good).filter (fun Q ↦ ∀ x ∈ e, x ∈ Q) ⊆
                Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧
                  G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q) := by
              intro Q hQ
              obtain ⟨hQs, heQ⟩ := mem_filter.mp hQ
              have hQ3 := (mem_sdiff.mp hQs).1
              simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3 ⊢
              exact ⟨hQ3.1, hQ3.2.1, hQ3.2.2, heQ⟩
            exact (sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ ↦ hw_nonneg Q)).trans
              (hw_edge e (mem_sdiff.mp he).1)
        _ = (E_bad.card : ℝ) := by simp
    exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hL2_pos.le)
  -- Define aggregated cluster weights `α₀ : { T // T ∈ 𝒯 } → ℝ`.
  let α₀ : { T // T ∈ 𝒯 } → ℝ := fun T ↦
    (1 / (m : ℝ) ^ 2) * ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1), w Q
  have hα₀_nonneg : ∀ T, 0 ≤ α₀ T := fun T ↦
    mul_nonneg (by positivity) (sum_nonneg fun Q _ ↦ hw_nonneg Q)
  -- For each `e ∈ E_reg`, pick canonical endpoints `ep1 e, ep2 e : Fin k`.
  have hep_ex : ∀ e ∈ E_reg, ∃ i j : Fin k, i ≠ j ∧ e = s(i, j) := by
    intro e he
    induction e using Sym2.ind with
    | h i j => exact ⟨i, j, ((hE_reg_mem i j).mp he).1, rfl⟩
  let ep1 : { e // e ∈ E_reg } → Fin k := fun e ↦ (hep_ex e.1 e.2).choose
  let ep2 : { e // e ∈ E_reg } → Fin k := fun e ↦ (hep_ex e.1 e.2).choose_spec.choose
  have hep_ne : ∀ e : { e // e ∈ E_reg }, ep1 e ≠ ep2 e :=
    fun e ↦ (hep_ex e.1 e.2).choose_spec.choose_spec.1
  have hep_eq : ∀ e : { e // e ∈ E_reg }, e.1 = s(ep1 e, ep2 e) :=
    fun e ↦ (hep_ex e.1 e.2).choose_spec.choose_spec.2
  -- Incidence matrix `A`, RHS `b`, objective `c` for cluster LP.
  let A : { e // e ∈ E_reg } → { T // T ∈ 𝒯 } → ℝ :=
    fun e T ↦ if (∀ i ∈ e.1, i ∈ T.1) then 1 else 0
  let b : { e // e ∈ E_reg } → ℝ :=
    fun e ↦ (G.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ)
  let c : { T // T ∈ 𝒯 } → ℝ :=
    fun T ↦ (T.1.card.choose 2 : ℝ) - 1
  -- Verify `α₀` satisfies the cluster edge capacity constraints.
  have hα₀_le : ∀ e : { e // e ∈ E_reg }, ∑ T : { T // T ∈ 𝒯 }, A e T * α₀ T ≤ b e := by
    intro e
    let i := ep1 e
    let j := ep2 e
    have hij : i ≠ j := hep_ne e
    have he_eq : e.1 = s(i, j) := hep_eq e
    have hcond : ∀ T : Finset (Fin k), (∀ x ∈ e.1, x ∈ T) ↔ (i ∈ T ∧ j ∈ T) := by
      intro T; rw [he_eq]
      exact ⟨fun h ↦ ⟨h i (Sym2.mem_mk_left i j), h j (Sym2.mem_mk_right i j)⟩,
        fun ⟨hi, hj⟩ x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩
    have hsum_lhs : ∑ T : { T // T ∈ 𝒯 }, A e T * α₀ T =
        (1 / (m : ℝ) ^ 2) * ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q), w Q := by
      have h1 : ∑ T : { T // T ∈ 𝒯 }, A e T * α₀ T =
          (1 / (m : ℝ) ^ 2) * ∑ T ∈ 𝒯.filter (fun T ↦ i ∈ T ∧ j ∈ T),
            ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T), w Q := by
        rw [mul_sum, Finset.sum_filter, ← Finset.sum_coe_sort 𝒯]
        refine sum_congr rfl fun T _ ↦ ?_
        simp only [A, hcond T.1, α₀]
        split_ifs <;> ring
      rw [h1]
      congr 1
      rw [← Finset.sum_biUnion]
      · congr 1
        ext Q
        simp only [mem_biUnion, mem_filter]
        constructor
        · rintro ⟨T, ⟨_, hiT, hjT⟩, hQg, rfl⟩; exact ⟨hQg, hiT, hjT⟩
        · rintro ⟨hQg, hiQ, hjQ⟩
          exact ⟨clSet Q, ⟨(hQgood_props Q hQg).1, hiQ, hjQ⟩, hQg, rfl⟩
      · intro T₁ _ T₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro Q h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    rw [hsum_lhs]
    -- Double count over `(u, v) ∈ G.interedges (V i) (V j)`.
    have hsum_inter : ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q), w Q ≤
        ((G.interedges (V i) (V j)).card : ℝ) := by
      have hpair_ex : ∀ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q),
          ∃ p ∈ G.interedges (V i) (V j), p.1 ∈ Q ∧ p.2 ∈ Q := by
        intro Q hQ
        obtain ⟨hQg, hiQ, hjQ⟩ := mem_filter.mp hQ
        obtain ⟨u, hu⟩ := (mem_filter.mp hiQ).2
        obtain ⟨v, hv⟩ := (mem_filter.mp hjQ).2
        have huQ : u ∈ Q := (mem_inter.mp hu).1
        have hui : u ∈ V i := (mem_inter.mp hu).2
        have hvQ : v ∈ Q := (mem_inter.mp hv).1
        have hvj : v ∈ V j := (mem_inter.mp hv).2
        have huv : u ≠ v := fun h ↦ Finset.disjoint_left.mp (hV_disj i j hij) hui (h ▸ hvj)
        have hQcl : G.IsClique (Q : Set (Fin n)) := (mem_filter.mp (mem_filter.mp hQg).1).2.2.2
        exact ⟨(u, v), (SimpleGraph.mem_interedges_iff G).mpr ⟨hui, hvj, hQcl huQ hvQ huv⟩, huQ, hvQ⟩
      calc ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q), w Q
          ≤ ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q),
              ∑ p ∈ G.interedges (V i) (V j), if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0 := by
            refine sum_le_sum fun Q hQ ↦ ?_
            obtain ⟨p₀, hp₀, hp₀Q⟩ := hpair_ex Q hQ
            calc w Q = (if (p₀.1 ∈ Q ∧ p₀.2 ∈ Q) then w Q else 0) := (if_pos hp₀Q).symm
              _ ≤ ∑ p ∈ G.interedges (V i) (V j), if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0 :=
                single_le_sum (f := fun p ↦ if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0)
                  (fun p _ ↦ by split_ifs <;> [exact hw_nonneg Q; exact le_rfl]) hp₀
        _ = ∑ p ∈ G.interedges (V i) (V j),
              ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q),
                if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0 := Finset.sum_comm
        _ ≤ ∑ p ∈ G.interedges (V i) (V j), (1 : ℝ) := by
            refine sum_le_sum fun p hp ↦ ?_
            rw [← Finset.sum_filter]
            have hadj : G.Adj p.1 p.2 := ((SimpleGraph.mem_interedges_iff G).mp hp).2.2
            have hsub : (𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q)).filter
                (fun Q ↦ p.1 ∈ Q ∧ p.2 ∈ Q) ⊆
                Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧
                  G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ s(p.1, p.2), x ∈ Q) := by
              intro Q hQ
              obtain ⟨hQ1, hp1, hp2⟩ := mem_filter.mp hQ
              have hQ3 := (mem_filter.mp (mem_filter.mp hQ1).1).1
              simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3 ⊢
              refine ⟨hQ3.1, hQ3.2.1, hQ3.2.2, fun x hx ↦ ?_⟩
              rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
            exact (sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ ↦ hw_nonneg Q)).trans
              (hw_edge s(p.1, p.2) (mem_edgeFinset.mpr hadj))
        _ = ((G.interedges (V i) (V j)).card : ℝ) := by simp
    have hbd : b e = (1 / (m : ℝ) ^ 2) * ((G.interedges (V i) (V j)).card : ℝ) := by
      simp only [b, i, j, SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges]
      push_cast
      rw [hV_card (ep1 e), hV_card (ep2 e)]
      ring
    rw [hbd]
    exact mul_le_mul_of_nonneg_left hsum_inter (by positivity)
  -- Every feasible `α` is bounded by `1` (since each `T ∈ 𝒯` has `T.card ≥ 3`, hence contains some `e ∈ E_reg`).
  have hbounded : ∀ x : { T // T ∈ 𝒯 } → ℝ,
      (∀ T, 0 ≤ x T) → (∀ e, ∑ T, A e T * x T ≤ b e) → ∀ T, x T ≤ 1 := by
    intro x hx_nn hx_le T
    have hT := (mem_filter.mp T.2).2
    have h2 : 2 ≤ T.1.card := by omega
    obtain ⟨a, ha, b', hb', hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.1.card)
    have he_mem : s(a, b') ∈ E_reg := hT.2.2 a ha b' hb' hab
    let e : { e // e ∈ E_reg } := ⟨s(a, b'), he_mem⟩
    have hAeT : A e T = 1 := by
      simp only [A, e]
      rw [if_pos]
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl <;> assumption
    have hbe_le : b e ≤ 1 := by
      have h1 : G.edgeDensity (V (ep1 e)) (V (ep2 e)) ≤ 1 :=
        SimpleGraph.edgeDensity_le_one G _ _
      change (G.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ) ≤ 1
      exact_mod_cast h1
    calc x T = A e T * x T := by rw [hAeT, one_mul]
      _ ≤ ∑ T' : { T // T ∈ 𝒯 }, A e T' * x T' :=
        single_le_sum (fun T' _ ↦ mul_nonneg (by simp only [A]; split_ifs <;> norm_num) (hx_nn T'))
          (mem_univ T)
      _ ≤ b e := hx_le e
      _ ≤ 1 := hbe_le
  -- Step 6: Apply Basic Feasible Solution support bound!
  obtain ⟨α_star, hα_nn, hα_le, hα_opt, hα_supp_card⟩ :=
    bfs_support_bound A b c 1 α₀ hα₀_nonneg hα₀_le hbounded
  -- Objective of `α₀` equals `𝒬_good` weight divided by `m^2`.
  have hα₀_obj : (∑ T : { T // T ∈ 𝒯 }, c T * α₀ T) * (m : ℝ) ^ 2 =
      ∑ Q ∈ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q := by
    rw [sum_mul]
    have h1 : ∑ T : { T // T ∈ 𝒯 }, c T * α₀ T * (m : ℝ) ^ 2 =
        ∑ T ∈ 𝒯, ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T),
          ((Q.card.choose 2 : ℝ) - 1) * w Q := by
      rw [← Finset.sum_coe_sort 𝒯]
      refine sum_congr rfl fun T _ ↦ ?_
      have hm2_ne : (m : ℝ) ^ 2 ≠ 0 := by positivity
      calc c T * α₀ T * (m : ℝ) ^ 2
          = c T * ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1), w Q := by
            simp only [α₀]; field_simp
        _ = ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1), c T * w Q := mul_sum _ _ _
        _ = ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1),
            ((Q.card.choose 2 : ℝ) - 1) * w Q := by
          refine sum_congr rfl fun Q hQ ↦ ?_
          have hQg : Q ∈ 𝒬_good := (mem_filter.mp hQ).1
          have hcl : clSet Q = T.1 := (mem_filter.mp hQ).2
          have hcard := (hQgood_props Q hQg).2.1
          simp only [c, ← hcl, hcard]
    rw [h1, ← Finset.sum_biUnion]
    · congr 1
      ext Q
      simp only [mem_biUnion, mem_filter]
      exact ⟨fun ⟨_, _, hQg, _⟩ ↦ hQg,
        fun hQg ↦ ⟨clSet Q, (hQgood_props Q hQg).1, hQg, rfl⟩⟩
    · intro T₁ _ T₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro Q h1 h2
      exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  -- Step 7: Drop small `α_star T < δ` to form `𝒯_big`.
  let 𝒯_big : Finset { T // T ∈ 𝒯 } := Finset.univ.filter (fun T ↦ δ ≤ α_star T)
  let supp_α : Finset { T // T ∈ 𝒯 } := Finset.univ.filter (fun T ↦ α_star T ≠ 0)
  have h𝒯_big_sub : 𝒯_big ⊆ supp_α := by
    intro T hT
    exact mem_filter.mpr ⟨mem_univ T, ne_of_gt (lt_of_lt_of_le hδ_pos (mem_filter.mp hT).2)⟩
  have hsupp_le_k2 : (supp_α.card : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h1 : (supp_α.card : ℝ) ≤ (Fintype.card { e // e ∈ E_reg } : ℝ) := by
      exact_mod_cast hα_supp_card
    rw [Fintype.card_coe] at h1
    exact h1.trans hE_reg_card
  have hc_le_L2 : ∀ T : { T // T ∈ 𝒯 }, c T ≤ (L : ℝ) ^ 2 := by
    intro T
    have hTL : T.1.card ≤ L := (mem_filter.mp T.2).2.2.1
    have h1 : T.1.card.choose 2 ≤ T.1.card * T.1.card := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ 1))
    have h2 : T.1.card * T.1.card ≤ L * L := Nat.mul_le_mul hTL hTL
    have h3 : (T.1.card.choose 2 : ℝ) ≤ (L : ℝ) ^ 2 := by
      have : (T.1.card.choose 2 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
      push_cast at this; linarith
    simp only [c]; linarith
  have hc_nonneg : ∀ T : { T // T ∈ 𝒯 }, 0 ≤ c T := by
    intro T
    have hT3 : 3 ≤ T.1.card := (mem_filter.mp T.2).2.1
    have h1 : 1 ≤ T.1.card.choose 2 := by
      rw [Nat.choose_two_right]
      have h32 : 3 * (3 - 1) ≤ T.1.card * (T.1.card - 1) := Nat.mul_le_mul hT3 (by omega)
      omega
    have h1r : (1 : ℝ) ≤ (T.1.card.choose 2 : ℝ) := by exact_mod_cast h1
    simp only [c]; linarith
  have hdrop_small :
      (∑ T : { T // T ∈ 𝒯 }, c T * α_star T - ∑ T ∈ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2 ≤
        (ζ / 32) * (n : ℝ) ^ 2 := by
    have hdiff : ∑ T : { T // T ∈ 𝒯 }, c T * α_star T - ∑ T ∈ 𝒯_big, c T * α_star T =
        ∑ T ∈ supp_α \ 𝒯_big, c T * α_star T := by
      have hsub1 : 𝒯_big ⊆ supp_α := h𝒯_big_sub
      have htot : ∑ T : { T // T ∈ 𝒯 }, c T * α_star T = ∑ T ∈ supp_α, c T * α_star T := by
        symm
        refine sum_subset (subset_univ supp_α) fun T _ hT ↦ ?_
        have h0 : α_star T = 0 := by
          by_contra hne; exact hT (mem_filter.mpr ⟨mem_univ T, hne⟩)
        simp [h0]
      rw [htot, ← Finset.sum_sdiff hsub1]
      ring
    rw [hdiff]
    have h1 : ∑ T ∈ supp_α \ 𝒯_big, c T * α_star T ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * δ) := by
      calc ∑ T ∈ supp_α \ 𝒯_big, c T * α_star T
          ≤ ∑ _T ∈ supp_α \ 𝒯_big, ((L : ℝ) ^ 2 * δ) := by
            refine sum_le_sum fun T hT ↦ ?_
            have hlt : α_star T < δ := by
              have hnot := (mem_sdiff.mp hT).2
              simp only [𝒯_big, mem_filter, mem_univ, true_and, not_le] at hnot
              exact hnot
            exact mul_le_mul (hc_le_L2 T) hlt.le (hα_nn T) hL2_pos.le
        _ = ((supp_α \ 𝒯_big).card : ℝ) * ((L : ℝ) ^ 2 * δ) := by simp
        _ ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * δ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card sdiff_subset) (by positivity)
    calc (∑ T ∈ supp_α \ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2
        ≤ ((supp_α.card : ℝ) * ((L : ℝ) ^ 2 * δ)) * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ (((k : ℝ) ^ 2 / 2) * ((L : ℝ) ^ 2 * δ)) * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsupp_le_k2 (by positivity)) (sq_nonneg _)
      _ = ((L : ℝ) ^ 2 * δ / 2) * ((k : ℝ) * (m : ℝ)) ^ 2 := by ring
      _ ≤ ((L : ℝ) ^ 2 * δ / 2) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg hk_real_pos.le hm_pos.le) hkm_le_n_real 2)
            (div_nonneg (mul_nonneg hL2_pos.le hδ_pos.le) (by norm_num))
      _ = (ζ / 32) * (n : ℝ) ^ 2 := by
          simp only [δ]; field_simp; ring
  -- Step 8: Apply `H1` on each regular cluster pair `e ∈ E_reg`.
  have hcol_ex : ∀ e : { e // e ∈ E_reg },
      ∃ col : Sym2 (Fin n) → Option (Finset (Fin k)),
        ∀ T ∈ 𝒯_big, (∀ x ∈ e.1, x ∈ T.1) →
          ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
            (∀ u v, H.Adj u v ↔ G.Adj u v ∧ col s(u, v) = some T.1) →
            H.IsUniform ε₁ (V (ep1 e)) (V (ep2 e)) ∧
            |(H.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ) - α_star T| ≤ ε₁ := by
    intro e
    let 𝒯_e : Finset { T // T ∈ 𝒯 } := 𝒯_big.filter (fun T ↦ ∀ x ∈ e.1, x ∈ T.1)
    let r : ℕ := 𝒯_e.card
    let equiv_e : 𝒯_e ≃ Fin r := 𝒯_e.equivFin
    let α_e : Fin r → ℝ := fun s ↦ α_star (equiv_e.symm s).1
    have hα_e_δ : ∀ s : Fin r, δ ≤ α_e s := fun s ↦
      (mem_filter.mp (mem_filter.mp (equiv_e.symm s).2).1).2
    have hα_e_sum : ∑ s : Fin r, α_e s ≤ (G.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ) := by
      have h1 : ∑ s : Fin r, α_e s = ∑ T ∈ 𝒯_e, α_star T := by
        rw [← Finset.sum_coe_sort 𝒯_e]
        exact Fintype.sum_equiv equiv_e.symm _ _ (fun _ ↦ rfl)
      rw [h1]
      calc ∑ T ∈ 𝒯_e, α_star T
          = ∑ T ∈ 𝒯_e, A e T * α_star T := by
            refine sum_congr rfl fun T hT ↦ ?_
            have hTe : ∀ x ∈ e.1, x ∈ T.1 := (mem_filter.mp hT).2
            simp only [A, if_pos hTe, one_mul]
        _ ≤ ∑ T : { T // T ∈ 𝒯 }, A e T * α_star T :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun T _ _ ↦
              mul_nonneg (by simp only [A]; split_ifs <;> norm_num) (hα_nn T)
        _ ≤ b e := hα_le e
    have he_unif : G.IsUniform ε_split (V (ep1 e)) (V (ep2 e)) :=
      hE_reg_unif_split (ep1 e) (ep2 e) (hep_eq e ▸ e.2)
    obtain ⟨col_raw, hcol_raw⟩ := hsplit n m hm_split G (V (ep1 e)) (V (ep2 e))
      (hV_disj (ep1 e) (ep2 e) (hep_ne e)) (hV_card (ep1 e)) (hV_card (ep2 e))
      he_unif r α_e hα_e_δ hα_e_sum
    refine ⟨fun f ↦ (col_raw f).map (fun s ↦ (equiv_e.symm s).1.1), ?_⟩
    intro T hT hTe H _ hH
    have hT_mem : T ∈ 𝒯_e := mem_filter.mpr ⟨hT, hTe⟩
    let s : Fin r := equiv_e ⟨T, hT_mem⟩
    have hs_eq : (equiv_e.symm s).1 = T := by simp [s]
    have hcol_iff : ∀ f : Sym2 (Fin n),
        (col_raw f).map (fun s' ↦ (equiv_e.symm s').1.1) = some T.1 ↔ col_raw f = some s := by
      intro f
      cases hc : col_raw f with
      | none => simp
      | some s' =>
        simp only [Option.map_some, Option.some.injEq]
        constructor
        · intro heq
          have h1 : (equiv_e.symm s').1 = (equiv_e.symm s).1 := Subtype.ext (heq.trans (by rw [hs_eq]))
          have h2 : equiv_e.symm s' = equiv_e.symm s := Subtype.ext h1
          exact equiv_e.symm.injective h2
        · rintro rfl; rw [hs_eq]
    have hH' : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ col_raw s(u, v) = some s := fun u v ↦ by
      rw [hH u v, hcol_iff s(u, v)]
    have hres := hcol_raw s H hH'
    simpa [α_e, hs_eq] using hres
  let owner : Sym2 (Fin k) → Sym2 (Fin n) → Option (Finset (Fin k)) :=
    fun e f ↦ if he : e ∈ E_reg then (hcol_ex ⟨e, he⟩).choose f else none
  -- Step 9: For each `T ∈ 𝒯_big`, apply `H2` to the color-`T` subgraph `G_T` to get `𝒬_T`.
  have hQT_ex : ∀ T ∈ 𝒯_big,
      ∃ 𝒬 : Finset (Finset (Fin n)),
        (∀ Q ∈ 𝒬, Q.card = T.1.card ∧ G.IsClique (Q : Set (Fin n)) ∧
          (∀ i ∈ T.1, (Q ∩ V i).card = 1) ∧
          (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v →
            ∃ i ∈ T.1, ∃ j ∈ T.1, i ≠ j ∧ u ∈ V i ∧ v ∈ V j ∧
              owner s(i, j) s(u, v) = some T.1)) ∧
        (∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
        (α_star T - η) * (m : ℝ) ^ 2 ≤ (𝒬.card : ℝ) := by
    intro T hT
    have hT_props := (mem_filter.mp T.2).2
    let q : ℕ := T.1.card
    have hq3 : 3 ≤ q := hT_props.1
    have hqL : q ≤ L := hT_props.2.1
    let τ : T.1 ≃ Fin q := T.1.equivFin
    let W : Fin q → Finset (Fin n) := fun a ↦ V (τ.symm a).1
    have hW_disj : ∀ a b : Fin q, a ≠ b → Disjoint (W a) (W b) := fun a b hab ↦
      hV_disj _ _ (fun h ↦ hab (τ.symm.injective (Subtype.ext h)))
    have hW_card : ∀ a : Fin q, (W a).card = m := fun a ↦ hV_card _
    -- Define the color-`T` subgraph `G_T` of `G`.
    let G_T : SimpleGraph (Fin n) :=
      { Adj := fun u v ↦ G.Adj u v ∧
          ∃ i ∈ T.1, ∃ j ∈ T.1, i ≠ j ∧ u ∈ V i ∧ v ∈ V j ∧
            owner s(i, j) s(u, v) = some T.1
        symm := ⟨fun u v ⟨hadj, i, hi, j, hj, hij, hui, hvj, hown⟩ ↦
          ⟨hadj.symm, j, hj, i, hi, hij.symm, hvj, hui, by
            rw [Sym2.eq_swap (a := j) (b := i), Sym2.eq_swap (a := v) (b := u)]
            exact hown⟩⟩
        loopless := ⟨fun u ⟨hadj, _⟩ ↦ hadj.ne rfl⟩ }
    have hGT_unif : ∀ a b : Fin q, a ≠ b →
        G_T.IsUniform ε₁ (W a) (W b) ∧
        |(G_T.edgeDensity (W a) (W b) : ℝ) - α_star T| ≤ ε₁ := by
      intro a b hab
      let i := (τ.symm a).1
      let j := (τ.symm b).1
      have hiT : i ∈ T.1 := (τ.symm a).2
      have hjT : j ∈ T.1 := (τ.symm b).2
      have hij : i ≠ j := fun h ↦ hab (τ.symm.injective (Subtype.ext h))
      have he_mem : s(i, j) ∈ E_reg := hT_props.2.2 i hiT j hjT hij
      let e : { e // e ∈ E_reg } := ⟨s(i, j), he_mem⟩
      let H_e : SimpleGraph (Fin n) :=
        { Adj := fun u v ↦ G.Adj u v ∧ (hcol_ex e).choose s(u, v) = some T.1
          symm := ⟨fun u v ⟨h, hc⟩ ↦ ⟨h.symm, by rwa [Sym2.eq_swap]⟩⟩
          loopless := ⟨fun u ⟨h, _⟩ ↦ h.ne rfl⟩ }
      have hHe_spec := (hcol_ex e).choose_spec T hT (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption) H_e (fun _ _ ↦ Iff.rfl)
      -- Match `(ep1 e, ep2 e)` with `(i, j)` (up to symmetry).
      have hHe_ij : H_e.IsUniform ε₁ (V i) (V j) ∧
          |(H_e.edgeDensity (V i) (V j) : ℝ) - α_star T| ≤ ε₁ := by
        rcases Sym2.eq_iff.mp (hep_eq e) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
          exact hHe_spec
        · rw [h1, h2]
          exact ⟨hHe_spec.1.symm, by rw [SimpleGraph.edgeDensity_comm]; exact hHe_spec.2⟩
      -- On `V i × V j`, `G_T.Adj` agrees with `H_e.Adj`.
      have hcongr : ∀ u ∈ V i, ∀ v ∈ V j, G_T.Adj u v ↔ H_e.Adj u v := by
        intro u hui v hvj
        constructor
        · rintro ⟨hadj, i', _, j', _, _, hui', hvj', hown⟩
          have hii' : i = i' := by
            by_contra h; exact Finset.disjoint_left.mp (hV_disj i i' h) hui hui'
          have hjj' : j = j' := by
            by_contra h; exact Finset.disjoint_left.mp (hV_disj j j' h) hvj hvj'
          subst hii' hjj'
          refine ⟨hadj, ?_⟩
          simpa [owner, dif_pos he_mem, e] using hown
        · rintro ⟨hadj, hc⟩
          refine ⟨hadj, i, hiT, j, hjT, hij, hui, hvj, ?_⟩
          simpa [owner, dif_pos he_mem, e] using hc
      change G_T.IsUniform ε₁ (V i) (V j) ∧ |(G_T.edgeDensity (V i) (V j) : ℝ) - α_star T| ≤ ε₁
      rw [isUniform_congr_on G_T H_e hcongr, edgeDensity_congr_on G_T H_e hcongr]
      exact hHe_ij
    have hα_δ : δ ≤ α_star T := (mem_filter.mp hT).2
    have hα_1 : α_star T ≤ 1 := hbounded α_star hα_nn hα_le T
    obtain ⟨𝒬, hQ_cl, hQ_disj, hQ_card⟩ :=
      hpack q hq3 hqL n m hm_pack G_T W hW_disj hW_card (α_star T) hα_δ hα_1 hGT_unif
    refine ⟨𝒬, ?_, hQ_disj, hQ_card⟩
    intro Q hQ
    obtain ⟨hQc, hQ_GT_cl, hQ_trans⟩ := hQ_cl Q hQ
    refine ⟨hQc, fun u hu v hv huv ↦ (hQ_GT_cl hu hv huv).1, ?_, ?_⟩
    · intro i hiT
      simpa [W] using hQ_trans (τ ⟨i, hiT⟩)
    · intro u hu v hv huv
      exact (hQ_GT_cl hu hv huv).2
  -- Step 10: Assemble all packed cliques `𝒬_pack` and complete to a clique edge partition `P_out`.
  let 𝒬_of : { T // T ∈ 𝒯_big } → Finset (Finset (Fin n)) :=
    fun T ↦ (hQT_ex T.1 T.2).choose
  have hQof_spec : ∀ T : { T // T ∈ 𝒯_big },
      (∀ Q ∈ 𝒬_of T, Q.card = T.1.1.card ∧ G.IsClique (Q : Set (Fin n)) ∧
        (∀ i ∈ T.1.1, (Q ∩ V i).card = 1) ∧
        (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v →
          ∃ i ∈ T.1.1, ∃ j ∈ T.1.1, i ≠ j ∧ u ∈ V i ∧ v ∈ V j ∧
            owner s(i, j) s(u, v) = some T.1.1)) ∧
      (∀ Q₁ ∈ 𝒬_of T, ∀ Q₂ ∈ 𝒬_of T, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
      (α_star T.1 - η) * (m : ℝ) ^ 2 ≤ ((𝒬_of T).card : ℝ) :=
    fun T ↦ (hQT_ex T.1 T.2).choose_spec
  -- Cliques from different `T₁ ≠ T₂` cannot share an edge (and in particular are distinct!).
  have hcross_disj : ∀ T₁ T₂ : { T // T ∈ 𝒯_big }, ∀ Q₁ ∈ 𝒬_of T₁, ∀ Q₂ ∈ 𝒬_of T₂,
      ∀ u v : Fin n, u ≠ v → u ∈ Q₁ → v ∈ Q₁ → u ∈ Q₂ → v ∈ Q₂ → T₁ = T₂ := by
    intro T₁ T₂ Q₁ hQ₁ Q₂ hQ₂ u v huv hu₁ hv₁ hu₂ hv₂
    obtain ⟨i₁, _, j₁, _, _, hui₁, hvj₁, hown₁⟩ := (hQof_spec T₁).1 Q₁ hQ₁ |>.2.2.2 u hu₁ v hv₁ huv
    obtain ⟨i₂, _, j₂, _, _, hui₂, hvj₂, hown₂⟩ := (hQof_spec T₂).1 Q₂ hQ₂ |>.2.2.2 u hu₂ v hv₂ huv
    have hi : i₁ = i₂ := by
      by_contra h; exact Finset.disjoint_left.mp (hV_disj i₁ i₂ h) hui₁ hui₂
    have hj : j₁ = j₂ := by
      by_contra h; exact Finset.disjoint_left.mp (hV_disj j₁ j₂ h) hvj₁ hvj₂
    subst hi hj
    have heq : some T₁.1.1 = some T₂.1.1 := hown₁.symm.trans hown₂
    exact Subtype.ext (Subtype.ext (Option.some.inj heq))
  have hQof_pairwise_disj :
      Set.PairwiseDisjoint (Finset.univ : Finset { T // T ∈ 𝒯_big }) 𝒬_of := by
    intro T₁ _ T₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro Q hQ₁ hQ₂
    have hQcard : 3 ≤ Q.card := by
      rw [((hQof_spec T₁).1 Q hQ₁).1]
      exact (mem_filter.mp T₁.1.2).2.1
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
    exact hne (hcross_disj T₁ T₂ Q hQ₁ Q hQ₂ u v huv hu hv hu hv)
  let 𝒬_pack : Finset (Finset (Fin n)) := Finset.univ.biUnion 𝒬_of
  have hpack_clique : ∀ Q ∈ 𝒬_pack, 3 ≤ Q.card ∧ G.IsClique (Q : Set (Fin n)) := by
    intro Q hQ
    obtain ⟨T, _, hQT⟩ := mem_biUnion.mp hQ
    have hs := (hQof_spec T).1 Q hQT
    exact ⟨hs.1 ▸ (mem_filter.mp T.1.2).2.1, hs.2.1⟩
  have hpack_edge_uniq : ∀ Q₁ ∈ 𝒬_pack, ∀ Q₂ ∈ 𝒬_pack,
      ∀ u v : Fin n, u ≠ v → u ∈ Q₁ → v ∈ Q₁ → u ∈ Q₂ → v ∈ Q₂ → Q₁ = Q₂ := by
    intro Q₁ hQ₁ Q₂ hQ₂ u v huv hu₁ hv₁ hu₂ hv₂
    obtain ⟨T₁, _, hQT₁⟩ := mem_biUnion.mp hQ₁
    obtain ⟨T₂, _, hQT₂⟩ := mem_biUnion.mp hQ₂
    have hT : T₁ = T₂ := hcross_disj T₁ T₂ Q₁ hQT₁ Q₂ hQT₂ u v huv hu₁ hv₁ hu₂ hv₂
    subst hT
    by_contra hne
    have hle := (hQof_spec T₁).2.1 Q₁ hQT₁ Q₂ hQT₂ hne
    have hge : 2 ≤ (Q₁ ∩ Q₂).card := by
      have hsub : ({u, v} : Finset (Fin n)) ⊆ Q₁ ∩ Q₂ := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact mem_inter.mpr ⟨by assumption, by assumption⟩
      exact (card_pair huv).symm.le.trans (card_le_card hsub)
    omega
  -- Complete `𝒬_pack` with uncovered edges as `K_2`s.
  let E_cov : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e ↦ ∃ Q ∈ 𝒬_pack, ∀ x ∈ e, x ∈ Q)
  let P_rem : Finset (Finset (Fin n)) := (G.edgeFinset \ E_cov).image Sym2.toFinset
  let P_out : Finset (Finset (Fin n)) := 𝒬_pack ∪ P_rem
  -- Verify `G.IsCliqueEdgePartition P_out`.
  have hP_part : G.IsCliqueEdgePartition P_out := by
    constructor
    · intro Q hQ
      rcases mem_union.mp hQ with h1 | h2
      · obtain ⟨hc, hcl⟩ := hpack_clique Q h1
        exact ⟨by omega, hcl⟩
      · obtain ⟨e, he, rfl⟩ := mem_image.mp h2
        have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp (mem_sdiff.mp he).1
        induction e using Sym2.ind with
        | h a b =>
          rw [Sym2.toFinset_mk_eq, card_pair (G.ne_of_adj hadj), coe_pair]
          exact ⟨le_rfl, isClique_pair.mpr (fun _ ↦ hadj)⟩
    · intro a b hab
      by_cases hcov : s(a, b) ∈ E_cov
      · obtain ⟨Q, hQ, hQab⟩ := (mem_filter.mp hcov).2
        refine ⟨Q, ⟨mem_union_left _ hQ, hQab a (by simp), hQab b (by simp)⟩, ?_⟩
        rintro Q' ⟨hQ'P, haQ', hbQ'⟩
        rcases mem_union.mp hQ'P with h1 | h2
        · exact hpack_edge_uniq Q' h1 Q hQ a b hab.ne haQ' hbQ'
            (hQab a (by simp)) (hQab b (by simp))
        · obtain ⟨e, he, rfl⟩ := mem_image.mp h2
          have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hab.ne).mp
            ⟨Sym2.mem_toFinset.mp haQ', Sym2.mem_toFinset.mp hbQ'⟩
          exact absurd (heq ▸ hcov) (mem_sdiff.mp he).2
      · have hmem : s(a, b).toFinset ∈ P_rem :=
          mem_image.mpr ⟨s(a, b), mem_sdiff.mpr ⟨mem_edgeFinset.mpr hab, hcov⟩, rfl⟩
        refine ⟨s(a, b).toFinset, ⟨mem_union_right _ hmem, by simp, by simp⟩, ?_⟩
        rintro Q' ⟨hQ'P, haQ', hbQ'⟩
        rcases mem_union.mp hQ'P with h1 | h2
        · exfalso
          exact hcov (mem_filter.mpr ⟨mem_edgeFinset.mpr hab, Q', h1, fun x hx ↦ by
            rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩)
        · obtain ⟨e, _, rfl⟩ := mem_image.mp h2
          have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hab.ne).mp
            ⟨Sym2.mem_toFinset.mp haQ', Sym2.mem_toFinset.mp hbQ'⟩
          rw [heq]
  -- Count `E_cov.card = ∑ Q ∈ 𝒬_pack, Q.card.choose 2`.
  have hE_cov_card : E_cov.card = ∑ Q ∈ 𝒬_pack, Q.card.choose 2 := by
    have hbi : E_cov = 𝒬_pack.biUnion (fun Q ↦ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)) := by
      ext e
      simp only [E_cov, mem_filter, mem_biUnion]
      exact ⟨fun ⟨he, Q, hQ, hQe⟩ ↦ ⟨Q, hQ, he, hQe⟩,
        fun ⟨Q, hQ, he, hQe⟩ ↦ ⟨he, Q, hQ, hQe⟩⟩
    rw [hbi, Finset.card_biUnion]
    · exact sum_congr rfl fun Q hQ ↦ clique_edges_card G Q (hpack_clique Q hQ).2
    · intro Q₁ hQ₁ Q₂ hQ₂ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp (mem_filter.mp he₁).1
      induction e using Sym2.ind with
      | h u v =>
        exact hne (hpack_edge_uniq Q₁ hQ₁ Q₂ hQ₂ u v (G.ne_of_adj hadj)
          ((mem_filter.mp he₁).2 u (by simp)) ((mem_filter.mp he₁).2 v (by simp))
          ((mem_filter.mp he₂).2 u (by simp)) ((mem_filter.mp he₂).2 v (by simp)))
  -- Final cardinality bound on `P_out`!
  have hP_card_le : (P_out.card : ℝ) ≤
      (G.edgeFinset.card : ℝ) - ∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1) := by
    have h1 : P_out.card ≤ 𝒬_pack.card + P_rem.card := card_union_le _ _
    have h2 : P_rem.card ≤ (G.edgeFinset \ E_cov).card := card_image_le
    have h3 : (G.edgeFinset \ E_cov).card + E_cov.card = G.edgeFinset.card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    have h4 : P_out.card + E_cov.card ≤ G.edgeFinset.card + 𝒬_pack.card := by omega
    have h4r : (P_out.card : ℝ) + (E_cov.card : ℝ) ≤ (G.edgeFinset.card : ℝ) + (𝒬_pack.card : ℝ) := by
      exact_mod_cast h4
    have h5 : ∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1) =
        (E_cov.card : ℝ) - (𝒬_pack.card : ℝ) := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hE_cov_card]
      push_cast; rfl
    linarith
  -- Lower bound `∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1)`.
  have hpack_gain :
      ∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1) ≥
        (∑ T ∈ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2 - (ζ / 32) * (n : ℝ) ^ 2 := by
    rw [Finset.sum_biUnion hQof_pairwise_disj]
    have hterm : ∀ T : { T // T ∈ 𝒯_big },
        ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1) ≥
          c T.1 * (α_star T.1 - η) * (m : ℝ) ^ 2 := by
      intro T
      have heq : ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1) =
          c T.1 * ((𝒬_of T).card : ℝ) := by
        calc ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1)
            = ∑ _Q ∈ 𝒬_of T, c T.1 := by
              refine sum_congr rfl fun Q hQ ↦ ?_
              simp [c, ((hQof_spec T).1 Q hQ).1]
          _ = ((𝒬_of T).card : ℝ) * c T.1 := by simp
          _ = c T.1 * ((𝒬_of T).card : ℝ) := mul_comm _ _
      rw [heq, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hQof_spec T).2.2 (hc_nonneg T.1)
    have hsum1 : ∑ T : { T // T ∈ 𝒯_big }, ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1) ≥
        ∑ T ∈ 𝒯_big, c T * (α_star T - η) * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_coe_sort 𝒯_big]
      exact sum_le_sum fun T _ ↦ hterm T
    have hη_err : (∑ T ∈ 𝒯_big, c T * η) * (m : ℝ) ^ 2 ≤ (ζ / 32) * (n : ℝ) ^ 2 := by
      have h1 : ∑ T ∈ 𝒯_big, c T * η ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * η) := by
        calc ∑ T ∈ 𝒯_big, c T * η
            ≤ ∑ _T ∈ 𝒯_big, ((L : ℝ) ^ 2 * η) :=
              sum_le_sum fun T _ ↦ mul_le_mul_of_nonneg_right (hc_le_L2 T) hη_pos.le
          _ = (𝒯_big.card : ℝ) * ((L : ℝ) ^ 2 * η) := by simp
          _ ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * η) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card h𝒯_big_sub) (by positivity)
      calc (∑ T ∈ 𝒯_big, c T * η) * (m : ℝ) ^ 2
          ≤ ((supp_α.card : ℝ) * ((L : ℝ) ^ 2 * η)) * (m : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ (((k : ℝ) ^ 2 / 2) * ((L : ℝ) ^ 2 * η)) * (m : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsupp_le_k2 (by positivity)) (sq_nonneg _)
        _ = ((L : ℝ) ^ 2 * η / 2) * ((k : ℝ) * (m : ℝ)) ^ 2 := by ring
        _ ≤ ((L : ℝ) ^ 2 * η / 2) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkm_le_n_real 2)
              (by positivity)
        _ = (ζ / 32) * (n : ℝ) ^ 2 := by
            simp only [η]; field_simp; ring
    have halg : ∑ T ∈ 𝒯_big, c T * (α_star T - η) * (m : ℝ) ^ 2 =
        (∑ T ∈ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2 - (∑ T ∈ 𝒯_big, c T * η) * (m : ℝ) ^ 2 := by
      rw [sum_mul, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun T _ ↦ by ring
    linarith
  -- Combine all bounds!
  have h𝒬3_split : ∑ Q ∈ 𝒬3, ((Q.card.choose 2 : ℝ) - 1) * w Q =
      ∑ Q ∈ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q +
      ∑ Q ∈ 𝒬3 \ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q := by
    rw [add_comm, Finset.sum_sdiff (filter_subset _ _)]
  have hbad_L2 : (L : ℝ) ^ 2 * (E_bad.card : ℝ) ≤ (3 * ζ / 16) * (n : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hE_bad_card hL2_pos.le
    have h2 : (L : ℝ) ^ 2 * ((3 * ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2) =
        (3 * ζ / 16) * (n : ℝ) ^ 2 := by field_simp
    linarith
  have hα_opt_m2 : (∑ T : { T // T ∈ 𝒯 }, c T * α₀ T) * (m : ℝ) ^ 2 ≤
      (∑ T : { T // T ∈ 𝒯 }, c T * α_star T) * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hα_opt (sq_nonneg _)
  have hζ_pos_n2 : 0 ≤ ζ * (n : ℝ) ^ 2 := by positivity
  refine ⟨P_out, hP_part, ?_⟩
  linarith

end OMA.R_Erdos81_erdos_81_R1_H2_R1
