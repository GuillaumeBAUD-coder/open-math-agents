import FormalConjectures.ErdosProblems.«556»

-- Reduction Erdos556.erdos_556.variants.luczak_asymptotic_even.R1 of Erdős Problem 556 — luczak asymptotic even
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Łuczak's asymptotic bound for even cycles via Szemerédi regularity and connected matchings

We reduce `Erdos556.erdos_556.variants.luczak_asymptotic_even` (`R(C_n; 3) ≤ (3 + ε)n` for large
even `n`) to two independent combinatorial pillars, while discharging the pigeonhole edge-counting
and Szemerédi regularity cluster-graph extraction directly inside this reduction:

* `H1`: Connected matching density lemma — any graph on `t` vertices with strictly more than
  `(k - 1) * t` edges contains a matching of size at least `k` inside a single connected
  component (Erdős–Gallai / Tutte–Berge).
* `H2`: Łuczak's blow-up / cycle-embedding lemma — a connected matching of `k` edges in an
  `η`-uniform, `d`-dense cluster graph with equipartite parts of size `m` embeds `C_n` for every
  even `4 ≤ n ≤ (1 - δ) * 2 * k * m` once `m` is sufficiently large relative to `(d, δ, t)`.
-/

namespace OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_even_R1

open Filter SimpleGraph Finset

/-- Connected matching density lemma: any graph on `t` vertices with strictly more than
`(k - 1) * t` edges contains a matching covering at least `2 * k` vertices within a single
connected component. -/
def H1 : Prop :=
  ∀ (t k : ℕ) (R : SimpleGraph (Fin t)) [DecidableRel R.Adj],
    1 ≤ k → (k - 1) * t < R.edgeFinset.card →
    ∃ M : R.Subgraph, M.IsMatching ∧ 2 * k ≤ M.verts.ncard ∧
      ∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v

/-- Łuczak's connected-matching blow-up lemma for even cycles: given density `d > 0` and slack
`δ ∈ (0, 1)`, there exists regularity parameter `η > 0` such that for any number of clusters `t`
and sufficiently large equipartite part size `m ≥ m₀`, any `η`-uniform `d`-dense cluster graph `R`
with a connected matching `M` covering at least `2 * k` clusters embeds `C_n` in `G` for all even
`4 ≤ n ≤ (1 - δ) * (2 * k * m)`. -/
def H2 : Prop :=
  ∀ (d δ : ℝ), 0 < d → 0 < δ → δ < 1 →
    ∃ η > (0 : ℝ), ∀ (t : ℕ), ∃ m₀ : ℕ,
      ∀ (N n m k : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t)) (M : R.Subgraph),
        Even n → 4 ≤ n → 1 ≤ k → m₀ ≤ m → (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) →
        Pairwise (fun i j => Disjoint (parts i) (parts j)) →
        (∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1) →
        (∀ u v : Fin t, R.Adj u v →
          G.IsUniform η (parts u) (parts v) ∧ (d : ℝ) ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) →
        M.IsMatching → 2 * k ≤ M.verts.ncard →
        (∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v) →
        (cycleGraph n).IsContained G

lemma dense_color_of_three_colouring (N : ℕ) (c : Fin 3 → SimpleGraph (Fin N))
    [∀ i, DecidableRel (c i).Adj]
    (hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c) :
    ∃ i : Fin 3, N * (N - 1) ≤ 6 * (c i).edgeFinset.card := by
  have hcov : (⊤ : SimpleGraph (Fin N)).edgeFinset ⊆
      (Finset.univ : Finset (Fin 3)).biUnion (fun i => (c i).edgeFinset) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet, top_adj] at he
      have hi : (⨆ i, c i).Adj x y := by rw [← hc.1]; exact (top_adj x y).mpr he
      rw [iSup_adj] at hi
      obtain ⟨i, hi⟩ := hi
      exact mem_biUnion.mpr ⟨i, mem_univ i, mem_edgeFinset.mpr hi⟩
  have hcard : (⊤ : SimpleGraph (Fin N)).edgeFinset.card ≤
      ∑ i : Fin 3, (c i).edgeFinset.card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have htop : (⊤ : SimpleGraph (Fin N)).edgeFinset.card = Nat.choose N 2 := by
    convert SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin N)
    simp
  have hchoose : 2 * Nat.choose N 2 = N * (N - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd
  rw [htop] at hcard
  have hsum : ∑ i : Fin 3, (c i).edgeFinset.card =
      (c 0).edgeFinset.card + (c 1).edgeFinset.card + (c 2).edgeFinset.card := by
    simp [Fin.sum_univ_three, add_assoc]
  have hmax : ∃ i : Fin 3, Nat.choose N 2 ≤ 3 * (c i).edgeFinset.card := by
    by_contra! h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  obtain ⟨i, hi⟩ := hmax
  exact ⟨i, by omega⟩

lemma regularity_cluster_graph (N : ℕ) (hN : 0 < N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : N * (N - 1) ≤ 6 * G.edgeFinset.card)
    (η d : ℝ) (hη : 0 < η) (hd : 0 ≤ d) (l : ℕ) (hl : l ≤ N) (hl_pos : 0 < l) :
    ∃ (t : ℕ) (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t))
      (_ : DecidableRel R.Adj),
      l ≤ t ∧ t ≤ SzemerediRegularity.bound η l ∧
      Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
      (∀ i : Fin t, N / t ≤ (parts i).card ∧ (parts i).card ≤ N / t + 1) ∧
      (∀ u v : Fin t, R.Adj u v →
        G.IsUniform η (parts u) (parts v) ∧ d ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) ∧
      (N : ℝ) * (N - 1) / 3 ≤
        (N : ℝ) * (N + t) / t + η * (N + t) ^ 2 + d * (N + t) ^ 2 +
          2 * (R.edgeFinset.card : ℝ) * ((N / t : ℕ) + 1 : ℝ) ^ 2 := by
  classical
  have hl_card : l ≤ Fintype.card (Fin N) := by simpa using hl
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G hη hl_card
  set t := P.parts.card
  have ht_pos : 0 < t := lt_of_lt_of_le hl_pos hP₂
  let e : Fin t ≃ P.parts := (Finset.equivFin P.parts).symm
  let parts : Fin t → Finset (Fin N) := fun i => (e i).1
  let R : SimpleGraph (Fin t) :=
    { Adj := fun u v => u ≠ v ∧ G.IsUniform η (parts u) (parts v) ∧
        d ≤ (G.edgeDensity (parts u) (parts v) : ℝ)
      symm := ⟨fun u v ⟨hne, hu, hd_uv⟩ =>
        ⟨hne.symm, hu.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩⟩
      loopless := ⟨fun u ⟨hne, _⟩ => hne rfl⟩ }
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  refine ⟨t, parts, R, inferInstance, hP₂, hP₃, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact P.disjoint (e i).2 (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  · intro i
    have hmem : parts i ∈ P.parts := (e i).2
    have h1 := hP₁.average_le_card_part hmem
    have h2 := hP₁.card_part_le_average_add_one hmem
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    exact ⟨h1, h2⟩
  · intro u v huv
    exact ⟨huv.2.1, huv.2.2⟩
  · have hA : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    let densePairs : Finset (Finset (Fin N) × Finset (Fin N)) :=
      P.parts.offDiag.filter (fun uv => G.IsUniform η uv.1 uv.2 ∧
        d ≤ (G.edgeDensity uv.1 uv.2 : ℝ))
    have hsub : (Finset.univ ×ˢ Finset.univ).filter (fun xy : Fin N × Fin N => G.Adj xy.1 xy.2) ⊆
        (P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2) ∪
          P.parts.biUnion Finset.offDiag ∪
          (P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2) ∪
          densePairs.biUnion (fun uv => G.interedges uv.1 uv.2) := by
      rintro ⟨x, y⟩ hxy
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hxy
      obtain ⟨U, hU, hx⟩ := P.exists_mem (Finset.mem_univ x)
      obtain ⟨V, hV, hy⟩ := P.exists_mem (Finset.mem_univ y)
      by_cases hUV : U = V
      · subst hUV
        refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        exact Finset.mem_biUnion.mpr ⟨U, hU, Finset.mem_offDiag.mpr ⟨hx, hy, G.ne_of_adj hxy⟩⟩
      · by_cases huni : G.IsUniform η U V
        · by_cases hd_uv : d ≤ (G.edgeDensity U V : ℝ)
          · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(U, V), ?_, ?_⟩)
            · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hU, hV, hUV⟩, huni, hd_uv⟩
            · exact G.mk_mem_interedges_iff.mpr ⟨hx, hy, hxy⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_biUnion.mpr ⟨(U, V), ?_, G.mk_mem_interedges_iff.mpr ⟨hx, hy, hxy⟩⟩
            exact (P.mk_mem_sparsePairs G U V d).mpr ⟨hU, hV, hUV, not_le.mp hd_uv⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
          refine Finset.mem_biUnion.mpr ⟨(U, V), ?_, Finset.mem_product.mpr ⟨hx, hy⟩⟩
          exact (P.mk_mem_nonUniforms G).mpr ⟨hU, hV, hUV, huni⟩
    have hcard_edges : 2 * G.edgeFinset.card ≤
        ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card +
        (P.parts.biUnion Finset.offDiag).card +
        ((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card +
        (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card := by
      have h2 := G.two_mul_card_edgeFinset
      rw [Finset.univ_product_univ] at hsub
      have hc := Finset.card_le_card hsub
      rw [← h2] at hc
      exact hc.trans (by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact Finset.card_union_le _ _)
    have h_dense_card : densePairs.card = 2 * R.edgeFinset.card := by
      have h2R := R.two_mul_card_edgeFinset
      rw [← Finset.univ_product_univ] at h2R
      rw [h2R]
      symm
      refine Finset.card_bij (fun uv _ => (parts uv.1, parts uv.2)) ?_ ?_ ?_
      · intro ⟨u, v⟩ huv
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at huv
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨(e u).2, (e v).2, ?_⟩, huv.2.1, huv.2.2⟩
        exact fun h => huv.1 (e.injective (Subtype.ext h))
      · intro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (e.injective (Subtype.ext heq.1)) (e.injective (Subtype.ext heq.2))
      · intro ⟨U, V⟩ hUV
        simp only [densePairs, Finset.mem_filter, Finset.mem_offDiag] at hUV
        obtain ⟨⟨hU, hV, hne⟩, huni, hd_uv⟩ := hUV
        refine ⟨(e.symm ⟨U, hU⟩, e.symm ⟨V, hV⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
          refine ⟨fun h => hne ?_, ?_, ?_⟩
          · exact congrArg Subtype.val (e.symm.injective h)
          · simpa [parts] using huni
          · simpa [parts] using hd_uv
        · simp [parts]
    have h_dense_inter : ((densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) ≤
        2 * (R.edgeFinset.card : ℝ) * ((N / t : ℕ) + 1 : ℝ) ^ 2 := by
      have h1 : (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card ≤
          ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card := Finset.card_biUnion_le
      have h2 : ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card ≤
          densePairs.card * (N / t + 1) ^ 2 := by
        calc ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card
            ≤ ∑ _uv ∈ densePairs, (N / t + 1) ^ 2 := by
              refine Finset.sum_le_sum fun uv huv => ?_
              have hmem := Finset.mem_offDiag.mp (Finset.mem_filter.mp huv).1
              have hu := hP₁.card_part_le_average_add_one hmem.1
              have hv := hP₁.card_part_le_average_add_one hmem.2.1
              simp only [Finset.card_univ, Fintype.card_fin] at hu hv
              rw [sq]
              exact (G.card_interedges_le_mul uv.1 uv.2).trans (Nat.mul_le_mul hu hv)
          _ = densePairs.card * (N / t + 1) ^ 2 := by simp
      have h3 : (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card ≤
          2 * R.edgeFinset.card * (N / t + 1) ^ 2 := by
        rw [← h_dense_card]
        exact h1.trans h2
      exact_mod_cast h3
    have h_nonuni : (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ) ≤
        η * ((N : ℝ) + t) ^ 2 := by
      have h1 : ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card ≤
          ∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card := by
        calc ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card
            ≤ ∑ uv ∈ P.nonUniforms G η, (uv.1 ×ˢ uv.2).card := Finset.card_biUnion_le
          _ = ∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card := by
              refine Finset.sum_congr rfl fun uv _ => Finset.card_product _ _
      have h2 := hP₁.sum_nonUniforms_lt' (𝕜 := ℝ) hA hη hP₄
      simp only [Finset.card_univ, Fintype.card_fin] at h2
      have h2le : (∑ uv ∈ P.nonUniforms G η, (#uv.1 : ℝ) * (#uv.2 : ℝ)) ≤ η * ((N : ℝ) + t) ^ 2 := by
        simpa [t] using h2.le
      calc (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ)
          ≤ ((∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card : ℕ) : ℝ) := Nat.cast_le.mpr h1
        _ = ∑ uv ∈ P.nonUniforms G η, (#uv.1 : ℝ) * (#uv.2 : ℝ) := by push_cast; rfl
        _ ≤ η * ((N : ℝ) + t) ^ 2 := h2le
    have h_off : ((P.parts.biUnion Finset.offDiag).card : ℝ) ≤ (N : ℝ) * ((N : ℝ) + t) / t := by
      have h := hP₁.card_biUnion_offDiag_le' (𝕜 := ℝ)
      simpa [t] using h
    have h_sparse : (((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) ≤
        d * ((N : ℝ) + t) ^ 2 := by
      have h := hP₁.card_interedges_sparsePairs_le' (G := G) (ε := d) hd
      simpa [t] using h
    have hG_real : (N : ℝ) * ((N : ℝ) - 1) / 3 ≤ 2 * (G.edgeFinset.card : ℝ) := by
      have hG' : (N : ℝ) * ((N : ℝ) - 1) ≤ 6 * (G.edgeFinset.card : ℝ) := by
        have hcast : ((N * (N - 1) : ℕ) : ℝ) ≤ ((6 * G.edgeFinset.card : ℕ) : ℝ) :=
          Nat.cast_le.mpr hG
        rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one] at hcast
        push_cast at hcast
        exact hcast
      linarith
    have hcard_real : 2 * (G.edgeFinset.card : ℝ) ≤
        (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ) +
        ((P.parts.biUnion Finset.offDiag).card : ℝ) +
        (((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) +
        ((densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) := by
      exact_mod_cast hcard_edges
    linarith

lemma cluster_edge_bound (ε' η d : ℝ) (N t k eR : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1)
    (hη_le : η ≤ ε' / 1000) (hd_le : d ≤ ε' / 1000)
    (ht_pos : 0 < t) (hN_pos : 0 < N)
    (ht_ge : 1000 / ε' ≤ (t : ℝ))
    (ht_leN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ))
    (hk_le : (k : ℝ) ≤ (t : ℝ) / (6 + ε' / 2))
    (hR_ineq : (N : ℝ) * ((N : ℝ) - 1) / 3 ≤
      (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) +
      η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 +
      2 * (eR : ℝ) * ((↑(N / t) : ℝ) + 1) ^ 2) :
    (k - 1) * t < eR := by
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_ge_inv : (10000 : ℝ) / ε' ≤ (N : ℝ) / (t : ℝ) := by
    rw [div_le_div_iff₀ hε' ht_real_pos]
    have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mp
      (by linarith : (t : ℝ) ≤ ε' * (N : ℝ) / 10000)
    linarith
  have h_one_le_Nt : (1 : ℝ) ≤ ε' / 10000 * ((N : ℝ) / (t : ℝ)) := by
    have h1 := (div_le_iff₀ hε').mp hN_ge_inv
    linarith
  have ht_ge1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
  have h_one_le_N : (1 : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
    have hNt1 : (N : ℝ) / (t : ℝ) ≤ (N : ℝ) := div_le_self hN_real_pos.le ht_ge1
    nlinarith
  have h_m_cast_le : (↑(N / t) : ℝ) ≤ (N : ℝ) / (t : ℝ) :=
    (le_div_iff₀ ht_real_pos).mpr (by exact_mod_cast Nat.div_mul_le_self N t)
  have h_N_add_t : (N : ℝ) + (t : ℝ) ≤ (1 + ε' / 10000) * (N : ℝ) := by linarith
  have h_N_sub_1 : (1 - ε' / 10000) * (N : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have h_m_add_1 : (↑(N / t) : ℝ) + 1 ≤ (1 + ε' / 10000) * ((N : ℝ) / (t : ℝ)) := by linarith
  have h_inv_t : (1 : ℝ) / (t : ℝ) ≤ ε' / 1000 := by
    rw [div_le_div_iff₀ ht_real_pos (by norm_num), one_mul]
    linarith only [(div_le_iff₀ hε').mp ht_ge]
  have hLHS : (1 - ε' / 10000) / 3 * (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 3 := by
    have hmul := mul_le_mul_of_nonneg_left h_N_sub_1 hN_real_pos.le
    linarith
  have h_off_term : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) ≤
      (ε' / 1000) * (1 + ε' / 10000) * (N : ℝ) ^ 2 := by
    have h1 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) =
        ((N : ℝ) * ((N : ℝ) + (t : ℝ))) * (1 / (t : ℝ)) := by ring
    rw [h1]
    have h2 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) ≤ (N : ℝ) * ((1 + ε' / 10000) * (N : ℝ)) := by
      gcongr
    calc ((N : ℝ) * ((N : ℝ) + (t : ℝ))) * (1 / (t : ℝ))
        ≤ ((N : ℝ) * ((1 + ε' / 10000) * (N : ℝ))) * (ε' / 1000) := by
          gcongr
      _ = (ε' / 1000) * (1 + ε' / 10000) * (N : ℝ) ^ 2 := by ring
  have h_sq_term : (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 ≤
      (ε' / 500) * (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 := by
    have hsq : ((N : ℝ) + (t : ℝ)) ^ 2 ≤ ((1 + ε' / 10000) * (N : ℝ)) ^ 2 := by gcongr
    have hhd : η + d ≤ ε' / 500 := by linarith
    calc (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2
        ≤ (ε' / 500) * ((1 + ε' / 10000) * (N : ℝ)) ^ 2 := by gcongr
      _ = (ε' / 500) * (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 := by ring
  have h_edge_term : 2 * (eR : ℝ) * ((↑(N / t) : ℝ) + 1) ^ 2 ≤
      2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) := by
    have hsq : ((↑(N / t) : ℝ) + 1) ^ 2 ≤ ((1 + ε' / 10000) * ((N : ℝ) / (t : ℝ))) ^ 2 := by
      gcongr
    have hsq' : ((1 + ε' / 10000) * ((N : ℝ) / (t : ℝ))) ^ 2 =
        (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2 := by ring
    rw [← hsq']
    gcongr
  have hN2_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h_comb : (1 / 3 - 0.0034 * ε') * (N : ℝ) ^ 2 ≤
      2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) := by
    have h_num1 : (ε' / 1000) * (1 + ε' / 10000) ≤ 0.0011 * ε' := by nlinarith only [hε', hε'1]
    have hsq_bnd : (1 + ε' / 10000) ^ 2 ≤ 1.05 := by nlinarith only [hε', hε'1]
    have h_num2 : (ε' / 500) * (1 + ε' / 10000) ^ 2 ≤ 0.0021 * ε' := by
      nlinarith only [hε', hsq_bnd]
    have h_num3 : 1 / 3 - 0.0001 * ε' ≤ (1 - ε' / 10000) / 3 := by linarith
    have h1 : (1 / 3 - 0.0001 * ε') * (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 3 := by
      nlinarith only [h_num3, hLHS, hN2_pos]
    have h2 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) ≤ 0.0011 * ε' * (N : ℝ) ^ 2 := by
      nlinarith only [h_num1, h_off_term, hN2_pos]
    have h3 : (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 ≤ 0.0021 * ε' * (N : ℝ) ^ 2 := by
      nlinarith only [h_num2, h_sq_term, hN2_pos]
    have h3' : η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 ≤
        0.0021 * ε' * (N : ℝ) ^ 2 := by
      linarith only [h3, show (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 =
        η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 by ring]
    have h_epsN2 : 0 ≤ ε' * (N : ℝ) ^ 2 := by positivity
    linarith only [hR_ineq, h1, h2, h3', h_edge_term, h_epsN2]
  have h_divN : (1 / 3 - 0.0034 * ε') ≤
      2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 / (t : ℝ) ^ 2 := by
    have h_eq : 2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) =
        (2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 / (t : ℝ) ^ 2) * (N : ℝ) ^ 2 := by ring
    rw [h_eq] at h_comb
    exact le_of_mul_le_mul_right h_comb hN2_pos
  have h_mul_t : (1 / 3 - 0.0034 * ε') * (t : ℝ) ^ 2 ≤
      2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 :=
    (le_div_iff₀ (by positivity)).mp h_divN
  have h_k_le : ((k - 1 : ℕ) : ℝ) * (t : ℝ) ≤ (t : ℝ) ^ 2 / (6 + ε' / 2) := by
    have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    calc ((k - 1 : ℕ) : ℝ) * (t : ℝ)
        ≤ (k : ℝ) * (t : ℝ) := by gcongr
      _ ≤ ((t : ℝ) / (6 + ε' / 2)) * (t : ℝ) := by gcongr
      _ = (t : ℝ) ^ 2 / (6 + ε' / 2) := by ring
  have h_strict : 2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 <
      (1 / 3 - 0.0034 * ε') * (t : ℝ) ^ 2 := by
    have h6 : 0 < 6 + ε' / 2 := by linarith
    have ht2 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
    suffices hcoef : 2 * (1 + ε' / 10000) ^ 2 < (1 / 3 - 0.0034 * ε') * (6 + ε' / 2) by
      have hmul : 2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 =
          (2 * (1 + ε' / 10000) ^ 2 / (6 + ε' / 2)) * (t : ℝ) ^ 2 := by ring
      rw [hmul]
      exact mul_lt_mul_of_pos_right ((div_lt_iff₀ h6).mpr hcoef) ht2
    nlinarith only [hε', hε'1]
  have h_final_real : ((k - 1 : ℕ) : ℝ) * (t : ℝ) < (eR : ℝ) := by
    have hpos_c : (0 : ℝ) < 2 * (1 + ε' / 10000) ^ 2 := by positivity
    have h1 : 2 * (((k - 1 : ℕ) : ℝ) * (t : ℝ)) * (1 + ε' / 10000) ^ 2 ≤
        2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 := by
      gcongr
    have h2 : 2 * (((k - 1 : ℕ) : ℝ) * (t : ℝ)) * (1 + ε' / 10000) ^ 2 <
        2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 := by
      linarith only [h1, h_strict, h_mul_t]
    nlinarith only [h2, hpos_c]
  exact_mod_cast h_final_real

lemma blowup_size_bound (ε' δ : ℝ) (N n t m k : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hδ : δ = ε' / 20)
    (ht_pos : 0 < t) (hn_pos : (0 : ℝ) < (n : ℝ))
    (ht_ge : 1000 / ε' ≤ (t : ℝ))
    (ht_leN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ))
    (hN_ge : (3 + ε') * (n : ℝ) - 1 < (N : ℝ))
    (h_n_big : 10000 / ε' ≤ 3 * (n : ℝ))
    (hk_gt : (t : ℝ) / (6 + ε' / 2) - 1 < (k : ℝ))
    (hm_gt : (N : ℝ) / (t : ℝ) - 1 < (m : ℝ)) :
    (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) := by
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have h_one_lt_tk : (1 : ℝ) < (ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) := by
    rw [div_mul_div_comm, lt_div_iff₀ (by positivity)]
    have h1 : (1000 : ℝ) ≤ ε' * (t : ℝ) := by linarith only [(div_le_iff₀ hε').mp ht_ge]
    linarith
  have hk_lower : (1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) < (k : ℝ) := by linarith
  have hN_ge_inv : (10000 : ℝ) / ε' ≤ (N : ℝ) / (t : ℝ) := by
    rw [div_le_div_iff₀ hε' ht_real_pos]
    have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mp
      (by linarith : (t : ℝ) ≤ ε' * (N : ℝ) / 10000)
    linarith
  have h_one_le_Nt : (1 : ℝ) ≤ ε' / 10000 * ((N : ℝ) / (t : ℝ)) := by
    have h1 := (div_le_iff₀ hε').mp hN_ge_inv
    linarith
  have hm_lower : (1 - ε' / 10000) * ((N : ℝ) / (t : ℝ)) < (m : ℝ) := by linarith
  have hN_lower : (3 + 0.99 * ε') * (n : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ 0.01 * ε' * (n : ℝ) := by
      have h2 := (div_le_iff₀ hε').mp h_n_big
      linarith
    linarith
  have hm_lower2 : (1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)) ≤ (m : ℝ) := by
    have h1 : (3 + 0.99 * ε') * (n : ℝ) / (t : ℝ) ≤ (N : ℝ) / (t : ℝ) := by gcongr
    have h2 : 0 ≤ (1 - ε' / 10000) := by linarith
    nlinarith only [h1, h2, hm_lower]
  have h_prod : (1 - ε' / 20) * (2 * ((1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2))) *
      ((1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)))) ≤
      (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) := by
    rw [hδ]
    have hk0 : 0 ≤ (1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) :=
      mul_nonneg (by linarith) (by positivity)
    have hm0 : 0 ≤ (1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)) :=
      mul_nonneg (by linarith) (by positivity)
    have hd0 : 0 ≤ 1 - ε' / 20 := by linarith
    gcongr
  have h_simp : (1 - ε' / 20) * (2 * ((1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2))) *
      ((1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)))) =
      (2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) * (3 + 0.99 * ε') / (6 + ε' / 2)) *
        (n : ℝ) := by
    field_simp
  have h_ge_one : (1 : ℝ) ≤ 2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) *
      (3 + 0.99 * ε') / (6 + ε' / 2) := by
    rw [le_div_iff₀ (by linarith)]
    have hp1 : 1 - 0.061 * ε' ≤ (1 - ε' / 20) * (1 - ε' / 100) := by nlinarith only [hε', hε'1]
    have hp2 : 1 - 0.062 * ε' ≤ (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) := by
      nlinarith only [hε', hε'1, hp1]
    have hp3 : 6 + ε' / 2 ≤ 2 * (1 - 0.062 * ε') * (3 + 0.99 * ε') := by
      nlinarith only [hε', hε'1]
    have hp4 : 2 * (1 - 0.062 * ε') * (3 + 0.99 * ε') ≤
        2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) * (3 + 0.99 * ε') := by
      nlinarith only [hε', hε'1, hp2]
    linarith only [hp3, hp4]
  have h_n_prod : (n : ℝ) ≤ (2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) *
      (3 + 0.99 * ε') / (6 + ε' / 2)) * (n : ℝ) := by
    nlinarith only [h_ge_one, hn_pos]
  linarith only [h_prod, h_simp, h_n_prod]

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.luczak_asymptotic_even := by
  intro h1 h2 ε hε
  classical
  set ε' : ℝ := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  have hε'1 : ε' ≤ 1 := min_le_right ε 1
  have hε'ε : ε' ≤ ε := min_le_left ε 1
  set d : ℝ := ε' / 1000
  set δ : ℝ := ε' / 20
  have hd : 0 < d := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨η₀, hη₀, hm₀_all⟩ := h2 d δ hd hδ0 hδ1
  set η : ℝ := min η₀ (ε' / 1000)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hη_le0 : η ≤ η₀ := min_le_left _ _
  have hη_le : η ≤ ε' / 1000 := min_le_right _ _
  set l : ℕ := Nat.ceil (1000 / ε')
  have hl_real : 1000 / ε' ≤ (l : ℝ) := Nat.le_ceil _
  have hl_ge : 1000 ≤ l := by
    have : (1000 : ℝ) ≤ 1000 / ε' := by rw [le_div_iff₀ hε']; nlinarith
    exact_mod_cast this.trans hl_real
  have hl_pos : 0 < l := by omega
  obtain ⟨M_bound, hM_eq⟩ : ∃ M, M = SzemerediRegularity.bound η l := ⟨_, rfl⟩
  have hM_pos : 0 < M_bound := hM_eq ▸ SzemerediRegularity.bound_pos η l
  have hl_le_M : l ≤ M_bound := hM_eq ▸ SzemerediRegularity.le_bound η l
  obtain ⟨m_req, hm_req_eq⟩ : ∃ mr, mr = (Finset.range (M_bound + 1)).sup (fun t => (hm₀_all t).choose) :=
    ⟨_, rfl⟩
  obtain ⟨N₀, hN₀_eq⟩ : ∃ n0, n0 = Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) + 4 :=
    ⟨_, rfl⟩
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn heven => ?_⟩
  have hN₀_ge4 : 4 ≤ N₀ := by rw [hN₀_eq]; exact Nat.le_add_left 4 _
  have hn4 : 4 ≤ n := hN₀_ge4.trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨N, hN_eq⟩ : ∃ N, N = Nat.floor ((3 + ε') * (n : ℝ)) := ⟨_, rfl⟩
  have hN_le : (N : ℝ) ≤ (3 + ε') * (n : ℝ) := hN_eq ▸ Nat.floor_le (by positivity)
  have hN_gt : (3 + ε') * (n : ℝ) - 1 < (N : ℝ) := hN_eq ▸ Nat.sub_one_lt_floor _
  have hn_bound : (10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3 ≤ (n : ℝ) := by
    have h1n : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2n : (10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3 ≤
        (Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) : ℝ) :=
      Nat.le_ceil _
    have h3n : ((Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) : ℕ) : ℝ) ≤ (N₀ : ℝ) := by
      rw [hN₀_eq]; exact_mod_cast Nat.le_add_right _ 4
    linarith
  have hN_big : 10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 99 ≤ (N : ℝ) := by
    have h3n : (3 + ε') * (n : ℝ) - 1 ≥ 3 * (n : ℝ) - 1 := by nlinarith
    linarith
  have hN_pos : 0 < N := by
    have : (1 : ℝ) ≤ (N : ℝ) := by
      have : (0 : ℝ) < 10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound := by positivity
      linarith
    exact_mod_cast this
  have hRamsey_le : multicolourRamsey (cycleGraph n) 3 ≤ N := by
    apply Nat.sInf_le
    intro c hc
    obtain ⟨ic, hic⟩ := dense_color_of_three_colouring N c hc
    let G := c ic
    have hlN : l ≤ N := by
      have h1 : (l : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast hl_le_M
      have h2 : (M_bound : ℝ) ≤ 10000 * (M_bound : ℝ) / ε' := by
        rw [le_div_iff₀ hε']; nlinarith only [hε', hε'1]
      have h3 : (10000 * (M_bound : ℝ) / ε' : ℝ) ≤ (N : ℝ) := by
        linarith [show (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 99 by positivity]
      exact Nat.cast_le.mp (h1.trans (h2.trans h3))
    obtain ⟨t, parts, R, _, htl, htM, hdisj, hparts_card, hR_prop, hR_ineq⟩ :=
      regularity_cluster_graph N hN_pos G hic η d hη hd.le l hlN hl_pos
    rw [← hM_eq] at htM
    have ht_pos : 0 < t := lt_of_lt_of_le hl_pos htl
    have ht_ge_1000 : (1000 : ℝ) / ε' ≤ (t : ℝ) := hl_real.trans (by exact_mod_cast htl)
    have ht_1000 : (1000 : ℝ) ≤ (t : ℝ) := by
      have : (1000 : ℝ) ≤ 1000 / ε' := by rw [le_div_iff₀ hε']; nlinarith only [hε', hε'1]
      exact this.trans ht_ge_1000
    obtain ⟨m, hm_eq⟩ : ∃ m, m = N / t := ⟨_, rfl⟩
    obtain ⟨k, hk_eq⟩ : ∃ k, k = Nat.floor ((t : ℝ) / (6 + ε' / 2)) := ⟨_, rfl⟩
    have hk_pos_real : (1 : ℝ) ≤ (t : ℝ) / (6 + ε' / 2) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hk1 : 1 ≤ k := by rw [hk_eq]; exact Nat.le_floor (by simpa using hk_pos_real)
    have hm_ge : (hm₀_all t).choose ≤ m := by
      have hsup : (hm₀_all t).choose ≤ m_req := by
        rw [hm_req_eq]
        exact Finset.le_sup (f := fun s => (hm₀_all s).choose)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le htM))
      have hmul : m_req * t ≤ N := by
        have h1 : (m_req : ℝ) * (t : ℝ) ≤ (m_req : ℝ) * (M_bound : ℝ) := by gcongr
        have h2 : (m_req : ℝ) * (M_bound : ℝ) ≤ (N : ℝ) := by
          have : (0 : ℝ) ≤ 10000 * (M_bound : ℝ) / ε' + 99 := by positivity
          linarith
        exact_mod_cast h1.trans h2
      rw [hm_eq]
      exact hsup.trans ((Nat.le_div_iff_mul_le ht_pos).mpr hmul)
    have ht_le_epsN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
      have h1 : (t : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast htM
      have h2 : 10000 * (M_bound : ℝ) / ε' ≤ (N : ℝ) := by
        have : (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 99 := by positivity
        linarith
      have h3 : (M_bound : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
        rw [div_le_iff₀ hε'] at h2; linarith
      exact h1.trans h3
    have hk_le : (k : ℝ) ≤ (t : ℝ) / (6 + ε' / 2) := hk_eq ▸ Nat.floor_le (by positivity)
    have hR_gt : (k - 1) * t < R.edgeFinset.card :=
      cluster_edge_bound ε' η d N t k R.edgeFinset.card hε' hε'1 hη_le le_rfl
        ht_pos hN_pos ht_ge_1000 ht_le_epsN hk_le hR_ineq
    obtain ⟨M, hM_match, hM_card, hM_reach⟩ := h1 t k R hk1 hR_gt
    have hn_big3 : 10000 / ε' ≤ 3 * (n : ℝ) := by
      have hM1 : (1 : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast hM_pos
      have h1 : (10000 : ℝ) ≤ 10000 * (M_bound : ℝ) := by linarith
      have h1' : (10000 : ℝ) / ε' ≤ 10000 * (M_bound : ℝ) / ε' := div_le_div_of_nonneg_right h1 hε'.le
      have h2 : (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 100 := by positivity
      linarith
    have hk_gt : (t : ℝ) / (6 + ε' / 2) - 1 < (k : ℝ) := hk_eq ▸ Nat.sub_one_lt_floor _
    have hm_gt : (N : ℝ) / (t : ℝ) - 1 < (m : ℝ) := by
      rw [hm_eq, sub_lt_iff_lt_add, div_lt_iff₀ (by exact_mod_cast ht_pos)]
      calc (N : ℝ) < (↑(N / t * t + t) : ℝ) := by exact_mod_cast Nat.lt_div_mul_add ht_pos
        _ = (↑(N / t) + 1) * ↑t := by push_cast; ring
    have h_n_le : (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) :=
      blowup_size_bound ε' δ N n t m k hε' hε'1 rfl ht_pos hn_pos ht_ge_1000 ht_le_epsN
        hN_gt hn_big3 hk_gt hm_gt
    have hparts_card' : ∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1 := by
      rw [hm_eq]; exact hparts_card
    exact ⟨ic, (hm₀_all t).choose_spec N n m k G parts R M heven hn4 hk1 hm_ge h_n_le
      hdisj hparts_card' (fun u v huv => ⟨(hR_prop u v huv).1.mono hη_le0, (hR_prop u v huv).2⟩)
      hM_match hM_card hM_reach⟩
  have h_final : (multicolourRamsey (cycleGraph n) 3 : ℝ) ≤ (3 + ε) * (n : ℝ) := by
    calc (multicolourRamsey (cycleGraph n) 3 : ℝ)
        ≤ (N : ℝ) := by exact_mod_cast hRamsey_le
      _ ≤ (3 + ε') * (n : ℝ) := hN_le
      _ ≤ (3 + ε) * (n : ℝ) := by gcongr
  exact h_final

end OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_even_R1
