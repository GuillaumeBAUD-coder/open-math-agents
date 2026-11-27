import OMAReductions.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Data.Nat.Choose.Bounds

/-! Average the edge count of induced subgraphs of a fixed size near the Turán limit.
Each unlabelled forbidden copy contaminates only the samples containing its vertices. -/

open Filter SimpleGraph Finset
open scoped Classical Topology

private lemma incidence {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} (B : Finset β) (v : β → Finset α) (m k : ℕ) (hm : k ≤ m)
    (h : ∀ b ∈ B, (v b).card = k) :
    (∑ s ∈ (univ : Finset α).powersetCard m, (B.filter (fun b => v b ⊆ s)).card) =
      B.card * (Fintype.card α - k).choose (m-k) := by
  change (∑ s ∈ (univ : Finset α).powersetCard m, (B.bipartiteBelow (fun b s => v b ⊆ s) s).card) = _
  rw [← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun b s => v b ⊆ s)]
  have hterm (b : β) (hb : b ∈ B) :
      (((univ : Finset α).powersetCard m).bipartiteAbove (fun b s => v b ⊆ s) b).card =
      (Fintype.card α - k).choose (m-k) := by
    rw [bipartiteAbove, card_filter_powersetCard_subset _ _ _ (subset_univ _) (by simpa [h b hb] using hm),
      h b hb, card_univ]
  rw [sum_congr rfl hterm]
  simp

set_option maxHeartbeats 1000000 in
private lemma sample {k n m : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n))
    (hm : 2 ≤ m) (hk : k ≤ m) :
    G.edgeFinset.card * (n-2).choose (m-2) ≤
      n.choose m * extremalNumber m H +
        m.choose 2 * (G.copyCount H * (n-k).choose (m-k)) := by
  classical
  let B := (univ : Finset G.Subgraph).filter (fun D => Nonempty (H ≃g D.coe))
  let S := (univ : Finset (Fin n)).powersetCard m
  let v (D : G.Subgraph) := D.verts.toFinset
  have hcard : B.card = G.copyCount H := by
    unfold copyCount
    apply congrArg Finset.card
    ext D
    simp [B]
  have hv (D : G.Subgraph) (hD : D ∈ B) : (v D).card = k := by
    obtain ⟨e⟩ := (mem_filter.mp hD).2
    simpa [v] using (Fintype.card_congr e.toEquiv).symm
  have hlocal (s : Finset (Fin n)) (hs : s ∈ S) :
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card ≤ extremalNumber m H +
        m.choose 2 * (B.filter (fun D => v D ⊆ s)).card := by
    let T := G.induce (s : Set (Fin n))
    have hms : Fintype.card (↥(s : Set (Fin n))) = m := by
      simpa using (mem_powersetCard.mp hs).2
    have he : (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card = T.edgeFinset.card := by
      have h := congrArg Finset.card (G.map_edgeFinset_induce (s := (s : Set (Fin n))))
      simp only [card_map] at h
      convert! h.symm using 1
      · congr 1
        ext e
        simp only [mem_filter, mem_inter, mem_sym2_iff, Set.mem_toFinset, Finset.mem_coe]
        apply and_congr_right
        intro _
        change (∀ a ∈ e.toFinset, a ∈ s) ↔ _
        simp only [Sym2.mem_toFinset]
      · apply congrArg Finset.card
        ext e
        simp [T]
    rw [he]
    by_cases free : H.Free T
    · have h := card_edgeFinset_le_extremalNumber free
      rw [hms] at h
      omega
    · obtain ⟨f⟩ : H ⊑ T := by simpa [SimpleGraph.Free] using free
      let g := (Copy.induce G (s : Set (Fin n))).comp f
      have inside : v g.toSubgraph ⊆ s := by
        intro a ha
        obtain ⟨b, -, rfl⟩ := Set.mem_toFinset.mp ha
        exact (f b).property
      have hpos : 1 ≤ (B.filter (fun D => v D ⊆ s)).card := card_pos.mpr
        ⟨g.toSubgraph, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ⟨g.isoToSubgraph⟩⟩, inside⟩⟩
      have hu := T.card_edgeFinset_le_card_choose_two
      rw [hms] at hu
      exact hu.trans (Nat.le_add_left_of_le (by simpa using Nat.mul_le_mul_left (m.choose 2) hpos))
  have bound := sum_le_sum hlocal
  have ecount := incidence G.edgeFinset (fun e => e.toFinset) m 2 hm
    (fun e he => G.card_toFinset_mem_edgeFinset ⟨e,he⟩)
  have bcount := incidence B v m k hk hv
  simp only [Fintype.card_fin] at ecount bcount
  simpa only [S, ecount, sum_add_distrib, sum_const, card_powersetCard, card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ← mul_sum, bcount, hcard] using bound

private lemma normalize_sample {a b c u v w x y : ℝ} (hu : 0 < u) (hv : 0 < v)
    (_hw : 0 < w) (hx : 0 < x)
    (h : a * (u*v/w) ≤ u*b + v*(c*(u*y/x))) : a/w ≤ b/v + c*y/x := by
  apply le_of_mul_le_mul_left (a := u*v) ?_ (mul_pos hu hv)
  calc
    _ = a*(u*v/w) := by ring
    _ ≤ _ := h
    _ = _ := by field_simp

private lemma density_sample {k n m : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n))
    (hm : 2 ≤ m) (hk : k ≤ m) (hn : m ≤ n) :
    (G.edgeFinset.card : ℝ) / n.choose 2 ≤ (extremalNumber m H : ℝ) / m.choose 2 +
      (G.copyCount H : ℝ) * m.choose k / n.choose k := by
  have h := sample H G hm hk
  have c2 : (n.choose m : ℝ) * m.choose 2 = n.choose 2 * ((n-2).choose (m-2) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) hm
  have ck : (n.choose m : ℝ) * m.choose k = n.choose k * ((n-k).choose (m-k) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) hk
  have hn2 : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos (hm.trans hn)
  have hnk : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (hk.trans hn)
  have hnm : (0 : ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hn
  have hm2 : (0 : ℝ) < m.choose 2 := by exact_mod_cast Nat.choose_pos hm
  have heq : ((n-2).choose (m-2) : ℝ) = n.choose m * (m.choose 2 : ℝ) / n.choose 2 := by
    apply (eq_div_iff hn2.ne').mpr
    linarith
  have hkq : ((n-k).choose (m-k) : ℝ) = n.choose m * (m.choose k : ℝ) / n.choose k := by
    apply (eq_div_iff hnk.ne').mpr
    linarith
  have bound : (G.edgeFinset.card : ℝ) * ((n-2).choose (m-2) : ℝ) ≤
      (n.choose m : ℝ) * extremalNumber m H +
      m.choose 2 * ((G.copyCount H : ℝ) * ((n-k).choose (m-k) : ℝ)) := by exact_mod_cast h
  rw [heq,hkq] at bound
  exact normalize_sample hnm hm2 hn2 hnk bound

theorem OMA.solution : OMA.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1.H2 := by
  intro k H _ δ hδ
  obtain ⟨m, hm⟩ := eventually_atTop.mp ((tendsto_turanDensity H).eventually_lt_const
    (show turanDensity H < turanDensity H + δ/2 by linarith))
  let M := max (max k 2) m
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hMk : k ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  let D : ℝ := (2:ℝ)^k * k.factorial * M.choose k
  have hD : 0 < D := mul_pos (mul_pos (by positivity) (by exact_mod_cast Nat.factorial_pos k))
    (by exact_mod_cast Nat.choose_pos hMk)
  refine ⟨δ/2/D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max M (2*k))] with n hn
  intro G copies
  have hnM := (le_max_left M (2*k)).trans hn
  have hn2 : 2 ≤ n := hM2.trans hnM
  have hπ : turanDensity H ≤ (extremalNumber n H : ℝ)/n.choose 2 :=
    (isGLB_turanDensity H).1 ⟨n,hn2,rfl⟩
  have h1 := (hm M (le_max_right _ _)).le.trans (add_le_add_left hπ (δ/2))
  have twok := (le_max_right M (2*k)).trans hn
  have hN : n ≤ 2 * (n+1-k) := by omega
  have hc : (n:ℝ)^k ≤ (2:ℝ)^k * k.factorial * n.choose k := by
    exact_mod_cast (calc
      n^k ≤ (2*(n+1-k))^k := Nat.pow_le_pow_left hN k
      _ = 2^k * (n+1-k)^k := mul_pow _ _ _
      _ ≤ 2^k * (k.factorial * n.choose k) := Nat.mul_le_mul_left _ (by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact n.pow_sub_le_descFactorial k)
      _ = _ := by ring)
  have hnck : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (hMk.trans hnM)
  have factor : (G.copyCount H : ℝ) * M.choose k / n.choose k ≤ δ/2 := by
    apply (div_le_iff₀ hnck).mpr
    calc
      _ ≤ (δ/2/D) * ((2:ℝ)^k * k.factorial * n.choose k) * M.choose k :=
        mul_le_mul_of_nonneg_right (copies.trans (mul_le_mul_of_nonneg_left hc (by positivity))) (by positivity)
      _ = (δ/2/D * D) * n.choose k := by dsimp [D]; ring
      _ = _ := by rw [div_mul_cancel₀ _ hD.ne']
  have b := (density_sample H G hM2 hMk hnM).trans (add_le_add h1 factor)
  have hx : (0:ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn2
  have hraw : (G.edgeFinset.card : ℝ) / n.choose 2 ≤ (extremalNumber n H : ℝ) / n.choose 2 + δ := by
    linarith
  have hh := (div_le_iff₀ hx).mp hraw
  rw [add_mul, div_mul_cancel₀ _ hx.ne'] at hh
  have hc2 : (n.choose 2 : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast Nat.choose_le_pow n 2
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hc2 hδ.le) _)
