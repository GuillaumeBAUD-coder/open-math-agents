import FormalConjectures.ErdosProblems.«712»

-- Problem: Erdős Problem 712 — limit exists
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/712.lean:56 (declaration Erdos712.erdos_712.variants.limit_exists)
-- Credit: @ashnewmanjones (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Filter Topology Finset

namespace OMA.E712

open scoped Classical in
lemma mem_adm {n r : ℕ} {P : Finset (Finset (Fin n)) → Prop} {H : Finset (Finset (Fin n))} :
    H ∈ (((univ : Finset (Fin n)).powersetCard r).powerset.filter P) ↔
      H ⊆ (univ : Finset (Fin n)).powersetCard r ∧ P H := by
  rw [mem_filter, mem_powerset]

lemma le_extremal {n r : ℕ} {P : Finset (Finset (Fin n)) → Prop} (H : Finset (Finset (Fin n)))
    (h1 : H ⊆ (univ : Finset (Fin n)).powersetCard r) (h2 : P H) :
    H.card ≤ Hypergraph.extremalNumber n r P := by
  unfold Hypergraph.extremalNumber
  exact le_sup (f := Finset.card) (mem_adm.mpr ⟨h1, h2⟩)

lemma extremal_le {n r b : ℕ} {P : Finset (Finset (Fin n)) → Prop}
    (h : ∀ H : Finset (Finset (Fin n)), H ⊆ (univ : Finset (Fin n)).powersetCard r → P H →
      H.card ≤ b) :
    Hypergraph.extremalNumber n r P ≤ b := by
  unfold Hypergraph.extremalNumber
  exact Finset.sup_le fun H hH => h H (mem_adm.mp hH).1 (mem_adm.mp hH).2

-- An admissible family is a subfamily of the r-subsets, so ex(n) ≤ C(n, r).
lemma ex_le_choose (n r k : ℕ) : Hypergraph.cliqueExtremalNumber n r k ≤ n.choose r := by
  refine extremal_le fun H h1 _ => ?_
  calc H.card ≤ ((univ : Finset (Fin n)).powersetCard r).card := card_le_card h1
    _ = n.choose r := by simp

-- Deleting a vertex v of a K_k^r-free family on n+1 vertices leaves at most ex(n) edges.
lemma card_avoid_le (n r k : ℕ) (H : Finset (Finset (Fin (n + 1))))
    (hH : H ⊆ (univ : Finset (Fin (n + 1))).powersetCard r)
    (hK : ¬ H.ContainsCompleteHypergraph r k) (v : Fin (n + 1)) :
    (H.filter (fun e => v ∉ e)).card ≤ Hypergraph.cliqueExtremalNumber n r k := by
  classical
  let emb : Fin n ↪ Fin (n + 1) := v.succAboveEmb
  let G : Finset (Finset (Fin n)) :=
    ((univ : Finset (Fin n)).powersetCard r).filter (fun e => e.map emb ∈ H)
  have hsub : H.filter (fun e => v ∉ e) ⊆ G.image (fun u => u.map emb) := by
    intro e he
    rw [mem_filter] at he
    have hsub' : e ⊆ (univ : Finset (Fin n)).map emb := by
      intro x hx
      have hxv : x ≠ v := fun h => he.2 (h ▸ hx)
      obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hxv
      exact mem_map.mpr ⟨z, mem_univ _, hz⟩
    obtain ⟨u, -, rfl⟩ := subset_map_iff.mp hsub'
    rw [mem_image]
    refine ⟨u, ?_, rfl⟩
    have hc := (mem_powersetCard.mp (hH he.1)).2
    rw [card_map] at hc
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hc⟩, he.1⟩
  have hGK : ¬ G.ContainsCompleteHypergraph r k := by
    rintro ⟨S, hS, hSG⟩
    apply hK
    refine ⟨S.map emb, by rw [card_map, hS], ?_⟩
    intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨U, hU, rfl⟩ := subset_map_iff.mp hT.1
    have hUc : U.card = r := by
      have := hT.2
      rwa [card_map] at this
    exact (mem_filter.mp (hSG (mem_powersetCard.mpr ⟨hU, hUc⟩))).2
  have hGle : G.card ≤ Hypergraph.cliqueExtremalNumber n r k := by
    exact le_extremal G (filter_subset _ _) hGK
  calc _ ≤ (G.image (fun u => u.map emb)).card := card_le_card hsub
    _ ≤ G.card := card_image_le
    _ ≤ _ := hGle

-- Double counting over the deleted vertex: |H| (n + 1 - r) ≤ (n + 1) ex(n).
lemma double_count (n r k : ℕ) (H : Finset (Finset (Fin (n + 1))))
    (hH : H ⊆ (univ : Finset (Fin (n + 1))).powersetCard r)
    (hK : ¬ H.ContainsCompleteHypergraph r k) :
    H.card * (n + 1 - r) ≤ (n + 1) * Hypergraph.cliqueExtremalNumber n r k := by
  classical
  have hsum : ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card = H.card * (n + 1 - r) := by
    simp_rw [card_filter]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.sum_mul]
    refine sum_congr rfl fun e he => ?_
    have hc := (mem_powersetCard.mp (hH he)).2
    rw [← Finset.card_filter]
    have hfe : (univ.filter fun v : Fin (n + 1) => v ∉ e) = eᶜ := by
      ext; simp
    rw [hfe, card_compl, Fintype.card_fin, hc, one_mul]
  rw [← hsum]
  calc ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card
      ≤ ∑ _v : Fin (n + 1), Hypergraph.cliqueExtremalNumber n r k :=
        sum_le_sum fun v _ => card_avoid_le n r k H hH hK v
    _ = (n + 1) * Hypergraph.cliqueExtremalNumber n r k := by simp

lemma key (n r k : ℕ) (hn : r ≤ n) :
    Hypergraph.cliqueExtremalNumber (n + 1) r k * (n + 1 - r) ≤
      (n + 1) * Hypergraph.cliqueExtremalNumber n r k := by
  have hc : 0 < n + 1 - r := by omega
  rw [← Nat.le_div_iff_mul_le hc]
  refine extremal_le fun H h1 h2 => ?_
  rw [Nat.le_div_iff_mul_le hc]
  exact double_count n r k H h1 h2

-- The normalized extremal numbers are non-increasing from n = r on.
lemma step (n r k : ℕ) (hn : r ≤ n) :
    (Hypergraph.cliqueExtremalNumber (n + 1) r k : ℝ) / ((n + 1).choose r : ℕ) ≤
      (Hypergraph.cliqueExtremalNumber n r k : ℝ) / (n.choose r : ℕ) := by
  have hc : 0 < n + 1 - r := by omega
  have hCn : 0 < n.choose r := Nat.choose_pos hn
  have hCn1 : 0 < (n + 1).choose r := Nat.choose_pos (by omega)
  have hnat : Hypergraph.cliqueExtremalNumber (n + 1) r k * n.choose r ≤
      Hypergraph.cliqueExtremalNumber n r k * (n + 1).choose r := by
    have hk := key n r k hn
    have h1 : Hypergraph.cliqueExtremalNumber (n + 1) r k * n.choose r * (n + 1 - r) ≤
        Hypergraph.cliqueExtremalNumber n r k * (n + 1).choose r * (n + 1 - r) := by
      calc Hypergraph.cliqueExtremalNumber (n + 1) r k * n.choose r * (n + 1 - r)
          = (Hypergraph.cliqueExtremalNumber (n + 1) r k * (n + 1 - r)) * n.choose r := by ring
        _ ≤ ((n + 1) * Hypergraph.cliqueExtremalNumber n r k) * n.choose r :=
          Nat.mul_le_mul_right _ hk
        _ = Hypergraph.cliqueExtremalNumber n r k * (n.choose r * (n + 1)) := by ring
        _ = Hypergraph.cliqueExtremalNumber n r k * ((n + 1).choose r * (n + 1 - r)) := by
          rw [Nat.choose_mul_succ_eq]
        _ = Hypergraph.cliqueExtremalNumber n r k * (n + 1).choose r * (n + 1 - r) := by ring
    exact Nat.le_of_mul_le_mul_right h1 hc
  rw [div_le_div_iff₀ (by exact_mod_cast hCn1) (by exact_mod_cast hCn)]
  exact_mod_cast hnat

end OMA.E712

theorem OMA.solution : type_of% @Erdos712.erdos_712.variants.limit_exists := by
  intro r k
  let b : ℕ → ℝ := fun m =>
    (Hypergraph.cliqueExtremalNumber (m + r) r k : ℝ) / ((m + r).choose r : ℕ)
  have hb_anti : Antitone b := antitone_nat_of_succ_le fun m => by
    show (Hypergraph.cliqueExtremalNumber (m + 1 + r) r k : ℝ) / ((m + 1 + r).choose r : ℕ) ≤
      (Hypergraph.cliqueExtremalNumber (m + r) r k : ℝ) / ((m + r).choose r : ℕ)
    rw [show m + 1 + r = (m + r) + 1 by ring]
    exact OMA.E712.step (m + r) r k (by omega)
  have hb_nonneg : ∀ m, 0 ≤ b m := fun m => by positivity
  have hb_le : ∀ m, b m ≤ 1 := fun m => by
    show (Hypergraph.cliqueExtremalNumber (m + r) r k : ℝ) / ((m + r).choose r : ℕ) ≤ 1
    rw [div_le_one (by exact_mod_cast Nat.choose_pos (by omega))]
    exact_mod_cast OMA.E712.ex_le_choose _ r k
  have hbdd : BddBelow (Set.range b) := ⟨0, by rintro _ ⟨m, rfl⟩; exact hb_nonneg m⟩
  refine ⟨⨅ m, b m, ⟨le_ciInf hb_nonneg, (ciInf_le hbdd 0).trans (hb_le 0)⟩, ?_⟩
  rw [← tendsto_add_atTop_iff_nat r]
  exact tendsto_atTop_ciInf hb_anti hbdd
