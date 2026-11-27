import FormalConjectures.ErdosProblems.«716»

-- Problem: Erdős Problem 716
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/716.lean:46 (declaration Erdos716.erdos_716)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Reference: Ruzsa and Szemerédi, Triple systems with no six points carrying three triangles (1978).

/-!
# Erdős Problem 716 (Ruzsa–Szemerédi (6,3) theorem)

Remove the edges that share two vertices with another edge (at most `2(n+1)` of them). The rest
form a linear family, whose shadow graph has exactly these edges as triangles, so its triangles
are edge-disjoint and number at most `n^2`. Mathlib's triangle removal lemma then bounds the
linear part by `ε n^2` for large `n`.
-/

open Filter Asymptotics Finset

namespace E716

variable {n : ℕ} {H : Finset (Finset (Fin n))}

lemma three_eq
    (hF : ∀ S : Finset (Fin n), S.card = 6 → #{e ∈ H | e ⊆ S} < 3) (hn : 6 ≤ n)
    {a b c : Finset (Fin n)} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (hT : (a ∪ b ∪ c).card ≤ 6) : a = b ∨ a = c ∨ b = c := by
  by_contra h
  push Not at h
  obtain ⟨hab, hac, hbc⟩ := h
  obtain ⟨S, hTS, hS⟩ := Finset.exists_superset_card_eq hT (by simpa using hn)
  have h3 : ({a, b, c} : Finset (Finset (Fin n))).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Finset (Finset (Fin n))) ⊆ {e ∈ H | e ⊆ S} := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rw [mem_filter]
    rcases he with rfl | rfl | rfl
    · exact ⟨ha, fun x hx => hTS (by simp [hx])⟩
    · exact ⟨hb, fun x hx => hTS (by simp [hx])⟩
    · exact ⟨hc, fun x hx => hTS (by simp [hx])⟩
  have := card_le_card hsub
  have := hF S hS
  omega

lemma card_union_le_of_mem {a b : Finset (Fin n)} {x : Fin n} (hxa : x ∈ a) (hxb : x ∈ b) :
    (a ∪ b).card + 1 ≤ a.card + b.card := by
  have h := card_union_add_card_inter a b
  have : 1 ≤ (a ∩ b).card := card_pos.mpr ⟨x, mem_inter.mpr ⟨hxa, hxb⟩⟩
  omega

lemma card_union_le_of_two {a b : Finset (Fin n)} {x y : Fin n} (hxy : x ≠ y)
    (hxa : x ∈ a) (hxb : x ∈ b) (hya : y ∈ a) (hyb : y ∈ b) :
    (a ∪ b).card + 2 ≤ a.card + b.card := by
  have h := card_union_add_card_inter a b
  have : 2 ≤ (a ∩ b).card := by
    have : ({x, y} : Finset (Fin n)) ⊆ a ∩ b := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [*]
    have h2 := card_le_card this
    rwa [card_pair hxy] at h2
  omega


lemma bad_card (hU : ∀ e ∈ H, e.card = 3)
    (hF : ∀ S : Finset (Fin n), S.card = 6 → #{e ∈ H | e ⊆ S} < 3) (hn : 6 ≤ n) :
    #(H.filter (fun e => ¬ ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1)) ≤ 2 * (n + 1) := by
  set B := H.filter (fun e => ¬ ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1) with hB
  -- two bad edges through a common vertex are partners
  have key : ∀ e1 ∈ B, ∀ e2 ∈ B, ∀ e3 ∈ B, ∀ v, v ∈ e1 → v ∈ e2 → v ∈ e3 →
      e1 ≠ e2 → e1 ≠ e3 → e2 = e3 := by
    intro e1 h1 e2 h2 e3 h3 v hv1 hv2 hv3 h12 h13
    rw [hB, mem_filter] at h1 h2 h3
    obtain ⟨h1H, h1b⟩ := h1
    push Not at h1b
    obtain ⟨f, hfH, hfe, hf2⟩ := h1b
    have hcf : (e1 ∪ f).card ≤ 4 := by
      have h := card_union_add_card_inter e1 f
      rw [hU _ h1H, hU _ hfH] at h
      omega
    have part : ∀ g ∈ H, v ∈ g → g ≠ e1 → g = f := by
      intro g hg hvg hge
      by_contra hgf
      have hu := card_union_le_of_mem (a := e1 ∪ f) (b := g) (mem_union_left _ hv1) hvg
      rw [hU _ hg] at hu
      rcases three_eq hF hn h1H hfH hg (by omega) with h | h | h
      · exact hfe h.symm
      · exact hge h.symm
      · exact hgf h.symm
    rw [part e2 h2.1 hv2 (Ne.symm h12), part e3 h3.1 hv3 (Ne.symm h13)]
  have hfib : ∀ b ∈ B.image (fun e => e.min), #{a ∈ B | a.min = b} ≤ 2 := by
    intro b _
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hlt
    rw [mem_filter] at hx hy hz
    have hxne : x.Nonempty := by
      rw [← card_pos, hU _ (mem_filter.mp hx.1).1]; norm_num
    obtain ⟨v, hv⟩ := Finset.min_of_nonempty hxne
    have hvx := Finset.mem_of_min hv
    have hvy : v ∈ y := Finset.mem_of_min (by rw [hy.2, ← hx.2, hv])
    have hvz : v ∈ z := Finset.mem_of_min (by rw [hz.2, ← hx.2, hv])
    exact hyz (key x hx.1 y hy.1 z hz.1 v hvx hvy hvz hxy hxz)
  calc #B ≤ 2 * #(B.image (fun e => e.min)) := card_le_mul_card_image B 2 hfib
    _ ≤ 2 * (n + 1) := by
      gcongr
      exact (card_le_univ _).trans (by
        rw [show Fintype.card (WithTop (Fin n)) = Fintype.card (Option (Fin n)) from rfl,
          Fintype.card_option, Fintype.card_fin])

lemma lin_bound (hU : ∀ e ∈ H, e.card = 3)
    (hF : ∀ S : Finset (Fin n), S.card = 6 → #{e ∈ H | e ⊆ S} < 3) (hn : 6 ≤ n) (ε : ℝ)
    (hL : ε * ((n ^ 2 : ℕ) : ℝ) ≤ #(H.filter (fun e => ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1))) :
    SimpleGraph.triangleRemovalBound ε * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 := by
  classical
  set L := H.filter (fun e => ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1) with hLdef
  have hLH : ∀ e ∈ L, e ∈ H := fun e he => (mem_filter.mp he).1
  have hLU : ∀ e ∈ L, e.card = 3 := fun e he => hU e (hLH e he)
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun x y => ∃ e ∈ L, x ∈ e ∧ y ∈ e)
  have hadj : ∀ x y, G.Adj x y ↔ x ≠ y ∧ ∃ e ∈ L, x ∈ e ∧ y ∈ e := by
    intro x y
    simp only [G, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨h, ⟨e, he, a, b⟩ | ⟨e, he, a, b⟩⟩
      · exact ⟨h, e, he, a, b⟩
      · exact ⟨h, e, he, b, a⟩
    · rintro ⟨h, e, he, a, b⟩
      exact ⟨h, Or.inl ⟨e, he, a, b⟩⟩
  have hLsub : L ⊆ G.cliqueFinset 3 := by
    intro e he
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (hLU e he)
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
    refine ⟨(hadj _ _).2 ⟨hxy, _, he, by simp, by simp⟩,
      (hadj _ _).2 ⟨hxz, _, he, by simp, by simp⟩, (hadj _ _).2 ⟨hyz, _, he, by simp, by simp⟩⟩
  have hcl : G.cliqueFinset 3 ⊆ L := by
    intro t ht
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := ht
    obtain ⟨hne1, e1, he1, hx1, hy1⟩ := (hadj _ _).1 hxy
    obtain ⟨hne2, e2, he2, hx2, hz2⟩ := (hadj _ _).1 hxz
    obtain ⟨hne3, e3, he3, hy3, hz3⟩ := (hadj _ _).1 hyz
    have tri : ∀ e ∈ L, x ∈ e → y ∈ e → z ∈ e → ({x, y, z} : Finset (Fin n)) ∈ L := by
      intro e he a b c
      have hsub : ({x, y, z} : Finset (Fin n)) ⊆ e := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have h3 : ({x, y, z} : Finset (Fin n)).card = 3 :=
        card_eq_three.mpr ⟨x, y, z, hne1, hne2, hne3, rfl⟩
      rwa [eq_of_subset_of_card_le hsub (by rw [hLU e he, h3])]
    have u1 := card_union_le_of_mem hx1 hx2
    have u2 := card_union_le_of_two hne3 (mem_union_left _ hy1) hy3 (mem_union_right _ hz2) hz3
    rw [hLU _ he1, hLU _ he2] at u1
    rw [hLU _ he3] at u2
    rcases three_eq hF hn (hLH _ he1) (hLH _ he2) (hLH _ he3) (by omega) with h | h | h
    · subst h; exact tri e1 he1 hx1 hy1 hz2
    · subst h; exact tri e1 he1 hx1 hy1 hz3
    · subst h; exact tri e2 he2 hx2 hy3 hz2
  have pd : (L : Set (Finset (Fin n))).Pairwise fun x y ↦ (x ∩ y : Set (Fin n)).Subsingleton := by
    intro s hs t ht hst
    have h := (mem_filter.mp hs).2 t (hLH t ht) (Ne.symm hst)
    intro a ha b hb
    exact card_le_one.mp h a (by simpa using ha) b (by simpa using hb)
  have hEDT : G.EdgeDisjointTriangles := by
    intro s hs t ht hst
    rw [SimpleGraph.mem_cliqueSet_iff, ← SimpleGraph.mem_cliqueFinset_iff] at hs ht
    exact pd (hcl hs) (hcl ht) hst
  have hfar : G.FarFromTriangleFree ε :=
    SimpleGraph.farFromTriangleFree_of_disjoint_triangles L hLsub pd
      (by rw [Fintype.card_fin]; exact hL)
  have h1 := hfar.le_card_cliqueFinset
  have h2 := hEDT.card_edgeFinset_le
  have h3 := G.card_edgeFinset_le_card_choose_two
  have h4 : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  rw [Fintype.card_fin] at h1 h3
  have h5 : #(G.cliqueFinset 3) ≤ n ^ 2 := by omega
  calc _ ≤ (#(G.cliqueFinset 3) : ℝ) := h1
    _ ≤ _ := by exact_mod_cast h5

end E716

theorem OMA.solution : type_of% @Erdos716.erdos_716 := by
  classical
  rw [isLittleO_iff]
  intro c hc
  set ε := c / 2 with hε
  have hεp : 0 < ε := by positivity
  set δ := SimpleGraph.triangleRemovalBound ε with hδ
  have hδp : 0 < δ := SimpleGraph.triangleRemovalBound_pos hεp
  filter_upwards [eventually_ge_atTop (⌈2 / δ⌉₊ + ⌈8 / c⌉₊ + 6)] with n hn
  have hn6 : 6 ≤ n := by omega
  have hnδ : 2 / δ ≤ (n : ℝ) := by
    have := Nat.le_ceil (2 / δ)
    have : (⌈2 / δ⌉₊ : ℝ) ≤ n := by exact_mod_cast (show ⌈2 / δ⌉₊ ≤ n by omega)
    linarith
  have hnc : 8 / c ≤ (n : ℝ) := by
    have := Nat.le_ceil (8 / c)
    have : (⌈8 / c⌉₊ : ℝ) ≤ n := by exact_mod_cast (show ⌈8 / c⌉₊ ≤ n by omega)
    linarith
  have hn6r : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have hnpos : (0 : ℝ) < n := by linarith
  have hbound : ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = 3) →
      (∀ S : Finset (Fin n), S.card = 6 → #{e ∈ H | e ⊆ S} < 3) →
      (#H : ℝ) ≤ c * (n : ℝ) ^ 2 := by
    intro H hU hF
    have hsplit := card_filter_add_card_filter_not
      (s := H) (fun e => ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1)
    have hB := E716.bad_card hU hF hn6
    have hL : (#(H.filter (fun e => ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1)) : ℝ) < ε * (n : ℝ) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have := E716.lin_bound hU hF hn6 ε (by push_cast; exact hcon)
      have h2 : δ * (n : ℝ) ≤ 1 := by
        have : (n : ℝ) ^ 2 * (δ * n) ≤ (n : ℝ) ^ 2 * 1 := by nlinarith
        exact le_of_mul_le_mul_left this (by positivity)
      have : 2 ≤ δ * (n : ℝ) := by
        rw [div_le_iff₀ hδp] at hnδ; linarith
      linarith
    have hBr : (#(H.filter (fun e => ¬ ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1)) : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
      exact_mod_cast hB
    have hcn : 8 ≤ c * (n : ℝ) := by rw [div_le_iff₀ hc] at hnc; linarith
    have : 2 * ((n : ℝ) + 1) ≤ ε * (n : ℝ) ^ 2 := by
      rw [hε]; nlinarith
    have hsum : (#H : ℝ) = (#(H.filter (fun e => ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1)) : ℝ) +
        (#(H.filter (fun e => ¬ ∀ f ∈ H, f ≠ e → (e ∩ f).card ≤ 1)) : ℝ) := by
      exact_mod_cast hsplit.symm
    rw [hsum]
    have : ε * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2 = c * (n : ℝ) ^ 2 := by rw [hε]; ring
    linarith
  have hsup : Hypergraph.configurationExtremalNumber n 3 6 3 ≤ ⌊c * (n : ℝ) ^ 2⌋₊ := by
    unfold Hypergraph.configurationExtremalNumber Hypergraph.extremalNumber
    apply Finset.sup_le
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    obtain ⟨hsub, hnot⟩ := hH
    apply Nat.le_floor
    apply hbound H
    · intro e he
      exact (mem_powersetCard.mp (hsub he)).2
    · intro S hS
      by_contra hcon
      push Not at hcon
      exact hnot ⟨S, hS, hcon⟩
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (Hypergraph.configurationExtremalNumber n 3 6 3 : ℝ) ≤ (⌊c * (n : ℝ) ^ 2⌋₊ : ℝ) := by
        exact_mod_cast hsup
    _ ≤ c * (n : ℝ) ^ 2 := Nat.floor_le (by positivity)
